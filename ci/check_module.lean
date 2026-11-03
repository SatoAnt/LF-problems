/-
lemmafund trust-side checker. Loads compiled modules and inspects every declaration they
define, using Lean's own data rather than reading source text:

  • no `axiom` declarations, nothing `unsafe`, no `opaque` constants
  • no `@[implemented_by]` / `@[extern]` (native code swapped in for a definition)
  • every declaration depends only on {propext, Classical.choice, Quot.sound}
    (so no `sorry`, which shows up as `sorryAx`, and no native-evaluation axioms)
  • --goals g1,g2: each goal that one of the checked modules defines must be a theorem whose
    type is exactly `<goal>_stmt` (so a weaker claim can't be passed off under the goal's name).
    Goals the modules don't define are skipped: a proof file proves some goals, not all.
  • --require g1,g2: these goals must be among the ones defined (and so exactly typed).
  • --defs d1,d2: each name must be a definition of type `Prop` in the checked modules
    (Target.lean must define `root_stmt`; Goals.lean must define every `<goal>_stmt`).

Usage (inside the Lean project):
  lake env lean --run ci/check_module.lean <module>... [--goals a,b] [--require a] [--defs x,y]
Exit code 0 = pass. Every problem is printed on its own line starting with "FAIL".
-/
import Lean
open Lean

def allowedAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

def isCompilerStage (n : Name) : Bool :=
  match n with
  | .str _ s => s.startsWith "_cstage"
  | _ => false

def splitList (s : String) : List String :=
  (s.splitOn ",").map String.trim |>.filter (· ≠ "")

def checkAll (env : Environment) (mods : List Name) (goals defs require : List String) :
    IO (List String) := do
  let mut problems : List String := []
  let modIdxs : List Nat := mods.filterMap fun m =>
    (env.header.moduleNames.toList.idxOf? m)
  if modIdxs.length != mods.length then
    problems := problems ++ [s!"FAIL could not find all modules {mods}"]
  let inMods (n : Name) : Bool :=
    match env.getModuleIdxFor? n with
    | some idx => modIdxs.contains idx.toNat
    | none => false
  let ctx : Core.Context := { fileName := "<lemmafund-check>", fileMap := default }
  let st : Core.State := { env }
  let mut seen := 0
  for (n, ci) in env.constants.map₁.toList do
    unless inMods n do continue
    seen := seen + 1
    match ci with
    | .axiomInfo _ => problems := problems ++ [s!"FAIL {n}: declares a new axiom"]
    | .opaqueInfo _ => problems := problems ++ [s!"FAIL {n}: opaque constant"]
    | _ => pure ()
    -- The compiler emits unsafe `_cstageN` copies of every compiled definition. The kernel
    -- never lets a safe declaration use an unsafe one, so these can't affect any proof; user
    -- code can't write `unsafe` at all (ci/scan.py), so skipping exactly these is safe.
    if ci.isUnsafe && !isCompilerStage n then
      problems := problems ++ [s!"FAIL {n}: unsafe declaration"]
    if (Compiler.implementedByAttr.getParam? env n).isSome then
      problems := problems ++ [s!"FAIL {n}: @[implemented_by] swaps in unchecked code"]
    if isExtern env n then
      problems := problems ++ [s!"FAIL {n}: @[extern] swaps in unchecked code"]
    let (axs, _) ← (collectAxioms n : CoreM (Array Name)).toIO ctx st
    let bad := axs.toList.filter (fun a => !allowedAxioms.contains a)
    unless bad.isEmpty do
      problems := problems ++ [s!"FAIL {n}: depends on disallowed axioms {bad}"]
  if seen == 0 then
    problems := problems ++ ["FAIL no declarations found in the checked modules"]
  for g in goals do
    let gname := g.toName
    let stmt := (g ++ "_stmt").toName
    unless inMods gname do continue
    match env.find? gname with
    | some (.thmInfo t) =>
      unless t.type == mkConst stmt do
        problems := problems ++ [s!"FAIL goal {g}: type is not exactly {stmt}"]
    | some _ => problems := problems ++ [s!"FAIL goal {g}: is not a theorem"]
    | none => pure ()
  for g in require do
    unless inMods g.toName do
      problems := problems ++ [s!"FAIL goal {g}: claimed but not proved here (must be a top-level theorem `{g}`)"]
  for d in defs do
    let dname := d.toName
    match env.find? dname with
    | some (.defnInfo v) =>
      unless inMods dname do
        problems := problems ++ [s!"FAIL {d}: defined outside the checked modules"]
      unless v.type == mkSort levelZero do
        problems := problems ++ [s!"FAIL {d}: must have type Prop"]
      unless v.levelParams.isEmpty do
        problems := problems ++ [s!"FAIL {d}: must not be universe-polymorphic"]
    | some _ => problems := problems ++ [s!"FAIL {d}: must be a `def … : Prop`"]
    | none => problems := problems ++ [s!"FAIL {d}: not defined"]
  return problems

def main (args : List String) : IO UInt32 := do
  let mut mods : List String := []
  let mut goals : List String := []
  let mut defs : List String := []
  let mut require : List String := []
  let mut rest := args
  while !rest.isEmpty do
    match rest with
    | "--goals" :: v :: tl => goals := goals ++ splitList v; rest := tl
    | "--defs" :: v :: tl => defs := defs ++ splitList v; rest := tl
    | "--require" :: v :: tl => require := require ++ splitList v; rest := tl
    | x :: tl =>
      if x.startsWith "--" then
        IO.eprintln s!"unknown option {x}"; return 2
      mods := mods ++ [x]; rest := tl
    | [] => rest := []
  if mods.isEmpty then
    IO.eprintln "usage: check_module <module>... [--goals a,b] [--require a] [--defs x,y]"
    return 2
  initSearchPath (← findSysroot)
  let modNames := mods.map String.toName
  let env ← importModules (modNames.map fun m => { module := m }).toArray {} 0
  let problems ← checkAll env modNames (goals ++ require).eraseDups defs require
  for p in problems do IO.println p
  if problems.isEmpty then
    IO.println s!"PASS {mods} (goals: {goals}, defs: {defs})"
    return 0
  return 1
