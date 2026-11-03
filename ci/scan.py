"""lemmafund source rules, shared by CI and the server (single source of truth).

Two jobs:
  1. scan_text(): reject constructs that run code at build time or fake a proof, BEFORE any
     Lean is built. Building a file runs its metaprograms, so this must come first.
  2. layout helpers: where each problem's files live and what a file may import.

The deeper check (every declaration's axioms, goal types) is done by Lean itself in
ci/check_module.lean after the build. This scan is the cheap first line.
"""
from __future__ import annotations
import re

# (regex, reason). Applied to source with comments stripped.
FORBIDDEN_PROOF = [
    (r"\bsorry\b", "incomplete proof (sorry)"),
    (r"\badmit\b", "incomplete proof (admit)"),
    (r"\bsorryAx\b", "direct use of sorryAx"),
    (r"\bnative_decide\b", "native evaluation (native_decide)"),
    (r"\bdecide\s*\+\s*native\b", "native evaluation (decide +native)"),
    (r"\bbv_decide\b", "native evaluation (bv_decide)"),
    (r"Lean\.ofReduceBool|Lean\.ofReduceNat", "native evaluation (ofReduce*)"),
    (r"Lean\.trustCompiler", "compiler-trust axiom"),
    (r"@\[\s*implemented_by", "implemented_by swap"),
    (r"@\[\s*extern", "extern swap"),
    (r"^\s*(private\s+|protected\s+)?axiom\b", "axiom declaration"),
    (r"\bopaque\b", "opaque declaration"),
    (r"\bunsafe\b", "unsafe declaration"),
    (r"\bpartial\b", "partial declaration"),
    (r"skipKernelTC|debug\.skipKernelTC", "kernel type-check bypass"),
    (r"set_option\s+debug\.", "debug option"),
    (r"set_option\s+maxHeartbeats\s+0\b", "disabled heartbeat limit"),
    # Code that runs while the file is built: it would run on CI and on every later
    # contributor's machine. Proofs never need it.
    (r"#eval\b|#exit\b|#print\s+raw", "build-time command"),
    (r"\brun_(cmd|tac|elab|meta)\b", "build-time code execution"),
    (r"\b(builtin_)?initialize\b", "initialize block"),
    (r"@\[\s*init\b", "@[init]"),
    (r"^\s*(local\s+|scoped\s+)?(elab|macro|syntax|elab_rules|macro_rules|declare_syntax_cat|notation3?)\b",
     "custom syntax or elaborator"),
    (r"\bIO\.|\bunsafeBaseIO\b|\bunsafeIO\b|\bSystem\.IO\b|\bIO\s+Unit\b", "IO"),
    (r"\bLean\.Elab\b|\bLean\.Meta\b|\bLean\.Environment\b|\baddDecl\b", "metaprogramming API"),
    (r"^\s*import\s+Lean\b", "import of Lean internals"),
]

# Statements (Target.lean, Goals.lean) may define things but follow the same bans.
FORBIDDEN_STATEMENT = FORBIDDEN_PROOF

MAX_LINE = 2000


def strip_comments(text: str) -> str:
    # Block comments can nest in Lean; strip innermost-first until stable.
    prev = None
    while prev != text:
        prev = text
        text = re.sub(r"/-(?:(?!/-|-/).)*?-/", " ", text, flags=re.S)
    text = re.sub(r"--[^\n]*", "", text)
    # String literals can hide nothing dangerous on their own, but keep their contents
    # from tripping the scan ("sorry" in a docstring was already removed above).
    return text


def imports(text: str) -> list[str]:
    return [m for line in re.findall(r"^\s*import\s+(.+)$", strip_comments(text), flags=re.M)
            for m in line.split()]


def scan_text(text: str, kind: str, module: str) -> list[str]:
    """Problems with a source file. kind: 'proof' | 'target' | 'goals'."""
    problems = []
    if "\x00" in text:
        problems.append("file contains NUL bytes")
    if any(len(l) > MAX_LINE for l in text.splitlines()):
        problems.append(f"a line is longer than {MAX_LINE} characters")
    body = strip_comments(text)
    rules = FORBIDDEN_PROOF if kind == "proof" else FORBIDDEN_STATEMENT
    for rx, why in rules:
        if re.search(rx, body, flags=re.M):
            problems.append(why)
    for imp in imports(text):
        if not import_allowed(imp, kind, module):
            problems.append(f"import of '{imp}' is not allowed here")
    if kind == "target" and not re.search(r"^\s*(noncomputable\s+)?def\s+root_stmt\s*:\s*Prop\s*:=", body, flags=re.M):
        problems.append("Target.lean must define `def root_stmt : Prop := …`")
    return sorted(set(problems))


def import_allowed(imp: str, kind: str, module: str) -> bool:
    if imp == "Mathlib" or imp.startswith("Mathlib.") or imp == "Batteries" or imp.startswith("Batteries."):
        return True
    own = f"Problems.{module}."
    if kind == "target":
        return False
    if kind == "goals":
        return imp == own + "Target"
    return imp in (own + "Target", own + "Goals", own + "Library") or re.fullmatch(
        re.escape(own) + r"Proofs\.T_[0-9a-f]{6,32}", imp) is not None


# ───────────── layout ─────────────

def module_for_slug(slug: str) -> str:
    """'sum-odd-core' -> 'SumOddCore'. Always a valid Lean identifier segment."""
    parts = re.findall(r"[A-Za-z0-9]+", slug)
    name = "".join(p[:1].upper() + p[1:] for p in parts) or "Problem"
    if not name[0].isalpha():
        name = "P" + name
    return name[:60]


def proof_module_for_task(module: str, task_id: str) -> str:
    hexid = re.sub(r"[^0-9a-f]", "", task_id.lower())
    return f"Problems.{module}.Proofs.T_{hexid}"


def path_for_module(mod: str) -> str:
    return mod.replace(".", "/") + ".lean"


GOAL_ID = re.compile(r"^[a-z][a-z0-9_]{0,48}$")
