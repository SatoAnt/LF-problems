#!/usr/bin/env python3
"""lemmafund CI: decides whether a change to the problems repo is acceptable.

Runs on every push to a `ci/**` branch (made by the lemmafund server, one commit on top of
main) and on `main` itself. Anyone can run it locally to re-check work:

    python3 ci/verify.py --branch ci/submit/SumOdd/t-1a2b3c4d5e
    python3 ci/verify.py --branch main

Branch kinds and what each may change (anything else fails):
  ci/submit/<Module>/<task>     add exactly one proof file  Problems/<Module>/Proofs/T_<id>.lean
  ci/statement/<Module>/<n>     add exactly                 Problems/<Module>/Target.lean
  ci/open/<Module>/<n>          add exactly                 Target, Goals, meta.json, Library (a blessed statement)
  ci/goals/<Module>/<v>         modify only                 Problems/<Module>/Goals.lean (+ meta.json)
  main                          anything; rebuilds every problem the push touched

Every check, in order: allowed changes → source scan (before building, since building runs
a file's metaprograms) → network-isolated build → Lean-side checker of every declaration
(ci/check_module.lean) → for proofs, a collision check against everything already merged.
"""
from __future__ import annotations
import argparse, hashlib, json, os, pathlib, re, shutil, subprocess, sys

HERE = pathlib.Path(__file__).resolve().parent
ROOT = HERE.parent  # the checkout being verified; --root overrides (CI runs a trusted copy of ci/)
sys.path.insert(0, str(HERE))
import scan  # noqa: E402

FAILS: list[str] = []


def fail(msg: str) -> None:
    FAILS.append(msg)
    print(f"FAIL {msg}", flush=True)


def finish() -> int:
    summary = os.environ.get("GITHUB_STEP_SUMMARY")
    if FAILS:
        text = "## lemmafund verify: FAIL\n\n" + "\n".join(f"- {f}" for f in FAILS) + "\n"
        print("RESULT: FAIL")
    else:
        text = "## lemmafund verify: PASS\n"
        print("RESULT: PASS")
    if summary:
        with open(summary, "a") as fh:
            fh.write(text)
    return 1 if FAILS else 0


def sha256_file(p: pathlib.Path) -> str:
    return hashlib.sha256(p.read_bytes()).hexdigest()


# ───────────── changes ─────────────

def claims_from_git() -> list[str]:
    """Goals the submission says it proves, from a `Lemmafund-Claims: a,b` commit trailer
    (written by the server). Each must exist in the file with exactly the goal's type."""
    out = subprocess.run(["git", "log", "-1", "--format=%B"], cwd=ROOT, capture_output=True, text=True)
    for line in out.stdout.splitlines():
        if line.lower().startswith("lemmafund-claims:"):
            return [c.strip() for c in line.split(":", 1)[1].split(",") if c.strip()]
    return []


def changes_from_git() -> list[tuple[str, str]]:
    out = subprocess.run(["git", "diff", "--name-status", "--no-renames", "HEAD~1", "HEAD"],
                         cwd=ROOT, capture_output=True, text=True)
    if out.returncode:
        raise SystemExit(f"git diff failed: {out.stderr.strip()}")
    rows = []
    for line in out.stdout.splitlines():
        parts = line.split("\t")
        if len(parts) == 2:
            rows.append((parts[0][:1], parts[1]))
    return rows


# ───────────── running Lean, without network ─────────────

def isolated(cmd: list[str]) -> list[str]:
    """Wrap a command so it runs with no network, and (on CI) as an unprivileged user.

    On GitHub's runners the default user has passwordless sudo, which could undo a network
    namespace. So CI creates a separate user with no sudo rights (LEMMAFUND_BUILD_USER) and
    every Lean command runs as that user inside a fresh network namespace."""
    build_user = os.environ.get("LEMMAFUND_BUILD_USER")
    keep = [f"{k}={os.environ[k]}" for k in ("PATH", "ELAN_HOME", "LANG") if k in os.environ]
    if build_user:
        return (["sudo", "-n", "unshare", "-n", "--", "sudo", "-n", "-u", build_user, "--",
                 "env", "-i", f"HOME=/home/{build_user}"] + keep + cmd)
    if shutil.which("unshare"):
        if os.geteuid() == 0:
            return ["unshare", "-n", "--"] + cmd
        if subprocess.run(["unshare", "-rn", "true"], capture_output=True).returncode == 0:
            return ["unshare", "-rn", "--"] + cmd
    if os.environ.get("GITHUB_ACTIONS"):
        raise SystemExit("network isolation unavailable on CI; refusing to build untrusted code")
    print("warning: no network isolation available locally; building anyway", flush=True)
    return cmd


def run(cmd: list[str], timeout: int = 3600, isolate: bool = True) -> subprocess.CompletedProcess:
    full = isolated(cmd) if isolate else cmd
    print("$ " + " ".join(cmd), flush=True)
    r = subprocess.run(full, cwd=ROOT, capture_output=True, text=True, timeout=timeout)
    out = (r.stdout + r.stderr).strip()
    if out:
        print("\n".join(out.splitlines()[-60:]), flush=True)
    return r


def build(module: str) -> bool:
    r = run(["lake", "build", module])
    if r.returncode:
        fail(f"{module} does not build")
        return False
    return True


def check_modules(modules: list[str], goals=(), defs=(), require=()) -> bool:
    args = ["lake", "env", "lean", "--run", str(HERE / "check_module.lean")] + list(modules)
    if goals:
        args += ["--goals", ",".join(goals)]
    if defs:
        args += ["--defs", ",".join(defs)]
    if require:
        args += ["--require", ",".join(require)]
    r = run(args)
    for line in (r.stdout + r.stderr).splitlines():
        if line.startswith("FAIL"):
            FAILS.append(line[5:])
    if r.returncode and not any(l.startswith("FAIL") for l in (r.stdout + r.stderr).splitlines()):
        fail("the Lean checker could not run")
    return r.returncode == 0


# ───────────── per-kind checks ─────────────

def load_meta(module: str) -> dict | None:
    p = ROOT / "Problems" / module / "meta.json"
    if not p.exists():
        fail(f"Problems/{module}/meta.json is missing")
        return None
    meta = json.loads(p.read_text())
    tgt = ROOT / "Problems" / module / "Target.lean"
    if not tgt.exists() or sha256_file(tgt) != meta.get("target_sha256"):
        fail("Target.lean does not match the blessed statement recorded in meta.json")
    goals = ROOT / "Problems" / module / "Goals.lean"
    if not goals.exists() or sha256_file(goals) != meta.get("goals_sha256"):
        fail("Goals.lean does not match meta.json")
    return meta


def scan_file(path: pathlib.Path, kind: str, module: str) -> bool:
    problems = scan.scan_text(path.read_text(errors="replace"), kind, module)
    for p in problems:
        fail(f"{path.relative_to(ROOT)}: {p}")
    return not problems


def verify_submit(module: str, task: str, changes: list[tuple[str, str]], claims: list[str],
                  guard_only: bool) -> None:
    mod = scan.proof_module_for_task(module, task)
    expected = scan.path_for_module(mod)
    if changes != [("A", expected)]:
        fail(f"a submission may only add {expected}; this commit changes {changes}")
        return
    meta = load_meta(module)
    if FAILS or meta is None:
        return
    goal_ids = [g["id"] for g in meta.get("goals", [])]
    for c in claims:
        if c not in goal_ids:
            fail(f"claims goal '{c}', which this problem doesn't have")
    if not scan_file(ROOT / expected, "proof", module) or FAILS or guard_only:
        return
    if not build(mod):
        return
    check_modules([mod], goals=goal_ids, require=claims)
    # Collision check: the new file together with everything already merged must build.
    audit = ROOT / "Problems" / module / "CIAudit.lean"
    audit.write_text(f"import Problems.{module}.Library\nimport {mod}\n")
    try:
        if run(["lake", "build", f"Problems.{module}.CIAudit"]).returncode:
            fail("the proof clashes with already-merged work (a name is declared twice?)")
    finally:
        audit.unlink(missing_ok=True)


def verify_statement(module: str, changes: list[tuple[str, str]], guard_only: bool) -> None:
    expected = f"Problems/{module}/Target.lean"
    if changes != [("A", expected)]:
        fail(f"a statement check may only add {expected}; this commit changes {changes}")
        return
    if not scan_file(ROOT / expected, "target", module) or guard_only:
        return
    if build(f"Problems.{module}.Target"):
        check_modules([f"Problems.{module}.Target"], defs=["root_stmt"])


def verify_open(module: str, changes: list[tuple[str, str]], guard_only: bool) -> None:
    d = f"Problems/{module}"
    expected = {("A", f"{d}/Target.lean"), ("A", f"{d}/Goals.lean"), ("A", f"{d}/meta.json"),
                ("A", f"{d}/Library.lean")}
    if set(changes) != expected:
        fail(f"opening a problem adds exactly Target.lean, Goals.lean, meta.json and Library.lean; "
             f"this commit changes {changes}")
        return
    meta = load_meta(module)
    if FAILS or meta is None:
        return
    if [g.get("id") for g in meta.get("goals", [])] != ["root"]:
        fail("a new problem starts with exactly one goal, root")
    lib = (ROOT / d / "Library.lean").read_text()
    if scan.imports(lib) != [f"Problems.{module}.Goals"]:
        fail("a new Library.lean imports only the problem's Goals")
    ok = scan_file(ROOT / d / "Target.lean", "target", module)
    ok = scan_file(ROOT / d / "Goals.lean", "goals", module) and ok
    if not ok or FAILS or guard_only:
        return
    if build(f"Problems.{module}.Library"):
        check_modules([f"Problems.{module}.Target"], defs=["root_stmt"])


def verify_goals(module: str, changes: list[tuple[str, str]], guard_only: bool) -> None:
    allowed = {("M", f"Problems/{module}/Goals.lean"), ("M", f"Problems/{module}/meta.json")}
    if not changes or not set(changes) <= allowed or ("M", f"Problems/{module}/Goals.lean") not in changes:
        fail(f"a goals check may only modify Goals.lean and meta.json; this commit changes {changes}")
        return
    meta = load_meta(module)
    if FAILS or meta is None:
        return
    for g in meta.get("goals", []):
        if not scan.GOAL_ID.match(g.get("id", "")):
            fail(f"bad goal id {g.get('id')!r}")
    # Goals are append-only: proofs already merged were checked against the old statements.
    old = subprocess.run(["git", "show", f"HEAD~1:Problems/{module}/Goals.lean"], cwd=ROOT,
                         capture_output=True, text=True).stdout
    new = (ROOT / "Problems" / module / "Goals.lean").read_text()
    if old and not new.startswith(old.rstrip("\n")):
        fail("Goals.lean may only grow: existing goals can't be edited or removed")
    if not scan_file(ROOT / "Problems" / module / "Goals.lean", "goals", module) or FAILS or guard_only:
        return
    if build(f"Problems.{module}.Goals"):
        defs = [f"{g['id']}_stmt" for g in meta.get("goals", []) if g["id"] != "root"]
        check_modules([f"Problems.{module}.Goals"], defs=defs)
        if (ROOT / "Problems" / module / "Library.lean").exists():
            build(f"Problems.{module}.Library")


def verify_main(changes: list[tuple[str, str]], guard_only: bool) -> None:
    if guard_only:
        return
    touched = sorted({p.split("/")[1] for s, p in changes if p.startswith("Problems/") and p.count("/") >= 2})
    for module in touched:
        if not (ROOT / "Problems" / module / "Library.lean").exists():
            continue
        load_meta(module)
        if build(f"Problems.{module}.Library"):
            new = [p for s, p in changes if s == "A" and p.startswith(f"Problems/{module}/Proofs/")]
            if new:
                check_modules([p[:-5].replace("/", ".") for p in new])


def verify_all() -> None:
    """Re-check everything: every problem's statement, goals and merged proofs."""
    for d in sorted((ROOT / "Problems").iterdir()):
        if not (d / "Library.lean").exists():
            continue
        module = d.name
        meta = load_meta(module)
        if meta is None or not build(f"Problems.{module}.Library"):
            continue
        proofs = sorted(f"Problems.{module}.Proofs.{p.stem}" for p in (d / "Proofs").glob("T_*.lean")) \
            if (d / "Proofs").is_dir() else []
        for p in proofs:
            scan_file(ROOT / scan.path_for_module(p), "proof", module)
        check_modules([f"Problems.{module}.Target"], defs=["root_stmt"])
        defs = [f"{g['id']}_stmt" for g in meta.get("goals", []) if g["id"] != "root"]
        if defs:
            check_modules([f"Problems.{module}.Goals"], defs=defs)
        if proofs:
            check_modules(proofs, goals=[g["id"] for g in meta.get("goals", [])])
        print(f"checked {module}: {len(proofs)} proof files", flush=True)


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--branch", default=os.environ.get("GITHUB_REF_NAME", ""))
    ap.add_argument("--changes-file", help="JSON [[status, path], ...] instead of git diff (testing)")
    ap.add_argument("--claims", help="comma-separated claimed goals instead of the commit trailer (testing)")
    ap.add_argument("--guard-only", action="store_true",
                    help="only check which files changed and scan sources; build nothing. Runs on CI "
                         "before anything is downloaded, so a change to the build setup is refused first")
    ap.add_argument("--root", help="the checkout to verify (default: the parent of this script)")
    ap.add_argument("--all", action="store_true", help="re-check every problem in the repo, not one change")
    a = ap.parse_args()
    global ROOT
    if a.root:
        ROOT = pathlib.Path(a.root).resolve()
    if a.all:
        verify_all()
        return finish()
    changes = ([tuple(x) for x in json.loads(pathlib.Path(a.changes_file).read_text())]
               if a.changes_file else changes_from_git())
    claims = ([c for c in a.claims.split(",") if c] if a.claims is not None else claims_from_git())
    print(f"branch: {a.branch}\nchanges: {changes}\nclaims: {claims}", flush=True)
    parts = a.branch.split("/")
    if parts[0] == "ci" and len(parts) == 4 and re.fullmatch(r"[A-Za-z][A-Za-z0-9]*", parts[2]):
        kind, module, ident = parts[1], parts[2], parts[3]
        if kind == "submit":
            verify_submit(module, ident, changes, claims, a.guard_only)
        elif kind == "statement":
            verify_statement(module, changes, a.guard_only)
        elif kind == "open":
            verify_open(module, changes, a.guard_only)
        elif kind == "goals":
            verify_goals(module, changes, a.guard_only)
        else:
            fail(f"unknown check kind {kind}")
    elif a.branch == "main":
        verify_main(changes, a.guard_only)
    else:
        fail(f"not a lemmafund check branch: {a.branch}")
    return finish()


if __name__ == "__main__":
    sys.exit(main())
