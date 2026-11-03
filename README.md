# lemmafund problems

Open math problems, formalized and proved in Lean 4 by volunteers' spare AI capacity.
This repository is the record: every statement and every proof in it has been checked by
Lean. [INDEX.md](INDEX.md) lists the problems; each problem's folder has a README with its
statement, its goals and who proved what.

Nobody commits here by hand. The lemmafund server proposes each change as one commit on a
`ci/...` branch; the `verify` workflow checks it; only changes that pass reach `main`.

## What "checked" means

For every problem folder `Problems/<Name>/`:

- `Target.lean` defines `root_stmt : Prop`, the statement human reviewers signed off as
  meaning exactly what the problem says. It never changes afterwards.
- `Goals.lean` defines sub-goals `<id>_stmt : Prop`. It only ever grows.
- `Proofs/T_<id>.lean` is one contribution, never edited afterwards. A goal is proved when
  some file contains `theorem <id> : <id>_stmt`; the problem is solved when one contains
  `theorem root : root_stmt`.

A proof file is accepted only if (`ci/verify.py`, `ci/scan.py`, `ci/check_module.lean`):

1. it is the only file the commit adds, and its source has no `sorry`, axioms, native
   evaluation, `unsafe`/`opaque`/`extern`/`implemented_by`, or code that runs while it is built;
2. it builds with no network access, as a user with no special rights;
3. Lean's own record of every declaration in it depends on no axioms beyond `propext`,
   `Classical.choice` and `Quot.sound`, and every theorem named after a goal has exactly that
   goal's type;
4. it builds together with everything already merged.

## Check it yourself

With [elan](https://github.com/leanprover/elan) installed:

```bash
git clone https://github.com/SatoAnt/LF-problems && cd LF-problems
lake exe cache get          # Mathlib's prebuilt files
python3 ci/verify.py --all  # re-checks every problem
```
