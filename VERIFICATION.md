# Verification record

The LeanShadow proof library was built and audited with Lean 4.33.0 and Mathlib
commit `db584cd6d46c92f209a44c0f1c829460d327499d`.

## Completed checks

- `python3 scripts/verify.py`: **PASS**, 141 proof modules, 1,019 theorems,
  and all 12 public main-result adapters. The proof build has no warnings or errors.
- Every theorem reports only `propext`, `Classical.choice`, and `Quot.sound`.
  There are no proof-library shortcuts or custom axioms.
- All 138 original modules are preserved exactly after reversing the local-import
  prefix change. The original workspace sources were not modified.
- The standalone Comparator reference imports only Mathlib. Its twelve theorem
  signatures match the proved submission; no proof module imports the reference.
- `formalization.yaml` validates against the published v0.4 JSON schema.

Source hashes and theorem axiom reports are included in
[verification.json](verification.json). Rerunning the audit also writes detailed
build output to the local `build.log`, which is excluded from Git.
The before/after import migration is recorded in [provenance.json](provenance.json).

## Comparator and external kernel

The reference-style check **passed for all 12 main results**, with exit code 0.
Comparator accepted the statement definitions and permitted axioms; both nanoda
and Lean accepted the exported proof dependency closure. The final tool output was
`Your solution is okay!`. Detailed results and input hashes are in
[comparator-status.json](comparator-status.json).

The run used Comparator
`3927ad383f208ae977c340a91c48ac9b497d2097`, lean4export
`15f6055e299ad5b89345e533cc2192f4cc00f659`, landrun v0.1.17, and nanoda v0.4.17
(commit `4c544ed4099c8227f07d5de77ad1e69fb0740a27`).
The run enables nanoda and uses the systemd Unix-socket restriction recommended
by Comparator for this Linux kernel. Its local output is in `comparator.log`, which
is excluded from Git. Tool revisions and binary hashes are recorded
in [verification-tools.json](verification-tools.json).

The twelve `sorry` placeholders in `ComparatorChallenges/Shadow.lean` are deliberate
reference statements, matching the convention in the OpenAI release. They are
excluded from the proof build, the 1,019-theorem audit, and the proved submission.
All challenge definitions are complete.

The reference statements were written for LeanShadow; they have not been supplied
or reviewed by an independent mathematical organization. Mechanical agreement with
this reference does not itself establish that its definitions express the intended
informal mathematics. The existing theorem statements are also retained for review.

## Reproduction

```bash
lake exe cache get
lake build
python3 scripts/verify.py
lake build lean4export comparator
# With landrun, lean4export, and nanoda_bin on PATH:
lake exe comparator ComparatorChallenges/LeanShadow.json
```

See [ComparatorChallenges/README.md](ComparatorChallenges/README.md) for the
sandboxed invocation and [README.md](README.md) for the package structure.
