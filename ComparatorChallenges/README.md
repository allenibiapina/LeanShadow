# Comparator challenge

[`Shadow.lean`](Shadow.lean) states twelve main results using only Mathlib and
explicit geometric definitions. It does not import the proof library. Its twelve
intentional `sorry` theorem placeholders specify what must be proved; they are
not proof certificates. Every definition is complete.

[`../LeanShadow/ComparatorSolution.lean`](../LeanShadow/ComparatorSolution.lean)
proves the same statements using the existing development. It imports its own
[`ComparatorDefinitions`](../LeanShadow/ComparatorDefinitions.lean), never the
challenge. The proof entry point also never imports the challenge.

The reference was written for this package from [MAIN_STATEMENT.md](../MAIN_STATEMENT.md).
It is not a pre-existing statement reviewed by an independent mathematical project.
Comparator checks agreement with this reference, not whether the reference is the
intended mathematical problem.

## Running the check

The workflow follows the
[OpenAI proof release](https://github.com/openai/NavierStokesAndEuler/blob/f9e8bc5b38b6e212696e8a30e3e91517af887bbd/ComparatorChallenges/README.md).
Install [landrun](https://github.com/Zouuup/landrun),
[lean4export](https://github.com/leanprover/lean4export) compatible with Lean 4.33.0,
and [nanoda_bin](https://github.com/ammkrn/nanoda_lib), and put them on `PATH`.
Use nanoda commit `4c544ed4099c8227f07d5de77ad1e69fb0740a27` (version 0.4.17)
with this package; older nanoda releases cannot parse its export format. The
checked tool revisions are recorded in [verification-tools.json](../verification-tools.json).
The exporter is already pinned as a transitive Lake dependency and can be built with:

```bash
lake build lean4export comparator
```

Then, from the LeanShadow package root:

```bash
lake exe cache get
lake exe comparator ComparatorChallenges/LeanShadow.json
```

The configuration enables nanoda and permits only `propext`, `Quot.sound`, and
`Classical.choice`. Comparator compares the theorem types and definitions, audits
axioms, and checks exported proofs with Lean and nanoda.

Follow the pinned [Comparator sandbox instructions](https://github.com/leanprover/comparator/tree/3927ad383f208ae977c340a91c48ac9b497d2097)
when checking untrusted submissions. On Linux before 7.1, its recommended invocation
adds a systemd restriction on Unix-domain sockets:

```bash
systemd-run --user --pipe --wait --collect \
  --property=RestrictAddressFamilies=~AF_UNIX \
  --working-directory="$PWD" -E PATH="$PATH" \
  lake exe comparator ComparatorChallenges/LeanShadow.json
```

Local checker executables, if installed under `.tools/bin`, can be activated with:

```bash
export PATH="$PWD/.tools/bin:$PWD/.lake/packages/lean4export/.lake/build/bin:$PATH"
```

The optional `scripts/replay.py` uses Lean's bundled checker. It is a different
check and does not substitute for a completed Comparator/nanoda run. Consult
[VERIFICATION.md](../VERIFICATION.md) for the actual recorded results.
