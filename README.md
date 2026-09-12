# LeanShadow

Lean 4 formalization of the sharp orthogonality-shadow theorem and its double-cap
consequence. The full statements are in [MAIN_STATEMENT.md](MAIN_STATEMENT.md).

For ambient dimension at least three, the formalization proves:

- A sharp lower bound for the compact inner measure of the literal orthogonality
  shadow of any completed-measurable spherical set of prescribed area.
- Attainment by opposite caps and almost-everywhere rigidity at interior masses.
- The corresponding results on the antipodal projective quotient.
- The double-cap bound, attainment, and rigidity for sets containing no orthogonal
  pair, including the explicit bound `1 - sqrt 2 / 2` on the ordinary sphere.

## Building the formalization

Install [elan](https://github.com/leanprover/elan), Git, curl, and Python 3. From this directory:

```bash
lake exe cache get
lake build
```

The package pins Lean **4.33.0**, Mathlib commit
`db584cd6d46c92f209a44c0f1c829460d327499d`, and Comparator's Lean 4.33.0 release.
`lake-manifest.json` fixes the transitive dependency revisions.

## Reading the proof

[`LeanShadow.lean`](LeanShadow.lean) is the public entry point. Import `LeanShadow`
to load the main results. All 138 original modules are under [`LeanShadow/`](LeanShadow/);
only their local import paths were changed. Existing declarations retain the
`ShadowVerification` namespace. The public adapters in
[`LeanShadow/ComparatorSolution.lean`](LeanShadow/ComparatorSolution.lean) use
`LeanShadow.Comparator` and expose explicit area and angular-integral statements.

| Results | Main declarations in `LeanShadow.Comparator` |
| --- | --- |
| Spherical shadow | `sharp_shadow_inequality`, `sharp_shadow_equality`, `caps_attain` |
| Double cap | `double_cap_bound`, `double_cap_equality`, `double_cap_attainment` |
| Extremal value | `double_cap_conjecture`, `alpha_eq_delta`, `s2_double_cap_bound` |
| Projective shadow | `projective_shadow_inequality`, `projective_shadow_equality`, `projective_caps_attain` |

The shadow adapters quantify over `r` in `[0, pi/2]` and explicitly assume that the
input area equals the cap-area integral at `r`. This avoids hiding the integral
formula behind the implementation's inverse-radius function. The original
inverse-radius statements remain available in `SharpShadow` and `ProjectiveShadow`.

## Verification

```bash
python3 scripts/verify.py
```

This builds the proof library, rejects proof shortcuts, and requires a standard-axiom
report for every local theorem. Results are saved in `verification.json` and `build.log`.
The reference challenge is kept outside the default proof build and this audit.

For statement comparison and independent kernel checking, see
[`ComparatorChallenges/README.md`](ComparatorChallenges/README.md).
An optional bundled-kernel replay is also available:

```bash
python3 scripts/replay.py
# Resume an interrupted replay with unchanged verified sources:
python3 scripts/replay.py --resume
```

See [VERIFICATION.md](VERIFICATION.md) for checks actually performed.

## Repository format and provenance

The layout follows OpenAI's
[NavierStokesAndEuler release](https://github.com/openai/NavierStokesAndEuler/tree/f9e8bc5b38b6e212696e8a30e3e91517af887bbd):
a root Lean entry point, a proof-module directory, pinned Lake configuration,
[`formalization.yaml`](formalization.yaml), and a separate `ComparatorChallenges`
directory. The reference supplies the presentation format; it is not a mathematical
dependency or an attribution of this proof to OpenAI.

[`provenance.json`](provenance.json) records the source hashes before and after the
import-path reorganization.

## Authors and license

Authors: Allen Ibiapina, Carlos Gomes, Alan Pio, Samuel Belo, and Ernandes Ferreira.

The project uses AI-assisted tools.

LeanShadow's source code and documentation are licensed under the
[Apache License, Version 2.0](LICENSE) (`Apache-2.0`). Third-party dependencies
retain their own licenses and notices.
