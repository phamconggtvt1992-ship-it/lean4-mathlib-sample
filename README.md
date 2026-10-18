# lean_demo: real inequalities, 3D distance bounds, decision rules, fixed point

A small Lean 4 + Mathlib sample. It covers the kind of statements that come up when a
numerical model is formalised: inequalities over `ℝ`, squared-distance bounds in `ℝ³`,
threshold rules / decision trees over `ℝ`, a fixed-point implementation proved
against the real-number model, and statements that are false as written.

- 33 theorems; `lake build` finishes with 0 errors and 0 warnings.
- No `sorry`, `admit`, `native_decide` or new `axiom`.
- `#print axioms` on every theorem shows only `propext`, `Classical.choice`,
  `Quot.sound` (see `AXIOMS.txt`).

## Files

| File | What it shows |
|---|---|
| `LeanDemo/RealIneq.lean` | 6 inequalities over `ℝ`: tolerance stacking (`abs_le` + `linarith`), weighted average and 3-variable Cauchy–Schwarz (`nlinarith` with product / `sq_nonneg` hints), `a / (a + b) ≤ 1/2` (division cleared under `positivity`), a monotone energy bound (`gcongr`), positivity of an inverse-square falloff. |
| `LeanDemo/Distance3D.lean` | Points in `EuclideanSpace ℝ (Fin 3)`. `dist p q ≤ r ↔ dist p q ^ 2 ≤ r ^ 2` for `0 ≤ r`; containment `dist q c ^ 2 ≤ (r + s) ^ 2`; `dist ^ 2` as a sum of coordinate squares; box check ⇒ ball check (`≤ 3 h²`) and ball check ⇒ box check; the concrete point `(1, 2, 2)` lies within `3` of the origin. |
| `LeanDemo/Decision.lean` | `noncomputable` rules with nested `if-then-else` on real comparisons (classical decidability). A three-band rule: outputs in a `Finset`, monotone when the levels are ordered, equal to a "base + steps" formula when `t₁ ≤ t₂` (`split_ifs`). A two-input speed decision tree: outputs in `{0, 1/2, 1}`, monotone in distance, equal to a flat formulation, and a stop guarantee from a 3D distance bound. |
| `LeanDemo/FixedPoint.lean` | Integers read as `n / S`. Sums and comparisons commute with the reading; the computable integer rule `bandInt` equals the real rule `band` on scaled inputs (plus a kernel `decide` check at `S = 1000`); rounding error `|x - round(x S)/S| ≤ 1/(2S)`; fixed-point multiplication with floor division is low by less than `1/S`. |
| `LeanDemo/FalseFlag.lean` | Three false "client-style" statements, each refuted with a counterexample (`theorem not_… : ¬ …`), a comment explaining the problem, and the corrected statement proved: squared radii do not add (missing `2rs`), a missing `0 ≤ r`, and quantization not preserving `<`. |
| `Axioms.lean` | `#print axioms` for every theorem; output in `AXIOMS.txt`. |

## Build

Requires [elan](https://github.com/leanprover/elan). Toolchain and Mathlib are pinned:

- Lean `v4.36.0-rc1` (`lean-toolchain`)
- Mathlib tag `v4.36.0-rc1`, commit `625d8914199bc567cca9b91f90e8e5afafa5ae51` (`lake-manifest.json`)

```sh
lake exe cache get        # download prebuilt Mathlib
lake build                # expect "Build completed successfully"
lake env lean Axioms.lean # axiom audit
grep -rnE '\bsorry\b|\badmit\b|native_decide|^\s*axiom\b' LeanDemo LeanDemo.lean  # expect no output
```

`BUILD_LOG.txt` is the output of a clean build of the `LeanDemo` modules (Windows 11).
The GitHub workflow in `.github/workflows/lean_action_ci.yml` runs the same three checks.

## How it was made

Written with AI assistance (Claude Code) and machine-checked: every proof is accepted
by `lake build` on the pinned versions above, and the axiom audit is in `AXIOMS.txt`.
