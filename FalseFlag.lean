module

public import LeanDemo.FixedPoint

/-!
# Flagging statements that are false as written

Each section takes a plausible "client-style" statement, proves its negation with an
explicit counterexample (`theorem not_… : ¬ (…)`), and proves the corrected statement.
This is the check to run before trying to prove anything: a goal that is false as
stated cannot be closed, and the fix should go back to the author, not into the proof.
-/

@[expose] public section

namespace LeanDemo

open Fixed

/-! ## Flag 1: squared radii do not add

Statement as written: from `dist p c ^ 2 ≤ r ^ 2` and `dist q p ^ 2 ≤ s ^ 2`
conclude `dist q c ^ 2 ≤ r ^ 2 + s ^ 2`.

Counterexample on one axis: `c = 0`, `p = (1, 0, 0)`, `q = (2, 0, 0)`, `r = s = 1`.
Then `dist q c ^ 2 = 4` but `r ^ 2 + s ^ 2 = 2`. The cross term `2 * r * s` is missing.

Suggested fix: `dist q c ^ 2 ≤ (r + s) ^ 2` (this is `sq_dist_le_add_sq`), or, if the
right-hand side must stay a sum of squares, `dist q c ^ 2 ≤ 2 * (r ^ 2 + s ^ 2)`.
-/

theorem not_sq_dist_le_sq_add_sq :
    ¬ ∀ (p q c : P3) (r s : ℝ), 0 ≤ r → 0 ≤ s →
      dist p c ^ 2 ≤ r ^ 2 → dist q p ^ 2 ≤ s ^ 2 → dist q c ^ 2 ≤ r ^ 2 + s ^ 2 := by
  intro h
  have h4 := h !₂[1, 0, 0] !₂[2, 0, 0] 0 1 1 zero_le_one zero_le_one
    (by rw [dist_sq_eq]; norm_num) (by rw [dist_sq_eq]; norm_num)
  rw [dist_sq_eq] at h4
  norm_num at h4

/-- Corrected statement, keeping a sum of squares on the right. -/
theorem sq_dist_le_two_mul {p q c : P3} {r s : ℝ} (hr : 0 ≤ r) (hs : 0 ≤ s)
    (hp : dist p c ^ 2 ≤ r ^ 2) (hq : dist q p ^ 2 ≤ s ^ 2) :
    dist q c ^ 2 ≤ 2 * (r ^ 2 + s ^ 2) := by
  have h := sq_dist_le_add_sq hr hs hp hq
  nlinarith [sq_nonneg (r - s)]

/-! ## Flag 2: a missing sign hypothesis

Statement as written: `dist p q ≤ r ↔ dist p q ^ 2 ≤ r ^ 2` for every real `r`.

Counterexample: `p = q` and `r = -1`: `0 ≤ -1` is false but `0 ≤ (-1) ^ 2` is true.

Suggested fix: add `0 ≤ r` (this is `dist_le_iff_sq_le`).
-/

theorem not_dist_le_iff_sq_le :
    ¬ ∀ (p q : P3) (r : ℝ), dist p q ≤ r ↔ dist p q ^ 2 ≤ r ^ 2 := by
  intro h
  have h1 := (h 0 0 (-1)).2 (by norm_num)
  norm_num at h1

/-! ## Flag 3: quantization does not preserve strict order

Statement as written: `x < y → quantize 1000 x < quantize 1000 y`.

Counterexample: `x = 0` and `y = 1 / 10000`; both round to the integer `0`.
For fixed-point code this matters: a strict real comparison can become an equality
after quantization, so a `<` branch in the model may not match a `<` branch in the code.

Suggested fix: weaken to `≤` (`quantize_mono`), or require a gap of at least one
unit, `x + 1 / S ≤ y` (`quantize_lt_of_gap`).
-/

theorem not_quantize_strictMono :
    ¬ ∀ x y : ℝ, x < y → quantize 1000 x < quantize 1000 y := by
  intro h
  have h1 := h 0 (1 / 10000) (by norm_num)
  have h0 : quantize 1000 (1 / 10000) = 0 := by
    rw [quantize, round_eq_zero_iff]
    norm_num
  rw [h0] at h1
  simp [quantize] at h1

/-- Corrected statement 1: quantization is monotone. -/
theorem quantize_mono (S : ℕ) {x y : ℝ} (hxy : x ≤ y) : quantize S x ≤ quantize S y := by
  unfold quantize
  rw [round_eq, round_eq]
  apply Int.floor_mono
  have : x * S ≤ y * S := mul_le_mul_of_nonneg_right hxy (Nat.cast_nonneg S)
  linarith

/-- Corrected statement 2: a gap of one fixed-point unit survives quantization. -/
theorem quantize_lt_of_gap {S : ℕ} (hS : 0 < S) {x y : ℝ} (h : x + 1 / S ≤ y) :
    quantize S x < quantize S y := by
  have hS' : (0 : ℝ) < S := by exact_mod_cast hS
  have h1 : x * S + 1 ≤ y * S := by
    have := mul_le_mul_of_nonneg_right h hS'.le
    rwa [add_mul, one_div_mul_cancel hS'.ne'] at this
  have h2 : round (x * S + 1) ≤ round (y * S) := by
    rw [round_eq, round_eq]
    exact Int.floor_mono (by linarith)
  rw [round_add_one] at h2
  unfold quantize
  omega

end LeanDemo
