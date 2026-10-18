module

public import Mathlib

/-!
# Inequalities over `ℝ`

Small bounds of the kind that appear when a numerical model is formalised:
tolerance stacking, a weighted average, Cauchy–Schwarz in three variables,
a ratio bound under positivity side conditions, a monotone energy bound and an
inverse-square falloff. Each proof has one main tactic: `linarith`, `nlinarith`
(with explicit product or square hints), `positivity` or `gcongr`.
-/

@[expose] public section

namespace LeanDemo

/-- Tolerance stacking: if `x` is within `ε` of `a` and `y` is within `δ` of `b`,
then `x + y` is within `ε + δ` of `a + b`. -/
theorem abs_add_sub_le {x y a b ε δ : ℝ} (hx : |x - a| ≤ ε) (hy : |y - b| ≤ δ) :
    |(x + y) - (a + b)| ≤ ε + δ := by
  rw [abs_le] at hx hy ⊢
  constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]

/-- A convex combination of two values bounded by `M` is bounded by `M`.
The products make this nonlinear, so `nlinarith` gets them as hints. -/
theorem weighted_avg_le {w a b M : ℝ} (hw0 : 0 ≤ w) (hw1 : w ≤ 1) (ha : a ≤ M) (hb : b ≤ M) :
    w * a + (1 - w) * b ≤ M := by
  nlinarith [mul_nonneg hw0 (sub_nonneg.2 ha), mul_nonneg (sub_nonneg.2 hw1) (sub_nonneg.2 hb)]

/-- Cauchy–Schwarz in three variables. The gap is Lagrange's sum of three squares,
which is exactly the hint list for `nlinarith`. -/
theorem cauchy_schwarz_three (a b c x y z : ℝ) :
    (a * x + b * y + c * z) ^ 2 ≤ (a ^ 2 + b ^ 2 + c ^ 2) * (x ^ 2 + y ^ 2 + z ^ 2) := by
  nlinarith [sq_nonneg (a * y - b * x), sq_nonneg (a * z - c * x), sq_nonneg (b * z - c * y)]

/-- Ratio bound with a division: if `0 ≤ a ≤ b` and `0 < b`, then `a / (a + b) ≤ 1 / 2`.
`positivity` supplies the positive denominator needed to clear the division. -/
theorem div_add_le_half {a b : ℝ} (ha : 0 ≤ a) (hb : 0 < b) (hab : a ≤ b) :
    a / (a + b) ≤ 1 / 2 := by
  have hpos : 0 < a + b := by positivity
  rw [div_le_iff₀ hpos]
  linarith

/-- Monotone product bound: growing a nonnegative mass and speed grows `m * v ^ 2`,
and dividing by `1 + t ≥ 1` can only shrink it. `gcongr` does the monotonicity step. -/
theorem scaled_energy_le {m M v V t : ℝ} (hm : 0 ≤ m) (hmM : m ≤ M) (hv : 0 ≤ v) (hvV : v ≤ V)
    (ht : 0 ≤ t) : m * v ^ 2 / (1 + t) ≤ M * V ^ 2 := by
  have hM : 0 ≤ M := hm.trans hmM
  have hmono : m * v ^ 2 ≤ M * V ^ 2 := by gcongr
  have hshrink : m * v ^ 2 / (1 + t) ≤ m * v ^ 2 :=
    div_le_self (by positivity) (by linarith)
  exact hshrink.trans hmono

/-- An inverse-square falloff with a softening term is strictly positive. -/
theorem falloff_pos {k ε : ℝ} (hk : 0 < k) (hε : 0 < ε) (x y z : ℝ) :
    0 < k / (x ^ 2 + y ^ 2 + z ^ 2 + ε) := by
  positivity

end LeanDemo
