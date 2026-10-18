module

public import LeanDemo.Decision

/-!
# Fixed-point code against the real-number model

A fixed-point value is an integer `n` read as the real number `n / S` for a positive
scale `S` (for example `S = 1000`: millimetres in a model that works in metres).
We show that

* addition and finite sums commute with this reading,
* integer comparison matches real comparison,
* the integer threshold rule `bandInt` computes exactly the real rule `band`,
* rounding a real into fixed point loses at most `1 / (2 * S)`,
* fixed-point multiplication with floor division loses less than `1 / S`.
-/

@[expose] public section

namespace LeanDemo.Fixed

/-- The real number represented by the fixed-point integer `n` at scale `S`. -/
noncomputable def toReal (S : ℕ) (n : ℤ) : ℝ := (n : ℝ) / S

/-- Fixed-point addition is exact. -/
theorem toReal_add (S : ℕ) (m n : ℤ) : toReal S (m + n) = toReal S m + toReal S n := by
  simp [toReal, add_div]

/-- The real value of a fixed-point sum is the sum of the real values. -/
theorem toReal_sum {ι : Type*} (S : ℕ) (s : Finset ι) (f : ι → ℤ) :
    toReal S (∑ i ∈ s, f i) = ∑ i ∈ s, toReal S (f i) := by
  simp only [toReal]
  push_cast
  rw [Finset.sum_div]

/-- Integer comparison of fixed-point values matches the real comparison. -/
theorem toReal_le_toReal {S : ℕ} (hS : 0 < S) {m n : ℤ} :
    toReal S m ≤ toReal S n ↔ m ≤ n := by
  have hS' : (0 : ℝ) < S := by exact_mod_cast hS
  rw [toReal, toReal, div_le_div_iff_of_pos_right hS']
  exact Int.cast_le

/-- The threshold rule as fixed-point code would compute it (computable, on `ℤ`). -/
def bandInt (t₁ t₂ lo mid hi n : ℤ) : ℤ :=
  if n ≤ t₁ then lo else if n ≤ t₂ then mid else hi

/-- At scale `1000`: thresholds `0.5` and `2.0`, input `1.234` gives the middle level.
`bandInt` is computable, so the kernel checks this with plain `decide`. -/
theorem bandInt_example : bandInt 500 2000 0 1 2 1234 = 1 := by decide

/-- The integer rule computes exactly the real rule `band` on the scaled values. -/
theorem toReal_bandInt {S : ℕ} (hS : 0 < S) (t₁ t₂ lo mid hi n : ℤ) :
    toReal S (bandInt t₁ t₂ lo mid hi n) =
      band (toReal S t₁) (toReal S t₂) (toReal S lo) (toReal S mid) (toReal S hi)
        (toReal S n) := by
  unfold bandInt band
  simp only [toReal_le_toReal hS]
  split_ifs <;> rfl

/-- Round a real number to the nearest fixed-point value at scale `S`. -/
noncomputable def quantize (S : ℕ) (x : ℝ) : ℤ := round (x * S)

/-- Rounding error: a real and its fixed-point image differ by at most `1 / (2 * S)`. -/
theorem abs_sub_toReal_quantize_le {S : ℕ} (hS : 0 < S) (x : ℝ) :
    |x - toReal S (quantize S x)| ≤ 1 / (2 * S) := by
  have hS' : (0 : ℝ) < S := by exact_mod_cast hS
  have h := abs_sub_round (x * S)
  have e : x - toReal S (quantize S x) = (x * S - round (x * S)) / S := by
    unfold toReal quantize
    field_simp
  rw [e, abs_div, abs_of_pos hS', div_le_div_iff₀ hS' (by positivity)]
  nlinarith

/-- Fixed-point multiplication with the usual rescale `m * n / S` (floor division):
the result never exceeds the real product and is less than `1 / S` below it. -/
theorem toReal_mul_div_bounds {S : ℕ} (hS : 0 < S) (m n : ℤ) :
    toReal S (m * n / S) ≤ toReal S m * toReal S n ∧
      toReal S m * toReal S n < toReal S (m * n / S) + 1 / S := by
  have hS' : (0 : ℝ) < S := by exact_mod_cast hS
  have hSz : (0 : ℤ) < S := by exact_mod_cast hS
  have hdecomp : ((m * n : ℤ) : ℝ) = S * ((m * n / S : ℤ) : ℝ) + ((m * n % S : ℤ) : ℝ) := by
    exact_mod_cast (Int.mul_ediv_add_emod (m * n) S).symm
  have hr0 : (0 : ℝ) ≤ ((m * n % S : ℤ) : ℝ) := by exact_mod_cast Int.emod_nonneg _ hSz.ne'
  have hrS : ((m * n % S : ℤ) : ℝ) < S := by exact_mod_cast Int.emod_lt_of_pos _ hSz
  unfold toReal
  generalize ((m * n / S : ℤ) : ℝ) = q at hdecomp ⊢
  generalize ((m * n % S : ℤ) : ℝ) = r at hdecomp hr0 hrS
  push_cast at hdecomp
  rw [div_mul_div_comm, hdecomp]
  constructor
  · rw [div_le_div_iff₀ hS' (by positivity)]
    nlinarith [mul_nonneg hr0 hS'.le]
  · rw [← add_div, div_lt_div_iff₀ (by positivity) hS']
    nlinarith [mul_lt_mul_of_pos_right hrS hS']

end LeanDemo.Fixed
