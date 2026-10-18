module

public import LeanDemo.Distance3D

/-!
# Threshold rules and a small decision tree over `ℝ`

Order on `ℝ` is decidable only classically (`Real.decidableLE` is noncomputable),
so rules that branch on real comparisons are `noncomputable def`s. For a three-band
threshold rule and a two-input decision tree we prove that

* the outputs lie in a finite set,
* the rule is monotone under stated assumptions,
* two formulations of the same rule agree (`split_ifs` case analysis),
* a squared-distance check on points of `ℝ³` triggers the stop branch.
-/

@[expose] public section

namespace LeanDemo

/-- Three-band threshold rule: `lo` up to `t₁`, `mid` up to `t₂`, `hi` above. -/
noncomputable def band (t₁ t₂ lo mid hi x : ℝ) : ℝ :=
  if x ≤ t₁ then lo else if x ≤ t₂ then mid else hi

/-- The rule only ever returns one of its three levels. -/
theorem band_mem (t₁ t₂ lo mid hi x : ℝ) :
    band t₁ t₂ lo mid hi x ∈ ({lo, mid, hi} : Finset ℝ) := by
  unfold band
  split_ifs <;> simp

/-- With ordered levels `lo ≤ mid ≤ hi` the rule is monotone in its input.
Without them it is not: take `t₁ < t₂` and `mid < lo`. -/
theorem band_monotone {t₁ t₂ lo mid hi : ℝ} (h₁ : lo ≤ mid) (h₂ : mid ≤ hi) :
    Monotone (band t₁ t₂ lo mid hi) := by
  intro x y hxy
  unfold band
  split_ifs <;> linarith

/-- Second formulation: base level plus two step functions. The two agree when
`t₁ ≤ t₂`; for `t₂ < x ≤ t₁` they differ, so the hypothesis cannot be dropped. -/
theorem band_eq_steps {t₁ t₂ lo mid hi : ℝ} (ht : t₁ ≤ t₂) (x : ℝ) :
    band t₁ t₂ lo mid hi x =
      lo + (if t₁ < x then mid - lo else 0) + (if t₂ < x then hi - mid else 0) := by
  unfold band
  split_ifs <;> linarith

/-- Thresholds of a speed rule: stop radius, slow radius and safe speed. -/
structure Limits where
  /-- Stop if the obstacle is closer than this. -/
  rStop : ℝ
  /-- Slow down (when fast) if the obstacle is closer than this. -/
  rSlow : ℝ
  /-- Speeds up to this value are always allowed outside the stop zone. -/
  vSafe : ℝ

/-- A two-input decision tree. `d2` is the squared distance to the nearest obstacle
and `v` the current speed; the result is a speed factor. -/
noncomputable def speedFactor (L : Limits) (d2 v : ℝ) : ℝ :=
  if d2 ≤ L.rStop ^ 2 then 0
  else if v ≤ L.vSafe then 1
  else if d2 ≤ L.rSlow ^ 2 then 1 / 2
  else 1

/-- The same rule written with one compound condition instead of a nested tree. -/
noncomputable def speedFactorFlat (L : Limits) (d2 v : ℝ) : ℝ :=
  if d2 ≤ L.rStop ^ 2 then 0
  else if v ≤ L.vSafe ∨ L.rSlow ^ 2 < d2 then 1
  else 1 / 2

/-- The speed factor is one of `0`, `1 / 2`, `1`. -/
theorem speedFactor_mem (L : Limits) (d2 v : ℝ) :
    speedFactor L d2 v ∈ ({0, 1 / 2, 1} : Finset ℝ) := by
  unfold speedFactor
  split_ifs <;> simp

/-- For a fixed speed, moving away from the obstacle never lowers the speed factor. -/
theorem speedFactor_monotone (L : Limits) (v : ℝ) :
    Monotone (fun d2 => speedFactor L d2 v) := by
  intro x y hxy
  simp only [speedFactor]
  split_ifs <;> linarith

/-- The nested tree and the flat formulation agree everywhere. -/
theorem speedFactor_eq_flat (L : Limits) (d2 v : ℝ) :
    speedFactor L d2 v = speedFactorFlat L d2 v := by
  unfold speedFactor speedFactorFlat
  by_cases hA : d2 ≤ L.rStop ^ 2
  · simp [hA]
  by_cases hB : v ≤ L.vSafe
  · simp [hA, hB]
  by_cases hC : d2 ≤ L.rSlow ^ 2
  · simp [hA, hB, hC, not_lt.2 hC]
  · simp [hA, hB, hC, lt_of_not_ge hC]

/-- Safety link to `ℝ³`: if a point is within the stop radius of an obstacle,
the rule fed with the squared distance returns `0`. -/
theorem speedFactor_eq_zero_of_dist_le (L : Limits) (hL : 0 ≤ L.rStop) {p o : P3} (v : ℝ)
    (h : dist p o ≤ L.rStop) : speedFactor L (dist p o ^ 2) v = 0 := by
  simp [speedFactor, (dist_le_iff_sq_le hL).1 h]

end LeanDemo
