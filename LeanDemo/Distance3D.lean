module

public import Mathlib

/-!
# Squared-distance bounds in `ℝ³`

Points live in `EuclideanSpace ℝ (Fin 3)`, Mathlib's `ℝ³` with the Euclidean metric.
Range and collision checks are usually written with squared distances (no square root),
so the lemmas below move between `dist ≤ r` and `dist ^ 2 ≤ r ^ 2`, expand `dist ^ 2`
into coordinates, and compare a ball check with an axis-aligned box check.
-/

@[expose] public section

namespace LeanDemo

/-- Points of `ℝ³` with the Euclidean metric. -/
abbrev P3 := EuclideanSpace ℝ (Fin 3)

/-- For a nonnegative radius, a distance bound and a squared-distance bound agree.
The hypothesis `0 ≤ r` is needed: see `not_dist_le_iff_sq_le` in `FalseFlag`. -/
theorem dist_le_iff_sq_le {p q : P3} {r : ℝ} (hr : 0 ≤ r) :
    dist p q ≤ r ↔ dist p q ^ 2 ≤ r ^ 2 :=
  (sq_le_sq₀ dist_nonneg hr).symm

/-- Containment with squared radii: if `p` is within `r` of `c` and `q` is within `s`
of `p`, then `q` is within `r + s` of `c`. -/
theorem sq_dist_le_add_sq {p q c : P3} {r s : ℝ} (hr : 0 ≤ r) (hs : 0 ≤ s)
    (hp : dist p c ^ 2 ≤ r ^ 2) (hq : dist q p ^ 2 ≤ s ^ 2) :
    dist q c ^ 2 ≤ (r + s) ^ 2 := by
  have hp' := (dist_le_iff_sq_le hr).2 hp
  have hq' := (dist_le_iff_sq_le hs).2 hq
  apply (dist_le_iff_sq_le (add_nonneg hr hs)).1
  linarith [dist_triangle q p c]

/-- Squared distance as a sum of squared coordinate differences. -/
theorem dist_sq_eq_sum (p q : P3) : dist p q ^ 2 = ∑ i, (p i - q i) ^ 2 := by
  rw [EuclideanSpace.dist_eq, Real.sq_sqrt (by positivity)]
  simp only [Real.dist_eq, sq_abs]

/-- Squared distance in `ℝ³`, written out coordinate by coordinate. -/
theorem dist_sq_eq (p q : P3) :
    dist p q ^ 2 = (p 0 - q 0) ^ 2 + (p 1 - q 1) ^ 2 + (p 2 - q 2) ^ 2 := by
  rw [dist_sq_eq_sum, Fin.sum_univ_three]

/-- Box check implies ball check: if every coordinate differs by at most `h`,
then the squared distance is at most `3 * h ^ 2`. -/
theorem dist_sq_le_of_abs_coord_le {p q : P3} {h : ℝ} (hc : ∀ i, |p i - q i| ≤ h) :
    dist p q ^ 2 ≤ 3 * h ^ 2 := by
  have key : ∀ i, (p i - q i) ^ 2 ≤ h ^ 2 := fun i => by
    have hi := hc i
    have h0 : 0 ≤ |p i - q i| := abs_nonneg _
    calc (p i - q i) ^ 2 = |p i - q i| ^ 2 := (sq_abs _).symm
      _ ≤ h ^ 2 := by gcongr
  rw [dist_sq_eq]
  linarith [key 0, key 1, key 2]

/-- Ball check implies box check: inside the ball of radius `r ≥ 0` around `c`,
every coordinate is within `r` of the centre. -/
theorem abs_coord_le_of_dist_sq_le {p c : P3} {r : ℝ} (hr : 0 ≤ r)
    (h : dist p c ^ 2 ≤ r ^ 2) (i : Fin 3) : |p i - c i| ≤ r := by
  have hi : (p i - c i) ^ 2 ≤ dist p c ^ 2 := by
    rw [dist_sq_eq_sum]
    exact Finset.single_le_sum (f := fun j => (p j - c j) ^ 2)
      (fun j _ => sq_nonneg _) (Finset.mem_univ i)
  have hsq : (p i - c i) ^ 2 ≤ r ^ 2 := hi.trans h
  rw [abs_le]
  constructor <;> nlinarith

/-- A concrete check through the coordinate formula: `(1, 2, 2)` is within `3` of the
origin (its squared distance is `1 + 4 + 4 = 9`). -/
theorem dist_example_le : dist (!₂[1, 2, 2] : P3) 0 ≤ 3 := by
  rw [dist_le_iff_sq_le (by norm_num), dist_sq_eq]
  norm_num

end LeanDemo
