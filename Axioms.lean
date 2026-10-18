import LeanDemo

/-! Axiom audit: every main theorem should depend only on
`propext`, `Classical.choice` and `Quot.sound` (no `sorryAx`, no custom axioms).
Run with `lake env lean Axioms.lean`. -/

-- RealIneq
#print axioms LeanDemo.abs_add_sub_le
#print axioms LeanDemo.weighted_avg_le
#print axioms LeanDemo.cauchy_schwarz_three
#print axioms LeanDemo.div_add_le_half
#print axioms LeanDemo.scaled_energy_le
#print axioms LeanDemo.falloff_pos

-- Distance3D
#print axioms LeanDemo.dist_le_iff_sq_le
#print axioms LeanDemo.sq_dist_le_add_sq
#print axioms LeanDemo.dist_sq_eq_sum
#print axioms LeanDemo.dist_sq_eq
#print axioms LeanDemo.dist_sq_le_of_abs_coord_le
#print axioms LeanDemo.abs_coord_le_of_dist_sq_le
#print axioms LeanDemo.dist_example_le

-- Decision
#print axioms LeanDemo.band_mem
#print axioms LeanDemo.band_monotone
#print axioms LeanDemo.band_eq_steps
#print axioms LeanDemo.speedFactor_mem
#print axioms LeanDemo.speedFactor_monotone
#print axioms LeanDemo.speedFactor_eq_flat
#print axioms LeanDemo.speedFactor_eq_zero_of_dist_le

-- FixedPoint
#print axioms LeanDemo.Fixed.toReal_add
#print axioms LeanDemo.Fixed.toReal_sum
#print axioms LeanDemo.Fixed.toReal_le_toReal
#print axioms LeanDemo.Fixed.bandInt_example
#print axioms LeanDemo.Fixed.toReal_bandInt
#print axioms LeanDemo.Fixed.abs_sub_toReal_quantize_le
#print axioms LeanDemo.Fixed.toReal_mul_div_bounds

-- FalseFlag
#print axioms LeanDemo.not_sq_dist_le_sq_add_sq
#print axioms LeanDemo.sq_dist_le_two_mul
#print axioms LeanDemo.not_dist_le_iff_sq_le
#print axioms LeanDemo.not_quantize_strictMono
#print axioms LeanDemo.quantize_mono
#print axioms LeanDemo.quantize_lt_of_gap
