import RamanujanWeil.Arith.DeuringWModel

/-! Axiom audit for `docs/ARITH_DEURING_WMODEL.md`. Every declaration below must depend only on
`[propext, Classical.choice, Quot.sound]`. -/

open RamanujanWeil.Arith.Deuring.WModel

#print axioms pullbackPushforwardUnitIso
#print axioms finrank_cohomologyOverField_split
#print axioms chi_eq_mul
#print axioms one_sub_genus_eq_mul
#print axioms legsIsColimit
#print axioms leg_cover
#print axioms leg_disjoint
#print axioms exists_one_sub_genus_eq_mul
#print axioms exists_prime_isUnit
#print axioms exists_large_subgroup
#print axioms one_le_genus
#print axioms genus_eq_one
#print axioms finrank_structureSheafCohomology_zero
#print axioms weierstrassModel_of_isAlgClosed
#print axioms weierstrassModel
#print axioms weierstrassDescent
