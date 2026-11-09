import RamanujanWeil.Arith.DeuringG8Frob

/-! Axiom audit for G7-dual (separable part) and G8(i)/(ii) (`docs/ARITH_DEURING_G8.md`). -/

open RamanujanWeil.Arith.Deuring.Dual2 RamanujanWeil.Arith.Deuring.G8

-- G7-dual: separable part, reduction to `RadicialDual`
#print axioms cancel_of_ne_one
#print axioms zpow_id_ne_one
#print axioms comm_of_comp_eq_zpow
#print axioms comp_eq_zpow_symm
#print axioms surjective_of_ne_one
#print axioms dim_eq_of_surjective
#print axioms exists_dual_of_radicialDual
#print axioms homDualHyp_of_radicialDual
#print axioms exists_frobDual
#print axioms frobHomDual_of_radicialDual
-- G8 algebra
#print axioms trace_det_of_sq_eq
#print axioms linearMap_trace_det_of_sq_eq
#print axioms finrank_eq_of_torsion
#print axioms finrank_le_two_of_torsion_quotient
#print axioms finrank_eq_two_of_torsion_quotient
#print axioms exists_mul_eq_of_sq
-- G8: `End_π(A) ⊗ ℚ = ℚ(π)`
#print axioms exists_int_trace
#print axioms postcompOf_sq
#print axioms exists_zpow_eq_of_comm
-- G8(i): `L(E)` free of rank two, Frobenius matrix in `TrDet t q`
#print axioms homPi_finite_free
#print axioms charPoly_data
#print axioms eq_zero_of_zpow_mul_zpow_eq_one
#print axioms finrank_homPi_eq_two
#print axioms exists_basis_trDet
#print axioms frobLattice_trDet
#print axioms frobLattice_trDet_of_tate
#print axioms exists_latticeMatrix
#print axioms exists_latticeMatrix_of_radicialDual
-- G8(ii): first steps
#print axioms finrank_endPi_eq_two
#print axioms postHom_piAct
#print axioms postHomAdd_injective
#print axioms exists_smul_eq_of_dual
#print axioms exists_postHom_eq_smul
