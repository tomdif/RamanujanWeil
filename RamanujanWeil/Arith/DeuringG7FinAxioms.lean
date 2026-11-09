import RamanujanWeil.Arith.DeuringG7FinCore
import RamanujanWeil.Arith.DeuringG7FinProd

/-! Axiom audit for A3-ord G7-fin (`docs/ARITH_DEURING_G7FIN.md`). -/

open RamanujanWeil.Arith.Deuring.Geom.G7.Fin

#print axioms exists_odd_prime_no_root
#print axioms int_exists_sq_dvd
#print axioms isSquare_of_isUnit_of_isSquare_red
#print axioms disc_not_square
#print axioms exists_sq_sub_disc_mul_sq
#print axioms exists_normForm_eq
#print axioms mat_comp
#print axioms isUnit_det_mat
#print axioms exists_equivariant_addEquiv_det
#print axioms graphFiniteness_of_quotientFiniteness
#print axioms polGraphFiniteness_of_quotientFiniteness
#print axioms exists_frobHom_of_graphFiniteness
#print axioms tate_exists_frobHom_pol
#print axioms tateFinitenessPol_of_tateFiniteness
#print axioms isogStep_of_trace_pol
#print axioms isogClassCount_le_one_pol
#print axioms tateFinitenessPolAll_of_tateFinitenessAll
#print axioms mult_le_one_pol
#print axioms exists_common_factor_of_prodIso
#print axioms comp_iso_fst_equivariant
