import RamanujanWeil.Ihara.FinalDeuringTate
import RamanujanWeil.Arith.DeuringG7Dual

/-! Axiom audit for the concrete isogeny-class count (`docs/ARITH_DEURING_MULT.md`). -/

open RamanujanWeil.Arith.Deuring.Mult

#print axioms isogClassPred_smul_iff
#print axioms isogStep_of_trace
#print axioms isogClassCount_le_one
#print axioms mult_le_one
#print axioms locusMapP_bijective
#print axioms orbitMassP_eq_matMass
#print axioms card_pred_eq_mass
#print axioms card_class_eq
#print axioms card_ell_eq_sum
#print axioms card_ell_eq_mult
#print axioms traceCount_eq_card_ell
#print axioms deuringMultiplicity_of_classLattice
#print axioms frobHom_comp_ne_one
#print axioms frobHomNe_trans
#print axioms tate_frobHomNe_both
#print axioms RamanujanWeil.Ihara.deligneBound_of_DeuringMult_tate
#print axioms RamanujanWeil.Ihara.deligneBound_of_classLattice_tate
