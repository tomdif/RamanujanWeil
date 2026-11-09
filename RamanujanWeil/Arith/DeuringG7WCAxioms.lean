import RamanujanWeil.Arith.DeuringG7WeilAlg
import RamanujanWeil.Arith.DeuringG7WeilHeis
import RamanujanWeil.Arith.DeuringG7WeilCore
import RamanujanWeil.Arith.DeuringG7Genus2Model

/-! Axiom audit for A3-ord G7-W and G7-C (`docs/ARITH_DEURING_G7_WC.md`). -/

open RamanujanWeil.Arith.Deuring.Geom.G7.Fin.Weil RamanujanWeil.Arith.Deuring.Geom.G7.Genus2

-- W, algebra
#print axioms IsAlt.swap
#print axioms IsAlt.eq_sCoord_mul_cdet
#print axioms IsAlt.isUnit_sCoord
#print axioms IsAlt.apply_apply_eq
#print axioms antiIsom_iff_det
#print axioms IsAlt.map_map_eq_det
#print axioms det_mat_eq_q
#print axioms IsAlt.map_map_eq_q
#print axioms graph_isotropic_iff
#print axioms eq_of_forall_graph_orth
#print axioms detPairing_isNondeg
#print axioms exists_alt_of_det
-- W, commutator pairing of a central extension
#print axioms CentralExt.commVal_congr
#print axioms CentralExt.commVal_mul_left
#print axioms CentralExt.pairing
#print axioms CentralExt.pairing_self
#print axioms CentralExt.pairing_nondeg
#print axioms CentralExt.zmodPairing_isAlt
#print axioms CentralExt.zmodPairing_isNondeg
#print axioms exists_injective_torsion_units_zmod
-- W, interface
#print axioms AltPairing.ofCentralExt
#print axioms sCoord_ofCentralExt
#print axioms torsionLog_injective
#print axioms AltPairing.ofTheta
#print axioms isUnit_lagDet
#print axioms detClass_eq_antiIsom
#print axioms polGraphFiniteness_of_lag
#print axioms exists_lag_of_polGraphFiniteness
#print axioms torAct_rel
#print axioms AltPairing.map_torAct
#print axioms tateFinitenessPol_of_lag
#print axioms tateFinitenessLag_of_pol
#print axioms tateFinitenessPolAll_of_lagAll
#print axioms mult_le_one_lag
-- C
#print axioms HypModel.sum_coeff_eq
#print axioms HypModel.exists_hypModel_eq
#print axioms finite_hypModel
#print axioms exists_iso_of_hypModel
#print axioms exists_ne_iso_of_hasHypModel
#print axioms isRegular_of_smooth_field
#print axioms exists_ne_iso_of_genus_eq_two
