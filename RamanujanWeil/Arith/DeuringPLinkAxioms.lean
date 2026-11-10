import RamanujanWeil.Arith.DeuringPLink
import RamanujanWeil.Ihara.FinalDeuringTatePol

/-!
# Axiom audit: `PrimeToPLink`

`docs/ARITH_DEURING_PLINK.md`. Every declaration below should depend only on
`[propext, Classical.choice, Quot.sound]`.
-/

open RamanujanWeil.Arith.Deuring

-- function fields (`DeuringPLinkField`)
#print axioms PLink.pow_finrank_mem
#print axioms PLink.surj_of_injective
#print axioms PLink.exists_comp_eq_of_mem
#print axioms PLink.homDegree_eq_finrank
#print axioms PLink.exists_pow_mem_of_injective
#print axioms PLink.exists_dual_exact
#print axioms PLink.exists_functionFieldMap_eq_pow

-- the radicial case (`DeuringPLinkRC`)
#print axioms PLink.trSeq_dvd
#print axioms PLink.ring_identities
#print axioms PLink.postcompOf_cpow
#print axioms PLink.homDegree_cpow
#print axioms PLink.functionFieldMap_cpow_eq_pow
#print axioms PLink.link_of_injective

-- the purely inseparable root and transport (`DeuringPLinkPhi`)
#print axioms PLink.endPolyEval_vOf
#print axioms PLink.good_of_hom
#print axioms PLink.card_torsion_le
#print axioms PLink.exists_phi

-- assembly (`DeuringPLink`)
#print axioms PLink.link_trans
#print axioms PLink.link_symm
#print axioms PLink.link_of_injective_good
#print axioms PLink.link_of_ne_one
#print axioms PLink.good_frobeniusJacobian
#print axioms PLink.primeToPLink
#print axioms PLink.primeToPLinkAll

-- headline (`Ihara/FinalDeuringTatePol`)
#print axioms RamanujanWeil.Ihara.deligneBound_of_tatePol
