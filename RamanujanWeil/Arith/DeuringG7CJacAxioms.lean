import RamanujanWeil.Arith.DeuringG7CJacBase

/-! # Axiom audit for step C-Jac (`docs/ARITH_DEURING_G7_CJAC.md`) -/

open RamanujanWeil.Arith.Deuring.Geom.G7.CJac

#print axioms curveBaseChangeMap_comp
#print axioms curvePicardMap_toPicardFunctor
#print axioms curvePicardMap_comp
#print axioms curvePicardMap_id
#print axioms twistedPicardMap_comp_curvePicardMap
#print axioms curvePicardMap_add
#print axioms picardHomEquiv_comp_curvePicardSchemeHom
#print axioms exists_curveJacobianHom
#print axioms degreeZeroHomAddEquiv_comp_curveJacobianHom
#print axioms isMonHom_curveJacobianHom
#print axioms curveJacobianHom_id
#print axioms curveJacobianHom_comp
#print axioms curveJacobianHom_comp_twistedJacobianHom
#print axioms isMonHom_curveJacobianPullback
#print axioms curveJacobianPullback_comp_jacobianFrobenius
#print axioms curveJacobianIso
#print axioms isMonHom_curveJacobianIso_hom
#print axioms curveJacobianIso_hom_comp_jacobianFrobenius
#print axioms exists_equivariant_jacobianIso
#print axioms exists_site_containing_family
#print axioms fieldBaseChangeIso
#print axioms fieldBaseChangeIso_hom_comp_galoisBaseChange
#print axioms exists_baseChange_iso
#print axioms IsEquivJacIso.trans
#print axioms exists_equivIso_of_jac
