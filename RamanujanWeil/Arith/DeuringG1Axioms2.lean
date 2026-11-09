import RamanujanWeil.Arith.DeuringG1Point

/-!
# Axiom audit for A3-ord G1.0 and G1.1 (`DeuringG1Jac`, `DeuringG1Abel`, `DeuringG1RR`,
`DeuringG1Point`)

Each declaration should depend only on `propext`, `Classical.choice`, `Quot.sound`.
-/

open RamanujanWeil.Arith.Deuring.Geom

-- G1.0: the concrete Jacobian
#print axioms charPoly_of_jacobianData
#print axioms Jac.nonempty_jacSite
#print axioms Jac.JacSite.twist_eq
#print axioms Jac.JacSite.dim_J
#print axioms Jac.JacSite.charPoly_π
#print axioms Jac.JacSite.frobeniusJacobian
#print axioms Jac.JacSite.frob_quadratic
#print axioms Jac.JacSite.endDegree_π
-- G1.1: Hilb¹ = X and the Abel–Jacobi isomorphism
#print axioms Abel.Hilb.representsSelf
#print axioms Abel.jacobianHomAddEquiv_comp_abelJacobi
#print axioms Abel.bijective_comp_abelJacobi
#print axioms Abel.isIso_abelJacobi
#print axioms Abel.finrank_fibreCohomology_one_eq_zero_of_large
#print axioms Abel.degreeOneNormalized
#print axioms Abel.isIso_abelJacobi_of_genus_eq_one
#print axioms Abel.jacobianHomAddEquiv_basePt_comp_abelJacobi
#print axioms Jac.JacSite.isIso_aj
#print axioms Jac.JacSite.ajIso
#print axioms Jac.JacSite.jacobianHomAddEquiv_zero_comp_aj
