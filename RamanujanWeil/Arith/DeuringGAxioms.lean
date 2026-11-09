import RamanujanWeil.Arith.DeuringG2
import RamanujanWeil.Arith.DeuringG3Sat

/-! Axiom audit for the geometric steps G2–G4 of A3-ord (`docs/ARITH_DEURING_PROGRESS.md`).
Expected: only `propext`, `Classical.choice`, `Quot.sound`. -/

open RamanujanWeil.Arith.Deuring.Geom

-- G3 (dimension one): injectivity into Tate modules, Cayley–Hamilton
#print axioms eq_one_of_infinite_pointKer
#print axioms eq_one_of_tateModuleMap_eq_zero
#print axioms tateModuleMap_injective
#print axioms eq_one_of_zpow_eq_one
#print axioms tateModuleMap_endPolyEval
#print axioms endPolyEval_eq_one_of_endCharPoly_eq
-- G3 (divisibility by `n` invertible)
#print axioms exists_isMonHom_zpow_comp_eq
#print axioms comp_eq_one_of_tateModuleMap_dvd
#print axioms exists_eq_comp_of_tateModuleMap_dvd
-- G4 (endomorphisms, dimension one)
#print axioms endCharPoly_eq_of_dim_one
#print axioms endDegree_zpow_mul_zpow
#print axioms trace_sq_le_four_mul_endDegree
#print axioms endDegree_eq_zero_iff
-- G2
#print axioms exists_jacobian_charPoly_twisted
#print axioms natCard_fixedClosedPoints_weierstrass
#print axioms nonempty_frobeniusJacobian
#print axioms FrobeniusJacobian.frob_quadratic
#print axioms FrobeniusJacobian.endDegree_π
