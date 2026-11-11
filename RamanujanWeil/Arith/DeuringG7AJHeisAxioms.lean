import RamanujanWeil.Arith.DeuringG7HeisAll

/-!
# Axiom audit: G7 Abel–Jacobi + Heisenberg

`docs/ARITH_DEURING_G7_AJHEIS.md`. Every declaration below depends only on
`[propext, Classical.choice, Quot.sound]`.
-/

open RamanujanWeil.Arith.Deuring.Geom.G7.DGeom

-- evaluation and zeros
#print axioms hasVal_trans
#print axioms eval_eq_zero_of_eigen
#print axioms mul_conj_eq_norm
#print axioms evPt_conj
#print axioms exists_zero
#print axioms right_eq_zero_of_left_const
-- Heisenberg
#print axioms exists_big_closure
#print axioms exists_common_eigenvector
#print axioms eigenPts
#print axioms two_nsmul_injOn
#print axioms thetaHeisenberg_of_torsion
-- Abel–Jacobi
#print axioms secEquiv
#print axioms ajEquiv
#print axioms abelJacobiMathlib_of_bridge
-- assembly
#print axioms torsion_of_aj
#print axioms thetaHeisenbergAll_of_aj
#print axioms dGeomGapsAll_of_aj
#print axioms abelJacobiAll_of_bridge
#print axioms dGeomGapsAll_of_bridge
#print axioms deligneBound_of_bridge
