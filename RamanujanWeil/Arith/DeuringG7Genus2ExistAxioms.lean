import RamanujanWeil.Arith.DeuringG7Genus2Exist

/-!
# Axiom audit for `DeuringG7Genus2Exist*` (`docs/ARITH_DEURING_G7_GENUS2.md`)

Every declaration below depends only on `[propext, Classical.choice, Quot.sound]`.
-/

open RamanujanWeil.Arith.Deuring.Geom.G7.Genus2.Exist

#print axioms linearIndependent_pow_pow_mul
#print axioms exists_relation
#print axioms exists_not_mem_adjoin
#print axioms irreducible_quadEqn
#print axioms nonempty_algEquiv_adjoinRoot
#print axioms PencilData.exists_model
#print axioms transcendental_inv
#print axioms exists_aeval_eq_of_isIntegralElem
#print axioms mem_cubicSpan_of_isIntegralElem
#print axioms IntegralPencilData.toPencilData
#print axioms finrank_sub_finrank_eq
#print axioms finrank_tensorPower_eq
#print axioms hasHypModel_of_pencilData
#print axioms genus2ModelExistence_of_pencilExistence
#print axioms genus2PencilExistence_of_canonical_of_pencil
#print axioms genus2ModelExistence_of_canonical_of_pencil
