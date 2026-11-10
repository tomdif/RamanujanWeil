import RamanujanWeil.Arith.DeuringG7Genus2Canon

/-!
# Axiom audit for the genus-2 model step after `DeuringG7Genus2Canon`
(`docs/ARITH_DEURING_G7_GENUS2.md` §6)

Every declaration below depends only on `[propext, Classical.choice, Quot.sound]`.
-/

open RamanujanWeil.Arith.Deuring.Geom.G7.Genus2.Exist

#print axioms dualizing_isInvertible_and_rank
#print axioms dualUnitTensorDualizingIso
#print axioms finrank_dualizing_zero
#print axioms invertibleCurveDegree_dualizing
#print axioms genus2CanonicalExistence
#print axioms genus2ModelExistence_of_canonical_of_pencil
#print axioms genus2ModelExistence_of_pencil
