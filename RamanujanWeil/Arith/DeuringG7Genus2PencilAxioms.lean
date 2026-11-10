import RamanujanWeil.Arith.DeuringG7Genus2Pencil

/-!
# Axiom audit for the canonical pencil and the genus-2 model step
(`docs/ARITH_DEURING_G7_GENUS2.md` §7)

Every declaration below depends only on `[propext, Classical.choice, Quot.sound]`.
-/

open RamanujanWeil.Arith.Deuring.Geom.G7.Genus2

-- the algebra of a base-point-free pencil (`DeuringG7Genus2PencilAlg`)
#print axioms Pencil.GradedPencil.le_sup_map
#print axioms Pencil.GradedPencil.isIntegralElem
#print axioms Pencil.GradedPencil.transcendental
#print axioms Pencil.GradedPencil.two_le
#print axioms Pencil.GradedPencil.finrank_adjoin_le
#print axioms Pencil.GradedPencil.toIntegralPencilData
-- two charts of an invertible module (`DeuringG7Genus2PencilChart`)
#print axioms Pencil.Chart.Data.theta_injective
#print axioms Pencil.Chart.Data.mem_range_theta_iff
-- the graded pencil on the curve (`DeuringG7Genus2PencilGeom`)
#print axioms Pencil.ratio_powSec
#print axioms Pencil.Setup.rho_data
#print axioms Pencil.Setup.gradedPencil
#print axioms Pencil.Setup.finrank_V
#print axioms Pencil.Setup.isAffineOpen_U
#print axioms Pencil.Setup.exists_div
-- assembly (`DeuringG7Genus2Pencil`)
#print axioms Pencil.finrank_tensorPower_eq_of_deg
#print axioms Pencil.two_le_finrank_H0
#print axioms Pencil.genus2PencilFunctionField
#print axioms Pencil.genus2ModelExistence
