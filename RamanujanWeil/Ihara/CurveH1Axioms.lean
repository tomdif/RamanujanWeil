import RamanujanWeil.Ihara.CurveH1Weierstrass

/-! Axiom audit for M4a (`docs/IHARA_CURVE_H1.md`). Expected for every entry:
`[propext, Classical.choice, Quot.sound]`. -/

-- linear-algebra core (Mathlib only)
#print axioms RamanujanWeil.Ihara.charpoly_eq_of_pure_of_traces
#print axioms RamanujanWeil.Ihara.trace_pow_eq_frobPowerSum_of_pure
#print axioms RamanujanWeil.Ihara.pointCount_eq_sub_frobPowerSum
#print axioms RamanujanWeil.Ihara.sq_le_four_mul_of_pure
#print axioms RamanujanWeil.Ihara.frobPowerSum_eq_add_pow
#print axioms RamanujanWeil.Ihara.natCard_point_extension_dvd
#print axioms RamanujanWeil.Ihara.natCard_point_extension_one
-- geometric layer (Weil/Stacks)
#print axioms RamanujanWeil.Ihara.rationalFrobenius_zero_eq_id
#print axioms RamanujanWeil.Ihara.finrank_rationalCohomology_zero
#print axioms RamanujanWeil.Ihara.charpoly_rationalFrobenius_two
#print axioms RamanujanWeil.Ihara.connectedSpace_of_connectedSpace_pullback
#print axioms RamanujanWeil.Ihara.pointSum_constantSystem
#print axioms RamanujanWeil.Ihara.curvePointCount_eq_alternating
#print axioms RamanujanWeil.Ihara.norm_sq_eq_card_of_isRoot
#print axioms RamanujanWeil.Ihara.trace_rationalFrobenius_one_pow
#print axioms RamanujanWeil.Ihara.charpoly_rationalFrobenius_one
#print axioms RamanujanWeil.Ihara.trace_rationalFrobenius_one_pow_eq_frobPowerSum
#print axioms RamanujanWeil.Ihara.curvePointCount_eq_sub_frobPowerSum
#print axioms RamanujanWeil.Ihara.sq_le_four_mul_card
#print axioms RamanujanWeil.Ihara.charpoly_rationalFrobenius_one_of_weierstrass
#print axioms RamanujanWeil.Ihara.natCard_point_extension_eq_of_weierstrass
#print axioms RamanujanWeil.Ihara.sq_le_four_mul_card_of_weierstrass
-- the plane cubic
#print axioms RamanujanWeil.Ihara.contains_projOf
#print axioms RamanujanWeil.Ihara.charpoly_weierstrassH1
