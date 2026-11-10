import RamanujanWeil.Arith.DeuringG7DGapsAll

/-!
# Axiom audit for G7-D-gaps (`docs/ARITH_DEURING_G7DGAPS.md`)
-/

open RamanujanWeil.Arith.Deuring.Geom.G7.DGeom

-- The valuation at `O` and `L(N·O)` (`DeuringG7DGapsVal`)
#print axioms vR
#print axioms vK
#print axioms exists_const_of_vR_le_one
#print axioms rrSpace_eq_LN

-- The conjugation and the degree of `m_Q^N` (`DeuringG7DGapsConj`)
#print axioms conj
#print axioms norm_conj
#print axioms map_conj_XYIdeal
#print axioms vR_of_pow_eq_span
#print axioms pow_eq_span_of_le

-- Translations (`DeuringG7DGapsTransl`)
#print axioms transX_neg
#print axioms transY_neg
#print axioms lam_mem
#print axioms trans_rr_mem
#print axioms vK_transX_le_one
#print axioms vK_transY_le_one
#print axioms vK_trans_rr_le_one

-- The divisor bridge (`DeuringG7DGapsBridge`)
#print axioms exists_rr_exact
#print axioms rrStabilizerBridge

-- Assembly (`DeuringG7DGapsAll`)
#print axioms dGeomGaps_of
#print axioms dGeomGapsAll_of
#print axioms deligneBound_of_gaps
