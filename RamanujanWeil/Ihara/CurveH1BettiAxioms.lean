import RamanujanWeil.Ihara.CurveH1Betti

/-! Axiom audit for gaps 1 and 3 of M4a (`CurveH1BettiConnected`, `CurveH1Betti`). -/

open RamanujanWeil.Ihara

#print axioms finrank_structureSheafCohomology_baseChange
#print axioms connectedSpace_baseChange_of_finrank_zero
#print axioms isCurve_baseChange_of_finrank_zero
#print axioms genus_pullback_snd
#print axioms connectedSpace_projOf_baseChange
#print axioms connectedSpace_weierstrass_geometric
#print axioms genus_projOf_baseChange
#print axioms isCurve_projOf_baseChange
#print axioms isUnit_natCast_of_ne_ringChar
#print axioms finrank_rationalCohomology_one_eq_two_mul_genus
#print axioms hasFirstBettiTwo_of_genus_eq_one
#print axioms hasFirstBettiTwo_weierstrass
#print axioms charpoly_weierstrassH1'
#print axioms natCard_point_extension_eq_weierstrassH1'
#print axioms sq_le_four_mul_card_weierstrassH1'
