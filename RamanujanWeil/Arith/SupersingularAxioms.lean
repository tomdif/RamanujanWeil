import RamanujanWeil.Arith.SupersingularBound

/-! Axiom audit for the supersingular count bound (docs/ARITH_SUPERSINGULAR.md). Expected output
for every declaration: `[propext, Classical.choice, Quot.sound]` (or a subset). -/

-- Hasse coefficient multiplicativity (Manin's digit lemma)
#print axioms RamanujanWeil.ArithPlan.hasseCoeff_succ
#print axioms RamanujanWeil.ArithPlan.hasseCoeff_eq_zero_iff
-- point count and the trace mod p
#print axioms RamanujanWeil.ArithPlan.natCard_point
#print axioms RamanujanWeil.ArithPlan.sum_eval_eq_neg_coeff
#print axioms RamanujanWeil.ArithPlan.traceOfFrob_cast_odd
#print axioms RamanujanWeil.ArithPlan.traceOfFrob_cast_two
-- the criterion
#print axioms RamanujanWeil.ArithPlan.dvd_traceOfFrob_iff_of_finite
#print axioms RamanujanWeil.ArithPlan.dvd_traceOfFrob_iff
-- Schwartz–Zippel and the bound
#print axioms RamanujanWeil.ArithPlan.totalDegree_hassePoly_le
#print axioms RamanujanWeil.ArithPlan.card_dvd_traceOfFrob_le
#print axioms RamanujanWeil.ArithPlan.supersingularCountBound
