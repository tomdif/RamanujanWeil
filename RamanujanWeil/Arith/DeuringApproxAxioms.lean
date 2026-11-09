import RamanujanWeil.Ihara.FinalDeuringApprox

/-! Axiom audit for the approximate-Deuring route (docs/ARITH_DEURING_APPROX.md).
Expected for every entry: `[propext, Classical.choice, Quot.sound]`. -/

-- Kronecker–Hurwitz from the Popa–Zagier core (`DeuringApproxKH.lean`)
#print axioms RamanujanWeil.Arith.ES.cosetCof_spec
#print axioms RamanujanWeil.Arith.ES.cosetKey_rep_mul
#print axioms RamanujanWeil.Arith.ES.sum_box_ptC
#print axioms RamanujanWeil.Arith.ES.kroneckerHurwitz
#print axioms RamanujanWeil.ArithPlan.ordSum0_rec
#print axioms RamanujanWeil.ArithPlan.esSum0_hurwitz
#print axioms RamanujanWeil.ArithPlan.ordSum0_bound

-- ordinary tuple count (`DeuringApproxCount.lean`)
#print axioms RamanujanWeil.ArithPlan.deltaPoly_ne_zero
#print axioms RamanujanWeil.ArithPlan.card_singular_le
#print axioms RamanujanWeil.ArithPlan.card_ordinary_lower

-- approximate assembly (`DeuringApprox.lean`)
#print axioms RamanujanWeil.ArithPlan.ordinaryDeuringApprox_of_exact
#print axioms RamanujanWeil.ArithPlan.ordinary_part_traces
#print axioms RamanujanWeil.ArithPlan.iharaApprox_of_deuringApprox_ordError
#print axioms RamanujanWeil.ArithPlan.iharaApprox_of_deuringApprox

-- structural interface (`DeuringApproxMult.lean`)
#print axioms RamanujanWeil.ArithPlan.kroneckerHurwitzLower_hurwitz
#print axioms RamanujanWeil.ArithPlan.kroneckerHurwitzUpper_hurwitz
#print axioms RamanujanWeil.ArithPlan.sum_traceCount_ord
#print axioms RamanujanWeil.ArithPlan.ordinaryDeuringApprox_of_mult_exists
#print axioms RamanujanWeil.ArithPlan.ordinaryDeuringApprox_of_mult_unique
#print axioms RamanujanWeil.ArithPlan.ordinaryDeuringApprox_of_mult_exists_hurwitz
#print axioms RamanujanWeil.ArithPlan.ordinaryDeuringApprox_of_mult_unique_hurwitz

-- headlines (`Ihara/FinalDeuringApprox.lean`)
#print axioms RamanujanWeil.Ihara.iharaApprox_of_DeuringApprox
#print axioms RamanujanWeil.Ihara.deligneBound_of_DeuringApprox
#print axioms RamanujanWeil.Ihara.deligneBound_of_DeuringMult_unique
#print axioms RamanujanWeil.Ihara.deligneBound_of_DeuringMult_exists
#print axioms RamanujanWeil.Ihara.deligneBound_of_Deuring'
