import RamanujanWeil.Arith.HurwitzOrbit
import RamanujanWeil.Arith.TorsorCount

/-! Axiom audit for A1 (Hurwitz class numbers) and the A4 torsor count. Expected output for
every declaration: `[propext, Classical.choice, Quot.sound]` (or a subset). -/

-- A1: reduction theory
#print axioms RamanujanWeil.Arith.Hurwitz.exists_reduced
#print axioms RamanujanWeil.Arith.Hurwitz.entries_bound
#print axioms RamanujanWeil.Arith.Hurwitz.reduced_unique
#print axioms RamanujanWeil.Arith.Hurwitz.card_stabilizer_reduced
-- A1: headline
#print axioms RamanujanWeil.Arith.Hurwitz.hurwitz_eq_hurwitzOrbit
#print axioms RamanujanWeil.Arith.Hurwitz.hurwitz_eq_hurwitzClasses
#print axioms RamanujanWeil.Arith.Hurwitz.hurwitz_eq_zero_of_mod_four
#print axioms RamanujanWeil.Arith.Hurwitz.hurwitz_values
#print axioms RamanujanWeil.Arith.Hurwitz.kronecker_hurwitz_check
#print axioms RamanujanWeil.Arith.Hurwitz.khLHS12_eq
-- A4: torsor count
#print axioms RamanujanWeil.Arith.card_vc
#print axioms RamanujanWeil.Arith.card_point_smul
#print axioms RamanujanWeil.Arith.traceOfFrob_smul
#print axioms RamanujanWeil.Arith.card_isoClass_mul_card_stabilizer
#print axioms RamanujanWeil.Arith.finsum_eq_finsum_orbits
#print axioms RamanujanWeil.Arith.sum_trace_eq_sum_orbits
