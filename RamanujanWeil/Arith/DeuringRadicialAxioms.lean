import RamanujanWeil.Arith.DeuringRadicialDual

/-! Axiom audit for `RadicialDual` (`docs/ARITH_DEURING_RADICIAL.md`).
Expected: only `propext`, `Classical.choice`, `Quot.sound`. -/

open RamanujanWeil.Arith.Deuring.Radicial

#print axioms etaleAt_genericPoint_of_formallyUnramified
#print axioms exists_lift_point
#print axioms finrank_le_one_of_injective
#print axioms exists_pow_eq_functionFieldMap_zpow_char
#print axioms exists_pow_eq_functionFieldMap_zpow_pow
#print axioms isPurelyInseparable_of_injective
#print axioms exists_functionFieldMap_zpow_mem
#print axioms exists_comp_eq_zpow_of_injective
#print axioms radicialDual
#print axioms frobHomDual
