import RamanujanWeil.Arith.ESTtilde
import RamanujanWeil.Arith.ESTraceW

/-! Axiom audit for the A2 (Eichler–Selberg) files. Expected: `propext`, `Classical.choice`,
`Quot.sound` only (no `sorryAx`, no `Lean.ofReduceBool`). -/

#print axioms RamanujanWeil.Arith.ES.act_mul
#print axioms RamanujanWeil.Arith.ES.act_neg
#print axioms RamanujanWeil.Arith.ES.trace_act
#print axioms RamanujanWeil.Arith.ES.sup_eq_top
#print axioms RamanujanWeil.Arith.ES.eq_of_mem_Wper
#print axioms RamanujanWeil.Arith.ES.finrank_Wper
#print axioms RamanujanWeil.Arith.ES.trace_eq_trace_restrict_inf
#print axioms RamanujanWeil.Arith.ES.trace_actR_sum
#print axioms RamanujanWeil.Arith.ES.trace_Ttilde
#print axioms RamanujanWeil.Arith.ES.traceSum_small
#print axioms RamanujanWeil.Arith.ES.trace_eq_trace_Wper
