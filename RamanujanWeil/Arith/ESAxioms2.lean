import RamanujanWeil.Arith.ESCosetsMain

/-! Axiom audit for the A2 (Eichler–Selberg) files, second batch (P4b, P5, P6, P7).
Expected: `propext`, `Classical.choice`, `Quot.sound` only. -/

-- P4b
#print axioms RamanujanWeil.Arith.ES.ptC_support
-- P6: Lemma 4 per trace, elliptic count, property (C)
#print axioms RamanujanWeil.Arith.ES.trSum_ptC
#print axioms RamanujanWeil.Arith.ES.six_regE
#print axioms RamanujanWeil.Arith.ES.trSum_regR
#print axioms RamanujanWeil.Arith.ES.trSum_regE
#print axioms RamanujanWeil.Arith.ES.trSum_regE_nonell
#print axioms RamanujanWeil.Arith.ES.traceSum_eq_trSum
#print axioms RamanujanWeil.Arith.ES.sum_trSum_regH
#print axioms RamanujanWeil.Arith.ES.traceSum_classNumber
-- P5: (16a), (16b), property (B), trace on W
#print axioms RamanujanWeil.Arith.ES.ptC_16a
#print axioms RamanujanWeil.Arith.ES.ptC_16b
#print axioms RamanujanWeil.Arith.ES.Ttilde_16a
#print axioms RamanujanWeil.Arith.ES.Ttilde_16b
#print axioms RamanujanWeil.Arith.ES.propBact_Ttilde
#print axioms RamanujanWeil.Arith.ES.trace_eq_trace_Wper'
#print axioms RamanujanWeil.Arith.ES.trace_Wper_Ttilde
-- P7: coset sums
#print axioms RamanujanWeil.Arith.ES.cS_ptC_16a
#print axioms RamanujanWeil.Arith.ES.cS_ptC_16b
#print axioms RamanujanWeil.Arith.ES.cS_ptC_U
#print axioms RamanujanWeil.Arith.ES.cS_ptC_S
#print axioms RamanujanWeil.Arith.ES.cS_ptC_T
#print axioms RamanujanWeil.Arith.ES.ptC_scale
#print axioms RamanujanWeil.Arith.ES.cS_ptC_K0
#print axioms RamanujanWeil.Arith.ES.cS_ptC_eq_neg_one
