import RamanujanWeil.Arith.ESMain

/-! Axiom audit for the A2 (Eichler–Selberg) files, third batch (P8, P9, algebraic P13).
Expected: `propext`, `Classical.choice`, `Quot.sound` only. -/

-- P8: orbit sums, regrouping, property (A)
#print axioms RamanujanWeil.Arith.ES.fibre_sum_eq_oS
#print axioms RamanujanWeil.Arith.ES.sum_smul_eq_zero_of_oS
#print axioms RamanujanWeil.Arith.ES.aO_S
#print axioms RamanujanWeil.Arith.ES.aO_U
#print axioms RamanujanWeil.Arith.ES.aO_cd
#print axioms RamanujanWeil.Arith.ES.aO_c0
#print axioms RamanujanWeil.Arith.ES.aO_d0
#print axioms RamanujanWeil.Arith.ES.propA_orbit
#print axioms RamanujanWeil.Arith.ES.propA_action
-- P9: Eisenstein line, trace in coordinates
#print axioms RamanujanWeil.Arith.ES.actR_Ttilde_e0
#print axioms RamanujanWeil.Arith.ES.traceSum_eq_coords
-- analytic interface and its algebraic consequences
#print axioms RamanujanWeil.Arith.ES.tauEigenPeriod_of_input
#print axioms RamanujanWeil.Arith.ES.W_decomp
#print axioms RamanujanWeil.Arith.ES.TauEigenPeriod.diag
#print axioms RamanujanWeil.Arith.ES.traceSum_eq_sig_tau
-- P13 (algebraic part)
#print axioms RamanujanWeil.Arith.ES.par_sum
#print axioms RamanujanWeil.Arith.ES.esSum_general
#print axioms RamanujanWeil.Arith.ES.hypTerm_eq
#print axioms RamanujanWeil.Arith.ES.eichlerSelbergPrimePow_of_tauEigenPeriod
#print axioms RamanujanWeil.Arith.ES.eichlerSelbergPrimePow_of_input
#print axioms RamanujanWeil.Arith.ES.eichlerSelberg_all_of_input
