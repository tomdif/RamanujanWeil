import RamanujanWeil.Arith.ESAnalytic

/-! Axiom audit for the A2 analytic files (P10–P12, `ESAnalytic*.lean`).
Expected: `propext`, `Classical.choice`, `Quot.sound` only. -/

-- τ: explicit bound and the full Hecke relation
#print axioms RamanujanWeil.Arith.ES.Analytic.tau_abs_mul_pow_le
#print axioms RamanujanWeil.Arith.ES.Analytic.hecke_comp
#print axioms RamanujanWeil.Arith.ES.Analytic.tau_hecke
-- P10: the Eichler integral, termwise derivatives, `D¹¹F̃ = (2πi)¹¹Δ`
#print axioms RamanujanWeil.Arith.ES.Analytic.hasDerivAt_G
#print axioms RamanujanWeil.Arith.ES.Analytic.iteratedDeriv_Fc
#print axioms RamanujanWeil.Arith.ES.Analytic.G_cj11
#print axioms RamanujanWeil.Arith.ES.Analytic.Dc_S
#print axioms RamanujanWeil.Arith.ES.Analytic.Fc_conj
-- P11: Bol, polynomiality
#print axioms RamanujanWeil.Arith.ES.Analytic.bol
#print axioms RamanujanWeil.Arith.ES.Analytic.poly_of_iteratedDeriv_eq_zero
#print axioms RamanujanWeil.Arith.ES.Analytic.rhoc_poly
-- P10: the model (slash action, ι, F̃|T, Hecke), parity
#print axioms RamanujanWeil.Arith.ES.Analytic.isSlash_sl
#print axioms RamanujanWeil.Arith.ES.Analytic.ιH_inj
#print axioms RamanujanWeil.Arith.ES.Analytic.ιH_equiv
#print axioms RamanujanWeil.Arith.ES.Analytic.Fh_T
#print axioms RamanujanWeil.Arith.ES.Analytic.ιH_rho
#print axioms RamanujanWeil.Arith.ES.Analytic.rho_conj
#print axioms RamanujanWeil.Arith.ES.Analytic.sum_heckeSet
#print axioms RamanujanWeil.Arith.ES.Analytic.coeff_hecke
#print axioms RamanujanWeil.Arith.ES.Analytic.Fh_hecke
-- P12: certified numerics
#print axioms RamanujanWeil.Arith.ES.Analytic.fr_bound
#print axioms RamanujanWeil.Arith.ES.Analytic.u_bounds
#print axioms RamanujanWeil.Arith.ES.Analytic.R_eq
#print axioms RamanujanWeil.Arith.ES.Analytic.rho_bounds
-- assembly
#print axioms RamanujanWeil.Arith.ES.Analytic.eichlerPeriodInput
#print axioms RamanujanWeil.Arith.ES.Analytic.eichlerSelberg_all
