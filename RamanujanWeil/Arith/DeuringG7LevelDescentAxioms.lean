import RamanujanWeil.Arith.DeuringG7LevelDescent

/-!
# Axiom audit for G7 level descent (`docs/ARITH_DEURING_G7_LEVELDESCENT.md`)
-/

open RamanujanWeil.Arith.Deuring.Geom.G7.LevelDescent

-- The abstract dimension count (`DeuringG7LevelDescentRep`)
#print axioms sum_char_eq_zero
#print axioms isoProj_mul_isoProj
#print axioms sum_isoProj
#print axioms g_mul_isoProj
#print axioms range_isoProj_zero
#print axioms nonempty_linearEquiv_pi
#print axioms finrank_eq_card_mul_finrank_invariants

-- The level representation (`DeuringG7LevelDescentRep`)
#print axioms levelRep
#print axioms leftUnit_mul_levelRep
#print axioms finrank_levelRep_invariants

-- The theta group on `L(N·O)` (`DeuringG7LevelDescentRep`)
#print axioms thetaRep
#print axioms thetaRep_scalar
#print axioms linearIndependent_rrFam
#print axioms finrank_rrSpace
#print axioms thetaLevelRep
#print axioms finrank_thetaLevelRep_invariants_eq_one

-- The constructed families and the seams (`DeuringG7LevelDescent`)
#print axioms isScalarKernel_thetaFamilyOf
#print axioms card_tor_J
#print axioms finrank_famInv_eq_one
#print axioms thetaLevelDescentGood_of_thetaLevelDescent
#print axioms thetaLevelDescentGood_of_levelSectionDescent
#print axioms thetaDescentFiniteness_of_split'
#print axioms deligneBound_of_levelDescent
#print axioms principallyPolarized_of_Ψ
#print axioms thetaLevelDescentΨ_of_levelSectionDescentΨ
#print axioms thetaDescentFiniteness_of_splitΨ
