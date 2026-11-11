import RamanujanWeil.Arith.DeuringG7AmpleDescent

/-!
# Axiom audit for G7 ample descent (`docs/ARITH_DEURING_G7_AMPLE.md`)
-/

open RamanujanWeil.Arith.Deuring.Geom.G7.AmpleDescent

-- The Stacks input (0B5V, both directions)
#print axioms Stacks.AmpleFiniteSurjective.isAmple_of_isAmple_modulePullback
#print axioms Stacks.AmpleFiniteSurjective.isAmple_iff_isAmple_modulePullback

-- The G6 quotient (`DeuringG7AmpleDescent`)
#print axioms isFinite_glue_q
#print axioms isProper_glue_B
#print axioms isAmple_of_isAmple_pullback_glue
#print axioms isAmple_iff_isAmple_pullback_glue
#print axioms glueAmpleDescent

-- The seams and Deligne with ample descent discharged
#print axioms thetaLevelDescentGood_of_levelSectionDescent'
#print axioms thetaLevelDescentΨ_of_levelSectionDescentΨ'
#print axioms levelDescentSplitAll_of'
#print axioms deligneBound_of_levelDescent'
