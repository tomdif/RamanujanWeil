import RamanujanWeil

/-! Combined public audit. Each section mirrors its focused audit so all five
groups can be checked with one load of the full dependency graph. -/

-- RamanujanWeil/Axioms.lean
section PublicAudit0

/-! Axiom audit of every headline (expected: `[propext, Classical.choice, Quot.sound]`). -/

#print axioms RamanujanTau.tau_two
#print axioms RamanujanTau.tau_three
#print axioms RamanujanTau.tau_five
#print axioms RamanujanWeil.isRoot_map_charpoly_of_isRoot_map_charpoly_restrict
#print axioms RamanujanWeil.norm_map_trace_restrict_le
#print axioms RamanujanWeil.nonempty_padic_ringHom_complex
#print axioms RamanujanWeil.norm_map_trace_le_of_stable
#print axioms RamanujanWeil.int_sq_le_of_stable
#print axioms RamanujanWeil.tau_sq_le_of_realization
#print axioms RamanujanWeil.deligneBound_of_realization
#print axioms RamanujanWeil.deligneBound_of_realization'
#print axioms RamanujanWeil.deligneBound_instance_of_realization
#print axioms Weil.satisfiesWeilEstimate

end PublicAudit0

-- RamanujanWeil/Arith/DeuringG7AJHeisAxioms.lean
section PublicAudit1

/-!
# Axiom audit: G7 Abel–Jacobi + Heisenberg

`docs/ARITH_DEURING_G7_AJHEIS.md`. Every declaration below depends only on
`[propext, Classical.choice, Quot.sound]`.
-/

open RamanujanWeil.Arith.Deuring.Geom.G7.DGeom

-- evaluation and zeros
#print axioms hasVal_trans
#print axioms eval_eq_zero_of_eigen
#print axioms mul_conj_eq_norm
#print axioms evPt_conj
#print axioms exists_zero
#print axioms right_eq_zero_of_left_const
-- Heisenberg
#print axioms exists_big_closure
#print axioms exists_common_eigenvector
#print axioms eigenPts
#print axioms two_nsmul_injOn
#print axioms thetaHeisenberg_of_torsion
-- Abel–Jacobi
#print axioms secEquiv
#print axioms ajEquiv
#print axioms abelJacobiMathlib_of_bridge
-- assembly
#print axioms torsion_of_aj
#print axioms thetaHeisenbergAll_of_aj
#print axioms dGeomGapsAll_of_aj
#print axioms abelJacobiAll_of_bridge
#print axioms dGeomGapsAll_of_bridge
#print axioms deligneBound_of_bridge

end PublicAudit1

-- RamanujanWeil/Arith/DeuringG7AmpleDescentAxioms.lean
section PublicAudit2

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

end PublicAudit2

-- RamanujanWeil/Arith/DeuringG7ThetaJAxioms.lean
section PublicAudit3

/-! Audit of `docs/ARITH_DEURING_G7_THETAJ.md`: every declaration below should depend only on
`[propext, Classical.choice, Quot.sound]`. -/

open RamanujanWeil.Arith.Deuring.Geom.G7.ThetaJ

#print axioms isTwist_J
#print axioms isTwist_tensor
#print axioms exists_isTwist_glue
#print axioms exists_twist
#print axioms exists_curve'
#print axioms exists_jacIso'
#print axioms comm_π_of_frobDefined
#print axioms isTwist_factor
#print axioms exists_factor_model
#print axioms prodJacModel_of_prodIso
#print axioms frobDefined_of_central
#print axioms thetaJacobianModel_of_gaps

end PublicAudit3

-- RamanujanWeil/Arith/DeuringG7G2Desc2CanonAxioms.lean
section PublicAudit4

/-! Audit of the genus-2 presentation-rigidity reduction. -/

open RamanujanWeil.Arith.Deuring.Geom.G7.Genus2Descent.Desc2

#print axioms frobQ_surjective
#print axioms pres_frob
#print axioms e₂_frob_eq_top
#print axioms frobFF_bijective
#print axioms genus2FrobCanonical_of_presRigid
#print axioms genus2FrobDescent_of_presRigid_of_fixed

end PublicAudit4
