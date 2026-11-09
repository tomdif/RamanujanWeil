import RamanujanWeil.Arith.DeuringG6ConstRank
import RamanujanWeil.Arith.DeuringG6Sub

/-! Axiom audit for G6 (quotients of abelian varieties by finite subgroups,
`docs/ARITH_DEURING_G6.md`). Expected: only `propext`, `Classical.choice`, `Quot.sound`. -/

open RamanujanWeil.Arith.Deuring.Geom.G6

-- general core (any base, commutative group scheme, finite locally free subgroup)
#print axioms isFreeAction_of_isTranslation
#print axioms nonempty_translationQuotient
#print axioms exists_desc_of_fqs
#print axioms TranslationQuotient.comp_q_eq_iff
#print axioms TranslationQuotient.exists_desc
#print axioms TranslationQuotient.grpObj
#print axioms TranslationQuotient.isMonHom_q
#print axioms TranslationQuotient.isCommMonObj
#print axioms TranslationQuotient.comp_q_eq_one_iff'
#print axioms TranslationQuotient.exists_isMonHom_desc
#print axioms TranslationQuotient.desc_unique
-- abelian variety, degree
#print axioms TranslationQuotient.isAbelianVariety
#print axioms TranslationQuotient.isFiniteLocallyFreeOfRank_q
#print axioms TranslationQuotient.degreeOver_q
-- étale (constant) case
#print axioms eq_of_toUnit_comp_eq
#print axioms translateHom
#print axioms smul_mul_right
#print axioms isTranslation_constJ
#print axioms isMonHom_constJ
#print axioms mono_constJ
#print axioms exists_eq_constantGroupSchemePoint
#print axioms isFiniteLocallyFreeOfRank_constantGroupScheme
#print axioms exists_quotient_by_finite_subgroup
#print axioms exists_quotient_by_finite_subgroup'
-- general subgroup scheme (p-part)
#print axioms isTranslation_translationModObj
#print axioms exists_quotient_by_subgroupScheme
