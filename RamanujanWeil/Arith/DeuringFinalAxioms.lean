import RamanujanWeil.Arith.DeuringFinal

/-! Axiom audit for `docs/ARITH_DEURING_FINAL.md`. Every entry must report
`[propext, Classical.choice, Quot.sound]` (or a subset). -/

open RamanujanWeil.Arith.Deuring.Final

#print axioms exists_siteIso
#print axioms frobHomNe_transport
#print axioms homRel_equivalence
#print axioms homRel_of_isogStep
#print axioms frobHomNe_both_class
#print axioms exists_latticeMatrix_cls
#print axioms surjClass_of_descent_cls
#print axioms classLattice_cls
#print axioms nonempty_classLattice_uncond
#print axioms deuringClassLatticeAll_uncond
#print axioms deuringMultiplicity_uncond
#print axioms one_le_mult_of_exists
#print axioms deligneBound_of_multLeOne
#print axioms deligneBound_of_ordinaryTraceExistence
#print axioms multLeOneAll_of_tatePol
#print axioms deligneBound_of_tatePol'
