import RamanujanWeil.Arith.DeuringG7DFinal

/-! Axiom audit for `docs/ARITH_DEURING_G7D.md`. Every entry must report
`[propext, Classical.choice, Quot.sound]` (or a subset). -/

open RamanujanWeil.Arith.Deuring.Geom.G7.Fin.Weil

#print axioms CentralExt.graphQuot_mul_comm
#print axioms CentralExt.ιQ_injective
#print axioms CentralExt.exists_graphLevel
#print axioms CentralExt.eq_of_forall_pairing_graph
#print axioms CentralExt.centralizer_graphLevel
#print axioms divisibleBy_units
#print axioms exists_primitiveRoots
#print axioms ThetaFamily.sCoord_pairing
#print axioms antiIsom_iff_pairing
#print axioms mem_antiIsom_iff_det
#print axioms graphLevel_of_antiIsom
#print axioms centralizer_of_antiIsom
#print axioms tateFinitenessLag_of_thetaDescent
#print axioms tateFinitenessLagAll_of_thetaDescent
#print axioms multLeOneAll_of_thetaDescent
#print axioms deligneBound_of_thetaDescent
