import RamanujanWeil.Arith.DeuringDescent

/-! Axiom audit for `docs/ARITH_DEURING_DESCENT.md`. Every declaration below must depend only on
`[propext, Classical.choice, Quot.sound]`. -/

open RamanujanWeil.Arith.Deuring.Descent

#print axioms eq_of_rigid
#print axioms isMonHom_of_pointed
#print axioms isMonHom_of_pointed'
#print axioms isMonHom_twHom
#print axioms exists_desc
#print axioms exists_desc_iso
#print axioms inv_mem_of_finite
#print axioms exists_map_frobQ_eq_mul
#print axioms exists_frobFixed_smul
#print axioms exists_map_eq_of_map_frobQ_eq
#print axioms substOf_mul
#print axioms changeMap_comp
#print axioms coordMap_comp
#print axioms frob_coordMap
#print axioms exists_descent
#print axioms exists_ΨB
#print axioms πB_ΨB
#print axioms exists_curve
#print axioms exists_jacIso
#print axioms trace_eq
#print axioms weierstrassDescent_of_model
