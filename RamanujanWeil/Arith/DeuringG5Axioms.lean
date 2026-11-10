import RamanujanWeil.Arith.DeuringG5Cyclic

/-!
# Axiom audit for G5 (`docs/ARITH_DEURING_G5.md`)

Every declaration below should depend only on `[propext, Classical.choice, Quot.sound]`.
-/

open RamanujanWeil.Arith.Deuring.G5

-- algebra
#print axioms exists_intertwiner
#print axioms conj_of_isFrobFamily
#print axioms isFrobFamily_of_injective
#print axioms det_smul_mem_span_colVec
-- kernel lattices
#print axioms GlueS.sMap_q
#print axioms GlueS.sMap_π
#print axioms GlueS.dim_B
#print axioms GlueS.comp_sMap_mem
#print axioms GlueS.comp_sMap_injective
#print axioms GlueS.exists_comp_sMap_eq
#print axioms GlueS.comm_iff_comp_sMap
-- realization and surj_class
#print axioms kernelLattice_iff
#print axioms realize
#print axioms surjClass_of_descent
-- cyclic torsion
#print axioms exists_annTriv_prime
#print axioms ann_of_root
#print axioms annTriv_mul
#print axioms gen_of_ann
#print axioms cyclicTorsion_of_minimalOrder
#print axioms lin_eq_one_iff
#print axioms surjClass_of_descent_minimal
