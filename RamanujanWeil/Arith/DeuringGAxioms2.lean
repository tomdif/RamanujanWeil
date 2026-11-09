import RamanujanWeil.Arith.DeuringG4Hom
import RamanujanWeil.Arith.DeuringG1Descent

/-! Axiom audit for the second geometric session of A3-ord (`docs/ARITH_DEURING_PROGRESS2.md`).
Expected: only `propext`, `Classical.choice`, `Quot.sound`. -/

open RamanujanWeil.Arith.Deuring.Geom

-- G3 lattice algebra (Mathlib only)
#print axioms Lattice.finite_free_saturation
#print axioms Lattice.linearIndependent_of_saturated
#print axioms Lattice.finite_free_of_anisotropic_of_saturated
#print axioms Lattice.finrank_le_of_anisotropic_of_saturated
#print axioms Lattice.liftBaseChange_injective_of_anisotropic_of_saturated
-- G3 completion: `Hom(A,B)` is a lattice of rank ≤ 4, `Hom ⊗ ℤ_ℓ ↪ Hom(T_ℓ)`
#print axioms degPolar_mul_left
#print axioms degPolar_self
#print axioms endForm_anisotropic
#print axioms comp_ne_one
#print axioms postcomp_injective
#print axioms homAV_saturated
#print axioms exists_anisotropic_form
#print axioms finrank_tateHom_target
#print axioms homAV_finite_free
#print axioms homAV_tensor_injective
#print axioms endAV_finite_free
#print axioms endAV_tensor_injective
-- G4 on `Hom(A,B)`
#print axioms homDegree_eq_endDegree
#print axioms isDominant_of_ne_one
#print axioms homDegree_pos_of_isDominant
#print axioms homDegree_eq_zero_iff
#print axioms homDegree_comp
#print axioms homDegree_zpow
#print axioms endDegree_comp_eq
#print axioms homPolar_mul_left
#print axioms homPolar_self
#print axioms homDegree_parallelogram
-- G1 (coordinate-level Galois descent)
#print axioms Descent.mem_range_of_pow_card_eq
#print axioms Descent.exists_map_eq_of_frobFixed
#print axioms Descent.mem_orbit_iff_exists_frobFixed
#print axioms Descent.stabilizerEquivFrobFixed
#print axioms Descent.card_stabilizer_eq_frobFixed
