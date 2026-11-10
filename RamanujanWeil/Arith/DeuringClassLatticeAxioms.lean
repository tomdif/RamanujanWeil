import RamanujanWeil.Arith.DeuringClassLattice

/-!
# Axiom audit: G8(ii) integral surjectivity and the `DeuringClassLattice` assembly

`docs/ARITH_DEURING_CLASSLATTICE.md`. Every declaration below should depend only on
`[propext, Classical.choice, Quot.sound]`.
-/

open RamanujanWeil.Arith.Deuring

-- G8(ii), abstract (`DeuringG8Int`, `DeuringG8IntIso`)
#print axioms G8Int.homPi_eq_of_smul_eq
#print axioms G8Int.exists_homPi_smul_eq
#print axioms G8Int.exists_postHom_eq
#print axioms G8Int.postHom_compPi
#print axioms G8Int.postHom_idPi
#print axioms G8Int.exists_ne_one_of_link
#print axioms G8Int.postHomSurj_of_link
#print axioms G8Int.nonempty_iso_iff
#print axioms G8Int.card_aut_eq

-- lattice isomorphisms ↔ conjugacy (`DeuringClassLatticeAlg`)
#print axioms ClassLattice.conj_of_linearEquiv
#print axioms ClassLattice.linearEquiv_of_conj
#print axioms ClassLattice.smul_eq_self_iff
#print axioms ClassLattice.stabEquiv

-- assembly (`DeuringClassLattice`)
#print axioms ClassLattice.nonempty_globalSite
#print axioms ClassLattice.exists_latticeMatrix_fam
#print axioms ClassLattice.postHomSurj_fam
#print axioms ClassLattice.rel_iff_fam
#print axioms ClassLattice.card_stab_fam
#print axioms ClassLattice.classLattice_fam
#print axioms ClassLattice.nonempty_equivIso_congr
#print axioms ClassLattice.mem_orbit_iff_global
#print axioms ClassLattice.card_stabilizer_global
#print axioms ClassLattice.frobHomNe_both_global
#print axioms ClassLattice.link_global
#print axioms ClassLattice.exists_latticeMatrix_global
#print axioms ClassLattice.surjClass_global
#print axioms ClassLattice.nonempty_classLattice_of_base
#print axioms ClassLattice.nonempty_classLattice
#print axioms ClassLattice.nonempty_classLattice_of_tate
#print axioms ClassLattice.deuringClassLatticeAll_of_props
#print axioms ClassLattice.deuringMultiplicity_of_props
