import RamanujanWeil.Arith.DeuringG1Assembly

/-!
# Axiom audit for G1 session 3 (G1.1′, η-pointedness, G1.2, G1.4)

`docs/ARITH_DEURING_G1_3.md`. Every result below depends only on
`[propext, Classical.choice, Quot.sound]`.
-/

open RamanujanWeil.Arith.Deuring.Geom

-- G1.1′ (Frobenius compatibility), general and for `W`
#print axioms Frob.pointIdeal_comap_of_comm
#print axioms Frob.abelJacobi_comp_jacobianFrobenius
#print axioms Jac.zeroPt_comp_twist
#print axioms Jac.geomFrob_comp_twist
#print axioms Jac.twist_comm_iff_geomFrob_comm
#print axioms Jac.JacSite.aj_comp_π
#print axioms Jac.JacSite.π_eq

-- `aj(O) = 0` in `η` form
#print axioms Abel.basePtO_comp_abelJacobi
#print axioms Jac.JacSite.zeroO_comp_aj

-- G1.2 (rigidity in dimension one)
#print axioms Rigid.transportMap_add
#print axioms Rigid.transportMap_univ
#print axioms Rigid.transportMap_constClass
#print axioms Rigid.jacobianHomAddEquiv_comp_transport
#print axioms Rigid.isMonHom_transport_site
#print axioms Rigid.isMonHom_transport

-- G1.4 (assembly)
#print axioms conj_comm_iff_of_comm
#print axioms Jac.nonempty_pairSite
#print axioms Jac.PairSite.frobIsoEquiv
#print axioms Jac.PairSite.isMonHom_jacHom
#print axioms Jac.PairSite.jacHom_comm
#print axioms Jac.PairSite.mem_orbit_iff_nonempty_jacIso
#print axioms Jac.JacSite.card_stabilizer_eq_card_jacAut
