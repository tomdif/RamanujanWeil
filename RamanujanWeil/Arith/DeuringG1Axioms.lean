import RamanujanWeil.Arith.DeuringG1Coord

/-!
# Axiom audit for A3-ord G1.3 (`DeuringG1Coord.lean`)

Each declaration should depend only on `propext`, `Classical.choice`, `Quot.sound`.
-/

open RamanujanWeil.Arith.Deuring.Geom.Coord

#print axioms familyIsoEquiv
#print axioms frobOf_comp_coordMap
#print axioms frobOf_comm_iff
#print axioms frobOf_comm_iff_familyIsoEquiv
#print axioms galoisBaseChange_comp_geomIso
#print axioms twist_comm_iff_coord
#print axioms geomIsoEquiv
#print axioms mem_orbit_iff_nonempty_frobIso
#print axioms card_stabilizer_eq_card_frobAut
