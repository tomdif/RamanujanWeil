import RamanujanWeil.Arith.DeuringMatrix
import RamanujanWeil.Arith.DeuringAssembly

/-! Axiom audit for the Deuring (A3-ord) files. Expected output for every declaration:
`[propext, Classical.choice, Quot.sound]` (or a subset). -/

-- D-ALG: matrix mass = Hurwitz mass / 2 (Latimer–MacDuffee, weighted)
#print axioms RamanujanWeil.Arith.Deuring.det_eq_one_of_conj
#print axioms RamanujanWeil.Arith.Deuring.psi_smul
#print axioms RamanujanWeil.Arith.Deuring.classMap_bijective
#print axioms RamanujanWeil.Arith.Deuring.card_stabilizer_psi
#print axioms RamanujanWeil.Arith.Deuring.matMass_eq_hurwitzOrbit
#print axioms RamanujanWeil.Arith.Deuring.matMass_eq_hurwitz
-- D-ASM: OrdinaryDeuring from the lattice functor (+ Hasse)
#print axioms RamanujanWeil.Arith.Deuring.locusMap_bijective
#print axioms RamanujanWeil.Arith.Deuring.orbitMass_eq_matMass
#print axioms RamanujanWeil.Arith.Deuring.card_trace_eq_mass
#print axioms RamanujanWeil.Arith.Deuring.ordinaryDeuring_of_lattice
