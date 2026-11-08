import RamanujanWeil.Arith.HurwitzPrimeSquare

/-! Axiom audit for A1′ (Hurwitz conventions and the prime-square relation). Expected output for
every declaration: `[propext, Classical.choice, Quot.sound]` (or a subset). -/

open RamanujanWeil.Arith.Hurwitz in
example : RamanujanWeil.ArithPlan.HurwitzConventions hurwitz := hurwitzConventions

open RamanujanWeil.Arith.Hurwitz in
example : ∀ p : ℕ, p.Prime → RamanujanWeil.ArithPlan.HurwitzPrimeSquare hurwitz p :=
  hurwitzPrimeSquare

-- headline
#print axioms RamanujanWeil.Arith.Hurwitz.hurwitzConventions
#print axioms RamanujanWeil.Arith.Hurwitz.hurwitzPrimeSquare
-- mass identity and its pieces
#print axioms RamanujanWeil.Arith.Hurwitz.hm_prime_square
#print axioms RamanujanWeil.Arith.Hurwitz.mass_Y2
#print axioms RamanujanWeil.Arith.Hurwitz.mass_rr
#print axioms RamanujanWeil.Arith.Hurwitz.mass_rr'
-- generic mass lemmas
#print axioms RamanujanWeil.Arith.Hurwitz.wmass_fiber
#print axioms RamanujanWeil.Arith.Hurwitz.wmass_induced
#print axioms RamanujanWeil.Arith.Hurwitz.wmass_equivariant
-- local counts
#print axioms RamanujanWeil.Arith.Hurwitz.card_P1
#print axioms RamanujanWeil.Arith.Hurwitz.card_cond_eq_one
#print axioms RamanujanWeil.Arith.Hurwitz.card_cond'_prim
#print axioms RamanujanWeil.Arith.Hurwitz.card_cond'_of_dvd
