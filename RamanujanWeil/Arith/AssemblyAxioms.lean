import RamanujanWeil.Arith.AssemblyIhara

/-! Axiom audit for the R-ord assembly (docs/ARITH_ASSEMBLY.md). Expected output for every
declaration: `[propext, Classical.choice, Quot.sound]` (or a subset).

The `example`s restate the frozen text of `scratch/ArithInterfaces.lean` verbatim and close it
with the proved theorem, as a statement check. -/

open Finset

namespace RamanujanWeil.ArithPlan

open RamanujanWeil.Ihara

example (H : ℕ → ℚ) (p : ℕ) [Fact p.Prime] (h0 : HurwitzConventions H)
    (hES : EichlerSelbergPrimePow H p) (hHR : HurwitzPrimeSquare H p)
    (hT : TauHeckeRecurrence p) :
    ∃ C : ℝ, ∀ m : ℕ,
      |((ordSum H p m + 2 * (tauPowerSum p m : ℚ) : ℚ) : ℝ)| ≤
        C * ((m : ℝ) + 1) ^ 2 * Real.sqrt p ^ (11 * m) :=
  ordSum_error H p h0 hES hHR hT

example (H : ℕ → ℚ) (p : ℕ) [Fact p.Prime] (h0 : HurwitzConventions H)
    (hES : EichlerSelbergApprox H p) (hHR : HurwitzPrimeSquare H p)
    (hT : TauHeckeRecurrence p) :
    ∃ C : ℝ, ∃ k : ℕ, ∀ m : ℕ,
      |((ordSum H p m + 2 * (tauPowerSum p m : ℚ) : ℚ) : ℝ)| ≤
        C * ((m : ℝ) + 1) ^ k * Real.sqrt p ^ (11 * m) :=
  ordSum_error_of_approx H p h0 hES hHR hT

example (H : ℕ → ℚ) (p : ℕ) [Fact p.Prime] (h0 : HurwitzConventions H)
    (hD : OrdinaryDeuring H p) (hES : EichlerSelbergPrimePow H p)
    (hHR : HurwitzPrimeSquare H p) (hT : TauHeckeRecurrence p)
    (hss : SupersingularCountBound p) (hH : HasseAll p) : IharaApprox p :=
  iharaApprox_of_arith H p h0 hD hES hHR hT hss hH

end RamanujanWeil.ArithPlan

-- part 1: reindexing, Hurwitz relation, the ordinary-sum recursion
#print axioms RamanujanWeil.ArithPlan.sum_dvd_reindex
#print axioms RamanujanWeil.ArithPlan.hr_ord
#print axioms RamanujanWeil.ArithPlan.hr_dvd
#print axioms RamanujanWeil.ArithPlan.ordSum_rec
-- part 2: the error recursion and growth
#print axioms RamanujanWeil.ArithPlan.tauPowerSum_add_two
#print axioms RamanujanWeil.ArithPlan.errSum_rec
#print axioms RamanujanWeil.ArithPlan.growth_of_rec
#print axioms RamanujanWeil.ArithPlan.abs_hypTerm_le
#print axioms RamanujanWeil.ArithPlan.ordSum_error_core
#print axioms RamanujanWeil.ArithPlan.ordSum_error
#print axioms RamanujanWeil.ArithPlan.ordSum_error_of_approx
-- part 3: IharaApprox
#print axioms RamanujanWeil.ArithPlan.abs_symTrace_ten_le
#print axioms RamanujanWeil.ArithPlan.ordinary_part
#print axioms RamanujanWeil.ArithPlan.iharaApprox_of_ordError
#print axioms RamanujanWeil.ArithPlan.iharaApprox_of_arith
#print axioms RamanujanWeil.ArithPlan.iharaApprox_of_arith_approx
