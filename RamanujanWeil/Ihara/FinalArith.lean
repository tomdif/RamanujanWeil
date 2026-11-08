import RamanujanWeil.Ihara.HasseAll
import RamanujanWeil.Ihara.FinalApprox
import RamanujanWeil.Arith.AssemblyIhara
import RamanujanWeil.Arith.HurwitzPrimeSquare

/-!
# Conditional headline: Eichler–Selberg + ordinary Deuring ⇒ Deligne's bound for `τ`

For `H = RamanujanWeil.Arith.Hurwitz.hurwitz` every input of the R-ord assembly
`iharaApprox_of_arith` is proved except the two arithmetic milestones A2 (Eichler–Selberg at prime
powers) and A3-ord (ordinary Deuring–Waterhouse):

* `HurwitzConventions hurwitz`, `HurwitzPrimeSquare hurwitz p` (`Arith/HurwitzPrimeSquare.lean`);
* `TauHeckeRecurrence p` (`Arith/TauHecke.lean`);
* `SupersingularCountBound p` (`Arith/SupersingularBound.lean`);
* `HasseAll p` (`Ihara/HasseAll.lean`, Weil closure).

`IharaApprox p` at every prime then gives `RamanujanTau.DeligneBound` by
`deligneBound_of_iharaApprox_all` (`FinalApprox.lean`).
-/

namespace RamanujanWeil.Ihara

open RamanujanWeil.ArithPlan RamanujanWeil.Arith.Hurwitz

/-- `IharaApprox p` from ES (exact) and ordinary Deuring at `p`, for the Hurwitz class number. -/
theorem iharaApprox_of_ES_Deuring (p : ℕ) [Fact p.Prime]
    (hES : EichlerSelbergPrimePow hurwitz p) (hD : OrdinaryDeuring hurwitz p) : IharaApprox p :=
  iharaApprox_of_arith hurwitz p hurwitzConventions hD hES (hurwitzPrimeSquare p Fact.out)
    (tauHeckeRecurrence p Fact.out) (supersingularCountBound p) (hasseAll p)

/-- `IharaApprox p` from approximate ES and ordinary Deuring at `p`. -/
theorem iharaApprox_of_ESApprox_Deuring (p : ℕ) [Fact p.Prime]
    (hES : EichlerSelbergApprox hurwitz p) (hD : OrdinaryDeuring hurwitz p) : IharaApprox p :=
  iharaApprox_of_arith_approx hurwitz p hurwitzConventions hD hES (hurwitzPrimeSquare p Fact.out)
    (tauHeckeRecurrence p Fact.out) (supersingularCountBound p) (hasseAll p)

/-- **Conditional headline.** Eichler–Selberg at prime powers and ordinary Deuring–Waterhouse
(for the Hurwitz class number) at every prime imply Deligne's bound `τ(p)² ≤ 4p¹¹`. -/
theorem deligneBound_of_ES_Deuring
    (hES : ∀ (p : ℕ) [Fact p.Prime], EichlerSelbergPrimePow hurwitz p)
    (hD : ∀ (p : ℕ) [Fact p.Prime], OrdinaryDeuring hurwitz p) : RamanujanTau.DeligneBound :=
  deligneBound_of_iharaApprox_all fun p _ => iharaApprox_of_ES_Deuring p (hES p) (hD p)

/-- **Conditional headline, approximate ES** (only the elliptic terms of ES exact). -/
theorem deligneBound_of_ESApprox_Deuring
    (hES : ∀ (p : ℕ) [Fact p.Prime], EichlerSelbergApprox hurwitz p)
    (hD : ∀ (p : ℕ) [Fact p.Prime], OrdinaryDeuring hurwitz p) : RamanujanTau.DeligneBound :=
  deligneBound_of_iharaApprox_all fun p _ => iharaApprox_of_ESApprox_Deuring p (hES p) (hD p)

end RamanujanWeil.Ihara
