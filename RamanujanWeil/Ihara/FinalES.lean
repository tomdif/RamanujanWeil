import RamanujanWeil.Ihara.FinalArith
import RamanujanWeil.Arith.ESAnalytic

/-!
# Headline after A2: ordinary Deuring ⇒ Deligne's bound for `τ`

Milestone A2 (Eichler–Selberg at prime powers for the Hurwitz class number) is now proved
unconditionally (`RamanujanWeil.Arith.ES.Analytic.eichlerSelberg_all`, `Arith/ESAnalytic.lean`:
the algebraic Popa–Zagier part `ESMain` plus the analytic input `eichlerPeriodInput`). Composing
with `deligneBound_of_ES_Deuring` (`FinalArith.lean`) leaves the single arithmetic hypothesis
A3-ord (ordinary Deuring–Waterhouse).
-/

namespace RamanujanWeil.Ihara

open RamanujanWeil.ArithPlan RamanujanWeil.Arith.Hurwitz

/-- **Headline, A2 discharged.** Ordinary Deuring–Waterhouse (for the Hurwitz class number) at
every prime implies Deligne's bound `τ(p)² ≤ 4p¹¹`. -/
theorem deligneBound_of_Deuring
    (hD : ∀ (p : ℕ) [Fact p.Prime], OrdinaryDeuring hurwitz p) : RamanujanTau.DeligneBound :=
  deligneBound_of_ES_Deuring RamanujanWeil.Arith.ES.Analytic.eichlerSelberg_all hD

end RamanujanWeil.Ihara
