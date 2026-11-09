import RamanujanWeil.Ihara.FinalES
import RamanujanWeil.Arith.DeuringApproxMult

/-!
# Headline with approximate Deuring: no Deuring/Honda existence needed

`deligneBound_of_Deuring` (`FinalES.lean`) needs the exact per-trace count `OrdinaryDeuring`,
whose proof via `DeuringLattice` needs both Tate uniqueness and Deuring/Honda existence
(docs/ARITH_DEURING_G7.md §2). The approximate endgame `IharaApprox` tolerates an `ℓ¹` error
`O((n+1)^k q^{9/2})` in the ordinary per-trace counts (`OrdinaryDeuringApprox`), and the
Kronecker–Hurwitz relation (proved here from the Popa–Zagier core, `DeuringApproxKH.lean`)
turns **either** half of the per-class count into such a bound.

* **`deligneBound_of_DeuringApprox`** : `OrdinaryDeuringApprox hurwitz` at every prime ⇒ Deligne.
* **`deligneBound_of_DeuringMult_unique`** : per-trace counts `q³(q−1)·m(t)·H/2` with
  `m(t) ≤ 1` (Tate uniqueness) at every prime ⇒ Deligne.
* **`deligneBound_of_DeuringMult_exists`** : the same with `m(t) ≥ 1` (existence) ⇒ Deligne.
* `deligneBound_of_Deuring'` : the old headline re-derived through the approximate one.
-/

namespace RamanujanWeil.Ihara

open RamanujanWeil.ArithPlan RamanujanWeil.Arith.Hurwitz

/-- `IharaApprox p` from approximate ordinary Deuring at `p` (ES, prime-square, Hecke,
supersingular count and Hasse are all proved). -/
theorem iharaApprox_of_DeuringApprox (p : ℕ) [Fact p.Prime]
    (hD : OrdinaryDeuringApprox hurwitz p) : IharaApprox p :=
  iharaApprox_of_deuringApprox p hurwitz hurwitzConventions hD
    (RamanujanWeil.Arith.ES.Analytic.eichlerSelberg_all p) (hurwitzPrimeSquare p Fact.out)
    (tauHeckeRecurrence p Fact.out) (supersingularCountBound p) (hasseAll p)

/-- **Headline, approximate Deuring.** If at every prime the ordinary per-trace counts agree
with `q³(q−1)H(4q−t²)/2` up to an `ℓ¹` error `C (n+1)^k q^{9/2}`, then `τ(p)² ≤ 4p¹¹`. -/
theorem deligneBound_of_DeuringApprox
    (hD : ∀ (p : ℕ) [Fact p.Prime], OrdinaryDeuringApprox hurwitz p) :
    RamanujanTau.DeligneBound :=
  deligneBound_of_iharaApprox_all fun p _ => iharaApprox_of_DeuringApprox p (hD p)

/-- **Headline, uniqueness only.** Per-trace counts `N(t) = q³(q−1)·m(t)·H(4q−t²)/2` with
`m(t) ≤ 1` (at most one ordinary isogeny class per trace, i.e. Tate) at every prime imply
Deligne's bound. No existence (Deuring/Honda lifting) is needed. -/
theorem deligneBound_of_DeuringMult_unique (mult : ℕ → ℕ → ℤ → ℕ)
    (hM : ∀ (p : ℕ) [Fact p.Prime], DeuringMultiplicity hurwitz p (mult p))
    (huniq : ∀ (p : ℕ) [Fact p.Prime], ∀ n : ℕ, 1 ≤ n → ∀ t : ℤ, ¬ (p : ℤ) ∣ t →
      t ^ 2 < 4 * (p : ℤ) ^ n → mult p n t ≤ 1) :
    RamanujanTau.DeligneBound :=
  deligneBound_of_DeuringApprox fun p _ =>
    ordinaryDeuringApprox_of_mult_unique_hurwitz p (mult p) (hM p) (huniq p) (hasseAll p)

/-- **Headline, existence only.** The same with `m(t) ≥ 1` (every ordinary trace occurs)
instead of uniqueness. -/
theorem deligneBound_of_DeuringMult_exists (mult : ℕ → ℕ → ℤ → ℕ)
    (hM : ∀ (p : ℕ) [Fact p.Prime], DeuringMultiplicity hurwitz p (mult p))
    (hex : ∀ (p : ℕ) [Fact p.Prime], ∀ n : ℕ, 1 ≤ n → ∀ t : ℤ, ¬ (p : ℤ) ∣ t →
      t ^ 2 < 4 * (p : ℤ) ^ n → 1 ≤ mult p n t) :
    RamanujanTau.DeligneBound :=
  deligneBound_of_DeuringApprox fun p _ =>
    ordinaryDeuringApprox_of_mult_exists_hurwitz p (mult p) (hM p) (hex p) (hasseAll p)

/-- Sanity: the exact headline factors through the approximate one. -/
theorem deligneBound_of_Deuring'
    (hD : ∀ (p : ℕ) [Fact p.Prime], OrdinaryDeuring hurwitz p) : RamanujanTau.DeligneBound :=
  deligneBound_of_DeuringApprox fun p _ => ordinaryDeuringApprox_of_exact p hurwitz (hD p)

end RamanujanWeil.Ihara
