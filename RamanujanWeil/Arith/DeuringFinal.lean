import RamanujanWeil.Arith.DeuringFinalLattice
import RamanujanWeil.Ihara.FinalDeuringTate
import RamanujanWeil.Arith.DeuringG7FinCore

/-!
# A3-ord, final: Deligne's bound from uniqueness alone, or from existence alone

`docs/ARITH_DEURING_FINAL.md`. With the per-class count now unconditional
(`Final.deuringMultiplicity_uncond`), the only remaining input of the Ihara endgame is **one** of
the two halves of Deuring's correspondence for the concrete class count `Mult.mult`:

* **`deligneBound_of_multLeOne`**: `mult p n t ≤ 1` on the ordinary range (Tate uniqueness);
* **`deligneBound_of_ordinaryTraceExistence`**: every ordinary trace `t` (`p ∤ t`, `t² < 4pⁿ`)
  is the trace of some elliptic Weierstrass curve over `𝔽_{pⁿ}` (Deuring/Waterhouse existence),
  which gives `mult ≥ 1`;
* `deligneBound_of_tatePol'`: the current headline `deligneBound_of_tatePol` re-derived through
  the first one (`mult_le_one_pol`).

`OrdinaryTraceExistence` and `MultLeOneAll` are two **independent** single named Props, each
sufficient on its own; `TateFinitenessPolAll` implies the second.
-/

namespace RamanujanWeil.Arith.Deuring.Final

open RamanujanWeil.Ihara RamanujanWeil.ArithPlan RamanujanWeil.Arith.Hurwitz
  RamanujanWeil.Arith.Deuring.Mult RamanujanWeil.Arith.Deuring.Geom.G7.Fin

/-- **Tate uniqueness for the concrete class count (named).** At most one isogeny class of
elliptic curves over `𝔽_{pⁿ}` per ordinary trace. -/
def MultLeOneAll : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (n : ℕ), 1 ≤ n → ∀ t : ℤ, ¬ (p : ℤ) ∣ t →
    t ^ 2 < 4 * (p : ℤ) ^ n → mult p n t ≤ 1

/-- **Deuring/Waterhouse existence (named).** Every ordinary trace occurs: for `p ∤ t`,
`t² < 4pⁿ`, some elliptic Weierstrass curve over `𝔽_{pⁿ}` has trace `t`. -/
def OrdinaryTraceExistence : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (n : ℕ), 1 ≤ n → ∀ t : ℤ, ¬ (p : ℤ) ∣ t →
    t ^ 2 < 4 * (p : ℤ) ^ n →
      ∃ W : WeierstrassCurve (GaloisField p n), W.Δ ≠ 0 ∧ traceOfFrob W = t

/-- A curve of trace `t` gives an isogeny class: `mult ≥ 1`. -/
theorem one_le_mult_of_exists (p : ℕ) [Fact p.Prime] (n : ℕ) (t : ℤ)
    (h : ∃ W : WeierstrassCurve (GaloisField p n), W.Δ ≠ 0 ∧ traceOfFrob W = t) :
    1 ≤ mult p n t := by
  letI : Fintype (GaloisField p n) := Fintype.ofFinite _
  obtain ⟨W, hW⟩ := h
  have : Nonempty (IsogClass (GaloisField p n) t) := ⟨Quotient.mk _ ⟨W, hW⟩⟩
  exact Nat.card_pos

theorem multAll_eq (p : ℕ) [hp : Fact p.Prime] : multAll p = mult p := by
  funext n t
  unfold multAll
  rw [dif_pos hp.out]

/-- **Headline, uniqueness only.** `τ(p)² ≤ 4p¹¹` from `mult ≤ 1` alone. -/
theorem deligneBound_of_multLeOne (h : MultLeOneAll) : RamanujanTau.DeligneBound := by
  refine deligneBound_of_DeuringMult_unique multAll
    (fun p _ => by rw [multAll_eq p]; exact deuringMultiplicity_uncond p) ?_
  intro p _ n hn t hpt hlt
  rw [multAll_eq p]
  exact h p n hn t hpt hlt

/-- **Headline, existence only.** `τ(p)² ≤ 4p¹¹` from Deuring/Waterhouse existence alone,
without any Tate/finiteness input. -/
theorem deligneBound_of_ordinaryTraceExistence (h : OrdinaryTraceExistence) :
    RamanujanTau.DeligneBound := by
  refine deligneBound_of_DeuringMult_exists multAll
    (fun p _ => by rw [multAll_eq p]; exact deuringMultiplicity_uncond p) ?_
  intro p _ n hn t hpt hlt
  rw [multAll_eq p]
  exact one_le_mult_of_exists p n t (h p n hn t hpt hlt)

/-- `TateFinitenessPolAll ⇒ MultLeOneAll` (`mult_le_one_pol`). -/
theorem multLeOneAll_of_tatePol (hfin : TateFinitenessPolAll) : MultLeOneAll :=
  fun p _ n hn t hpt hlt => mult_le_one_pol hfin p n hn t hpt hlt

/-- The current headline, re-derived through `deligneBound_of_multLeOne`. -/
theorem deligneBound_of_tatePol' (hfin : TateFinitenessPolAll) : RamanujanTau.DeligneBound :=
  deligneBound_of_multLeOne (multLeOneAll_of_tatePol hfin)

end RamanujanWeil.Arith.Deuring.Final
