import RamanujanWeil.Ihara.CurveH1Core
import RamanujanWeil.Ihara.SymWeights
import RamanujanWeil.Ihara.IharaStatement

/-!
# M6 (B), arithmetic part: traces of Frobenius over finite extensions (Mathlib only)

* `ExtensionTraces W q`: for every finite extension `L/k`,
  `a(W_L) = s_{[L:k]}(a(W), q)`, where `a(·) = traceOfFrob` and `s_m(a, q) = powSum a q m`
  (`= αᵐ + βᵐ` for the roots of `X² − aX + q`). Equivalently `#W(L) = q^m + 1 − (αᵐ + βᵐ)`.
* `extensionTraces_of_extension`: M4a's output (`natCard_point_extension_eq_of_weierstrass`, for
  Mathlib's chosen extensions `FiniteField.Extension k (ringChar k) n`, with `frobPowerSum`)
  implies `ExtensionTraces W #k` for **every** finite extension `L/k` (transport along
  `FiniteField.algEquivExtension`, `natCard_point_congr`).
* `powSum_eq_frobPowerSum`: M5's `powSum` and M4a's `frobPowerSum` are the same recursion.
-/

namespace RamanujanWeil.Ihara

theorem powSum_eq_frobPowerSum (a q : ℤ) : ∀ m, powSum a q m = frobPowerSum a q m
  | 0 => rfl
  | 1 => rfl
  | m + 2 => by
    rw [powSum, frobPowerSum_add_two, powSum_eq_frobPowerSum a q (m + 1),
      powSum_eq_frobPowerSum a q m]

/-- **Traces over all finite extensions.** For every finite field `L` over `k`,
`a(W_L) = s_{[L:k]}(a(W), q)`. (For `q = #k` this is the rationality of the zeta function of the
genus-one curve `W`, i.e. `#W(𝔽_{qᵐ}) = qᵐ + 1 − αᵐ − βᵐ`.) -/
def ExtensionTraces {k : Type} [Field k] (W : WeierstrassCurve k) (q : ℤ) : Prop :=
  ∀ (L : Type) [Field L] [Finite L] [Algebra k L],
    traceOfFrob (W.baseChange L) = powSum (traceOfFrob W) q (Module.finrank k L)

/-- **M4a's output ⇒ `ExtensionTraces`.** If `#W(k_n) = qⁿ + 1 − s_n(q + 1 − #W(k), q)` for
Mathlib's chosen extensions `k_n = FiniteField.Extension k (ringChar k) n` (the first conjunct of
`natCard_point_extension_eq_of_weierstrass`), then the same holds for every finite extension. -/
theorem extensionTraces_of_extension {k : Type} [Field k] [Fintype k] (W : WeierstrassCurve k)
    (h : haveI : Fact (ringChar k).Prime := ⟨CharP.char_is_prime k _⟩
      ∀ n : ℕ, ∀ hn : 1 ≤ n, haveI : NeZero n := ⟨by omega⟩
      (Nat.card (W.baseChange (FiniteField.Extension k (ringChar k) n)).toAffine.Point : ℤ) =
        (Fintype.card k : ℤ) ^ n + 1 -
          frobPowerSum ((Fintype.card k : ℤ) + 1 - Nat.card W.toAffine.Point) (Fintype.card k) n) :
    ExtensionTraces W (Fintype.card k) := by
  haveI : Fact (ringChar k).Prime := ⟨CharP.char_is_prime k _⟩
  intro L _ _ _
  have : Module.Finite k L := Module.Finite.of_finite
  set m := Module.finrank k L with hm
  have hm1 : 1 ≤ m := Module.finrank_pos
  haveI : NeZero m := ⟨by omega⟩
  have hL := natCard_point_congr W
    (FiniteField.algEquivExtension k (ringChar k) m L hm.symm)
  have hcard : Nat.card L = Nat.card k ^ m := Module.natCard_eq_pow_finrank
  have h' := h m hm1
  rw [traceOfFrob, traceOfFrob, hL, h', hcard, powSum_eq_frobPowerSum,
    Nat.card_eq_fintype_card (α := k)]
  push_cast
  ring

/-- `ExtensionTraces` is insensitive to rewriting `q`. -/
theorem ExtensionTraces.congr_q {k : Type} [Field k] {W : WeierstrassCurve k} {q q' : ℤ}
    (h : ExtensionTraces W q) (hq : q = q') : ExtensionTraces W q' := hq ▸ h

/-- `#W(L) = q^m + 1 − s_m` from `ExtensionTraces`, for `q = #k`. -/
theorem natCard_baseChange_of_extensionTraces {k : Type} [Field k] [Finite k]
    {W : WeierstrassCurve k} (h : ExtensionTraces W (Nat.card k)) (L : Type) [Field L] [Finite L]
    [Algebra k L] :
    (Nat.card (W.baseChange L).toAffine.Point : ℤ) =
      (Nat.card k : ℤ) ^ Module.finrank k L + 1 -
        powSum (traceOfFrob W) (Nat.card k) (Module.finrank k L) := by
  have : Module.Finite k L := Module.Finite.of_finite
  have h1 := h L
  have hcard : Nat.card L = Nat.card k ^ Module.finrank k L := Module.natCard_eq_pow_finrank
  rw [traceOfFrob, hcard] at h1
  push_cast at h1
  linarith

end RamanujanWeil.Ihara
