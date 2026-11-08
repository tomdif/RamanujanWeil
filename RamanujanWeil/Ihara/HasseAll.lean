import RamanujanWeil.Ihara.CurveH1BettiStacks
import RamanujanWeil.Ihara.PointsRealizes
import RamanujanWeil.Arith.AssemblyVocab

/-!
# `HasseAll p` for every prime `p` (Weil closure)

For `c : Fin 5 → 𝔽_{pⁿ}` with `Δ(c) ≠ 0`, `a(E_c)² ≤ 4pⁿ`: Hasse's bound
`sq_le_four_mul_card_weierstrassH1'` (from `dim H¹ = 2` and the Weil bound on `H¹`) with
`H1RankFormula` discharged by `h1RankFormula` (Stacks Tag 0C1Z) and `RealizesWeierstrass` by
`realizesWeierstrass_projOf`. The big étale site and the auxiliary prime `ℓ ≠ p` are chosen inside
the proof, as in `Final.lean`.
-/

open CategoryTheory AlgebraicGeometry

namespace RamanujanWeil.ArithPlan

open RamanujanWeil.Ihara

/-- **Hasse's bound for every Weierstrass tuple over every `𝔽_{pⁿ}`.** -/
theorem hasseAll (p : ℕ) [Fact p.Prime] : HasseAll p := by
  intro n hn c hc
  letI : Fintype (GaloisField p n) := Fintype.ofFinite _
  haveI : (wc c).IsElliptic := ⟨hc.isUnit⟩
  obtain ⟨ℓ, hℓle, hℓ⟩ := Nat.exists_infinite_primes (p + 1)
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  haveI : Fact (ℓ ≠ ringChar (GaloisField p n)) :=
    ⟨by rw [ringChar.eq (GaloisField p n) p]; omega⟩
  have h := sq_le_four_mul_card_weierstrassH1' (wc c)
    (BigEtaleSite.containing (Spec (.of (ZMod p)))) ℓ h1RankFormula
    (realizesWeierstrass_projOf _ _)
  have hcard : (Nat.card (GaloisField p n) : ℤ) = (p : ℤ) ^ n := by
    rw [GaloisField.card p n (by omega)]; push_cast; rfl
  have h' : ((Nat.card (GaloisField p n) : ℤ) + 1 - Nat.card (wc c).toAffine.Point) ^ 2 ≤
      4 * (Nat.card (GaloisField p n) : ℤ) := by
    simpa only [Fintype.card_eq_nat_card] using h
  show traceOfFrob (wc c) ^ 2 ≤ 4 * (p : ℤ) ^ n
  rw [traceOfFrob, ← hcard]
  exact h'

end RamanujanWeil.ArithPlan
