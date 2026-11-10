import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Algebra.Module.NatInt
import Mathlib.Tactic.Abel

/-!
# A3-ord, G7 Θ: the swap case of a product theta divisor, algebraic core

`docs/ARITH_DEURING_G7_PRINCIPAL.md` §3. If a principally polarized `B ≅ C₁ × C₂` had a
Frobenius `π` swapping the factors, `π(x, y) = (ρ₂ y, ρ₁ x)`, then `φ(x, y) = (x, −y)` would
anticommute with `π`. On points `π² − tπ + q = 0`, so also `π² + tπ + q = 0`, hence
`2tπ = 0` and `2tq = 0` on `B(k̄)`. Since `B(k̄)` has points of every `ℓ`-power order and
`p ∤ t`, this is impossible: in `ThetaJacobianModel` the product case is diagonal.

This file proves the group-theoretic core, `two_mul_trace_mul_card_smul_eq_zero`.
-/

namespace RamanujanWeil.Arith.Deuring.Geom.G7.Theta

variable {M : Type*} [AddCommGroup M]

/-- **Swap core.** If `π² − tπ + q = 0` on `M` and an injective `φ` anticommutes with `π`, then
`2tq · x = 0` for every `x`. -/
theorem two_mul_trace_mul_card_smul_eq_zero (π φ : M →+ M) (t q : ℤ)
    (hrel : ∀ x, π (π x) - t • π x + q • x = 0) (hφ : Function.Injective φ)
    (hanti : ∀ x, π (φ x) = -φ (π x)) (x : M) : (2 * t * q) • x = 0 := by
  have hplus : ∀ y, π (π y) + t • π y + q • y = 0 := by
    intro y
    apply hφ
    have h := hrel (φ y)
    rw [hanti, map_neg, hanti, neg_neg, smul_neg, sub_neg_eq_add] at h
    rw [map_add, map_add, map_zsmul, map_zsmul, map_zero]
    exact h
  have h2 : ∀ y, (2 * t) • π y = 0 := by
    intro y
    have h := congrArg₂ (· - ·) (hplus y) (hrel y)
    simp only [sub_self] at h
    rw [mul_smul, two_smul]
    rw [← h]
    abel
  have hq : q • x = -π (π x - t • x) := by
    have := hrel x
    rw [map_sub, map_zsmul, eq_neg_iff_add_eq_zero, add_comm]
    exact this
  rw [mul_smul, hq, smul_neg, h2, neg_zero]

end RamanujanWeil.Arith.Deuring.Geom.G7.Theta
