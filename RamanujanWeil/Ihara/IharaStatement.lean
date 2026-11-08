import RamanujanWeil.Ihara.Endgame
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.FieldTheory.Finite.GaloisField

/-!
# The Ihara–Birch identity (frozen arithmetic interface)

`wc`, `traceOfFrob` and `IharaIdentity` copied verbatim from `scratch/ProbeInterfaces.lean`
(`symTrace` and `tauPowerSum` are those of `Endgame.lean`, which are verbatim copies too).
Definitions only; nothing is assumed or proved here.
-/

open Finset

namespace RamanujanWeil.Ihara

/-- The general Weierstrass curve with coefficient vector `c = (a₁,a₂,a₃,a₄,a₆)`. -/
def wc {F : Type*} [CommRing F] (c : Fin 5 → F) : WeierstrassCurve F := ⟨c 0, c 1, c 2, c 3, c 4⟩

/-- `a(E) = q + 1 − #E(F)` (Mathlib's convention, as in `WeierstrassCurve.localPolynomial`). -/
noncomputable def traceOfFrob {F : Type*} [Field F] (W : WeierstrassCurve F) : ℤ :=
  (Nat.card F : ℤ) + 1 - Nat.card W.toAffine.Point

/-- **Ihara–Birch identity, level 1, weight 12** (numerically verified, scripts/scout):
`Σ_{c ∈ 𝔽_q⁵, Δ(c) ≠ 0} tr Sym¹⁰(Frob | E_c) = q³ (q − 1)(−1 − (αⁿ + βⁿ))`, `q = pⁿ`. -/
noncomputable def IharaIdentity (p : ℕ) [Fact p.Prime] : Prop :=
  ∀ n : ℕ, 1 ≤ n →
    letI : Fintype (GaloisField p n) := Fintype.ofFinite _
    open scoped Classical in
    ∑ c ∈ ({c : Fin 5 → GaloisField p n | (wc c).Δ ≠ 0} : Finset _),
        symTrace 10 (traceOfFrob (wc c)) ((p : ℤ) ^ n) =
      (p : ℤ) ^ (3 * n) * ((p : ℤ) ^ n - 1) * (-1 - tauPowerSum p n)

/-- The integer Weierstrass sum `S n = Σ_{c ∈ 𝔽_{pⁿ}⁵, Δ(c) ≠ 0} symTrace 10 (a(E_c)) (pⁿ)`, the
left side of `IharaIdentity` (M6 identifies it with the point side of the Lefschetz package). -/
noncomputable def weierstrassSum (p : ℕ) [Fact p.Prime] (n : ℕ) : ℤ :=
  letI : Fintype (GaloisField p n) := Fintype.ofFinite _
  open scoped Classical in
  ∑ c ∈ ({c : Fin 5 → GaloisField p n | (wc c).Δ ≠ 0} : Finset _),
    symTrace 10 (traceOfFrob (wc c)) ((p : ℤ) ^ n)

theorem weierstrassSum_eq_of_ihara {p : ℕ} [Fact p.Prime] (h : IharaIdentity p) (n : ℕ)
    (hn : 1 ≤ n) :
    weierstrassSum p n = (p : ℤ) ^ ((5 - 2) * n) * ((p : ℤ) ^ n - 1) * (-1 - tauPowerSum p n) :=
  h n hn

end RamanujanWeil.Ihara
