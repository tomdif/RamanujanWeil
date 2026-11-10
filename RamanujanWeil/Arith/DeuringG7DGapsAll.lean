import RamanujanWeil.Arith.DeuringG7DGapsBridge
import RamanujanWeil.Arith.DeuringG7DGeomFamily

/-!
# A3-ord, G7-D-gaps (assembly): `DGeomGaps` with the divisor bridge discharged

`docs/ARITH_DEURING_G7DGAPS.md` §4. `rrStabilizerBridge` (`DeuringG7DGapsBridge`) proves the
`bridge` field of `DGeomGaps` at every level `N = ℓⁿ⁺¹ ≥ 2`. What is left of `DGeomGapsAll K`:

* **`AbelJacobiAll K`**: `AbelJacobiMathlib W S` for every `W / K` and Jacobian site `S`
  (Mathlib's chord–tangent law on `E(k̄)` is the law of `J_W(k̄)` through `aj`);
* **`ThetaHeisenbergAll K`**: `ThetaHeisenberg (Wbar W) (ℓⁿ⁺¹)` for odd primes `ℓ` invertible in
  `k̄` (nondegeneracy of the commutator pairing on `E[ℓⁿ⁺¹]`).

* `dGeomGaps_of`, **`dGeomGapsAll_of`**: these two give `DGeomGapsAll K`, hence the constructed
  theta families `thetaFamilyOf`.
* **`deligneBound_of_gaps`**: Deligne's bound from `AbelJacobiAll`, `ThetaHeisenbergAll`,
  `ThetaLevelDescent` and `PrincipalFiniteness` at every finite field.
-/

open AlgebraicGeometry CategoryTheory
open WeierstrassCurve WeierstrassCurve.Affine

universe u

noncomputable section

namespace RamanujanWeil.Arith.Deuring.Geom.G7.DGeom

open scoped Classical

/-- `ℓⁿ⁺¹ ≥ 2` for a prime `ℓ`. -/
theorem two_le_prime_pow {ℓ : ℕ} (hℓ : ℓ.Prime) (n : ℕ) : 2 ≤ ℓ ^ (n + 1) :=
  hℓ.two_le.trans (Nat.le_self_pow (Nat.succ_ne_zero n) ℓ)

variable {K : Type u} [Field K] [Fintype K]

/-- **`DGeomGaps` from Abel–Jacobi and Heisenberg**: the divisor bridge is now a theorem. -/
theorem dGeomGaps_of (W₀ : WeierstrassCurve K) [W₀.IsElliptic] (S : Jac.JacSite W₀) {ℓ : ℕ}
    (hℓ : ℓ.Prime) (haj : AbelJacobiMathlib W₀ S)
    (hheis : ∀ n : ℕ, ThetaHeisenberg (Wbar W₀) (ℓ ^ (n + 1))) : DGeomGaps W₀ S ℓ where
  aj := haj
  bridge n := rrStabilizerBridge (Wbar W₀) (two_le_prime_pow hℓ n)
  heis := hheis

variable (K)

/-- **Abel–Jacobi compatibility for every curve over `K`** (named). -/
def AbelJacobiAll : Prop :=
  ∀ (W : WeierstrassCurve K) [W.IsElliptic] (S : Jac.JacSite W), AbelJacobiMathlib W S

/-- **The Heisenberg property at every level `ℓⁿ⁺¹`**, `ℓ` an odd prime invertible in `k̄`
(named). -/
def ThetaHeisenbergAll : Prop :=
  ∀ (W : WeierstrassCurve K) [W.IsElliptic] (ℓ : ℕ), ℓ.Prime → ℓ ≠ 2 →
    IsUnit (ℓ : AlgebraicClosure K) → ∀ n : ℕ, ThetaHeisenberg (Wbar W) (ℓ ^ (n + 1))

variable {K}

/-- **`DGeomGapsAll K` from the two remaining inputs.** -/
theorem dGeomGapsAll_of (haj : AbelJacobiAll K) (hheis : ThetaHeisenbergAll K) :
    DGeomGapsAll K := by
  intro W _ S ℓ hℓ hodd hk
  exact dGeomGaps_of W S hℓ (haj W S) (hheis W ℓ hℓ hodd hk)

/-- The remaining seams at every finite field. -/
def DGapsSplitAll : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (n : ℕ), 1 ≤ n →
    letI : Fintype (GaloisField p n) := Fintype.ofFinite _
    AbelJacobiAll (GaloisField p n) ∧ ThetaHeisenbergAll (GaloisField p n) ∧
      ThetaLevelDescent (GaloisField p n) ∧ PrincipalFiniteness (GaloisField p n)

/-- **Deligne's bound** from Abel–Jacobi, Heisenberg, descent and Θ + J + C; the divisor
bridge is no longer an input. -/
theorem deligneBound_of_gaps (h : DGapsSplitAll) : RamanujanTau.DeligneBound :=
  deligneBound_of_split fun p _ n hn =>
    letI : Fintype (GaloisField p n) := Fintype.ofFinite _
    have h' := h p n hn
    ⟨dGeomGapsAll_of h'.1 h'.2.1, h'.2.2.1, h'.2.2.2⟩

end RamanujanWeil.Arith.Deuring.Geom.G7.DGeom
