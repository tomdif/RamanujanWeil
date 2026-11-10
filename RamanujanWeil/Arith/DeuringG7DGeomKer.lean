import RamanujanWeil.Arith.DeuringG7DGeomTheta

/-!
# A3-ord, G7-D-geom (kernel): `K(𝒪(N·O)) = E[N]` via Abel–Jacobi, and the Heisenberg seam

`docs/ARITH_DEURING_G7DGEOM.md` §3.

* **`isPrincipal_XYIdeal'_pow_iff`** (Abel–Jacobi, in Mathlib's form): for an affine point
  `Q = (x, y)` with maximal ideal `m_Q = ⟨X − x, Y − y⟩`, `m_Q^N` is principal iff `N·Q = 0`. It is
  the injectivity of `Point.toClass : E(F) → Cl(F[E])` (Mathlib), applied to `N·Q`.
* **`RRStabilizerBridge W N`** (named, the divisor-theoretic input): for `Q ≠ O`, the
  translation by `P = −Q` lifts to `𝒢(L(N·O))` iff `m_Q^N` is principal. Mathematically
  `f · τ_P L(N·O) = L(N·O)` iff `div f = N[Q] − N[O]` (`N ≥ 2`, base-point freeness), iff the
  fractional ideal `(f)` of `F[E]` is `m_Q^N` (the pole order at `O` is forced by degree `0`).
* **`thetaKer_eq_torsion`**: given the bridge, `K(L) = E[N]`, i.e. `t_P^*L ≅ L ⟺ N·P = 0`.
* **`ThetaHeisenberg W N`** (named): the center of `𝒢(L)` is `F^×`. This is the
  nondegeneracy of the commutator pairing (`e^L = e_N`, the Weil pairing).
* `CentralExt.transport`: a central extension of `K` is one of `K'` along `K ≃+ K'`.
-/

noncomputable section

namespace RamanujanWeil.Arith.Deuring.Geom.G7.DGeom

open WeierstrassCurve WeierstrassCurve.Affine Polynomial
open RamanujanWeil.Arith.Deuring.Geom.G7.Fin.Weil (CentralExt)
open scoped nonZeroDivisors

universe u

/-! ### Transport of central extensions -/

namespace CentralExtTransport

variable {G K K' A : Type*} [Group G] [AddCommGroup K] [AddCommGroup K'] [AddCommGroup A]

/-- A central extension of `K` by `A`, read as one of `K'` along `u : K ≃+ K'`. -/
def transport (X : CentralExt G K A) (u : K ≃+ K') : CentralExt G K' A where
  p := (AddEquiv.toMultiplicative u).toMonoidHom.comp X.p
  surj := (AddEquiv.toMultiplicative u).surjective.comp X.surj
  ι := X.ι
  inj := X.inj
  exact g := by
    rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff]
    exact X.exact g
  central := X.central

theorem transport_p_eq_one (X : CentralExt G K A) (u : K ≃+ K') (g : G) :
    (transport X u).p g = 1 ↔ X.p g = 1 := by
  change (AddEquiv.toMultiplicative u) (X.p g) = 1 ↔ _
  exact MulEquiv.map_eq_one_iff _

end CentralExtTransport

variable {F : Type u} [Field F] (W : Affine F) [W.IsElliptic] [DecidableEq F]

open scoped Classical

/-! ### Abel–Jacobi in Mathlib's form -/

/-- **`m_Q^N` is principal iff `N·Q = 0`** (Mathlib's `Point.toClass` is an injective
homomorphism `E(F) → Cl(F[E])`). -/
theorem isPrincipal_XYIdeal'_pow_iff {x y : F} (h : (W⁄F).Nonsingular x y) (N : ℕ) :
    ((((CoordinateRing.XYIdeal' h ^ N : (FractionalIdeal (Rg W)⁰ (Kf W))ˣ) :
      FractionalIdeal (Rg W)⁰ (Kf W)) : Submodule (Rg W) (Kf W))).IsPrincipal ↔
      N • (Point.some x y h : (W⁄F).Point) = 0 := by
  rw [← ClassGroup.mk_eq_one_iff, map_pow, ← Point.toClass_eq_zero, map_nsmul,
    Point.toClass_some]
  change _ ↔ Additive.ofMul (ClassGroup.mk (Kf W) (CoordinateRing.XYIdeal' h) ^ N) = 0
  rw [ofMul_eq_zero]

/-! ### The kernel `K(L)` -/

/-- **The divisor bridge (named).** For `Q = (x, y) ≠ O` and `P = −Q`: some `f` has
`f · τ_P L(N·O) = L(N·O)` iff `m_Q^N` is a principal fractional ideal of `F[E]`. -/
def RRStabilizerBridge (N : ℕ) : Prop :=
  ∀ {x y : F} (h : (W⁄F).Nonsingular x y),
    (-(Point.some x y h) ∈ thetaKer W (rrSpace W N)) ↔
      ((((CoordinateRing.XYIdeal' h ^ N : (FractionalIdeal (Rg W)⁰ (Kf W))ˣ) :
        FractionalIdeal (Rg W)⁰ (Kf W)) : Submodule (Rg W) (Kf W))).IsPrincipal

/-- **`K(𝒪(N·O)) = E[N]`**: `t_P^*L ≅ L ⟺ N·P = 0`, given the divisor bridge. -/
theorem thetaKer_eq_torsion {N : ℕ} (hB : RRStabilizerBridge W N) :
    thetaKer W (rrSpace W N) = AddSubgroup.torsionBy (W⁄F).Point (N : ℤ) := by
  ext P
  by_cases hP : P = 0
  · subst hP
    exact ⟨fun _ => smul_zero _, fun _ => (thetaKer W _).zero_mem⟩
  · have hQ : -P ≠ 0 := neg_ne_zero.2 hP
    have hQe := eq_some_pt W hQ
    have key := hB (nonsingular_pt W hQ)
    rw [← hQe, neg_neg, isPrincipal_XYIdeal'_pow_iff, ← hQe] at key
    rw [key]
    change N • -P = 0 ↔ (N : ℤ) • P = 0
    rw [smul_neg, neg_eq_zero, natCast_zsmul]

/-- The torsion subgroup `E[N]` read as `K(L)`. -/
def torsionEquivThetaKer {N : ℕ} (hB : RRStabilizerBridge W N) :
    AddSubgroup.torsionBy (W⁄F).Point (N : ℤ) ≃+ thetaKer W (rrSpace W N) :=
  AddEquiv.addSubgroupCongr (thetaKer_eq_torsion W hB).symm

/-! ### The Heisenberg property -/

variable [IsAlgClosed F]

/-- **The Heisenberg property (named).** The center of `𝒢(𝒪(N·O))` is `F^×`: a central element
lies over `P = O`. Equivalently the commutator pairing `e^L : K(L) × K(L) → F^×` (which is the
Weil pairing `e_N`) is nondegenerate. -/
def ThetaHeisenberg (N : ℕ) : Prop :=
  ∀ g : thetaGroup W (rrSpace W N), (∀ h, g * h = h * g) → (thetaExtN W N).p g = 1

end RamanujanWeil.Arith.Deuring.Geom.G7.DGeom
