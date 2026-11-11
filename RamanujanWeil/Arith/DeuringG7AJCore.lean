import RamanujanWeil.Arith.DeuringG7DGeomFamily
import RamanujanWeil.Arith.DeuringG1Point

/-!
# A3-ord, G7 Abel–Jacobi: the bijection `E(k̄) ≃ J_W(k̄)` and the class-group bridge

`docs/ARITH_DEURING_G7_AJHEIS.md` §1. For `W / 𝔽_q` and a Jacobian site `S`:

* `curvePtFvp` is a bijection: sections `z` of `E_W → Spec k̄` are `k̄`-points of the
  Weierstrass scheme (`fvpCurvePt`, the pullback universal property).
* **`ajEquiv`**: `E(k̄) ≃ J_W(k̄)`, `P_z ↦ z ≫ aj`. This is Mathlib's points, through
  `Ihara.fvpEquivPoint`, followed by Abel–Jacobi, which is bijective on points because `aj` is an
  isomorphism (G1, `JacSite.isIso_aj`).
* **`PicClassBridge W S`** (named): a homomorphism `ρ : J_W(k̄) → Cl(k̄[E])` with
  `ρ(aj z) = Point.toClass P_z`. Mathematically `ρ` restricts a degree-zero line bundle on
  `E_W` to the affine chart `E_W ∖ O = Spec k̄[E]`, followed by `Pic(k̄[E]) ≅ Cl(k̄[E])`
  (`ClassGroup.equivPic`). It is additive because restriction commutes with `⊗`, and it sends
  `𝒪(P − O)|_U = m_P^{−1}` to `[m_P]^{−1}`, so `−ρ` works.
* **`abelJacobiMathlib_of_bridge`**: `PicClassBridge ⟹ AbelJacobiMathlib`. No injectivity of `ρ`
  needs to be assumed. `ρ ∘ ajEquiv = toClass`, where Mathlib's `Point.toClass` is an
  injective group homomorphism (the chord–tangent law is the class-group law), and `ajEquiv` is
  onto. So `ρ` is injective, and then `ajEquiv` is additive.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory
  CartesianMonoidalCategory
open WeierstrassCurve WeierstrassCurve.Affine
open scoped CategoryTheory.MonObj

universe u

noncomputable section

namespace RamanujanWeil.Arith.Deuring.Geom.G7.DGeom

open Stacks.Groupoids RamanujanWeil.Arith.Deuring.Geom.G7 RamanujanWeil.Arith.Deuring.Geom.G7.Fin
  RamanujanWeil.Ihara Stacks.EtaleCohomology Stacks.PicardFunctor
  AlgebraicGeometry.ModuliEllipticCurves.Weierstrass

open scoped Classical

set_option linter.unusedSectionVars false

variable {K : Type u} [Field K] [Fintype K] (W₀ : WeierstrassCurve K) [W₀.IsElliptic]
  (S : Jac.JacSite W₀)

/-- The `k̄`-points (sections) of `E_W → Spec k̄`. -/
abbrev Sec := 𝟙_ (Over (Spec (.of (AlgebraicClosure K)))) ⟶ curveOver S.B S.hX S.hk S.f

/-- **The inverse of `curvePtFvp`**: a `k̄`-point `g` of the Weierstrass scheme is the section
`(g, id)` of `E_W = projOf W ×_K k̄`. -/
def fvpCurvePt (g : fieldValuedPoints (projectionOf W₀) (AlgebraicClosure K)) : Sec W₀ S :=
  Over.homMk (pullback.lift g.1 (𝟙 _) (by
    rw [Category.id_comp]
    exact g.2)) (by
    change pullback.lift g.1 (𝟙 _) _ ≫ Jac.gw W₀ = 𝟙 _
    exact pullback.lift_snd _ _ _)

theorem curvePtFvp_fvpCurvePt (g : fieldValuedPoints (projectionOf W₀) (AlgebraicClosure K)) :
    curvePtFvp W₀ S (fvpCurvePt W₀ S g) = g := by
  apply Subtype.ext
  exact pullback.lift_fst _ _ _

theorem fvpCurvePt_curvePtFvp (z : Sec W₀ S) : fvpCurvePt W₀ S (curvePtFvp W₀ S z) = z := by
  apply Over.OverMorphism.ext
  change pullback.lift _ (𝟙 _) _ = (z.left : Spec (.of (AlgebraicClosure K)) ⟶ Jac.Ew W₀)
  apply pullback.hom_ext
  · rw [pullback.lift_fst]; rfl
  · rw [pullback.lift_snd]
    have h0 := Over.w z
    simp at h0
    exact h0.symm

/-- **Sections of `E_W` are Mathlib's points `E(k̄)`.** -/
def secEquiv : Sec W₀ S ≃ ((Wbar W₀)⁄(AlgebraicClosure K)).Point where
  toFun z := fvpEquivPoint W₀ (AlgebraicClosure K) (curvePtFvp W₀ S z)
  invFun P := fvpCurvePt W₀ S ((fvpEquivPoint W₀ (AlgebraicClosure K)).symm P)
  left_inv z := by
    simp only [Equiv.symm_apply_apply, fvpCurvePt_curvePtFvp]
  right_inv P := by
    show fvpEquivPoint W₀ _ (curvePtFvp W₀ S (fvpCurvePt W₀ S _)) = P
    rw [curvePtFvp_fvpCurvePt]
    exact Equiv.apply_symm_apply _ P

/-- **Abel–Jacobi on `k̄`-points**: `E(k̄) ≃ J_W(k̄)`, `P_z ↦ z ≫ aj`. -/
def ajEquiv : ((Wbar W₀)⁄(AlgebraicClosure K)).Point ≃ Pt S.J :=
  (secEquiv W₀ S).symm.trans
    { toFun := fun z => z ≫ S.aj
      invFun := fun t => t ≫ inv S.aj
      left_inv := fun z => by simp
      right_inv := fun t => by simp }

theorem ajEquiv_secEquiv (z : Sec W₀ S) : ajEquiv W₀ S (secEquiv W₀ S z) = z ≫ S.aj := by
  simp [ajEquiv]

/-- **The class-group bridge (named).** A homomorphism `ρ : J_W(k̄) → Cl(k̄[E])` with
`ρ(aj z) = [m_{P_z}]` (Mathlib's `Point.toClass`): restriction of degree-zero line bundles from
`E_W` to the affine chart `Spec k̄[E] = E_W ∖ O` (with a sign). -/
def PicClassBridge : Prop :=
  ∃ ρ : Additive (Pt S.J) →+ Additive (ClassGroup (Rg (Wbar W₀))),
    ∀ z : Sec W₀ S, ρ (Additive.ofMul (z ≫ S.aj)) =
      Point.toClass (fvpEquivPoint W₀ (AlgebraicClosure K) (curvePtFvp W₀ S z))

/-- **Abel–Jacobi compatibility from the class-group bridge.** -/
theorem abelJacobiMathlib_of_bridge (h : PicClassBridge W₀ S) : AbelJacobiMathlib W₀ S := by
  obtain ⟨ρ, hρ⟩ := h
  have key : ∀ P, ρ (Additive.ofMul (ajEquiv W₀ S P)) = Point.toClass P := by
    intro P
    obtain ⟨z, rfl⟩ := (secEquiv W₀ S).surjective P
    rw [ajEquiv_secEquiv, hρ]
    rfl
  have hinj : Function.Injective ρ := by
    intro a b hab
    obtain ⟨P, rfl⟩ : ∃ P, Additive.ofMul (ajEquiv W₀ S P) = a :=
      ⟨(ajEquiv W₀ S).symm a.toMul, by simp⟩
    obtain ⟨Q, rfl⟩ : ∃ Q, Additive.ofMul (ajEquiv W₀ S Q) = b :=
      ⟨(ajEquiv W₀ S).symm b.toMul, by simp⟩
    rw [key, key] at hab
    rw [Point.toClass_injective hab]
  refine ⟨
    { toEquiv := (ajEquiv W₀ S).trans Additive.ofMul
      map_add' := fun P Q => hinj (by
        change ρ (Additive.ofMul (ajEquiv W₀ S (P + Q))) =
          ρ (Additive.ofMul (ajEquiv W₀ S P) + Additive.ofMul (ajEquiv W₀ S Q))
        rw [key (P + Q), map_add ρ, key P, key Q, map_add Point.toClass]) }, ?_⟩
  intro z
  change Additive.ofMul (ajEquiv W₀ S (secEquiv W₀ S z)) = _
  rw [ajEquiv_secEquiv]

end RamanujanWeil.Arith.Deuring.Geom.G7.DGeom
