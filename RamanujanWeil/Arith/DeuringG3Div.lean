import RamanujanWeil.Arith.DeuringG3
import StacksFrontier.AlgebraicGeometry.GroupScheme.AbelianVariety.ZPowEtaleOfIsUnit
import StacksFrontier.AlgebraicGeometry.Spaces.ReducedClosedSubspace
import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.ReducedProduct
import Mathlib.AlgebraicGeometry.Sites.Fpqc

/-!
# A3-ord, G3 (divisibility): a homomorphism killing `A[n]` is divisible by `n`, `n` invertible

Let `A`, `B` be abelian varieties over an algebraically closed field `k` and `n` an integer
invertible in `k`. If a homomorphism `α : A ⟶ B` kills the `n`-torsion points `A(k)[n]`, then
`α = β ∘ [n]` for a homomorphism `β : A ⟶ B` (`exists_isMonHom_zpow_comp_eq`).

Proof: `[n]` is étale and surjective (Stacks), hence an effective epimorphism of schemes
(Mathlib, `Sites/Fpqc`). On `P = A ×_{[n], A, [n]} A`, which is étale over `A` hence reduced, the
two composites `P ⇉ A → B` agree on `k`-points (two points with the same image under `[n]`
differ by an `n`-torsion point), hence agree (`Stacks.Varieties.overHom_ext_of_points`); so `α`
descends along `[n]`. The descended map is a homomorphism: it is multiplicative on `k`-points
(every point is an `n`-th multiple, `Stacks.Groupoids.exists_pow_eq`) and `A ⊗ A` is reduced.

This is the descent half of Mumford §19 Thm 3 used for G3 (torsion-free cokernel of
`Hom(A,B) ⊗ ℤ_ℓ → Hom(T_ℓ A, T_ℓ B)`) and G6/G8; it does not need `dim A = 1`.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory
  CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

universe u

namespace RamanujanWeil.Arith.Deuring.Geom

open Stacks.Groupoids

variable {k : Type u} [Field k] [IsAlgClosed k]
  {A B : Over (Spec (.of k))} [GrpObj A] [GrpObj B]
  [AlgebraicGeometry.IsAbelianVariety k A] [AlgebraicGeometry.IsAbelianVariety k B]

/-- Every `k`-point of `A` is an `n`-th multiple, `n ≠ 0`. -/
theorem exists_zpow_eq_point (n : ℤ) (hn : n ≠ 0) (x : 𝟙_ (Over (Spec (.of k))) ⟶ A) :
    ∃ y : 𝟙_ (Over (Spec (.of k))) ⟶ A, y ^ n = x := by
  rcases Int.natAbs_eq n with h | h
  · obtain ⟨y, hy⟩ := exists_pow_eq k A n.natAbs (Int.natAbs_ne_zero.mpr hn) x
    exact ⟨y, by rw [h, zpow_natCast, hy]⟩
  · obtain ⟨y, hy⟩ := exists_pow_eq k A n.natAbs (Int.natAbs_ne_zero.mpr hn) x⁻¹
    exact ⟨y, by rw [h, zpow_neg, zpow_natCast, hy, inv_inv]⟩

omit [IsAlgClosed k] [AlgebraicGeometry.IsAbelianVariety k A] in
/-- `x ≫ [n] = x ^ n`. -/
theorem comp_zpow_id (n : ℤ) {Z : Over (Spec (.of k))} (x : Z ⟶ A) :
    x ≫ ((𝟙 A) ^ n) = x ^ n := by
  rw [GrpObj.comp_zpow, Category.comp_id]

/-- **Divisibility.** For `n` invertible in `k`, a homomorphism `α : A ⟶ B` killing `A(k)[n]`
factors as `α = [n] ≫ β` with `β` a homomorphism. -/
theorem exists_isMonHom_zpow_comp_eq (n : ℤ) (hn : IsUnit (n : k)) (α : A ⟶ B) [IsMonHom α]
    (h : ∀ x : 𝟙_ (Over (Spec (.of k))) ⟶ A, x ^ n = 1 → x ≫ α = 1) :
    ∃ β : A ⟶ B, IsMonHom β ∧ ((𝟙 A) ^ n) ≫ β = α := by
  have hn0 : n ≠ 0 := by rintro rfl; simp at hn
  set N := ((𝟙 A : A ⟶ A) ^ n).left with hN
  have : Etale N := etale_zpow_id_left_of_isUnit A n hn
  have : Surjective N := surjective_zpow_id_left_of_isUnit A n hn
  have hNA : N ≫ A.hom = A.hom := Over.w ((𝟙 A : A ⟶ A) ^ n)
  -- the two composites on `P = A ×_{[n]} A` agree
  have hPA : pullback.fst N N ≫ A.hom = pullback.snd N N ≫ A.hom := by
    rw [← hNA, ← Category.assoc, pullback.condition, Category.assoc, hNA]
  have key : pullback.fst N N ≫ α.left = pullback.snd N N ≫ α.left := by
    let Pk : Over (Spec (.of k)) := Over.mk (pullback.fst N N ≫ A.hom)
    have : IsReduced A.left := inferInstance
    have : IsReduced Pk.left := isReduced_of_etale (pullback.fst N N)
    have : LocallyOfFiniteType Pk.hom := by
      show LocallyOfFiniteType (pullback.fst N N ≫ A.hom)
      infer_instance
    let f1 : Pk ⟶ B := Over.homMk (pullback.fst N N ≫ α.left) (by
      show (pullback.fst N N ≫ α.left) ≫ B.hom = pullback.fst N N ≫ A.hom
      rw [Category.assoc, Over.w α])
    let f2 : Pk ⟶ B := Over.homMk (pullback.snd N N ≫ α.left) (by
      show (pullback.snd N N ≫ α.left) ≫ B.hom = pullback.fst N N ≫ A.hom
      rw [Category.assoc, Over.w α, hPA])
    have hf := Stacks.Varieties.overHom_ext_of_points f1 f2 (fun x => by
      let a : 𝟙_ (Over (Spec (.of k))) ⟶ A := Over.homMk (x.left ≫ pullback.fst N N) (by
        show (x.left ≫ pullback.fst N N) ≫ A.hom = _
        rw [Category.assoc]; exact Over.w x)
      let b : 𝟙_ (Over (Spec (.of k))) ⟶ A := Over.homMk (x.left ≫ pullback.snd N N) (by
        show (x.left ≫ pullback.snd N N) ≫ A.hom = _
        rw [Category.assoc, ← hPA]; exact Over.w x)
      have hab' : a ≫ ((𝟙 A) ^ n) = b ≫ ((𝟙 A) ^ n) := Over.OverMorphism.ext (by
        show (x.left ≫ pullback.fst N N) ≫ N = (x.left ≫ pullback.snd N N) ≫ N
        rw [Category.assoc, Category.assoc, pullback.condition])
      have hab : a ^ n = b ^ n := by rw [← comp_zpow_id n a, ← comp_zpow_id n b, hab']
      have h1 : (a * b⁻¹) ^ n = 1 := by
        rw [mul_zpow, inv_zpow, hab, mul_inv_cancel]
      have h2 := h _ h1
      have h3 : a ≫ α = b ≫ α := by
        rw [show (a * b⁻¹) ≫ α = IsMonHom.monoidHom α _ (a * b⁻¹) from rfl, map_mul, map_inv]
          at h2
        exact mul_inv_eq_one.mp h2
      have e1 : x ≫ f1 = a ≫ α := Over.OverMorphism.ext (by
        simp only [Over.comp_left, Over.homMk_left, f1, a, Category.assoc])
      have e2 : x ≫ f2 = b ≫ α := Over.OverMorphism.ext (by
        simp only [Over.comp_left, Over.homMk_left, f2, b, Category.assoc])
      rw [e1, e2, h3])
    exact congrArg (fun r => r.left) hf
  -- descend along the effective epimorphism `[n]`
  have hdesc : ∀ {Z : Scheme.{u}} (g₁ g₂ : Z ⟶ A.left), g₁ ≫ N = g₂ ≫ N →
      g₁ ≫ α.left = g₂ ≫ α.left := fun g₁ g₂ hg => by
    calc g₁ ≫ α.left = (pullback.lift g₁ g₂ hg ≫ pullback.fst N N) ≫ α.left := by
          rw [pullback.lift_fst]
      _ = (pullback.lift g₁ g₂ hg ≫ pullback.snd N N) ≫ α.left := by
          rw [Category.assoc, Category.assoc, key]
      _ = g₂ ≫ α.left := by rw [pullback.lift_snd]
  set β' : A.left ⟶ B.left := EffectiveEpi.desc N α.left hdesc
  have hfac : N ≫ β' = α.left := EffectiveEpi.fac N α.left hdesc
  have hw : β' ≫ B.hom = A.hom := by
    rw [← cancel_epi N, ← Category.assoc, hfac, Over.w α, hNA]
  let β : A ⟶ B := Over.homMk β' hw
  have hβ : ((𝟙 A) ^ n) ≫ β = α := Over.OverMorphism.ext (by
    simp only [Over.comp_left, Over.homMk_left, β]; exact hfac)
  -- `β` on points
  have hpt : ∀ y : 𝟙_ (Over (Spec (.of k))) ⟶ A, (y ^ n) ≫ β = y ≫ α := fun y => by
    rw [← comp_zpow_id, Category.assoc, hβ]
  have hmulpt : ∀ x y : 𝟙_ (Over (Spec (.of k))) ⟶ A, (x * y) ≫ β = (x ≫ β) * (y ≫ β) := by
    intro x y
    obtain ⟨x', rfl⟩ := exists_zpow_eq_point n hn0 x
    obtain ⟨y', rfl⟩ := exists_zpow_eq_point n hn0 y
    rw [← mul_zpow, hpt, hpt, hpt]
    exact map_mul (IsMonHom.monoidHom α _) x' y'
  refine ⟨β, ⟨?_, ?_⟩, hβ⟩
  · -- `η ≫ β = η`
    have h1 : η[A] ≫ ((𝟙 A) ^ n) = η[A] := IsMonHom.one_hom ((𝟙 A) ^ n)
    rw [← h1, Category.assoc, hβ, IsMonHom.one_hom α]
  · -- `μ ≫ β = (β ⊗ β) ≫ μ`, checked on `k`-points of the reduced variety `A ⊗ A`
    have : IsReduced (A ⊗ A).left := by
      show IsReduced (pullback A.hom A.hom)
      exact isReduced_pullback_over_perfectField A.hom A.hom
    have : LocallyOfFiniteType (A ⊗ A).hom := by
      show LocallyOfFiniteType (pullback.fst A.hom A.hom ≫ A.hom)
      infer_instance
    apply Stacks.Varieties.overHom_ext_of_points
    intro P
    have hP : P = lift (P ≫ fst A A) (P ≫ snd A A) := by
      apply CartesianMonoidalCategory.hom_ext <;> simp
    have e1 : P ≫ μ[A] = (P ≫ fst A A) * (P ≫ snd A A) := by
      rw [Hom.mul_def, ← hP]
    have e2 : P ≫ (β ⊗ₘ β) ≫ μ[B] = (P ≫ fst A A ≫ β) * (P ≫ snd A A ≫ β) := by
      rw [Hom.mul_def, ← Category.assoc]
      congr 1
      apply CartesianMonoidalCategory.hom_ext <;> simp
    rw [← Category.assoc, e1, e2, hmulpt]
    simp only [Category.assoc]

end RamanujanWeil.Arith.Deuring.Geom
