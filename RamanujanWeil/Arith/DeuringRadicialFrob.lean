import RamanujanWeil.Arith.DeuringRadicialGen
import StacksFrontier.AlgebraicGeometry.GroupScheme.ZPowUnramified
import StacksFrontier.AlgebraicGeometry.GroupScheme.AbelianVariety.EndomorphismKernelCount
import StacksFrontier.AlgebraicGeometry.Curves.FunctionFieldFrobenius
import StacksFrontier.FieldTheory.SeparableCompositumFrobenius
import StacksFrontier.FieldTheory.PBasisRank

/-!
# RadicialDual, step (b): `[p]^* k(A) ⊆ k(A)^p`

`docs/ARITH_DEURING_RADICIAL.md`. Let `k` be algebraically closed of characteristic `p > 0` and
`A` a one-dimensional abelian variety over `k`, `L = k(A)`.

* **`exists_pow_eq_functionFieldMap_zpow_char`**: every element of `[p]^* L` is a `p`-th power
  in `L`. Otherwise (Stacks `isSeparable_of_notMem_compositumFrobenius`, with
  `[L : k L^p] = p`) `L / [p]^* L` is separable, so `[p]` is étale at the generic point
  (`etaleAt_genericPoint_of_formallyUnramified`), hence at a closed point, hence at the
  identity (translation, Stacks `etaleAt_unit_of_etaleAt_closedPoint`), hence unramified there;
  but then `p` is a unit in `k` (Stacks `isUnit_of_unramifiedAt_zpow_id_left_unit`: the tangent
  map of `[p]` is multiplication by `p`).
* **`exists_pow_eq_functionFieldMap_zpow_pow`**: iterating, every element of `[p^e]^* L` is a
  `p^e`-th power.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.MonObj

universe u

namespace RamanujanWeil.Arith.Deuring.Radicial

open Stacks.Groupoids RamanujanWeil.Arith.Deuring.Geom RamanujanWeil.Arith.Deuring.Dual2

variable {k : Type u} [Field k] [IsAlgClosed k] {A : Over (Spec (.of k))} [GrpObj A]
  [AlgebraicGeometry.IsAbelianVariety k A]

/-- The variety underlying an abelian variety. -/
noncomputable abbrev var (A : Over (Spec (.of k))) [GrpObj A] [AlgebraicGeometry.IsAbelianVariety k A] :
    Variety k :=
  ⟨A.left, A.hom⟩

omit [IsAlgClosed k] [GrpObj A] [AlgebraicGeometry.IsAbelianVariety k A] in
/-- `functionFieldMap` respects equality of morphisms. -/
theorem functionFieldMap_congr {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y] {f g : X ⟶ Y}
    [IsDominant f] [IsDominant g] (h : f = g) : functionFieldMap f = functionFieldMap g := by
  subst h; rfl

/-- `[n]`, `n ≠ 0`, is dominant in dimension one. -/
theorem isDominant_zpow (hA : abelianVarietyDimension A = 1) (n : ℤ) (hn : n ≠ 0) :
    IsDominant ((𝟙 A : A ⟶ A) ^ n).left :=
  isDominant_of_ne_one hA hA _ (zpow_id_ne_one hA n hn)

/-- **`[p]` is inseparable**: every element of `[p]^* k(A)` is a `p`-th power. -/
theorem exists_pow_eq_functionFieldMap_zpow_char (hA : abelianVarietyDimension A = 1) (p : ℕ)
    [hp : Fact p.Prime] [CharP k p] (y : A.left.functionField) :
    haveI := isDominant_zpow hA (p : ℤ) (by exact_mod_cast hp.out.ne_zero)
    ∃ w : A.left.functionField,
      functionFieldMap ((𝟙 A : A ⟶ A) ^ (p : ℤ)).left y = w ^ p := by
  haveI := isDominant_zpow hA (p : ℤ) (by exact_mod_cast hp.out.ne_zero)
  set β : A ⟶ A := (𝟙 A : A ⟶ A) ^ (p : ℤ) with hβdef
  set φ : A.left.functionField →+* A.left.functionField := functionFieldMap β.left
  letI : Algebra k A.left.functionField := varietyFunctionFieldAlgebra (var A)
  have hcurve : IsCurve k A.hom := isCurve_of_dim_one hA
  have := smooth_hom A
  have : CharP A.left.functionField p := charP_functionField p A.hom
  have : ExpChar A.left.functionField p := ExpChar.prime hp.out
  have : ExpChar k p := ExpChar.prime hp.out
  by_contra hne
  push Not at hne
  have hnot : φ y ∉ compositumFrobenius k A.left.functionField p := by
    rw [compositumFrobenius_eq_fieldRange_frobenius k A.left.functionField p]
    intro hmem
    obtain ⟨w, hw⟩ := RingHom.mem_fieldRange.mp hmem
    exact hne w (by rw [← hw, frobenius_def])
  -- `A.left.functionField / φ A.left.functionField` is separable
  set N : Subfield A.left.functionField := φ.fieldRange
  have hdeg := finrank_compositumFrobenius_functionField p A.hom
  have hfin : @Module.Finite A.left.functionField A.left.functionField _ _ φ.toAlgebra.toModule :=
    finiteDimensional_functionField_of_isCurve A.hom A.hom β.left (Over.w β)
  let eN : A.left.functionField ≃+* N := RingEquiv.ofBijective φ.rangeRestrictField φ.rangeRestrictField_bijective
  have : Module.Finite N A.left.functionField :=
    @Module.Finite.of_equiv_equiv A.left.functionField A.left.functionField N A.left.functionField _ _ _ _ φ.toAlgebra _ eN (RingEquiv.refl A.left.functionField)
      (RingHom.ext fun a => rfl) hfin
  have hkE : ∀ a : k, algebraMap k A.left.functionField a ∈ (algebraMap N A.left.functionField).fieldRange := by
    intro a
    exact RingHom.mem_fieldRange.mpr ⟨⟨algebraMap k A.left.functionField a, RingHom.mem_fieldRange.mpr
      ⟨algebraMap k A.left.functionField a, functionFieldMap_algebraMap (var A) (var A) β a⟩⟩, rfl⟩
  have hsep := isSeparable_of_notMem_compositumFrobenius (E := N) (k := k) p hdeg hkE
    (f := ⟨φ y, RingHom.mem_fieldRange.mpr ⟨y, rfl⟩⟩) hnot
  have hφ : φ = (algebraMap N A.left.functionField).comp eN.toRingHom := RingHom.ext fun a => rfl
  have hfu : φ.FormallyUnramified := by
    rw [hφ]
    exact RingHom.FormallyUnramified.comp
      (RingHom.FormallyUnramified.of_surjective eN.surjective)
      (formallyUnramified_algebraMap_of_isSeparable N A.left.functionField)
  -- hence `[p]` is étale at the identity
  have := isLocallyNoetherian_left A
  have : LocallyOfFiniteType (β.left ≫ A.hom) := β.w.symm ▸ inferInstance
  have : LocallyOfFiniteType β.left := locallyOfFiniteType_of_comp β.left A.hom
  have : JacobsonSpace A.left := LocallyOfFiniteType.jacobsonSpace A.hom
  have : IsIntegral A.left := GeometricallyIntegral.isIntegral_of_subsingleton A.hom
  have het := etaleAt_genericPoint_of_formallyUnramified β.left hfu
  obtain ⟨z, hzc, hz⟩ := exists_closedPoint_etaleAt β.left het
  have hunit := etaleAt_unit_of_etaleAt_closedPoint k A β hzc hz
  have hunr : UnramifiedAt β.left ((η[A]).left (IsLocalRing.closedPoint k)) :=
    ((etaleAt_iff_mem_smoothLocus_and_unramifiedAt β.left _).1 hunit).2
  have hdim : 0 < topologicalKrullDim A.left := by
    rw [topologicalKrullDim_eq_abelianVarietyDimension A, hA]; simp
  have hu := isUnit_of_unramifiedAt_zpow_id_left_unit k A hdim _ (p : ℤ) hunr
  rw [Int.cast_natCast, CharP.cast_eq_zero, isUnit_iff_ne_zero] at hu
  exact hu rfl

/-- **`[p^e]^* k(A) ⊆ k(A)^{p^e}`.** -/
theorem exists_pow_eq_functionFieldMap_zpow_pow (hA : abelianVarietyDimension A = 1) (p : ℕ)
    [hp : Fact p.Prime] [CharP k p] (e : ℕ) (y : A.left.functionField) :
    haveI := isDominant_zpow hA ((p ^ e : ℕ) : ℤ) (by exact_mod_cast (pow_pos hp.out.pos e).ne')
    ∃ w : A.left.functionField,
      functionFieldMap ((𝟙 A : A ⟶ A) ^ ((p ^ e : ℕ) : ℤ)).left y = w ^ (p ^ e) := by
  have hA' : IsIntegral A.left := GeometricallyIntegral.isIntegral_of_subsingleton A.hom
  induction e generalizing y with
  | zero =>
    haveI := isDominant_zpow hA ((p ^ 0 : ℕ) : ℤ) (by simp)
    exact ⟨_, (pow_one _).symm⟩
  | succ e ih =>
    haveI h1 := isDominant_zpow hA ((p ^ e : ℕ) : ℤ)
      (by exact_mod_cast (pow_pos hp.out.pos e).ne')
    haveI h2 := isDominant_zpow hA (p : ℤ) (by exact_mod_cast hp.out.ne_zero)
    haveI h3 := isDominant_zpow hA ((p ^ (e + 1) : ℕ) : ℤ)
      (by exact_mod_cast (pow_pos hp.out.pos (e + 1)).ne')
    have hcomp : (𝟙 A : A ⟶ A) ^ ((p ^ (e + 1) : ℕ) : ℤ) =
        ((𝟙 A : A ⟶ A) ^ ((p ^ e : ℕ) : ℤ)) ≫ ((𝟙 A : A ⟶ A) ^ (p : ℤ)) := by
      rw [comp_zpow_id, ← zpow_mul]
      congr 1
      all_goals (push_cast; try ring)
    have hff : functionFieldMap ((𝟙 A : A ⟶ A) ^ ((p ^ (e + 1) : ℕ) : ℤ)).left =
        (functionFieldMap ((𝟙 A : A ⟶ A) ^ ((p ^ e : ℕ) : ℤ)).left).comp
          (functionFieldMap ((𝟙 A : A ⟶ A) ^ (p : ℤ)).left) := by
      rw [← functionFieldMap_comp]
      exact functionFieldMap_congr (by rw [hcomp, Over.comp_left])
    obtain ⟨w, hw⟩ := exists_pow_eq_functionFieldMap_zpow_char hA p y
    obtain ⟨v, hv⟩ := ih w
    refine ⟨v, ?_⟩
    rw [hff, RingHom.comp_apply, hw, map_pow, hv, ← pow_mul, pow_succ]

end RamanujanWeil.Arith.Deuring.Radicial
