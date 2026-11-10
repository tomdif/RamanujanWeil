import RamanujanWeil.Arith.DeuringG7CJac

/-!
# A3-ord, G7 step C-Jac: the two-curve pullback on `Pic⁰` and the Jacobian isomorphism

`docs/ARITH_DEURING_G7_CJAC.md`. Continues `DeuringG7CJac` (presheaf / Picard functor level).

* `curvePicardMap_add`, `curvePicardMap_zero`: `φ^*` is additive on Picard functors.
* `curvePicardSchemeHom`: `φ^*` on Picard schemes (Yoneda).
* `exists_curveJacobianHom`, `curveJacobianHom`: `φ^*` maps `Pic⁰_{X'}` into `Pic⁰_X`.
* `isMonHom_curveJacobianHom`, `curveJacobianHom_comp`, `curveJacobianHom_id`.
* `curveJacobianHom_comp_twistedJacobianHom`: the Frobenius square on `Pic⁰`.
* Over `Spec k`: `curveJacobianPullback`, `isMonHom_curveJacobianPullback`,
  **`curveJacobianIso`**, **`curveJacobianPullback_comp_jacobianFrobenius`**,
  **`exists_equivariant_jacobianIso`**.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite Stacks.Frobenius
open MonoidalCategory CartesianMonoidalCategory Stacks.PicardFunctor
open scoped CategoryTheory.MonObj

universe u

noncomputable section

namespace RamanujanWeil.Arith.Deuring.Geom.G7.CJac

/-! ## Additivity -/

section Curve

variable {k : Type u} [Field k] (B : BigFppfSite.{u}) {X X' : Scheme.{u}}
  (hX : B.Contains X) (hX' : B.Contains X')
  (hk : B.Contains (Spec (.of k))) (f : B.obj hX ⟶ B.obj hk) (f' : B.obj hX' ⟶ B.obj hk)
  (φ : X ⟶ X') (hφ : φ ≫ B.inclusion.map f' = B.inclusion.map f)
  (σ' : Spec (.of k) ⟶ X') (hσ' : σ' ≫ B.inclusion.map f' = 𝟙 (Spec (.of k)))
  [IsCurve k (B.inclusion.map f')] [IsProjectiveVariety k (B.inclusion.map f')]
  [Smooth (B.inclusion.map f')]

include σ' hσ' in
/-- `φ^*` on Picard functors is additive (the source `X'` has a rational point, so every point
of `Pic_{X'/k}` is the class of an invertible module, Stacks 0B9N). -/
theorem curvePicardMap_add (T : BigFppfOver B (Spec (.of k)) hk)
    (a b : (picardFunctor B hX' hk f').obj (op T)) :
    (curvePicardMap B hX hX' hk f f' φ hφ).app (op T) (a + b) =
      (curvePicardMap B hX hX' hk f f' φ hφ).app (op T) a +
        (curvePicardMap B hX hX' hk f f' φ hφ).app (op T) b := by
  have hsurj := surjective_toPicardFunctorHom B hX' hk f' σ' hσ'
    (isIso_baseChangeProj_c_of_isCurve B hX' hk f' σ' hσ') T
  obtain ⟨x, rfl⟩ := hsurj a
  obtain ⟨y, rfl⟩ := hsurj b
  rw [← map_add, toPicardFunctorHom_apply, toPicardFunctorHom_apply, toPicardFunctorHom_apply,
    curvePicardMap_toPicardFunctor, curvePicardMap_toPicardFunctor,
    curvePicardMap_toPicardFunctor, Stacks.Picard.schemePullbackClass_add,
    toPicardFunctor_app_add]

include σ' hσ' in
theorem curvePicardMap_zero (T : BigFppfOver B (Spec (.of k)) hk) :
    (curvePicardMap B hX hX' hk f f' φ hφ).app (op T) 0 = 0 := by
  have h := curvePicardMap_add B hX hX' hk f f' φ hφ σ' hσ' T 0 0
  rw [add_zero] at h
  exact left_eq_add.mp h

end Curve

/-! ## Picard schemes -/

section Scheme

variable {k : Type u} [Field k] (B : BigFppfSite.{u}) {X X' : Scheme.{u}}
  (hX : B.Contains X) (hX' : B.Contains X')
  (hk : B.Contains (Spec (.of k))) (f : B.obj hX ⟶ B.obj hk) (f' : B.obj hX' ⟶ B.obj hk)
  (φ : X ⟶ X') (hφ : φ ≫ B.inclusion.map f' = B.inclusion.map f)
  [(picardFunctor B hX hk f).IsRepresentable] [(picardFunctor B hX' hk f').IsRepresentable]

/-- **`φ^*` on Picard schemes**, `Pic_{X'/k} ⟶ Pic_{X/k}`, by Yoneda. -/
def curvePicardSchemeHom : picardSchemeOver B hX' hk f' ⟶ picardSchemeOver B hX hk f :=
  (picardHomEquiv B hX hk f).symm
    ((curvePicardMap B hX hX' hk f f' φ hφ).app _ (universalPoint B hX' hk f'))

/-- The morphism of Picard schemes classifies `φ^*` of the classified point. -/
theorem picardHomEquiv_comp_curvePicardSchemeHom {T : BigFppfOver B (Spec (.of k)) hk}
    (x : T ⟶ picardSchemeOver B hX' hk f') :
    picardHomEquiv B hX hk f (x ≫ curvePicardSchemeHom B hX hX' hk f f' φ hφ) =
      (curvePicardMap B hX hX' hk f f' φ hφ).app (op T) (picardHomEquiv B hX' hk f' x) := by
  have hx : picardHomEquiv B hX' hk f' x =
      (picardFunctor B hX' hk f').map x.op (universalPoint B hX' hk f') := by
    rw [← (picardFunctor B hX' hk f').representableBy.homEquiv_comp x (𝟙 _), Category.comp_id]
  rw [(picardFunctor B hX hk f).representableBy.homEquiv_comp, curvePicardSchemeHom,
    Equiv.apply_symm_apply, hx]
  exact (NatTrans.naturality_apply (curvePicardMap B hX hX' hk f f' φ hφ) x.op
    (universalPoint B hX' hk f')).symm

end Scheme

/-! ## Jacobians in the site -/

section Jacobian

variable {k : Type u} [Field k] (B : BigFppfSite.{u}) {X X' : Scheme.{u}}
  (hX : B.Contains X) (hX' : B.Contains X')
  (hk : B.Contains (Spec (.of k))) (f : B.obj hX ⟶ B.obj hk) (f' : B.obj hX' ⟶ B.obj hk)
  (φ : X ⟶ X') (hφ : φ ≫ B.inclusion.map f' = B.inclusion.map f)
  [IsCurve k (B.inclusion.map f)] [GeometricallyIrreducible (B.inclusion.map f)]
  [Smooth (B.inclusion.map f)] [IsProper (B.inclusion.map f)]
  [IsProjectiveVariety k (B.inclusion.map f)]
  [IsCurve k (B.inclusion.map f')] [GeometricallyIrreducible (B.inclusion.map f')]
  [Smooth (B.inclusion.map f')] [IsProper (B.inclusion.map f')]
  [IsProjectiveVariety k (B.inclusion.map f')]
  (σ : Spec (.of k) ⟶ X) (hσ : σ ≫ B.inclusion.map f = 𝟙 (Spec (.of k)))
  (σ' : Spec (.of k) ⟶ X') (hσ' : σ' ≫ B.inclusion.map f' = 𝟙 (Spec (.of k)))
  [(picardFunctor B hX hk f).IsRepresentable] [(picardFunctor B hX' hk f').IsRepresentable]
  [IsSepClosed k]

/-- **`φ^*` maps `Pic⁰_{X'/k}` into `Pic⁰_{X/k}`.** The image of the irreducible `Pic⁰_{X'}` is
connected and contains the zero point, and `Pic⁰_X` is open and closed in `Pic_X`. -/
theorem exists_curveJacobianHom :
    ∃ F : picardSchemeDegreeComponent B hX' hk f' σ' hσ' 0 ⟶
        picardSchemeDegreeComponent B hX hk f σ hσ 0,
      F ≫ picardSchemeDegreeComponentι B hX hk f σ hσ 0 =
        picardSchemeDegreeComponentι B hX' hk f' σ' hσ' 0 ≫
          curvePicardSchemeHom B hX hX' hk f f' φ hφ := by
  set ιJ' := picardSchemeDegreeComponentι B hX' hk f' σ' hσ' 0
  set ν := curvePicardSchemeHom B hX hX' hk f f' φ hφ
  refine (exists_comp_picardSchemeDegreeComponentι_iff B hX hk f σ hσ (ιJ' ≫ ν) 0).mpr
    ((range_subset_picardDegreeLocus_iff B hX hk f σ hσ (ιJ' ≫ ν) 0).mp ?_)
  obtain ⟨-, -, hirr⟩ := universallyClosed_picardSchemeDegreeComponent_zero B hX' hk f' σ' hσ'
  have hconn : _root_.IsPreconnected (Set.range (B.inclusion.map (ιJ' ≫ ν).left)) := by
    simpa only [Set.image_univ] using
      (IsPreirreducible.isPreconnected (@IrreducibleSpace.isIrreducible_univ _ _ hirr).2).image
        (B.inclusion.map (ιJ' ≫ ν).left) (B.inclusion.map (ιJ' ≫ ν).left).continuous.continuousOn
  refine hconn.subset_isClopen (isClopen_picardDegreeLocus B hX hk f σ hσ 0) ?_
  let T₀ : BigFppfOver B (Spec (.of k)) hk := fieldObj B hk k hk
  let φ₀ : T₀ ⟶ picardSchemeOver B hX hk f := (picardHomEquiv B hX hk f).symm 0
  have hφ₀ : ∀ t, curveFibreDegree B hX hk f σ hσ T₀ (picardHomEquiv B hX hk f φ₀) t = 0 := by
    rw [Equiv.apply_symm_apply]
    exact (degreeZeroAddSubgroup B hX hk f σ hσ T₀).zero_mem
  let φ₀' : T₀ ⟶ picardSchemeOver B hX' hk f' := (picardHomEquiv B hX' hk f').symm 0
  have hφ₀' : ∀ t, curveFibreDegree B hX' hk f' σ' hσ' T₀
      (picardHomEquiv B hX' hk f' φ₀') t = 0 := by
    rw [Equiv.apply_symm_apply]
    exact (degreeZeroAddSubgroup B hX' hk f' σ' hσ' T₀).zero_mem
  obtain ⟨ψ₀, hψ₀⟩ :=
    (exists_comp_picardSchemeDegreeComponentι_iff B hX' hk f' σ' hσ' φ₀' 0).mpr hφ₀'
  have hfix : ψ₀ ≫ ιJ' ≫ ν = φ₀ := by
    apply (picardHomEquiv B hX hk f).injective
    rw [← Category.assoc, picardHomEquiv_comp_curvePicardSchemeHom, hψ₀]
    simp only [φ₀', φ₀, Equiv.apply_symm_apply]
    exact curvePicardMap_zero B hX hX' hk f f' φ hφ σ' hσ' T₀
  obtain ⟨t₀⟩ : Nonempty ((BigFppfOver.toScheme B (Spec (.of k)) hk).obj T₀) :=
    inferInstanceAs (Nonempty (Spec (.of k)))
  refine ⟨B.inclusion.map φ₀.left t₀, ⟨B.inclusion.map ψ₀.left t₀, ?_⟩, ?_⟩
  · rw [← Scheme.Hom.comp_apply, ← Functor.map_comp, ← Over.comp_left, hfix]
  · exact (range_subset_picardDegreeLocus_iff B hX hk f σ hσ φ₀ 0).mpr hφ₀ ⟨t₀, rfl⟩

/-- **`φ^* : Pic⁰_{X'/k} ⟶ Pic⁰_{X/k}`** in the site. -/
def curveJacobianHom :
    picardSchemeDegreeComponent B hX' hk f' σ' hσ' 0 ⟶
      picardSchemeDegreeComponent B hX hk f σ hσ 0 :=
  (exists_curveJacobianHom B hX hX' hk f f' φ hφ σ hσ σ' hσ').choose

theorem curveJacobianHom_comp_ι :
    curveJacobianHom B hX hX' hk f f' φ hφ σ hσ σ' hσ' ≫
        picardSchemeDegreeComponentι B hX hk f σ hσ 0 =
      picardSchemeDegreeComponentι B hX' hk f' σ' hσ' 0 ≫
        curvePicardSchemeHom B hX hX' hk f f' φ hφ :=
  (exists_curveJacobianHom B hX hX' hk f f' φ hφ σ hσ σ' hσ').choose_spec

attribute [local instance] CartesianMonoidalCategory.ofHasFiniteProducts in
/-- On `T`-points, `φ^*` on `Pic⁰` is `φ^*` on the Picard functor. -/
theorem degreeZeroHomAddEquiv_comp_curveJacobianHom {T : BigFppfOver B (Spec (.of k)) hk}
    (x : T ⟶ picardSchemeDegreeComponent B hX' hk f' σ' hσ' 0) :
    letI := jacobianGrpObj B hX hk f σ hσ
    letI := jacobianGrpObj B hX' hk f' σ' hσ'
    (degreeZeroHomAddEquiv B hX hk f σ hσ T
        (Additive.ofMul (x ≫ curveJacobianHom B hX hX' hk f f' φ hφ σ hσ σ' hσ')) :
          (picardFunctor B hX hk f).obj (op T)) =
      (curvePicardMap B hX hX' hk f f' φ hφ).app (op T)
        (degreeZeroHomAddEquiv B hX' hk f' σ' hσ' T (Additive.ofMul x)) := by
  show picardHomEquiv B hX hk f ((x ≫ curveJacobianHom B hX hX' hk f f' φ hφ σ hσ σ' hσ') ≫
      picardSchemeDegreeComponentι B hX hk f σ hσ 0) =
    (curvePicardMap B hX hX' hk f f' φ hφ).app (op T)
      (picardHomEquiv B hX' hk f' (x ≫ picardSchemeDegreeComponentι B hX' hk f' σ' hσ' 0))
  rw [Category.assoc, curveJacobianHom_comp_ι, ← Category.assoc,
    picardHomEquiv_comp_curvePicardSchemeHom]

omit [IsCurve k (B.inclusion.map f')] [GeometricallyIrreducible (B.inclusion.map f')]
  [Smooth (B.inclusion.map f')] [IsProper (B.inclusion.map f')]
  [IsProjectiveVariety k (B.inclusion.map f')] [(picardFunctor B hX' hk f').IsRepresentable] in
attribute [local instance] CartesianMonoidalCategory.ofHasFiniteProducts in
/-- **Morphisms into `Pic⁰_X` are determined by their points**: two morphisms `A ⟶ Pic⁰_X`
whose composites with every `x : T ⟶ A` give the same degree-zero point are equal. -/
theorem pic0_hom_ext {A : BigFppfOver B (Spec (.of k)) hk}
    (g h : A ⟶ picardSchemeDegreeComponent B hX hk f σ hσ 0)
    (H : letI := jacobianGrpObj B hX hk f σ hσ
      (degreeZeroHomAddEquiv B hX hk f σ hσ A (Additive.ofMul g) :
          (picardFunctor B hX hk f).obj (op A)) =
        degreeZeroHomAddEquiv B hX hk f σ hσ A (Additive.ofMul h)) : g = h := by
  letI := jacobianGrpObj B hX hk f σ hσ
  apply Additive.ofMul.injective
  apply (degreeZeroHomAddEquiv B hX hk f σ hσ A).injective
  exact Subtype.ext H

attribute [local instance] CartesianMonoidalCategory.ofHasFiniteProducts in
/-- `φ^*` on `Pic⁰` is a homomorphism of group objects. -/
theorem isMonHom_curveJacobianHom :
    letI := jacobianGrpObj B hX hk f σ hσ
    letI := jacobianGrpObj B hX' hk f' σ' hσ'
    IsMonHom (curveJacobianHom B hX hX' hk f f' φ hφ σ hσ σ' hσ') := by
  letI := jacobianGrpObj B hX hk f σ hσ
  letI := jacobianGrpObj B hX' hk f' σ' hσ'
  set F := curveJacobianHom B hX hX' hk f f' φ hφ σ hσ σ' hσ'
  set N := curvePicardMap B hX hX' hk f f' φ hφ
  have key : ∀ {T : BigFppfOver B (Spec (.of k)) hk}
      (x : T ⟶ picardSchemeDegreeComponent B hX' hk f' σ' hσ' 0)
      (y : T ⟶ picardSchemeDegreeComponent B hX hk f σ hσ 0)
      (h : (N.app (op T) (degreeZeroHomAddEquiv B hX' hk f' σ' hσ' T (Additive.ofMul x)) :
          (picardFunctor B hX hk f).obj (op T)) =
        degreeZeroHomAddEquiv B hX hk f σ hσ T (Additive.ofMul y)), x ≫ F = y := by
    intro T x y h
    apply pic0_hom_ext B hX hk f σ hσ
    rwa [degreeZeroHomAddEquiv_comp_curveJacobianHom]
  constructor
  · refine key _ _ ?_
    have h1 : (η[picardSchemeDegreeComponent B hX hk f σ hσ 0] :
        𝟙_ (BigFppfOver B (Spec (.of k)) hk) ⟶ _) = 1 := by
      rw [CategoryTheory.Hom.one_def, toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]
    have h1' : (η[picardSchemeDegreeComponent B hX' hk f' σ' hσ' 0] :
        𝟙_ (BigFppfOver B (Spec (.of k)) hk) ⟶ _) = 1 := by
      rw [CategoryTheory.Hom.one_def, toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]
    rw [h1, h1']
    simp only [ofMul_one, map_zero, ZeroMemClass.coe_zero]
    exact curvePicardMap_zero B hX hX' hk f f' φ hφ σ' hσ' _
  · have hμ' : (μ[picardSchemeDegreeComponent B hX' hk f' σ' hσ' 0]) =
        fst _ _ * snd _ _ := by
      rw [CategoryTheory.Hom.mul_def, lift_fst_snd, Category.id_comp]
    have hFF : (F ⊗ₘ F) ≫ μ[picardSchemeDegreeComponent B hX hk f σ hσ 0] =
        (fst _ _ ≫ F) * (snd _ _ ≫ F) := by
      rw [CategoryTheory.Hom.mul_def]
      congr 1
    rw [hFF]
    refine key _ _ ?_
    rw [hμ', ofMul_mul, ofMul_mul, map_add, map_add, AddSubgroup.coe_add, AddSubgroup.coe_add,
      curvePicardMap_add B hX hX' hk f f' φ hφ σ' hσ',
      ← degreeZeroHomAddEquiv_comp_curveJacobianHom,
      ← degreeZeroHomAddEquiv_comp_curveJacobianHom]

end Jacobian

end RamanujanWeil.Arith.Deuring.Geom.G7.CJac

end
