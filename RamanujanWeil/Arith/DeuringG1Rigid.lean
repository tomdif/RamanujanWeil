import RamanujanWeil.Arith.DeuringG1Frob

/-!
# A3-ord, G1.2: rigidity in dimension one, by transport through the Abel–Jacobi map

`docs/ARITH_DEURING_G1_3.md`. Let `X, X'` be two pointed genus-one curves over `k` in the same
big fppf site, with Jacobians `J, J'` and Abel–Jacobi isomorphisms `aj, aj'`, and let
`α : X' ≅ X` be a pointed `k`-isomorphism. Then

  `e = aj'⁻¹ ≫ α ≫ aj : J' ⟶ J`

is a **homomorphism** of group objects (`Rigid.isMonHom_transport`).

Proof. Pulling back along `β_T = α⁻¹ × 1_T : X_T ⟶ X'_T` is an additive natural transformation
`N : Pic_{X'/k} ⟶ Pic_{X/k}` (`Rigid.transportMap`, the same construction as Stacks'
`twistedPicardMap`). At the universal point, `N[𝒪(Δ')] = α^*[𝒪(Δ)]` (both are the graph of `α`,
`Frob.pointIdeal_comap_of_comm`), and `N[c₀']_T = [c₀]_T` since `α` is pointed. Every
`T`-point of `J'` is `m ≫ aj'` (Abel–Jacobi is bijective on `T`-points in genus one), so on
`T`-points `e` is `N`, which is additive. The group-object argument is then that of Stacks'
`isMonHom_twistedJacobianHom`.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
open CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

universe u

noncomputable section

namespace RamanujanWeil.Arith.Deuring.Geom

namespace Rigid

open Stacks.PicardFunctor Stacks.Hilbert

variable {k : Type u} [Field k] (B : BigFppfSite.{u}) {X X' : Scheme.{u}} (hX : B.Contains X)
  (hX' : B.Contains X') (hk : B.Contains (Spec (.of k)))
  (f : B.obj hX ⟶ B.obj hk) (f' : B.obj hX' ⟶ B.obj hk)
  (α : X' ⟶ X) [IsIso α] (hαf : α ≫ B.inclusion.map f = B.inclusion.map f')

/-! ### The transport map on Picard functors -/

include hαf in
theorem inv_comp_f : inv α ≫ B.inclusion.map f' = B.inclusion.map f := by
  rw [← hαf, IsIso.inv_hom_id_assoc]

/-- `β_T = α⁻¹ × 1_T : X_T ⟶ X'_T`. -/
def transportBase (T : BigFppfOver B (Spec (.of k)) hk) :
    baseChange B hX hk f T ⟶ baseChange B hX' hk f' T :=
  pullback.map (B.inclusion.map f) (B.inclusion.map T.hom) (B.inclusion.map f')
    (B.inclusion.map T.hom) (inv α) (𝟙 _) (𝟙 _)
    (by rw [Category.comp_id, inv_comp_f B hX hX' hk f f' α hαf]) (by simp)

@[reassoc]
theorem transportBase_fst (T : BigFppfOver B (Spec (.of k)) hk) :
    transportBase B hX hX' hk f f' α hαf T ≫
        pullback.fst (B.inclusion.map f') (B.inclusion.map T.hom) =
      pullback.fst (B.inclusion.map f) (B.inclusion.map T.hom) ≫ inv α :=
  pullback.lift_fst _ _ _

@[reassoc]
theorem transportBase_snd (T : BigFppfOver B (Spec (.of k)) hk) :
    transportBase B hX hX' hk f f' α hαf T ≫
        pullback.snd (B.inclusion.map f') (B.inclusion.map T.hom) =
      pullback.snd (B.inclusion.map f) (B.inclusion.map T.hom) ≫ 𝟙 _ :=
  pullback.lift_snd _ _ _

theorem baseChangeMap_transportBase {T U : BigFppfOver B (Spec (.of k)) hk} (g : T ⟶ U) :
    Stacks.PicardFunctor.baseChangeMap B hX hk f g ≫ transportBase B hX hX' hk f f' α hαf U =
      transportBase B hX hX' hk f f' α hαf T ≫ Stacks.PicardFunctor.baseChangeMap B hX' hk f' g := by
  apply pullback.hom_ext
  · simp only [Stacks.PicardFunctor.baseChangeMap, transportBase, Category.assoc, pullback.lift_fst,
      pullback.lift_fst_assoc, Category.comp_id]
  · simp only [Stacks.PicardFunctor.baseChangeMap, transportBase, Category.assoc, pullback.lift_snd,
      pullback.lift_snd_assoc, Category.comp_id, Category.id_comp]

theorem schemePullbackClass_transportBase_picardMap {T U : BigFppfOver B (Spec (.of k)) hk}
    (g : T ⟶ U) (x : picardAt B hX' hk f' U) :
    Stacks.Picard.schemePullbackClass (transportBase B hX hX' hk f f' α hαf T)
        (picardMap B hX' hk f' g x) =
      picardMap B hX hk f g
        (Stacks.Picard.schemePullbackClass (transportBase B hX hX' hk f f' α hαf U) x) := by
  change Stacks.Picard.schemePullbackClass (transportBase B hX hX' hk f f' α hαf T)
      (Stacks.Picard.schemePullbackClass (Stacks.PicardFunctor.baseChangeMap B hX' hk f' g) x) =
    Stacks.Picard.schemePullbackClass (Stacks.PicardFunctor.baseChangeMap B hX hk f g)
      (Stacks.Picard.schemePullbackClass (transportBase B hX hX' hk f f' α hαf U) x)
  rw [Stacks.Picard.schemePullbackClass_comp, Stacks.Picard.schemePullbackClass_comp,
    baseChangeMap_transportBase]

/-- `β^*` on the presheaves `T ↦ Pic(X'_T) ⟶ Pic(X_T)`. -/
def transportPresheafMap : picardPresheaf B hX' hk f' ⟶ picardPresheaf B hX hk f where
  app T := TypeCat.ofHom
    (Stacks.Picard.schemePullbackClass (transportBase B hX hX' hk f f' α hαf T.unop))
  naturality {T U} g := by
    ext x
    exact schemePullbackClass_transportBase_picardMap B hX hX' hk f f' α hαf g.unop x

/-- **The transport map `N : Pic_{X'/k} ⟶ Pic_{X/k}`**, the sheafification of `β^*`. -/
def transportMap : picardFunctor B hX' hk f' ⟶ picardFunctor B hX hk f :=
  sheafifyMap (BigFppfOver.topology B (Spec (.of k)) hk)
    (transportPresheafMap B hX hX' hk f f' α hαf)

theorem transportMap_toPicardFunctor (T : BigFppfOver B (Spec (.of k)) hk)
    (x : picardAt B hX' hk f' T) :
    (transportMap B hX hX' hk f f' α hαf).app (op T) ((toPicardFunctor B hX' hk f').app (op T) x) =
      (toPicardFunctor B hX hk f).app (op T)
        (Stacks.Picard.schemePullbackClass (transportBase B hX hX' hk f f' α hαf T) x) :=
  (ConcreteCategory.congr_hom (NatTrans.congr_app (toSheafify_naturality
    (BigFppfOver.topology B (Spec (.of k)) hk)
    (transportPresheafMap B hX hX' hk f f' α hαf)) (op T)) x).symm

theorem transportMap_naturality {T U : BigFppfOver B (Spec (.of k)) hk} (g : T ⟶ U)
    (ζ : (picardFunctor B hX' hk f').obj (op U)) :
    (transportMap B hX hX' hk f f' α hαf).app (op T) ((picardFunctor B hX' hk f').map g.op ζ) =
      (picardFunctor B hX hk f).map g.op ((transportMap B hX hX' hk f f' α hαf).app (op U) ζ) :=
  NatTrans.naturality_apply (transportMap B hX hX' hk f f' α hαf) g.op ζ

variable [IsCurve k (B.inclusion.map f')] [Smooth (B.inclusion.map f')]
  [IsProjectiveVariety k (B.inclusion.map f')]
  (σ' : Spec (.of k) ⟶ X') (hσ' : σ' ≫ B.inclusion.map f' = 𝟙 (Spec (.of k)))

include σ' hσ' in
/-- `N` is additive (every point of `Pic_{X'/k}` is a class on `X'_T`, [Stacks, Tag 0B9N]). -/
theorem transportMap_add (T : BigFppfOver B (Spec (.of k)) hk)
    (a b : (picardFunctor B hX' hk f').obj (op T)) :
    (transportMap B hX hX' hk f f' α hαf).app (op T) (a + b) =
      (transportMap B hX hX' hk f f' α hαf).app (op T) a +
        (transportMap B hX hX' hk f f' α hαf).app (op T) b := by
  have hsurj := surjective_toPicardFunctorHom B hX' hk f' σ' hσ'
    (isIso_baseChangeProj_c_of_isCurve B hX' hk f' σ' hσ') T
  obtain ⟨x, rfl⟩ := hsurj a
  obtain ⟨y, rfl⟩ := hsurj b
  rw [← map_add, toPicardFunctorHom_apply, toPicardFunctorHom_apply, toPicardFunctorHom_apply,
    transportMap_toPicardFunctor, transportMap_toPicardFunctor, transportMap_toPicardFunctor,
    Stacks.Picard.schemePullbackClass_add, toPicardFunctor_app_add]

include σ' hσ' in
theorem transportMap_zero (T : BigFppfOver B (Spec (.of k)) hk) :
    (transportMap B hX hX' hk f f' α hαf).app (op T) 0 = 0 := by
  have h := transportMap_add B hX hX' hk f f' α hαf σ' hσ' T 0 0
  rw [add_zero] at h
  exact left_eq_add.mp h

include σ' hσ' in
theorem transportMap_sub (T : BigFppfOver B (Spec (.of k)) hk)
    (a b : (picardFunctor B hX' hk f').obj (op T)) :
    (transportMap B hX hX' hk f f' α hαf).app (op T) (a - b) =
      (transportMap B hX hX' hk f f' α hαf).app (op T) a -
        (transportMap B hX hX' hk f f' α hαf).app (op T) b := by
  have h := transportMap_add B hX hX' hk f f' α hαf σ' hσ' T (a - b) b
  rw [sub_add_cancel] at h
  rw [h, add_sub_cancel_right]

/-! ### `N` at the universal point -/

variable [IsCurve k (B.inclusion.map f)] [Smooth (B.inclusion.map f)]
  [IsProjectiveVariety k (B.inclusion.map f)]
  [GeometricallyIrreducible (B.inclusion.map f)] [IsProper (B.inclusion.map f)]
  [GeometricallyIrreducible (B.inclusion.map f')] [IsProper (B.inclusion.map f')]
  (σ : Spec (.of k) ⟶ X) (hσ : σ ≫ B.inclusion.map f = 𝟙 (Spec (.of k)))
  [(picardFunctor B hX hk f).IsRepresentable] [(picardFunctor B hX' hk f').IsRepresentable]
  (hg : genus (B.inclusion.map f) = 1) (hg' : genus (B.inclusion.map f') = 1)

/-- `α` as a morphism of test schemes `X' ⟶ X`. -/
def transportHom : curveObj B hX' hk f' ⟶ curveObj B hX hk f :=
  Over.homMk (B.inclusion.preimage (X := B.obj hX') (Y := B.obj hX) α) (by
    apply B.inclusion.map_injective
    rw [Functor.map_comp]
    erw [Functor.map_preimage]
    exact hαf)

theorem post_map_transportHom :
    (Over.post (X := B.obj hk) B.inclusion).map (transportHom B hX hX' hk f f' α hαf) =
      (Over.homMk α hαf : curveOver B hX' hk f' ⟶ curveOver B hX hk f) :=
  Over.OverMorphism.ext (B.inclusion.map_preimage (X := B.obj hX') (Y := B.obj hX) α)

include hg hg' in
/-- **`N[𝒪(Δ')] = α^*[𝒪(Δ)]`**: both are the class of the graph of `α` on `X ×_k X'`. -/
theorem transportMap_univ :
    (transportMap B hX hX' hk f f' α hαf).app (op (curveObj B hX' hk f'))
        (Abel.univ B hX' hk f' hg') =
      (picardFunctor B hX hk f).map (transportHom B hX hX' hk f f' α hαf).op
        (Abel.univ B hX hk f hg) := by
  set T := curveObj B hX' hk f'
  set aO : curveOver B hX' hk f' ⟶ curveOver B hX hk f := Over.homMk α hαf
  haveI := isClosedImmersion_pointGraph_of_isSeparated (curveOver B hX' hk f')
    (curveOver B hX' hk f') (𝟙 _)
  haveI := isClosedImmersion_pointGraph_of_isSeparated (curveOver B hX hk f)
    (curveOver B hX hk f) (𝟙 _)
  let D : HilbertFamily (curveOver B hX hk f) (Over.mk (B.inclusion.map T.hom)) 1 :=
    Abel.Hilb.pointFamily (curveOver B hX hk f) rfl aO
  have h1 : (pointIdeal (curveOver B hX' hk f') (curveOver B hX' hk f') (𝟙 _)).comap
      (transportBase B hX hX' hk f f' α hαf T) = D.ideal :=
    Frob.pointIdeal_comap_of_comm (X := curveOver B hX' hk f') (X' := curveOver B hX hk f)
      (T := curveOver B hX' hk f') (T' := curveOver B hX' hk f') _ (inv α) (𝟙 _) (transportBase_fst B hX hX' hk f f' α hαf T)
      (transportBase_snd B hX hX' hk f f' α hαf T) _ _ (by
        show α ≫ inv α = 𝟙 _ ≫ 𝟙 _
        rw [IsIso.hom_inv_id, Category.comp_id])
  have h2 : (pointIdeal (curveOver B hX hk f) (curveOver B hX hk f) (𝟙 _)).comap
      (Stacks.PicardFunctor.baseChangeMap B hX hk f (transportHom B hX hX' hk f f' α hαf)) = D.ideal :=
    Frob.pointIdeal_comap_of_comm (X := curveOver B hX hk f) (X' := curveOver B hX hk f)
      (T := curveOver B hX hk f) (T' := curveOver B hX' hk f') _ (𝟙 _) (B.inclusion.map (transportHom B hX hX' hk f f' α hαf).left)
      (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _) _ _ (by
        show α ≫ 𝟙 _ = B.inclusion.map (B.inclusion.preimage (X := B.obj hX') (Y := B.obj hX) α) ≫
          𝟙 _
        erw [Functor.map_preimage]
        rfl)
  have i1 := (diagonalFamily B hX hk f).isEffectiveCartierDivisor_ideal
  have i2 := (diagonalFamily B hX' hk f').isEffectiveCartierDivisor_ideal
  have i3 := D.isEffectiveCartierDivisor_ideal
  have e1 := @Stacks.Divisors.schemePullbackClass_picardClass_of_eq_comap _ _
    (transportBase B hX hX' hk f f' α hαf T) (diagonalFamily B hX' hk f').ideal D.ideal i2 i3
    h1.symm
  have e2 := @Stacks.Divisors.schemePullbackClass_picardClass_of_eq_comap _ _
    (Stacks.PicardFunctor.baseChangeMap B hX hk f (transportHom B hX hX' hk f f' α hαf))
    (diagonalFamily B hX hk f).ideal D.ideal i1 i3 h2.symm
  rw [← Abel.familyClass_diagonalFamily B hX' hk f' hg',
    ← Abel.familyClass_diagonalFamily B hX hk f hg]
  refine (transportMap_toPicardFunctor B hX hX' hk f f' α hαf T _).trans ?_
  refine Eq.trans ?_ (toPicardFunctor_app_naturality B hX hk f
    (transportHom B hX hX' hk f f' α hαf) _)
  exact congrArg _ (e1.trans e2.symm)

include hσ hσ' hg hg' in
/-- **`N[c₀']_T = [c₀]_T`**, as `α` is pointed. -/
theorem transportMap_constClass (hασ : σ' ≫ α = σ) (T : BigFppfOver B (Spec (.of k)) hk) :
    (transportMap B hX hX' hk f f' α hαf).app (op T) (Abel.constClass B hX' hk f' σ' hσ' hg' T) =
      Abel.constClass B hX hk f σ hσ hg T := by
  have hb : Abel.basePt B hX' hk f' σ' hσ' ≫ transportHom B hX hX' hk f f' α hαf =
      Abel.basePt B hX hk f σ hσ := by
    apply Over.OverMorphism.ext
    apply B.inclusion.map_injective
    simp only [Over.comp_left, Functor.map_comp]
    erw [Functor.map_preimage, Functor.map_preimage, Functor.map_preimage]
    exact hασ
  rw [Abel.constClass, transportMap_naturality, transportMap_univ B hX hX' hk f f' α hαf hg hg',
    Abel.constClass, ← picardFunctor_map_comp_apply]
  rw [Abel.constPt, Abel.constPt, Category.assoc, hb]

/-! ### `e = aj'⁻¹ ≫ α ≫ aj` on `T`-points -/

/-- The transported morphism `e = aj'⁻¹ ≫ α ≫ aj : J' ⟶ J`. -/
def transport : (jacobianGrp B hX' hk f' σ' hσ').X ⟶ (jacobianGrp B hX hk f σ hσ).X :=
  haveI := Abel.isIso_abelJacobi_of_genus_eq_one B hX' hk f' σ' hσ' hg'
  inv (abelJacobi B hX' hk f' σ' hσ') ≫
    (Over.homMk α hαf : curveOver B hX' hk f' ⟶ curveOver B hX hk f) ≫
    abelJacobi B hX hk f σ hσ

theorem abelJacobi_comp_transport :
    abelJacobi B hX' hk f' σ' hσ' ≫ transport B hX hX' hk f f' α hαf σ' hσ' σ hσ hg' =
      (Over.homMk α hαf : curveOver B hX' hk f' ⟶ curveOver B hX hk f) ≫
        abelJacobi B hX hk f σ hσ := by
  haveI := Abel.isIso_abelJacobi_of_genus_eq_one B hX' hk f' σ' hσ' hg'
  rw [transport, IsIso.hom_inv_id_assoc]

include hσ hg in
/-- **On `T`-points, `e` is the transport map `N`.** -/
theorem jacobianHomAddEquiv_comp_transport (hασ : σ' ≫ α = σ)
    (T : BigFppfOver B (Spec (.of k)) hk)
    (z : (Over.post (X := B.obj hk) B.inclusion).obj T ⟶ (jacobianGrp B hX' hk f' σ' hσ').X) :
    ((jacobianHomAddEquiv B hX hk f σ hσ T
        (Additive.ofMul (z ≫ transport B hX hX' hk f f' α hαf σ' hσ' σ hσ hg'))) :
        (picardFunctor B hX hk f).obj (op T)) =
      (transportMap B hX hX' hk f f' α hαf).app (op T)
        (jacobianHomAddEquiv B hX' hk f' σ' hσ' T (Additive.ofMul z)) := by
  obtain ⟨m, hm⟩ := (Abel.bijective_comp_abelJacobi B hX' hk f' σ' hσ' hg'
    (Abel.degreeOneNormalized B hX' hk f' σ' hσ' hg') T).2 z
  change (Over.post (X := B.obj hk) B.inclusion).map m ≫ abelJacobi B hX' hk f' σ' hσ' = z at hm
  set tH := transportHom B hX hX' hk f f' α hαf
  have h4 := abelJacobi_comp_transport B hX hX' hk f f' α hαf σ' hσ' σ hσ hg'
  have h5 := post_map_transportHom B hX hX' hk f f' α hαf
  have e1 : z ≫ transport B hX hX' hk f f' α hαf σ' hσ' σ hσ hg' =
      (Over.post (X := B.obj hk) B.inclusion).map (m ≫ tH) ≫ abelJacobi B hX hk f σ hσ := by
    calc z ≫ transport B hX hX' hk f f' α hαf σ' hσ' σ hσ hg' =
        ((Over.post (X := B.obj hk) B.inclusion).map m ≫ abelJacobi B hX' hk f' σ' hσ') ≫
          transport B hX hX' hk f f' α hαf σ' hσ' σ hσ hg' :=
          congrArg (· ≫ transport B hX hX' hk f f' α hαf σ' hσ' σ hσ hg') hm.symm
      _ = (Over.post (X := B.obj hk) B.inclusion).map m ≫
          (abelJacobi B hX' hk f' σ' hσ' ≫ transport B hX hX' hk f f' α hαf σ' hσ' σ hσ hg') :=
          Category.assoc _ _ _
      _ = (Over.post (X := B.obj hk) B.inclusion).map m ≫
          ((Over.homMk α hαf : curveOver B hX' hk f' ⟶ curveOver B hX hk f) ≫
            abelJacobi B hX hk f σ hσ) := congrArg _ h4
      _ = ((Over.post (X := B.obj hk) B.inclusion).map m ≫
          (Over.post (X := B.obj hk) B.inclusion).map tH) ≫ abelJacobi B hX hk f σ hσ := by
          rw [h5]
          exact (Category.assoc _ _ _).symm
      _ = (Over.post (X := B.obj hk) B.inclusion).map (m ≫ tH) ≫ abelJacobi B hX hk f σ hσ := by
          rw [Functor.map_comp]
  have e2 := Abel.jacobianHomAddEquiv_comp_abelJacobi B hX hk f σ hσ hg (m ≫ tH)
  have e3 := Abel.jacobianHomAddEquiv_comp_abelJacobi B hX' hk f' σ' hσ' hg' m
  rw [e1]
  refine e2.trans ?_
  rw [← hm, e3, transportMap_sub B hX hX' hk f f' α hαf σ' hσ', transportMap_naturality,
    transportMap_univ B hX hX' hk f f' α hαf hg hg',
    transportMap_constClass B hX hX' hk f f' α hαf σ' hσ' σ hσ hg hg' hασ,
    picardFunctor_map_comp_apply]

/-! ### `e` is a homomorphism -/

section MonHom

attribute [local instance] CartesianMonoidalCategory.ofHasFiniteProducts

include hσ hg in
/-- The site-level form of `e`, on `T`-points. -/
theorem degreeZeroHomAddEquiv_comp_transport (hασ : σ' ≫ α = σ)
    {T : BigFppfOver B (Spec (.of k)) hk}
    (x : T ⟶ picardSchemeDegreeComponent B hX' hk f' σ' hσ' 0) :
    letI := jacobianGrpObj B hX' hk f' σ' hσ'
    letI := jacobianGrpObj B hX hk f σ hσ
    (degreeZeroHomAddEquiv B hX hk f σ hσ T (Additive.ofMul
        (x ≫ (fullyFaithful_overPost_bigFppfInclusion B (Spec (.of k)) hk).preimage
          (transport B hX hX' hk f f' α hαf σ' hσ' σ hσ hg'))) :
        (picardFunctor B hX hk f).obj (op T)) =
      (transportMap B hX hX' hk f f' α hαf).app (op T)
        (degreeZeroHomAddEquiv B hX' hk f' σ' hσ' T (Additive.ofMul x)) := by
  let hF := fullyFaithful_overPost_bigFppfInclusion B (Spec (.of k)) hk
  set e := transport B hX hX' hk f f' α hαf σ' hσ' σ hσ hg'
  have h := jacobianHomAddEquiv_comp_transport B hX hX' hk f f' α hαf σ' hσ' σ hσ hg hg' hασ T
    ((Over.post (X := B.obj hk) B.inclusion).map x)
  have h1 : hF.preimage ((Over.post (X := B.obj hk) B.inclusion).map x ≫ e) =
      x ≫ hF.preimage e :=
    hF.map_injective (by
      rw [hF.map_preimage, Functor.map_comp]
      exact congrArg (fun t => (Over.post (X := B.obj hk) B.inclusion).map x ≫ t)
        (hF.map_preimage e).symm)
  have h2 : hF.preimage ((Over.post (X := B.obj hk) B.inclusion).map x) = x := hF.preimage_map x
  change (degreeZeroHomAddEquiv B hX hk f σ hσ T (Additive.ofMul
      (hF.preimage ((Over.post (X := B.obj hk) B.inclusion).map x ≫ e))) :
        (picardFunctor B hX hk f).obj (op T)) =
    (transportMap B hX hX' hk f f' α hαf).app (op T)
      (degreeZeroHomAddEquiv B hX' hk f' σ' hσ' T (Additive.ofMul
        (hF.preimage ((Over.post (X := B.obj hk) B.inclusion).map x)))) at h
  rwa [h1, h2] at h

include hσ hg in
/-- **G1.2 (site level)**: the transported morphism is a homomorphism of group objects. -/
theorem isMonHom_transport_site (hασ : σ' ≫ α = σ) :
    letI := jacobianGrpObj B hX' hk f' σ' hσ'
    letI := jacobianGrpObj B hX hk f σ hσ
    IsMonHom ((fullyFaithful_overPost_bigFppfInclusion B (Spec (.of k)) hk).preimage
      (transport B hX hX' hk f f' α hαf σ' hσ' σ hσ hg')) := by
  letI := jacobianGrpObj B hX' hk f' σ' hσ'
  letI := jacobianGrpObj B hX hk f σ hσ
  set e₀ := (fullyFaithful_overPost_bigFppfInclusion B (Spec (.of k)) hk).preimage
      (transport B hX hX' hk f f' α hαf σ' hσ' σ hσ hg')
  set N := transportMap B hX hX' hk f f' α hαf
  have key : ∀ {T : BigFppfOver B (Spec (.of k)) hk}
      (x : T ⟶ picardSchemeDegreeComponent B hX' hk f' σ' hσ' 0)
      (y : T ⟶ picardSchemeDegreeComponent B hX hk f σ hσ 0)
      (h : N.app (op T) (degreeZeroHomAddEquiv B hX' hk f' σ' hσ' T (Additive.ofMul x) :
          (picardFunctor B hX' hk f').obj (op T)) =
        degreeZeroHomAddEquiv B hX hk f σ hσ T (Additive.ofMul y)), x ≫ e₀ = y := by
    intro T x y h
    apply Additive.ofMul.injective
    apply (degreeZeroHomAddEquiv B hX hk f σ hσ T).injective
    apply Subtype.ext
    rw [degreeZeroHomAddEquiv_comp_transport B hX hX' hk f f' α hαf σ' hσ' σ hσ hg hg' hασ x, h]
  constructor
  · refine key _ _ ?_
    have h1 : (η[picardSchemeDegreeComponent B hX' hk f' σ' hσ' 0] :
        𝟙_ (BigFppfOver B (Spec (.of k)) hk) ⟶ _) = 1 := by
      rw [CategoryTheory.Hom.one_def, toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]
    have h2 : (η[picardSchemeDegreeComponent B hX hk f σ hσ 0] :
        𝟙_ (BigFppfOver B (Spec (.of k)) hk) ⟶ _) = 1 := by
      rw [CategoryTheory.Hom.one_def, toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]
    simp only [h1, h2, ofMul_one, map_zero, ZeroMemClass.coe_zero]
    exact transportMap_zero B hX hX' hk f f' α hαf σ' hσ' _
  · have hμ : (μ[picardSchemeDegreeComponent B hX' hk f' σ' hσ' 0]) = fst _ _ * snd _ _ := by
      rw [CategoryTheory.Hom.mul_def, lift_fst_snd, Category.id_comp]
    have hFF : (e₀ ⊗ₘ e₀) ≫ μ[picardSchemeDegreeComponent B hX hk f σ hσ 0] =
        (fst _ _ ≫ e₀) * (snd _ _ ≫ e₀) := by
      rw [CategoryTheory.Hom.mul_def]
      congr 1
    rw [hFF]
    refine key _ _ ?_
    rw [hμ, ofMul_mul, ofMul_mul, map_add, map_add, AddSubgroup.coe_add, AddSubgroup.coe_add,
      transportMap_add B hX hX' hk f f' α hαf σ' hσ',
      ← degreeZeroHomAddEquiv_comp_transport B hX hX' hk f f' α hαf σ' hσ' σ hσ hg hg' hασ,
      ← degreeZeroHomAddEquiv_comp_transport B hX hX' hk f f' α hαf σ' hσ' σ hσ hg hg' hασ]

end MonHom

section MonHomOver

include hσ hg in
attribute [local instance] CartesianMonoidalCategory.ofHasFiniteProducts
  Functor.Monoidal.ofChosenFiniteProducts in
theorem isMonHom_transport_aux (hασ : σ' ≫ α = σ) :
    IsMonHom (transport B hX hX' hk f f' α hαf σ' hσ' σ hσ hg') := by
  haveI := preservesFiniteProducts_overPost_bigFppfInclusion B (Spec (.of k)) hk
  letI := jacobianGrpObj B hX' hk f' σ' hσ'
  letI := jacobianGrpObj B hX hk f σ hσ
  haveI := isMonHom_transport_site B hX hX' hk f f' α hαf σ' hσ' σ hσ hg hg' hασ
  have h := Functor.map.instIsMonHom (F := Over.post (X := B.obj hk) B.inclusion)
    (f := (fullyFaithful_overPost_bigFppfInclusion B (Spec (.of k)) hk).preimage
      (transport B hX hX' hk f f' α hαf σ' hσ' σ hσ hg'))
  have e := (fullyFaithful_overPost_bigFppfInclusion B (Spec (.of k)) hk).map_preimage
    (transport B hX hX' hk f f' α hαf σ' hσ' σ hσ hg')
  first
  | (rw [← e]; exact h)
  | exact e ▸ h
  | (convert h using 2; exact e.symm)

include hσ hg in
/-- **G1.2: rigidity in dimension one.** For pointed genus-one curves `X, X'` and a pointed
`k`-isomorphism `α : X' ≅ X`, the transported map `aj'⁻¹ ≫ α ≫ aj : J' ⟶ J` is a
homomorphism of group objects. -/
theorem isMonHom_transport (hασ : σ' ≫ α = σ) :
    IsMonHom (transport B hX hX' hk f f' α hαf σ' hσ' σ hσ hg') :=
  isMonHom_transport_aux B hX hX' hk f f' α hαf σ' hσ' σ hσ hg hg' hασ

end MonHomOver

end Rigid

end RamanujanWeil.Arith.Deuring.Geom
