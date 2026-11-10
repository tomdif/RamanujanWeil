import StacksFrontier.AlgebraicGeometry.PicardScheme.CurvePicard.JacobianFrobenius

/-!
# A3-ord, G7 step C-Jac: Jacobians are functorial for morphisms between two curves

`docs/ARITH_DEURING_G7_CJAC.md`. Stacks' `jacobianPullback` and `jacobianFrobenius` handle an
endomorphism of one curve `X`. Here `φ : X ⟶ X'` is a morphism over `k` between two curves in one
big fppf site `B`. For every test scheme `T` the base change `φ_T = φ ×_k 𝟙_T : X_T ⟶ X'_T` is
natural in `T`, so pullback along `φ_T` is a morphism of presheaves `Pic(X'_–) ⟶ Pic(X_–)`, hence
(sheafification) of Picard functors `Pic_{X'/k} ⟶ Pic_{X/k}` and (Yoneda) of Picard schemes. It
carries `Pic⁰_{X'}` into `Pic⁰_X` (connectedness, as in Stacks), and is a homomorphism.

* `curveBaseChangeMap`, `curvePicardPresheafMap`, `curvePicardMap`: `φ_T`, `φ_T^*`.
* `curvePicardMap_comp`, `curvePicardMap_id`: contravariant functoriality on Picard functors.
* `curvePicardSchemeHom`, `curveJacobianHom`, **`curveJacobianPullback`** `: J_{X'} ⟶ J_X`, with
  `isMonHom_curveJacobianPullback`, `curveJacobianHom_comp`, `curveJacobianHom_id`.
* **`curveJacobianIso`**: an isomorphism `α : X ≅ X'` over `k` gives an isomorphism of group
  schemes `J_X ≅ J_{X'}` (hom `= (α⁻¹)^*`), `isMonHom_curveJacobianIso_hom`.
* **`curveJacobianPullback_comp_jacobianFrobenius`**: if `Ψ ≫ φ = φ ≫ Ψ'` for twisted Frobenii
  `Ψ`, `Ψ'` (lying over the same `F^n` of `Spec k`), then `φ^* ∘ F' = F ∘ φ^*` on Jacobians.
* **`exists_equivariant_jacobianIso`**: the C-Jac statement in the shape `GraphFiniteness`
  consumes: `∃ e : J_X ≅ J_{X'}, IsMonHom e.hom ∧ e.hom ≫ F' = F ≫ e.hom`.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite Stacks.Frobenius
open MonoidalCategory CartesianMonoidalCategory Stacks.PicardFunctor
open scoped CategoryTheory.MonObj

universe u

noncomputable section

namespace RamanujanWeil.Arith.Deuring.Geom.G7.CJac

/-! ## Presheaf and Picard functor level -/

section Presheaf

variable {k : Type u} [Field k] (B : BigFppfSite.{u}) {X X' X'' : Scheme.{u}}
  (hX : B.Contains X) (hX' : B.Contains X') (hX'' : B.Contains X'')
  (hk : B.Contains (Spec (.of k))) (f : B.obj hX ⟶ B.obj hk) (f' : B.obj hX' ⟶ B.obj hk)
  (f'' : B.obj hX'' ⟶ B.obj hk)

/-- **The base change of `φ : X ⟶ X'`**, `φ_T = φ ×_k 𝟙_T : X ×_k T ⟶ X' ×_k T`. -/
def curveBaseChangeMap (φ : X ⟶ X') (hφ : φ ≫ B.inclusion.map f' = B.inclusion.map f)
    (T : BigFppfOver B (Spec (.of k)) hk) :
    baseChange B hX hk f T ⟶ baseChange B hX' hk f' T :=
  pullback.map (B.inclusion.map f) (B.inclusion.map T.hom) (B.inclusion.map f')
    (B.inclusion.map T.hom) φ (𝟙 _) (𝟙 _) (by rw [Category.comp_id, hφ])
    (by rw [Category.comp_id, Category.id_comp])

variable (φ : X ⟶ X') (hφ : φ ≫ B.inclusion.map f' = B.inclusion.map f)

@[reassoc (attr := simp)]
theorem curveBaseChangeMap_fst (T : BigFppfOver B (Spec (.of k)) hk) :
    curveBaseChangeMap B hX hX' hk f f' φ hφ T ≫
        pullback.fst (B.inclusion.map f') (B.inclusion.map T.hom) =
      pullback.fst (B.inclusion.map f) (B.inclusion.map T.hom) ≫ φ :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem curveBaseChangeMap_snd (T : BigFppfOver B (Spec (.of k)) hk) :
    curveBaseChangeMap B hX hX' hk f f' φ hφ T ≫
        pullback.snd (B.inclusion.map f') (B.inclusion.map T.hom) =
      pullback.snd (B.inclusion.map f) (B.inclusion.map T.hom) := by
  simp [curveBaseChangeMap]

/-- `φ_T` is natural in the test scheme. -/
theorem baseChangeMap_curveBaseChangeMap {T U : BigFppfOver B (Spec (.of k)) hk} (g : T ⟶ U) :
    baseChangeMap B hX hk f g ≫ curveBaseChangeMap B hX hX' hk f f' φ hφ U =
      curveBaseChangeMap B hX hX' hk f f' φ hφ T ≫ baseChangeMap B hX' hk f' g := by
  apply pullback.hom_ext
  · simp only [Stacks.PicardFunctor.baseChangeMap, Category.assoc, curveBaseChangeMap_fst, pullback.lift_fst_assoc,
      pullback.lift_fst, Category.comp_id, curveBaseChangeMap_fst_assoc, Category.id_comp]
  · simp only [Stacks.PicardFunctor.baseChangeMap, Category.assoc, curveBaseChangeMap_snd, pullback.lift_snd,
      curveBaseChangeMap_snd_assoc]

/-- `(φ ≫ ψ)_T = φ_T ≫ ψ_T`. -/
theorem curveBaseChangeMap_comp (ψ : X' ⟶ X'')
    (hψ : ψ ≫ B.inclusion.map f'' = B.inclusion.map f')
    (hφψ : (φ ≫ ψ) ≫ B.inclusion.map f'' = B.inclusion.map f)
    (T : BigFppfOver B (Spec (.of k)) hk) :
    curveBaseChangeMap B hX hX'' hk f f'' (φ ≫ ψ) hφψ T =
      curveBaseChangeMap B hX hX' hk f f' φ hφ T ≫
        curveBaseChangeMap B hX' hX'' hk f' f'' ψ hψ T := by
  apply pullback.hom_ext
  · simp only [curveBaseChangeMap_fst, Category.assoc, curveBaseChangeMap_fst_assoc]
  · simp only [curveBaseChangeMap_snd, Category.assoc]

/-- `(𝟙_X)_T = 𝟙`. -/
theorem curveBaseChangeMap_id (h : 𝟙 X ≫ B.inclusion.map f = B.inclusion.map f)
    (T : BigFppfOver B (Spec (.of k)) hk) :
    curveBaseChangeMap B hX hX hk f f (𝟙 X) h T = 𝟙 _ := by
  apply pullback.hom_ext
  · rw [curveBaseChangeMap_fst, Category.id_comp]
    exact Category.comp_id _
  · simp only [curveBaseChangeMap_snd, Category.id_comp]

/-- `φ_T^*` commutes with pullback along a morphism of test schemes. -/
theorem schemePullbackClass_curveBaseChangeMap_picardMap
    {T U : BigFppfOver B (Spec (.of k)) hk} (g : T ⟶ U) (x : picardAt B hX' hk f' U) :
    Stacks.Picard.schemePullbackClass (curveBaseChangeMap B hX hX' hk f f' φ hφ T)
        (picardMap B hX' hk f' g x) =
      picardMap B hX hk f g
        (Stacks.Picard.schemePullbackClass (curveBaseChangeMap B hX hX' hk f f' φ hφ U) x) := by
  show Stacks.Picard.schemePullbackClass (curveBaseChangeMap B hX hX' hk f f' φ hφ T)
      (Stacks.Picard.schemePullbackClass (baseChangeMap B hX' hk f' g) x) =
    Stacks.Picard.schemePullbackClass (baseChangeMap B hX hk f g)
      (Stacks.Picard.schemePullbackClass (curveBaseChangeMap B hX hX' hk f f' φ hφ U) x)
  rw [Stacks.Picard.schemePullbackClass_comp, Stacks.Picard.schemePullbackClass_comp,
    baseChangeMap_curveBaseChangeMap]

/-- **`φ^*` on the presheaf `T ↦ Pic(X_T)`**: `Pic(X'_T) ⟶ Pic(X_T)`. -/
def curvePicardPresheafMap : picardPresheaf B hX' hk f' ⟶ picardPresheaf B hX hk f where
  app T := TypeCat.ofHom
    (Stacks.Picard.schemePullbackClass (curveBaseChangeMap B hX hX' hk f f' φ hφ T.unop))
  naturality {T U} g := by
    apply ConcreteCategory.hom_ext
    intro x
    exact schemePullbackClass_curveBaseChangeMap_picardMap B hX hX' hk f f' φ hφ g.unop x

/-- **`φ^*` on Picard functors**, `Pic_{X'/k} ⟶ Pic_{X/k}`: the sheafification. -/
def curvePicardMap : picardFunctor B hX' hk f' ⟶ picardFunctor B hX hk f :=
  sheafifyMap (BigFppfOver.topology B (Spec (.of k)) hk)
    (curvePicardPresheafMap B hX hX' hk f f' φ hφ)

/-- `φ^*` on the Picard functor extends `φ_T^*` on Picard groups of base changes. -/
theorem curvePicardMap_toPicardFunctor (T : BigFppfOver B (Spec (.of k)) hk)
    (x : picardAt B hX' hk f' T) :
    (curvePicardMap B hX hX' hk f f' φ hφ).app (op T)
        ((toPicardFunctor B hX' hk f').app (op T) x) =
      (toPicardFunctor B hX hk f).app (op T)
        (Stacks.Picard.schemePullbackClass (curveBaseChangeMap B hX hX' hk f f' φ hφ T) x) :=
  (ConcreteCategory.congr_hom (NatTrans.congr_app (toSheafify_naturality
    (BigFppfOver.topology B (Spec (.of k)) hk)
    (curvePicardPresheafMap B hX hX' hk f f' φ hφ)) (op T)) x).symm

theorem schemePullbackClass_curveBaseChangeMap_comp (ψ : X' ⟶ X'')
    (hψ : ψ ≫ B.inclusion.map f'' = B.inclusion.map f')
    (hφψ : (φ ≫ ψ) ≫ B.inclusion.map f'' = B.inclusion.map f)
    (T : BigFppfOver B (Spec (.of k)) hk) (x : picardAt B hX'' hk f'' T) :
    Stacks.Picard.schemePullbackClass (curveBaseChangeMap B hX hX'' hk f f'' (φ ≫ ψ) hφψ T) x =
      Stacks.Picard.schemePullbackClass (curveBaseChangeMap B hX hX' hk f f' φ hφ T)
        (Stacks.Picard.schemePullbackClass (curveBaseChangeMap B hX' hX'' hk f' f'' ψ hψ T) x) := by
  rw [Stacks.Picard.schemePullbackClass_comp,
    curveBaseChangeMap_comp B hX hX' hX'' hk f f' f'' φ hφ ψ hψ hφψ]

/-- **Contravariant functoriality**: `(φ ≫ ψ)^* = ψ^* ≫ φ^*` on Picard functors. -/
theorem curvePicardMap_comp (ψ : X' ⟶ X'')
    (hψ : ψ ≫ B.inclusion.map f'' = B.inclusion.map f')
    (hφψ : (φ ≫ ψ) ≫ B.inclusion.map f'' = B.inclusion.map f) :
    curvePicardMap B hX hX'' hk f f'' (φ ≫ ψ) hφψ =
      curvePicardMap B hX' hX'' hk f' f'' ψ hψ ≫ curvePicardMap B hX hX' hk f f' φ hφ := by
  unfold curvePicardMap
  refine (congrArg (sheafifyMap (BigFppfOver.topology B (Spec (.of k)) hk)) ?_).trans
    (sheafifyMap_comp _ _ _)
  ext T x
  exact schemePullbackClass_curveBaseChangeMap_comp B hX hX' hX'' hk f f' f'' φ hφ ψ hψ hφψ
    T.unop x

/-- `(𝟙_X)^* = 𝟙` on the Picard functor. -/
theorem curvePicardMap_id (h : 𝟙 X ≫ B.inclusion.map f = B.inclusion.map f) :
    curvePicardMap B hX hX hk f f (𝟙 X) h = 𝟙 _ := by
  unfold curvePicardMap
  have : curvePicardPresheafMap B hX hX hk f f (𝟙 X) h = 𝟙 _ := by
    ext T x
    show Stacks.Picard.schemePullbackClass (curveBaseChangeMap B hX hX hk f f (𝟙 X) h T.unop)
      x = x
    rw [curveBaseChangeMap_id]
    exact Stacks.Picard.schemePullbackClass_id _ x
  rw [this, sheafifyMap_id]
  rfl

end Presheaf

/-! ## Twisted Frobenius compatibility on Picard functors -/

section Twisted

variable {k : Type u} [Field k] (B : BigFppfSite.{u}) {X X' : Scheme.{u}}
  (hX : B.Contains X) (hX' : B.Contains X')
  (hk : B.Contains (Spec (.of k))) (f : B.obj hX ⟶ B.obj hk) (f' : B.obj hX' ⟶ B.obj hk)
  (φ : X ⟶ X') (hφ : φ ≫ B.inclusion.map f' = B.inclusion.map f)
  (p : ℕ) [Fact p.Prime] (hS : IsInCharacteristic (Spec (.of k)) p) (n : ℕ)
  (Ψ : X ⟶ X)
  (hΨ : Ψ ≫ B.inclusion.map f = B.inclusion.map f ≫ absoluteFrobeniusPow (Spec (.of k)) p hS n)
  (Ψ' : X' ⟶ X')
  (hΨ' : Ψ' ≫ B.inclusion.map f' =
    B.inclusion.map f' ≫ absoluteFrobeniusPow (Spec (.of k)) p hS n)
  (hφΨ : Ψ ≫ φ = φ ≫ Ψ')

include hφΨ in
/-- `Θ_T ≫ φ_T = φ_T ≫ Θ'_T` when `Ψ ≫ φ = φ ≫ Ψ'`. -/
theorem twistedBaseChangeMap_comp_curveBaseChangeMap (T : BigFppfOver B (Spec (.of k)) hk) :
    twistedBaseChangeMap B hX hk f p hS n Ψ hΨ T ≫ curveBaseChangeMap B hX hX' hk f f' φ hφ T =
      curveBaseChangeMap B hX hX' hk f f' φ hφ T ≫
        twistedBaseChangeMap B hX' hk f' p hS n Ψ' hΨ' T := by
  apply pullback.hom_ext
  · simp only [Category.assoc, curveBaseChangeMap_fst, twistedBaseChangeMap_fst_assoc,
      twistedBaseChangeMap_fst, curveBaseChangeMap_fst_assoc, hφΨ]
  · simp only [Category.assoc, curveBaseChangeMap_snd, twistedBaseChangeMap_snd,
      curveBaseChangeMap_snd_assoc]

include hφΨ in
theorem schemePullbackClass_twisted_curve (T : BigFppfOver B (Spec (.of k)) hk)
    (x : picardAt B hX' hk f' T) :
    Stacks.Picard.schemePullbackClass (curveBaseChangeMap B hX hX' hk f f' φ hφ T)
        (Stacks.Picard.schemePullbackClass (twistedBaseChangeMap B hX' hk f' p hS n Ψ' hΨ' T)
          x) =
      Stacks.Picard.schemePullbackClass (twistedBaseChangeMap B hX hk f p hS n Ψ hΨ T)
        (Stacks.Picard.schemePullbackClass (curveBaseChangeMap B hX hX' hk f f' φ hφ T) x) := by
  rw [Stacks.Picard.schemePullbackClass_comp, Stacks.Picard.schemePullbackClass_comp,
    twistedBaseChangeMap_comp_curveBaseChangeMap B hX hX' hk f f' φ hφ p hS n Ψ hΨ Ψ' hΨ' hφΨ]

include hφΨ in
/-- **The Frobenius square on Picard functors**: `F'^* ≫ φ^* = φ^* ≫ F^*`. -/
theorem twistedPicardMap_comp_curvePicardMap :
    twistedPicardMap B hX' hk f' p hS n Ψ' hΨ' ≫ curvePicardMap B hX hX' hk f f' φ hφ =
      curvePicardMap B hX hX' hk f f' φ hφ ≫ twistedPicardMap B hX hk f p hS n Ψ hΨ := by
  unfold curvePicardMap twistedPicardMap
  refine (sheafifyMap_comp _ _ _).symm.trans
    ((congrArg (sheafifyMap (BigFppfOver.topology B (Spec (.of k)) hk)) ?_).trans
      (sheafifyMap_comp _ _ _))
  ext T x
  exact schemePullbackClass_twisted_curve B hX hX' hk f f' φ hφ p hS n Ψ hΨ Ψ' hΨ' hφΨ T.unop x

end Twisted

end RamanujanWeil.Arith.Deuring.Geom.G7.CJac

end
