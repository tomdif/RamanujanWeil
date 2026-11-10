import RamanujanWeil.Arith.DeuringG7CJacPic0

/-!
# A3-ord, G7 step C-Jac: `C ≅ C′ ⇒ Jac C ≅ Jac C′`, Frobenius-equivariantly

`docs/ARITH_DEURING_G7_CJAC.md`. Continues `DeuringG7CJacPic0`.

* `curveJacobianHom_comp`, `curveJacobianHom_id`: `φ ↦ φ^*` is a contravariant functor on `Pic⁰`.
* `curveJacobianHom_comp_twistedJacobianHom`: the Frobenius square on `Pic⁰`.
* `curveJacobianPullback : J_{X'} ⟶ J_X` over `Spec k`, a homomorphism.
* **`curveJacobianIso`**: `α : X ≅ X'` over `k` gives `J_X ≅ J_{X'}` with `hom = (α⁻¹)^*`.
* **`curveJacobianPullback_comp_jacobianFrobenius`**: `φ^* ≫ F_X = F_{X'} ≫ φ^*` when
  `Ψ ≫ φ = φ ≫ Ψ'`.
* **`exists_equivariant_jacobianIso`** (C-Jac): `α : X ≅ X'` over `k` with `α ≫ Ψ' = Ψ ≫ α`
  gives `e : J_X ≅ J_{X'}` with `IsMonHom e.hom` and `e.hom ≫ F_{X'} = F_X ≫ e.hom`.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite Stacks.Frobenius
open MonoidalCategory CartesianMonoidalCategory Stacks.PicardFunctor
open scoped CategoryTheory.MonObj

universe u

noncomputable section

namespace RamanujanWeil.Arith.Deuring.Geom.G7.CJac

section Functor

variable {k : Type u} [Field k] (B : BigFppfSite.{u}) {X X' X'' : Scheme.{u}}
  (hX : B.Contains X) (hX' : B.Contains X') (hX'' : B.Contains X'')
  (hk : B.Contains (Spec (.of k))) (f : B.obj hX ⟶ B.obj hk) (f' : B.obj hX' ⟶ B.obj hk)
  (f'' : B.obj hX'' ⟶ B.obj hk)
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

omit [IsCurve k (B.inclusion.map f')] [GeometricallyIrreducible (B.inclusion.map f')]
  [Smooth (B.inclusion.map f')] [IsProper (B.inclusion.map f')]
  [IsProjectiveVariety k (B.inclusion.map f')] [(picardFunctor B hX' hk f').IsRepresentable] in
attribute [local instance] CartesianMonoidalCategory.ofHasFiniteProducts in
/-- Yoneda form of `pic0_hom_ext`: test against every `x : T ⟶ A`. -/
theorem pic0_hom_ext' {A : BigFppfOver B (Spec (.of k)) hk}
    (g h : A ⟶ picardSchemeDegreeComponent B hX hk f σ hσ 0)
    (H : ∀ {T : BigFppfOver B (Spec (.of k)) hk} (x : T ⟶ A),
      letI := jacobianGrpObj B hX hk f σ hσ
      (degreeZeroHomAddEquiv B hX hk f σ hσ T (Additive.ofMul (x ≫ g)) :
          (picardFunctor B hX hk f).obj (op T)) =
        degreeZeroHomAddEquiv B hX hk f σ hσ T (Additive.ofMul (x ≫ h))) : g = h := by
  have := H (𝟙 A)
  rw [Category.id_comp, Category.id_comp] at this
  exact pic0_hom_ext B hX hk f σ hσ g h this

omit [IsCurve k (B.inclusion.map f')] [GeometricallyIrreducible (B.inclusion.map f')]
  [Smooth (B.inclusion.map f')] [IsProper (B.inclusion.map f')]
  [IsProjectiveVariety k (B.inclusion.map f')] [(picardFunctor B hX' hk f').IsRepresentable] in
attribute [local instance] CartesianMonoidalCategory.ofHasFiniteProducts in
/-- `(𝟙_X)^* = 𝟙` on `Pic⁰_X`. -/
theorem curveJacobianHom_id (h : 𝟙 X ≫ B.inclusion.map f = B.inclusion.map f) :
    curveJacobianHom B hX hX hk f f (𝟙 X) h σ hσ σ hσ = 𝟙 _ := by
  refine pic0_hom_ext' B hX hk f σ hσ _ _ fun {T} x => ?_
  rw [degreeZeroHomAddEquiv_comp_curveJacobianHom, curvePicardMap_id, Category.comp_id]
  rfl

omit [IsCurve k (B.inclusion.map f')] [GeometricallyIrreducible (B.inclusion.map f')]
  [Smooth (B.inclusion.map f')] [IsProper (B.inclusion.map f')]
  [IsProjectiveVariety k (B.inclusion.map f')] [(picardFunctor B hX' hk f').IsRepresentable] in
theorem curveJacobianHom_eq_id (φ : X ⟶ X) (hφ : φ ≫ B.inclusion.map f = B.inclusion.map f)
    (h : φ = 𝟙 X) : curveJacobianHom B hX hX hk f f φ hφ σ hσ σ hσ = 𝟙 _ := by
  subst h
  exact curveJacobianHom_id B hX hk f σ hσ hφ

variable [IsCurve k (B.inclusion.map f'')] [GeometricallyIrreducible (B.inclusion.map f'')]
  [Smooth (B.inclusion.map f'')] [IsProper (B.inclusion.map f'')]
  [IsProjectiveVariety k (B.inclusion.map f'')]
  (σ'' : Spec (.of k) ⟶ X'') (hσ'' : σ'' ≫ B.inclusion.map f'' = 𝟙 (Spec (.of k)))
  [(picardFunctor B hX'' hk f'').IsRepresentable]

attribute [local instance] CartesianMonoidalCategory.ofHasFiniteProducts in
/-- **Contravariant functoriality on `Pic⁰`**: `(φ ≫ ψ)^* = ψ^* ≫ φ^*`. -/
theorem curveJacobianHom_comp (φ : X ⟶ X') (hφ : φ ≫ B.inclusion.map f' = B.inclusion.map f)
    (ψ : X' ⟶ X'') (hψ : ψ ≫ B.inclusion.map f'' = B.inclusion.map f')
    (hφψ : (φ ≫ ψ) ≫ B.inclusion.map f'' = B.inclusion.map f) :
    curveJacobianHom B hX hX'' hk f f'' (φ ≫ ψ) hφψ σ hσ σ'' hσ'' =
      curveJacobianHom B hX' hX'' hk f' f'' ψ hψ σ' hσ' σ'' hσ'' ≫
        curveJacobianHom B hX hX' hk f f' φ hφ σ hσ σ' hσ' := by
  refine pic0_hom_ext' B hX hk f σ hσ _ _ fun {T} x => ?_
  rw [degreeZeroHomAddEquiv_comp_curveJacobianHom B hX hX'' hk f f'' (φ ≫ ψ) hφψ σ hσ σ'' hσ'',
    ← Category.assoc,
    degreeZeroHomAddEquiv_comp_curveJacobianHom B hX hX' hk f f' φ hφ σ hσ σ' hσ',
    degreeZeroHomAddEquiv_comp_curveJacobianHom B hX' hX'' hk f' f'' ψ hψ σ' hσ' σ'' hσ'',
    curvePicardMap_comp B hX hX' hX'' hk f f' f'' φ hφ ψ hψ hφψ]
  rfl

end Functor

section Frobenius

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
  (p : ℕ) [Fact p.Prime] (hS : IsInCharacteristic (Spec (.of k)) p) (n : ℕ)
  (Ψ : X ⟶ X)
  (hΨ : Ψ ≫ B.inclusion.map f = B.inclusion.map f ≫ absoluteFrobeniusPow (Spec (.of k)) p hS n)
  (Ψ' : X' ⟶ X')
  (hΨ' : Ψ' ≫ B.inclusion.map f' =
    B.inclusion.map f' ≫ absoluteFrobeniusPow (Spec (.of k)) p hS n)
  (hφΨ : Ψ ≫ φ = φ ≫ Ψ')

include hφΨ in
attribute [local instance] CartesianMonoidalCategory.ofHasFiniteProducts in
/-- **The Frobenius square on `Pic⁰`**: `φ^* ≫ F_X = F_{X'} ≫ φ^*`. -/
theorem curveJacobianHom_comp_twistedJacobianHom :
    curveJacobianHom B hX hX' hk f f' φ hφ σ hσ σ' hσ' ≫
        twistedJacobianHom B hX hk f p hS n Ψ hΨ σ hσ =
      twistedJacobianHom B hX' hk f' p hS n Ψ' hΨ' σ' hσ' ≫
        curveJacobianHom B hX hX' hk f f' φ hφ σ hσ σ' hσ' := by
  refine pic0_hom_ext' B hX hk f σ hσ _ _ fun {T} x => ?_
  rw [← Category.assoc, ← Category.assoc, degreeZeroHomAddEquiv_comp_twistedJacobianHom,
    degreeZeroHomAddEquiv_comp_curveJacobianHom, degreeZeroHomAddEquiv_comp_curveJacobianHom,
    degreeZeroHomAddEquiv_comp_twistedJacobianHom]
  have hsq := twistedPicardMap_comp_curvePicardMap B hX hX' hk f f' φ hφ p hS n Ψ hΨ Ψ' hΨ' hφΨ
  letI := jacobianGrpObj B hX' hk f' σ' hσ'
  exact (ConcreteCategory.congr_hom (NatTrans.congr_app hsq (op T))
    (degreeZeroHomAddEquiv B hX' hk f' σ' hσ' T (Additive.ofMul x) :
      (picardFunctor B hX' hk f').obj (op T))).symm

/-- **`φ^* : J_{X'} ⟶ J_X`** over `Spec k`. -/
def curveJacobianPullback :
    (jacobianGrp B hX' hk f' σ' hσ').X ⟶ (jacobianGrp B hX hk f σ hσ).X :=
  (Over.post (X := B.obj hk) B.inclusion).map (curveJacobianHom B hX hX' hk f f' φ hφ σ hσ σ' hσ')

attribute [local instance] CartesianMonoidalCategory.ofHasFiniteProducts
  Functor.Monoidal.ofChosenFiniteProducts in
/-- `φ^*` on Jacobians is a homomorphism. -/
instance isMonHom_curveJacobianPullback :
    IsMonHom (curveJacobianPullback B hX hX' hk f f' φ hφ σ hσ σ' hσ') := by
  haveI := preservesFiniteProducts_overPost_bigFppfInclusion B (Spec (.of k)) hk
  letI := jacobianGrpObj B hX hk f σ hσ
  letI := jacobianGrpObj B hX' hk f' σ' hσ'
  haveI := isMonHom_curveJacobianHom B hX hX' hk f f' φ hφ σ hσ σ' hσ'
  exact Functor.map.instIsMonHom (F := Over.post (X := B.obj hk) B.inclusion)
    (f := curveJacobianHom B hX hX' hk f f' φ hφ σ hσ σ' hσ')

include hφΨ in
/-- **Frobenius compatibility on Jacobians**: `φ^* ≫ F_X = F_{X'} ≫ φ^*`. -/
theorem curveJacobianPullback_comp_jacobianFrobenius :
    curveJacobianPullback B hX hX' hk f f' φ hφ σ hσ σ' hσ' ≫
        jacobianFrobenius B hX hk f p hS n Ψ hΨ σ hσ =
      jacobianFrobenius B hX' hk f' p hS n Ψ' hΨ' σ' hσ' ≫
        curveJacobianPullback B hX hX' hk f f' φ hφ σ hσ σ' hσ' := by
  have h := congrArg (fun g => (Over.post (X := B.obj hk) B.inclusion).map g)
    (curveJacobianHom_comp_twistedJacobianHom B hX hX' hk f f' φ hφ σ hσ σ' hσ' p hS n Ψ hΨ Ψ'
      hΨ' hφΨ)
  simp only [Functor.map_comp] at h
  exact h

end Frobenius

section Iso

variable {k : Type u} [Field k] (B : BigFppfSite.{u}) {X X' : Scheme.{u}}
  (hX : B.Contains X) (hX' : B.Contains X')
  (hk : B.Contains (Spec (.of k))) (f : B.obj hX ⟶ B.obj hk) (f' : B.obj hX' ⟶ B.obj hk)
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
  (α : X ≅ X') (hα : α.hom ≫ B.inclusion.map f' = B.inclusion.map f)

include hα in
theorem inv_comp_of_hom_comp : α.inv ≫ B.inclusion.map f = B.inclusion.map f' := by
  rw [Iso.inv_comp_eq, hα]

/-- **C-Jac (isomorphism).** An isomorphism `α : X ≅ X'` of curves over `k` (in a common site)
gives an isomorphism of Jacobians `J_X ≅ J_{X'}`, with `hom = (α⁻¹)^*` and `inv = α^*`. -/
def curveJacobianIso : (jacobianGrp B hX hk f σ hσ).X ≅ (jacobianGrp B hX' hk f' σ' hσ').X where
  hom := curveJacobianPullback B hX' hX hk f' f α.inv
    (inv_comp_of_hom_comp B hX hX' hk f f' α hα) σ' hσ' σ hσ
  inv := curveJacobianPullback B hX hX' hk f f' α.hom hα σ hσ σ' hσ'
  hom_inv_id := by
    have h := curveJacobianHom_comp B hX hX' hX hk f f' f σ hσ σ' hσ' σ hσ
      α.hom hα α.inv (inv_comp_of_hom_comp B hX hX' hk f f' α hα)
      (by rw [α.hom_inv_id]; exact Category.id_comp _)
    rw [curveJacobianHom_eq_id B hX hk f σ hσ _ _ α.hom_inv_id] at h
    have h2 := congrArg (fun g => (Over.post (X := B.obj hk) B.inclusion).map g) h
    simp only [Functor.map_comp, Functor.map_id] at h2
    exact h2.symm
  inv_hom_id := by
    have h := curveJacobianHom_comp B hX' hX hX' hk f' f f' σ' hσ' σ hσ σ' hσ'
      α.inv (inv_comp_of_hom_comp B hX hX' hk f f' α hα) α.hom hα
      (by rw [α.inv_hom_id]; exact Category.id_comp _)
    rw [curveJacobianHom_eq_id B hX' hk f' σ' hσ' _ _ α.inv_hom_id] at h
    have h2 := congrArg (fun g => (Over.post (X := B.obj hk) B.inclusion).map g) h
    simp only [Functor.map_comp, Functor.map_id] at h2
    exact h2.symm

instance isMonHom_curveJacobianIso_hom :
    IsMonHom (curveJacobianIso B hX hX' hk f f' σ hσ σ' hσ' α hα).hom :=
  isMonHom_curveJacobianPullback B hX' hX hk f' f _ _ σ' hσ' σ hσ

instance isMonHom_curveJacobianIso_inv :
    IsMonHom (curveJacobianIso B hX hX' hk f f' σ hσ σ' hσ' α hα).inv :=
  isMonHom_curveJacobianPullback B hX hX' hk f f' _ _ σ hσ σ' hσ'

variable (p : ℕ) [Fact p.Prime] (hS : IsInCharacteristic (Spec (.of k)) p) (n : ℕ)
  (Ψ : X ⟶ X)
  (hΨ : Ψ ≫ B.inclusion.map f = B.inclusion.map f ≫ absoluteFrobeniusPow (Spec (.of k)) p hS n)
  (Ψ' : X' ⟶ X')
  (hΨ' : Ψ' ≫ B.inclusion.map f' =
    B.inclusion.map f' ≫ absoluteFrobeniusPow (Spec (.of k)) p hS n)
  (hαΨ : α.hom ≫ Ψ' = Ψ ≫ α.hom)

include hαΨ in
/-- **The C-Jac Frobenius square**: `e.hom ≫ F_{X'} = F_X ≫ e.hom` for `e = curveJacobianIso`. -/
theorem curveJacobianIso_hom_comp_jacobianFrobenius :
    (curveJacobianIso B hX hX' hk f f' σ hσ σ' hσ' α hα).hom ≫
        jacobianFrobenius B hX' hk f' p hS n Ψ' hΨ' σ' hσ' =
      jacobianFrobenius B hX hk f p hS n Ψ hΨ σ hσ ≫
        (curveJacobianIso B hX hX' hk f f' σ hσ σ' hσ' α hα).hom :=
  curveJacobianPullback_comp_jacobianFrobenius B hX' hX hk f' f α.inv
    (inv_comp_of_hom_comp B hX hX' hk f f' α hα) σ' hσ' σ hσ p hS n Ψ' hΨ' Ψ hΨ
    (by rw [Iso.comp_inv_eq, Category.assoc, ← hαΨ, Iso.inv_hom_id_assoc])

include hα hαΨ in
/-- **C-Jac.** For smooth proper (projective) geometrically irreducible curves `X`, `X'` over a
separably closed `k` with rational points, in a common big fppf site, an isomorphism
`α : X ≅ X'` over `k` intertwining twisted Frobenii `Ψ`, `Ψ'` (lying over the same `F^n` of
`Spec k`) gives an isomorphism of Jacobians `J_X ≅ J_{X'}` which is a homomorphism of group
schemes and intertwines the Jacobian Frobenii. This is the shape `GraphFiniteness` consumes. -/
theorem exists_equivariant_jacobianIso :
    ∃ e : (jacobianGrp B hX hk f σ hσ).X ≅ (jacobianGrp B hX' hk f' σ' hσ').X,
      IsMonHom e.hom ∧ e.hom ≫ jacobianFrobenius B hX' hk f' p hS n Ψ' hΨ' σ' hσ' =
        jacobianFrobenius B hX hk f p hS n Ψ hΨ σ hσ ≫ e.hom :=
  ⟨curveJacobianIso B hX hX' hk f f' σ hσ σ' hσ' α hα, inferInstance,
    curveJacobianIso_hom_comp_jacobianFrobenius B hX hX' hk f f' σ hσ σ' hσ' α hα p hS n Ψ hΨ Ψ'
      hΨ' hαΨ⟩

end Iso

end RamanujanWeil.Arith.Deuring.Geom.G7.CJac

end
