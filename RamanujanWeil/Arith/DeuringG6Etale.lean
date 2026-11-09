import RamanujanWeil.Arith.DeuringG6AbVar
import StacksFrontier.AlgebraicGeometry.GroupScheme.Examples.ConstantAction
import StacksFrontier.AlgebraicGeometry.GroupScheme.Examples.ConstantFiniteLocallyFree

/-!
# A3-ord, G6 (étale case): quotient of an abelian variety by a finite subgroup of `A(k)`

Let `k` be algebraically closed, `A` an abelian variety over `k` and `H ⊆ A(k)` a finite
subgroup of the group of `k`-points. The constant group scheme `H_k` (Stacks 03YW,
`AlgebraicGeometry.constantGroupSchemeObj`) acts on `A` by translations (`translate h : x ↦ h·x`,
`AlgebraicGeometry.constantGroupSchemeModObj`). This action commutes with right multiplication,
so `j : H_k ⟶ A`, `j(g) = g • 1`, is a homomorphism through which `H_k` acts by translation, and
`j` is a monomorphism because the action is free (`k`-points of a nonempty scheme are detected
after pulling back to it). Hence `DeuringG6Quot`/`DeuringG6AbVar` apply:

**`exists_quotient_by_finite_subgroup`**: there are an abelian variety `B` over `k` and a
homomorphism `q : A ⟶ B`, finite locally free and surjective, with
* `ker q = H` on `k`-points: `x ≫ q = 1 ↔ x ∈ H`;
* the universal property: a homomorphism `α : A ⟶ C` with `h ≫ α = 1` for all `h ∈ H`
  factors uniquely as `q ≫ β` with `β` a homomorphism.

No assumption on `#H` versus `char k` is needed (the constant group scheme is étale in every
characteristic); the non-reduced `p`-part (G5) is covered by `DeuringG6AbVar` for any finite
locally free subgroup scheme.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory
  CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

universe u

namespace RamanujanWeil.Arith.Deuring.Geom.G6

variable {k : Type u} [Field k]

/-- `(toUnit T).left` is the structure morphism of `T`. -/
theorem toUnit_left_eq {S : Scheme.{u}} (T : Over S) : (toUnit T).left = T.hom := by
  simpa using Over.w (toUnit T)

/-- **`k`-points are detected on any nonempty `k`-scheme**: if `T` is nonempty, two `k`-points
`g, g'` of `X` with `T ⟶ Spec k ⟶ X` equal are equal. (A nonempty affine open of `T` maps
flatly, quasi-compactly and surjectively onto `Spec k`, so is an epimorphism.) -/
theorem eq_of_toUnit_comp_eq {T X : Over (Spec (.of k))} [hT : Nonempty T.left]
    {g g' : 𝟙_ (Over (Spec (.of k))) ⟶ X} (h : toUnit T ≫ g = toUnit T ≫ g') : g = g' := by
  obtain ⟨t⟩ := hT
  obtain ⟨U, hU, htU, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (Set.mem_univ t)
  have : IsAffine U.toScheme := hU
  let e : U.toScheme ⟶ Spec (.of k) := U.ι ≫ T.hom
  have : Flat e := inferInstance
  have : QuasiCompact e := inferInstance
  have : Surjective e := ⟨fun y => ⟨⟨t, htU⟩, Subsingleton.elim _ _⟩⟩
  have : Epi e := inferInstance
  apply Over.OverMorphism.ext
  rw [← cancel_epi e]
  have h' := congrArg (fun f => U.ι ≫ f.left) h
  simp only [Over.comp_left, toUnit_left_eq] at h'
  simpa [e] using h'

section Translate

variable {A : Over (Spec (.of k))} [GrpObj A] [IsCommMonObj A]

/-- Translation by a `k`-point `h` on `T`-points: `x ↦ h_T · x`. -/
theorem comp_translate {T : Over (Spec (.of k))} (h : 𝟙_ (Over (Spec (.of k))) ⟶ A)
    (x : T ⟶ A) : x ≫ ((toUnit A ≫ h) * 𝟙 A) = (toUnit T ≫ h) * x := by
  rw [MonObj.comp_mul, ← Category.assoc, toUnit_unique (x ≫ toUnit A) (toUnit T),
    Category.comp_id]

/-- Translation by a `k`-point, as an automorphism of `A`. -/
noncomputable def translate (h : 𝟙_ (Over (Spec (.of k))) ⟶ A) : A ≅ A where
  hom := (toUnit A ≫ h) * 𝟙 A
  inv := (toUnit A ≫ h⁻¹) * 𝟙 A
  hom_inv_id := by
    rw [comp_translate, GrpObj.comp_inv, inv_mul_cancel_left]
  inv_hom_id := by
    rw [comp_translate, GrpObj.comp_inv, mul_inv_cancel_left]

theorem comp_translate_hom {T : Over (Spec (.of k))} (h : 𝟙_ (Over (Spec (.of k))) ⟶ A)
    (x : T ⟶ A) : x ≫ (translate h).hom = (toUnit T ≫ h) * x :=
  comp_translate h x

/-- A subgroup of `A(k)` acts on `A` by translations. -/
noncomputable def translateHom (H : Subgroup (𝟙_ (Over (Spec (.of k))) ⟶ A)) : H →* Aut A where
  toFun h := translate h.1
  map_one' := Iso.ext (by
    show (toUnit A ≫ (1 : 𝟙_ _ ⟶ A)) * 𝟙 A = 𝟙 A
    rw [MonObj.comp_one, one_mul])
  map_mul' h₁ h₂ := Iso.ext (by
    show _ = (translate h₂.1 ≪≫ translate h₁.1).hom
    rw [Iso.trans_hom, comp_translate_hom]
    show (toUnit A ≫ (h₁.1 * h₂.1)) * 𝟙 A = _
    rw [MonObj.comp_mul, mul_assoc]
    rfl)

end Translate

section Constant

variable {A : Over (Spec (.of k))} [GrpObj A] [IsCommMonObj A]
  (H : Subgroup (𝟙_ (Over (Spec (.of k))) ⟶ A))

/-- Shortcut for the group structure of the constant group scheme `H_k`. -/
noncomputable instance constGrpObj : GrpObj (constantGroupSchemeObj H (Spec (.of k))) :=
  (constantGroupScheme H (Spec (.of k))).grp

/-- The action of the constant group scheme `H_k` on `A` by translations. -/
@[instance_reducible]
noncomputable def constModObj : ModObj (constantGroupSchemeObj H (Spec (.of k))) A :=
  constantGroupSchemeModObj A (translateHom H)

attribute [local instance] constModObj

/-- On the piece of `T` where a `T`-point `g` of `H_k` is the constant `h`. -/
theorem pullback_fst_comp_eq {T : Over (Spec (.of k))}
    (g : T ⟶ constantGroupSchemeObj H (Spec (.of k))) (h : H) :
    pullback.fst g (constantGroupSchemePoint H (Spec (.of k)) h) ≫ g =
      toUnit _ ≫ constantGroupSchemePoint H (Spec (.of k)) h := by
  rw [pullback.condition, toUnit_unique (pullback.snd _ _) (toUnit _)]

/-- The constant point `h` acts by the translation `translate h`. -/
theorem constPoint_smul {T : Over (Spec (.of k))} (h : H) (x : T ⟶ A) :
    (toUnit T ≫ constantGroupSchemePoint H (Spec (.of k)) h) • x = (toUnit T ≫ h.1) * x := by
  rw [← comp_translate_hom]
  exact constantGroupSchemePoint_smul A (translateHom H) h x

/-- The translation action commutes with right multiplication. -/
theorem smul_mul_right {T : Over (Spec (.of k))}
    (g : T ⟶ constantGroupSchemeObj H (Spec (.of k))) (x y : T ⟶ A) :
    g • (x * y) = (g • x) * y := by
  refine hom_ext_of_constantGroupSchemePoint g fun h => ?_
  rw [MonObj.comp_mul, ModObj.comp_smul, ModObj.comp_smul, pullback_fst_comp_eq,
    constPoint_smul, constPoint_smul, mul_assoc, MonObj.comp_mul]

/-- The embedding `j : H_k ⟶ A`, `g ↦ g • 1`. -/
noncomputable def constJ : constantGroupSchemeObj H (Spec (.of k)) ⟶ A :=
  (𝟙 (constantGroupSchemeObj H (Spec (.of k)))) •
    (1 : constantGroupSchemeObj H (Spec (.of k)) ⟶ A)

theorem comp_constJ {T : Over (Spec (.of k))} (g : T ⟶ constantGroupSchemeObj H (Spec (.of k))) :
    g ≫ constJ H = g • (1 : T ⟶ A) := by
  rw [constJ, ModObj.comp_smul, Category.comp_id, MonObj.comp_one]

/-- `H_k` acts on `A` by translation through `j`. -/
theorem isTranslation_constJ : IsTranslation (constJ H) := fun T g x => by
  rw [comp_constJ, ← smul_mul_right, one_mul]

/-- `j` on the constant point `h` is `h`. -/
theorem constantGroupSchemePoint_constJ (h : H) :
    constantGroupSchemePoint H (Spec (.of k)) h ≫ constJ H = h.1 := by
  have e := constPoint_smul H h (1 : 𝟙_ (Over (Spec (.of k))) ⟶ A)
  rw [toUnit_unit, Category.id_comp, Category.id_comp, mul_one] at e
  rw [comp_constJ, e]

instance isMonHom_constJ : IsMonHom (constJ H) where
  one_hom := by
    have h1 : η[constantGroupSchemeObj H (Spec (.of k))] =
        (1 : 𝟙_ (Over (Spec (.of k))) ⟶ constantGroupSchemeObj H (Spec (.of k))) := by
      rw [Hom.one_def, toUnit_unit, Category.id_comp]
    rw [h1, comp_constJ, one_smul, Hom.one_def, toUnit_unit, Category.id_comp]
  mul_hom := by
    have hμ : μ[constantGroupSchemeObj H (Spec (.of k))] = fst _ _ * snd _ _ := by
      rw [Hom.mul_def, lift_fst_snd, Category.id_comp]
    rw [hμ, comp_constJ, mul_smul, ← one_mul (snd _ _ • (1 : _ ⟶ A)), smul_mul_right,
      ← lift_fst_comp_snd_comp, ← Hom.mul_def, comp_constJ, comp_constJ]

/-- The translation action of `H_k` is free (Stacks 07S1). -/
theorem isFreeAction_const : IsFreeAction (constantGroupSchemeObj H (Spec (.of k))) A :=
  isFreeAction_constantGroupSchemeModObj A (translateHom H) fun T hT x g g' hx => by
    have e : (toUnit T ≫ g.1) * x = (toUnit T ≫ g'.1) * x := by
      rw [← comp_translate_hom, ← comp_translate_hom]
      exact hx
    exact Subtype.ext (eq_of_toUnit_comp_eq (mul_right_cancel e))

instance mono_constJ : Mono (constJ H) := ⟨fun {T} m n hmn => by
  have := isFreeAction_const H T
  refine IsCancelSMul.right_cancel m n (1 : T ⟶ A) ?_
  rw [← comp_constJ, ← comp_constJ, hmn]⟩

/-- **`k`-points of the constant group scheme are constant.** -/
theorem exists_eq_constantGroupSchemePoint
    (g : 𝟙_ (Over (Spec (.of k))) ⟶ constantGroupSchemeObj H (Spec (.of k))) :
    ∃ h : H, g = constantGroupSchemePoint H (Spec (.of k)) h := by
  by_contra hne
  push Not at hne
  -- every piece of `Spec k` over which `g` is constant is empty
  have hempty : ∀ h : H,
      IsEmpty (pullback g (constantGroupSchemePoint H (Spec (.of k)) h)).left := fun h => by
    rw [← not_nonempty_iff]
    intro hP
    apply hne h
    have e := pullback_fst_comp_eq H g h
    rw [toUnit_unique (pullback.fst g _) (toUnit _)] at e
    exact eq_of_toUnit_comp_eq e
  -- but `Spec k` is their disjoint union
  obtain ⟨hc⟩ := isUniversalColimit_of_isColimit_cofanOver
    (isColimit_constantGroupSchemeCofan H (Spec (.of k)))
    (Cofan.mk (𝟙_ (Over (Spec (.of k)))) fun h ↦
      pullback.fst g (constantGroupSchemePoint H (Spec (.of k)) h))
    (Discrete.natTrans fun h ↦ pullback.snd g (constantGroupSchemePoint H (Spec (.of k)) h.as)) g
    (by
      ext ⟨h⟩
      exact congrArg Over.Hom.left
        (pullback.condition (f := g) (g := constantGroupSchemePoint H (Spec (.of k)) h)).symm)
    (.of_discrete _)
    fun ⟨h⟩ ↦ IsPullback.of_hasPullback g (constantGroupSchemePoint H (Spec (.of k)) h)
  let E : Over (Spec (.of k)) := Over.mk (Scheme.emptyTo (Spec (.of k)))
  have hE : IsEmpty E.left := inferInstanceAs (IsEmpty (∅ : Scheme.{u}))
  let d : 𝟙_ (Over (Spec (.of k))) ⟶ E := Cofan.IsColimit.desc hc fun h =>
    haveI := hempty h
    Over.homMk (isInitialOfIsEmpty.to E.left) (isInitialOfIsEmpty.hom_ext _ _)
  have pt : (𝟙_ (Over (Spec (.of k)))).left := (inferInstance : Nonempty (Spec (.of k))).some
  exact hE.elim (d.left pt)

end Constant

section Main

variable [IsAlgClosed k]

/-- **G6 (étale case): the quotient of an abelian variety by a finite subgroup of `A(k)`.**
For `A` an abelian variety over an algebraically closed field `k` and `H ⊆ A(k)` a finite
subgroup there are an abelian variety `B` and a homomorphism `q : A ⟶ B`, finite locally free
and surjective, such that `ker q = H` on `k`-points and every homomorphism `A ⟶ C` killing `H`
factors uniquely through `q` by a homomorphism. -/
theorem exists_quotient_by_finite_subgroup (A : Over (Spec (.of k))) [GrpObj A]
    [IsAbelianVariety k A] (H : Subgroup (𝟙_ (Over (Spec (.of k))) ⟶ A)) [Finite H] :
    ∃ (B : Over (Spec (.of k))) (_ : GrpObj B) (_ : IsAbelianVariety k B) (q : A ⟶ B),
      IsMonHom q ∧ Stacks.Morphisms.IsFiniteLocallyFree q.left ∧ Surjective q.left ∧
      (∀ x : 𝟙_ (Over (Spec (.of k))) ⟶ A, x ≫ q = 1 ↔ x ∈ H) ∧
      ∀ (C : Over (Spec (.of k))) [GrpObj C] (α : A ⟶ C) [IsMonHom α],
        (∀ h ∈ H, h ≫ α = 1) → ∃! β : B ⟶ C, IsMonHom β ∧ q ≫ β = α := by
  have : IsCommMonObj A := isCommMonObj_of_isProper_of_geometricallyIntegral A
  let := constModObj H
  have : Stacks.Morphisms.IsFiniteLocallyFree
      (constantGroupSchemeObj H (Spec (.of k))).hom :=
    isFiniteLocallyFree_constantGroupScheme H (Spec (.of k))
  obtain ⟨Q⟩ := nonempty_translationQuotient (constJ H) (isTranslation_constJ H)
    (hasAffineFinitePointsInFibres_of_isProjective A.hom (isProjective_of_isAbelianVariety k A))
  refine ⟨Q.B, inferInstance, Q.isAbelianVariety, Q.q, inferInstance, Q.finiteLocallyFree,
    Q.surjective, fun x => ?_, fun C _ α _ hα => ?_⟩
  · rw [Q.comp_q_eq_one_iff']
    constructor
    · rintro ⟨g, rfl⟩
      obtain ⟨h, rfl⟩ := exists_eq_constantGroupSchemePoint H g
      rw [constantGroupSchemePoint_constJ]
      exact h.2
    · intro hx
      exact ⟨_, constantGroupSchemePoint_constJ H ⟨x, hx⟩⟩
  · have hjα : constJ H ≫ α = 1 := by
      refine hom_ext_of_constantGroupSchemePoint (𝟙 _) fun h => ?_
      have e := pullback_fst_comp_eq H (𝟙 _) h
      rw [Category.comp_id] at e
      have e2 := constantGroupSchemePoint_constJ H h
      rw [MonObj.comp_one, ← Category.assoc, e, Category.assoc, Category.assoc,
        reassoc_of% e2, hα _ h.2, MonObj.comp_one]
    obtain ⟨β, hβ, hβα⟩ := Q.exists_isMonHom_desc α hjα
    exact ⟨β, ⟨hβ, hβα⟩, fun β' hβ' => Q.desc_unique _ _ (hβ'.2.trans hβα.symm)⟩

end Main

end RamanujanWeil.Arith.Deuring.Geom.G6
