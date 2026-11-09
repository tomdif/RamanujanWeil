import RamanujanWeil.Arith.DeuringG3Hom
import StacksFrontier.AlgebraicGeometry.Curves.InseparableFactorizationChain
import StacksFrontier.AlgebraicGeometry.Curves.TwistedFrobeniusDegree

/-!
# A3-ord, G4 on `Hom(A, B)`: the degree of a homomorphism of elliptic curves

Let `k` be algebraically closed and `A`, `B`, `C` one-dimensional abelian varieties over `k`.
For a morphism `α : A ⟶ B` over `k` let `deg α = homDegree α` be `[k(A) : α^* k(B)]`
(`AlgebraicGeometry.degreeOver`) when `α` is dominant and `0` otherwise, exactly as Stacks'
`endDegree` for `A = B` (`homDegree_eq_endDegree`). This file proves:

* `isDominant_of_ne_one`, **`homDegree_eq_zero_iff`**: `deg α = 0 ↔ α = 0` for a homomorphism;
* **`homDegree_comp`**: `deg (α ≫ β) = deg α · deg β` (tower law, Stacks 02NZ);
* **`homDegree_zpow`**: `deg (nα) = n² deg α`;
* `homPolar_mul_left`, `homPolar_self`: if some nonzero `ψ : B ⟶ A` exists, the polar form
  `⟨α, β⟩ = deg(α + β) − deg α − deg β` is biadditive with `⟨α, α⟩ = 2 deg α`, i.e. `deg` is a
  positive definite quadratic form on `Hom(A, B)` (`deg(α ≫ ψ) = deg α · deg ψ` transports the
  form of `End(A)`).
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.MonObj

universe u

namespace RamanujanWeil.Arith.Deuring.Geom

open Stacks.Groupoids

variable {k : Type u} [Field k]

section Defs

variable {A B : Over (Spec (.of k))} [GrpObj A] [GrpObj B]
  [AlgebraicGeometry.IsAbelianVariety k A] [AlgebraicGeometry.IsAbelianVariety k B]

/-- A morphism of abelian varieties over `k` is proper. -/
theorem isProper_left_hom (α : A ⟶ B) : IsProper α.left := by
  have : IsProper (α.left ≫ B.hom) := by rw [Over.w α]; infer_instance
  exact IsProper.of_comp _ B.hom

/-- **The degree of a morphism `A ⟶ B`** of abelian varieties over `k`: `[k(A) : α^* k(B)]` if
`α` is dominant, `0` otherwise. -/
noncomputable def homDegree (α : A ⟶ B) : ℕ := by
  classical
  exact if h : IsDominant α.left then
    haveI := h
    haveI := isProper_left_hom α
    degreeOver α.left
  else 0

theorem homDegree_of_isDominant (α : A ⟶ B) [h : IsDominant α.left] :
    homDegree α = (haveI := isProper_left_hom α; degreeOver α.left) := by
  classical
  unfold homDegree
  rw [dite_eq_left_of_eq_true (eq_true h)]

theorem homDegree_of_not_isDominant (α : A ⟶ B) (h : ¬ IsDominant α.left) :
    homDegree α = 0 := by
  classical
  unfold homDegree
  rw [dite_eq_right_of_eq_false (eq_false h)]

/-- On `End(A)` the degree is Stacks' `endDegree`. -/
theorem homDegree_eq_endDegree (f : A ⟶ A) : homDegree f = endDegree A f := by
  classical
  by_cases h : IsDominant f.left
  · rw [homDegree_of_isDominant, endDegree, dite_eq_left_of_eq_true (eq_true h)]
  · rw [homDegree_of_not_isDominant f h, endDegree, dite_eq_right_of_eq_false (eq_false h)]

end Defs

section Curves

variable [IsAlgClosed k] {A B C : Over (Spec (.of k))} [GrpObj A] [GrpObj B] [GrpObj C]
  [AlgebraicGeometry.IsAbelianVariety k A] [AlgebraicGeometry.IsAbelianVariety k B]
  [AlgebraicGeometry.IsAbelianVariety k C]

omit [IsAlgClosed k] in
/-- A one-dimensional abelian variety is a curve. -/
theorem isCurve_of_dim_one {A : Over (Spec (.of k))} [GrpObj A]
    [AlgebraicGeometry.IsAbelianVariety k A] (hA : abelianVarietyDimension A = 1) :
    IsCurve k A.hom := by
  refine (isCurve_iff k _).2 ⟨inferInstance, ?_⟩
  have hd := topologicalKrullDim_eq_abelianVarietyDimension A
  rw [hd, hA]
  rfl

omit [IsAlgClosed k] in
theorem functionFieldMap_eq_dominantFunctionFieldMap' {X Y : Scheme.{u}} (h : X ⟶ Y)
    [IsIntegral X] [IsIntegral Y] [IsDominant h] :
    functionFieldMap h = dominantFunctionFieldMap h :=
  (congrArg CommRingCat.Hom.hom
    (stalkMap_cast_target h (genericPoint X) (map_genericPoint_of_isDominant h))).symm

omit [IsAlgClosed k] in
/-- A dominant morphism of one-dimensional abelian varieties has positive degree. -/
theorem homDegree_pos_of_isDominant (hA : abelianVarietyDimension A = 1)
    (hB : abelianVarietyDimension B = 1) (α : A ⟶ B) [IsDominant α.left] :
    0 < homDegree α := by
  have := isCurve_of_dim_one hA
  have := isCurve_of_dim_one hB
  have := isProper_left_hom α
  rw [homDegree_of_isDominant]
  have hfin := finiteDimensional_functionField_of_isCurve A.hom B.hom α.left (Over.w α)
  rw [functionFieldMap_eq_dominantFunctionFieldMap'] at hfin
  exact degreeOver_pos _ hfin

/-- The map `y ↦ y(pt)` from `k`-points of `B` to the underlying space is injective. -/
theorem point_injective :
    Function.Injective (fun y : 𝟙_ (Over (Spec (.of k))) ⟶ B => y.left (pt k)) :=
  fun _ _ h => point_ext h

/-- **A nontrivial homomorphism of one-dimensional abelian varieties is dominant.** -/
theorem isDominant_of_ne_one (hA : abelianVarietyDimension A = 1)
    (hB : abelianVarietyDimension B = 1) (α : A ⟶ B) [IsMonHom α] (hα : α ≠ 1) :
    IsDominant α.left := by
  by_contra hnd
  have := isProper_left_hom α
  set R := Set.range α.left.base
  have hRc : IsClosed R := α.left.isClosedMap.isClosed_range
  have hRne : R ≠ Set.univ := fun h => hnd ⟨by
    show Dense (Set.range α.left.base)
    rw [show Set.range α.left.base = R from rfl, h]; exact dense_univ⟩
  have : CompactSpace B.left := QuasiCompact.compactSpace_of_compactSpace B.hom
  have := isLocallyNoetherian_left B
  have : IsNoetherian B.left := {}
  have hdim : topologicalKrullDim B.left ≤ 1 := by
    rw [topologicalKrullDim_eq_abelianVarietyDimension B, hB]; rfl
  have hRfin : R.Finite := Stacks.Topology.Dimension.finite_of_isClosed_of_ne_univ hdim hRc hRne
  -- the point map of `α` has finite kernel and finite image
  have hfα : (pointKer α).Finite := by
    by_contra hinf; exact hα (eq_one_of_infinite_pointKer hA α hinf)
  let φ := IsMonHom.monoidHom α (𝟙_ (Over (Spec (.of k))))
  have : Finite φ.ker := by
    show Finite (φ.ker : Set (𝟙_ (Over (Spec (.of k))) ⟶ A))
    exact hfα.to_subtype
  have hmaps : Set.MapsTo (fun y : 𝟙_ (Over (Spec (.of k))) ⟶ B => y.left (pt k))
      (φ.range : Set (𝟙_ (Over (Spec (.of k))) ⟶ B)) R := by
    rintro _ ⟨x, rfl⟩
    exact ⟨x.left (pt k), by
      show α.left (x.left (pt k)) = (x ≫ α).left (pt k)
      simp only [Over.comp_left, Scheme.Hom.comp_apply]⟩
  have : Finite φ.range :=
    (Set.Finite.of_finite_image (hRfin.subset (hmaps.image_subset))
      (point_injective.injOn)).to_subtype
  have := finite_of_finite_ker_of_finite_range φ
  exact (infinite_points hA).not_finite this

omit [GrpObj A] [AlgebraicGeometry.IsAbelianVariety k A] in
/-- The trivial homomorphism is not dominant. -/
theorem not_isDominant_one (hB : abelianVarietyDimension B = 1) :
    ¬ IsDominant (1 : A ⟶ B).left := by
  intro hd
  set e : B.left := (η[B]).left (pt k)
  have he : IsClosed ({e} : Set B.left) := Stacks.Groupoids.isClosed_singleton_unit_left B _
  have hsub : Set.range (1 : A ⟶ B).left.base ⊆ {e} := by
    rintro _ ⟨x, rfl⟩
    show (1 : A ⟶ B).left x = e
    rw [Hom.one_def, Over.comp_left, Scheme.Hom.comp_apply]
    congr 1
    exact @Subsingleton.elim (Spec (.of k) : Scheme.{u}) _ _ _
  have hdense := hd.denseRange
  have huniv : (Set.univ : Set B.left) ⊆ {e} := by
    rw [← hdense.closure_range]
    exact closure_minimal hsub he
  -- then `B(k)` has at most one element
  have : Finite (𝟙_ (Over (Spec (.of k))) ⟶ B) := by
    refine Finite.of_injective (fun y : 𝟙_ (Over (Spec (.of k))) ⟶ B =>
      (⟨y.left (pt k), huniv (Set.mem_univ _)⟩ : ({e} : Set B.left))) ?_
    intro y y' h
    exact point_ext (congrArg Subtype.val h)
  exact (infinite_points hB).not_finite this

theorem homDegree_one (hB : abelianVarietyDimension B = 1) : homDegree (1 : A ⟶ B) = 0 :=
  homDegree_of_not_isDominant _ (not_isDominant_one hB)

/-- **`deg α = 0 ↔ α = 0`** for a homomorphism of one-dimensional abelian varieties. -/
theorem homDegree_eq_zero_iff (hA : abelianVarietyDimension A = 1)
    (hB : abelianVarietyDimension B = 1) (α : A ⟶ B) [IsMonHom α] :
    homDegree α = 0 ↔ α = 1 := by
  constructor
  · intro h0
    by_contra hα
    have := isDominant_of_ne_one hA hB α hα
    exact (homDegree_pos_of_isDominant hA hB α).ne' h0
  · rintro rfl
    exact homDegree_one hB

/-- **Multiplicativity of the degree**: `deg (α ≫ β) = deg α · deg β`. -/
theorem homDegree_comp (hA : abelianVarietyDimension A = 1) (hB : abelianVarietyDimension B = 1)
    (hC : abelianVarietyDimension C = 1) (α : A ⟶ B) (β : B ⟶ C) [IsMonHom α] [IsMonHom β] :
    homDegree (α ≫ β) = homDegree α * homDegree β := by
  by_cases hα : α = 1
  · subst hα
    rw [MonObj.one_comp, homDegree_one hC, homDegree_one hB, zero_mul]
  by_cases hβ : β = 1
  · subst hβ
    rw [MonObj.comp_one, homDegree_one hC, homDegree_one hC, mul_zero]
  have := isDominant_of_ne_one hA hB α hα
  have := isDominant_of_ne_one hB hC β hβ
  have hpα := homDegree_pos_of_isDominant hA hB α
  have hpβ := homDegree_pos_of_isDominant hB hC β
  have hαβ : IsDominant (α ≫ β).left := by rw [Over.comp_left]; infer_instance
  have := isProper_left_hom α
  have := isProper_left_hom β
  have := isProper_left_hom (α ≫ β)
  rw [homDegree_of_isDominant] at hpα hpβ ⊢
  rw [homDegree_of_isDominant, homDegree_of_isDominant]
  have : LocallyOfFiniteType (α.left ≫ β.left) := inferInstance
  have hc : (α ≫ β).left = α.left ≫ β.left := by simp
  rw [degreeOver_congr hc, degreeOver_comp_of_pos α.left β.left hpα hpβ]

/-- **`deg (nα) = n² deg α`** (`nα` is `α ^ n` in the multiplicative notation). -/
theorem homDegree_zpow (hA : abelianVarietyDimension A = 1) (hB : abelianVarietyDimension B = 1)
    (α : A ⟶ B) [IsMonHom α] (n : ℤ) (hn : n ≠ 0) :
    homDegree (α ^ n) = n.natAbs ^ 2 * homDegree α := by
  have h : α ^ n = ((𝟙 A : A ⟶ A) ^ n) ≫ α := by
    rw [GrpObj.zpow_comp, Category.id_comp]
  rw [h, homDegree_comp hA hA hB, homDegree_eq_endDegree, endDegree_zpow_id A n hn, hA]

/-- `deg (α ≫ ψ) = deg α · deg ψ` with `α ≫ ψ ∈ End(A)` measured by `endDegree`. -/
theorem endDegree_comp_eq (hA : abelianVarietyDimension A = 1)
    (hB : abelianVarietyDimension B = 1) (α : A ⟶ B) (ψ : B ⟶ A) [IsMonHom α] [IsMonHom ψ] :
    endDegree A (α ≫ ψ) = homDegree α * homDegree ψ := by
  rw [← homDegree_eq_endDegree, homDegree_comp hA hB hA]

/-- The polar form of the degree on `Hom(A, B)`. -/
noncomputable def homPolar (α β : A ⟶ B) : ℤ :=
  (homDegree (α * β) : ℤ) - homDegree α - homDegree β

/-- Transport of the polar form along `· ≫ ψ`. -/
theorem homPolar_mul_degree (hA : abelianVarietyDimension A = 1)
    (hB : abelianVarietyDimension B = 1) (ψ : B ⟶ A) [IsMonHom ψ] (α β : A ⟶ B)
    [IsMonHom α] [IsMonHom β] :
    homPolar α β * homDegree ψ = degPolar A (α ≫ ψ) (β ≫ ψ) := by
  simp only [homPolar, degPolar]
  rw [← MonObj.mul_comp, endDegree_comp_eq hA hB, endDegree_comp_eq hA hB,
    endDegree_comp_eq hA hB]
  push_cast
  ring

/-- **The polar form of `deg` on `Hom(A, B)` is biadditive**, given a nonzero `ψ : B ⟶ A`. -/
theorem homPolar_mul_left (hA : abelianVarietyDimension A = 1)
    (hB : abelianVarietyDimension B = 1) (ψ : B ⟶ A) [IsMonHom ψ] (hψ : ψ ≠ 1)
    (α α' β : A ⟶ B) [IsMonHom α] [IsMonHom α'] [IsMonHom β] :
    homPolar (α * α') β = homPolar α β + homPolar α' β := by
  have hpos : (0 : ℤ) < homDegree ψ := by
    have := isDominant_of_ne_one hB hA ψ hψ
    exact_mod_cast homDegree_pos_of_isDominant hB hA ψ
  apply mul_right_cancel₀ hpos.ne'
  rw [add_mul, homPolar_mul_degree hA hB, homPolar_mul_degree hA hB,
    homPolar_mul_degree hA hB, MonObj.mul_comp, degPolar_mul_left hA]

omit [IsAlgClosed k] in
theorem homPolar_comm (α β : A ⟶ B) : homPolar α β = homPolar β α := by
  simp only [homPolar, mul_comm α β]
  ring

/-- `⟨α, α⟩ = 2 deg α`, given a nonzero `ψ : B ⟶ A`. -/
theorem homPolar_self (hA : abelianVarietyDimension A = 1)
    (hB : abelianVarietyDimension B = 1) (ψ : B ⟶ A) [IsMonHom ψ] (hψ : ψ ≠ 1)
    (α : A ⟶ B) [IsMonHom α] : homPolar α α = 2 * homDegree α := by
  have hpos : (0 : ℤ) < homDegree ψ := by
    have := isDominant_of_ne_one hB hA ψ hψ
    exact_mod_cast homDegree_pos_of_isDominant hB hA ψ
  apply mul_right_cancel₀ hpos.ne'
  rw [homPolar_mul_degree hA hB, degPolar_self hA, endDegree_comp_eq hA hB]
  push_cast
  ring

/-- **The parallelogram law** `deg(α + β) + deg(α − β) = 2 deg α + 2 deg β` on `Hom(A, B)`,
given a nonzero `ψ : B ⟶ A`: `deg` is a positive definite quadratic form on `Hom(A, B)`. -/
theorem homDegree_parallelogram (hA : abelianVarietyDimension A = 1)
    (hB : abelianVarietyDimension B = 1) (ψ : B ⟶ A) [IsMonHom ψ] (hψ : ψ ≠ 1)
    (α β : A ⟶ B) [IsMonHom α] [IsMonHom β] :
    (homDegree (α * β) : ℤ) + homDegree (α * β⁻¹) = 2 * homDegree α + 2 * homDegree β := by
  have h1 := homPolar_mul_left hA hB ψ hψ β β⁻¹ α
  rw [mul_inv_cancel] at h1
  have h0 : homPolar (1 : A ⟶ B) α = 0 := by
    simp only [homPolar, one_mul, homDegree_one hB]
    ring
  rw [h0] at h1
  have h3 : homDegree β⁻¹ = homDegree β := by
    rw [← zpow_neg_one, homDegree_zpow hA hB β (-1) (by norm_num)]
    simp
  simp only [homPolar] at h1
  rw [mul_comm β α, mul_comm β⁻¹ α, h3] at h1
  linarith

end Curves

end RamanujanWeil.Arith.Deuring.Geom
