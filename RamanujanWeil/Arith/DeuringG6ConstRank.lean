import RamanujanWeil.Arith.DeuringG6Etale
import RamanujanWeil.Arith.DeuringG6Degree
import StacksFrontier.AlgebraicGeometry.FiniteLocallyFreeRank.FieldTarget

/-!
# A3-ord, G6 (étale case): `deg (A ⟶ A/H) = #H`

The constant group scheme `H_S` of a finite group is finite locally free of rank `#H`
(`isFiniteLocallyFreeOfRank_constantGroupScheme`; Stacks records only the unranked statement):
over the terminal scheme it is `Spec (H → ℤ)`, free of rank `#H`, and rank is stable under base
change. Combined with `DeuringG6Degree`, the quotient `q : A ⟶ A/H` of
`exists_quotient_by_finite_subgroup` has degree `#H` (`exists_quotient_by_finite_subgroup'`).
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory
  CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

universe u v

namespace RamanujanWeil.Arith.Deuring.Geom.G6

/-- A free module of rank `r` is finite locally free of rank `r`. -/
theorem module_isFiniteLocallyFreeOfRank_of_basis {R : Type u} [CommRing R] {M : Type v}
    [AddCommGroup M] [Module R M] {r : ℕ} (b : Module.Basis (Fin r) R M) :
    Module.IsFiniteLocallyFreeOfRank R M r := by
  refine ⟨PUnit, fun _ => 1, by simp, fun _ => ?_⟩
  exact ⟨b.ofIsLocalizedModule (Localization.Away (1 : R)) (Submonoid.powers (1 : R))
    (LocalizedModule.mkLinearMap (Submonoid.powers (1 : R)) M)⟩

/-- The coproduct of `n` copies of the terminal scheme is finite locally free of rank `n` over
the terminal scheme. -/
theorem isFiniteLocallyFreeOfRank_terminal_from_constantSchemeOverIntegers
    (G : Type u) [Finite G] :
    Stacks.Morphisms.IsFiniteLocallyFreeOfRank
      (terminal.from (constantSchemeOverIntegers.{u} G)) (Nat.card G) := by
  classical
  have : Fintype G := Fintype.ofFinite G
  let P := Stacks.Morphisms.IsFiniteLocallyFreeOfRank.property.{u} (Nat.card G)
  have hP : MorphismProperty.RespectsIso P := inferInstance
  let B : CommRingCat.{u} := .of (G → ULift.{u} ℤ)
  let φ : CommRingCat.of (ULift.{u} ℤ) ⟶ B :=
    CommRingCat.ofHom (RingHom.pi fun _ : G ↦ RingHom.id (ULift.{u} ℤ))
  let e₀ : (⊤_ Scheme.{u}) ≅ Spec (CommRingCat.of (ULift.{u} ℤ)) :=
    terminalIsTerminal.uniqueUpToIso specULiftZIsTerminal.{u}
  have hB : P (terminal.from (Spec B)) := by
    rw [← MorphismProperty.cancel_right_of_respectsIso P (terminal.from (Spec B)) e₀.hom,
      specULiftZIsTerminal.hom_ext (terminal.from (Spec B) ≫ e₀.hom) (Spec.map φ)]
    show Stacks.Morphisms.IsFiniteLocallyFreeOfRank
      (Spec.map (CommRingCat.ofHom (algebraMap (ULift.{u} ℤ) (G → ULift.{u} ℤ)))) _
    rw [Stacks.Morphisms.isFiniteLocallyFreeOfRank_specMap_iff_module]
    refine module_isFiniteLocallyFreeOfRank_of_basis ((Pi.basisFun (ULift.{u} ℤ) G).reindex ?_)
    exact (Fintype.equivFin G).trans (finCongr (Nat.card_eq_fintype_card).symm)
  let eT : constantSchemeOverIntegers.{u} G ≅ Spec B :=
    (Sigma.whiskerEquiv (f := fun _ : G ↦ ⊤_ Scheme.{u})
        (g := fun _ : G ↦ Spec (CommRingCat.of (ULift.{u} ℤ)))
        (Equiv.refl G) fun _ ↦ e₀.symm).trans
      (asIso (sigmaSpec fun _ : G ↦ CommRingCat.of (ULift.{u} ℤ)))
  rw [← terminalIsTerminal.hom_ext (eT.hom ≫ terminal.from (Spec B))
    (terminal.from (constantSchemeOverIntegers.{u} G))]
  exact (MorphismProperty.cancel_left_of_respectsIso P eT.hom (terminal.from (Spec B))).mpr hB

/-- **The constant group scheme of a finite group `G` is finite locally free of rank `#G`.** -/
theorem isFiniteLocallyFreeOfRank_constantGroupScheme (G : Type u) [Group G] [Finite G]
    (S : Scheme.{u}) :
    Stacks.Morphisms.IsFiniteLocallyFreeOfRank (constantGroupSchemeObj G S).hom (Nat.card G) :=
  have := isFiniteLocallyFreeOfRank_terminal_from_constantSchemeOverIntegers G
  Stacks.Morphisms.IsFiniteLocallyFreeOfRank.of_isPullback
    (IsPullback.of_hasPullback (terminal.from (constantSchemeOverIntegers.{u} G))
      (terminal.from S))

section Main

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- **G6, étale case, with degree.** For `A` an abelian variety over an algebraically closed
field `k` and `H ⊆ A(k)` a finite subgroup there are an abelian variety `B` and a homomorphism
`q : A ⟶ B` such that
* `q` is finite locally free of rank `#H` and surjective, and `deg q = [k(A) : k(B)] = #H`;
* `ker q = H` on `k`-points;
* every homomorphism `α : A ⟶ C` killing `H` factors uniquely as `q ≫ β`, `β` a homomorphism. -/
theorem exists_quotient_by_finite_subgroup' (A : Over (Spec (.of k))) [GrpObj A]
    [IsAbelianVariety k A] (H : Subgroup (𝟙_ (Over (Spec (.of k))) ⟶ A)) [Finite H] :
    ∃ (B : Over (Spec (.of k))) (_ : GrpObj B) (_ : IsAbelianVariety k B) (q : A ⟶ B),
      IsMonHom q ∧ Stacks.Morphisms.IsFiniteLocallyFreeOfRank q.left (Nat.card H) ∧
      Surjective q.left ∧
      (∀ (_ : IsFinite q.left) (_ : IsDominant q.left), degreeOver q.left = Nat.card H) ∧
      (∀ x : 𝟙_ (Over (Spec (.of k))) ⟶ A, x ≫ q = 1 ↔ x ∈ H) ∧
      ∀ (C : Over (Spec (.of k))) [GrpObj C] (α : A ⟶ C) [IsMonHom α],
        (∀ h ∈ H, h ≫ α = 1) → ∃! β : B ⟶ C, IsMonHom β ∧ q ≫ β = α := by
  have : IsCommMonObj A := isCommMonObj_of_isProper_of_geometricallyIntegral A
  let := constModObj H
  have : Stacks.Morphisms.IsFiniteLocallyFree
      (constantGroupSchemeObj H (Spec (.of k))).hom :=
    isFiniteLocallyFree_constantGroupScheme H (Spec (.of k))
  have : Stacks.Morphisms.IsFiniteLocallyFreeOfRank
      (constantGroupSchemeObj H (Spec (.of k))).hom (Nat.card H) :=
    isFiniteLocallyFreeOfRank_constantGroupScheme H (Spec (.of k))
  obtain ⟨Q⟩ := nonempty_translationQuotient (constJ H) (isTranslation_constJ H)
    (hasAffineFinitePointsInFibres_of_isProjective A.hom (isProjective_of_isAbelianVariety k A))
  have hB := Q.isAbelianVariety
  refine ⟨Q.B, inferInstance, hB, Q.q, inferInstance, Q.isFiniteLocallyFreeOfRank_q _,
    Q.surjective, fun _ _ => ?_, fun x => ?_, fun C _ α _ hα => ?_⟩
  · have := Q.isFiniteLocallyFreeOfRank_q (Nat.card H)
    exact (Stacks.Morphisms.eq_degreeOver_of_isFiniteLocallyFreeOfRank _ _).symm
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
