import RamanujanWeil.Arith.DeuringG6Degree

/-!
# A3-ord, G6 (general case): quotient by a finite locally free subgroup scheme

For the `p`-part (G5) the relevant subgroups (`μ_p ⊆ A[p]`, kernels of Frobenius) are not
reduced, so they are not determined by `k`-points. This file packages G6 for an arbitrary
finite locally free subgroup scheme `j : G ↪ A` (a monomorphic homomorphism), acting by the
restriction of the regular action (`translationModObj`).

**`exists_quotient_by_subgroupScheme`**: there are an abelian variety `B` and a homomorphism
`q : A ⟶ B`, finite locally free (of rank `rank G` when `G` has constant rank) and surjective,
with scheme-theoretic kernel `G` (`x ≫ q = 1 ↔ x` factors through `j`, for `T`-points) and the
universal property for homomorphisms `α` with `j ≫ α = 1`.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory
  CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

universe u

namespace RamanujanWeil.Arith.Deuring.Geom.G6

section Translation

variable {S : Scheme.{u}} {A G : Over S} [GrpObj A] [GrpObj G]

/-- The action of a subgroup `j : G ⟶ A` on `A` by translation: the regular action of `A`
restricted along `j`, `γ = (j ▷ A) ≫ μ`. -/
@[instance_reducible]
noncomputable def translationModObj (j : G ⟶ A) [IsMonHom j] : ModObj G A :=
  letI := ModObj.regular A
  Mod.scalarRestriction j A

theorem isTranslation_translationModObj (j : G ⟶ A) [IsMonHom j] :
    letI := translationModObj j
    IsTranslation j := by
  intro T g x
  show lift g x ≫ (j ▷ A ≫ μ[A]) = _
  rw [lift_whiskerRight_assoc, Hom.mul_def]

end Translation

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- **G6, general finite locally free subgroup scheme.** -/
theorem exists_quotient_by_subgroupScheme (A : Over (Spec (.of k))) [GrpObj A]
    [IsAbelianVariety k A] (G : Over (Spec (.of k))) [GrpObj G]
    [Stacks.Morphisms.IsFiniteLocallyFree G.hom] (j : G ⟶ A) [IsMonHom j] [Mono j] :
    ∃ (B : Over (Spec (.of k))) (_ : GrpObj B) (_ : IsAbelianVariety k B) (q : A ⟶ B),
      IsMonHom q ∧ Stacks.Morphisms.IsFiniteLocallyFree q.left ∧ Surjective q.left ∧
      (∀ r : ℕ, Stacks.Morphisms.IsFiniteLocallyFreeOfRank G.hom r →
        Stacks.Morphisms.IsFiniteLocallyFreeOfRank q.left r) ∧
      (∀ {T : Over (Spec (.of k))} (x : T ⟶ A), x ≫ q = 1 ↔ ∃ g : T ⟶ G, g ≫ j = x) ∧
      ∀ (C : Over (Spec (.of k))) [GrpObj C] (α : A ⟶ C) [IsMonHom α],
        j ≫ α = 1 → ∃! β : B ⟶ C, IsMonHom β ∧ q ≫ β = α := by
  have : IsCommMonObj A := isCommMonObj_of_isProper_of_geometricallyIntegral A
  let := translationModObj j
  obtain ⟨Q⟩ := nonempty_translationQuotient j (isTranslation_translationModObj j)
    (hasAffineFinitePointsInFibres_of_isProjective A.hom (isProjective_of_isAbelianVariety k A))
  refine ⟨Q.B, inferInstance, Q.isAbelianVariety, Q.q, inferInstance, Q.finiteLocallyFree,
    Q.surjective, fun r hr => ?_, fun x => Q.comp_q_eq_one_iff' x, fun C _ α _ hα => ?_⟩
  · have := hr
    exact Q.isFiniteLocallyFreeOfRank_q r
  · obtain ⟨β, hβ, hβα⟩ := Q.exists_isMonHom_desc α hα
    exact ⟨β, ⟨hβ, hβα⟩, fun β' hβ' => Q.desc_unique _ _ (hβ'.2.trans hβα.symm)⟩

end RamanujanWeil.Arith.Deuring.Geom.G6
