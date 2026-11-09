import RamanujanWeil.Arith.DeuringG7Tate

/-!
# A3-ord, G7-fin: the product case of the genus-2 route

`docs/ARITH_DEURING_G7FIN.md` §2(a), §2(d) (route F2′). The theta divisor of a principally
polarized abelian surface `B` is either a genus-2 curve (so `B` is a Jacobian) or `C₁ + C₂` (so
`B ≅ C₁ × C₂`). This file disposes of the **product case without any finiteness**:

* `exists_common_factor_of_prodIso`: if a gluing quotient `B_n = (E × E')/graph(u_n)` is
  isomorphic to a product `C₁ × C₂` (as a group object), then some factor `C_j` receives
  **nontrivial** homomorphisms from **both** `E` (through `i_n`) and `E'` (through `i'_n`).
  Reason: `i_n(E) ∩ i'_n(E') = i_n(E[ℓⁿ⁺¹])` has more than one point, and an intersection point
  is killed by every component that kills `i_n(E)` or `i'_n(E')`.
* `comp_iso_fst_equivariant`: if the isomorphism is `π`-equivariant for the diagonal Frobenius
  `ρ₁ × ρ₂`, these homomorphisms are `π`-equivariant.

With `FrobHomDual` (now reduced to `RadicialDual`, G8 doc §1), a factor receiving nonzero
equivariant maps from `E` and `E'` gives a nonzero equivariant `E ⟶ E'`. So in the
genus-2 route, the product case never needs finiteness.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory
  CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

universe u

namespace RamanujanWeil.Arith.Deuring.Geom.G7.Fin

open Stacks.Groupoids RamanujanWeil.Arith.Deuring.Geom.G7

variable {k : Type u} [Field k] [IsAlgClosed k] {E E' : Over (Spec (.of k))} [GrpObj E]
  [GrpObj E'] [AlgebraicGeometry.IsAbelianVariety k E] [AlgebraicGeometry.IsAbelianVariety k E']
  {π : E ⟶ E} {π' : E' ⟶ E'} [IsMonHom π] [IsMonHom π']
  {ℓ : ℕ} {u : ∀ n : ℕ, Tor E (ℓ ^ (n + 1)) ≃+ Tor E' (ℓ ^ (n + 1))} {n : ℕ}

/-- **Product case of the genus-2 route.** If `B_n ≅ C₁ × C₂` and `E[ℓⁿ⁺¹] ≠ 0`, then for
`j = 1` or `j = 2` both `i_n ≫ e ≫ pr_j` and `i'_n ≫ e ≫ pr_j` are nontrivial. -/
theorem exists_common_factor_of_prodIso (G : Glue (Γ ℓ u n))
    {C₁ C₂ : Over (Spec (.of k))} [GrpObj C₁] [GrpObj C₂]
    (e : G.B ≅ C₁ ⊗ C₂) [IsMonHom e.hom]
    (hpos : ∃ x : Tor E (ℓ ^ (n + 1)), x ≠ 0) :
    (G.i ≫ e.hom ≫ fst C₁ C₂ ≠ 1 ∧ G.i' ≫ e.hom ≫ fst C₁ C₂ ≠ 1) ∨
      (G.i ≫ e.hom ≫ snd C₁ C₂ ≠ 1 ∧ G.i' ≫ e.hom ≫ snd C₁ C₂ ≠ 1) := by
  by_contra hcon
  simp only [not_or, not_and_or, not_not] at hcon
  obtain ⟨h₁, h₂⟩ := hcon
  obtain ⟨x, hx⟩ := hpos
  set w : Pt G.B := pt x ≫ G.i with hwdef
  obtain ⟨⟨-, -⟩, ⟨y, hy⟩⟩ := (G.mem_inter_iff w).2 ⟨x, rfl⟩
  -- each component of `w ≫ e` is trivial
  have hcomp : ∀ (C : Over (Spec (.of k))) [GrpObj C] (f : C₁ ⊗ C₂ ⟶ C),
      (G.i ≫ e.hom ≫ f = 1 ∨ G.i' ≫ e.hom ≫ f = 1) → w ≫ e.hom ≫ f = 1 := by
    intro C _ f hf
    rcases hf with hf | hf
    · rw [hwdef, Category.assoc, hf, MonObj.comp_one]
    · rw [hy, Category.assoc, hf, MonObj.comp_one]
  have hw : w ≫ e.hom = 1 := by
    apply CartesianMonoidalCategory.hom_ext
    · rw [Category.assoc, hcomp _ _ h₁, MonObj.one_comp]
    · rw [Category.assoc, hcomp _ _ h₂, MonObj.one_comp]
  have hw1 : w = 1 := by
    rw [← cancel_mono e.hom, hw, MonObj.one_comp]
  apply hx
  apply pt_injective
  apply G.i_injective
  rw [← hwdef, hw1, pt_zero, MonObj.one_comp]

/-- The maps `E → C_j`, `E' → C_j` of `exists_common_factor_of_prodIso` are `π`-equivariant when
`e` intertwines `π_n` with the diagonal `ρ₁ × ρ₂`. -/
theorem comp_iso_fst_equivariant (hu : ∀ n x, u n (torAct π _ x) = torAct π' _ (u n x))
    (G : Glue (Γ ℓ u n)) {C₁ C₂ : Over (Spec (.of k))} [GrpObj C₁] [GrpObj C₂]
    (ρ₁ : C₁ ⟶ C₁) (ρ₂ : C₂ ⟶ C₂) (e : G.B ≅ C₁ ⊗ C₂)
    (he : G.πB π π' hu ≫ e.hom = e.hom ≫ lift (fst C₁ C₂ ≫ ρ₁) (snd C₁ C₂ ≫ ρ₂)) :
    (G.i ≫ e.hom ≫ fst C₁ C₂) ≫ ρ₁ = π ≫ G.i ≫ e.hom ≫ fst C₁ C₂ ∧
    (G.i' ≫ e.hom ≫ fst C₁ C₂) ≫ ρ₁ = π' ≫ G.i' ≫ e.hom ≫ fst C₁ C₂ ∧
    (G.i ≫ e.hom ≫ snd C₁ C₂) ≫ ρ₂ = π ≫ G.i ≫ e.hom ≫ snd C₁ C₂ ∧
    (G.i' ≫ e.hom ≫ snd C₁ C₂) ≫ ρ₂ = π' ≫ G.i' ≫ e.hom ≫ snd C₁ C₂ := by
  have hf : e.hom ≫ fst C₁ C₂ ≫ ρ₁ = G.πB π π' hu ≫ e.hom ≫ fst C₁ C₂ := by
    calc e.hom ≫ fst C₁ C₂ ≫ ρ₁
        = e.hom ≫ (lift (fst C₁ C₂ ≫ ρ₁) (snd C₁ C₂ ≫ ρ₂) ≫ fst C₁ C₂) := by rw [lift_fst]
      _ = (e.hom ≫ lift (fst C₁ C₂ ≫ ρ₁) (snd C₁ C₂ ≫ ρ₂)) ≫ fst C₁ C₂ :=
          (Category.assoc _ _ _).symm
      _ = (G.πB π π' hu ≫ e.hom) ≫ fst C₁ C₂ := by rw [he]
      _ = _ := Category.assoc _ _ _
  have hs : e.hom ≫ snd C₁ C₂ ≫ ρ₂ = G.πB π π' hu ≫ e.hom ≫ snd C₁ C₂ := by
    calc e.hom ≫ snd C₁ C₂ ≫ ρ₂
        = e.hom ≫ (lift (fst C₁ C₂ ≫ ρ₁) (snd C₁ C₂ ≫ ρ₂) ≫ snd C₁ C₂) := by rw [lift_snd]
      _ = (e.hom ≫ lift (fst C₁ C₂ ≫ ρ₁) (snd C₁ C₂ ≫ ρ₂)) ≫ snd C₁ C₂ :=
          (Category.assoc _ _ _).symm
      _ = (G.πB π π' hu ≫ e.hom) ≫ snd C₁ C₂ := by rw [he]
      _ = _ := Category.assoc _ _ _
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [Category.assoc, Category.assoc, hf, ← Category.assoc, G.i_πB hu, Category.assoc]
  · rw [Category.assoc, Category.assoc, hf, ← Category.assoc, G.i'_πB hu, Category.assoc]
  · rw [Category.assoc, Category.assoc, hs, ← Category.assoc, G.i_πB hu, Category.assoc]
  · rw [Category.assoc, Category.assoc, hs, ← Category.assoc, G.i'_πB hu, Category.assoc]

end RamanujanWeil.Arith.Deuring.Geom.G7.Fin
