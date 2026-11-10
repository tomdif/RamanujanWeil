import RamanujanWeil.Arith.DeuringG7Dual2

/-!
# A3-ord, G5 (kernel lattices): `Hom(A₀, A/Γ)` is the lattice of maps sending `A₀[n]` into `Γ`

`docs/ARITH_DEURING_G5.md` §3. Setting: `k` algebraically closed, `A₀`, `A` one-dimensional
abelian varieties over `k` with endomorphisms `π₀`, `π`; `Γ ⊆ A(k)` a finite `π`-stable subgroup
killed by `n`, `n` invertible in `k`; `G : Glue Γ` the G6 quotient `q : A → B = A/Γ`.

* `Glue.sMap`: the cofactor `s : B → A` with `q ≫ s = [n]` (`q_sMap`) and `s ≫ q = [n]`
  (`sMap_q`); `Glue.dim_B`: `dim B = 1`.
* `Glue.πB`: the Frobenius descended to `B` (`q ≫ π_B = π ≫ q`, `q_πB`), and `sMap_π`:
  `s ≫ π = π_B ≫ s`. So `q` and `s` are equivariant isogenies.
* **The kernel-lattice theorem** (`comp_sMap_mem`, `exists_comp_sMap_eq`, `comp_sMap_injective`,
  `comm_iff_comp_sMap`): `g ↦ g ≫ s` is a bijection from homomorphisms `A₀ ⟶ B` onto the
  homomorphisms `β : A₀ ⟶ A` with `β(A₀(k)[n]) ⊆ Γ`, and it preserves and reflects
  `π`-equivariance. In lattice terms: `Hom_π(A₀, A/Γ) ≅ L_Γ := {β ∈ Hom_π(A₀, A) : β(A₀[n]) ⊆ Γ}`,
  a sublattice of `Hom_π(A₀, A)` containing `n · Hom_π(A₀, A)`, `ℤ[π]`-equivariantly.

This uses only G6 (the quotient and its universal property), G3-div (a homomorphism killing
`A₀[n]` factors through `[n]`, `n` invertible) and G7-dual (nonzero homomorphisms of
one-dimensional abelian varieties are epimorphisms). No Tate module and no descent.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.MonObj

universe u

namespace RamanujanWeil.Arith.Deuring.G5

open RamanujanWeil.Arith.Deuring.Geom RamanujanWeil.Arith.Deuring.Geom.G7
  RamanujanWeil.Arith.Deuring.Dual2 Stacks.Groupoids

variable {k : Type u} [Field k] [IsAlgClosed k]
  {A₀ A : Over (Spec (.of k))} [GrpObj A₀] [GrpObj A]
  [AlgebraicGeometry.IsAbelianVariety k A₀] [AlgebraicGeometry.IsAbelianVariety k A]

/-- `(x ^ n) ≫ g = (x ≫ g) ^ n` and `1 ≫ g = 1` for a homomorphism `g`. -/
theorem zpow_comp_hom {X Y Z : Over (Spec (.of k))} [GrpObj Y] [GrpObj Z] (x : X ⟶ Y)
    (g : Y ⟶ Z) [IsMonHom g] (n : ℤ) : (x ^ n) ≫ g = (x ≫ g) ^ n :=
  GrpObj.zpow_comp x n g

namespace GlueS

variable {Γ : Subgroup (Pt A)} (G : Glue Γ)

theorem kill_zpow (n : ℤ) (hΓ : ∀ h ∈ Γ, h ^ n = 1) : ∀ h ∈ Γ, h ≫ (𝟙 A) ^ n = 1 :=
  fun h hh => by rw [comp_zpow_id, hΓ h hh]

/-- **The cofactor `s : A/Γ → A`** with `q ≫ s = [n]`. -/
noncomputable def sMap (n : ℤ) (hΓ : ∀ h ∈ Γ, h ^ n = 1) : G.B ⟶ A :=
  G.desc ((𝟙 A) ^ n) (kill_zpow n hΓ)

instance isMonHom_sMap (n : ℤ) (hΓ : ∀ h ∈ Γ, h ^ n = 1) : IsMonHom (sMap G n hΓ) :=
  G.desc_isMonHom _ _

theorem q_sMap (n : ℤ) (hΓ : ∀ h ∈ Γ, h ^ n = 1) : G.q ≫ sMap G n hΓ = (𝟙 A) ^ n :=
  G.q_desc _ _

theorem q_sMap_assoc (n : ℤ) (hΓ : ∀ h ∈ Γ, h ^ n = 1) {Z : Over (Spec (.of k))} (f : A ⟶ Z) :
    G.q ≫ sMap G n hΓ ≫ f = ((𝟙 A) ^ n) ≫ f := by
  rw [← Category.assoc, q_sMap]

theorem sMap_q (n : ℤ) (hΓ : ∀ h ∈ Γ, h ^ n = 1) : sMap G n hΓ ≫ G.q = (𝟙 G.B) ^ n := by
  apply G.cancel
  rw [q_sMap_assoc, zpow_id_comp_comm]

/-- **`dim A/Γ = 1`.** -/
theorem dim_B (n : ℤ) (hΓ : ∀ h ∈ Γ, h ^ n = 1) (hA : abelianVarietyDimension A = 1)
    (hn : n ≠ 0) : abelianVarietyDimension G.B = 1 := by
  have hNA : (𝟙 A : A ⟶ A) ^ n ≠ 1 := zpow_id_ne_one hA n hn
  have hsurjN : Surjective ((𝟙 A : A ⟶ A) ^ n).left := surjective_of_ne_one hA hA _ hNA
  have hs : Surjective (sMap G n hΓ).left := by
    have : Surjective (G.q ≫ sMap G n hΓ).left := by rw [q_sMap]; exact hsurjN
    rw [Over.comp_left] at this
    exact Surjective.of_comp G.q.left (sMap G n hΓ).left
  exact (dim_eq_of_surjective G.q (sMap G n hΓ) G.surj hs).symm.trans hA

theorem kill_π (π : A ⟶ A) (hπ : ∀ x ∈ Γ, x ≫ π ∈ Γ) : ∀ h ∈ Γ, h ≫ (π ≫ G.q) = 1 :=
  fun h hh => by rw [← Category.assoc]; exact (G.ker _).2 (hπ h hh)

/-- **The Frobenius descended to `A/Γ`.** -/
noncomputable def πB (π : A ⟶ A) [IsMonHom π] (hπ : ∀ x ∈ Γ, x ≫ π ∈ Γ) : G.B ⟶ G.B :=
  G.desc (π ≫ G.q) (kill_π G π hπ)

instance isMonHom_πB (π : A ⟶ A) [IsMonHom π] (hπ : ∀ x ∈ Γ, x ≫ π ∈ Γ) :
    IsMonHom (πB G π hπ) := G.desc_isMonHom _ _

theorem q_πB (π : A ⟶ A) [IsMonHom π] (hπ : ∀ x ∈ Γ, x ≫ π ∈ Γ) :
    G.q ≫ πB G π hπ = π ≫ G.q := G.q_desc _ _

/-- Any descended Frobenius is `πB`. -/
theorem eq_πB (π : A ⟶ A) [IsMonHom π] (hπ : ∀ x ∈ Γ, x ≫ π ∈ Γ) (π' : G.B ⟶ G.B)
    [IsMonHom π'] (h : G.q ≫ π' = π ≫ G.q) : π' = πB G π hπ :=
  G.cancel _ _ (by rw [h, q_πB])

/-- `s` is equivariant. -/
theorem sMap_π (n : ℤ) (hΓ : ∀ h ∈ Γ, h ^ n = 1) (π : A ⟶ A) [IsMonHom π]
    (hπ : ∀ x ∈ Γ, x ≫ π ∈ Γ) : sMap G n hΓ ≫ π = πB G π hπ ≫ sMap G n hΓ := by
  apply G.cancel
  rw [q_sMap_assoc, ← Category.assoc, q_πB, Category.assoc, q_sMap, zpow_id_comp_comm]

/-! ### The kernel-lattice theorem -/

/-- `g ≫ s` sends `A₀(k)[n]` into `Γ`. -/
theorem comp_sMap_mem (n : ℤ) (hΓ : ∀ h ∈ Γ, h ^ n = 1) (g : A₀ ⟶ G.B) [IsMonHom g]
    (x : Pt A₀) (hx : x ^ n = 1) : x ≫ (g ≫ sMap G n hΓ) ∈ Γ := by
  rw [← G.ker]
  simp only [Category.assoc]
  rw [sMap_q, comp_zpow_id, GrpObj.comp_zpow, ← zpow_comp_hom, hx, MonObj.one_comp]

/-- `g ↦ g ≫ s` is injective (on homomorphisms, `dim A₀ = 1`). -/
theorem comp_sMap_injective (n : ℤ) (hΓ : ∀ h ∈ Γ, h ^ n = 1)
    (hA₀ : abelianVarietyDimension A₀ = 1) (hn : n ≠ 0)
    (g₁ g₂ : A₀ ⟶ G.B) [IsMonHom g₁] [IsMonHom g₂]
    (h : g₁ ≫ sMap G n hΓ = g₂ ≫ sMap G n hΓ) : g₁ = g₂ := by
  have h1 := congrArg (· ≫ G.q) h
  simp only [Category.assoc, sMap_q] at h1
  rw [← zpow_id_comp_comm, ← zpow_id_comp_comm] at h1
  exact cancel_of_ne_one hA₀ hA₀ _ (zpow_id_ne_one hA₀ n hn) h1

/-- **Every `β : A₀ ⟶ A` with `β(A₀[n]) ⊆ Γ` factors as `g ≫ s`** (`n` invertible in `k`). -/
theorem exists_comp_sMap_eq (n : ℤ) (hΓ : ∀ h ∈ Γ, h ^ n = 1)
    (hA₀ : abelianVarietyDimension A₀ = 1) (hn : IsUnit (n : k))
    (β : A₀ ⟶ A) [IsMonHom β] (hβ : ∀ x : Pt A₀, x ^ n = 1 → x ≫ β ∈ Γ) :
    ∃ g : A₀ ⟶ G.B, IsMonHom g ∧ g ≫ sMap G n hΓ = β := by
  have hn0 : n ≠ 0 := by rintro rfl; simp at hn
  obtain ⟨g, hg, hgq⟩ := exists_isMonHom_zpow_comp_eq n hn (β ≫ G.q) (fun x hx => by
    rw [← Category.assoc]; exact (G.ker _).2 (hβ x hx))
  refine ⟨g, hg, ?_⟩
  apply cancel_of_ne_one hA₀ hA₀ _ (zpow_id_ne_one hA₀ n hn0)
  rw [← Category.assoc, hgq, Category.assoc, q_sMap, zpow_id_comp_comm]

/-- **`g ≫ s` is equivariant iff `g` is.** -/
theorem comm_iff_comp_sMap (n : ℤ) (hΓ : ∀ h ∈ Γ, h ^ n = 1)
    (hA₀ : abelianVarietyDimension A₀ = 1) (hn : n ≠ 0) (π : A ⟶ A) [IsMonHom π]
    (hπ : ∀ x ∈ Γ, x ≫ π ∈ Γ) (π₀ : A₀ ⟶ A₀) [IsMonHom π₀] (g : A₀ ⟶ G.B) [IsMonHom g] :
    g ≫ πB G π hπ = π₀ ≫ g ↔
      (g ≫ sMap G n hΓ) ≫ π = π₀ ≫ (g ≫ sMap G n hΓ) := by
  constructor
  · intro h
    rw [Category.assoc, sMap_π G n hΓ π hπ, ← Category.assoc, h, Category.assoc]
  · intro h
    apply comp_sMap_injective G n hΓ hA₀ hn
    rw [Category.assoc, ← sMap_π G n hΓ π hπ, ← Category.assoc, h, Category.assoc]

/-- `q` is nontrivial. -/
theorem q_ne_one (n : ℤ) (hΓ : ∀ h ∈ Γ, h ^ n = 1) (hA : abelianVarietyDimension A = 1)
    (hn : n ≠ 0) : G.q ≠ 1 := by
  intro h
  apply zpow_id_ne_one hA n hn
  rw [← q_sMap G n hΓ, h, MonObj.one_comp]

end GlueS

end RamanujanWeil.Arith.Deuring.G5
