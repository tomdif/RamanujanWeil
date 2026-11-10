import RamanujanWeil.Arith.DeuringDescentRigid
import RamanujanWeil.Arith.DeuringG7Tate
import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteLocallyFreeProper

/-!
# A3-ord, descent: semilinear automorphisms descend to quotients

`docs/ARITH_DEURING_DESCENT.md` §2. Let `k` be algebraically closed and `Φ : Spec k ⟶ Spec k` an
isomorphism (later the `q`-power Frobenius). A *`Φ`-semilinear* morphism `ψ : X ⟶ Y` of
`k`-schemes is a morphism of schemes with `ψ ≫ Y.hom = X.hom ≫ Φ`; it is the same as a
`k`-morphism `X ⟶ Φ^*Y` (`twHom`). The twist `Φ^* = Over.pullback Φ` is a monoidal functor, so
`Φ^*Y` is a group scheme when `Y` is.

* `isMonHom_twHom`: a pointed semilinear map between abelian varieties is a homomorphism into
  the twist (rigidity, `DeuringDescentRigid`).
* **`exists_desc`**: let `G : Glue Γ` be a quotient `q : A ⟶ B = A/Γ` and `ψ` a pointed
  semilinear map on `A` with `ψ(Γ) ⊆ Φ(Γ)` (on points). Then `ψ` descends: there is a
  semilinear `ψ_B` on `B` with `q ≫ ψ_B = ψ ≫ q`.
* **`exists_desc_iso`**: if `ψ` is an isomorphism and its inverse also maps `Γ` to `Γ`, then
  `ψ_B` is an isomorphism (`q` is an epimorphism of schemes).
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory
  CartesianMonoidalCategory MonObj
open scoped CategoryTheory.MonObj CategoryTheory.Obj

universe u

noncomputable section

namespace RamanujanWeil.Arith.Deuring.Descent

open RamanujanWeil.Arith.Deuring.Geom.G7

variable {k : Type u} [Field k]

/-- An abelian variety squared is integral. -/
theorem isIntegral_tensor (A : Over (Spec (.of k))) [GrpObj A]
    [AlgebraicGeometry.IsAbelianVariety k A] : IsIntegral (A ⊗ A).left := by
  have : IsIntegral A.left := GeometricallyIntegral.isIntegral_of_subsingleton A.hom
  have : IsLocallyNoetherian A.left := LocallyOfFiniteType.isLocallyNoetherian A.hom
  have : Flat A.hom := inferInstance
  have : UniversallyOpen A.hom := inferInstance
  show IsIntegral (pullback A.hom A.hom)
  exact GeometricallyIntegral.isIntegral_of_isLocallyNoetherian (pullback.fst A.hom A.hom)

/-- **Pointed morphisms between abelian varieties are homomorphisms.** -/
theorem isMonHom_of_pointed' [IsAlgClosed k] {A C : Over (Spec (.of k))} [GrpObj A] [GrpObj C]
    [AlgebraicGeometry.IsAbelianVariety k A] [IsSeparated C.hom] [LocallyOfFiniteType C.hom]
    (f : A ⟶ C) (hf : η[A] ≫ f = η[C]) : IsMonHom f :=
  have := isIntegral_tensor A
  isMonHom_of_pointed f hf

variable (Φ : Spec (.of k) ⟶ Spec (.of k))

/-- The twist `Φ^*`. -/
abbrev Tw : Over (Spec (.of k)) ⥤ Over (Spec (.of k)) := Over.pullback Φ

instance grpTw (X : Over (Spec (.of k))) [GrpObj X] : GrpObj ((Tw Φ).obj X) := Functor.grpObjObj

instance (X : Over (Spec (.of k))) [IsSeparated X.hom] : IsSeparated ((Tw Φ).obj X).hom := by
  dsimp; infer_instance

instance (X : Over (Spec (.of k))) [LocallyOfFiniteType X.hom] :
    LocallyOfFiniteType ((Tw Φ).obj X).hom := by
  dsimp; infer_instance

/-- A `Φ`-semilinear map as a `k`-morphism into the twist. -/
def twHom {X Y : Over (Spec (.of k))} (ψ : X.left ⟶ Y.left) (h : ψ ≫ Y.hom = X.hom ≫ Φ) :
    X ⟶ (Tw Φ).obj Y :=
  Over.homMk (pullback.lift ψ X.hom h) (pullback.lift_snd _ _ _)

@[simp]
theorem twHom_left_fst {X Y : Over (Spec (.of k))} (ψ : X.left ⟶ Y.left)
    (h : ψ ≫ Y.hom = X.hom ≫ Φ) : (twHom Φ ψ h).left ≫ pullback.fst Y.hom Φ = ψ :=
  pullback.lift_fst _ _ _

/-- The first projection of a twisted point. -/
theorem tw_left_snd {X Y : Over (Spec (.of k))} (g : X ⟶ (Tw Φ).obj Y) :
    g.left ≫ pullback.snd Y.hom Φ = X.hom :=
  Over.w g

theorem tw_ext {X Y : Over (Spec (.of k))} {g₁ g₂ : X ⟶ (Tw Φ).obj Y}
    (h : g₁.left ≫ pullback.fst Y.hom Φ = g₂.left ≫ pullback.fst Y.hom Φ) : g₁ = g₂ := by
  ext1
  apply pullback.hom_ext h
  rw [tw_left_snd, tw_left_snd]

theorem map_left_fst {X Y : Over (Spec (.of k))} (f : X ⟶ Y) :
    ((Tw Φ).map f).left ≫ pullback.fst Y.hom Φ = pullback.fst X.hom Φ ≫ f.left := by
  simp only [Over.pullback]
  erw [pullback.lift_fst]

/-- The unit of the twist, on the first projection. -/
theorem η_tw_fst (Y : Over (Spec (.of k))) [GrpObj Y] :
    (η[(Tw Φ).obj Y]).left ≫ pullback.fst Y.hom Φ = Φ ≫ η[Y].left := by
  rw [Functor.obj.η_def, Over.comp_left, Category.assoc, map_left_fst, ← Category.assoc]
  congr 1
  have h1 : (Functor.LaxMonoidal.ε (Tw Φ)).left ≫ pullback.snd (𝟙_ (Over (Spec (.of k)))).hom Φ
      = 𝟙 _ := Over.w (Functor.LaxMonoidal.ε (Tw Φ))
  have h2 := pullback.condition (f := (𝟙_ (Over (Spec (.of k)))).hom) (g := Φ)
  have h2' : pullback.fst (𝟙_ (Over (Spec (.of k)))).hom Φ =
      pullback.snd (𝟙_ (Over (Spec (.of k)))).hom Φ ≫ Φ := (Category.comp_id _).symm.trans h2
  rw [h2', ← Category.assoc, h1, Category.id_comp]

/-- A point of the twist is `1` iff its first projection is `Φ ≫ e`. -/
theorem eq_one_tw {Y : Over (Spec (.of k))} [GrpObj Y] (x : Pt ((Tw Φ).obj Y))
    (h : x.left ≫ pullback.fst Y.hom Φ = Φ ≫ η[Y].left) : x = 1 := by
  apply tw_ext
  rw [h, show (1 : Pt ((Tw Φ).obj Y)) = η[(Tw Φ).obj Y] from
    (Hom.one_def).trans (Category.id_comp _), η_tw_fst]

theorem one_left {Y : Over (Spec (.of k))} [GrpObj Y] : (1 : Pt Y).left = η[Y].left := by
  rw [show (1 : Pt Y) = η[Y] from (Hom.one_def).trans (Category.id_comp _)]

/-- **A pointed semilinear map out of an abelian variety is a homomorphism into the twist.** -/
theorem isMonHom_twHom [IsAlgClosed k] {X Y : Over (Spec (.of k))} [GrpObj X] [GrpObj Y]
    [AlgebraicGeometry.IsAbelianVariety k X] [IsSeparated Y.hom] [LocallyOfFiniteType Y.hom]
    (ψ : X.left ⟶ Y.left) (h : ψ ≫ Y.hom = X.hom ≫ Φ)
    (hη : η[X].left ≫ ψ = Φ ≫ η[Y].left) : IsMonHom (twHom Φ ψ h) := by
  refine isMonHom_of_pointed' _ ?_
  apply tw_ext
  rw [Over.comp_left, Category.assoc, twHom_left_fst, hη, η_tw_fst]

section Desc

variable [IsAlgClosed k] {A : Over (Spec (.of k))} [GrpObj A]
  [AlgebraicGeometry.IsAbelianVariety k A] {Γ : Subgroup (Pt A)} (G : Glue Γ)

/-- **Semilinear maps descend to quotients.** -/
theorem exists_desc (ψ : A.left ⟶ A.left) (h : ψ ≫ A.hom = A.hom ≫ Φ)
    (hη : η[A].left ≫ ψ = Φ ≫ η[A].left)
    (hΓ : ∀ x ∈ Γ, ∃ y ∈ Γ, x.left ≫ ψ = Φ ≫ y.left) :
    ∃ ψB : G.B.left ⟶ G.B.left, ψB ≫ G.B.hom = G.B.hom ≫ Φ ∧ G.q.left ≫ ψB = ψ ≫ G.q.left := by
  have := isMonHom_twHom Φ ψ h hη
  let α : A ⟶ (Tw Φ).obj G.B := twHom Φ ψ h ≫ (Tw Φ).map G.q
  have hα : ∀ x ∈ Γ, x ≫ α = 1 := by
    intro x hx
    obtain ⟨y, hy, hxy⟩ := hΓ x hx
    apply eq_one_tw
    simp only [α, Over.comp_left, Category.assoc, map_left_fst]
    rw [← Category.assoc (twHom Φ ψ h).left, twHom_left_fst, ← Category.assoc, hxy,
      Category.assoc, ← Over.comp_left, (G.ker y).2 hy, one_left]
  obtain ⟨β, -, hβ⟩ := (G.univ _ α hα).exists
  refine ⟨β.left ≫ pullback.fst G.B.hom Φ, ?_, ?_⟩
  · rw [Category.assoc, pullback.condition, ← Category.assoc, tw_left_snd]
  · rw [← Category.assoc, ← Over.comp_left, hβ]
    simp only [α, Over.comp_left, Category.assoc, map_left_fst]
    rw [← Category.assoc (twHom Φ ψ h).left, twHom_left_fst]

/-- `q` is an epimorphism of schemes. -/
theorem epi_q : Epi G.q.left := by
  have := G.rank
  have := Stacks.Morphisms.flat_of_isFiniteLocallyFreeOfRank G.q.left (Nat.card Γ)
  have := G.surj
  exact Flat.epi_of_flat_of_surjective _

/-- **Semilinear automorphisms descend to automorphisms.** -/
theorem exists_desc_iso [IsIso Φ] (ψ : A.left ⟶ A.left) [IsIso ψ] (h : ψ ≫ A.hom = A.hom ≫ Φ)
    (hη : η[A].left ≫ ψ = Φ ≫ η[A].left)
    (hΓ : ∀ x ∈ Γ, ∃ y ∈ Γ, x.left ≫ ψ = Φ ≫ y.left)
    (hΓ' : ∀ x ∈ Γ, ∃ y ∈ Γ, x.left ≫ inv ψ = inv Φ ≫ y.left) :
    ∃ ψB : G.B.left ≅ G.B.left, ψB.hom ≫ G.B.hom = G.B.hom ≫ Φ ∧
      G.q.left ≫ ψB.hom = ψ ≫ G.q.left := by
  have := epi_q G
  obtain ⟨ψB, h1, h2⟩ := exists_desc Φ G ψ h hη hΓ
  have h' : inv ψ ≫ A.hom = A.hom ≫ inv Φ := by
    rw [IsIso.eq_comp_inv, Category.assoc, ← h, IsIso.inv_hom_id_assoc]
  have hη' : η[A].left ≫ inv ψ = inv Φ ≫ η[A].left := by
    rw [IsIso.eq_inv_comp, ← Category.assoc, ← hη, Category.assoc, IsIso.hom_inv_id,
      Category.comp_id]
  obtain ⟨ψB', h1', h2'⟩ := exists_desc (inv Φ) G (inv ψ) h' hη' hΓ'
  refine ⟨⟨ψB, ψB', ?_, ?_⟩, h1, h2⟩
  · rw [← cancel_epi G.q.left, reassoc_of% h2, h2', IsIso.hom_inv_id_assoc, Category.comp_id]
  · rw [← cancel_epi G.q.left, reassoc_of% h2', h2, IsIso.inv_hom_id_assoc, Category.comp_id]

end Desc

/-- If `ψ` is injective on `Γ`-points (it is a monomorphism) and maps `Γ` into `Φ(Γ)`, with `Γ`
finite, then `ψ⁻¹` maps `Γ` into `Φ⁻¹(Γ)`. -/
theorem inv_mem_of_finite [IsIso Φ] {A : Over (Spec (.of k))} [GrpObj A] {Γ : Subgroup (Pt A)}
    [Finite Γ] (ψ : A.left ⟶ A.left) [IsIso ψ]
    (hΓ : ∀ x ∈ Γ, ∃ y ∈ Γ, x.left ≫ ψ = Φ ≫ y.left) :
    ∀ x ∈ Γ, ∃ y ∈ Γ, x.left ≫ inv ψ = inv Φ ≫ y.left := by
  classical
  let f : Γ → Γ := fun x => ⟨(hΓ x.1 x.2).choose, (hΓ x.1 x.2).choose_spec.1⟩
  have hf : ∀ x : Γ, x.1.left ≫ ψ = Φ ≫ (f x).1.left := fun x => (hΓ x.1 x.2).choose_spec.2
  have hinj : Function.Injective f := by
    intro x₁ x₂ he
    have h1 := hf x₁
    have h2 := hf x₂
    rw [he, ← h2] at h1
    have : x₁.1.left = x₂.1.left := (cancel_mono ψ).mp h1
    exact Subtype.ext (Over.OverMorphism.ext this)
  have hsurj := Finite.injective_iff_surjective.mp hinj
  intro x hx
  obtain ⟨y, hy⟩ := hsurj ⟨x, hx⟩
  refine ⟨y.1, y.2, ?_⟩
  have := hf y
  rw [hy] at this
  rw [IsIso.eq_inv_comp, ← Category.assoc, IsIso.comp_inv_eq]
  exact this.symm

end RamanujanWeil.Arith.Deuring.Descent
