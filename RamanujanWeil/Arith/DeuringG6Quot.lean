import StacksFrontier.AlgebraicGeometry.Spaces.FreeGroupSchemeQuotient
import Mathlib.AlgebraicGeometry.Sites.Fpqc

/-!
# A3-ord, G6: quotients of commutative group schemes by finite locally free subgroups

Let `S` be a scheme, `A` a commutative group scheme over `S` and `j : G ⟶ A` a monomorphic
homomorphism from a finite locally free group scheme `G`, acting on `A` by translation
(`IsTranslation j`). If every finite set of points in a fibre of `A ⟶ S` lies in an affine
open (e.g. `A` projective over `S`, so in particular `A` an abelian variety), then:

* Stacks 07S7 (`AlgebraicGeometry.nonempty_finiteFlatQuotient_actionGroupoid_of_geometry`)
  gives a scheme `B` and a finite locally free surjective `q : A ⟶ B` whose kernel pair is
  `G ×_S A` (`TranslationQuotient`, `nonempty_translationQuotient`);
* `q` is an effective epimorphism (Mathlib, `Sites/Fpqc`), so morphisms out of `A` constant on
  `G`-orbits descend (`TranslationQuotient.exists_desc`);
* `B` carries a unique commutative group structure making `q` a homomorphism
  (`TranslationQuotient.grpObj`, `isMonHom_q`, `isCommMonObj`): the group law descends along
  the effective epimorphism `q ⊗ q` (also flat, quasi-compact, surjective);
* `ker q = G`: `x ≫ q = 1 ↔ x` factors through `j` (`comp_q_eq_one_iff`);
* universal property: every homomorphism `α : A ⟶ C` with `j ≫ α = 1` factors uniquely as
  `q ≫ β`, `β` a homomorphism (`exists_unique_isMonHom_desc`).

This is the general-dimension, all-characteristic core of G6 (`docs/ARITH_DEURING_G6.md`).
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory
  CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

universe u

namespace RamanujanWeil.Arith.Deuring.Geom.G6

section Flat

variable {S : Scheme.{u}}

/-- Flat, quasi-compact, surjective `.left`s are stable under `⊗` in `Over S`. -/
theorem fqs_tensorHom {X Y Z W : Over S} (f : X ⟶ Y) (g : Z ⟶ W)
    (hf : Flat f.left ∧ QuasiCompact f.left ∧ Surjective f.left)
    (hg : Flat g.left ∧ QuasiCompact g.left ∧ Surjective g.left) :
    Flat (f ⊗ₘ g).left ∧ QuasiCompact (f ⊗ₘ g).left ∧ Surjective (f ⊗ₘ g).left := by
  rw [Over.tensorHom_left]
  refine ⟨?_, ?_, ?_⟩
  · exact MorphismProperty.pullbackMap (P := @Flat) hf.1 hg.1 (Over.w f).symm (Over.w g).symm
  · exact MorphismProperty.pullbackMap (P := @QuasiCompact) hf.2.1 hg.2.1
      (Over.w f).symm (Over.w g).symm
  · exact MorphismProperty.pullbackMap (P := @Surjective) hf.2.2 hg.2.2
      (Over.w f).symm (Over.w g).symm

/-- A morphism in `Over S` whose underlying morphism is flat, quasi-compact and surjective is an
epimorphism. -/
theorem epi_of_fqs {X Y : Over S} (f : X ⟶ Y)
    (hf : Flat f.left ∧ QuasiCompact f.left ∧ Surjective f.left) : Epi f := by
  obtain ⟨h1, h2, h3⟩ := hf
  have : Epi f.left := inferInstance
  exact (Over.forget S).epi_of_epi_map this

/-- **Descent along a flat, quasi-compact, surjective morphism** (an effective epimorphism of
schemes, Mathlib `Sites/Fpqc`): a morphism `f` out of `X` which is constant on the fibres of
`p` on all `T`-points factors through `p`. -/
theorem exists_desc_of_fqs {X Y C : Over S} (p : X ⟶ Y)
    (hp : Flat p.left ∧ QuasiCompact p.left ∧ Surjective p.left) (f : X ⟶ C)
    (hf : ∀ ⦃T : Over S⦄ (x y : T ⟶ X), x ≫ p = y ≫ p → x ≫ f = y ≫ f) :
    ∃ f' : Y ⟶ C, p ≫ f' = f := by
  obtain ⟨h1, h2, h3⟩ := hp
  have hdesc : ∀ {Z : Scheme.{u}} (g₁ g₂ : Z ⟶ X.left), g₁ ≫ p.left = g₂ ≫ p.left →
      g₁ ≫ f.left = g₂ ≫ f.left := fun {Z} g₁ g₂ hg => by
    let T : Over S := Over.mk (g₂ ≫ X.hom)
    have hw : g₁ ≫ X.hom = T.hom := by
      show g₁ ≫ X.hom = g₂ ≫ X.hom
      rw [← Over.w p, ← Category.assoc, hg, Category.assoc]
    let x : T ⟶ X := Over.homMk g₁ hw
    let y : T ⟶ X := Over.homMk g₂ rfl
    exact congrArg CommaMorphism.left (hf x y (Over.OverMorphism.ext (by simpa [x, y] using hg)))
  set f'' : Y.left ⟶ C.left := EffectiveEpi.desc p.left f.left hdesc
  have hfac : p.left ≫ f'' = f.left := EffectiveEpi.fac p.left f.left hdesc
  have hw : f'' ≫ C.hom = Y.hom := by
    rw [← cancel_epi p.left, ← Category.assoc, hfac, Over.w f, Over.w p]
  exact ⟨Over.homMk f'' hw, Over.OverMorphism.ext (by simpa using hfac)⟩

theorem fqs_id (X : Over S) : Flat (𝟙 X : X ⟶ X).left ∧ QuasiCompact (𝟙 X : X ⟶ X).left ∧
    Surjective (𝟙 X : X ⟶ X).left :=
  ⟨inferInstanceAs (Flat (𝟙 X.left)), inferInstanceAs (QuasiCompact (𝟙 X.left)),
    inferInstanceAs (Surjective (𝟙 X.left))⟩

end Flat

variable {S : Scheme.{u}} {A G : Over S} [GrpObj A] [GrpObj G] [ModObj G A]

/-- `G` acts on `A` by translation through `j`. -/
def IsTranslation (j : G ⟶ A) : Prop :=
  ∀ ⦃T : Over S⦄ (g : T ⟶ G) (x : T ⟶ A), g • x = (g ≫ j) * x

/-- Translation through a monomorphism is a free action (Stacks 07S1). -/
theorem isFreeAction_of_isTranslation (j : G ⟶ A) [Mono j] (h : IsTranslation j) :
    IsFreeAction G A := fun _ =>
  { left_cancel' := fun g x y hxy => by
      rw [h, h] at hxy
      exact mul_left_cancel hxy
    right_cancel' := fun g g' x hx => by
      rw [h, h] at hx
      exact (cancel_mono j).mp (mul_right_cancel hx) }

/-- A quotient of `A` by the translation action of `G`: a finite locally free surjective
`q : A ⟶ B` over `S` whose kernel pair is `(g, x) ↦ (g • x, x)`. -/
structure TranslationQuotient (j : G ⟶ A) where
  /-- The quotient `A/G`. -/
  B : Over S
  /-- The quotient map. -/
  q : A ⟶ B
  finiteLocallyFree : Stacks.Morphisms.IsFiniteLocallyFree q.left
  surjective : Surjective q.left
  isPullback : IsPullback (γ[G, A]).left (snd G A).left q.left q.left
  /-- The action is translation through `j`. -/
  isTranslation : IsTranslation j

/-- **Existence of the quotient (Stacks 07S7).** -/
theorem nonempty_translationQuotient (j : G ⟶ A) [Mono j] (hj : IsTranslation j)
    [Stacks.Morphisms.IsFiniteLocallyFree G.hom]
    (hfib : HasAffineFinitePointsInFibres A.hom) : Nonempty (TranslationQuotient j) := by
  obtain ⟨Q⟩ := nonempty_finiteFlatQuotient_actionGroupoid G A
    (isFreeAction_of_isTranslation j hj) hfib
  exact ⟨{ B := Q.space
           q := Over.homMk Q.quotientMap.left
             ((Over.w Q.quotientMap).trans (Category.comp_id A.hom))
           finiteLocallyFree := Q.finiteLocallyFree
           surjective := Q.surjective
           isPullback := Q.isPullback_left
           isTranslation := hj }⟩

namespace TranslationQuotient

variable {j : G ⟶ A} (Q : TranslationQuotient j)

theorem fqs : Flat Q.q.left ∧ QuasiCompact Q.q.left ∧ Surjective Q.q.left := by
  obtain ⟨hfin, hflat, -⟩ :=
    (Stacks.Morphisms.isFiniteLocallyFree_iff_isFinite_flat_locallyOfFinitePresentation
      Q.q.left).mp Q.finiteLocallyFree
  exact ⟨hflat, inferInstance, Q.surjective⟩

theorem smul_comp_q {T : Over S} (g : T ⟶ G) (x : T ⟶ A) : (g • x) ≫ Q.q = x ≫ Q.q := by
  have hw : γ[G, A] ≫ Q.q = snd G A ≫ Q.q := Over.OverMorphism.ext Q.isPullback.w
  rw [CategoryTheory.Hom.smul_def, Category.assoc, hw, lift_snd_assoc]

/-- Two points of `A` with the same image in `B` differ by a point of `G`. -/
theorem exists_smul_eq {T : Over S} (x y : T ⟶ A) (h : x ≫ Q.q = y ≫ Q.q) :
    ∃ g : T ⟶ G, g • y = x := by
  have hl : x.left ≫ Q.q.left = y.left ≫ Q.q.left := congrArg CommaMorphism.left h
  set r := Q.isPullback.lift x.left y.left hl
  have hr : r ≫ (G ⊗ A).hom = T.hom := by
    rw [← Over.w (snd G A), ← Category.assoc, Q.isPullback.lift_snd]
    exact Over.w y
  let r' : T ⟶ G ⊗ A := Over.homMk r hr
  refine ⟨r' ≫ fst G A, ?_⟩
  have hy : r' ≫ snd G A = y := Over.OverMorphism.ext (by simp [r', r])
  rw [← hy, CategoryTheory.Hom.smul_def, ← comp_lift, lift_fst_snd, Category.comp_id]
  exact Over.OverMorphism.ext (Q.isPullback.lift_fst _ _ _)

/-- Two points of `A` have the same image in `B` iff they differ by a point of `G`. -/
theorem comp_q_eq_iff {T : Over S} (x y : T ⟶ A) :
    x ≫ Q.q = y ≫ Q.q ↔ ∃ g : T ⟶ G, x = (g ≫ j) * y := by
  constructor
  · intro h
    obtain ⟨g, hg⟩ := Q.exists_smul_eq x y h
    exact ⟨g, by rw [← hg, Q.isTranslation]⟩
  · rintro ⟨g, rfl⟩
    rw [← Q.isTranslation, Q.smul_comp_q]

/-- `B` is a quotient: morphisms out of `B` are determined by their composite with `q`. -/
instance epi_q : Epi Q.q := epi_of_fqs Q.q Q.fqs

/-- **Descent** of a morphism constant on `G`-orbits. -/
theorem exists_desc {C : Over S} (f : A ⟶ C)
    (hf : ∀ ⦃T : Over S⦄ (g : T ⟶ G) (x : T ⟶ A), ((g ≫ j) * x) ≫ f = x ≫ f) :
    ∃ f' : Q.B ⟶ C, Q.q ≫ f' = f :=
  exists_desc_of_fqs Q.q Q.fqs f fun _ x y h => by
    obtain ⟨g, rfl⟩ := (Q.comp_q_eq_iff x y).mp h
    exact hf g y

/-- **Kernel of `q`.** A point of `A` maps to `1` in `B` iff it comes from `G`. -/
theorem comp_q_eq_one_iff {T : Over S} (x : T ⟶ A) :
    x ≫ Q.q = (1 : T ⟶ A) ≫ Q.q ↔ ∃ g : T ⟶ G, g ≫ j = x := by
  rw [Q.comp_q_eq_iff]
  simp only [mul_one]
  exact ⟨fun ⟨g, hg⟩ => ⟨g, hg.symm⟩, fun ⟨g, hg⟩ => ⟨g, hg.symm⟩⟩

section Group

variable [IsCommMonObj A] [IsMonHom j]

theorem fqs_qq : Flat (Q.q ⊗ₘ Q.q).left ∧ QuasiCompact (Q.q ⊗ₘ Q.q).left ∧
    Surjective (Q.q ⊗ₘ Q.q).left := fqs_tensorHom _ _ Q.fqs Q.fqs

theorem exists_mul : ∃ m : Q.B ⊗ Q.B ⟶ Q.B, (Q.q ⊗ₘ Q.q) ≫ m = μ[A] ≫ Q.q := by
  refine exists_desc_of_fqs _ Q.fqs_qq _ fun T x y h => ?_
  have h1 : (x ≫ fst A A) ≫ Q.q = (y ≫ fst A A) ≫ Q.q := by
    simpa using congrArg (· ≫ fst Q.B Q.B) h
  have h2 : (x ≫ snd A A) ≫ Q.q = (y ≫ snd A A) ≫ Q.q := by
    simpa using congrArg (· ≫ snd Q.B Q.B) h
  obtain ⟨g₁, hg₁⟩ := (Q.comp_q_eq_iff _ _).mp h1
  obtain ⟨g₂, hg₂⟩ := (Q.comp_q_eq_iff _ _).mp h2
  have ex : ∀ z : T ⟶ A ⊗ A, z ≫ μ[A] = (z ≫ fst A A) * (z ≫ snd A A) := fun z => by
    rw [Hom.mul_def, ← comp_lift, lift_fst_snd, Category.comp_id]
  rw [← Category.assoc, ← Category.assoc, ex, ex]
  refine (Q.comp_q_eq_iff _ _).mpr ⟨g₁ * g₂, ?_⟩
  rw [hg₁, hg₂, MonObj.mul_comp]
  ac_rfl

theorem exists_inv : ∃ i : Q.B ⟶ Q.B, Q.q ≫ i = ι[A] ≫ Q.q := by
  refine exists_desc_of_fqs _ Q.fqs _ fun T x y h => ?_
  obtain ⟨g, rfl⟩ := (Q.comp_q_eq_iff _ _).mp h
  rw [← Category.assoc, ← Category.assoc, ← Hom.inv_def, ← Hom.inv_def]
  refine (Q.comp_q_eq_iff _ _).mpr ⟨g⁻¹, ?_⟩
  rw [mul_inv, show g⁻¹ ≫ j = (g ≫ j)⁻¹ from map_inv (IsMonHom.monoidHom j T) g]

/-- The multiplication of `B`. -/
noncomputable def mulB : Q.B ⊗ Q.B ⟶ Q.B := Q.exists_mul.choose
/-- The inverse of `B`. -/
noncomputable def invB : Q.B ⟶ Q.B := Q.exists_inv.choose
/-- The unit of `B`. -/
noncomputable def oneB : 𝟙_ (Over S) ⟶ Q.B := η[A] ≫ Q.q

theorem qq_mulB : (Q.q ⊗ₘ Q.q) ≫ Q.mulB = μ[A] ≫ Q.q := Q.exists_mul.choose_spec
theorem q_invB : Q.q ≫ Q.invB = ι[A] ≫ Q.q := Q.exists_inv.choose_spec

theorem lift_mulB {T : Over S} (x y : T ⟶ A) :
    lift (x ≫ Q.q) (y ≫ Q.q) ≫ Q.mulB = (x * y) ≫ Q.q := by
  rw [← lift_map, Category.assoc, qq_mulB, Hom.mul_def, Category.assoc]

theorem comp_invB {T : Over S} (x : T ⟶ A) : (x ≫ Q.q) ≫ Q.invB = x⁻¹ ≫ Q.q := by
  rw [Category.assoc, q_invB, Hom.inv_def, Category.assoc]

theorem comp_oneB {T : Over S} (t : T ⟶ 𝟙_ (Over S)) : t ≫ Q.oneB = (1 : T ⟶ A) ≫ Q.q := by
  rw [Hom.one_def, oneB, toUnit_unique t (toUnit T), Category.assoc]

/-- Morphisms out of `B` are determined on points coming from `A`. -/
theorem hom_ext₁ {C : Over S} {f₁ f₂ : Q.B ⟶ C}
    (h : ∀ ⦃T : Over S⦄ (x : T ⟶ A), (x ≫ Q.q) ≫ f₁ = (x ≫ Q.q) ≫ f₂) : f₁ = f₂ := by
  rw [← cancel_epi Q.q]
  simpa using h (𝟙 A)

/-- Morphisms out of `B ⊗ B` are determined on points coming from `A`. -/
theorem hom_ext₂ {C : Over S} {f₁ f₂ : Q.B ⊗ Q.B ⟶ C}
    (h : ∀ ⦃T : Over S⦄ (x y : T ⟶ A),
      lift (x ≫ Q.q) (y ≫ Q.q) ≫ f₁ = lift (x ≫ Q.q) (y ≫ Q.q) ≫ f₂) : f₁ = f₂ := by
  have := epi_of_fqs _ Q.fqs_qq
  rw [← cancel_epi (Q.q ⊗ₘ Q.q), ← lift_fst_comp_snd_comp]
  exact h _ _

/-- Morphisms out of `(B ⊗ B) ⊗ B` are determined on points coming from `A`. -/
theorem hom_ext₃ {C : Over S} {f₁ f₂ : (Q.B ⊗ Q.B) ⊗ Q.B ⟶ C}
    (h : ∀ ⦃T : Over S⦄ (x y z : T ⟶ A),
      lift (lift (x ≫ Q.q) (y ≫ Q.q)) (z ≫ Q.q) ≫ f₁ =
        lift (lift (x ≫ Q.q) (y ≫ Q.q)) (z ≫ Q.q) ≫ f₂) : f₁ = f₂ := by
  have := epi_of_fqs _ (fqs_tensorHom _ _ Q.fqs_qq Q.fqs)
  rw [← cancel_epi ((Q.q ⊗ₘ Q.q) ⊗ₘ Q.q)]
  have e : (Q.q ⊗ₘ Q.q) ⊗ₘ Q.q = lift (lift ((fst _ _ ≫ fst A A) ≫ Q.q)
      ((fst _ _ ≫ snd A A) ≫ Q.q)) (snd _ _ ≫ Q.q) := by
    ext <;> simp
  rw [e]
  exact h _ _ _

/-- Morphisms out of `𝟙 ⊗ B` are determined on points coming from `A`. -/
theorem hom_ext_unit_left {C : Over S} {f₁ f₂ : 𝟙_ (Over S) ⊗ Q.B ⟶ C}
    (h : ∀ ⦃T : Over S⦄ (x : T ⟶ A),
      lift (toUnit T) (x ≫ Q.q) ≫ f₁ = lift (toUnit T) (x ≫ Q.q) ≫ f₂) : f₁ = f₂ := by
  have := epi_of_fqs _ (fqs_tensorHom _ _ (fqs_id (𝟙_ (Over S))) Q.fqs)
  rw [← cancel_epi (𝟙 (𝟙_ (Over S)) ⊗ₘ Q.q)]
  have e : 𝟙 (𝟙_ (Over S)) ⊗ₘ Q.q = lift (toUnit _) (snd _ _ ≫ Q.q) := by
    apply CartesianMonoidalCategory.hom_ext
    · apply toUnit_unique
    · simp [leftUnitor_hom]
  rw [e]
  exact h _

/-- Morphisms out of `B ⊗ 𝟙` are determined on points coming from `A`. -/
theorem hom_ext_unit_right {C : Over S} {f₁ f₂ : Q.B ⊗ 𝟙_ (Over S) ⟶ C}
    (h : ∀ ⦃T : Over S⦄ (x : T ⟶ A),
      lift (x ≫ Q.q) (toUnit T) ≫ f₁ = lift (x ≫ Q.q) (toUnit T) ≫ f₂) : f₁ = f₂ := by
  have := epi_of_fqs _ (fqs_tensorHom _ _ Q.fqs (fqs_id (𝟙_ (Over S))))
  rw [← cancel_epi (Q.q ⊗ₘ 𝟙 (𝟙_ (Over S)))]
  have e : Q.q ⊗ₘ 𝟙 (𝟙_ (Over S)) = lift (fst _ _ ≫ Q.q) (toUnit _) := by
    apply CartesianMonoidalCategory.hom_ext
    · simp [rightUnitor_hom]
    · apply toUnit_unique
  rw [e]
  exact h _

/-- **The group structure on the quotient `B = A/G`.** -/
@[instance_reducible]
noncomputable def grpObj : GrpObj Q.B where
  one := Q.oneB
  mul := Q.mulB
  inv := Q.invB
  one_mul := Q.hom_ext_unit_left fun T x => by
    rw [lift_whiskerRight_assoc, comp_oneB, lift_mulB, one_mul, leftUnitor_hom, lift_snd]
  mul_one := Q.hom_ext_unit_right fun T x => by
    rw [lift_whiskerLeft_assoc, comp_oneB, lift_mulB, mul_one, rightUnitor_hom, lift_fst]
  mul_assoc := Q.hom_ext₃ fun T x y z => by
    rw [lift_whiskerRight_assoc, lift_mulB, lift_mulB, lift_lift_associator_hom_assoc,
      lift_whiskerLeft_assoc, lift_mulB, lift_mulB, mul_assoc]
  left_inv := Q.hom_ext₁ fun T x => by
    rw [comp_lift_assoc, Category.comp_id, comp_invB, lift_mulB, inv_mul_cancel,
      comp_toUnit_assoc, comp_oneB]
  right_inv := Q.hom_ext₁ fun T x => by
    rw [comp_lift_assoc, Category.comp_id, comp_invB, lift_mulB, mul_inv_cancel,
      comp_toUnit_assoc, comp_oneB]

attribute [instance] grpObj

/-- `q : A ⟶ A/G` is a homomorphism. -/
instance isMonHom_q : IsMonHom Q.q where
  one_hom := rfl
  mul_hom := Q.qq_mulB.symm

/-- `A/G` is commutative. -/
instance isCommMonObj : IsCommMonObj Q.B where
  mul_comm := Q.hom_ext₂ fun T x y => by
    show lift _ _ ≫ (β_ Q.B Q.B).hom ≫ Q.mulB = lift _ _ ≫ Q.mulB
    rw [lift_braiding_hom_assoc, lift_mulB, lift_mulB, mul_comm]

/-- **Kernel of `q`**, group form: `x ≫ q = 1 ↔ x` comes from `G`. -/
theorem comp_q_eq_one_iff' {T : Over S} (x : T ⟶ A) :
    x ≫ Q.q = 1 ↔ ∃ g : T ⟶ G, g ≫ j = x := by
  rw [← Q.comp_q_eq_one_iff, MonObj.one_comp]

/-- **Universal property of `A ⟶ A/G`.** A homomorphism `α : A ⟶ C` killing `G` factors as
`q ≫ β` with `β` a homomorphism; `β` is unique since `q` is an epimorphism. -/
theorem exists_isMonHom_desc {C : Over S} [GrpObj C] (α : A ⟶ C) [IsMonHom α]
    (hα : j ≫ α = 1) : ∃ β : Q.B ⟶ C, IsMonHom β ∧ Q.q ≫ β = α := by
  obtain ⟨β, hβ⟩ := Q.exists_desc α fun T g x => by
    rw [MonObj.mul_comp, Category.assoc, hα, MonObj.comp_one, one_mul]
  refine ⟨β, ⟨?_, ?_⟩, hβ⟩
  · show (η[A] ≫ Q.q) ≫ β = η
    rw [Category.assoc, hβ, IsMonHom.one_hom]
  · refine Q.hom_ext₂ fun T x y => ?_
    show lift _ _ ≫ Q.mulB ≫ β = _
    rw [← Category.assoc, lift_mulB, Category.assoc, hβ, MonObj.mul_comp, lift_map_assoc,
      Category.assoc, Category.assoc, hβ, Hom.mul_def]

/-- Uniqueness in the universal property. -/
theorem desc_unique {C : Over S} (β₁ β₂ : Q.B ⟶ C) (h : Q.q ≫ β₁ = Q.q ≫ β₂) : β₁ = β₂ :=
  (cancel_epi Q.q).mp h

end Group

end TranslationQuotient

end RamanujanWeil.Arith.Deuring.Geom.G6
