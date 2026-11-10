import RamanujanWeil.Arith.DeuringG7CJacIso
import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.ArithmeticFrobeniusInverse
import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.ContainingSet

/-!
# A3-ord, G7 step C-Jac: interfaces with step C and step J

`docs/ARITH_DEURING_G7_CJAC.md`.

* **Common sites.** `exists_site_containing_family`: a ℕ-indexed family of schemes (the curves
  `Θ_n` of step J, or the `Y n` of step C after base change) together with `Spec K̄` lies in one
  big fppf site, so `exists_equivariant_jacobianIso` applies to any two of them.
* **From step C to the hypotheses of C-Jac.** Step C (`Genus2.exists_ne_iso_of_genus_eq_two`)
  delivers `φ : Y n ≅ Y m` with `φ.hom ≫ s m = s n` over the finite field `K`. Base change to an
  extension `L` (`fieldBaseChangeIso`) gives an isomorphism over `L`
  (`fieldBaseChangeIso_hom_snd`) that commutes with every Galois twist `id × Spec(τ)`
  (`fieldBaseChangeIso_hom_comp_galoisBaseChange`), in particular with the twisted Frobenius
  `Ψ = galoisBaseChange _ _ frob` that G1 uses for its Jacobian Frobenius.
* **Composition.** `IsEquivJacIso` (an isomorphism that is a homomorphism and intertwines given
  endomorphisms) is closed under `trans` and `symm`, so C-Jac composes with the step-J
  isomorphisms `Jac(Θ_n) ≅ B_n` to give the `B_n ≅ B_m` of `GraphFiniteness`
  (`exists_equivIso_of_jac`).
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Stacks.Frobenius
open scoped CategoryTheory.MonObj

universe u

noncomputable section

namespace RamanujanWeil.Arith.Deuring.Geom.G7.CJac

/-! ## Common sites -/

/-- A ℕ-indexed family of schemes and one more scheme lie in a common big fppf site. -/
theorem exists_site_containing_family (Y : ℕ → Scheme.{u}) (Z : Scheme.{u}) :
    ∃ B : BigFppfSite.{u}, (∀ n, B.Contains (Y n)) ∧ B.Contains Z := by
  let S₀ : Set Scheme.{u} := Set.range Y ∪ {Z}
  have : Small.{u} S₀ := by dsimp [S₀]; infer_instance
  obtain ⟨B, hB⟩ := BigFppfSite.exists_containing S₀
  exact ⟨B, fun n => hB _ (Or.inl ⟨n, rfl⟩), hB _ (Or.inr rfl)⟩

/-! ## Base change of an isomorphism of curves over `k` -/

section BaseChange

variable {k : Type u} [Field k] (K : Type u) [Field K] [Algebra k K]
  {X Y Z : Over (Spec (.of k))}

/-- **The base change** `φ_K = φ × 𝟙 : X_K ⟶ Y_K` of a morphism over `k`. -/
def fieldBaseChangeMap (φ : X ⟶ Y) : fieldBaseChange X K ⟶ fieldBaseChange Y K :=
  pullback.map X.hom (specAlgebraMap k K) Y.hom (specAlgebraMap k K) φ.left (𝟙 _) (𝟙 _)
    (by rw [Category.comp_id, Over.w]) (by rw [Category.comp_id, Category.id_comp])

@[reassoc (attr := simp)]
theorem fieldBaseChangeMap_fst (φ : X ⟶ Y) :
    fieldBaseChangeMap K φ ≫ pullback.fst Y.hom (specAlgebraMap k K) =
      pullback.fst X.hom (specAlgebraMap k K) ≫ φ.left :=
  pullback.lift_fst _ _ _

/-- `φ_K` is a morphism over `K`. -/
@[reassoc (attr := simp)]
theorem fieldBaseChangeMap_snd (φ : X ⟶ Y) :
    fieldBaseChangeMap K φ ≫ pullback.snd Y.hom (specAlgebraMap k K) =
      pullback.snd X.hom (specAlgebraMap k K) := by
  simp [fieldBaseChangeMap]

theorem fieldBaseChangeMap_comp (φ : X ⟶ Y) (ψ : Y ⟶ Z) :
    fieldBaseChangeMap K (φ ≫ ψ) = fieldBaseChangeMap K φ ≫ fieldBaseChangeMap K ψ := by
  apply pullback.hom_ext
  · simp only [fieldBaseChangeMap_fst, Over.comp_left, Category.assoc,
      fieldBaseChangeMap_fst_assoc]
  · simp only [fieldBaseChangeMap_snd, Category.assoc]

theorem fieldBaseChangeMap_id : fieldBaseChangeMap K (𝟙 X) = 𝟙 _ := by
  apply pullback.hom_ext
  · simp only [fieldBaseChangeMap_fst, Over.id_left, Category.comp_id, Category.id_comp]
  · simp only [fieldBaseChangeMap_snd, Category.id_comp]

/-- **`φ_K` commutes with every Galois twist** `id × Spec(τ)`. -/
theorem fieldBaseChangeMap_comp_galoisBaseChange (φ : X ⟶ Y) (τ : K ≃ₐ[k] K) :
    fieldBaseChangeMap K φ ≫ galoisBaseChange Y K τ =
      galoisBaseChange X K τ ≫ fieldBaseChangeMap K φ := by
  apply pullback.hom_ext
  · simp only [Category.assoc, galoisBaseChange_comp_fst, fieldBaseChangeMap_fst,
      galoisBaseChange_comp_fst_assoc]
  · simp only [Category.assoc, galoisBaseChange_comp_snd, fieldBaseChangeMap_snd_assoc,
      fieldBaseChangeMap_snd, galoisBaseChange_comp_snd_assoc]

/-- **The base change of an isomorphism over `k`**, `X_K ≅ Y_K`. -/
def fieldBaseChangeIso (e : X ≅ Y) : fieldBaseChange X K ≅ fieldBaseChange Y K where
  hom := fieldBaseChangeMap K e.hom
  inv := fieldBaseChangeMap K e.inv
  hom_inv_id := by rw [← fieldBaseChangeMap_comp, e.hom_inv_id, fieldBaseChangeMap_id]
  inv_hom_id := by rw [← fieldBaseChangeMap_comp, e.inv_hom_id, fieldBaseChangeMap_id]

theorem fieldBaseChangeIso_hom_snd (e : X ≅ Y) :
    (fieldBaseChangeIso K e).hom ≫ pullback.snd Y.hom (specAlgebraMap k K) =
      pullback.snd X.hom (specAlgebraMap k K) :=
  fieldBaseChangeMap_snd K e.hom

theorem fieldBaseChangeIso_hom_comp_galoisBaseChange (e : X ≅ Y) (τ : K ≃ₐ[k] K) :
    (fieldBaseChangeIso K e).hom ≫ galoisBaseChange Y K τ =
      galoisBaseChange X K τ ≫ (fieldBaseChangeIso K e).hom :=
  fieldBaseChangeMap_comp_galoisBaseChange K e.hom τ

/-- **Step C's output, base changed.** An isomorphism `φ : Y ≅ Y'` of schemes with
`φ.hom ≫ s' = s` over `k` gives an isomorphism of the base changes to `K`, over `K` and
commuting with every Galois twist: exactly the `α`, `hα`, `hαΨ` hypotheses of
`exists_equivariant_jacobianIso` for `Ψ = id × Spec(τ)`. -/
theorem exists_baseChange_iso {Y₀ Y₀' : Scheme.{u}} (s : Y₀ ⟶ Spec (.of k))
    (s' : Y₀' ⟶ Spec (.of k)) (φ : Y₀ ≅ Y₀') (hφ : φ.hom ≫ s' = s) :
    ∃ α : fieldBaseChange (Over.mk s) K ≅ fieldBaseChange (Over.mk s') K,
      α.hom ≫ pullback.snd s' (specAlgebraMap k K) = pullback.snd s (specAlgebraMap k K) ∧
      ∀ τ : K ≃ₐ[k] K, α.hom ≫ galoisBaseChange (Over.mk s') K τ =
        galoisBaseChange (Over.mk s) K τ ≫ α.hom :=
  ⟨fieldBaseChangeIso K (Over.isoMk φ hφ), fieldBaseChangeIso_hom_snd K _,
    fieldBaseChangeIso_hom_comp_galoisBaseChange K _⟩

end BaseChange

/-! ## Equivariant isomorphisms compose -/

section Compose

variable {C : Type*} [Category C] [CartesianMonoidalCategory C]

/-- `e : A ≅ A'` is a homomorphism of group objects intertwining `π` and `π'`. -/
def IsEquivJacIso {A A' : C} [MonObj A] [MonObj A'] (π : A ⟶ A) (π' : A' ⟶ A') (e : A ≅ A') :
    Prop :=
  IsMonHom e.hom ∧ e.hom ≫ π' = π ≫ e.hom

theorem IsEquivJacIso.symm {A A' : C} [MonObj A] [MonObj A'] {π : A ⟶ A} {π' : A' ⟶ A'}
    {e : A ≅ A'} (h : IsEquivJacIso π π' e) : IsEquivJacIso π' π e.symm := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨?_, ?_⟩
  · exact inferInstanceAs (IsMonHom e.inv)
  · change e.inv ≫ π = π' ≫ e.inv
    rw [Iso.inv_comp_eq, ← Category.assoc, h2, Category.assoc, Iso.hom_inv_id,
      Category.comp_id]

theorem IsEquivJacIso.trans {A A' A'' : C} [MonObj A] [MonObj A'] [MonObj A'']
    {π : A ⟶ A} {π' : A' ⟶ A'} {π'' : A'' ⟶ A''} {e : A ≅ A'} {e' : A' ≅ A''}
    (h : IsEquivJacIso π π' e) (h' : IsEquivJacIso π' π'' e') :
    IsEquivJacIso π π'' (e ≪≫ e') := by
  obtain ⟨h1, h2⟩ := h
  obtain ⟨h1', h2'⟩ := h'
  refine ⟨?_, ?_⟩
  · exact inferInstanceAs (IsMonHom (e.hom ≫ e'.hom))
  · change (e.hom ≫ e'.hom) ≫ π'' = π ≫ e.hom ≫ e'.hom
    rw [Category.assoc, h2', ← Category.assoc, h2, Category.assoc]

/-- **Assembly of J and C-Jac.** If `Jac_n ≅ B_n` and `Jac_m ≅ B_m` equivariantly (step J) and
`Jac_n ≅ Jac_m` equivariantly (C-Jac applied to step C's curve isomorphism), then
`B_n ≅ B_m` equivariantly: the conclusion shape of `GraphFiniteness`. -/
theorem exists_equivIso_of_jac {J J' Bn Bm : C} [MonObj J] [MonObj J'] [MonObj Bn] [MonObj Bm]
    {πJ : J ⟶ J} {πJ' : J' ⟶ J'} {πn : Bn ⟶ Bn} {πm : Bm ⟶ Bm}
    (hn : ∃ e : J ≅ Bn, IsMonHom e.hom ∧ e.hom ≫ πn = πJ ≫ e.hom)
    (hm : ∃ e : J' ≅ Bm, IsMonHom e.hom ∧ e.hom ≫ πm = πJ' ≫ e.hom)
    (hJ : ∃ e : J ≅ J', IsMonHom e.hom ∧ e.hom ≫ πJ' = πJ ≫ e.hom) :
    ∃ e : Bn ≅ Bm, IsMonHom e.hom ∧ e.hom ≫ πm = πn ≫ e.hom := by
  obtain ⟨en, hn⟩ := hn
  obtain ⟨em, hm⟩ := hm
  obtain ⟨eJ, hJ⟩ := hJ
  exact ⟨en.symm ≪≫ eJ ≪≫ em,
    (IsEquivJacIso.symm (π := πJ) (π' := πn) hn).trans
      ((IsEquivJacIso.trans (π := πJ) (π' := πJ') (π'' := πm) hJ hm))⟩

end Compose

end RamanujanWeil.Arith.Deuring.Geom.G7.CJac

end
