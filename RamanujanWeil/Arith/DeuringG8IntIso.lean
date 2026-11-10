import RamanujanWeil.Arith.DeuringG8Int

/-!
# A3-ord, G8(ii): isomorphisms and automorphisms through `L A = Hom_π(A₀, A)`

`docs/ARITH_DEURING_CLASSLATTICE.md` §1. Consequences of the integral surjectivity
`exists_postHom_eq` (`DeuringG8Int`):

* `Link π₀ π`: equivariant `α : A₀ ⟶ A`, `β : A ⟶ A₀` with `α ≫ β = [n]`, `n` invertible in
  `k` (a link of degree prime to the characteristic);
* `postHomSurj_of_link`: with `End_π(A₀) = ℤ[π₀]`, a link makes `postHom` surjective onto the
  `ℤ[π]`-linear maps (`PostHomSurj`);
* **`nonempty_iso_iff`**: `A' ≅ A` equivariantly (as group objects) iff `L A' ≃ L A` as
  `ℤ[π]`-modules;
* **`card_aut_eq`**: `#Aut_π(A) = #Aut_{ℤ[π]}(L A)`.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.MonObj

set_option linter.unusedSectionVars false

universe u

namespace RamanujanWeil.Arith.Deuring.G8Int

open RamanujanWeil.Arith.Deuring.Geom RamanujanWeil.Arith.Deuring.Geom.G7
  RamanujanWeil.Arith.Deuring.Dual2 RamanujanWeil.Arith.Deuring.G8
  RamanujanWeil.Arith.Deuring.G5 Stacks.Groupoids

variable {k : Type u} [Field k] [IsAlgClosed k] {A₀ A A' : Over (Spec (.of k))} [GrpObj A₀]
  [GrpObj A] [GrpObj A'] [AlgebraicGeometry.IsAbelianVariety k A₀]
  [AlgebraicGeometry.IsAbelianVariety k A] [AlgebraicGeometry.IsAbelianVariety k A']

section Defs

variable (π₀ : A₀ ⟶ A₀) (π : A ⟶ A) (π' : A' ⟶ A') [IsMonHom π₀] [IsMonHom π] [IsMonHom π']

/-- **A link of degree prime to the characteristic**: equivariant `α : A₀ ⟶ A`, `β : A ⟶ A₀`
with `α ≫ β = [n]`, `n` invertible in `k`. -/
def Link : Prop :=
  ∃ (α : A₀ ⟶ A) (β : A ⟶ A₀) (n : ℤ), IsUnit (n : k) ∧ IsMonHom α ∧ IsMonHom β ∧
    α ≫ π = π₀ ≫ α ∧ β ≫ π₀ = π ≫ β ∧ α ≫ β = (𝟙 A₀) ^ n

/-- Every `ℤ[π]`-linear map `L A → L A'` is `postHom φ`. -/
def PostHomSurj : Prop :=
  ∀ f : homPi π₀ π →ₗ[ℤ] homPi π₀ π', (∀ x, f (piAct π₀ π x) = piAct π₀ π' (f x)) →
    ∃ φ : homPi π π', postHom φ = f

end Defs

variable {π₀ : A₀ ⟶ A₀} {π : A ⟶ A} {π' : A' ⟶ A'} [IsMonHom π₀] [IsMonHom π] [IsMonHom π']

/-- A link gives a nonzero element of `L A`. -/
theorem exists_ne_one_of_link (hA₀ : abelianVarietyDimension A₀ = 1) (h : Link π₀ π) :
    ∃ x : homPi π₀ π, hm (x : homAV A₀ A) ≠ 1 := by
  obtain ⟨α, β, n, hn, hα, hβ, hαπ, hβπ, hαβ⟩ := h
  have hn0 : n ≠ 0 := by rintro rfl; simp at hn
  refine ⟨homPi.mk α hαπ, fun h1 => zpow_id_ne_one hA₀ n hn0 ?_⟩
  change α = 1 at h1
  rw [← hαβ, h1, MonObj.one_comp]

/-- **G8(ii) surjectivity from a link.** -/
theorem postHomSurj_of_link (hA₀ : abelianVarietyDimension A₀ = 1)
    (hA : abelianVarietyDimension A = 1) (hmin : MinimalOrder π₀)
    (hind : ∀ a b : ℤ, lin π₀ a b = 1 → a = 0 ∧ b = 0) (t q : ℤ)
    (hπ₀ : endPolyEval π₀ (Polynomial.X ^ 2 - Polynomial.C t * Polynomial.X +
      Polynomial.C q) = 1) (hdisc : t ^ 2 < 4 * q) (h : Link π₀ π) :
    PostHomSurj π₀ π π' := by
  intro f hf
  obtain ⟨α, β, n, hn, hα, hβ, hαπ, hβπ, hαβ⟩ := h
  have hn0 : n ≠ 0 := by rintro rfl; simp at hn
  have hα1 : α ≠ 1 := by
    rintro rfl
    exact zpow_id_ne_one hA₀ n hn0 (by rw [← hαβ, MonObj.one_comp])
  exact exists_postHom_eq hA₀ hA hmin hind t q hπ₀ hdisc α hα1 hαπ β n hn hαβ hβπ f hf

/-- An equivariant isomorphism as an element of `Hom_π`. -/
noncomputable def isoHom (e : A' ≅ A) (h : IsMonHom e.hom) (he : e.hom ≫ π = π' ≫ e.hom) :
    homPi π' π :=
  homPi.mk e.hom he

/-- Its inverse. -/
noncomputable def isoInv (e : A' ≅ A) (h : IsMonHom e.hom) (he : e.hom ≫ π = π' ≫ e.hom) :
    homPi π π' :=
  homPi.mk e.inv (by rw [Iso.inv_comp_eq, ← Category.assoc, he, Category.assoc,
    Iso.hom_inv_id, Category.comp_id])

theorem compPi_isoHom_isoInv (e : A' ≅ A) (h : IsMonHom e.hom) (he : e.hom ≫ π = π' ≫ e.hom) :
    compPi (isoHom e h he) (isoInv e h he) = idPi :=
  homPi.ext (by rw [hm_compPi, hm_idPi]; exact e.hom_inv_id)

theorem compPi_isoInv_isoHom (e : A' ≅ A) (h : IsMonHom e.hom) (he : e.hom ≫ π = π' ≫ e.hom) :
    compPi (isoInv e h he) (isoHom e h he) = idPi :=
  homPi.ext (by rw [hm_compPi, hm_idPi]; exact e.inv_hom_id)

/-- An isomorphism from two mutually inverse equivariant homomorphisms. -/
noncomputable def isoOfPi (φ : homPi π' π) (ψ : homPi π π') (h1 : compPi φ ψ = idPi)
    (h2 : compPi ψ φ = idPi) : A' ≅ A where
  hom := hm (φ : homAV A' A)
  inv := hm (ψ : homAV A A')
  hom_inv_id := by
    have := congrArg (fun z : homPi π' π' => hm (z : homAV A' A')) h1
    simpa only [hm_compPi, hm_idPi] using this
  inv_hom_id := by
    have := congrArg (fun z : homPi π π => hm (z : homAV A A)) h2
    simpa only [hm_compPi, hm_idPi] using this

/-- **Isomorphisms ↔ lattice isomorphisms.** -/
theorem nonempty_iso_iff (hA₀ : abelianVarietyDimension A₀ = 1)
    (hA : abelianVarietyDimension A = 1) (hA' : abelianVarietyDimension A' = 1)
    (hs : PostHomSurj π₀ π' π) (hs' : PostHomSurj π₀ π π')
    (x : homPi π₀ π) (hx : hm (x : homAV A₀ A) ≠ 1)
    (x' : homPi π₀ π') (hx' : hm (x' : homAV A₀ A') ≠ 1) :
    Nonempty {e : A' ≅ A // IsMonHom e.hom ∧ e.hom ≫ π = π' ≫ e.hom} ↔
      ∃ f : homPi π₀ π' ≃ₗ[ℤ] homPi π₀ π, ∀ y, f (piAct π₀ π' y) = piAct π₀ π (f y) := by
  constructor
  · rintro ⟨e, he1, he⟩
    let φ := isoHom e he1 he
    let ψ := isoInv e he1 he
    refine ⟨LinearEquiv.ofLinear (postHom φ) (postHom ψ) ?_ ?_, fun y => postHom_piAct φ y⟩
    · rw [← postHom_compPi, compPi_isoInv_isoHom, postHom_idPi]
    · rw [← postHom_compPi, compPi_isoHom_isoInv, postHom_idPi]
  · rintro ⟨f, hf⟩
    obtain ⟨φ, hφ⟩ := hs f.toLinearMap hf
    have hf' : ∀ y, f.symm (piAct π₀ π y) = piAct π₀ π' (f.symm y) := fun y =>
      f.injective (by rw [hf, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply])
    obtain ⟨ψ, hψ⟩ := hs' f.symm.toLinearMap hf'
    have h1 : compPi φ ψ = idPi := postHom_injective hA₀ hA' x' hx' (by
      rw [postHom_compPi, postHom_idPi, hφ, hψ]
      exact LinearMap.ext fun y => by simp)
    have h2 : compPi ψ φ = idPi := postHom_injective hA₀ hA x hx (by
      rw [postHom_compPi, postHom_idPi, hφ, hψ]
      exact LinearMap.ext fun y => by simp)
    exact ⟨⟨isoOfPi φ ψ h1 h2, inferInstanceAs (IsMonHom (hm (φ : homAV A' A))), φ.2⟩⟩

theorem postHom_isoHom_mul (e : A ≅ A) (h : IsMonHom e.hom) (he : e.hom ≫ π = π ≫ e.hom) :
    (postHom (π₀ := π₀) (isoHom e h he) : Module.End ℤ (homPi π₀ π)) *
      postHom (isoInv e h he) = 1 := by
  rw [Module.End.mul_eq_comp, ← postHom_compPi, compPi_isoInv_isoHom, postHom_idPi]
  rfl

theorem postHom_isoInv_mul (e : A ≅ A) (h : IsMonHom e.hom) (he : e.hom ≫ π = π ≫ e.hom) :
    (postHom (π₀ := π₀) (isoInv e h he) : Module.End ℤ (homPi π₀ π)) *
      postHom (isoHom e h he) = 1 := by
  rw [Module.End.mul_eq_comp, ← postHom_compPi, compPi_isoHom_isoInv, postHom_idPi]
  rfl

theorem postHom_mul_piAct (φ : homPi π π) :
    (postHom (π₀ := π₀) φ : Module.End ℤ (homPi π₀ π)) * piAct π₀ π =
      piAct π₀ π * postHom φ :=
  LinearMap.ext fun y => postHom_piAct φ y

/-- The `ℤ[π]`-linear automorphism of `L A` induced by an equivariant automorphism. -/
noncomputable def autToUnit (e : {e : A ≅ A // IsMonHom e.hom ∧ e.hom ≫ π = π ≫ e.hom}) :
    {u : (Module.End ℤ (homPi π₀ π))ˣ //
      (u : Module.End ℤ (homPi π₀ π)) * piAct π₀ π = piAct π₀ π * u} :=
  ⟨⟨postHom (isoHom e.1 e.2.1 e.2.2), postHom (isoInv e.1 e.2.1 e.2.2),
    postHom_isoHom_mul e.1 e.2.1 e.2.2, postHom_isoInv_mul e.1 e.2.1 e.2.2⟩,
    postHom_mul_piAct (isoHom e.1 e.2.1 e.2.2)⟩

/-- **`#Aut_π(A) = #Aut_{ℤ[π]}(L A)`.** -/
theorem card_aut_eq (hA₀ : abelianVarietyDimension A₀ = 1)
    (hA : abelianVarietyDimension A = 1) (hs : PostHomSurj π₀ π π)
    (x : homPi π₀ π) (hx : hm (x : homAV A₀ A) ≠ 1) :
    Nat.card {e : A ≅ A // IsMonHom e.hom ∧ e.hom ≫ π = π ≫ e.hom} =
      Nat.card {u : (Module.End ℤ (homPi π₀ π))ˣ //
        (u : Module.End ℤ (homPi π₀ π)) * piAct π₀ π = piAct π₀ π * u} := by
  refine Nat.card_congr (Equiv.ofBijective (autToUnit (π₀ := π₀)) ⟨?_, ?_⟩)
  · rintro ⟨e₁, h₁, he₁⟩ ⟨e₂, h₂, he₂⟩ h
    have h' := congrArg (fun u : {u : (Module.End ℤ (homPi π₀ π))ˣ //
      (u : Module.End ℤ (homPi π₀ π)) * piAct π₀ π = piAct π₀ π * u} =>
        ((u.1 : Module.End ℤ (homPi π₀ π)) : homPi π₀ π →ₗ[ℤ] homPi π₀ π)) h
    have h3 : isoHom e₁ h₁ he₁ = isoHom e₂ h₂ he₂ := postHom_injective hA₀ hA x hx h'
    have h4 := congrArg (fun z : homPi π π => hm (z : homAV A A)) h3
    exact Subtype.ext (Iso.ext h4)
  · rintro ⟨u, hu⟩
    obtain ⟨φ, hφ⟩ := hs (u : Module.End ℤ (homPi π₀ π)) (fun y => LinearMap.congr_fun hu y)
    have hu' : ((u⁻¹ : (Module.End ℤ (homPi π₀ π))ˣ) : Module.End ℤ (homPi π₀ π)) *
        piAct π₀ π = piAct π₀ π * ↑u⁻¹ := by
      rw [Units.inv_mul_eq_iff_eq_mul, ← mul_assoc, hu, mul_assoc, Units.mul_inv, mul_one]
    obtain ⟨ψ, hψ⟩ := hs (↑u⁻¹ : Module.End ℤ (homPi π₀ π)) (fun y => LinearMap.congr_fun hu' y)
    have h1 : compPi φ ψ = idPi := postHom_injective hA₀ hA x hx (by
      rw [postHom_compPi, postHom_idPi, hφ, hψ, ← Module.End.mul_eq_comp, Units.inv_mul]; rfl)
    have h2 : compPi ψ φ = idPi := postHom_injective hA₀ hA x hx (by
      rw [postHom_compPi, postHom_idPi, hφ, hψ, ← Module.End.mul_eq_comp, Units.mul_inv]; rfl)
    refine ⟨⟨isoOfPi φ ψ h1 h2, inferInstanceAs (IsMonHom (hm (φ : homAV A A))), φ.2⟩, ?_⟩
    apply Subtype.ext
    apply Units.ext
    change postHom (isoHom (isoOfPi φ ψ h1 h2)
      (inferInstanceAs (IsMonHom (hm (φ : homAV A A)))) φ.2) = (u : Module.End ℤ (homPi π₀ π))
    rw [← hφ]
    rfl

end RamanujanWeil.Arith.Deuring.G8Int
