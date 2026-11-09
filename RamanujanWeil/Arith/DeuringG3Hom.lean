import RamanujanWeil.Arith.DeuringG4
import RamanujanWeil.Arith.DeuringG3Sat
import RamanujanWeil.Arith.DeuringG3Lattice

/-!
# A3-ord, G3 (completion): `Hom(A, B)` is a lattice of rank `≤ 4` and `Hom ⊗ ℤ_ℓ ↪ Hom(T_ℓ)`

Let `k` be algebraically closed and `A`, `B` one-dimensional abelian varieties over `k`. Write
`homAV A B` for the group of homomorphisms `A ⟶ B` (additively). This file proves:

* `degPolar`, `degPolar_add_left`, `degPolar_self`: the polar form
  `⟨f, g⟩ = deg(f + g) − deg f − deg g` of the degree on `End(A)` is biadditive (it is the polar
  form of `det` on `2 × 2` matrices, through `T_ℓ`), and `⟨f, f⟩ = 2 deg f`, so it is anisotropic
  (`endDegree_eq_zero_iff`);
* `comp_ne_one`: a composite of nontrivial homomorphisms of one-dimensional abelian varieties is
  nontrivial;
* `homAV_saturated`: `T_ℓ α ∈ ℓ · Hom(T_ℓ A, T_ℓ B)` implies `α ∈ ℓ · Hom(A, B)` (from
  `DeuringG3Sat`);
* **`homAV_finite_free`**: `Hom(A, B)` is a finitely generated free abelian group of rank `≤ 4`;
* **`homAV_tensor_injective`**: `Hom(A, B) ⊗_ℤ ℤ_ℓ → Hom_{ℤ_ℓ}(T_ℓ A, T_ℓ B)` is injective.

The last two are proved under the hypothesis `HomDualHyp A B`: either `Hom(A, B) = 0`, or there
is a nonzero homomorphism `B ⟶ A` (used to transport the degree form of `End(A)` to `Hom(A, B)`
along the injective map `α ↦ α ≫ ψ`). This holds for `A = B` (`homDualHyp_self`, giving the
unconditional statements for `End(A)`), and it holds for all `A`, `B` once the dual isogeny
exists (see `docs/ARITH_DEURING_PROGRESS2.md`, sub-lemma G3-dual).
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory Module
open scoped CategoryTheory.MonObj

universe u

namespace RamanujanWeil.Arith.Deuring.Geom

open Stacks.Groupoids

variable {k : Type u} [Field k]

section Group

variable (A B : Over (Spec (.of k))) [GrpObj A] [GrpObj B] [IsCommMonObj B]

/-- **The group of homomorphisms `A ⟶ B`**, written additively. -/
def homAV : AddSubgroup (Additive (A ⟶ B)) where
  carrier := {α | IsMonHom (Additive.toMul α)}
  add_mem' := fun {a b} ha hb => by
    have : IsMonHom (Additive.toMul a) := ha
    have : IsMonHom (Additive.toMul b) := hb
    show IsMonHom (Additive.toMul a * Additive.toMul b)
    infer_instance
  zero_mem' := by
    show IsMonHom (1 : A ⟶ B)
    infer_instance
  neg_mem' := fun {a} ha => by
    have : IsMonHom (Additive.toMul a) := ha
    show IsMonHom ((Additive.toMul a)⁻¹)
    have := isMonHom_zpow_of_isCommMonObj (Additive.toMul a) (-1)
    rwa [zpow_neg_one] at this

variable {A B}

instance (x : homAV A B) : IsMonHom (Additive.toMul (x : Additive (A ⟶ B))) := x.2

/-- The element of `homAV A B` given by a homomorphism. -/
def homAV.mk (α : A ⟶ B) [h : IsMonHom α] : homAV A B := ⟨Additive.ofMul α, h⟩

@[simp] theorem homAV.toMul_mk (α : A ⟶ B) [IsMonHom α] :
    Additive.toMul ((homAV.mk α : homAV A B) : Additive (A ⟶ B)) = α := rfl

theorem homAV.toMul_add (x y : homAV A B) :
    Additive.toMul ((x + y : homAV A B) : Additive (A ⟶ B)) =
      Additive.toMul (x : Additive (A ⟶ B)) * Additive.toMul (y : Additive (A ⟶ B)) := rfl

theorem homAV.toMul_zsmul (n : ℤ) (x : homAV A B) :
    Additive.toMul ((n • x : homAV A B) : Additive (A ⟶ B)) =
      Additive.toMul (x : Additive (A ⟶ B)) ^ n := rfl

theorem homAV.ext_toMul {x y : homAV A B}
    (h : Additive.toMul (x : Additive (A ⟶ B)) = Additive.toMul (y : Additive (A ⟶ B))) :
    x = y := Subtype.ext h

end Group

section Tate

variable [IsAlgClosed k] {A B : Over (Spec (.of k))} [GrpObj A] [GrpObj B]
  [AlgebraicGeometry.IsAbelianVariety k A] [AlgebraicGeometry.IsAbelianVariety k B]
  (ℓ : ℕ) [Fact ℓ.Prime]

/-- **The Tate-module map** `Hom(A, B) → Hom_{ℤ_ℓ}(T_ℓ A, T_ℓ B)`, as an additive map. -/
noncomputable def tateHom : homAV A B →+ (tateModule A ℓ →ₗ[ℤ_[ℓ]] tateModule B ℓ) where
  toFun x := tateModuleMap ℓ (Additive.toMul (x : Additive (A ⟶ B)))
  map_zero' := tateModuleMap_one
  map_add' _ _ := tateModuleMap_mul _ _

@[simp] theorem tateHom_apply (x : homAV A B) :
    tateHom ℓ x = tateModuleMap ℓ (Additive.toMul (x : Additive (A ⟶ B))) := rfl

/-- **Saturation**: if `T_ℓ α ∈ ℓ · Hom(T_ℓ A, T_ℓ B)` then `α ∈ ℓ · Hom(A, B)`. -/
theorem homAV_saturated (hℓ : IsUnit (ℓ : k)) (x : homAV A B)
    (z : tateModule A ℓ →ₗ[ℤ_[ℓ]] tateModule B ℓ) (hz : tateHom ℓ x = (ℓ : ℤ_[ℓ]) • z) :
    ∃ y : homAV A B, x = (ℓ : ℤ) • y := by
  obtain ⟨β, hβ, hfac⟩ := exists_eq_comp_of_tateModuleMap_dvd ℓ hℓ 1
    (Additive.toMul (x : Additive (A ⟶ B))) (fun y => ⟨z y, by
      rw [← tateHom_apply, hz, pow_one, LinearMap.smul_apply]⟩)
  refine ⟨homAV.mk β, homAV.ext_toMul ?_⟩
  rw [homAV.toMul_zsmul, homAV.toMul_mk, ← hfac, GrpObj.zpow_comp, Category.id_comp, pow_one]

end Tate

section Degree

variable [IsAlgClosed k] {A : Over (Spec (.of k))} [GrpObj A] [AlgebraicGeometry.IsAbelianVariety k A]

variable (A) in
/-- **The polar form of the degree** on `End(A)`: `⟨f, g⟩ = deg(f + g) − deg f − deg g`
(`f + g` is `f * g` in the multiplicative notation of `A ⟶ A`). -/
noncomputable def degPolar (f g : A ⟶ A) : ℤ :=
  (endDegree A (f * g) : ℤ) - endDegree A f - endDegree A g

/-- The polar form of `det` on `2 × 2` matrices. -/
def detPolar {R : Type*} [CommRing R] (X Y : Matrix (Fin 2) (Fin 2) R) : R :=
  (X + Y).det - X.det - Y.det

theorem detPolar_add_left {R : Type*} [CommRing R] (X X' Y : Matrix (Fin 2) (Fin 2) R) :
    detPolar (X + X') Y = detPolar X Y + detPolar X' Y := by
  simp only [detPolar, Matrix.det_fin_two, Matrix.add_apply]
  ring

theorem detPolar_comm {R : Type*} [CommRing R] (X Y : Matrix (Fin 2) (Fin 2) R) :
    detPolar X Y = detPolar Y X := by
  simp only [detPolar, Matrix.det_fin_two, Matrix.add_apply]
  ring

/-- Through `T_ℓ`, the polar form of the degree is the polar form of `det`. -/
theorem degPolar_cast (ℓ : ℕ) [Fact ℓ.Prime]
    (hℓ : IsUnit (ℓ : k)) (b : Basis (Fin 2) ℤ_[ℓ] (tateModule A ℓ)) (f g : A ⟶ A)
    [IsMonHom f] [IsMonHom g] :
    ((degPolar A f g : ℤ) : ℤ_[ℓ]) =
      detPolar (LinearMap.toMatrix b b (tateModuleMap ℓ f))
        (LinearMap.toMatrix b b (tateModuleMap ℓ g)) := by
  have h1 := endDegree_eq_det_tateModuleMap A ℓ (f * g) hℓ
  have h2 := endDegree_eq_det_tateModuleMap A ℓ f hℓ
  have h3 := endDegree_eq_det_tateModuleMap A ℓ g hℓ
  rw [← LinearMap.det_toMatrix b] at h1 h2 h3
  rw [tateModuleMap_mul, map_add] at h1
  simp only [degPolar, detPolar, Int.cast_sub, Int.cast_natCast]
  rw [h1, h2, h3]

theorem exists_basis_fin_two (hA : abelianVarietyDimension A = 1) (ℓ : ℕ) [Fact ℓ.Prime]
    (hℓ : IsUnit (ℓ : k)) : Nonempty (Basis (Fin 2) ℤ_[ℓ] (tateModule A ℓ)) := by
  have := module_free_tateModule A ℓ hℓ
  have := module_finite_tateModule A ℓ hℓ
  have hrank : Module.finrank ℤ_[ℓ] (tateModule A ℓ) = 2 := by
    rw [finrank_tateModule A ℓ hℓ, hA]
  exact ⟨Module.finBasisOfFinrankEq _ _ hrank⟩

/-- **The polar form is additive in the first variable.** -/
theorem degPolar_mul_left (hA : abelianVarietyDimension A = 1) (f f' g : A ⟶ A)
    [IsMonHom f] [IsMonHom f'] [IsMonHom g] :
    degPolar A (f * f') g = degPolar A f g + degPolar A f' g := by
  obtain ⟨ℓ, hℓp, hℓ⟩ := exists_prime_isUnit k
  have := Fact.mk hℓp
  obtain ⟨b⟩ := exists_basis_fin_two hA ℓ hℓ
  apply (Int.cast_injective (α := ℤ_[ℓ]))
  rw [Int.cast_add, degPolar_cast ℓ hℓ b, degPolar_cast ℓ hℓ b, degPolar_cast ℓ hℓ b,
    tateModuleMap_mul, map_add, detPolar_add_left]

theorem degPolar_comm (f g : A ⟶ A) : degPolar A f g = degPolar A g f := by
  simp only [degPolar, mul_comm f g]
  ring

/-- `⟨f, f⟩ = 2 deg f`. -/
theorem degPolar_self (hA : abelianVarietyDimension A = 1) (f : A ⟶ A) [IsMonHom f] :
    degPolar A f f = 2 * endDegree A f := by
  obtain ⟨ℓ, hℓp, hℓ⟩ := exists_prime_isUnit k
  have := Fact.mk hℓp
  obtain ⟨b⟩ := exists_basis_fin_two hA ℓ hℓ
  apply (Int.cast_injective (α := ℤ_[ℓ]))
  rw [degPolar_cast ℓ hℓ b, Int.cast_mul, Int.cast_natCast,
    endDegree_eq_det_tateModuleMap A ℓ f hℓ, ← LinearMap.det_toMatrix b]
  simp only [detPolar, Matrix.det_fin_two, Matrix.add_apply]
  push_cast
  ring

/-- **The degree form on `End(A)`**, as a biadditive map on `homAV A A`. -/
noncomputable def endForm (hA : abelianVarietyDimension A = 1) :
    homAV A A →+ homAV A A →+ ℤ :=
  AddMonoidHom.mk' (fun x => AddMonoidHom.mk'
      (fun y => degPolar A (Additive.toMul (x : Additive (A ⟶ A)))
        (Additive.toMul (y : Additive (A ⟶ A))))
      (fun y y' => by
        rw [homAV.toMul_add, degPolar_comm, degPolar_mul_left hA, degPolar_comm,
          degPolar_comm (Additive.toMul (y' : Additive (A ⟶ A)))]))
    (fun x x' => by
      ext y
      simp only [AddMonoidHom.mk'_apply, AddMonoidHom.add_apply]
      rw [homAV.toMul_add, degPolar_mul_left hA])

/-- **The degree form is anisotropic**: `⟨f, f⟩ = 0 → f = 0`. -/
theorem endForm_anisotropic (hA : abelianVarietyDimension A = 1) (x : homAV A A)
    (h : endForm hA x x = 0) : x = 0 := by
  have h' : degPolar A (Additive.toMul (x : Additive (A ⟶ A)))
      (Additive.toMul (x : Additive (A ⟶ A))) = 0 := h
  rw [degPolar_self hA] at h'
  have h0 : endDegree A (Additive.toMul (x : Additive (A ⟶ A))) = 0 := by omega
  exact homAV.ext_toMul ((endDegree_eq_zero_iff hA _).mp h0)

end Degree

section Comp

variable [IsAlgClosed k] {A B C : Over (Spec (.of k))} [GrpObj A] [GrpObj B] [GrpObj C]
  [AlgebraicGeometry.IsAbelianVariety k A] [AlgebraicGeometry.IsAbelianVariety k B]
  [AlgebraicGeometry.IsAbelianVariety k C]

/-- **A composite of nontrivial homomorphisms of one-dimensional abelian varieties is
nontrivial.** -/
theorem comp_ne_one (hA : abelianVarietyDimension A = 1) (hB : abelianVarietyDimension B = 1)
    (α : A ⟶ B) (ψ : B ⟶ C) [IsMonHom α] [IsMonHom ψ] (hα : α ≠ 1) (hψ : ψ ≠ 1) :
    α ≫ ψ ≠ 1 := by
  intro h
  have hfα : (pointKer α).Finite := by
    by_contra hinf; exact hα (eq_one_of_infinite_pointKer hA α hinf)
  have hfψ : (pointKer ψ).Finite := by
    by_contra hinf; exact hψ (eq_one_of_infinite_pointKer hB ψ hinf)
  let φ := IsMonHom.monoidHom α (𝟙_ (Over (Spec (.of k))))
  have : Finite φ.ker := by
    show Finite (φ.ker : Set (𝟙_ (Over (Spec (.of k))) ⟶ A))
    exact hfα.to_subtype
  have hrange : (φ.range : Set (𝟙_ (Over (Spec (.of k))) ⟶ B)) ⊆ pointKer ψ := by
    rintro _ ⟨x, rfl⟩
    show (x ≫ α) ≫ ψ = 1
    rw [Category.assoc, h, MonObj.comp_one]
  have : Finite φ.range := (hfψ.subset hrange).to_subtype
  have := finite_of_finite_ker_of_finite_range φ
  exact (infinite_points hA).not_finite this

/-- Post-composition with a homomorphism, as an additive map `Hom(A, B) → Hom(A, C)`. -/
noncomputable def postcomp (ψ : B ⟶ C) [IsMonHom ψ] : homAV A B →+ homAV A C where
  toFun x := homAV.mk (Additive.toMul (x : Additive (A ⟶ B)) ≫ ψ)
  map_zero' := homAV.ext_toMul (by
    show (1 : A ⟶ B) ≫ ψ = 1
    exact MonObj.one_comp ψ)
  map_add' x y := homAV.ext_toMul (by
    show (Additive.toMul (x : Additive (A ⟶ B)) * Additive.toMul (y : Additive (A ⟶ B))) ≫ ψ = _
    rw [MonObj.mul_comp]
    rfl)

theorem postcomp_injective (hA : abelianVarietyDimension A = 1)
    (hB : abelianVarietyDimension B = 1) (ψ : B ⟶ C) [IsMonHom ψ] (hψ : ψ ≠ 1) :
    Function.Injective (postcomp (A := A) ψ) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  by_contra hne
  apply comp_ne_one hA hB (Additive.toMul (x : Additive (A ⟶ B))) ψ (fun h => hne
    (homAV.ext_toMul h)) hψ
  exact congrArg (fun z : homAV A C => Additive.toMul (z : Additive (A ⟶ C))) hx

end Comp

section Main

variable [IsAlgClosed k] {A B : Over (Spec (.of k))} [GrpObj A] [GrpObj B]
  [AlgebraicGeometry.IsAbelianVariety k A] [AlgebraicGeometry.IsAbelianVariety k B]

variable (A B) in
/-- The hypothesis under which `Hom(A, B)` gets a definite form: `Hom(A, B) = 0`, or there is a
nonzero homomorphism `B ⟶ A`. It holds for `A = B`; for all `A, B` it is the existence of dual
isogenies (sub-lemma G3-dual). -/
def HomDualHyp : Prop :=
  (∀ α : A ⟶ B, IsMonHom α → α = 1) ∨ ∃ ψ : B ⟶ A, IsMonHom ψ ∧ ψ ≠ 1

/-- `𝟙 A ≠ 1` for a one-dimensional abelian variety. -/
theorem id_ne_one (hA : abelianVarietyDimension A = 1) : (𝟙 A : A ⟶ A) ≠ 1 := by
  intro h
  have h1 : endDegree A (𝟙 A) = 1 := by
    have := endDegree_zpow_id A 1 one_ne_zero
    simpa using this
  rw [h, endDegree_one hA] at h1
  exact zero_ne_one h1

theorem homDualHyp_self (hA : abelianVarietyDimension A = 1) : HomDualHyp A A :=
  Or.inr ⟨𝟙 A, inferInstance, id_ne_one hA⟩

/-- **An anisotropic biadditive form on `Hom(A, B)`** under `HomDualHyp`. -/
theorem exists_anisotropic_form (hA : abelianVarietyDimension A = 1)
    (hB : abelianVarietyDimension B = 1) (hd : HomDualHyp A B) :
    ∃ F : homAV A B →+ homAV A B →+ ℤ, ∀ x, F x x = 0 → x = 0 := by
  rcases hd with h0 | ⟨ψ, hψ, hne⟩
  · refine ⟨0, fun x _ => homAV.ext_toMul (h0 _ inferInstance)⟩
  · refine ⟨((endForm hA).comp (postcomp ψ)).compl₂ (postcomp ψ), fun x hx => ?_⟩
    exact postcomp_injective hA hB ψ hne (by
      rw [map_zero]
      exact endForm_anisotropic hA _ hx)

/-- `Hom_{ℤ_ℓ}(T_ℓ A, T_ℓ B)` is free of rank `4`. -/
theorem finrank_tateHom_target (hA : abelianVarietyDimension A = 1)
    (hB : abelianVarietyDimension B = 1) (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : IsUnit (ℓ : k)) :
    haveI := module_free_tateModule A ℓ hℓ
    haveI := module_finite_tateModule A ℓ hℓ
    haveI := module_free_tateModule B ℓ hℓ
    haveI := module_finite_tateModule B ℓ hℓ
    finrank ℤ_[ℓ] (tateModule A ℓ →ₗ[ℤ_[ℓ]] tateModule B ℓ) = 4 := by
  have := module_free_tateModule A ℓ hℓ
  have := module_finite_tateModule A ℓ hℓ
  have := module_free_tateModule B ℓ hℓ
  have := module_finite_tateModule B ℓ hℓ
  rw [Module.finrank_linearMap, finrank_tateModule A ℓ hℓ, finrank_tateModule B ℓ hℓ, hA, hB]

/-- **G3: `Hom(A, B)` is a finitely generated free abelian group of rank `≤ 4`.** -/
theorem homAV_finite_free (hA : abelianVarietyDimension A = 1)
    (hB : abelianVarietyDimension B = 1) (hd : HomDualHyp A B) :
    Module.Finite ℤ (homAV A B) ∧ Module.Free ℤ (homAV A B) ∧
      finrank ℤ (homAV A B) ≤ 4 := by
  obtain ⟨F, hF⟩ := exists_anisotropic_form hA hB hd
  obtain ⟨ℓ, hℓp, hℓ⟩ := exists_prime_isUnit k
  have := Fact.mk hℓp
  have := module_free_tateModule A ℓ hℓ
  have := module_finite_tateModule A ℓ hℓ
  have := module_free_tateModule B ℓ hℓ
  have := module_finite_tateModule B ℓ hℓ
  have hsat := homAV_saturated (A := A) (B := B) ℓ hℓ
  obtain ⟨h1, h2⟩ := Lattice.finite_free_of_anisotropic_of_saturated F hF (tateHom ℓ) hsat
  refine ⟨h1, h2, ?_⟩
  have := Lattice.finrank_le_of_anisotropic_of_saturated F hF (tateHom ℓ) hsat
  rwa [finrank_tateHom_target hA hB ℓ hℓ] at this

/-- **G3: `Hom(A, B) ⊗_ℤ ℤ_ℓ → Hom_{ℤ_ℓ}(T_ℓ A, T_ℓ B)` is injective.** -/
theorem homAV_tensor_injective (hA : abelianVarietyDimension A = 1)
    (hB : abelianVarietyDimension B = 1) (hd : HomDualHyp A B) (ℓ : ℕ) [Fact ℓ.Prime]
    (hℓ : IsUnit (ℓ : k)) :
    Function.Injective (((tateHom (A := A) (B := B) ℓ).toIntLinearMap).liftBaseChange ℤ_[ℓ]) := by
  obtain ⟨F, hF⟩ := exists_anisotropic_form hA hB hd
  have := module_free_tateModule A ℓ hℓ
  have := module_finite_tateModule A ℓ hℓ
  have := module_free_tateModule B ℓ hℓ
  have := module_finite_tateModule B ℓ hℓ
  exact Lattice.liftBaseChange_injective_of_anisotropic_of_saturated F hF (tateHom ℓ)
    (homAV_saturated ℓ hℓ)

/-- **G3 for `End(A)`** (unconditional): finitely generated free of rank `≤ 4`, and
`End(A) ⊗ ℤ_ℓ ↪ End(T_ℓ A)`. -/
theorem endAV_finite_free (hA : abelianVarietyDimension A = 1) :
    Module.Finite ℤ (homAV A A) ∧ Module.Free ℤ (homAV A A) ∧ finrank ℤ (homAV A A) ≤ 4 :=
  homAV_finite_free hA hA (homDualHyp_self hA)

theorem endAV_tensor_injective (hA : abelianVarietyDimension A = 1) (ℓ : ℕ) [Fact ℓ.Prime]
    (hℓ : IsUnit (ℓ : k)) :
    Function.Injective (((tateHom (A := A) (B := A) ℓ).toIntLinearMap).liftBaseChange ℤ_[ℓ]) :=
  homAV_tensor_injective hA hA (homDualHyp_self hA) ℓ hℓ

end Main

end RamanujanWeil.Arith.Deuring.Geom
