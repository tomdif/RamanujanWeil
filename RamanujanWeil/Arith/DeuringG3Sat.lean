import RamanujanWeil.Arith.DeuringG3Div

/-!
# A3-ord, G3 (saturation): `Hom(A, B)` is `ℓ`-saturated in `Hom(T_ℓ A, T_ℓ B)`

For `ℓ` invertible in the algebraically closed field `k` and abelian varieties `A`, `B`:
if `T_ℓ α` is divisible by `ℓ^m` in `Hom_{ℤ_ℓ}(T_ℓ A, T_ℓ B)`, then `α = [ℓ^m] ≫ β` for a
homomorphism `β` (`exists_eq_comp_of_tateModuleMap_dvd`). This is the statement that the cokernel
of `Hom(A,B) → Hom(T_ℓ A, T_ℓ B)` has no `ℓ`-torsion. It is the key input (Mumford §19 Thm 3,
Silverman III.7.4) for injectivity of `Hom(A,B) ⊗ ℤ_ℓ → Hom(T_ℓ A, T_ℓ B)`.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.MonObj

universe u

namespace RamanujanWeil.Arith.Deuring.Geom

open Stacks.Groupoids

variable {k : Type u} [Field k] [IsAlgClosed k]
  {A B : Over (Spec (.of k))} [GrpObj A] [GrpObj B]
  [AlgebraicGeometry.IsAbelianVariety k A] [AlgebraicGeometry.IsAbelianVariety k B]
  (ℓ : ℕ) [Fact ℓ.Prime]

/-- If `T_ℓ α` is divisible by `ℓ^m`, then `α` kills `A(k)[ℓ^m]`. -/
theorem comp_eq_one_of_tateModuleMap_dvd (m : ℕ) (α : A ⟶ B) [IsMonHom α]
    (h : ∀ y : tateModule A ℓ, ∃ z, tateModuleMap ℓ α y = ((ℓ : ℤ_[ℓ]) ^ m) • z)
    (x : 𝟙_ (Over (Spec (.of k))) ⟶ A) (hx : x ^ ((ℓ ^ m : ℕ) : ℤ) = 1) : x ≫ α = 1 := by
  have hmem : Additive.ofMul x ∈
      AddSubgroup.torsionBy (Additive (𝟙_ (Over (Spec (.of k))) ⟶ A)) ((ℓ ^ m : ℕ) : ℤ) := by
    show ((ℓ ^ m : ℕ) : ℤ) • Additive.ofMul x = 0
    rw [← ofMul_zpow, hx]; rfl
  obtain ⟨y, hy⟩ := Stacks.AbelianGroup.tateReduction_surjective (exists_nsmul_eq_point A ℓ) m
    ⟨_, hmem⟩
  obtain ⟨z, hz⟩ := h y
  have h1 := tateReduction_tateModuleMap (ℓ := ℓ) α m y
  have h0 : Stacks.AbelianGroup.tateReduction ℓ m (tateModuleMap ℓ α y) = 0 := by
    rw [hz, ← tateModuleQuotientEquiv_mk B ℓ m, (Submodule.Quotient.mk_eq_zero _).mpr
      (Submodule.smul_mem_pointwise_smul _ _ _ Submodule.mem_top), map_zero]
  rw [h0, hy] at h1
  have h2 := congrArg (fun z : AddSubgroup.torsionBy (Additive (𝟙_ (Over (Spec (.of k))) ⟶ B))
    ((ℓ ^ m : ℕ) : ℤ) => (z : Additive (𝟙_ (Over (Spec (.of k))) ⟶ B)).toMul) h1
  exact h2.symm

/-- **Saturation.** If `T_ℓ α` is divisible by `ℓ^m` in `Hom_{ℤ_ℓ}(T_ℓ A, T_ℓ B)`, then
`α = [ℓ^m] ≫ β` for a homomorphism `β : A ⟶ B`. -/
theorem exists_eq_comp_of_tateModuleMap_dvd (hℓ : IsUnit (ℓ : k)) (m : ℕ) (α : A ⟶ B)
    [IsMonHom α]
    (h : ∀ y : tateModule A ℓ, ∃ z, tateModuleMap ℓ α y = ((ℓ : ℤ_[ℓ]) ^ m) • z) :
    ∃ β : A ⟶ B, IsMonHom β ∧ ((𝟙 A) ^ ((ℓ ^ m : ℕ) : ℤ)) ≫ β = α := by
  apply exists_isMonHom_zpow_comp_eq _ _ α (comp_eq_one_of_tateModuleMap_dvd ℓ m α h)
  rw [Int.cast_natCast, Nat.cast_pow]
  exact hℓ.pow m

end RamanujanWeil.Arith.Deuring.Geom
