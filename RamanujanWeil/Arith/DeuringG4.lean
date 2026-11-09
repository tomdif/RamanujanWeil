import RamanujanWeil.Arith.DeuringG3

/-!
# A3-ord, G4 (endomorphisms, dimension one): the degree is a positive definite quadratic form

Let `A` be an abelian variety of dimension one over an algebraically closed field `k` (an
elliptic curve as a Stacks group object). For an endomorphism `α` write `deg α = endDegree A α`
(degree of the function-field extension, `0` if `α` is not dominant) and
`Tr α = abelianVarietyTrace A α`. This file proves:

* `endCharPoly_eq_of_dim_one`: `χ_α = X² − (Tr α) X + deg α`;
* **`endDegree_zpow_mul_zpow`**: `deg(mα + n) = m² deg α + mn Tr α + n²` for all `m, n ∈ ℤ`
  (computed as `det(m T_ℓα + n)` on the rank-two Tate module);
* **`trace_sq_le_four_mul_endDegree`** (Hasse for every endomorphism): `(Tr α)² ≤ 4 deg α`;
* **`endDegree_eq_zero_iff`**: `deg α = 0 ↔ α = 0`, so `deg` is positive definite on `End(A)`.

`deg (α ≫ β) = deg α · deg β` and `deg (nα) = n² deg α` are Stacks'
`Stacks.Groupoids.endDegree_comp` and `Stacks.Groupoids.endDegree_zpow`.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory Polynomial
open scoped CategoryTheory.MonObj

universe u

namespace RamanujanWeil.Arith.Deuring.Geom

open Stacks.Groupoids

variable {k : Type u} [Field k] [IsAlgClosed k]
  {A : Over (Spec (.of k))} [GrpObj A] [AlgebraicGeometry.IsAbelianVariety k A]

/-- A degree-two polynomial with leading coefficient `1` is `X² − aX + b`. -/
theorem quadratic_ext (χ : ℚ[X]) (a b : ℚ) (hdeg : χ.natDegree = 2) (h2 : χ.coeff 2 = 1)
    (h1 : χ.coeff 1 = -a) (h0 : χ.coeff 0 = b) :
    χ = Polynomial.X ^ 2 - C a * Polynomial.X + C b := by
  ext n
  rcases n with _ | _ | _ | n
  · simp only [coeff_add, coeff_sub, coeff_C_mul, coeff_X_pow, coeff_X_zero, coeff_C_zero, h0]
    norm_num
  · simp only [coeff_add, coeff_sub, coeff_C_mul, coeff_X_pow, coeff_C, h1]
    norm_num
  · simp only [coeff_add, coeff_sub, coeff_C_mul, coeff_X_pow, coeff_X, coeff_C, h2]
    norm_num
  · rw [coeff_eq_zero_of_natDegree_lt (by omega)]
    simp only [coeff_add, coeff_sub, coeff_C_mul, coeff_X_pow, coeff_X, coeff_C]
    have h3 : n + 1 + 1 + 1 ≠ 2 := by omega
    have h4 : 1 ≠ n + 1 + 1 + 1 := by omega
    have h5 : n + 1 + 1 + 1 ≠ 0 := by omega
    simp only [h3, h4, h5, ite_false]
    ring

omit [IsAlgClosed k] in
/-- **`χ_α = X² − (Tr α) X + deg α`** in dimension one. -/
theorem endCharPoly_eq_of_dim_one (hA : abelianVarietyDimension A = 1) (α : A ⟶ A)
    [IsMonHom α] :
    endCharPoly A α = Polynomial.X ^ 2 - C (abelianVarietyTrace A α) * Polynomial.X + C (endDegree A α : ℚ) := by
  have hmon := endCharPoly_monic A α
  have hdeg : (endCharPoly A α).natDegree = 2 := by rw [natDegree_endCharPoly, hA]
  have h2 : (endCharPoly A α).coeff 2 = 1 := by
    rw [← hdeg]; exact hmon.coeff_natDegree
  have h1 : (endCharPoly A α).coeff 1 = -abelianVarietyTrace A α := by
    rw [abelianVarietyTrace, neg_neg, nextCoeff, hdeg]; rfl
  exact quadratic_ext _ _ _ hdeg h2 h1 (coeff_zero_endCharPoly A α)

/-- **`deg(mα + n) = m² deg α + mn Tr α + n²`** in dimension one (`mα + n` is
`α ^ m * (𝟙 A) ^ n` in the multiplicative notation of `A ⟶ A`). -/
theorem endDegree_zpow_mul_zpow (hA : abelianVarietyDimension A = 1) (α : A ⟶ A) [IsMonHom α]
    (m n : ℤ) :
    haveI : IsMonHom (α ^ m * (𝟙 A) ^ n) := isMonHom_mul _ _
    (endDegree A (α ^ m * (𝟙 A) ^ n) : ℚ) =
      (m : ℚ) ^ 2 * endDegree A α + m * n * abelianVarietyTrace A α + (n : ℚ) ^ 2 := by
  have : IsMonHom (α ^ m * (𝟙 A) ^ n) := isMonHom_mul _ _
  obtain ⟨ℓ, hℓp, hℓ⟩ := exists_prime_isUnit k
  have := Fact.mk hℓp
  have := module_free_tateModule A ℓ hℓ
  have := module_finite_tateModule A ℓ hℓ
  have hrank : Module.finrank ℤ_[ℓ] (tateModule A ℓ) = 2 := by
    rw [finrank_tateModule A ℓ hℓ, hA]
  let b : Module.Basis (Fin 2) ℤ_[ℓ] (tateModule A ℓ) := Module.finBasisOfFinrankEq _ _ hrank
  set M := LinearMap.toMatrix b b (tateModuleMap ℓ α)
  have hT : tateModuleMap ℓ (α ^ m * (𝟙 A) ^ n) =
      (m : ℤ_[ℓ]) • tateModuleMap ℓ α + (n : ℤ_[ℓ]) • LinearMap.id := by
    rw [tateModuleMap_mul, tateModuleMap_zpow, tateModuleMap_zpow, tateModuleMap_id,
      ← Int.cast_smul_eq_zsmul ℤ_[ℓ], ← Int.cast_smul_eq_zsmul ℤ_[ℓ]]
  have hdetβ := endDegree_eq_det_tateModuleMap A ℓ (α ^ m * (𝟙 A) ^ n) hℓ
  have hdetα := endDegree_eq_det_tateModuleMap A ℓ α hℓ
  have htrα := trace_tateModuleMap_eq_abelianVarietyTrace A ℓ α hℓ
  rw [← LinearMap.det_toMatrix b, hT, map_add, map_smul, map_smul, LinearMap.toMatrix_id,
    Matrix.det_fin_two] at hdetβ
  rw [← LinearMap.det_toMatrix b, Matrix.det_fin_two] at hdetα
  rw [LinearMap.trace_eq_matrix_trace ℤ_[ℓ] b, Matrix.trace_fin_two] at htrα
  apply (algebraMap ℚ ℚ_[ℓ]).injective
  have e1 : ((endDegree A (α ^ m * (𝟙 A) ^ n) : ℚ) : ℚ_[ℓ]) =
      ((endDegree A (α ^ m * (𝟙 A) ^ n) : ℤ_[ℓ]) : ℚ_[ℓ]) := by
    rw [PadicInt.coe_natCast, Rat.cast_natCast]
  have e2 : ((endDegree A α : ℚ) : ℚ_[ℓ]) = ((endDegree A α : ℤ_[ℓ]) : ℚ_[ℓ]) := by
    rw [PadicInt.coe_natCast, Rat.cast_natCast]
  simp only [eq_ratCast, Rat.cast_add, Rat.cast_mul, Rat.cast_pow, Rat.cast_intCast]
  rw [e1, e2, hdetβ, hdetα, ← htrα]
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul,
    Matrix.one_apply_ne (show (0 : Fin 2) ≠ 1 by decide),
    Matrix.one_apply_ne (show (1 : Fin 2) ≠ 0 by decide)]
  push_cast
  ring

/-- **Hasse's inequality for an endomorphism** of a one-dimensional abelian variety:
`(Tr α)² ≤ 4 deg α`. -/
theorem trace_sq_le_four_mul_endDegree (hA : abelianVarietyDimension A = 1) (α : A ⟶ A)
    [IsMonHom α] : abelianVarietyTrace A α ^ 2 ≤ 4 * endDegree A α := by
  set a := abelianVarietyTrace A α
  have h := endDegree_zpow_mul_zpow hA α (2 * a.den) (-a.num)
  have hnn : (0 : ℚ) ≤ (endDegree A (α ^ (2 * (a.den : ℤ)) * (𝟙 A) ^ (-a.num)) : ℚ) :=
    Nat.cast_nonneg _
  rw [h] at hnn
  have hden : (0 : ℚ) < a.den := by exact_mod_cast a.den_pos
  have hnum : (a.num : ℚ) = a * a.den := (Rat.mul_den_eq_num a).symm
  push_cast at hnn
  rw [hnum] at hnn
  have : 0 ≤ (a.den : ℚ) ^ 2 * (4 * endDegree A α - a ^ 2) := by nlinarith
  have hpos : (0 : ℚ) < (a.den : ℚ) ^ 2 := by positivity
  nlinarith [(mul_nonneg_iff_of_pos_left hpos).mp this]

/-- The trivial endomorphism has degree `0`. -/
theorem endDegree_one (hA : abelianVarietyDimension A = 1) : endDegree A (1 : A ⟶ A) = 0 := by
  have h := endDegree_zpow_mul_zpow hA (1 : A ⟶ A) 0 0
  simp only [zpow_zero, mul_one, Int.cast_zero, zero_mul, add_zero, ne_eq,
    OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow] at h
  exact_mod_cast h

/-- A finite-kernel homomorphism of groups with finite image has finite source. -/
theorem finite_of_finite_ker_of_finite_range {G H : Type*} [Group G] [Group H] (φ : G →* H)
    [Finite φ.ker] [Finite φ.range] : Finite G := by
  have : Finite (G ⧸ φ.ker) := Finite.of_equiv _ (QuotientGroup.quotientKerEquivRange φ).symm.toEquiv
  exact Finite.of_equiv _ (Subgroup.groupEquivQuotientProdSubgroup (s := φ.ker)).symm

/-- The group of `k`-points of a one-dimensional abelian variety over an algebraically closed
field is infinite. -/
theorem infinite_points (hA : abelianVarietyDimension A = 1) :
    Infinite (𝟙_ (Over (Spec (.of k))) ⟶ A) := by
  obtain ⟨ℓ, hℓp, hℓ⟩ := exists_prime_isUnit k
  have := Fact.mk hℓp
  refine ⟨fun hfin => ?_⟩
  have : Finite (𝟙_ (Over (Spec (.of k))) ⟶ A) := hfin
  set N := Nat.card (𝟙_ (Over (Spec (.of k))) ⟶ A)
  obtain ⟨E⟩ := nonempty_torsionBy_pow_addEquiv A ℓ hℓ N
  let f : AddSubgroup.torsionBy (Additive (𝟙_ (Over (Spec (.of k))) ⟶ A)) ((ℓ ^ N : ℕ) : ℤ) →
      (𝟙_ (Over (Spec (.of k))) ⟶ A) :=
    fun x => Additive.toMul (x : Additive (𝟙_ (Over (Spec (.of k))) ⟶ A))
  have hf : Function.Injective f := fun x y hxy => Subtype.ext (Additive.toMul.injective hxy)
  have hle := Nat.card_le_card_of_injective f hf
  rw [Nat.card_congr E.toEquiv, Nat.card_fun, Nat.card_zmod, Nat.card_eq_fintype_card,
    Fintype.card_fin, hA] at hle
  have hℓ2 : 2 ≤ ℓ := hℓp.two_le
  have h1 : N < 2 ^ N := Nat.lt_two_pow_self
  have h2 : 2 ^ N ≤ ℓ ^ N := Nat.pow_le_pow_left hℓ2 N
  have h3 : ℓ ^ N ≤ (ℓ ^ N) ^ (2 * 1) := Nat.le_self_pow (by norm_num) _
  omega

/-- **The degree is positive definite**: in dimension one, `deg α = 0` iff `α` is trivial. -/
theorem endDegree_eq_zero_iff (hA : abelianVarietyDimension A = 1) (α : A ⟶ A) [IsMonHom α] :
    endDegree A α = 0 ↔ α = 1 := by
  constructor
  · intro h0
    -- `Tr α = 0`, so `χ_α = X²` and `α ∘ α = 0`
    have hle := trace_sq_le_four_mul_endDegree hA α
    rw [h0, Nat.cast_zero, mul_zero] at hle
    have htr : abelianVarietyTrace A α = 0 := by nlinarith [sq_nonneg (abelianVarietyTrace A α)]
    have hχ : endCharPoly A α = (Polynomial.X ^ 2 : ℤ[X]).map (Int.castRingHom ℚ) := by
      rw [endCharPoly_eq_of_dim_one hA α, htr, h0]; simp
    have hsq := endPolyEval_eq_one_of_endCharPoly_eq hA α _ hχ
    rw [pow_two, endPolyEval_mul, endPolyEval_X] at hsq
    -- if `α ≠ 0` its kernel is finite, hence so is `A(k)`
    by_contra hne
    have hfin : (pointKer α).Finite := by
      by_contra hinf
      exact hne (eq_one_of_infinite_pointKer hA α hinf)
    let φ := IsMonHom.monoidHom α (𝟙_ (Over (Spec (.of k))))
    have hker : (φ.ker : Set (𝟙_ (Over (Spec (.of k))) ⟶ A)) = pointKer α := rfl
    have : Finite φ.ker := by
      show Finite (φ.ker : Set (𝟙_ (Over (Spec (.of k))) ⟶ A))
      rw [hker]; exact hfin.to_subtype
    have hrange : (φ.range : Set (𝟙_ (Over (Spec (.of k))) ⟶ A)) ⊆ pointKer α := by
      rintro _ ⟨x, rfl⟩
      show (x ≫ α) ≫ α = 1
      rw [Category.assoc, hsq, MonObj.comp_one]
    have : Finite φ.range := (hfin.subset hrange).to_subtype
    have := finite_of_finite_ker_of_finite_range φ
    exact (infinite_points hA).not_finite this
  · rintro rfl
    exact endDegree_one hA

end RamanujanWeil.Arith.Deuring.Geom
