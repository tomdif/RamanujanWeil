import StacksFrontier.AlgebraicGeometry.GroupScheme.AbelianVariety.CharPoly
import StacksFrontier.AlgebraicGeometry.GroupScheme.AbelianVariety.TorsionPoints
import StacksFrontier.AlgebraicGeometry.Variety.RationalPointsHomExt
import StacksFrontier.Topology.Dimension.DimensionLEOne

/-!
# A3-ord, G3 (dimension one): homomorphisms of elliptic curves inject into Tate modules

Let `k` be algebraically closed and `A`, `B` abelian varieties over `k` (Stacks group objects
`A : Over (Spec k)`, `[GrpObj A]`, `IsAbelianVariety k A`), with `dim A = 1`. This file proves,
working against the Stacks abelian-variety API:

* `eq_one_of_infinite_pointKer`: a homomorphism `α : A ⟶ B` killing infinitely many `k`-points
  is trivial. (The kernel is closed; a proper closed subset of the irreducible curve `A` is
  finite, `Stacks.Topology.Dimension.finite_of_isClosed_of_ne_univ`; a morphism from a reduced
  variety is determined by its `k`-points, `Stacks.Varieties.overHom_ext_of_points`.)
* `eq_one_of_tateModuleMap_eq_zero`, `tateModuleMap_injective`: for `ℓ` invertible in `k`,
  `Hom(A, B) → Hom_{ℤ_ℓ}(T_ℓ A, T_ℓ B)` is injective (`T_ℓ α = 0` forces `α` to kill
  `A(k)[ℓ^n] ≅ (ℤ/ℓ^n)²` for every `n`).
* `eq_one_of_zpow_eq_one`: `Hom(A, B)` is torsion free.
* `tateModuleMap_endPolyEval`: `T_ℓ (R(α)) = R(T_ℓ α)` for `R ∈ ℤ[X]`.
* **`endPolyEval_eq_one_of_endCharPoly_eq`** (Cayley–Hamilton in `End(A)`): if the
  characteristic polynomial `χ_α ∈ ℚ[X]` of an endomorphism `α` is the image of `R ∈ ℤ[X]`,
  then `R(α) = 0` in `End(A)`.

This is the injectivity half of blueprint step G3 (`docs/ARITH_DEURING_PLAN.md` §4) for
`dim A = 1`, and the input that turns G2 (`χ_π = X² − tX + q`) into `π² − tπ + q = 0`.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory Polynomial
open scoped CategoryTheory.MonObj

universe u

namespace RamanujanWeil.Arith.Deuring.Geom

open Stacks.Groupoids

section Points

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- The unique point of `Spec k`. -/
noncomputable abbrev pt (k : Type u) [Field k] : (Spec (.of k) : Scheme.{u}) :=
  IsLocalRing.closedPoint k

/-- Two `k`-points of a scheme locally of finite type over an algebraically closed field `k` with
the same image point are equal. -/
theorem point_ext {B : Over (Spec (.of k))} [LocallyOfFiniteType B.hom]
    {P Q : 𝟙_ (Over (Spec (.of k))) ⟶ B} (h : P.left (pt k) = Q.left (pt k)) : P = Q := by
  have hcl : IsClosed ({P.left (pt k)} : Set B.left) := by
    have : IsClosedImmersion P.left := isClosedImmersion_of_comp_eq_id B.hom P.left (Over.w P)
    have hc : IsClosed ({pt k} : Set (Spec (.of k) : Scheme.{u})) :=
      isClosed_discrete (α := Spec (.of k)) _
    have h' := P.left.isClosedEmbedding.isClosedMap _ hc
    rwa [Set.image_singleton] at h'
  exact Over.OverMorphism.ext (ext_of_apply_closedPoint_eq_of_comp_eq B.hom hcl rfl h.symm
    ((Over.w P).trans (Over.w Q).symm))

end Points

section DimOne

variable {k : Type u} [Field k] [IsAlgClosed k]
  {A B : Over (Spec (.of k))} [GrpObj A] [GrpObj B]
  [AlgebraicGeometry.IsAbelianVariety k A] [AlgebraicGeometry.IsAbelianVariety k B]

/-- The `k`-points killed by a morphism `α : A ⟶ B` (into the unit section). -/
def pointKer (α : A ⟶ B) : Set (𝟙_ (Over (Spec (.of k))) ⟶ A) := {x | x ≫ α = 1}

omit [IsAlgClosed k] in
/-- The image of the constant point `1 : 𝟙 ⟶ B` is the unit `e_B`. -/
theorem one_left_apply (s : (Spec (.of k) : Scheme.{u})) :
    ((1 : 𝟙_ (Over (Spec (.of k))) ⟶ B).left s) = (η[B]).left (pt k) := by
  rw [Hom.one_def, Over.comp_left, Scheme.Hom.comp_apply]
  congr 1
  exact @Subsingleton.elim (Spec (.of k) : Scheme.{u}) _ _ _

/-- **A homomorphism from a one-dimensional abelian variety which kills infinitely many
`k`-points is trivial.** -/
theorem eq_one_of_infinite_pointKer (hA : abelianVarietyDimension A = 1) (α : A ⟶ B)
    [IsMonHom α] (h : (pointKer α).Infinite) : α = 1 := by
  set e : B.left := (η[B]).left (pt k)
  set S : Set A.left := α.left ⁻¹' {e}
  have he : IsClosed ({e} : Set B.left) := Stacks.Groupoids.isClosed_singleton_unit_left B _
  have hS : IsClosed S := he.preimage α.left.continuous
  have : CompactSpace A.left := QuasiCompact.compactSpace_of_compactSpace A.hom
  have := isLocallyNoetherian_left A
  have : IsNoetherian A.left := {}
  have hdim : topologicalKrullDim A.left ≤ 1 := by
    rw [topologicalKrullDim_eq_abelianVarietyDimension A, hA]; rfl
  -- the kernel points lie in `S`, injectively
  have hmaps : Set.MapsTo (fun x : 𝟙_ (Over (Spec (.of k))) ⟶ A => x.left (pt k)) (pointKer α) S := by
    intro x hx
    show α.left (x.left (pt k)) = e
    have hx' : x ≫ α = 1 := hx
    have := congrArg (fun r : 𝟙_ (Over (Spec (.of k))) ⟶ B => r.left (pt k)) hx'
    simp only [Over.comp_left, Scheme.Hom.comp_apply] at this
    rw [this, one_left_apply]
  have hinj : Set.InjOn (fun x : 𝟙_ (Over (Spec (.of k))) ⟶ A => x.left (pt k)) (pointKer α) :=
    fun x _ y _ hxy => point_ext hxy
  have hSinf : S.Infinite := Set.infinite_of_injOn_mapsTo hinj hmaps h
  have hSu : S = Set.univ := by
    by_contra hne
    exact hSinf (Stacks.Topology.Dimension.finite_of_isClosed_of_ne_univ hdim hS hne)
  apply Stacks.Varieties.overHom_ext_of_points
  intro P
  apply point_ext
  have hP : P.left (pt k) ∈ S := hSu ▸ Set.mem_univ _
  rw [MonObj.comp_one]
  simp only [Over.comp_left, Scheme.Hom.comp_apply]
  rw [hP, one_left_apply]

end DimOne

/-! ### Tate modules -/

/-- There is a prime invertible in any field. -/
theorem exists_prime_isUnit (k : Type u) [Field k] : ∃ ℓ : ℕ, ℓ.Prime ∧ IsUnit (ℓ : k) := by
  obtain ⟨ℓ, hle, hℓ⟩ := Nat.exists_infinite_primes (ringChar k + 1)
  refine ⟨ℓ, hℓ, isUnit_iff_ne_zero.mpr fun h0 => ?_⟩
  have hd : ringChar k ∣ ℓ := (ringChar.spec k ℓ).mp h0
  rcases hℓ.eq_one_or_self_of_dvd _ hd with h1 | h1
  · exact CharP.ringChar_ne_one h1
  · omega

section Tate

variable {k : Type u} [Field k] [IsAlgClosed k]
  {A B : Over (Spec (.of k))} [GrpObj A] [GrpObj B]
  [AlgebraicGeometry.IsAbelianVariety k A] [AlgebraicGeometry.IsAbelianVariety k B]
  (ℓ : ℕ) [Fact ℓ.Prime]

omit [IsAlgClosed k] in
/-- `T_ℓ` only depends on the homomorphism, not on the proof that it is one. -/
theorem tateModuleMap_congr {f₁ f₂ : A ⟶ B} [IsMonHom f₁] [IsMonHom f₂] (h : f₁ = f₂) :
    tateModuleMap ℓ f₁ = tateModuleMap ℓ f₂ := by
  subst h; rfl

/-- `T_ℓ α = 0` forces `α` to kill `A(k)[ℓ^n]`. -/
theorem mem_pointKer_of_tateModuleMap_eq_zero (α : A ⟶ B) [IsMonHom α]
    (h : tateModuleMap ℓ α = 0) (n : ℕ)
    (x : AddSubgroup.torsionBy (Additive (𝟙_ (Over (Spec (.of k))) ⟶ A)) ((ℓ ^ n : ℕ) : ℤ)) :
    (x : Additive (𝟙_ (Over (Spec (.of k))) ⟶ A)).toMul ∈ pointKer α := by
  obtain ⟨y, rfl⟩ := Stacks.AbelianGroup.tateReduction_surjective (exists_nsmul_eq_point A ℓ) n x
  have h1 := tateReduction_tateModuleMap (ℓ := ℓ) α n y
  rw [h, LinearMap.zero_apply, map_zero] at h1
  have h2 := congrArg (fun z : AddSubgroup.torsionBy (Additive (𝟙_ (Over (Spec (.of k))) ⟶ B))
    ((ℓ ^ n : ℕ) : ℤ) => (z : Additive (𝟙_ (Over (Spec (.of k))) ⟶ B)).toMul) h1
  exact h2.symm

/-- **`Hom(A, B) → Hom(T_ℓ A, T_ℓ B)` has trivial kernel** for `dim A = 1`, `ℓ` invertible. -/
theorem eq_one_of_tateModuleMap_eq_zero (hA : abelianVarietyDimension A = 1)
    (hℓ : IsUnit (ℓ : k)) (α : A ⟶ B) [IsMonHom α] (h : tateModuleMap ℓ α = 0) : α = 1 := by
  apply eq_one_of_infinite_pointKer hA α
  intro hfin
  have : Finite (pointKer α) := hfin.to_subtype
  set N := Nat.card (pointKer α)
  obtain ⟨E⟩ := nonempty_torsionBy_pow_addEquiv A ℓ hℓ N
  let f : AddSubgroup.torsionBy (Additive (𝟙_ (Over (Spec (.of k))) ⟶ A)) ((ℓ ^ N : ℕ) : ℤ) →
      pointKer α := fun x => ⟨_, mem_pointKer_of_tateModuleMap_eq_zero ℓ α h N x⟩
  have hf : Function.Injective f := fun x y hxy => by
    have := congrArg Subtype.val hxy
    exact Subtype.ext (Additive.toMul.injective this)
  have hle := Nat.card_le_card_of_injective f hf
  rw [Nat.card_congr E.toEquiv, Nat.card_fun, Nat.card_zmod, Nat.card_eq_fintype_card,
    Fintype.card_fin, hA] at hle
  have hℓ2 : 2 ≤ ℓ := (Fact.out : ℓ.Prime).two_le
  have h1 : N < 2 ^ N := Nat.lt_two_pow_self
  have h2 : 2 ^ N ≤ ℓ ^ N := Nat.pow_le_pow_left hℓ2 N
  have h3 : ℓ ^ N ≤ (ℓ ^ N) ^ (2 * 1) :=
    Nat.le_self_pow (by norm_num) _
  omega

/-- **Injectivity of `Hom(A, B) → Hom_{ℤ_ℓ}(T_ℓ A, T_ℓ B)`** for `dim A = 1`. -/
theorem tateModuleMap_injective (hA : abelianVarietyDimension A = 1) (hℓ : IsUnit (ℓ : k))
    (α β : A ⟶ B) [IsMonHom α] [IsMonHom β] (h : tateModuleMap ℓ α = tateModuleMap ℓ β) :
    α = β := by
  have : IsMonHom (α * β⁻¹) := isMonHom_mul _ _
  have h0 : tateModuleMap ℓ (α * β⁻¹) = 0 := by
    rw [tateModuleMap_mul, tateModuleMap_inv, h, add_neg_cancel]
  exact mul_inv_eq_one.mp (eq_one_of_tateModuleMap_eq_zero ℓ hA hℓ _ h0)

omit [Fact ℓ.Prime] in
/-- **`Hom(A, B)` is torsion free** for `dim A = 1`. -/
theorem eq_one_of_zpow_eq_one (hA : abelianVarietyDimension A = 1) (α : A ⟶ B) [IsMonHom α]
    (n : ℤ) (hn : n ≠ 0) (h : α ^ n = 1) : α = 1 := by
  obtain ⟨ℓ, hℓp, hℓ⟩ := exists_prime_isUnit k
  have := Fact.mk hℓp
  apply eq_one_of_tateModuleMap_eq_zero ℓ hA hℓ
  have h1 : tateModuleMap ℓ (α ^ n) = 0 := by
    rw [tateModuleMap_congr ℓ h, tateModuleMap_one]
  rw [tateModuleMap_zpow] at h1
  have := module_free_tateModule B ℓ hℓ
  ext1 x
  have h2 := congrArg (fun f => f x) h1
  simp only [LinearMap.smul_apply, LinearMap.zero_apply] at h2
  rw [← Int.cast_smul_eq_zsmul ℤ_[ℓ]] at h2
  rcases smul_eq_zero.mp h2 with h3 | h3
  · exact absurd h3 (Int.cast_ne_zero.mpr hn)
  · simpa using h3

/-- **`T_ℓ (R(α)) = R(T_ℓ α)`** for `R ∈ ℤ[X]`. -/
theorem tateModuleMap_endPolyEval (α : A ⟶ A) [IsMonHom α] (R : ℤ[X]) :
    haveI := isMonHom_endPolyEval α R
    tateModuleMap ℓ (endPolyEval α R) = aeval (tateModuleMap ℓ α) R := by
  induction R using Polynomial.induction_on with
  | C c =>
    have := isMonHom_endPolyEval α (C c)
    rw [tateModuleMap_congr ℓ (endPolyEval_C α c), tateModuleMap_zpow, tateModuleMap_id, aeval_C,
      algebraMap_int_eq, eq_intCast, ← zsmul_one]
    rfl
  | add R S hR hS =>
    have := isMonHom_endPolyEval α R
    have := isMonHom_endPolyEval α S
    have := isMonHom_endPolyEval α (R + S)
    rw [tateModuleMap_congr ℓ (endPolyEval_add α R S), tateModuleMap_mul, hR, hS, map_add]
  | monomial n c ih =>
    have := isMonHom_endPolyEval α (C c * Polynomial.X ^ n)
    have := isMonHom_endPolyEval α (C c * Polynomial.X ^ (n + 1))
    have hpow : (C c * Polynomial.X ^ (n + 1) : ℤ[X]) = (C c * Polynomial.X ^ n) * Polynomial.X := by ring
    have h1 : endPolyEval α (C c * Polynomial.X ^ (n + 1)) = α ≫ endPolyEval α (C c * Polynomial.X ^ n) := by
      rw [hpow, endPolyEval_mul, endPolyEval_X]
    rw [tateModuleMap_congr ℓ h1, tateModuleMap_comp, ih, hpow,
      map_mul (aeval (tateModuleMap ℓ α)) (C c * Polynomial.X ^ n) Polynomial.X, aeval_X]
    rfl

/-- **Cayley–Hamilton in `End(A)`** for `dim A = 1`: if the characteristic polynomial
`χ_α ∈ ℚ[X]` (`χ_α(n) = deg(α − n)`) is the image of `R ∈ ℤ[X]`, then `R(α) = 0`. -/
theorem endPolyEval_eq_one_of_endCharPoly_eq (hA : abelianVarietyDimension A = 1)
    (α : A ⟶ A) [IsMonHom α] (R : ℤ[X]) (hR : endCharPoly A α = R.map (Int.castRingHom ℚ)) :
    endPolyEval α R = 1 := by
  obtain ⟨ℓ, hℓp, hℓ⟩ := exists_prime_isUnit k
  have := Fact.mk hℓp
  have := module_free_tateModule A ℓ hℓ
  have := module_finite_tateModule A ℓ hℓ
  have hT := charpoly_tateModuleMap A ℓ α hℓ
  have hcp : LinearMap.charpoly (tateModuleMap ℓ α) = R.map (Int.castRingHom ℤ_[ℓ]) := by
    apply Polynomial.map_injective PadicInt.Coe.ringHom Subtype.coe_injective
    rw [hT, hR, Polynomial.map_map, Polynomial.map_map]
    congr 1
  have := isMonHom_endPolyEval α R
  apply eq_one_of_tateModuleMap_eq_zero ℓ hA hℓ
  rw [tateModuleMap_endPolyEval]
  have hCH := LinearMap.aeval_self_charpoly (tateModuleMap ℓ α)
  rw [hcp, ← algebraMap_int_eq, Polynomial.aeval_map_algebraMap] at hCH
  exact hCH

end Tate

end RamanujanWeil.Arith.Deuring.Geom
