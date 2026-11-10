import RamanujanWeil.Arith.DeuringRadicialDual

/-!
# `PrimeToPLink`, function-field step: right factors of purely inseparable isogenies

`docs/ARITH_DEURING_PLINK.md` §2. Let `k` be algebraically closed of characteristic `p` and `B`,
`A'`, `C` one-dimensional abelian varieties over `k`; write `L = k(B)`.

* **`exists_comp_eq_of_mem`** (generalising `Radicial.exists_comp_eq_zpow_of_injective`): if
  `f : B ⟶ A'` is injective on `k`-points and `g : B ⟶ C` is a homomorphism with
  `g^* k(C) ⊆ f^* k(A')`, then `g = f ≫ h` for a homomorphism `h : A' ⟶ C`.
* **`exists_dual_exact`**: for `f` injective on `k`-points, `deg f = p^e` and `f ≫ h = [p^e]`
  (the radicial dual of *exactly* the degree: `L^{p^e} ⊆ f^* k(A')` because every element of a
  purely inseparable extension of degree `p^e` has its `p^e`-th power in the base).
* **`exists_functionFieldMap_eq_pow`**: an endomorphism `Φ` injective on `k`-points and of degree
  `≠ 1` is inseparable, `Φ^* L ⊆ L^p` (Stacks `isSeparable_of_notMem_compositumFrobenius` with
  `[L : kL^p] = p`; a separable and purely inseparable extension is trivial).
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory
  CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

universe u

namespace RamanujanWeil.Arith.Deuring.PLink

open Stacks.Groupoids RamanujanWeil.Arith.Deuring.Geom RamanujanWeil.Arith.Deuring.Dual2
  RamanujanWeil.Arith.Deuring.Radicial

section Field

/-- In a purely inseparable extension of degree `p^e`, every `p^e`-th power lies in the base. -/
theorem pow_finrank_mem {F E : Type*} [Field F] [Field E] [Algebra F E] (p : ℕ) [hp : Fact p.Prime]
    [ExpChar F p] [IsPurelyInseparable F E] [FiniteDimensional F E] (e : ℕ)
    (he : Module.finrank F E = p ^ e) (x : E) : x ^ p ^ e ∈ (algebraMap F E).range := by
  obtain ⟨n, y, hmin⟩ := IsPurelyInseparable.minpoly_eq_X_pow_sub_C F p x
  have hdeg : (minpoly F x).natDegree ≤ Module.finrank F E :=
    minpoly.natDegree_le x
  have hnd : (minpoly F x).natDegree = p ^ n := by
    rw [hmin, Polynomial.natDegree_sub_C, Polynomial.natDegree_pow, Polynomial.natDegree_X,
      mul_one]
  have hx : x ^ p ^ n = algebraMap F E y := by
    have h := minpoly.aeval F x
    rw [hmin] at h
    simp only [map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C] at h
    exact sub_eq_zero.mp h
  have hne : n ≤ e := by
    rw [hnd, he] at hdeg
    exact (Nat.pow_le_pow_iff_right hp.out.one_lt).mp hdeg
  refine ⟨y ^ p ^ (e - n), ?_⟩
  rw [map_pow, ← hx, ← pow_mul, ← pow_add, Nat.add_sub_cancel' hne]

end Field

variable {k : Type u} [Field k] [IsAlgClosed k] {B A' C : Over (Spec (.of k))} [GrpObj B]
  [GrpObj A'] [GrpObj C] [AlgebraicGeometry.IsAbelianVariety k B]
  [AlgebraicGeometry.IsAbelianVariety k A'] [AlgebraicGeometry.IsAbelianVariety k C]

/-- A homomorphism injective on `k`-points is not trivial. -/
theorem ne_one_of_injective (hB : abelianVarietyDimension B = 1) (f : B ⟶ A')
    (hinj : ∀ x : 𝟙_ (Over (Spec (.of k))) ⟶ B, x ≫ f = 1 → x = 1) : f ≠ 1 := by
  intro h1
  have : Subsingleton (𝟙_ (Over (Spec (.of k))) ⟶ B) :=
    ⟨fun x y => (hinj x (by rw [h1, MonObj.comp_one])).trans
      (hinj y (by rw [h1, MonObj.comp_one])).symm⟩
  exact (infinite_points hB).not_finite inferInstance

/-- A homomorphism injective on `k`-points is surjective on `k`-points. -/
theorem surj_of_injective (hB : abelianVarietyDimension B = 1)
    (hA : abelianVarietyDimension A' = 1) (f : B ⟶ A') [IsMonHom f]
    (hinj : ∀ x : 𝟙_ (Over (Spec (.of k))) ⟶ B, x ≫ f = 1 → x = 1)
    (a : 𝟙_ (Over (Spec (.of k))) ⟶ A') : ∃ x, x ≫ f = a := by
  obtain ⟨n, h₁, hn, hh₁, hfh₁⟩ := exists_comp_eq_zpow_of_injective hB hA f hinj
  have hhf₁ : h₁ ≫ f = (𝟙 A') ^ n :=
    comp_eq_zpow_symm hB hA f (ne_one_of_injective hB f hinj) h₁ n hfh₁
  obtain ⟨c, rfl⟩ := exists_zpow_eq_point n hn a
  exact ⟨c ≫ h₁, by rw [Category.assoc, hhf₁, comp_zpow_id]⟩

/-- **Right factors of a homomorphism injective on points.** If `f : B ⟶ A'` is injective on
`k`-points and `g^* k(C) ⊆ f^* k(A')`, then `g = f ≫ h` with `h` a homomorphism. -/
theorem exists_comp_eq_of_mem (hB : abelianVarietyDimension B = 1)
    (hA : abelianVarietyDimension A' = 1) (hC : abelianVarietyDimension C = 1)
    (f : B ⟶ A') [IsMonHom f] (hinj : ∀ x : 𝟙_ (Over (Spec (.of k))) ⟶ B, x ≫ f = 1 → x = 1)
    (g : B ⟶ C) [IsMonHom g] [IsDominant f.left] [IsDominant g.left]
    (hmem : ∀ y : C.left.functionField,
      functionFieldMap g.left y ∈ (functionFieldMap f.left).range) :
    ∃ h : A' ⟶ C, IsMonHom h ∧ f ≫ h = g := by
  classical
  have hcB := isCurve_of_dim_one hB
  have hcA := isCurve_of_dim_one hA
  have hcC := isCurve_of_dim_one hC
  have := isNormal_left B
  have := isNormal_left A'
  have := isNormal_left C
  let VB := var B
  let VA := var A'
  let VC := var C
  letI : Algebra k B.left.functionField := varietyFunctionFieldAlgebra VB
  letI : Algebra k A'.left.functionField := varietyFunctionFieldAlgebra VA
  letI : Algebra k C.left.functionField := varietyFunctionFieldAlgebra VC
  let fA : A'.left.functionField →ₐ[k] B.left.functionField :=
    { toRingHom := functionFieldMap f.left
      commutes' := functionFieldMap_algebraMap VB VA f }
  let gA : C.left.functionField →ₐ[k] B.left.functionField :=
    { toRingHom := functionFieldMap g.left
      commutes' := functionFieldMap_algebraMap VB VC g }
  have hmem' : ∀ y, gA y ∈ fA.range := fun y => by
    obtain ⟨x, hx⟩ := hmem y
    exact ⟨x, hx⟩
  let ψ : C.left.functionField →ₐ[k] A'.left.functionField :=
    (AlgEquiv.ofInjectiveField fA).symm.toAlgHom.comp (gA.codRestrict fA.range hmem')
  have hψ : ∀ y, fA (ψ y) = gA y := fun y =>
    congrArg Subtype.val
      ((AlgEquiv.ofInjectiveField fA).apply_symm_apply (gA.codRestrict fA.range hmem' y))
  obtain ⟨h₀, -, -, -, hhdom₀, hhff₀⟩ := exists_hom_functionFieldMap_eq VA VC ψ
  obtain ⟨h, hhdom, hhff⟩ : ∃ h : A' ⟶ C, ∃ _ : IsDominant h.left,
      functionFieldMap h.left = ψ.toRingHom := ⟨h₀, hhdom₀, hhff₀⟩
  have hfh : f ≫ h = g := by
    haveI : IsDominant (f ≫ h).left := inferInstanceAs (IsDominant (f.left ≫ h.left))
    refine over_hom_ext_of_functionFieldMap VB VC (f ≫ h) g ?_
    rw [functionFieldMap_congr (Over.comp_left _ _ _ f h), functionFieldMap_comp, hhff]
    ext y
    exact hψ y
  refine ⟨h, ?_, hfh⟩
  have hpt : ∀ x : 𝟙_ (Over (Spec (.of k))) ⟶ B, (x ≫ f) ≫ h = x ≫ g := fun x => by
    rw [Category.assoc, hfh]
  have hmulpt : ∀ a b : 𝟙_ (Over (Spec (.of k))) ⟶ A', (a * b) ≫ h = (a ≫ h) * (b ≫ h) := by
    intro a b
    obtain ⟨x, rfl⟩ := surj_of_injective hB hA f hinj a
    obtain ⟨y, rfl⟩ := surj_of_injective hB hA f hinj b
    rw [show (x ≫ f) * (y ≫ f) = (x * y) ≫ f from (map_mul (IsMonHom.monoidHom f _) x y).symm,
      hpt, hpt, hpt]
    exact map_mul (IsMonHom.monoidHom g _) x y
  refine ⟨?_, ?_⟩
  · rw [← IsMonHom.one_hom f, Category.assoc, hfh]
    exact IsMonHom.one_hom _
  · have : IsReduced (A' ⊗ A').left := by
      show IsReduced (pullback A'.hom A'.hom)
      exact isReduced_pullback_over_perfectField A'.hom A'.hom
    have : LocallyOfFiniteType (A' ⊗ A').hom := by
      show LocallyOfFiniteType (pullback.fst A'.hom A'.hom ≫ A'.hom)
      infer_instance
    apply Stacks.Varieties.overHom_ext_of_points
    intro P
    have hP : P = lift (P ≫ fst A' A') (P ≫ snd A' A') := by
      apply CartesianMonoidalCategory.hom_ext <;> simp
    have e1 : P ≫ μ[A'] = (P ≫ fst A' A') * (P ≫ snd A' A') := by
      rw [Hom.mul_def, ← hP]
    have e2 : P ≫ (h ⊗ₘ h) ≫ μ[C] = (P ≫ fst A' A' ≫ h) * (P ≫ snd A' A' ≫ h) := by
      rw [Hom.mul_def, ← Category.assoc]
      congr 1
      apply CartesianMonoidalCategory.hom_ext <;> simp
    rw [← Category.assoc, e1, e2, hmulpt]
    simp only [Category.assoc]

/-- The degree of a dominant homomorphism is the degree of the extension of function fields. -/
theorem homDegree_eq_finrank (f : B ⟶ A') [IsDominant f.left] :
    letI := (functionFieldMap f.left).toAlgebra
    homDegree f = Module.finrank A'.left.functionField B.left.functionField := by
  letI := (functionFieldMap f.left).toAlgebra
  have := isProper_left_hom f
  have : IsIntegral B.left := GeometricallyIntegral.isIntegral_of_subsingleton B.hom
  have : IsIntegral A'.left := GeometricallyIntegral.isIntegral_of_subsingleton A'.hom
  rw [homDegree_of_isDominant]
  exact degreeOver_eq_finrank f.left (functionFieldMap_eq_dominantFunctionFieldMap' f.left)

/-- **Degree and exponent of a homomorphism injective on points.** `deg f = p^e` and every
`p^e`-th power of `k(B)` lies in `f^* k(A')`. -/
theorem exists_pow_mem_of_injective (p : ℕ) [hp : Fact p.Prime] [CharP k p]
    (hB : abelianVarietyDimension B = 1) (hA : abelianVarietyDimension A' = 1)
    (f : B ⟶ A') [IsMonHom f] (hinj : ∀ x : 𝟙_ (Over (Spec (.of k))) ⟶ B, x ≫ f = 1 → x = 1)
    [IsDominant f.left] :
    ∃ e : ℕ, homDegree f = p ^ e ∧
      ∀ x : B.left.functionField, x ^ p ^ e ∈ (functionFieldMap f.left).range := by
  classical
  have hcB := isCurve_of_dim_one hB
  have hcA := isCurve_of_dim_one hA
  letI : Algebra k A'.left.functionField := varietyFunctionFieldAlgebra (var A')
  letI : Algebra A'.left.functionField B.left.functionField :=
    (functionFieldMap f.left).toAlgebra
  have hinj' : ∀ x y : 𝟙_ (Over (Spec (.of k))) ⟶ B, x ≫ f = y ≫ f → x = y := by
    intro x y hxy
    have h1 : (x * y⁻¹) ≫ f = 1 := by
      rw [show (x * y⁻¹) ≫ f = IsMonHom.monoidHom f _ (x * y⁻¹) from rfl, map_mul, map_inv]
      exact mul_inv_eq_one.mpr hxy
    exact mul_inv_eq_one.mp (hinj _ h1)
  have hpi := isPurelyInseparable_of_injective hB hA f hinj'
  haveI : FiniteDimensional A'.left.functionField B.left.functionField :=
    finiteDimensional_functionField_of_isCurve B.hom A'.hom f.left (Over.w f)
  haveI : ExpChar A'.left.functionField p :=
    expChar_of_injective_algebraMap (algebraMap k A'.left.functionField).injective p
  obtain ⟨e, he⟩ := IsPurelyInseparable.finrank_eq_pow A'.left.functionField
    B.left.functionField p
  refine ⟨e, ?_, fun x => pow_finrank_mem p e he x⟩
  rw [homDegree_eq_finrank f]
  exact he

/-- **The exact radicial dual.** A homomorphism `f` injective on `k`-points has degree `p^e`,
and `f ≫ h = [p^e]` for a homomorphism `h`; moreover `k(B)^{p^e} ⊆ f^* k(A')`. -/
theorem exists_dual_exact (p : ℕ) [hp : Fact p.Prime] [CharP k p]
    (hB : abelianVarietyDimension B = 1) (hA : abelianVarietyDimension A' = 1)
    (f : B ⟶ A') [IsMonHom f] (hinj : ∀ x : 𝟙_ (Over (Spec (.of k))) ⟶ B, x ≫ f = 1 → x = 1) :
    ∃ (e : ℕ) (h : A' ⟶ B), homDegree f = p ^ e ∧ IsMonHom h ∧
      f ≫ h = (𝟙 B) ^ ((p ^ e : ℕ) : ℤ) ∧
      ∃ _ : IsDominant f.left,
        ∀ x : B.left.functionField, x ^ p ^ e ∈ (functionFieldMap f.left).range := by
  classical
  have hf1 := ne_one_of_injective hB f hinj
  haveI hfd := isDominant_of_ne_one hB hA f hf1
  obtain ⟨e, hdeg, hpow⟩ := exists_pow_mem_of_injective p hB hA f hinj
  have hpe : ((p ^ e : ℕ) : ℤ) ≠ 0 := by exact_mod_cast (pow_pos hp.out.pos e).ne'
  haveI := isDominant_zpow hB ((p ^ e : ℕ) : ℤ) hpe
  have hmem : ∀ y : B.left.functionField,
      functionFieldMap ((𝟙 B : B ⟶ B) ^ ((p ^ e : ℕ) : ℤ)).left y ∈
        (functionFieldMap f.left).range := by
    intro y
    obtain ⟨w, hw⟩ := exists_pow_eq_functionFieldMap_zpow_pow hB p e y
    rw [hw]
    exact hpow w
  obtain ⟨h, hh, hfh⟩ := exists_comp_eq_of_mem hB hA hB f hinj _ hmem
  exact ⟨e, h, hdeg, hh, hfh, hfd, hpow⟩

/-- **A purely inseparable endomorphism of degree `≠ 1` is inseparable**: `Φ^* L ⊆ L^p`. -/
theorem exists_functionFieldMap_eq_pow (p : ℕ) [hp : Fact p.Prime] [CharP k p]
    (hB : abelianVarietyDimension B = 1) (Φ : B ⟶ B) [IsMonHom Φ]
    (hinj : ∀ x : 𝟙_ (Over (Spec (.of k))) ⟶ B, x ≫ Φ = 1 → x = 1) (hdeg : homDegree Φ ≠ 1)
    [IsDominant Φ.left] (y : B.left.functionField) :
    ∃ w : B.left.functionField, functionFieldMap Φ.left y = w ^ p := by
  classical
  set φ : B.left.functionField →+* B.left.functionField := functionFieldMap Φ.left
  letI : Algebra k B.left.functionField := varietyFunctionFieldAlgebra (var B)
  have hcurve : IsCurve k B.hom := isCurve_of_dim_one hB
  have := smooth_hom B
  have : CharP B.left.functionField p := charP_functionField p B.hom
  have : ExpChar B.left.functionField p := ExpChar.prime hp.out
  have : ExpChar k p := ExpChar.prime hp.out
  have hiB : IsIntegral B.left := GeometricallyIntegral.isIntegral_of_subsingleton B.hom
  by_contra hne
  push Not at hne
  have hnot : φ y ∉ compositumFrobenius k B.left.functionField p := by
    rw [compositumFrobenius_eq_fieldRange_frobenius k B.left.functionField p]
    intro hmem
    obtain ⟨w, hw⟩ := RingHom.mem_fieldRange.mp hmem
    exact hne w (by rw [← hw, frobenius_def])
  set N : Subfield B.left.functionField := φ.fieldRange
  have hdeg' := finrank_compositumFrobenius_functionField p B.hom
  have hfin : @Module.Finite B.left.functionField B.left.functionField _ _
      φ.toAlgebra.toModule :=
    finiteDimensional_functionField_of_isCurve B.hom B.hom Φ.left (Over.w Φ)
  let eN : B.left.functionField ≃+* N :=
    RingEquiv.ofBijective φ.rangeRestrictField φ.rangeRestrictField_bijective
  have : Module.Finite N B.left.functionField :=
    @Module.Finite.of_equiv_equiv B.left.functionField B.left.functionField N
      B.left.functionField _ _ _ _ φ.toAlgebra _ eN (RingEquiv.refl B.left.functionField)
      (RingHom.ext fun a => rfl) hfin
  have hkE : ∀ a : k, algebraMap k B.left.functionField a ∈
      (algebraMap N B.left.functionField).fieldRange := by
    intro a
    exact RingHom.mem_fieldRange.mpr ⟨⟨algebraMap k B.left.functionField a,
      RingHom.mem_fieldRange.mpr ⟨algebraMap k B.left.functionField a,
        functionFieldMap_algebraMap (var B) (var B) Φ a⟩⟩, rfl⟩
  have hsep := isSeparable_of_notMem_compositumFrobenius (E := N) (k := k) p hdeg' hkE
    (f := ⟨φ y, RingHom.mem_fieldRange.mpr ⟨y, rfl⟩⟩) hnot
  -- `L / N` is purely inseparable
  have hinj' : ∀ x y : 𝟙_ (Over (Spec (.of k))) ⟶ B, x ≫ Φ = y ≫ Φ → x = y := by
    intro x y hxy
    have h1 : (x * y⁻¹) ≫ Φ = 1 := by
      rw [show (x * y⁻¹) ≫ Φ = IsMonHom.monoidHom Φ _ (x * y⁻¹) from rfl, map_mul, map_inv]
      exact mul_inv_eq_one.mpr hxy
    exact mul_inv_eq_one.mp (hinj _ h1)
  have hpi := isPurelyInseparable_of_injective hB hB Φ hinj'
  have hpow : ∀ x : B.left.functionField, ∃ n : ℕ, x ^ p ^ n ∈ φ.range := by
    intro x
    letI : Algebra B.left.functionField B.left.functionField := φ.toAlgebra
    haveI : ExpChar B.left.functionField p := ExpChar.prime hp.out
    exact @IsPurelyInseparable.pow_mem _ _ _ _ _ φ.toAlgebra p _ x hpi
  haveI : ExpChar N p := ExpChar.prime hp.out
  have hpiN : IsPurelyInseparable N B.left.functionField := by
    rw [isPurelyInseparable_iff_pow_mem N p]
    intro x
    obtain ⟨n, z, hz⟩ := hpow x
    exact ⟨n, ⟨⟨φ z, RingHom.mem_fieldRange.mpr ⟨z, rfl⟩⟩, hz⟩⟩
  have hsurjN := IsPurelyInseparable.surjective_algebraMap_of_isSeparable N B.left.functionField
  have hsurj : Function.Surjective φ := fun x => by
    obtain ⟨⟨_, hz⟩, hx⟩ := hsurjN x
    obtain ⟨z, rfl⟩ := RingHom.mem_fieldRange.mp hz
    exact ⟨z, hx⟩
  apply hdeg
  rw [homDegree_eq_finrank Φ]
  letI : Algebra B.left.functionField B.left.functionField := φ.toAlgebra
  let i : B.left.functionField ≃+* B.left.functionField :=
    RingEquiv.ofBijective φ ⟨φ.injective, hsurj⟩
  have h := @Algebra.finrank_eq_of_equiv_equiv B.left.functionField B.left.functionField _ _
    φ.toAlgebra B.left.functionField B.left.functionField _ _ (Algebra.id _) i
    (RingEquiv.refl _) (RingHom.ext fun a => rfl)
  rw [h, Module.finrank_self]

end RamanujanWeil.Arith.Deuring.PLink
