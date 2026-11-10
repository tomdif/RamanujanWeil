import RamanujanWeil.Arith.DeuringRadicialFrob
import RamanujanWeil.Arith.DeuringG3Div
import Mathlib.FieldTheory.PurelyInseparable.Exponent

/-!
# RadicialDual: a purely inseparable isogeny of elliptic curves divides `[p^e]`

`docs/ARITH_DEURING_RADICIAL.md`. Let `k` be algebraically closed, `B`, `A'` one-dimensional
abelian varieties over `k` and `f : B ⟶ A'` a homomorphism injective on `k`-points. Write
`L = k(B)`, `K = k(A')`, with `K ⊆ L` via `f^*`.

* **(a) `isPurelyInseparable_of_injective`**: `L / K` is purely inseparable. Let `S` be the
  separable closure of `K` in `L` and `C` a proper nonsingular model of `S` (Stacks 0BY1,
  `nonempty_functionFieldModel`). Then `f = u ≫ v` with `u : B ⟶ C`, `v : C ⟶ A'`
  (`exists_hom_functionFieldMap_eq`, `over_hom_ext_of_functionFieldMap`); `u` is surjective, so
  `v` is injective on `k`-points (as `f` is), and `v` is separable. The fibre count
  (`finrank_le_one_of_injective`) gives `[S : K] = 1`.
* **(c) `exists_functionFieldMap_zpow_mem`**: with `e` the exponent of `L / K`
  (`L^{p^e} ⊆ K`) and step (b) (`[p^e]^* L ⊆ L^{p^e}`), `[p^e]^* L ⊆ K`.
* **`exists_comp_eq_zpow_of_injective`** and **`radicialDual : RadicialDual`**: the `k`-algebra
  map `L → K`, `y ↦ (f^*)^{-1}([p^e]^* y)`, is induced by a morphism `h : A' ⟶ B`
  (`exists_hom_functionFieldMap_eq`), and `f ≫ h = [p^e]` because both induce the same map of
  function fields. `h` is a homomorphism: `h ≫ f = [p^e]` too (`f` is an epimorphism), so every
  point of `A'` is in the image of `f`, `h` is multiplicative on `k`-points, and `A' ⊗ A'` is
  reduced (as in `DeuringG3Div`).

Consequently `FrobHomDual` holds (`frobHomDual`, via `frobHomDual_of_radicialDual`).
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory
  CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

universe u

namespace RamanujanWeil.Arith.Deuring.Radicial

open Stacks.Groupoids RamanujanWeil.Arith.Deuring.Geom RamanujanWeil.Arith.Deuring.Dual2

variable {k : Type u} [Field k] [IsAlgClosed k] {B A' : Over (Spec (.of k))} [GrpObj B] [GrpObj A']
  [AlgebraicGeometry.IsAbelianVariety k B] [AlgebraicGeometry.IsAbelianVariety k A']

omit [IsAlgClosed k] in
/-- An abelian variety is normal. -/
theorem isNormal_left (A : Over (Spec (.of k))) [GrpObj A]
    [AlgebraicGeometry.IsAbelianVariety k A] : IsNormal A.left := by
  have := smooth_hom A
  exact isNormal_of_isRegular _ (isRegular_of_smooth_over_field A.hom)

/-- **Step (a): a homomorphism injective on points is purely inseparable.** -/
theorem isPurelyInseparable_of_injective (hB : abelianVarietyDimension B = 1)
    (hA : abelianVarietyDimension A' = 1) (f : B ⟶ A') [IsDominant f.left]
    (hinj : ∀ x y : 𝟙_ (Over (Spec (.of k))) ⟶ B, x ≫ f = y ≫ f → x = y) :
    letI := (functionFieldMap f.left).toAlgebra
    IsPurelyInseparable A'.left.functionField B.left.functionField := by
  classical
  have hcB := isCurve_of_dim_one hB
  have hcA := isCurve_of_dim_one hA
  have := isNormal_left B
  have := isNormal_left A'
  have hiB : IsIntegral B.left := GeometricallyIntegral.isIntegral_of_subsingleton B.hom
  have hiA : IsIntegral A'.left := GeometricallyIntegral.isIntegral_of_subsingleton A'.hom
  let VB := var B
  let VA := var A'
  letI : Algebra k B.left.functionField := varietyFunctionFieldAlgebra VB
  letI : Algebra k A'.left.functionField := varietyFunctionFieldAlgebra VA
  letI : Algebra A'.left.functionField B.left.functionField :=
    (functionFieldMap f.left).toAlgebra
  haveI : IsScalarTower k A'.left.functionField B.left.functionField :=
    IsScalarTower.of_algebraMap_eq fun a => (functionFieldMap_algebraMap VB VA f a).symm
  haveI : FiniteDimensional A'.left.functionField B.left.functionField :=
    finiteDimensional_functionField_of_isCurve B.hom A'.hom f.left (Over.w f)
  haveI : Algebra.EssFiniteType k A'.left.functionField := varietyFunctionField_essFiniteType VA
  have htrL : Algebra.trdeg k B.left.functionField = 1 :=
    (isCurve_iff_trdeg_functionField_eq_one VB).mp hcB
  set S := separableClosure A'.left.functionField B.left.functionField with hSdef
  haveI : IsScalarTower k S B.left.functionField := IsScalarTower.of_algebraMap_eq fun a => rfl
  have htr : Algebra.trdeg k S = 1 := by
    have hz : Algebra.trdeg S B.left.functionField = 0 := trdeg_eq_zero
    have h := trdeg_add_eq k S (A := B.left.functionField)
    rw [hz, add_zero, htrL] at h
    exact h
  haveI : Algebra.EssFiniteType k S := Algebra.EssFiniteType.comp k A'.left.functionField S
  obtain ⟨Mo⟩ := nonempty_functionFieldModel (k := k) S htr
  have := Mo.isCurve
  have := Mo.isProper
  have : IsNormal Mo.variety.toScheme := isNormal_of_isRegular _ Mo.isRegular
  let θ : A'.left.functionField →ₐ[k] Mo.variety.toScheme.functionField :=
    Mo.equiv.symm.toAlgHom.comp ((Algebra.ofId A'.left.functionField S).restrictScalars k)
  let iota : Mo.variety.toScheme.functionField →ₐ[k] B.left.functionField :=
    ((S.val).restrictScalars k).comp Mo.equiv.toAlgHom
  obtain ⟨v, -, -, -, hvdom, hvff⟩ := exists_hom_functionFieldMap_eq Mo.variety VA θ
  obtain ⟨u, -, -, -, hudom, huff⟩ := exists_hom_functionFieldMap_eq VB Mo.variety iota
  -- `u ≫ v = f`
  have huv : u ≫ v = f := by
    haveI : IsDominant (u ≫ v).left := inferInstanceAs (IsDominant (u.left ≫ v.left))
    refine over_hom_ext_of_functionFieldMap VB VA (u ≫ v) f ?_
    rw [functionFieldMap_congr (Over.comp_left _ _ _ u v), functionFieldMap_comp, hvff, huff]
    ext a
    show ((Mo.equiv (Mo.equiv.symm (algebraMap A'.left.functionField S a)) : S) :
      B.left.functionField) = algebraMap A'.left.functionField B.left.functionField a
    rw [AlgEquiv.apply_symm_apply]
    rfl
  -- `v` is separable
  have hfu : (functionFieldMap v.left).FormallyUnramified := by
    rw [hvff]
    have : θ.toRingHom = Mo.equiv.symm.toRingEquiv.toRingHom.comp
        (algebraMap A'.left.functionField S) := RingHom.ext fun a => rfl
    rw [this]
    exact RingHom.FormallyUnramified.comp
      (formallyUnramified_algebraMap_of_isSeparable A'.left.functionField S)
      (RingHom.FormallyUnramified.of_surjective (by exact Mo.equiv.symm.surjective))
  -- `u` is surjective
  have hu_surj : Function.Surjective u.left.base := by
    have : IsProper (u.left ≫ Mo.variety.structureMap) := by
      have hw : u.left ≫ Mo.variety.structureMap = B.hom := Over.w u
      rw [hw]; infer_instance
    have : IsProper u.left := IsProper.of_comp u.left Mo.variety.structureMap
    exact (surjective_of_isDominant_of_isClosed_range _ u.left.isClosedMap.isClosed_range).surj
  -- `v` is injective on `k`-points
  have hinjv : ∀ c₁ c₂ : Spec (.of k) ⟶ Mo.variety.toScheme,
      c₁ ≫ Mo.variety.structureMap = 𝟙 _ → c₂ ≫ Mo.variety.structureMap = 𝟙 _ →
      c₁ ≫ v.left = c₂ ≫ v.left → c₁ = c₂ := by
    intro c₁ c₂ h₁ h₂ h
    obtain ⟨b₁, hb₁, rfl⟩ := exists_lift_point B.hom Mo.variety.structureMap u.left (Over.w u)
      hu_surj c₁ h₁
    obtain ⟨b₂, hb₂, rfl⟩ := exists_lift_point B.hom Mo.variety.structureMap u.left (Over.w u)
      hu_surj c₂ h₂
    let x₁ : 𝟙_ (Over (Spec (.of k))) ⟶ B := Over.homMk b₁ hb₁
    let x₂ : 𝟙_ (Over (Spec (.of k))) ⟶ B := Over.homMk b₂ hb₂
    have hx : x₁ ≫ f = x₂ ≫ f := by
      rw [← huv]
      apply Over.OverMorphism.ext
      simp only [Over.comp_left, Over.homMk_left, x₁, x₂, ← Category.assoc]
      exact h
    have := congrArg (fun x => x.left) (hinj x₁ x₂ hx)
    simp only [Over.homMk_left, x₁, x₂] at this
    rw [this]
  -- the fibre count
  have hle := finrank_le_one_of_injective Mo.variety.structureMap A'.hom v.left (Over.w v)
    hfu hinjv
  have hle' := (finrank_congr_ringHom (R := A'.left.functionField)
    (S := Mo.variety.toScheme.functionField) hvff).symm.trans_le hle
  have hS : Module.finrank A'.left.functionField S ≤ 1 := by
    letI : Algebra A'.left.functionField Mo.variety.toScheme.functionField :=
      θ.toRingHom.toAlgebra
    exact (Algebra.finrank_eq_of_equiv_equiv (RingEquiv.refl _) Mo.equiv.toRingEquiv
      (RingHom.ext fun a => by
        show algebraMap _ S a = Mo.equiv (Mo.equiv.symm (algebraMap _ S a))
        rw [AlgEquiv.apply_symm_apply])).symm.trans_le hle'
  have hpos : 0 < Module.finrank A'.left.functionField S := Module.finrank_pos
  have hbot : S = ⊥ := IntermediateField.finrank_eq_one_iff.mp (by omega)
  exact separableClosure.eq_bot_iff.mp hbot

/-- **Step (c): `[n]^* k(B) ⊆ f^* k(A')` for some `n > 0`** (`n = p^e`, `e` the exponent of the
purely inseparable extension; `n = 1` in characteristic zero). -/
theorem exists_functionFieldMap_zpow_mem (hB : abelianVarietyDimension B = 1)
    (hA : abelianVarietyDimension A' = 1) (f : B ⟶ A') [IsDominant f.left]
    (hinj : ∀ x y : 𝟙_ (Over (Spec (.of k))) ⟶ B, x ≫ f = y ≫ f → x = y) :
    ∃ n : ℕ, ∃ hn : 0 < n, ∀ y : B.left.functionField,
      haveI := isDominant_zpow hB (n : ℤ) (by exact_mod_cast hn.ne')
      functionFieldMap ((𝟙 B : B ⟶ B) ^ (n : ℤ)).left y ∈ (functionFieldMap f.left).range := by
  classical
  have hcB := isCurve_of_dim_one hB
  have hcA := isCurve_of_dim_one hA
  letI : Algebra k A'.left.functionField := varietyFunctionFieldAlgebra (var A')
  letI : Algebra A'.left.functionField B.left.functionField :=
    (functionFieldMap f.left).toAlgebra
  have hpi := isPurelyInseparable_of_injective hB hA f hinj
  haveI : FiniteDimensional A'.left.functionField B.left.functionField :=
    finiteDimensional_functionField_of_isCurve B.hom A'.hom f.left (Over.w f)
  obtain ⟨q, hq⟩ := ExpChar.exists k
  rcases hq with _ | ⟨hqp⟩
  · haveI : CharZero A'.left.functionField :=
      charZero_of_injective_algebraMap (algebraMap k A'.left.functionField).injective
    obtain ⟨e, he⟩ := (IsPurelyInseparable.hasExponent_iff' A'.left.functionField
      B.left.functionField 1).1 inferInstance
    refine ⟨1, one_pos, fun y => ?_⟩
    haveI := isDominant_zpow hB ((1 : ℕ) : ℤ) (by norm_num)
    have := he (functionFieldMap ((𝟙 B : B ⟶ B) ^ ((1 : ℕ) : ℤ)).left y)
    rw [one_pow, pow_one] at this
    exact this
  · haveI : Fact q.Prime := ⟨hqp⟩
    haveI : ExpChar A'.left.functionField q :=
      expChar_of_injective_algebraMap (algebraMap k A'.left.functionField).injective q
    obtain ⟨e, he⟩ := (IsPurelyInseparable.hasExponent_iff' A'.left.functionField
      B.left.functionField q).1 inferInstance
    refine ⟨q ^ e, pow_pos hqp.pos e, fun y => ?_⟩
    obtain ⟨w, hw⟩ := exists_pow_eq_functionFieldMap_zpow_pow hB q e y
    rw [hw]
    exact he w

/-- **RadicialDual, the general statement.** A homomorphism of one-dimensional abelian varieties
over an algebraically closed field which is injective on `k`-points is a left factor of `[n]`,
`n ≠ 0` (indeed `n = p^e`). -/
theorem exists_comp_eq_zpow_of_injective (hB : abelianVarietyDimension B = 1)
    (hA : abelianVarietyDimension A' = 1) (f : B ⟶ A') [IsMonHom f]
    (hinj : ∀ x : 𝟙_ (Over (Spec (.of k))) ⟶ B, x ≫ f = 1 → x = 1) :
    ∃ (n : ℤ) (h : A' ⟶ B), n ≠ 0 ∧ IsMonHom h ∧ f ≫ h = (𝟙 B) ^ n := by
  classical
  have hinj' : ∀ x y : 𝟙_ (Over (Spec (.of k))) ⟶ B, x ≫ f = y ≫ f → x = y := by
    intro x y hxy
    have h1 : (x * y⁻¹) ≫ f = 1 := by
      rw [show (x * y⁻¹) ≫ f = IsMonHom.monoidHom f _ (x * y⁻¹) from rfl, map_mul, map_inv]
      exact mul_inv_eq_one.mpr hxy
    exact mul_inv_eq_one.mp (hinj _ h1)
  have hf1 : f ≠ 1 := by
    intro h1
    have : Subsingleton (𝟙_ (Over (Spec (.of k))) ⟶ B) :=
      ⟨fun x y => (hinj x (by rw [h1, MonObj.comp_one])).trans
        (hinj y (by rw [h1, MonObj.comp_one])).symm⟩
    exact (infinite_points hB).not_finite inferInstance
  haveI := isDominant_of_ne_one hB hA f hf1
  have hcB := isCurve_of_dim_one hB
  have hcA := isCurve_of_dim_one hA
  have := isNormal_left B
  have := isNormal_left A'
  obtain ⟨n, hn, hmem⟩ := exists_functionFieldMap_zpow_mem hB hA f hinj'
  haveI hdn := isDominant_zpow hB (n : ℤ) (by exact_mod_cast hn.ne')
  let VB := var B
  let VA := var A'
  letI : Algebra k B.left.functionField := varietyFunctionFieldAlgebra VB
  letI : Algebra k A'.left.functionField := varietyFunctionFieldAlgebra VA
  let fA : A'.left.functionField →ₐ[k] B.left.functionField :=
    { toRingHom := functionFieldMap f.left
      commutes' := functionFieldMap_algebraMap VB VA f }
  let nA : B.left.functionField →ₐ[k] B.left.functionField :=
    { toRingHom := functionFieldMap ((𝟙 B : B ⟶ B) ^ (n : ℤ)).left
      commutes' := functionFieldMap_algebraMap VB VB ((𝟙 B : B ⟶ B) ^ (n : ℤ)) }
  have hmem' : ∀ y, nA y ∈ fA.range := fun y => by
    obtain ⟨x, hx⟩ := hmem y
    exact ⟨x, hx⟩
  let ψ : B.left.functionField →ₐ[k] A'.left.functionField :=
    (AlgEquiv.ofInjectiveField fA).symm.toAlgHom.comp (nA.codRestrict fA.range hmem')
  have hψ : ∀ y, fA (ψ y) = nA y := fun y =>
    congrArg Subtype.val
      ((AlgEquiv.ofInjectiveField fA).apply_symm_apply (nA.codRestrict fA.range hmem' y))
  obtain ⟨h₀, -, -, -, hhdom₀, hhff₀⟩ := exists_hom_functionFieldMap_eq VA VB ψ
  obtain ⟨h, hhdom, hhff⟩ : ∃ h : A' ⟶ B, ∃ _ : IsDominant h.left,
      functionFieldMap h.left = ψ.toRingHom := ⟨h₀, hhdom₀, hhff₀⟩
  have hn0 : ((n : ℕ) : ℤ) ≠ 0 := by exact_mod_cast hn.ne'
  have hfh : f ≫ h = (𝟙 B : B ⟶ B) ^ (n : ℤ) := by
    haveI : IsDominant (f ≫ h).left := inferInstanceAs (IsDominant (f.left ≫ h.left))
    refine over_hom_ext_of_functionFieldMap VB VB (f ≫ h) ((𝟙 B : B ⟶ B) ^ (n : ℤ)) ?_
    rw [functionFieldMap_congr (Over.comp_left _ _ _ f h), functionFieldMap_comp, hhff]
    ext y
    exact hψ y
  have hhf : h ≫ f = (𝟙 A' : A' ⟶ A') ^ (n : ℤ) := comp_eq_zpow_symm hB hA f hf1 h n hfh
  refine ⟨n, h, hn0, ?_, hfh⟩
  -- `h` is a homomorphism
  have hpt : ∀ x : 𝟙_ (Over (Spec (.of k))) ⟶ B, (x ≫ f) ≫ h = x ^ (n : ℤ) := fun x => by
    rw [Category.assoc, hfh, comp_zpow_id]
  have hsurj : ∀ a : 𝟙_ (Over (Spec (.of k))) ⟶ A', ∃ x, x ≫ f = a := fun a => by
    obtain ⟨c, rfl⟩ := exists_zpow_eq_point (n : ℤ) hn0 a
    exact ⟨c ≫ h, by rw [Category.assoc, hhf, comp_zpow_id]⟩
  have hmulpt : ∀ a b : 𝟙_ (Over (Spec (.of k))) ⟶ A', (a * b) ≫ h = (a ≫ h) * (b ≫ h) := by
    intro a b
    obtain ⟨x, rfl⟩ := hsurj a
    obtain ⟨y, rfl⟩ := hsurj b
    rw [show (x ≫ f) * (y ≫ f) = (x * y) ≫ f from (map_mul (IsMonHom.monoidHom f _) x y).symm,
      hpt, hpt, hpt, mul_zpow]
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
    have e2 : P ≫ (h ⊗ₘ h) ≫ μ[B] = (P ≫ fst A' A' ≫ h) * (P ≫ snd A' A' ≫ h) := by
      rw [Hom.mul_def, ← Category.assoc]
      congr 1
      apply CartesianMonoidalCategory.hom_ext <;> simp
    rw [← Category.assoc, e1, e2, hmulpt]
    simp only [Category.assoc]

/-- **`RadicialDual` holds.** -/
theorem radicialDual : RadicialDual.{u} := by
  intro k _ _ B A' _ _ _ _ hB hA f _ hinj
  exact exists_comp_eq_zpow_of_injective hB hA f hinj

/-- **`FrobHomDual` holds** (G7-dual, unconditionally). -/
theorem frobHomDual : RamanujanWeil.Arith.Deuring.Mult.FrobHomDual.{u} :=
  frobHomDual_of_radicialDual radicialDual

end RamanujanWeil.Arith.Deuring.Radicial
