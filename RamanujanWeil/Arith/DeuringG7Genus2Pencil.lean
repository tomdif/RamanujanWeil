import RamanujanWeil.Arith.DeuringG7Genus2PencilGeom
import RamanujanWeil.Arith.DeuringG7Genus2Canon

/-!
# A3-ord, G7-C: `Genus2PencilFunctionField` and `Genus2ModelExistence`, proved

`docs/ARITH_DEURING_G7_GENUS2.md` §7. Let `Y / K` be a smooth proper geometrically irreducible
curve of genus 2 and `L` invertible of degree 2 with `h⁰(L) = 2`.

1. **Base points.** A basis of `H⁰(L)` lifts to two sections `t₀, t₁` generating an invertible
   `L' → L` (Stacks 0CC4, `hasGeneratingInvertibleLift_seriesSections`). Then `deg L' = 2`:
   * `deg L' ≤ deg L = 2` (Stacks 0B40 (5), the map `L' → L` is nonzero);
   * `deg L' ≤ 0` is impossible: `L'` would be trivial (0B40 (4)), so `h⁰(L') = 1`, while
     `H⁰(L') → H⁰(L)` hits a basis (`two_le_finrank_H0`);
   * `deg L' = 1` is impossible: `dim V n = n − 1` for `n ≥ 3` (Riemann–Roch and 0B90,
     `finrank_tensorPower_eq_of_deg`) contradicts `GradedPencil.two_le`.
2. **The graded pencil** of `(L', t₀, t₁)` (`DeuringG7Genus2PencilGeom`) has `dim V n = 2n − 1`
   for `n ≥ 2` and generates `K(Y)` (`L'` is ample, Stacks 0B5X), so it gives
   `IntegralPencilData` (`GradedPencil.toIntegralPencilData`).

Main results:

* **`genus2PencilFunctionField : Genus2PencilFunctionField K`** (every field `K`);
* **`genus2ModelExistence : Genus2ModelExistence K`**, with `genus2ModelExistence_of_pencil`.
-/

universe u

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite Module
open Stacks.SheafOfModules.Invertible (tensorPower tensorPower_isInvertible)
open Stacks.TensorPowers (natTensorPow)

namespace RamanujanWeil.Arith.Deuring.Geom.G7.Genus2.Pencil

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory
  Stacks.SectionRingGeometric.schemePreadditive
  Stacks.SectionRingGeometric.schemeTensorRightAdditive

attribute [local implicit_reducible] Stacks.TensorPowers.natTensorPow

attribute [local instance] Stacks.AlgebraicGeometry.ProjectiveSpaceGeneratingSections.globalSectionsModule

open Exist

attribute [local instance] Setup.algK

variable {K : Type u} [Field K]

section Curve

variable {Y : Scheme.{u}} (s : Y ⟶ Spec (.of K)) [IsCurve K s] [Smooth s] [IsProper s]
  [GeometricallyIrreducible s]

/-- **Riemann–Roch on a genus-2 curve**: `h⁰(L^{⊗n}) = n·deg L − 1` once `n·deg L ≥ 3`. -/
theorem finrank_tensorPower_eq_of_deg (hg : genus s = 2) (L : Y.Modules)
    [SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 L] (d : ℤ)
    (hL : invertibleCurveDegree K s (hdim s) L = d) (n : ℕ) (hn : (3 : ℤ) ≤ n * d) :
    (Module.finrank K (cohomologyOverField K s
      (tensorPower Y.toRingedSpace.presheaf (structureSheafRing Y.toRingedSpace).property L n)
        0) : ℤ) = n * d - 1 := by
  have := geometricallyIntegral s
  have hinv := tensorPower_isInvertible Y.toRingedSpace.presheaf
    (structureSheafRing Y.toRingedSpace).property L n
  have hdeg := invertibleCurveDegree_tensorPower_eq_mul_of_isCurve K s (hdim s) L n
  rw [hL] at hdeg
  have hz := isZero_cohomologyOverField_one_of_geometricallyIntegral K s _ hinv (by
    rw [hg]
    refine le_of_le_of_eq ?_ hdeg.symm
    push_cast
    linarith)
  have hrr := finrank_sub_finrank_eq s hg (tensorPower Y.toRingedSpace.presheaf
    (structureSheafRing Y.toRingedSpace).property L n)
  have : Subsingleton (cohomologyOverField K s (tensorPower Y.toRingedSpace.presheaf
      (structureSheafRing Y.toRingedSpace).property L n) 1) :=
    (ModuleCat.subsingleton_of_isZero hz)
  rw [Module.finrank_zero_of_subsingleton (M := cohomologyOverField K s
    (tensorPower Y.toRingedSpace.presheaf (structureSheafRing Y.toRingedSpace).property L n) 1),
    hdeg] at hrr
  linear_combination hrr

end Curve

/-! ### The graded pencil of a lifted pencil -/

section Pencil

variable {Y : Scheme.{u}} [IsIntegral Y] [Y.Over (Spec (.of K))]

theorem finrank_sections_eq (M : Y.Modules) :
    finrank K Γ(M, ⊤) = finrank K (cohomologyOverField K (Y ↘ Spec (.of K)) M 0) :=
  ((cohomologyOverFieldZeroIsoSections K (Y ↘ Spec (.of K)) M).toLinearEquiv).finrank_eq.symm

theorem finiteDimensional_sections [IsProper (Y ↘ Spec (.of K))] (L : Y.Modules)
    [Stacks.Ample.IsInvertibleModule Y L] (m : ℕ) :
    FiniteDimensional K Γ(natTensorPow L m, ⊤) := by
  have := GenusOne.finiteDimensional_cohomologyOverField_natTensorPow (Y ↘ Spec (.of K)) L m 0
  exact LinearEquiv.finiteDimensional
    ((cohomologyOverFieldZeroIsoSections K (Y ↘ Spec (.of K)) (natTensorPow L m)).toLinearEquiv)

/-- `dim V n = h⁰(L^{⊗n})` for `n ≥ 1`. -/
theorem Setup.finrank_V_eq (S : Setup Y) (n : ℕ) (hn : 1 ≤ n) :
    finrank K (S.V (K := K) n) = finrank K (cohomologyOverField K (Y ↘ Spec (.of K))
      (tensorPower Y.toRingedSpace.presheaf (structureSheafRing Y.toRingedSpace).property S.L
        ((1 * n : ℕ) : ℤ)) 0) := by
  rw [S.finrank_V n hn, finrank_sections_eq,
    finrank_cohomologyOverField_eq_of_iso K _ (GenusOne.tensorPowerIsoNatTensorPow S.L (1 * n)) 0]

end Pencil

/-! ### The main theorem -/

section Main

variable {Y : Scheme.{u}} (s : Y ⟶ Spec (.of K)) [IsCurve K s] [Smooth s] [IsProper s]
  [GeometricallyIrreducible s]

/-- **`H⁰(L') → H⁰(L)` hits a basis**, so `h⁰(L') ≥ 2` whenever `h⁰(L') ` is finite. -/
theorem two_le_finrank_H0 (L L' : Y.Modules) (j : L' ⟶ L) (b : Module.Basis (Fin 2) K
    (⊤ : Submodule K (cohomologyOverField K s L 0))) (t : Fin 2 → Γ(L', ⊤))
    (hj : ∀ i, j.app ⊤ (t i) =
      cohomologyOverFieldZeroEquivSections K s L (b i : cohomologyOverField K s L 0))
    [FiniteDimensional K (cohomologyOverField K s L' 0)] :
    2 ≤ finrank K (cohomologyOverField K s L' 0) := by
  set φ := (cohomologyOverFieldMap K s j 0).hom
  have hmem : ∀ i, (b i : cohomologyOverField K s L 0) ∈ LinearMap.range φ := fun i => by
    refine ⟨(cohomologyOverFieldZeroEquivSections K s L').symm (t i), ?_⟩
    apply (cohomologyOverFieldZeroEquivSections K s L).injective
    rw [← hj i]
    have := cohomologyOverFieldZeroEquivSections_cohomologyOverFieldMap K s j
      ((cohomologyOverFieldZeroEquivSections K s L').symm (t i))
    rw [Equiv.apply_symm_apply] at this
    exact this
  have hli : LinearIndependent K (fun i => (⟨b i, hmem i⟩ : LinearMap.range φ)) := by
    refine LinearIndependent.of_comp (LinearMap.range φ).subtype ?_
    exact b.linearIndependent.map' (⊤ : Submodule K _).subtype (Submodule.ker_subtype _)
  have h1 := hli.fintype_card_le_finrank
  rw [Fintype.card_fin] at h1
  exact h1.trans (LinearMap.finrank_range_le φ)

/-- **The canonical pencil on the function field.** -/
theorem genus2PencilFunctionField_aux (hg : genus s = 2) (L : Y.Modules)
    [SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 L]
    (hdegL : invertibleCurveDegree K s (hdim s) L = 2)
    (h0L : Module.finrank K (cohomologyOverField K s L 0) = 2) :
    letI := functionFieldAlgebra K s; Nonempty (IntegralPencilData K Y.functionField) := by
  letI : Y.Over (Spec (.of K)) := ⟨s⟩
  haveI : IsProper (Y ↘ Spec (.of K)) := ‹IsProper s›
  have hint : IsIntegral Y := IsCurve.toIsVariety.toIsIntegral (k := K) (f := s)
  have hnoeth : IsLocallyNoetherian Y :=
    Stacks.AlgebraicGeometry.CurveEulerBridge.isLocallyNoetherian_of_isProper_over_field K s
  have hreg : IsRegular Y := isRegular_of_smooth_field s
  -- the linear series `(L, H⁰(L))` and a basis
  let E : LinearSeries K s (hdim s) 2 1 :=
    { L := L
      isInvertible := inferInstance
      degree_eq := by rw [hdegL]; norm_num
      V := ⊤
      finrank_eq := by rw [finrank_top, h0L] }
  obtain ⟨b⟩ := Stacks.LinearSeriesMorphism.nonempty_basis E
  -- Stacks 0CC4: the generating invertible lift
  obtain ⟨L', hL', j, t, hgen, hj⟩ :=
    Stacks.LinearSeriesMorphism.hasGeneratingInvertibleLift_seriesSections hreg E b
  have ht0 : ∀ i, t i ≠ 0 := fun i h => by
    refine Stacks.LinearSeriesMorphism.seriesSections_ne_zero E b i ?_
    rw [← hj i, h, map_zero]
  have hLinv : SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 L' := hL'
  -- the setup
  have hη : ∀ i, genericPoint Y ∈ Stacks.AmpleFiniteAvoidance.nvOpen L' (deg1 L' (t i)) := by
    intro i
    rw [nvOpen_deg1, Stacks.NonvanishingSpelling.mem_nonvanishingOpen_iff]
    have hmax : Stacks.ModuleStalk.maximalSmul L' (genericPoint Y) = ⊥ := by
      have hm : IsLocalRing.maximalIdeal (Y.presheaf.stalk (genericPoint Y)) = ⊥ :=
        IsLocalRing.isField_iff_maximalIdeal_eq.mp (Field.toIsField Y.functionField)
      rw [Stacks.ModuleStalk.maximalSmul, hm, Submodule.bot_smul]
    rw [hmax, Submodule.mem_bot]
    exact Stacks.AlgebraicGeometry.ReflexiveModules.Γgerm_genericPoint_ne_zero_of_ne_zero L'
      (ht0 i)
  have hcov : (⊤ : Y.Opens) ≤ Stacks.AmpleFiniteAvoidance.nvOpen L' (deg1 L' (t 0)) ⊔
      Stacks.AmpleFiniteAvoidance.nvOpen L' (deg1 L' (t 1)) := by
    intro y _
    obtain ⟨i, hi⟩ := Stacks.ProjectiveFromSections.exists_mem_nvCover_of_generatesStalks t hgen y
    rw [Opens.mem_sup, nvOpen_deg1, nvOpen_deg1]
    fin_cases i
    · exact Or.inl hi
    · exact Or.inr hi
  let S : Setup Y := ⟨L', t, hη, hcov⟩
  have hfin : ∀ n, 1 ≤ n → FiniteDimensional K Γ(natTensorPow S.L (1 * n), ⊤) :=
    fun n _ => finiteDimensional_sections (K := K) S.L (1 * n)
  let P := S.gradedPencil (K := K) hfin
  -- the degree of `L'`
  set d' := invertibleCurveDegree K s (hdim s) L' with hd'
  have hj0 : j ≠ 0 := by
    intro h
    apply Stacks.LinearSeriesMorphism.seriesSections_ne_zero E b 0
    rw [← hj 0, h, Scheme.Modules.Hom.zero_app]
    rfl
  have hle : d' ≤ 2 :=
    (invertibleCurveDegree_le_of_hom_ne_zero K s (hdim s) L' L j hj0).trans_eq hdegL
  have hpos : 1 ≤ d' := by
    by_contra hlt
    push Not at hlt
    have hL'' : SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property L' := hL'
    have htriv := isTrivial_of_invertibleCurveDegree_nonpos K s (hdim s) L' (hL := hL'')
      (Stacks.SheafOfModules.sectionsOfTop L' (t 0))
      (by erw [Stacks.SheafOfModules.sectionsOfTop_eval_top]; exact ht0 0)
      (Int.le_of_lt_add_one hlt)
    obtain ⟨e⟩ := htriv
    have := isIso_globalSections s
    have h1 : Module.finrank K (cohomologyOverField K s L' 0) = 1 :=
      (finrank_cohomologyOverField_eq_of_iso K s e 0).trans
        (finrank_cohomologyOverField_unit_zero_eq_one s)
    have : FiniteDimensional K (cohomologyOverField K s L' 0) :=
      Module.finite_of_finrank_eq_succ h1
    have h2 := two_le_finrank_H0 s L L' j b t hj
    omega
  have hd2 : d' = 2 := by
    by_contra hne
    have hd1 : d' = 1 := by omega
    have hdim1 : ∀ n, 3 ≤ n → (finrank K (P.V n) : ℤ) = ((1 : ℕ) : ℤ) * n - 1 := by
      intro n hn
      show (finrank K (S.V (K := K) n) : ℤ) = _
      rw [S.finrank_V_eq n (by omega)]
      have := finrank_tensorPower_eq_of_deg s hg L' 1 (by exact hd1) (1 * n) (by push_cast; omega)
      exact this.trans (by push_cast; ring)
    have := P.two_le hdim1 le_rfl
    omega
  -- dimensions and generation
  have hdim2 : ∀ n, 2 ≤ n → (finrank K (P.V n) : ℤ) = 2 * n - 1 := by
    intro n hn
    show (finrank K (S.V (K := K) n) : ℤ) = _
    rw [S.finrank_V_eq n (by omega)]
    have := finrank_tensorPower_eq_of_deg s hg L' 2 (by exact hd2) (1 * n) (by push_cast; omega)
    exact this.trans (by push_cast; ring)
  have hamp : Stacks.Ample.IsAmple Y L' :=
    Stacks.PowerFamilyBridge.isAmple_of_modulesIsAmple Y L'
      ((isAmple_iff_invertibleCurveDegree_pos K s (hdim s) L').mpr (by omega))
  have huc : UniversallyClosed Y.toSpecΓ :=
    Stacks.SectionRingProjMorphism.ToSpecZero.universallyClosed_toSpecΓ s
  have hgenF := fun f => S.exists_div (K := K) hamp huc f
  exact ⟨P.toIntegralPencilData hdim2 hgenF⟩

/-- **`Genus2PencilFunctionField K` holds over every field.** -/
theorem genus2PencilFunctionField : Genus2PencilFunctionField K := by
  intro Y s _ _ _ _ hg L _ hdegL h0L _
  exact genus2PencilFunctionField_aux s hg L hdegL h0L

/-- **`Genus2ModelExistence K` holds over every field**: every smooth proper geometrically
irreducible curve of genus 2 has a hyperelliptic model `y² + h(x) y = f(x)`, `deg h ≤ 3`,
`deg f ≤ 6`. -/
theorem genus2ModelExistence : Genus2ModelExistence K :=
  genus2ModelExistence_of_pencil genus2PencilFunctionField

end Main

end RamanujanWeil.Arith.Deuring.Geom.G7.Genus2.Pencil
