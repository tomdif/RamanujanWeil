import RamanujanWeil.Arith.ESPropC
import RamanujanWeil.Arith.ESPropBRegions
import RamanujanWeil.Arith.ESTraceW

/-!
# A2 / ES-P5: property (B) for `T̃ₙ` (docs/ARITH_ES_PLAN.md, §2 P5)

The pointwise identities `ptC_16a`, `ptC_16b` become exact identities in `ℚ[M₂(ℤ)]`:

* `Ttilde_16a : T̃ₙ = −F − (−U)F S − (−U²)F + T₁ − T₁S`,
* `Ttilde_16b : T̃ₙ = −G − (−S)G U + T₁ − T₁U + (Q − QU)/12`,

(`F, G, T₁, Q` truncated to determinant `n`, all supported in `[−n, n]⁴`). Since `S²` and `U³`
act trivially on `V₁₀`, these give PZ's

  `T̃(1 + S) ≡ −(1 + U + U²)F(1 + S)`,   `T̃(1 + U + U²) ≡ −(1 + S)G(1 + U + U²)`

as identities of operators on `V₁₀` (`PropBact (Ttilde n)`), and hence (`trace_eq_trace_Wper'`)
`tr(T̃ₙ | V₁₀) = tr(T̃ₙ | W₁₀)` (PZ Prop. 3).
-/

open Finset Module

namespace RamanujanWeil.Arith.ES

open M2

/-! ### Elements of the group ring from coefficient functions -/

/-- `Σ_{M ∈ [−n,n]⁴, det M = n} f(M) · M`. -/
noncomputable def elt (n : ℕ) (f : M2 → ℚ) : R :=
  ∑ M ∈ boxM n, (if M.det = n then f M else 0) • MonoidAlgebra.of ℚ M2 M

lemma elt_coeff {n : ℕ} {f : M2 → ℚ} (hf : ∀ M, M.det = (n : ℤ) → f M ≠ 0 → EntBd n M)
    (N : M2) : (elt n f).coeff N = if N.det = n then f N else 0 := by
  unfold elt
  rw [MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]
  simp only [MonoidAlgebra.coeff_smul, MonoidAlgebra.of_apply, MonoidAlgebra.coeff_single,
    Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq']
  by_cases hN : N ∈ boxM n
  · rw [esIfPos hN]
  · rw [esIfNeg hN]
    by_cases hd : N.det = n
    · rw [esIfPos hd]
      by_contra hne
      exact hN (mem_boxM.mpr (hf N hd (Ne.symm hne)))
    · rw [esIfNeg hd]

lemma Ttilde_eq_elt (n : ℕ) : Ttilde n = elt n ptC := by
  unfold Ttilde elt
  rw [sum_boxM]
  rfl

/-! ### Coefficients of products with invertible matrices -/

lemma coeff_of_mul {g g' : M2} (h1 : g' * g = 1) (h2 : g * g' = 1) (x : R) (M : M2) :
    (MonoidAlgebra.of ℚ M2 g * x).coeff M = x.coeff (g' * M) := by
  rw [MonoidAlgebra.of_apply, MonoidAlgebra.coeff_single_mul_eq_mul_coeff (g' * M), one_mul]
  intro m' _
  constructor
  · intro h; rw [← h, ← mul_assoc, h1, one_mul]
  · intro h; rw [h, ← mul_assoc, h2, one_mul]

lemma coeff_mul_of {g g' : M2} (h1 : g * g' = 1) (h2 : g' * g = 1) (x : R) (M : M2) :
    (x * MonoidAlgebra.of ℚ M2 g).coeff M = x.coeff (M * g') := by
  rw [MonoidAlgebra.of_apply, MonoidAlgebra.coeff_mul_single_eq_coeff_mul (M * g'), mul_one]
  intro m' _
  constructor
  · intro h; rw [← h, mul_assoc, h1, mul_one]
  · intro h; rw [h, mul_assoc, h2, mul_one]

/-- `S⁻¹`. -/
def Si : M2 := ⟨0, 1, -1, 0⟩
/-- `U⁻¹`. -/
def Ui : M2 := ⟨0, 1, -1, 1⟩

lemma S_Si : S * Si = 1 := by decide
lemma Si_S : Si * S = 1 := by decide
lemma U_Ui : U * Ui = 1 := by decide
lemma Ui_U : Ui * U = 1 := by decide
lemma nU_nUi : -U * -Ui = 1 := by decide
lemma nUi_nU : -Ui * -U = 1 := by decide
lemma nUU_nUiUi : -(U * U) * -(Ui * Ui) = 1 := by decide
lemma nUiUi_nUU : -(Ui * Ui) * -(U * U) = 1 := by decide
lemma nS_nSi : -S * -Si = 1 := by decide
lemma nSi_nS : -Si * -S = 1 := by decide

lemma mapA_eq (M : M2) : -Ui * (M * Si) = mapA M := by
  obtain ⟨a, b, c, d⟩ := M; ext <;> simp [Ui, Si, mapA] <;> ring
lemma mapB_eq (M : M2) : -(Ui * Ui) * M = mapB M := by
  obtain ⟨a, b, c, d⟩ := M; ext <;> simp [Ui, mapB] <;> ring
lemma mapC_eq (M : M2) : M * Si = mapC M := by
  obtain ⟨a, b, c, d⟩ := M; ext <;> simp [Si, mapC]
lemma mapD_eq (M : M2) : -Si * (M * Ui) = mapD M := by
  obtain ⟨a, b, c, d⟩ := M; ext <;> (simp [Ui, Si, mapD]; try ring)
lemma mapE_eq (M : M2) : M * Ui = mapE M := by
  obtain ⟨a, b, c, d⟩ := M; ext <;> simp [Ui, mapE]

lemma det_mapA (M : M2) : (mapA M).det = M.det := by simp only [mapA, det]; ring
lemma det_mapB (M : M2) : (mapB M).det = M.det := by simp only [mapB, det]; ring
lemma det_mapC (M : M2) : (mapC M).det = M.det := by simp only [mapC, det]; ring
lemma det_mapD (M : M2) : (mapD M).det = M.det := by simp only [mapD, det]; ring
lemma det_mapE (M : M2) : (mapE M).det = M.det := by simp only [mapE, det]; ring

/-! ### (16a) and (16b) in `ℚ[M₂(ℤ)]` -/

local notation "ofM" => MonoidAlgebra.of ℚ M2

lemma fF {n : ℕ} : ∀ M, M.det = (n : ℤ) → regF M ≠ 0 → EntBd n M := fun _ h1 h2 => regF_bd h1 h2
lemma fG {n : ℕ} : ∀ M, M.det = (n : ℤ) → regG M ≠ 0 → EntBd n M := fun _ h1 h2 => regG_bd h1 h2
lemma fQ {n : ℕ} : ∀ M, M.det = (n : ℤ) → regQ M ≠ 0 → EntBd n M := fun _ h1 h2 => regQ_bd h1 h2
lemma fT1 {n : ℕ} : ∀ M, M.det = (n : ℤ) → regT1 M ≠ 0 → EntBd n M :=
  fun _ h1 h2 => regT1_bd h1 h2
lemma fptC {n : ℕ} : ∀ M, M.det = (n : ℤ) → ptC M ≠ 0 → EntBd n M :=
  fun _ h1 h2 => ptC_support h1 h2

/-- **PZ (16a)** in `ℚ[M₂(ℤ)]`: `T̃ₙ = −F − (−U)F S − (−U²)F + T₁ − T₁ S`. -/
theorem Ttilde_16a (n : ℕ) :
    Ttilde n = -elt n regF - ofM (-U) * elt n regF * ofM S - ofM (-(U * U)) * elt n regF +
      elt n regT1 - elt n regT1 * ofM S := by
  rw [Ttilde_eq_elt, ← MonoidAlgebra.coeff_inj]
  ext M
  simp only [MonoidAlgebra.coeff_add, MonoidAlgebra.coeff_sub, MonoidAlgebra.coeff_neg,
    Finsupp.add_apply, Finsupp.sub_apply, Finsupp.neg_apply]
  rw [coeff_mul_of S_Si Si_S, coeff_of_mul nUi_nU nU_nUi, coeff_of_mul nUiUi_nUU nUU_nUiUi,
    coeff_mul_of S_Si Si_S, mapA_eq, mapB_eq, mapC_eq, elt_coeff fptC, elt_coeff fF, elt_coeff fF,
    elt_coeff fF, elt_coeff fT1, elt_coeff fT1, det_mapA, det_mapB, det_mapC]
  by_cases h : M.det = n
  · simp only [esIfPos h]; exact ptC_16a M
  · simp only [esIfNeg h]; ring

/-- **PZ (16b)** in `ℚ[M₂(ℤ)]`: `T̃ₙ = −G − (−S)G U + T₁ − T₁U + (Q − QU)/12`. -/
theorem Ttilde_16b (n : ℕ) :
    Ttilde n = -elt n regG - ofM (-S) * elt n regG * ofM U + elt n regT1 -
      elt n regT1 * ofM U + (1 / 12 : ℚ) • (elt n regQ - elt n regQ * ofM U) := by
  rw [Ttilde_eq_elt, ← MonoidAlgebra.coeff_inj]
  ext M
  simp only [MonoidAlgebra.coeff_add, MonoidAlgebra.coeff_sub, MonoidAlgebra.coeff_neg,
    MonoidAlgebra.coeff_smul, Finsupp.add_apply, Finsupp.sub_apply, Finsupp.neg_apply,
    Finsupp.smul_apply, smul_eq_mul]
  rw [coeff_mul_of U_Ui Ui_U, coeff_of_mul nSi_nS nS_nSi, coeff_mul_of U_Ui Ui_U,
    coeff_mul_of U_Ui Ui_U, mapD_eq, mapE_eq, elt_coeff fptC, elt_coeff fG, elt_coeff fG,
    elt_coeff fT1, elt_coeff fT1, elt_coeff fQ, elt_coeff fQ, det_mapD, det_mapE]
  by_cases h : M.det = n
  · simp only [esIfPos h]; rw [ptC_16b M]; ring
  · simp only [esIfNeg h]; ring

/-! ### Property (B) at the level of operators on `V₁₀` -/

lemma actR_neg' (x : R) : actR (-x) = -actR x := by simp [actR]
lemma actR_sub' (x y : R) : actR (x - y) = actR x - actR y := by simp [actR]
lemma actR_smul' (r : ℚ) (x : R) : actR (r • x) = r • actR x := actR_smul r x

lemma rSS (v : V) : rAct S (rAct S v) = v := by
  rw [← LinearMap.comp_apply, ← rAct_mul, show S * S = -1 by decide, rAct_neg, rAct_one]; rfl
lemma rUU (v : V) : rAct U (rAct U v) = rAct U2 v := by
  rw [← LinearMap.comp_apply, ← rAct_mul, U_mul_U]
lemma rU2U (v : V) : rAct U2 (rAct U v) = v := by
  rw [← LinearMap.comp_apply, ← rAct_mul, show U * U2 = -1 by decide, rAct_neg, rAct_one]; rfl
lemma rUU2 (v : V) : rAct U (rAct U2 v) = v := by
  rw [← LinearMap.comp_apply, ← rAct_mul, show U2 * U = -1 by decide, rAct_neg, rAct_one]; rfl

/-- Property (B) as operator identities: `x(1+S)` acts as `(1+U+U²)y₁` and `x(1+U+U²)` as
`(1+S)y₂` (this is what PZ Prop. 3 uses). -/
def PropBact (x : R) : Prop :=
  (∃ y : R, actR (x * oneS) = actR (oneU * y)) ∧ (∃ y : R, actR (x * oneU) = actR (oneS * y))

/-- **Property (B) for `T̃ₙ`** (PZ Theorem 4(a)), via (16a) and (16b). -/
theorem propBact_Ttilde (n : ℕ) : PropBact (Ttilde n) := by
  constructor
  · refine ⟨-(elt n regF * oneS), ?_⟩
    rw [Ttilde_16a]
    apply LinearMap.ext; intro P
    simp only [oneS, oneU, actR_mul, actR_add, actR_sub', actR_neg', actR_of, actR_one,
      LinearMap.comp_apply, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.neg_apply,
      LinearMap.id_apply, rAct_neg, U_mul_U, map_add, map_sub, map_neg, rSS]
    abel
  · refine ⟨-(elt n regG * oneU), ?_⟩
    rw [Ttilde_16b]
    apply LinearMap.ext; intro P
    simp only [oneS, oneU, actR_mul, actR_add, actR_sub', actR_neg', actR_smul', actR_of,
      actR_one, LinearMap.comp_apply, LinearMap.add_apply, LinearMap.sub_apply,
      LinearMap.neg_apply, LinearMap.smul_apply, LinearMap.id_apply, rAct_neg, map_add, map_sub,
      map_neg, map_smul, rUU, rU2U]
    module

lemma mapsTo_A_B' {x : R} (hx : PropBact x) : ∀ P ∈ Aker, actR x P ∈ Bker := by
  intro P hP
  obtain ⟨y, hy⟩ := hx.2
  have h := congrArg (fun F : V →ₗ[ℚ] V => F P) hy
  simp only [actR_mul, LinearMap.comp_apply, actR_oneS, actR_oneU] at h
  show _ ∈ LinearMap.ker _
  rw [LinearMap.mem_ker, h]
  have : (LinearMap.id + rAct S : V →ₗ[ℚ] V) P = 0 := hP
  rw [this, map_zero]

lemma mapsTo_B_A' {x : R} (hx : PropBact x) : ∀ P ∈ Bker, actR x P ∈ Aker := by
  intro P hP
  obtain ⟨y, hy⟩ := hx.1
  have h := congrArg (fun F : V →ₗ[ℚ] V => F P) hy
  simp only [actR_mul, LinearMap.comp_apply, actR_oneS, actR_oneU] at h
  show _ ∈ LinearMap.ker _
  rw [LinearMap.mem_ker, h]
  have : (LinearMap.id + rAct U + rAct U2 : V →ₗ[ℚ] V) P = 0 := hP
  rw [this, map_zero]

/-- **PZ Prop. 3** for elements with operator-level property (B). -/
theorem trace_eq_trace_Wper' {x : R} (hx : PropBact x) :
    LinearMap.trace ℚ V (actR x) = LinearMap.trace ℚ Wper
      ((actR x).restrict (p := Wper) (q := Wper)
        (fun P hP => Submodule.mem_inf.2 ⟨mapsTo_B_A' hx P (Submodule.mem_inf.1 hP).2,
          mapsTo_A_B' hx P (Submodule.mem_inf.1 hP).1⟩)) :=
  trace_eq_trace_restrict_inf Aker Bker sup_eq_top (actR x) (mapsTo_A_B' hx) (mapsTo_B_A' hx)

/-- **`tr(T̃ₙ | W₁₀) = traceSum n`**: the trace of `T̃ₙ` on the period space `W₁₀`. -/
theorem trace_Wper_Ttilde (n : ℕ) :
    LinearMap.trace ℚ Wper ((actR (Ttilde n)).restrict (p := Wper) (q := Wper)
        (fun P hP => Submodule.mem_inf.2 ⟨mapsTo_B_A' (propBact_Ttilde n) P
          (Submodule.mem_inf.1 hP).2, mapsTo_A_B' (propBact_Ttilde n) P
          (Submodule.mem_inf.1 hP).1⟩)) = traceSum n := by
  rw [← trace_eq_trace_Wper' (propBact_Ttilde n), trace_Ttilde]

end RamanujanWeil.Arith.ES
