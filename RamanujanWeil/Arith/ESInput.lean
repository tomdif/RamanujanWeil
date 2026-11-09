import RamanujanWeil.Arith.ESEigen
import RamanujanWeil.Tau

/-!
# A2 / ES-P10–P12 interface: the one analytic input, and what the algebra extracts from it

**The analytic input** (`EichlerPeriodInput`, P10–P12 must construct an `EichlerData`):

* a complex vector space `E` (P10: functions `ℍ → ℂ`) with a right action `sl` of
  `M₂(ℤ)⁺/±1` (P10: the weight `−10` slash action `(f|M)(z) = (cz + d)¹⁰ f(Mz)`), `IsSlash sl`;
* an injective, equivariant `ι : ℂ¹¹ → E` (polynomials `P ↦ (z ↦ Σ_j P_j zʲ)`; equivariance for
  `det M > 0` is `P(az + b, cz + d) = (cz + d)¹⁰ P(Mz)`);
* `F ∈ E` with `F|T = F` and `F|T^∞ₙ = τ(n)·F` for `n ≥ 1` (P10: the Eichler integral
  `F̃ = Σ τ(m) m⁻¹¹ qᵐ`; `heckeSet n` is `{[[a,b],[0,d]] : ad = n, 0 ≤ b < d}`);
* `ρ ∈ ℂ¹¹` with `ι ρ = F|(1 − S)` (P11: Bol, `ρ` is a polynomial);
* `conj ρ_j = (−1)ʲ ρ_j` (P11/P12: from `F̃(−z̄) = conj F̃(z)`, `τ` real) and
  `ρ₈ ≠ 0`, `ρ₉ ≠ 0` (P12: certified numerics, `ρ ≈ −0.989 e0 + 18.99 p⁺ + 6.156 i p⁻`).

**Consumed here** (no further analysis):
* `EichlerData.tauEigenPeriod` : the data give `ρ ∈ W₁₀ ⊗ ℂ` with `ρ|T̃ₙ = τ(n)ρ` for all
  `n ≥ 1` (property (A), `propA_action`, and the group-ring identity
  `(1 − S)(1 + U + U²) ≡ (1 − T⁻¹)(1 + ST⁻¹) + (T − 1)S`);
* `TauEigenPeriod.diag` : `(p⁺|T̃ₙ)₈ = τ(n)` and `(p⁻|T̃ₙ)₉ = τ(n)` (complex conjugation separates
  the even and odd parts of `ρ`);
* `traceSum_eq_sig_tau` : `traceSum n = σ₁₁(n) + 2τ(n)`.
-/

open Finset Module
open scoped Matrix

namespace RamanujanWeil.Arith.ES

open M2

/-- The action matrix of `M` with complex entries. -/
noncomputable def cmat (M : M2) : Matrix (Fin 11) (Fin 11) ℂ := (act M).map (Rat.castHom ℂ)

/-- `T̃ₙ` acting on `ℂ¹¹` (row vectors): `ρ ↦ Σ_M c_M · ρ|M`. -/
noncomputable def heckeC (n : ℕ) : (Fin 11 → ℂ) →ₗ[ℂ] (Fin 11 → ℂ) :=
  ∑ N ∈ boxM n, (ptCd n N : ℂ) • Matrix.vecMulLinear (cmat N)

/-- **The algebraic shadow of the analytic input**: a complex period polynomial `ρ ∈ W₁₀ ⊗ ℂ`
which is a `τ(n)`-eigenvector of every `T̃ₙ`, has the conjugation symmetry of a real cusp form,
and has nonzero `p⁺`- and `p⁻`-coordinates. -/
def TauEigenPeriod : Prop :=
  ∃ ρ : Fin 11 → ℂ,
    ρ + ρ ᵥ* cmat S = 0 ∧ ρ + ρ ᵥ* cmat U + ρ ᵥ* cmat U2 = 0 ∧
    (∀ n : ℕ, 1 ≤ n → heckeC n ρ = (RamanujanTau.tau n : ℂ) • ρ) ∧
    (∀ j : Fin 11, starRingEnd ℂ (ρ j) = (-1) ^ (j : ℕ) * ρ j) ∧ ρ 8 ≠ 0 ∧ ρ 9 ≠ 0

/-- **The analytic input** (to be constructed by P10–P12): the Eichler integral of `Δ` in a
module with a weight `−10` slash action, and its period polynomial. -/
structure EichlerData where
  /-- The function space (P10: functions `ℍ → ℂ`). -/
  E : Type
  [instG : AddCommGroup E]
  [instM : Module ℂ E]
  /-- The slash action. -/
  sl : M2 → E →ₗ[ℂ] E
  isSlash : IsSlash sl
  /-- Polynomials as functions. -/
  ι : (Fin 11 → ℂ) →ₗ[ℂ] E
  ι_inj : Function.Injective ι
  ι_equiv : ∀ M : M2, 0 < M.det → ∀ P : Fin 11 → ℂ, ι (P ᵥ* cmat M) = sl M (ι P)
  /-- The Eichler integral `F̃ = Σ τ(m) m⁻¹¹ qᵐ`. -/
  F : E
  F_T : sl T F = F
  F_hecke : ∀ n : ℕ, 1 ≤ n → ∑ N ∈ heckeSet n, sl N F = (RamanujanTau.tau n : ℂ) • F
  /-- The period polynomial `ρ = F̃|(1 − S)`. -/
  ρ : Fin 11 → ℂ
  ρ_eq : ι ρ = F - sl S F
  ρ_conj : ∀ j : Fin 11, starRingEnd ℂ (ρ j) = (-1) ^ (j : ℕ) * ρ j
  ρ_8 : ρ 8 ≠ 0
  ρ_9 : ρ 9 ≠ 0

attribute [instance] EichlerData.instG EichlerData.instM

/-- **The single analytic input of A2** (Eichler integral + Bol + certified nonvanishing). -/
def EichlerPeriodInput : Prop := Nonempty EichlerData

/-! ### From the analytic data to `TauEigenPeriod` -/

lemma heckeC_apply (n : ℕ) (ρ : Fin 11 → ℂ) :
    heckeC n ρ = ∑ N ∈ boxM n, (ptCd n N : ℂ) • (ρ ᵥ* cmat N) := by
  simp [heckeC, LinearMap.sum_apply]

namespace EichlerData

variable (D : EichlerData)

lemma sl_mul_apply {M N : M2} (hM : 0 < M.det) (hN : 0 < N.det) (v : D.E) :
    D.sl (M * N) v = D.sl N (D.sl M v) := D.isSlash.mul_apply hM hN v

lemma ι_ρ_hecke {n : ℕ} (hn : 1 ≤ n) :
    D.ι (heckeC n D.ρ) = (RamanujanTau.tau n : ℂ) • D.ι D.ρ := by
  have hn' : (0 : ℤ) < n := by omega
  rw [heckeC_apply, map_sum]
  have e : ∀ N ∈ boxM n, D.ι ((ptCd n N : ℂ) • (D.ρ ᵥ* cmat N)) =
      (ptCd n N : ℂ) • D.sl N (D.F - D.sl S D.F) := by
    intro N _
    rw [map_smul]
    unfold ptCd
    split_ifs with hd
    · rw [D.ι_equiv N (by rw [hd]; exact hn'), D.ρ_eq]
    · simp
  rw [Finset.sum_congr rfl e, propA_action D.isSlash D.F_T hn, Finset.sum_sub_distrib,
    ← map_sum, D.F_hecke n hn, D.ρ_eq, map_smul, smul_sub]

lemma ρ_hecke {n : ℕ} (hn : 1 ≤ n) : heckeC n D.ρ = (RamanujanTau.tau n : ℂ) • D.ρ :=
  D.ι_inj (by rw [D.ι_ρ_hecke hn, map_smul])

lemma ρ_S : D.ρ + D.ρ ᵥ* cmat S = 0 := by
  apply D.ι_inj
  rw [map_add, D.ι_equiv S (by decide), D.ρ_eq, map_zero, map_sub,
    ← D.sl_mul_apply (by decide) (by decide), show S * S = -1 by decide, D.isSlash.negOne]
  simp

lemma ρ_U : D.ρ + D.ρ ᵥ* cmat U + D.ρ ᵥ* cmat U2 = 0 := by
  apply D.ι_inj
  have hF1 : D.sl (Pk (-1)) D.F = D.F := D.isSlash.Pk_fix D.F_T (-1)
  rw [map_add, map_add, D.ι_equiv U (by decide), D.ι_equiv U2 (by decide), D.ρ_eq, map_zero,
    map_sub, map_sub, ← D.sl_mul_apply (by decide) (by decide),
    ← D.sl_mul_apply (M := S) (by decide) (by decide)]
  -- `U = TS`, `U² = T(STS)`, `SU = STS`, `SU² = −T⁻¹`
  have e1 : D.sl U D.F = D.sl S D.F := by
    rw [show U = T * S by decide, D.sl_mul_apply (by decide) (by decide), D.F_T]
  have e2 : D.sl U2 D.F = D.sl (S * T * S) D.F := by
    rw [show U2 = T * (S * T * S) by decide, D.sl_mul_apply (by decide) (by decide), D.F_T]
  have e3 : D.sl (S * U) D.F = D.sl (S * T * S) D.F := by rw [show S * U = S * T * S by decide]
  have e4 : D.sl (S * U2) D.F = D.F := by
    rw [show S * U2 = -Pk (-1) by decide, D.isSlash.neg_apply (by decide), hF1]
  rw [e1, e2, e3, e4]
  abel

/-- The analytic data give the algebraic eigen-period. -/
theorem tauEigenPeriod (D : EichlerData) : TauEigenPeriod :=
  ⟨D.ρ, D.ρ_S, D.ρ_U, fun _ hn => D.ρ_hecke hn, D.ρ_conj, D.ρ_8, D.ρ_9⟩

end EichlerData

theorem tauEigenPeriod_of_input (h : EichlerPeriodInput) : TauEigenPeriod :=
  EichlerData.tauEigenPeriod h.some

/-! ### From `TauEigenPeriod` to the diagonal of `T̃ₙ` on `W₁₀` -/

lemma dual_smul_cast (φ : Module.Dual ℚ ℂ) (z : ℂ) (q : ℚ) : φ (z * (q : ℂ)) = φ z * q := by
  rw [mul_comm, ← Rat.smul_def, map_smul, smul_eq_mul, mul_comm]

lemma dual_vecMul (φ : Module.Dual ℚ ℂ) (ρ : Fin 11 → ℂ) (M : M2) (i : Fin 11) :
    φ ((ρ ᵥ* cmat M) i) = ((fun k => φ (ρ k)) ᵥ* act M) i := by
  simp only [Matrix.vecMul, dotProduct, cmat, Matrix.map_apply, Rat.coe_castHom, map_sum,
    dual_smul_cast]

/-- A complex period polynomial is `ρ₁₀ e0 + ρ₈ p⁺ + ρ₉ p⁻` (rational structure of `W₁₀`,
transported to `ℂ` through `ℚ`-linear functionals). -/
lemma W_decomp {ρ : Fin 11 → ℂ} (hS : ρ + ρ ᵥ* cmat S = 0)
    (hU : ρ + ρ ᵥ* cmat U + ρ ᵥ* cmat U2 = 0) (j : Fin 11) :
    ρ j = ρ 10 * (e0 j : ℂ) + ρ 8 * (pplus j : ℂ) + ρ 9 * (pminus j : ℂ) := by
  rw [← sub_eq_zero]
  refine (Module.forall_dual_apply_eq_zero_iff ℚ _).mp fun φ => ?_
  set P : V := fun k => φ (ρ k) with hPdef
  have hP : P ∈ Wper := by
    refine ⟨?_, ?_⟩
    · show (LinearMap.id + rAct S : V →ₗ[ℚ] V) P = 0
      funext i
      have := congrArg (fun v => φ (v i)) hS
      simp only [Pi.add_apply, Pi.zero_apply, map_add, map_zero, dual_vecMul] at this
      simpa [rAct_apply] using this
    · show (LinearMap.id + rAct U + rAct U2 : V →ₗ[ℚ] V) P = 0
      funext i
      have := congrArg (fun v => φ (v i)) hU
      simp only [Pi.add_apply, Pi.zero_apply, map_add, map_zero, dual_vecMul] at this
      simpa [rAct_apply] using this
  have h := congrFun (eq_of_mem_Wper hP) j
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hPdef] at h
  rw [map_sub, map_add, map_add, dual_smul_cast, dual_smul_cast, dual_smul_cast, h]
  ring

lemma heckeC_cast (n : ℕ) (P : V) :
    heckeC n (fun i => (P i : ℂ)) = fun i => ((actR (Ttilde n) P i : ℚ) : ℂ) := by
  funext i
  rw [heckeC_apply, actR_Ttilde_apply, Finset.sum_apply, Finset.sum_apply, Rat.cast_sum]
  refine Finset.sum_congr rfl fun N _ => ?_
  simp only [Pi.smul_apply, smul_eq_mul, Rat.cast_mul, rAct_apply]
  congr 1
  have := RingHom.map_vecMul (Rat.castHom ℂ) (act N) P i
  simp only [Rat.coe_castHom] at this
  rw [this]; rfl

lemma conj_eq_of_parity {ρ : Fin 11 → ℂ}
    (h : ∀ j : Fin 11, starRingEnd ℂ (ρ j) = (-1) ^ (j : ℕ) * ρ j) :
    starRingEnd ℂ (ρ 10) = ρ 10 ∧ starRingEnd ℂ (ρ 8) = ρ 8 ∧ starRingEnd ℂ (ρ 9) = -ρ 9 := by
  refine ⟨?_, ?_, ?_⟩
  · have := h 10; norm_num at this; exact this
  · have := h 8; norm_num at this; exact this
  · have := h 9; norm_num at this; exact this

/-- **The cuspidal diagonal**: `(p⁺|T̃ₙ)₈ = τ(n)` and `(p⁻|T̃ₙ)₉ = τ(n)`. -/
theorem TauEigenPeriod.diag (h : TauEigenPeriod) {n : ℕ} (hn : 1 ≤ n) :
    actR (Ttilde n) pplus 8 = RamanujanTau.tau n ∧ actR (Ttilde n) pminus 9 = RamanujanTau.tau n := by
  obtain ⟨ρ, hS, hU, hH, hconj, h8, h9⟩ := h
  obtain ⟨c10, c8, c9⟩ := conj_eq_of_parity hconj
  set α := ρ 10
  set β := ρ 8
  set γ := ρ 9
  have hρ : ρ = α • (fun i => (e0 i : ℂ)) + β • (fun i => (pplus i : ℂ)) +
      γ • (fun i => (pminus i : ℂ)) := by
    funext j; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; exact W_decomp hS hU j
  have hE := actR_Ttilde_e0 hn
  have key := hH n hn
  rw [hρ, map_add, map_add, map_smul, map_smul, map_smul, heckeC_cast, heckeC_cast, heckeC_cast,
    hE] at key
  have k8 := congrFun key 8
  have k9 := congrFun key 9
  have l1 : e0 8 = 0 := rfl
  have l2 : e0 9 = 0 := rfl
  have l3 : pplus 8 = 1 := rfl
  have l4 : pplus 9 = 0 := rfl
  have l5 : pminus 8 = 0 := rfl
  have l6 : pminus 9 = 1 := rfl
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, l1, l2, l3, l4, l5, l6, mul_zero,
    Rat.cast_zero, Rat.cast_one, mul_one, zero_add, add_zero] at k8 k9
  set P8 := actR (Ttilde n) pplus 8
  set Q8 := actR (Ttilde n) pminus 8
  set P9 := actR (Ttilde n) pplus 9
  set Q9 := actR (Ttilde n) pminus 9
  have k8c := congrArg (starRingEnd ℂ) k8
  have k9c := congrArg (starRingEnd ℂ) k9
  simp only [map_add, map_mul, map_ratCast, map_intCast, c8, c9] at k8c k9c
  constructor
  · have hb : β * ((P8 : ℂ) - RamanujanTau.tau n) = 0 := by linear_combination (k8 + k8c) / 2
    have := (mul_eq_zero.mp hb).resolve_left h8
    exact_mod_cast sub_eq_zero.mp this
  · have hg : γ * ((Q9 : ℂ) - RamanujanTau.tau n) = 0 := by linear_combination (k9 - k9c) / 2
    have := (mul_eq_zero.mp hg).resolve_left h9
    exact_mod_cast sub_eq_zero.mp this

/-- **`tr(T̃ₙ | W₁₀) = σ₁₁(n) + 2τ(n)`**, given the eigen-period. -/
lemma e0_10 : e0 10 = 1 := rfl

theorem traceSum_eq_sig_tau (h : TauEigenPeriod) {n : ℕ} (hn : 1 ≤ n) :
    traceSum n = sig11 n + 2 * RamanujanTau.tau n := by
  obtain ⟨h8, h9⟩ := h.diag hn
  rw [traceSum_eq_coords, h8, h9, actR_Ttilde_e0 hn, Pi.smul_apply, smul_eq_mul, e0_10]
  ring

end RamanujanWeil.Arith.ES
