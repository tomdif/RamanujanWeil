import RamanujanWeil.Arith.ESAnalyticNum
import RamanujanWeil.Arith.ESMain

/-!
# A2 / ES-P10–P12 assembled: `EichlerPeriodInput` holds, hence Eichler–Selberg at prime powers

* `rhoV_S`, `rhoV_U` : `ρ ∈ W₁₀ ⊗ ℂ` (as in `EichlerData.ρ_S/ρ_U`);
* `R_eq` : `f(y) + y¹⁰f(1/y) = Re ρ₁₀·(−1 − y¹⁰) + Re ρ₈·(y² + 3y⁴ + 3y⁶ + y⁸) − Im ρ₉·Q(y)`;
* `rho8_re_gt`, `rho9_im_gt` : `Re ρ₈ > 1`, `Im ρ₉ > 1` (three evaluations, `y = 1, 2, 3/2`);
* **`eichlerData`**, **`eichlerPeriodInput : EichlerPeriodInput`**;
* **`eichlerSelberg_all`** : `∀ p [Fact p.Prime], EichlerSelbergPrimePow hurwitz p`.
-/

set_option autoImplicit false

namespace RamanujanWeil.Arith.ES.Analytic

open Complex Filter Set Finset RamanujanTau
open RamanujanWeil.Arith.ES RamanujanWeil.Arith.ES.M2
open scoped Real Topology Matrix

/-! ### `ρ ∈ W₁₀ ⊗ ℂ` -/

lemma sl_mul_apply' {M N : M2} (hM : 0 < M.det) (hN : 0 < N.det) (v : EH) :
    sl (M * N) v = sl N (sl M v) := isSlash_sl.mul_apply hM hN v

lemma rhoV_S : rhoV + rhoV ᵥ* cmat S = 0 := by
  apply ιH_inj
  rw [map_add, ιH_equiv S (by decide), ιH_rho, map_zero, map_sub,
    ← sl_mul_apply' (by decide) (by decide), show S * S = -1 by decide, isSlash_sl.negOne]
  simp

lemma rhoV_U : rhoV + rhoV ᵥ* cmat U + rhoV ᵥ* cmat U2 = 0 := by
  apply ιH_inj
  have hF1 : sl (Pk (-1)) Fh = Fh := isSlash_sl.Pk_fix Fh_T (-1)
  rw [map_add, map_add, ιH_equiv U (by decide), ιH_equiv U2 (by decide), ιH_rho, map_zero,
    map_sub, map_sub, ← sl_mul_apply' (by decide) (by decide),
    ← sl_mul_apply' (M := S) (by decide) (by decide)]
  have e1 : sl U Fh = sl S Fh := by
    rw [show U = T * S by decide, sl_mul_apply' (by decide) (by decide), Fh_T]
  have e2 : sl U2 Fh = sl (S * T * S) Fh := by
    rw [show U2 = T * (S * T * S) by decide, sl_mul_apply' (by decide) (by decide), Fh_T]
  have e3 : sl (S * U) Fh = sl (S * T * S) Fh := by rw [show S * U = S * T * S by decide]
  have e4 : sl (S * U2) Fh = Fh := by
    rw [show S * U2 = -Pk (-1) by decide, isSlash_sl.neg_apply (by decide), hF1]
  rw [e1, e2, e3, e4]
  abel

lemma rhoV_decomp (j : Fin 11) :
    rhoV j = rhoV 10 * (e0 j : ℂ) + rhoV 8 * (pplus j : ℂ) + rhoV 9 * (pminus j : ℂ) :=
  W_decomp rhoV_S rhoV_U j

/-! ### `ρ` on the imaginary axis -/

lemma evP_W (a b c z : ℂ) :
    ∑ j : Fin 11, (a * (e0 j : ℂ) + b * (pplus j : ℂ) + c * (pminus j : ℂ)) * z ^ (j : ℕ) =
      a * (z ^ 10 - 1) + b * (-z ^ 2 + 3 * z ^ 4 - 3 * z ^ 6 + z ^ 8) +
      c * (z - 25 / 4 * z ^ 3 + 21 / 2 * z ^ 5 - 25 / 4 * z ^ 7 + z ^ 9) := by
  simp [Fin.sum_univ_succ, e0, pplus, pminus]
  ring

lemma evP_decomp (z : ℂ) :
    evP rhoV z = rhoV 10 * (z ^ 10 - 1) + rhoV 8 * (-z ^ 2 + 3 * z ^ 4 - 3 * z ^ 6 + z ^ 8) +
      rhoV 9 * (z - 25 / 4 * z ^ 3 + 21 / 2 * z ^ 5 - 25 / 4 * z ^ 7 + z ^ 9) := by
  rw [← evP_W]
  exact Finset.sum_congr rfl fun j _ => by rw [← rhoV_decomp j]

lemma evP_I_mul (y : ℝ) :
    evP rhoV (I * y) = rhoV 10 * ((-1 - y ^ 10 : ℝ) : ℂ) +
      rhoV 8 * ((y ^ 2 + 3 * y ^ 4 + 3 * y ^ 6 + y ^ 8 : ℝ) : ℂ) +
      rhoV 9 * I * ((y + 25 / 4 * y ^ 3 + 21 / 2 * y ^ 5 + 25 / 4 * y ^ 7 + y ^ 9 : ℝ) : ℂ) := by
  rw [evP_decomp]
  have h2 : I ^ 2 = -1 := I_sq
  have h3 : I ^ 3 = -I := by rw [pow_succ, h2]; ring
  have h4 : I ^ 4 = 1 := by rw [pow_succ, h3]; ring_nf; rw [h2]; ring
  have h5 : I ^ 5 = I := by rw [pow_succ, h4]; ring
  have h6 : I ^ 6 = -1 := by rw [pow_succ, h5, ← sq, h2]
  have h7 : I ^ 7 = -I := by rw [pow_succ, h6]; ring
  have h8 : I ^ 8 = 1 := by rw [pow_succ, h7]; ring_nf; rw [h2]; ring
  have h9 : I ^ 9 = I := by rw [pow_succ, h8]; ring
  have h10 : I ^ 10 = -1 := by rw [pow_succ, h9, ← sq, h2]
  simp only [mul_pow, h2, h3, h4, h5, h6, h7, h8, h9, h10]
  push_cast
  ring

lemma rhoc_I_mul {y : ℝ} (hy : 0 < y) :
    rhoc (I * y) = ((fr y + y ^ 10 * fr (1 / y) : ℝ) : ℂ) := by
  have hy0 : (y : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
  have e1 : -1 / (I * y) = I * ((1 / y : ℝ) : ℂ) := by
    rw [div_eq_iff (mul_ne_zero I_ne_zero hy0)]
    push_cast
    field_simp
    rw [I_sq]
  have e2 : (I * y) ^ 10 = -((y ^ 10 : ℝ) : ℂ) := by
    rw [mul_pow, show I ^ 10 = (I ^ 2) ^ 5 by ring, I_sq]; push_cast; ring
  rw [rhoc, e1, e2, Fc_I_mul, Fc_I_mul]
  push_cast; ring

/-- **The real identity on the imaginary axis.** -/
theorem R_eq {y : ℝ} (hy : 0 < y) :
    fr y + y ^ 10 * fr (1 / y) = (rhoV 10).re * (-1 - y ^ 10) +
      (rhoV 8).re * (y ^ 2 + 3 * y ^ 4 + 3 * y ^ 6 + y ^ 8) -
      (rhoV 9).im * (y + 25 / 4 * y ^ 3 + 21 / 2 * y ^ 5 + 25 / 4 * y ^ 7 + y ^ 9) := by
  have hmem : I * (y : ℂ) ∈ Hs := by show 0 < (I * (y : ℂ)).im; simpa using hy
  have h := evP_rhoV hmem
  rw [evP_I_mul, rhoc_I_mul hy] at h
  have h' := congrArg Complex.re h
  simp only [add_re, mul_re, ofReal_re, ofReal_im, mul_zero, sub_zero, I_re, I_im, mul_one,
    mul_im] at h'
  linarith

/-! ### Interval bounds for `f` -/

lemma exp_eq_u (y : ℝ) (k : ℕ) (h : 2 * y = (k : ℝ) / 3) :
    Real.exp (-2 * π * y) = Real.exp (-(π / 3)) ^ k := by
  rw [← Real.exp_nat_mul]; congr 1
  have : -2 * π * y = -(π * (2 * y)) := by ring
  rw [this, h]; ring

lemma fr_interval (y : ℝ) (k : ℕ) (hk : 3 ≤ k) (h : 2 * y = (k : ℝ) / 3) :
    (0.35 : ℝ) ^ k - (0.352 : ℝ) ^ (2 * k) / 5 ≤ fr y ∧
      fr y ≤ (0.352 : ℝ) ^ k + (0.352 : ℝ) ^ (2 * k) / 5 := by
  obtain ⟨hu1, hu2⟩ := u_bounds
  set u := Real.exp (-(π / 3))
  have hv1 : (0.35 : ℝ) ^ k ≤ u ^ k := pow_le_pow_left₀ (by norm_num) hu1 k
  have hv2 : u ^ k ≤ (0.352 : ℝ) ^ k := pow_le_pow_left₀ (by linarith) hu2 k
  have hv0 : 0 ≤ u ^ k := pow_nonneg (Real.exp_pos _).le k
  have hsmall : (0.352 : ℝ) ^ k ≤ 1 / 20 := by
    calc (0.352 : ℝ) ^ k ≤ 0.352 ^ 3 := pow_le_pow_of_le_one (by norm_num) (by norm_num) hk
      _ ≤ 1 / 20 := by norm_num
  have hb := fr_bound y (by rw [exp_eq_u y k h]; linarith)
  rw [exp_eq_u y k h] at hb
  have hsq : (u ^ k) ^ 2 ≤ (0.352 : ℝ) ^ (2 * k) := by
    rw [pow_mul']; exact pow_le_pow_left₀ hv0 hv2 2
  rw [abs_le] at hb
  constructor <;> linarith

/-! ### Certified nonvanishing -/

theorem rho_bounds : 1 < (rhoV 8).re ∧ 1 < (rhoV 9).im := by
  have r1 := R_eq (y := 1) (by norm_num)
  have r2 := R_eq (y := 2) (by norm_num)
  have r3 := R_eq (y := 3 / 2) (by norm_num)
  norm_num at r1 r2 r3
  obtain ⟨a1, b1⟩ := fr_interval 1 6 (by norm_num) (by norm_num)
  obtain ⟨a2, b2⟩ := fr_interval 2 12 (by norm_num) (by norm_num)
  obtain ⟨ah, bh⟩ := fr_interval (1 / 2) 3 (by norm_num) (by norm_num)
  obtain ⟨a32, b32⟩ := fr_interval (3 / 2) 9 (by norm_num) (by norm_num)
  obtain ⟨a23, b23⟩ := fr_interval (2 / 3) 4 (by norm_num) (by norm_num)
  norm_num at a1 b1 a2 b2 ah bh a32 b32 a23 b23
  constructor <;> linarith

theorem rhoV_8_ne : rhoV 8 ≠ 0 := by
  intro h; have := rho_bounds.1; rw [h] at this; simp at this; linarith

theorem rhoV_9_ne : rhoV 9 ≠ 0 := by
  intro h; have := rho_bounds.2; rw [h] at this; simp at this; linarith

/-! ### The analytic input -/

/-- **The Eichler data of `Δ`.** -/
noncomputable def eichlerData : EichlerData where
  E := EH
  sl := sl
  isSlash := isSlash_sl
  ι := ιH
  ι_inj := ιH_inj
  ι_equiv := ιH_equiv
  F := Fh
  F_T := Fh_T
  F_hecke := Fh_hecke
  ρ := rhoV
  ρ_eq := ιH_rho
  ρ_conj := rho_conj
  ρ_8 := rhoV_8_ne
  ρ_9 := rhoV_9_ne

/-- **P10–P12: the analytic input of A2 holds.** -/
theorem eichlerPeriodInput : EichlerPeriodInput := ⟨eichlerData⟩

/-- **A2 (Eichler–Selberg at prime powers), unconditionally.** -/
theorem eichlerSelberg_all :
    ∀ (p : ℕ) [Fact p.Prime], RamanujanWeil.ArithPlan.EichlerSelbergPrimePow Hurwitz.hurwitz p :=
  eichlerSelberg_all_of_input eichlerPeriodInput

end RamanujanWeil.Arith.ES.Analytic
