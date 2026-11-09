import RamanujanWeil.Arith.ESAnalyticTau
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# A2 / ES-P10: the Eichler integral `F̃ = Σ τ(m) m⁻¹¹ qᵐ` as a function on `ℂ`

* `G c z = Σ' m, c m · e^{2πimz}`; for coefficients with `Bd c` (`Σ ‖c m‖ xᵐ < ∞` for `x < 1`)
  it converges on `Im z > 0` and differentiates termwise (`hasDerivAt_G`).
* `cj j m = (2πim)ʲ τ(m)/m¹¹`; `Fc = G (cj 0)` is the Eichler integral and
  `iteratedDeriv j Fc = G (cj j)` on `ℍ` for `j ≤ 11` (`iteratedDeriv_Fc`);
  `G (cj 11) = (2πi)¹¹ Δ` (`G_cj11`), with `Δ(−1/z) = z¹²Δ(z)` (`Dc_S`).
* `Fc (z + 1) = Fc z`, `conj (Fc z) = Fc (−conj z)`.
-/

set_option autoImplicit false

namespace RamanujanWeil.Arith.ES.Analytic

open Complex Filter Set RamanujanTau RamanujanWeil.ArithPlan
open scoped Real Topology

/-- the open upper half plane as a subset of `ℂ`. -/
def Hs : Set ℂ := {z : ℂ | 0 < z.im}

lemma isOpen_Hs : IsOpen Hs := isOpen_lt continuous_const Complex.continuous_im

/-- `e^{2πimz}`. -/
noncomputable def qe (z : ℂ) (m : ℕ) : ℂ := cexp (2 * π * I * m * z)

lemma norm_qe (z : ℂ) (m : ℕ) : ‖qe z m‖ = Real.exp (-2 * π * z.im) ^ m := by
  rw [qe, Complex.norm_exp, ← Real.exp_nat_mul]
  congr 1
  simp [mul_re, mul_im]
  ring

lemma qe_add_one (z : ℂ) (m : ℕ) : qe (z + 1) m = qe z m := by
  rw [qe, qe, show 2 * π * I * m * (z + 1) = 2 * π * I * m * z + m * (2 * π * I) by ring,
    Complex.exp_add, Complex.exp_nat_mul_two_pi_mul_I, mul_one]

lemma conj_qe (z : ℂ) (m : ℕ) : (starRingEnd ℂ) (qe z m) = qe (-(starRingEnd ℂ) z) m := by
  rw [qe, qe, ← Complex.exp_conj]
  congr 1
  simp only [map_mul, map_ofNat, Complex.conj_ofReal, Complex.conj_I, map_natCast]
  ring

/-- the q-series with coefficients `c`. -/
noncomputable def G (c : ℕ → ℂ) (z : ℂ) : ℂ := ∑' m, c m * qe z m

/-- coefficients of at most sub-exponential growth. -/
def Bd (c : ℕ → ℂ) : Prop := ∀ x : ℝ, 0 ≤ x → x < 1 → Summable fun m => ‖c m‖ * x ^ m

lemma bd_tau : Bd fun m => (tau m : ℂ) := by
  intro x hx0 hx1
  obtain ⟨r, hr⟩ : ∃ r : ℝ, r = (x + 1) / 2 := ⟨_, rfl⟩
  have hr0 : 0 < r := by rw [hr]; linarith
  have hr1 : r < 1 := by rw [hr]; linarith
  have hxr : x / r < 1 := (div_lt_one hr0).mpr (by rw [hr]; linarith)
  have hg : Summable fun m : ℕ => (r * Real.exp (24 * (r / (1 - r)))) * (x / r) ^ m :=
    (summable_geometric_of_lt_one (div_nonneg hx0 hr0.le) hxr).mul_left _
  refine hg.of_nonneg_of_le (fun m => by positivity) fun m => ?_
  have h := tau_abs_mul_pow_le hr0.le hr1 m
  rw [Complex.norm_intCast]
  calc |(tau m : ℝ)| * x ^ m = (|(tau m : ℝ)| * r ^ m) * (x / r) ^ m := by
        rw [div_pow]; field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_right h (by positivity)

lemma Bd.mono {c c' : ℕ → ℂ} {K : ℝ} (_hK : 0 ≤ K) (h : ∀ m, ‖c' m‖ ≤ K * ‖c m‖) (hc : Bd c) :
    Bd c' := fun x hx0 hx1 =>
  ((hc x hx0 hx1).mul_left K).of_nonneg_of_le (fun _ => by positivity) fun m => by
    rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right (h m) (pow_nonneg hx0 m)

lemma exp_neg_lt_one {y : ℝ} (hy : 0 < y) : Real.exp (-2 * π * y) < 1 := by
  rw [Real.exp_lt_one_iff]; have := Real.pi_pos; nlinarith

lemma summable_G {c : ℕ → ℂ} (hc : Bd c) {z : ℂ} (hz : 0 < z.im) :
    Summable fun m => c m * qe z m := by
  refine Summable.of_norm_bounded (hc _ (Real.exp_pos _).le (exp_neg_lt_one hz)) fun m => ?_
  rw [norm_mul, norm_qe]

lemma hasSum_G {c : ℕ → ℂ} (hc : Bd c) {z : ℂ} (hz : 0 < z.im) :
    HasSum (fun m => c m * qe z m) (G c z) := (summable_G hc hz).hasSum

lemma hasDerivAt_qe_term (a : ℂ) (m : ℕ) (w : ℂ) :
    HasDerivAt (fun w => a * qe w m) ((2 * π * I * m * a) * qe w m) w := by
  have h1 : HasDerivAt (fun w : ℂ => 2 * π * I * m * w) (2 * π * I * m) w := by
    simpa using (hasDerivAt_id w).const_mul (2 * π * I * (m : ℂ))
  have := (h1.cexp).const_mul a
  have e : (2 * π * I * m * a) * qe w m = a * (cexp (2 * π * I * m * w) * (2 * π * I * m)) := by
    unfold qe; ring
  rw [e]; exact this

/-- **Termwise differentiation**. -/
theorem hasDerivAt_G {c : ℕ → ℂ} (hc : Bd c) (hc' : Bd fun m => 2 * π * I * m * c m) {z : ℂ}
    (hz : 0 < z.im) : HasDerivAt (G c) (G (fun m => 2 * π * I * m * c m) z) z := by
  set y0 := z.im / 2
  have hy0 : 0 < y0 := by positivity
  set t : Set ℂ := {w : ℂ | y0 < w.im}
  have ht : IsOpen t := isOpen_lt continuous_const Complex.continuous_im
  have ht' : IsPreconnected t := (convex_halfSpace_im_gt y0).isPreconnected
  have hzt : z ∈ t := by show y0 < z.im; simp only [y0]; linarith
  set x0 := Real.exp (-2 * π * y0)
  have hx0 : 0 ≤ x0 := (Real.exp_pos _).le
  have hx1 : x0 < 1 := exp_neg_lt_one hy0
  refine hasDerivAt_tsum_of_isPreconnected (u := fun m => ‖2 * π * I * m * c m‖ * x0 ^ m)
    (g := fun m w => c m * qe w m) (g' := fun m w => (2 * π * I * m * c m) * qe w m)
    (hc' x0 hx0 hx1) ht ht' (fun m w _ => hasDerivAt_qe_term (c m) m w) ?_ hzt
    (summable_G hc hz) hzt
  intro m w hw
  rw [norm_mul, norm_qe]
  refine mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Real.exp_pos _).le ?_ m) (norm_nonneg _)
  rw [Real.exp_le_exp]
  have := Real.pi_pos
  have hw' : y0 < w.im := hw
  nlinarith

/-! ### The coefficients `cj j m = (2πim)ʲ τ(m)/m¹¹` -/

/-- `(2πim)ʲ τ(m) / m¹¹`. -/
noncomputable def cj (j m : ℕ) : ℂ := (2 * π * I * m) ^ j * (tau m : ℂ) / (m : ℂ) ^ 11

lemma cj_succ (j m : ℕ) : cj (j + 1) m = 2 * π * I * m * cj j m := by
  unfold cj; ring

lemma two_pi_ge_one : (1 : ℝ) ≤ 2 * π := by have := Real.pi_gt_three; linarith

lemma norm_cj_le {j : ℕ} (hj : j ≤ 11) (m : ℕ) : ‖cj j m‖ ≤ (2 * π) ^ 11 * ‖(tau m : ℂ)‖ := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp [cj, tau_zero]
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hn : ‖cj j m‖ = (2 * π) ^ j * (m : ℝ) ^ j * ‖(tau m : ℂ)‖ / (m : ℝ) ^ 11 := by
    simp only [cj, norm_div, norm_mul, norm_pow, Complex.norm_natCast, Complex.norm_I,
      Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    ring
  rw [hn, div_le_iff₀ (by positivity)]
  have h1 : (2 * π) ^ j ≤ (2 * π) ^ 11 := pow_le_pow_right₀ two_pi_ge_one hj
  have h2 : (m : ℝ) ^ j ≤ (m : ℝ) ^ 11 := pow_le_pow_right₀ hm1 hj
  have h3 : 0 ≤ ‖(tau m : ℂ)‖ := norm_nonneg _
  calc (2 * π) ^ j * (m : ℝ) ^ j * ‖(tau m : ℂ)‖ ≤ (2 * π) ^ 11 * (m : ℝ) ^ 11 * ‖(tau m : ℂ)‖ := by
        gcongr
    _ = _ := by ring

lemma bd_cj {j : ℕ} (hj : j ≤ 11) : Bd (cj j) := bd_tau.mono (by positivity) (norm_cj_le hj)

/-- **The Eichler integral** `F̃(z) = Σ τ(m) m⁻¹¹ e^{2πimz}` (on `ℂ`; meaningful on `ℍ`). -/
noncomputable def Fc : ℂ → ℂ := G (cj 0)

lemma hasDerivAt_cj {j : ℕ} (hj : j < 11) {z : ℂ} (hz : 0 < z.im) :
    HasDerivAt (G (cj j)) (G (cj (j + 1)) z) z := by
  have e : cj (j + 1) = fun m => 2 * π * I * m * cj j m := funext (cj_succ j)
  rw [e]
  exact hasDerivAt_G (bd_cj hj.le) (e ▸ bd_cj (by omega)) hz

lemma differentiableOn_Gcj {j : ℕ} (hj : j < 11) : DifferentiableOn ℂ (G (cj j)) Hs :=
  fun _ hz => (hasDerivAt_cj hj hz).differentiableAt.differentiableWithinAt

lemma differentiableOn_Fc : DifferentiableOn ℂ Fc Hs := differentiableOn_Gcj (by norm_num)

/-- `iteratedDeriv j F̃ = G (cj j)` on `ℍ`, for `j ≤ 11`. -/
theorem iteratedDeriv_Fc : ∀ j : ℕ, j ≤ 11 → EqOn (iteratedDeriv j Fc) (G (cj j)) Hs
  | 0, _ => fun z _ => by simp [Fc]
  | j + 1, hj => by
    intro z hz
    rw [iteratedDeriv_succ, (iteratedDeriv_Fc j (by omega)).deriv isOpen_Hs hz]
    exact (hasDerivAt_cj (by omega) hz).deriv

/-! ### `G (cj 11) = (2πi)¹¹ Δ` -/

open UpperHalfPlane ModularForm in
/-- Mathlib's `Δ`, read on `ℂ`. -/
noncomputable def Dc : ℂ → ℂ := (⇑CuspForm.discriminant) ∘ UpperHalfPlane.ofComplex

open UpperHalfPlane ModularForm in
lemma hasSum_Dc {z : ℂ} (hz : 0 < z.im) : HasSum (fun m => (tau m : ℂ) * qe z m) (Dc z) := by
  have h := TauHecke.hasSum_cusp (k := 12) CuspForm.discriminant hz
  convert h using 2 with m
  · rw [TauHeckeBridge.qExpansion_discriminant_coeff]
    congr 1
    simp only [Function.Periodic.qParam, qe, ofReal_one, div_one]
    rw [← Complex.exp_nat_mul]; ring_nf
  · rfl

lemma cj_eleven (m : ℕ) : cj 11 m = (2 * π * I) ^ 11 * (tau m : ℂ) := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp [cj, tau_zero]
  have : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
  unfold cj
  field_simp

theorem G_cj11 {z : ℂ} (hz : 0 < z.im) : G (cj 11) z = (2 * π * I) ^ 11 * Dc z := by
  rw [← (hasSum_Dc hz).tsum_eq, ← tsum_mul_left, G]
  congr 1; funext m; rw [cj_eleven]; ring

lemma Dc_S {z : ℂ} (hz : 0 < z.im) : Dc (-1 / z) = z ^ 12 * Dc z := by
  have := (TauHecke.isModular_of (k := 12) CuspForm.discriminant).neg_inv hz
  simpa [Dc, zpow_ofNat] using this

/-! ### Periodicity and conjugation -/

lemma G_add_one (c : ℕ → ℂ) (z : ℂ) : G c (z + 1) = G c z := by
  simp only [G, qe_add_one]

lemma cj0_conj (m : ℕ) : (starRingEnd ℂ) (cj 0 m) = cj 0 m := by
  simp [cj, map_div₀]

lemma Fc_conj (z : ℂ) : (starRingEnd ℂ) (Fc z) = Fc (-(starRingEnd ℂ) z) := by
  rw [Fc, G, Complex.conj_tsum, G]
  congr 1; funext m
  rw [map_mul, cj0_conj, conj_qe]

end RamanujanWeil.Arith.ES.Analytic
