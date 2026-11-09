import RamanujanWeil.Arith.ESAnalyticHecke
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# A2 / ES-P12: certified nonvanishing `ρ₈ ≠ 0`, `ρ₉ ≠ 0`

On the imaginary axis `R(y) := ρ(iy) = f(y) + y¹⁰ f(1/y)` with
`f(y) = F̃(iy) = Σ τ(m) m⁻¹¹ e^{−2πmy}` (real). Writing `ρ = ρ₁₀e0 + ρ₈p⁺ + ρ₉p⁻` (`W_decomp`),

  `R(y) = Re ρ₁₀·(−1 − y¹⁰) + Re ρ₈·y²(1 + y²)³ − Im ρ₉·(y + 25/4y³ + 21/2y⁵ + 25/4y⁷ + y⁹)`.

Three evaluations `y = 1, 2, 3/2` determine the three real unknowns; with
`|f(y) − x| ≤ x²/5` for `x = e^{−2πy} ≤ 1/20` (`fr_bound`, from `tau_abs_mul_pow_le` with
`r = 1/14`) and `e^{−π/3} ∈ [0.35, 0.352]` (`u_bounds`), `linarith` gives `Re ρ₈ > 1` and
`Im ρ₉ > 1` (true values `18.99`, `6.156`).
-/

set_option autoImplicit false

namespace RamanujanWeil.Arith.ES.Analytic

open Complex Filter Set Finset RamanujanTau
open RamanujanWeil.Arith.ES RamanujanWeil.Arith.ES.M2
open scoped Real Topology Matrix

/-! ### `f(y) = F̃(iy)` -/

/-- `f(y) = Σ τ(m) m⁻¹¹ (e^{−2πy})ᵐ`. -/
noncomputable def fr (y : ℝ) : ℝ :=
  ∑' m : ℕ, (tau m : ℝ) / (m : ℝ) ^ 11 * Real.exp (-2 * π * y) ^ m

lemma qe_I_mul (y : ℝ) (m : ℕ) : qe (I * y) m = ((Real.exp (-2 * π * y) ^ m : ℝ) : ℂ) := by
  rw [qe, ofReal_pow, ofReal_exp, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring_nf
  rw [I_sq]; ring

lemma Fc_I_mul (y : ℝ) : Fc (I * y) = (fr y : ℂ) := by
  rw [Fc, G, fr, ofReal_tsum]
  congr 1; funext m
  rw [qe_I_mul, cj0_apply]
  push_cast; ring

/-! ### Bounds -/

lemma exp_two_lt : Real.exp 2 < 7.39 := by
  have h := Real.exp_one_lt_d9
  rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
  have h0 := Real.exp_pos 1
  nlinarith

lemma summable_abs_tau {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    Summable fun m : ℕ => |(tau m : ℝ)| * x ^ m := by
  have := bd_tau x hx0 hx1
  simpa [Complex.norm_intCast] using this

lemma summable_fr_terms {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    Summable fun m : ℕ => (tau m : ℝ) / (m : ℝ) ^ 11 * x ^ m := by
  refine Summable.of_norm_bounded (summable_abs_tau hx0 hx1) fun m => ?_
  rw [Real.norm_eq_abs, abs_mul, abs_div, abs_pow, abs_of_nonneg (pow_nonneg hx0 m)]
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  have hm1 : (1 : ℝ) ≤ |(m : ℝ)| ^ 11 := by
    rw [abs_of_nonneg (Nat.cast_nonneg m)]; exact one_le_pow₀ (by exact_mod_cast hm)
  have : |(tau m : ℝ)| / |(m : ℝ)| ^ 11 ≤ |(tau m : ℝ)| := div_le_self (abs_nonneg _) hm1
  exact mul_le_mul_of_nonneg_right this (pow_nonneg hx0 m)

/-- **`|f − x| ≤ x²/5`** for `x = e^{−2πy} ≤ 1/20`. -/
theorem fr_bound (y : ℝ) (hx : Real.exp (-2 * π * y) ≤ 1 / 20) :
    |fr y - Real.exp (-2 * π * y)| ≤ Real.exp (-2 * π * y) ^ 2 / 5 := by
  set x := Real.exp (-2 * π * y) with hxdef
  have hx0 : 0 ≤ x := (Real.exp_pos _).le
  have hx1 : x < 1 := by linarith
  set f : ℕ → ℝ := fun m => (tau m : ℝ) / (m : ℝ) ^ 11 * x ^ m with hf
  have hs : Summable f := summable_fr_terms hx0 hx1
  have hsplit := hs.sum_add_tsum_nat_add 2
  have hfr : fr y = ∑' m, f m := rfl
  have h01 : ∑ i ∈ range 2, f i = x := by
    simp [hf, Finset.sum_range_succ, tau_zero, tau_one]
  rw [hfr, ← hsplit, h01, add_sub_cancel_left]
  -- the tail
  obtain ⟨r, hr⟩ : ∃ r : ℝ, r = 1 / 14 := ⟨_, rfl⟩
  have hr0 : 0 < r := by rw [hr]; norm_num
  have hr1 : r < 1 := by rw [hr]; norm_num
  obtain ⟨C, hCdef⟩ : ∃ C : ℝ, C = Real.exp (24 * (r / (1 - r))) := ⟨_, rfl⟩
  have hC : C ≤ 7.39 := by
    rw [hCdef]
    refine le_trans (Real.exp_le_exp.mpr ?_) exp_two_lt.le
    rw [hr]; norm_num
  have hC0 : 0 ≤ C := by rw [hCdef]; exact (Real.exp_pos _).le
  have hxr : x / r ≤ 7 / 10 := by
    rw [div_le_iff₀ hr0, hr]; linarith
  have hxr0 : 0 ≤ x / r := div_nonneg hx0 hr0.le
  have hgeo : Summable fun m : ℕ => (x / r) ^ m := summable_geometric_of_lt_one hxr0 (by linarith)
  set g : ℕ → ℝ := fun m => r * C / 2048 * (x / r) ^ 2 * (x / r) ^ m with hgdef
  have hg : Summable g := hgeo.mul_left _
  have hfg : ∀ m, ‖f (m + 2)‖ ≤ g m := by
    intro m
    have hb := tau_abs_mul_pow_le hr0.le hr1 (m + 2)
    rw [← hCdef] at hb
    simp only [hf, hgdef, Real.norm_eq_abs, abs_mul, abs_div, abs_pow, abs_of_nonneg hx0]
    have hm : (2 : ℝ) ≤ |((m + 2 : ℕ) : ℝ)| := by
      rw [abs_of_nonneg (Nat.cast_nonneg _)]; push_cast; linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
    have hm11 : (2048 : ℝ) ≤ |((m + 2 : ℕ) : ℝ)| ^ 11 := by
      calc (2048 : ℝ) = 2 ^ 11 := by norm_num
        _ ≤ _ := pow_le_pow_left₀ (by norm_num) hm 11
    have e1 : |(tau (m + 2) : ℝ)| * x ^ (m + 2) =
        (|(tau (m + 2) : ℝ)| * r ^ (m + 2)) * (x / r) ^ (m + 2) := by
      rw [div_pow, mul_assoc, mul_div_assoc', mul_div_cancel_left₀ _ (pow_ne_zero _ hr0.ne')]
    have h1 : |(tau (m + 2) : ℝ)| * x ^ (m + 2) ≤ r * C * (x / r) ^ (m + 2) := by
      rw [e1]; exact mul_le_mul_of_nonneg_right hb (pow_nonneg hxr0 _)
    have h2 : 0 ≤ |(tau (m + 2) : ℝ)| * x ^ (m + 2) := mul_nonneg (abs_nonneg _) (pow_nonneg hx0 _)
    calc |(tau (m + 2) : ℝ)| / |((m + 2 : ℕ) : ℝ)| ^ 11 * x ^ (m + 2)
        = (|(tau (m + 2) : ℝ)| * x ^ (m + 2)) / |((m + 2 : ℕ) : ℝ)| ^ 11 := by ring
      _ ≤ (|(tau (m + 2) : ℝ)| * x ^ (m + 2)) / 2048 :=
          div_le_div_of_nonneg_left h2 (by norm_num) hm11
      _ ≤ (r * C * (x / r) ^ (m + 2)) / 2048 := div_le_div_of_nonneg_right h1 (by norm_num)
      _ = r * C / 2048 * (x / r) ^ 2 * (x / r) ^ m := by ring
  have htail : ‖∑' m, f (m + 2)‖ ≤ ∑' m, g m := tsum_of_norm_bounded hg.hasSum hfg
  have hgsum : ∑' m, g m = r * C / 2048 * (x / r) ^ 2 * (1 - x / r)⁻¹ := by
    rw [hgdef, tsum_mul_left, tsum_geometric_of_lt_one hxr0 (by linarith)]
  rw [Real.norm_eq_abs, hgsum] at htail
  refine htail.trans ?_
  have hq : (1 - x / r)⁻¹ ≤ 10 / 3 := by
    rw [inv_le_comm₀ (by linarith) (by norm_num)]; linarith
  have hxx : (x / r) ^ 2 = 196 * x ^ 2 := by rw [div_pow, hr]; ring
  rw [hxx]
  have hA : 0 ≤ r * C / 2048 * (196 * x ^ 2) := by positivity
  calc r * C / 2048 * (196 * x ^ 2) * (1 - x / r)⁻¹ ≤ r * C / 2048 * (196 * x ^ 2) * (10 / 3) :=
        mul_le_mul_of_nonneg_left hq hA
    _ = C * x ^ 2 * (196 * 10 / (14 * 2048 * 3)) := by rw [hr]; ring
    _ ≤ 7.39 * x ^ 2 * (196 * 10 / (14 * 2048 * 3)) := by gcongr
    _ ≤ x ^ 2 / 5 := by nlinarith [sq_nonneg x]

/-- `e^{−π/3} ∈ [0.35, 0.352]`. -/
theorem u_bounds : 0.35 ≤ Real.exp (-(π / 3)) ∧ Real.exp (-(π / 3)) ≤ 0.352 := by
  have hp1 := Real.pi_gt_d4
  have hp2 := Real.pi_lt_d4
  have he1 := Real.exp_one_gt_d9
  have he2 := Real.exp_one_lt_d9
  rw [Real.exp_neg]
  -- `e^{π/3} = e · e^{π/3 − 1}`, `π/3 − 1 ∈ [0.0471, 0.0472]`
  have hs : π / 3 = 1 + (π / 3 - 1) := by ring
  set t := π / 3 - 1 with ht
  have ht0 : 0 ≤ t := by rw [ht]; linarith
  have ht1 : t ≤ 0.0473 := by rw [ht]; linarith
  have hlo : 1 + t ≤ Real.exp t := by linarith [Real.add_one_le_exp t]
  have hhi : Real.exp t ≤ 1 + t + t ^ 2 := by
    have := Real.exp_bound' ht0 (by linarith) (n := 2) (by norm_num)
    simp [Finset.sum_range_succ, Nat.factorial] at this
    nlinarith
  have hE : Real.exp (π / 3) = Real.exp 1 * Real.exp t := by rw [hs, Real.exp_add]
  have hpos := Real.exp_pos (π / 3)
  rw [hE] at hpos ⊢
  have h1 : 2.846 ≤ Real.exp 1 * Real.exp t := by
    have : 0.0471 ≤ t := by rw [ht]; linarith
    nlinarith [Real.exp_pos t]
  have h2 : Real.exp 1 * Real.exp t ≤ 2.853 := by
    nlinarith [Real.exp_pos t, Real.exp_pos 1]
  constructor
  · rw [le_inv_comm₀ (by norm_num) hpos]; norm_num; linarith
  · rw [inv_le_comm₀ hpos (by norm_num)]; norm_num; linarith

end RamanujanWeil.Arith.ES.Analytic
