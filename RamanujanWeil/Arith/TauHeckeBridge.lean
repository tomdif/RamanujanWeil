import RamanujanWeil.Tau
import Mathlib.NumberTheory.ModularForms.QExpansion
import Mathlib.NumberTheory.ModularForms.Discriminant
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.RingTheory.PowerSeries.Basic

/-!
# The bridge `qExpansion(Δ).coeff n = RamanujanTau.tau n`

Ported (and pruned) from `~/RamanujanTau/RamanujanTau/TauBridge.lean` and
`~/RamanujanTau/RamanujanTau/DiscriminantQExpansion.lean`.

* Formal side: the coefficient lists of `Tau.lean` are given their power-series meaning
  (`toPS`); every list operation is the ring operation and truncation agrees modulo `X^{d+1}`,
  so `tau n = [qⁿ] q·(∏_{k<N}(1 − q^{k+1}))²⁴` for every `N ≥ n` (`tau_eq_coeff_qfac`).
  Unlike the source repo we never need the infinite product `qfacInf` (nor its ~100-module
  import closure through the mock-theta / four-squares files): the finite products stabilize.
* Analytic side: Mathlib's `discriminant_cuspFunction_eqOn` identifies the cusp function of `Δ`
  with `q ↦ q ∏'(1 − q^{k+1})²⁴` on the unit disc; the polynomial partial products converge to it
  locally uniformly, and Weierstrass (`TendstoLocallyUniformlyOn.deriv`, iterated) transports
  Taylor coefficients at `0`.
-/

set_option autoImplicit false

namespace RamanujanWeil.ArithPlan.TauHeckeBridge
open PowerSeries RamanujanTau

/-! ## Formal side -/

/-- the finite Euler product `∏_{k<m} (1 − X^{k+1})`. -/
noncomputable def qfac (m : ℕ) : PowerSeries ℤ := ∏ k ∈ Finset.range m, (1 - X ^ (k + 1))

lemma qfac_succ' (n : ℕ) : qfac (n + 1) = qfac n * (1 - X ^ (n + 1)) := by
  rw [qfac, qfac, Finset.prod_range_succ]

lemma coeff_eq_of_dvd {f g : PowerSeries ℤ} {K k : ℕ} (h : (X : PowerSeries ℤ) ^ K ∣ f - g)
    (hk : k < K) : coeff k f = coeff k g := by
  have := (PowerSeries.X_pow_dvd_iff.mp h) k hk
  rwa [map_sub, sub_eq_zero] at this

/-- reduction modulo `X^N`. -/
noncomputable abbrev π (N : ℕ) :
    PowerSeries ℤ →+* PowerSeries ℤ ⧸ Ideal.span {(X : PowerSeries ℤ) ^ N} :=
  Ideal.Quotient.mk _

lemma π_eq_iff {N : ℕ} {f g : PowerSeries ℤ} : π N f = π N g ↔ (X : PowerSeries ℤ) ^ N ∣ f - g := by
  rw [Ideal.Quotient.eq, Ideal.mem_span_singleton]

lemma X_pow_dvd_qfac_sub (N : ℕ) : ∀ M, N ≤ M → (X : PowerSeries ℤ) ^ (N + 1) ∣ qfac M - qfac N := by
  intro M hM
  induction M, hM using Nat.le_induction with
  | base => simp
  | succ M hNM ih =>
    rw [qfac_succ', show qfac M * (1 - X ^ (M + 1)) - qfac N
      = (qfac M - qfac N) - qfac M * X ^ (M + 1) by ring]
    exact dvd_sub ih (Dvd.dvd.mul_left (pow_dvd_pow X (by omega)) _)

/-- the power series with coefficient list `l`. -/
noncomputable def toPS (l : List ℤ) : PowerSeries ℤ := mk (coeffList l)

lemma toPS_nil : toPS [] = 0 := by ext n; simp [toPS, coeffList]

lemma toPS_cons (a : ℤ) (l : List ℤ) : toPS (a :: l) = C a + X * toPS l := by
  ext n
  rcases n with _ | n
  · simp [toPS, coeffList]
  · rw [map_add, coeff_C, if_neg (by omega), zero_add, coeff_succ_X_mul, toPS, toPS, coeff_mk,
      coeff_mk]; rfl

lemma toPS_addList : ∀ p q : List ℤ, toPS (addList p q) = toPS p + toPS q
  | [], q => by rw [addList, toPS_nil, zero_add]
  | a :: as, [] => by simp [addList, toPS_nil]
  | a :: as, b :: bs => by
    rw [addList, toPS_cons, toPS_cons, toPS_cons, toPS_addList as bs, map_add]; ring

lemma toPS_scaleList (c : ℤ) : ∀ p : List ℤ, toPS (scaleList c p) = C c * toPS p
  | [] => by rw [scaleList, toPS_nil, mul_zero]
  | a :: as => by rw [scaleList, toPS_cons, toPS_cons, toPS_scaleList c as, map_mul]; ring

lemma toPS_mulList : ∀ p q : List ℤ, toPS (mulList p q) = toPS p * toPS q
  | [], q => by rw [mulList, toPS_nil, zero_mul]
  | a :: as, q => by
    rw [mulList, toPS_addList, toPS_scaleList, toPS_cons, toPS_cons, toPS_mulList as q, map_zero,
      zero_add]; ring

lemma toPS_shiftList_one (p : List ℤ) : toPS (shiftList 1 p) = X * toPS p := by
  rw [shiftList, shiftList, toPS_cons, map_zero, zero_add]

lemma coeffList_replicate_append (k m : ℕ) (l : List ℤ) :
    coeffList (List.replicate k 0 ++ l) m = if m < k then 0 else coeffList l (m - k) := by
  induction k generalizing m with
  | zero => simp
  | succ k ih =>
    rcases m with _ | m
    · simp [List.replicate_succ, coeffList]
    · rw [List.replicate_succ, List.cons_append, coeffList, ih]
      split_ifs <;> first | rfl | omega | (congr 1; omega)

lemma coeffList_single (a : ℤ) (j : ℕ) : coeffList [a] j = if j = 0 then a else 0 := by
  rcases j with _ | j <;> simp [coeffList]

lemma toPS_oneMinusXk (k : ℕ) : toPS (oneMinusXk (k + 1)) = 1 - X ^ (k + 1) := by
  ext n
  rw [toPS, coeff_mk, oneMinusXk, map_sub, coeff_one, coeff_X_pow]
  rcases n with _ | m
  · simp [coeffList]
  · rw [coeffList, coeffList_replicate_append, if_neg (by omega : m + 1 ≠ 0)]
    by_cases hlt : m < k
    · rw [if_pos hlt, if_neg (by omega)]; simp
    · rw [if_neg hlt, coeffList_single]
      by_cases he : m = k
      · subst he; simp
      · rw [if_neg (by omega), if_neg (by omega)]; simp

/-- truncation keeps the coefficients of degree `≤ d`. -/
lemma coeffList_truncList : ∀ (d : ℕ) (p : List ℤ) (k : ℕ),
    coeffList (truncList d p) k = if k ≤ d then coeffList p k else 0
  | _, [], k => by simp [truncList, coeffList]
  | d, a :: as, k => by
    rw [truncList]
    by_cases hd : d = 0
    · subst hd
      rcases k with _ | k <;> simp [coeffList]
    · rw [if_neg hd]
      rcases k with _ | k
      · simp [coeffList]
      · rw [coeffList, coeffList, coeffList_truncList (d - 1) as k]
        split_ifs <;> first | rfl | omega

lemma π_truncList (d : ℕ) (p : List ℤ) : π (d + 1) (toPS (truncList d p)) = π (d + 1) (toPS p) := by
  rw [π_eq_iff, PowerSeries.X_pow_dvd_iff]
  intro k hk
  rw [map_sub, toPS, toPS, coeff_mk, coeff_mk, coeffList_truncList, if_pos (by omega), sub_self]

lemma π_euler (d N : ℕ) : π (d + 1) (toPS (eulerProductTrunc d N)) = π (d + 1) (qfac N) := by
  induction N with
  | zero => simp [eulerProductTrunc, qfac, toPS_cons, toPS_nil]
  | succ N ih =>
    rw [eulerProductTrunc, π_truncList, toPS_mulList, map_mul, ih, toPS_oneMinusXk, qfac_succ' N,
      map_mul]

lemma π_truncPow (d : ℕ) (p : List ℤ) (n : ℕ) :
    π (d + 1) (toPS (truncPowList d p n)) = π (d + 1) (toPS p) ^ n := by
  induction n with
  | zero => simp [truncPowList, toPS_cons, toPS_nil]
  | succ n ih => rw [truncPowList, π_truncList, toPS_mulList, map_mul, ih]; ring

/-- **formal bridge**: `τ(n) = [qⁿ] q·(∏_{k<N}(1 − q^{k+1}))²⁴` for every `N ≥ n`. -/
theorem tau_eq_coeff_qfac {n N : ℕ} (hN : n ≤ N) : tau n = coeff n (X * qfac N ^ 24) := by
  have hq : π (n + 1) (qfac n) = π (n + 1) (qfac N) :=
    π_eq_iff.mpr ((dvd_sub_comm).mp (X_pow_dvd_qfac_sub n N hN))
  have h : π (n + 1) (toPS (shiftList 1 (truncPowList n (eulerProductTrunc n n) 24)))
      = π (n + 1) (X * qfac N ^ 24) := by
    rw [toPS_shiftList_one, map_mul, π_truncPow, π_euler, hq, map_mul, map_pow]
  have hc := coeff_eq_of_dvd (π_eq_iff.mp h) (Nat.lt_succ_self n)
  rw [toPS, coeff_mk] at hc
  exact hc

/-- `q·(∏_{k<N}(1 − qᵏ⁺¹))²⁴` as an integer polynomial. -/
noncomputable def PN (N : ℕ) : Polynomial ℤ :=
  Polynomial.X * (∏ k ∈ Finset.range N, (1 - Polynomial.X ^ (k + 1))) ^ 24

lemma coe_PN (N : ℕ) : ((PN N : Polynomial ℤ) : PowerSeries ℤ) = PowerSeries.X * qfac N ^ 24 := by
  rw [PN, qfac, ← Polynomial.coeToPowerSeries.ringHom_apply, map_mul, map_pow, map_prod]
  simp

lemma PN_coeff {n N : ℕ} (hN : n ≤ N) : (PN N).coeff n = tau n := by
  rw [← Polynomial.coeff_coe, coe_PN, tau_eq_coeff_qfac hN]

/-! ## Analytic side -/

open Complex Filter Metric Function Set ModularForm UpperHalfPlane
open scoped Topology

/-- iterated derivatives commute with locally uniform limits of holomorphic functions. -/
lemma tlu_iteratedDeriv {U : Set ℂ} (hU : IsOpen U) (n : ℕ) :
    ∀ {F : ℕ → ℂ → ℂ} {f : ℂ → ℂ}, TendstoLocallyUniformlyOn F f atTop U →
      (∀ N, DifferentiableOn ℂ (F N) U) →
      TendstoLocallyUniformlyOn (fun N => iteratedDeriv n (F N)) (iteratedDeriv n f) atTop U := by
  induction n with
  | zero => intro F f hF _; simpa using hF
  | succ n ih =>
    intro F f hF hd
    simp_rw [iteratedDeriv_succ']
    exact ih (hF.deriv (Eventually.of_forall hd) hU) (fun N => (hd N).deriv hU)

lemma eventuallyEq_iteratedDeriv {f g : ℂ → ℂ} {x : ℂ} (h : f =ᶠ[𝓝 x] g) (n : ℕ) :
    iteratedDeriv n f =ᶠ[𝓝 x] iteratedDeriv n g := by
  induction n with
  | zero => simpa using h
  | succ n ih => simp_rw [iteratedDeriv_succ]; exact ih.deriv

lemma iteratedDeriv_poly (p : Polynomial ℂ) (n : ℕ) :
    iteratedDeriv n (fun x => p.eval x) = fun x => (Polynomial.derivative^[n] p).eval x := by
  induction n generalizing p with
  | zero => simp
  | succ n ih =>
    rw [iteratedDeriv_succ', show deriv (fun x => p.eval x) = fun x => (Polynomial.derivative p).eval x from
      funext fun x => Polynomial.deriv p, ih, Function.iterate_succ_apply]

lemma iteratedDeriv_poly_zero (p : Polynomial ℂ) (n : ℕ) :
    iteratedDeriv n (fun x => p.eval x) 0 = n.factorial * p.coeff n := by
  rw [iteratedDeriv_poly]
  dsimp only
  rw [← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_iterate_derivative, zero_add,
    Nat.descFactorial_self, nsmul_eq_mul]

lemma tlu_const {U : Set ℂ} (f : ℂ → ℂ) : TendstoLocallyUniformlyOn (fun (_ : ℕ) => f) f atTop U :=
  TendstoUniformlyOn.tendstoLocallyUniformlyOn
    (fun _ hu => Eventually.of_forall fun _ _ _ => refl_mem_uniformity hu)

lemma tlu_pow {U : Set ℂ} {G : ℕ → ℂ → ℂ} {g : ℂ → ℂ} (hG : TendstoLocallyUniformlyOn G g atTop U)
    (hg : ContinuousOn g U) (k : ℕ) :
    TendstoLocallyUniformlyOn (fun N q => G N q ^ k) (fun q => g q ^ k) atTop U := by
  induction k with
  | zero => simpa using tlu_const (U := U) (fun _ : ℂ => (1 : ℂ))
  | succ k ih =>
    simp_rw [pow_succ]
    exact ih.mul₀ hG (hg.pow k) hg

/-- the complex partial products. -/
noncomputable def FN (N : ℕ) (q : ℂ) : ℂ := ((PN N).map (Int.castRingHom ℂ)).eval q

lemma FN_eq (N : ℕ) (q : ℂ) : FN N q = q * (∏ k ∈ Finset.range N, (1 - q ^ (k + 1))) ^ 24 := by
  simp [FN, PN, Polynomial.map_prod, Polynomial.eval_prod]

/-- the limit function `q·(∏'(1 − qᵏ⁺¹))²⁴`. -/
noncomputable def Flim (q : ℂ) : ℂ := q * (∏' k : ℕ, (1 - q ^ (k + 1))) ^ 24

lemma tlu_FN : TendstoLocallyUniformlyOn FN Flim atTop (ball (0 : ℂ) 1) := by
  have hP := multipliableLocallyUniformlyOn_one_sub_pow.hasProdLocallyUniformlyOn.tendstoLocallyUniformlyOn_finsetRange
  have hc : ContinuousOn (fun q : ℂ => ∏' k : ℕ, (1 - q ^ (k + 1))) (ball (0 : ℂ) 1) :=
    differentiableOn_tprod_one_sub_pow.continuousOn
  have h24 := tlu_pow hP hc 24
  have hid : TendstoLocallyUniformlyOn (fun (_ : ℕ) (q : ℂ) => q) (fun q => q) atTop (ball (0 : ℂ) 1) :=
    tlu_const _
  have := hid.mul₀ h24 continuousOn_id (hc.pow 24)
  convert this using 1
  · funext N q; rw [FN_eq]; rfl
  · rfl

lemma cusp_eventuallyEq : cuspFunction 1 (CuspForm.discriminant : ℍ → ℂ) =ᶠ[𝓝 0] Flim := by
  filter_upwards [ball_mem_nhds (0 : ℂ) one_pos] with q hq
  have hq' : ‖q‖ < 1 := by simpa using hq
  rw [CuspForm.coe_discriminant, discriminant_cuspFunction_eqOn hq, Flim]
  beta_reduce
  rw [(multipliable_one_sub_pow hq').tprod_pow 24]

/-- **The analytic–formal bridge.** The `n`-th q-expansion coefficient of Mathlib's modular
discriminant `Δ = η²⁴` is `RamanujanTau.tau n`. -/
theorem qExpansion_discriminant_coeff (n : ℕ) :
    (qExpansion 1 (CuspForm.discriminant : ℍ → ℂ)).coeff n = (tau n : ℂ) := by
  rw [qExpansion_coeff, (eventuallyEq_iteratedDeriv cusp_eventuallyEq n).eq_of_nhds]
  have hlim := (tlu_iteratedDeriv isOpen_ball n tlu_FN
    (fun N => (Polynomial.differentiable _).differentiableOn)).tendsto_at (mem_ball_self one_pos)
  have hconst : ∀ᶠ N in atTop, iteratedDeriv n (FN N) 0 = n.factorial * (tau n : ℂ) := by
    filter_upwards [eventually_ge_atTop n] with N hN
    rw [show FN N = fun q => ((PN N).map (Int.castRingHom ℂ)).eval q from rfl, iteratedDeriv_poly_zero,
      Polynomial.coeff_map, PN_coeff hN, eq_intCast]
  have := tendsto_nhds_unique hlim (tendsto_const_nhds.congr' (EventuallyEq.symm hconst))
  rw [this, ← mul_assoc, inv_mul_cancel₀ (by exact_mod_cast n.factorial_ne_zero), one_mul]

end RamanujanWeil.ArithPlan.TauHeckeBridge
