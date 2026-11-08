import RamanujanWeil.Ihara.IharaStatement
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics

/-!
# M1′: the approximate endgame of the Ihara route (Mathlib + `Endgame.lean` only)

Milestone M1′ of `docs/ARITH_ROUTE.md` (§4, frozen in `scratch/ArithInterfaces.lean`): the exact
Ihara–Birch identity in `deligne_of_package` is replaced by a growth bound
`S n = main n + O((n+1)^k (√p)^{(2(d−2)+13)n})`.

* `coeff_eq_zero_of_tendsto`: if `‖u‖ = M > 0` for `u ∈ U` and `Σ_U d_u (u/M)ⁿ → 0`, then all
  `d_u = 0` (multiply by `(w/M)^{−n}`, take Cesàro means; `tendsto_cesaro_geom`).
* `coeff_eq_zero_of_growth`: an exponential polynomial that is `O((n+1)^k Rⁿ)` has no base of
  modulus `> R` (top modulus layer + `coeff_eq_zero_of_tendsto`). **Deviation:** the hypothesis
  `0 ≤ R` is added; the frozen statement is false for `R < 0` (`coeff_eq_zero_of_growth_frozen_false`).
* `false_of_package_approx`, `deligne_of_package_approx_gen`, `deligne_of_package_approx`
  (frozen statement): rerun of `false_of_package` with the growth lemma at `zw = p^{e+1}β`, whose
  modulus exceeds `p^{e+13/2}` under a violation.
* `IharaApprox` (frozen, with the repo's `weierstrassSum`), `iharaApprox_of_iharaIdentity`,
  `deligne_of_package_iharaApprox` (the `d = 5` hand-off used by `FinalApprox.lean`).
-/

open Finset Filter Topology

namespace RamanujanWeil.Ihara

/-- Cesàro means of `xⁿ` vanish for `‖x‖ = 1`, `x ≠ 1`. -/
theorem tendsto_cesaro_geom (x : ℂ) (hx : ‖x‖ = 1) (hx1 : x ≠ 1) :
    Tendsto (fun N : ℕ => (N⁻¹ : ℝ) • ∑ n ∈ range N, x ^ n) atTop (𝓝 0) := by
  have hne : x - 1 ≠ 0 := sub_ne_zero.2 hx1
  have hpos : 0 < ‖x - 1‖ := norm_pos_iff.2 hne
  refine squeeze_zero_norm (a := fun N : ℕ => 2 / ‖x - 1‖ * (N : ℝ)⁻¹) (fun N => ?_) ?_
  · rw [norm_smul, geom_sum_eq hx1, norm_div, Real.norm_eq_abs, abs_inv, Nat.abs_cast]
    have h2 : ‖x ^ N - 1‖ ≤ 2 := by
      calc ‖x ^ N - 1‖ ≤ ‖x ^ N‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
        _ = 2 := by rw [norm_pow, hx]; norm_num
    have : ‖x ^ N - 1‖ / ‖x - 1‖ ≤ 2 / ‖x - 1‖ := div_le_div_of_nonneg_right h2 hpos.le
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_right this (by positivity)
  · simpa using (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (2 / ‖x - 1‖)

/-- **Unimodular exponential sums tending to zero vanish.** If all `u ∈ U` have `‖u‖ = M > 0` and
`Σ_{u ∈ U} d u · (u / M)ⁿ → 0`, then every `d u = 0` (Cesàro extraction of one coefficient). -/
theorem coeff_eq_zero_of_tendsto (U : Finset ℂ) (d : ℂ → ℂ) (M : ℝ) (hM : 0 < M)
    (hU : ∀ u ∈ U, ‖u‖ = M)
    (h : Tendsto (fun n : ℕ => ∑ u ∈ U, d u * (u / M) ^ n) atTop (𝓝 0)) :
    ∀ w ∈ U, d w = 0 := by
  intro w hw
  have hM0 : (M : ℂ) ≠ 0 := by exact_mod_cast hM.ne'
  have hw0 : w ≠ 0 := by
    intro h0; have := hU w hw; rw [h0, norm_zero] at this; linarith
  set y : ℂ := ((w : ℂ) / M)⁻¹ with hy
  have hy1 : ‖y‖ = 1 := by
    rw [hy, norm_inv, norm_div, hU w hw, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hM,
      div_self hM.ne', inv_one]
  -- multiply by the unimodular `yⁿ`
  have h1 : Tendsto (fun n : ℕ => ∑ u ∈ U, d u * (u / w) ^ n) atTop (𝓝 0) := by
    have hb : Tendsto (fun n : ℕ => (∑ u ∈ U, d u * (u / M) ^ n) * y ^ n) atTop (𝓝 0) := by
      have hn := h.norm
      rw [norm_zero] at hn
      refine squeeze_zero_norm (fun n => le_of_eq ?_) hn
      rw [norm_mul, norm_pow, hy1, one_pow, mul_one]
    refine hb.congr fun n => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [mul_assoc, ← mul_pow, hy]
    congr 2
    field_simp
  -- Cesàro means
  have h2 := h1.cesaro_smul
  have h3 : Tendsto (fun N : ℕ => (N⁻¹ : ℝ) • ∑ n ∈ range N, ∑ u ∈ U, d u * (u / w) ^ n) atTop
      (𝓝 (∑ u ∈ U, if u = w then d w else 0)) := by
    have : ∀ N : ℕ, (N⁻¹ : ℝ) • ∑ n ∈ range N, ∑ u ∈ U, d u * (u / w) ^ n =
        ∑ u ∈ U, d u * ((N⁻¹ : ℝ) • ∑ n ∈ range N, (u / w) ^ n) := by
      intro N
      rw [Finset.sum_comm, Finset.smul_sum]
      refine Finset.sum_congr rfl fun u _ => ?_
      rw [← Finset.mul_sum, mul_smul_comm]
    simp_rw [this]
    refine tendsto_finsetSum _ fun u hu => ?_
    by_cases huw : u = w
    · subst huw
      simp only [ite_true]
      have : ∀ᶠ N : ℕ in atTop, d u * ((N⁻¹ : ℝ) • ∑ n ∈ range N, (u / u) ^ n) = d u := by
        filter_upwards [eventually_ge_atTop 1] with N hN
        rw [div_self hw0]
        simp only [one_pow, sum_const, card_range, nsmul_eq_mul, mul_one]
        rw [Complex.real_smul]
        have : (N : ℂ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
        push_cast
        field_simp
      exact tendsto_const_nhds.congr' (this.mono fun N h => h.symm)
    · simp only [huw, ite_false]
      have hx : ‖u / w‖ = 1 := by
        rw [norm_div, hU u hu, hU w hw, div_self hM.ne']
      have hx1 : u / w ≠ 1 := fun h => huw ((div_eq_one_iff_eq hw0).1 h)
      simpa using (tendsto_cesaro_geom (u / w) hx hx1).const_mul (d u)
  have := tendsto_nhds_unique h3 h2
  simpa [Finset.sum_ite_eq', hw] using this


/-- `(n+1)^k ρⁿ → 0` for `0 < ρ < 1`. -/
theorem tendsto_succ_pow_mul_pow (k : ℕ) {ρ : ℝ} (h0 : 0 < ρ) (h1 : ρ < 1) :
    Tendsto (fun n : ℕ => ((n : ℝ) + 1) ^ k * ρ ^ n) atTop (𝓝 0) := by
  have h := (tendsto_pow_const_mul_const_pow_of_abs_lt_one k
    (show |ρ| < 1 by rwa [abs_of_pos h0])).comp (tendsto_add_atTop_nat 1)
  have h2 := h.const_mul ρ⁻¹
  rw [mul_zero] at h2
  refine h2.congr fun n => ?_
  simp only [Function.comp, Nat.cast_add, Nat.cast_one, pow_succ]
  field_simp

/-- **Growth lemma (M1′ core).** An exponential polynomial `Σ_{z ∈ T} c_z zⁿ` that is
`O((n+1)^k Rⁿ)` (for `n ≥ 1`, with `R ≥ 0`) has `c_z = 0` for every base with `‖z‖ > R`.
Proof: let `M` be the largest modulus with `c_z ≠ 0`; after dividing by `Mⁿ` the lower layers
and the error tend to `0`, so the top layer `Σ_{‖z‖ = M} c_z (z/M)ⁿ → 0`, and
`coeff_eq_zero_of_tendsto` kills it. -/
theorem coeff_eq_zero_of_growth (T : Finset ℂ) (c : ℂ → ℂ) (R C : ℝ) (k : ℕ) (hR : 0 ≤ R)
    (h : ∀ n : ℕ, 1 ≤ n → ‖∑ z ∈ T, c z * z ^ n‖ ≤ C * ((n : ℝ) + 1) ^ k * R ^ n) :
    ∀ z ∈ T, R < ‖z‖ → c z = 0 := by
  classical
  intro z0 hz0 hRz0
  by_contra hc0
  set T0 := T.filter (fun z => c z ≠ 0) with hT0
  have hz0' : z0 ∈ T0 := Finset.mem_filter.2 ⟨hz0, hc0⟩
  have hne : T0.Nonempty := ⟨z0, hz0'⟩
  set M : ℝ := T0.sup' hne (fun z => ‖z‖) with hMdef
  have hzM : ∀ z ∈ T0, ‖z‖ ≤ M := fun z hz => Finset.le_sup' (fun z => ‖z‖) hz
  obtain ⟨w, hwT0, hwM⟩ := Finset.exists_mem_eq_sup' hne (fun z => ‖z‖)
  have hRM : R < M := lt_of_lt_of_le hRz0 (hzM z0 hz0')
  have hM : 0 < M := lt_of_le_of_lt hR hRM
  have hM0 : (M : ℂ) ≠ 0 := by exact_mod_cast hM.ne'
  obtain ⟨R', hR'⟩ : ∃ R' : ℝ, R' = (R + M) / 2 := ⟨_, rfl⟩
  have hR'0 : 0 < R' := by rw [hR']; linarith
  have hRR' : R ≤ R' := by rw [hR']; linarith
  have hR'M : R' < M := by rw [hR']; linarith
  -- the normalized sum tends to zero
  set a : ℕ → ℂ := fun n => ∑ z ∈ T0, c z * (z / M) ^ n with ha
  have ha_eq : ∀ n, a n = (∑ z ∈ T, c z * z ^ n) / (M : ℂ) ^ n := by
    intro n
    show ∑ z ∈ T0, c z * (z / M) ^ n = _
    rw [hT0, Finset.sum_filter, Finset.sum_div]
    refine Finset.sum_congr rfl fun z _ => ?_
    split_ifs with hcz
    · rw [div_pow, mul_div_assoc]
    · push Not at hcz
      simp [hcz]
  have ha0 : Tendsto a atTop (𝓝 0) := by
    have hlim : Tendsto (fun n : ℕ => |C| * (((n : ℝ) + 1) ^ k * (R' / M) ^ n)) atTop (𝓝 0) := by
      simpa using (tendsto_succ_pow_mul_pow k (div_pos hR'0 hM)
        ((div_lt_one hM).2 hR'M)).const_mul |C|
    refine squeeze_zero_norm' ?_ hlim
    filter_upwards [eventually_ge_atTop 1] with n hn
    rw [ha_eq n, norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hM,
      div_le_iff₀ (by positivity)]
    calc ‖∑ z ∈ T, c z * z ^ n‖ ≤ C * ((n : ℝ) + 1) ^ k * R ^ n := h n hn
      _ ≤ |C| * ((n : ℝ) + 1) ^ k * R' ^ n := by
          apply mul_le_mul (mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity))
            (pow_le_pow_left₀ hR hRR' n) (by positivity) (by positivity)
      _ = |C| * (((n : ℝ) + 1) ^ k * (R' / M) ^ n) * M ^ n := by
          rw [div_pow]; field_simp
  -- the lower layers tend to zero
  set L := T0.filter (fun z => ‖z‖ ≠ M) with hL
  set U := T0.filter (fun z => ‖z‖ = M) with hU
  have hLlim : Tendsto (fun n : ℕ => ∑ z ∈ L, c z * (z / M) ^ n) atTop (𝓝 0) := by
    have : (0 : ℂ) = ∑ z ∈ L, c z * 0 := by simp
    rw [this]
    refine tendsto_finsetSum _ fun z hz => (tendsto_pow_atTop_nhds_zero_of_norm_lt_one ?_).const_mul _
    obtain ⟨hzT0, hzM'⟩ := Finset.mem_filter.1 hz
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hM, div_lt_one hM]
    exact lt_of_le_of_ne (hzM z hzT0) hzM'
  have hUlim : Tendsto (fun n : ℕ => ∑ z ∈ U, c z * (z / M) ^ n) atTop (𝓝 0) := by
    have := ha0.sub hLlim
    rw [sub_zero] at this
    refine this.congr fun n => ?_
    simp only [ha, hU, hL]
    rw [← Finset.sum_filter_add_sum_filter_not T0 (fun z => ‖z‖ = M)]
    simp only [ne_eq, add_sub_cancel_right]
  have hwU : w ∈ U := Finset.mem_filter.2 ⟨hwT0, hwM.symm⟩
  have := coeff_eq_zero_of_tendsto U c M hM (fun u hu => (Finset.mem_filter.1 hu).2) hUlim w hwU
  exact (Finset.mem_filter.1 hwT0).2 this


/-- The frozen form of `coeff_eq_zero_of_growth` (without `0 ≤ R`) is false: `T = {0}`, `c = 1`,
`R = −1`, `C = 0`. -/
theorem coeff_eq_zero_of_growth_frozen_false :
    ¬ ∀ (T : Finset ℂ) (c : ℂ → ℂ) (R C : ℝ) (k : ℕ),
      (∀ n : ℕ, 1 ≤ n → ‖∑ z ∈ T, c z * z ^ n‖ ≤ C * ((n : ℝ) + 1) ^ k * R ^ n) →
        ∀ z ∈ T, R < ‖z‖ → c z = 0 := by
  intro h
  have := h {0} (fun _ => 1) (-1) 0 0 (fun n hn => by simp [zero_pow (by omega : n ≠ 0)]) 0
    (by simp) (by norm_num)
  norm_num at this

/-! ## The approximate endgame -/

private theorem ofReal_ne_of_sq_lt' {x y : ℝ} (h : x ^ 2 < y ^ 2) : (x : ℂ) ≠ (y : ℂ) := by
  intro hxy
  rw [Complex.ofReal_injective hxy] at h
  exact lt_irrefl _ h

theorem false_of_package_approx (p : ℕ) (hp : 1 < p) (d e : ℕ) (hde : d ≤ e + 2)
    (K : Type*) [Field K] (ι : K →+* ℂ)
    (V : Fin (2 * d + 1) → Type*) [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
    [∀ i, FiniteDimensional K (V i)] (F : ∀ i, Module.End K (V i))
    (hw : ∀ i z, ((F i).charpoly.map ι).IsRoot z → ‖z‖ ≤ (p : ℝ) ^ (((10 : ℝ) + (i : ℕ)) / 2))
    (S : ℕ → ℤ)
    (htr : ∀ n : ℕ, 1 ≤ n →
      ∑ i : Fin (2 * d + 1), (-1 : K) ^ (i : ℕ) * LinearMap.trace K (V i) (F i ^ n) = (S n : K))
    (C : ℝ) (k : ℕ)
    (hS : ∀ n : ℕ, 1 ≤ n →
      |((S n - (p : ℤ) ^ (e * n) * ((p : ℤ) ^ n - 1) * (-1 - tauPowerSum p n) : ℤ) : ℝ)| ≤
        C * ((n : ℝ) + 1) ^ k * Real.sqrt p ^ ((2 * e + 13) * n))
    (α β : ℝ) (hsum : α + β = (RamanujanTau.tau p : ℝ)) (hprod : α * β = (p : ℝ) ^ 11)
    (hβ : (p : ℝ) ^ 11 < β ^ 2) : False := by
  classical
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp
  have hp0 : (0 : ℝ) < p := by linarith
  have hP : (0 : ℝ) < (p : ℝ) ^ 11 := by positivity
  have hP1 : (1 : ℝ) ≤ (p : ℝ) ^ 11 := one_le_pow₀ hp1.le
  have hα : α ^ 2 < (p : ℝ) ^ 11 := by
    by_contra hcon
    push Not at hcon
    have h1 : α ^ 2 * β ^ 2 = ((p : ℝ) ^ 11) ^ 2 := by rw [← mul_pow, hprod]
    nlinarith
  obtain ⟨Q, hQ⟩ : ∃ Q : ℝ, Q = (p : ℝ) ^ e := ⟨_, rfl⟩
  have hQ0 : 0 < Q := by rw [hQ]; positivity
  -- the six bases on the right-hand side
  obtain ⟨zA, hzA⟩ : ∃ z : ℂ, z = ((p * Q : ℝ) : ℂ) := ⟨_, rfl⟩
  obtain ⟨zB, hzB⟩ : ∃ z : ℂ, z = ((Q : ℝ) : ℂ) := ⟨_, rfl⟩
  obtain ⟨zC, hzC⟩ : ∃ z : ℂ, z = ((p * Q * α : ℝ) : ℂ) := ⟨_, rfl⟩
  obtain ⟨zw, hzw⟩ : ∃ z : ℂ, z = ((p * Q * β : ℝ) : ℂ) := ⟨_, rfl⟩
  obtain ⟨zE, hzE⟩ : ∃ z : ℂ, z = ((Q * α : ℝ) : ℂ) := ⟨_, rfl⟩
  obtain ⟨zG, hzG⟩ : ∃ z : ℂ, z = ((Q * β : ℝ) : ℂ) := ⟨_, rfl⟩
  have hMr : ∀ n : ℕ,
      (((p : ℤ) ^ (e * n) * ((p : ℤ) ^ n - 1) * (-1 - tauPowerSum p n) : ℤ) : ℂ) =
        -zA ^ n + zB ^ n - zC ^ n - zw ^ n + zE ^ n + zG ^ n := by
    intro n
    have h1 : (((p : ℤ) ^ (e * n) * ((p : ℤ) ^ n - 1) * (-1 - tauPowerSum p n) : ℤ) : ℝ) =
        -(p * Q) ^ n + Q ^ n - (p * Q * α) ^ n - (p * Q * β) ^ n +
        (Q * α) ^ n + (Q * β) ^ n := by
      push_cast
      rw [tauPowerSum_eq p α β hsum hprod n, pow_mul, ← hQ]
      ring
    rw [← Complex.ofReal_intCast, h1, hzA, hzB, hzC, hzw, hzE, hzG]
    push_cast
    ring
  -- spectral decomposition of every `F i` along `ι`
  choose s m hs hroot htrace using fun i => exists_trace_pow_decomp ι (F i)
  set T : Finset ℂ := (univ.biUnion s) ∪ {zA, zB, zC, zw, zE, zG} with hT
  set c : ℂ → ℂ := fun z => ∑ i : Fin (2 * d + 1), (-1 : ℂ) ^ (i : ℕ) * (m i z : ℂ) with hc
  set dd : ℂ → ℂ := fun z => (if z = zA then -1 else 0) + (if z = zB then 1 else 0) +
    (if z = zC then -1 else 0) + (if z = zw then -1 else 0) + (if z = zE then 1 else 0) +
    (if z = zG then 1 else 0) with hdd
  have hLHS : ∀ n : ℕ, 1 ≤ n → ∑ z ∈ T, c z * z ^ n = (S n : ℂ) := by
    intro n hn
    have h := congrArg ι (htr n hn)
    rw [map_sum, map_intCast] at h
    rw [← h]
    simp only [map_mul, map_pow, map_neg, map_one, htrace]
    have hsub : ∀ i, ∑ μ ∈ s i, (m i μ : ℂ) * μ ^ n = ∑ μ ∈ T, (m i μ : ℂ) * μ ^ n := by
      intro i
      apply Finset.sum_subset
      · intro μ hμ
        exact Finset.mem_union_left _ (Finset.mem_biUnion.2 ⟨i, Finset.mem_univ _, hμ⟩)
      · intro μ _ hμ
        simp [hs i μ hμ]
    simp_rw [hsub, Finset.mul_sum, hc, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun z _ => Finset.sum_congr rfl fun i _ => ?_
    ring
  have hmem : zA ∈ T ∧ zB ∈ T ∧ zC ∈ T ∧ zw ∈ T ∧ zE ∈ T ∧ zG ∈ T := by
    simp [hT]
  have hRHS : ∀ n : ℕ, ∑ z ∈ T, dd z * z ^ n = -zA ^ n + zB ^ n - zC ^ n - zw ^ n + zE ^ n + zG ^ n := by
    intro n
    simp only [hdd, add_mul, Finset.sum_add_distrib, ite_mul, zero_mul, Finset.sum_ite_eq',
      hmem.1, hmem.2.1, hmem.2.2.1, hmem.2.2.2.1,
      hmem.2.2.2.2.1, hmem.2.2.2.2.2, ↓reduceIte]
    ring
  have hgrowth : ∀ n : ℕ, 1 ≤ n → ‖∑ z ∈ T, (c z - dd z) * z ^ n‖ ≤
      C * ((n : ℝ) + 1) ^ k * (Real.sqrt p ^ (2 * e + 13)) ^ n := by
    intro n hn
    have : ∑ z ∈ T, (c z - dd z) * z ^ n =
        (((S n - (p : ℤ) ^ (e * n) * ((p : ℤ) ^ n - 1) * (-1 - tauPowerSum p n)) : ℤ) : ℂ) := by
      simp only [sub_mul, Finset.sum_sub_distrib]
      rw [hLHS n hn, hRHS n, Int.cast_sub, hMr n]
    rw [this, Complex.norm_intCast, ← pow_mul]
    exact hS n hn
  -- `zw = p^(e+1) β` differs from the other five bases (compare squares)
  have hβ1 : 1 < β ^ 2 := by linarith
  have hαβ : α ^ 2 < β ^ 2 := by linarith
  have hp2 : 1 < (p : ℝ) ^ 2 := by nlinarith
  have hQ2 : 0 < Q ^ 2 := by positivity
  have hwA : zw ≠ zA := by
    rw [hzw, hzA]; apply Ne.symm; apply ofReal_ne_of_sq_lt'
    rw [mul_pow (p * Q : ℝ)]; nlinarith [mul_pos (by positivity : (0:ℝ) < (p:ℝ) ^ 2) hQ2]
  have hwB : zw ≠ zB := by
    rw [hzw, hzB]; apply Ne.symm; apply ofReal_ne_of_sq_lt'
    rw [mul_pow, mul_pow]; nlinarith [mul_pos (by positivity : (0:ℝ) < (p:ℝ) ^ 2) hQ2]
  have hwC : zw ≠ zC := by
    rw [hzw, hzC]; apply Ne.symm; apply ofReal_ne_of_sq_lt'
    rw [mul_pow (p * Q : ℝ), mul_pow (p * Q : ℝ)]
    nlinarith [mul_pos (by positivity : (0:ℝ) < (p:ℝ) ^ 2) hQ2, mul_pow (p : ℝ) Q 2]
  have hwE : zw ≠ zE := by
    rw [hzw, hzE]; apply Ne.symm; apply ofReal_ne_of_sq_lt'
    rw [mul_pow, mul_pow, mul_pow]
    nlinarith [mul_pos hQ2 (by positivity : (0:ℝ) < β ^ 2)]
  have hwG : zw ≠ zG := by
    rw [hzw, hzG]; apply Ne.symm; apply ofReal_ne_of_sq_lt'
    rw [mul_pow, mul_pow, mul_pow]
    nlinarith [mul_pos hQ2 (by positivity : (0:ℝ) < β ^ 2)]
  -- net multiplicity of `zw` is `-1`
  have hwsq' : ‖zw‖ ^ 2 = (p : ℝ) ^ (2 * e + 2) * β ^ 2 := by
    rw [hzw, Complex.norm_real, Real.norm_eq_abs, sq_abs, hQ]
    ring
  have hRw : Real.sqrt p ^ (2 * e + 13) < ‖zw‖ := by
    refine lt_of_pow_lt_pow_left₀ 2 (norm_nonneg _) ?_
    rw [← pow_mul, mul_comm, pow_mul, Real.sq_sqrt hp0.le, hwsq',
      show 2 * e + 13 = (2 * e + 2) + 11 by ring, pow_add]
    exact mul_lt_mul_of_pos_left hβ (by positivity)
  have hcw : c zw - dd zw = 0 :=
    coeff_eq_zero_of_growth T (fun z => c z - dd z) _ C k (by positivity) hgrowth zw
      hmem.2.2.2.1 hRw
  have hddw : dd zw = -1 := by
    simp [hdd, hwA, hwB, hwC, hwE, hwG]
  have hcZ : ∑ i : Fin (2 * d + 1), (-1 : ℤ) ^ (i : ℕ) * (m i zw : ℤ) = -1 := by
    have h1 : ((∑ i : Fin (2 * d + 1), (-1 : ℤ) ^ (i : ℕ) * (m i zw : ℤ) : ℤ) : ℂ) = c zw := by
      simp [hc]
    have h2 : c zw = -1 := by rw [← hddw]; exact sub_eq_zero.1 hcw
    exact_mod_cast h1.trans h2
  -- hence `zw` is an eigenvalue in some odd degree
  obtain ⟨i, hodd, hi⟩ : ∃ i : Fin (2 * d + 1), Odd (i : ℕ) ∧ m i zw ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have : 0 ≤ ∑ i : Fin (2 * d + 1), (-1 : ℤ) ^ (i : ℕ) * (m i zw : ℤ) := by
      apply Finset.sum_nonneg
      intro i _
      rcases Nat.even_or_odd (i : ℕ) with he | ho
      · rw [he.neg_one_pow]; positivity
      · rw [hcon i ho]; simp
    omega
  have hnorm := hw i zw (hroot i zw hi)
  have hi_le : (i : ℕ) + 1 ≤ 2 * d := by
    have := i.isLt
    obtain ⟨k, hk⟩ := hodd
    omega
  have hsq : ‖zw‖ ^ 2 ≤ (p : ℝ) ^ (10 + (i : ℕ)) := by
    calc ‖zw‖ ^ 2 ≤ ((p : ℝ) ^ (((10 : ℝ) + (i : ℕ)) / 2)) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) hnorm 2
      _ = (p : ℝ) ^ (10 + (i : ℕ)) := by
        rw [← Real.rpow_natCast _ 2, ← Real.rpow_mul hp0.le, ← Real.rpow_natCast]
        congr 1
        push_cast
        ring
  have hwsq : ‖zw‖ ^ 2 = (p : ℝ) ^ (2 * e + 2) * β ^ 2 := by
    rw [hzw, Complex.norm_real, Real.norm_eq_abs, sq_abs, hQ]
    ring
  have hmono : (p : ℝ) ^ (10 + (i : ℕ)) ≤ (p : ℝ) ^ (2 * e + 13) :=
    pow_le_pow_right₀ hp1.le (by omega)
  have hbig : (p : ℝ) ^ (2 * e + 13) < (p : ℝ) ^ (2 * e + 2) * β ^ 2 := by
    rw [show 2 * e + 13 = (2 * e + 2) + 11 by ring, pow_add]
    exact mul_lt_mul_of_pos_left hβ (by positivity)
  linarith


/-- **M1′, generalized.** `deligne_of_package_gen` with the exact identity replaced by a growth
bound `|S n − main n| ≤ C (n+1)^k (√p)^{(2e+13)n}` (only `d ≤ e + 2` and `1 < p` are used). -/
theorem deligne_of_package_approx_gen (p : ℕ) (hp : 1 < p) (d e : ℕ) (hde : d ≤ e + 2)
    (K : Type*) [Field K] (ι : K →+* ℂ)
    (V : Fin (2 * d + 1) → Type*) [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
    [∀ i, FiniteDimensional K (V i)] (F : ∀ i, Module.End K (V i))
    (hw : ∀ i z, ((F i).charpoly.map ι).IsRoot z → ‖z‖ ≤ (p : ℝ) ^ (((10 : ℝ) + (i : ℕ)) / 2))
    (S : ℕ → ℤ)
    (htr : ∀ n : ℕ, 1 ≤ n →
      ∑ i : Fin (2 * d + 1), (-1 : K) ^ (i : ℕ) * LinearMap.trace K (V i) (F i ^ n) = (S n : K))
    (hS : ∃ C : ℝ, ∃ k : ℕ, ∀ n : ℕ, 1 ≤ n →
      |((S n - (p : ℤ) ^ (e * n) * ((p : ℤ) ^ n - 1) * (-1 - tauPowerSum p n) : ℤ) : ℝ)| ≤
        C * ((n : ℝ) + 1) ^ k * Real.sqrt p ^ ((2 * e + 13) * n)) :
    RamanujanTau.tau p ^ 2 ≤ 4 * (p : ℤ) ^ 11 := by
  obtain ⟨C, k, hS⟩ := hS
  by_contra hlt
  push Not at hlt
  set t : ℝ := (RamanujanTau.tau p : ℝ) with ht
  have hlt' : 4 * (p : ℝ) ^ 11 < t ^ 2 := by rw [ht]; exact_mod_cast hlt
  have hP : (0 : ℝ) < (p : ℝ) ^ 11 := by positivity
  set D : ℝ := t ^ 2 - 4 * (p : ℝ) ^ 11 with hD
  have hD0 : 0 < D := by rw [hD]; linarith
  set r : ℝ := Real.sqrt D with hr
  have hr0 : 0 < r := Real.sqrt_pos.2 hD0
  have hr2 : r ^ 2 = D := Real.sq_sqrt hD0.le
  have hsum : (t - r) / 2 + (t + r) / 2 = t := by ring
  have hprod : (t - r) / 2 * ((t + r) / 2) = (p : ℝ) ^ 11 := by
    have : (t - r) / 2 * ((t + r) / 2) = (t ^ 2 - r ^ 2) / 4 := by ring
    rw [this, hr2, hD]; ring
  rcases lt_or_gt_of_ne (show t ≠ 0 by rintro h0; rw [h0] at hlt'; linarith) with htn | htp
  · refine false_of_package_approx p hp d e hde K ι V F hw S htr C k hS ((t + r) / 2)
      ((t - r) / 2) (by rw [← ht]; ring) (by rw [mul_comm]; exact hprod) ?_
    nlinarith
  · refine false_of_package_approx p hp d e hde K ι V F hw S htr C k hS ((t - r) / 2)
      ((t + r) / 2) (by rw [← ht]; exact hsum) hprod ?_
    nlinarith

/-- **M1′ (frozen statement, `scratch/ArithInterfaces.lean`).** The endgame with a growth
hypothesis: same package as `deligne_of_package'`, with `hS` weakened to
`S n = main n + O((n+1)^k (√p)^{(2(d−2)+13)n})`. -/
theorem deligne_of_package_approx (p : ℕ) [Fact p.Prime] (d : ℕ) (K : Type) [Field K]
    (ι : K →+* ℂ)
    (V : Fin (2 * d + 1) → Type) [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
    [∀ i, FiniteDimensional K (V i)] (F : ∀ i, Module.End K (V i))
    (hw : ∀ i z, ((F i).charpoly.map ι).IsRoot z → ‖z‖ ≤ (p : ℝ) ^ (((10 : ℝ) + (i : ℕ)) / 2))
    (S : ℕ → ℤ)
    (htr : ∀ n : ℕ, 1 ≤ n →
      ∑ i : Fin (2 * d + 1), (-1 : K) ^ (i : ℕ) * LinearMap.trace K (V i) (F i ^ n) = (S n : K))
    (hS : ∃ C : ℝ, ∃ k : ℕ, ∀ n : ℕ, 1 ≤ n →
      |((S n - (p : ℤ) ^ ((d - 2) * n) * ((p : ℤ) ^ n - 1) * (-1 - tauPowerSum p n) : ℤ) : ℝ)| ≤
        C * ((n : ℝ) + 1) ^ k * Real.sqrt p ^ ((2 * (d - 2) + 13) * n)) :
    RamanujanTau.tau p ^ 2 ≤ 4 * (p : ℤ) ^ 11 :=
  deligne_of_package_approx_gen p (Fact.out : p.Prime).one_lt d (d - 2) (by omega) K ι V F hw S
    htr hS

/-! ## The approximate Ihara–Birch identity -/

/-- **Approximate Ihara–Birch identity** (frozen, `scratch/ArithInterfaces.lean`). Error allowed
up to `(n+1)^k p^{19n/2}`: strictly below the dominant base `p⁴β` (`|β| > p^{11/2}` under a
violation). -/
def IharaApprox (p : ℕ) [Fact p.Prime] : Prop :=
  ∃ C : ℝ, ∃ k : ℕ, ∀ n : ℕ, 1 ≤ n →
    |((weierstrassSum p n -
        (p : ℤ) ^ (3 * n) * ((p : ℤ) ^ n - 1) * (-1 - tauPowerSum p n) : ℤ) : ℝ)| ≤
      C * ((n : ℝ) + 1) ^ k * Real.sqrt p ^ (19 * n)

/-- The exact identity implies the approximate one (`C = 0`). -/
theorem iharaApprox_of_iharaIdentity (p : ℕ) [Fact p.Prime] (h : IharaIdentity p) :
    IharaApprox p :=
  ⟨0, 0, fun n hn => by
    have := weierstrassSum_eq_of_ihara h n hn
    rw [show (5 - 2) * n = 3 * n by norm_num] at this
    rw [this, sub_self]
    simp⟩

/-- **Hand-off for the Weil closure.** A package of dimension `d = 5` whose alternating traces
are the Weierstrass sums, plus `IharaApprox p`, forces `τ(p)² ≤ 4p¹¹`. (`FinalApprox.lean` feeds
this the `Sym¹⁰ R¹` package on `W_p`.) -/
theorem deligne_of_package_iharaApprox (p : ℕ) [Fact p.Prime] (K : Type) [Field K]
    (ι : K →+* ℂ)
    (V : Fin (2 * 5 + 1) → Type) [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
    [∀ i, FiniteDimensional K (V i)] (F : ∀ i, Module.End K (V i))
    (hw : ∀ i z, ((F i).charpoly.map ι).IsRoot z → ‖z‖ ≤ (p : ℝ) ^ (((10 : ℝ) + (i : ℕ)) / 2))
    (htr : ∀ n : ℕ, 1 ≤ n →
      ∑ i : Fin (2 * 5 + 1), (-1 : K) ^ (i : ℕ) * LinearMap.trace K (V i) (F i ^ n) =
        (weierstrassSum p n : K))
    (hA : IharaApprox p) :
    RamanujanTau.tau p ^ 2 ≤ 4 * (p : ℤ) ^ 11 :=
  deligne_of_package_approx p 5 K ι V F hw (weierstrassSum p) htr hA

/-! ## Sanity checks -/

/-- Contrapositive: under a violation, no package satisfies the approximate identity. -/
theorem no_package_approx_of_violation (p : ℕ) [Fact p.Prime] (d : ℕ) (K : Type) [Field K]
    (ι : K →+* ℂ) (V : Fin (2 * d + 1) → Type) [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
    [∀ i, FiniteDimensional K (V i)] (F : ∀ i, Module.End K (V i))
    (hw : ∀ i z, ((F i).charpoly.map ι).IsRoot z → ‖z‖ ≤ (p : ℝ) ^ (((10 : ℝ) + (i : ℕ)) / 2))
    (S : ℕ → ℤ)
    (htr : ∀ n : ℕ, 1 ≤ n →
      ∑ i : Fin (2 * d + 1), (-1 : K) ^ (i : ℕ) * LinearMap.trace K (V i) (F i ^ n) = (S n : K))
    (hviol : 4 * (p : ℤ) ^ 11 < RamanujanTau.tau p ^ 2) :
    ¬ ∃ C : ℝ, ∃ k : ℕ, ∀ n : ℕ, 1 ≤ n →
      |((S n - (p : ℤ) ^ ((d - 2) * n) * ((p : ℤ) ^ n - 1) * (-1 - tauPowerSum p n) : ℤ) : ℝ)| ≤
        C * ((n : ℝ) + 1) ^ k * Real.sqrt p ^ ((2 * (d - 2) + 13) * n) :=
  fun h => absurd (deligne_of_package_approx p d K ι V F hw S htr h) (not_le.2 hviol)

end RamanujanWeil.Ihara
