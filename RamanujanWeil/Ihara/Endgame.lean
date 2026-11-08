import RamanujanWeil.Tau
import Mathlib.LinearAlgebra.Charpoly.BaseChange
import Mathlib.LinearAlgebra.Eigenspace.Charpoly
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.Algebra.DirectSum.LinearMap
import Mathlib.LinearAlgebra.Trace
import Mathlib.LinearAlgebra.LinearIndependent.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# M1: the endgame of the Ihara route (Mathlib only)

This file proves `RamanujanWeil.Ihara.deligne_of_package`, the frozen M1 statement of
`docs/REALIZATION_PLAN.md` (copied verbatim from `scratch/ProbeInterfaces.lean`): a weighted
Lefschetz package (finitely many finite-dimensional `K`-spaces `V i`, `i < 2d+1`, with
endomorphisms whose eigenvalues along `ι : K →+* ℂ` have absolute value `≤ p^((10+i)/2)`, and
whose alternating traces of powers equal `S n`) together with the Ihara identity
`S n = p^((d-2)n) (pⁿ - 1) (-1 - (αⁿ + βⁿ))` forces `τ(p)² ≤ 4 p¹¹`.

## Structure

* `trace_pow_eq_sum_maxGenEigenspace`: over `ℂ`, `tr(fⁿ) = Σ_μ dim(maxGenEigenspace μ) · μⁿ`.
* `exists_trace_pow_decomp`: the same, read along `ι` after base change `ℂ ⊗_{K,ι} V`; every
  `μ` of positive multiplicity is a root of `charpoly(f).map ι`.
* `coeff_eq_zero_of_sum_pow_eq_zero`: uniqueness of exponential sums
  (`Σ_z c_z zⁿ = 0` for all `n ≥ 1` ⇒ `c_z = 0` for `z ≠ 0`), via Dedekind's independence of
  characters `linearIndependent_monoidHom` applied to `n ↦ zⁿ : Multiplicative ℕ →* ℂ`.
* `tauPowerSum_eq`: `s_n = αⁿ + βⁿ` for real `α, β` with `α + β = τ(p)`, `αβ = p¹¹`.
* `deligne_of_package_gen`: the argument of plan §3 with a general exponent `e` (`d ≤ e + 2`)
  and `1 < p` in place of primality.
* `deligne_of_package`: the frozen statement.
-/

open Finset Polynomial Module TensorProduct

namespace RamanujanWeil.Ihara

/-! ## Frozen definitions (verbatim from `scratch/ProbeInterfaces.lean`) -/

/-- `tr Sym^k g` for a `2 × 2` matrix `g` with trace `a` and determinant `q`. -/
def symTrace (k : ℕ) (a q : ℤ) : ℤ :=
  ∑ j ∈ range (k / 2 + 1), (-q) ^ j * ((k - j).choose j : ℤ) * a ^ (k - 2 * j)

/-- `s_n = αⁿ + βⁿ` for the roots of `X² − τ(p) X + p¹¹`. -/
def tauPowerSum (p : ℕ) : ℕ → ℤ
  | 0 => 2
  | 1 => RamanujanTau.tau p
  | n + 2 => RamanujanTau.tau p * tauPowerSum p (n + 1) - (p : ℤ) ^ 11 * tauPowerSum p n

/-! ## Traces of powers via generalized eigenspaces -/

section TracePow

variable {W : Type*} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]

/-- On the generalized `μ`-eigenspace, `tr(fⁿ) = dim · μⁿ`. -/
theorem trace_pow_restrict_maxGenEigenspace (f : End ℂ W) (μ : ℂ) (n : ℕ) :
    LinearMap.trace ℂ _ ((f ^ n).restrict
        (f.mapsTo_maxGenEigenspace_of_comm ((Commute.refl f).pow_right n) μ)) =
      (finrank ℂ (f.maxGenEigenspace μ) : ℂ) * μ ^ n := by
  set g : End ℂ (f.maxGenEigenspace μ) :=
    f.restrict (f.mapsTo_maxGenEigenspace_of_comm (Commute.refl f) μ) with hg
  have hnil : IsNilpotent (g - algebraMap ℂ _ μ) := by
    have := f.isNilpotent_restrict_maxGenEigenspace_sub_algebraMap μ
    convert this using 1
    ext x
    simp only [g, LinearMap.sub_apply, Submodule.coe_sub, Module.algebraMap_end_apply,
      Submodule.coe_smul]
    change f x - μ • (x : W) = (f - algebraMap ℂ (End ℂ W) μ) x
    simp [Module.algebraMap_end_apply]
  have hpow : ∀ k : ℕ, (f ^ k).restrict
      (f.mapsTo_maxGenEigenspace_of_comm ((Commute.refl f).pow_right k) μ) = g ^ k := by
    intro k
    exact (Module.End.pow_restrict k _).symm
  rw [hpow]
  induction n with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, Module.End.mul_eq_comp,
      LinearMap.trace_comp_eq_mul_of_commute_of_isNilpotent μ ((Commute.refl g).pow_left k) hnil, ih]
    ring

/-- **Traces of powers are power sums of generalized eigenvalues** (over `ℂ`). -/
theorem trace_pow_eq_sum_maxGenEigenspace (f : End ℂ W) :
    ∃ s : Finset ℂ, (∀ μ ∉ s, f.maxGenEigenspace μ = ⊥) ∧ ∀ n : ℕ,
      LinearMap.trace ℂ W (f ^ n) = ∑ μ ∈ s, (finrank ℂ (f.maxGenEigenspace μ) : ℂ) * μ ^ n := by
  classical
  have hds := DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    f.independent_maxGenEigenspace (Module.End.iSup_maxGenEigenspace_eq_top f)
  have h_fin : {μ | f.maxGenEigenspace μ ≠ ⊥}.Finite :=
    WellFoundedGT.finite_ne_bot_of_iSupIndep f.independent_maxGenEigenspace
  refine ⟨h_fin.toFinset, fun μ hμ => by simpa using hμ, fun n => ?_⟩
  rw [LinearMap.trace_eq_sum_trace_restrict' hds h_fin
    (fun μ => f.mapsTo_maxGenEigenspace_of_comm ((Commute.refl f).pow_right n) μ)]
  exact Finset.sum_congr rfl fun μ _ => trace_pow_restrict_maxGenEigenspace f μ n

end TracePow

section BaseChange

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- **Traces of powers along `ι`.** For `f : End K V` and `ι : K →+* ℂ` there are finitely many
complex numbers `μ` with multiplicities `m μ` such that `ι (tr fⁿ) = Σ m μ · μⁿ` for all `n`, and
every `μ` of positive multiplicity is a root of `charpoly(f)` read along `ι`. -/
theorem exists_trace_pow_decomp (ι : K →+* ℂ) (f : End K V) :
    ∃ (s : Finset ℂ) (m : ℂ → ℕ), (∀ μ ∉ s, m μ = 0) ∧
      (∀ μ, m μ ≠ 0 → (f.charpoly.map ι).IsRoot μ) ∧
      ∀ n : ℕ, ι (LinearMap.trace K V (f ^ n)) = ∑ μ ∈ s, (m μ : ℂ) * μ ^ n := by
  let _ : Algebra K ℂ := ι.toAlgebra
  have hι : algebraMap K ℂ = ι := rfl
  set g : End ℂ (ℂ ⊗[K] V) := f.baseChange ℂ
  obtain ⟨s, hs, htr⟩ := trace_pow_eq_sum_maxGenEigenspace g
  refine ⟨s, fun μ => finrank ℂ (g.maxGenEigenspace μ), fun μ hμ => by simp [hs μ hμ],
    fun μ hμ => ?_, fun n => ?_⟩
  · have hne : g.maxGenEigenspace μ ≠ ⊥ := fun h => hμ (by simp [h])
    have hev : g.HasEigenvalue μ :=
      (Module.End.hasUnifEigenvalue_iff_hasUnifEigenvalue_one (by simp)).1 hne
    have := (Module.End.hasEigenvalue_iff_isRoot_charpoly g μ).1 hev
    rwa [LinearMap.charpoly_baseChange, hι] at this
  · rw [← hι, ← LinearMap.trace_baseChange, LinearMap.baseChange_pow]
    exact htr n

end BaseChange

/-! ## Uniqueness of exponential sums -/

/-- **Uniqueness of exponential sums.** If `Σ_{z ∈ T} c z · zⁿ = 0` for all `n ≥ 1`, then
`c z = 0` for every nonzero `z ∈ T`. (Dedekind independence of the characters `n ↦ zⁿ`.) -/
theorem coeff_eq_zero_of_sum_pow_eq_zero (T : Finset ℂ) (c : ℂ → ℂ)
    (h : ∀ n : ℕ, 1 ≤ n → ∑ z ∈ T, c z * z ^ n = 0) :
    ∀ z ∈ T, z ≠ 0 → c z = 0 := by
  have hli : LinearIndependent ℂ (fun z : ℂ => ((powersHom ℂ z : Multiplicative ℕ →* ℂ) :
      Multiplicative ℕ → ℂ)) :=
    (linearIndependent_monoidHom (Multiplicative ℕ) ℂ).comp (powersHom ℂ)
      (powersHom ℂ).injective
  have key := linearIndependent_iff'.1 hli T (fun z => c z * z) (by
    funext m
    simp only [Finset.sum_apply, Pi.smul_apply, powersHom_apply, smul_eq_mul, Pi.zero_apply]
    have := h (m.toAdd + 1) (by omega)
    rw [← this]
    refine Finset.sum_congr rfl fun z _ => ?_
    ring)
  intro z hz hz0
  have := key z hz
  simpa [hz0] using this


/-! ## The power sums `s_n = αⁿ + βⁿ` -/

/-- If `α + β = τ(p)` and `αβ = p¹¹` (over `ℝ`), then `tauPowerSum p n = αⁿ + βⁿ`. -/
theorem tauPowerSum_eq (p : ℕ) (α β : ℝ) (hs : α + β = (RamanujanTau.tau p : ℝ))
    (hp : α * β = (p : ℝ) ^ 11) : ∀ n : ℕ, (tauPowerSum p n : ℝ) = α ^ n + β ^ n
  | 0 => by norm_num [tauPowerSum]
  | 1 => by simp [tauPowerSum, hs]
  | n + 2 => by
    rw [tauPowerSum]
    push_cast
    rw [tauPowerSum_eq p α β hs hp (n + 1), tauPowerSum_eq p α β hs hp n, ← hs, ← hp]
    ring

/-! ## The endgame -/

private theorem ofReal_ne_of_sq_lt {x y : ℝ} (h : x ^ 2 < y ^ 2) : (x : ℂ) ≠ (y : ℂ) := by
  intro hxy
  rw [Complex.ofReal_injective hxy] at h
  exact lt_irrefl _ h

/-- **Core of the endgame (plan §3).** A weighted Lefschetz package whose alternating traces are
`p^(en) (pⁿ - 1)(-1 - αⁿ - βⁿ)`, with `α + β = τ(p)`, `αβ = p¹¹` real and `β² > p¹¹`, and with
`d ≤ e + 2`, cannot exist. -/
theorem false_of_package (p : ℕ) (hp : 1 < p) (d e : ℕ) (hde : d ≤ e + 2)
    (K : Type*) [Field K] (ι : K →+* ℂ)
    (V : Fin (2 * d + 1) → Type*) [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
    [∀ i, FiniteDimensional K (V i)] (F : ∀ i, Module.End K (V i))
    (hw : ∀ i z, ((F i).charpoly.map ι).IsRoot z → ‖z‖ ≤ (p : ℝ) ^ (((10 : ℝ) + (i : ℕ)) / 2))
    (S : ℕ → ℤ)
    (htr : ∀ n : ℕ, 1 ≤ n →
      ∑ i : Fin (2 * d + 1), (-1 : K) ^ (i : ℕ) * LinearMap.trace K (V i) (F i ^ n) = (S n : K))
    (hS : ∀ n : ℕ, 1 ≤ n →
      S n = (p : ℤ) ^ (e * n) * ((p : ℤ) ^ n - 1) * (-1 - tauPowerSum p n))
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
  have hSr : ∀ n : ℕ, 1 ≤ n →
      (S n : ℂ) = -zA ^ n + zB ^ n - zC ^ n - zw ^ n + zE ^ n + zG ^ n := by
    intro n hn
    have h1 : (S n : ℝ) = -(p * Q) ^ n + Q ^ n - (p * Q * α) ^ n - (p * Q * β) ^ n +
        (Q * α) ^ n + (Q * β) ^ n := by
      rw [hS n hn]
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
  have hzero : ∀ n : ℕ, 1 ≤ n → ∑ z ∈ T, (c z - dd z) * z ^ n = 0 := by
    intro n hn
    simp only [sub_mul, Finset.sum_sub_distrib]
    rw [hLHS n hn, hRHS n, hSr n hn]
    ring
  -- `zw = p^(e+1) β` differs from the other five bases (compare squares)
  have hβ1 : 1 < β ^ 2 := by linarith
  have hαβ : α ^ 2 < β ^ 2 := by linarith
  have hp2 : 1 < (p : ℝ) ^ 2 := by nlinarith
  have hQ2 : 0 < Q ^ 2 := by positivity
  have hwA : zw ≠ zA := by
    rw [hzw, hzA]; apply Ne.symm; apply ofReal_ne_of_sq_lt
    rw [mul_pow (p * Q : ℝ)]; nlinarith [mul_pos (by positivity : (0:ℝ) < (p:ℝ) ^ 2) hQ2]
  have hwB : zw ≠ zB := by
    rw [hzw, hzB]; apply Ne.symm; apply ofReal_ne_of_sq_lt
    rw [mul_pow, mul_pow]; nlinarith [mul_pos (by positivity : (0:ℝ) < (p:ℝ) ^ 2) hQ2]
  have hwC : zw ≠ zC := by
    rw [hzw, hzC]; apply Ne.symm; apply ofReal_ne_of_sq_lt
    rw [mul_pow (p * Q : ℝ), mul_pow (p * Q : ℝ)]
    nlinarith [mul_pos (by positivity : (0:ℝ) < (p:ℝ) ^ 2) hQ2, mul_pow (p : ℝ) Q 2]
  have hwE : zw ≠ zE := by
    rw [hzw, hzE]; apply Ne.symm; apply ofReal_ne_of_sq_lt
    rw [mul_pow, mul_pow, mul_pow]
    nlinarith [mul_pos hQ2 (by positivity : (0:ℝ) < β ^ 2)]
  have hwG : zw ≠ zG := by
    rw [hzw, hzG]; apply Ne.symm; apply ofReal_ne_of_sq_lt
    rw [mul_pow, mul_pow, mul_pow]
    nlinarith [mul_pos hQ2 (by positivity : (0:ℝ) < β ^ 2)]
  have hw0 : zw ≠ 0 := by
    rw [hzw]
    have : (p : ℝ) * Q * β ≠ 0 := by
      have : β ≠ 0 := by rintro rfl; norm_num at hβ1
      positivity
    exact_mod_cast this
  -- net multiplicity of `zw` is `-1`
  have hcw : c zw - dd zw = 0 := coeff_eq_zero_of_sum_pow_eq_zero T _ hzero zw hmem.2.2.2.1 hw0
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

/-- **M1, generalized.** Same conclusion as `deligne_of_package` with the base dimension `d`
decoupled from the exponent `e` of the Ihara identity (only `d ≤ e + 2` is used), and `p > 1` in
place of primality. -/
theorem deligne_of_package_gen (p : ℕ) (hp : 1 < p) (d e : ℕ) (hde : d ≤ e + 2)
    (K : Type*) [Field K] (ι : K →+* ℂ)
    (V : Fin (2 * d + 1) → Type*) [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
    [∀ i, FiniteDimensional K (V i)] (F : ∀ i, Module.End K (V i))
    (hw : ∀ i z, ((F i).charpoly.map ι).IsRoot z → ‖z‖ ≤ (p : ℝ) ^ (((10 : ℝ) + (i : ℕ)) / 2))
    (S : ℕ → ℤ)
    (htr : ∀ n : ℕ, 1 ≤ n →
      ∑ i : Fin (2 * d + 1), (-1 : K) ^ (i : ℕ) * LinearMap.trace K (V i) (F i ^ n) = (S n : K))
    (hS : ∀ n : ℕ, 1 ≤ n →
      S n = (p : ℤ) ^ (e * n) * ((p : ℤ) ^ n - 1) * (-1 - tauPowerSum p n)) :
    RamanujanTau.tau p ^ 2 ≤ 4 * (p : ℤ) ^ 11 := by
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
  · -- `t < 0`: the large root is `(t - r)/2`
    refine false_of_package p hp d e hde K ι V F hw S htr hS ((t + r) / 2) ((t - r) / 2)
      (by rw [← ht]; ring) (by rw [mul_comm]; exact hprod) ?_
    nlinarith
  · refine false_of_package p hp d e hde K ι V F hw S htr hS ((t - r) / 2) ((t + r) / 2)
      (by rw [← ht]; exact hsum) hprod ?_
    nlinarith

/-- **M1 (frozen statement, verbatim from `scratch/ProbeInterfaces.lean`).** A weighted Lefschetz
package for the sum `S` plus the Ihara identity forces `τ(p)² ≤ 4 p¹¹`. The hypothesis `hd` is
not needed (see `deligne_of_package_gen`). -/
theorem deligne_of_package (p : ℕ) [Fact p.Prime] (d : ℕ) (hd : 2 ≤ d) (K : Type) [Field K] (ι : K →+* ℂ)
    (V : Fin (2 * d + 1) → Type) [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
    [∀ i, FiniteDimensional K (V i)] (F : ∀ i, Module.End K (V i))
    (hw : ∀ i z, ((F i).charpoly.map ι).IsRoot z → ‖z‖ ≤ (p : ℝ) ^ (((10 : ℝ) + (i : ℕ)) / 2))
    (S : ℕ → ℤ)
    (htr : ∀ n : ℕ, 1 ≤ n →
      ∑ i : Fin (2 * d + 1), (-1 : K) ^ (i : ℕ) * LinearMap.trace K (V i) (F i ^ n) = (S n : K))
    (hS : ∀ n : ℕ, 1 ≤ n →
      S n = (p : ℤ) ^ ((d - 2) * n) * ((p : ℤ) ^ n - 1) * (-1 - tauPowerSum p n)) :
    RamanujanTau.tau p ^ 2 ≤ 4 * (p : ℤ) ^ 11 :=
  deligne_of_package_gen p (Fact.out : p.Prime).one_lt d (d - 2) (by omega) K ι V F hw S htr hS

/-- `hd` dropped: the frozen statement holds for every `d`. -/
theorem deligne_of_package' (p : ℕ) [Fact p.Prime] (d : ℕ) (K : Type) [Field K] (ι : K →+* ℂ)
    (V : Fin (2 * d + 1) → Type) [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
    [∀ i, FiniteDimensional K (V i)] (F : ∀ i, Module.End K (V i))
    (hw : ∀ i z, ((F i).charpoly.map ι).IsRoot z → ‖z‖ ≤ (p : ℝ) ^ (((10 : ℝ) + (i : ℕ)) / 2))
    (S : ℕ → ℤ)
    (htr : ∀ n : ℕ, 1 ≤ n →
      ∑ i : Fin (2 * d + 1), (-1 : K) ^ (i : ℕ) * LinearMap.trace K (V i) (F i ^ n) = (S n : K))
    (hS : ∀ n : ℕ, 1 ≤ n →
      S n = (p : ℤ) ^ ((d - 2) * n) * ((p : ℤ) ^ n - 1) * (-1 - tauPowerSum p n)) :
    RamanujanTau.tau p ^ 2 ≤ 4 * (p : ℤ) ^ 11 :=
  deligne_of_package_gen p (Fact.out : p.Prime).one_lt d (d - 2) (by omega) K ι V F hw S htr hS

/-! ## Sanity checks -/

theorem tauPowerSum_zero (p : ℕ) : tauPowerSum p 0 = 2 := rfl

theorem tauPowerSum_one (p : ℕ) : tauPowerSum p 1 = RamanujanTau.tau p := rfl

theorem tauPowerSum_two (p : ℕ) :
    tauPowerSum p 2 = RamanujanTau.tau p ^ 2 - 2 * (p : ℤ) ^ 11 := by
  simp [tauPowerSum]; ring

/-- `Sym⁰`, `Sym¹`, `Sym²` traces: `1`, `a`, `a² - q`. -/
theorem symTrace_small (a q : ℤ) :
    symTrace 0 a q = 1 ∧ symTrace 1 a q = a ∧ symTrace 2 a q = a ^ 2 - q := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [symTrace, Finset.sum_range_succ]
  ring

/-- Contrapositive form: if `τ(p)² > 4p¹¹`, no weighted Lefschetz package realizes the Ihara
sum. -/
theorem no_package_of_violation (p : ℕ) [Fact p.Prime] (d : ℕ) (K : Type) [Field K]
    (ι : K →+* ℂ) (V : Fin (2 * d + 1) → Type) [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
    [∀ i, FiniteDimensional K (V i)] (F : ∀ i, Module.End K (V i))
    (hw : ∀ i z, ((F i).charpoly.map ι).IsRoot z → ‖z‖ ≤ (p : ℝ) ^ (((10 : ℝ) + (i : ℕ)) / 2))
    (hviol : 4 * (p : ℤ) ^ 11 < RamanujanTau.tau p ^ 2) :
    ¬ ∀ n : ℕ, 1 ≤ n →
      ∑ i : Fin (2 * d + 1), (-1 : K) ^ (i : ℕ) * LinearMap.trace K (V i) (F i ^ n) =
        (((p : ℤ) ^ ((d - 2) * n) * ((p : ℤ) ^ n - 1) * (-1 - tauPowerSum p n) : ℤ) : K) :=
  fun h => absurd (deligne_of_package' p d K ι V F hw _ h (fun _ _ => rfl)) (not_le.2 hviol)

end RamanujanWeil.Ihara
