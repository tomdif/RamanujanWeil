import RamanujanWeil.Arith.AssemblyIhara
import RamanujanWeil.Arith.DeuringApproxKH

/-!
# A3-ord, approximate form: `OrdinaryDeuringApprox` suffices for `IharaApprox`

`IharaApprox p` (`EndgameApprox.lean`) tolerates an error `C (n+1)^k (√p)^{19n}` in
`S(n) − q³(q−1)(−1 − s_n)`. The ordinary part of `S(n)` is `Σ_{p ∤ t} N(t)·h₁₀(t, q)` with
`|h₁₀(t, q)| ≤ 2876 q⁵` (Hasse). So an `ℓ¹` error `O((n+1)^k q^{9/2})` in the ordinary per-trace
counts `N(t) = traceCount p n t` against `q³(q−1)H(4q−t²)/2` costs only `O((n+1)^k q^{19/2})`.

* `OrdinaryDeuringApprox H p` : `Σ_{t² ≤ 4q, p ∤ t} |N(t) − q³(q−1)H(4q−t²)/2| ≤ C(n+1)^k (√p)^{9n}`;
* `ordinaryDeuringApprox_of_exact` : `OrdinaryDeuring H p → OrdinaryDeuringApprox H p`;
* **`iharaApprox_of_deuringApprox`** : the R-ord assembly with `OrdinaryDeuring` weakened to
  `OrdinaryDeuringApprox`.

The structural interface (`DeuringMultiplicity`):
`N(t) = q³(q−1)·m(t)·H(4q−t²)/2` for `p ∤ t`, `t² < 4q`, with `m(t) ∈ ℕ` (the number of
ordinary isogeny classes of trace `t`). Together with a Kronecker–Hurwitz bound on
`O₀(n) = Σ_{p ∤ t} H(4q − t²)`:

* **existence** (`m ≥ 1`) + `O₀(n) ≥ 2q − C(n+1)^k (√p)ⁿ` + the trivial `Σ N(t) ≤ q⁵`
  ⇒ `OrdinaryDeuringApprox` (`ordinaryDeuringApprox_of_mult_exists`);
* **uniqueness** (`m ≤ 1`) + `O₀(n) ≤ 2q + C(n+1)^k (√p)ⁿ` + `Σ N(t) ≥ q⁵ − C'q⁴`
  ⇒ `OrdinaryDeuringApprox` (`ordinaryDeuringApprox_of_mult_unique`); the lower bound on the
  ordinary tuple count is `ordinaryTupleCount_lower` (`DeuringApproxCount.lean`).

For `H = hurwitz` both Kronecker–Hurwitz bounds are proved (`ordSum0_bound`).
-/

open Finset

namespace RamanujanWeil.ArithPlan

open RamanujanWeil.Ihara

set_option linter.unusedSectionVars false

/-- **Approximate ordinary Deuring–Waterhouse.** The ordinary per-trace counts agree with
`q³(q−1)H(4q−t²)/2` up to an `ℓ¹` error `C (n+1)^k (√p)^{9n} = C (n+1)^k q^{9/2}`. Here
`tset p n = {t : t² ≤ 4pⁿ}` and `nArg p n t = 4pⁿ − t²` (`AssemblyRecursion.lean`). -/
def OrdinaryDeuringApprox (H : ℕ → ℚ) (p : ℕ) [Fact p.Prime] : Prop :=
  ∃ C : ℝ, ∃ k : ℕ, ∀ n : ℕ, 1 ≤ n →
    ∑ t ∈ (tset p n).filter (fun t => ¬ (p : ℤ) ∣ t),
      |(((traceCount p n t : ℚ) -
          (p : ℚ) ^ (3 * n) * ((p : ℚ) ^ n - 1) * H (nArg p n t) / 2 : ℚ) : ℝ)| ≤
      C * ((n : ℝ) + 1) ^ k * Real.sqrt p ^ (9 * n)

variable (p : ℕ) [hp : Fact p.Prime]

/-- On `tset p n` with `n ≥ 1`, `p ∤ t` forces `t² < 4pⁿ`. -/
lemma sq_lt_of_ord {n : ℕ} (hn : 1 ≤ n) {t : ℤ} (ht : t ∈ tset p n) (hpt : ¬ (p : ℤ) ∣ t) :
    t ^ 2 < 4 * (p : ℤ) ^ n := by
  have hle := (mem_tset p).mp ht
  refine lt_of_le_of_ne hle fun heq => hpt ?_
  have : (p : ℤ) ∣ t ^ 2 := by
    rw [heq]
    exact dvd_mul_of_dvd_right (dvd_pow_self _ (by omega)) _
  exact (prime_int p).dvd_of_dvd_pow this

lemma nArg_eq (n : ℕ) (t : ℤ) : nArg p n t = (4 * (p : ℤ) ^ n - t ^ 2).toNat := by
  rw [nArg, cast_ppow]

/-- Exact ordinary Deuring implies the approximate form (with `C = 0`). -/
theorem ordinaryDeuringApprox_of_exact (H : ℕ → ℚ) (hD : OrdinaryDeuring H p) :
    OrdinaryDeuringApprox H p := by
  refine ⟨0, 0, fun n hn => ?_⟩
  rw [zero_mul, zero_mul]
  refine le_of_eq (sum_eq_zero fun t ht => ?_)
  rw [mem_filter] at ht
  rw [hD n hn t ht.2, if_pos (sq_lt_of_ord p hn ht.1 ht.2), nArg_eq]
  simp

/-- The ordinary part of the Weierstrass sum, regrouped by traces (Hasse only). -/
theorem ordinary_part_traces (hH : HasseAll p) (n : ℕ) (hn : 1 ≤ n) :
    letI : Fintype (GaloisField p n) := Fintype.ofFinite _
    open scoped Classical in
    ∑ c ∈ ({c : Fin 5 → GaloisField p n | (wc c).Δ ≠ 0} : Finset _) with
        ¬ (p : ℤ) ∣ traceOfFrob (wc c),
      (symTrace 10 (traceOfFrob (wc c)) ((p : ℤ) ^ n) : ℚ) =
      ∑ t ∈ (tset p n).filter (fun t => ¬ (p : ℤ) ∣ t), (traceCount p n t : ℚ) * hq p n t := by
  letI : Fintype (GaloisField p n) := Fintype.ofFinite _
  classical
  set S := ({c : Fin 5 → GaloisField p n | (wc c).Δ ≠ 0} : Finset _).filter
    (fun c => ¬ (p : ℤ) ∣ traceOfFrob (wc c)) with hS
  set T := (tset p n).filter (fun t => ¬ (p : ℤ) ∣ t) with hT
  have hmaps : ∀ c ∈ S, traceOfFrob (wc c) ∈ T := by
    intro c hc
    simp only [hS, mem_filter, mem_univ, true_and] at hc
    rw [hT, mem_filter, mem_tset]
    exact ⟨hH n hn c hc.1, hc.2⟩
  have step := sum_fiberwise_of_maps_to' hmaps (fun t => (symTrace 10 t ((p : ℤ) ^ n) : ℚ))
  rw [← step]
  refine sum_congr rfl fun t ht => ?_
  rw [sum_const, nsmul_eq_mul]
  rw [hT, mem_filter] at ht
  have hcard : (S.filter (fun c => traceOfFrob (wc c) = t)).card = traceCount p n t := by
    rw [traceCount]
    congr 1
    ext c
    simp only [hS, mem_filter, mem_univ, true_and]
    constructor
    · rintro ⟨⟨h1, _⟩, h2⟩; exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨⟨h1, h2 ▸ ht.2⟩, h2⟩
  rw [hcard, hq, cast_ppow]

/-- **R-ord assembly with approximate Deuring.** `OrdinaryDeuringApprox` + supersingular count +
Hasse + an ordinary error bound (from ES, `ordSum_error`) give `IharaApprox p`. -/
theorem iharaApprox_of_deuringApprox_ordError (H : ℕ → ℚ) (hDA : OrdinaryDeuringApprox H p)
    (hss : SupersingularCountBound p) (hH : HasseAll p)
    (hE : ∃ C : ℝ, ∃ k : ℕ, ∀ m : ℕ,
      |((ordSum H p m + 2 * (tauPowerSum p m : ℚ) : ℚ) : ℝ)| ≤
        C * ((m : ℝ) + 1) ^ k * Real.sqrt p ^ (11 * m)) : IharaApprox p := by
  obtain ⟨C, k₁, hC⟩ := hE
  obtain ⟨CA, k₂, hCA⟩ := hDA
  obtain ⟨Css, hCss⟩ := hss
  have hC0 : 0 ≤ C := by
    have := (abs_nonneg _).trans (hC 0); simpa using this
  set k := k₁ + k₂ with hk
  refine ⟨C + 1 + 2876 * Css + 2876 * |CA|, k, fun n hn => ?_⟩
  letI : Fintype (GaloisField p n) := Fintype.ofFinite _
  classical
  set s := Real.sqrt p with hsdef
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.out.one_lt.le
  have hs : 1 ≤ s := by rw [hsdef]; exact Real.one_le_sqrt.mpr hp1
  have hs0 : 0 ≤ s := by linarith
  have hs2 : s ^ 2 = (p : ℝ) := Real.sq_sqrt (Nat.cast_nonneg p)
  set P : ℝ := (p : ℝ) ^ n with hP
  have hP1 : 1 ≤ P := one_le_pow₀ hp1
  have hsP : ∀ j, s ^ (2 * j * n) = P ^ j := by
    intro j; rw [hP, ← hs2, ← pow_mul, ← pow_mul]; ring_nf
  have hn1 : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have hk1 : ((n : ℝ) + 1) ^ k₁ ≤ ((n : ℝ) + 1) ^ k := pow_le_pow_right₀ hn1 (by omega)
  have hk2 : ((n : ℝ) + 1) ^ k₂ ≤ ((n : ℝ) + 1) ^ k := pow_le_pow_right₀ hn1 (by omega)
  have hk0 : (1 : ℝ) ≤ ((n : ℝ) + 1) ^ k := one_le_pow₀ hn1
  -- the decomposition in `ℚ`
  set U := ({c : Fin 5 → GaloisField p n | (wc c).Δ ≠ 0} : Finset _) with hU
  set SS := U.filter (fun c => (p : ℤ) ∣ traceOfFrob (wc c)) with hSS
  set T := (tset p n).filter (fun t => ¬ (p : ℤ) ∣ t) with hT
  set R : ℚ := ∑ t ∈ T, ((traceCount p n t : ℚ) -
      (p : ℚ) ^ (3 * n) * ((p : ℚ) ^ n - 1) * H (nArg p n t) / 2) * hq p n t with hR
  have hord : ∑ t ∈ T, (traceCount p n t : ℚ) * hq p n t =
      (p : ℚ) ^ (3 * n) * ((p : ℚ) ^ n - 1) / 2 * ordSum H p n + R := by
    rw [hR, ordSum_eq, mul_sum, ← sum_add_distrib]
    refine sum_congr rfl fun t _ => ?_
    ring
  have hW : (weierstrassSum p n : ℚ) =
      (p : ℚ) ^ (3 * n) * ((p : ℚ) ^ n - 1) / 2 * ordSum H p n + R +
        ∑ c ∈ SS, (symTrace 10 (traceOfFrob (wc c)) ((p : ℤ) ^ n) : ℚ) := by
    rw [← hord, ← ordinary_part_traces p hH n hn, weierstrassSum]
    push_cast
    rw [add_comm, sum_filter_add_sum_filter_not]
  -- the supersingular sum
  have hSSb : |((∑ c ∈ SS, (symTrace 10 (traceOfFrob (wc c)) ((p : ℤ) ^ n) : ℚ) : ℚ) : ℝ)| ≤
      2876 * Css * (s ^ (8 * n) * P ^ 5) := by
    push_cast
    refine (abs_sum_le_sum_abs _ _).trans ?_
    have hterm : ∀ c ∈ SS, |((symTrace 10 (traceOfFrob (wc c)) ((p : ℤ) ^ n) : ℤ) : ℝ)| ≤
        2876 * P ^ 5 := by
      intro c hc
      simp only [hSS, hU, mem_filter, mem_univ, true_and] at hc
      have := abs_symTrace_ten_le _ _ (by positivity) (hH n hn c hc.1)
      have h' : ((|symTrace 10 (traceOfFrob (wc c)) ((p : ℤ) ^ n)| : ℤ) : ℝ) ≤
          ((2876 * ((p : ℤ) ^ n) ^ 5 : ℤ) : ℝ) := by exact_mod_cast this
      push_cast at h'
      exact h'
    have hcard : (SS.card : ℝ) ≤ Css * s ^ (8 * n) := by
      have h1 := hCss n hn
      have h2 : SS.card ≤ Css * p ^ (4 * n) := by
        convert h1 using 2
        rw [hSS, hU, filter_filter]
      have : (SS.card : ℝ) ≤ (Css : ℝ) * (p : ℝ) ^ (4 * n) := by exact_mod_cast h2
      rw [show 8 * n = 2 * (4 * n) by ring, pow_mul, hs2]
      exact this
    calc ∑ c ∈ SS, |((symTrace 10 (traceOfFrob (wc c)) ((p : ℤ) ^ n) : ℤ) : ℝ)|
        ≤ ∑ _c ∈ SS, 2876 * P ^ 5 := sum_le_sum hterm
      _ = (SS.card : ℝ) * (2876 * P ^ 5) := by rw [sum_const, nsmul_eq_mul]
      _ ≤ (Css * s ^ (8 * n)) * (2876 * P ^ 5) :=
          mul_le_mul_of_nonneg_right hcard (by positivity)
      _ = _ := by ring
  -- the Deuring defect
  have hRb : |((R : ℚ) : ℝ)| ≤ 2876 * |CA| * (((n : ℝ) + 1) ^ k * s ^ (19 * n)) := by
    have hA := hCA n hn
    rw [hR]; push_cast
    refine (abs_sum_le_sum_abs _ _).trans ?_
    have hterm : ∀ t ∈ T, |(((traceCount p n t : ℚ) -
        (p : ℚ) ^ (3 * n) * ((p : ℚ) ^ n - 1) * H (nArg p n t) / 2 : ℚ) : ℝ) *
          ((hq p n t : ℚ) : ℝ)| ≤
        |(((traceCount p n t : ℚ) -
          (p : ℚ) ^ (3 * n) * ((p : ℚ) ^ n - 1) * H (nArg p n t) / 2 : ℚ) : ℝ)| * (2876 * P ^ 5) := by
      intro t ht
      rw [abs_mul]
      refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
      have htt := (mem_tset p).mp (mem_filter.mp ht).1
      have := abs_symTrace_ten_le t ((p ^ n : ℕ) : ℤ) (by positivity) (by rw [cast_ppow]; exact htt)
      have h' : ((|symTrace 10 t ((p ^ n : ℕ) : ℤ)| : ℤ) : ℝ) ≤
          ((2876 * (((p ^ n : ℕ) : ℤ)) ^ 5 : ℤ) : ℝ) := by exact_mod_cast this
      push_cast at h'
      simp only [hq, Rat.cast_intCast]
      push_cast
      exact h'
    have hsum := sum_le_sum hterm
    rw [← sum_mul] at hsum
    push_cast at hsum
    refine hsum.trans ?_
    have hP5 : P ^ 5 = s ^ (10 * n) := by rw [← hsP 5]
    have hA' : ∑ t ∈ T, |(((traceCount p n t : ℚ) -
          (p : ℚ) ^ (3 * n) * ((p : ℚ) ^ n - 1) * H (nArg p n t) / 2 : ℚ) : ℝ)| ≤
        |CA| * ((n : ℝ) + 1) ^ k * s ^ (9 * n) := by
      refine hA.trans ?_
      refine mul_le_mul_of_nonneg_right ?_ (pow_nonneg hs0 _)
      exact mul_le_mul (le_abs_self _) hk2 (by positivity) (abs_nonneg _)
    push_cast at hA'
    calc _ ≤ (|CA| * ((n : ℝ) + 1) ^ k * s ^ (9 * n)) * (2876 * P ^ 5) :=
          mul_le_mul_of_nonneg_right hA' (by positivity)
      _ = 2876 * |CA| * (((n : ℝ) + 1) ^ k * (s ^ (9 * n) * s ^ (10 * n))) := by rw [hP5]; ring
      _ = 2876 * |CA| * (((n : ℝ) + 1) ^ k * s ^ (19 * n)) := by rw [← pow_add]; ring_nf
  -- the ordinary error
  have hEn := hC n
  set E : ℝ := ((ordSum H p n + 2 * (tauPowerSum p n : ℚ) : ℚ) : ℝ) with hEdef
  set SSr : ℝ := ((∑ c ∈ SS, (symTrace 10 (traceOfFrob (wc c)) ((p : ℤ) ^ n) : ℚ) : ℚ) : ℝ)
    with hSSr
  set Rr : ℝ := ((R : ℚ) : ℝ) with hRr
  have hdecomp : ((weierstrassSum p n - (p : ℤ) ^ (3 * n) * ((p : ℤ) ^ n - 1) *
      (-1 - tauPowerSum p n) : ℤ) : ℝ) =
      P ^ 3 * (P - 1) / 2 * E + P ^ 3 * (P - 1) + Rr + SSr := by
    have hq' : ((weierstrassSum p n - (p : ℤ) ^ (3 * n) * ((p : ℤ) ^ n - 1) *
        (-1 - tauPowerSum p n) : ℤ) : ℚ) =
        (p : ℚ) ^ (3 * n) * ((p : ℚ) ^ n - 1) / 2 * ordSum H p n + R +
          (∑ c ∈ SS, (symTrace 10 (traceOfFrob (wc c)) ((p : ℤ) ^ n) : ℚ)) -
          (p : ℚ) ^ (3 * n) * ((p : ℚ) ^ n - 1) * (-1 - (tauPowerSum p n : ℚ)) := by
      push_cast; rw [hW]
    rw [← Rat.cast_intCast, hq', hEdef, hSSr, hRr, hP]
    push_cast
    rw [pow_mul]; ring
  rw [hdecomp]
  have hB0 : 0 ≤ P ^ 3 * (P - 1) := mul_nonneg (by positivity) (by linarith)
  have hP4 : P ^ 4 = s ^ (8 * n) := by rw [← hsP 4]
  have hP5 : P ^ 5 = s ^ (10 * n) := by rw [← hsP 5]
  have h19 : s ^ (8 * n) * s ^ (11 * n) = s ^ (19 * n) := by rw [← pow_add]; ring_nf
  have h18 : s ^ (8 * n) * s ^ (10 * n) ≤ s ^ (19 * n) := by
    rw [← pow_add]; exact pow_le_pow_right₀ hs (by omega)
  have h8 : s ^ (8 * n) ≤ s ^ (19 * n) := pow_le_pow_right₀ hs (by omega)
  have hS19 : 0 ≤ s ^ (19 * n) := pow_nonneg hs0 _
  have t1 : |P ^ 3 * (P - 1) / 2 * E| ≤ C * ((n : ℝ) + 1) ^ k * s ^ (19 * n) := by
    rw [abs_mul, abs_of_nonneg (by positivity)]
    calc P ^ 3 * (P - 1) / 2 * |E| ≤ P ^ 4 * |E| :=
          mul_le_mul_of_nonneg_right (by nlinarith [pow_pos (by linarith : (0:ℝ) < P) 3])
            (abs_nonneg _)
      _ ≤ P ^ 4 * (C * ((n : ℝ) + 1) ^ k₁ * s ^ (11 * n)) :=
          mul_le_mul_of_nonneg_left hEn (by positivity)
      _ ≤ P ^ 4 * (C * ((n : ℝ) + 1) ^ k * s ^ (11 * n)) := by
          gcongr
      _ = C * ((n : ℝ) + 1) ^ k * (s ^ (8 * n) * s ^ (11 * n)) := by rw [hP4]; ring
      _ = C * ((n : ℝ) + 1) ^ k * s ^ (19 * n) := by rw [h19]
  have t2 : |P ^ 3 * (P - 1)| ≤ 1 * ((n : ℝ) + 1) ^ k * s ^ (19 * n) := by
    rw [abs_of_nonneg hB0, one_mul]
    have hB : P ^ 3 * (P - 1) ≤ P ^ 4 := by nlinarith [pow_pos (by linarith : (0:ℝ) < P) 3]
    calc P ^ 3 * (P - 1) ≤ s ^ (19 * n) := by rw [← hP4] at h8; linarith
      _ = 1 * s ^ (19 * n) := (one_mul _).symm
      _ ≤ ((n : ℝ) + 1) ^ k * s ^ (19 * n) := mul_le_mul_of_nonneg_right hk0 hS19
  have hCss0 : (0 : ℝ) ≤ Css := Nat.cast_nonneg _
  have t3 : |SSr| ≤ 2876 * Css * ((n : ℝ) + 1) ^ k * s ^ (19 * n) := by
    refine hSSb.trans ?_
    rw [hP5]
    have hc : 0 ≤ 2876 * (Css : ℝ) := by positivity
    calc 2876 * (Css : ℝ) * (s ^ (8 * n) * s ^ (10 * n)) ≤ 2876 * Css * s ^ (19 * n) :=
          mul_le_mul_of_nonneg_left h18 hc
      _ = 2876 * Css * (1 * s ^ (19 * n)) := by ring
      _ ≤ 2876 * Css * (((n : ℝ) + 1) ^ k * s ^ (19 * n)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hk0 hS19) hc
      _ = _ := by ring
  have t4 : |Rr| ≤ 2876 * |CA| * ((n : ℝ) + 1) ^ k * s ^ (19 * n) := by
    rw [hRr]; refine hRb.trans (le_of_eq ?_); ring
  calc |P ^ 3 * (P - 1) / 2 * E + P ^ 3 * (P - 1) + Rr + SSr|
      ≤ |P ^ 3 * (P - 1) / 2 * E| + |P ^ 3 * (P - 1)| + |Rr| + |SSr| := by
        refine (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans
          (add_le_add (abs_add_le _ _) le_rfl)) le_rfl)
    _ ≤ C * ((n : ℝ) + 1) ^ k * s ^ (19 * n) + 1 * ((n : ℝ) + 1) ^ k * s ^ (19 * n) +
        2876 * |CA| * ((n : ℝ) + 1) ^ k * s ^ (19 * n) +
        2876 * Css * ((n : ℝ) + 1) ^ k * s ^ (19 * n) :=
        add_le_add (add_le_add (add_le_add t1 t2) t4) t3
    _ = (C + 1 + 2876 * Css + 2876 * |CA|) * ((n : ℝ) + 1) ^ k * s ^ (19 * n) := by ring

/-- **R-ord assembly, approximate Deuring** (frozen-style statement): approximate ordinary
Deuring + ES + the prime-square relation + Hecke + supersingular count + Hasse ⇒ `IharaApprox`. -/
theorem iharaApprox_of_deuringApprox (H : ℕ → ℚ) (h0 : HurwitzConventions H)
    (hDA : OrdinaryDeuringApprox H p) (hES : EichlerSelbergPrimePow H p)
    (hHR : HurwitzPrimeSquare H p) (hT : TauHeckeRecurrence p)
    (hss : SupersingularCountBound p) (hH : HasseAll p) : IharaApprox p := by
  obtain ⟨C, hC⟩ := ordSum_error H p h0 hES hHR hT
  exact iharaApprox_of_deuringApprox_ordError p H hDA hss hH ⟨C, 2, hC⟩

end RamanujanWeil.ArithPlan
