import RamanujanWeil.Arith.ESInput
import RamanujanWeil.Arith.AssemblyVocab

/-!
# A2 / ES-P13: assembly — Eichler–Selberg at prime powers, conditional on the analytic input

The algebraic part of P13: rewrite property (C) (`traceSum_classNumber`) together with
`traceSum n = σ₁₁(n) + 2τ(n)` into the frozen `esSum`/`hypTerm` shape of `AssemblyVocab.lean`:

* `gegenbauer`   : `(d − a)·p₁₀(a + d, ad) = d¹¹ − a¹¹`, `p₁₀(2a, a²) = 11a¹⁰`;
* `hyp_minus_sig`: `hypW(a, d)·p₁₀(a + d, ad) − d¹¹ = −min(a, d)¹¹ + [a = d]·(11/6)a¹⁰`;
* `par_sum`      : the parabolic terms `Σ_{t² = 4n} p₁₀(t, n)` equal `22·Σ_{a² = n} a¹⁰`, so they
  cancel the scalar terms (`H(0) = −1/12`);
* `esSum_general`: `esSum H n = −2τ(n) − Σ_{0<a∣n} min(a, n/a)¹¹` for every `n ≥ 1`;
* **`eichlerSelbergPrimePow_of_tauEigenPeriod`**, **`eichlerSelbergPrimePow_of_input`**:
  `EichlerPeriodInput → ∀ p prime, EichlerSelbergPrimePow hurwitz p`.
-/

open Finset

namespace RamanujanWeil.Arith.ES

open M2 RamanujanWeil.ArithPlan

lemma symTrace_eq (t q : ℤ) : RamanujanWeil.Ihara.symTrace 10 t q = symTr10 t q := rfl

lemma gegenbauer (a d : ℤ) : (d - a) * symTr10 (a + d) (a * d) = d ^ 11 - a ^ 11 := by
  norm_num [symTr10, Finset.sum_range_succ, Nat.choose]; ring

lemma symTr10_two (a : ℤ) : symTr10 (2 * a) (a * a) = 11 * a ^ 10 := by
  norm_num [symTr10, Finset.sum_range_succ, Nat.choose]; ring

lemma symTr10_neg (t n : ℤ) : symTr10 (-t) n = symTr10 t n := by
  norm_num [symTr10, Finset.sum_range_succ, Nat.choose]

lemma hyp_minus_sig (a d : ℤ) :
    hypW a d * (symTr10 (a + d) (a * d) : ℚ) - (d : ℚ) ^ 11 =
      -(((min a d : ℤ) : ℚ) ^ 11) + (if a = d then 11 / 6 * (a : ℚ) ^ 10 else 0) := by
  unfold hypW
  rcases lt_trichotomy a d with h | h | h
  · rw [esIfPos h, esIfNeg h.ne, min_eq_left h.le]
    have := congrArg (fun z : ℤ => (z : ℚ)) (gegenbauer a d)
    push_cast at this ⊢
    linarith
  · subst h
    rw [esIfNeg (lt_irrefl a), esIfPos rfl, esIfPos rfl, min_self, show a + a = 2 * a by ring,
      symTr10_two]
    push_cast; ring
  · rw [esIfNeg (by omega), esIfNeg (by omega), esIfNeg h.ne', min_eq_right h.le]
    ring

/-- The parabolic terms. -/
lemma par_sum (n : ℕ) (hn : 1 ≤ n) :
    ∑ t ∈ Icc (-(2 * (n : ℤ))) (2 * n), (if t ^ 2 = 4 * (n : ℤ) then (symTr10 t n : ℚ) else 0) =
      ∑ a ∈ (Icc (1 : ℤ) n).filter (· ∣ (n : ℤ)),
        (if a * a = (n : ℤ) then 22 * (a : ℚ) ^ 10 else 0) := by
  by_cases hsq : ∃ r : ℤ, 1 ≤ r ∧ r * r = n
  · obtain ⟨r, hr1, hrn⟩ := hsq
    have hrn' : r ≤ n := by nlinarith
    rw [Finset.sum_eq_add (2 * r) (-(2 * r)) (by omega)]
    · rw [Finset.sum_eq_single r]
      · rw [esIfPos (by rw [← hrn]; ring), esIfPos (by rw [← hrn]; ring), esIfPos hrn, ← hrn,
          symTr10_neg, symTr10_two]
        push_cast; ring
      · intro a ha hne
        simp only [Finset.mem_filter, Finset.mem_Icc] at ha
        rw [esIfNeg]
        intro h
        apply hne
        nlinarith
      · intro h
        exfalso; apply h
        simp only [Finset.mem_filter, Finset.mem_Icc]
        exact ⟨⟨hr1, hrn'⟩, ⟨r, hrn.symm⟩⟩
    · intro c _ hc
      rw [esIfNeg]
      intro h
      have : (c - 2 * r) * (c + 2 * r) = 0 := by rw [← hrn] at h; linear_combination h
      rcases mul_eq_zero.mp this with h1 | h1
      · exact hc.1 (by linarith)
      · exact hc.2 (by linarith)
    · intro h; exfalso; apply h; simp only [Finset.mem_Icc]; constructor <;> nlinarith
    · intro h; exfalso; apply h; simp only [Finset.mem_Icc]; constructor <;> nlinarith
  · push Not at hsq
    rw [Finset.sum_eq_zero, Finset.sum_eq_zero]
    · intro a ha
      simp only [Finset.mem_filter, Finset.mem_Icc] at ha
      rw [esIfNeg (hsq a ha.1.1)]
    · intro t _
      rw [esIfNeg]
      intro h
      obtain ⟨s, hs⟩ : Even t := by
        by_contra ho
        rw [Int.not_even_iff_odd] at ho
        obtain ⟨k, hk⟩ := ho
        subst hk
        ring_nf at h
        omega
      subst hs
      have hss : s * s = n := by nlinarith
      rcases le_or_gt 0 s with h0 | h0
      · exact hsq s (by nlinarith) hss
      · exact hsq (-s) (by nlinarith) (by rw [← hss]; ring)

lemma hurwitz_zero' : Hurwitz.hurwitz 0 = -1 / 12 := by simp [Hurwitz.hurwitz]

/-- **Eichler–Selberg, general `n ≥ 1`** (given `traceSum n = σ₁₁(n) + 2τ(n)`). -/
theorem esSum_general (h : TauEigenPeriod) {n : ℕ} (hn : 1 ≤ n) :
    esSum Hurwitz.hurwitz n = -2 * (RamanujanTau.tau n : ℚ) -
      ∑ a ∈ (Icc (1 : ℤ) n).filter (· ∣ (n : ℤ)), ((min a ((n : ℤ) / a) : ℤ) : ℚ) ^ 11 := by
  have tc := traceSum_classNumber n hn
  have ts := traceSum_eq_sig_tau h hn
  set D := (Icc (1 : ℤ) n).filter (· ∣ (n : ℤ)) with hD
  -- the class-number side split into `t² < 4n` and `t² = 4n`
  have hes : esSum Hurwitz.hurwitz n =
      (∑ t ∈ Icc (-(2 * (n : ℤ))) (2 * n),
        if t ^ 2 < 4 * (n : ℤ) then (symTr10 t n : ℚ) * Hurwitz.hurwitz (4 * (n : ℤ) - t ^ 2).toNat
        else 0) +
      (-1 / 12) * ∑ t ∈ Icc (-(2 * (n : ℤ))) (2 * n),
        (if t ^ 2 = 4 * (n : ℤ) then (symTr10 t n : ℚ) else 0) := by
    unfold esSum
    rw [Finset.sum_filter, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [symTrace_eq]
    by_cases h1 : t ^ 2 < 4 * (n : ℤ)
    · rw [esIfPos h1.le, esIfPos h1, esIfNeg h1.ne]; ring
    · by_cases h2 : t ^ 2 = 4 * (n : ℤ)
      · rw [esIfPos h2.le, esIfNeg h1, esIfPos h2, h2, sub_self, Int.toNat_zero, hurwitz_zero']
        ring
      · rw [esIfNeg (by omega), esIfNeg h1, esIfNeg h2]; ring
  -- the hyperbolic side minus `σ₁₁`
  have hhyp : (∑ a ∈ Icc (1 : ℤ) n,
        if a ∣ (n : ℤ) then hypW a ((n : ℤ) / a) * (symTr10 (a + (n : ℤ) / a) n : ℚ) else 0) -
      sig11 n =
      -(∑ a ∈ D, ((min a ((n : ℤ) / a) : ℤ) : ℚ) ^ 11) +
        (11 / 6 / 22) * ∑ a ∈ D, (if a * a = (n : ℤ) then 22 * (a : ℚ) ^ 10 else 0) := by
    rw [← Finset.sum_filter, sig11, ← hD, ← Finset.sum_sub_distrib, Finset.mul_sum,
      ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a ha => ?_
    simp only [hD, Finset.mem_filter, Finset.mem_Icc] at ha
    obtain ⟨⟨ha1, _⟩, hdvd⟩ := ha
    have had : a * ((n : ℤ) / a) = n := Int.mul_ediv_cancel' hdvd
    have hd1 : 1 ≤ (n : ℤ) / a := by
      by_contra hc
      have : (n : ℤ) / a ≤ 0 := by omega
      nlinarith
    have key := hyp_minus_sig a ((n : ℤ) / a)
    rw [had] at key
    rw [key]
    by_cases hsq : a = (n : ℤ) / a
    · rw [esIfPos hsq, esIfPos (by rw [← had, ← hsq])]; ring
    · rw [esIfNeg hsq, esIfNeg (by intro h; apply hsq; nlinarith)]; ring
  rw [hes, par_sum n hn]
  linarith

/-- Divisor sums over `{0 < a ∣ n} ⊂ ℤ` as sums over `Nat.divisors`. -/
lemma sum_int_divisors {β : Type*} [AddCommMonoid β] (n : ℕ) (g : ℤ → β) :
    ∑ a ∈ (Icc (1 : ℤ) n).filter (· ∣ (n : ℤ)), g a = ∑ d ∈ n.divisors, g d := by
  have e : (Icc (1 : ℤ) n).filter (· ∣ (n : ℤ)) = n.divisors.image (fun d : ℕ => (d : ℤ)) := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_image, Nat.mem_divisors]
    constructor
    · rintro ⟨⟨ha1, han⟩, hdvd⟩
      refine ⟨a.toNat, ⟨?_, by omega⟩, by omega⟩
      have : ((a.toNat : ℕ) : ℤ) ∣ (n : ℤ) := by rw [Int.toNat_of_nonneg (by omega)]; exact hdvd
      exact_mod_cast this
    · rintro ⟨d, ⟨hdvd, hn0⟩, rfl⟩
      have hd := Nat.divisor_le (Nat.mem_divisors.mpr ⟨hdvd, hn0⟩)
      have hd1 : 1 ≤ d := Nat.pos_of_dvd_of_pos hdvd (Nat.pos_of_ne_zero hn0)
      exact ⟨⟨by exact_mod_cast hd1, by exact_mod_cast hd⟩, by exact_mod_cast hdvd⟩
  rw [e, Finset.sum_image (fun x _ y _ h => by exact_mod_cast h)]

lemma hypTerm_eq (p m : ℕ) (hp : p.Prime) :
    ∑ a ∈ (Icc (1 : ℤ) ((p ^ m : ℕ) : ℤ)).filter (· ∣ ((p ^ m : ℕ) : ℤ)),
        ((min a (((p ^ m : ℕ) : ℤ) / a) : ℤ) : ℚ) ^ 11 = (hypTerm p m : ℚ) := by
  rw [sum_int_divisors, Nat.divisors_prime_pow hp, Finset.sum_map, hypTerm, Int.cast_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hjm : j ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  simp only [Function.Embedding.coeFn_mk]
  have e2 : min ((p ^ j : ℕ) : ℤ) (((p ^ m : ℕ) : ℤ) / ((p ^ j : ℕ) : ℤ)) =
      ((min (p ^ j) (p ^ (m - j)) : ℕ) : ℤ) := by
    rw [← Int.natCast_div, Nat.pow_div hjm hp.pos, Nat.cast_min]
  rw [e2, Int.cast_pow]

/-- **Eichler–Selberg at prime powers from the eigen-period.** -/
theorem eichlerSelbergPrimePow_of_tauEigenPeriod (h : TauEigenPeriod) (p : ℕ) (hp : p.Prime) :
    EichlerSelbergPrimePow Hurwitz.hurwitz p := by
  intro m
  have hn : 1 ≤ p ^ m := Nat.one_le_pow _ _ hp.pos
  rw [esSum_general h hn, hypTerm_eq p m hp]

/-- **A2, conditional form**: the single analytic input (`EichlerPeriodInput`, to be supplied by
P10–P12) implies `EichlerSelbergPrimePow hurwitz p` for every prime `p`. -/
theorem eichlerSelbergPrimePow_of_input (h : EichlerPeriodInput) (p : ℕ) (hp : p.Prime) :
    EichlerSelbergPrimePow Hurwitz.hurwitz p :=
  eichlerSelbergPrimePow_of_tauEigenPeriod (tauEigenPeriod_of_input h) p hp

/-- The same, in the shape consumed by `Ihara.deligneBound_of_ES_Deuring`. -/
theorem eichlerSelberg_all_of_input (h : EichlerPeriodInput) :
    ∀ (p : ℕ) [Fact p.Prime], EichlerSelbergPrimePow Hurwitz.hurwitz p :=
  fun p hp => eichlerSelbergPrimePow_of_input h p hp.out

end RamanujanWeil.Arith.ES
