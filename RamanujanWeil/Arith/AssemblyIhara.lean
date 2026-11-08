import RamanujanWeil.Arith.AssemblyError
import RamanujanWeil.Arith.SupersingularBound
import RamanujanWeil.Ihara.EndgameApprox

/-!
# R-ord assembly, part 3: `IharaApprox` from the arithmetic inputs

`S(n) = q³(q−1)·½·O(n) + S_ss(n)` (ordinary Deuring on `p ∤ a`, Hasse to locate `a`), so
`S(n) − q³(q−1)(−1 − s_n) = q³(q−1)·½·E(n) + q³(q−1) + S_ss(n)`, and
* `|q³(q−1)·½·E(n)| ≤ C (n+1)^k (√p)^{19n}` (`ordSum_error` / `ordSum_error_of_approx`);
* `|S_ss(n)| ≤ #ss · 2876 q⁵ ≤ 2876 C_ss (√p)^{18n}` (`abs_symTrace_ten_le` under Hasse,
  `SupersingularCountBound`).

Main results: `iharaApprox_of_ordError` (generic), `iharaApprox_of_arith` (frozen) and
`iharaApprox_of_arith_approx` (ES in approximate form).
-/

open Finset

namespace RamanujanWeil.ArithPlan

open RamanujanWeil.Ihara

/-- `|h₁₀(a, q)| ≤ 2876 q⁵` when `a² ≤ 4q`. -/
theorem abs_symTrace_ten_le (a Q : ℤ) (hQ : 0 ≤ Q) (ha : a ^ 2 ≤ 4 * Q) :
    |symTrace 10 a Q| ≤ 2876 * Q ^ 5 := by
  set x := a ^ 2 with hx
  have hx0 : 0 ≤ x := sq_nonneg a
  have expand : symTrace 10 a Q = x ^ 5 - 9 * (Q * x ^ 4) + 28 * (Q ^ 2 * x ^ 3) -
      35 * (Q ^ 3 * x ^ 2) + 15 * (Q ^ 4 * x) - Q ^ 5 := by
    rw [symTrace_ten, hx]; ring
  have p5 : x ^ 5 ≤ 1024 * Q ^ 5 := by
    have := pow_le_pow_left₀ hx0 ha 5; nlinarith [this]
  have p4 : Q * x ^ 4 ≤ 256 * Q ^ 5 := by
    have := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hx0 ha 4) hQ; nlinarith [this]
  have p3 : Q ^ 2 * x ^ 3 ≤ 64 * Q ^ 5 := by
    have := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hx0 ha 3) (pow_nonneg hQ 2)
    nlinarith [this]
  have p2 : Q ^ 3 * x ^ 2 ≤ 16 * Q ^ 5 := by
    have := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hx0 ha 2) (pow_nonneg hQ 3)
    nlinarith [this]
  have p1 : Q ^ 4 * x ≤ 4 * Q ^ 5 := by
    have := mul_le_mul_of_nonneg_left ha (pow_nonneg hQ 4); nlinarith [this]
  have n5 : 0 ≤ x ^ 5 := pow_nonneg hx0 5
  have n4 : 0 ≤ Q * x ^ 4 := mul_nonneg hQ (pow_nonneg hx0 4)
  have n3 : 0 ≤ Q ^ 2 * x ^ 3 := mul_nonneg (pow_nonneg hQ 2) (pow_nonneg hx0 3)
  have n2 : 0 ≤ Q ^ 3 * x ^ 2 := mul_nonneg (pow_nonneg hQ 3) (pow_nonneg hx0 2)
  have n1 : 0 ≤ Q ^ 4 * x := mul_nonneg (pow_nonneg hQ 4) hx0
  have n0 : 0 ≤ Q ^ 5 := pow_nonneg hQ 5
  rw [expand, abs_le]
  constructor <;> linarith

variable (p : ℕ) [hp : Fact p.Prime]

/-- **The ordinary part of the Weierstrass sum** (ordinary Deuring + Hasse):
`Σ_{Δ ≠ 0, p ∤ a_c} h₁₀(a_c, q) = q³(q−1)/2 · ordSum H p n`. -/
theorem ordinary_part (H : ℕ → ℚ) (hD : OrdinaryDeuring H p) (hH : HasseAll p) (n : ℕ)
    (hn : 1 ≤ n) :
    letI : Fintype (GaloisField p n) := Fintype.ofFinite _
    open scoped Classical in
    ∑ c ∈ ({c : Fin 5 → GaloisField p n | (wc c).Δ ≠ 0} : Finset _) with
        ¬ (p : ℤ) ∣ traceOfFrob (wc c),
      (symTrace 10 (traceOfFrob (wc c)) ((p : ℤ) ^ n) : ℚ) =
      (p : ℚ) ^ (3 * n) * ((p : ℚ) ^ n - 1) / 2 * ordSum H p n := by
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
  convert step.symm using 1
  rw [ordSum_eq, ← hT, mul_sum]
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
  rw [hcard, hD n hn t ht.2]
  have hlt : t ^ 2 < 4 * (p : ℤ) ^ n := by
    have hle := (mem_tset p).mp ht.1
    refine lt_of_le_of_ne hle fun heq => ht.2 ?_
    have : (p : ℤ) ∣ t ^ 2 := by
      rw [heq]
      exact dvd_mul_of_dvd_right (dvd_pow_self _ (by omega)) _
    exact (prime_int p).dvd_of_dvd_pow this
  rw [if_pos hlt, hq, nArg, cast_ppow]
  ring

/-- **R-ord assembly, generic form**: ordinary Deuring + supersingular count + Hasse + an ordinary
error bound give `IharaApprox p`. -/
theorem iharaApprox_of_ordError (H : ℕ → ℚ) (hD : OrdinaryDeuring H p)
    (hss : SupersingularCountBound p) (hH : HasseAll p)
    (hE : ∃ C : ℝ, ∃ k : ℕ, ∀ m : ℕ,
      |((ordSum H p m + 2 * (tauPowerSum p m : ℚ) : ℚ) : ℝ)| ≤
        C * ((m : ℝ) + 1) ^ k * Real.sqrt p ^ (11 * m)) : IharaApprox p := by
  obtain ⟨C, k, hC⟩ := hE
  obtain ⟨Css, hCss⟩ := hss
  have hC0 : 0 ≤ C := by
    have := (abs_nonneg _).trans (hC 0); simpa using this
  refine ⟨C + 1 + 2876 * Css, k, fun n hn => ?_⟩
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
  -- the decomposition in `ℚ`
  set U := ({c : Fin 5 → GaloisField p n | (wc c).Δ ≠ 0} : Finset _) with hU
  set SS := U.filter (fun c => (p : ℤ) ∣ traceOfFrob (wc c)) with hSS
  have hW : (weierstrassSum p n : ℚ) =
      (p : ℚ) ^ (3 * n) * ((p : ℚ) ^ n - 1) / 2 * ordSum H p n +
        ∑ c ∈ SS, (symTrace 10 (traceOfFrob (wc c)) ((p : ℤ) ^ n) : ℚ) := by
    rw [← ordinary_part p H hD hH n hn, weierstrassSum]
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
  -- the ordinary error
  have hEn := hC n
  set E : ℝ := ((ordSum H p n + 2 * (tauPowerSum p n : ℚ) : ℚ) : ℝ) with hEdef
  set SSr : ℝ := ((∑ c ∈ SS, (symTrace 10 (traceOfFrob (wc c)) ((p : ℤ) ^ n) : ℚ) : ℚ) : ℝ)
    with hSSr
  have hdecomp : ((weierstrassSum p n - (p : ℤ) ^ (3 * n) * ((p : ℤ) ^ n - 1) *
      (-1 - tauPowerSum p n) : ℤ) : ℝ) =
      P ^ 3 * (P - 1) / 2 * E + P ^ 3 * (P - 1) + SSr := by
    have hq : ((weierstrassSum p n - (p : ℤ) ^ (3 * n) * ((p : ℤ) ^ n - 1) *
        (-1 - tauPowerSum p n) : ℤ) : ℚ) =
        (p : ℚ) ^ (3 * n) * ((p : ℚ) ^ n - 1) / 2 * ordSum H p n +
          (∑ c ∈ SS, (symTrace 10 (traceOfFrob (wc c)) ((p : ℤ) ^ n) : ℚ)) -
          (p : ℚ) ^ (3 * n) * ((p : ℚ) ^ n - 1) * (-1 - (tauPowerSum p n : ℚ)) := by
      push_cast; rw [hW]
    rw [← Rat.cast_intCast, hq, hEdef, hSSr, hP]
    push_cast
    rw [pow_mul]; ring
  rw [hdecomp]
  -- estimate each piece
  have hB0 : 0 ≤ P ^ 3 * (P - 1) := mul_nonneg (by positivity) (by linarith)
  have hB : P ^ 3 * (P - 1) ≤ P ^ 4 := by nlinarith [pow_pos (by linarith : (0:ℝ) < P) 3]
  have hP4 : P ^ 4 = s ^ (8 * n) := by rw [← hsP 4]
  have hP5 : P ^ 5 = s ^ (10 * n) := by rw [← hsP 5]
  have hk1 : (1 : ℝ) ≤ ((n : ℝ) + 1) ^ k := one_le_pow₀ (by linarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)])
  have h19 : s ^ (8 * n) * s ^ (11 * n) = s ^ (19 * n) := by rw [← pow_add]; ring_nf
  have h18 : s ^ (8 * n) * s ^ (10 * n) ≤ s ^ (19 * n) := by
    rw [← pow_add]; exact pow_le_pow_right₀ hs (by omega)
  have h8 : s ^ (8 * n) ≤ s ^ (19 * n) := pow_le_pow_right₀ hs (by omega)
  have hS19 : 0 ≤ s ^ (19 * n) := pow_nonneg hs0 _
  -- piece 1
  have t1 : |P ^ 3 * (P - 1) / 2 * E| ≤ C * ((n : ℝ) + 1) ^ k * s ^ (19 * n) := by
    rw [abs_mul, abs_of_nonneg (by positivity)]
    calc P ^ 3 * (P - 1) / 2 * |E| ≤ P ^ 4 * |E| :=
          mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg _)
      _ ≤ P ^ 4 * (C * ((n : ℝ) + 1) ^ k * s ^ (11 * n)) :=
          mul_le_mul_of_nonneg_left hEn (by positivity)
      _ = C * ((n : ℝ) + 1) ^ k * (s ^ (8 * n) * s ^ (11 * n)) := by rw [hP4]; ring
      _ = C * ((n : ℝ) + 1) ^ k * s ^ (19 * n) := by rw [h19]
  -- piece 2
  have t2 : |P ^ 3 * (P - 1)| ≤ 1 * ((n : ℝ) + 1) ^ k * s ^ (19 * n) := by
    rw [abs_of_nonneg hB0, one_mul]
    calc P ^ 3 * (P - 1) ≤ s ^ (19 * n) := by rw [← hP4] at h8; linarith
      _ = 1 * s ^ (19 * n) := (one_mul _).symm
      _ ≤ ((n : ℝ) + 1) ^ k * s ^ (19 * n) := mul_le_mul_of_nonneg_right hk1 hS19
  -- piece 3
  have hCss0 : (0 : ℝ) ≤ Css := Nat.cast_nonneg _
  have t3 : |SSr| ≤ 2876 * Css * ((n : ℝ) + 1) ^ k * s ^ (19 * n) := by
    refine hSSb.trans ?_
    rw [hP5]
    have hc : 0 ≤ 2876 * (Css : ℝ) := by positivity
    calc 2876 * (Css : ℝ) * (s ^ (8 * n) * s ^ (10 * n)) ≤ 2876 * Css * s ^ (19 * n) :=
          mul_le_mul_of_nonneg_left h18 hc
      _ = 2876 * Css * (1 * s ^ (19 * n)) := by ring
      _ ≤ 2876 * Css * (((n : ℝ) + 1) ^ k * s ^ (19 * n)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hk1 hS19) hc
      _ = _ := by ring
  calc |P ^ 3 * (P - 1) / 2 * E + P ^ 3 * (P - 1) + SSr|
      ≤ |P ^ 3 * (P - 1) / 2 * E| + |P ^ 3 * (P - 1)| + |SSr| :=
        (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ C * ((n : ℝ) + 1) ^ k * s ^ (19 * n) + 1 * ((n : ℝ) + 1) ^ k * s ^ (19 * n) +
        2876 * Css * ((n : ℝ) + 1) ^ k * s ^ (19 * n) := add_le_add (add_le_add t1 t2) t3
    _ = (C + 1 + 2876 * Css) * ((n : ℝ) + 1) ^ k * s ^ (19 * n) := by ring

/-- **R-ord assembly** (frozen statement). -/
theorem iharaApprox_of_arith (H : ℕ → ℚ) (p : ℕ) [Fact p.Prime] (h0 : HurwitzConventions H)
    (hD : OrdinaryDeuring H p) (hES : EichlerSelbergPrimePow H p)
    (hHR : HurwitzPrimeSquare H p) (hT : TauHeckeRecurrence p)
    (hss : SupersingularCountBound p) (hH : HasseAll p) : IharaApprox p := by
  obtain ⟨C, hC⟩ := ordSum_error H p h0 hES hHR hT
  exact iharaApprox_of_ordError p H hD hss hH ⟨C, 2, hC⟩

/-- **R-ord assembly, approximate ES** (only the elliptic terms of ES exact). -/
theorem iharaApprox_of_arith_approx (H : ℕ → ℚ) (p : ℕ) [Fact p.Prime]
    (h0 : HurwitzConventions H) (hD : OrdinaryDeuring H p) (hES : EichlerSelbergApprox H p)
    (hHR : HurwitzPrimeSquare H p) (hT : TauHeckeRecurrence p)
    (hss : SupersingularCountBound p) (hH : HasseAll p) : IharaApprox p :=
  iharaApprox_of_ordError p H hD hss hH (ordSum_error_of_approx H p h0 hES hHR hT)

end RamanujanWeil.ArithPlan
