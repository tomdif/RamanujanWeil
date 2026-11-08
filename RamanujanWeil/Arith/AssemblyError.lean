import RamanujanWeil.Arith.AssemblyRecursion

/-!
# R-ord assembly, part 2: the ordinary error bound

* `tauPowerSum_add_two`: `s_{m+2} = τ(p^{m+2}) − p¹¹τ(pᵐ)` (Hecke recurrence).
* `errSum_rec`: `E(m+4) = p¹⁰E(m+2) + ε(m+4) − p¹⁰(p+1)ε(m+2) + p²¹ε(m)`, where
  `E(m) = ordSum H p m + 2 s_m` and `ε(m) = esSum H (pᵐ) + 2τ(pᵐ)` (V3b).
* `growth_of_rec`: the recursion `E(m+4) = s²⁰E(m+2) + μ(m+4)` with
  `|μ(m+4)| ≤ D (m+5)^K s^{11(m+4)}` and `s ≥ 1` gives `|E(m)| ≤ C (m+1)^{K+1} s^{11m}` (V3c).
* `ordSum_error_core`, `ordSum_error`, `ordSum_error_of_approx` (frozen statements).
-/

open Finset

namespace RamanujanWeil.ArithPlan

open RamanujanWeil.Ihara

/-- `s_{m+2} = τ(p^{m+2}) − p¹¹ τ(pᵐ)`, from the Hecke recurrence. -/
theorem tauPowerSum_add_two (p : ℕ) (hT : TauHeckeRecurrence p) (m : ℕ) :
    tauPowerSum p (m + 2) =
      RamanujanTau.tau (p ^ (m + 2)) - (p : ℤ) ^ 11 * RamanujanTau.tau (p ^ m) := by
  have key : ∀ m, (tauPowerSum p (m + 2) =
      RamanujanTau.tau (p ^ (m + 2)) - (p : ℤ) ^ 11 * RamanujanTau.tau (p ^ m)) ∧
      (tauPowerSum p (m + 3) =
      RamanujanTau.tau (p ^ (m + 3)) - (p : ℤ) ^ 11 * RamanujanTau.tau (p ^ (m + 1))) := by
    intro m
    induction m with
    | zero =>
      have e1 : RamanujanTau.tau (p ^ 2) = RamanujanTau.tau p * RamanujanTau.tau p -
          (p : ℤ) ^ 11 := by
        have := hT 1 le_rfl
        simpa [RamanujanTau.tau_one] using this
      have e2 : RamanujanTau.tau (p ^ 3) = RamanujanTau.tau p * RamanujanTau.tau (p ^ 2) -
          (p : ℤ) ^ 11 * RamanujanTau.tau p := by
        have := hT 2 (by norm_num)
        simpa using this
      refine ⟨?_, ?_⟩
      · simp only [tauPowerSum, zero_add, pow_zero, RamanujanTau.tau_one]
        linear_combination (-1 : ℤ) * e1
      · simp only [tauPowerSum, zero_add, pow_one]
        linear_combination RamanujanTau.tau p * (-1 : ℤ) * e1 - e2
    | succ m ih =>
      refine ⟨ih.2, ?_⟩
      obtain ⟨h0, h1⟩ := ih
      have e3 : RamanujanTau.tau (p ^ (m + 4)) = RamanujanTau.tau p *
          RamanujanTau.tau (p ^ (m + 3)) - (p : ℤ) ^ 11 * RamanujanTau.tau (p ^ (m + 2)) := by
        have := hT (m + 3) (by omega)
        simpa using this
      have e1 : RamanujanTau.tau (p ^ (m + 2)) = RamanujanTau.tau p *
          RamanujanTau.tau (p ^ (m + 1)) - (p : ℤ) ^ 11 * RamanujanTau.tau (p ^ m) := by
        have := hT (m + 1) (by omega)
        simpa using this
      have hdef : tauPowerSum p (m + 1 + 3) =
          RamanujanTau.tau p * tauPowerSum p (m + 3) - (p : ℤ) ^ 11 * tauPowerSum p (m + 2) := rfl
      rw [hdef, show m + 1 + 3 = m + 4 by ring, show m + 1 + 1 = m + 2 by ring]
      linear_combination RamanujanTau.tau p * h1 - (p : ℤ) ^ 11 * h0 - e3 + (p : ℤ) ^ 11 * e1
  exact (key m).1

/-- `E(m) = ordSum H p m + 2 s_m`. -/
noncomputable def errSum (H : ℕ → ℚ) (p m : ℕ) : ℚ := ordSum H p m + 2 * (tauPowerSum p m : ℚ)

/-- `ε(m) = esSum H (pᵐ) + 2 τ(pᵐ)` (the non-elliptic part of ES, `= −λ(m)` under exact ES). -/
noncomputable def esErr (H : ℕ → ℚ) (p m : ℕ) : ℚ :=
  esSum H (p ^ m) + 2 * (RamanujanTau.tau (p ^ m) : ℚ)

/-- **The error recursion (V3b).** -/
theorem errSum_rec (H : ℕ → ℚ) (p : ℕ) [Fact p.Prime] (hHR : HurwitzPrimeSquare H p)
    (hT : TauHeckeRecurrence p) (m : ℕ) :
    errSum H p (m + 4) = (p : ℚ) ^ 10 * errSum H p (m + 2) +
      (esErr H p (m + 4) - (p : ℚ) ^ 10 * ((p : ℚ) + 1) * esErr H p (m + 2) +
        (p : ℚ) ^ 21 * esErr H p m) := by
  have h4 := tauPowerSum_add_two p hT (m + 2)
  have h2 := tauPowerSum_add_two p hT m
  rw [show m + 2 + 2 = m + 4 by ring] at h4
  have h4q : (tauPowerSum p (m + 4) : ℚ) = (RamanujanTau.tau (p ^ (m + 4)) : ℚ) -
      (p : ℚ) ^ 11 * (RamanujanTau.tau (p ^ (m + 2)) : ℚ) := by exact_mod_cast h4
  have h2q : (tauPowerSum p (m + 2) : ℚ) = (RamanujanTau.tau (p ^ (m + 2)) : ℚ) -
      (p : ℚ) ^ 11 * (RamanujanTau.tau (p ^ m) : ℚ) := by exact_mod_cast h2
  rw [errSum, errSum, esErr, esErr, esErr, ordSum_rec p H hHR m, h4q, h2q]
  ring

/-- **Growth from the recursion (V3c).** -/
theorem growth_of_rec (s : ℝ) (hs : 1 ≤ s) (E μ : ℕ → ℝ) (D : ℝ) (K : ℕ) (hD : 0 ≤ D)
    (hrec : ∀ m, E (m + 4) = s ^ 20 * E (m + 2) + μ (m + 4))
    (hμ : ∀ m, |μ (m + 4)| ≤ D * ((m : ℝ) + 5) ^ K * s ^ (11 * m + 44)) :
    ∃ C : ℝ, ∀ m, |E m| ≤ C * ((m : ℝ) + 1) ^ (K + 1) * s ^ (11 * m) := by
  set C := |E 0| + |E 1| + |E 2| + |E 3| + D with hC
  have hC0 : 0 ≤ C := by positivity
  have hDC : D ≤ C := by
    have := abs_nonneg (E 0); have := abs_nonneg (E 1); have := abs_nonneg (E 2)
    have := abs_nonneg (E 3); linarith
  refine ⟨C, fun m => ?_⟩
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    rcases lt_or_ge m 4 with hm | hm
    · have hle : |E m| ≤ C := by
        have := abs_nonneg (E 0); have := abs_nonneg (E 1); have := abs_nonneg (E 2)
        have := abs_nonneg (E 3)
        interval_cases m <;> linarith
      have h1 : (1 : ℝ) ≤ ((m : ℝ) + 1) ^ (K + 1) * s ^ (11 * m) :=
        one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by linarith [(Nat.cast_nonneg m : (0:ℝ) ≤ m)]))
          (one_le_pow₀ hs)
      calc |E m| ≤ C := hle
        _ = C * 1 := (mul_one C).symm
        _ ≤ C * (((m : ℝ) + 1) ^ (K + 1) * s ^ (11 * m)) := mul_le_mul_of_nonneg_left h1 hC0
        _ = _ := by ring
    · obtain ⟨n, rfl⟩ : ∃ n, m = n + 4 := ⟨m - 4, by omega⟩
      have ihn := ih (n + 2) (by omega)
      have hs0 : 0 ≤ s := by linarith
      have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      set w := s ^ (11 * n) with hw
      have hw0 : 0 ≤ w := pow_nonneg hs0 _
      have e2 : s ^ (11 * (n + 2)) = s ^ 22 * w := by rw [hw, ← pow_add]; ring_nf
      have e4 : s ^ (11 * (n + 4)) = s ^ 44 * w := by rw [hw, ← pow_add]; ring_nf
      have e44 : s ^ (11 * n + 44) = s ^ 44 * w := by rw [hw, ← pow_add]; ring_nf
      have h42 : s ^ 42 ≤ s ^ 44 := pow_le_pow_right₀ hs (by norm_num)
      have c2 : ((↑(n + 2) : ℝ) + 1) = (n : ℝ) + 3 := by push_cast; ring
      have c4 : ((↑(n + 4) : ℝ) + 1) = (n : ℝ) + 5 := by push_cast; ring
      rw [c2, e2] at ihn
      rw [c4, e4, hrec n]
      have hμn := hμ n
      rw [e44] at hμn
      set X := (n : ℝ) + 3
      set Y := (n : ℝ) + 5
      have hX0 : 0 ≤ X := by positivity
      have hXY : X ≤ Y := by simp only [X, Y]; linarith
      have hYK : 0 ≤ Y ^ K := by positivity
      have hXK : X ^ (K + 1) ≤ X * Y ^ K := by
        rw [pow_succ']; exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hX0 hXY K) hX0
      have hs20 : 0 ≤ s ^ 20 := pow_nonneg hs0 _
      -- |E(n+4)| ≤ s²⁰|E(n+2)| + |μ|
      have step1 : |s ^ 20 * E (n + 2) + μ (n + 4)| ≤
          s ^ 20 * (C * X ^ (K + 1) * (s ^ 22 * w)) + D * Y ^ K * (s ^ 44 * w) := by
        refine (abs_add_le _ _).trans (add_le_add ?_ hμn)
        rw [abs_mul, abs_of_nonneg hs20]
        exact mul_le_mul_of_nonneg_left ihn hs20
      refine step1.trans ?_
      have hCw : 0 ≤ C * w := mul_nonneg hC0 hw0
      have a1 : s ^ 20 * (C * X ^ (K + 1) * (s ^ 22 * w)) = s ^ 42 * (C * w * X ^ (K + 1)) := by
        ring
      have a2 : s ^ 42 * (C * w * X ^ (K + 1)) ≤ s ^ 44 * (C * w * (X * Y ^ K)) :=
        mul_le_mul h42 (mul_le_mul_of_nonneg_left hXK hCw)
          (mul_nonneg hCw (pow_nonneg hX0 _)) (pow_nonneg hs0 _)
      have a3 : D * Y ^ K * (s ^ 44 * w) ≤ C * Y ^ K * (s ^ 44 * w) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hDC hYK)
          (mul_nonneg (pow_nonneg hs0 _) hw0)
      have a4 : s ^ 44 * (C * w * (X * Y ^ K)) + C * Y ^ K * (s ^ 44 * w) =
          (s ^ 44 * w * Y ^ K * C) * (X + 1) := by ring
      have a5 : (s ^ 44 * w * Y ^ K * C) * (X + 1) ≤ (s ^ 44 * w * Y ^ K * C) * Y :=
        mul_le_mul_of_nonneg_left (by simp only [X, Y]; linarith)
          (mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg hs0 _) hw0) hYK) hC0)
      have a6 : (s ^ 44 * w * Y ^ K * C) * Y = C * Y ^ (K + 1) * (s ^ 44 * w) := by ring
      rw [a1]; linarith

/-- `|λ(m)| ≤ (m+1) (√p)^{11m}`: each `min(pʲ, p^{m−j}) ≤ √(pᵐ)`. -/
theorem abs_hypTerm_le (p m : ℕ) :
    |((hypTerm p m : ℤ) : ℝ)| ≤ ((m : ℝ) + 1) * Real.sqrt p ^ (11 * m) := by
  set s := Real.sqrt p
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hs2 : s ^ 2 = (p : ℝ) := Real.sq_sqrt (Nat.cast_nonneg p)
  have hterm : ∀ j ∈ range (m + 1),
      (((min (p ^ j) (p ^ (m - j)) : ℕ) : ℝ)) ^ 11 ≤ s ^ (11 * m) := by
    intro j hj
    have hjm : j ≤ m := Nat.lt_succ_iff.mp (mem_range.mp hj)
    have hx : ((min (p ^ j) (p ^ (m - j)) : ℕ) : ℝ) ≤ s ^ m := by
      have hsq : (min (p ^ j) (p ^ (m - j))) * (min (p ^ j) (p ^ (m - j))) ≤ p ^ m := by
        calc _ ≤ p ^ j * p ^ (m - j) := Nat.mul_le_mul (min_le_left _ _) (min_le_right _ _)
          _ = p ^ m := by rw [← pow_add, Nat.add_sub_cancel' hjm]
      have hsqR : ((min (p ^ j) (p ^ (m - j)) : ℕ) : ℝ) ^ 2 ≤ (s ^ m) ^ 2 := by
        rw [← pow_mul, mul_comm, pow_mul, hs2, sq]; exact_mod_cast hsq
      exact (pow_le_pow_iff_left₀ (Nat.cast_nonneg _) (pow_nonneg hs0 _) two_ne_zero).mp hsqR
    rw [pow_mul']
    exact pow_le_pow_left₀ (Nat.cast_nonneg _) hx 11
  have hnn : 0 ≤ ((hypTerm p m : ℤ) : ℝ) := by
    simp only [hypTerm, Int.cast_sum, Int.cast_pow, Int.cast_natCast]; positivity
  rw [abs_of_nonneg hnn]
  simp only [hypTerm, Int.cast_sum, Int.cast_pow, Int.cast_natCast]
  calc ∑ j ∈ range (m + 1), (((min (p ^ j) (p ^ (m - j)) : ℕ) : ℝ)) ^ 11
      ≤ ∑ j ∈ range (m + 1), s ^ (11 * m) := by
        refine sum_le_sum fun j hj => ?_
        exact hterm j hj
    _ = ((m : ℝ) + 1) * s ^ (11 * m) := by simp

/-- **Ordinary error bound, generic form**: an `O((m+1)^K (√p)^{11m})` bound on the non-elliptic
ES error `ε(m)` gives `|E(m)| ≤ C (m+1)^{K+1} (√p)^{11m}`. -/
theorem ordSum_error_core (H : ℕ → ℚ) (p : ℕ) [Fact p.Prime] (hHR : HurwitzPrimeSquare H p)
    (hT : TauHeckeRecurrence p) (D : ℝ) (K : ℕ)
    (hε : ∀ m : ℕ, |((esSum H (p ^ m) + 2 * (RamanujanTau.tau (p ^ m) : ℚ) : ℚ) : ℝ)| ≤
      D * ((m : ℝ) + 1) ^ K * Real.sqrt p ^ (11 * m)) :
    ∃ C : ℝ, ∀ m : ℕ,
      |((ordSum H p m + 2 * (tauPowerSum p m : ℚ) : ℚ) : ℝ)| ≤
        C * ((m : ℝ) + 1) ^ (K + 1) * Real.sqrt p ^ (11 * m) := by
  set s := Real.sqrt p with hsdef
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (Fact.out : p.Prime).one_lt.le
  have hs : 1 ≤ s := by rw [hsdef]; exact Real.one_le_sqrt.mpr hp1
  have hs0 : 0 ≤ s := by linarith
  have hs2 : s ^ 2 = (p : ℝ) := Real.sq_sqrt (Nat.cast_nonneg p)
  have hD : 0 ≤ D := by
    have := (abs_nonneg _).trans (hε 0)
    simpa using this
  let εr : ℕ → ℝ := fun m => ((esErr H p m : ℚ) : ℝ)
  have hεr : ∀ m, |εr m| ≤ D * ((m : ℝ) + 1) ^ K * s ^ (11 * m) := fun m => hε m
  let μ : ℕ → ℝ := fun n =>
    εr n - s ^ 20 * (s ^ 2 + 1) * εr (n - 2) + s ^ 42 * εr (n - 4)
  have hrec : ∀ m, ((errSum H p (m + 4) : ℚ) : ℝ) =
      s ^ 20 * ((errSum H p (m + 2) : ℚ) : ℝ) + μ (m + 4) := by
    intro m
    have h := congrArg (fun x : ℚ => (x : ℝ)) (errSum_rec H p hHR hT m)
    have e2 : m + 4 - 2 = m + 2 := by omega
    have e4 : m + 4 - 4 = m := by omega
    simp only [μ, εr, e2, e4]
    rw [h]
    have p10 : (p : ℝ) ^ 10 = s ^ 20 := by rw [← hs2]; ring
    have p21 : (p : ℝ) ^ 21 = s ^ 42 := by rw [← hs2]; ring
    push_cast
    rw [p10, p21, ← hs2]
  have hμ : ∀ m, |μ (m + 4)| ≤ (4 * D) * ((m : ℝ) + 5) ^ K * s ^ (11 * m + 44) := by
    intro m
    have e2 : m + 4 - 2 = m + 2 := by omega
    have e4 : m + 4 - 4 = m := by omega
    simp only [μ, e2, e4]
    set w := s ^ (11 * m)
    have hw0 : 0 ≤ w := pow_nonneg hs0 _
    have hn0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    set Y := (m : ℝ) + 5
    have hYK : 0 ≤ Y ^ K := by positivity
    have b4 := hεr (m + 4)
    have b2 := hεr (m + 2)
    have b0 := hεr m
    have r4 : D * ((↑(m + 4) : ℝ) + 1) ^ K * s ^ (11 * (m + 4)) = D * Y ^ K * (s ^ 44 * w) := by
      have : s ^ (11 * (m + 4)) = s ^ 44 * w := by rw [← pow_add]; ring_nf
      rw [this]; push_cast; simp only [Y]; ring
    have r2 : D * ((↑(m + 2) : ℝ) + 1) ^ K * s ^ (11 * (m + 2)) ≤ D * Y ^ K * (s ^ 22 * w) := by
      have : s ^ (11 * (m + 2)) = s ^ 22 * w := by rw [← pow_add]; ring_nf
      rw [this]
      refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (by positivity) (by push_cast; simp only [Y]; linarith) K) hD)
        (mul_nonneg (pow_nonneg hs0 _) hw0)
    have r0 : D * ((m : ℝ) + 1) ^ K * s ^ (11 * m) ≤ D * Y ^ K * w := by
      refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (by positivity) (by simp only [Y]; linarith) K) hD) hw0
    rw [r4] at b4
    have b2' := b2.trans r2
    have b0' := b0.trans r0
    have h42 : s ^ 42 ≤ s ^ 44 := pow_le_pow_right₀ hs (by norm_num)
    have hk : 0 ≤ D * Y ^ K * w := mul_nonneg (mul_nonneg hD hYK) hw0
    have hc2 : 0 ≤ s ^ 20 * (s ^ 2 + 1) := by positivity
    have t2 : |s ^ 20 * (s ^ 2 + 1) * εr (m + 2)| ≤ s ^ 20 * (s ^ 2 + 1) * (D * Y ^ K * (s ^ 22 * w)) := by
      rw [abs_mul, abs_of_nonneg hc2]; exact mul_le_mul_of_nonneg_left b2' hc2
    have t0 : |s ^ 42 * εr m| ≤ s ^ 42 * (D * Y ^ K * w) := by
      rw [abs_mul, abs_of_nonneg (pow_nonneg hs0 _)]
      exact mul_le_mul_of_nonneg_left b0' (pow_nonneg hs0 _)
    have tri : |εr (m + 4) - s ^ 20 * (s ^ 2 + 1) * εr (m + 2) + s ^ 42 * εr m| ≤
        |εr (m + 4)| + |s ^ 20 * (s ^ 2 + 1) * εr (m + 2)| + |s ^ 42 * εr m| :=
      (abs_add_le _ _).trans (add_le_add_left (abs_sub _ _) _)
    have e44 : s ^ (11 * m + 44) = s ^ 44 * w := by rw [← pow_add]; ring_nf
    rw [e44]
    have q1 : s ^ 20 * (s ^ 2 + 1) * (D * Y ^ K * (s ^ 22 * w)) =
        (D * Y ^ K * w) * s ^ 44 + (D * Y ^ K * w) * s ^ 42 := by ring
    have q2 := mul_le_mul_of_nonneg_left h42 hk
    have q3 : s ^ 42 * (D * Y ^ K * w) = (D * Y ^ K * w) * s ^ 42 := by ring
    have q4 : 4 * D * Y ^ K * (s ^ 44 * w) = 4 * ((D * Y ^ K * w) * s ^ 44) := by ring
    have q5 : D * Y ^ K * (s ^ 44 * w) = (D * Y ^ K * w) * s ^ 44 := by ring
    rw [q4]
    rw [q5] at b4
    rw [q1] at t2
    rw [q3] at t0
    linarith
  obtain ⟨C, hC⟩ := growth_of_rec s hs (fun m => ((errSum H p m : ℚ) : ℝ)) μ (4 * D) K
    (by linarith) hrec hμ
  exact ⟨C, fun m => hC m⟩

/-- **Ordinary error bound** (frozen). From ES + the prime-square relation + the Hecke
recurrence: `E(m) := ordSum H p m + 2 s_m` satisfies `E(m) = p¹⁰ E(m−2) + μ(m)` for `m ≥ 4`,
`μ(m) = −λ(m) + p¹⁰(p+1)λ(m−2) − p²¹λ(m−4)` (V3b), hence `|E(m)| ≤ C (m+1)² p^{11m/2}` (V3c).
(`h0` is not needed.) -/
theorem ordSum_error (H : ℕ → ℚ) (p : ℕ) [Fact p.Prime] (h0 : HurwitzConventions H)
    (hES : EichlerSelbergPrimePow H p) (hHR : HurwitzPrimeSquare H p)
    (hT : TauHeckeRecurrence p) :
    ∃ C : ℝ, ∀ m : ℕ,
      |((ordSum H p m + 2 * (tauPowerSum p m : ℚ) : ℚ) : ℝ)| ≤
        C * ((m : ℝ) + 1) ^ 2 * Real.sqrt p ^ (11 * m) := by
  refine ordSum_error_core H p hHR hT 1 1 fun m => ?_
  have e : esSum H (p ^ m) + 2 * (RamanujanTau.tau (p ^ m) : ℚ) = -((hypTerm p m : ℤ) : ℚ) := by
    rw [hES m]; ring
  rw [e]
  have := abs_hypTerm_le p m
  push_cast at this ⊢
  rw [abs_neg]
  linarith

/-- Same conclusion from the approximate ES (only elliptic terms exact) (frozen). -/
theorem ordSum_error_of_approx (H : ℕ → ℚ) (p : ℕ) [Fact p.Prime] (h0 : HurwitzConventions H)
    (hES : EichlerSelbergApprox H p) (hHR : HurwitzPrimeSquare H p)
    (hT : TauHeckeRecurrence p) :
    ∃ C : ℝ, ∃ k : ℕ, ∀ m : ℕ,
      |((ordSum H p m + 2 * (tauPowerSum p m : ℚ) : ℚ) : ℝ)| ≤
        C * ((m : ℝ) + 1) ^ k * Real.sqrt p ^ (11 * m) := by
  obtain ⟨D, K, hD⟩ := hES
  obtain ⟨C, hC⟩ := ordSum_error_core H p hHR hT D K hD
  exact ⟨C, K + 1, hC⟩

end RamanujanWeil.ArithPlan
