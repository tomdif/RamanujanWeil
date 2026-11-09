import RamanujanWeil.Arith.DeuringApprox
import RamanujanWeil.Arith.DeuringApproxCount

/-!
# The structural interface: per-trace counts with multiplicity ⇒ `OrdinaryDeuringApprox`

Let `m(t)` be the number of ordinary isogeny classes of trace `t` over `𝔽_q`. The per-class
lattice count (route L, `DeuringAssembly.lean`, without `surj`) gives

  `N(t) = q³(q−1)·m(t)·H(4q − t²)/2`   (`p ∤ t`, `t² < 4q`)       — `DeuringMultiplicity`.

With `d(t) = N(t) − q³(q−1)H/2 = q³(q−1)(m(t) − 1)H/2`, the `ℓ¹` defect `Σ_{p ∤ t} |d(t)|` is a
signed total as soon as `m − 1` has constant sign:

* **existence** (`m ≥ 1`): `Σ|d| = N_ord − q³(q−1)/2·O₀ ≤ q⁵ − q³(q−1)/2·(2q − C X)`
  `≤ q⁴ + q⁴·C X/2`, with `N_ord ≤ q⁵` trivial and `O₀ ≥ 2q − C X` (Kronecker–Hurwitz lower
  bound), `X = (n+1)^k (√p)ⁿ`;
* **uniqueness** (`m ≤ 1`): `Σ|d| = q³(q−1)/2·O₀ − N_ord ≤ q³(q−1)/2·(2q + C X) − (q⁵ − C'q⁴)`
  `≤ C'q⁴ + q⁴·C X/2`, with `N_ord ≥ q⁵ − C'q⁴` (`card_ordinary_lower`) and the
  Kronecker–Hurwitz upper bound.

Either way `Σ|d| = O((n+1)^k q^{9/2})`, which is `OrdinaryDeuringApprox`. For `H = hurwitz` both
Kronecker–Hurwitz bounds are proved (`ordSum0_bound`, `k = 2`).
-/

open Finset

namespace RamanujanWeil.ArithPlan

open RamanujanWeil.Ihara

set_option linter.unusedSectionVars false

/-- **Per-trace count with multiplicity** `m(t) = mult n t` (number of ordinary isogeny classes
of trace `t` over `𝔽_{pⁿ}`): `N(t) = q³(q−1)·m(t)·H(4q − t²)/2` for `p ∤ t`, `t² < 4q`. -/
def DeuringMultiplicity (H : ℕ → ℚ) (p : ℕ) [Fact p.Prime] (mult : ℕ → ℤ → ℕ) : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ t : ℤ, ¬ (p : ℤ) ∣ t → t ^ 2 < 4 * (p : ℤ) ^ n →
    (traceCount p n t : ℚ) =
      (p : ℚ) ^ (3 * n) * ((p : ℚ) ^ n - 1) * (mult n t : ℚ) *
        H (4 * (p : ℤ) ^ n - t ^ 2).toNat / 2

/-- **Kronecker–Hurwitz lower bound** on the ordinary class-number mass:
`Σ_{p ∤ t, t² ≤ 4q} H(4q − t²) ≥ 2q − C (n+1)^k (√p)ⁿ`. -/
def KroneckerHurwitzLower (H : ℕ → ℚ) (p : ℕ) [Fact p.Prime] : Prop :=
  ∃ C : ℝ, ∃ k : ℕ, ∀ n : ℕ, 1 ≤ n →
    2 * (p : ℝ) ^ n - C * ((n : ℝ) + 1) ^ k * Real.sqrt p ^ n ≤ ((ordSum0 p H n : ℚ) : ℝ)

/-- **Kronecker–Hurwitz upper bound**: `Σ_{p ∤ t, t² ≤ 4q} H(4q − t²) ≤ 2q + C (n+1)^k (√p)ⁿ`. -/
def KroneckerHurwitzUpper (H : ℕ → ℚ) (p : ℕ) [Fact p.Prime] : Prop :=
  ∃ C : ℝ, ∃ k : ℕ, ∀ n : ℕ, 1 ≤ n →
    ((ordSum0 p H n : ℚ) : ℝ) ≤ 2 * (p : ℝ) ^ n + C * ((n : ℝ) + 1) ^ k * Real.sqrt p ^ n

variable (p : ℕ) [hp : Fact p.Prime]

/-- Both Kronecker–Hurwitz bounds hold for the Hurwitz class number (`ordSum0_bound`). -/
theorem kroneckerHurwitzLower_hurwitz :
    KroneckerHurwitzLower RamanujanWeil.Arith.Hurwitz.hurwitz p := by
  obtain ⟨C, hC⟩ := ordSum0_bound p
  refine ⟨C, 2, fun n _ => ?_⟩
  have h := (abs_le.mp (hC n)).1
  push_cast at h
  linarith

theorem kroneckerHurwitzUpper_hurwitz :
    KroneckerHurwitzUpper RamanujanWeil.Arith.Hurwitz.hurwitz p := by
  obtain ⟨C, hC⟩ := ordSum0_bound p
  refine ⟨C, 2, fun n _ => ?_⟩
  have h := (abs_le.mp (hC n)).2
  push_cast at h
  linarith

lemma hurwitz_nonneg {N : ℕ} (hN : 0 < N) : 0 ≤ RamanujanWeil.Arith.Hurwitz.hurwitz N := by
  rw [RamanujanWeil.Arith.Hurwitz.hurwitz, if_neg hN.ne']
  positivity

/-- The ordinary tuple count as a sum of per-trace counts (Hasse). -/
theorem sum_traceCount_ord (hH : HasseAll p) (n : ℕ) (hn : 1 ≤ n) :
    letI : Fintype (GaloisField p n) := Fintype.ofFinite _
    open scoped Classical in
    ∑ t ∈ (tset p n).filter (fun t => ¬ (p : ℤ) ∣ t), traceCount p n t =
      #({c : Fin 5 → GaloisField p n | (wc c).Δ ≠ 0 ∧ ¬ (p : ℤ) ∣ traceOfFrob (wc c)} :
        Finset _) := by
  letI : Fintype (GaloisField p n) := Fintype.ofFinite _
  classical
  set U' := ({c : Fin 5 → GaloisField p n | (wc c).Δ ≠ 0 ∧ ¬ (p : ℤ) ∣ traceOfFrob (wc c)} :
    Finset _) with hU'
  set T := (tset p n).filter (fun t => ¬ (p : ℤ) ∣ t) with hT
  have h1 : ∀ t ∈ T, traceCount p n t = #(U'.filter (fun c => traceOfFrob (wc c) = t)) := by
    intro t ht
    rw [hT, mem_filter] at ht
    rw [traceCount]
    congr 1
    ext c
    simp only [hU', mem_filter, mem_univ, true_and]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨⟨h1, h2 ▸ ht.2⟩, h2⟩
    · rintro ⟨⟨h1, _⟩, h2⟩; exact ⟨h1, h2⟩
  rw [sum_congr rfl h1, sum_card_fiberwise_eq_card_filter, filter_true_of_mem]
  intro c hc
  simp only [hU', mem_filter, mem_univ, true_and] at hc
  rw [hT, mem_filter, mem_tset]
  exact ⟨hH n hn c hc.1, hc.2⟩

/-- `Σ_T d(t) = N_ord − q³(q−1)/2·O₀(n)` in `ℚ`. -/
lemma sum_defect (H : ℕ → ℚ) (n : ℕ) :
    ∑ t ∈ (tset p n).filter (fun t => ¬ (p : ℤ) ∣ t),
        ((traceCount p n t : ℚ) - (p : ℚ) ^ (3 * n) * ((p : ℚ) ^ n - 1) * H (nArg p n t) / 2) =
      ((∑ t ∈ (tset p n).filter (fun t => ¬ (p : ℤ) ∣ t), traceCount p n t : ℕ) : ℚ) -
        (p : ℚ) ^ (3 * n) * ((p : ℚ) ^ n - 1) / 2 * ordSum0 p H n := by
  rw [sum_sub_distrib, ordSum0, mul_sum, Nat.cast_sum]
  congr 1
  exact sum_congr rfl fun t _ => by ring

/-- The defect `d(t)` in terms of the multiplicity. -/
lemma defect_eq (H : ℕ → ℚ) (mult : ℕ → ℤ → ℕ) (hM : DeuringMultiplicity H p mult) {n : ℕ}
    (hn : 1 ≤ n) {t : ℤ} (ht : t ∈ (tset p n).filter (fun t => ¬ (p : ℤ) ∣ t)) :
    (traceCount p n t : ℚ) - (p : ℚ) ^ (3 * n) * ((p : ℚ) ^ n - 1) * H (nArg p n t) / 2 =
      (p : ℚ) ^ (3 * n) * ((p : ℚ) ^ n - 1) / 2 * ((mult n t : ℚ) - 1) * H (nArg p n t) := by
  rw [mem_filter] at ht
  rw [hM n hn t ht.2 (sq_lt_of_ord p hn ht.1 ht.2), ← nArg_eq]
  ring

lemma nArg_pos {n : ℕ} (hn : 1 ≤ n) {t : ℤ} (ht : t ∈ (tset p n).filter (fun t => ¬ (p : ℤ) ∣ t)) :
    0 < nArg p n t := by
  rw [mem_filter] at ht
  have := sq_lt_of_ord p hn ht.1 ht.2
  rw [nArg_eq]; omega

/-- Common real-number bookkeeping: `q³(q−1)/2 · C X ≤ (C/2) (n+1)^k (√p)^{9n}` etc. -/
lemma pow_facts (n : ℕ) :
    let s := Real.sqrt p
    (1 : ℝ) ≤ (p : ℝ) ^ n ∧ (p : ℝ) ^ n = s ^ (2 * n) ∧ s ^ (8 * n) * s ^ n = s ^ (9 * n) ∧
      s ^ (8 * n) ≤ s ^ (9 * n) := by
  intro s
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.out.one_lt.le
  have hs : 1 ≤ s := Real.one_le_sqrt.mpr hp1
  have hs2 : s ^ 2 = (p : ℝ) := Real.sq_sqrt (Nat.cast_nonneg p)
  refine ⟨one_le_pow₀ hp1, by rw [← hs2, ← pow_mul], by rw [← pow_add]; ring_nf,
    pow_le_pow_right₀ hs (by omega)⟩

/-- **Existence variant.** Per-trace counts with multiplicity `m ≥ 1` + the Kronecker–Hurwitz
lower bound (+ `H ≥ 0`, Hasse) ⇒ `OrdinaryDeuringApprox`. -/
theorem ordinaryDeuringApprox_of_mult_exists (H : ℕ → ℚ) (mult : ℕ → ℤ → ℕ)
    (hM : DeuringMultiplicity H p mult)
    (hex : ∀ n : ℕ, 1 ≤ n → ∀ t : ℤ, ¬ (p : ℤ) ∣ t → t ^ 2 < 4 * (p : ℤ) ^ n → 1 ≤ mult n t)
    (hpos : ∀ N : ℕ, 0 < N → 0 ≤ H N) (hKH : KroneckerHurwitzLower H p) (hH : HasseAll p) :
    OrdinaryDeuringApprox H p := by
  obtain ⟨C, k, hC⟩ := hKH
  set Cp := max C 0
  refine ⟨1 + Cp / 2, k, fun n hn => ?_⟩
  letI : Fintype (GaloisField p n) := Fintype.ofFinite _
  classical
  set T := (tset p n).filter (fun t => ¬ (p : ℤ) ∣ t) with hT
  obtain ⟨hQ1, hQs, h9, h89⟩ := pow_facts p n
  set s := Real.sqrt p with hsdef
  set Q : ℝ := (p : ℝ) ^ n with hQ
  set X : ℝ := ((n : ℝ) + 1) ^ k * s ^ n with hX
  have hn1 : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have hk0 : (1 : ℝ) ≤ ((n : ℝ) + 1) ^ k := one_le_pow₀ hn1
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hX0 : 0 ≤ X := by positivity
  -- each defect is nonnegative
  have hnn : ∀ t ∈ T, (0 : ℚ) ≤ (traceCount p n t : ℚ) -
      (p : ℚ) ^ (3 * n) * ((p : ℚ) ^ n - 1) * H (nArg p n t) / 2 := by
    intro t ht
    rw [defect_eq p H mult hM hn ht]
    have ht' := mem_filter.mp ht
    have hm : (1 : ℚ) ≤ mult n t := by
      exact_mod_cast hex n hn t ht'.2 (sq_lt_of_ord p hn ht'.1 ht'.2)
    have hq1 : (1 : ℚ) ≤ (p : ℚ) ^ n := one_le_pow₀ (by exact_mod_cast hp.out.one_lt.le)
    have := hpos _ (nArg_pos p hn ht)
    have : (0 : ℚ) ≤ (p : ℚ) ^ (3 * n) := by positivity
    have : (0 : ℚ) ≤ (mult n t : ℚ) - 1 := by linarith
    have : (0 : ℚ) ≤ (p : ℚ) ^ n - 1 := by linarith
    positivity
  have habs : ∑ t ∈ T, |(((traceCount p n t : ℚ) -
      (p : ℚ) ^ (3 * n) * ((p : ℚ) ^ n - 1) * H (nArg p n t) / 2 : ℚ) : ℝ)| =
      ((((∑ t ∈ T, traceCount p n t : ℕ) : ℚ) -
        (p : ℚ) ^ (3 * n) * ((p : ℚ) ^ n - 1) / 2 * ordSum0 p H n : ℚ) : ℝ) := by
    rw [← sum_defect, Rat.cast_sum]
    exact sum_congr rfl fun t ht => abs_of_nonneg (by exact_mod_cast hnn t ht)
  rw [habs]
  -- `N_ord ≤ q⁵`
  have hN : ((∑ t ∈ T, traceCount p n t : ℕ) : ℝ) ≤ Q ^ 5 := by
    rw [hT, sum_traceCount_ord p hH n hn]
    have hcard : #({c : Fin 5 → GaloisField p n | (wc c).Δ ≠ 0 ∧
        ¬ (p : ℤ) ∣ traceOfFrob (wc c)} : Finset _) ≤ (p ^ n) ^ 5 := by
      refine (card_le_univ _).trans (le_of_eq ?_)
      rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_eq_nat_card,
        GaloisField.card p n (by omega)]
    rw [hQ]; exact_mod_cast hcard
  have hO := hC n hn
  have hO' : 2 * Q - Cp * X ≤ ((ordSum0 p H n : ℚ) : ℝ) := by
    refine le_trans ?_ hO
    have : C * (((n : ℝ) + 1) ^ k * s ^ n) ≤ Cp * X :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) hX0
    rw [hX] at this ⊢; nlinarith
  push_cast
  set O : ℝ := ((ordSum0 p H n : ℚ) : ℝ)
  have hQ3 : 0 ≤ Q ^ 3 * (Q - 1) / 2 := by
    have : 0 ≤ Q - 1 := by linarith
    positivity
  have hmain : ((∑ t ∈ T, traceCount p n t : ℕ) : ℝ) - Q ^ 3 * (Q - 1) / 2 * O ≤
      Q ^ 4 + Q ^ 4 * (Cp * X) / 2 := by
    have h1 : Q ^ 3 * (Q - 1) / 2 * (2 * Q - Cp * X) ≤ Q ^ 3 * (Q - 1) / 2 * O :=
      mul_le_mul_of_nonneg_left hO' hQ3
    have h2 : Q ^ 3 * (Q - 1) / 2 * (Cp * X) ≤ Q ^ 4 * (Cp * X) / 2 := by
      have : 0 ≤ Cp * X := mul_nonneg (le_max_right _ _) hX0
      have : Q ^ 3 * (Q - 1) ≤ Q ^ 4 := by nlinarith [pow_pos (by linarith : (0:ℝ) < Q) 3]
      nlinarith
    nlinarith
  have hQ4 : Q ^ 4 = s ^ (8 * n) := by rw [hQs, ← pow_mul]; ring_nf
  have hCp : 0 ≤ Cp := le_max_right _ _
  have hfin : Q ^ 4 + Q ^ 4 * (Cp * X) / 2 ≤ (1 + Cp / 2) * ((n : ℝ) + 1) ^ k * s ^ (9 * n) := by
    rw [hQ4, hX]
    have e : s ^ (8 * n) * (Cp * (((n : ℝ) + 1) ^ k * s ^ n)) / 2 =
        Cp / 2 * ((n : ℝ) + 1) ^ k * (s ^ (8 * n) * s ^ n) := by ring
    rw [e, h9]
    have : s ^ (8 * n) ≤ ((n : ℝ) + 1) ^ k * s ^ (9 * n) :=
      h89.trans (le_mul_of_one_le_left (pow_nonneg hs0 _) hk0)
    nlinarith
  push_cast at hmain
  have hp3 : (p : ℝ) ^ (3 * n) * ((p : ℝ) ^ n - 1) / 2 = Q ^ 3 * (Q - 1) / 2 := by
    rw [hQ, ← pow_mul, mul_comm 3 n]
  rw [hp3]
  linarith

/-- **Uniqueness variant.** Per-trace counts with multiplicity `m ≤ 1` (Tate) + the
Kronecker–Hurwitz upper bound (+ `H ≥ 0`, Hasse) ⇒ `OrdinaryDeuringApprox`. The ordinary tuple
count `≥ q⁵ − C'q⁴` is proved (`card_ordinary_lower`). -/
theorem ordinaryDeuringApprox_of_mult_unique (H : ℕ → ℚ) (mult : ℕ → ℤ → ℕ)
    (hM : DeuringMultiplicity H p mult)
    (huniq : ∀ n : ℕ, 1 ≤ n → ∀ t : ℤ, ¬ (p : ℤ) ∣ t → t ^ 2 < 4 * (p : ℤ) ^ n → mult n t ≤ 1)
    (hpos : ∀ N : ℕ, 0 < N → 0 ≤ H N) (hKH : KroneckerHurwitzUpper H p) (hH : HasseAll p) :
    OrdinaryDeuringApprox H p := by
  obtain ⟨C, k, hC⟩ := hKH
  set Cp := max C 0
  set C' : ℝ := ((deltaDeg + p : ℕ) : ℝ)
  refine ⟨C' + Cp / 2, k, fun n hn => ?_⟩
  letI : Fintype (GaloisField p n) := Fintype.ofFinite _
  classical
  set T := (tset p n).filter (fun t => ¬ (p : ℤ) ∣ t) with hT
  obtain ⟨hQ1, hQs, h9, h89⟩ := pow_facts p n
  set s := Real.sqrt p with hsdef
  set Q : ℝ := (p : ℝ) ^ n with hQ
  set X : ℝ := ((n : ℝ) + 1) ^ k * s ^ n with hX
  have hn1 : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have hk0 : (1 : ℝ) ≤ ((n : ℝ) + 1) ^ k := one_le_pow₀ hn1
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hX0 : 0 ≤ X := by positivity
  -- each defect is nonpositive
  have hnp : ∀ t ∈ T, (traceCount p n t : ℚ) -
      (p : ℚ) ^ (3 * n) * ((p : ℚ) ^ n - 1) * H (nArg p n t) / 2 ≤ 0 := by
    intro t ht
    rw [defect_eq p H mult hM hn ht]
    have ht' := mem_filter.mp ht
    have hm : (mult n t : ℚ) ≤ 1 := by
      exact_mod_cast huniq n hn t ht'.2 (sq_lt_of_ord p hn ht'.1 ht'.2)
    have hq1 : (1 : ℚ) ≤ (p : ℚ) ^ n := one_le_pow₀ (by exact_mod_cast hp.out.one_lt.le)
    have hH0 := hpos _ (nArg_pos p hn ht)
    have : (0 : ℚ) ≤ (p : ℚ) ^ (3 * n) * ((p : ℚ) ^ n - 1) / 2 := by
      have : (0 : ℚ) ≤ (p : ℚ) ^ n - 1 := by linarith
      positivity
    have : (0 : ℚ) ≤ (1 - (mult n t : ℚ)) * H (nArg p n t) :=
      mul_nonneg (by linarith) hH0
    nlinarith
  have habs : ∑ t ∈ T, |(((traceCount p n t : ℚ) -
      (p : ℚ) ^ (3 * n) * ((p : ℚ) ^ n - 1) * H (nArg p n t) / 2 : ℚ) : ℝ)| =
      -((((∑ t ∈ T, traceCount p n t : ℕ) : ℚ) -
        (p : ℚ) ^ (3 * n) * ((p : ℚ) ^ n - 1) / 2 * ordSum0 p H n : ℚ) : ℝ) := by
    rw [← sum_defect, Rat.cast_sum, ← sum_neg_distrib]
    exact sum_congr rfl fun t ht => abs_of_nonpos (by exact_mod_cast hnp t ht)
  rw [habs]
  -- `N_ord ≥ q⁵ − C'q⁴`
  have hN : Q ^ 5 ≤ ((∑ t ∈ T, traceCount p n t : ℕ) : ℝ) + C' * Q ^ 4 := by
    rw [hT, sum_traceCount_ord p hH n hn]
    have h := card_ordinary_lower (F := GaloisField p n) p
    have hcF : Fintype.card (GaloisField p n) = p ^ n := by
      rw [Fintype.card_eq_nat_card, GaloisField.card p n (by omega)]
    rw [hcF] at h
    have h' : ((p ^ n) ^ 5 : ℕ) ≤ (#({c : Fin 5 → GaloisField p n | (wc c).Δ ≠ 0 ∧
        ¬ (p : ℤ) ∣ traceOfFrob (wc c)} : Finset _) + (deltaDeg + p) * (p ^ n) ^ 4 : ℕ) := by
      convert h using 3
    have h'' : (((p ^ n) ^ 5 : ℕ) : ℝ) ≤ ((#({c : Fin 5 → GaloisField p n | (wc c).Δ ≠ 0 ∧
        ¬ (p : ℤ) ∣ traceOfFrob (wc c)} : Finset _) + (deltaDeg + p) * (p ^ n) ^ 4 : ℕ) : ℝ) := by
      exact_mod_cast h'
    push_cast at h''
    rw [hQ]
    simp only [C']
    push_cast
    linarith
  have hO := hC n hn
  have hO' : ((ordSum0 p H n : ℚ) : ℝ) ≤ 2 * Q + Cp * X := by
    refine hO.trans ?_
    have : C * (((n : ℝ) + 1) ^ k * s ^ n) ≤ Cp * X :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) hX0
    rw [hX] at this ⊢; nlinarith
  push_cast
  set O : ℝ := ((ordSum0 p H n : ℚ) : ℝ)
  have hQ3 : 0 ≤ Q ^ 3 * (Q - 1) / 2 := by
    have : 0 ≤ Q - 1 := by linarith
    positivity
  have hCp : 0 ≤ Cp := le_max_right _ _
  have hmain : Q ^ 3 * (Q - 1) / 2 * O - ((∑ t ∈ T, traceCount p n t : ℕ) : ℝ) ≤
      C' * Q ^ 4 + Q ^ 4 * (Cp * X) / 2 := by
    have h1 : Q ^ 3 * (Q - 1) / 2 * O ≤ Q ^ 3 * (Q - 1) / 2 * (2 * Q + Cp * X) :=
      mul_le_mul_of_nonneg_left hO' hQ3
    have h2 : Q ^ 3 * (Q - 1) / 2 * (Cp * X) ≤ Q ^ 4 * (Cp * X) / 2 := by
      have : 0 ≤ Cp * X := mul_nonneg hCp hX0
      have : Q ^ 3 * (Q - 1) ≤ Q ^ 4 := by nlinarith [pow_pos (by linarith : (0:ℝ) < Q) 3]
      nlinarith
    have h3 : Q ^ 3 * (Q - 1) / 2 * (2 * Q) = Q ^ 5 - Q ^ 4 := by ring
    have hQ4 : 0 ≤ Q ^ 4 := by positivity
    nlinarith
  have hQ4 : Q ^ 4 = s ^ (8 * n) := by rw [hQs, ← pow_mul]; ring_nf
  have hC'0 : 0 ≤ C' := Nat.cast_nonneg _
  have hfin : C' * Q ^ 4 + Q ^ 4 * (Cp * X) / 2 ≤
      (C' + Cp / 2) * ((n : ℝ) + 1) ^ k * s ^ (9 * n) := by
    rw [hQ4, hX]
    have e : s ^ (8 * n) * (Cp * (((n : ℝ) + 1) ^ k * s ^ n)) / 2 =
        Cp / 2 * ((n : ℝ) + 1) ^ k * (s ^ (8 * n) * s ^ n) := by ring
    rw [e, h9]
    have : s ^ (8 * n) ≤ ((n : ℝ) + 1) ^ k * s ^ (9 * n) :=
      h89.trans (le_mul_of_one_le_left (pow_nonneg hs0 _) hk0)
    nlinarith
  push_cast at hmain
  have hp3 : (p : ℝ) ^ (3 * n) * ((p : ℝ) ^ n - 1) / 2 = Q ^ 3 * (Q - 1) / 2 := by
    rw [hQ, ← pow_mul, mul_comm 3 n]
  rw [hp3]
  linarith

/-- **Existence variant for `hurwitz`** (Kronecker–Hurwitz discharged). -/
theorem ordinaryDeuringApprox_of_mult_exists_hurwitz (mult : ℕ → ℤ → ℕ)
    (hM : DeuringMultiplicity RamanujanWeil.Arith.Hurwitz.hurwitz p mult)
    (hex : ∀ n : ℕ, 1 ≤ n → ∀ t : ℤ, ¬ (p : ℤ) ∣ t → t ^ 2 < 4 * (p : ℤ) ^ n → 1 ≤ mult n t)
    (hH : HasseAll p) : OrdinaryDeuringApprox RamanujanWeil.Arith.Hurwitz.hurwitz p :=
  ordinaryDeuringApprox_of_mult_exists p _ mult hM hex (fun _ h => hurwitz_nonneg h)
    (kroneckerHurwitzLower_hurwitz p) hH

/-- **Uniqueness variant for `hurwitz`** (Kronecker–Hurwitz discharged). -/
theorem ordinaryDeuringApprox_of_mult_unique_hurwitz (mult : ℕ → ℤ → ℕ)
    (hM : DeuringMultiplicity RamanujanWeil.Arith.Hurwitz.hurwitz p mult)
    (huniq : ∀ n : ℕ, 1 ≤ n → ∀ t : ℤ, ¬ (p : ℤ) ∣ t → t ^ 2 < 4 * (p : ℤ) ^ n → mult n t ≤ 1)
    (hH : HasseAll p) : OrdinaryDeuringApprox RamanujanWeil.Arith.Hurwitz.hurwitz p :=
  ordinaryDeuringApprox_of_mult_unique p _ mult hM huniq (fun _ h => hurwitz_nonneg h)
    (kroneckerHurwitzUpper_hurwitz p) hH

end RamanujanWeil.ArithPlan
