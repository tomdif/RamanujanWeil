import Mathlib
import RamanujanWeil.Arith.SupersingularTrace

/-!
# The supersingular count bound `#{c : Δ ≠ 0, p ∣ a_c} ≤ p · q⁴`

By `dvd_traceOfFrob_iff_of_finite`, the bad tuples lie in the zero set of
* `X₀` (p = 2), of total degree 1;
* the generic Hasse polynomial `hassePoly F p = hasseInv p (X₀, …, X₄)` (p odd), of total degree
  `≤ p − 1`, nonzero because it is `4^{(p−1)/2} ≠ 0` at `c = (0,1,0,0,0)`.

Schwartz–Zippel (`MvPolynomial.schwartz_zippel_totalDegree`) bounds the zero set by
`deg · q⁴ ≤ p · q⁴`. The constant `C = p` is uniform in `n`.
-/

open Finset Polynomial

namespace RamanujanWeil.ArithPlan

open RamanujanWeil.Ihara

/-! ## Total degree of coefficients of powers -/

section MvDeg

variable {σ R : Type*} [CommRing R]

lemma totalDegree_coeff_pow_le (f : (MvPolynomial σ R)[X]) (d : ℕ)
    (hf : ∀ i, (f.coeff i).totalDegree ≤ d) (m : ℕ) :
    ∀ i, ((f ^ m).coeff i).totalDegree ≤ m * d := by
  induction m with
  | zero =>
    intro i; rw [pow_zero, coeff_one]
    split_ifs
    · simp [MvPolynomial.totalDegree_one]
    · simp [MvPolynomial.totalDegree_zero]
  | succ m ih =>
    intro i
    rw [pow_succ, coeff_mul]
    refine (MvPolynomial.totalDegree_finsetSum _ _).trans (Finset.sup_le fun x _ => ?_)
    refine (MvPolynomial.totalDegree_mul _ _).trans ?_
    have := ih x.1; have := hf x.2
    rw [Nat.succ_mul]; omega

lemma totalDegree_ofNat_le (n : ℕ) [n.AtLeastTwo] :
    (OfNat.ofNat n : MvPolynomial σ R).totalDegree ≤ 0 := by
  rw [← map_ofNat MvPolynomial.C n, MvPolynomial.totalDegree_C]

lemma totalDegree_add_le' {a b : MvPolynomial σ R} {d : ℕ} (ha : a.totalDegree ≤ d)
    (hb : b.totalDegree ≤ d) : (a + b).totalDegree ≤ d :=
  (MvPolynomial.totalDegree_add _ _).trans (max_le ha hb)

lemma totalDegree_mul_le' {a b : MvPolynomial σ R} {d e : ℕ} (ha : a.totalDegree ≤ d)
    (hb : b.totalDegree ≤ e) : (a * b).totalDegree ≤ d + e :=
  (MvPolynomial.totalDegree_mul _ _).trans (Nat.add_le_add ha hb)

end MvDeg

/-! ## The generic Hasse polynomial -/

section Generic

variable (F : Type*) [Field F]

/-- The Hasse invariant as a polynomial in the five Weierstrass coefficients. -/
noncomputable def hassePoly (p : ℕ) : MvPolynomial (Fin 5) F :=
  hasseInv p (fun i => MvPolynomial.X i)

variable {F}

lemma eval_hassePoly (p : ℕ) (c : Fin 5 → F) :
    MvPolynomial.eval c (hassePoly F p) = hasseInv p c := by
  unfold hassePoly
  rw [hasseInv_eq, hasseInv_eq, ← Polynomial.coeff_map, Polynomial.map_pow]
  congr 2
  simp [hasseCubic, wc, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆]

omit [Field F] in
lemma coeff_hasseCubic {R : Type*} [CommRing R] (c : Fin 5 → R) (i : ℕ) :
    (hasseCubic c).coeff i = if i = 0 then (wc c).b₆ else if i = 1 then 2 * (wc c).b₄ else
      if i = 2 then (wc c).b₂ else if i = 3 then 4 else 0 := by
  rcases i with _ | _ | _ | _ | i <;> simp [hasseCubic, coeff_X, coeff_C, coeff_X_pow]

lemma totalDegree_hasseCubic_coeff (i : ℕ) :
    ((hasseCubic (fun j : Fin 5 => (MvPolynomial.X j : MvPolynomial (Fin 5) F))).coeff i
      ).totalDegree ≤ 2 := by
  have hX : ∀ j : Fin 5, (MvPolynomial.X j : MvPolynomial (Fin 5) F).totalDegree ≤ 1 :=
    fun j => (MvPolynomial.totalDegree_X j).le
  have hX2 : ∀ j : Fin 5, ((MvPolynomial.X j : MvPolynomial (Fin 5) F) ^ 2).totalDegree ≤ 2 :=
    fun j => (MvPolynomial.totalDegree_X_pow j 2).le
  have h4 := totalDegree_ofNat_le (σ := Fin 5) (R := F) 4
  have h2 := totalDegree_ofNat_le (σ := Fin 5) (R := F) 2
  rw [coeff_hasseCubic]
  simp only [wc, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆]
  split_ifs
  · exact totalDegree_add_le' (hX2 2) ((totalDegree_mul_le' h4 (hX 4)).trans (by norm_num))
  · exact (totalDegree_mul_le' h2 (totalDegree_add_le'
      ((totalDegree_mul_le' h2 (hX 3)).trans (by norm_num))
      (totalDegree_mul_le' (hX 0) (hX 2)))).trans (by norm_num)
  · exact totalDegree_add_le' (hX2 0) ((totalDegree_mul_le' h4 (hX 1)).trans (by norm_num))
  · exact h4.trans (by norm_num)
  · simp [MvPolynomial.totalDegree_zero]

lemma totalDegree_hassePoly_le (p : ℕ) : (hassePoly F p).totalDegree ≤ p := by
  unfold hassePoly
  rw [hasseInv_eq]
  refine (totalDegree_coeff_pow_le _ 2 totalDegree_hasseCubic_coeff _ _).trans ?_
  omega

lemma hasseInv_witness {p : ℕ} (hp : Odd p) :
    hasseInv p (![0, 1, 0, 0, 0] : Fin 5 → F) = 4 ^ ((p - 1) / 2) := by
  have hf : hasseCubic (![0, 1, 0, 0, 0] : Fin 5 → F) = (4 * X + 4) * X ^ 2 := by
    simp [hasseCubic, wc, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆]
    rw [map_ofNat C 4]
    ring
  obtain ⟨r, hr⟩ := hp
  have e1 : (p - 1) / 2 = r := by omega
  have e2 : p - 1 = 0 + 2 * r := by omega
  rw [hasseInv_eq, hf, mul_pow, ← pow_mul, e1, e2, mul_comm 2 r, coeff_mul_X_pow,
    coeff_zero_eq_eval_zero]
  simp

end Generic

/-! ## Schwartz–Zippel and the count -/

lemma card_zero_set_le {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (P : MvPolynomial (Fin 5) F) (hP : P ≠ 0) :
    #{c : Fin 5 → F | MvPolynomial.eval c P = 0} ≤ P.totalDegree * Fintype.card F ^ 4 := by
  have h := MvPolynomial.schwartz_zippel_totalDegree hP (univ : Finset F)
  rw [Fintype.piFinset_univ, card_univ] at h
  have hq : 0 < Fintype.card F := Fintype.card_pos
  rw [div_le_div_iff₀ (by positivity) (by exact_mod_cast hq)] at h
  have h' : #{c : Fin 5 → F | MvPolynomial.eval c P = 0} * Fintype.card F ≤
      P.totalDegree * Fintype.card F ^ 4 * Fintype.card F := by
    rw [mul_assoc, ← pow_succ]; exact_mod_cast h
  exact Nat.le_of_mul_le_mul_right h' hq

open scoped Classical in
/-- **The supersingular count bound over any finite field of characteristic `p`.** -/
theorem card_dvd_traceOfFrob_le {F : Type*} [Field F] [Fintype F] (p : ℕ) [Fact p.Prime]
    [CharP F p] :
    #{c : Fin 5 → F | (wc c).Δ ≠ 0 ∧ (p : ℤ) ∣ traceOfFrob (wc c)} ≤ p * Fintype.card F ^ 4 := by
  have hp := (Fact.out : p.Prime)
  by_cases hp2 : p = 2
  · subst hp2
    have hP : (MvPolynomial.X 0 : MvPolynomial (Fin 5) F) ≠ 0 := MvPolynomial.X_ne_zero _
    refine (card_le_card ?_).trans ((card_zero_set_le _ hP).trans ?_)
    · intro c hc
      simp only [mem_filter, mem_univ, true_and] at hc ⊢
      have := (dvd_traceOfFrob_iff_of_finite 2 c hc.1).mp hc.2
      simpa using this
    · rw [MvPolynomial.totalDegree_X]
      exact Nat.mul_le_mul_right _ (by norm_num)
  · have hodd : Odd p := hp.odd_of_ne_two hp2
    have hP : hassePoly F p ≠ 0 := by
      intro h
      have := eval_hassePoly (F := F) p ![0, 1, 0, 0, 0]
      rw [h, map_zero, hasseInv_witness hodd] at this
      have h2 : (2 : F) ≠ 0 := by
        intro h2
        have := (CharP.cast_eq_zero_iff F p 2).mp (by exact_mod_cast h2)
        exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp this)
      exact pow_ne_zero _ (show (4 : F) ≠ 0 by
        rw [show (4 : F) = 2 * 2 by norm_num]; exact mul_ne_zero h2 h2) this.symm
    refine (card_le_card ?_).trans ((card_zero_set_le _ hP).trans ?_)
    · intro c hc
      simp only [mem_filter, mem_univ, true_and] at hc ⊢
      have := (dvd_traceOfFrob_iff_of_finite p c hc.1).mp hc.2
      simp only [hp2, ↓reduceIte] at this
      rw [eval_hassePoly]; exact this
    · exact Nat.mul_le_mul_right _ (totalDegree_hassePoly_le p)

/-- `#{c : Δ ≠ 0, p ∣ a_c} ≤ C·q⁴` (verbatim from `scratch/ArithInterfaces.lean`). -/
def SupersingularCountBound (p : ℕ) [Fact p.Prime] : Prop :=
  ∃ C : ℕ, ∀ n : ℕ, 1 ≤ n →
    (letI : Fintype (GaloisField p n) := Fintype.ofFinite _
     open scoped Classical in
     ({c : Fin 5 → GaloisField p n | (wc c).Δ ≠ 0 ∧ (p : ℤ) ∣ traceOfFrob (wc c)} :
        Finset _).card) ≤ C * p ^ (4 * n)

/-- **The supersingular count bound**, with `C = p`. -/
theorem supersingularCountBound (p : ℕ) [Fact p.Prime] : SupersingularCountBound p := by
  refine ⟨p, fun n hn => ?_⟩
  letI : Fintype (GaloisField p n) := Fintype.ofFinite _
  have hq : Fintype.card (GaloisField p n) = p ^ n := by
    rw [Fintype.card_eq_nat_card, GaloisField.card p n (by omega)]
  have h := card_dvd_traceOfFrob_le (F := GaloisField p n) p
  rw [hq, ← pow_mul, mul_comm n 4] at h
  exact h

end RamanujanWeil.ArithPlan
