import RamanujanWeil.Arith.AssemblyVocab
import RamanujanWeil.Arith.TauHecke

/-!
# R-ord assembly, part 1: the ordinary-sum recursion (pure algebra)

For `q = pᵐ` write `A(m) = esSum H (pᵐ)`, `O(m) = ordSum H p m` and `P(m) = A(m) − O(m)` (the
`p ∣ t` part). With the prime-square relation `HurwitzPrimeSquare H p` alone:

* `sum_dvd_reindex`: `Σ_{t ∈ T(m+2), p ∣ t} g t = Σ_{t ∈ T(m)} g (p t)`;
* `ordSum_rec`: `O(m+4) = A(m+4) − p¹⁰((p+1)A(m+2) − O(m+2) − p¹¹A(m))`.

With the Hecke recurrence, `tauPowerSum_add_two`: `s_{m+2} = τ(p^{m+2}) − p¹¹τ(pᵐ)`; hence
(`errSum_rec`) `E(m) := O(m) + 2 s_m` satisfies
`E(m+4) = p¹⁰ E(m+2) + ε(m+4) − p¹⁰(p+1) ε(m+2) + p²¹ ε(m)`, `ε(k) := A(k) + 2τ(pᵏ)`.
(`HurwitzConventions` is not needed: `4q − t² ≡ 0, 3 mod 4` holds automatically.)
-/

open Finset

namespace RamanujanWeil.ArithPlan

open RamanujanWeil.Ihara

set_option linter.unusedSectionVars false

section Recursion

variable (p : ℕ) [hp : Fact p.Prime]

/-- The summation range `{t : t² ≤ 4pᵐ}` of `esSum H (pᵐ)`. -/
def tset (m : ℕ) : Finset ℤ :=
  (Icc (-(2 * ((p ^ m : ℕ) : ℤ))) (2 * ((p ^ m : ℕ) : ℤ))).filter
    (fun t => t ^ 2 ≤ 4 * ((p ^ m : ℕ) : ℤ))

/-- `4pᵐ − t²` as a natural number. -/
def nArg (m : ℕ) (t : ℤ) : ℕ := (4 * ((p ^ m : ℕ) : ℤ) - t ^ 2).toNat

/-- `h₁₀(t, pᵐ)` over `ℚ`. -/
def hq (m : ℕ) (t : ℤ) : ℚ := (symTrace 10 t (p ^ m : ℕ) : ℚ)

lemma esSum_eq (H : ℕ → ℚ) (m : ℕ) :
    esSum H (p ^ m) = ∑ t ∈ tset p m, hq p m t * H (nArg p m t) := rfl

lemma ordSum_eq (H : ℕ → ℚ) (m : ℕ) :
    ordSum H p m = ∑ t ∈ (tset p m).filter (fun t => ¬ (p : ℤ) ∣ t),
      hq p m t * H (nArg p m t) := by
  unfold ordSum tset hq nArg
  rw [filter_filter]

lemma one_le_ppow (m : ℕ) : (1 : ℤ) ≤ ((p ^ m : ℕ) : ℤ) := by
  have := Nat.one_le_pow m p hp.out.pos
  exact_mod_cast this

lemma cast_ppow (m : ℕ) : ((p ^ m : ℕ) : ℤ) = (p : ℤ) ^ m := by push_cast; rfl

lemma mem_tset {m : ℕ} {t : ℤ} : t ∈ tset p m ↔ t ^ 2 ≤ 4 * (p : ℤ) ^ m := by
  have hQ := one_le_ppow p m
  rw [tset, mem_filter, mem_Icc, ← cast_ppow]
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨⟨?_, ?_⟩, h⟩
    · by_contra hc; have hc := not_le.mp hc; nlinarith
    · by_contra hc; have hc := not_le.mp hc; nlinarith

lemma nArg_cast {m : ℕ} {t : ℤ} (ht : t ∈ tset p m) :
    ((nArg p m t : ℕ) : ℤ) = 4 * (p : ℤ) ^ m - t ^ 2 := by
  rw [mem_tset] at ht
  rw [nArg, cast_ppow, Int.toNat_of_nonneg (by linarith)]

lemma symTrace_ten (a q : ℤ) :
    symTrace 10 a q = a ^ 10 - 9 * q * a ^ 8 + 28 * q ^ 2 * a ^ 6 - 35 * q ^ 3 * a ^ 4 +
      15 * q ^ 4 * a ^ 2 - q ^ 5 := by
  simp [symTrace, Finset.sum_range_succ, Nat.choose]
  ring

lemma hq_scale (m : ℕ) (t : ℤ) : hq p (m + 2) (p * t) = (p : ℚ) ^ 10 * hq p m t := by
  unfold hq
  rw [cast_ppow, cast_ppow, symTrace_ten, symTrace_ten]
  push_cast; ring

lemma nArg_scale {m : ℕ} {t : ℤ} (ht : t ∈ tset p m) :
    nArg p (m + 2) (p * t) = p ^ 2 * nArg p m t := by
  apply Int.ofNat.inj
  have h1 := nArg_cast p ht
  rw [mem_tset] at ht
  have h2 : (0 : ℤ) ≤ 4 * (p : ℤ) ^ (m + 2) - (p * t) ^ 2 := by
    have : (4 * (p : ℤ) ^ (m + 2) - (p * t) ^ 2) = (p : ℤ) ^ 2 * (4 * (p : ℤ) ^ m - t ^ 2) := by
      ring
    rw [this]; exact mul_nonneg (by positivity) (by linarith)
  simp only [Int.ofNat_eq_natCast]
  rw [nArg, cast_ppow, Int.toNat_of_nonneg h2]
  push_cast; rw [h1]; ring

/-- **Reindexing** `t = p t'`: `Σ_{t ∈ T(m+2), p ∣ t} g t = Σ_{t' ∈ T(m)} g (p t')`. -/
lemma sum_dvd_reindex (m : ℕ) (g : ℤ → ℚ) :
    ∑ t ∈ (tset p (m + 2)).filter (fun t => (p : ℤ) ∣ t), g t =
      ∑ t ∈ tset p m, g (p * t) := by
  have hp0 : (0 : ℤ) < p := by exact_mod_cast hp.out.pos
  symm
  apply Finset.sum_nbij' (fun t => (p : ℤ) * t) (fun t => t / p)
  · intro t ht
    simp only [mem_filter] at ht ⊢
    rw [mem_tset] at ht
    refine ⟨?_, dvd_mul_right _ _⟩
    rw [mem_tset]
    have : (p * t) ^ 2 = (p : ℤ) ^ 2 * t ^ 2 := by ring
    rw [this, pow_add]
    nlinarith [pow_pos hp0 2]
  · intro t ht
    simp only [mem_filter] at ht ⊢
    obtain ⟨ht, u, rfl⟩ := ht
    rw [mem_tset] at ht ⊢
    rw [Int.mul_ediv_cancel_left _ hp0.ne']
    have : (p * u) ^ 2 = (p : ℤ) ^ 2 * u ^ 2 := by ring
    rw [this, pow_add] at ht
    have hp2 : (0 : ℤ) < (p : ℤ) ^ 2 := by positivity
    nlinarith
  · intro t _
    simp [Int.mul_ediv_cancel_left _ hp0.ne']
  · intro t ht
    simp only [mem_filter] at ht
    exact Int.mul_ediv_cancel' ht.2
  · intro t _; rfl

/-- `4pᵐ − t² ≡ 0, 3 mod 4`. -/
lemma nArg_mod {m : ℕ} {t : ℤ} (ht : t ∈ tset p m) :
    nArg p m t % 4 = 0 ∨ nArg p m t % 4 = 3 := by
  have h1 := nArg_cast p ht
  have h2 : t ^ 2 % 4 = 0 ∨ t ^ 2 % 4 = 1 := by
    have : t ^ 2 % 4 = (t % 4) * (t % 4) % 4 := by rw [sq, Int.mul_emod]
    have h4 : t % 4 = 0 ∨ t % 4 = 1 ∨ t % 4 = 2 ∨ t % 4 = 3 := by omega
    rcases h4 with h | h | h | h <;> rw [this, h] <;> norm_num
  generalize t ^ 2 = Y at h1 h2
  generalize (p : ℤ) ^ m = X at h1
  omega

lemma prime_int : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp.out

/-- HR on the ordinary part: `p ∤ t`, `q = p^{k+1}` ⇒ `H(p²(4q − t²)) = p·H(4q − t²)`. -/
lemma hr_ord (H : ℕ → ℚ) (hHR : HurwitzPrimeSquare H p) (k : ℕ) {t : ℤ}
    (ht : t ∈ tset p (k + 1)) (hpt : ¬ (p : ℤ) ∣ t) :
    H (p ^ 2 * nArg p (k + 1) t) = (p : ℚ) * H (nArg p (k + 1) t) := by
  have hN := nArg_cast p ht
  rw [hHR _ (nArg_mod p ht)]
  have hndvd : ¬ p ^ 2 ∣ nArg p (k + 1) t := by
    intro h
    have h' : (p : ℤ) ∣ (nArg p (k + 1) t : ℤ) :=
      Int.natCast_dvd_natCast.mpr (dvd_trans (dvd_pow_self p two_ne_zero) h)
    rw [hN] at h'
    have h3 : (p : ℤ) ∣ t ^ 2 := by
      have : t ^ 2 = (p : ℤ) * (4 * (p : ℤ) ^ k) - (4 * (p : ℤ) ^ (k + 1) - t ^ 2) := by ring
      rw [this]; exact dvd_sub (dvd_mul_right _ _) h'
    exact hpt ((prime_int p).dvd_of_dvd_pow h3)
  have hkron : kron (-((nArg p (k + 1) t : ℕ) : ℤ)) p = 1 := by
    rw [hN]
    by_cases h2 : p = 2
    · subst h2
      have hodd : t % 2 = 1 := by
        have : ¬ (2 : ℤ) ∣ t := by exact_mod_cast hpt
        omega
      have h8 : t ^ 2 % 8 = 1 := by
        have : t ^ 2 % 8 = (t % 8) * (t % 8) % 8 := by rw [sq, Int.mul_emod]
        have h4 : t % 8 = 1 ∨ t % 8 = 3 ∨ t % 8 = 5 ∨ t % 8 = 7 := by omega
        rcases h4 with h | h | h | h <;> rw [this, h] <;> norm_num
      have e : -(4 * ((2 : ℕ) : ℤ) ^ (k + 1) - t ^ 2) = t ^ 2 - 8 * 2 ^ k := by
        push_cast; ring
      rw [kron, if_pos rfl, e]
      generalize t ^ 2 = Y at h8
      generalize (2 : ℤ) ^ k = X
      have ha : (Y - 8 * X) % 2 ≠ 0 := by omega
      have hb : (Y - 8 * X) % 8 = 1 := by omega
      simp [ha, hb]
    · rw [kron, if_neg h2]
      have e : -(4 * (p : ℤ) ^ (k + 1) - t ^ 2) = t ^ 2 + (p : ℤ) * (-4 * (p : ℤ) ^ k) := by ring
      rw [e, jacobiSym.mod_left, Int.add_mul_emod_self_left, ← jacobiSym.mod_left]
      apply jacobiSym.sq_one'
      have hc : IsCoprime (p : ℤ) t := (Prime.coprime_iff_not_dvd (prime_int p)).mpr hpt
      exact Int.isCoprime_iff_gcd_eq_one.mp hc.symm
  rw [hkron, if_neg hndvd]
  push_cast; ring

/-- HR on the `p ∣ t` part: `H(p²(4p^{k+2} − p²u²)) = (p+1)·H(4p^{k+2} − p²u²) − p·H(4pᵏ − u²)`. -/
lemma hr_dvd (H : ℕ → ℚ) (hHR : HurwitzPrimeSquare H p) (k : ℕ) {u : ℤ} (hu : u ∈ tset p k) :
    H (p ^ 2 * nArg p (k + 2) (p * u)) =
      ((p : ℚ) + 1) * H (nArg p (k + 2) (p * u)) - (p : ℚ) * H (nArg p k u) := by
  have hpu : (p : ℤ) * u ∈ tset p (k + 2) := by
    rw [mem_tset] at hu ⊢
    have : ((p : ℤ) * u) ^ 2 = (p : ℤ) ^ 2 * u ^ 2 := by ring
    rw [this, pow_add]
    have : (0 : ℤ) ≤ (p : ℤ) ^ 2 := by positivity
    nlinarith
  rw [hHR _ (nArg_mod p hpu), nArg_scale p hu]
  have hdvd : p ^ 2 ∣ p ^ 2 * nArg p k u := dvd_mul_right _ _
  have hdiv : p ^ 2 * nArg p k u / p ^ 2 = nArg p k u :=
    Nat.mul_div_cancel_left _ (pow_pos hp.out.pos 2)
  have hkron : kron (-((p ^ 2 * nArg p k u : ℕ) : ℤ)) p = 0 := by
    by_cases h2 : p = 2
    · subst h2
      rw [kron, if_pos rfl]
      rw [if_pos (by push_cast; omega)]
    · rw [kron, if_neg h2, jacobiSym.mod_left]
      have : (-((p ^ 2 * nArg p k u : ℕ) : ℤ)) % (p : ℤ) = 0 := by
        have e : (-((p ^ 2 * nArg p k u : ℕ) : ℤ)) = (p : ℤ) * (-(p * nArg p k u)) := by
          push_cast; ring
        rw [e, Int.mul_emod_right]
      rw [this]
      exact jacobiSym.zero_left hp.out.one_lt
  rw [hkron, if_pos hdvd, hdiv]
  push_cast; ring

/-- The `p ∣ t` part of `esSum H (pᵐ)`. -/
def psum (H : ℕ → ℚ) (m : ℕ) : ℚ :=
  ∑ t ∈ (tset p m).filter (fun t => (p : ℤ) ∣ t), hq p m t * H (nArg p m t)

lemma esSum_split (H : ℕ → ℚ) (m : ℕ) : esSum H (p ^ m) = ordSum H p m + psum p H m := by
  rw [esSum_eq, ordSum_eq, psum, add_comm, sum_filter_add_sum_filter_not]

/-- **The ordinary-sum recursion** (from `HurwitzPrimeSquare` only):
`O(m+4) = A(m+4) − p¹⁰((p+1)A(m+2) − O(m+2) − p¹¹A(m))`. -/
theorem ordSum_rec (H : ℕ → ℚ) (hHR : HurwitzPrimeSquare H p) (m : ℕ) :
    ordSum H p (m + 4) = esSum H (p ^ (m + 4)) -
      (p : ℚ) ^ 10 * (((p : ℚ) + 1) * esSum H (p ^ (m + 2)) - ordSum H p (m + 2) -
        (p : ℚ) ^ 11 * esSum H (p ^ m)) := by
  -- `P(m+2)` reindexed
  have e1 : psum p H (m + 2) = ∑ u ∈ tset p m, hq p (m + 2) (p * u) * H (nArg p (m + 2) (p * u)) :=
    sum_dvd_reindex p m _
  -- `P(m+4)` reindexed and rescaled
  have e2 : psum p H (m + 4) = (p : ℚ) ^ 10 *
      ∑ t ∈ tset p (m + 2), hq p (m + 2) t * H (p ^ 2 * nArg p (m + 2) t) := by
    rw [psum, sum_dvd_reindex p (m + 2), mul_sum]
    refine sum_congr rfl fun t ht => ?_
    rw [hq_scale, nArg_scale p ht]; ring
  -- split the rescaled sum by `p ∣ t`
  have e3 : ∑ t ∈ tset p (m + 2), hq p (m + 2) t * H (p ^ 2 * nArg p (m + 2) t) =
      (((p : ℚ) + 1) * psum p H (m + 2) - (p : ℚ) ^ 11 * esSum H (p ^ m)) +
        (p : ℚ) * ordSum H p (m + 2) := by
    rw [← sum_filter_add_sum_filter_not (tset p (m + 2)) (fun t => (p : ℤ) ∣ t)]
    congr 1
    · rw [sum_dvd_reindex p m, e1, esSum_eq, mul_sum, mul_sum, ← sum_sub_distrib]
      refine sum_congr rfl fun u hu => ?_
      rw [hr_dvd p H hHR m hu, hq_scale]; ring
    · rw [ordSum_eq, mul_sum]
      refine sum_congr rfl fun t ht => ?_
      rw [mem_filter] at ht
      rw [hr_ord p H hHR (m + 1) ht.1 ht.2]; ring
  have hA4 := esSum_split p H (m + 4)
  have hA2 := esSum_split p H (m + 2)
  rw [e3] at e2
  rw [hA4, hA2, e2]
  ring

end Recursion

end RamanujanWeil.ArithPlan
