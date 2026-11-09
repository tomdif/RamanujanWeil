import RamanujanWeil.Arith.TauHecke

/-!
# A2 / ES-P10 (arithmetic part): bounds on `τ` and the full Hecke relation

* `tau_abs_mul_pow_le` : `|τ(m)|·rᵐ ≤ r·exp(24r/(1 − r))` for `0 < r < 1` (coefficientwise
  domination of `q∏(1 − qᵏ)²⁴` by `q∏(1 + qᵏ)²⁴`, evaluated at `r`).
* `tau_hecke` : `Σ_{a ∣ (n, k)} a¹¹ τ(nk/a²) = τ(n) τ(k)` for `n ≥ 1` (from Mordell's master
  identity `tau_master` and the operator identity `T_p T_m = T_{pm} + p¹¹[p ∣ m] T_{m/p}` on
  arbitrary sequences, `hecke_comp`).
-/

set_option autoImplicit false

namespace RamanujanWeil.Arith.ES.Analytic

open Polynomial Finset RamanujanTau RamanujanWeil.ArithPlan

/-! ### Coefficientwise domination -/

/-- `p` is dominated by `P` coefficientwise in absolute value. -/
def Dom (p P : ℤ[X]) : Prop := ∀ n, |p.coeff n| ≤ P.coeff n

lemma Dom.nonneg {p P : ℤ[X]} (h : Dom p P) (n : ℕ) : 0 ≤ P.coeff n := (abs_nonneg _).trans (h n)

lemma Dom.mul {p P q Q : ℤ[X]} (h1 : Dom p P) (h2 : Dom q Q) : Dom (p * q) (P * Q) := by
  intro n
  rw [coeff_mul, coeff_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun x _ => ?_)
  rw [abs_mul]
  exact mul_le_mul (h1 _) (h2 _) (abs_nonneg _) (h1.nonneg _)

lemma dom_one : Dom 1 1 := by
  intro n; rw [coeff_one]; split_ifs <;> simp

lemma Dom.pow {p P : ℤ[X]} (h : Dom p P) : ∀ k : ℕ, Dom (p ^ k) (P ^ k)
  | 0 => by simpa using dom_one
  | k + 1 => by rw [pow_succ, pow_succ]; exact (h.pow k).mul h

lemma dom_prod (s : Finset ℕ) (f g : ℕ → ℤ[X]) (h : ∀ i ∈ s, Dom (f i) (g i)) :
    Dom (∏ i ∈ s, f i) (∏ i ∈ s, g i) := by
  induction s using Finset.induction_on with
  | empty => simpa using dom_one
  | insert a s ha ih =>
    rw [prod_insert ha, prod_insert ha]
    exact (h a (mem_insert_self a s)).mul (ih fun i hi => h i (mem_insert_of_mem hi))

lemma dom_X : Dom X X := by
  intro n; rw [coeff_X]; split_ifs <;> simp

lemma dom_one_sub (k : ℕ) : Dom (1 - X ^ (k + 1)) (1 + X ^ (k + 1)) := by
  intro n
  rw [coeff_sub, coeff_add, coeff_one, coeff_X_pow]
  split_ifs with h1 h2 <;> first | omega | simp

/-- the dominating polynomial `q∏_{k<N}(1 + q^{k+1})²⁴`. -/
noncomputable def PD (N : ℕ) : ℤ[X] := X * (∏ k ∈ range N, (1 + X ^ (k + 1))) ^ 24

lemma dom_PN (N : ℕ) : Dom (TauHeckeBridge.PN N) (PD N) :=
  dom_X.mul ((dom_prod _ _ _ fun k _ => dom_one_sub k).pow 24)

lemma coeff_mul_pow_le_eval (P : ℤ[X]) (hP : ∀ n, 0 ≤ P.coeff n) {r : ℝ} (hr : 0 ≤ r) (m : ℕ) :
    (P.coeff m : ℝ) * r ^ m ≤ (P.map (Int.castRingHom ℝ)).eval r := by
  set N := max (P.natDegree + 1) (m + 1)
  have hdeg : (P.map (Int.castRingHom ℝ)).natDegree < N :=
    lt_of_le_of_lt natDegree_map_le (by omega)
  rw [eval_eq_sum_range' hdeg]
  have hm : m ∈ range N := mem_range.mpr (by omega)
  have := Finset.single_le_sum (f := fun i => (P.map (Int.castRingHom ℝ)).coeff i * r ^ i)
    (fun i _ => mul_nonneg (by rw [coeff_map, eq_intCast]; exact_mod_cast hP i) (pow_nonneg hr i)) hm
  simpa [coeff_map] using this

lemma prod_one_add_le {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (N : ℕ) :
    ∏ k ∈ range N, (1 + r ^ (k + 1)) ≤ Real.exp (r / (1 - r)) := by
  calc ∏ k ∈ range N, (1 + r ^ (k + 1)) ≤ ∏ k ∈ range N, Real.exp (r ^ (k + 1)) := by
        refine Finset.prod_le_prod (fun k _ => by positivity) fun k _ => ?_
        have := Real.add_one_le_exp (r ^ (k + 1)); linarith
    _ = Real.exp (∑ k ∈ range N, r ^ (k + 1)) := (Real.exp_sum _ _).symm
    _ ≤ Real.exp (r / (1 - r)) := by
        refine Real.exp_le_exp.mpr ?_
        have h1 : ∑ k ∈ range N, r ^ (k + 1) = r * ∑ k ∈ range N, r ^ k := by
          rw [mul_sum]; exact sum_congr rfl fun k _ => by ring
        have h2 : ∑ k ∈ range N, r ^ k ≤ 1 / (1 - r) := by
          rw [geom_sum_eq hr1.ne, show (r ^ N - 1) / (r - 1) = (1 - r ^ N) / (1 - r) by
            rw [div_eq_div_iff (sub_ne_zero.mpr hr1.ne) (by linarith)]; ring]
          have : 0 ≤ r ^ N := pow_nonneg hr0 N
          exact div_le_div_of_nonneg_right (by linarith) (by linarith)
        rw [h1, div_eq_mul_one_div r]
        exact mul_le_mul_of_nonneg_left h2 hr0

/-- **Explicit bound**: `|τ(m)|·rᵐ ≤ r·exp(24r/(1 − r))` for `0 ≤ r < 1`. -/
theorem tau_abs_mul_pow_le {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (m : ℕ) :
    |(tau m : ℝ)| * r ^ m ≤ r * Real.exp (24 * (r / (1 - r))) := by
  have hc : (tau m : ℤ) = (TauHeckeBridge.PN m).coeff m := (TauHeckeBridge.PN_coeff le_rfl).symm
  have h1 : |(tau m : ℝ)| ≤ ((PD m).coeff m : ℝ) := by
    rw [hc]; exact_mod_cast dom_PN m m
  have h2 := coeff_mul_pow_le_eval (PD m) (dom_PN m).nonneg hr0 m
  have h3 : (( PD m).map (Int.castRingHom ℝ)).eval r = r * (∏ k ∈ range m, (1 + r ^ (k + 1))) ^ 24 := by
    simp [PD, Polynomial.map_prod, eval_prod]
  have h4 : (∏ k ∈ range m, (1 + r ^ (k + 1))) ^ 24 ≤ Real.exp (24 * (r / (1 - r))) := by
    rw [show 24 * (r / (1 - r)) = (24 : ℕ) * (r / (1 - r)) by norm_num, Real.exp_nat_mul]
    exact pow_le_pow_left₀ (prod_nonneg fun k _ => by positivity) (prod_one_add_le hr0 hr1 m) 24
  calc |(tau m : ℝ)| * r ^ m ≤ ((PD m).coeff m : ℝ) * r ^ m :=
        mul_le_mul_of_nonneg_right h1 (pow_nonneg hr0 m)
    _ ≤ _ := h2
    _ = _ := h3
    _ ≤ r * Real.exp (24 * (r / (1 - r))) := mul_le_mul_of_nonneg_left h4 hr0

/-! ### The Hecke relation -/

/-- the Hecke operator `T_n` on sequences (weight 12): `(T_n c)(k) = Σ_{a ∣ (n,k)} a¹¹ c(nk/a²)`. -/
def Tn (n : ℕ) (c : ℕ → ℤ) (k : ℕ) : ℤ :=
  ∑ a ∈ (Nat.gcd n k).divisors, (a : ℤ) ^ 11 * c (n * k / (a * a))

lemma Tn_one (c : ℕ → ℤ) (k : ℕ) : Tn 1 c k = c k := by
  simp [Tn]

lemma Tn_prime {p : ℕ} (hp : p.Prime) (c : ℕ → ℤ) (k : ℕ) :
    Tn p c k = c (p * k) + if p ∣ k then (p : ℤ) ^ 11 * c (k / p) else 0 := by
  unfold Tn
  by_cases hk : p ∣ k
  · rw [Nat.gcd_eq_left hk, hp.divisors, if_pos hk, sum_pair hp.one_lt.ne]
    obtain ⟨j, rfl⟩ := hk
    have hp0 := hp.pos
    simp only [Nat.cast_one, one_pow, one_mul, mul_one, Nat.div_one]
    congr 2
    rw [show p * (p * j) = j * (p * p) by ring, Nat.mul_div_cancel _ (by positivity),
      Nat.mul_div_cancel_left _ hp0]
  · rw [(Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hp).mpr hk)).symm.gcd_eq_one]
    simp [if_neg hk]

/-- membership in the divisors of a gcd. -/
lemma mem_gcd_divisors {a x y : ℕ} (hx : x ≠ 0) : a ∈ (Nat.gcd x y).divisors ↔ a ∣ x ∧ a ∣ y := by
  rw [Nat.mem_divisors, Nat.dvd_gcd_iff]
  exact ⟨fun h => h.1, fun h => ⟨h, Nat.gcd_pos_of_pos_left _ (Nat.pos_of_ne_zero hx) |>.ne'⟩⟩

/-- a gcd-divisor sum as a filtered sum over a fixed universe. -/
lemma sum_gcd_eq {D : Finset ℕ} {x y : ℕ} (hx : x ≠ 0) (g : ℕ → ℤ)
    (hD : ∀ a, a ∣ x → a ∣ y → a ∈ D) :
    ∑ a ∈ (Nat.gcd x y).divisors, g a = ∑ a ∈ D, if a ∣ x ∧ a ∣ y then g a else 0 := by
  rw [← sum_filter]
  refine sum_congr ?_ fun _ _ => rfl
  ext a
  rw [mem_gcd_divisors hx, mem_filter]
  exact ⟨fun h => ⟨hD a h.1 h.2, h⟩, fun h => h.2⟩

/-- the `p`-shifted gcd-divisor sum as a filtered sum. -/
lemma sum_gcd_shift_eq {p : ℕ} (hp : p.Prime) {D : Finset ℕ} {x y : ℕ} (hx : x ≠ 0)
    (g : ℕ → ℤ) (hD : ∀ a, a ∣ p * x → a ∣ p * y → a ∈ D) :
    ∑ b ∈ (Nat.gcd x y).divisors, g (p * b) =
      ∑ a ∈ D, if a ∣ p * x ∧ a ∣ p * y ∧ p ∣ a then g a else 0 := by
  rw [← sum_filter]
  have hp0 := hp.pos
  refine sum_nbij' (fun b => p * b) (fun a => a / p) ?_ ?_ ?_ ?_ ?_
  · intro b hb
    rw [mem_gcd_divisors hx] at hb
    rw [mem_filter]
    refine ⟨hD _ (Nat.mul_dvd_mul_left p hb.1) (Nat.mul_dvd_mul_left p hb.2),
      Nat.mul_dvd_mul_left p hb.1, Nat.mul_dvd_mul_left p hb.2, dvd_mul_right p b⟩
  · intro a ha
    rw [mem_filter] at ha
    obtain ⟨_, h1, h2, ⟨b, rfl⟩⟩ := ha
    rw [mem_gcd_divisors hx, Nat.mul_div_cancel_left _ hp0]
    exact ⟨Nat.dvd_of_mul_dvd_mul_left hp0 h1, Nat.dvd_of_mul_dvd_mul_left hp0 h2⟩
  · intro b _; simp [Nat.mul_div_cancel_left _ hp0]
  · intro a ha
    rw [mem_filter] at ha
    obtain ⟨_, _, _, ⟨b, rfl⟩⟩ := ha
    simp [Nat.mul_div_cancel_left _ hp0]
  · intro b _; rfl

/-- **The operator identity** `T_m(c)(pk) + [p ∣ k]p¹¹T_m(c)(k/p) = T_{pm}(c)(k) + [p ∣ m]p¹¹T_{m/p}(c)(k)`. -/
theorem hecke_comp {p : ℕ} (hp : p.Prime) {m : ℕ} (hm : 1 ≤ m) (c : ℕ → ℤ) (k : ℕ) :
    Tn m c (p * k) + (if p ∣ k then (p : ℤ) ^ 11 * Tn m c (k / p) else 0) =
      Tn (p * m) c k + (if p ∣ m then (p : ℤ) ^ 11 * Tn (m / p) c k else 0) := by
  have hp0 := hp.pos
  set g : ℕ → ℤ := fun a => (a : ℤ) ^ 11 * c (p * m * k / (a * a)) with hg
  set D := (p * m).divisors
  have hm0 : m ≠ 0 := by omega
  have hpm0 : p * m ≠ 0 := by positivity
  have memD : ∀ a, a ∣ p * m → a ∈ D := fun a h => Nat.mem_divisors.mpr ⟨h, hpm0⟩
  -- the four sums as filtered sums of `g` over `D`
  have e1 : Tn m c (p * k) = ∑ a ∈ D, if a ∣ m ∧ a ∣ p * k then g a else 0 := by
    unfold Tn
    rw [sum_gcd_eq hm0 _ fun a h _ => memD a (dvd_mul_of_dvd_right h p)]
    refine sum_congr rfl fun a _ => ?_
    simp only [hg]; congr 3; ring_nf
  have e3 : Tn (p * m) c k = ∑ a ∈ D, if a ∣ p * m ∧ a ∣ k then g a else 0 := by
    unfold Tn
    rw [sum_gcd_eq hpm0 _ fun a h _ => memD a h]
  -- the shifted sums: `p¹¹ b¹¹ c(mk/(p b²)) = g(pb)`
  have gsh : ∀ x y b : ℕ, p * x * (p * y) = p * m * k →
      (p : ℤ) ^ 11 * ((b : ℤ) ^ 11 * c (x * y / (b * b))) = g (p * b) := by
    intro x y b hxy
    simp only [hg]
    push_cast
    by_cases hb : b = 0
    · subst hb; simp
    have : p * m * k / (p * b * (p * b)) = x * y / (b * b) := by
      rw [← hxy, show p * x * (p * y) = (x * y) * (p * p) by ring,
        show p * b * (p * b) = (b * b) * (p * p) by ring, Nat.mul_div_mul_right _ _ (by positivity)]
    rw [this]; ring
  have e2 : (if p ∣ k then (p : ℤ) ^ 11 * Tn m c (k / p) else 0) =
      ∑ a ∈ D, if a ∣ p * m ∧ a ∣ k ∧ p ∣ a then g a else 0 := by
    by_cases hk : p ∣ k
    · rw [if_pos hk]
      obtain ⟨j, rfl⟩ := hk
      rw [Nat.mul_div_cancel_left _ hp0]
      unfold Tn
      rw [mul_sum]
      rw [sum_congr rfl fun b _ => gsh m j b (by ring)]
      rw [sum_gcd_shift_eq hp hm0 g fun a h _ => memD a h]
    · rw [if_neg hk]
      symm
      refine sum_eq_zero fun a _ => if_neg fun h => hk (h.2.2.trans h.2.1)
  have e4 : (if p ∣ m then (p : ℤ) ^ 11 * Tn (m / p) c k else 0) =
      ∑ a ∈ D, if a ∣ m ∧ a ∣ p * k ∧ p ∣ a then g a else 0 := by
    by_cases hpm : p ∣ m
    · rw [if_pos hpm]
      obtain ⟨j, rfl⟩ := hpm
      rw [Nat.mul_div_cancel_left _ hp0]
      have hj0 : j ≠ 0 := by rintro rfl; simp at hm
      unfold Tn
      rw [mul_sum]
      rw [sum_congr rfl fun b _ => gsh j k b (by ring)]
      rw [sum_gcd_shift_eq hp hj0 g fun a h _ => memD a (by
        rw [show p * (p * j) = p * (p * j) from rfl]; exact dvd_mul_of_dvd_right h p)]
    · rw [if_neg hpm]
      symm
      refine sum_eq_zero fun a _ => if_neg fun h => hpm (h.2.2.trans h.1)
  rw [e1, e2, e3, e4, ← sum_add_distrib, ← sum_add_distrib]
  refine sum_congr rfl fun a _ => ?_
  by_cases hpa : p ∣ a
  · -- `p ∣ a`: both sides are `[a ∣ m ∧ a ∣ pk] g + [a ∣ pm ∧ a ∣ k] g`
    simp only [hpa, and_true]
    split_ifs <;> ring
  · -- `p ∤ a`: `a ∣ px ↔ a ∣ x`
    have hcop : Nat.Coprime a p :=
      (Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpa))
    have h1 : a ∣ p * k ↔ a ∣ k := hcop.dvd_mul_left
    have h2 : a ∣ p * m ↔ a ∣ m := hcop.dvd_mul_left
    simp only [hpa, and_false, h1, h2]

/-- **The Hecke relation for `τ`**: `Σ_{a ∣ (n,k)} a¹¹ τ(nk/a²) = τ(n)τ(k)` for `n ≥ 1`. -/
theorem tau_hecke : ∀ n : ℕ, 1 ≤ n → ∀ k : ℕ, Tn n tau k = tau n * tau k := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn k
    rcases Nat.lt_or_ge n 2 with h2 | h2
    · obtain rfl : n = 1 := by omega
      rw [Tn_one, tau_one, one_mul]
    set p := n.minFac
    have hp : p.Prime := Nat.minFac_prime (by omega)
    obtain ⟨m, hnm⟩ : p ∣ n := Nat.minFac_dvd n
    have hp0 := hp.pos
    have hm : 1 ≤ m := by
      rcases Nat.eq_zero_or_pos m with h | h
      · subst h; omega
      · exact h
    have hmn : m < n := by
      rw [hnm]; exact lt_mul_left hm hp.one_lt
    have key := hecke_comp hp hm tau k
    rw [hnm, eq_sub_of_add_eq key.symm]
    have ihm : ∀ k, Tn m tau k = tau m * tau k := ih m hmn hm
    rw [ihm, ihm]
    have hk := tau_master hp k
    have hmm := tau_master hp m
    by_cases hpm : p ∣ m
    · have hmp : 1 ≤ m / p := Nat.div_pos (Nat.le_of_dvd (by omega) hpm) hp0
      have hlt : m / p < n := lt_of_le_of_lt (Nat.div_le_self _ _) hmn
      have ihp := ih (m / p) hlt hmp k
      simp only [if_pos hpm] at hmm ⊢
      rw [ihp]
      split_ifs at hk ⊢ <;> linear_combination (-(tau m)) * hk + (tau k) * hmm
    · simp only [if_neg hpm] at hmm ⊢
      split_ifs at hk ⊢ <;> linear_combination (-(tau m)) * hk + (tau k) * hmm

end RamanujanWeil.Arith.ES.Analytic
