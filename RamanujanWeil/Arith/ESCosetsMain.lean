import RamanujanWeil.Arith.ESCosets

/-!
# A2 / ES-P7: `⟨T̃ₙ, K⟩ = −1` for every right coset `K = AΓ` (PZ Theorem 4(b))

* `ptC_scale`, `cS_scale` : homogeneity `ptC (g·N) = ptC N` (`g > 0`), hence
  `⟨T̃, g·BΓ⟩ = ⟨T̃, BΓ⟩`;
* `cS_ptC_K0` : `⟨T̃, diag(1, m)Γ⟩ = −1` (PZ: `T₁ − T₂` and `T₃` contribute `0`, `T₄` gives
  `½ + ½`; `m = 1` by `decide`);
* `cS_ptC_eq_neg_one` : for every `A` with `det A > 0`, `⟨T̃, AΓ⟩ = −1`, by a Euclid descent on
  `|a|` using left invariance under `S`, `[[1,k],[0,1]]`, `[[1,0],[k,1]]` (`ESCosets`) and right
  invariance.
-/

namespace RamanujanWeil.Arith.ES

open M2

/-- `g · M`. -/
def scale (g : ℤ) (M : M2) : M2 := ⟨g * M.a, g * M.b, g * M.c, g * M.d⟩

lemma scale_mul (g : ℤ) (B γ : M2) : scale g B * γ = scale g (B * γ) := by
  ext <;> simp [scale] <;> ring

section scale
variable {g : ℤ} (hg : 0 < g)
include hg

lemma sc_le (x y : ℤ) : g * x ≤ g * y ↔ x ≤ y :=
  ⟨fun h => le_of_mul_le_mul_left h hg, fun h => mul_le_mul_of_nonneg_left h hg.le⟩
lemma sc_lt (x y : ℤ) : g * x < g * y ↔ x < y :=
  ⟨fun h => lt_of_mul_lt_mul_left h hg.le, fun h => mul_lt_mul_of_pos_left h hg⟩
lemma sc_eq (x y : ℤ) : g * x = g * y ↔ x = y :=
  ⟨fun h => mul_left_cancel₀ hg.ne' h, fun h => by rw [h]⟩
lemma sc_nonneg (x : ℤ) : 0 ≤ g * x ↔ 0 ≤ x := by
  simpa using sc_le hg 0 x
lemma sc_pos (x : ℤ) : 0 < g * x ↔ 0 < x := by
  simpa using sc_lt hg 0 x
lemma sc_nonpos (x : ℤ) : g * x ≤ 0 ↔ x ≤ 0 := by
  simpa using sc_le hg x 0
lemma sc_zero_eq (x : ℤ) : 0 = g * x ↔ 0 = x := by
  simpa using sc_eq hg 0 x

/-- **Homogeneity**: the coefficient of `T̃` is invariant under positive scaling. -/
theorem ptC_scale (M : M2) : ptC (scale g M) = ptC M := by
  obtain ⟨a, b, c, d⟩ := M
  simp only [scale, ptC_eq, regT1_mk, regT2_mk, regT3_mk, regT4_mk, ← mul_sub, ← mul_neg, w3, w4,
    sc_le hg, sc_lt hg, sc_eq hg, sc_nonneg hg, sc_pos hg, sc_nonpos hg, sc_zero_eq hg]

theorem cS_scale (B : M2) : cS ptC (scale g B) = cS ptC B := by
  unfold cS
  congr 1; funext γ
  rw [scale_mul, ptC_scale hg]

end scale

/-! ### The coset `diag(1, m)Γ` -/

lemma K0_mul (m : ℤ) (γ : M2) : (⟨1, 0, 0, m⟩ : M2) * γ = ⟨γ.a, γ.b, m * γ.c, m * γ.d⟩ := by
  ext <;> simp

lemma regT3_K0 {m : ℤ} (hm : 2 ≤ m) {γ : M2} (hγ : γ.det = 1) :
    regT3 ((⟨1, 0, 0, m⟩ : M2) * γ) = 0 := by
  rw [K0_mul]
  obtain ⟨a, b, c, d⟩ := γ
  simp only [det] at hγ
  rw [regT3_mk]
  by_cases h0 : a ≤ 0 ∧ 0 < m * c
  · rw [esIfPos h0]
    by_contra hw
    obtain ⟨h1, h2, h3⟩ := w4_ne_zero hw
    have hc : 1 ≤ c := by
      by_contra hc'
      have : m * c ≤ 0 := by nlinarith
      omega
    have e1 : m * c ≤ -b := h3
    have e2 : m ≤ m * c := by nlinarith
    have e3 : 0 ≤ (-a) * (a - m * d) := by nlinarith
    have key : m = m * c * (-b) + (-a) * (a - m * d) + a ^ 2 := by linear_combination -m * hγ
    nlinarith
  · rw [esIfNeg h0]

/-- The only matrices of `diag(1, m)Γ` in the support of `T₄` (for `m ≥ 2`). -/
lemma regT4_K0_support {m : ℤ} (hm : 2 ≤ m) {γ : M2} (hγ : γ.det = 1)
    (h : regT4 ((⟨1, 0, 0, m⟩ : M2) * γ) ≠ 0) :
    γ = ⟨0, -1, 1, 0⟩ ∨ γ = ⟨1, -1, 1, 0⟩ := by
  rw [K0_mul] at h
  obtain ⟨a, b, c, d⟩ := γ
  simp only [det] at hγ
  rw [regT4_mk] at h
  by_cases h0 : m * d ≤ 0 ∧ 0 < -b
  · rw [esIfPos h0] at h
    obtain ⟨h1, h2, h3⟩ := w4_ne_zero h
    have hd : d = 0 := by
      by_contra hd
      have hd' : d ≤ -1 := by
        rcases lt_or_gt_of_ne hd with h | h
        · omega
        · have : 0 < m * d := by positivity
          omega
      have hD : m ≤ -(m * d) := by nlinarith
      have key : m = m * c * (-b) + (m * d) * (a - m * d) + (m * d) ^ 2 := by
        linear_combination -m * hγ
      nlinarith [sq_nonneg (-(m * d) - 2 * (-b))]
    subst hd
    have hbc : (-b) * c = 1 := by linarith
    have hb1 : -b = 1 := Int.eq_one_of_mul_eq_one_right (by omega) hbc
    have hc1 : c = 1 := by rw [hb1, one_mul] at hbc; exact hbc
    have hb : b = -1 := by omega
    subst hb hc1
    rcases (show a = 0 ∨ a = 1 by simp at h1 h2; omega) with ha | ha
    · left; subst ha; rfl
    · right; subst ha; rfl
  · rw [esIfNeg h0] at h; exact absurd rfl h

lemma cS_regT4_K0 {m : ℤ} (hm : 2 ≤ m) : cS regT4 ⟨1, 0, 0, m⟩ = 1 := by
  unfold cS
  have hs : (Function.support fun γ : M2 => if γ.det = 1 then regT4 (⟨1, 0, 0, m⟩ * γ) else 0) ⊆
      ↑({⟨0, -1, 1, 0⟩, ⟨1, -1, 1, 0⟩} : Finset M2) := by
    intro γ hγ
    simp only [Function.mem_support] at hγ
    split_ifs at hγ with h
    · rcases regT4_K0_support hm h hγ with h' | h' <;> simp [h']
    · exact absurd rfl hγ
  rw [finsum_eq_sum_of_support_subset _ hs, Finset.sum_pair (by decide)]
  rw [esIfPos (by decide), esIfPos (by decide), K0_mul, K0_mul]
  simp only [regT4_mk, w4]
  simp (disch := omega) only [esIfPos, esIfNeg]
  norm_num

lemma cS_ptC_K0_one : cS ptC ⟨1, 0, 0, 1⟩ = -1 := by
  unfold cS
  have hs : (Function.support fun γ : M2 => if γ.det = 1 then ptC (⟨1, 0, 0, 1⟩ * γ) else 0) ⊆
      ↑(boxM 1) := by
    intro γ hγ
    simp only [Function.mem_support] at hγ
    split_ifs at hγ with h
    · rw [show (⟨1, 0, 0, 1⟩ : M2) = 1 from rfl, one_mul] at hγ
      exact Finset.mem_coe.mpr (mem_boxM.mpr (ptC_support h hγ))
    · exact absurd rfl hγ
  rw [finsum_eq_sum_of_support_subset _ hs, sum_boxM]
  decide +kernel

/-- **PZ's computation at `K₀ = diag(1, m)Γ`**: `⟨T̃, K₀⟩ = −1`. -/
theorem cS_ptC_K0 {m : ℤ} (hm : 1 ≤ m) : cS ptC ⟨1, 0, 0, m⟩ = -1 := by
  rcases eq_or_lt_of_le hm with h | h
  · subst h; exact cS_ptC_K0_one
  have hm2 : 2 ≤ m := h
  set K : M2 := ⟨1, 0, 0, m⟩
  have hK : K.det ≠ 0 := by simp [K, det]; omega
  have e0 : cS ptC K = cS regT1 K - cS regT2 K - cS regT3 K - cS regT4 K := by
    rw [cS_congr ptC_eq, cS_sub hK (((fin_T1 _).sub (fin_T2 _)).sub (fin_T3 _)) (fin_T4 _),
      cS_sub hK ((fin_T1 _).sub (fin_T2 _)) (fin_T3 _), cS_sub hK (fin_T1 _) (fin_T2 _)]
  have e2 : cS regT2 K = cS regT1 K := by
    rw [← cS_congr regT1_mapE]
    have : ∀ N, regT1 (mapE N) = regT1 (N * Ui) := fun N => by rw [mapE_eq]
    rw [cS_congr this, cS_right regT1 Ui_U U_Ui det_Ui]
  have e3 : cS regT3 K = 0 := by
    unfold cS
    refine finsum_eq_zero_of_forall_eq_zero fun γ => ?_
    split_ifs with hγ
    · exact regT3_K0 hm2 hγ
    · rfl
  rw [e0, e2, e3, cS_regT4_K0 hm2]; ring

/-! ### Euclid descent -/

lemma det_mul_ne_right {g A : M2} (hA : A.det ≠ 0) (hg : g.det = 1) : (A * g).det ≠ 0 := by
  rw [det_mul, hg, mul_one]; exact hA

lemma Pk_mul_Pk (k : ℤ) : Pk k * Pk (-k) = 1 := by ext <;> simp [Pk]
lemma Pk_neg_mul_Pk (k : ℤ) : Pk (-k) * Pk k = 1 := by ext <;> simp [Pk]

/-- Right multiplication by `[[1,k],[0,1]]` then `S`. -/
lemma cS_ptC_PS (k : ℤ) (A : M2) : cS ptC (A * Pk k * S) = cS ptC A := by
  rw [cS_mul_right ptC S_Si Si_S det_S, cS_mul_right ptC (Pk_mul_Pk k) (Pk_neg_mul_Pk k) (det_Pk k)]

lemma natAbs_emod_lt {x a : ℤ} (ha : a ≠ 0) : (x % a).natAbs < a.natAbs := by
  have h1 := Int.emod_nonneg x ha
  have h2 := Int.emod_lt x ha
  have := Int.natAbs_lt_natAbs_of_nonneg_of_lt h1 h2
  simpa [Int.natAbs_abs] using this

/-- Every `diag(a, d')` with `a ∣ d'` and `a d' > 0` has coset sum `−1`. -/
lemma cS_ptC_diag {a d' : ℤ} (ha : a ≠ 0) (hdiv : d' % a = 0) (hpos : 0 < a * d') :
    cS ptC ⟨a, 0, 0, d'⟩ = -1 := by
  have hd : d' = a * (d' / a) := (Int.mul_ediv_cancel' (Int.dvd_of_emod_eq_zero hdiv)).symm
  have hm : 1 ≤ d' / a := by
    by_contra h'
    have hq : d' / a ≤ 0 := by omega
    have haa : 0 < a * a := mul_self_pos.mpr ha
    have h1 : 0 < a * a * (d' / a) := by rw [mul_assoc, ← hd]; exact hpos
    have h2 := mul_nonpos_of_nonneg_of_nonpos haa.le hq
    linarith
  rcases lt_or_gt_of_ne ha with hneg | hpos'
  · have e : (⟨a, 0, 0, d'⟩ : M2) = -scale (-a) ⟨1, 0, 0, d' / a⟩ := by
      ext <;> (simp [scale]; try linarith)
    rw [e, cS_neg, cS_scale (by omega), cS_ptC_K0 hm]
  · have e : (⟨a, 0, 0, d'⟩ : M2) = scale a ⟨1, 0, 0, d' / a⟩ := by
      ext <;> (simp [scale]; try linarith)
    rw [e, cS_scale hpos', cS_ptC_K0 hm]

theorem cS_ptC_descent : ∀ (k : ℕ) (A : M2), A.a.natAbs = k → A.a ≠ 0 → 0 < A.det →
    cS ptC A = -1 := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro A hk ha hdet
  obtain ⟨a, b, c, d⟩ := A
  simp only at hk ha
  have hA : (⟨a, b, c, d⟩ : M2).det ≠ 0 := hdet.ne'
  by_cases hb : b % a = 0
  · by_cases hc : c % a = 0
    · -- clear `b` and `c`
      set q1 := b / a
      set q2 := c / a
      have eb : b = a * q1 := (Int.mul_ediv_cancel' (Int.dvd_of_emod_eq_zero hb)).symm
      have ec : c = a * q2 := (Int.mul_ediv_cancel' (Int.dvd_of_emod_eq_zero hc)).symm
      set d' := d - q1 * c
      have e2 : Lk (-q2) * (⟨a, b, c, d⟩ * Pk (-q1)) = ⟨a, 0, 0, d'⟩ := by
        ext <;> simp only [Lk, Pk, mul_a, mul_b, mul_c, mul_d, d']
        · ring
        · linear_combination eb
        · linear_combination ec
        · linear_combination (-q2) * eb
      have hA2 : cS ptC ⟨a, b, c, d⟩ = cS ptC ⟨a, 0, 0, d'⟩ := by
        rw [← e2, cS_ptC_Lk _ (det_mul_ne_right hA (det_Pk _)), cS_mul_right ptC (Pk_neg_mul_Pk q1)
          (Pk_mul_Pk q1) (by rw [det_Pk])]
      have hdet2 : 0 < a * d' := by
        have := congrArg M2.det e2
        rw [det_mul, det_Lk, one_mul, det_mul, det_Pk, mul_one] at this
        simp only [det] at this hdet
        nlinarith
      rw [hA2]
      by_cases hd' : d' % a = 0
      · exact cS_ptC_diag ha hd' hdet2
      · -- `T · diag(a, d') = [[a, d'], [0, d']]`, then reduce `d'` mod `a`
        have e3 : (Pk 1 * ⟨a, 0, 0, d'⟩ * Pk (-(d' / a)) * S).a = d' % a := by
          simp [Pk, S, Int.emod_def]; ring
        have hA3 : (Pk 1 * ⟨a, 0, 0, d'⟩ : M2).det ≠ 0 := by
          rw [det_mul, det_Pk, one_mul]; simp only [det]; nlinarith
        rw [← cS_ptC_Pk 1 (by simp only [det]; nlinarith), ← cS_ptC_PS (-(d' / a))]
        refine ih _ ?_ _ rfl (by rw [e3]; exact hd') ?_
        · rw [e3, ← hk]; exact natAbs_emod_lt ha
        · rw [det_mul, det_S, mul_one, det_mul, det_Pk, mul_one, det_mul, det_Pk, one_mul]
          simp only [det]; linarith
    · -- reduce `c` mod `a` on the left
      have e1 : (S * (Lk (-(c / a)) * ⟨a, b, c, d⟩)).a = -(c % a) := by
        simp [S, Lk, Int.emod_def]; ring
      rw [← cS_ptC_Lk (-(c / a)) hA, ← cS_ptC_S (det_mul_ne (det_Lk _) hA)]
      refine ih _ ?_ _ rfl (by rw [e1]; omega) ?_
      · rw [e1, Int.natAbs_neg, ← hk]; exact natAbs_emod_lt ha
      · rw [det_mul, det_S, one_mul, det_mul, det_Lk, one_mul]; exact hdet
  · -- reduce `b` mod `a` on the right
    have e1 : (⟨a, b, c, d⟩ * Pk (-(b / a)) * S).a = b % a := by
      simp [Pk, S, Int.emod_def]; ring
    rw [← cS_ptC_PS (-(b / a))]
    refine ih _ ?_ _ rfl (by rw [e1]; exact hb) ?_
    · rw [e1, ← hk]; exact natAbs_emod_lt ha
    · rw [det_mul, det_S, mul_one, det_mul, det_Pk, mul_one]; exact hdet

/-- **PZ Theorem 4(b)**: for every integer matrix `A` with `det A > 0`,
`⟨T̃, AΓ⟩ = Σ_{det γ = 1} ptC(Aγ) = −1`. -/
theorem cS_ptC_eq_neg_one {A : M2} (hdet : 0 < A.det) : cS ptC A = -1 := by
  by_cases ha : A.a = 0
  · have e : (A * S).a = A.b := by simp [S]
    have hb : A.b ≠ 0 := by
      intro hb; obtain ⟨a, b, c, d⟩ := A; simp only at ha hb; simp [det, ha, hb] at hdet
    rw [← cS_mul_right ptC S_Si Si_S det_S A]
    exact cS_ptC_descent _ _ rfl (by rw [e]; exact hb)
      (by rw [det_mul, det_S, mul_one]; exact hdet)
  · exact cS_ptC_descent _ _ rfl ha hdet

end RamanujanWeil.Arith.ES
