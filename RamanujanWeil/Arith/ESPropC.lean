import RamanujanWeil.Arith.ESEllipticCount

/-!
# A2 / ES-P6: property (C) — `tr(T̃ₙ | V₁₀)` as a class-number sum (docs/ARITH_ES_PLAN.md, §2 P6)

Assembling P4b (`ptC_support`), Lemma 4 per trace (`trSum_ptC`) and the elliptic count
(`trSum_regE`):

* `traceSum_eq_trSum` : `traceSum n = Σ_{|t| ≤ 2n} Sym¹⁰(t, n) · Σ_{det = n, tr = t} T̃ₙ`;
* `traceSum_classNumber` (**property (C)**): for `n ≥ 1`,

    `traceSum n = Σ_{a ∣ n, 0 < a} hypW a (n/a) · Sym¹⁰(a + n/a, n)
                  − Σ_{|t| ≤ 2n, t² < 4n} Sym¹⁰(t, n) · H(4n − t²)`

  with `hypW a d = d − a` for `a < d`, `1/6` for `a = d`, `0` for `a > d` — i.e. PZ's
  hyperbolic/parabolic conventions `H(−u²) = −u/2`, `H(0) = −1/12` after symmetrising `t ↦ −t`.
-/

open Finset

namespace RamanujanWeil.Arith.ES

open M2

/-! ### The box of matrices with entries in `[−n, n]` -/

/-- Matrices with all entries in `[−K, K]`. -/
def boxM (K : ℤ) : Finset M2 :=
  ((Icc (-K) K ×ˢ Icc (-K) K) ×ˢ (Icc (-K) K ×ˢ Icc (-K) K)).image
    fun x => (⟨x.1.1, x.1.2, x.2.1, x.2.2⟩ : M2)

lemma mem_boxM {K : ℤ} {M : M2} : M ∈ boxM K ↔ EntBd K M := by
  constructor
  · intro h
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp h
    simp only [Finset.mem_product, Finset.mem_Icc] at hx
    exact ⟨abs_le.mpr hx.1.1, abs_le.mpr hx.1.2, abs_le.mpr hx.2.1, abs_le.mpr hx.2.2⟩
  · intro h
    obtain ⟨a, b, c, d⟩ := M
    refine Finset.mem_image.mpr ⟨((a, b), (c, d)), ?_, rfl⟩
    simp only [Finset.mem_product, Finset.mem_Icc]
    exact ⟨⟨abs_le.mp h.1, abs_le.mp h.2.1⟩, abs_le.mp h.2.2.1, abs_le.mp h.2.2.2⟩

/-- A per-trace sum of a function supported (in determinant `n`) in the box, as a box sum. -/
lemma trSum_eq_box {n t : ℤ} {f : M2 → ℚ} (hf : ∀ M, M.det = n → f M ≠ 0 → EntBd n M) :
    trSum n t f = ∑ M ∈ boxM n, slice n t f M := by
  unfold trSum
  refine finsum_eq_sum_of_support_subset _ fun M hM => ?_
  rw [Function.mem_support] at hM
  simp only [slice] at hM
  split_ifs at hM with h
  · exact Finset.mem_coe.mpr (mem_boxM.mpr (hf M h.1 hM))
  · exact absurd rfl hM

/-- Regrouping a box sum by traces. -/
lemma sum_trSum_eq_box {n : ℤ} (f : M2 → ℚ) (hf : ∀ M, M.det = n → f M ≠ 0 → EntBd n M)
    (g : ℤ → ℚ) :
    ∑ t ∈ Icc (-(2 * n)) (2 * n), g t * trSum n t f =
      ∑ M ∈ boxM n, if M.det = n then f M * g M.tr else 0 := by
  simp only [trSum_eq_box hf, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun M hM => ?_
  have hb := mem_boxM.mp hM
  have htr : M.tr ∈ Icc (-(2 * n)) (2 * n) := by
    obtain ⟨h1, h2, h3, h4⟩ := hb
    rw [abs_le] at h1 h4
    simp only [Finset.mem_Icc, tr]; constructor <;> linarith
  simp only [slice]
  split_ifs with hd
  · have : ∀ t, g t * (if M.det = n ∧ M.tr = t then f M else 0) =
        if M.tr = t then f M * g M.tr else 0 := fun t => by
      by_cases ht : M.tr = t
      · subst ht; simp [hd, mul_comm]
      · simp [ht]
    simp only [this]
    rw [Finset.sum_ite_eq _ _ _, esIfPos htr]
  · simp [hd]

/-- `traceSum` as a sum over the box `boxM n`. -/
lemma traceSum_eq_box (n : ℕ) :
    traceSum n = ∑ M ∈ boxM n, if M.det = n then ptC M * (symTr10 M.tr n : ℚ) else 0 := by
  unfold traceSum boxM
  rw [Finset.sum_image]
  · simp only [Finset.sum_product]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
      Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
    by_cases h : a * d - b * c = n
    · have hd : (⟨a, b, c, d⟩ : M2).det = n := h
      rw [ptCn, esIfPos h, esIfPos hd, h]; rfl
    · have hd : ¬(⟨a, b, c, d⟩ : M2).det = n := h
      rw [ptCn, esIfNeg h, esIfNeg hd, zero_mul]
  · intro x _ y _ hxy
    simp only [M2.mk.injEq] at hxy
    obtain ⟨⟨_, _⟩, _, _⟩ := x
    obtain ⟨⟨_, _⟩, _, _⟩ := y
    simp_all

/-- **Trace regrouped by traces**: `traceSum n = Σ_{|t| ≤ 2n} Sym¹⁰(t, n) · (Σ_{tr = t} T̃ₙ)`. -/
theorem traceSum_eq_trSum (n : ℕ) :
    traceSum n = ∑ t ∈ Icc (-(2 * (n : ℤ))) (2 * n), (symTr10 t n : ℚ) * trSum n t ptC := by
  rw [sum_trSum_eq_box ptC (fun M h1 h2 => ptC_support h1 h2) (fun t => (symTr10 t n : ℚ)),
    traceSum_eq_box]

/-! ### The hyperbolic/parabolic part `H` -/

/-- PZ's hyperbolic/parabolic weight of the split pair `(a, d)`, `ad = n`. -/
def hypW (a d : ℤ) : ℚ := if a < d then ((d - a : ℤ) : ℚ) else if a = d then 1 / 6 else 0

lemma w3_split (m b : ℤ) (hm : 1 ≤ m) :
    w3 (-m) (-b) 0 = (if 0 < b ∧ b < m then 1 else 0) + (if b = 0 then 1 / 2 else 0) +
      (if b = m then 1 / 2 else 0) := by
  unfold w3
  split_ifs <;> first | (exfalso; omega) | norm_num

/-- `Σ_{b} w3(a − d, −b, 0) = hypW a d` over a large enough window. -/
lemma sum_w3_hyp {a d K : ℤ} (ha : 1 ≤ a) (hd : d ≤ K) :
    ∑ b ∈ Icc (-K) K, w3 (a - d) (-b) 0 = hypW a d := by
  unfold hypW
  rcases lt_trichotomy a d with h | h | h
  · rw [esIfPos h]
    have e : a - d = -(d - a) := by ring
    simp only [e, w3_split (d - a) _ (by omega), Finset.sum_add_distrib]
    rw [Finset.sum_ite_eq' _ _ _, Finset.sum_ite_eq' _ _ _, esIfPos (by simp; omega),
      esIfPos (by simp; omega), Finset.sum_boole]
    have hf : (Icc (-K) K).filter (fun b => 0 < b ∧ b < d - a) = Ioo 0 (d - a) := by
      ext b; simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ioo]; omega
    rw [hf, Int.card_Ioo]
    have : ((d - a - 0 - 1).toNat : ℚ) = ((d - a - 1 : ℤ) : ℚ) := by
      rw [show d - a - 0 - 1 = d - a - 1 by ring]
      exact_mod_cast Int.toNat_of_nonneg (by omega)
    rw [this]; push_cast; ring
  · subst h
    rw [esIfNeg (lt_irrefl a), esIfPos rfl]
    have : ∀ b, w3 (a - a) (-b) 0 = if b = 0 then 1 / 6 else 0 := fun b => by
      unfold w3; split_ifs <;> first | (exfalso; omega) | norm_num
    simp only [this]
    rw [Finset.sum_ite_eq' _ _ _, esIfPos (by simp; omega)]
  · rw [esIfNeg (by omega), esIfNeg (by omega)]
    refine Finset.sum_eq_zero fun b _ => ?_
    unfold w3; rw [esIfNeg (by omega)]

lemma sum_boxM {β : Type*} [AddCommMonoid β] (K : ℤ) (F : M2 → β) :
    ∑ M ∈ boxM K, F M = ∑ a ∈ Icc (-K) K, ∑ b ∈ Icc (-K) K, ∑ c ∈ Icc (-K) K,
      ∑ d ∈ Icc (-K) K, F ⟨a, b, c, d⟩ := by
  unfold boxM
  rw [Finset.sum_image]
  · simp only [Finset.sum_product]
  · intro x _ y _ hxy
    simp only [M2.mk.injEq] at hxy
    obtain ⟨⟨_, _⟩, _, _⟩ := x
    obtain ⟨⟨_, _⟩, _, _⟩ := y
    simp_all

/-- **The hyperbolic/parabolic part**: `Σ_t Sym¹⁰(t, n) Σ_{tr = t} H = Σ_{a ∣ n} hypW(a, n/a)
Sym¹⁰(a + n/a, n)`. -/
theorem sum_trSum_regH (n : ℕ) (hn : 1 ≤ n) (g : ℤ → ℚ) :
    ∑ t ∈ Icc (-(2 * (n : ℤ))) (2 * n), g t * trSum n t regH =
      ∑ a ∈ Icc (1 : ℤ) n, if a ∣ (n : ℤ) then hypW a ((n : ℤ) / a) * g (a + (n : ℤ) / a)
        else 0 := by
  rw [sum_trSum_eq_box regH (fun M h1 h2 => regH_bd h1 h2), sum_boxM]
  have hn' : (1 : ℤ) ≤ n := by exact_mod_cast hn
  -- only `c = 0` contributes
  have hc : ∀ a b : ℤ, ∑ c ∈ Icc (-(n : ℤ)) n, ∑ d ∈ Icc (-(n : ℤ)) n,
      (if (⟨a, b, c, d⟩ : M2).det = n then regH ⟨a, b, c, d⟩ * g (⟨a, b, c, d⟩ : M2).tr
        else 0) =
      ∑ d ∈ Icc (-(n : ℤ)) n, if a * d = n ∧ 0 < a then w3 (a - d) (-b) 0 * g (a + d) else 0 := by
    intro a b
    rw [Finset.sum_eq_single (0 : ℤ)]
    · refine Finset.sum_congr rfl fun d _ => ?_
      by_cases h : a * d = n ∧ 0 < a
      · have hd : (⟨a, b, 0, d⟩ : M2).det = n := by simp only [det]; linarith [h.1]
        rw [esIfPos hd, esIfPos h, regH_mk, esIfPos ⟨rfl, h.2⟩]; rfl
      · rw [esIfNeg h]
        by_cases hd : (⟨a, b, 0, d⟩ : M2).det = n
        · rw [esIfPos hd, regH_mk, esIfNeg (by
            intro h'; apply h; refine ⟨?_, h'.2⟩; simp only [det] at hd; linarith), zero_mul]
        · rw [esIfNeg hd]
    · intro c _ hc0
      refine Finset.sum_eq_zero fun d _ => ?_
      by_cases hd : (⟨a, b, c, d⟩ : M2).det = n
      · rw [esIfPos hd, regH_mk, esIfNeg (fun h' => hc0 h'.1), zero_mul]
      · rw [esIfNeg hd]
    · intro h; exfalso; apply h; simp only [Finset.mem_Icc]; omega
  simp only [hc]
  -- only `d = n / a` contributes
  have hd : ∀ a b : ℤ, ∑ d ∈ Icc (-(n : ℤ)) n,
      (if a * d = n ∧ 0 < a then w3 (a - d) (-b) 0 * g (a + d) else 0) =
      if 0 < a ∧ a ∣ (n : ℤ) then w3 (a - n / a) (-b) 0 * g (a + n / a) else 0 := by
    intro a b
    by_cases ha : 0 < a ∧ a ∣ (n : ℤ)
    · rw [esIfPos ha, Finset.sum_eq_single ((n : ℤ) / a)]
      · rw [esIfPos ⟨Int.mul_ediv_cancel' ha.2, ha.1⟩]
      · intro d _ hdn
        rw [esIfNeg]
        rintro ⟨h1, h2⟩
        apply hdn
        rw [← h1, Int.mul_ediv_cancel_left _ h2.ne']
      · intro h
        exfalso; apply h
        have h1 : 0 ≤ (n : ℤ) / a := Int.ediv_nonneg (by omega) ha.1.le
        have h2 : (n : ℤ) / a ≤ n := Int.ediv_le_self _ (by omega)
        simp only [Finset.mem_Icc]; omega
    · rw [esIfNeg ha]
      refine Finset.sum_eq_zero fun d _ => ?_
      rw [esIfNeg]
      rintro ⟨h1, h2⟩
      exact ha ⟨h2, ⟨d, h1.symm⟩⟩
  simp only [hd]
  -- sum over `b`
  have hb : ∀ a : ℤ, ∑ b ∈ Icc (-(n : ℤ)) n,
      (if 0 < a ∧ a ∣ (n : ℤ) then w3 (a - n / a) (-b) 0 * g (a + n / a) else 0) =
      if 0 < a ∧ a ∣ (n : ℤ) then hypW a ((n : ℤ) / a) * g (a + n / a) else 0 := by
    intro a
    by_cases ha : 0 < a ∧ a ∣ (n : ℤ)
    · simp only [esIfPos ha]
      rw [← Finset.sum_mul, sum_w3_hyp (by omega) (Int.ediv_le_self _ (by omega))]
    · simp only [esIfNeg ha, Finset.sum_const_zero]
  simp only [hb]
  rw [← Finset.sum_subset (s₁ := Icc (1 : ℤ) n) (s₂ := Icc (-(n : ℤ)) n)]
  · refine Finset.sum_congr rfl fun a ha => ?_
    have ha1 : 0 < a := by simp only [Finset.mem_Icc] at ha; omega
    by_cases hdv : a ∣ (n : ℤ)
    · rw [esIfPos hdv, esIfPos ⟨ha1, hdv⟩]
    · rw [esIfNeg hdv, esIfNeg (fun h => hdv h.2)]
  · intro a ha; simp only [Finset.mem_Icc] at ha ⊢; omega
  · intro a ha ha'
    have ha0 : ¬ 0 < a := by
      intro h; apply ha'; simp only [Finset.mem_Icc] at ha ⊢; omega
    rw [esIfNeg (fun h => ha0 h.1)]

/-! ### Property (C) -/

/-- **Property (C)** (Popa–Zagier Theorem 1(iii) for `T̃ₙ`, eq. (15)): for `n ≥ 1`,

  `tr(T̃ₙ | V₁₀) = Σ_{0 < a ∣ n} hypW(a, n/a)·Sym¹⁰(a + n/a, n)
                  − Σ_{t² < 4n} Sym¹⁰(t, n)·H(4n − t²)`,

with `H = Hurwitz.hurwitz` (reduced forms). -/
theorem traceSum_classNumber (n : ℕ) (hn : 1 ≤ n) :
    traceSum n =
      (∑ a ∈ Icc (1 : ℤ) n,
        if a ∣ (n : ℤ) then hypW a ((n : ℤ) / a) * (symTr10 (a + (n : ℤ) / a) n : ℚ) else 0) -
      ∑ t ∈ Icc (-(2 * (n : ℤ))) (2 * n),
        if t ^ 2 < 4 * (n : ℤ) then (symTr10 t n : ℚ) * Hurwitz.hurwitz (4 * (n : ℤ) - t ^ 2).toNat
        else 0 := by
  rw [traceSum_eq_trSum]
  simp only [trSum_ptC, mul_sub, Finset.sum_sub_distrib]
  rw [sum_trSum_regH n hn (fun t => (symTr10 t n : ℚ))]
  congr 1
  refine Finset.sum_congr rfl fun t _ => ?_
  by_cases h : t ^ 2 < 4 * (n : ℤ)
  · rw [esIfPos h, trSum_regE (N := (4 * (n : ℤ) - t ^ 2).toNat)
      (Int.toNat_of_nonneg (by omega)) (by omega)]
  · rw [esIfNeg h, trSum_regE_nonell (by omega), mul_zero]

end RamanujanWeil.Arith.ES
