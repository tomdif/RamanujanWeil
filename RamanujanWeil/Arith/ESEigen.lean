import RamanujanWeil.Arith.ESPropA

/-!
# A2 / ES-P8c, P9: property (A) on modules, the Eisenstein eigenvalue, trace in coordinates

* `propA_action` (**property (A)**, action form). Let `E` be a vector space over a field `K` of
  characteristic `0` with linear maps `sl M : E → E` such that `sl 1 = sl (−1) = id` and
  `sl (MN) = sl N ∘ sl M` for `det M, det N > 0` (a right action of `M₂(ℤ)⁺/±1`), and let `F ∈ E`
  with `F|T = F`. Then for `n ≥ 1`

    `(F|(1 − S))|T̃ₙ = (F|T^∞ₙ)|(1 − S)`,   `T^∞ₙ = Σ_{ad = n, 0 ≤ b < d} [[a, b], [0, d]]`.

  This is PZ Proposition 2's use of (A); it applies to `V₁₀` and to the weight `−10` slash action
  on functions on `ℍ` (P10).
* `actR_Ttilde_e0` (**P9, Eisenstein line**): `e0|T̃ₙ = σ₁₁(n)·e0`, `e0 = X¹⁰ − Y¹⁰`, with
  `σ₁₁(n) = sig11 n = Σ_{0<a∣n} (n/a)¹¹`.
* `traceSum_eq_coords` : `traceSum n = (e0|T̃ₙ)₁₀ + (p⁺|T̃ₙ)₈ + (p⁻|T̃ₙ)₉`
  (the trace on `W₁₀` in the basis `e0, p⁺, p⁻`).
-/

open Finset Module

namespace RamanujanWeil.Arith.ES

open M2

/-! ### `T̃ₙ` and `T^∞ₙ` as finite sums -/

/-- Coefficient of `T̃ₙ` (restricted to determinant `n`). -/
def ptCd (n : ℤ) (N : M2) : ℚ := if N.det = n then ptC N else 0

/-- The Hecke set `{[[a, b], [0, d]] : ad = n, d > 0, 0 ≤ b < d}` (the support of `T^∞ₙ`). -/
def heckeSet (n : ℕ) : Finset M2 :=
  ((Icc (1 : ℤ) n).filter (· ∣ (n : ℤ))).biUnion fun a =>
    (Ico (0 : ℤ) ((n : ℤ) / a)).image fun b => (⟨a, b, 0, (n : ℤ) / a⟩ : M2)

lemma mem_heckeSet {n : ℕ} (hn : 1 ≤ n) {N : M2} :
    N ∈ heckeSet n ↔ N.c = 0 ∧ N.det = n ∧ 0 < N.d ∧ 0 ≤ N.b ∧ N.b < N.d := by
  unfold heckeSet
  simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_Icc, Finset.mem_image,
    Finset.mem_Ico]
  constructor
  · rintro ⟨a, ⟨⟨ha1, han⟩, hdvd⟩, b, ⟨hb0, hbd⟩, rfl⟩
    obtain ⟨q, hq⟩ := hdvd
    have hq' : (n : ℤ) / a = q := by rw [hq, Int.mul_ediv_cancel_left _ (by omega)]
    rw [hq'] at hbd ⊢
    refine ⟨rfl, by simp only [det]; rw [hq]; ring, lt_of_le_of_lt hb0 hbd, hb0, hbd⟩
  · rintro ⟨hc, hdet, hd, hb0, hbd⟩
    obtain ⟨a, b, c, d⟩ := N
    simp only [det] at hc hdet hd hb0 hbd
    subst hc
    have had : a * d = n := by simpa using hdet
    have ha : 0 < a := pos_of_mul_pos_left (by rw [had]; omega) hd.le
    have hda : (n : ℤ) / a = d := by rw [← had, Int.mul_ediv_cancel_left _ (by omega)]
    refine ⟨a, ⟨⟨ha, by nlinarith⟩, ⟨d, had.symm⟩⟩, b, ⟨hb0, by rw [hda]; exact hbd⟩, ?_⟩
    rw [hda]

lemma heckeSet_sub_box {n : ℕ} (hn : 1 ≤ n) : heckeSet n ⊆ boxM n := by
  intro N hN
  rw [mem_heckeSet hn] at hN
  have h := fin_tinf (n := n) (by omega)
  have : tinf n N ≠ 0 := by unfold tinf; rw [esIfPos hN]; norm_num
  rw [mem_boxM]
  obtain ⟨a, b, c, d⟩ := N
  obtain ⟨hc, hdet, hd, hb0, hbd⟩ := hN
  simp only [det] at hc hdet hd hb0 hbd
  subst hc
  have had : a * d = n := by simpa using hdet
  have ha : 0 < a := pos_of_mul_pos_left (by rw [had]; omega) hd.le
  simp only [EntBd]
  refine ⟨abs_le.mpr ⟨by omega, by nlinarith⟩, abs_le.mpr ⟨by omega, by nlinarith⟩,
    abs_le.mpr ⟨by omega, by omega⟩, abs_le.mpr ⟨by omega, by nlinarith⟩⟩

lemma sum_heckeSet {β : Type*} [AddCommMonoid β] {n : ℕ} (hn : 1 ≤ n) (g : M2 → β) :
    ∑ N ∈ boxM n, (if tinf n N = 1 then g N else 0) = ∑ N ∈ heckeSet n, g N := by
  rw [← Finset.sum_filter]
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext N
  rw [Finset.mem_filter, mem_heckeSet hn]
  constructor
  · rintro ⟨-, h⟩
    unfold tinf at h; split_ifs at h with h1
    · exact h1
    · norm_num at h
  · intro h
    refine ⟨heckeSet_sub_box hn ((mem_heckeSet hn).mpr h), ?_⟩
    unfold tinf; rw [esIfPos h]

lemma tinf_eq (n : ℤ) (N : M2) : tinf n N = if tinf n N = 1 then 1 else 0 := by
  unfold tinf; split_ifs <;> simp_all

/-- Sum over `T^∞ₙ` of a function of `d`: `Σ_{0 < a ∣ n} (n/a)·g(n/a)`. -/
lemma sum_heckeSet_d {β : Type*} [AddCommMonoid β] [Module ℚ β] (n : ℕ) (g : ℤ → β) :
    ∑ N ∈ heckeSet n, g N.d =
      ∑ a ∈ (Icc (1 : ℤ) n).filter (· ∣ (n : ℤ)), (((n : ℤ) / a : ℤ) : ℚ) • g ((n : ℤ) / a) := by
  unfold heckeSet
  rw [Finset.sum_biUnion]
  · refine Finset.sum_congr rfl fun a ha => ?_
    rw [Finset.sum_image]
    · simp only [Finset.sum_const, Int.card_Ico, sub_zero]
      rw [← Nat.cast_smul_eq_nsmul ℚ]
      congr 1
      have : 0 ≤ (n : ℤ) / a := Int.ediv_nonneg (by omega)
        (by simp only [Finset.mem_filter, Finset.mem_Icc] at ha; omega)
      rw [show ((((n : ℤ) / a).toNat : ℕ) : ℚ) = ((((n : ℤ) / a).toNat : ℤ) : ℚ) by norm_cast,
        Int.toNat_of_nonneg this]
    · intro x _ y _ h; simpa using h
  · intro a _ a' _ hne
    simp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro N h1 h2
    simp only [Finset.mem_image] at h1 h2
    obtain ⟨_, _, rfl⟩ := h1
    obtain ⟨_, _, h⟩ := h2
    exact hne (congrArg M2.a h).symm

/-! ### Box reindexings -/

lemma S_mul_mem_box {n : ℤ} {N : M2} : S * N ∈ boxM n ↔ N ∈ boxM n := by
  obtain ⟨a, b, c, d⟩ := N
  simp only [mem_boxM, EntBd, S, mk_mul_mk]
  simp only [zero_mul, neg_mul, one_mul, zero_add, add_zero, abs_neg]
  tauto

lemma mul_S_mem_box {n : ℤ} {N : M2} : N * S ∈ boxM n ↔ N ∈ boxM n := by
  obtain ⟨a, b, c, d⟩ := N
  simp only [mem_boxM, EntBd, S, mk_mul_mk]
  simp only [mul_zero, mul_neg, mul_one, zero_add, add_zero, abs_neg]
  tauto

lemma S_mul_Si' (N : M2) : S * (Si * N) = N := by rw [← mul_assoc, S_Si, one_mul]
lemma Si_mul_S' (N : M2) : Si * (S * N) = N := by rw [← mul_assoc, Si_S, one_mul]

lemma sum_box_S {β : Type*} [AddCommMonoid β] (n : ℤ) (g : M2 → β) :
    ∑ N ∈ boxM n, g (S * N) = ∑ N ∈ boxM n, g N :=
  Finset.sum_nbij' (fun N => S * N) (fun N => Si * N)
    (fun N h => S_mul_mem_box.mpr h)
    (fun N h => S_mul_mem_box.mp (by rw [S_mul_Si']; exact h))
    (fun N _ => Si_mul_S' N) (fun N _ => S_mul_Si' N) (fun _ _ => rfl)

lemma sum_box_S_right {β : Type*} [AddCommMonoid β] (n : ℤ) (g : M2 → β) :
    ∑ N ∈ boxM n, g (N * S) = ∑ N ∈ boxM n, g N :=
  Finset.sum_nbij' (fun N => N * S) (fun N => N * Si)
    (fun N h => mul_S_mem_box.mpr h)
    (fun N h => mul_S_mem_box.mp (by rw [mul_assoc, Si_S, mul_one]; exact h))
    (fun N _ => by rw [mul_assoc, S_Si, mul_one]) (fun N _ => by rw [mul_assoc, Si_S, mul_one])
    (fun _ _ => rfl)

/-! ### Property (A) on modules -/

section Action

variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]

/-- The hypotheses on a weight-`k` (here `−10`) slash action: a right action of `M₂(ℤ)⁺/±1`. -/
structure IsSlash (sl : M2 → E →ₗ[K] E) : Prop where
  one : sl 1 = LinearMap.id
  negOne : sl (-1) = LinearMap.id
  mul : ∀ M N : M2, 0 < M.det → 0 < N.det → sl (M * N) = sl N ∘ₗ sl M

variable {sl : M2 → E →ₗ[K] E}

lemma IsSlash.mul_apply (h : IsSlash sl) {M N : M2} (hM : 0 < M.det) (hN : 0 < N.det) (v : E) :
    sl (M * N) v = sl N (sl M v) := by rw [h.mul M N hM hN]; rfl

lemma IsSlash.neg_apply (h : IsSlash sl) {N : M2} (hN : 0 < N.det) (v : E) :
    sl (-N) v = sl N v := by
  have : -N = -1 * N := by ext <;> simp
  rw [this, h.mul_apply (by decide) hN, h.negOne]; rfl

lemma Pk_det_pos (k : ℤ) : 0 < (Pk k).det := by rw [det_Pk]; norm_num

lemma IsSlash.Pk_fix (h : IsSlash sl) {F : E} (hF : sl T F = F) (k : ℤ) : sl (Pk k) F = F := by
  have h1 : sl (Pk (-1)) F = F := by
    have : T * Pk (-1) = 1 := by decide
    have e := h.mul_apply (M := T) (N := Pk (-1)) (by decide) (by decide) F
    rw [this, hF, h.one] at e; exact e.symm
  induction k using Int.induction_on with
  | zero => rw [show Pk 0 = 1 by decide, h.one]; rfl
  | succ i ih =>
    rw [show Pk ((i : ℤ) + 1) = Pk i * T by ext <;> simp [Pk, T]; ring,
      h.mul_apply (Pk_det_pos _) (by decide), ih, hF]
  | pred i ih =>
    rw [show Pk (-(i : ℤ) - 1) = Pk (-(i : ℤ)) * Pk (-1) by ext <;> simp [Pk]; ring,
      h.mul_apply (Pk_det_pos _) (Pk_det_pos _), ih, h1]

lemma IsSlash.tpow_fix (h : IsSlash sl) {F : E} (hF : sl T F = F) (k : ℤ) {N : M2}
    (hN : 0 < N.det) : sl (tpow k N) F = sl N F := by
  rw [tpow_eq_Pk_mul, h.mul_apply (Pk_det_pos _) hN, h.Pk_fix hF]

/-- **Property (A), action form**: `(F|(1 − S))|T̃ₙ = (F|T^∞ₙ)|(1 − S)` whenever `F|T = F`. -/
theorem propA_action [CharZero K] (h : IsSlash sl) {F : E} (hF : sl T F = F) {n : ℕ} (hn : 1 ≤ n) :
    ∑ N ∈ boxM n, (ptCd n N : K) • sl N (F - sl S F) =
      ∑ N ∈ heckeSet n, (sl N F - sl S (sl N F)) := by
  have hn' : (0 : ℤ) < n := by omega
  -- left side as `Σ_box xi(N) • F|N`
  have hL : ∑ N ∈ boxM n, (ptCd n N : K) • sl N (F - sl S F) =
      ∑ N ∈ boxM n, ((ptCd n N - ptCd n (Si * N) : ℚ) : K) • sl N F := by
    have e1 : ∀ N ∈ boxM n, (ptCd n N : K) • sl N (sl S F) = (ptCd n N : K) • sl (S * N) F := by
      intro N _
      unfold ptCd
      split_ifs with hd
      · rw [h.mul_apply (by decide) (by rw [hd]; exact hn')]
      · simp
    calc ∑ N ∈ boxM n, (ptCd n N : K) • sl N (F - sl S F)
        = ∑ N ∈ boxM n, (ptCd n N : K) • sl N F - ∑ N ∈ boxM n, (ptCd n N : K) • sl (S * N) F := by
          simp only [map_sub, smul_sub, Finset.sum_sub_distrib]; rw [Finset.sum_congr rfl e1]
      _ = ∑ N ∈ boxM n, (ptCd n N : K) • sl N F -
            ∑ N ∈ boxM n, (ptCd n (Si * N) : K) • sl N F := by
          rw [← sum_box_S n (fun N => (ptCd n (Si * N) : K) • sl N F)]; simp only [Si_mul_S']
      _ = _ := by
          rw [← Finset.sum_sub_distrib]; simp only [Rat.cast_sub, sub_smul]
  have hR : ∑ N ∈ heckeSet n, (sl N F - sl S (sl N F)) =
      ∑ N ∈ boxM n, ((tinf n N - tinf n (N * Si) : ℚ) : K) • sl N F := by
    rw [← sum_heckeSet hn]
    have e1 : ∀ N ∈ boxM n, (if tinf n N = 1 then sl N F - sl S (sl N F) else 0) =
        (tinf n N : K) • sl N F - (tinf n N : K) • sl (N * S) F := by
      intro N _
      split_ifs with h1
      · rw [h1, Rat.cast_one, one_smul, one_smul, h.mul_apply _ (by decide)]
        exact (tinf_bd (by rw [h1]; norm_num)).2.1 ▸ hn'
      · have : tinf n N = 0 := by rw [tinf_eq]; simp [h1]
        simp [this]
    calc ∑ N ∈ boxM n, (if tinf n N = 1 then sl N F - sl S (sl N F) else 0)
        = ∑ N ∈ boxM n, (tinf n N : K) • sl N F - ∑ N ∈ boxM n, (tinf n N : K) • sl (N * S) F := by
          rw [Finset.sum_congr rfl e1, Finset.sum_sub_distrib]
      _ = ∑ N ∈ boxM n, (tinf n N : K) • sl N F -
            ∑ N ∈ boxM n, (tinf n (N * Si) : K) • sl N F := by
          rw [← sum_box_S_right n (fun N => (tinf n (N * Si) : K) • sl N F)]
          simp only [mul_assoc, S_Si, mul_one]
      _ = _ := by
          rw [← Finset.sum_sub_distrib]; simp only [Rat.cast_sub, sub_smul]
  rw [hL, hR, ← sub_eq_zero, ← Finset.sum_sub_distrib]
  simp only [← sub_smul, ← Rat.cast_sub]
  set f : M2 → ℚ := fun N => ptCd n N - ptCd n (Si * N) - (tinf n N - tinf n (N * Si)) with hf
  have hdetSi : ∀ N : M2, (Si * N).det = N.det := fun N => by rw [det_mul, det_Si, one_mul]
  have hdetSi' : ∀ N : M2, (N * Si).det = N.det := fun N => by rw [det_mul, det_Si, mul_one]
  have hsupp : ∀ N, f N ≠ 0 → N.det = n := by
    intro N hN
    by_contra hd
    apply hN
    have z3 : tinf n N = 0 := by
      by_contra hne; exact hd (tinf_bd hne).2.1
    have z4 : tinf n (N * Si) = 0 := by
      by_contra hne; exact hd (by rw [← hdetSi' N]; exact (tinf_bd hne).2.1)
    simp only [hf, ptCd, esIfNeg hd, esIfNeg (show ¬(Si * N).det = n by rw [hdetSi]; exact hd),
      z3, z4]
    ring
  rw [← Finset.sum_filter_of_ne (p := fun N => N.det = (n : ℤ)) (fun N _ hN => hsupp N (by
    intro h0; apply hN; simp only [hf] at h0 ⊢; rw [h0, Rat.cast_zero, zero_smul]))]
  refine sum_smul_eq_zero_of_oS (n := n) (by omega) (fun N => sl N F)
    (fun k N hN => h.tpow_fix hF k (by rw [hN]; exact hn'))
    (fun N hN => h.neg_apply (by rw [hN]; exact hn') F) _ ?_ ?_ ?_
  · intro N hN
    refine Finset.mem_filter.mpr ⟨?_, hsupp N hN⟩
    by_contra hb
    apply hN
    have z1 : ptCd n N = 0 := by
      unfold ptCd; split_ifs with hd
      · by_contra hne; exact hb (mem_boxM.mpr (ptC_support hd hne))
      all_goals rfl
    have z2 : ptCd n (Si * N) = 0 := by
      unfold ptCd; split_ifs with hd
      · by_contra hne
        exact hb (by
          rw [← S_mul_Si' N]; exact S_mul_mem_box.mpr (mem_boxM.mpr (ptC_support hd hne)))
      all_goals rfl
    have z3 : tinf n N = 0 := by
      by_contra hne
      exact hb (heckeSet_sub_box hn ((mem_heckeSet hn).mpr (tinf_bd hne)))
    have z4 : tinf n (N * Si) = 0 := by
      by_contra hne
      have := heckeSet_sub_box hn ((mem_heckeSet hn).mpr (tinf_bd hne))
      have e : N * Si * S = N := by rw [mul_assoc, Si_S, mul_one]
      exact hb (e ▸ mul_S_mem_box.mpr this)
    simp only [z1, z2, z3, z4]; ring
  · intro N hN; exact (Finset.mem_filter.mp hN).2
  · intro M hM
    have hM0 : M.det ≠ 0 := by rw [hM]; omega
    have e : oS f M = oS (fun N => xiC N - rhsC n N) M := by
      unfold oS; congr 1; funext k
      have d1 : (tpow k M).det = n := by rw [det_tpow, hM]
      have d2 : (-tpow k M).det = n := by rw [det_neg', det_tpow, hM]
      simp only [hf, ptCd, xiC, rhsC, esIfPos d1, esIfPos d2,
        esIfPos (show (Si * tpow k M).det = n by rw [hdetSi, d1]),
        esIfPos (show (Si * -tpow k M).det = n by rw [hdetSi, d2])]
    rw [e, oS_sub hM0 (by rw [hM]; exact fin_xi n) (by rw [hM]; exact fin_rhs hn'),
      propA_orbit hn' hM, sub_self]

end Action

/-! ### P9: the Eisenstein eigenvalue on `V₁₀` -/

/-- `Y¹⁰` (coefficient vector of `X⁰Y¹⁰`). -/
def Y10 : V := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

lemma rAct_upper_Y10 (a b d : ℤ) : rAct ⟨a, b, 0, d⟩ Y10 = ((d : ℚ) ^ 10) • Y10 := by
  apply eq_of_ev; intro x
  rw [ev_rAct]
  simp [ev, Fin.sum_univ_succ, Y10]

lemma rAct_T_Y10 : rAct T Y10 = Y10 := by
  rw [show T = ⟨1, 1, 0, 1⟩ from rfl, rAct_upper_Y10]; simp

lemma Y10_sub_S : Y10 - rAct S Y10 = -e0 := by
  apply eq_of_ev; intro x
  have h1 : ev (Y10 - rAct S Y10) x = ev Y10 x - ev (rAct S Y10) x := by
    simp [ev, Finset.sum_sub_distrib, sub_mul]
  have h2 : ev (-e0) x = -ev e0 x := by simp [ev]
  rw [h1, h2, ev_rAct]
  simp [ev, Fin.sum_univ_succ, Y10, e0, S]
  ring

lemma isSlash_rAct : IsSlash (K := ℚ) rAct where
  one := rAct_one
  negOne := by rw [rAct_neg, rAct_one]
  mul M N _ _ := rAct_mul M N

lemma actR_Ttilde_apply (n : ℕ) (P : V) :
    actR (Ttilde n) P = ∑ N ∈ boxM n, ptCd n N • rAct N P := by
  rw [Ttilde_eq_elt, elt, actR_sum, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun N _ => ?_
  rw [actR_smul, actR_of]; rfl

/-- `σ₁₁(n) = Σ_{0 < a ∣ n} (n/a)¹¹`. -/
def sig11 (n : ℕ) : ℚ := ∑ a ∈ (Icc (1 : ℤ) n).filter (· ∣ (n : ℤ)), (((n : ℤ) / a : ℤ) : ℚ) ^ 11

/-- **P9 (Eisenstein line)**: `e0|T̃ₙ = σ₁₁(n)·e0` for `e0 = X¹⁰ − Y¹⁰` (PZ, proof of Prop. 2). -/
theorem actR_Ttilde_e0 {n : ℕ} (hn : 1 ≤ n) : actR (Ttilde n) e0 = sig11 n • e0 := by
  have hA := propA_action (K := ℚ) isSlash_rAct rAct_T_Y10 hn
  simp only [Rat.cast_id, Y10_sub_S] at hA
  have hR : ∑ N ∈ heckeSet n, (rAct N Y10 - rAct S (rAct N Y10)) = sig11 n • (-e0) := by
    have e : ∀ N ∈ heckeSet n, rAct N Y10 - rAct S (rAct N Y10) = ((N.d : ℚ) ^ 10) • (-e0) := by
      intro N hN
      have hc := ((mem_heckeSet hn).mp hN).1
      obtain ⟨a, b, c, d⟩ := N
      simp only at hc; subst hc
      rw [rAct_upper_Y10, map_smul, ← smul_sub, Y10_sub_S]
    rw [Finset.sum_congr rfl e, sum_heckeSet_d n (fun d => ((d : ℚ) ^ 10) • (-e0)), sig11,
      Finset.sum_smul]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [smul_smul]; congr 1; ring
  rw [hR] at hA
  rw [actR_Ttilde_apply]
  have : ∑ N ∈ boxM n, ptCd n N • rAct N e0 = -∑ N ∈ boxM n, ptCd n N • rAct N (-e0) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun N _ => ?_
    rw [map_neg, smul_neg, neg_neg]
  rw [this, hA, smul_neg, neg_neg]

/-! ### The trace on `W₁₀` in coordinates -/

/-- The basis vectors of `W₁₀` as elements of the subtype. -/
def wVec : Fin 3 → Wper := ![⟨e0, e0_mem⟩, ⟨pplus, pplus_mem⟩, ⟨pminus, pminus_mem⟩]

lemma wVec_li : LinearIndependent ℚ wVec := by
  apply LinearIndependent.of_comp Wper.subtype
  convert linearIndependent_basis using 1
  funext i; fin_cases i <;> rfl

lemma wVec_span : ⊤ ≤ Submodule.span ℚ (Set.range wVec) := by
  rintro ⟨w, hw⟩ -
  have e : (⟨w, hw⟩ : Wper) = w 10 • wVec 0 + w 8 • wVec 1 + w 9 • wVec 2 := by
    apply Subtype.ext
    simp only [Submodule.coe_add, Submodule.coe_smul]
    exact eq_of_mem_Wper hw
  rw [e]
  refine Submodule.add_mem _ (Submodule.add_mem _ ?_ ?_) ?_ <;>
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)

/-- The basis `e0, p⁺, p⁻` of `W₁₀`. -/
noncomputable def wBasis : Basis (Fin 3) ℚ Wper := Basis.mk wVec_li wVec_span

lemma wBasis_repr (w : Wper) : wBasis.repr w = ![(w : V) 10, (w : V) 8, (w : V) 9] := by
  have e : w = ∑ i, (![(w : V) 10, (w : V) 8, (w : V) 9] : Fin 3 → ℚ) i • wBasis i := by
    apply Subtype.ext
    simp only [Fin.sum_univ_three, wBasis, Basis.mk_apply, Submodule.coe_add,
      Submodule.coe_smul, wVec]
    simpa using eq_of_mem_Wper w.2
  conv_lhs => rw [e]
  ext i
  rw [Basis.repr_sum_self]

/-- The trace of an operator preserving `W₁₀`, in the coordinates `(P₁₀, P₈, P₉)`. -/
theorem trace_Wper_coord (f : V →ₗ[ℚ] V) (hf : ∀ P ∈ Wper, f P ∈ Wper) :
    LinearMap.trace ℚ Wper (f.restrict hf) = f e0 10 + f pplus 8 + f pminus 9 := by
  rw [LinearMap.trace_eq_matrix_trace ℚ wBasis, Matrix.trace, Fin.sum_univ_three]
  simp only [Matrix.diag, LinearMap.toMatrix_apply, wBasis_repr]
  simp [wBasis, Basis.mk_apply, wVec, LinearMap.restrict_apply]

/-- **`tr(T̃ₙ | W₁₀)` in coordinates**: `traceSum n = (e0|T̃ₙ)₁₀ + (p⁺|T̃ₙ)₈ + (p⁻|T̃ₙ)₉`. -/
theorem traceSum_eq_coords (n : ℕ) :
    traceSum n = actR (Ttilde n) e0 10 + actR (Ttilde n) pplus 8 + actR (Ttilde n) pminus 9 := by
  rw [← trace_Wper_Ttilde n]
  exact trace_Wper_coord _ _

end RamanujanWeil.Arith.ES
