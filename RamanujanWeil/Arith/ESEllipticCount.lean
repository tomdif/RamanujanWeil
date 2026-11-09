import RamanujanWeil.Arith.ESPerTrace
import RamanujanWeil.Arith.HurwitzOrbit

/-!
# A2 / ES-P6c: the elliptic count `Σ_{tr = t} E = H(4n − t²)` (docs/ARITH_ES_PLAN.md, §2 P6)

The matrix `M = [[a, b], [c, d]]` has the quadratic form `Q_M = [c, d − a, −b] = (A, B, C)` of
discriminant `t² − 4n`. Conjugation `M ↦ −SMS` acts as `(A, B, C) ↦ (C, −B, A)` and
`M ↦ T⁻¹MT` (`conjT`) as `(A, B, C) ↦ (A, B + 2A, A + B + C)`.

`E` is the fundamental-domain sum for `F = {0 ≤ Re z ≤ ½, |z − 1| ≥ 1}`, and `F = F⁺ ∪ F⁻`
with `S F⁻` in the standard domain. Pointwise (`six_regE`):

  `6 E(M) = R⁻(M) + ½(R⁰(M) + R⁰(SMS)) + R⁺(SMS) + ½(Rᵉ(SMS) + Rᵉ(T⁻¹MT))`

where `R(M) = [Q_M reduced] · wt6(Q_M)` split by the sign of `B` (`Rᵉ`: the edge `B = A < C`).
Summing over `det = n, tr = t` and using conjugation invariance, `6 Σ E = Σ R = 6 H(4n − t²)`.
-/

namespace RamanujanWeil.Arith.ES

open M2

/-! ### Reduced matrices -/

/-- `Q_M = [c, d − a, −b]` is reduced (`−A < B ≤ A ≤ C`, `A = C → B ≥ 0`), weighted by `wt6`. -/
def regR (M : M2) : ℚ :=
  if -M.c < M.d - M.a ∧ M.d - M.a ≤ M.c ∧ M.c ≤ -M.b ∧ (M.c = -M.b → 0 ≤ M.d - M.a) then
    (if M.d - M.a = 0 ∧ M.c = -M.b then 3 else if M.d - M.a = M.c ∧ M.c = -M.b then 2 else 6)
  else 0

lemma regR_mk (a b c d : ℤ) : regR ⟨a, b, c, d⟩ =
    if -c < d - a ∧ d - a ≤ c ∧ c ≤ -b ∧ (c = -b → 0 ≤ d - a) then
      (if d - a = 0 ∧ c = -b then 3 else if d - a = c ∧ c = -b then 2 else 6)
    else 0 := rfl

/-- `R` on `B < 0`. -/
def regRn (M : M2) : ℚ := if M.d - M.a < 0 then regR M else 0
/-- `R` on `B = 0`. -/
def regR0 (M : M2) : ℚ := if M.d - M.a = 0 then regR M else 0
/-- `R` on `B > 0` off the edge `B = A < C`. -/
def regRp (M : M2) : ℚ :=
  if 0 < M.d - M.a ∧ ¬(M.d - M.a = M.c ∧ M.c < -M.b) then regR M else 0
/-- `R` on the edge `B = A < C`. -/
def regRe (M : M2) : ℚ := if M.d - M.a = M.c ∧ M.c < -M.b then regR M else 0

lemma regRn_mk (a b c d : ℤ) : regRn ⟨a, b, c, d⟩ = if d - a < 0 then regR ⟨a, b, c, d⟩ else 0 :=
  rfl
lemma regR0_mk (a b c d : ℤ) : regR0 ⟨a, b, c, d⟩ = if d - a = 0 then regR ⟨a, b, c, d⟩ else 0 :=
  rfl
lemma regRp_mk (a b c d : ℤ) : regRp ⟨a, b, c, d⟩ =
    if 0 < d - a ∧ ¬(d - a = c ∧ c < -b) then regR ⟨a, b, c, d⟩ else 0 := rfl
lemma regRe_mk (a b c d : ℤ) : regRe ⟨a, b, c, d⟩ =
    if d - a = c ∧ c < -b then regR ⟨a, b, c, d⟩ else 0 := rfl

lemma regR_split (M : M2) : regR M = regRn M + regR0 M + regRp M + regRe M := by
  obtain ⟨a, b, c, d⟩ := M
  simp only [regRn_mk, regR0_mk, regRp_mk, regRe_mk, regR_mk]
  split_ifs <;> first | (exfalso; omega) | norm_num

/-- `T⁻¹ M T`. -/
def conjT (M : M2) : M2 := ⟨M.a - M.c, M.a + M.b - M.c - M.d, M.c, M.c + M.d⟩
/-- `T M T⁻¹`. -/
def conjTinv (M : M2) : M2 := ⟨M.a + M.c, M.b - M.a + M.d - M.c, M.c, M.d - M.c⟩

lemma det_conjT (M : M2) : (conjT M).det = M.det := by simp only [conjT, det]; ring
lemma tr_conjT (M : M2) : (conjT M).tr = M.tr := by simp only [conjT, tr]; ring

/-- `M ↦ T⁻¹MT` as a bijection. -/
def conjTEquiv : M2 ≃ M2 where
  toFun := conjT
  invFun := conjTinv
  left_inv M := by ext <;> (simp [conjT, conjTinv]; try ring)
  right_inv M := by ext <;> (simp [conjT, conjTinv]; try ring)

lemma trSum_conjT {n t : ℤ} (f : M2 → ℚ) : trSum n t (fun M => f (conjT M)) = trSum n t f :=
  trSum_comp f conjTEquiv det_conjT tr_conjT

/-! Closed forms of the five pieces (each a small case analysis). -/

lemma regRn_cf (a b c d : ℤ) : regRn ⟨a, b, c, d⟩ =
    if -c < d - a ∧ d - a < 0 ∧ c < -b then 6 else 0 := by
  simp only [regRn_mk, regR_mk]
  split_ifs <;> first | (exfalso; omega) | norm_num

lemma regR0_cf (a b c d : ℤ) : regR0 ⟨a, b, c, d⟩ =
    if d - a = 0 ∧ 0 < c ∧ c ≤ -b then (if c = -b then 3 else 6) else 0 := by
  simp only [regR0_mk, regR_mk]
  split_ifs <;> first | (exfalso; omega) | norm_num

lemma regR0_S (a b c d : ℤ) : regR0 (conjS ⟨a, b, c, d⟩) =
    if d - a = 0 ∧ 0 < -b ∧ -b ≤ c then (if c = -b then 3 else 6) else 0 := by
  simp only [conjS, regR0_mk, regR_mk]
  split_ifs <;> first | (exfalso; omega) | norm_num

lemma regRp_S (a b c d : ℤ) : regRp (conjS ⟨a, b, c, d⟩) =
    if 0 < a - d ∧ a - d ≤ -b ∧ -b ≤ c ∧ ¬(a - d = -b ∧ -b < c) then
      (if a - d = -b ∧ -b = c then 2 else 6) else 0 := by
  simp only [conjS, regRp_mk, regR_mk]
  split_ifs <;> first | (exfalso; omega) | norm_num

lemma regRe_S (a b c d : ℤ) : regRe (conjS ⟨a, b, c, d⟩) =
    if a - d = -b ∧ -b < c ∧ 0 < -b then 6 else 0 := by
  simp only [conjS, regRe_mk, regR_mk]
  split_ifs <;> first | (exfalso; omega) | norm_num

lemma regRe_T (a b c d : ℤ) : regRe (conjT ⟨a, b, c, d⟩) =
    if d - a = -c ∧ c < -b ∧ 0 < c then 6 else 0 := by
  simp only [conjT, regRe_mk, regR_mk]
  split_ifs <;> first | (exfalso; omega) | norm_num

/-- **The fundamental-domain identity** `6E = R⁻ + ½(R⁰ + R⁰∘S) + R⁺∘S + ½(Rᵉ∘S + Rᵉ∘T)`. -/
theorem six_regE (M : M2) :
    6 * regE M = regRn M + (regR0 M + regR0 (conjS M)) / 2 + regRp (conjS M) +
      (regRe (conjS M) + regRe (conjT M)) / 2 := by
  obtain ⟨a, b, c, d⟩ := M
  rw [regRn_cf, regR0_cf, regR0_S, regRp_S, regRe_S, regRe_T, regE_mk]
  rcases lt_trichotomy (d - a) 0 with h | h | h
  · simp (disch := omega) only [esIfPos, esIfNeg, eW]
    split_ifs <;> first | (exfalso; omega) | norm_num
  · simp (disch := omega) only [esIfPos, esIfNeg, eW]
    split_ifs <;> first | (exfalso; omega) | norm_num
  · simp (disch := omega) only [esIfPos, esIfNeg, eW]
    split_ifs <;> norm_num

/-! ### Finiteness and the per-trace identity `6 Σ E = Σ R` -/

lemma bnd_red {a b c d n : ℤ} (hdet : a * d - b * c = n) (h1 : -c < d - a) (h2 : d - a ≤ c)
    (h3 : c ≤ -b) : EntBd (2 * n) ⟨a, b, c, d⟩ := by
  simp only [EntBd]
  have hc : 1 ≤ c := by omega
  have k1 : (d - a) ^ 2 ≤ c * c := by nlinarith
  have k2 : c * c ≤ c * (-b) := by nlinarith
  have key : (a + d) ^ 2 + 3 * (c * (-b)) ≤ 4 * n := by nlinarith
  have hn : 1 ≤ n := by nlinarith
  have e1 : c ≤ c * (-b) := by nlinarith
  have e2 : -b ≤ c * (-b) := by nlinarith
  have e3 : a + d ≤ 2 * n := by nlinarith
  have e4 : -(2 * n) ≤ a + d := by nlinarith
  refine ⟨abs_le.mpr ⟨?_, ?_⟩, abs_le.mpr ⟨?_, ?_⟩, abs_le.mpr ⟨?_, ?_⟩,
    abs_le.mpr ⟨?_, ?_⟩⟩ <;> nlinarith

lemma regR_ne {M : M2} (h : regR M ≠ 0) :
    -M.c < M.d - M.a ∧ M.d - M.a ≤ M.c ∧ M.c ≤ -M.b ∧ (M.c = -M.b → 0 ≤ M.d - M.a) := by
  by_contra hc; apply h; unfold regR; rw [esIfNeg hc]

lemma FinDet.of_bdK {n K : ℤ} {f : M2 → ℚ} (h : ∀ M, M.det = n → f M ≠ 0 → EntBd K M) :
    FinDet n f :=
  (finite_entBd K).subset fun M hM => h M hM.1 hM.2

lemma FinDet.mono {n : ℤ} {f g : M2 → ℚ} (hf : FinDet n f) (h : ∀ M, g M ≠ 0 → f M ≠ 0) :
    FinDet n g :=
  hf.subset fun M hM => ⟨hM.1, h M hM.2⟩

lemma fin_R (n : ℤ) : FinDet n regR := FinDet.of_bdK (K := 2 * n) fun M h1 h2 => by
  obtain ⟨a, b, c, d⟩ := M
  have := regR_ne h2
  exact bnd_red h1 this.1 this.2.1 this.2.2.1

lemma ite_ne_zero_imp {p : Prop} [Decidable p] {x : ℚ} (h : (if p then x else 0) ≠ 0) : x ≠ 0 := by
  by_contra hx; apply h; rw [hx]; simp

lemma fin_Rn (n : ℤ) : FinDet n regRn := (fin_R n).mono fun _ h => ite_ne_zero_imp h
lemma fin_R0 (n : ℤ) : FinDet n regR0 := (fin_R n).mono fun _ h => ite_ne_zero_imp h
lemma fin_Rp (n : ℤ) : FinDet n regRp := (fin_R n).mono fun _ h => ite_ne_zero_imp h
lemma fin_Re (n : ℤ) : FinDet n regRe := (fin_R n).mono fun _ h => ite_ne_zero_imp h

lemma trSum_mul {n t : ℤ} (r : ℚ) (f : M2 → ℚ) :
    trSum n t (fun M => r * f M) = r * trSum n t f := by
  unfold trSum
  rw [mul_finsum]
  congr 1; funext M
  simp only [slice]; split_ifs <;> simp

/-- `6 Σ_{tr = t} E = Σ_{tr = t} R`. -/
theorem six_trSum_regE (n t : ℤ) : 6 * trSum n t regE = trSum n t regR := by
  have fS : ∀ f : M2 → ℚ, FinDet n f → FinDet n (fun M => f (conjS M)) :=
    fun f hf => hf.comp conjSEquiv det_conjS
  have fT : ∀ f : M2 → ℚ, FinDet n f → FinDet n (fun M => f (conjT M)) :=
    fun f hf => hf.comp conjTEquiv det_conjT
  have h1 : 6 * trSum n t regE = trSum n t regRn + (trSum n t regR0 + trSum n t regR0) / 2 +
      trSum n t regRp + (trSum n t regRe + trSum n t regRe) / 2 := by
    rw [← trSum_mul, trSum_congr six_regE]
    have A1 := (fin_R0 n).add (fS _ (fin_R0 n))
    have B1 : FinDet n (fun M => (regR0 M + regR0 (conjS M)) / 2) :=
      A1.mono fun M h => by intro h'; apply h; simp [h']
    have B2 : FinDet n (fun M => (regRe (conjS M) + regRe (conjT M)) / 2) :=
      ((fS _ (fin_Re n)).add (fT _ (fin_Re n))).mono fun M h => by intro h'; apply h; simp [h']
    rw [trSum_add (((fin_Rn n).add B1).add (fS _ (fin_Rp n))) B2,
      trSum_add ((fin_Rn n).add B1) (fS _ (fin_Rp n)), trSum_add (fin_Rn n) B1]
    have d1 : ∀ f : M2 → ℚ, trSum n t (fun M => f M / 2) = trSum n t f / 2 := fun f => by
      rw [show (fun M => f M / 2) = fun M => (1 / 2 : ℚ) * f M from funext fun M => by ring,
        trSum_mul]; ring
    rw [d1 (fun M => regR0 M + regR0 (conjS M)), d1 (fun M => regRe (conjS M) + regRe (conjT M)),
      trSum_add (fin_R0 n) (fS _ (fin_R0 n)), trSum_add (fS _ (fin_Re n)) (fT _ (fin_Re n)),
      trSum_conjS regR0, trSum_conjS regRp, trSum_conjS regRe, trSum_conjT regRe]
  rw [h1, trSum_congr regR_split, trSum_add (((fin_Rn n).add (fin_R0 n)).add (fin_Rp n)) (fin_Re n),
    trSum_add ((fin_Rn n).add (fin_R0 n)) (fin_Rp n), trSum_add (fin_Rn n) (fin_R0 n)]
  ring

/-! ### `Σ_{tr = t} R = 6 H(4n − t²)` via `redPairs` -/

open Hurwitz in
/-- The quadratic form `[c, d − a, −b]` of a matrix. -/
def qfOf (M : M2) : QF := ⟨M.c, M.d - M.a, -M.b⟩

open Hurwitz in
lemma wt6_mk (a b c : ℤ) : wt6 ⟨a, b, c⟩ =
    if b = 0 ∧ a = c then 3 else if b = a ∧ a = c then 2 else 6 := rfl

open Hurwitz in
lemma regR_eq_qf (M : M2) :
    regR M = if (qfOf M).IsReduced then (wt6 (qfOf M) : ℚ) else 0 := by
  obtain ⟨a, b, c, d⟩ := M
  have e : (qfOf ⟨a, b, c, d⟩).IsReduced ↔
      (-c < d - a ∧ d - a ≤ c ∧ c ≤ -b ∧ (c = -b → 0 ≤ d - a)) := Iff.rfl
  by_cases h : (qfOf ⟨a, b, c, d⟩).IsReduced
  · rw [esIfPos h, regR_mk, esIfPos (e.mp h), show qfOf ⟨a, b, c, d⟩ = ⟨c, d - a, -b⟩ from rfl,
      wt6_mk]
    split_ifs <;> norm_num
  · rw [esIfNeg h, regR_mk, esIfNeg (fun h' => h (e.mpr h'))]

/-- The matrix with trace `t` and form `(A, B, (B² + N)/(4A))`. -/
def mkM (t : ℤ) (N : ℕ) (ab : ℤ × ℤ) : M2 :=
  ⟨(t - ab.2) / 2, -((ab.2 ^ 2 + N) / (4 * ab.1)), ab.1, (t + ab.2) / 2⟩

lemma parity_of_dvd {n t A B : ℤ} {N : ℕ} (hN : (N : ℤ) = 4 * n - t ^ 2)
    (hdiv : (B ^ 2 + N) % (4 * A) = 0) : (t - B) % 2 = 0 := by
  have h4 : (2 : ℤ) ∣ B ^ 2 + N :=
    (Dvd.intro (2 * A) (by ring)).trans (Int.dvd_of_emod_eq_zero hdiv)
  have h2 : Even (B ^ 2 - t ^ 2) := by
    rw [hN] at h4
    have : B ^ 2 - t ^ 2 = (B ^ 2 + (4 * n - t ^ 2)) - 2 * (2 * n) := by ring
    rw [this]
    exact (even_iff_two_dvd.mpr h4).sub (even_two_mul _)
  rw [Int.even_sub, Int.even_pow' two_ne_zero, Int.even_pow' two_ne_zero] at h2
  have : Even (t - B) := Int.even_sub.mpr h2.symm
  exact Int.even_iff.mp this

open Hurwitz in
/-- For `(A, B) ∈ redPairs N`, `mkM` has determinant `n`, trace `t`, and form `formOf N (A, B)`. -/
lemma mkM_props {n t : ℤ} {N : ℕ} (hN : (N : ℤ) = 4 * n - t ^ 2) {ab : ℤ × ℤ}
    (hab : ab ∈ redPairs N) :
    (mkM t N ab).det = n ∧ (mkM t N ab).tr = t ∧ qfOf (mkM t N ab) = formOf N ab := by
  obtain ⟨A, B⟩ := ab
  have hm := Finset.mem_filter.mp hab
  have hdiv := hm.2.1
  have hpar := parity_of_dvd hN hdiv
  have hC := Int.mul_ediv_cancel' (Int.dvd_of_emod_eq_zero hdiv)
  set C := (B ^ 2 + (N : ℤ)) / (4 * A) with hCdef
  dsimp only at hdiv hpar hC
  have ea : 2 * ((t - B) / 2) = t - B := by omega
  have ed : 2 * ((t + B) / 2) = t + B := by omega
  refine ⟨?_, ?_, ?_⟩
  · simp only [mkM, det]
    have : 4 * ((t - B) / 2 * ((t + B) / 2) - -C * A) = 4 * n := by
      have e1 : 4 * ((t - B) / 2 * ((t + B) / 2)) = (t - B) * (t + B) := by
        linear_combination (2 * ((t + B) / 2)) * ea + (t - B) * ed
      linear_combination e1 + hC + hN
    linarith
  · simp only [mkM, tr]; omega
  · simp only [mkM, qfOf, formOf]
    ext
    · rfl
    · show (t + B) / 2 - (t - B) / 2 = B; omega
    · show - -((B ^ 2 + (N : ℤ)) / (4 * A)) = _; rw [neg_neg]

open Hurwitz in
/-- **The reduced-form count**: `Σ_{det = n, tr = t} R = 6 H(N)` for `N = 4n − t² > 0`. -/
theorem trSum_regR {n t : ℤ} {N : ℕ} (hN : (N : ℤ) = 4 * n - t ^ 2) :
    trSum n t regR = (H6 N : ℚ) := by
  unfold trSum
  have hsupp : Function.support (slice n t regR) ⊆ ↑((redPairs N).image (mkM t N)) := by
    intro M hM
    rw [Function.mem_support] at hM
    simp only [slice] at hM
    split_ifs at hM with hdt
    · obtain ⟨hdet, htr⟩ := hdt
      have hr := regR_ne hM
      obtain ⟨a, b, c, d⟩ := M
      simp only [det, tr] at hdet htr hr
      have hNv : (N : ℤ) = 4 * c * (-b) - (d - a) ^ 2 := by rw [hN, ← hdet, ← htr]; ring
      have hc1 : 1 ≤ c := by omega
      have e4 : (d - a) ^ 2 + (N : ℤ) = 4 * c * (-b) := by rw [hNv]; ring
      have hq : ((d - a) ^ 2 + (N : ℤ)) / (4 * c) = -b := by
        rw [e4]; exact Int.mul_ediv_cancel_left _ (by omega)
      rw [Finset.coe_image]
      refine ⟨(c, d - a), ?_, ?_⟩
      · have hcc : c * c ≤ N := by nlinarith
        have hs := le_sqrt_of_mul_le (by omega) hcc
        have hdiv : ((d - a) ^ 2 + (N : ℤ)) % (4 * c) = 0 := by
          rw [e4]; exact Int.mul_emod_right _ _
        simp only [Finset.mem_coe, redPairs, Finset.mem_filter, Finset.mem_product,
          Finset.mem_Icc]
        refine ⟨⟨⟨hc1, hs⟩, by omega, by omega⟩, hdiv, ?_⟩
        simp only [formOf, hq]
        exact hr
      · simp only [mkM, hq, neg_neg]
        ext <;> simp <;> omega
    · exact absurd rfl hM
  rw [finsum_eq_sum_of_support_subset _ hsupp, Finset.sum_image]
  · simp only [H6]
    push_cast
    refine Finset.sum_congr rfl fun ab hab => ?_
    obtain ⟨h1, h2, h3⟩ := mkM_props hN hab
    rw [slice, esIfPos ⟨h1, h2⟩, regR_eq_qf, h3, esIfPos (Finset.mem_filter.mp hab).2.2]
  · intro x hx y hy hxy
    have hx3 := (mkM_props hN hx).2.2
    have hy3 := (mkM_props hN hy).2.2
    rw [hxy, hy3] at hx3
    have e1 := congrArg QF.a hx3
    have e2 := congrArg QF.b hx3
    simp only [formOf] at e1 e2
    exact Prod.ext e1.symm e2.symm

/-- Off the elliptic range there are no reduced matrices. -/
theorem trSum_regR_nonell {n t : ℤ} (h : 4 * n ≤ t ^ 2) : trSum n t regR = 0 := by
  unfold trSum
  rw [finsum_eq_zero_of_forall_eq_zero]
  intro M
  simp only [slice]
  split_ifs with hdt
  · by_contra hM
    have hr := regR_ne hM
    obtain ⟨a, b, c, d⟩ := M
    obtain ⟨hdet, htr⟩ := hdt
    simp only [det, tr] at hdet htr hr
    subst hdet htr
    nlinarith
  · rfl

/-- **The elliptic count (property (C), elliptic part)**: for `N = 4n − t² > 0`,
`Σ_{det M = n, tr M = t} E(M) = H(N)` (Hurwitz class number, via reduced forms). -/
theorem trSum_regE {n t : ℤ} {N : ℕ} (hN : (N : ℤ) = 4 * n - t ^ 2) (hpos : 0 < N) :
    trSum n t regE = Hurwitz.hurwitz N := by
  have h := six_trSum_regE n t
  rw [trSum_regR hN] at h
  rw [Hurwitz.hurwitz, esIfNeg hpos.ne']
  linarith

theorem trSum_regE_nonell {n t : ℤ} (h : 4 * n ≤ t ^ 2) : trSum n t regE = 0 := by
  have h6 := six_trSum_regE n t
  rw [trSum_regR_nonell h] at h6
  linarith

end RamanujanWeil.Arith.ES
