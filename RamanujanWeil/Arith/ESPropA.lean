import RamanujanWeil.Arith.ESOrbit

/-!
# A2 / ES-P8b: property (A) for `T̃ₙ` as vanishing of orbit sums (docs/ARITH_ES_PROGRESS3.md)

Let `ξ = (1 − S)T̃` as a coefficient function, `xiC N = T̃(N) − T̃(S⁻¹N)`, and let
`aO M = oS xiC M` be its left `±T^ℤ`-orbit sums (PZ's `a(K)`, proof of Theorem A). We prove:

* `aO_S`  : `a(M) + a(MS) = 0`            (from (16a), i.e. property (B), first half);
* `aO_U`  : `a(M) + a(MU) + a(MU²) = 0`   (from (16b), property (B), second half);
* `aO_rec`: `a(M) = a(MT) + a(MT′)`, `T′ = [[1,0],[1,1]]`;
* `aO_cd`  (**acyclicity**, PZ Lemma 2 / Thm A): `a(M) = 0` unless `c = 0` or `d = 0`;
* `aO_c0`  (direct evaluation, replacing PZ Theorem B(b)): `a(M) = 1` if `c = 0`;
* `aO_d0`  : `a(M) = −1` if `d = 0`;
* `propA_orbit` (**property (A)**, orbit form): for `det M = n ≥ 1`,
  `oS ((1−S)T̃) M = oS (T^∞(1−S)) M`, with `T^∞ₙ = Σ_{ad=n, 0≤b<d} [[a,b],[0,d]]` (`tinf n`).
-/

open Finset

namespace RamanujanWeil.Arith.ES

open M2

/-! ### Literal matrix arithmetic -/

lemma mk_mul_mk (a b c d e f g h : ℤ) :
    (⟨a, b, c, d⟩ : M2) * ⟨e, f, g, h⟩ = ⟨a * e + b * g, a * f + b * h, c * e + d * g, c * f + d * h⟩ :=
  rfl
lemma neg_mk (a b c d : ℤ) : -(⟨a, b, c, d⟩ : M2) = ⟨-a, -b, -c, -d⟩ := rfl

/-- `T′ = [[1, 0], [1, 1]]`. -/
def Tp : M2 := ⟨1, 0, 1, 1⟩

/-! ### The coefficient function of `(1 − S)T̃` and its orbit sums -/

/-- Coefficient of `(1 − S)T̃` at `N` (`(S·x)(N) = x(S⁻¹N)`). -/
def xiC (N : M2) : ℚ := ptC N - ptC (Si * N)

/-- `a(M) = ⟨(1 − S)T̃, Γ∞M⟩`. -/
noncomputable def aO (M : M2) : ℚ := oS xiC M

lemma fin_xi (n : ℤ) : FinDet n xiC := (fin_ptC n).sub ((fin_ptC n).left det_Si)

lemma aO_neg (M : M2) : aO (-M) = aO M := oS_neg _ _

/-! ### The two period relations (from (16a), (16b)) -/

/-- `G = F + F·S` (as a coefficient function). -/
def gF (N : M2) : ℚ := regF N + regF (N * S)
/-- `H = G + U⁻¹G + U⁻²G`. -/
def hF (N : M2) : ℚ := gF N + gF (Ui * N) + gF (Ui * Ui * N)

/-- Pointwise (symmetrised) form of `(1−S)T̃(1+S) ≡ −(1−S)(1+U+U²)F(1+S)`. -/
lemma rel1_pt (X : M2) :
    (xiC X + xiC (X * S)) + (xiC (-X) + xiC (-X * S)) =
      (-hF X + hF (Si * X)) + (-hF (-X) + hF (Si * -X)) := by
  obtain ⟨a, b, c, d⟩ := X
  simp only [xiC, hF, gF, ptC_16a, mapA, mapB, mapC, Si, Ui, S, mk_mul_mk, neg_mk]
  ring_nf

/-- Pointwise (symmetrised) form of `(1−S)T̃(1+U+U²) ≡ −(1−S)(1+S)G(1+U+U²) ≡ 0`. -/
lemma rel2_pt (X : M2) :
    (xiC X + xiC (X * U) + xiC (X * U * U)) + (xiC (-X) + xiC (-X * U) + xiC (-X * U * U)) =
      0 := by
  obtain ⟨a, b, c, d⟩ := X
  simp only [xiC, ptC_16b, mapD, mapE, Si, U, mk_mul_mk, neg_mk]
  ring_nf


/-- Orbit sums are unchanged when the symmetrised function is transported along `X ↦ TʲX`. -/
lemma oS_congr_tpow {f g : M2 → ℚ} (j : ℤ)
    (h : ∀ X, f X + f (-X) = g (tpow j X) + g (-tpow j X)) (M : M2) : oS f M = oS g M := by
  have : oS f M = oS g (tpow j M) := by
    unfold oS; congr 1; funext k
    rw [h, tpow_tpow, tpow_tpow, add_comm j k]
  rw [this, oS_tpow]

lemma fin_gF (n : ℤ) : FinDet n gF := (fin_F n).add ((fin_F n).right det_S)
lemma det_UiUi : (Ui * Ui).det = 1 := by decide
lemma fin_hF (n : ℤ) : FinDet n hF :=
  (((fin_gF n).add ((fin_gF n).left det_Ui)).add ((fin_gF n).left det_UiUi))

/-- `⟨H, Γ∞M⟩ = ⟨S⁻¹·H, Γ∞M⟩`, i.e. `(1 − S)(1 + U + U²) ∈ (1 − T)R` (mod `±`). -/
lemma oS_hF {M : M2} (hM : M.det ≠ 0) : oS (fun N => hF (Si * N)) M = oS hF M := by
  have f0 := fin_gF M.det
  have e1 : oS (fun N => gF (Ui * Ui * (Si * N))) M = oS gF M := by
    refine oS_congr_tpow 1 (fun X => ?_) M
    have h1 : Ui * Ui * (Si * X) = -tpow 1 X := by
      obtain ⟨a, b, c, d⟩ := X; simp only [Ui, Si, mk_mul_mk, neg_mk, tpow]; ext <;> simp
    have h2 : Ui * Ui * (Si * -X) = tpow 1 X := by rw [mul_neg', mul_neg', h1, neg_neg']
    rw [h1, h2]; ring
  have e2 : oS (fun N => gF (Ui * N)) M = oS (fun N => gF (Si * N)) M := by
    refine oS_congr_tpow (-1) (fun X => ?_) M
    have h1 : Ui * X = Si * tpow (-1) X := by
      obtain ⟨a, b, c, d⟩ := X; simp only [Ui, Si, mk_mul_mk, tpow]; ext <;> simp <;> ring
    rw [h1, mul_neg', h1, mul_neg']
  have e3 : oS (fun N => gF (Ui * (Si * N))) M = oS (fun N => gF (Ui * Ui * N)) M := by
    refine oS_congr_tpow 1 (fun X => ?_) M
    have h1 : Ui * (Si * X) = Ui * Ui * tpow 1 X := by
      obtain ⟨a, b, c, d⟩ := X; simp only [Ui, Si, mk_mul_mk, tpow]; ext <;> simp
    rw [h1, mul_neg', mul_neg', h1, mul_neg']
  have fl : ∀ g : M2, g.det = 1 → FinDet M.det (fun N => gF (g * N)) := fun g hg => f0.left hg
  have det_UiSi : (Ui * Si).det = 1 := by decide
  have det_UiUiSi : (Ui * Ui * Si).det = 1 := by decide
  have hH : ∀ N, hF (Si * N) = gF (Si * N) + gF (Ui * (Si * N)) + gF (Ui * Ui * (Si * N)) :=
    fun N => rfl
  rw [oS_congr_tpow 0 (g := fun N => gF (Si * N) + gF (Ui * (Si * N)) + gF (Ui * Ui * (Si * N)))
    (fun X => by simp only [tpow_zero, hH]) M]
  have fA := fl Si det_Si
  have fB : FinDet M.det (fun N => gF (Ui * (Si * N))) :=
    (fl _ det_UiSi).congr fun N => by rw [mul_assoc]
  have fC : FinDet M.det (fun N => gF (Ui * Ui * (Si * N))) :=
    (fl _ det_UiUiSi).congr fun N => by rw [mul_assoc]
  rw [oS_add hM (fA.add fB) fC, oS_add hM fA fB, e1, e3]
  unfold hF
  rw [oS_add hM (f0.add (fl Ui det_Ui)) (fl _ det_UiUi), oS_add hM f0 (fl Ui det_Ui), e2]
  ring

/-- **First period relation**: `a(M) + a(MS) = 0`. -/
theorem aO_S {M : M2} (hM : M.det ≠ 0) : aO M + aO (M * S) = 0 := by
  unfold aO
  have fx := fin_xi M.det
  rw [oS_mul_right, ← oS_add hM fx (fx.right det_S),
    oS_congr_tpow 0 (g := fun N => -hF N + hF (Si * N))
      (fun X => by simp only [tpow_zero]; rw [rel1_pt]) M]
  have fh := fin_hF M.det
  rw [oS_add hM fh.neg (fh.left det_Si), oS_neg_fun, oS_hF hM]
  ring

/-- **Second period relation**: `a(M) + a(MU) + a(MU²) = 0`. -/
theorem aO_U {M : M2} (hM : M.det ≠ 0) : aO M + aO (M * U) + aO (M * U * U) = 0 := by
  unfold aO
  have fx := fin_xi M.det
  have hUU : (U * U).det = 1 := by decide
  rw [oS_mul_right, show M * U * U = M * (U * U) by rw [mul_assoc], oS_mul_right,
    ← oS_add hM fx (fx.right det_U),
    ← oS_add hM (fx.add (fx.right det_U)) (fx.right hUU)]
  rw [oS_congr_tpow 0 (g := fun _ => 0) (fun X => by
    simp only [add_zero]
    have := rel2_pt X
    simp only [mul_assoc] at this ⊢
    linarith) M]
  unfold oS; simp

lemma U_S_T (M : M2) : M * T = -(M * U * S) := by
  obtain ⟨a, b, c, d⟩ := M; simp only [T, U, S, mk_mul_mk, neg_mk]; ext <;> simp
lemma UU_S_Tp (M : M2) : M * Tp = -(M * U * U * S) := by
  obtain ⟨a, b, c, d⟩ := M; simp only [Tp, U, S, mk_mul_mk, neg_mk]; ext <;> simp

lemma det_mul_unimod {M g : M2} (hg : g.det = 1) : (M * g).det = M.det := by
  rw [det_mul, hg, mul_one]

/-- `a(M) = a(MT) + a(MT′)`. -/
theorem aO_rec {M : M2} (hM : M.det ≠ 0) : aO M = aO (M * T) + aO (M * Tp) := by
  have h2 := aO_U hM
  have hU : (M * U).det ≠ 0 := by rw [det_mul_unimod det_U]; exact hM
  have hUU : (M * U * U).det ≠ 0 := by rw [det_mul_unimod det_U, det_mul_unimod det_U]; exact hM
  have h1 := aO_S hU
  have h1' := aO_S hUU
  rw [U_S_T, UU_S_Tp, aO_neg, aO_neg]
  linarith

/-! ### Support bound and acyclicity -/

lemma ptC_zero_of {N : M2} (h : ¬(|N.c| ≤ N.det ∧ |N.d| ≤ N.det)) : ptC N = 0 := by
  by_contra hne
  have := ptC_support rfl hne
  exact h ⟨this.2.2.1, this.2.2.2⟩

lemma ptC_Si_zero_of {N : M2} (h : ¬(|N.c| ≤ N.det ∧ |N.d| ≤ N.det)) : ptC (Si * N) = 0 := by
  by_contra hne
  have := ptC_support rfl hne
  have hd : (Si * N).det = N.det := by rw [det_mul, det_Si, one_mul]
  rw [hd] at this
  obtain ⟨a, b, c, d⟩ := N
  simp only [Si, mk_mul_mk, EntBd] at this h
  simp only [zero_mul, one_mul, zero_add] at this
  exact h ⟨this.1, this.2.1⟩

/-- `a(M) ≠ 0` forces `|c|, |d| ≤ det M`. -/
lemma aO_bd {M : M2} (h : aO M ≠ 0) : |M.c| ≤ M.det ∧ |M.d| ≤ M.det := by
  by_contra hc
  apply h
  unfold aO oS
  refine finsum_eq_zero_of_forall_eq_zero fun k => ?_
  have h1 : ¬(|(tpow k M).c| ≤ (tpow k M).det ∧ |(tpow k M).d| ≤ (tpow k M).det) := by
    rw [det_tpow]; exact hc
  have h2 : ¬(|(-tpow k M).c| ≤ (-tpow k M).det ∧ |(-tpow k M).d| ≤ (-tpow k M).det) := by
    rw [det_neg', det_tpow]; simpa [abs_neg] using hc
  simp only [xiC, ptC_zero_of h1, ptC_zero_of h2, ptC_Si_zero_of h1, ptC_Si_zero_of h2]
  ring

/-- **Acyclicity** (positive second row). -/
theorem aO_pos {n : ℤ} : ∀ m : ℕ, ∀ M : M2, M.det = n → 0 < M.c → 0 < M.d →
    (2 * n + 1 - M.c - M.d).toNat ≤ m → aO M = 0 := by
  intro m
  induction m with
  | zero =>
    intro M hM hc hd hm
    by_contra h
    have := aO_bd h
    rw [abs_of_pos hc, abs_of_pos hd, hM] at this
    omega
  | succ m ih =>
    intro M hM hc hd hm
    by_contra h
    have hb := aO_bd h
    rw [abs_of_pos hc, abs_of_pos hd, hM] at hb
    have hn : M.det ≠ 0 := by rw [hM]; omega
    apply h
    rw [aO_rec hn]
    have e1 := ih (M * T) (by rw [det_mul_unimod det_T, hM]) (by simp [T]; omega)
      (by simp [T]; omega) (by simp [T]; omega)
    have e2 := ih (M * Tp) (by rw [det_mul_unimod (by decide), hM]) (by simp [Tp]; omega)
      (by simp [Tp]; omega) (by simp [Tp]; omega)
    rw [e1, e2, add_zero]

/-- **Acyclicity** (PZ Lemma 2 / proof of Theorem A): `a(M) = 0` if `c ≠ 0` and `d ≠ 0`. -/
theorem aO_cd {M : M2} (hc : M.c ≠ 0) (hd : M.d ≠ 0) : aO M = 0 := by
  have key : ∀ X : M2, 0 < X.c → 0 < X.d → aO X = 0 := fun X h1 h2 =>
    aO_pos _ X rfl h1 h2 le_rfl
  rcases lt_or_gt_of_ne hc with h1 | h1 <;> rcases lt_or_gt_of_ne hd with h2 | h2
  · rw [← aO_neg]; exact key _ (by simp; omega) (by simp; omega)
  · -- `c < 0 < d`: `MS` has second row `(d, −c)`
    by_cases h0 : M.det = 0
    · by_contra h; have := aO_bd h; rw [h0] at this
      have := abs_pos.mpr hc; omega
    · have := aO_S h0
      have e : aO (M * S) = 0 := key _ (by simp [S]; omega) (by simp [S]; omega)
      linarith
  · by_cases h0 : M.det = 0
    · by_contra h; have := aO_bd h; rw [h0] at this
      have := abs_pos.mpr hc; omega
    · have := aO_S h0
      have e : aO (M * S) = 0 := by
        rw [← aO_neg]; exact key _ (by simp [S]; omega) (by simp [S]; omega)
      linarith
  · exact key _ h1 h2

/-! ### The orbits with `c = 0` (direct evaluation) and `d = 0` -/

/-- The weight function on the `T`-orbit of `[[a, b], [0, d]]` (in the variable `x = −b`). -/
def winW (a d x : ℤ) : ℚ := w3 (a - d) x 0 + w4 0 x a d + w4 0 x d a

/-- Left end of the window. -/
def winL (a d : ℤ) : ℤ := if a < d then a - d else 0

lemma winW_out {a d x : ℤ} (ha : 0 < a) (hd : 0 < d) (hx : x < winL a d ∨ winL a d + d < x) :
    winW a d x = 0 := by
  unfold winL at hx
  split_ifs at hx with h
  · simp (disch := omega) only [winW, w3, w4, esIfNeg]; norm_num
  · simp (disch := omega) only [winW, w3, w4, esIfNeg]; norm_num

lemma winW_pair {a d r : ℤ} (ha : 0 < a) (hd : 0 < d) (hr0 : 0 ≤ r) (hrd : r < d) :
    winW a d (winL a d + r) + winW a d (winL a d + r + d) = 1 := by
  unfold winL
  rcases lt_trichotomy a d with h | h | h
  · rw [esIfPos h]
    rcases eq_or_lt_of_le hr0 with hr | hr
    · subst hr
      simp (disch := omega) only [winW, w3, w4, esIfPos, esIfNeg]; norm_num
    · rcases lt_trichotomy (a - d + r) 0 with h3 | h3 | h3 <;>
        simp (disch := omega) only [winW, w3, w4, esIfPos, esIfNeg] <;> norm_num
  · rw [esIfNeg (by omega)]
    subst h
    rcases eq_or_lt_of_le hr0 with hr | hr
    · subst hr
      simp (disch := omega) only [winW, w3, w4, esIfPos, esIfNeg]; norm_num
    · simp (disch := omega) only [winW, w3, w4, esIfPos, esIfNeg]; norm_num
  · rw [esIfNeg (by omega)]
    rcases eq_or_lt_of_le hr0 with hr | hr
    · subst hr
      simp (disch := omega) only [winW, w3, w4, esIfPos, esIfNeg]; norm_num
    · simp (disch := omega) only [winW, w3, w4, esIfPos, esIfNeg]; norm_num

/-- Summing the window over a residue class mod `d` gives `1`. -/
lemma sum_winW {a d : ℤ} (ha : 0 < a) (hd : 0 < d) (b : ℤ) :
    ∑ᶠ k : ℤ, winW a d (-(b + k * d)) = 1 := by
  set L := winL a d
  set q := (-b - L) / d
  set r := (-b - L) % d
  have hr0 : 0 ≤ r := Int.emod_nonneg _ (by omega)
  have hrd : r < d := Int.emod_lt_of_pos _ hd
  have hqr : -b - L = d * q + r := by have := Int.mul_ediv_add_emod (-b - L) d; linarith
  have hx : ∀ k : ℤ, -(b + k * d) = L + r + (q - k) * d := by
    intro k; linear_combination hqr
  rw [finsum_eq_sum_of_support_subset (s := {q, q - 1})]
  · rw [Finset.sum_pair (by omega), hx, hx]
    have e1 : L + r + (q - q) * d = L + r := by ring
    have e2 : L + r + (q - (q - 1)) * d = L + r + d := by ring
    rw [e1, e2]; exact winW_pair ha hd hr0 hrd
  · intro k hk
    rw [Function.mem_support] at hk
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff]
    by_contra hne
    push Not at hne
    apply hk
    rw [hx]
    apply winW_out ha hd
    rcases lt_or_gt_of_ne hne.1 with h1 | h1
    · -- `k < q`, `k ≠ q − 1`: `q − k ≥ 2`
      right
      have : 2 ≤ q - k := by omega
      nlinarith
    · left
      have : q - k ≤ -1 := by omega
      nlinarith

lemma w3_zero {x y z : ℤ} (h : ¬(x ≤ y ∧ y ≤ z)) : w3 x y z = 0 := by
  unfold w3; rw [esIfNeg h]
lemma w4_zero {x y z u : ℤ} (h : ¬(x ≤ y ∧ y ≤ z ∧ z ≤ u)) : w4 x y z u = 0 := by
  unfold w4; rw [esIfNeg h]

lemma xiC_c0 {a d : ℤ} (ha : 0 < a) (hd : 0 < d) (y : ℤ) :
    xiC ⟨a, y, 0, d⟩ + xiC (-⟨a, y, 0, d⟩) = winW a d (-y) := by
  simp only [xiC, Si, mk_mul_mk, neg_mk, winW, mul_zero, zero_mul, add_zero, zero_add, one_mul,
    neg_mul, neg_zero, neg_neg]
  simp only [ptC]
  simp (disch := omega) only [esIfPos, esIfNeg]
  simp only [neg_neg, zero_sub, sub_neg_eq_add, sub_zero]
  split_ifs <;> simp (disch := omega) only [w3_zero, w4_zero] <;> ring

/-- **`c = 0`**: `a(M) = 1` (the parabolic/hyperbolic orbits of `T^∞`). -/
theorem aO_c0 {M : M2} (hc : M.c = 0) (hn : 0 < M.det) : aO M = 1 := by
  have key : ∀ X : M2, X.c = 0 → 0 < X.d → 0 < X.det → aO X = 1 := by
    intro X hc hd hn
    obtain ⟨a, b, c, d⟩ := X
    simp only at hc hd; subst hc
    have ha : 0 < a := by
      simp only [det, mul_zero, sub_zero] at hn; exact pos_of_mul_pos_left hn hd.le
    unfold aO oS
    have e : ∀ k : ℤ, tpow k ⟨a, b, 0, d⟩ = ⟨a, b + k * d, 0, d⟩ := fun k => by
      ext <;> simp
    simp only [e, xiC_c0 ha hd]
    exact sum_winW ha hd b
  rcases lt_trichotomy M.d 0 with hd | hd | hd
  · rw [← aO_neg]
    exact key _ (by simp [hc]) (by simp; omega) (by rw [det_neg']; exact hn)
  · exfalso; simp [det, hc, hd] at hn
  · exact key M hc hd hn

/-- **`d = 0`**: `a(M) = −1`. -/
theorem aO_d0 {M : M2} (hd : M.d = 0) (hn : 0 < M.det) : aO M = -1 := by
  have h := aO_S hn.ne'
  have e : aO (M * S) = 1 := aO_c0 (by simp [S, hd]) (by rw [det_mul_unimod det_S]; exact hn)
  linarith

/-! ### The element `T^∞ₙ(1 − S)` -/

/-- Coefficient function of `T^∞ₙ = Σ_{ad = n, d > 0, 0 ≤ b < d} [[a, b], [0, d]]`. -/
def tinf (n : ℤ) (N : M2) : ℚ :=
  if N.c = 0 ∧ N.det = n ∧ 0 < N.d ∧ 0 ≤ N.b ∧ N.b < N.d then 1 else 0

/-- Coefficient function of `T^∞ₙ(1 − S)` (`(x·S)(N) = x(N S⁻¹)`). -/
def rhsC (n : ℤ) (N : M2) : ℚ := tinf n N - tinf n (N * Si)

lemma tinf_bd {n : ℤ} {N : M2} (h : tinf n N ≠ 0) :
    N.c = 0 ∧ N.det = n ∧ 0 < N.d ∧ 0 ≤ N.b ∧ N.b < N.d := by
  unfold tinf at h; split_ifs at h with h1
  · exact h1
  · exact absurd rfl h

lemma fin_tinf {n : ℤ} (hn : 0 < n) : FinDet n (tinf n) := by
  refine FinDet.of_bd fun N hdet hN => ?_
  obtain ⟨h1, h2, h3, h4, h5⟩ := tinf_bd hN
  obtain ⟨a, b, c, d⟩ := N
  simp only [det] at h2 h1 h3 h4 h5
  subst h1
  have had : a * d = n := by simpa using h2
  have ha : 0 < a := pos_of_mul_pos_left (by rw [had]; exact hn) h3.le
  have e1 : a ≤ n := by nlinarith
  have e2 : d ≤ n := by nlinarith
  simp only [EntBd]
  refine ⟨abs_le.mpr ⟨by omega, e1⟩, abs_le.mpr ⟨by omega, by omega⟩,
    abs_le.mpr ⟨by omega, by omega⟩, abs_le.mpr ⟨by omega, e2⟩⟩

lemma fin_rhs {n : ℤ} (hn : 0 < n) : FinDet n (rhsC n) :=
  (fin_tinf hn).sub ((fin_tinf hn).right det_Si)

/-- Each orbit with `c = 0` meets `T^∞ₙ` exactly once. -/
lemma oS_tinf {n : ℤ} {M : M2} (hM : M.det = n) (hn : 0 < n) :
    oS (tinf n) M = if M.c = 0 then 1 else 0 := by
  by_cases hc : M.c = 0
  · rw [esIfPos hc]
    have key : ∀ X : M2, X.c = 0 → 0 < X.d → X.det = n → oS (tinf n) X = 1 := by
      intro X hc hd hX
      unfold oS
      rw [finsum_eq_single _ (-(X.b / X.d))]
      · have h1 : tinf n (tpow (-(X.b / X.d)) X) = 1 := by
          unfold tinf
          rw [esIfPos]
          refine ⟨by simp [hc], by rw [det_tpow, hX], by simp; exact hd, ?_, ?_⟩
          · have := Int.mul_ediv_add_emod X.b X.d
            have := Int.emod_nonneg X.b hd.ne'
            simp only [tpow_b]; nlinarith
          · have := Int.mul_ediv_add_emod X.b X.d
            have := Int.emod_lt_of_pos X.b hd
            simp only [tpow_b, tpow_d]; nlinarith
        have h2 : tinf n (-tpow (-(X.b / X.d)) X) = 0 := by
          unfold tinf; rw [esIfNeg]; simp; omega
        rw [h1, h2, add_zero]
      · intro k hk
        have h2 : tinf n (-tpow k X) = 0 := by
          unfold tinf; rw [esIfNeg]; simp; omega
        have h1 : tinf n (tpow k X) = 0 := by
          unfold tinf; rw [esIfNeg]
          rintro ⟨-, -, -, h4, h5⟩
          apply hk
          simp only [tpow_b, tpow_d] at h4 h5
          have e1 : (X.b + k * X.d) / X.d = X.b / X.d + k := Int.add_mul_ediv_right _ _ hd.ne'
          have e2 : (X.b + k * X.d) / X.d = 0 := Int.ediv_eq_zero_of_lt h4 h5
          omega
        rw [h1, h2, add_zero]
    rcases lt_trichotomy M.d 0 with hd | hd | hd
    · rw [← oS_neg]; exact key _ (by simp [hc]) (by simp; omega) (by rw [det_neg', hM])
    · exfalso; rw [← hM] at hn; simp [det, hc, hd] at hn
    · exact key M hc hd hM
  · rw [esIfNeg hc]
    unfold oS
    refine finsum_eq_zero_of_forall_eq_zero fun k => ?_
    unfold tinf
    rw [esIfNeg (by simp; omega), esIfNeg (by simp; omega), add_zero]

lemma oS_rhsC {n : ℤ} {M : M2} (hM : M.det = n) (hn : 0 < n) :
    oS (rhsC n) M = (if M.c = 0 then 1 else 0) - (if M.d = 0 then 1 else 0) := by
  have hM0 : M.det ≠ 0 := by rw [hM]; exact hn.ne'
  unfold rhsC
  rw [oS_sub hM0 (by rw [hM]; exact fin_tinf hn) (by rw [hM]; exact (fin_tinf hn).right det_Si),
    ← oS_mul_right, oS_tinf hM hn, oS_tinf (by rw [det_mul_unimod det_Si, hM]) hn]
  have : (M * Si).c = -M.d := by simp [Si]
  rw [this]
  congr 1
  by_cases h : M.d = 0
  · rw [esIfPos (by omega), esIfPos h]
  · rw [esIfNeg (by omega), esIfNeg h]

/-- **Property (A)**, orbit form (PZ (A) ⟺ (10)): every left `±T^ℤ`-orbit sum of
`(1 − S)T̃ₙ − T^∞ₙ(1 − S)` vanishes. -/
theorem propA_orbit {n : ℤ} (hn : 0 < n) {M : M2} (hM : M.det = n) :
    oS xiC M = oS (rhsC n) M := by
  rw [oS_rhsC hM hn]
  have hpos : 0 < M.det := by rw [hM]; exact hn
  by_cases hc : M.c = 0
  · have hd : M.d ≠ 0 := by intro hd; simp [det, hc, hd] at hpos
    rw [esIfPos hc, esIfNeg hd]; exact (aO_c0 hc hpos).trans (by norm_num)
  · by_cases hd : M.d = 0
    · rw [esIfNeg hc, esIfPos hd]; exact (aO_d0 hd hpos).trans (by norm_num)
    · rw [esIfNeg hc, esIfNeg hd]; exact (aO_cd hc hd).trans (by norm_num)

end RamanujanWeil.Arith.ES
