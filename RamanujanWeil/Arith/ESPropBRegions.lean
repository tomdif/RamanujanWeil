import RamanujanWeil.Arith.ESSupport

/-!
# A2 / ES-P5a: Popa–Zagier (16a), (16b) as pointwise identities (docs/ARITH_ES_PLAN.md, §2 P5)

PZ (arXiv:1711.00327, proof of Theorem 4(a)):

  (16a) `T̃ = −F − UFS − U²F + T₁(1 − S)`,
  (16b) `T̃ = −G − SGU + T₁(1 − U) + (1/12)[a−d = c = −b ; d ≤ 0 < a](1 − U)`,

with `F = ⟨0 ≤ a−d ≤ c ; a−d ≤ −b | d ≤ b < 0 < c⟩`,
`G = ⟨0 ≤ a−d ≤ c ; a−d ≤ −b ; a ≤ −b−c | a ≤ 0 ; b < 0 < c⟩*`.

The coefficient of `γ x δ` at `M` is `x(γ⁻¹ M δ⁻¹)`. With the sign choices below the identities
hold **exactly** in `ℚ[M₂(ℤ)]`, i.e. pointwise for every integer matrix `M` (no `±`):

* `ptC_16a : ptC M = −F(M) − F(αM) − F(βM) + T₁(M) − T₁(γM)` with
  `αM = −U⁻¹MS⁻¹`, `βM = −U⁻²M`, `γM = MS⁻¹`;
* `ptC_16b : ptC M = −G(M) − G(δM) + T₁(M) − T₁(εM) + (Q(M) − Q(εM))/12` with
  `δM = −S⁻¹MU⁻¹`, `εM = MU⁻¹`.

Each is reduced to PZ's closed forms `T₁S = ⟨d ≤ a ≤ b+c | b < d ≤ 0⟩`,
`UFS = ⟨d ≤ a ≤ c+d ; b+c ≤ a | a ≤ 0 < c ; b < d⟩`, `U²F = ⟨a−d ≤ c ; −b ≤ c ≤ a−b | b < d ≤ 0 < a⟩`,
`T₁U = T₂`, and then to `T₂ + T₃ + T₄ = F + UFS + U²F + T₁S` resp.
`T₃ + T₄ = G + SGU + (QU − Q)/12`, checked by case analysis on the second-line signs.
(Numerically verified on `[−5, 5]⁴`, scratch `es2/p16b.py`.)
-/

namespace RamanujanWeil.Arith.ES

open M2

/-- `F = ⟨0 ≤ a−d ≤ c ; a−d ≤ −b | d ≤ b < 0 < c⟩`. -/
def regF (M : M2) : ℚ := if M.d ≤ M.b ∧ M.b < 0 ∧ 0 < M.c then eW (M.a - M.d) (-M.b) M.c else 0

/-- PZ's starred weight for `G`: `1/4` at `a−d = c = −b` or `a = d = −b−c`, else `1/2` on the
boundary, `1` inside. -/
def gW (a b c d : ℤ) : ℚ :=
  if 0 ≤ a - d ∧ a - d ≤ c ∧ a - d ≤ -b ∧ a ≤ -b - c then
    (if (a - d = c ∧ c = -b) ∨ (a = d ∧ d = -b - c) then 1 / 4
     else if 0 = a - d ∨ a - d = c ∨ a - d = -b ∨ a = -b - c then 1 / 2 else 1)
  else 0

/-- `G = ⟨0 ≤ a−d ≤ c ; a−d ≤ −b ; a ≤ −b−c | a ≤ 0 ; b < 0 < c⟩*`. -/
def regG (M : M2) : ℚ := if M.a ≤ 0 ∧ M.b < 0 ∧ 0 < M.c then gW M.a M.b M.c M.d else 0

/-- `Q = [a−d = c = −b ; d ≤ 0 < a]`. -/
def regQ (M : M2) : ℚ := if M.a - M.d = M.c ∧ M.c = -M.b ∧ M.d ≤ 0 ∧ 0 < M.a then 1 else 0

lemma regF_mk (a b c d : ℤ) : regF ⟨a, b, c, d⟩ =
    if d ≤ b ∧ b < 0 ∧ 0 < c then eW (a - d) (-b) c else 0 := rfl
lemma regG_mk (a b c d : ℤ) : regG ⟨a, b, c, d⟩ =
    if a ≤ 0 ∧ b < 0 ∧ 0 < c then gW a b c d else 0 := rfl
lemma regQ_mk (a b c d : ℤ) : regQ ⟨a, b, c, d⟩ =
    if a - d = c ∧ c = -b ∧ d ≤ 0 ∧ 0 < a then 1 else 0 := rfl

/-- Case analysis on the signs of the given linear forms, then evaluate all weights. -/
syntax "es_signs" "[" term,* "]" : tactic
macro_rules
  | `(tactic| es_signs []) => `(tactic| first
      | (exfalso; omega)
      | (simp (disch := omega) only [esIfPos, esIfNeg, w3, w4, eW, gW, wI] <;> norm_num)
      | norm_num)
  | `(tactic| es_signs [$t]) =>
      `(tactic| (rcases lt_trichotomy $t 0 with h | h | h <;> es_signs []))
  | `(tactic| es_signs [$t, $ts,*]) =>
      `(tactic| (rcases lt_trichotomy $t 0 with h | h | h <;> es_signs [$ts,*]))


/-! ### The transformed arguments -/

/-- `αM = −U⁻¹ M S⁻¹`. -/
def mapA (M : M2) : M2 := ⟨M.d, -M.c, M.d - M.b, M.a - M.c⟩
/-- `βM = −U⁻² M`. -/
def mapB (M : M2) : M2 := ⟨M.a - M.c, M.b - M.d, M.a, M.b⟩
/-- `γM = M S⁻¹`. -/
def mapC (M : M2) : M2 := ⟨-M.b, M.a, -M.d, M.c⟩
/-- `δM = −S⁻¹ M U⁻¹`. -/
def mapD (M : M2) : M2 := ⟨M.d, -M.c - M.d, -M.b, M.a + M.b⟩
/-- `εM = M U⁻¹`. -/
def mapE (M : M2) : M2 := ⟨-M.b, M.a + M.b, -M.d, M.c + M.d⟩

/-! ### Closed forms (PZ's descriptions of `T₁S`, `UFS`, `U²F`, `T₁U`, `SGU`, `QU`) -/

lemma w3_rev (x y z : ℤ) : w3 (-z) (-y) (-x) = w3 x y z := by
  unfold w3
  split_ifs <;> first | (exfalso; omega) | norm_num

/-- `T₁S = ⟨d ≤ a ≤ b + c | b < d ≤ 0⟩`. -/
lemma regT1_mapC (a b c d : ℤ) : regT1 (mapC ⟨a, b, c, d⟩) =
    if b < d ∧ d ≤ 0 then w3 d a (b + c) else 0 := by
  simp only [mapC, regT1_mk]
  have e : w3 (-b - c) (- a) (-d) = w3 d a (b + c) := by
    rw [← w3_rev d a (b + c)]; congr 1; ring
  rw [e]
  split_ifs <;> first | (exfalso; omega) | rfl

/-- `UFS = ⟨d ≤ a ≤ c + d ; b + c ≤ a | a ≤ 0 < c ; b < d⟩`. -/
lemma regF_mapA (a b c d : ℤ) : regF (mapA ⟨a, b, c, d⟩) =
    if a ≤ 0 ∧ 0 < c ∧ b < d then eW (c + d - a) c (d - b) else 0 := by
  simp only [mapA, regF_mk]
  have e : eW (d - (a - c)) (-(-c)) (d - b) = eW (c + d - a) c (d - b) := by
    congr 1 <;> ring
  rw [e]
  split_ifs <;> first | (exfalso; omega) | rfl

/-- `U²F = ⟨a−d ≤ c ; −b ≤ c ≤ a−b | b < d ≤ 0 < a⟩`. -/
lemma regF_mapB (a b c d : ℤ) : regF (mapB ⟨a, b, c, d⟩) =
    if b < d ∧ d ≤ 0 ∧ 0 < a then eW (a - b - c) (d - b) a else 0 := by
  simp only [mapB, regF_mk]
  have e : eW (a - c - b) (-(b - d)) a = eW (a - b - c) (d - b) a := by
    congr 1 <;> ring
  rw [e]
  split_ifs <;> first | (exfalso; omega) | rfl

/-- `T₁U = T₂`. -/
lemma regT1_mapE (M : M2) : regT1 (mapE M) = regT2 M := by
  obtain ⟨a, b, c, d⟩ := M
  simp only [mapE, regT1_mk, regT2_mk]
  have e : w3 (-b - (c + d)) (-(a + b)) (-d) = w3 (-b) (a - d) c := by
    rw [← w3_rev, ← w3_shift (-b) (a - d) c (b + d)]; congr 1 <;> ring
  rw [e]
  split_ifs <;> first | (exfalso; omega) | rfl

/-- `SGU = ⟨0 ≤ a−d ≤ −b ≤ c ; −b−c ≤ a | −c < d ≤ 0 < −b⟩*` (in `gW` form). -/
lemma regG_mapD (a b c d : ℤ) : regG (mapD ⟨a, b, c, d⟩) =
    if d ≤ 0 ∧ 0 < c + d ∧ b < 0 then gW d (-c - d) (-b) (a + b) else 0 := by
  simp only [mapD, regG_mk]
  split_ifs <;> first | (exfalso; omega) | rfl

/-- `QU = [a−d = c = −b ; c + d ≤ 0 < c]`. -/
lemma regQ_mapE (a b c d : ℤ) : regQ (mapE ⟨a, b, c, d⟩) =
    if a - d = c ∧ c = -b ∧ c + d ≤ 0 ∧ 0 < c then 1 else 0 := by
  simp only [mapE, regQ_mk]
  split_ifs <;> first | (exfalso; omega) | rfl

/-! ### The two identities -/

lemma eW_split' (x p q : ℤ) (hp : 0 < p) (hq : 0 < q) :
    eW x p q = w4 0 x q p + w4 0 x p q := by
  simp only [eW, w4]
  split_ifs <;> first | (exfalso; omega) | norm_num

/-- (16a), case `b < d ≤ 0`, `a ≤ 0 < c`: `T₂ + T₃ + T₄ = UFS + T₁S`. -/
lemma c16a_neg (a b c d : ℤ) (h1 : b < d) (h2 : d ≤ 0) (h3 : a ≤ 0) (h4 : 0 < c) :
    w3 (-b) (a - d) c + w4 0 (a - d) c (-b) + w4 0 (a - d) (-b) c =
      eW (c + d - a) c (d - b) + w3 d a (b + c) := by
  es_signs [a - d + b, c - a + d, a - d, c + b, a - b - c]

/-- (16a), case `b < d ≤ 0 < a`: `T₂ + T₄ = U²F + T₁S`. -/
lemma c16a_pos (a b c d : ℤ) (h1 : b < d) (h2 : d ≤ 0) (h3 : 0 < a) :
    w3 (-b) (a - d) c + w4 0 (a - d) (-b) c = eW (a - b - c) (d - b) a + w3 d a (b + c) := by
  es_signs [a - d + b, c - a + d, a - d, c + b, a - b - c]

/-- `T₂ + T₃ + T₄ = F + UFS + U²F + T₁S`. -/
lemma sum16a (a b c d : ℤ) :
    regT2 ⟨a, b, c, d⟩ + regT3 ⟨a, b, c, d⟩ + regT4 ⟨a, b, c, d⟩ =
      regF ⟨a, b, c, d⟩ + regF (mapA ⟨a, b, c, d⟩) + regF (mapB ⟨a, b, c, d⟩) +
        regT1 (mapC ⟨a, b, c, d⟩) := by
  rw [regF_mapA, regF_mapB, regT1_mapC, regT2_mk, regT3_mk, regT4_mk, regF_mk]
  rcases le_or_gt d b with hdb | hbd
  · simp (disch := omega) only [esIfNeg]
    by_cases hb : b < 0 <;> by_cases hc : 0 < c <;> by_cases ha : a ≤ 0 <;>
      (try simp (disch := omega) only [esIfPos, esIfNeg]) <;>
      es_signs [a - d + b, c - a + d, a - d, c + b]
  · rcases le_or_gt d 0 with hd | hd
    · by_cases ha : a ≤ 0
      · by_cases hc : 0 < c
        · simp (disch := omega) only [esIfPos, esIfNeg]
          linarith [c16a_neg a b c d hbd hd ha hc]
        · simp (disch := omega) only [esIfPos, esIfNeg]
          es_signs [a - d + b, c - a + d, a - d, c + b, a - b - c]
      · simp (disch := omega) only [esIfPos, esIfNeg]
        linarith [c16a_pos a b c d hbd hd (by omega)]
    · simp (disch := omega) only [esIfNeg]
      by_cases ha : a ≤ 0 <;> by_cases hc : 0 < c <;>
        (try simp (disch := omega) only [esIfPos, esIfNeg]) <;>
        es_signs [a - d, c - a + d]

/-- (16b), main case `b < 0 < c`, `d ≤ 0`. -/
lemma c16b (a b c d : ℤ) (hb : b < 0) (hc : 0 < c) (hd : d ≤ 0) :
    ((if a ≤ 0 ∧ 0 < c then w4 0 (a - d) c (-b) else 0) +
      if d ≤ 0 ∧ 0 < -b then w4 0 (a - d) (-b) c else 0) =
      (if a ≤ 0 ∧ b < 0 ∧ 0 < c then gW a b c d else 0) +
        (if d ≤ 0 ∧ 0 < c + d ∧ b < 0 then gW d (-c - d) (-b) (a + b) else 0) +
        ((if a - d = c ∧ c = -b ∧ c + d ≤ 0 ∧ 0 < c then 1 else 0) -
          (if a - d = c ∧ c = -b ∧ d ≤ 0 ∧ 0 < a then 1 else 0)) / 12 := by
  by_cases ha : a ≤ 0 <;> by_cases hcd : 0 < c + d <;>
    simp (disch := omega) only [esIfPos, esIfNeg] <;>
    es_signs [a - d, c - a + d, a - d + b, a + b + c, c + b]

/-- `T₃ + T₄ = G + SGU + (QU − Q)/12`. -/
lemma sum16b (a b c d : ℤ) :
    regT3 ⟨a, b, c, d⟩ + regT4 ⟨a, b, c, d⟩ =
      regG ⟨a, b, c, d⟩ + regG (mapD ⟨a, b, c, d⟩) +
        (regQ (mapE ⟨a, b, c, d⟩) - regQ ⟨a, b, c, d⟩) / 12 := by
  rw [regG_mapD, regQ_mapE, regT3_mk, regT4_mk, regG_mk, regQ_mk]
  by_cases hb : b < 0
  · by_cases hc : 0 < c
    · by_cases hd : d ≤ 0
      · exact c16b a b c d hb hc hd
      · simp (disch := omega) only [esIfNeg]
        by_cases ha : a ≤ 0 <;> (try simp (disch := omega) only [esIfPos, esIfNeg]) <;>
          es_signs [a - d]
    · simp (disch := omega) only [esIfNeg]
      by_cases hd : d ≤ 0 <;> (try simp (disch := omega) only [esIfPos, esIfNeg]) <;>
        es_signs [a - d + b, c + b]
  · simp (disch := omega) only [esIfNeg]
    by_cases ha : a ≤ 0 <;> by_cases hc : 0 < c <;>
      (try simp (disch := omega) only [esIfPos, esIfNeg]) <;> es_signs [a - d, c + b]

/-- **PZ (16a), pointwise**: `T̃ = −F − UFS − U²F + T₁ − T₁S`. -/
theorem ptC_16a (M : M2) :
    ptC M = -regF M - regF (mapA M) - regF (mapB M) + regT1 M - regT1 (mapC M) := by
  obtain ⟨a, b, c, d⟩ := M
  have := sum16a a b c d
  rw [ptC_eq]; linarith

/-- **PZ (16b), pointwise**: `T̃ = −G − SGU + T₁ − T₁U + (Q − QU)/12`. -/
theorem ptC_16b (M : M2) :
    ptC M = -regG M - regG (mapD M) + regT1 M - regT1 (mapE M) +
      (regQ M - regQ (mapE M)) / 12 := by
  obtain ⟨a, b, c, d⟩ := M
  have := sum16b a b c d
  rw [ptC_eq, regT1_mapE]; linarith

/-! ### Support bounds for `F`, `G`, `Q` -/

lemma eW_ne_zero {x p q : ℤ} (h : eW x p q ≠ 0) : 0 ≤ x ∧ x ≤ p ∧ x ≤ q := by
  by_contra hc; apply h; unfold eW; rw [esIfNeg hc]

lemma gW_ne_zero {a b c d : ℤ} (h : gW a b c d ≠ 0) :
    0 ≤ a - d ∧ a - d ≤ c ∧ a - d ≤ -b ∧ a ≤ -b - c := by
  by_contra hc; apply h; unfold gW; rw [esIfNeg hc]

lemma regF_bd {M : M2} {n : ℤ} (hdet : M.det = n) (h : regF M ≠ 0) : EntBd n M := by
  obtain ⟨a, b, c, d⟩ := M
  rw [regF_mk] at h
  split_ifs at h with h0
  · have hw := eW_ne_zero h
    rcases le_total c (-b) with hcb | hcb
    · exact bnd_T3 hdet (by omega) h0.2.2 ⟨hw.1, hw.2.2, hcb⟩
    · exact bnd_T4 hdet (by omega) (by omega) ⟨hw.1, hw.2.1, hcb⟩
  · exact absurd rfl h

lemma regG_bd {M : M2} {n : ℤ} (hdet : M.det = n) (h : regG M ≠ 0) : EntBd n M := by
  obtain ⟨a, b, c, d⟩ := M
  rw [regG_mk] at h
  split_ifs at h with h0
  · have hw := gW_ne_zero h
    rcases le_total c (-b) with hcb | hcb
    · exact bnd_T3 hdet h0.1 h0.2.2 ⟨hw.1, hw.2.1, hcb⟩
    · exact bnd_T4 hdet (by omega) (by omega) ⟨hw.1, hw.2.2.1, hcb⟩
  · exact absurd rfl h

lemma regQ_bd {M : M2} {n : ℤ} (hdet : M.det = n) (h : regQ M ≠ 0) : EntBd n M := by
  obtain ⟨a, b, c, d⟩ := M
  rw [regQ_mk] at h
  split_ifs at h with h0
  · exact bnd_T4 hdet h0.2.2.1 (by omega) ⟨by omega, by omega, by omega⟩
  · exact absurd rfl h

end RamanujanWeil.Arith.ES
