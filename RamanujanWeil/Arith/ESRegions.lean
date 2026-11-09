import RamanujanWeil.Arith.ESTtilde

/-!
# A2 / ES-P6a: Popa–Zagier Lemma 4 as pointwise region identities (docs/ARITH_ES_PLAN.md, §2 P6)

Popa–Zagier (arXiv:1711.00327, §4) define `E, H, X, Y, Z` and show (Lemma 4)
`T̃ = −E + H + X − SXS + Y − U²YU + Z − U²ZU`. Their proof splits `E = A₁ + A₂ + B₁ + B₂`,
`Z = Z₁ + Z₂`, `U²ZU = Z₃ + Z₄` and checks `Z₁ = SXS`, `Z₂ = A₁`, `X = B₁ + Z₃ + U²YU`,
`Y + H = T₁`, `Z₄ = T₂`, `A₂ = T₃`, `B₂ = T₄`.

We record exactly these facts as identities of coefficient functions `M2 → ℚ`, valid for **all**
integer matrices (no determinant condition), with the conjugations realised by the explicit
maps `conjS M = −S M S` and `conjU M = −U M U²` (`= U⁻² M U⁻¹`). Both preserve `det` and `tr`
(`det_conjS`, `tr_conjS`, `det_conjU`, `tr_conjU`) and are bijections (`conjSEquiv`, `conjUEquiv`).

* `regZ_eq`  : `Z(M) = X(−SMS) + A₁(M)`;
* `regZ_conjU` : `Z(−UMU²) = Z₃(M) + T₂(M)`;
* `regX_eq`  : `X(M) = B₁(M) + Z₃(M) + Y(−UMU²)`;
* `regT1_eq` : `T₁ = Y + H`;
* `regE_eq`  : `E = A₁ + T₃ + B₁ + T₄`.

All checked numerically on `[−7,7]⁴` (scratch `es2/pw.py`).
-/

namespace RamanujanWeil.Arith.ES

open M2

/-- `if_pos`, stated locally (used as a `simp` lemma with an `omega` discharger). -/
theorem esIfPos {α : Sort*} {p : Prop} [Decidable p] {x y : α} (h : p) :
    (if p then x else y) = x := by simp [h]
/-- `if_neg`, stated locally. -/
theorem esIfNeg {α : Sort*} {p : Prop} [Decidable p] {x y : α} (h : ¬p) :
    (if p then x else y) = y := by simp [h]

/-- Weight of two independent inequalities `x ≤ y`, `z ≤ u` (product of half-weights). -/
def wI (x y z u : ℤ) : ℚ :=
  if x ≤ y ∧ z ≤ u then (if x = y then 1 / 2 else 1) * (if z = u then 1 / 2 else 1) else 0

/-- Weight of `0 ≤ x ≤ p ; x ≤ q` (PZ's `E`): `1/6` for nested, `1/3` for overlapping
equalities. -/
def eW (x p q : ℤ) : ℚ :=
  if 0 ≤ x ∧ x ≤ p ∧ x ≤ q then
    (if x = 0 then (if x = p ∨ x = q then 1 / 6 else 1 / 2)
     else (if x = p then (if x = q then 1 / 3 else 1 / 2) else (if x = q then 1 / 2 else 1)))
  else 0

/-- `T₁ = ⟨a−d ≤ −b ≤ c | 0 ≤ c < a⟩`. -/
def regT1 (M : M2) : ℚ := if 0 ≤ M.c ∧ M.c < M.a then w3 (M.a - M.d) (-M.b) M.c else 0
/-- `T₂ = ⟨−b ≤ a−d ≤ c | b < d ≤ 0⟩`. -/
def regT2 (M : M2) : ℚ := if M.b < M.d ∧ M.d ≤ 0 then w3 (-M.b) (M.a - M.d) M.c else 0
/-- `T₃ = ⟨0 ≤ a−d ≤ c ≤ −b | a ≤ 0 < c⟩` (`= A₂`). -/
def regT3 (M : M2) : ℚ := if M.a ≤ 0 ∧ 0 < M.c then w4 0 (M.a - M.d) M.c (-M.b) else 0
/-- `T₄ = ⟨0 ≤ a−d ≤ −b ≤ c | d ≤ 0 < −b⟩` (`= B₂`). -/
def regT4 (M : M2) : ℚ := if M.d ≤ 0 ∧ 0 < -M.b then w4 0 (M.a - M.d) (-M.b) M.c else 0
/-- `H = ⟨a−d ≤ −b ≤ c | c = 0 < a⟩`. -/
def regH (M : M2) : ℚ := if M.c = 0 ∧ 0 < M.a then w3 (M.a - M.d) (-M.b) M.c else 0
/-- `Y = ⟨a−d ≤ −b ≤ c | 0 < c < a⟩`. -/
def regY (M : M2) : ℚ := if 0 < M.c ∧ M.c < M.a then w3 (M.a - M.d) (-M.b) M.c else 0
/-- `A₁ = ⟨0 ≤ a−d ≤ c ≤ −b | 0 < c, 0 < a⟩`. -/
def regA1 (M : M2) : ℚ := if 0 < M.c ∧ 0 < M.a then w4 0 (M.a - M.d) M.c (-M.b) else 0
/-- `B₁ = ⟨0 ≤ a−d ≤ −b ≤ c | b < 0 < d⟩`. -/
def regB1 (M : M2) : ℚ := if M.b < 0 ∧ 0 < M.d then w4 0 (M.a - M.d) (-M.b) M.c else 0
/-- `E = ⟨0 ≤ a−d ≤ −b ; a−d ≤ c | b < 0 < c⟩` (elliptic matrices with fixed point in `F`). -/
def regE (M : M2) : ℚ := if M.b < 0 ∧ 0 < M.c then eW (M.a - M.d) (-M.b) M.c else 0
/-- `X = ⟨0 ≤ a−d ; −b ≤ c | b < 0 < d⟩`. -/
def regX (M : M2) : ℚ := if M.b < 0 ∧ 0 < M.d then wI 0 (M.a - M.d) (-M.b) M.c else 0
/-- `Z = ⟨a−d ≤ c ≤ −b | 0 < a ; 0 < c⟩`. -/
def regZ (M : M2) : ℚ := if 0 < M.a ∧ 0 < M.c then w3 (M.a - M.d) M.c (-M.b) else 0
/-- `Z₃ = ⟨−b ≤ a−d ≤ c | b < 0 < d⟩`. -/
def regZ3 (M : M2) : ℚ := if M.b < 0 ∧ 0 < M.d then w3 (-M.b) (M.a - M.d) M.c else 0

lemma regT1_mk (a b c d : ℤ) : regT1 ⟨a, b, c, d⟩ = if 0 ≤ c ∧ c < a then w3 (a - d) (-b) c else 0 := rfl
lemma regT2_mk (a b c d : ℤ) : regT2 ⟨a, b, c, d⟩ = if b < d ∧ d ≤ 0 then w3 (-b) (a - d) c else 0 := rfl
lemma regT3_mk (a b c d : ℤ) : regT3 ⟨a, b, c, d⟩ = if a ≤ 0 ∧ 0 < c then w4 0 (a - d) c (-b) else 0 := rfl
lemma regT4_mk (a b c d : ℤ) : regT4 ⟨a, b, c, d⟩ = if d ≤ 0 ∧ 0 < -b then w4 0 (a - d) (-b) c else 0 := rfl
lemma regH_mk (a b c d : ℤ) : regH ⟨a, b, c, d⟩ = if c = 0 ∧ 0 < a then w3 (a - d) (-b) c else 0 := rfl
lemma regY_mk (a b c d : ℤ) : regY ⟨a, b, c, d⟩ = if 0 < c ∧ c < a then w3 (a - d) (-b) c else 0 := rfl
lemma regA1_mk (a b c d : ℤ) : regA1 ⟨a, b, c, d⟩ = if 0 < c ∧ 0 < a then w4 0 (a - d) c (-b) else 0 := rfl
lemma regB1_mk (a b c d : ℤ) : regB1 ⟨a, b, c, d⟩ = if b < 0 ∧ 0 < d then w4 0 (a - d) (-b) c else 0 := rfl
lemma regE_mk (a b c d : ℤ) : regE ⟨a, b, c, d⟩ = if b < 0 ∧ 0 < c then eW (a - d) (-b) c else 0 := rfl
lemma regX_mk (a b c d : ℤ) : regX ⟨a, b, c, d⟩ = if b < 0 ∧ 0 < d then wI 0 (a - d) (-b) c else 0 := rfl
lemma regZ_mk (a b c d : ℤ) : regZ ⟨a, b, c, d⟩ = if 0 < a ∧ 0 < c then w3 (a - d) c (-b) else 0 := rfl
lemma regZ3_mk (a b c d : ℤ) : regZ3 ⟨a, b, c, d⟩ = if b < 0 ∧ 0 < d then w3 (-b) (a - d) c else 0 := rfl

lemma ptC_eq (M : M2) : ptC M = regT1 M - regT2 M - regT3 M - regT4 M := rfl

/-- `−S M S`. -/
def conjS (M : M2) : M2 := ⟨M.d, -M.c, -M.b, M.a⟩
/-- `−U M U² = U⁻² M U⁻¹`. -/
def conjU (M : M2) : M2 := ⟨M.d - M.b, M.a + M.b - M.c - M.d, -M.b, M.a + M.b⟩
/-- Inverse of `conjU`: `−U² M U`. -/
def conjUinv (M : M2) : M2 := ⟨M.c + M.d, -M.c, M.c - M.a - M.b + M.d, M.a - M.c⟩

lemma conjS_eq (M : M2) : conjS M = -(S * M * S) := by
  ext <;> simp [conjS, S]
lemma conjU_eq (M : M2) : conjU M = -(U * M * (U * U)) := by
  ext <;> (simp [conjU, U]; try ring)

lemma det_conjS (M : M2) : (conjS M).det = M.det := by simp only [conjS, det]; ring
lemma tr_conjS (M : M2) : (conjS M).tr = M.tr := by simp only [conjS, tr]; ring
lemma det_conjU (M : M2) : (conjU M).det = M.det := by simp only [conjU, det]; ring
lemma tr_conjU (M : M2) : (conjU M).tr = M.tr := by simp only [conjU, tr]; ring

/-- `M ↦ −SMS` as an involutive bijection. -/
def conjSEquiv : M2 ≃ M2 where
  toFun := conjS
  invFun := conjS
  left_inv M := by ext <;> simp [conjS]
  right_inv M := by ext <;> simp [conjS]

/-- `M ↦ −UMU²` as a bijection. -/
def conjUEquiv : M2 ≃ M2 where
  toFun := conjU
  invFun := conjUinv
  left_inv M := by ext <;> (simp [conjU, conjUinv]; try ring)
  right_inv M := by ext <;> (simp [conjU, conjUinv]; try ring)

/-! ### Reduced shape lemmas for the weights -/

lemma w3_shift (x y z k : ℤ) : w3 (x + k) (y + k) (z + k) = w3 x y z := by
  unfold w3
  have h1 : (x + k ≤ y + k ∧ y + k ≤ z + k) ↔ (x ≤ y ∧ y ≤ z) := by omega
  have h2 : x + k = y + k ↔ x = y := by omega
  have h3 : y + k = z + k ↔ y = z := by omega
  simp only [h1, h2, h3]

/-! ### The identities -/

/-- `Z = SXS + A₁` (PZ: `Z₁ = SXS`, `Z₂ = A₁`). -/
theorem regZ_eq (M : M2) : regZ M = regX (conjS M) + regA1 M := by
  obtain ⟨a, b, c, d⟩ := M
  simp only [conjS, regZ_mk, regX_mk, regA1_mk, w3, w4, wI]
  split_ifs <;> first | (exfalso; omega) | norm_num

/-- `U²ZU = Z₃ + T₂` (PZ: `U²ZU = Z₃ + Z₄`, `Z₄ = T₂`). -/
theorem regZ_conjU (M : M2) : regZ (conjU M) = regZ3 M + regT2 M := by
  obtain ⟨a, b, c, d⟩ := M
  simp only [conjU, regZ_mk, regZ3_mk, regT2_mk]
  have e : w3 (d - b - (a + b)) (-b) (-(a + b - c - d)) = w3 (-b) (a - d) c := by
    rw [← w3_shift (-b) (a - d) c (d - a - b)]; congr 1 <;> ring
  rw [e]
  simp only [w3]
  split_ifs <;> first | (exfalso; omega) | norm_num

/-- `X = B₁ + Z₃ + U²YU`. -/
theorem regX_eq (M : M2) : regX M = regB1 M + regZ3 M + regY (conjU M) := by
  obtain ⟨a, b, c, d⟩ := M
  simp only [conjU, regX_mk, regB1_mk, regZ3_mk, regY_mk]
  have e : w3 (d - b - (a + b)) (-(a + b - c - d)) (-b) = w3 (-b) c (a - d) := by
    rw [← w3_shift (-b) c (a - d) (d - a - b)]; congr 1 <;> ring
  rw [e]
  simp only [w3, w4, wI]
  split_ifs <;> first | (exfalso; omega) | norm_num

/-- `T₁ = Y + H`. -/
theorem regT1_eq (M : M2) : regT1 M = regY M + regH M := by
  obtain ⟨a, b, c, d⟩ := M
  simp only [regT1_mk, regY_mk, regH_mk]
  split_ifs <;> first | (exfalso; omega) | norm_num

lemma eW_split (x p q : ℤ) (hp : 0 < p) (hq : 0 < q) :
    eW x p q = w4 0 x q p + w4 0 x p q := by
  simp only [eW, w4]
  split_ifs <;> first | (exfalso; omega) | norm_num

lemma w4_eq_zero_of_lt {x y z u : ℤ} (h : u < z) : w4 x y z u = 0 := by
  unfold w4; rw [esIfNeg (by omega)]

/-- `E = A₁ + A₂ + B₁ + B₂` with `A₂ = T₃`, `B₂ = T₄` (fundamental domain split `F = F⁺ ∪ F⁻`). -/
theorem regE_eq (M : M2) : regE M = regA1 M + regT3 M + regB1 M + regT4 M := by
  obtain ⟨a, b, c, d⟩ := M
  simp only [regE_mk, regA1_mk, regT3_mk, regB1_mk, regT4_mk]
  by_cases hb : b < 0
  · by_cases hc : 0 < c
    · rw [eW_split _ _ _ (by omega) hc]
      by_cases ha : 0 < a <;> by_cases hd : 0 < d <;>
        simp (disch := omega) only [esIfPos, esIfNeg] <;> ring
    · rw [w4_eq_zero_of_lt (show c < -b by omega)]
      simp (disch := omega) only [esIfNeg]
      split_ifs <;> simp
  · simp (disch := omega) only [esIfNeg]
    by_cases hc : 0 < c
    · rw [w4_eq_zero_of_lt (show -b < c by omega)]
      split_ifs <;> simp
    · simp (disch := omega) only [esIfNeg]; simp

end RamanujanWeil.Arith.ES
