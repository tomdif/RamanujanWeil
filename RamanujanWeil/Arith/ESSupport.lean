import RamanujanWeil.Arith.ESRegions

/-!
# A2 / ES-P4b: support bounds for `T̃ₙ` and the PZ regions (docs/ARITH_ES_PLAN.md, §2 P4b)

Every matrix `M = [[a, b], [c, d]]` of determinant `n` in the support of one of the Popa–Zagier
regions `T₁, …, T₄, A₁, B₁, Z₃` (hence also `Y, H, E`) has `|a|, |b|, |c|, |d| ≤ n`.

* `ptC_support` : `ptC M ≠ 0 → det M = n → |a|, |b|, |c|, |d| ≤ n`. So the box truncation
  `Ttilde n` (entries in `[−n, n]`) is the full `T̃ₙ` of PZ (15).

The bounds come from writing `n = ad − bc` as a sum of non-negative products in each region.
-/

namespace RamanujanWeil.Arith.ES

open M2

/-- All four entries bounded by `K`. -/
def EntBd (K : ℤ) (M : M2) : Prop := |M.a| ≤ K ∧ |M.b| ≤ K ∧ |M.c| ≤ K ∧ |M.d| ≤ K

lemma w3_ne_zero {x y z : ℤ} (h : w3 x y z ≠ 0) : x ≤ y ∧ y ≤ z := by
  by_contra hc; apply h; unfold w3; rw [esIfNeg hc]

lemma w4_ne_zero {x y z u : ℤ} (h : w4 x y z u ≠ 0) : x ≤ y ∧ y ≤ z ∧ z ≤ u := by
  by_contra hc; apply h; unfold w4; rw [esIfNeg hc]

lemma bnd_T1 {a b c d n : ℤ} (hdet : a * d - b * c = n) (h1 : 0 ≤ c) (h2 : c < a)
    (h3 : a - d ≤ -b) (h4 : -b ≤ c) : EntBd n ⟨a, b, c, d⟩ := by
  simp only [EntBd]
  rcases le_or_gt b 0 with hb | hb
  · have hd : 1 ≤ d := by omega
    have e1 : a ≤ a * d := by nlinarith
    have e2 : d ≤ a * d := by nlinarith
    have e3 : 0 ≤ (-b) * c := by nlinarith
    refine ⟨abs_le.mpr ⟨?_, ?_⟩, abs_le.mpr ⟨?_, ?_⟩, abs_le.mpr ⟨?_, ?_⟩,
      abs_le.mpr ⟨?_, ?_⟩⟩ <;> nlinarith
  · have hd : a + b ≤ d := by omega
    have e1 : 0 ≤ (a - 1) * (d - b) := by nlinarith
    have e2 : 0 ≤ b * (a - 1 - c) := by nlinarith
    have e3 : d ≤ n := by nlinarith
    refine ⟨abs_le.mpr ⟨?_, ?_⟩, abs_le.mpr ⟨?_, ?_⟩, abs_le.mpr ⟨?_, ?_⟩,
      abs_le.mpr ⟨?_, ?_⟩⟩ <;> nlinarith

lemma bnd_T2 {a b c d n : ℤ} (hdet : a * d - b * c = n) (h1 : b < d) (h2 : d ≤ 0)
    (h3 : -b ≤ a - d) (h4 : a - d ≤ c) : EntBd n ⟨a, b, c, d⟩ := by
  simp only [EntBd]
  have e1 : 0 ≤ (c - a) * (-d) := by nlinarith
  have e2 : 0 ≤ c * (-b - 1 + d) := by nlinarith
  have e3 : c ≤ n := by nlinarith
  refine ⟨abs_le.mpr ⟨?_, ?_⟩, abs_le.mpr ⟨?_, ?_⟩, abs_le.mpr ⟨?_, ?_⟩,
    abs_le.mpr ⟨?_, ?_⟩⟩ <;> nlinarith

/-- `0 ≤ a − d ≤ q ≤ p` with `p = −b`, `q = c`, `a ≤ 0 < c` (`T₃`), or the symmetric `T₄` shape. -/
lemma bnd_nonpos {a b c d n : ℤ} (hdet : a * d - b * c = n) (ha : a ≤ 0) (hx : 0 ≤ a - d)
    (hc : 0 < c) (hb : 0 < -b) (hxc : a - d ≤ c) (hxb : a - d ≤ -b) :
    EntBd n ⟨a, b, c, d⟩ := by
  simp only [EntBd]
  have e0 : 0 ≤ a * d := by nlinarith
  have e1 : c ≤ (-b) * c := by nlinarith
  have e2 : -b ≤ (-b) * c := by nlinarith
  have e3 : -d ≤ n := by
    rcases eq_or_lt_of_le ha with h | h
    · subst h; nlinarith
    · nlinarith
  refine ⟨abs_le.mpr ⟨?_, ?_⟩, abs_le.mpr ⟨?_, ?_⟩, abs_le.mpr ⟨?_, ?_⟩,
    abs_le.mpr ⟨?_, ?_⟩⟩ <;> nlinarith

lemma bnd_T3 {a b c d n : ℤ} (hdet : a * d - b * c = n) (ha : a ≤ 0) (hc : 0 < c)
    (hw : 0 ≤ a - d ∧ a - d ≤ c ∧ c ≤ -b) : EntBd n ⟨a, b, c, d⟩ :=
  bnd_nonpos hdet ha hw.1 hc (by omega) hw.2.1 (by omega)

/-- `T₄`: `d ≤ 0 < −b`, `0 ≤ a − d ≤ −b ≤ c`. -/
lemma bnd_T4 {a b c d n : ℤ} (hdet : a * d - b * c = n) (hd : d ≤ 0) (hb : 0 < -b)
    (hw : 0 ≤ a - d ∧ a - d ≤ -b ∧ -b ≤ c) : EntBd n ⟨a, b, c, d⟩ := by
  rcases le_or_gt a 0 with ha | ha
  · exact bnd_nonpos hdet ha hw.1 (by omega) hb (by omega) hw.2.1
  · simp only [EntBd]
    have e1 : 0 ≤ (c - a) * (-d) := by nlinarith
    have e2 : 0 ≤ c * (-b - 1 + d) := by nlinarith
    have e3 : c ≤ n := by nlinarith
    refine ⟨abs_le.mpr ⟨?_, ?_⟩, abs_le.mpr ⟨?_, ?_⟩, abs_le.mpr ⟨?_, ?_⟩,
      abs_le.mpr ⟨?_, ?_⟩⟩ <;> nlinarith

/-- `A₁`: `0 < c`, `0 < a`, `0 ≤ a − d ≤ c ≤ −b`. -/
lemma bnd_A1 {a b c d n : ℤ} (hdet : a * d - b * c = n) (hc : 0 < c) (ha : 0 < a)
    (hw : 0 ≤ a - d ∧ a - d ≤ c ∧ c ≤ -b) : EntBd n ⟨a, b, c, d⟩ := by
  simp only [EntBd]
  rcases le_or_gt 0 d with hd | hd
  · have e0 : 0 ≤ a * d := by nlinarith
    have e1 : c ≤ (-b) * c := by nlinarith
    have e2 : -b ≤ (-b) * c := by nlinarith
    have e3 : a ≤ n := by
      rcases eq_or_lt_of_le hd with h | h
      · subst h; nlinarith
      · nlinarith
    refine ⟨abs_le.mpr ⟨?_, ?_⟩, abs_le.mpr ⟨?_, ?_⟩, abs_le.mpr ⟨?_, ?_⟩,
      abs_le.mpr ⟨?_, ?_⟩⟩ <;> nlinarith
  · have e1 : 0 ≤ (-b - a) * (-d) := by nlinarith
    have e2 : 0 ≤ (-b) * (c - 1 + d) := by nlinarith
    have e3 : -b ≤ n := by nlinarith
    refine ⟨abs_le.mpr ⟨?_, ?_⟩, abs_le.mpr ⟨?_, ?_⟩, abs_le.mpr ⟨?_, ?_⟩,
      abs_le.mpr ⟨?_, ?_⟩⟩ <;> nlinarith

/-- All-positive shape: `0 < d ≤ a`, `0 < −b`, `0 < c` (`B₁`, `Z₃`). -/
lemma bnd_pos {a b c d n : ℤ} (hdet : a * d - b * c = n) (hd : 0 < d) (hda : d ≤ a)
    (hb : 0 < -b) (hc : 0 < c) : EntBd n ⟨a, b, c, d⟩ := by
  simp only [EntBd]
  have e0 : a ≤ a * d := by nlinarith
  have e1 : c ≤ (-b) * c := by nlinarith
  have e2 : -b ≤ (-b) * c := by nlinarith
  refine ⟨abs_le.mpr ⟨?_, ?_⟩, abs_le.mpr ⟨?_, ?_⟩, abs_le.mpr ⟨?_, ?_⟩,
    abs_le.mpr ⟨?_, ?_⟩⟩ <;> nlinarith

/-! ### Support lemmas for the region functions -/

lemma regT1_bd {M : M2} {n : ℤ} (hdet : M.det = n) (h : regT1 M ≠ 0) : EntBd n M := by
  obtain ⟨a, b, c, d⟩ := M
  rw [regT1_mk] at h
  split_ifs at h with h0
  · have := w3_ne_zero h; exact bnd_T1 hdet h0.1 h0.2 this.1 this.2
  · exact absurd rfl h

lemma regT2_bd {M : M2} {n : ℤ} (hdet : M.det = n) (h : regT2 M ≠ 0) : EntBd n M := by
  obtain ⟨a, b, c, d⟩ := M
  rw [regT2_mk] at h
  split_ifs at h with h0
  · have := w3_ne_zero h; exact bnd_T2 hdet h0.1 h0.2 this.1 this.2
  · exact absurd rfl h

lemma regT3_bd {M : M2} {n : ℤ} (hdet : M.det = n) (h : regT3 M ≠ 0) : EntBd n M := by
  obtain ⟨a, b, c, d⟩ := M
  rw [regT3_mk] at h
  split_ifs at h with h0
  · exact bnd_T3 hdet h0.1 h0.2 (w4_ne_zero h)
  · exact absurd rfl h

lemma regT4_bd {M : M2} {n : ℤ} (hdet : M.det = n) (h : regT4 M ≠ 0) : EntBd n M := by
  obtain ⟨a, b, c, d⟩ := M
  rw [regT4_mk] at h
  split_ifs at h with h0
  · exact bnd_T4 hdet h0.1 h0.2 (w4_ne_zero h)
  · exact absurd rfl h

lemma regA1_bd {M : M2} {n : ℤ} (hdet : M.det = n) (h : regA1 M ≠ 0) : EntBd n M := by
  obtain ⟨a, b, c, d⟩ := M
  rw [regA1_mk] at h
  split_ifs at h with h0
  · exact bnd_A1 hdet h0.1 h0.2 (w4_ne_zero h)
  · exact absurd rfl h

lemma regB1_bd {M : M2} {n : ℤ} (hdet : M.det = n) (h : regB1 M ≠ 0) : EntBd n M := by
  obtain ⟨a, b, c, d⟩ := M
  rw [regB1_mk] at h
  split_ifs at h with h0
  · have := w4_ne_zero h
    exact bnd_pos hdet h0.2 (by omega) (by omega) (by omega)
  · exact absurd rfl h

lemma regZ3_bd {M : M2} {n : ℤ} (hdet : M.det = n) (h : regZ3 M ≠ 0) : EntBd n M := by
  obtain ⟨a, b, c, d⟩ := M
  rw [regZ3_mk] at h
  split_ifs at h with h0
  · have := w3_ne_zero h
    exact bnd_pos hdet h0.2 (by omega) (by omega) (by omega)
  · exact absurd rfl h

lemma regY_bd {M : M2} {n : ℤ} (hdet : M.det = n) (h : regY M ≠ 0) : EntBd n M := by
  refine regT1_bd hdet ?_
  obtain ⟨a, b, c, d⟩ := M
  rw [regY_mk] at h; rw [regT1_mk]
  split_ifs at h with h0
  · rwa [esIfPos ⟨h0.1.le, h0.2⟩]
  · exact absurd rfl h

lemma regH_bd {M : M2} {n : ℤ} (hdet : M.det = n) (h : regH M ≠ 0) : EntBd n M := by
  refine regT1_bd hdet ?_
  obtain ⟨a, b, c, d⟩ := M
  rw [regH_mk] at h; rw [regT1_mk]
  split_ifs at h with h0
  · rwa [esIfPos ⟨h0.1.ge, by omega⟩]
  · exact absurd rfl h

/-- **P4b.** The Popa–Zagier coefficient `ptC` is supported, in determinant `n`, on matrices
with all entries in `[−n, n]`. -/
theorem ptC_support {M : M2} {n : ℤ} (hdet : M.det = n) (h : ptC M ≠ 0) : EntBd n M := by
  rw [ptC_eq] at h
  by_cases h1 : regT1 M = 0
  · by_cases h2 : regT2 M = 0
    · by_cases h3 : regT3 M = 0
      · exact regT4_bd hdet (by intro h4; apply h; rw [h1, h2, h3, h4]; ring)
      · exact regT3_bd hdet h3
    · exact regT2_bd hdet h2
  · exact regT1_bd hdet h1

end RamanujanWeil.Arith.ES
