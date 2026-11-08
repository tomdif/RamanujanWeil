import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.Data.Int.Interval
import Mathlib.Data.Nat.Sqrt
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Tactic

/-!
# A1: Hurwitz class numbers — forms, the `SL₂(ℤ)` action, and the reduced-form count

* `QF`: integral binary quadratic forms `a x² + b x y + c y²`, `disc f = b² − 4ac`.
* `SL(2, ℤ)` acts on the left by `(γ • f)(x, y) = f((x, y) γ)`, i.e. for `γ = [[p, q], [r, s]]`
  `γ • f = (f(p, q), 2apr + b(ps + qr) + 2cqs, f(r, s))`.
* `Form N`: positive definite forms of discriminant `−N` (`disc = −N`, `a > 0`), an
  `SL(2, ℤ)`-set.
* `QF.IsReduced`: `|b| ≤ a ≤ c`, and `b ≥ 0` if `|b| = a` or `a = c`.
* `hurwitz N : ℚ`: `−1/12` for `N = 0`, otherwise `H6 N / 6` where `H6 N : ℕ` counts reduced forms
  of discriminant `−N` with weight `6` (`3` for `a(x² + y²)`, `2` for `a(x² + xy + y²)`).
  Computable; small values are checked by `decide`.
-/

namespace RamanujanWeil.Arith.Hurwitz

/-- An integral binary quadratic form `a x² + b x y + c y²`. -/
@[ext]
structure QF where
  a : ℤ
  b : ℤ
  c : ℤ
  deriving DecidableEq, Repr

namespace QF

/-- The discriminant `b² − 4ac`. -/
def disc (f : QF) : ℤ := f.b ^ 2 - 4 * f.a * f.c

/-- Evaluation `f(x, y)`. -/
def eval (f : QF) (x y : ℤ) : ℤ := f.a * x ^ 2 + f.b * x * y + f.c * y ^ 2

/-- The reduced forms: `−a < b ≤ a ≤ c`, and `b ≥ 0` if `a = c`. For `a > 0` this is the usual
`|b| ≤ a ≤ c`, `b ≥ 0` if `|b| = a` or `a = c` (`isReduced_iff`). -/
def IsReduced (f : QF) : Prop :=
  -f.a < f.b ∧ f.b ≤ f.a ∧ f.a ≤ f.c ∧ (f.a = f.c → 0 ≤ f.b)

lemma isReduced_iff {f : QF} (ha : 0 < f.a) :
    f.IsReduced ↔ |f.b| ≤ f.a ∧ f.a ≤ f.c ∧ (|f.b| = f.a ∨ f.a = f.c → 0 ≤ f.b) := by
  unfold IsReduced
  rcases le_or_gt 0 f.b with hb | hb
  · rw [abs_of_nonneg hb]
    constructor
    · rintro ⟨h1, h2, h3, h4⟩; exact ⟨h2, h3, fun _ => hb⟩
    · rintro ⟨h2, h3, h4⟩; exact ⟨by linarith, h2, h3, fun _ => hb⟩
  · rw [abs_of_neg hb]
    constructor
    · rintro ⟨h1, h2, h3, h4⟩
      refine ⟨by linarith, h3, ?_⟩
      rintro (h | h)
      · linarith
      · exact h4 h
    · rintro ⟨h2, h3, h4⟩
      refine ⟨?_, by linarith, h3, fun h => h4 (Or.inr h)⟩
      rcases lt_or_eq_of_le h2 with h | h
      · linarith
      · exact absurd (h4 (Or.inl h)) (not_le.mpr hb)

instance : DecidablePred IsReduced := fun f => by unfold IsReduced; infer_instance

/-- The action of a `2 × 2` integer matrix given by its entries `p q r s` (rows `(p,q)`,
`(r,s)`): `f ↦ f((x, y)·[[p, q], [r, s]])`. -/
def act (p q r s : ℤ) (f : QF) : QF :=
  ⟨f.eval p q, 2 * f.a * p * r + f.b * (p * s + q * r) + 2 * f.c * q * s, f.eval r s⟩

lemma disc_act (p q r s : ℤ) (f : QF) :
    (act p q r s f).disc = (p * s - q * r) ^ 2 * f.disc := by
  simp only [disc, act, eval]; ring

/-- `4a·f(x, y) = (2ax + by)² − disc·y²`. -/
lemma four_a_eval (f : QF) (x y : ℤ) :
    4 * f.a * f.eval x y = (2 * f.a * x + f.b * y) ^ 2 - f.disc * y ^ 2 := by
  simp only [eval, disc]; ring

lemma eval_pos {f : QF} (ha : 0 < f.a) (hd : f.disc < 0) {x y : ℤ} (hxy : x ≠ 0 ∨ y ≠ 0) :
    0 < f.eval x y := by
  have h4 := four_a_eval f x y
  rcases eq_or_ne y 0 with rfl | hy
  · have hx : x ≠ 0 := by simpa using hxy
    simp only [eval]; simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
      mul_zero, add_zero]
    positivity
  · have : 0 < y ^ 2 := by positivity
    have : 0 < 4 * f.a * f.eval x y := by nlinarith [sq_nonneg (2 * f.a * x + f.b * y)]
    by_contra h
    push Not at h
    nlinarith

end QF

open QF Matrix
open scoped MatrixGroups

/-- `SL(2, ℤ)` acts on forms by `(γ • f)(x, y) = f((x, y) γ)`. -/
instance : MulAction SL(2, ℤ) QF where
  smul γ f := act (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1) f
  one_smul f := by
    change act _ _ _ _ f = f
    simp [act, eval]
  mul_smul γ δ f := by
    change act _ _ _ _ f = act _ _ _ _ (act _ _ _ _ f)
    simp only [SpecialLinearGroup.coe_mul, mul_apply, Fin.sum_univ_two, act, eval]
    ext <;> simp only <;> ring

lemma smul_def (γ : SL(2, ℤ)) (f : QF) : γ • f = act (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1) f := rfl

lemma det_entries (γ : SL(2, ℤ)) : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
  have := γ.det_coe
  rwa [det_fin_two] at this

lemma disc_smul (γ : SL(2, ℤ)) (f : QF) : (γ • f).disc = f.disc := by
  rw [smul_def, disc_act, det_entries]; ring

/-- Positive definite: `disc < 0` and `a > 0`. -/
def IsPosDef (f : QF) : Prop := f.disc < 0 ∧ 0 < f.a

/-- Positive definite forms of discriminant `−N` (empty for `N = 0`). -/
def Form (N : ℕ) : Type := {f : QF // f.disc = -(N : ℤ) ∧ IsPosDef f}

instance (N : ℕ) : MulAction SL(2, ℤ) (Form N) where
  smul γ f := ⟨γ • f.1, by rw [disc_smul]; exact f.2.1, by rw [disc_smul]; exact f.2.2.1, by
    rw [smul_def]
    apply eval_pos f.2.2.2 f.2.2.1
    · by_contra h
      push Not at h
      have := det_entries γ
      rw [h.1, h.2] at this
      simp at this⟩
  one_smul f := Subtype.ext (one_smul _ f.1)
  mul_smul γ δ f := Subtype.ext (mul_smul γ δ f.1)

/-! ### The computable count over reduced forms -/

/-- The form `(a, b, (b² + N) / (4a))`. -/
def formOf (N : ℕ) (ab : ℤ × ℤ) : QF := ⟨ab.1, ab.2, (ab.2 ^ 2 + N) / (4 * ab.1)⟩

/-- Candidate pairs `(a, b)` of reduced forms of discriminant `−N`: `1 ≤ a ≤ √N`, `|b| ≤ a`,
`4a ∣ b² + N`, and `formOf N (a, b)` reduced. -/
def redPairs (N : ℕ) : Finset (ℤ × ℤ) :=
  ((Finset.Icc (1 : ℤ) (Nat.sqrt N)) ×ˢ (Finset.Icc (-(Nat.sqrt N : ℤ)) (Nat.sqrt N))).filter
    fun ab => (ab.2 ^ 2 + N) % (4 * ab.1) = 0 ∧ (formOf N ab).IsReduced

/-- Six times the weight of a reduced form: `3` for `a(x² + y²)`, `2` for `a(x² + xy + y²)`,
`6` otherwise. -/
def wt6 (f : QF) : ℕ :=
  if f.b = 0 ∧ f.a = f.c then 3 else if f.b = f.a ∧ f.a = f.c then 2 else 6

/-- `6 H(N)` for `N ≥ 1`, as a natural number. -/
def H6 (N : ℕ) : ℕ := ∑ ab ∈ redPairs N, wt6 (formOf N ab)

/-- **The Hurwitz class number** `H(N)`: `H(0) = −1/12`, and for `N ≥ 1` the number of reduced
positive definite forms of discriminant `−N`, those equivalent to `a(x² + y²)` resp.
`a(x² + xy + y²)` weighted by `1/2` resp. `1/3`. -/
def hurwitz (N : ℕ) : ℚ := if N = 0 then -1 / 12 else (H6 N : ℚ) / 6

end RamanujanWeil.Arith.Hurwitz
