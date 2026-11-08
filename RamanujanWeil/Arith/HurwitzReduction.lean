import RamanujanWeil.Arith.HurwitzBasic

/-!
# A1: reduction theory for positive definite binary quadratic forms

* `exists_reduced`: every positive definite form is `SL₂(ℤ)`-equivalent to a reduced one.
* `entries_bound`: if `f` and `γ • f` are both reduced then all entries of `γ` lie in `{−1, 0, 1}`.
* `reduced_cases`: the resulting finite check (81 matrices, `omega`).
* `reduced_unique`: two equivalent reduced forms are equal.
* `card_stabilizer_reduced`: `#Stab(f) = 4` for `a(x² + y²)`, `6` for `a(x² + xy + y²)`, `2` else.
-/

namespace RamanujanWeil.Arith.Hurwitz

open QF Matrix MulAction
open scoped MatrixGroups

/-- An element of `SL(2, ℤ)` from its entries. -/
def mkSL (p q r s : ℤ) (h : p * s - q * r = 1) : SL(2, ℤ) :=
  ⟨!![p, q; r, s], by rw [det_fin_two_of]; exact h⟩

@[simp] lemma mkSL_smul (p q r s : ℤ) (h : p * s - q * r = 1) (f : QF) :
    mkSL p q r s h • f = act p q r s f := rfl

lemma form_smul_val {N : ℕ} (γ : SL(2, ℤ)) (f : Form N) : (γ • f).1 = γ • f.1 := rfl

lemma c_pos {f : QF} (hf : IsPosDef f) : 0 < f.c := by
  obtain ⟨hd, ha⟩ := hf
  unfold disc at hd
  by_contra h
  push Not at h
  nlinarith [sq_nonneg f.b, mul_nonneg ha.le (neg_nonneg.mpr h)]

/-! ### Existence of a reduced representative -/

lemma exists_reduced_aux (N : ℕ) :
    ∀ n : ℕ, ∀ f : Form N, f.1.a.toNat = n → ∃ γ : SL(2, ℤ), (γ • f).1.IsReduced := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro f hn
  have ha : 0 < f.1.a := f.2.2.2
  set k := (f.1.a - f.1.b) / (2 * f.1.a) with hk
  let T : SL(2, ℤ) := mkSL 1 0 k 1 (by ring)
  have ha1 : (T • f).1.a = f.1.a := by
    rw [form_smul_val]; simp [T, act, eval]
  have hb1 : (T • f).1.b = f.1.b + 2 * f.1.a * k := by
    rw [form_smul_val]; simp [T, act]; ring
  have hmod := Int.mul_ediv_add_emod (f.1.a - f.1.b) (2 * f.1.a)
  have hlo := Int.emod_nonneg (f.1.a - f.1.b) (by positivity : (2 * f.1.a) ≠ 0)
  have hhi := Int.emod_lt_of_pos (f.1.a - f.1.b) (by positivity : 0 < 2 * f.1.a)
  rw [← hk] at hmod
  have hb1lo : -(T • f).1.a < (T • f).1.b := by rw [ha1, hb1]; linarith
  have hb1hi : (T • f).1.b ≤ (T • f).1.a := by rw [ha1, hb1]; linarith
  set g := T • f with hg
  let S : SL(2, ℤ) := mkSL 0 1 (-1) 0 (by ring)
  have hS : (S • g).1 = ⟨g.1.c, -g.1.b, g.1.a⟩ := by
    rw [form_smul_val]; simp [S, act, eval]
  have hgc : 0 < g.1.c := c_pos g.2.2
  rcases lt_or_ge g.1.c g.1.a with hlt | hle
  · obtain ⟨γ, hγ⟩ := ih (S • g).1.a.toNat (by rw [hS]; dsimp only; omega) (S • g) rfl
    exact ⟨γ * S * T, by rwa [mul_smul, mul_smul]⟩
  · by_cases hcase : g.1.a = g.1.c ∧ g.1.b < 0
    · refine ⟨S * T, ?_⟩
      rw [mul_smul, ← hg, hS]
      refine ⟨?_, ?_, ?_, ?_⟩ <;> dsimp only <;> omega
    · exact ⟨T, by rw [← hg]; refine ⟨?_, ?_, ?_, ?_⟩ <;> omega⟩

/-- **Existence.** Every positive definite form is equivalent to a reduced form. -/
theorem exists_reduced {N : ℕ} (f : Form N) : ∃ γ : SL(2, ℤ), (γ • f).1.IsReduced :=
  exists_reduced_aux N _ f rfl

/-! ### Bounds for reduced forms -/

lemma eval_ge {f : QF} (hred : f.IsReduced) (x y : ℤ) :
    f.a * |x| ^ 2 - f.a * (|x| * |y|) + f.c * |y| ^ 2 ≤ f.eval x y := by
  have hb : |f.b| ≤ f.a := abs_le.mpr ⟨by linarith [hred.1], hred.2.1⟩
  have h1 : -(|f.b| * (|x| * |y|)) ≤ f.b * x * y := by
    have := neg_abs_le (f.b * x * y)
    rw [abs_mul, abs_mul] at this
    linarith [mul_assoc |f.b| |x| |y|]
  have h2 : |f.b| * (|x| * |y|) ≤ f.a * (|x| * |y|) :=
    mul_le_mul_of_nonneg_right hb (by positivity)
  unfold eval
  rw [← sq_abs x, ← sq_abs y]
  linarith

lemma quad_ge_one {X Y : ℤ} (hX : 0 ≤ X) (hY : 0 ≤ Y) (h : X ≠ 0 ∨ Y ≠ 0) :
    1 ≤ X ^ 2 - X * Y + Y ^ 2 := by
  rcases eq_or_ne X 0 with rfl | hX0
  · have : Y ≠ 0 := by simpa using h
    have : 1 ≤ Y := by omega
    nlinarith
  rcases eq_or_ne Y 0 with rfl | hY0
  · have : 1 ≤ X := by omega
    nlinarith
  · have : 1 ≤ X := by omega
    have : 1 ≤ Y := by omega
    nlinarith [sq_nonneg (X - Y)]

lemma quad_ge_three {X Y : ℤ} (hX : 0 ≤ X) (hY : 0 ≤ Y) (h : 2 ≤ X ∨ 2 ≤ Y) :
    3 ≤ X ^ 2 - X * Y + Y ^ 2 := by
  rcases h with h | h
  · nlinarith [sq_nonneg (2 * Y - X)]
  · nlinarith [sq_nonneg (2 * X - Y)]

/-- A reduced form takes no value below `a` at a nonzero vector. -/
lemma a_le_eval {f : QF} (hred : f.IsReduced) (ha : 0 < f.a) {x y : ℤ} (hxy : x ≠ 0 ∨ y ≠ 0) :
    f.a ≤ f.eval x y := by
  have he := eval_ge hred x y
  have hq := quad_ge_one (abs_nonneg x) (abs_nonneg y) (by simpa using hxy)
  have h3 : f.a * 1 ≤ f.a * (|x| ^ 2 - |x| * |y| + |y| ^ 2) :=
    mul_le_mul_of_nonneg_left hq ha.le
  have h4 : 0 ≤ (f.c - f.a) * |y| ^ 2 :=
    mul_nonneg (by linarith [hred.2.2.1]) (by positivity)
  nlinarith

/-- If a reduced form takes the value `a` at `(x, y)`, then `|x|, |y| ≤ 1`. -/
lemma abs_le_one_of_eval_eq {f : QF} (hred : f.IsReduced) (ha : 0 < f.a) {x y : ℤ}
    (h : f.eval x y = f.a) : |x| ≤ 1 ∧ |y| ≤ 1 := by
  by_contra hc
  rw [not_and_or, not_le, not_le] at hc
  have he := eval_ge hred x y
  have hq := quad_ge_three (abs_nonneg x) (abs_nonneg y) (by omega)
  have h3 : f.a * 3 ≤ f.a * (|x| ^ 2 - |x| * |y| + |y| ^ 2) :=
    mul_le_mul_of_nonneg_left hq ha.le
  have h4 : 0 ≤ (f.c - f.a) * |y| ^ 2 :=
    mul_nonneg (by linarith [hred.2.2.1]) (by positivity)
  nlinarith

/-- Away from `|y| ≤ 1`, `|x| ≤ 1` (or `y = 0`), a reduced form exceeds `c + a/4`. -/
lemma lt_four_a_eval {f : QF} (hred : f.IsReduced) (ha : 0 < f.a) {x y : ℤ}
    (h : 2 ≤ |y| ∨ (2 ≤ |x| ∧ 1 ≤ |y|)) :
    4 * f.a * f.c + f.a ^ 2 < 4 * f.a * f.eval x y := by
  have he := eval_ge hred x y
  have hac : f.a ≤ f.c := hred.2.2.1
  have hac' : f.a * f.a ≤ f.a * f.c := mul_le_mul_of_nonneg_left hac ha.le
  rcases h with h | ⟨hx, hy⟩
  · have hY : 4 ≤ |y| ^ 2 := by nlinarith
    have h1 : (4 * f.c - f.a) * 4 ≤ (4 * f.c - f.a) * |y| ^ 2 :=
      mul_le_mul_of_nonneg_left hY (by linarith)
    have h2 : 16 * f.c - 4 * f.a ≤ 4 * f.eval x y := by
      nlinarith [mul_nonneg ha.le (sq_nonneg (2 * |x| - |y|))]
    have h3 : f.a * (16 * f.c - 4 * f.a) ≤ f.a * (4 * f.eval x y) :=
      mul_le_mul_of_nonneg_left h2 ha.le
    nlinarith
  · have hq := quad_ge_three (abs_nonneg x) (abs_nonneg y) (Or.inl hx)
    have h3 : f.a * 3 ≤ f.a * (|x| ^ 2 - |x| * |y| + |y| ^ 2) :=
      mul_le_mul_of_nonneg_left hq ha.le
    have hY : 1 ≤ |y| ^ 2 := by nlinarith
    have h4 : (f.c - f.a) * 1 ≤ (f.c - f.a) * |y| ^ 2 :=
      mul_le_mul_of_nonneg_left hY (by linarith)
    have h5 : f.c + 2 * f.a ≤ f.eval x y := by nlinarith
    have h6 : f.a * (f.c + 2 * f.a) ≤ f.a * f.eval x y := mul_le_mul_of_nonneg_left h5 ha.le
    nlinarith

lemma smul_a (γ : SL(2, ℤ)) (f : QF) : (γ • f).a = f.eval (γ 0 0) (γ 0 1) := rfl
lemma smul_c (γ : SL(2, ℤ)) (f : QF) : (γ • f).c = f.eval (γ 1 0) (γ 1 1) := rfl

lemma row0_ne_zero (γ : SL(2, ℤ)) : γ 0 0 ≠ 0 ∨ γ 0 1 ≠ 0 := by
  by_contra h
  push Not at h
  have := det_entries γ
  rw [h.1, h.2] at this
  simp at this

lemma a_le_smul_a {f : QF} (hred : f.IsReduced) (ha : 0 < f.a) (γ : SL(2, ℤ)) :
    f.a ≤ (γ • f).a := by
  rw [smul_a]; exact a_le_eval hred ha (row0_ne_zero γ)

/-- **Entry bound.** If `f` and `γ • f` are both reduced (and positive definite), every entry of
`γ` lies in `{−1, 0, 1}`. -/
theorem entries_bound {N : ℕ} (f : Form N) (hf : f.1.IsReduced) (γ : SL(2, ℤ))
    (hg : (γ • f).1.IsReduced) :
    |γ 0 0| ≤ 1 ∧ |γ 0 1| ≤ 1 ∧ |γ 1 0| ≤ 1 ∧ |γ 1 1| ≤ 1 := by
  have ha : 0 < f.1.a := f.2.2.2
  have hga : 0 < (γ • f).1.a := (γ • f).2.2.2
  have h1 : f.1.a ≤ (γ • f).1.a := a_le_smul_a hf ha γ
  have h2 : (γ • f).1.a ≤ f.1.a := by
    have := a_le_smul_a hg hga γ⁻¹
    rwa [← form_smul_val, inv_smul_smul] at this
  have heq : (γ • f).1.a = f.1.a := le_antisymm h2 h1
  have hrow0 := abs_le_one_of_eval_eq hf ha (by rw [← smul_a, ← form_smul_val, heq])
  -- second row
  have hdisc : (γ • f).1.disc = f.1.disc := by rw [form_smul_val, disc_smul]
  unfold disc at hdisc
  rw [heq] at hdisc
  have hgb : (γ • f).1.b ^ 2 ≤ f.1.a ^ 2 := by
    have : |(γ • f).1.b| ≤ (γ • f).1.a := abs_le.mpr ⟨by linarith [hg.1], hg.2.1⟩
    rw [heq] at this
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) this 2
  have hfb : 0 ≤ f.1.b ^ 2 := sq_nonneg _
  have hc : 4 * f.1.a * (γ • f).1.c ≤ 4 * f.1.a * f.1.c + f.1.a ^ 2 := by linarith
  rw [form_smul_val, smul_c] at hc
  have hnot : ¬ (2 ≤ |γ 1 1| ∨ (2 ≤ |γ 1 0| ∧ 1 ≤ |γ 1 1|)) := fun h =>
    absurd hc (not_le.mpr (lt_four_a_eval hf ha h))
  refine ⟨hrow0.1, hrow0.2, ?_, ?_⟩
  · rcases eq_or_ne (γ 1 1) 0 with h0 | h0
    · have hd := det_entries γ
      rw [h0] at hd
      have : |γ 0 1| * |γ 1 0| = 1 := by
        rw [← abs_mul]; rw [show γ 0 1 * γ 1 0 = -1 by linarith]; simp
      have h01 : 1 ≤ |γ 0 1| := by
        by_contra hh; push Not at hh
        have : |γ 0 1| = 0 := by have := abs_nonneg (γ 0 1); omega
        simp_all
      nlinarith [abs_nonneg (γ 1 0)]
    · have : 1 ≤ |γ 1 1| := by have := abs_pos.mpr h0; omega
      omega
  · omega

/-- **The finite check.** For `f = (a, b, c)` reduced and `γ` with entries in `{−1, 0, 1}`,
if `γ • f` is reduced then `γ • f = f`, and `γ = ±1` unless `f` is `a(x² + y²)` or
`a(x² + xy + y²)`. -/
theorem reduced_cases (a b c p q r s : ℤ) (_ha : 0 < a) (hf : QF.IsReduced ⟨a, b, c⟩)
    (hp : |p| ≤ 1) (hq : |q| ≤ 1) (hr : |r| ≤ 1) (hs : |s| ≤ 1) (hdet : p * s - q * r = 1)
    (hg : (act p q r s ⟨a, b, c⟩).IsReduced) :
    act p q r s ⟨a, b, c⟩ = ⟨a, b, c⟩ ∧
      ((p = 1 ∧ q = 0 ∧ r = 0 ∧ s = 1) ∨ (p = -1 ∧ q = 0 ∧ r = 0 ∧ s = -1) ∨
        (b = 0 ∧ a = c) ∨ (b = a ∧ a = c)) := by
  rw [abs_le] at hp hq hr hs
  obtain ⟨hp1, hp2⟩ := hp
  obtain ⟨hq1, hq2⟩ := hq
  obtain ⟨hr1, hr2⟩ := hr
  obtain ⟨hs1, hs2⟩ := hs
  unfold QF.IsReduced at hf hg
  dsimp only at hf
  simp only [act, eval, QF.mk.injEq] at hg ⊢
  interval_cases p <;> interval_cases q <;> interval_cases r <;> interval_cases s <;>
    (try norm_num at hdet) <;> (try norm_num at hg ⊢) <;> omega

/-- **Uniqueness.** Two equivalent reduced forms are equal. -/
theorem reduced_unique {N : ℕ} {f g : Form N} (hf : f.1.IsReduced) (hg : g.1.IsReduced)
    (h : g ∈ orbit SL(2, ℤ) f) : f = g := by
  obtain ⟨γ, rfl⟩ := h
  have hb := entries_bound f hf γ hg
  obtain ⟨⟨a, b, c⟩, hd, hpd⟩ := f
  have := (reduced_cases a b c _ _ _ _ hpd.2 hf hb.1 hb.2.1 hb.2.2.1 hb.2.2.2 (det_entries γ)
    hg).1
  exact Subtype.ext this.symm

/-! ### Stabilizers -/

/-- The entries of `γ ∈ SL(2, ℤ)`. -/
def tup (γ : SL(2, ℤ)) : ℤ × ℤ × ℤ × ℤ := (γ 0 0, γ 0 1, γ 1 0, γ 1 1)

lemma tup_injective : Function.Injective tup := by
  intro γ δ h
  simp only [tup, Prod.mk.injEq] at h
  ext i j
  fin_cases i <;> fin_cases j
  exacts [h.1, h.2.1, h.2.2.1, h.2.2.2]

/-- The candidate stabilizer: `t ∈ {−1,0,1}⁴` with `det t = 1` and `t • f = f`. -/
def stabSet (f : QF) : Finset (ℤ × ℤ × ℤ × ℤ) :=
  (Finset.Icc (-1 : ℤ) 1 ×ˢ Finset.Icc (-1 : ℤ) 1 ×ˢ Finset.Icc (-1 : ℤ) 1 ×ˢ
    Finset.Icc (-1 : ℤ) 1).filter
    fun t => t.1 * t.2.2.2 - t.2.1 * t.2.2.1 = 1 ∧ act t.1 t.2.1 t.2.2.1 t.2.2.2 f = f

lemma card_stabilizer_eq_stabSet {N : ℕ} (f : Form N) (hf : f.1.IsReduced) :
    Nat.card (stabilizer SL(2, ℤ) f) = (stabSet f.1).card := by
  have hinj : Function.Injective (fun γ : stabilizer SL(2, ℤ) f => tup γ.1) :=
    fun x y h => Subtype.ext (tup_injective h)
  rw [← Nat.card_range_of_injective hinj, Nat.card_coe_set_eq, ← Set.ncard_coe_finset]
  · congr 1
    ext t
    simp only [Set.mem_range, Subtype.exists, mem_stabilizer_iff, Finset.coe_filter,
      Set.mem_ofPred_eq, stabSet, Finset.mem_product, Finset.mem_Icc]
    constructor
    · rintro ⟨γ, hγ, rfl⟩
      have hγ' : (γ • f).1.IsReduced := by rw [hγ]; exact hf
      have hb := entries_bound f hf γ hγ'
      simp only [abs_le] at hb
      refine ⟨⟨hb.1, hb.2.1, hb.2.2.1, hb.2.2.2⟩, det_entries γ, ?_⟩
      have := congrArg Subtype.val hγ
      rw [form_smul_val, smul_def] at this
      exact this
    · rintro ⟨-, hdet, hact⟩
      refine ⟨mkSL _ _ _ _ hdet, Subtype.ext ?_, rfl⟩
      rw [form_smul_val, mkSL_smul]
      exact hact

lemma act_smul_form (p q r s k : ℤ) (f : QF) :
    act p q r s ⟨k * f.a, k * f.b, k * f.c⟩ =
      ⟨k * (act p q r s f).a, k * (act p q r s f).b, k * (act p q r s f).c⟩ := by
  simp only [act, eval, QF.mk.injEq]; refine ⟨?_, ?_, ?_⟩ <;> ring

lemma stabSet_scale (f : QF) {k : ℤ} (hk : k ≠ 0) :
    stabSet ⟨k * f.a, k * f.b, k * f.c⟩ = stabSet f := by
  unfold stabSet
  refine Finset.filter_congr fun t _ => ?_
  rw [act_smul_form]
  simp only [QF.mk.injEq, mul_right_inj' hk]
  constructor
  · rintro ⟨h1, h2, h3, h4⟩; exact ⟨h1, QF.ext h2 h3 h4⟩
  · rintro ⟨h1, h⟩; rw [h]; exact ⟨h1, rfl, rfl, rfl⟩

lemma stabSet_card_101 : (stabSet ⟨1, 0, 1⟩).card = 4 := by decide +kernel
lemma stabSet_card_111 : (stabSet ⟨1, 1, 1⟩).card = 6 := by decide +kernel

lemma stabSet_card {f : QF} (ha : 0 < f.a) (hf : f.IsReduced) :
    (stabSet f).card =
      if f.b = 0 ∧ f.a = f.c then 4 else if f.b = f.a ∧ f.a = f.c then 6 else 2 := by
  obtain ⟨a, b, c⟩ := f
  dsimp only at ha ⊢
  split_ifs with h1 h2
  · obtain ⟨rfl, rfl⟩ := h1
    rw [← stabSet_card_101, ← stabSet_scale ⟨1, 0, 1⟩ ha.ne']
    simp
  · obtain ⟨rfl, rfl⟩ := h2
    rw [← stabSet_card_111, ← stabSet_scale ⟨1, 1, 1⟩ ha.ne']
    simp
  · have : stabSet ⟨a, b, c⟩ = {(1, 0, 0, 1), (-1, 0, 0, -1)} := by
      ext ⟨p, q, r, s⟩
      simp only [stabSet, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc,
        Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]
      constructor
      · rintro ⟨⟨hp, hq, hr, hs⟩, hdet, hact⟩
        have hg : QF.IsReduced (act p q r s ⟨a, b, c⟩) := by rw [hact]; exact hf
        have := (reduced_cases a b c p q r s ha hf (abs_le.mpr hp) (abs_le.mpr hq)
          (abs_le.mpr hr) (abs_le.mpr hs) hdet hg).2
        rcases this with h | h | h | h
        · exact Or.inl h
        · exact Or.inr h
        · exact absurd h h1
        · exact absurd h h2
      · rintro (⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩) <;>
          refine ⟨by norm_num, by norm_num, ?_⟩ <;> simp [act, eval]
    rw [this]
    decide

/-- **Stabilizer orders.** For a reduced positive definite form `f = (a, b, c)`, `#Stab(f)` is
`4` if `f = a(x² + y²)`, `6` if `f = a(x² + xy + y²)`, and `2` otherwise. -/
theorem card_stabilizer_reduced {N : ℕ} (f : Form N) (hf : f.1.IsReduced) :
    Nat.card (stabilizer SL(2, ℤ) f) =
      if f.1.b = 0 ∧ f.1.a = f.1.c then 4 else if f.1.b = f.1.a ∧ f.1.a = f.1.c then 6 else 2 := by
  rw [card_stabilizer_eq_stabSet f hf, stabSet_card f.2.2.2 hf]

lemma card_stabilizer_smul {N : ℕ} (γ : SL(2, ℤ)) (f : Form N) :
    Nat.card (stabilizer SL(2, ℤ) (γ • f)) = Nat.card (stabilizer SL(2, ℤ) f) := by
  rw [stabilizer_smul_eq_stabilizer_map_conj]
  exact Subgroup.card_map_of_injective (MulAut.conj γ).injective

end RamanujanWeil.Arith.Hurwitz
