import RamanujanWeil.Arith.HurwitzReduction

/-!
# A1: the Hurwitz class number as an orbit count

* `hurwitzOrbit N = Σ_{O ∈ SL₂(ℤ) \ Form N} 2 / #Stab(O)` (a `finsum` over the orbit space).
* `hurwitzClasses N = Σ_O w(O)`, `w(O) = 1/2` if `O ∋ a(x² + y²)`, `1/3` if `O ∋ a(x² + xy + y²)`,
  `1` otherwise — the textbook definition.
* `hurwitz_eq_hurwitzOrbit`, `hurwitz_eq_hurwitzClasses` (`N ≥ 1`): both equal the computable
  reduced-form count `hurwitz N`.
* `hurwitz_eq_zero_of_mod_four`: `H(N) = 0` for `N ≡ 1, 2 (mod 4)`.
* Sanity values (by `decide`) and the Kronecker–Hurwitz class number relation checked for
  `1 ≤ n ≤ 20` (numerical only, not a proof of the relation).
-/

namespace RamanujanWeil.Arith.Hurwitz

open QF Matrix MulAction
open scoped MatrixGroups

/-- The orbit space `SL₂(ℤ) \ {positive definite forms of discriminant −N}`. -/
abbrev Classes (N : ℕ) := orbitRel.Quotient SL(2, ℤ) (Form N)

/-- **Orbit-count definition**: `Σ_O 2 / #Stab_{SL₂(ℤ)}(O)`. -/
noncomputable def hurwitzOrbit (N : ℕ) : ℚ :=
  ∑ᶠ O : Classes N, (2 : ℚ) / Nat.card (stabilizer SL(2, ℤ) O.out)

open scoped Classical in
/-- The textbook class weight: `1/2` for the class of `a(x² + y²)`, `1/3` for the class of
`a(x² + xy + y²)`, `1` otherwise. -/
noncomputable def classWeight {N : ℕ} (O : Classes N) : ℚ :=
  if ∃ f : Form N, (Quotient.mk'' f : Classes N) = O ∧ f.1.b = 0 ∧ f.1.a = f.1.c then 1 / 2
  else if ∃ f : Form N, (Quotient.mk'' f : Classes N) = O ∧ f.1.b = f.1.a ∧ f.1.a = f.1.c then
    1 / 3
  else 1

/-- **Class-count definition**: `Σ_O w(O)`. -/
noncomputable def hurwitzClasses (N : ℕ) : ℚ := ∑ᶠ O : Classes N, classWeight O

/-- Reduced positive definite forms of discriminant `−N`. -/
def Red (N : ℕ) : Type := {f : Form N // f.1.IsReduced}

/-- A reduced form's class. -/
def toClass (N : ℕ) (f : Red N) : Classes N := Quotient.mk'' f.1

theorem toClass_bijective (N : ℕ) : Function.Bijective (toClass N) := by
  constructor
  · intro f g h
    have h' : f.1 ∈ orbit SL(2, ℤ) g.1 := Quotient.exact' h
    exact Subtype.ext (reduced_unique g.2 f.2 h').symm
  · intro O
    induction O using Quotient.inductionOn' with
    | h f =>
      obtain ⟨γ, hγ⟩ := exists_reduced f
      exact ⟨⟨γ • f, hγ⟩, Quotient.sound' (mem_orbit f γ)⟩

lemma card_stabilizer_out {N : ℕ} (f : Red N) :
    Nat.card (stabilizer SL(2, ℤ) (toClass N f).out) = Nat.card (stabilizer SL(2, ℤ) f.1) := by
  have h : (toClass N f).out ∈ orbit SL(2, ℤ) f.1 :=
    Quotient.exact' (Quotient.out_eq' (toClass N f))
  obtain ⟨γ, hγ⟩ := h
  rw [← hγ, card_stabilizer_smul]

lemma two_div_card_stabilizer {N : ℕ} (f : Red N) :
    (2 : ℚ) / Nat.card (stabilizer SL(2, ℤ) (toClass N f).out) = (wt6 f.1.1 : ℚ) / 6 := by
  rw [card_stabilizer_out, card_stabilizer_reduced f.1 f.2, wt6]
  split_ifs <;> norm_num

lemma isReduced_101 {a : ℤ} (ha : 0 < a) : QF.IsReduced ⟨a, 0, a⟩ :=
  ⟨by simp; omega, by simp; omega, le_rfl, fun _ => le_rfl⟩

lemma isReduced_111 {a : ℤ} (ha : 0 < a) : QF.IsReduced ⟨a, a, a⟩ :=
  ⟨by simp; omega, le_rfl, le_rfl, fun _ => ha.le⟩

lemma classWeight_toClass {N : ℕ} (f : Red N) : classWeight (toClass N f) = (wt6 f.1.1 : ℚ) / 6 := by
  -- a form of shape `a(x² + y²)` or `a(x² + xy + y²)` is reduced, hence equal to `f` if in its class
  have key : ∀ g : Form N, g.1.IsReduced →
      ((Quotient.mk'' g : Classes N) = toClass N f ↔ g = f.1) := by
    intro g hg
    constructor
    · intro h
      exact reduced_unique hg f.2 (Quotient.exact' h.symm)
    · rintro rfl; rfl
  have h1 : (∃ g : Form N, (Quotient.mk'' g : Classes N) = toClass N f ∧ g.1.b = 0 ∧
      g.1.a = g.1.c) ↔ f.1.1.b = 0 ∧ f.1.1.a = f.1.1.c := by
    constructor
    · rintro ⟨g, hg, hb, hac⟩
      have hred : g.1.IsReduced := by
        have : g.1 = ⟨g.1.a, 0, g.1.a⟩ := by ext <;> simp [hb, hac]
        rw [this]; exact isReduced_101 g.2.2.2
      rw [← (key g hred).1 hg]; exact ⟨hb, hac⟩
    · intro h; exact ⟨f.1, rfl, h⟩
  have h2 : (∃ g : Form N, (Quotient.mk'' g : Classes N) = toClass N f ∧ g.1.b = g.1.a ∧
      g.1.a = g.1.c) ↔ f.1.1.b = f.1.1.a ∧ f.1.1.a = f.1.1.c := by
    constructor
    · rintro ⟨g, hg, hb, hac⟩
      have hred : g.1.IsReduced := by
        have : g.1 = ⟨g.1.a, g.1.a, g.1.a⟩ := by ext <;> simp [hb, hac]
        rw [this]; exact isReduced_111 g.2.2.2
      rw [← (key g hred).1 hg]; exact ⟨hb, hac⟩
    · intro h; exact ⟨f.1, rfl, h⟩
  unfold classWeight
  rw [wt6]
  simp only [h1, h2]
  split_ifs <;> norm_num

lemma le_sqrt_of_mul_le {a : ℤ} {N : ℕ} (ha : 0 ≤ a) (h : a * a ≤ N) : a ≤ (Nat.sqrt N : ℤ) := by
  lift a to ℕ using ha
  exact_mod_cast Nat.le_sqrt.mpr (by exact_mod_cast h)

lemma formOf_disc {N : ℕ} {ab : ℤ × ℤ} (h : (ab.2 ^ 2 + N) % (4 * ab.1) = 0) :
    (formOf N ab).disc = -(N : ℤ) := by
  have := Int.mul_ediv_cancel' (Int.dvd_of_emod_eq_zero h)
  unfold disc formOf
  dsimp only
  linarith

lemma formOf_eq {N : ℕ} (f : Form N) : formOf N (f.1.a, f.1.b) = f.1 := by
  have hd := f.2.1
  have ha := f.2.2.2
  unfold disc at hd
  ext
  · rfl
  · rfl
  · show (f.1.b ^ 2 + N) / (4 * f.1.a) = f.1.c
    rw [show f.1.b ^ 2 + (N : ℤ) = 4 * f.1.a * f.1.c by linarith]
    exact Int.mul_ediv_cancel_left _ (by positivity)

/-- `redPairs N` parametrizes the reduced forms of discriminant `−N`. -/
def pairEquiv {N : ℕ} (hN : 0 < N) : {ab // ab ∈ redPairs N} ≃ Red N where
  toFun ab := ⟨⟨formOf N ab.1, by
      have h := (Finset.mem_filter.mp ab.2)
      refine ⟨formOf_disc h.2.1, ?_, ?_⟩
      · rw [formOf_disc h.2.1]; simp; exact_mod_cast hN
      · have := (Finset.mem_product.mp h.1).1
        rw [Finset.mem_Icc] at this
        exact this.1⟩, (Finset.mem_filter.mp ab.2).2.2⟩
  invFun f := ⟨(f.1.1.a, f.1.1.b), by
      have hd := f.1.2.1
      have ha := f.1.2.2.2
      have hr := f.2
      unfold disc at hd
      obtain ⟨h1, h2, h3, h4⟩ := hr
      have hN' : f.1.1.a * f.1.1.a ≤ N := by nlinarith
      have hs := le_sqrt_of_mul_le ha.le hN'
      simp only [redPairs, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
      refine ⟨⟨⟨by omega, hs⟩, by omega, by omega⟩, ?_, ?_⟩
      · rw [show f.1.1.b ^ 2 + (N : ℤ) = 4 * f.1.1.a * f.1.1.c by linarith]
        exact Int.mul_emod_right _ _
      · rw [formOf_eq f.1]; exact f.2⟩
  left_inv _ := rfl
  right_inv f := Subtype.ext (Subtype.ext (formOf_eq f.1))

/-- Any orbit-space sum whose weight on the class of a reduced form `f` is `wt6 f / 6`
equals `hurwitz N`. -/
theorem finsum_classes_eq_hurwitz {N : ℕ} (hN : 0 < N) (w : Classes N → ℚ)
    (hw : ∀ f : Red N, w (toClass N f) = (wt6 f.1.1 : ℚ) / 6) :
    ∑ᶠ O : Classes N, w O = hurwitz N := by
  rw [← finsum_comp_equiv (Equiv.ofBijective _ (toClass_bijective N))]
  simp only [Equiv.ofBijective_apply, hw]
  rw [← finsum_comp_equiv (pairEquiv hN), finsum_eq_sum_of_fintype]
  change ∑ i : {ab // ab ∈ redPairs N}, (wt6 (formOf N i.1) : ℚ) / 6 = _
  rw [Finset.sum_coe_sort (redPairs N) (fun ab => (wt6 (formOf N ab) : ℚ) / 6)]
  simp only [hurwitz, hN.ne', ↓reduceIte, H6]
  push_cast
  rw [Finset.sum_div]

/-- **Main theorem (A1).** For `N ≥ 1` the computable reduced-form count equals the orbit count
`Σ_{O} 2 / #Stab_{SL₂(ℤ)}(O)` over classes of positive definite forms of discriminant `−N`. -/
theorem hurwitz_eq_hurwitzOrbit {N : ℕ} (hN : 0 < N) : hurwitz N = hurwitzOrbit N :=
  (finsum_classes_eq_hurwitz hN _ two_div_card_stabilizer).symm

/-- **Main theorem (A1), textbook form.** For `N ≥ 1`, `hurwitz N` is the number of classes,
the classes of `a(x² + y²)` and `a(x² + xy + y²)` weighted `1/2` and `1/3`. -/
theorem hurwitz_eq_hurwitzClasses {N : ℕ} (hN : 0 < N) : hurwitz N = hurwitzClasses N :=
  (finsum_classes_eq_hurwitz hN _ classWeight_toClass).symm

theorem hurwitz_zero : hurwitz 0 = -1 / 12 := rfl

/-- `H(N) = 0` for `N ≡ 1, 2 (mod 4)` (no form has such a discriminant). -/
theorem hurwitz_eq_zero_of_mod_four {N : ℕ} (h : N % 4 = 1 ∨ N % 4 = 2) : hurwitz N = 0 := by
  have hN : N ≠ 0 := by omega
  have hempty : redPairs N = ∅ := by
    rw [Finset.eq_empty_iff_forall_notMem]
    rintro ⟨a, b⟩ hab
    have hmod := (Finset.mem_filter.mp hab).2.1
    dsimp only at hmod
    have h4 : (b ^ 2 + (N : ℤ)) % 4 = 0 := by
      have := Int.emod_emod_of_dvd (b ^ 2 + (N : ℤ)) (Dvd.intro a rfl : (4 : ℤ) ∣ 4 * a)
      rw [hmod] at this
      simpa using this.symm
    rcases Int.even_or_odd' b with ⟨k, rfl | rfl⟩
    · have : (2 * k) ^ 2 = 4 * (k * k) := by ring
      rw [this] at h4; omega
    · have : (2 * k + 1) ^ 2 = 4 * (k * k + k) + 1 := by ring
      rw [this] at h4; omega
  simp only [hurwitz, hN, ↓reduceIte, H6, hempty]
  simp

/-! ### Sanity values -/

theorem H6_values :
    H6 3 = 2 ∧ H6 4 = 3 ∧ H6 7 = 6 ∧ H6 8 = 6 ∧ H6 11 = 6 ∧ H6 12 = 8 ∧ H6 15 = 12 ∧
      H6 16 = 9 ∧ H6 20 = 12 ∧ H6 23 = 18 := by
  decide +kernel

/-- `H(3) = 1/3, H(4) = 1/2, H(7) = 1, H(8) = 1, H(11) = 1, H(12) = 4/3, H(15) = 2,
H(16) = 3/2, H(20) = 2, H(23) = 3`. -/
theorem hurwitz_values :
    hurwitz 3 = 1 / 3 ∧ hurwitz 4 = 1 / 2 ∧ hurwitz 7 = 1 ∧ hurwitz 8 = 1 ∧ hurwitz 11 = 1 ∧
      hurwitz 12 = 4 / 3 ∧ hurwitz 15 = 2 ∧ hurwitz 16 = 3 / 2 ∧ hurwitz 20 = 2 ∧
        hurwitz 23 = 3 := by
  obtain ⟨h3, h4, h7, h8, h11, h12, h15, h16, h20, h23⟩ := H6_values
  simp only [hurwitz, h3, h4, h7, h8, h11, h12, h15, h16, h20, h23]
  norm_num

/-! ### Kronecker–Hurwitz relation: numerical check for `n ≤ 20` (not a proof)

`Σ_{t ∈ ℤ, t² ≤ 4n} H(4n − t²) = 2σ(n) − Σ_{d ∣ n} min(d, n/d)`, multiplied by `12` to stay in `ℤ`
(`12 H(m) = 2·H6(m)` for `m ≥ 1`, `12 H(0) = −1`). -/

/-- `12 · Σ_{t² ≤ 4n} H(4n − t²)`, computed through `H6`. -/
def khLHS12 (n : ℕ) : ℤ :=
  ∑ t ∈ (Finset.Icc (-(2 * n : ℤ)) (2 * n)).filter (fun t => t ^ 2 ≤ 4 * (n : ℤ)),
    if t ^ 2 = 4 * (n : ℤ) then -1 else 2 * (H6 (4 * (n : ℤ) - t ^ 2).toNat : ℤ)

/-- `12 · (2σ(n) − Σ_{d ∣ n} min(d, n/d))`. -/
def khRHS12 (n : ℕ) : ℤ :=
  12 * (2 * (∑ d ∈ n.divisors, (d : ℤ)) - ∑ d ∈ n.divisors, (min d (n / d) : ℤ))

lemma khLHS12_eq (n : ℕ) :
    (khLHS12 n : ℚ) = 12 * ∑ t ∈ (Finset.Icc (-(2 * n : ℤ)) (2 * n)).filter
      (fun t => t ^ 2 ≤ 4 * (n : ℤ)), hurwitz (4 * (n : ℤ) - t ^ 2).toNat := by
  unfold khLHS12
  push_cast
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun t ht => ?_
  rw [Finset.mem_filter] at ht
  split_ifs with h
  · have h0 : (4 * (n : ℤ) - t ^ 2).toNat = 0 := by omega
    rw [h0, hurwitz_zero]; norm_num
  · have hne : (4 * (n : ℤ) - t ^ 2).toNat ≠ 0 := by omega
    simp only [hurwitz, hne, ↓reduceIte]; ring

/-- The Kronecker–Hurwitz relation holds for `1 ≤ n ≤ 20` (checked by the kernel). -/
theorem kronecker_hurwitz_check : ∀ n ∈ Finset.Icc 1 20, khLHS12 n = khRHS12 n := by
  decide +kernel

end RamanujanWeil.Arith.Hurwitz
