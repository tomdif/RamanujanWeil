import Mathlib
import RamanujanWeil.Ihara.IharaStatement

/-!
# The trace of Frobenius modulo `p` and the Hasse invariant

For a Weierstrass tuple `c ∈ 𝔽_q⁵` (`q = pⁿ`) with `Δ ≠ 0` and `a = traceOfFrob (wc c)`:

* `p` odd: `(a : 𝔽_q) = coeff_{x^{q−1}} f^{(q−1)/2}` with `f = 4x³ + b₂x² + 2b₄x + b₆`
  (`traceOfFrob_cast_odd`), and this coefficient factors as
  `A_{pᵏ⁺¹} = A_{pᵏ} · A_p^{pᵏ}` (`coeff_hassePow_succ`), so `p ∣ a ⟺ hasseInv p c = 0`;
* `p = 2`: `p ∣ a ⟺ a₁ = 0`, by the involution `P ↦ −P` on affine points (its fixed points are
  the `x` with `a₁x + a₃ = 0`, each with exactly one `y`).

Everything is elementary: point count = `1 + #{(x,y) : Equation}`, Euler's criterion
(`quadraticChar_card_sqrts`), and `Σ_{x ∈ 𝔽_q} xⁱ`.
-/

open Finset Polynomial

namespace RamanujanWeil.ArithPlan

open RamanujanWeil.Ihara

/-- The Hasse invariant of `wc c` (p odd): coefficient of `x^{p−1}` in `f^{(p−1)/2}`,
`f = 4x³ + b₂x² + 2b₄x + b₆` (verbatim from `scratch/ArithInterfaces.lean`). -/
noncomputable def hasseInv {F : Type*} [CommRing F] (p : ℕ) (c : Fin 5 → F) : F :=
  ((4 * Polynomial.X ^ 3 + Polynomial.C (wc c).b₂ * Polynomial.X ^ 2 +
      Polynomial.C (2 * (wc c).b₄) * Polynomial.X + Polynomial.C (wc c).b₆) ^ ((p - 1) / 2)).coeff
    (p - 1)

/-- The cubic `f = 4x³ + b₂x² + 2b₄x + b₆` of `wc c`. -/
noncomputable def hasseCubic {F : Type*} [CommRing F] (c : Fin 5 → F) : F[X] :=
  4 * X ^ 3 + C (wc c).b₂ * X ^ 2 + C (2 * (wc c).b₄) * X + C (wc c).b₆

lemma hasseInv_eq {F : Type*} [CommRing F] (p : ℕ) (c : Fin 5 → F) :
    hasseInv p c = (hasseCubic c ^ ((p - 1) / 2)).coeff (p - 1) := rfl

lemma natDegree_hasseCubic {F : Type*} [CommRing F] (c : Fin 5 → F) :
    (hasseCubic c).natDegree ≤ 3 := by
  unfold hasseCubic; compute_degree

/-! ## Multiplicativity of the Hasse coefficient -/

section Mult

variable {R : Type*} [CommRing R] {p : ℕ} [Fact p.Prime] [CharP R p]

/-- `A_k(f) = coeff_{x^{pᵏ−1}} f^{(pᵏ−1)/2}`. -/
noncomputable def hasseCoeff (p : ℕ) (f : R[X]) (k : ℕ) : R :=
  (f ^ ((p ^ k - 1) / 2)).coeff (p ^ k - 1)

lemma coeff_pow_iterateFrobenius (g : R[X]) (k j : ℕ) :
    ((g ^ p ^ k).coeff j) = if p ^ k ∣ j then (g.coeff (j / p ^ k)) ^ p ^ k else 0 := by
  rw [← map_iterateFrobenius_expand, coeff_map, coeff_expand (pow_pos (Fact.out : p.Prime).pos k)]
  split_ifs <;> simp [iterateFrobenius_def, (Fact.out : p.Prime).ne_zero]

/-- **Manin's digit lemma, one step**: `A_{k+1} = A_k · A_1^{pᵏ}` for a cubic `f`, `p` odd. -/
lemma hasseCoeff_succ (hp2 : p ≠ 2) (f : R[X]) (hf : f.natDegree ≤ 3) (k : ℕ) :
    hasseCoeff p f (k + 1) = hasseCoeff p f k * hasseCoeff p f 1 ^ p ^ k := by
  have hp := (Fact.out : p.Prime)
  have hodd : Odd p := hp.odd_of_ne_two hp2
  obtain ⟨s, hs⟩ := Odd.pow (n := k) hodd
  obtain ⟨r, hr⟩ := hodd
  have hP : 0 < p ^ k := pow_pos hp.pos k
  set P := p ^ k with hPdef
  have hpk1 : p ^ (k + 1) = p * P := by rw [pow_succ, mul_comm]
  have e1 : (p - 1) / 2 = r := by omega
  have ek : (P - 1) / 2 = s := by omega
  have pP : p * P = 2 * (2 * s * r + s + r) + 1 := by rw [hr, hs]; ring
  have ek1 : (p * P - 1) / 2 = s + r * P := by rw [pP, hs]; ring_nf; omega
  unfold hasseCoeff
  rw [hpk1, ← hPdef, ek1, ek, pow_one, e1, pow_add, pow_mul, coeff_mul]
  rw [Finset.sum_eq_single (P - 1, (p - 1) * P)]
  · rw [coeff_pow_iterateFrobenius, if_pos (dvd_mul_left _ _), Nat.mul_div_cancel _ hP, hPdef]
  · rintro ⟨i, j⟩ hij hne
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hij
    simp only at hij
    rw [coeff_pow_iterateFrobenius, ← hPdef]
    split_ifs with hd
    · obtain ⟨t, rfl⟩ := hd
      have hdeg : (f ^ s).natDegree ≤ 3 * s :=
        natDegree_pow_le.trans (by rw [mul_comm]; exact Nat.mul_le_mul_right _ hf)
      have hpP : P * p = p * P := mul_comm _ _
      have h2 : P * (p - 1) + P = P * p := by
        rw [← Nat.mul_succ]; congr 1; omega
      rcases lt_trichotomy t (p - 1) with ht | ht | ht
      · have h1 : P * t + P ≤ P * (p - 1) := by
          rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ ht
        rw [coeff_eq_zero_of_natDegree_lt (by omega), zero_mul]
      · exfalso; apply hne
        rw [ht] at hij ⊢
        rw [Prod.mk.injEq, mul_comm (p - 1) P]
        exact ⟨by omega, rfl⟩
      · have h1 : P * p ≤ P * t := Nat.mul_le_mul_left _ (by omega)
        omega
    · rw [mul_zero]
  · intro h
    exfalso; apply h
    rw [Finset.HasAntidiagonal.mem_antidiagonal]
    have h2 : P * (p - 1) + P = P * p := by rw [← Nat.mul_succ]; congr 1; omega
    have hpP : P * p = p * P := mul_comm _ _
    show P - 1 + (p - 1) * P = p * P - 1
    rw [mul_comm (p - 1) P]; omega

lemma hasseCoeff_eq_zero_iff [IsDomain R] (hp2 : p ≠ 2) (f : R[X]) (hf : f.natDegree ≤ 3)
    {n : ℕ} (hn : 1 ≤ n) : hasseCoeff p f n = 0 ↔ hasseCoeff p f 1 = 0 := by
  induction n, hn using Nat.le_induction with
  | base => rfl
  | succ k hk ih =>
    rw [hasseCoeff_succ hp2 f hf, mul_eq_zero, ih,
      pow_eq_zero_iff (pow_pos (Fact.out : p.Prime).pos k).ne', or_self]

end Mult

/-! ## Sums over a finite field -/

section Sums

variable {F : Type*} [Field F] [Fintype F]

lemma sum_pow_eq_ite (i : ℕ) (hi : i < 2 * (Fintype.card F - 1)) :
    ∑ x : F, x ^ i = if i = Fintype.card F - 1 then -1 else 0 := by
  classical
  have hq : 1 < Fintype.card F := Fintype.one_lt_card
  rcases Nat.eq_zero_or_pos i with rfl | hpos
  · rw [if_neg (show (0:ℕ) ≠ Fintype.card F - 1 by omega)]
    simp
  have h1 : ∑ x : Fˣ, (x : F) ^ i = ∑ x ∈ (univ : Finset F).erase 0, x ^ i := by
    refine Finset.sum_bij' (fun u _ => (u : F)) (fun x hx => Units.mk0 x (ne_of_mem_erase hx))
      ?_ ?_ ?_ ?_ ?_ <;> simp
  rw [Finset.sum_erase _ (by simp [hpos.ne'])] at h1
  rw [← h1, FiniteField.sum_pow_units]
  congr 1
  apply propext
  constructor
  · rintro ⟨k, rfl⟩
    rcases k with _ | _ | k
    · omega
    · ring
    · nlinarith
  · rintro rfl; exact dvd_rfl

/-- `Σ_{x ∈ 𝔽_q} g(x) = −coeff_{q−1}(g)` when `deg g < 2(q − 1)`. -/
lemma sum_eval_eq_neg_coeff (g : F[X]) (hg : g.natDegree < 2 * (Fintype.card F - 1)) :
    ∑ x : F, g.eval x = -g.coeff (Fintype.card F - 1) := by
  simp_rw [eval_eq_sum_range]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum]
  rw [Finset.sum_congr rfl (fun i hi => by
    rw [sum_pow_eq_ite i (by rw [mem_range] at hi; omega)])]
  simp only [mul_ite, mul_neg, mul_one, mul_zero, Finset.sum_ite_eq', mem_range]
  split_ifs with h
  · rfl
  · rw [coeff_eq_zero_of_natDegree_lt (by omega), neg_zero]

end Sums

/-! ## Point count -/

section Count

variable {F : Type*} [Field F] [Fintype F]

lemma natCard_point (W : WeierstrassCurve F) (hΔ : W.Δ ≠ 0) :
    Nat.card W.toAffine.Point = Nat.card {xy : F × F // W.toAffine.Equation xy.1 xy.2} + 1 := by
  rw [Nat.card_congr W.toAffine.nonsingularPointEquiv]
  rw [show WithZero {xy : F × F // W.toAffine.Nonsingular xy.1 xy.2} =
    Option {xy : F × F // W.toAffine.Nonsingular xy.1 xy.2} from rfl]
  classical
  rw [Nat.card_eq_fintype_card, Fintype.card_option, ← Nat.card_eq_fintype_card]
  congr 1
  exact Nat.card_congr (Equiv.subtypeEquivRight fun xy =>
    (WeierstrassCurve.Affine.equation_iff_nonsingular_of_Δ_ne_zero hΔ).symm)

lemma traceOfFrob_cast (W : WeierstrassCurve F) (hΔ : W.Δ ≠ 0) :
    ((traceOfFrob W : ℤ) : F) = -(Nat.card {xy : F × F // W.toAffine.Equation xy.1 xy.2} : F) := by
  unfold traceOfFrob
  rw [natCard_point W hΔ, Nat.card_eq_fintype_card (α := F)]
  push_cast
  rw [FiniteField.cast_card_eq_zero]
  ring

lemma natCard_subtype_prod (P : F → F → Prop) :
    (Nat.card {xy : F × F // P xy.1 xy.2} : F) = ∑ x : F, (Nat.card {y : F // P x y} : F) := by
  classical
  simp_rw [Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.card_filter]
  push_cast
  rw [Fintype.sum_prod_type]

end Count

/-! ## p odd -/

section Odd

variable {F : Type*} [Field F] [Fintype F] {p : ℕ} [Fact p.Prime] [CharP F p]

lemma equation_iff_sq (c : Fin 5 → F) (h4 : (4 : F) ≠ 0) (x y : F) :
    (wc c).toAffine.Equation x y ↔ (2 * y + c 0 * x + c 2) ^ 2 = (hasseCubic c).eval x := by
  rw [WeierstrassCurve.Affine.equation_iff]
  simp only [hasseCubic, eval_add, eval_mul, eval_pow, eval_C, eval_X, eval_ofNat, wc,
    WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆]
  constructor
  · intro h; linear_combination 4 * h
  · intro h
    have : 4 * ((y ^ 2 + c 0 * x * y + c 2 * y) - (x ^ 3 + c 1 * x ^ 2 + c 3 * x + c 4)) = 0 := by
      linear_combination h
    rw [mul_eq_zero] at this
    exact sub_eq_zero.mp (this.resolve_left h4)

lemma natCard_fiber_odd (hp2 : p ≠ 2) (c : Fin 5 → F) (x : F) :
    (Nat.card {y : F // (wc c).toAffine.Equation x y} : F) =
      ((hasseCubic c).eval x) ^ (Fintype.card F / 2) + 1 := by
  classical
  have hch : ringChar F ≠ 2 := by rwa [ringChar.eq F p]
  have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero hch
  have h4 : (4 : F) ≠ 0 := by
    rw [show (4 : F) = 2 * 2 by norm_num]; exact mul_ne_zero h2 h2
  have hc := quadraticChar_card_sqrts hch ((hasseCubic c).eval x)
  have hcard : Nat.card {y : F // (wc c).toAffine.Equation x y} =
      #{y : F | y ^ 2 = (hasseCubic c).eval x}.toFinset := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    refine Finset.card_nbij' (fun y => 2 * y + c 0 * x + c 2) (fun z => (z - c 0 * x - c 2) / 2)
      ?_ ?_ ?_ ?_
    · intro y hy
      simp only [Set.coe_toFinset, Set.mem_setOf_eq, Finset.coe_filter, Finset.mem_univ, true_and] at hy ⊢
      exact (equation_iff_sq c h4 x y).mp hy
    · intro z hz
      simp only [Set.coe_toFinset, Set.mem_setOf_eq, Finset.coe_filter, Finset.mem_univ, true_and] at hz ⊢
      rw [equation_iff_sq c h4]
      convert hz using 2
      field_simp; ring
    · intro y _; simp only; field_simp; ring
    · intro z _; simp only; field_simp; ring
  rw [hcard]
  have := congrArg (fun z : ℤ => (z : F)) hc
  simp only [Int.cast_natCast, Int.cast_add, Int.cast_one] at this
  rw [this, quadraticChar_eq_pow_of_char_ne_two' hch]

/-- `(a : 𝔽_q) = coeff_{x^{q−1}} f^{(q−1)/2}` for `p` odd. -/
lemma traceOfFrob_cast_odd (hp2 : p ≠ 2) (c : Fin 5 → F) (hΔ : (wc c).Δ ≠ 0) :
    ((traceOfFrob (wc c) : ℤ) : F) =
      (hasseCubic c ^ ((Fintype.card F - 1) / 2)).coeff (Fintype.card F - 1) := by
  have hq : 1 < Fintype.card F := Fintype.one_lt_card
  have hqodd : Fintype.card F % 2 = 1 := by
    obtain ⟨n, hpr, hn⟩ := FiniteField.card F p
    rw [hn, Nat.pow_mod]
    have : p % 2 = 1 := Nat.odd_iff.mp (hpr.odd_of_ne_two hp2)
    rw [this, one_pow]; rfl
  rw [traceOfFrob_cast _ hΔ, natCard_subtype_prod]
  simp_rw [natCard_fiber_odd hp2 c]
  rw [Finset.sum_add_distrib]
  simp only [sum_const, card_univ, nsmul_eq_mul, mul_one, FiniteField.cast_card_eq_zero,
    add_zero]
  have hm : Fintype.card F / 2 = (Fintype.card F - 1) / 2 := by omega
  simp_rw [hm, ← eval_pow]
  rw [sum_eval_eq_neg_coeff, neg_neg]
  refine (natDegree_pow_le).trans_lt ?_
  have := natDegree_hasseCubic c
  have : (Fintype.card F - 1) / 2 * (hasseCubic c).natDegree ≤ (Fintype.card F - 1) / 2 * 3 :=
    Nat.mul_le_mul_left _ this
  omega

end Odd

/-! ## p = 2 -/

section Two

variable {F : Type*} [Field F] [Fintype F] [CharP F 2]

lemma natCard_fixed_two (c : Fin 5 → F) :
    (Nat.card {xy : F × F // (wc c).toAffine.Equation xy.1 xy.2} : F) =
      (Nat.card {x : F // c 0 * x + c 2 = 0} : F) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2 : (2 : F) = 0 := CharP.ofNat_eq_zero F 2
  set W := (wc c).toAffine
  let α := {xy : F × F // W.Equation xy.1 xy.2}
  let f : Function.End α := fun P =>
    ⟨(P.1.1, W.negY P.1.1 P.1.2), (W.equation_neg _ _).mpr P.2⟩
  have hf : f ^ 2 ^ 1 = 1 := by
    funext P
    apply Subtype.ext
    show (P.1.1, W.negY P.1.1 (W.negY P.1.1 P.1.2)) = P.1
    rw [W.negY_negY]
  have hmod := Equiv.Perm.card_fixedPoints_modEq (p := 2) (n := 1) hf
  have hfix : Function.IsFixedPt f = fun P : α => c 0 * P.1.1 + c 2 = 0 := by
    funext P
    apply propext
    rw [Function.IsFixedPt, Subtype.ext_iff, Prod.ext_iff]
    show (P.1.1 = P.1.1 ∧ W.negY P.1.1 P.1.2 = P.1.2) ↔ _
    rw [and_iff_right rfl]
    simp only [WeierstrassCurve.Affine.negY, W, wc]
    constructor
    · intro h; linear_combination -h - P.1.2 * h2
    · intro h; linear_combination -h - P.1.2 * h2
  have hbij : Fintype.card (Function.fixedPoints f) = Fintype.card {x : F // c 0 * x + c 2 = 0} := by
    refine Fintype.card_of_bijective (f := fun P => ⟨P.1.1.1, ?_⟩) ⟨?_, ?_⟩
    · have := P.2; rw [Function.mem_fixedPoints, hfix] at this; exact this
    · rintro ⟨⟨⟨x, y⟩, hy⟩, hP⟩ ⟨⟨⟨x', y'⟩, hy'⟩, hP'⟩ h
      simp only [Subtype.mk.injEq] at h
      subst h
      rw [Function.mem_fixedPoints, hfix] at hP hP'
      simp only at hP hP'
      have e1 := (WeierstrassCurve.Affine.equation_iff _ _).mp hy
      have e2 := (WeierstrassCurve.Affine.equation_iff _ _).mp hy'
      simp only [W, wc] at e1 e2
      have : frobenius F 2 y = frobenius F 2 y' := by
        simp only [frobenius_def]
        linear_combination e1 - e2 - (y - y') * hP
      have := frobenius_inj F 2 this
      subst this; rfl
    · rintro ⟨x, hx⟩
      obtain ⟨y, hy⟩ := (Finite.injective_iff_surjective.mp (frobenius_inj F 2))
        (x ^ 3 + c 1 * x ^ 2 + c 3 * x + c 4)
      rw [frobenius_def] at hy
      have hE : W.Equation x y := by
        rw [WeierstrassCurve.Affine.equation_iff]
        simp only [W, wc]
        linear_combination hy + y * hx
      refine ⟨⟨⟨(x, y), hE⟩, ?_⟩, rfl⟩
      rw [Function.mem_fixedPoints, hfix]; exact hx
  have := (CharP.natCast_eq_natCast F 2).mpr hmod
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  convert this using 2
  exact hbij.symm

lemma delta_eq_zero_two (c : Fin 5 → F) (h0 : c 0 = 0) (h2 : c 2 = 0) : (wc c).Δ = 0 := by
  have h : (2 : F) = 0 := CharP.ofNat_eq_zero F 2
  simp only [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
    WeierstrassCurve.b₈, wc, h0, h2]
  linear_combination (-8 * c 1 ^ 2 * (4 * c 1 * c 4 - c 3 ^ 2) - 32 * c 3 ^ 3 - 216 * c 4 ^ 2
    + 144 * c 1 * c 3 * c 4) * h

open scoped Classical in
lemma traceOfFrob_cast_two (c : Fin 5 → F) (hΔ : (wc c).Δ ≠ 0) :
    ((traceOfFrob (wc c) : ℤ) : F) = if c 0 = 0 then 0 else -1 := by
  rw [traceOfFrob_cast _ hΔ, natCard_fixed_two]
  split_ifs with h0
  · have h2 : c 2 ≠ 0 := fun h2 => hΔ (delta_eq_zero_two c h0 h2)
    haveI : IsEmpty {x : F // c 0 * x + c 2 = 0} := ⟨fun ⟨x, hx⟩ => h2 (by simpa [h0] using hx)⟩
    simp
  · have : Nat.card {x : F // c 0 * x + c 2 = 0} = 1 := by
      rw [Nat.card_eq_one_iff_exists]
      refine ⟨⟨-c 2 / c 0, by field_simp; ring⟩, ?_⟩
      rintro ⟨x, hx⟩
      apply Subtype.ext
      simp only
      field_simp
      linear_combination hx
    rw [this, Nat.cast_one]

end Two

/-! ## The criterion -/

/-- **`p ∣ a(E) ⟺ Hasse(E) = 0` (p odd), `⟺ a₁ = 0` (p = 2)**, over any finite field of
characteristic `p`. -/
theorem dvd_traceOfFrob_iff_of_finite {F : Type*} [Field F] [Fintype F] (p : ℕ) [Fact p.Prime]
    [CharP F p] (c : Fin 5 → F) (hc : (wc c).Δ ≠ 0) :
    ((p : ℤ) ∣ traceOfFrob (wc c) ↔ if p = 2 then c 0 = 0 else hasseInv p c = 0) := by
  rw [← CharP.intCast_eq_zero_iff F p]
  split_ifs with hp2
  · subst hp2
    rw [traceOfFrob_cast_two c hc]
    split_ifs with h0
    · simp [h0]
    · simp [h0]
  · obtain ⟨n, -, hn⟩ := FiniteField.card F p
    rw [traceOfFrob_cast_odd hp2 c hc, hasseInv_eq, hn]
    have := hasseCoeff_eq_zero_iff (p := p) hp2 (hasseCubic c) (natDegree_hasseCubic c) n.pos
    simpa only [hasseCoeff, pow_one] using this

/-- The frozen form (over `GaloisField p n`). -/
theorem dvd_traceOfFrob_iff (p : ℕ) [Fact p.Prime] (n : ℕ) (hn : 1 ≤ n)
    (c : Fin 5 → GaloisField p n) (hc : (wc c).Δ ≠ 0) :
    letI : Fintype (GaloisField p n) := Fintype.ofFinite _
    ((p : ℤ) ∣ traceOfFrob (wc c) ↔ if p = 2 then c 0 = 0 else hasseInv p c = 0) := by
  letI : Fintype (GaloisField p n) := Fintype.ofFinite _
  exact dvd_traceOfFrob_iff_of_finite p c hc

end RamanujanWeil.ArithPlan
