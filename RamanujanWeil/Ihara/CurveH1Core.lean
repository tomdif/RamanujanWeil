import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.LinearAlgebra.Trace
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.FieldTheory.Finite.Extension

/-!
# M4a, linear-algebra core: the Frobenius on `H¹` of a genus-one curve (Mathlib only)

The cohomological input of milestone M4a (`docs/IHARA_CURVE_H1.md`) is reduced here to a
statement about one endomorphism `F` of a two-dimensional vector space `V` over a field `K` of
characteristic zero (in the application `V = H¹(X_k̄, ℚ_ℓ)` and `F` the geometric Frobenius):

* `hpure`: every complex root `z` of `charpoly(F)` read along some `ι : K →+* ℂ` has `‖z‖² = q`
  (Deligne's purity of weight one, `Weil.isCharpolyPureOfWeight_rationalFrobenius`);
* `htr`: `tr(Fⁿ) = qⁿ + 1 − N n` for every `n ≥ 1` (the Lefschetz trace formula with
  `H⁰ = ℚ_ℓ`, `F = 1` and `H² = ℚ_ℓ`, `F = q`);
* `hdvd`: `N 3 ∣ N 6`. For an elliptic curve `E` with `N n = #E(𝔽_{qⁿ})` this is Lagrange for
  the subgroup `E(𝔽_{q³}) ≤ E(𝔽_{q⁶})` (`natCard_point_dvd_of_finrank_dvd`).

The conclusion is `charpoly(F) = X² − aX + q` with `a = q + 1 − N 1`
(`charpoly_eq_of_pure_of_traces`). The proof never needs the alternation of the cup product:

* `F` has rational determinant `c` (from the traces of `F` and `F²`), and purity gives `|c| = q`;
* if `c = −q`, purity forces the two roots to be `z, −z̄`, so `a = z − z̄` is purely imaginary,
  hence `a = 0`; then `tr F³ = 0` and `tr F⁶ = 2q³`, so `N 3 = q³ + 1` and `N 6 = (q³ − 1)²`;
  `q³ + 1 ∣ (q³ − 1)² = (q³ + 1)(q³ − 3) + 4` gives `q³ + 1 ∣ 4`, impossible for `q ≥ 2`.

We also record the power-sum form (`trace_pow_eq_frobPowerSum`,
`pointCount_eq_sub_frobPowerSum`, `frobPowerSum_eq_add_pow`) and the Hasse bound
`a² ≤ 4q` (`sq_le_four_mul_of_pure`).
-/

open Polynomial Module

namespace RamanujanWeil.Ihara

/-! ### Power sums `αⁿ + βⁿ` of the roots of `X² − aX + q` -/

/-- `s_n = αⁿ + βⁿ` for the roots `α, β` of `X² − aX + q`, by the recursion
`s₀ = 2`, `s₁ = a`, `s_{n+2} = a s_{n+1} − q s_n`. -/
def frobPowerSum (a q : ℤ) : ℕ → ℤ
  | 0 => 2
  | 1 => a
  | n + 2 => a * frobPowerSum a q (n + 1) - q * frobPowerSum a q n

@[simp] theorem frobPowerSum_zero (a q : ℤ) : frobPowerSum a q 0 = 2 := rfl
@[simp] theorem frobPowerSum_one (a q : ℤ) : frobPowerSum a q 1 = a := rfl
theorem frobPowerSum_add_two (a q : ℤ) (n : ℕ) :
    frobPowerSum a q (n + 2) = a * frobPowerSum a q (n + 1) - q * frobPowerSum a q n := rfl

/-- `s_n = αⁿ + βⁿ` in any commutative ring containing `α, β` with `α + β = a`, `αβ = q`. -/
theorem frobPowerSum_eq_add_pow {R : Type*} [CommRing R] (a q : ℤ) (α β : R)
    (hs : α + β = a) (hp : α * β = q) (n : ℕ) : (frobPowerSum a q n : R) = α ^ n + β ^ n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n, ih with
    | 0, _ => norm_num
    | 1, _ => simp [hs]
    | n + 2, ih =>
      rw [frobPowerSum_add_two, Int.cast_sub, Int.cast_mul, Int.cast_mul, ih (n + 1) (by omega),
        ih n (by omega), ← hs, ← hp]
      ring

/-- A sequence with the recursion of `frobPowerSum` and the right initial values is it. -/
theorem eq_frobPowerSum {K : Type*} [CommRing K] (a q : ℤ) (s : ℕ → K) (h0 : s 0 = 2)
    (h1 : s 1 = a) (hrec : ∀ n, s (n + 2) = a * s (n + 1) - q * s n) (n : ℕ) :
    s n = frobPowerSum a q n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n, ih with
    | 0, _ => simp [h0]
    | 1, _ => simp [h1]
    | n + 2, ih =>
      rw [hrec, ih (n + 1) (by omega), ih n (by omega), frobPowerSum_add_two]
      push_cast; ring

/-! ### Two-dimensional endomorphisms -/

section TwoDim

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- `charpoly F = X² − tr(F) X + c₀` on a two-dimensional space (`c₀ = det F`). -/
theorem charpoly_eq_of_finrank_eq_two (F : Module.End K V) (h : finrank K V = 2) :
    F.charpoly = X ^ 2 - C (LinearMap.trace K V F) * X + C (F.charpoly.coeff 0) := by
  have hdeg : F.charpoly.natDegree = 2 := by rw [LinearMap.charpoly_natDegree, h]
  have htr : LinearMap.trace K V F = - F.charpoly.coeff 1 := by
    let b := Module.finBasisOfFinrankEq K V h
    rw [LinearMap.trace_eq_matrix_trace K b, Matrix.trace_eq_neg_charpoly_coeff,
      LinearMap.charpoly_toMatrix]
    rfl
  conv_lhs => rw [(LinearMap.charpoly_monic F).as_sum, hdeg]
  rw [htr, Finset.sum_range_succ, Finset.sum_range_one]
  simp only [pow_zero, mul_one, pow_one, map_neg, neg_mul, sub_neg_eq_add]
  ring

/-- Cayley–Hamilton on a two-dimensional space: `F^{n+2} = tr(F) F^{n+1} − c₀ Fⁿ`, on traces. -/
theorem trace_pow_add_two_of_finrank_eq_two (F : Module.End K V) (h : finrank K V = 2) (n : ℕ) :
    LinearMap.trace K V (F ^ (n + 2)) =
      LinearMap.trace K V F * LinearMap.trace K V (F ^ (n + 1)) -
        F.charpoly.coeff 0 * LinearMap.trace K V (F ^ n) := by
  have hCH := LinearMap.aeval_self_charpoly F
  rw [charpoly_eq_of_finrank_eq_two F h] at hCH
  simp only [map_add, map_sub, map_mul, map_pow, aeval_X, aeval_C] at hCH
  have hF2 : F ^ 2 = algebraMap K _ (LinearMap.trace K V F) * F -
      algebraMap K _ (F.charpoly.coeff 0) := by
    rw [← sub_eq_zero, ← hCH]; abel
  have : F ^ (n + 2) = LinearMap.trace K V F • F ^ (n + 1) - F.charpoly.coeff 0 • F ^ n := by
    rw [show n + 2 = 2 + n by omega, pow_add, hF2, sub_mul, mul_assoc, ← pow_succ',
      Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, smul_mul_assoc,
      smul_mul_assoc, one_mul, one_mul]
  rw [this, map_sub, map_smul, map_smul, smul_eq_mul, smul_eq_mul]

theorem trace_pow_zero_of_finrank_eq_two (F : Module.End K V) (h : finrank K V = 2) :
    LinearMap.trace K V (F ^ 0) = 2 := by
  rw [pow_zero, LinearMap.trace_one, h]; norm_num

/-- If `charpoly F = X² − aX + q` with `a, q ∈ ℤ`, then `tr(Fⁿ) = s_n(a, q)` for every `n`. -/
theorem trace_pow_eq_frobPowerSum (F : Module.End K V) (h : finrank K V = 2) (a q : ℤ)
    (hF : F.charpoly = X ^ 2 - C (a : K) * X + C (q : K)) (n : ℕ) :
    LinearMap.trace K V (F ^ n) = frobPowerSum a q n := by
  have hc0 : F.charpoly.coeff 0 = q := by rw [hF]; simp
  have htr : LinearMap.trace K V F = a := by
    have := charpoly_eq_of_finrank_eq_two F h
    rw [hF] at this
    have h1 := congrArg (fun P => P.coeff 1) this
    simp only [coeff_add, coeff_sub, coeff_C_mul, coeff_X_pow, coeff_X_one, coeff_C] at h1
    norm_num at h1
    exact h1.symm
  refine eq_frobPowerSum a q (fun n => LinearMap.trace K V (F ^ n)) ?_ ?_ ?_ n
  · exact trace_pow_zero_of_finrank_eq_two F h
  · simpa using htr
  · intro n
    rw [trace_pow_add_two_of_finrank_eq_two F h, htr, hc0]

end TwoDim


/-! ### One-dimensional endomorphisms -/

section OneDim

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- `charpoly F = X − tr(F)` on a one-dimensional space. -/
theorem charpoly_eq_of_finrank_eq_one (F : Module.End K V) (h : finrank K V = 1) :
    F.charpoly = X - C (LinearMap.trace K V F) := by
  have hdeg : F.charpoly.natDegree = 1 := by rw [LinearMap.charpoly_natDegree, h]
  have htr : LinearMap.trace K V F = - F.charpoly.coeff 0 := by
    let b := Module.finBasisOfFinrankEq K V h
    rw [LinearMap.trace_eq_matrix_trace K b, Matrix.trace_eq_neg_charpoly_coeff,
      LinearMap.charpoly_toMatrix]
    rfl
  conv_lhs => rw [(LinearMap.charpoly_monic F).as_sum, hdeg]
  rw [htr, Finset.sum_range_one]
  simp

/-- An endomorphism with characteristic polynomial `X − c` is `c • id`. -/
theorem eq_smul_id_of_charpoly_eq (F : Module.End K V) (c : K) (hF : F.charpoly = X - C c) :
    F = c • LinearMap.id := by
  have hCH := LinearMap.aeval_self_charpoly F
  rw [hF] at hCH
  simp only [map_sub, aeval_X, aeval_C] at hCH
  rw [sub_eq_zero] at hCH
  rw [hCH, Algebra.algebraMap_eq_smul_one]
  rfl

/-- The dimension is the degree of the characteristic polynomial. -/
theorem finrank_eq_one_of_charpoly_eq (F : Module.End K V) (c : K) (hF : F.charpoly = X - C c) :
    finrank K V = 1 := by
  rw [← LinearMap.charpoly_natDegree F, hF, natDegree_X_sub_C]

/-- With `charpoly F = X − c`, `tr(Fⁿ) = cⁿ`. -/
theorem trace_pow_of_charpoly_eq (F : Module.End K V) (c : K) (hF : F.charpoly = X - C c)
    (n : ℕ) : LinearMap.trace K V (F ^ n) = c ^ n := by
  rw [eq_smul_id_of_charpoly_eq F c hF, smul_pow, map_smul, ← Module.End.one_eq_id, one_pow,
    LinearMap.trace_one, finrank_eq_one_of_charpoly_eq F c hF]
  simp

/-- On a one-dimensional space, `charpoly (c • id) = X − c`. -/
theorem charpoly_smul_id_of_finrank_eq_one (c : K) (h : finrank K V = 1) :
    (c • LinearMap.id : Module.End K V).charpoly = X - C c := by
  rw [charpoly_eq_of_finrank_eq_one _ h, map_smul, LinearMap.trace_id, h]
  simp

end OneDim

/-! ### The arithmetic exclusion of `det = −q` -/

/-- `q³ + 1 ∤ (q³ − 1)²` for `q ≥ 2`. -/
theorem not_dvd_of_two_le (q : ℕ) (hq : 2 ≤ q) (N3 N6 : ℕ) (h3 : N3 = q ^ 3 + 1)
    (h6 : N6 + 2 * q ^ 3 = q ^ 6 + 1) : ¬ N3 ∣ N6 := by
  intro hd
  have h6' : (N6 : ℤ) = ((q : ℤ) ^ 3 + 1) * ((q : ℤ) ^ 3 - 3) + 4 := by
    have : (N6 : ℤ) + 2 * (q : ℤ) ^ 3 = (q : ℤ) ^ 6 + 1 := by exact_mod_cast h6
    linear_combination this
  have hd' : ((q : ℤ) ^ 3 + 1) ∣ (N6 : ℤ) := by
    rw [h3] at hd; exact_mod_cast Int.natCast_dvd_natCast.2 hd
  rw [h6'] at hd'
  have h4 : ((q : ℤ) ^ 3 + 1) ∣ 4 := (Int.dvd_add_right (dvd_mul_right _ _)).1 hd'
  have hle := Int.le_of_dvd (by norm_num) h4
  have : (8 : ℤ) ≤ (q : ℤ) ^ 3 := by
    have : (2 : ℤ) ≤ q := by exact_mod_cast hq
    calc (8 : ℤ) = 2 ^ 3 := by norm_num
      _ ≤ (q : ℤ) ^ 3 := pow_le_pow_left₀ (by norm_num) this 3
  linarith

/-! ### The main linear-algebra theorem -/

section Main

variable {K V : Type*} [Field K] [CharZero K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

/-- Over `ℂ`, a monic quadratic `X² − tX + c` has roots `z₁, z₂` with `z₁ + z₂ = t`,
`z₁ z₂ = c`. -/
theorem exists_roots_of_quadratic (t c : ℂ) :
    ∃ z₁ z₂ : ℂ, z₁ + z₂ = t ∧ z₁ * z₂ = c ∧
      (X ^ 2 - C t * X + C c : ℂ[X]).IsRoot z₁ ∧ (X ^ 2 - C t * X + C c : ℂ[X]).IsRoot z₂ := by
  have hdeg : (X ^ 2 - C t * X + C c : ℂ[X]).degree ≠ 0 := by
    rw [show (X ^ 2 - C t * X + C c : ℂ[X]) = C 1 * X ^ 2 + C (-t) * X + C c by
      rw [map_neg, map_one]; ring]
    rw [Polynomial.degree_quadratic one_ne_zero]; norm_num
  obtain ⟨z, hz0⟩ := IsAlgClosed.exists_root _ hdeg
  have hz := hz0
  simp only [IsRoot, eval_add, eval_sub, eval_mul, eval_pow, eval_X, eval_C] at hz
  refine ⟨z, t - z, by ring, by linear_combination -hz, hz0, ?_⟩
  simp only [IsRoot, eval_add, eval_sub, eval_mul, eval_pow, eval_X, eval_C]
  linear_combination hz

omit [CharZero K] in
/-- The complex roots of `charpoly(F).map ι` for `F` on a two-dimensional space. -/
theorem exists_roots_charpoly_map (F : Module.End K V) (h : finrank K V = 2) (ι : K →+* ℂ) :
    ∃ z₁ z₂ : ℂ, z₁ + z₂ = ι (LinearMap.trace K V F) ∧ z₁ * z₂ = ι (F.charpoly.coeff 0) ∧
      (F.charpoly.map ι).IsRoot z₁ ∧ (F.charpoly.map ι).IsRoot z₂ := by
  have hmap : F.charpoly.map ι = X ^ 2 - C (ι (LinearMap.trace K V F)) * X +
      C (ι (F.charpoly.coeff 0)) := by
    conv_lhs => rw [charpoly_eq_of_finrank_eq_two F h]
    simp [Polynomial.map_sub, Polynomial.map_add]
  rw [hmap]
  exact exists_roots_of_quadratic _ _

omit [CharZero K] in
/-- **Hasse bound from purity.** If the roots of `charpoly(F)` along `ι` have `‖z‖² = q`, then
`‖ι(tr F)‖ ≤ 2√q`. -/
theorem norm_trace_le_of_pure (F : Module.End K V) (h : finrank K V = 2) (ι : K →+* ℂ) (q : ℕ)
    (hpure : ∀ z : ℂ, (F.charpoly.map ι).IsRoot z → ‖z‖ ^ 2 = q) :
    ‖ι (LinearMap.trace K V F)‖ ≤ 2 * Real.sqrt q := by
  obtain ⟨z₁, z₂, hs, -, h₁, h₂⟩ := exists_roots_charpoly_map F h ι
  have hn : ∀ z : ℂ, ‖z‖ ^ 2 = q → ‖z‖ = Real.sqrt q := fun z hz => by
    rw [← hz, Real.sqrt_sq (norm_nonneg _)]
  rw [← hs]
  calc ‖z₁ + z₂‖ ≤ ‖z₁‖ + ‖z₂‖ := norm_add_le _ _
    _ = 2 * Real.sqrt q := by rw [hn _ (hpure _ h₁), hn _ (hpure _ h₂)]; ring

omit [CharZero K] in
/-- **Integer Hasse bound**: if moreover `tr F = a ∈ ℤ`, then `a² ≤ 4q`. -/
theorem sq_le_four_mul_of_pure (F : Module.End K V) (h : finrank K V = 2) (ι : K →+* ℂ) (q : ℕ)
    (hpure : ∀ z : ℂ, (F.charpoly.map ι).IsRoot z → ‖z‖ ^ 2 = q) (a : ℤ)
    (ha : LinearMap.trace K V F = a) : a ^ 2 ≤ 4 * q := by
  have hle := norm_trace_le_of_pure F h ι q hpure
  rw [ha, map_intCast, Complex.norm_intCast] at hle
  have h0 : (0 : ℝ) ≤ 2 * Real.sqrt q := by positivity
  have hsq : ((a : ℝ)) ^ 2 ≤ (2 * Real.sqrt q) ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hle 2
  rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg _)] at hsq
  exact_mod_cast hsq

/-- **M4a, linear-algebra core.** Let `F` be an endomorphism of a two-dimensional vector space
over a field of characteristic zero, `q ≥ 2`, and `N : ℕ → ℕ` with

* every root `z` of `charpoly(F)` along `ι : K →+* ℂ` satisfying `‖z‖² = q` (purity),
* `tr(Fⁿ) = qⁿ + 1 − N n` for all `n ≥ 1` (trace formula),
* `N 3 ∣ N 6` (Lagrange in `E(𝔽_{q³}) ≤ E(𝔽_{q⁶})`).

Then `charpoly(F) = X² − aX + q` with `a = q + 1 − N 1`. -/
theorem charpoly_eq_of_pure_of_traces (F : Module.End K V) (h : finrank K V = 2)
    (ι : K →+* ℂ) (q : ℕ) (hq : 2 ≤ q)
    (hpure : ∀ z : ℂ, (F.charpoly.map ι).IsRoot z → ‖z‖ ^ 2 = q) (N : ℕ → ℕ)
    (htr : ∀ n : ℕ, 1 ≤ n → LinearMap.trace K V (F ^ n) = (q : K) ^ n + 1 - N n)
    (hdvd : N 3 ∣ N 6) :
    F.charpoly = X ^ 2 - C (((q : ℤ) + 1 - N 1 : ℤ) : K) * X + C (q : K) := by
  have hrec := trace_pow_add_two_of_finrank_eq_two F h
  have hchar := charpoly_eq_of_finrank_eq_two F h
  obtain ⟨z₁, z₂, hs, hp, h₁, h₂⟩ := exists_roots_charpoly_map F h ι
  have hz₁ := hpure _ h₁
  have hz₂ := hpure _ h₂
  have e2 : LinearMap.trace K V (F ^ 2) =
      LinearMap.trace K V F * LinearMap.trace K V F - F.charpoly.coeff 0 * 2 := by
    rw [← trace_pow_zero_of_finrank_eq_two F h, ← pow_one F]
    exact hrec 0
  have e3 : LinearMap.trace K V (F ^ 3) = LinearMap.trace K V F * LinearMap.trace K V (F ^ 2) -
      F.charpoly.coeff 0 * LinearMap.trace K V F := by
    have := hrec 1; rwa [pow_one] at this
  have e4 : LinearMap.trace K V (F ^ 4) = LinearMap.trace K V F * LinearMap.trace K V (F ^ 3) -
      F.charpoly.coeff 0 * LinearMap.trace K V (F ^ 2) := hrec 2
  have e5 : LinearMap.trace K V (F ^ 5) = LinearMap.trace K V F * LinearMap.trace K V (F ^ 4) -
      F.charpoly.coeff 0 * LinearMap.trace K V (F ^ 3) := hrec 3
  have e6 : LinearMap.trace K V (F ^ 6) = LinearMap.trace K V F * LinearMap.trace K V (F ^ 5) -
      F.charpoly.coeff 0 * LinearMap.trace K V (F ^ 4) := hrec 4
  have h1 := htr 1 le_rfl
  rw [pow_one, pow_one] at h1
  have h2 := htr 2 (by norm_num)
  have h3 := htr 3 (by norm_num)
  have h6 := htr 6 (by norm_num)
  rw [hchar]
  clear hrec hpure htr h₁ h₂ hchar
  generalize LinearMap.trace K V F = t at *
  generalize F.charpoly.coeff 0 = c at *
  generalize LinearMap.trace K V (F ^ 2) = T2 at *
  generalize LinearMap.trace K V (F ^ 3) = T3 at *
  generalize LinearMap.trace K V (F ^ 4) = T4 at *
  generalize LinearMap.trace K V (F ^ 5) = T5 at *
  generalize LinearMap.trace K V (F ^ 6) = T6 at *
  have ht1 : t = (((q : ℤ) + 1 - N 1 : ℤ) : K) := by rw [h1]; push_cast; ring
  -- `c` is rational
  set r : ℚ := ((((q : ℤ) + 1 - N 1) ^ 2 - ((q : ℤ) ^ 2 + 1 - N 2) : ℤ) : ℚ) / 2 with hr
  have hcr : c = (r : K) := by
    have e : (r : K) = (t ^ 2 - ((q : K) ^ 2 + 1 - N 2)) / 2 := by
      rw [hr, ht1]; push_cast; ring
    rw [e, eq_div_iff two_ne_zero]
    linear_combination e2 - h2
  -- purity: `|r| = q`
  have hnc : ‖ι c‖ = q := by
    rw [← hp, norm_mul]
    have : ‖z₁‖ ^ 2 * ‖z₂‖ ^ 2 = (q : ℝ) ^ 2 := by rw [hz₁, hz₂]; ring
    have h0' : 0 ≤ ‖z₁‖ * ‖z₂‖ := by positivity
    nlinarith [sq_nonneg (‖z₁‖ * ‖z₂‖ - q), sq_nonneg (‖z₁‖ * ‖z₂‖ + q)]
  rw [hcr, map_ratCast, Complex.norm_ratCast] at hnc
  have hr' : r = q ∨ r = -q := by
    rcases abs_eq (by positivity : (0 : ℝ) ≤ q) |>.1 hnc with h | h
    · left; exact_mod_cast h
    · right; exact_mod_cast h
  rcases hr' with hrq | hrq
  · -- the generic case `det = q`
    rw [ht1, hcr, hrq]
    push_cast; ring
  · -- `det = −q` is impossible
    exfalso
    have hcq : c = -(q : K) := by rw [hcr, hrq]; push_cast; ring
    have hpq : z₁ * z₂ = -(q : ℂ) := by rw [hp, hcq]; simp
    have hz₁0 : z₁ ≠ 0 := by
      intro h0; rw [h0, norm_zero] at hz₁
      have : (q : ℝ) ≥ 2 := by exact_mod_cast hq
      have : (q : ℝ) = 0 := by rw [← hz₁]; ring
      linarith
    have hconj : (starRingEnd ℂ) z₁ * z₁ = (q : ℂ) := by
      rw [Complex.conj_mul', ← Complex.ofReal_pow, hz₁, Complex.ofReal_natCast]
    have hz₂ : z₂ = -(starRingEnd ℂ) z₁ := by
      have : z₁ * (z₂ + (starRingEnd ℂ) z₁) = 0 := by
        rw [mul_add, hpq, mul_comm z₁, hconj]; ring
      rcases mul_eq_zero.1 this with h | h
      · exact absurd h hz₁0
      · linear_combination h
    have hre : (ι t).re = 0 := by
      rw [← hs, hz₂]; simp
    have ht0 : ((q : ℤ) + 1 - N 1 : ℤ) = 0 := by
      rw [ht1, map_intCast, Complex.intCast_re] at hre
      exact_mod_cast hre
    have ht0' : t = 0 := by rw [ht1, ht0]; simp
    subst ht0'
    have hT2 : T2 = 2 * q := by rw [e2, hcq]; ring
    have hT3 : T3 = 0 := by rw [e3]; ring
    have hT4 : T4 = 2 * q ^ 2 := by rw [e4, hT2, hcq]; ring
    have hT5 : T5 = 0 := by rw [e5, hT3, hcq]; ring
    have hT6 : T6 = 2 * q ^ 3 := by rw [e6, hT4, hcq]; ring
    rw [hT3] at h3; rw [hT6] at h6
    have hN3 : N 3 = q ^ 3 + 1 := by
      have : ((N 3 : ℕ) : K) = ((q ^ 3 + 1 : ℕ) : K) := by push_cast; linear_combination h3
      exact_mod_cast this
    have hN6 : N 6 + 2 * q ^ 3 = q ^ 6 + 1 := by
      have : ((N 6 + 2 * q ^ 3 : ℕ) : K) = ((q ^ 6 + 1 : ℕ) : K) := by
        push_cast; linear_combination h6
      exact_mod_cast this
    exact not_dvd_of_two_le q hq _ _ hN3 hN6 hdvd

/-- **Power-sum form.** Under the hypotheses of `charpoly_eq_of_pure_of_traces`,
`tr(Fⁿ) = s_n(a, q)` for every `n`, where `s_n = αⁿ + βⁿ`, `α, β` the roots of `X² − aX + q`. -/
theorem trace_pow_eq_frobPowerSum_of_pure (F : Module.End K V) (h : finrank K V = 2)
    (ι : K →+* ℂ) (q : ℕ) (hq : 2 ≤ q)
    (hpure : ∀ z : ℂ, (F.charpoly.map ι).IsRoot z → ‖z‖ ^ 2 = q) (N : ℕ → ℕ)
    (htr : ∀ n : ℕ, 1 ≤ n → LinearMap.trace K V (F ^ n) = (q : K) ^ n + 1 - N n)
    (hdvd : N 3 ∣ N 6) (n : ℕ) :
    LinearMap.trace K V (F ^ n) = frobPowerSum ((q : ℤ) + 1 - N 1) q n := by
  have := charpoly_eq_of_pure_of_traces F h ι q hq hpure N htr hdvd
  exact trace_pow_eq_frobPowerSum F h _ _ (by rw [this]; push_cast; ring) n

/-- **Point counts over every extension.** Under the same hypotheses,
`N n = qⁿ + 1 − s_n(a, q)` for every `n ≥ 1`. -/
theorem pointCount_eq_sub_frobPowerSum (F : Module.End K V) (h : finrank K V = 2)
    (ι : K →+* ℂ) (q : ℕ) (hq : 2 ≤ q)
    (hpure : ∀ z : ℂ, (F.charpoly.map ι).IsRoot z → ‖z‖ ^ 2 = q) (N : ℕ → ℕ)
    (htr : ∀ n : ℕ, 1 ≤ n → LinearMap.trace K V (F ^ n) = (q : K) ^ n + 1 - N n)
    (hdvd : N 3 ∣ N 6) (n : ℕ) (hn : 1 ≤ n) :
    (N n : ℤ) = (q : ℤ) ^ n + 1 - frobPowerSum ((q : ℤ) + 1 - N 1) q n := by
  have h1 := trace_pow_eq_frobPowerSum_of_pure F h ι q hq hpure N htr hdvd n
  rw [htr n hn] at h1
  have : ((N n : ℤ) : K) = (((q : ℤ) ^ n + 1 - frobPowerSum ((q : ℤ) + 1 - N 1) q n : ℤ) : K) := by
    push_cast; linear_combination -h1
  exact_mod_cast this

end Main

/-! ### Lagrange for Weierstrass curves over finite fields -/

section Lagrange

open WeierstrassCurve

/-- For field extensions `K → L` of `k` (as `k`-algebras), `#W(K) ∣ #W(L)`: `W(K)` is a subgroup
of `W(L)` through `Point.map`. (`Nat.card` is `0` for infinite groups, where this is trivial.) -/
theorem natCard_point_dvd_of_algHom {k K L : Type*} [Field k] [Field K] [Field L] [Algebra k K]
    [Algebra k L] (W : WeierstrassCurve k) (φ : K →ₐ[k] L) :
    Nat.card (W.baseChange K).toAffine.Point ∣ Nat.card (W.baseChange L).toAffine.Point := by
  classical
  let m := Affine.Point.map (W' := W.toAffine) φ
  have hm : Function.Injective m := Affine.Point.map_injective φ
  have : Nat.card m.range = Nat.card (W.baseChange K).toAffine.Point :=
    (Nat.card_congr (AddMonoidHom.ofInjective hm).toEquiv).symm
  rw [← this]
  exact AddSubgroup.card_addSubgroup_dvd_card _

/-- `#W(𝔽_{q^m}) ∣ #W(𝔽_{q^n})` for `m ∣ n`, with Mathlib's chosen extensions
`FiniteField.Extension k p m`. -/
theorem natCard_point_extension_dvd {k : Type*} [Field k] [Finite k] (p : ℕ) [Fact p.Prime]
    [CharP k p] (W : WeierstrassCurve k) (m n : ℕ) [NeZero m] [NeZero n] (hmn : m ∣ n) :
    Nat.card (W.baseChange (FiniteField.Extension k p m)).toAffine.Point ∣
      Nat.card (W.baseChange (FiniteField.Extension k p n)).toAffine.Point := by
  obtain ⟨φ⟩ := FiniteField.nonempty_algHom_of_finrank_dvd (F := k)
    (K := FiniteField.Extension k p m) (L := FiniteField.Extension k p n)
    (by rw [FiniteField.finrank_extension, FiniteField.finrank_extension]; exact hmn)
  exact natCard_point_dvd_of_algHom W φ

/-- `#W(K) = #W(L)` for `k`-isomorphic fields `K ≃ L`. -/
theorem natCard_point_congr {k K L : Type*} [Field k] [Field K] [Field L] [Algebra k K]
    [Algebra k L] (W : WeierstrassCurve k) (e : K ≃ₐ[k] L) :
    Nat.card (W.baseChange K).toAffine.Point = Nat.card (W.baseChange L).toAffine.Point := by
  classical
  refine Nat.card_congr
    { toFun := Affine.Point.map (W' := W.toAffine) e.toAlgHom
      invFun := Affine.Point.map (W' := W.toAffine) e.symm.toAlgHom
      left_inv := fun P => ?_
      right_inv := fun P => ?_ }
  · cases P with
    | zero => rfl
    | some h => simp [Affine.Point.map_some]
  · cases P with
    | zero => rfl
    | some h => simp [Affine.Point.map_some]

/-- `W` base changed to `k` itself is `W`. -/
theorem baseChange_self {k : Type*} [Field k] (W : WeierstrassCurve k) : W.baseChange k = W := by
  simp [WeierstrassCurve.baseChange, Algebra.algebraMap_self, WeierstrassCurve.map_id]

/-- `#W(𝔽_q) = #W(k₁)` for Mathlib's chosen degree-one extension `k₁ = Extension k p 1`. -/
theorem natCard_point_extension_one {k : Type*} [Field k] [Finite k] (p : ℕ) [Fact p.Prime]
    [CharP k p] (W : WeierstrassCurve k) :
    Nat.card (W.baseChange (FiniteField.Extension k p 1)).toAffine.Point =
      Nat.card W.toAffine.Point := by
  rw [natCard_point_congr W (FiniteField.algEquivExtension k p 1 k (Module.finrank_self k)).symm,
    baseChange_self]

end Lagrange

end RamanujanWeil.Ihara
