import RamanujanWeil.Ihara.SymCore
import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CharpolyTracePowers

/-!
# M5, part 2: eigenvalues of `Sym¹⁰` and the arithmetic of `X² − aX + q`

Pure linear algebra; the only non-Mathlib input is Newton's identities for matrices
(`Stacks.EtaleCohomology.matrix_charpoly_eq_of_trace_pow_eq`, char 0).

* `trace_pow_add_two`: `tr G^{m+2} = tr G · tr G^{m+1} − det G · tr G^m` for `G ∈ M₂(R)`.
* `charpoly_symMat_ten`: over `ℂ`, if `α + β = tr G` and `αβ = det G` then
  `charpoly(Sym¹⁰ G) = ∏_{b ≤ 10} (X − αᵇ β¹⁰⁻ᵇ)`.
* `norm_sq_eq_of_sq_le`: `α + β = a`, `αβ = q` real, `a² ≤ 4q` ⟹ `‖α‖² = q` (Hasse ⟹ purity).
* `trace_pow_of_charpoly`: `charpoly g = X² − aX + q` with `a, q ∈ ℤ` ⟹ `tr gᵐ = s_m(a, q) ∈ ℤ`
  (`powSum a q m`, the power sums `αᵐ + βᵐ`).
-/

open Polynomial Finset

namespace RamanujanWeil.Ihara

section TwoByTwo

variable {R : Type*} [CommRing R]

theorem sq_fin_two_eq (G : Matrix (Fin 2) (Fin 2) R) :
    G ^ 2 = G.trace • G - G.det • (1 : Matrix (Fin 2) (Fin 2) R) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sq, Matrix.mul_apply, Fin.sum_univ_two, Matrix.trace_fin_two, Matrix.det_fin_two] <;> ring

/-- Cayley–Hamilton for traces of powers of a `2 × 2` matrix. -/
theorem trace_pow_add_two (G : Matrix (Fin 2) (Fin 2) R) (m : ℕ) :
    (G ^ (m + 2)).trace = G.trace * (G ^ (m + 1)).trace - G.det * (G ^ m).trace := by
  rw [pow_add, sq_fin_two_eq, Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_smul, Matrix.mul_one,
    Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_smul, ← pow_succ, smul_eq_mul, smul_eq_mul]

/-- `tr Gᵐ = αᵐ + βᵐ` when `α + β = tr G`, `αβ = det G`. -/
theorem trace_pow_eq_add_pow (G : Matrix (Fin 2) (Fin 2) R) (α β : R) (hs : α + β = G.trace)
    (hp : α * β = G.det) (m : ℕ) : (G ^ m).trace = α ^ m + β ^ m := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    match m, ih with
    | 0, _ => simp; norm_num
    | 1, _ => simp [hs]
    | m + 2, ih =>
      rw [trace_pow_add_two, ih (m + 1) (by omega), ih m (by omega), ← hs, ← hp]
      ring

/-- The power sums `s_m = αᵐ + βᵐ` of the roots of `X² − aX + q`, over `ℤ`. -/
def powSum (a q : ℤ) : ℕ → ℤ
  | 0 => 2
  | 1 => a
  | m + 2 => a * powSum a q (m + 1) - q * powSum a q m

theorem trace_pow_eq_powSum (G : Matrix (Fin 2) (Fin 2) R) (a q : ℤ) (ha : G.trace = a)
    (hq : G.det = q) (m : ℕ) : (G ^ m).trace = (powSum a q m : R) := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    match m, ih with
    | 0, _ => simp [powSum]
    | 1, _ => simp [ha, powSum]
    | m + 2, ih =>
      rw [trace_pow_add_two, ih (m + 1) (by omega), ih m (by omega), ha, hq, powSum]
      push_cast; ring

theorem symMat_map {S : Type*} [CommRing S] (f : R →+* S) (n : ℕ) (G : Matrix (Fin 2) (Fin 2) R) :
    (symMat n G).map f = symMat n (G.map f) := by
  ext a b
  simp [symMat, symEntry, map_sum, apply_ite f]

theorem symTraceR_map {S : Type*} [CommRing S] (f : R →+* S) (k : ℕ) (a q : R) :
    f (symTraceR k a q) = symTraceR k (f a) (f q) := by
  simp [symTraceR, map_sum]

/-- `tr (Sym¹⁰ G)ᵐ = symTrace 10 (tr Gᵐ) (det G)ᵐ`. -/
theorem trace_symMat_ten_pow (G : Matrix (Fin 2) (Fin 2) R) (m : ℕ) :
    ((symMat 10 G) ^ m).trace = symTraceR 10 (G ^ m).trace (G.det ^ m) := by
  rw [← symMat_pow, trace_symMat_ten, Matrix.det_pow]

end TwoByTwo

section Complex

/-- **The eigenvalues of `Sym¹⁰ G`** over `ℂ` are `αᵇ β¹⁰⁻ᵇ`. -/
theorem charpoly_symMat_ten (G : Matrix (Fin 2) (Fin 2) ℂ) (α β : ℂ) (hs : α + β = G.trace)
    (hp : α * β = G.det) :
    (symMat 10 G).charpoly = ∏ b : Fin 11, (X - C (α ^ (b : ℕ) * β ^ (10 - (b : ℕ)))) := by
  rw [← Matrix.charpoly_diagonal]
  refine Stacks.EtaleCohomology.matrix_charpoly_eq_of_trace_pow_eq _ _ rfl fun k _ => ?_
  rw [trace_symMat_ten_pow, trace_pow_eq_add_pow G α β hs hp, Matrix.diagonal_pow,
    Matrix.trace_diagonal, ← hp, mul_pow, ← sum_pow_mul_pow_eq_symTraceR_ten]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Pi.pow_apply, mul_pow, ← pow_mul, ← pow_mul, ← pow_mul, ← pow_mul, mul_comm k, mul_comm k]

theorem natDegree_quadratic_monic {K : Type*} [Field K] (a q : K) :
    (X ^ 2 - C a * X + C q).natDegree = 2 := by
  have : (X ^ 2 - C a * X + C q : K[X]) = C 1 * X ^ 2 + C (-a) * X + C q := by
    simp only [map_one, one_mul, map_neg, neg_mul]; ring
  rw [this, natDegree_quadratic one_ne_zero]

theorem exists_add_mul_eq (t c : ℂ) : ∃ α β : ℂ, α + β = t ∧ α * β = c := by
  obtain ⟨α, hα⟩ := Complex.exists_root (f := X ^ 2 - C t * X + C c)
    (natDegree_pos_iff_degree_pos.1 (by rw [natDegree_quadratic_monic]; norm_num))
  refine ⟨α, t - α, by ring, ?_⟩
  simp only [IsRoot, eval_add, eval_sub, eval_mul, eval_pow, eval_X, eval_C] at hα
  linear_combination -hα

/-- **Hasse ⟹ purity**: if `α + β = a` and `αβ = q` are real with `a² ≤ 4q`, then `‖α‖² = q`. -/
theorem norm_sq_eq_of_sq_le (α β : ℂ) (a q : ℝ) (hs : α + β = a) (hp : α * β = q)
    (hd : a ^ 2 ≤ 4 * q) : ‖α‖ ^ 2 = q := by
  have hβ : β = a - α := by rw [← hs]; ring
  rw [hβ] at hp
  have hre := congrArg Complex.re hp
  have him := congrArg Complex.im hp
  simp only [Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im, Complex.ofReal_re,
    Complex.ofReal_im] at hre him
  rw [Complex.sq_norm, Complex.normSq_apply]
  set x := α.re
  set y := α.im
  -- him : x * (0 - y) + y * (a - x) = 0, i.e. y (a - 2x) = 0
  have h1 : y * (a - 2 * x) = 0 := by linarith
  rcases mul_eq_zero.1 h1 with hy | hx
  · rw [hy] at hre ⊢
    -- x (a - x) = q and a² ≤ 4q force (a - 2x)² ≤ 0
    have : (a - 2 * x) ^ 2 ≤ 0 := by nlinarith
    have hx : a - 2 * x = 0 := by nlinarith [sq_nonneg (a - 2 * x)]
    nlinarith
  · have : a = 2 * x := by linarith
    subst this
    nlinarith

theorem trace_det_of_charpoly {K : Type*} [Field K] (G : Matrix (Fin 2) (Fin 2) K) (a q : K)
    (h : G.charpoly = X ^ 2 - C a * X + C q) : G.trace = a ∧ G.det = q := by
  refine ⟨?_, ?_⟩
  · rw [Matrix.trace_eq_neg_charpoly_coeff, h]
    simp [coeff_X, coeff_C]
  · rw [Matrix.det_eq_sign_charpoly_coeff, h]
    simp [coeff_X, coeff_C]

end Complex

end RamanujanWeil.Ihara
