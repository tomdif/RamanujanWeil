import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Tactic

/-!
# A2 / ES-P1: integer `2 × 2` matrices acting on `V₁₀` (docs/ARITH_ES_PLAN.md, §2 P1)

`V₁₀` = homogeneous polynomials of degree 10 in `X, Y`, coordinates `P = Σ_j P_j X^j Y^{10-j}`,
modelled as row vectors `Fin 11 → ℚ`. A matrix `M = [[a, b], [c, d]]` acts on the right by
`(P|M)(X, Y) = P(aX + bY, cX + dY)` (Popa–Zagier's convention), i.e. `P|M = P ᵥ* act M` with

  `act M j i = [X^i Y^{10-i}] (aX + bY)^j (cX + dY)^{10-j}`.

Main results:
* `act_hom`   : `Σ_i act M j i x^i y^{10-i} = (a x + b y)^j (c x + d y)^{10-j}`;
* `act_mul`   : `act (M * N) = act M * act N` (so `P|M|N = P|MN`, a right action);
* `act_neg`   : `act (-M) = act M` (so the action factors through matrices modulo `±1`);
* `trace_act` : `tr (act M) = symTr10 (tr M) (det M)` (Gegenbauer / `Sym¹⁰` trace),
  where `symTr10` is verbatim `RamanujanWeil.Ihara.symTrace 10`.
-/

open Finset

namespace RamanujanWeil.Arith.ES

/-- An integer `2 × 2` matrix `[[a, b], [c, d]]`. -/
@[ext]
structure M2 where
  a : ℤ
  b : ℤ
  c : ℤ
  d : ℤ
  deriving DecidableEq, Repr

namespace M2

instance : Mul M2 := ⟨fun M N => ⟨M.a * N.a + M.b * N.c, M.a * N.b + M.b * N.d,
  M.c * N.a + M.d * N.c, M.c * N.b + M.d * N.d⟩⟩
instance : One M2 := ⟨⟨1, 0, 0, 1⟩⟩
instance : Neg M2 := ⟨fun M => ⟨-M.a, -M.b, -M.c, -M.d⟩⟩

@[simp] lemma mul_a (M N : M2) : (M * N).a = M.a * N.a + M.b * N.c := rfl
@[simp] lemma mul_b (M N : M2) : (M * N).b = M.a * N.b + M.b * N.d := rfl
@[simp] lemma mul_c (M N : M2) : (M * N).c = M.c * N.a + M.d * N.c := rfl
@[simp] lemma mul_d (M N : M2) : (M * N).d = M.c * N.b + M.d * N.d := rfl
@[simp] lemma one_a : (1 : M2).a = 1 := rfl
@[simp] lemma one_b : (1 : M2).b = 0 := rfl
@[simp] lemma one_c : (1 : M2).c = 0 := rfl
@[simp] lemma one_d : (1 : M2).d = 1 := rfl
@[simp] lemma neg_a (M : M2) : (-M).a = -M.a := rfl
@[simp] lemma neg_b (M : M2) : (-M).b = -M.b := rfl
@[simp] lemma neg_c (M : M2) : (-M).c = -M.c := rfl
@[simp] lemma neg_d (M : M2) : (-M).d = -M.d := rfl

/-- Determinant. -/
def det (M : M2) : ℤ := M.a * M.d - M.b * M.c
/-- Trace. -/
def tr (M : M2) : ℤ := M.a + M.d

lemma det_mul (M N : M2) : (M * N).det = M.det * N.det := by
  simp only [det, mul_a, mul_b, mul_c, mul_d]; ring

instance : Monoid M2 where
  mul_assoc M N P := by ext <;> simp <;> ring
  one_mul M := by ext <;> simp
  mul_one M := by ext <;> simp

/-- `S = [[0, -1], [1, 0]]`. -/
def S : M2 := ⟨0, -1, 1, 0⟩
/-- `U = [[1, -1], [1, 0]]` (order 3 modulo `±1`). -/
def U : M2 := ⟨1, -1, 1, 0⟩
/-- `T = [[1, 1], [0, 1]] = U S`. -/
def T : M2 := ⟨1, 1, 0, 1⟩
/-- `ε = [[-1, 0], [0, 1]]`. -/
def eps : M2 := ⟨-1, 0, 0, 1⟩

lemma T_eq_neg_U_mul_S : T = -(U * S) := by decide

end M2

open M2

/-- Matrix coefficient of the action: `[X^i Y^{10-i}] (aX + bY)^j (cX + dY)^{10-j}`. -/
def actC (M : M2) (j i : ℕ) : ℚ :=
  ∑ l ∈ range (j + 1), ∑ m ∈ range (10 - j + 1),
    if l + m = i then
      ((j.choose l : ℚ) * ((10 - j).choose m : ℚ)) * (M.a : ℚ) ^ l * (M.b : ℚ) ^ (j - l) *
        (M.c : ℚ) ^ m * (M.d : ℚ) ^ (10 - j - m)
    else 0

/-- The action matrix on `V₁₀` (row-vector convention `P|M = P ᵥ* act M`). -/
def act (M : M2) : Matrix (Fin 11) (Fin 11) ℚ := fun j i => actC M j i

/-- `Sym¹⁰` trace; verbatim the formula of `RamanujanWeil.Ihara.symTrace 10`. -/
def symTr10 (t n : ℤ) : ℤ :=
  ∑ j ∈ range (10 / 2 + 1), (-n) ^ j * ((10 - j).choose j : ℤ) * t ^ (10 - 2 * j)

/-- Sum over `Fin 11` as a sum over `range 11`. -/
lemma sum_fin11 (f : ℕ → ℚ) : ∑ i : Fin 11, f i = ∑ i ∈ range 11, f i :=
  Fin.sum_univ_eq_sum_range f 11

/-- **The defining identity**: `Σ_i act M j i x^i y^{10-i} = (ax + by)^j (cx + dy)^{10-j}`. -/
theorem act_hom (M : M2) (j : Fin 11) (x y : ℚ) :
    ∑ i : Fin 11, act M j i * x ^ (i : ℕ) * y ^ (10 - (i : ℕ)) =
      ((M.a : ℚ) * x + (M.b : ℚ) * y) ^ (j : ℕ) * ((M.c : ℚ) * x + (M.d : ℚ) * y) ^ (10 - (j : ℕ)) := by
  have hj : (j : ℕ) ≤ 10 := Nat.lt_succ_iff.mp j.isLt
  show ∑ i : Fin 11, actC M j i * x ^ (i : ℕ) * y ^ (10 - (i : ℕ)) = _
  rw [sum_fin11 (fun i => actC M j i * x ^ i * y ^ (10 - i))]
  rw [add_pow, add_pow, Finset.sum_mul_sum]
  simp only [actC, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l hl => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hl' : l ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hl)
  have hm' : m < 10 - (j : ℕ) + 1 := Finset.mem_range.mp hm
  have hlm : l + m < 11 := by omega
  rw [Finset.sum_eq_single (l + m)]
  · rw [if_pos rfl]
    have e1 : 10 - (l + m) = (j - l) + (10 - j - m) := by omega
    rw [e1, pow_add]
    ring
  · intro i _ hi
    rw [if_neg (Ne.symm hi)]; ring
  · intro h; exact absurd (Finset.mem_range.mpr hlm) h

/-- Uniqueness of coefficients: two rows with the same `y = 1` evaluations on `ℚ` agree. -/
lemma row_eq_of_eval (u v : Fin 11 → ℚ)
    (h : ∀ x : ℚ, ∑ i : Fin 11, u i * x ^ (i : ℕ) = ∑ i : Fin 11, v i * x ^ (i : ℕ)) : u = v := by
  classical
  let p : Polynomial ℚ := ∑ i : Fin 11, Polynomial.C (u i - v i) * Polynomial.X ^ (i : ℕ)
  have hp : p = 0 := by
    apply Polynomial.funext
    intro x
    simp only [p, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_zero, sub_mul,
      Finset.sum_sub_distrib, h x, sub_self]
  funext i
  have hc := congrArg (fun q => Polynomial.coeff q (i : ℕ)) hp
  simp only [p, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
    Polynomial.coeff_zero] at hc
  rw [Finset.sum_eq_single i] at hc
  · simpa [sub_eq_zero] using hc
  · intro b _ hb
    have : (i : ℕ) ≠ (b : ℕ) := fun h => hb (Fin.ext h).symm
    simp [this]
  · simp

/-- **Right action**: `act (M * N) = act M * act N`. -/
theorem act_mul (M N : M2) : act (M * N) = act M * act N := by
  ext j i
  revert i
  rw [← funext_iff]
  apply row_eq_of_eval
  intro x
  have hj : (j : ℕ) ≤ 10 := Nat.lt_succ_iff.mp j.isLt
  have h1 := act_hom (M * N) j x 1
  simp only [one_pow, mul_one] at h1
  rw [h1]
  simp only [Matrix.mul_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  have h2 : ∀ k : Fin 11, ∑ i : Fin 11, act M j k * act N k i * x ^ (i : ℕ) =
      act M j k * (((N.a : ℚ) * x + (N.b : ℚ)) ^ (k : ℕ) *
        ((N.c : ℚ) * x + (N.d : ℚ)) ^ (10 - (k : ℕ))) := by
    intro k
    have := act_hom N k x 1
    simp only [one_pow, mul_one] at this
    rw [← this, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  simp only [h2]
  have h3 := act_hom M j ((N.a : ℚ) * x + N.b) ((N.c : ℚ) * x + N.d)
  have h3' : ∑ k : Fin 11, act M j k * (((N.a : ℚ) * x + (N.b : ℚ)) ^ (k : ℕ) *
      ((N.c : ℚ) * x + (N.d : ℚ)) ^ (10 - (k : ℕ))) =
      ((M.a : ℚ) * ((N.a : ℚ) * x + N.b) + (M.b : ℚ) * ((N.c : ℚ) * x + N.d)) ^ (j : ℕ) *
      ((M.c : ℚ) * ((N.a : ℚ) * x + N.b) + (M.d : ℚ) * ((N.c : ℚ) * x + N.d)) ^ (10 - (j : ℕ)) := by
    rw [← h3]; exact Finset.sum_congr rfl fun k _ => by ring
  rw [h3']
  simp only [M2.mul_a, M2.mul_b, M2.mul_c, M2.mul_d, Int.cast_add, Int.cast_mul]
  ring

/-- The action of `-M` equals that of `M` (weight 10 is even). -/
theorem act_neg (M : M2) : act (-M) = act M := by
  ext j i
  revert i
  rw [← funext_iff]
  apply row_eq_of_eval
  intro x
  have hj : (j : ℕ) ≤ 10 := Nat.lt_succ_iff.mp j.isLt
  have h1 := act_hom (-M) j x 1
  have h2 := act_hom M j x 1
  simp only [one_pow, mul_one] at h1 h2
  rw [h1, h2]
  simp only [M2.neg_a, M2.neg_b, M2.neg_c, M2.neg_d, Int.cast_neg]
  have e : (-(M.a : ℚ) * x + -(M.b : ℚ)) ^ (j : ℕ) * (-(M.c : ℚ) * x + -(M.d : ℚ)) ^ (10 - (j : ℕ))
      = ((-1) ^ ((j : ℕ) + (10 - (j : ℕ)))) * (((M.a : ℚ) * x + M.b) ^ (j : ℕ) *
        ((M.c : ℚ) * x + M.d) ^ (10 - (j : ℕ))) := by
    rw [pow_add]
    have ha : -(M.a : ℚ) * x + -(M.b : ℚ) = (-1) * ((M.a : ℚ) * x + M.b) := by ring
    have hc : -(M.c : ℚ) * x + -(M.d : ℚ) = (-1) * ((M.c : ℚ) * x + M.d) := by ring
    rw [ha, hc, mul_pow, mul_pow]; ring
  rw [e, show (j : ℕ) + (10 - (j : ℕ)) = 10 by omega]
  norm_num

/-- **Trace**: `tr (act M) = Sym¹⁰`-trace of `M`. -/
theorem trace_act (M : M2) : Matrix.trace (act M) = (symTr10 M.tr M.det : ℚ) := by
  simp only [Matrix.trace, Matrix.diag, act]
  rw [sum_fin11 (fun j => actC M j j)]
  simp only [actC, symTr10, M2.tr, M2.det, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [Nat.choose]
  ring

end RamanujanWeil.Arith.ES
