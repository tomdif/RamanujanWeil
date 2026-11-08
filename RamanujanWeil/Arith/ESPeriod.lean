import RamanujanWeil.Arith.ESAction
import Mathlib.LinearAlgebra.Trace
import Mathlib.LinearAlgebra.Projection
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# A2 / ES-P2: the period space `W₁₀` and the trace lemma (docs/ARITH_ES_PLAN.md, §2 P2)

* `rAct M : V →ₗ V`, `P ↦ P|M = P ᵥ* act M` (right action: `rAct (M * N) = rAct N ∘ₗ rAct M`).
* `Aker = ker(1 + S)`, `Bker = ker(1 + U + U²)`, `Wper = Aker ⊓ Bker` (period polynomials).
* `Aker ⊔ Bker = ⊤` (`sup_eq_top`, explicit decompositions of the 11 unit vectors).
* `Wper = span {e0, pplus, pminus}`, `finrank Wper = 3`, where (coefficients of `X^j Y^{10-j}`,
  `j = 0, …, 10`) `e0 = X¹⁰ − Y¹⁰`, `pplus = X²Y²(X² − Y²)³`, and `pminus` is the odd period
  polynomial `XY⁹ − 25/4 X³Y⁷ + 21/2 X⁵Y⁵ − 25/4 X⁷Y³ + X⁹Y` of `Δ` (up to a scalar).
* `trace_eq_trace_restrict_inf` (Popa–Zagier Prop. 3, abstract form): if `A ⊔ B = ⊤` and `f`
  maps `A → B` and `B → A`, then `tr f = tr (f|_{A ⊓ B})`.
-/

open Finset Module Matrix

namespace RamanujanWeil.Arith.ES

open M2

/-- `V₁₀` as row vectors. -/
abbrev V := Fin 11 → ℚ

/-- The right action `P ↦ P|M`. -/
def rAct (M : M2) : V →ₗ[ℚ] V := Matrix.vecMulLinear (act M)

lemma rAct_apply (M : M2) (P : V) : rAct M P = P ᵥ* act M := rfl

lemma rAct_mul (M N : M2) : rAct (M * N) = rAct N ∘ₗ rAct M :=
  LinearMap.ext fun P => by simp [rAct_apply, act_mul, Matrix.vecMul_vecMul]

lemma rAct_neg (M : M2) : rAct (-M) = rAct M :=
  LinearMap.ext fun P => by simp [rAct_apply, act_neg]

lemma act_one : act 1 = 1 := by
  ext j k
  revert k
  rw [← funext_iff]
  apply row_eq_of_eval
  intro x
  have h := act_hom 1 j x 1
  simp only [one_pow, mul_one, M2.one_a, M2.one_b, M2.one_c, M2.one_d, Int.cast_one,
    Int.cast_zero, zero_mul, add_zero, zero_add, one_mul, one_pow] at h
  rw [h, Finset.sum_eq_single j]
  · simp
  · intro b _ hb; simp [Matrix.one_apply, Ne.symm hb]
  · simp

lemma rAct_one : rAct 1 = LinearMap.id :=
  LinearMap.ext fun P => by simp [rAct_apply, act_one]

/-- Evaluation of a row vector as a polynomial in `x` (dehomogenised at `y = 1`). -/
def ev (P : V) (x : ℚ) : ℚ := ∑ i : Fin 11, P i * x ^ (i : ℕ)

lemma ev_rAct (M : M2) (P : V) (x : ℚ) :
    ev (rAct M P) x = ∑ j : Fin 11, P j * (((M.a : ℚ) * x + M.b) ^ (j : ℕ) *
      ((M.c : ℚ) * x + M.d) ^ (10 - (j : ℕ))) := by
  simp only [ev, rAct_apply, Matrix.vecMul, dotProduct, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  have h := act_hom M j x 1
  simp only [one_pow, mul_one] at h
  rw [← h, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

lemma eq_of_ev (P Q : V) (h : ∀ x, ev P x = ev Q x) : P = Q := row_eq_of_eval P Q h

/-! ## Explicit matrices of `S`, `U`, `U²` -/

/-- `U² = [[0, -1], [1, -1]]`. -/
def U2 : M2 := ⟨0, -1, 1, -1⟩

lemma U_mul_U : U * U = U2 := by decide

def litS : Matrix (Fin 11) (Fin 11) ℚ :=
  !![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1;
    0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0;
    0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0;
    0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0;
    0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0;
    0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

def litU : Matrix (Fin 11) (Fin 11) ℚ :=
  !![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1;
    0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1;
    0, 0, 0, 0, 0, 0, 0, 0, 1, -2, 1;
    0, 0, 0, 0, 0, 0, 0, -1, 3, -3, 1;
    0, 0, 0, 0, 0, 0, 1, -4, 6, -4, 1;
    0, 0, 0, 0, 0, -1, 5, -10, 10, -5, 1;
    0, 0, 0, 0, 1, -6, 15, -20, 15, -6, 1;
    0, 0, 0, -1, 7, -21, 35, -35, 21, -7, 1;
    0, 0, 1, -8, 28, -56, 70, -56, 28, -8, 1;
    0, -1, 9, -36, 84, -126, 126, -84, 36, -9, 1;
    1, -10, 45, -120, 210, -252, 210, -120, 45, -10, 1]

def litU2 : Matrix (Fin 11) (Fin 11) ℚ :=
  !![1, -10, 45, -120, 210, -252, 210, -120, 45, -10, 1;
    1, -9, 36, -84, 126, -126, 84, -36, 9, -1, 0;
    1, -8, 28, -56, 70, -56, 28, -8, 1, 0, 0;
    1, -7, 21, -35, 35, -21, 7, -1, 0, 0, 0;
    1, -6, 15, -20, 15, -6, 1, 0, 0, 0, 0;
    1, -5, 10, -10, 5, -1, 0, 0, 0, 0, 0;
    1, -4, 6, -4, 1, 0, 0, 0, 0, 0, 0;
    1, -3, 3, -1, 0, 0, 0, 0, 0, 0, 0;
    1, -2, 1, 0, 0, 0, 0, 0, 0, 0, 0;
    1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

/-- The three spanning vectors of `Wper`. -/
def e0 : V := ![-1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
def pplus : V := ![0, 0, -1, 0, 3, 0, -3, 0, 1, 0, 0]
def pminus : V := ![0, 1, 0, -25/4, 0, 21/2, 0, -25/4, 0, 1, 0]

/-- Explicit `A`-parts of the unit vectors (`decA i + decB i = eᵢ`). -/
def decA : Fin 11 → V := ![![(0), (0), (0), (25/4), (0), (-21/2), (0), (25/4), (0), (0), (0)],
    ![(0), (0), (0), (25/8), (3/2), (-21/4), (-3/2), (25/8), (0), (0), (0)],
    ![(0), (0), (0), (11/8), (3/2), (-7/4), (-3/2), (11/8), (0), (0), (0)],
    ![(0), (0), (0), (1/2), (1), (0), (-1), (1/2), (0), (0), (0)],
    ![(0), (0), (0), (1/8), (1/2), (3/4), (-1/2), (1/8), (0), (0), (0)],
    ![(0), (0), (0), (0), (0), (1), (0), (0), (0), (0), (0)],
    ![(0), (0), (0), (1/8), (-1/2), (3/4), (1/2), (1/8), (0), (0), (0)],
    ![(0), (0), (0), (1/2), (-1), (0), (1), (1/2), (0), (0), (0)],
    ![(0), (0), (-1), (11/8), (3/2), (-7/4), (-3/2), (11/8), (1), (0), (0)],
    ![(0), (1), (0), (-25/8), (-3/2), (21/4), (3/2), (-25/8), (0), (1), (0)],
    ![(-1), (0), (0), (25/4), (0), (-21/2), (0), (25/4), (0), (0), (1)]]

/-- Explicit `B`-parts of the unit vectors. -/
def decB : Fin 11 → V := ![![(1), (0), (0), (-25/4), (0), (21/2), (0), (-25/4), (0), (0), (0)],
    ![(0), (1), (0), (-25/8), (-3/2), (21/4), (3/2), (-25/8), (0), (0), (0)],
    ![(0), (0), (1), (-11/8), (-3/2), (7/4), (3/2), (-11/8), (0), (0), (0)],
    ![(0), (0), (0), (1/2), (-1), (0), (1), (-1/2), (0), (0), (0)],
    ![(0), (0), (0), (-1/8), (1/2), (-3/4), (1/2), (-1/8), (0), (0), (0)],
    ![(0), (0), (0), (0), (0), (0), (0), (0), (0), (0), (0)],
    ![(0), (0), (0), (-1/8), (1/2), (-3/4), (1/2), (-1/8), (0), (0), (0)],
    ![(0), (0), (0), (-1/2), (1), (0), (-1), (1/2), (0), (0), (0)],
    ![(0), (0), (1), (-11/8), (-3/2), (7/4), (3/2), (-11/8), (0), (0), (0)],
    ![(0), (-1), (0), (25/8), (3/2), (-21/4), (-3/2), (25/8), (0), (0), (0)],
    ![(1), (0), (0), (-25/4), (0), (21/2), (0), (-25/4), (0), (0), (0)]]

lemma rAct_S (P : V) : rAct S P = P ᵥ* litS := by
  apply eq_of_ev; intro x
  rw [ev_rAct]
  simp [ev, Matrix.vecMul, dotProduct, Fin.sum_univ_succ, litS, S]
  ring

lemma rAct_U (P : V) : rAct U P = P ᵥ* litU := by
  apply eq_of_ev; intro x
  rw [ev_rAct]
  simp [ev, Matrix.vecMul, dotProduct, Fin.sum_univ_succ, litU, U]
  ring

lemma rAct_U2 (P : V) : rAct U2 P = P ᵥ* litU2 := by
  apply eq_of_ev; intro x
  rw [ev_rAct]
  simp [ev, Matrix.vecMul, dotProduct, Fin.sum_univ_succ, litU2, U2]
  ring

/-! ## The period space -/

/-- `ker (1 + S)`. -/
def Aker : Submodule ℚ V := LinearMap.ker (LinearMap.id + rAct S)
/-- `ker (1 + U + U²)`. -/
def Bker : Submodule ℚ V := LinearMap.ker (LinearMap.id + rAct U + rAct U2)
/-- The period polynomials `W₁₀ = ker (1 + S) ∩ ker (1 + U + U²)`. -/
def Wper : Submodule ℚ V := Aker ⊓ Bker

lemma mem_Aker (P : V) : P ∈ Aker ↔ P + P ᵥ* litS = 0 := by
  simp [Aker, rAct_S]

lemma mem_Bker (P : V) : P ∈ Bker ↔ P + P ᵥ* litU + P ᵥ* litU2 = 0 := by
  simp [Bker, rAct_U, rAct_U2]

lemma decA_eq : ∀ i : Fin 11, decA i + decA i ᵥ* litS = 0 := by decide +kernel

lemma decA_mem (i : Fin 11) : decA i ∈ Aker := (mem_Aker _).2 (decA_eq i)

lemma decB_eq : ∀ i : Fin 11, decB i + decB i ᵥ* litU + decB i ᵥ* litU2 = 0 := by
  decide +kernel

lemma decB_mem (i : Fin 11) : decB i ∈ Bker := (mem_Bker _).2 (decB_eq i)

lemma dec_add' : ∀ i k : Fin 11, (decA i + decB i) k = if i = k then 1 else 0 := by
  decide +kernel

lemma dec_add (i : Fin 11) : decA i + decB i = Pi.single i 1 := by
  funext k; rw [dec_add' i k]; simp [Pi.single_apply, eq_comm]

/-- **`A + B = V`** (Popa–Zagier, proof of Prop. 3; here by explicit decomposition). -/
theorem sup_eq_top : Aker ⊔ Bker = ⊤ := by
  rw [eq_top_iff]
  intro P _
  rw [pi_eq_sum_univ P]
  refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_
  have : (fun j => if i = j then (1 : ℚ) else 0) = Pi.single i 1 := by
    funext j; simp [Pi.single_apply, eq_comm]
  rw [this, ← dec_add i]
  exact Submodule.add_mem_sup (decA_mem i) (decB_mem i)

lemma e0_mem : e0 ∈ Wper :=
  ⟨(mem_Aker _).2 (by decide +kernel), (mem_Bker _).2 (by decide +kernel)⟩

lemma pplus_mem : pplus ∈ Wper :=
  ⟨(mem_Aker _).2 (by decide +kernel), (mem_Bker _).2 (by decide +kernel)⟩

lemma pminus_mem : pminus ∈ Wper :=
  ⟨(mem_Aker _).2 (by decide +kernel), (mem_Bker _).2 (by decide +kernel)⟩

lemma vecMul_litS (P : V) : P ᵥ* litS = ![P 10,
      -P 9,
      P 8,
      -P 7,
      P 6,
      -P 5,
      P 4,
      -P 3,
      P 2,
      -P 1,
      P 0] := by
  funext k; fin_cases k <;>
    simp [Matrix.vecMul, dotProduct, Fin.sum_univ_succ, litS] <;> ring

lemma vecMul_litU (P : V) : P ᵥ* litU = ![P 10,
      -P 9 + (-10) * P 10,
      P 8 + (9) * P 9 + (45) * P 10,
      -P 7 + (-8) * P 8 + (-36) * P 9 + (-120) * P 10,
      P 6 + (7) * P 7 + (28) * P 8 + (84) * P 9 + (210) * P 10,
      -P 5 + (-6) * P 6 + (-21) * P 7 + (-56) * P 8 + (-126) * P 9 + (-252) * P 10,
      P 4 + (5) * P 5 + (15) * P 6 + (35) * P 7 + (70) * P 8 + (126) * P 9 + (210) * P 10,
      -P 3 + (-4) * P 4 + (-10) * P 5 + (-20) * P 6 + (-35) * P 7 + (-56) * P 8 + (-84) * P 9 + (-120) * P 10,
      P 2 + (3) * P 3 + (6) * P 4 + (10) * P 5 + (15) * P 6 + (21) * P 7 + (28) * P 8 + (36) * P 9 + (45) * P 10,
      -P 1 + (-2) * P 2 + (-3) * P 3 + (-4) * P 4 + (-5) * P 5 + (-6) * P 6 + (-7) * P 7 + (-8) * P 8 + (-9) * P 9 + (-10) * P 10,
      P 0 + P 1 + P 2 + P 3 + P 4 + P 5 + P 6 + P 7 + P 8 + P 9 + P 10] := by
  funext k; fin_cases k <;>
    simp [Matrix.vecMul, dotProduct, Fin.sum_univ_succ, litU] <;> ring

lemma vecMul_litU2 (P : V) : P ᵥ* litU2 = ![P 0 + P 1 + P 2 + P 3 + P 4 + P 5 + P 6 + P 7 + P 8 + P 9 + P 10,
      (-10) * P 0 + (-9) * P 1 + (-8) * P 2 + (-7) * P 3 + (-6) * P 4 + (-5) * P 5 + (-4) * P 6 + (-3) * P 7 + (-2) * P 8 + -P 9,
      (45) * P 0 + (36) * P 1 + (28) * P 2 + (21) * P 3 + (15) * P 4 + (10) * P 5 + (6) * P 6 + (3) * P 7 + P 8,
      (-120) * P 0 + (-84) * P 1 + (-56) * P 2 + (-35) * P 3 + (-20) * P 4 + (-10) * P 5 + (-4) * P 6 + -P 7,
      (210) * P 0 + (126) * P 1 + (70) * P 2 + (35) * P 3 + (15) * P 4 + (5) * P 5 + P 6,
      (-252) * P 0 + (-126) * P 1 + (-56) * P 2 + (-21) * P 3 + (-6) * P 4 + -P 5,
      (210) * P 0 + (84) * P 1 + (28) * P 2 + (7) * P 3 + P 4,
      (-120) * P 0 + (-36) * P 1 + (-8) * P 2 + -P 3,
      (45) * P 0 + (9) * P 1 + P 2,
      (-10) * P 0 + -P 1,
      P 0] := by
  funext k; fin_cases k <;>
    simp [Matrix.vecMul, dotProduct, Fin.sum_univ_succ, litU2] <;> ring

/-- Every period polynomial is `P₁₀ e0 + P₈ pplus + P₉ pminus`. -/
theorem eq_of_mem_Wper {P : V} (hP : P ∈ Wper) :
    P = P 10 • e0 + P 8 • pplus + P 9 • pminus := by
  have hA := (mem_Aker P).1 (Submodule.mem_inf.1 hP).1
  have hB := (mem_Bker P).1 (Submodule.mem_inf.1 hP).2
  rw [vecMul_litS] at hA
  rw [vecMul_litU, vecMul_litU2] at hB
  have a0 := congrFun hA 0
  have b0 := congrFun hB 0
  have a1 := congrFun hA 1
  have b1 := congrFun hB 1
  have a2 := congrFun hA 2
  have b2 := congrFun hB 2
  have a3 := congrFun hA 3
  have b3 := congrFun hB 3
  have a4 := congrFun hA 4
  have b4 := congrFun hB 4
  have a5 := congrFun hA 5
  have b5 := congrFun hB 5
  have a6 := congrFun hA 6
  have b6 := congrFun hB 6
  have a7 := congrFun hA 7
  have b7 := congrFun hB 7
  have a8 := congrFun hA 8
  have b8 := congrFun hB 8
  have a9 := congrFun hA 9
  have b9 := congrFun hB 9
  have a10 := congrFun hA 10
  have b10 := congrFun hB 10
  simp [Matrix.vecHead, Matrix.vecTail] at a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10
  funext k
  fin_cases k
  · simp [e0, pplus, pminus] <;> linear_combination (1) * a0
  · simp [e0, pplus, pminus] <;> linear_combination (1) * a1
  · simp [e0, pplus, pminus] <;> linear_combination (1) * a2
  · simp [e0, pplus, pminus] <;> linear_combination (-25/4) * a0 + (-25/8) * a1 + (-11/8) * a2 + (1/2) * a3 + (-1/8) * a4 + (25/8) * b0 + (9/8) * b1 + (1/4) * b2
  · simp [e0, pplus, pminus] <;> linear_combination (-3/2) * a1 + (-3/2) * a2 + (-1) * a3 + (1/2) * a4 + (-5/2) * b0 + (-1/2) * b1
  · simp [e0, pplus, pminus] <;> linear_combination (21/2) * a0 + (21/4) * a1 + (7/4) * a2 + (-3/4) * a4 + (-21/4) * b0 + (-9/4) * b1 + (-1/2) * b2
  · simp [e0, pplus, pminus] <;> linear_combination (3/2) * a1 + (3/2) * a2 + (1) * a3 + (1/2) * a4 + (5/2) * b0 + (1/2) * b1
  · simp [e0, pplus, pminus] <;> linear_combination (-25/4) * a0 + (-25/8) * a1 + (-11/8) * a2 + (-1/2) * a3 + (-1/8) * a4 + (25/8) * b0 + (9/8) * b1 + (1/4) * b2
  · simp [e0, pplus, pminus] <;> linear_combination 0
  · simp [e0, pplus, pminus] <;> linear_combination 0
  · simp [e0, pplus, pminus] <;> linear_combination 0

theorem Wper_eq_span : Wper = Submodule.span ℚ (Set.range ![e0, pplus, pminus]) := by
  apply le_antisymm
  · intro P hP
    rw [eq_of_mem_Wper hP]
    refine Submodule.add_mem _ (Submodule.add_mem _ ?_ ?_) ?_ <;>
      refine Submodule.smul_mem _ _ (Submodule.subset_span ?_)
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
    · exact ⟨2, rfl⟩
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    fin_cases i
    · exact e0_mem
    · exact pplus_mem
    · exact pminus_mem

lemma linearIndependent_basis : LinearIndependent ℚ ![e0, pplus, pminus] := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have h10 := congrFun hg 10
  have h8 := congrFun hg 8
  have h9 := congrFun hg 9
  simp [Fin.sum_univ_succ, e0, pplus, pminus] at h10 h8 h9
  intro i; fin_cases i <;> simp <;> linarith

/-- **`dim W₁₀ = 3`** (`= dim M₁₂ + dim S₁₂`). -/
theorem finrank_Wper : finrank ℚ Wper = 3 := by
  rw [Wper_eq_span, finrank_span_eq_card linearIndependent_basis]
  simp

/-! ## Popa–Zagier Proposition 3 (abstract linear algebra) -/

/-- If `A ⊔ B = ⊤` and `f` maps `A` into `B` and `B` into `A`, then `f` preserves `A ⊓ B` and
`tr f = tr (f|_{A ⊓ B})`. -/
theorem trace_eq_trace_restrict_inf {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
    [FiniteDimensional K E] (A B : Submodule K E) (hAB : A ⊔ B = ⊤) (f : E →ₗ[K] E)
    (hA : ∀ x ∈ A, f x ∈ B) (hB : ∀ x ∈ B, f x ∈ A) :
    LinearMap.trace K E f = LinearMap.trace K (A ⊓ B : Submodule K E)
      (f.restrict (p := A ⊓ B) (q := A ⊓ B)
        (fun x hx => Submodule.mem_inf.2 ⟨hB x (Submodule.mem_inf.1 hx).2,
          hA x (Submodule.mem_inf.1 hx).1⟩)) := by
  classical
  obtain ⟨Q, hQ⟩ := (A ⊓ B).exists_isCompl
  -- relative complements `A₁ = A ⊓ Q` of `B`, `B₁ = B ⊓ Q` of `A`
  have key : ∀ (X Y : Submodule K E), X ⊔ Y = ⊤ → IsCompl (X ⊓ Y) Q →
      IsCompl (X ⊓ Q) Y := by
    intro X Y hXY hQ'
    constructor
    · rw [disjoint_iff]
      have : X ⊓ Q ⊓ Y = (X ⊓ Y) ⊓ Q := by
        rw [inf_assoc, inf_comm Q Y, ← inf_assoc]
      rw [this, hQ'.inf_eq_bot]
    · rw [codisjoint_iff]
      have hX : X ⊓ Y ⊔ X ⊓ Q = X := by
        rw [inf_comm X Q, ← sup_inf_assoc_of_le Q (inf_le_left : X ⊓ Y ≤ X), hQ'.sup_eq_top,
          top_inf_eq]
      apply eq_top_iff.2
      rw [← hXY]
      apply sup_le
      · calc X = X ⊓ Y ⊔ X ⊓ Q := hX.symm
          _ ≤ X ⊓ Q ⊔ Y := sup_le (le_sup_of_le_right inf_le_right) le_sup_left
      · exact le_sup_right
  have hA1 : IsCompl (A ⊓ Q) B := key A B hAB hQ
  have hB1 : IsCompl (B ⊓ Q) A := key B A (by rw [sup_comm]; exact hAB) (by rw [inf_comm]; exact hQ)
  set p := (A ⊓ Q).projection B hA1 with hp
  set q := (B ⊓ Q).projection A hB1 with hq
  have p_mem : ∀ x, p x ∈ A := fun x =>
    (Submodule.projection_apply_mem hA1 x : p x ∈ A ⊓ Q).1
  have q_mem : ∀ x, q x ∈ B := fun x =>
    (Submodule.projection_apply_mem hB1 x : q x ∈ B ⊓ Q).1
  have p_zero : ∀ x ∈ B, p x = 0 := fun x hx =>
    (Submodule.projection_apply_eq_zero_iff hA1).2 hx
  have q_zero : ∀ x ∈ A, q x = 0 := fun x hx =>
    (Submodule.projection_apply_eq_zero_iff hB1).2 hx
  have p_sub : ∀ x, x - p x ∈ B := fun x => Submodule.sub_projection_mem hA1 x
  have q_sub : ∀ x, x - q x ∈ A := fun x => Submodule.sub_projection_mem hB1 x
  have pp : p ∘ₗ p = p := (Submodule.isIdempotentElem_projection hA1).eq
  have qq : q ∘ₗ q = q := (Submodule.isIdempotentElem_projection hB1).eq
  set r : E →ₗ[K] E := LinearMap.id - p - q with hr
  have r_mem : ∀ x, r x ∈ A ⊓ B := by
    intro x
    refine Submodule.mem_inf.2 ⟨?_, ?_⟩
    · have : r x = (x - q x) - p x := by
        show x - p x - q x = (x - q x) - p x; abel
      rw [this]; exact Submodule.sub_mem _ (q_sub x) (p_mem x)
    · have : r x = (x - p x) - q x := rfl
      rw [this]; exact Submodule.sub_mem _ (p_sub x) (q_mem x)
  have r_fix : ∀ x ∈ A ⊓ B, r x = x := by
    intro x hx
    have h1 := p_zero x (Submodule.mem_inf.1 hx).2
    have h2 := q_zero x (Submodule.mem_inf.1 hx).1
    simp [hr, h1, h2]
  -- split `f = f r + f p + f q`
  have hsplit : f = f ∘ₗ r + f ∘ₗ p + f ∘ₗ q := by
    ext x
    simp only [LinearMap.add_apply, LinearMap.comp_apply]
    rw [← map_add, ← map_add]
    congr 1
    show x = (x - p x - q x) + p x + q x
    abel
  have tp : LinearMap.trace K E (f ∘ₗ p) = 0 := by
    have : f ∘ₗ p = (f ∘ₗ p) ∘ₗ p := by rw [LinearMap.comp_assoc, pp]
    rw [this, LinearMap.trace_comp_comm']
    have hz : p ∘ₗ (f ∘ₗ p) = 0 := by
      ext x; simp [p_zero _ (hA _ (p_mem x))]
    rw [hz, map_zero]
  have tq : LinearMap.trace K E (f ∘ₗ q) = 0 := by
    have : f ∘ₗ q = (f ∘ₗ q) ∘ₗ q := by rw [LinearMap.comp_assoc, qq]
    rw [this, LinearMap.trace_comp_comm']
    have hz : q ∘ₗ (f ∘ₗ q) = 0 := by
      ext x; simp [q_zero _ (hB _ (q_mem x))]
    rw [hz, map_zero]
  set r' : E →ₗ[K] (A ⊓ B : Submodule K E) := r.codRestrict (A ⊓ B) r_mem
  have hr' : r = (A ⊓ B).subtype ∘ₗ r' := by ext x; rfl
  have tr_ : LinearMap.trace K E (f ∘ₗ r) = LinearMap.trace K (A ⊓ B : Submodule K E)
      (f.restrict (p := A ⊓ B) (q := A ⊓ B)
        (fun x hx => Submodule.mem_inf.2 ⟨hB x (Submodule.mem_inf.1 hx).2,
          hA x (Submodule.mem_inf.1 hx).1⟩)) := by
    rw [hr', ← LinearMap.comp_assoc, LinearMap.trace_comp_comm']
    congr 1
    ext ⟨x, hx⟩
    simp only [LinearMap.comp_apply, Submodule.subtype_apply, LinearMap.restrict_apply]
    simp only [r', LinearMap.codRestrict_apply]
    exact r_fix _ (Submodule.mem_inf.2 ⟨hB x (Submodule.mem_inf.1 hx).2,
      hA x (Submodule.mem_inf.1 hx).1⟩)
  conv_lhs => rw [hsplit]
  rw [map_add, map_add, tp, tq, tr_, add_zero, add_zero]

end RamanujanWeil.Arith.ES
