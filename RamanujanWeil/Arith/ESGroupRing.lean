import RamanujanWeil.Arith.ESPeriod
import Mathlib.Algebra.MonoidAlgebra.Basic

/-!
# A2 / ES-P3: the Hecke algebra `ℚ[M₂(ℤ)]` acting on `V₁₀` (docs/ARITH_ES_PLAN.md, §2 P3)

`R := MonoidAlgebra ℚ M2` (finite formal combinations of integer matrices). The right action
`P ↦ P|M` extends to an algebra anti-homomorphism `actR : R → End V`
(`actR (x * y) = actR y ∘ₗ actR x`), and `actR (−M) = actR M`, so identities in
Popa–Zagier's `ℚ[M_n / ±1]` may be checked after any choice of signs.
-/

open Finset Module Matrix

namespace RamanujanWeil.Arith.ES

open M2

/-- The group ring of integer `2 × 2` matrices. -/
abbrev R := MonoidAlgebra ℚ M2

/-- `M ↦ op (P ↦ P|M)` as a monoid hom into the opposite endomorphism algebra. -/
noncomputable def actHom : M2 →* (Module.End ℚ V)ᵐᵒᵖ where
  toFun M := MulOpposite.op (rAct M)
  map_one' := by rw [rAct_one]; rfl
  map_mul' M N := by
    rw [rAct_mul, ← MulOpposite.op_mul]; rfl

/-- The action of the group ring, as an algebra map to the opposite algebra. -/
noncomputable def actAlg : R →ₐ[ℚ] (Module.End ℚ V)ᵐᵒᵖ :=
  MonoidAlgebra.lift ℚ (Module.End ℚ V)ᵐᵒᵖ M2 actHom

/-- `P ↦ P|x` for `x ∈ ℚ[M₂(ℤ)]`. -/
noncomputable def actR (x : R) : V →ₗ[ℚ] V := (actAlg x).unop

@[simp] lemma actR_of (M : M2) : actR (MonoidAlgebra.of ℚ M2 M) = rAct M := by
  simp [actR, actAlg, actHom]

lemma actR_single (M : M2) (r : ℚ) : actR (MonoidAlgebra.single M r) = r • rAct M := by
  simp [actR, actAlg, actHom, MonoidAlgebra.lift_single]

lemma actR_mul (x y : R) : actR (x * y) = actR y ∘ₗ actR x := by
  simp only [actR, map_mul, MulOpposite.unop_mul]; rfl

lemma actR_add (x y : R) : actR (x + y) = actR x + actR y := by
  simp [actR]

lemma actR_smul (r : ℚ) (x : R) : actR (r • x) = r • actR x := by
  simp [actR]

lemma actR_zero : actR 0 = 0 := by simp [actR]

lemma actR_sum {ι : Type*} (s : Finset ι) (f : ι → R) :
    actR (∑ i ∈ s, f i) = ∑ i ∈ s, actR (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [actR_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, actR_add, ih]

lemma actR_one : actR 1 = LinearMap.id := by
  simp [actR]; rfl

/-- **Trace of a group-ring element**: `tr (·|Σ c_M M) = Σ c_M · Sym¹⁰(tr M, det M)`. -/
theorem trace_actR_sum {ι : Type*} (s : Finset ι) (c : ι → ℚ) (M : ι → M2) :
    LinearMap.trace ℚ V (actR (∑ i ∈ s, c i • MonoidAlgebra.of ℚ M2 (M i))) =
      ∑ i ∈ s, c i * (symTr10 (M i).tr (M i).det : ℚ) := by
  rw [actR_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [actR_smul, actR_of, map_smul, smul_eq_mul, ← trace_act]
  congr 1
  rw [rAct, Matrix.vecMulLinear, LinearMap.trace_eq_matrix_trace ℚ (Pi.basisFun ℚ (Fin 11)),
    ← Matrix.trace_transpose]
  congr 1
  ext i j
  simp [LinearMap.toMatrix_apply, Matrix.vecMul, dotProduct, Pi.single_apply]

end RamanujanWeil.Arith.ES
