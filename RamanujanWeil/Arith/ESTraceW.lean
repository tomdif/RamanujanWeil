import RamanujanWeil.Arith.ESGroupRing
import Mathlib.Algebra.MonoidAlgebra.MapDomain

/-!
# A2 / ES-P9a: property (B) ⇒ `tr(T̃ | W₁₀) = tr(T̃ | V₁₀)` (docs/ARITH_ES_PLAN.md, §2 P9)

Popa–Zagier, Proposition 3. Identities in `ℚ[M_n/±1]` are encoded in `R = ℚ[M₂(ℤ)]` after pushing
forward along a sign normalisation `nf : M ↦ ±M` (`mapDomain nf`); the action does not see
`mapDomain nf` (`actR_nf`). Property (B) for `x` reads

  `x(1 + S) ≡ (1 + U + U²) y₁`,   `x(1 + U + U²) ≡ (1 + S) y₂`   (mod `±1`).

Then `x` maps `ker(1+S)` into `ker(1+U+U²)` and back, so by `trace_eq_trace_restrict_inf` and
`sup_eq_top` its trace on `V₁₀` equals its trace on the period space `Wper`.
-/

open Finset Module

namespace RamanujanWeil.Arith.ES

open M2

/-- Sign normalisation: the representative of `±M` with `c > 0`, or `c = 0, d ≥ 0`. -/
def nf (M : M2) : M2 := if M.c < 0 ∨ (M.c = 0 ∧ M.d < 0) then -M else M

lemma rAct_nf (M : M2) : rAct (nf M) = rAct M := by
  unfold nf; split_ifs
  · exact rAct_neg M
  · rfl

/-- The action does not see the sign normalisation. -/
lemma actR_nf (z : R) : actR (MonoidAlgebra.mapDomain nf z) = actR z := by
  induction z using MonoidAlgebra.induction_linear with
  | zero => simp [MonoidAlgebra.mapDomain, actR_zero]
  | add f g hf hg => rw [MonoidAlgebra.mapDomain_add, actR_add, actR_add, hf, hg]
  | single M r =>
    rw [MonoidAlgebra.mapDomain_single, actR_single, actR_single, rAct_nf]

/-- `1 + S`. -/
noncomputable def oneS : R := 1 + MonoidAlgebra.of ℚ M2 S
/-- `1 + U + U²`. -/
noncomputable def oneU : R := 1 + MonoidAlgebra.of ℚ M2 U + MonoidAlgebra.of ℚ M2 U2

lemma actR_oneS : actR oneS = LinearMap.id + rAct S := by
  simp [oneS, actR_add, actR_one, actR_single]

lemma actR_oneU : actR oneU = LinearMap.id + rAct U + rAct U2 := by
  simp [oneU, actR_add, actR_one, actR_single]

/-- Equality in `ℚ[M₂(ℤ)/±1]`. -/
def EqPM (x y : R) : Prop := MonoidAlgebra.mapDomain nf x = MonoidAlgebra.mapDomain nf y

lemma actR_eq_of_EqPM {x y : R} (h : EqPM x y) : actR x = actR y := by
  rw [← actR_nf x, ← actR_nf y, h]

/-- **Property (B)** of Popa–Zagier. -/
def PropB (x : R) : Prop :=
  (∃ y : R, EqPM (x * oneS) (oneU * y)) ∧ (∃ y : R, EqPM (x * oneU) (oneS * y))

lemma mapsTo_A_B {x : R} (hx : PropB x) : ∀ P ∈ Aker, actR x P ∈ Bker := by
  intro P hP
  obtain ⟨y, hy⟩ := hx.2
  have h := congrArg (fun F : V →ₗ[ℚ] V => F P) (actR_eq_of_EqPM hy)
  simp only [actR_mul, LinearMap.comp_apply, actR_oneS, actR_oneU] at h
  show _ ∈ LinearMap.ker _
  rw [LinearMap.mem_ker, h]
  have : (LinearMap.id + rAct S : V →ₗ[ℚ] V) P = 0 := hP
  rw [this, map_zero]

lemma mapsTo_B_A {x : R} (hx : PropB x) : ∀ P ∈ Bker, actR x P ∈ Aker := by
  intro P hP
  obtain ⟨y, hy⟩ := hx.1
  have h := congrArg (fun F : V →ₗ[ℚ] V => F P) (actR_eq_of_EqPM hy)
  simp only [actR_mul, LinearMap.comp_apply, actR_oneS, actR_oneU] at h
  show _ ∈ LinearMap.ker _
  rw [LinearMap.mem_ker, h]
  have : (LinearMap.id + rAct U + rAct U2 : V →ₗ[ℚ] V) P = 0 := hP
  rw [this, map_zero]

/-- **Popa–Zagier Prop. 3** for `V₁₀`: an element with property (B) preserves `W₁₀` and has the
same trace on `W₁₀` as on `V₁₀`. -/
theorem trace_eq_trace_Wper {x : R} (hx : PropB x) :
    LinearMap.trace ℚ V (actR x) = LinearMap.trace ℚ Wper
      ((actR x).restrict (p := Wper) (q := Wper)
        (fun P hP => Submodule.mem_inf.2 ⟨mapsTo_B_A hx P (Submodule.mem_inf.1 hP).2,
          mapsTo_A_B hx P (Submodule.mem_inf.1 hP).1⟩)) :=
  trace_eq_trace_restrict_inf Aker Bker sup_eq_top (actR x) (mapsTo_A_B hx) (mapsTo_B_A hx)

end RamanujanWeil.Arith.ES
