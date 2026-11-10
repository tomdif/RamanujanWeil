import RamanujanWeil.Arith.DeuringG1Descent

/-!
# A3-ord, descent: Lang's theorem for Weierstrass coordinate changes

`docs/ARITH_DEURING_DESCENT.md` §3. Let `K = 𝔽_q`, `F = frobQ : x ↦ x^q` on `K̄`. Every
`γ ∈ VariableChange(K̄)` is a Frobenius coboundary: `F(δ) = δ γ` for some `δ`
(`exists_map_frobQ_eq_mul`). Componentwise this is `u^{q-1} = γ_u` and three equations
`x^q = a x + b`, all solvable since `K̄` is algebraically closed and `q ≥ 2`.

Consequently (`exists_frobFixed_smul`), if `γ • C^F = C` for a Weierstrass curve `C` over `K̄`,
then `δ • C` is Frobenius-fixed, hence (`exists_map_eq_of_map_frobQ_eq`) the base change of a
Weierstrass curve over `K`.
-/

open Polynomial WeierstrassCurve

namespace RamanujanWeil.Arith.Deuring.Descent

open RamanujanWeil.Arith.Deuring.Geom.Descent

variable {K : Type*} [Field K] [Fintype K]

local notation "K̄" => AlgebraicClosure K

theorem two_le_card : 2 ≤ Fintype.card K := Fintype.one_lt_card

/-- `x^q = a x + b` is solvable in `K̄`. -/
theorem exists_pow_card_eq (a b : K̄) : ∃ x : K̄, x ^ Fintype.card K = a * x + b := by
  set q := Fintype.card K
  have hq : 2 ≤ q := two_le_card
  let P : K̄[X] := X ^ q - (C a * X + C b)
  have hdeg : P.degree = q := by
    have h1 : (C a * X + C b : K̄[X]).degree < (X ^ q : K̄[X]).degree := by
      rw [degree_X_pow]
      refine lt_of_le_of_lt (degree_linear_le) ?_
      exact_mod_cast (by omega : 1 < q)
    rw [degree_sub_eq_left_of_degree_lt h1, degree_X_pow]
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_root P (by rw [hdeg]; exact_mod_cast (by omega : q ≠ 0))
  refine ⟨x, ?_⟩
  have : P.eval x = 0 := hx
  simp only [P, eval_sub, eval_pow, eval_X, eval_add, eval_mul, eval_C] at this
  exact sub_eq_zero.mp this

/-- `u^{q-1} = a` is solvable by a unit for `a ≠ 0`. -/
theorem exists_unit_pow (a : K̄ˣ) : ∃ u : K̄ˣ, (u : K̄) ^ Fintype.card K = u * a := by
  set q := Fintype.card K
  have hq : 2 ≤ q := two_le_card
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_pow_nat_eq (a : K̄) (by omega : 0 < q - 1)
  have hx0 : x ≠ 0 := by
    rintro rfl
    rw [zero_pow (by omega)] at hx
    exact a.ne_zero hx.symm
  refine ⟨Units.mk0 x hx0, ?_⟩
  show x ^ q = x * a
  rw [← hx, ← pow_succ']
  congr 1
  omega

/-- **Lang's theorem for `VariableChange(K̄)`**: `F(δ) = δ γ` is solvable. -/
theorem exists_map_frobQ_eq_mul (γ : VariableChange K̄) :
    ∃ δ : VariableChange K̄, δ.map frobQ = δ * γ := by
  obtain ⟨u, hu⟩ := exists_unit_pow (K := K) γ.u
  obtain ⟨r, hr⟩ := exists_pow_card_eq (K := K) ((γ.u : K̄) ^ 2) γ.r
  obtain ⟨s, hs⟩ := exists_pow_card_eq (K := K) (γ.u : K̄) γ.s
  obtain ⟨t, ht⟩ := exists_pow_card_eq (K := K) ((γ.u : K̄) ^ 3) (r * γ.s * (γ.u : K̄) ^ 2 + γ.t)
  refine ⟨⟨u, r, s, t⟩, ?_⟩
  ext
  · show frobQ (u : K̄) = (u : K̄) * γ.u
    rw [frobQ_apply, hu]
  · show frobQ r = r * (γ.u : K̄) ^ 2 + γ.r
    rw [frobQ_apply, hr, mul_comm]
  · show frobQ s = (γ.u : K̄) * s + γ.s
    rw [frobQ_apply, hs]
  · show frobQ t = t * (γ.u : K̄) ^ 3 + r * γ.s * (γ.u : K̄) ^ 2 + γ.t
    rw [frobQ_apply, ht]
    ring

/-- **Lang descent of a Weierstrass curve.** If `γ • C^F = C`, there is `δ` with `δ • C`
Frobenius-fixed, `F(δ) = δ γ`. -/
theorem exists_frobFixed_smul (C : WeierstrassCurve K̄) (γ : VariableChange K̄)
    (hγ : γ • C.map frobQ = C) :
    ∃ δ : VariableChange K̄, δ.map frobQ = δ * γ ∧ (δ • C).map frobQ = δ • C := by
  obtain ⟨δ, hδ⟩ := exists_map_frobQ_eq_mul γ
  refine ⟨δ, hδ, ?_⟩
  rw [← map_variableChange, hδ, mul_smul, hγ]

/-- A Frobenius-fixed Weierstrass curve over `K̄` comes from `K`. -/
theorem exists_map_eq_of_map_frobQ_eq (C : WeierstrassCurve K̄) (h : C.map frobQ = C) :
    ∃ W : WeierstrassCurve K, W.map (algebraMap K K̄) = C := by
  have h1 : frobQ C.a₁ = C.a₁ := congrArg WeierstrassCurve.a₁ h
  have h2 : frobQ C.a₂ = C.a₂ := congrArg WeierstrassCurve.a₂ h
  have h3 : frobQ C.a₃ = C.a₃ := congrArg WeierstrassCurve.a₃ h
  have h4 : frobQ C.a₄ = C.a₄ := congrArg WeierstrassCurve.a₄ h
  have h6 : frobQ C.a₆ = C.a₆ := congrArg WeierstrassCurve.a₆ h
  obtain ⟨a₁, e₁⟩ := (frobQ_eq_iff _).mp h1
  obtain ⟨a₂, e₂⟩ := (frobQ_eq_iff _).mp h2
  obtain ⟨a₃, e₃⟩ := (frobQ_eq_iff _).mp h3
  obtain ⟨a₄, e₄⟩ := (frobQ_eq_iff _).mp h4
  obtain ⟨a₆, e₆⟩ := (frobQ_eq_iff _).mp h6
  refine ⟨⟨a₁, a₂, a₃, a₄, a₆⟩, ?_⟩
  ext <;> simp [e₁, e₂, e₃, e₄, e₆]

end RamanujanWeil.Arith.Deuring.Descent
