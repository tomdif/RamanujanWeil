import RamanujanWeil.Arith.ESGroupRing

/-!
# A2 / ES-P4: the Popa–Zagier Hecke element `T̃ₙ` (docs/ARITH_ES_PLAN.md, §2 P4)

Popa–Zagier (arXiv:1711.00327, eq. (15)):

  `T̃ = ⟨a−d ≤ −b ≤ c ; 0 ≤ c < a⟩ − ⟨−b ≤ a−d ≤ c ; b < d ≤ 0⟩
        − ⟨0 ≤ a−d ≤ c ≤ −b ; a ≤ 0 < c⟩ − ⟨0 ≤ a−d ≤ −b ≤ c ; d ≤ 0 < −b⟩`,

where `⟨first line ; second line⟩` sums the matrices `[[a,b],[c,d]]` satisfying both lines, with
weight `1` if no first-line inequality is an equality, `1/2` for one equality, and for two
equalities `1/6` if they are adjacent in the chain (nested) and `1/4` otherwise (independent).
(Three equalities never occur: they would force `c = 0` resp. `b = 0` against the second line.)
All matrices in the support have `c ≥ 0`, and `c = 0` only with `a > 0`, so no `±` duplicates.

* `ptC M` : the coefficient of `M` in `T̃`;
* `Ttilde n = Σ_{M ∈ [−n, n]⁴, det M = n} ptC M · M ∈ ℚ[M₂(ℤ)]`
  (support bound `|entries| ≤ n` checked numerically for `n ≤ 40`; proof planned, P4b);
* `trace_Ttilde` : `tr(·|T̃ₙ) = Σ_M ptC M · Sym¹⁰(tr M, n)`;
* sanity: for `n = 1, 2, 3` this equals `σ₁₁(n) + 2τ(n)` (`3, 2001, 177652`), by `decide`.
-/

open Finset

namespace RamanujanWeil.Arith.ES

open M2

/-- Weight of a 3-chain `x ≤ y ≤ z`. -/
def w3 (x y z : ℤ) : ℚ :=
  if x ≤ y ∧ y ≤ z then
    (if x = y then (if y = z then 1 / 6 else 1 / 2) else (if y = z then 1 / 2 else 1))
  else 0

/-- Weight of a 4-chain `x ≤ y ≤ z ≤ u` (three equalities: weight 0, never used). -/
def w4 (x y z u : ℤ) : ℚ :=
  if x ≤ y ∧ y ≤ z ∧ z ≤ u then
    (if x = y then
      (if y = z then (if z = u then 0 else 1 / 6) else (if z = u then 1 / 4 else 1 / 2))
    else
      (if y = z then (if z = u then 1 / 6 else 1 / 2) else (if z = u then 1 / 2 else 1)))
  else 0

/-- The coefficient of `M` in Popa–Zagier's `T̃` (eq. (15)). -/
def ptC (M : M2) : ℚ :=
  (if 0 ≤ M.c ∧ M.c < M.a then w3 (M.a - M.d) (-M.b) M.c else 0)
  - (if M.b < M.d ∧ M.d ≤ 0 then w3 (-M.b) (M.a - M.d) M.c else 0)
  - (if M.a ≤ 0 ∧ 0 < M.c then w4 0 (M.a - M.d) M.c (-M.b) else 0)
  - (if M.d ≤ 0 ∧ 0 < -M.b then w4 0 (M.a - M.d) (-M.b) M.c else 0)

/-- The coefficient restricted to determinant `n`. -/
def ptCn (n : ℕ) (a b c d : ℤ) : ℚ :=
  if a * d - b * c = n then ptC ⟨a, b, c, d⟩ else 0

/-- **Popa–Zagier's `T̃ₙ`** as an element of `ℚ[M₂(ℤ)]`. -/
noncomputable def Ttilde (n : ℕ) : R :=
  ∑ a ∈ Icc (-(n : ℤ)) n, ∑ b ∈ Icc (-(n : ℤ)) n, ∑ c ∈ Icc (-(n : ℤ)) n,
    ∑ d ∈ Icc (-(n : ℤ)) n, ptCn n a b c d • MonoidAlgebra.of ℚ M2 ⟨a, b, c, d⟩

/-- The trace of `T̃ₙ` on `V₁₀` as an explicit finite sum (the `ℚ`-valued "class-number side" before
the per-trace regrouping of P6). -/
def traceSum (n : ℕ) : ℚ :=
  ∑ a ∈ Icc (-(n : ℤ)) n, ∑ b ∈ Icc (-(n : ℤ)) n, ∑ c ∈ Icc (-(n : ℤ)) n,
    ∑ d ∈ Icc (-(n : ℤ)) n, ptCn n a b c d * (symTr10 (a + d) (a * d - b * c) : ℚ)

theorem trace_Ttilde (n : ℕ) : LinearMap.trace ℚ V (actR (Ttilde n)) = traceSum n := by
  simp only [Ttilde, traceSum, actR_sum, map_sum, actR_smul, actR_of, map_smul, smul_eq_mul]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
    Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
  congr 1
  have := trace_actR_sum {()} (fun _ => (1 : ℚ)) (fun _ => (⟨a, b, c, d⟩ : M2))
  simpa [M2.tr, M2.det, actR_single] using this

/-- Sanity check of the definition against `σ₁₁(n) + 2τ(n)` (Eichler–Selberg + Eichler–Shimura):
`3 = 1 + 2·1`, `2001 = 2049 + 2·(−24)`, `177652 = 177148 + 2·252`. -/
theorem traceSum_small : traceSum 1 = 3 ∧ traceSum 2 = 2001 ∧ traceSum 3 = 177652 := by
  decide +kernel

end RamanujanWeil.Arith.ES
