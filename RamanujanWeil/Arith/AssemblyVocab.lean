import RamanujanWeil.Arith.ArithVocab
import RamanujanWeil.Ihara.IharaStatement
import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Shared vocabulary for the R-ord assembly (frozen text of `scratch/ArithInterfaces.lean`)

`hypTerm`, `esSum`, `ordSum`, `EichlerSelbergPrimePow`, `EichlerSelbergApprox`, `traceCount`,
`OrdinaryDeuring` and `HasseAll` are copied verbatim (docs/ARITH_ROUTE.md §4), in namespace
`RamanujanWeil.ArithPlan`. Definitions only; nothing is assumed or proved here.
(`kron`, `HurwitzConventions`, `HurwitzPrimeSquare` live in `ArithVocab.lean`,
`TauHeckeRecurrence` in `TauHecke.lean`, `SupersingularCountBound` in `SupersingularBound.lean`.)
-/

open Finset

namespace RamanujanWeil.ArithPlan

open RamanujanWeil.Ihara

/-- Hyperbolic term of Eichler–Selberg at `n = p^m`: `Σ_{d ∣ n} min(d, n/d)¹¹`. -/
def hypTerm (p m : ℕ) : ℤ :=
  ∑ j ∈ range (m + 1), ((min (p ^ j) (p ^ (m - j)) : ℕ) : ℤ) ^ 11

/-- Class-number side of Eichler–Selberg (weight 12) at `q`:
`Σ_{t² ≤ 4q} h₁₀(t, q) H(4q − t²)` (parabolic terms use `H 0 = −1/12`). -/
def esSum (H : ℕ → ℚ) (q : ℕ) : ℚ :=
  ∑ t ∈ Icc (-(2 * (q : ℤ))) (2 * q) with t ^ 2 ≤ 4 * (q : ℤ),
    (symTrace 10 t q : ℚ) * H (4 * (q : ℤ) - t ^ 2).toNat

/-- Ordinary part: the same sum restricted to `p ∤ t`. -/
def ordSum (H : ℕ → ℚ) (p m : ℕ) : ℚ :=
  ∑ t ∈ Icc (-(2 * ((p ^ m : ℕ) : ℤ))) (2 * (p ^ m : ℕ)) with
      t ^ 2 ≤ 4 * ((p ^ m : ℕ) : ℤ) ∧ ¬ (p : ℤ) ∣ t,
    (symTrace 10 t (p ^ m : ℕ) : ℚ) * H (4 * ((p ^ m : ℕ) : ℤ) - t ^ 2).toNat

/-! ## A2: Eichler–Selberg at prime powers (exact and approximate forms) -/

/-- **ES, weight 12, level 1, `n = p^m`** (checked n ≤ 300 and p^m ≤ 2·10⁷, V3a). -/
def EichlerSelbergPrimePow (H : ℕ → ℚ) (p : ℕ) : Prop :=
  ∀ m : ℕ, esSum H (p ^ m) = -2 * (RamanujanTau.tau (p ^ m) : ℚ) - hypTerm p m

/-- Weaker form that suffices for R-ord: only the elliptic terms must be exact. -/
def EichlerSelbergApprox (H : ℕ → ℚ) (p : ℕ) : Prop :=
  ∃ C : ℝ, ∃ k : ℕ, ∀ m : ℕ,
    |((esSum H (p ^ m) + 2 * (RamanujanTau.tau (p ^ m) : ℚ) : ℚ) : ℝ)| ≤
      C * ((m : ℝ) + 1) ^ k * Real.sqrt p ^ (11 * m)

/-! ## A3-ord: Deuring–Waterhouse on the ordinary locus only -/

/-- Number of Weierstrass tuples over `𝔽_{pⁿ}` with `Δ ≠ 0` and trace `t`. -/
noncomputable def traceCount (p : ℕ) [Fact p.Prime] (n : ℕ) (t : ℤ) : ℕ :=
  letI : Fintype (GaloisField p n) := Fintype.ofFinite _
  open scoped Classical in
  ({c : Fin 5 → GaloisField p n | (wc c).Δ ≠ 0 ∧ traceOfFrob (wc c) = t} : Finset _).card

/-- **Ordinary Deuring–Waterhouse, 5-parameter form** (`p ∤ t`):
`N(t, q) = q³(q − 1)·H(4q − t²)/2` (checked q ≤ 16 incl. p = 2, 3, V2).
Factorization: `TorsorCount.sum_trace_eq_sum_orbits` (Hurwitz/torsor agent) +
`Σ_{E/≅, a_E = t} 1/#Aut E = H(4q − t²)/2` (the A3 core). -/
def OrdinaryDeuring (H : ℕ → ℚ) (p : ℕ) [Fact p.Prime] : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ t : ℤ, ¬ (p : ℤ) ∣ t →
    (traceCount p n t : ℚ) =
      (p : ℚ) ^ (3 * n) * ((p : ℚ) ^ n - 1) *
        (if t ^ 2 < 4 * (p : ℤ) ^ n then H (4 * (p : ℤ) ^ n - t ^ 2).toNat else 0) / 2

/-- Hasse for every Weierstrass tuple (unconditional in the repo:
`sq_le_four_mul_card_weierstrassH1'` + `h1RankFormula`; needs the Weil closure). -/
def HasseAll (p : ℕ) [Fact p.Prime] : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ c : Fin 5 → GaloisField p n, (wc c).Δ ≠ 0 →
    (letI : Fintype (GaloisField p n) := Fintype.ofFinite _
     traceOfFrob (wc c) ^ 2 ≤ 4 * (p : ℤ) ^ n)

end RamanujanWeil.ArithPlan
