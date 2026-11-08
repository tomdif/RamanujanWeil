import Mathlib.Data.Int.Notation
import Mathlib.Data.List.Defs

/-
  RamanujanWeil/Tau.lean

  VERBATIM copy of `~/RamanujanTau/RamanujanTau/Basic.lean` (toolchain v4.30) from the line
  `import Mathlib.Data.Int.Notation` down to the final `end RamanujanTau`; only this comment
  block and the sanity section after the copied text are new. Toolchain changes forced by the bump
  to Lean v4.34.0-rc2 / Mathlib 16edf57: NONE (the copied text compiles unchanged).
  Keeping namespace `RamanujanTau` and the names `tau`, `coeffList`, ... means that the
  final statement `(RamanujanTau.tau p) ^ 2 ≤ 4 * (p : ℤ) ^ 11` is textually identical to
  `RamanujanTau.DeligneBound.bound`.
-/

/-! # Ramanujan's τ function

Definition of `τ : ℕ → ℤ` as the coefficient sequence of the modular discriminant
`Δ(q) = q · ∏_{n≥1} (1 - q^n)^{24} = Σ_{n≥1} τ(n) q^n`.

## Implementation strategy

Mathlib's `Polynomial` is noncomputable (built via quotients on Finsupp).  We
therefore work with a small computable representation `Coeffs := List ℤ` —
coefficients listed low-degree-first — and define the operations needed for
the Euler product. This keeps `tau` fully reducible by `native_decide`.

The infinite Euler product `∏_{k≥1} (1 - q^k)` agrees with its truncation
`∏_{k=1}^{N} (1 - q^k)` through every coefficient of degree `≤ N` (since each
omitted factor `(1 - q^j)` for `j > N` contributes only at degrees `≥ j > N`).
So `τ(n)` is the coefficient of `q^n` in `q · (∏_{k=1}^{n} (1-q^k))^{24}`.

## Bridge to Mathlib

Mathlib has `ModularForm.discriminant : ℍ → ℂ := fun z => (eta z)^24` plus
its `q`-expansion. Connecting our `tau` to that q-expansion is a downstream
theorem (`tau_coeff_discriminant`), stated but not proved here.
-/

namespace RamanujanTau

/-! ## Polynomial coefficient lists

Convention: `[a₀, a₁, a₂, …]` represents `a₀ + a₁·X + a₂·X² + …`.
Trailing zeros are allowed (and ignored when reading coefficients).
-/

/-- Read the `n`-th coefficient of a coefficient list, default `0`. -/
def coeffList : List ℤ → ℕ → ℤ
  | [], _ => 0
  | a :: _, 0 => a
  | _ :: as, n+1 => coeffList as n

/-- Pointwise addition of two coefficient lists. -/
def addList : List ℤ → List ℤ → List ℤ
  | [], q => q
  | p, [] => p
  | a :: as, b :: bs => (a + b) :: addList as bs

/-- Scalar multiplication: `c · [a₀, a₁, …] = [c·a₀, c·a₁, …]`. -/
def scaleList (c : ℤ) : List ℤ → List ℤ
  | [] => []
  | a :: as => (c * a) :: scaleList c as

/-- Shift up by `n` (multiply by `Xⁿ`): prepend `n` zeros. -/
def shiftList : ℕ → List ℤ → List ℤ
  | 0, p => p
  | n+1, p => 0 :: shiftList n p

/-- Polynomial multiplication of coefficient lists. -/
def mulList : List ℤ → List ℤ → List ℤ
  | [], _ => []
  | a :: as, q => addList (scaleList a q) (0 :: mulList as q)

/-- Truncate to the first `d+1` coefficients (i.e. degree `≤ d`). -/
def truncList (d : ℕ) : List ℤ → List ℤ
  | [] => []
  | a :: as => if d = 0 then [a] else a :: truncList (d-1) as

/-- The polynomial `1 - X^k` as a coefficient list. For `k = 0` we get `[0]`. -/
def oneMinusXk : ℕ → List ℤ
  | 0 => [0]
  | k+1 => 1 :: (List.replicate k 0 ++ [-1])

/-- Truncated `n`-th power, keeping only coefficients of degree `≤ d`. -/
def truncPowList (d : ℕ) (p : List ℤ) : ℕ → List ℤ
  | 0 => [1]
  | n+1 => truncList d (mulList (truncPowList d p n) p)

/-- Truncated Euler product `∏_{k=1}^{N} (1 - X^k)` keeping degrees `≤ d`. -/
def eulerProductTrunc (d : ℕ) : ℕ → List ℤ
  | 0 => [1]
  | N+1 => truncList d (mulList (eulerProductTrunc d N) (oneMinusXk (N+1)))

/-- **Ramanujan's τ function**: the n-th coefficient of `Δ(q) = q · ∏(1-q^k)^{24}`.

For each `n`, we work with the truncated Euler product through degree `n`,
which agrees with the infinite product on coefficients of degree `≤ n`. -/
def tau (n : ℕ) : ℤ :=
  let p := eulerProductTrunc n n
  let p24 := truncPowList n p 24
  coeffList (shiftList 1 p24) n

/-- Notation: `τ` for `RamanujanTau.tau`. -/
scoped notation "τ" => RamanujanTau.tau

/-! ## Sanity: τ(0) = 0 and τ(1) = 1 -/

theorem tau_zero : τ 0 = 0 := by decide +kernel

theorem tau_one : τ 1 = 1 := by decide +kernel


/-! ## Sanity values (added in RamanujanWeil; kernel `decide`, no `native_decide`) -/

theorem tau_two : τ 2 = -24 := by decide +kernel

theorem tau_three : τ 3 = 252 := by decide +kernel

theorem tau_five : τ 5 = 4830 := by decide +kernel

end RamanujanTau
