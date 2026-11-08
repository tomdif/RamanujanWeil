import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol

/-!
# Shared arithmetic vocabulary (frozen text of `scratch/ArithInterfaces.lean`, docs/ARITH_ROUTE.md §4)

`kron`, `HurwitzConventions` and `HurwitzPrimeSquare` are copied verbatim, in namespace
`RamanujanWeil.ArithPlan`, so that later milestones can share them.
-/

open Finset

namespace RamanujanWeil.ArithPlan

/-- Kronecker symbol `(D / p)` for a prime `p` (`p = 2` via `D mod 8`). -/
def kron (D : ℤ) (p : ℕ) : ℤ :=
  if p = 2 then (if D % 2 = 0 then 0 else if D % 8 = 1 ∨ D % 8 = 7 then 1 else -1)
  else jacobiSym D p

/-- `H 0 = −1/12` and `H N = 0` off discriminants (`N ≡ 1, 2 mod 4`). -/
def HurwitzConventions (H : ℕ → ℚ) : Prop :=
  H 0 = -1 / 12 ∧ ∀ N : ℕ, N % 4 = 1 ∨ N % 4 = 2 → H N = 0

/-- `H(p²N) = (p + 1 − (−N/p)) H(N) − p·[p² ∣ N] H(N/p²)` for `N ≡ 0, 3 mod 4`
(checked for p ≤ 13, N ≤ 3000, `arith_route_check.out` V1). -/
def HurwitzPrimeSquare (H : ℕ → ℚ) (p : ℕ) : Prop :=
  ∀ N : ℕ, N % 4 = 0 ∨ N % 4 = 3 →
    H (p ^ 2 * N) = ((p : ℚ) + 1 - kron (-(N : ℤ)) p) * H N -
      (if p ^ 2 ∣ N then (p : ℚ) * H (N / p ^ 2) else 0)

end RamanujanWeil.ArithPlan
