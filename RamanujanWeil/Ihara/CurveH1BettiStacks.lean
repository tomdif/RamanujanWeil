import RamanujanWeil.Ihara.CurveH1Betti
import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.ConstantCurveH1Trace

/-! Discharge of `H1RankFormula` by Stacks' Tag 0C1Z (needs `ConstantCurveH1Trace` built). -/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
  AlgebraicGeometry.ModuliEllipticCurves.Weierstrass Polynomial

universe u

namespace RamanujanWeil.Ihara

theorem h1RankFormula : H1RankFormula.{u} :=
  fun B X ℓ _ _ _ _ _ f _ kbar _ _ p q _ _ hcard _ _ _ _ _ hℓ =>
    Stacks.EtaleCohomology.LAdicSheaf.finrank_rationalGeometricCompactlySupportedCohomology_constant_one
      B X ℓ f kbar p q hcard hℓ

variable {k : Type u} [Field k] [Fintype k] (W : WeierstrassCurve k) [W.IsElliptic]
  (B : BigEtaleSite.{u}) (ℓ : ℕ) [Fact ℓ.Prime] [Fact (ℓ ≠ ringChar k)]

/-- M4a for `projOf W` from `[W.IsElliptic]` and `RealizesWeierstrass` only. -/
theorem charpoly_weierstrassH1''
    (hW : RealizesWeierstrass (weierstrassScheme W B) (projectionOf W) W) :
    (Weil.rationalFrobenius B (weierstrassScheme W B) (projectionOf W) ℓ 1).charpoly =
      Polynomial.X ^ 2 -
          C (((Fintype.card k : ℤ) + 1 - Nat.card W.toAffine.Point : ℤ) : ℚ_[ℓ]) * Polynomial.X +
        C (Fintype.card k : ℚ_[ℓ]) :=
  charpoly_weierstrassH1' W B ℓ h1RankFormula hW

end RamanujanWeil.Ihara
