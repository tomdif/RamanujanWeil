import RamanujanWeil.Ihara.CurveH1Weierstrass
import RamanujanWeil.Ihara.PointsCurve

/-!
# M4a gap 2: `RealizesWeierstrass` for the plane cubic, unconditionally

`realizesWeierstrass_projOf`: for every elliptic Weierstrass curve `W` over a finite field `k` and
every big étale site `B`, `RealizesWeierstrass (weierstrassScheme W B) (projectionOf W) W`, i.e.
`#E(k_n) = #W(k_n)` for all `n ≥ 1` (`E = projOf W`, Mathlib's `Point` on the right). From
`natCard_fieldValuedPoints_projOf` (`PointsCurve.lean`) and `natCard_point_congr` (CurveH1Core)
for `ULift (k_n) ≃ₐ[k] k_n`.
-/

open CategoryTheory AlgebraicGeometry Stacks.EtaleCohomology
open AlgebraicGeometry.ModuliEllipticCurves.Weierstrass

universe u

namespace RamanujanWeil.Ihara

variable {k : Type u} [Field k] (W : WeierstrassCurve k)

/-- **M4a gap 2, proved.** For every elliptic Weierstrass curve `W` over a finite field `k`, the
plane cubic `projOf W` realizes `W`: `#E(k_n) = #W(k_n)` for all `n ≥ 1`. -/
theorem realizesWeierstrass_projOf [Fintype k] [W.IsElliptic] (B : BigEtaleSite.{u}) :
    RealizesWeierstrass (weierstrassScheme W B) (projectionOf W) W := by
  intro n hn
  have : NeZero n := ⟨by omega⟩
  rw [curvePointCount_eq, pointCountOfDegree, pointCount]
  exact (natCard_fieldValuedPoints_projOf W _).trans (natCard_point_congr W ULift.algEquiv)

end RamanujanWeil.Ihara
