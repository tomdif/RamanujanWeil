import RamanujanWeil.Arith.DeuringG7DCore
import RamanujanWeil.Arith.DeuringFinal

/-!
# A3-ord, G7-D: Deligne's bound from the step-D seam

`docs/ARITH_DEURING_G7D.md` §3. `ThetaDescentFinitenessAll` (theta groups + Mumford descent +
Θ + J + C, named) ⇒ `TateFinitenessLagAll` (`tateFinitenessLagAll_of_thetaDescent`, through
`AltPairing.ofTheta` and the proved level-subgroup criterion) ⇒ `MultLeOneAll` ⇒ Deligne
(`Final.deligneBound_of_multLeOne`, with the unconditional per-class count).
-/

namespace RamanujanWeil.Arith.Deuring.Geom.G7.Fin.Weil

open RamanujanWeil.Arith.Deuring.Final

/-- `ThetaDescentFinitenessAll ⇒ MultLeOneAll`. -/
theorem multLeOneAll_of_thetaDescent (h : ThetaDescentFinitenessAll) : MultLeOneAll :=
  fun p _ n hn t hp hlt => mult_le_one_lag (tateFinitenessLagAll_of_thetaDescent h) p n hn t hp hlt

/-- **Headline through step D.** `τ(p)² ≤ 4p¹¹` from `ThetaDescentFinitenessAll`. -/
theorem deligneBound_of_thetaDescent (h : ThetaDescentFinitenessAll) :
    RamanujanTau.DeligneBound :=
  deligneBound_of_multLeOne (multLeOneAll_of_thetaDescent h)

end RamanujanWeil.Arith.Deuring.Geom.G7.Fin.Weil
