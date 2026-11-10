import RamanujanWeil.Ihara.FinalDeuringLattice
import RamanujanWeil.Arith.DeuringPLink

/-!
# Current headline: Deligne's bound from `TateFinitenessPolAll` alone

`PrimeToPLinkAll` is now a theorem (`PLink.primeToPLinkAll`, `docs/ARITH_DEURING_PLINK.md`), so
`deligneBound_of_tatePol_link` needs only the finiteness of principally polarized graph quotients
(`TateFinitenessPolAll`, `docs/ARITH_DEURING_G7FIN.md`).
-/

namespace RamanujanWeil.Ihara

open RamanujanWeil.Arith.Deuring.Geom.G7.Fin RamanujanWeil.Arith.Deuring.PLink

/-- **Headline.** `τ(p)² ≤ 4p¹¹` from `TateFinitenessPolAll`. -/
theorem deligneBound_of_tatePol (hfin : TateFinitenessPolAll) : RamanujanTau.DeligneBound :=
  deligneBound_of_tatePol_link hfin primeToPLinkAll

end RamanujanWeil.Ihara
