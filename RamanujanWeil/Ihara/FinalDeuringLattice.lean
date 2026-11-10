import RamanujanWeil.Ihara.FinalDeuringTate
import RamanujanWeil.Arith.DeuringClassLattice
import RamanujanWeil.Arith.DeuringG7FinCore

/-!
# Current headline: Deligne's bound from two named geometric hypotheses

`τ(p)² ≤ 4p¹¹` from
* `TateFinitenessPolAll`: finiteness of principally polarized graph quotients of `J_W × J_{W'}`
  (`docs/ARITH_DEURING_G7FIN.md`), which gives `mult ≤ 1` (`mult_le_one_pol`), and
* `PrimeToPLinkAll`: isogenous ordinary Jacobians are linked by `α ≫ β = [n]` with `p ∤ n`
  (`docs/ARITH_DEURING_CLASSLATTICE.md`), which with everything else proved gives the per-class
  count `DeuringMultiplicity` (`deuringMultiplicity_of_props`).

Everything else (Weil II geometric side, Eichler–Selberg, Kronecker–Hurwitz, the per-class lattice
`Λ`, `rel_iff`, `card_stab`, `surj_class`, Weierstrass descent, minimal base) is proved.
-/

namespace RamanujanWeil.Ihara

open RamanujanWeil.ArithPlan RamanujanWeil.Arith.Hurwitz RamanujanWeil.Arith.Deuring.Mult
  RamanujanWeil.Arith.Deuring.ClassLattice RamanujanWeil.Arith.Deuring.Geom.G7.Fin

/-- **Headline.** -/
theorem deligneBound_of_tatePol_link (hfin : TateFinitenessPolAll) (hlink : PrimeToPLinkAll) :
    RamanujanTau.DeligneBound := by
  have key : ∀ (p : ℕ) [Fact p.Prime], multAll p = mult p := fun p hp => by
    funext n t
    unfold multAll
    rw [dif_pos hp.out]
  refine deligneBound_of_DeuringMult_unique multAll
    (fun p _ => by rw [key p]; exact deuringMultiplicity_of_props hfin hlink p) ?_
  intro p _ n hn t hpt hlt
  rw [key p]
  exact mult_le_one_pol hfin p n hn t hpt hlt

end RamanujanWeil.Ihara
