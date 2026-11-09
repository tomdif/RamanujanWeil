import RamanujanWeil.Ihara.FinalDeuringApprox
import RamanujanWeil.Arith.DeuringMultCount

/-!
# Headline with the concrete isogeny-class count and Tate uniqueness

`docs/ARITH_DEURING_MULT.md`. `deligneBound_of_DeuringMult_unique` (`FinalDeuringApprox`) takes
an abstract `mult` with `DeuringMultiplicity` and `mult ≤ 1`. Here `mult` is the concrete
`Mult.mult p n t` = number of isogeny classes of elliptic curves over `𝔽_{pⁿ}` with trace `t`
(`DeuringMultDef`), and `mult ≤ 1` is discharged by Tate (`tate_exists_frobHom`, G7) modulo the
single named hypothesis `TateFinitenessAll`.

* **`deligneBound_of_DeuringMult_tate`**: `TateFinitenessAll` + `DeuringMultiplicity` for the
  concrete `mult` ⇒ Deligne.
* **`deligneBound_of_classLattice_tate`**: `TateFinitenessAll` + the per-class lattice interface
  `DeuringClassLatticeAll` (G8 within one isogeny class) at every prime ⇒ Deligne.
-/

namespace RamanujanWeil.Ihara

open RamanujanWeil.ArithPlan RamanujanWeil.Arith.Hurwitz RamanujanWeil.Arith.Deuring.Mult

/-- `mult` as a function of an arbitrary `p : ℕ` (`0` when `p` is not prime), the shape taken by
`deligneBound_of_DeuringMult_unique`. -/
noncomputable def multAll (p n : ℕ) (t : ℤ) : ℕ :=
  if h : p.Prime then @mult p ⟨h⟩ n t else 0

/-- **Headline, Tate.** Given Tate finiteness (`QuotientFiniteness` for `J_W × J_{W'}`, same
ordinary trace) and the per-trace counts `N(t) = q³(q−1)·m(t)·H(4q−t²)/2` for the concrete
isogeny-class count `m = Mult.mult`, `τ(p)² ≤ 4p¹¹`. -/
theorem deligneBound_of_DeuringMult_tate (hfin : TateFinitenessAll)
    (hM : ∀ (p : ℕ) [Fact p.Prime], DeuringMultiplicity hurwitz p (mult p)) :
    RamanujanTau.DeligneBound := by
  have key : ∀ (p : ℕ) [Fact p.Prime], multAll p = mult p := fun p hp => by
    funext n t
    unfold multAll
    rw [dif_pos hp.out]
  refine deligneBound_of_DeuringMult_unique multAll (fun p _ => by rw [key p]; exact hM p) ?_
  intro p _ n hn t hpt hlt
  rw [key p]
  exact mult_le_one p hfin n hn t hpt hlt

/-- **Headline, Tate + per-class lattices.** Tate finiteness and, at every prime, a per-class
lattice interface for every ordinary isogeny class give `τ(p)² ≤ 4p¹¹`. -/
theorem deligneBound_of_classLattice_tate (hfin : TateFinitenessAll)
    (hL : ∀ (p : ℕ) [Fact p.Prime], DeuringClassLatticeAll p) :
    RamanujanTau.DeligneBound :=
  deligneBound_of_DeuringMult_tate hfin fun p _ => deuringMultiplicity_of_classLattice p (hL p)

end RamanujanWeil.Ihara
