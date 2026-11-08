import RamanujanWeil.Ihara.M4bFibre
import RamanujanWeil.Ihara.CurveH1BettiStacks
import RamanujanWeil.Ihara.Assembly

/-!
# M4b discharged: `IharaIdentity p ⇒ τ(p)² ≤ 4 p¹¹`

* `r1StalkCharpolyFibre`: the frozen M4b interface `R1StalkCharpolyFibre p B ℓ` holds for every
  `ℓ ≠ p`, from `r1StalkCharpolyFibre_of_h1RankFormula` and Stacks' Tag 0C1Z (`h1RankFormula`).
* `deligneBound_of_ihara`: `deligneBound_of_ihara_M4b` without the M4b hypothesis.
-/

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.SmallEtale Stacks.EtaleCohomology

noncomputable section

namespace RamanujanWeil.Ihara

attribute [local instance] HasDerivedCategory.standard moduleCat_hasLimitsOfSize

variable (p : ℕ) [Fact p.Prime] (B : BigEtaleSite.{0}) (ℓ : ℕ) [Fact ℓ.Prime]
  [∀ (n : ℕ) (S T : B.Scheme) (g : T ⟶ S),
    ((AlgebraicGeometry.smallEtaleBaseChange B g).sheafPushforwardContinuous
      (ModuleCat.{1} (ZMod (ℓ ^ (n + 1))))
      (SmallEtale.topology B S.1 S.property)
      (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
  [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
    HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
      (ModuleCat.{1} (ZMod (ℓ ^ (n + 1))))]
  [∀ (n : ℕ) (T : B.Scheme), HasWeakSheafify (SmallEtale.topology B T.1 T.property)
    (ModuleCat.{1} (ZMod (ℓ ^ (n + 1))))]

/-- **M4b.** The frozen interface `R1StalkCharpolyFibre p B ℓ` holds for every prime `ℓ ≠ p`. -/
theorem r1StalkCharpolyFibre (hℓp : ℓ ≠ p) : R1StalkCharpolyFibre p B ℓ :=
  r1StalkCharpolyFibre_of_h1RankFormula p B ℓ h1RankFormula hℓp

include B in
/-- **Ihara–Birch ⇒ Deligne at `p`.** Given the Ihara–Birch identity at `p` (and any big étale
site `B`, any prime `ℓ ≠ p`), Deligne's bound `τ(p)² ≤ 4 p¹¹` holds. -/
theorem deligneBound_of_ihara (hℓp : ℓ ≠ p) (hI : IharaIdentity p) :
    RamanujanTau.tau p ^ 2 ≤ 4 * (p : ℤ) ^ 11 :=
  deligneBound_of_ihara_M4b p B ℓ hℓp (r1StalkCharpolyFibre p B ℓ hℓp) hI

end RamanujanWeil.Ihara
