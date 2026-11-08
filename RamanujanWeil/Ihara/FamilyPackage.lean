import RamanujanWeil.Ihara.FamilyR1
import RamanujanWeil.Ihara.WeilPackage

/-!
# M3 → M2: the Lefschetz package over `W_p`

The geometric data of M3 (`FamilyGeometry.lean`, `FamilyR1.lean`) fit the hypotheses of the M2
headline `lefschetzPackage_of_lisse_pure'` with `X = W_p`, `k = 𝔽_p = ZMod p`, `q = 1`, `d = 5`.
`lefschetzPackage_Wp` is that instantiation: every lisse, pointwise `ι`-mixed `≤ w`, `ι`-realizable
ℓ-adic sheaf `F` on `W_p` has a Lefschetz package with point side `pointSum F`. M5 applies it to
`F = Sym¹⁰ R¹` (`R1 p B ℓ`, lisse by `isLisse_R1`).
-/

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.SmallEtale Stacks.EtaleCohomology

namespace RamanujanWeil.Ihara

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

/-- `#𝔽_p = p ^ 1`. -/
theorem card_zmod_eq_pow_one : Fintype.card (ZMod p) = p ^ 1 := by
  rw [ZMod.card, pow_one]

/-- **M2 over `W_p`**: a lisse, pointwise `ι`-mixed of weights `≤ w`, `ι`-realizable ℓ-adic sheaf
on `W_p` (`ℓ ≠ p`) has a Lefschetz package of dimension `5` over `𝔽_p`, with point side
`pointSum B (Wp p B) ℓ (toSpecK p B) F`. -/
theorem lefschetzPackage_Wp (hℓp : ℓ ≠ p) (ι : ℚ_[ℓ] →+* ℂ)
    (F : LAdicSheaf.{0, 1} B (Wp p B) ℓ) (w : ℤ) (hF : F.IsLisse)
    (hmix : LAdicSheaf.IsPointwiseMixedOfWeightLE B (Wp p B) ℓ (toSpecK p B) F (p ^ 1) ι w)
    (hreal : LAdicSheaf.IsIotaRealizable B (Wp p B) ℓ (toSpecK p B) F ι) :
    Nonempty (LefschetzPackage ℚ_[ℓ] ι (p ^ 1) w 5 (pointSum B (Wp p B) ℓ (toSpecK p B) F)) :=
  lefschetzPackage_of_lisse_pure' B (Wp p B) ℓ (toSpecK p B) p 1 (card_zmod_eq_pow_one p) hℓp ι 5
    (topologicalKrullDim_Wp_le p B) F w hF hmix hreal

end RamanujanWeil.Ihara
