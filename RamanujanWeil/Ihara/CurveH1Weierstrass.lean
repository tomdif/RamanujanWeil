import RamanujanWeil.Ihara.CurveH1
import StacksFrontier.AlgebraicGeometry.Stacks.WeierstrassFamilyProper
import StacksFrontier.AlgebraicGeometry.Stacks.WeierstrassFamilySmooth
import StacksFrontier.AlgebraicGeometry.Size.Cutoff
import StacksFrontier.AlgebraicGeometry.Size.Affine

/-!
# M4a for the plane cubic of a Weierstrass equation over `𝔽_q`

For a Weierstrass curve `W` over a finite field `k` with `Δ ≠ 0` (`W.IsElliptic`), Stacks' plane
cubic `E = projOf W ⊂ P²_k` with its projection `projectionOf W : E ⟶ Spec k` is

* an object of every big étale site `B` (`contains_projOf`: size bound, as `Family.contains_total`),
* proper (`isProper_projectionOf`) and smooth of relative dimension one
  (`smoothOfRelativeDimension_projectionOf`, using `Δ` a unit),
* pointed by `(0 : 1 : 0)` (`zeroOf W`, `zeroOf_projectionOf`).

`charpoly_weierstrassH1` is then the M4a statement for `E`, with the three remaining inputs as
explicit hypotheses (see `docs/IHARA_CURVE_H1.md`): connectedness of `E_k̄`,
`HasFirstBettiTwo` (`dim H¹(E_k̄, ℚ_ℓ) = 2`) and `RealizesWeierstrass` (`#E(k_n) = #W(k_n)`).
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
  AlgebraicGeometry.ModuliEllipticCurves.Weierstrass Stacks.Frobenius Polynomial Module

universe u

namespace RamanujanWeil.Ihara

variable {k : Type u} [Field k] [Fintype k] (W : WeierstrassCurve k) [W.IsElliptic]

/-- Every big étale site contains `Spec k` for `k` finite. -/
theorem contains_spec_finite (B : BigEtaleSite.{u}) : B.Contains (Spec (CommRingCat.of k)) := by
  show (Spec (CommRingCat.of k)).size < B.cutoff
  rw [Scheme.size_Spec]
  exact lt_of_le_of_lt (max_le le_rfl Cardinal.mk_le_aleph0) B.aleph0_lt_cutoff

/-- Every big étale site contains the plane cubic of `W`. -/
theorem contains_projOf (B : BigEtaleSite.{u}) : B.Contains (projOf W) :=
  Scheme.size_lt_of_locallyOfFiniteType_of_quasiCompact (projectionOf W) (contains_spec_finite B)

/-- The plane cubic `E = projOf W` as an object of `B`. -/
noncomputable abbrev weierstrassScheme (B : BigEtaleSite.{u}) : B.Scheme := B.obj (projOf W) (contains_projOf W B)

instance smoothOfRelativeDimension_projectionOf_of_isElliptic :
    SmoothOfRelativeDimension 1 (projectionOf W) :=
  smoothOfRelativeDimension_projectionOf W W.isUnit_Δ

instance smooth_projectionOf_of_isElliptic : Smooth (projectionOf W) :=
  SmoothOfRelativeDimension.smooth 1 (projectionOf W)

omit [Fintype k] [W.IsElliptic] in
/-- The rational point `(0 : 1 : 0)`. -/
theorem exists_section_projectionOf :
    ∃ s : Spec (.of k) ⟶ projOf W, s ≫ projectionOf W = 𝟙 _ :=
  ⟨zeroOf W, zeroOf_projectionOf W⟩

/-- **M4a for the Weierstrass cubic.** For `W` over `𝔽_q` with `Δ ≠ 0`, `E = projOf W`, `ℓ ≠ p`:
if `E_k̄` is connected, `dim H¹(E_k̄, ℚ_ℓ) = 2` and `#E(k_n) = #W(k_n)` for `n ≥ 1`, then
`charpoly(Frob | H¹(E_k̄, ℚ_ℓ)) = X² − aX + q` with `a = q + 1 − #W(k)`. -/
theorem charpoly_weierstrassH1 (B : BigEtaleSite.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
    [Fact (ℓ ≠ ringChar k)]
    [ConnectedSpace ↥(pullback (Over.mk (projectionOf W)).hom
      (specAlgebraMap k (AlgebraicClosure k)))]
    (hb1 : HasFirstBettiTwo (weierstrassScheme W B) (projectionOf W) ℓ)
    (hW : RealizesWeierstrass (weierstrassScheme W B) (projectionOf W) W) :
    (Weil.rationalFrobenius B (weierstrassScheme W B) (projectionOf W) ℓ 1).charpoly =
      Polynomial.X ^ 2 - C (((Fintype.card k : ℤ) + 1 - Nat.card W.toAffine.Point : ℤ) : ℚ_[ℓ]) * Polynomial.X +
        C (Fintype.card k : ℚ_[ℓ]) :=
  charpoly_rationalFrobenius_one_of_weierstrass (weierstrassScheme W B) (projectionOf W) ℓ
    (exists_section_projectionOf W) W hb1 hW

end RamanujanWeil.Ihara
