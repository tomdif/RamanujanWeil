import RamanujanWeil.Ihara.CurveH1BettiConnected

/-!
# Gap 1 of M4a: `dim H¹(E_k̄, ℚ_ℓ) = 2`, reduced to Stacks' Tag 0C1Z

Let `f : X ⟶ Spec k` be proper and smooth of relative dimension one over a finite field `k` with
`H⁰(X, 𝒪_X) = k`, and `ℓ ≠ char k`. Then `X_k̄` is a smooth proper curve over `k̄`
(`isCurve_baseChange_of_finrank_zero`), and the genus does not change under `k → k̄`
(`genus_pullback_snd`). Stacks' computation

`LAdicSheaf.finrank_rationalGeometricCompactlySupportedCohomology_constant_one` (Tag 0C1Z,
`Trace/ConstantCurveH1Trace.lean`): `dim H¹(X_k̄, ℚ_ℓ) = 2 · genus X_k̄`

is recorded here as the named proposition `H1RankFormula`, whose statement is that theorem's
statement verbatim (all its hypotheses as binders), so that

`H1RankFormula = fun … => LAdicSheaf.finrank_rationalGeometricCompactlySupportedCohomology_constant_one …`

once `ConstantCurveH1Trace` is built (see `docs/IHARA_CURVE_H1_BETTI.md`: its closure contains two
modules whose elaboration exceeds the 6 GB per-process memory cap of this build, so it is not
imported here). Everything else is proved:

* `finrank_rationalCohomology_one_eq_two_mul_genus`: `H1RankFormula → dim H¹(X_k̄, ℚ_ℓ) = 2 · genus X`;
* `hasFirstBettiTwo_weierstrass`: `H1RankFormula → HasFirstBettiTwo (projOf W) …` for `W` elliptic;
* `charpoly_weierstrassH1'`: M4a for `projOf W` from `[W.IsElliptic]`, `H1RankFormula` and
  `RealizesWeierstrass` only (geometric connectedness is the instance
  `connectedSpace_weierstrass_geometric` of `CurveH1BettiConnected`).
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
  AlgebraicGeometry.ModuliEllipticCurves.Weierstrass Stacks.EtaleCohomology Stacks.Frobenius
  Polynomial Module

universe u

namespace RamanujanWeil.Ihara

attribute [local instance] HasDerivedCategory.standard fact_ringChar_prime

/-- A proper scheme over a field is noetherian, hence quasi-separated (as in `Weil.Definitions`). -/
local instance quasiSeparatedSpace_of_isNoetherian {X : Scheme.{u}} [IsNoetherian X] :
    QuasiSeparatedSpace X :=
  @IsLocallyNoetherian.quasiSeparatedSpace X (inferInstance : IsNoetherian X).toIsLocallyNoetherian

/-- **Stacks, Tag 0C1Z, for the constant system** (statement of
`Stacks.EtaleCohomology.LAdicSheaf.finrank_rationalGeometricCompactlySupportedCohomology_constant_one`,
`StacksFrontier/AlgebraicGeometry/EtaleCohomology/Trace/ConstantCurveH1Trace.lean`, with every
hypothesis of that theorem as a binder): for `X` proper over a finite field `k` with `X_k̄` a
smooth proper curve and `ℓ` invertible in `k̄`, `dim H¹(X_k̄, ℚ_ℓ) = 2 · genus X_k̄`. -/
def H1RankFormula : Prop :=
  ∀ (B : BigEtaleSite.{u}) (X : B.Scheme) (ℓ : ℕ) [IsNoetherian X.1] [Fact ℓ.Prime]
    {k : Type u} [Field k] [Fintype k] (f : X.1 ⟶ Spec (.of k)) [IsProper f]
    (kbar : Type u) [Field kbar] [Algebra k kbar] (p q : ℕ) [Fact p.Prime] [CharP k p]
    (_hcard : Fintype.card k = p ^ q) [IsAlgClosed kbar]
    [IsCurve kbar (pullback.snd (Over.mk f).hom (specAlgebraMap k kbar))]
    [Smooth (pullback.snd (Over.mk f).hom (specAlgebraMap k kbar))]
    [IsProper (pullback.snd (Over.mk f).hom (specAlgebraMap k kbar))],
    IsUnit (ℓ : kbar) →
      Module.finrank ℚ_[ℓ] (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f
          (CompactificationOf.ofProper f) kbar (LAdicSheaf.constantSystem B X ℓ) ((1 : ℕ) : ℤ)) =
        2 * genus (pullback.snd (Over.mk f).hom (specAlgebraMap k kbar))

/-- `ℓ ≠ char k`, `ℓ` prime, makes `ℓ` a unit in any extension field of `k`. -/
theorem isUnit_natCast_of_ne_ringChar {k : Type u} [Field k] (K : Type u) [Field K]
    [Algebra k K] (ℓ : ℕ) [hℓ : Fact ℓ.Prime] [hℓk : Fact (ℓ ≠ ringChar k)]
    (hp : (ringChar k).Prime) : IsUnit (ℓ : K) := by
  have hk : (ℓ : k) ≠ 0 := by
    intro h
    rw [ringChar.spec] at h
    rcases (Nat.dvd_prime hℓ.out).mp h with h1 | h1
    · exact hp.one_lt.ne' h1
    · exact hℓk.out h1.symm
  rw [isUnit_iff_ne_zero, ← map_natCast (algebraMap k K)]
  exact (_root_.map_ne_zero _).mpr hk

section General

variable {B : BigEtaleSite.{u}} (X : B.Scheme) {k : Type u} [Field k] [Fintype k]
  (f : X.1 ⟶ Spec (.of k)) [IsProper f] [SmoothOfRelativeDimension 1 f] (ℓ : ℕ) [Fact ℓ.Prime]
  [Fact (ℓ ≠ ringChar k)]

/-- **`dim H¹(X_k̄, ℚ_ℓ) = 2g`** for `X` proper and smooth of relative dimension one over the
finite field `k` with `H⁰(X, 𝒪_X) = k`, `g = genus X`, from Tag 0C1Z on `X_k̄` and invariance of
the genus under `k → k̄`. -/
theorem finrank_rationalCohomology_one_eq_two_mul_genus (hS : H1RankFormula.{u})
    (h0 : Module.finrank k (structureSheafCohomology f 0) = 1) :
    finrank ℚ_[ℓ] (Weil.rationalCohomology B X f ℓ 1) = 2 * genus f := by
  have : IsNoetherian X.1 := Weil.isNoetherian_of_isProper f
  have : CharP k (ringChar k) := ringChar.charP k
  have : IsProper (Over.mk f).hom := inferInstanceAs (IsProper f)
  have : SmoothOfRelativeDimension 1 (Over.mk f).hom :=
    inferInstanceAs (SmoothOfRelativeDimension 1 f)
  have : IsCurve (AlgebraicClosure k)
      (pullback.snd (Over.mk f).hom (specAlgebraMap k (AlgebraicClosure k))) :=
    isCurve_baseChange_of_finrank_zero (Over.mk f).hom (AlgebraicClosure k) h0
  have : Smooth (pullback.snd (Over.mk f).hom (specAlgebraMap k (AlgebraicClosure k))) :=
    SmoothOfRelativeDimension.smooth 1 _
  have h := hS B X ℓ f (AlgebraicClosure k) (ringChar k) (cardExp k) card_eq_ringChar_pow
    (isUnit_natCast_of_ne_ringChar (AlgebraicClosure k) ℓ (CharP.char_is_prime k _))
  rw [genus_pullback_snd (Over.mk f).hom (AlgebraicClosure k)] at h
  exact h

/-- **`HasFirstBettiTwo` for a curve of genus one** with `H⁰(X, 𝒪_X) = k`. -/
theorem hasFirstBettiTwo_of_genus_eq_one (hS : H1RankFormula.{u})
    (h0 : Module.finrank k (structureSheafCohomology f 0) = 1) (hg : genus f = 1) :
    HasFirstBettiTwo X f ℓ := by
  unfold HasFirstBettiTwo
  rw [finrank_rationalCohomology_one_eq_two_mul_genus X f ℓ hS h0, hg]

end General

section Weierstrass

variable {k : Type u} [Field k] [Fintype k] (W : WeierstrassCurve k) [W.IsElliptic]
  (B : BigEtaleSite.{u}) (ℓ : ℕ) [Fact ℓ.Prime] [Fact (ℓ ≠ ringChar k)]

/-- **Gap 1 of M4a, modulo Tag 0C1Z**: `dim H¹(E_k̄, ℚ_ℓ) = 2` for the plane cubic `E` of an
elliptic Weierstrass curve over `𝔽_q`. -/
theorem hasFirstBettiTwo_weierstrass (hS : H1RankFormula.{u}) :
    HasFirstBettiTwo (weierstrassScheme W B) (projectionOf W) ℓ :=
  hasFirstBettiTwo_of_genus_eq_one (weierstrassScheme W B) (projectionOf W) ℓ hS
    (finrank_structureSheafCohomology_projectionOf_zero W) (genus_projectionOf W)

/-- **M4a for the Weierstrass cubic, gaps 1 and 3 discharged** (gap 1 modulo the Stacks
statement `H1RankFormula`). For `W` over `𝔽_q` with `Δ ≠ 0`, `E = projOf W` and `ℓ ≠ p`: if
`#E(k_n) = #W(k_n)` for `n ≥ 1`, then `charpoly(Frob | H¹(E_k̄, ℚ_ℓ)) = X² − aX + q` with
`a = q + 1 − #W(k)`. -/
theorem charpoly_weierstrassH1' (hS : H1RankFormula.{u})
    (hW : RealizesWeierstrass (weierstrassScheme W B) (projectionOf W) W) :
    (Weil.rationalFrobenius B (weierstrassScheme W B) (projectionOf W) ℓ 1).charpoly =
      Polynomial.X ^ 2 -
          C (((Fintype.card k : ℤ) + 1 - Nat.card W.toAffine.Point : ℤ) : ℚ_[ℓ]) * Polynomial.X +
        C (Fintype.card k : ℚ_[ℓ]) :=
  charpoly_weierstrassH1 W B ℓ (hasFirstBettiTwo_weierstrass W B ℓ hS) hW

/-- Point counts over every `𝔽_{qⁿ}` and the traces of `Frobⁿ` on `H¹(E_k̄, ℚ_ℓ)`, from
`H1RankFormula` and `RealizesWeierstrass`. -/
theorem natCard_point_extension_eq_weierstrassH1' (hS : H1RankFormula.{u})
    (hW : RealizesWeierstrass (weierstrassScheme W B) (projectionOf W) W) (n : ℕ) (hn : 1 ≤ n) :
    haveI : NeZero n := ⟨by omega⟩
    (Nat.card (W.baseChange (FiniteField.Extension k (ringChar k) n)).toAffine.Point : ℤ) =
      (Fintype.card k : ℤ) ^ n + 1 -
        frobPowerSum ((Fintype.card k : ℤ) + 1 - Nat.card W.toAffine.Point) (Fintype.card k) n ∧
    LinearMap.trace ℚ_[ℓ] _
        (Weil.rationalFrobenius B (weierstrassScheme W B) (projectionOf W) ℓ 1 ^ n) =
      frobPowerSum ((Fintype.card k : ℤ) + 1 - Nat.card W.toAffine.Point) (Fintype.card k) n :=
  natCard_point_extension_eq_of_weierstrass (weierstrassScheme W B) (projectionOf W) ℓ
    (exists_section_projectionOf W) W (hasFirstBettiTwo_weierstrass W B ℓ hS) hW n hn

include ℓ in
/-- Hasse's bound `(q + 1 − #W(k))² ≤ 4q`, from `H1RankFormula` and `RealizesWeierstrass`. -/
theorem sq_le_four_mul_card_weierstrassH1' (hS : H1RankFormula.{u})
    (hW : RealizesWeierstrass (weierstrassScheme W B) (projectionOf W) W) :
    ((Fintype.card k : ℤ) + 1 - Nat.card W.toAffine.Point) ^ 2 ≤ 4 * Fintype.card k :=
  sq_le_four_mul_card_of_weierstrass (weierstrassScheme W B) (projectionOf W) ℓ
    (exists_section_projectionOf W) W (hasFirstBettiTwo_weierstrass W B ℓ hS) hW

end Weierstrass

end RamanujanWeil.Ihara
