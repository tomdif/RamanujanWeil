import RamanujanWeil.Ihara.WeilPackageTrace
import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.WeilIIWeightBound
import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.WeilIIAssembly
import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.WeilIIFinalAssemblyAbsIrrCharNe
import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FourierDeligne.LaumonFourierLineAbsIrrInputProof
import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LaumonFourierLineLatticeInputProof
import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LaumonFlatLevelZeroFirstProjectionProof
import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LaumonFamilyNoPunctualSectionsCharNe
import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LaumonDegenerationFamilyAssembly
import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Purity.KummerClassMapStalks
import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Purity.TwistNegOneTowerInverseImageIso
import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Purity.RelativeCurvePurityLAdic
import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CompactificationIndependence.Independence

/-!
# M2: the Lefschetz package of a lisse pure sheaf, from Axiom/Stacks

For a lisse ℓ-adic sheaf `F` (`ℓ ≠ p`) on a noetherian `B`-scheme `X`, separated and of finite
type over a finite field `k` with `p ^ q` elements, pointwise `ι`-mixed of weights `≤ w` and
`ι`-realizable (Stacks' hypotheses of Weil II 3.3.1), and `topologicalKrullDim X ≤ d`, we build a
`LefschetzPackage ℚ_[ℓ] ι (p ^ q) w d (pointSum F)`:

* `V i = Hⁱ_c(X_k̄, F ⊗ ℚ_ℓ)` (`rationalGeometricCompactlySupportedCohomology`, degree `i : ℤ`,
  `0 ≤ i ≤ 2d`), written in `Module.finBasis`; `F i` = the geometric Frobenius
  `rationalGeometricCompactlySupportedFrobenius`;
* weights from `LAdicSheaf.SatisfiesWeightBound` (unconditional, Laumon inputs discharged), which
  gives `‖ι z‖ = (p^q)^(w'/2)` with `w' ≤ w + i`, hence `≤ (p^q)^((w+i)/2)`;
* the trace identity for **every** `n ≥ 1` from Tag 03V0
  (`rationalLFunction_eq_gradedCharSeries_compactSupportFrobenius`) by comparing the `Tⁿ`
  coefficients of the logarithmic derivatives
  (`FrobeniusMatrices.coeff_logDerivative_lFunction`, `coeff_logDerivative_gradedCharSeries`);
* the vanishing of `Hⁱ_c` outside `0 ≤ i ≤ 2 dim X` and finite-dimensionality from Tag 03V2
  (`LAdicSheaf.traceFormula`).

The point side is
`pointSum F n = ∑ᶠ (x : |X|) (_ : deg x ∣ n), deg x · tr((π_x^*)^{n / deg x} | F_x̄ ⊗ ℚ_ℓ)`:
closed points `x` with `deg x = [κ(x) : k]` dividing `n`, weighted by `deg x`, with the trace of
the `(n / deg x)`-th power of the geometric Frobenius of `κ(x)` on the rational stalk. (Each such
`x` accounts for exactly `deg x` points of `X(k_n)`, `[k_n : k] = n`; that bijection is M6.)
-/

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.SmallEtale Stacks.EtaleCohomology
  PowerSeries

universe u

namespace RamanujanWeil.Ihara

attribute [local instance] HasDerivedCategory.standard

variable (B : BigEtaleSite.{u}) (X : B.Scheme) (ℓ : ℕ) [Fact ℓ.Prime]
  [∀ (n : ℕ) (S T : B.Scheme) (g : T ⟶ S),
    ((AlgebraicGeometry.smallEtaleBaseChange B g).sheafPushforwardContinuous
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
      (SmallEtale.topology B S.1 S.property)
      (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
  [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
    HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [∀ (n : ℕ) (T : B.Scheme), HasWeakSheafify (SmallEtale.topology B T.1 T.property)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [IsNoetherian X.1]
  {k : Type u} [Field k] [Fintype k] (f : X.1 ⟶ Spec (.of k))
  [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f]

/-! ### Weil II (unconditional) -/

/-- **Weil II 3.3.1 for lisse sheaves, unconditional** (the probe `probe_satisfiesWeightBound`
made a lemma): weights of `Hⁱ_c(X_k̄, F)` are `≤ w + i`. All Laumon/purity inputs discharged. -/
theorem satisfiesWeightBound (kbar : Type u) [Field kbar] [Algebra k kbar] [IsAlgClosure k kbar]
    (p q : ℕ) [Fact p.Prime] [CharP k p] (hcard : Fintype.card k = p ^ q) (hℓ : ℓ ≠ p)
    (ι : ℚ_[ℓ] →+* ℂ) :
    LAdicSheaf.SatisfiesWeightBound B ℓ kbar p q hcard ι X f :=
  LAdicSheaf.satisfiesWeightBound_of_laumonInputs
    (laumonFibrePurityInput_of_absIrr' laumonFourierLineAbsIrrInput' laumonFourierLineLatticeInput)
    (laumonDegenerationFamilyInput_of_noPunctualSections
      (laumonFamilyNoPunctualSectionsInput'_of_levelZero'
        (laumonFamilyFlatLevelZeroVanishingInput'_of_firstProjection
          laumonFamilyFirstProjectionVanishingInput')))
    (Purity.relativeCurvePurityInput_of_isIsoStalksOver B ℓ
      (Purity.twistNegOneTowerInverseImageInput B ℓ) Purity.purityClassMapStalkIsoInput)
    kbar p q hcard hℓ ι X f

/-! ### The package -/

section Package

variable (j : CompactificationOf (Over.mk f)) (kbar : Type u) [Field kbar] [Algebra k kbar]
  [IsAlgClosure k kbar] (p q : ℕ) [Fact p.Prime] [CharP k p] (hcard : Fintype.card k = p ^ q)

/-- **M2 headline (data).** The Lefschetz package of a lisse, pointwise `ι`-mixed of weights
`≤ w`, `ι`-realizable ℓ-adic sheaf on `X` with `dim X ≤ d`: `V i = Hⁱ_c(X_k̄, F)` in
`Module.finBasis`, `F i` = geometric Frobenius, `Q = p ^ q = #k`, `P = pointSum F`. -/
noncomputable def lefschetzPackageOfLissePure (hℓp : ℓ ≠ p) (ι : ℚ_[ℓ] →+* ℂ) (d : ℕ)
    (hdim : topologicalKrullDim X.1 ≤ d) (F : LAdicSheaf.{u, u + 1} B X ℓ) (w : ℤ)
    (hF : F.IsLisse) (hmix : LAdicSheaf.IsPointwiseMixedOfWeightLE B X ℓ f F (p ^ q) ι w)
    (hreal : LAdicSheaf.IsIotaRealizable B X ℓ f F ι) :
    LefschetzPackage ℚ_[ℓ] ι (p ^ q) w d (pointSum B X ℓ f F) :=
  haveI := (LAdicSheaf.traceFormula B X ℓ f j kbar p q hcard hℓp F).1
  { rank := fun i => Module.finrank ℚ_[ℓ]
      (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f j kbar F ((i : ℕ) : ℤ))
    frob := fun i => LinearMap.toMatrix (Module.finBasis ℚ_[ℓ] _) (Module.finBasis ℚ_[ℓ] _)
      (LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B X ℓ f j kbar p q hcard F
        ((i : ℕ) : ℤ)).hom
    weight_le := fun i z hz => by
      rw [LinearMap.charpoly_toMatrix] at hz
      obtain ⟨w', hw', hz'⟩ := satisfiesWeightBound B X ℓ f kbar p q hcard hℓp ι j F w hF hmix
        hreal ((i : ℕ) : ℤ) z hz
      rw [hz']
      have hQ : (1 : ℝ) ≤ ((p ^ q : ℕ) : ℝ) := by
        exact_mod_cast Nat.one_le_pow _ _ (Fact.out : p.Prime).pos
      refine Real.rpow_le_rpow_of_exponent_le hQ ?_
      have : (w' : ℝ) ≤ (w : ℝ) + ((i : ℕ) : ℝ) := by exact_mod_cast hw'
      linarith
    trace_eq := fun n hn => by
      have h := alternating_trace_pow_eq_pointSum B X ℓ f j kbar p q hcard hℓp d hdim F
        (n := n) (by omega)
      rw [finsum_int_eq_sum_fin d _ fun i hi => by
        by_contra hb
        refine hi ?_
        have : Subsingleton (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f j
            kbar F i) := by
          by_contra hns
          rw [not_subsingleton_iff_nontrivial] at hns
          exact hb (nonneg_and_le_of_nontrivial B X ℓ f j kbar p q hcard hℓp d hdim F i hns)
        simp only [Subsingleton.elim (_ ^ n) (0 : Module.End ℚ_[ℓ] _), map_zero, mul_zero]] at h
      rw [← h]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [ite_even_natCast, trace_toMatrix_pow] }

include j kbar hcard in
/-- **M2 headline.** Every lisse, pointwise `ι`-mixed `≤ w`, `ι`-realizable ℓ-adic sheaf on a
separated finite-type `X/𝔽_{p^q}` with `dim X ≤ d` has a Lefschetz package with point side
`pointSum F`, for every compactification `j`. -/
theorem lefschetzPackage_of_lisse_pure (hℓp : ℓ ≠ p) (ι : ℚ_[ℓ] →+* ℂ) (d : ℕ)
    (hdim : topologicalKrullDim X.1 ≤ d) (F : LAdicSheaf.{u, u + 1} B X ℓ) (w : ℤ)
    (hF : F.IsLisse) (hmix : LAdicSheaf.IsPointwiseMixedOfWeightLE B X ℓ f F (p ^ q) ι w)
    (hreal : LAdicSheaf.IsIotaRealizable B X ℓ f F ι) :
    Nonempty (LefschetzPackage ℚ_[ℓ] ι (p ^ q) w d (pointSum B X ℓ f F)) :=
  ⟨lefschetzPackageOfLissePure B X ℓ f j kbar p q hcard hℓp ι d hdim F w hF hmix hreal⟩

end Package

/-- Same, with the compactification (Nagata, Tag 0F41) and the algebraic closure supplied. -/
theorem lefschetzPackage_of_lisse_pure' (p q : ℕ) [Fact p.Prime] [CharP k p]
    (hcard : Fintype.card k = p ^ q) (hℓp : ℓ ≠ p) (ι : ℚ_[ℓ] →+* ℂ) (d : ℕ)
    (hdim : topologicalKrullDim X.1 ≤ d) (F : LAdicSheaf.{u, u + 1} B X ℓ) (w : ℤ)
    (hF : F.IsLisse) (hmix : LAdicSheaf.IsPointwiseMixedOfWeightLE B X ℓ f F (p ^ q) ι w)
    (hreal : LAdicSheaf.IsIotaRealizable B X ℓ f F ι) :
    Nonempty (LefschetzPackage ℚ_[ℓ] ι (p ^ q) w d (pointSum B X ℓ f F)) := by
  obtain ⟨j⟩ : Nonempty (CompactificationOf (Over.mk f)) := IsCofiltered.nonempty
  exact lefschetzPackage_of_lisse_pure B X ℓ f j (AlgebraicClosure k) p q hcard hℓp ι d hdim F w
    hF hmix hreal

end RamanujanWeil.Ihara
