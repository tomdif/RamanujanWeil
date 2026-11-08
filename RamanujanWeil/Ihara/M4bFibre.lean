import RamanujanWeil.Ihara.PointsFibre
import RamanujanWeil.Ihara.PointsRealizes
import RamanujanWeil.Ihara.CurveH1Betti
import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.WeilIIAssembly
import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CompactSupportSchemeIsoTransport
import Weil.AlgebraicGeometry.EtaleCohomology.Trace.ConnectedComponentsCharpoly

/-!
# M4b: the stalks of `R¹` are the `H¹` of the fibre curves

For a closed point `y` of `W_p = Spec 𝔽_p[a₁..a₆][1/Δ]` with residue field `κ = κ(y)` and fibre
curve `E_y = fibreCurve p y = (curve p).map (residueMapOf y)` over `κ`:

`charpoly(π_y | R¹_ȳ ⊗ ℚ_ℓ) = charpoly(F₁ | H¹((projOf E_y)_κ̄, ℚ_ℓ))`
(`charpoly_rationalStalkFrobenius_R1_eq`), by the chain

1. proper base change with Frobenius, Stacks
   `LAdicSheaf.higherDirectImageStalkInput_higherDirectImageShriek` (Tags 0F7L/0F7J), with its two
   inputs discharged exactly as in Stacks' `WeilIIAssembly`: the stalk is `H¹_c` of the scheme
   fibre `E ×_{W_p} Spec κ` with coefficients `ι⁻¹ ℤ_ℓ`, for some compactification `j_w`;
2. Weil's `charpoly_frobenius_inverseImage_constantSystem` (`ι⁻¹ℤ_ℓ ≅ ℤ_ℓ`, independence of the
   compactification, Tag 0F7I): this is `charpoly(Weil.rationalFrobenius (fibre) 1)`;
3. `charpoly_rationalFrobenius_eq_of_isIso` (here; from Stacks'
   `rationalGeometricCompactlySupportedCohomologyIsoOfIsIso_hom_frobenius` and Weil's bridge
   again): transport along the isomorphism `fibre ≅ projOf E_y` over `κ` given by
   `isPullback_fromSpecResidueField`.

Then M4a at `E_y` (`charpoly_weierstrassH1'`, `natCard_point_extension_eq_weierstrassH1'`,
`sq_le_four_mul_card_weierstrassH1'`, `realizesWeierstrass_projOf`) gives all three conjuncts of
`R1StalkCharpolyFibre` (`r1StalkCharpolyFibre_of_h1RankFormula`), modulo `H1RankFormula`, which
`RamanujanWeil.Ihara.M4b` discharges with `h1RankFormula` (CurveH1BettiStacks).
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.SmallEtale
  Stacks.EtaleCohomology AlgebraicGeometry.ModuliEllipticCurves.Weierstrass

noncomputable section

namespace RamanujanWeil.Ihara

attribute [local instance] HasDerivedCategory.standard moduleCat_hasLimitsOfSize

section Transport

universe u

variable {B : BigEtaleSite.{u}} {ℓ : ℕ} [Fact ℓ.Prime]
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

/-- **`charpoly(F_ν)` is invariant under an isomorphism of proper schemes over `𝔽_q`.** -/
theorem charpoly_rationalFrobenius_eq_of_isIso {k : Type u} [Field k] [Fintype k]
    [Fact (ℓ ≠ ringChar k)] {X X' : B.Scheme} (g : X' ⟶ X) [IsIso (B.inclusion.map g)]
    (f : X.1 ⟶ Spec (.of k)) [IsProper f] (f' : X'.1 ⟶ Spec (.of k)) [IsProper f']
    (hf : B.inclusion.map g ≫ f = f') (ν : ℕ) :
    (Weil.rationalFrobenius B X' f' ℓ ν).charpoly = (Weil.rationalFrobenius B X f ℓ ν).charpoly := by
  subst hf
  have : Fact (ringChar k).Prime := ⟨CharP.char_is_prime k _⟩
  have hℓ : ℓ ≠ ringChar k := Fact.out
  have : IsNoetherian X.1 := Weil.isNoetherian_of_isProper f
  have : IsNoetherian X'.1 := Weil.isNoetherian_of_isProper (B.inclusion.map g ≫ f)
  have : QuasiSeparatedSpace X.1 :=
    @IsLocallyNoetherian.quasiSeparatedSpace X.1 IsNoetherian.toIsLocallyNoetherian
  have : QuasiSeparatedSpace X'.1 :=
    @IsLocallyNoetherian.quasiSeparatedSpace X'.1 IsNoetherian.toIsLocallyNoetherian
  set j := (CompactificationOf.ofProper f).restrictOpen (B.inclusion.map g)
  have := LAdicSheaf.finiteDimensional_rationalGeometricCompactlySupportedCohomology B ℓ
    (AlgebraicClosure k) (ringChar k) _ (FiniteField.card k (ringChar k)).choose_spec.2 hℓ X'
    (B.inclusion.map g ≫ f) j (LAdicSheaf.inverseImage g (LAdicSheaf.constantSystem B X ℓ)) ν
  have := LAdicSheaf.finiteDimensional_rationalGeometricCompactlySupportedCohomology B ℓ
    (AlgebraicClosure k) (ringChar k) _ (FiniteField.card k (ringChar k)).choose_spec.2 hℓ X
    f (CompactificationOf.ofProper f) (LAdicSheaf.constantSystem B X ℓ) ν
  rw [← Weil.charpoly_frobenius_inverseImage_constantSystem g (B.inclusion.map g ≫ f) j ν]
  exact charpoly_eq_of_comm_iso inferInstance inferInstance
    (LAdicSheaf.rationalGeometricCompactlySupportedCohomologyIsoOfIsIso B ℓ g f
      (CompactificationOf.ofProper f) (AlgebraicClosure k) ν (LAdicSheaf.constantSystem B X ℓ)) _ _
    (LAdicSheaf.rationalGeometricCompactlySupportedCohomologyIsoOfIsIso_hom_frobenius B ℓ g f
      (CompactificationOf.ofProper f) (AlgebraicClosure k) ν (ringChar k) _
      (FiniteField.card k (ringChar k)).choose_spec.2 (LAdicSheaf.constantSystem B X ℓ))

end Transport

end RamanujanWeil.Ihara

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

/-- The fibre `E_y = E ×_{W_p} Spec κ(y)` lies in every big étale site (`κ(y)` finite). -/
theorem contains_fiber (y : Family.base p) [Fintype ((Family.base p).residueField y)] :
    B.Contains ((Family.proj p).fiber y) :=
  Scheme.size_lt_of_locallyOfFiniteType_of_quasiCompact
    ((Family.proj p).fiberToSpecResidueField y)
    (contains_spec_finite (k := (Family.base p).residueField y) B)

instance isElliptic_fibreCurve (y : Family.base p) : (Family.fibreCurve p y).IsElliptic :=
  inferInstanceAs ((Family.curve p).map (residueMapOf y)).IsElliptic

/-- `κ(y)` as `Scheme.residueField`. -/
abbrev κw (y : (Wp p B).1) : Type := (Wp p B).1.residueField y

/-- `κ(y)` in the unfolded form produced by unifying `Spec (.of ?k)` with `Spec κ(y)`. -/
abbrev κs (y : (Wp p B).1) : Type := IsLocalRing.ResidueField ((B.inclusion.obj (Wp p B)).presheaf.stalk y)

/-- **M4b transport.** At a closed point `y` of `W_p`, the stalk Frobenius of `R¹` has the
characteristic polynomial of the Frobenius on `H¹` of the plane cubic of the fibre curve. -/
theorem charpoly_rationalStalkFrobenius_R1_eq (y : closedPoints (Wp p B).1)
    [Fintype (κw p B y.1)] [Fact (ℓ ≠ ringChar (κw p B y.1))] :
    (LAdicSheaf.rationalStalkFrobenius B (Wp p B) ℓ (R1 p B ℓ) y.1
        (finite_residueField (toSpecK p B) y.1 y.2)).charpoly =
      (Weil.rationalFrobenius B (weierstrassScheme (Family.fibreCurve p y.1) B)
        (projectionOf (Family.fibreCurve p y.1)) ℓ 1).charpoly := by
  have : Fact (ringChar (κw p B y.1)).Prime := ⟨CharP.char_is_prime (κw p B y.1) _⟩
  have hℓ : ℓ ≠ ringChar (κw p B y.1) := Fact.out
  have hB : B.Contains ((B.inclusion.map (π p B)).fiber y.1) := contains_fiber p B y.1
  have hprop : IsProper ((B.inclusion.map (π p B)).fiberToSpecResidueField y.1) :=
    inferInstanceAs (IsProper ((Family.proj p).fiberToSpecResidueField y.1))
  have : @IsProper _ (Spec (.of (κw p B y.1))) ((B.inclusion.map (π p B)).fiberToSpecResidueField y.1) :=
    hprop
  have hN : IsNoetherian ((B.inclusion.map (π p B)).fiber y.1) :=
    Weil.isNoetherian_of_isProper (k := (κw p B y.1)) ((B.inclusion.map (π p B)).fiberToSpecResidueField y.1)
  have hstalk : LAdicSheaf.HigherDirectImageStalkInput
      (LAdicSheaf.higherDirectImageShriekFamily B ℓ) :=
    LAdicSheaf.higherDirectImageStalkInput_higherDirectImageShriek B ℓ
      (lowerShriekConstructibilityInput B)
      (by
        intro U W _ _ g _ _ _ jg k _ _ fW _ _ _ jW kbar _ _ p q _ _ hcard
        exact LAdicSheaf.lerayFrobeniusComparison B ℓ g jg fW jW kbar p q hcard)
  obtain ⟨jw, hjw⟩ := hstalk (ZMod p) (Ep p B) (Wp p B) (π p B) (jπ p B) (toSpecK p B) y hB
    (AlgebraicClosure (κw p B y.1)) (ringChar (κw p B y.1)) _ (FiniteField.card (κw p B y.1) (ringChar (κw p B y.1))).choose_spec.2
  let Fy : B.Scheme := B.obj _ hB
  let ι : Fy ⟶ Ep p B := ObjectProperty.homMk ((B.inclusion.map (π p B)).fiberι y.1)
  have : IsNoetherian Fy.1 := hN
  have : QuasiSeparatedSpace Fy.1 :=
    @IsLocallyNoetherian.quasiSeparatedSpace ((B.inclusion.map (π p B)).fiber y.1)
      IsNoetherian.toIsLocallyNoetherian
  have : FiniteDimensional ℚ_[ℓ] (LAdicSheaf.rationalGeometricCompactlySupportedCohomology (k := κw p B y.1) B Fy ℓ
      ((B.inclusion.map (π p B)).fiberToSpecResidueField y.1) jw (AlgebraicClosure (κw p B y.1))
      (LAdicSheaf.inverseImage ι (constE p B ℓ)) ((1 : ℕ) : ℤ)) :=
    LAdicSheaf.finiteDimensional_rationalGeometricCompactlySupportedCohomology (k := κw p B y.1) B ℓ
      (AlgebraicClosure (κw p B y.1)) (ringChar (κw p B y.1)) _ (FiniteField.card (κw p B y.1) (ringChar (κw p B y.1))).choose_spec.2 hℓ Fy
      _ jw _ _
  refine (@hjw (constE p B ℓ) 1 this).trans ?_
  refine (Weil.charpoly_frobenius_inverseImage_constantSystem (k := κw p B y.1) ι
    ((B.inclusion.map (π p B)).fiberToSpecResidueField y.1) jw 1).trans ?_
  have hP := isPullback_fromSpecResidueField (Family.curve p) y.1
  let α : Fy ⟶ weierstrassScheme (Family.fibreCurve p y.1) B :=
    ObjectProperty.homMk hP.isoPullback.inv
  have : IsIso (B.inclusion.map α) := inferInstanceAs (IsIso hP.isoPullback.inv)
  exact charpoly_rationalFrobenius_eq_of_isIso α (projectionOf (Family.fibreCurve p y.1))
    ((B.inclusion.map (π p B)).fiberToSpecResidueField y.1) hP.isoPullback_inv_snd 1

/-- `ringChar κ(y) = p` at every point of `W_p`. -/
theorem ringChar_residueField_Wp (y : (Wp p B).1) : ringChar ((Wp p B).1.residueField y) = p := by
  have : CharP ((Wp p B).1.residueField y) p :=
    charP_of_injective_ringHom (fieldToResidue (toSpecK p B) y).hom.injective p
  exact ringChar.eq _ p

/-- **M4b, conditional on `H1RankFormula`** (the statement of Stacks' Tag 0C1Z theorem). -/
theorem r1StalkCharpolyFibre_of_h1RankFormula (hS : H1RankFormula.{0}) (hℓp : ℓ ≠ p) :
    R1StalkCharpolyFibre p B ℓ := by
  intro y
  have := finite_residueField (toSpecK p B) y.1 y.2
  let : Fintype (κw p B y.1) := Fintype.ofFinite _
  have : Fact (ℓ ≠ ringChar (κw p B y.1)) :=
    ⟨by rw [ringChar_residueField_Wp p B y.1]; exact hℓp⟩
  have hW := realizesWeierstrass_projOf (Family.fibreCurve p y.1) B
  have hcard : (Fintype.card (κw p B y.1) : ℤ) =
      (p : ℤ) ^ residueDegree (toSpecK p B) y.1 := by
    rw [← Nat.card_eq_fintype_card, Family.natCard_residueField p y.1 y.2]
    push_cast; rfl
  have htr : traceOfFrob (Family.fibreCurve p y.1) =
      (Fintype.card (κw p B y.1) : ℤ) + 1 -
        Nat.card (Family.fibreCurve p y.1).toAffine.Point := by
    rw [traceOfFrob, Nat.card_eq_fintype_card]
  refine ⟨?_, ?_, ?_⟩
  · rw [htr, ← hcard]
    exact sq_le_four_mul_card_weierstrassH1' _ B ℓ hS hW
  · rw [charpoly_rationalStalkFrobenius_R1_eq p B ℓ y, charpoly_weierstrassH1' _ B ℓ hS hW, htr]
    have hq : (Fintype.card (κw p B y.1) : ℚ_[ℓ]) =
        (p : ℚ_[ℓ]) ^ residueDegree (toSpecK p B) y.1 := by exact_mod_cast hcard
    rw [hq]
  · exact (extensionTraces_of_extension _ fun n hn =>
      (natCard_point_extension_eq_weierstrassH1' _ B ℓ hS hW n hn).1).congr_q hcard

end RamanujanWeil.Ihara
