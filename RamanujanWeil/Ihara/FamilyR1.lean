import RamanujanWeil.Ihara.FamilyGeometry
import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LowerShriekLocallyConstantClosure
import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmoothProperHigherDirectImageLocallyConstantNoetherian
import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LaumonFlatLevelZeroDegreeZero
import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.HigherDirectImageTopGysinMorphismShriek
import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.ConstantLevelExtComparison
import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleSheaves.ConstantFiniteModule
import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Purity.AffineLineChartVanishing

/-!
# M3 (ℓ-adic): `R¹ = R¹π_! ℤ_ℓ` of the universal Weierstrass curve over `W_p`, and its lisseness

Standing context: the one of `RamanujanWeil.Ihara.lefschetzPackage_of_lisse_pure'` (M2) at universe
`0`: `B : BigEtaleSite.{0}` with the three families of site instances for the coefficient rings
`ℤ/ℓⁿ⁺¹`, `ℓ` prime.

* `Wp p B : B.Scheme` is `W_p = Spec 𝔽_p[a₁..a₆][1/Δ]` (`Family.base p`), `Ep p B` the universal
  curve `E` (`Family.total p`), `π p B : Ep p B ⟶ Wp p B` the projection and
  `toSpecK p B : (Wp p B).1 ⟶ Spec 𝔽_p` the structure morphism (locally of finite type,
  quasi-compact, separated), `topologicalKrullDim (Wp p B).1 ≤ 5`.
* `jπ p B` is the identity compactification of the proper `π` (`CompactificationOf.ofProper`).
* `R1 p B ℓ := higherDirectImageShriek B ℓ (π p B) (jπ p B) (constantSystem B (Ep p B) ℓ) 1`:
  the ℓ-adic sheaf `R¹π_! ℤ_ℓ = R¹π_* ℤ_ℓ` on `W_p`.
* **`isLisse_R1 : (R1 p B ℓ).IsLisse`** for `ℓ ≠ p`, unconditionally.

Proof of lisseness. By `LAdicSheaf.isLisse_higherDirectImageShriek_of_levelZero` it suffices that
every `Rˢπ_! G'₀` is locally constant of finite type as a sheaf of `ℤ_ℓ`-modules, `G'₀` the level
zero of the flat model of `ℤ_ℓ`. `G'₀` is locally constant of finite type (the constant ℓ-adic
sheaf is lisse, `isLisse_constantSystem`, hence so is its flat model) and killed by `ℓ`, and `ℓ` is
prime to every residue characteristic of `E` (all equal to `p`). For the identity
compactification `Rˢπ_! = Rˢπ_*` (`derivedLowerShriekOfProperIso`), which vanishes for `s < 0`, and
for `s ≥ 0` Tag 0GLI over the Noetherian base `W_p`
(`isFiniteTypeLocallyConstantModuleSheaf_rightDerived_of_smooth_of_isProper_of_isNoetherian`)
gives local constancy, `π` being smooth and proper.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.SmallEtale
  Stacks.EtaleCohomology CategoryTheory.LAdicTower

noncomputable section

namespace RamanujanWeil.Ihara

open Family

attribute [local instance] HasDerivedCategory.standard moduleCat_hasLimitsOfSize

variable (p : ℕ) [Fact p.Prime] (B : BigEtaleSite.{0})

/-- `W_p` as an object of the big étale site `B`. -/
abbrev Wp : B.Scheme := B.obj (base p) (contains_base p B)

/-- The universal Weierstrass curve `E` as an object of `B`. -/
abbrev Ep : B.Scheme := B.obj (total p) (contains_total p B)

/-- The projection `E ⟶ W_p` in `B`. -/
abbrev π : Ep p B ⟶ Wp p B := ObjectProperty.homMk (proj p)

/-- The structure morphism `W_p ⟶ Spec 𝔽_p`. -/
noncomputable abbrev toSpecK : (Wp p B).1 ⟶ Spec (CommRingCat.of (ZMod p)) := Family.toSpecK p

instance : IsNoetherian (Wp p B).1 := isNoetherian_base p
instance : IsNoetherian (Ep p B).1 := isNoetherian_total p
instance : LocallyOfFiniteType (toSpecK p B) := locallyOfFiniteType_toSpecK p
instance : QuasiCompact (toSpecK p B) := quasiCompact_toSpecK p
instance : IsSeparated (toSpecK p B) := isSeparated_toSpecK p
instance : IsProper (B.inclusion.map (π p B)) := isProper_proj p
instance : Smooth (B.inclusion.map (π p B)) := smooth_proj p
instance : SmoothOfRelativeDimension 1 (B.inclusion.map (π p B)) := smoothOfRelativeDimension_proj p
instance : CompactSpace (Ep p B).obj := inferInstanceAs (CompactSpace (total p))
instance : QuasiSeparatedSpace (Ep p B).obj :=
  @IsLocallyNoetherian.quasiSeparatedSpace (total p) IsNoetherian.toIsLocallyNoetherian
instance : IsNoetherian (B.inclusion.obj (Wp p B)) := isNoetherian_base p
instance : IsNoetherian (B.inclusion.obj (Ep p B)) := isNoetherian_total p

/-- `dim W_p ≤ 5`, in the form consumed by M2. -/
theorem topologicalKrullDim_Wp_le : topologicalKrullDim (Wp p B).1 ≤ (5 : ℕ) :=
  topologicalKrullDim_base_le p

/-- The identity compactification of the proper morphism `π`. -/
noncomputable abbrev jπ : CompactificationOf (Over.mk (B.inclusion.map (π p B))) :=
  CompactificationOf.ofProper (B.inclusion.map (π p B))

variable (ℓ : ℕ) [Fact ℓ.Prime]
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

/-- The constant ℓ-adic sheaf `ℤ_ℓ` on `E`. -/
noncomputable abbrev constE : LAdicSheaf.{0, 1} B (Ep p B) ℓ :=
  LAdicSheaf.constantSystem B (Ep p B) ℓ

/-- **`R¹ = R¹π_! ℤ_ℓ`** (`= R¹π_* ℤ_ℓ`, `π` proper), an ℓ-adic sheaf on `W_p`. -/
noncomputable def R1 : LAdicSheaf.{0, 1} B (Wp p B) ℓ :=
  LAdicSheaf.higherDirectImageShriek B ℓ (π p B) (jπ p B) (constE p B ℓ) 1

/-! ### The constant ℓ-adic sheaf is lisse -/

omit [Fact p.Prime] in
/-- **The constant ℓ-adic sheaf is lisse** (on any noetherian qcqs `X` in `B`): its level `n`, read
on Mathlib's small étale site, is the constant sheaf `ℤ/ℓⁿ⁺¹`
(`LAdicSheaf.etaleLevelConstantSystemIso`). -/
theorem isLisse_constantSystem (X : B.Scheme) [IsNoetherian X.1]
    [QuasiSeparatedSpace X.obj] : (LAdicSheaf.constantSystem B X ℓ).IsLisse := by
  intro n
  have hN : NeZero (ℓ ^ (n + 1)) := ⟨pow_ne_zero _ (Fact.out : ℓ.Prime).ne_zero⟩
  have h₁ : Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant (ZMod (ℓ ^ (n + 1)))
      X.1.smallEtaleTopology (LAdicSheaf.etaleLevel B X ℓ (LAdicSheaf.constantSystem B X ℓ) n) :=
    ObjectProperty.prop_of_iso
      (P := fun F => Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant (ZMod (ℓ ^ (n + 1)))
        X.1.smallEtaleTopology F)
      (LAdicSheaf.etaleLevelConstantSystemIso B X ℓ n).symm
      (Stacks.ConstantSheaf.isFiniteTypeLocallyConstant_constantSheaf _ _
        (by rw [ModuleCat.isFG_iff]; exact Module.Finite.of_finite))
  have h₂ := (SmallEtale.isFiniteTypeLocallyConstant_sheafEquiv_functor_iff B X _ _).1 h₁
  refine ⟨fun U => ?_⟩
  obtain ⟨I, V, f, hcov, h⟩ := h₂ U
  exact ⟨I, V, f, hcov, fun i => by
    obtain ⟨E, -, ⟨e⟩⟩ := h i
    exact Sheaf.isConstant_of_iso _ e.symm⟩

/-! ### Torsion and residue characteristics on `E` -/

/-- Every geometric point of `E` has residue characteristic `p`. -/
theorem ringChar_residueField_Ep (x : GeometricPoint (Ep p B).1) :
    ringChar x.residueField = p := by
  let φ : CommRingCat.of (ZMod p) ⟶ CommRingCat.of x.residueField :=
    Spec.preimage (x.hom ≫ proj p ≫ Family.toSpecK p)
  have : CharP x.residueField p := charP_of_injective_ringHom φ.hom.injective p
  exact ringChar.eq x.residueField p

/-! ### Lisseness of `R¹` -/

/-- `Rⁿπ_* F ≅ Hⁿ(Rπ_! F)` for the identity compactification (local copy of Stacks'
`rightDerivedIsoHomologyDerivedLowerShriekOfProper`, specialised). -/
noncomputable def rightDerivedIsoLowerShriekHomology (F : EtaleModules.{0, 0} ℤ_[ℓ] (Ep p B).1)
    (n : ℕ) :
    ((etaleModuleDirectImage.{0, 0} ℤ_[ℓ] (B.inclusion.map (π p B))).rightDerived n).obj F ≅
      (lowerShriekHomology ℤ_[ℓ] (B.inclusion.map (π p B)) (jπ p B) (n : ℤ)).obj F :=
  rightDerivedIsoHomologyDerivedLowerShriekOfProper (B.inclusion.map (π p B)) ℤ_[ℓ] F n ≪≫
    (lowerShriekHomologyIsoHomologyDerivedLowerShriek ℤ_[ℓ] _ (jπ p B) F n).symm

/-- **`Rˢπ_! G'₀` is locally constant of finite type for every `s`**, `G'₀` the level zero of the
flat model of the constant ℓ-adic sheaf on `E`, `ℓ ≠ p`. -/
theorem isFiniteTypeLocallyConstant_lowerShriekHomology_levelZero (hℓp : ℓ ≠ p) (s : ℤ) :
    Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant.{1} ℤ_[ℓ] (Wp p B).1.smallEtaleTopology
      ((lowerShriekHomology ℤ_[ℓ] (B.inclusion.map (π p B)) (jπ p B) s).obj
        (towerObj (LAdicSheaf.padicTower B (Ep p B) ℓ
          (LAdicSheaf.flatModel B ℓ (constE p B ℓ))) 0)) := by
  let P : ObjectProperty (EtaleModules.{0, 0} ℤ_[ℓ] (Wp p B).1) :=
    Stacks.ConstantSheaf.IsFiniteTypeLocallyConstantModuleSheaf.{0, 1, 0}
      (Wp p B).1.smallEtaleTopology ℤ_[ℓ]
  show P _
  set F₀ := towerObj (LAdicSheaf.padicTower B (Ep p B) ℓ
    (LAdicSheaf.flatModel B ℓ (constE p B ℓ))) 0
  have hF₀ : Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant.{1} ℤ_[ℓ]
      (Ep p B).1.smallEtaleTopology F₀ :=
    LAdicSheaf.isFiniteTypeLocallyConstant_padicTower_of_isLisse B (Ep p B) ℓ _
      (LAdicSheaf.isLisse_flatModel B ℓ _ (isLisse_constantSystem B ℓ (Ep p B))) 0
  rcases lt_or_ge s 0 with hs | hs
  · refine P.prop_of_iso
      (((DerivedCategory.Plus.homologyFunctor _ s).mapIso
        ((derivedLowerShriekOfProperIso ℤ_[ℓ] (B.inclusion.map (π p B))).app _)).symm ≪≫
        (lowerShriekHomologyIsoHomologyDerivedLowerShriek ℤ_[ℓ] _ (jπ p B) F₀ s).symm) ?_
    exact P.prop_of_isZero
      ((etaleModuleDirectImage.{0, 0} ℤ_[ℓ] (B.inclusion.map (π p B))).isZero_rightDerivedPlus_of_neg
        _ s hs)
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hs
    refine P.prop_of_iso (rightDerivedIsoLowerShriekHomology p B ℓ F₀ n) ?_
    refine isFiniteTypeLocallyConstantModuleSheaf_rightDerived_of_smooth_of_isProper_of_isNoetherian
      (B.inclusion.map (π p B)) ℤ_[ℓ] F₀ hF₀ (fun x => ⟨ℓ, (Fact.out : ℓ.Prime).pos, ?_, ?_⟩) n
    · right
      rw [ringChar_residueField_Ep p B x]
      exact (Nat.coprime_primes (Fact.out : ℓ.Prime) (Fact.out : p.Prime)).2 hℓp
    · have h := LAdicSheaf.padicTower_annihilated B (Ep p B) ℓ
        (LAdicSheaf.flatModel B ℓ (constE p B ℓ)) 0
      rw [zero_add, pow_one] at h
      have hG : ℓ • 𝟙 ((etaleModuleForget ℤ_[ℓ] (Ep p B).1).obj F₀) = 0 := by
        rw [← CategoryTheory.Functor.map_id, ← Functor.map_nsmul, h, Functor.map_zero]
      exact Stacks.EtaleCohomology.Purity.nsmul_eq_zero_stalk_of_nsmul_id hG x

/-- **M3 headline: `R¹π_! ℤ_ℓ` is lisse on all of `W_p`**, for `ℓ ≠ p` (ℓ-adic upgrade of
Tag 0GLI for the universal Weierstrass curve). -/
theorem isLisse_R1 (hℓp : ℓ ≠ p) : (R1 p B ℓ).IsLisse :=
  LAdicSheaf.isLisse_higherDirectImageShriek_of_levelZero B ℓ (π p B) (jπ p B) (constE p B ℓ)
    (isFiniteTypeLocallyConstant_lowerShriekHomology_levelZero p B ℓ hℓp) 1

/-- More generally every `Rʳπ_! ℤ_ℓ` is lisse. -/
theorem isLisse_higherDirectImage (hℓp : ℓ ≠ p) (r : ℕ) :
    (LAdicSheaf.higherDirectImageShriek B ℓ (π p B) (jπ p B) (constE p B ℓ) r).IsLisse :=
  LAdicSheaf.isLisse_higherDirectImageShriek_of_levelZero B ℓ (π p B) (jπ p B) (constE p B ℓ)
    (isFiniteTypeLocallyConstant_lowerShriekHomology_levelZero p B ℓ hℓp) r

end RamanujanWeil.Ihara

end
