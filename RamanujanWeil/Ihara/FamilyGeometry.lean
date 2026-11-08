import StacksFrontier.AlgebraicGeometry.Stacks.WeierstrassFamilyProper
import StacksFrontier.AlgebraicGeometry.Stacks.WeierstrassFamilySmooth
import StacksFrontier.AlgebraicGeometry.Stacks.WeierstrassFamilyElliptic
import StacksFrontier.AlgebraicGeometry.Size.Cutoff
import StacksFrontier.AlgebraicGeometry.Size.Affine
import StacksFrontier.AlgebraicGeometry.Topologies.Etale
import Mathlib.RingTheory.KrullDimension.Polynomial
import Mathlib.Topology.KrullDimension
import Mathlib.AlgebraicGeometry.Noetherian

/-!
# M3 (geometry): the Weierstrass base `W_p` over `𝔽_p` and the universal curve over it

Fix a prime `p` and `k = 𝔽_p = ZMod p`. Write

* `coeffRing p = 𝔽_p[a₁, a₂, a₃, a₄, a₆]` (`MvPolynomial (Fin 5) (ZMod p)`, variables `0..4`),
* `genericCurve p = ⟨X 0, X 1, X 2, X 3, X 4⟩`, the generic Weierstrass equation over it,
* `baseRing p = 𝔽_p[a₁..a₆][1/Δ]` (`Localization.Away (genericCurve p).Δ`),
* `curve p = (genericCurve p).baseChange (baseRing p)`, an elliptic Weierstrass curve
  (`isUnit_curve_Δ`),
* `base p = Spec (baseRing p)`, the scheme `W_p`, with structure morphism `toSpecK p : W_p ⟶ Spec 𝔽_p`,
* `total p = projOf (curve p)`, the plane cubic `E ⊂ ℙ²_{W_p}` of Stacks
  (`AlgebraicGeometry.ModuliEllipticCurves.Weierstrass.projOf`), with projection
  `proj p = projectionOf (curve p) : E ⟶ W_p`; it is proper (`isProper_projectionOf`) and smooth of
  relative dimension one (`smoothOfRelativeDimension_projectionOf`), and `familyOf (curve p)` is an
  elliptic curve over `W_p` (`isElliptic_familyOf`).

`curve p` is the image of Stacks' generic equation `Weierstrass.curve` over
`ℤ[a₁..a₆][1/Δ]` under the ring map `ℤ[a][1/Δ] → 𝔽_p[a][1/Δ]` (`curve_eq_map`), so `E → W_p` is
the base change of Stacks' universal family `Weierstrass.family` (as Weierstrass equations; the
plane cubic `projOf` of an equation is functorial in the ring).

Everything lives in universe `0` (`ZMod p : Type`), so the big étale site has `B : BigEtaleSite.{0}`.
Every such `B` contains `W_p` and `E` (`contains_base`, `contains_total`): `W_p` is the spectrum of
a countable ring and `E → W_p` is of finite type.
-/

open CategoryTheory AlgebraicGeometry MvPolynomial Cardinal
open AlgebraicGeometry.ModuliEllipticCurves.Weierstrass

noncomputable section

namespace RamanujanWeil.Ihara.Family

variable (p : ℕ) [Fact p.Prime]

/-- `𝔽_p[a₁, a₂, a₃, a₄, a₆]`, the variables `0, 1, 2, 3, 4` standing for `a₁, a₂, a₃, a₄, a₆`. -/
abbrev coeffRing : Type := MvPolynomial (Fin 5) (ZMod p)

/-- The generic Weierstrass equation over `𝔽_p[a₁..a₆]`. -/
def genericCurve : WeierstrassCurve (coeffRing p) := ⟨X 0, X 1, X 2, X 3, X 4⟩

/-- The discriminant `Δ ∈ 𝔽_p[a₁..a₆]` of the generic equation. -/
abbrev discriminant : coeffRing p := (genericCurve p).Δ

/-- `𝔽_p[a₁..a₆][1/Δ]`. -/
abbrev baseRing : Type := Localization.Away (discriminant p)

/-- The generic Weierstrass equation over `𝔽_p[a₁..a₆][1/Δ]`. -/
def curve : WeierstrassCurve (baseRing p) := (genericCurve p).baseChange (baseRing p)

theorem isUnit_curve_Δ : IsUnit (curve p).Δ := by
  rw [curve, WeierstrassCurve.baseChange, WeierstrassCurve.map_Δ]
  exact IsLocalization.Away.algebraMap_isUnit _

instance : (curve p).IsElliptic := ⟨isUnit_curve_Δ p⟩

/-- `W_p = Spec 𝔽_p[a₁..a₆][1/Δ]`, as a scheme. -/
abbrev base : Scheme.{0} := Spec (CommRingCat.of (baseRing p))

/-- The structure morphism `W_p ⟶ Spec 𝔽_p`. -/
def toSpecK : base p ⟶ Spec (CommRingCat.of (ZMod p)) :=
  Spec.map (CommRingCat.ofHom (algebraMap (ZMod p) (baseRing p)))

/-- The universal Weierstrass curve `E ⊂ ℙ²_{W_p}`. -/
abbrev total : Scheme.{0} := projOf (curve p)

/-- The projection `E ⟶ W_p`. -/
abbrev proj : total p ⟶ base p := projectionOf (curve p)

/-! ### `W_p` -/

instance : IsNoetherianRing (baseRing p) :=
  IsLocalization.isNoetherianRing (Submonoid.powers (discriminant p)) _ inferInstance

instance isNoetherian_base : IsNoetherian (base p) := inferInstance

instance : Algebra.FiniteType (ZMod p) (baseRing p) :=
  Algebra.FiniteType.trans (S := coeffRing p) inferInstance
    (IsLocalization.finiteType_of_monoid_fg (Submonoid.powers (discriminant p)) _)

instance locallyOfFiniteType_toSpecK : LocallyOfFiniteType (toSpecK p) := by
  rw [toSpecK, HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
  exact RingHom.finiteType_algebraMap.mpr inferInstance

instance quasiCompact_toSpecK : QuasiCompact (toSpecK p) := inferInstance

instance isSeparated_toSpecK : IsSeparated (toSpecK p) := inferInstance

/-- `dim W_p ≤ 5`: `W_p` is an open subscheme of `𝔸⁵_{𝔽_p}`. -/
theorem topologicalKrullDim_base_le : topologicalKrullDim (base p) ≤ 5 := by
  have h₁ : topologicalKrullDim (PrimeSpectrum (baseRing p)) ≤
      topologicalKrullDim (PrimeSpectrum (coeffRing p)) :=
    (PrimeSpectrum.localization_comap_isInducing (S := baseRing p)
      (Submonoid.powers (discriminant p))).topologicalKrullDim_le
  have h₂ : topologicalKrullDim (PrimeSpectrum (coeffRing p)) = 5 := by
    rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim,
      MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field]
    simp
  exact h₁.trans h₂.le

/-! ### The curve `E → W_p` -/

instance isProper_proj : IsProper (proj p) := isProper_projectionOf _

instance smoothOfRelativeDimension_proj : SmoothOfRelativeDimension 1 (proj p) :=
  smoothOfRelativeDimension_projectionOf _ (isUnit_curve_Δ p)

instance smooth_proj : Smooth (proj p) := SmoothOfRelativeDimension.smooth 1 (proj p)

/-- `(E, proj, 0)` is an elliptic curve over `W_p` (Stacks Tag 072S). -/
theorem isElliptic_family : (familyOf (curve p)).IsElliptic := isElliptic_familyOf _

instance isNoetherian_total : IsNoetherian (total p) := by
  have : IsLocallyNoetherian (total p) := LocallyOfFiniteType.isLocallyNoetherian (proj p)
  have : CompactSpace (total p) := QuasiCompact.compactSpace_of_compactSpace (proj p)
  exact {}

/-! ### Size: every big étale site contains `W_p` and `E` -/

theorem contains_base (B : BigEtaleSite.{0}) : B.Contains (base p) := by
  show (base p).size < B.cutoff
  rw [Scheme.size_Spec]
  refine lt_of_le_of_lt (max_le le_rfl ?_) B.aleph0_lt_cutoff
  refine (mk_localization_powers_le (discriminant p)).trans (max_le le_rfl ?_)
  exact Cardinal.mk_le_aleph0

theorem contains_total (B : BigEtaleSite.{0}) : B.Contains (total p) :=
  Scheme.size_lt_of_locallyOfFiniteType_of_quasiCompact (proj p) (contains_base p B)

end RamanujanWeil.Ihara.Family

end
