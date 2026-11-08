# M3: the Weierstrass family over 𝔽_p and R¹ (frozen interface)

Status 2026-11-08. Milestone M3 of `docs/REALIZATION_PLAN.md`, §5 (geometric half).
**No gap hypothesis.** `isLisse_R1` (the ℓ-adic upgrade of Tag 0GLI for the universal curve) is
proved unconditionally. No `sorry`, `admit`, `native_decide` or `axiom`.

## Files

| File | Imports | Content |
|---|---|---|
| `RamanujanWeil/Ihara/FamilyGeometry.lean` | Mathlib + Stacks `Weierstrass{FamilyProper,FamilySmooth,FamilyElliptic}`, `Size`, `Topologies.Etale` | rings, `W_p`, `E`, `π`, finiteness, dimension, size |
| `RamanujanWeil/Ihara/FamilyR1.lean` | Geometry + Stacks ℓ-adic (`LowerShriekLocallyConstantClosure`, `SmoothProperHigherDirectImageLocallyConstantNoetherian`, …) | `Wp`, `Ep`, `π`, `jπ`, `R1`, `isLisse_constantSystem`, `isLisse_R1` |
| `RamanujanWeil/Ihara/FamilyPackage.lean` | R1 + `WeilPackage` (M2) | `lefschetzPackage_Wp`, M2 instantiated over `W_p` |
| `RamanujanWeil/Ihara/FamilyConnected.lean` | Geometry | `Δ ≠ 0`, `baseRing` a domain, `W_p` irreducible and connected |
| `RamanujanWeil/Ihara/FamilyAxioms.lean` | Package + Connected | `#print axioms` audit |

Stacks modules that were not prebuilt and got built (16 in all, about 1.5k lines of Stacks source):
the Weierstrass closure (11: `ModuliEllipticCurves{,BaseChange,Algebraic}`,
`Weierstrass{Family,FamilyProper,FamilySmooth,FamilyElliptic,FamilyFibres,CubicPoints,CubicCharts,CubicIso}`)
and the Noetherian Tag 0GLI file with its closure (5:
`EtaleCohomology.SmoothProperHigherDirectImageLocallyConstantNoetherian`,
`DerivedLowerShriek.ConstructibilityTorsion`,
`PullbackStalk.{SpecializationFiniteTypeLocallyConstantModuleConverse,ConcreteBijectiveGerm}`,
`Algebra.Category.ModuleCat.FilteredColimitFinitePresentation`). The general (non-Noetherian)
`isFiniteTypeLocallyConstantModuleSheaf_rightDerived_of_smooth_of_isProper` was avoided, because its
closure is about 160 unbuilt modules.

## Conventions

* `k = 𝔽_p` is `ZMod p` (`[Fact p.Prime]`). Everything is in **universe 0**, so
  `B : BigEtaleSite.{0}` and the ℓ-adic sheaves are `LAdicSheaf.{0, 1}`. `Fintype.card (ZMod p) = p ^ 1`
  is `card_zmod_eq_pow_one`, and `CharP (ZMod p) p` is the Mathlib instance.
* Every `B` contains `W_p` and `E` (`Family.contains_base`, `Family.contains_total`). There is no
  hypothesis on `B` beyond the three families of site instances that M2 also uses.
* Coordinates: the variables `0,1,2,3,4` of `MvPolynomial (Fin 5) (ZMod p)` are `a₁,a₂,a₃,a₄,a₆`.

## Frozen statements

Namespace `RamanujanWeil.Ihara.Family` (in `FamilyGeometry.lean`):

```lean
abbrev coeffRing : Type := MvPolynomial (Fin 5) (ZMod p)
def genericCurve : WeierstrassCurve (coeffRing p) := ⟨X 0, X 1, X 2, X 3, X 4⟩
abbrev discriminant : coeffRing p := (genericCurve p).Δ
abbrev baseRing : Type := Localization.Away (discriminant p)            -- 𝔽_p[a][1/Δ]
def curve : WeierstrassCurve (baseRing p) := (genericCurve p).baseChange (baseRing p)
theorem isUnit_curve_Δ : IsUnit (curve p).Δ ;  instance : (curve p).IsElliptic
abbrev base : Scheme.{0} := Spec (CommRingCat.of (baseRing p))          -- W_p
def toSpecK : base p ⟶ Spec (CommRingCat.of (ZMod p)) := Spec.map (CommRingCat.ofHom (algebraMap _ _))
abbrev total : Scheme.{0} := projOf (curve p)                            -- E ⊂ ℙ²_{W_p}
abbrev proj : total p ⟶ base p := projectionOf (curve p)
instances: IsNoetherian (base p), IsNoetherian (total p), LocallyOfFiniteType/QuasiCompact/IsSeparated (toSpecK p),
           IsProper (proj p), SmoothOfRelativeDimension 1 (proj p), Smooth (proj p)
theorem topologicalKrullDim_base_le : topologicalKrullDim (base p) ≤ 5
theorem isElliptic_family : (familyOf (curve p)).IsElliptic             -- Stacks Tag 072S
theorem contains_base (B : BigEtaleSite.{0}) : B.Contains (base p)
theorem contains_total (B : BigEtaleSite.{0}) : B.Contains (total p)
```

`curve p` is the generic equation. It is the image of Stacks' `Weierstrass.curve` over
`ℤ[a][1/Δ]` along `ℤ[a][1/Δ] → 𝔽_p[a][1/Δ]`, so `(total p, proj p)` is the base change of Stacks'
universal family as Weierstrass equations. That identification is not formalised as a pullback
square of schemes, and nothing downstream needs it. Properness and smoothness are obtained directly
from Stacks' `isProper_projectionOf` and `smoothOfRelativeDimension_projectionOf`, which hold over
any ring with `Δ` a unit.

Namespace `RamanujanWeil.Ihara` (in `FamilyR1.lean`). Variables: `(p) [Fact p.Prime] (B : BigEtaleSite.{0})
(ℓ) [Fact ℓ.Prime]` together with the three site-instance families of M2 at `ModuleCat.{1} (ZMod (ℓ^(n+1)))`.

```lean
abbrev Wp : B.Scheme := B.obj (base p) (contains_base p B)
abbrev Ep : B.Scheme := B.obj (total p) (contains_total p B)
abbrev π : Ep p B ⟶ Wp p B := ObjectProperty.homMk (proj p)
abbrev toSpecK : (Wp p B).1 ⟶ Spec (CommRingCat.of (ZMod p)) := Family.toSpecK p
abbrev jπ : CompactificationOf (Over.mk (B.inclusion.map (π p B))) :=
  CompactificationOf.ofProper (B.inclusion.map (π p B))
instances: IsNoetherian (Wp p B).1, (Ep p B).1, B.inclusion.obj (Wp/Ep);
           LocallyOfFiniteType/QuasiCompact/IsSeparated (toSpecK p B);
           IsProper/Smooth/SmoothOfRelativeDimension 1 (B.inclusion.map (π p B));
           CompactSpace / QuasiSeparatedSpace (Ep p B).obj
theorem topologicalKrullDim_Wp_le : topologicalKrullDim (Wp p B).1 ≤ (5 : ℕ)

abbrev constE : LAdicSheaf.{0, 1} B (Ep p B) ℓ := LAdicSheaf.constantSystem B (Ep p B) ℓ   -- ℤ_ℓ on E
def R1 : LAdicSheaf.{0, 1} B (Wp p B) ℓ :=
  LAdicSheaf.higherDirectImageShriek B ℓ (π p B) (jπ p B) (constE p B ℓ) 1        -- R¹π_! ℤ_ℓ = R¹π_* ℤ_ℓ

theorem isLisse_constantSystem (X : B.Scheme) [IsNoetherian X.1] [QuasiSeparatedSpace X.obj] :
    (LAdicSheaf.constantSystem B X ℓ).IsLisse
theorem ringChar_residueField_Ep (x : GeometricPoint (Ep p B).1) : ringChar x.residueField = p
theorem isLisse_R1 (hℓp : ℓ ≠ p) : (R1 p B ℓ).IsLisse                              -- HEADLINE
theorem isLisse_higherDirectImage (hℓp : ℓ ≠ p) (r : ℕ) :
    (LAdicSheaf.higherDirectImageShriek B ℓ (π p B) (jπ p B) (constE p B ℓ) r).IsLisse
```

In `FamilyPackage.lean`:

```lean
theorem lefschetzPackage_Wp (hℓp : ℓ ≠ p) (ι : ℚ_[ℓ] →+* ℂ) (F : LAdicSheaf.{0, 1} B (Wp p B) ℓ) (w : ℤ)
    (hF : F.IsLisse)
    (hmix : LAdicSheaf.IsPointwiseMixedOfWeightLE B (Wp p B) ℓ (toSpecK p B) F (p ^ 1) ι w)
    (hreal : LAdicSheaf.IsIotaRealizable B (Wp p B) ℓ (toSpecK p B) F ι) :
    Nonempty (LefschetzPackage ℚ_[ℓ] ι (p ^ 1) w 5 (pointSum B (Wp p B) ℓ (toSpecK p B) F))
```

This is M2's `lefschetzPackage_of_lisse_pure'` with `X = W_p`, `k = ZMod p`, `q = 1`, `d = 5`.

## Proof of `isLisse_R1`

`LAdicSheaf.isLisse_higherDirectImageShriek_of_levelZero` (Stacks) reduces lisseness of `Rʳπ_! G` to
one condition: every `Rˢπ_! G'₀` (`s : ℤ`, coefficients `ℤ_ℓ`, `G'₀` = level 0 of the flat model of
`G`) is locally constant of finite type on `W_p,ét`. That condition is checked as follows.

1. `G'₀` is locally constant of finite type. `constantSystem` is lisse, because its level `n` on
   Mathlib's site is the constant sheaf `ℤ/ℓⁿ⁺¹` (`etaleLevelConstantSystemIso`). The flat model of
   a lisse sheaf is lisse (`isLisse_flatModel`), and lisse levels are f.t. locally constant over
   `ℤ_ℓ` (`isFiniteTypeLocallyConstant_padicTower_of_isLisse`).
2. `G'₀` is killed by `ℓ` (`padicTower_annihilated`), hence so are its stalks. Every residue field
   of `E` has characteristic `p` (`ringChar_residueField_Ep`, via `Spec.preimage` of
   `E → Spec 𝔽_p`), and `ℓ ≠ p`.
3. For `s < 0`: `Rπ_! = Rπ_*` (`derivedLowerShriekOfProperIso`) and `isZero_rightDerivedPlus_of_neg`.
   For `s = n ≥ 0`: `Rⁿπ_* ≅ Hⁿ(Rπ_!)` (Stacks `rightDerivedIsoHomologyDerivedLowerShriekOfProper`
   together with `lowerShriekHomologyIsoHomologyDerivedLowerShriek`). Then Tag 0GLI over the
   Noetherian base,
   `isFiniteTypeLocallyConstantModuleSheaf_rightDerived_of_smooth_of_isProper_of_isNoetherian`
   with `Λ = ℤ_ℓ`, applies because `π` is smooth and proper.

## Interface for M4b (stalks of R¹)

At a closed point `w : closedPoints (Wp p B).1`, the charpoly of Frobenius on the rational stalk of
`R1 p B ℓ` comes from Stacks' `LAdicSheaf.higherDirectImageStalkInput_higherDirectImageShriek`. Its
inputs `hC` and `hL` are discharged in `EC/Trace/WeilIIAssembly.lean:123`, and it gives

```
(rationalStalkFrobenius B (Wp p B) ℓ (R1 p B ℓ) w (finite_residueField (toSpecK p B) w w.2)).charpoly
  = (rationalGeometricCompactlySupportedFrobenius (k := κ(w)) B (B.obj E_w hB) ℓ
       ((B.inclusion.map (π p B)).fiberToSpecResidueField w) jw kbar p n hcard
       (LAdicSheaf.inverseImage (homMk (fiberι w)) (constE p B ℓ)) 1).hom.charpoly
```

for some compactification `jw` of the fibre. Here `g = π p B`, `jg = jπ p B`,
`fW = toSpecK p B`, `R = higherDirectImageShriekFamily B ℓ` (whose value at `r = 1` is `R1`, by
`rfl` modulo unfolding).

M4b still has to supply the following:

* side instances for the fibre `E_w = (B.inclusion.map (π p B)).fiber w`: `B.Contains` it (use
  `Scheme.size_lt_of_locallyOfFiniteType_of_quasiCompact`), `IsNoetherian`, and the
  `LocallyOfFiniteType`/`QuasiCompact`/`IsSeparated` instances of `fiberToSpecResidueField`
  (base change of the proper `π`);
* the finite residue field data: `Fintype κ(w)`, `CharP κ(w) p`, `#κ(w) = p ^ deg w`;
* the identification of `inverseImage (fiberι) (constantSystem B Ep ℓ)` with
  `constantSystem` on the fibre (levels are constant sheaves:
  `smallEtaleSheafPullbackConstantSheafIso`, or via `etaleLevelConstantSystemIso`), so that the
  constant-curve results `Trace/ConstantCurveH1Trace.lean` apply to the elliptic curve
  `E_w = projOf ((curve p).map (residueMapOf w))` over the finite field `κ(w)`
  (`WeierstrassFamilyElliptic.isPullback_fromSpecResidueField`). That gives
  `charpoly = X² − a_w X + q_w`, with `q_w = p^{deg w}` and
  `a_w = q_w + 1 − #E_w(κ(w))`.

## Interface for M5 (Sym¹⁰)

M5 needs a lisse `F := Sym¹⁰ (R1 p B ℓ)` on `Wp p B`. The route through
`LAdicSheaf.exists_representationSheaf_isogeny_of_isLisse` (Stacks, `LisseRepresentation.lean:492`)
needs `[ConnectedSpace (Wp p B).1]` and a geometric point. Connectedness is supplied by
`FamilyConnected.lean`:

```lean
theorem Family.discriminant_ne_zero : discriminant p ≠ 0      -- Δ(0,0,1,0,0) = -27, Δ(0,0,0,-1,0) = 64
instance : IsDomain (baseRing p)
instance Family.irreducibleSpace_base : IrreducibleSpace (base p)
instance Family.connectedSpace_base : ConnectedSpace (base p)   -- use inferInstanceAs for (Wp p B).1
```

M5 then feeds `lefschetzPackage_Wp p B ℓ hℓp ι F 10 hF hmix hreal`.

## Build and audit

`nice -n 10 lake build RamanujanWeil.Ihara.FamilyAxioms` builds Geometry → {R1 → Package, Connected} → Axioms (exit 0, 2026-11-08).
Each of the R1 and Package files takes about 3–4 minutes, mostly import loading. Every headline
in `FamilyAxioms.lean` prints `[propext, Classical.choice, Quot.sound]` (18 audited names, including `isLisse_R1`, `R1`,
`lefschetzPackage_Wp`, `connectedSpace_base`).
