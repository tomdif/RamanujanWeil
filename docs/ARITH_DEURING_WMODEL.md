# A3-ord, G5: `WeierstrassModel` proved (2026-11-09)

This closes the last input of `docs/ARITH_DEURING_DESCENT.md` §5.

**Result.** `WModel.weierstrassModel_of_isAlgClosed : ∀ k [IsAlgClosed k], Descent.WeierstrassModel k`
is proved, hence `WModel.weierstrassModel K : WeierstrassModel (AlgebraicClosure K)` and

```lean
theorem WModel.weierstrassDescent (K : Type u) [Field K] [Fintype K] : G5.WeierstrassDescent K
```

unconditionally. No named Prop is left in this step. No existing file was edited; no `sorry`,
`admit`, `native_decide` or `axiom`. Audit: `RamanujanWeil/Arith/DeuringWModelAxioms.lean`
(all declarations depend only on `[propext, Classical.choice, Quot.sound]`).

| File | Content |
|---|---|
| `Arith/DeuringWModelChi.lean` | `chi`, `pullbackPushforwardUnitIso` (copy of Stacks' affine base change at `𝒪`, whose module is unbuilt), `finrank_cohomologyOverField_split`, **`chi_eq_mul`**, **`one_sub_genus_eq_mul`** |
| `Arith/DeuringWModelGenus.lean` | `legsIsColimit`/`leg_cover`/`leg_disjoint` (`H_S ×_S U = ∐_H U` on underlying schemes), **`exists_one_sub_genus_eq_mul`**, `exists_large_subgroup`, `one_le_genus`, **`genus_eq_one`**, `finrank_structureSheafCohomology_zero` |
| `Arith/DeuringWModel.lean` | **`weierstrassModel_of_isAlgClosed`**, `weierstrassModel`, **`weierstrassDescent`** |
| `Arith/DeuringWModelAxioms.lean` | audit |

## 1. Route: genus one by an Euler-characteristic count (not the Picard route)

The predecessor's options were Tag 0C1A (`deg Ω = 2g − 2`, ~600 unbuilt Stacks modules) or a
Picard-scheme argument (Jacobi inversion + torsion). Both were avoided. The route used:

**χ is multiplicative along the G6 quotient** (`DeuringWModelChi`). Let `q : A ⟶ B` be finite
locally free of rank `d` between proper curves, and suppose the kernel pair `W = A ×_B A`
splits as `d` open-and-affine sections `s_i` of a projection `p`, with disjoint images covering
`W`. Then `χ(A) = d·χ(B)`. Proof (the argument of Stacks' `genus_sub_one_eq_of_isGalois`,
`Curves/EtaleCoverGenus.lean`, which itself needs 69 unbuilt modules; the Galois hypothesis is
replaced by the explicit splitting):

* `ℰ = q_*𝒪_A` is locally free of rank `d`, and `deg(q^*ℰ) = deg q · deg ℰ` (Tag 0AYZ,
  `curveDegree_pullback_eq_degreeOver_mul`, prebuilt);
* `q^*ℰ ≅ p_*𝒪_W` (affine base change, Tag 02KG) and `𝒪_W ≅ ∏ (s_i)_*𝒪_A`
  (`structureSheafDisjointCoverIso`), so `χ(A, q^*ℰ) = d·χ(A)`, i.e. `deg(q^*ℰ) = 0`;
* so `deg ℰ = 0`: `χ(A) = χ(B, ℰ) = d·χ(B)`.

With `h⁰ = 1` (`isIso_globalSections_of_geometricallyIntegral`), `1 − g_A = d(1 − g_B)`.

**Applied to `A ⟶ A/H`** (`DeuringWModelGenus`). For a finite `H ⊆ A(k)`, the G6 quotient
(`nonempty_translationQuotient`, Stacks 07S7) has kernel pair `H_k ×_k A`, rank `#H`, and
`H_k ×_k A = ∐_{h∈H} A` (Stacks `isColimit_constantGroupSchemeTensorCofan`, pushed to schemes
through `Over.forget`; the legs `(h, x) ↦ (h, x)` are open and closed immersions, sections of
`snd`). `A/H` is again a one-dimensional abelian variety (`[#H] = q ≫ β`, `dim_eq_of_surjective`).
So `1 − g(A) = #H·(1 − g(A/H))`.

**Counting.** `A(k)[ℓ] ≅ (ℤ/ℓ)²` for primes `ℓ ≠ char k` (Stacks
`nonempty_torsionBy_addEquiv_of_isUnit`, prebuilt), so `#H = ℓ²` can be taken arbitrarily large.
* `g ≥ 1`: if `g(A) = 0` then `#H·(1 − g(A/H)) = 1` with `#H ≥ 4`.
* `g ≤ 1`: if `g(A) ≥ 2` then `g(A/H) ≥ 2` (as `g(A/H) ≥ 1` and the left side is negative), so
  `g(A) − 1 = #H(g(A/H) − 1) ≥ #H > g(A)`.

`genus` is Stacks' `dim_k H¹(A, 𝒪_A)` (`Curves/GenusCurve/Basic.lean`), the one in
`exists_weierstrassCurve_iso`.

## 2. Assembly

`weierstrassModel_of_isAlgClosed`: `IsCurve` (G4Hom `isCurve_of_dim_one`), `Smooth`
(Mathlib `smooth_of_grpObj`), `SmoothOfRelativeDimension 1` (Stacks
`smoothOfRelativeDimension_one_of_isCurve`), `h⁰ = 1`, `genus = 1`, base point `η.left`; then
Stacks `GenusOne.exists_weierstrassCurve_iso` and invert the isomorphism.

## 3. Stacks modules built

The 17 unbuilt modules under `Curves/GenusOne/WeierstrassEquation` were built once, one at a
time (each 10–90 s): `Constructions.{GradedSectionRingMap, ProjDegreeOneRepresents,
ProjectiveSpaceGeneratingSections}`, `Curves.GenusOne.{StalkOrder, SectionOrder, PointDivisor,
SectionDivision, SectionRing, SectionRingData, WeierstrassProj, WeierstrassModel,
WeierstrassEquation}`, `SectionProduct.StalkMultiple`, `RingTheory.GradedAlgebra.GenusOneSectionRing`,
`RingTheory.Smooth.PlaneHypersurface`, `EllipticCurve.{DiscriminantSmooth, DiscriminantSmoothCubic}`.
Nothing else outside the project was built. `h⁰ = 1` came from prebuilt modules
(`EulerCharAdditivity`, `CohomologyComparison`, `ProperGlobalSections`); the predecessor's
`SepClosedComponents` route was not needed.

## 4. Build and audit

`nice -n 10 lake build RamanujanWeil.Arith.DeuringWModelAxioms`. About 0.5k lines in total (Chi 206, Genus 243, main 53). Full audit build ~13 min.
`DeuringWModelGenus` peaks at about 11 GB RSS and ~10 min (mostly import loading of G6/G7 plus
the Stacks cohomology stack); `DeuringWModel` imports `DeuringDescent`.

## 5. Consequences

* `Descent.weierstrassDescent_of_model` is now unconditional: `WModel.weierstrassDescent K`.
* The hypothesis `hD : WeierstrassDescent K` of `G5.surjClass_of_descent_minimal` can now be
  discharged by `WModel.weierstrassDescent K`, so `surj_class` no longer depends on
  `WeierstrassModel K̄`; its remaining inputs are the others of that theorem (`MinimalOrder`
  for the base curve, `hΛ`, …). This corollary is not packaged here.
