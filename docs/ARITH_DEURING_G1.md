# A3-ord, G1: geometric cubics, coordinate changes, and the route to the Jacobian (2026-11-09)

This continues `docs/ARITH_DEURING_PROGRESS2.md` §3c. This session proves **G1.3 in full**,
including the Frobenius twist, and combines it with `DeuringG1Descent`. The frozen fields
`rel_iff` and `card_stab` are now reduced to one statement: **`Ψ`-equivariant pointed
isomorphisms of the geometric cubics `E_W` correspond to `π`-equivariant isomorphisms of their
Jacobians.** That statement is G1.0 + G1.1 + G1.2, and none of the three is proved yet.

All new files are axiom-clean: only `propext`, `Classical.choice`, `Quot.sound`, with no
`sorry`/`admit`/`native_decide`/`axiom`. The audit file is
`RamanujanWeil/Arith/DeuringG1Axioms.lean`. No existing file was edited. The Stacks module
`Stacks.WeierstrassCubicAutomorphisms` was not prebuilt; it was built once this session, alone.

| File | Imports |
|---|---|
| `Arith/DeuringG1Coord.lean` (~420 lines) | `DeuringG1Descent`, Stacks `WeierstrassCubicAutomorphisms`, `EtaleCohomology.Trace.ArithmeticFrobeniusInverse` |
| `Arith/DeuringG1Axioms.lean` | audit |

Build: `nice -n 10 lake build RamanujanWeil.Arith.DeuringG1Axioms` (about 1–3 min, mostly import
loading).

## 1. Proved (`DeuringG1Coord.lean`, namespace `…Deuring.Geom.Coord`)

### 1a. Any commutative ring `R`

| Name | Statement |
|---|---|
| `familyIsoEquiv C C'` | `FamilyIso (familyOf C') (familyOf C) ≃ {γ : VariableChange R // γ • C = C'}`. Pointed isomorphisms of plane cubics over `Spec R` are coordinate changes; this is Stacks' `exists_unique_variableChange` packaged as an `Equiv`. |
| `coordMap γ h`, `familyIsoOfVariableChange` | The morphism, and the pointed isomorphism, of a coordinate change. |
| `isIso_mapMap` | `mapMap C e` is an isomorphism when `e` is a ring isomorphism. |
| `mapMap_comp'`, `mapMap_congr` | Changing coefficients in two steps (a copy of the Torsor-file lemma, which avoids building that module). |
| `frobOf σ C hC` | The twist `E_C ⟶ E_C` over `Spec σ`, for a ring automorphism `σ` with `C.map σ = C`. |
| **`frobOf_comp_coordMap`** | `frobOf σ C' ≫ coordMap γ = coordMap (γ.map σ) ≫ frobOf σ C`. |
| **`frobOf_comm_iff`** | The isomorphism of `γ` commutes with the twists iff `γ.map σ = γ`. |
| `frobOf_comm_iff_familyIsoEquiv` | The same statement, read through `familyIsoEquiv`. |

### 1b. `K = 𝔽_q`, `K̄ = AlgebraicClosure K`

`geomFamily W = (familyOf W).pullback (Spec K̄ → Spec K)` has total space Stacks'
`fieldBaseChange (Over.mk (projectionOf W)) K̄`, the curve used in `DeuringG2`.
`twistFrob W = galoisBaseChange … (frobeniusAlgEquivOfAlgebraic K K̄)` is `Ψ_W`.

| Name | Statement |
|---|---|
| `geomIsoHom W` | `E_W ≅ projOf (W_K̄)`, from Stacks' `familyOfMapIso`. |
| **`galoisBaseChange_comp_geomIso`** | `Ψ_W ≫ geomIsoHom = geomIsoHom ≫ frobOf (x ↦ x^q)`: the twisted Frobenius, written in coordinates. |
| `twist_comm_iff_coord` | A pointed isomorphism commutes with `Ψ` iff its coordinate transport commutes with `frobOf`. |
| **`geomIsoEquiv W W'`** | `{α : E_{W'} ≅ E_W pointed over K̄ // α ≫ Ψ_W = Ψ_{W'} ≫ α} ≃ {γ ∈ frobFixed // γ • W_K̄ = W'_K̄}`. |
| **`mem_orbit_iff_nonempty_frobIso`** | `W' ∈ VariableChange(K) • W ↔ Nonempty (FrobIso W W')`. |
| **`card_stabilizer_eq_card_frobAut`** | `#Stab_{VariableChange K}(W) = #{pointed Ψ-equivariant automorphisms of E_W}`. |

None of these needs `W` to be elliptic.

## 2. What remains of G1, and how to do it

The target, G1.4, is

`FrobIso W W' ≃ {e : J_{W'} ≅ J_W // IsMonHom e.hom ∧ e.hom ≫ π_W = π_{W'} ≫ e.hom}`

for **concrete** Jacobians. Combined with §1b it gives exactly what `rel_iff` and `card_stab`
consume.

**Correction to PROGRESS2 §3c, G1.0.** Adding the field
`E : A(k̄) ≃+ Pic⁰` to `FrobeniusJacobian` (the old "FrobeniusJacobianPic" plan) is **not
enough**. `E` pins down only the `k̄`-points of `A`, not `A` as a scheme, so no morphism
`A ≅ A'` can be produced from it. The Jacobian has to be the representing object itself.

### G1.0, concrete Jacobian (0.4–0.7k lines, low risk)

Use `structure JacSite W := (B : BigFppfSite) (hX : B.Contains E_W) (hk : B.Contains (Spec K̄))`.
Nonemptiness is `BigFppfSite.exists_containing {E_W, Spec K̄}`. Different `W` may live in
different sites: `J_W` and the Abel–Jacobi map `aj` are objects and morphisms of
`Over (Spec K̄)`, so isomorphisms across sites need no common site.

* Base point: `σ = pullback.lift (Spec K̄ → Spec K ≫ zeroOf W) (𝟙)`, the zero section. Do not
  use Stacks' arbitrary `exists_section_of_smooth_of_isSepClosed`; the base point must be `O`.
* Definitions: `J_W = (jacobianGrp B hX hk f σ hσ).X`, `π_W = jacobianFrobenius …` with the
  `DeuringG2` choice `Ψ = galoisBaseChangeIso … (arithmeticFrobenius …)^1`, and
  `aj_W = abelJacobi B hX hk f σ hσ` (`PicardScheme/CurvePicard/AbelJacobi.lean`).
* `σ ≫ aj = 1` is Stacks' `curvePowerZeroBasePoint_comp_abelJacobi`.
* The instances on `B.inclusion.map f` are discharged exactly as in
  `Stacks.Zeta.exists_jacobianFrobenius_data`: `isCurve_projOf_baseChange`, smooth, proper,
  `geometricallyIrreducible_of_irreducibleSpace_of_isSepClosed`, projective variety, and
  `isRepresentable_picardFunctor_of_isSepClosed`.
* G2 for this concrete `J_W`: restate `DeuringG2.exists_jacobian_charPoly_twisted` with
  `A, E, F, hdimA, hpts, htan` as hypotheses. The body after its `obtain` line can be reused
  verbatim, then fed with `jacobianPointsAddEquiv`,
  `jacobianPointsAddEquiv_comp_jacobianFrobenius` and `tangent_comp_jacobianFrobenius`. This
  gives `FrobeniusJacobian W` (charpoly `X² − tX + q`, `π² − tπ + q = 0`, `deg π = q`) for the
  concrete `J_W`. The trace input `natCard_fixedClosedPoints_weierstrass` is already stated for
  this `Ψ`.
* `frobAlg = arithmeticFrobenius^1` (both are `x ↦ x^q`; use `eq_arithmeticFrobenius`). This
  links §1b's `Ψ` to G2's `Ψ`.

### G1.1, `aj` is an isomorphism in genus 1 (1.2–2.5k lines, the main risk)

Inventory findings:
* There is no genus-1 Abel isomorphism in Stacks. `abelJacobi` is used only in the
  polarization files.
* The best route found is `Picard/AbelMapBirationalCurve.lean`,
  `isOpenImmersion_normalizedOpen_ι_comp_curveAbelMap`: `γ_g` is an open immersion on the
  normalized open `{D : h⁰(𝒪(D)) = 1, h¹ = 0}` of `Hilb^g`. For `g = 1`, every degree-1 divisor
  is normalized: `GenusOne/PointDivisorData` gives `dim H⁰(𝒪(p)) = 1` and `H¹ = 0`. So
  `γ_1 : Hilb¹ → Pic¹` is an open immersion everywhere. It is also surjective (clause (5),
  `surjective_smooth_curveAbelMap` at `d = g`), hence an isomorphism.
  * The hypothesis `TwistToNormalized` is discharged by `twistToNormalized_of_isSepClosed`.
* Still to build:
  1. `Hilb¹_{X} ≅ X`, via the diagonal family. `HilbertFunctorRepresentableAmbientDegreeOne`
     may help.
  2. Translation `Pic¹ ≅ Pic⁰` by `−[σ]`.
  3. Identifying the composite with `abelJacobi`. Both are classifying maps, so use
     `classifyingMap_eq_classifyingMap_iff` (seesaw).
* Fallback if (1)–(3) are expensive: show `aj` is finite and birational, then use Stacks'
  `isIso_of_isIntegralHom_of_isBirational_of_isNormal`-type results
  (`Spaces/IntegralBirationalOverNormal.lean`, scheme version) with `J` normal.

### G1.1′, Frobenius compatibility (0.3–0.6k lines)

`aj ≫ π = φ ≫ aj`, where `φ = geometricFrobeniusBaseChangePow` is the `K̄`-linear Frobenius.
On `K̄`-points this is `Ψ^*[P − O] = [φ(P) − O]`, which needs the pullback of point divisors
under `Ψ`. Then extend to morphisms: two `K̄`-morphisms from a reduced variety that agree on
`K̄`-points are equal. That lemma (a morphism-level `point_ext`) is not in Stacks and must be
proved (~150 lines).

Passing between `Ψ`- and `φ`-equivariance of a pointed isomorphism uses `Ψ ≫ φ = F^f` and
naturality of `F`. The direction "commutes with `φ` ⇒ commutes with `Ψ`" also needs `F^f` to be
an epimorphism on the reduced curve, or the same morphism-level `point_ext`.

### G1.2, rigidity in dimension 1 (0.4–1k lines)

A pointed isomorphism `J' ≅ J` of 1-dimensional abelian varieties is a homomorphism.

* Not in Stacks (`grep rigidity` finds nothing).
* `jacobianPullback` handles only endomorphisms of a single curve, so it cannot give
  functoriality between different curves.
* Cheapest route: rigidity lemma for `J' × J' → J`. Alternatively, transport through `aj` and
  prove that pullback along a pointed curve isomorphism preserves linear equivalence of point
  divisors.

### G1.4, assembly (0.2–0.4k lines once G1.0–G1.2 exist)

Write `e = aj'⁻¹ ≫ α ≫ aj` in `Over (Spec K̄)`, with
`α ↦ Over.homMk α.iso.hom α.iso_map`. Then:
* `e` is pointed by `σ ≫ aj = 1`, so G1.2 makes it a homomorphism.
* `e ≫ π = π' ≫ e ⟺ α ≫ φ = φ' ≫ α ⟺ α ≫ Ψ = Ψ' ≫ α`, by G1.1′.
* Compose with `geomIsoEquiv`, `mem_orbit_iff_nonempty_frobIso` and
  `card_stabilizer_eq_card_frobAut`.

**Remaining G1 total: about 2.5–5.2k lines.** G1.3 (estimated 0.3–0.6k) is done. The risk is
still G1.1; the normalized-open route above makes it concrete.
