# A3-ord, G7-C: `Genus2ModelExistence`, PROVED (2026-11-10; see §6, §7)

This continues `ARITH_DEURING_G7_WC.md` §2/§3 (step **C** of route F2′, `ARITH_DEURING_G7FIN.md`).
Target: `Genus2ModelExistence K` (`Arith/DeuringG7Genus2Model.lean`). Every smooth proper
geometrically irreducible genus-2 curve `Y / K` has function field `≅ K(x)[y]/(y² + h y − f)`
with `deg h ≤ 3`, `deg f ≤ 6`.

**Result.**

```lean
theorem genus2ModelExistence_of_canonical_of_pencil
    (hω : Genus2CanonicalExistence K) (hP : Genus2PencilFunctionField K) :
    Genus2ModelExistence K
```

The algebra (function field ⇒ model) and the Riemann–Roch dimension count are fully proved. What
remains are two named Props: the **canonical bundle** and the **canonical pencil on the function
field**. No existing file was edited. There is no `sorry`, `admit`, `native_decide` or `axiom`.
Audit: `RamanujanWeil/Arith/DeuringG7Genus2ExistAxioms.lean`; everything depends only on
`[propext, Classical.choice, Quot.sound]`.

| File | Imports | Content |
|---|---|---|
| `Arith/DeuringG7Genus2ExistAlg.lean` | Mathlib only | the function-field algebra: `PencilData`, `IntegralPencilData`, model isomorphism |
| `Arith/DeuringG7Genus2ExistRR.lean` | Stacks RR, 0B90-over-any-field, `deg L^{⊗n}` | `h⁰(L^{⊗n}) = 2n − 1` for `deg L = 2`, `g = 2`, `n ≥ 2` |
| `Arith/DeuringG7Genus2Exist.lean` | Genus2Model, Alg, RR | named Props, reductions |
| `Arith/DeuringG7Genus2ExistAxioms.lean` | all | audit |

Stacks modules built: only `StacksFrontier.AlgebraicGeometry.Curves.LargeDegreeVanishingField`
(1 module, 38 s). Everything else used was already built.

## 1. Survey: what Stacks has (and what it would cost)

* **No hyperelliptic / canonical-map / genus-2 model theorem** exists in Stacks. A grep of
  `Curves/` for hyperelliptic, GenusTwo or canonical map finds nothing. The genus-1 analogue
  `GenusOne.exists_weierstrassCurve_iso` needs a **rational point** (it uses orders at `p`, via
  `GenusOneSectionRing.Data`). A genus-2 curve over `𝔽_q` may have none, so that route does not
  transfer.
* **The canonical bundle.** The facts needed are `ω` invertible, `deg ω = 2g − 2` and
  `h⁰(ω) = g`. Unbuilt module counts (transitive):
  * `deg ω = −2χ(𝒪)` given invertibility: `VanishingResults.DualizingCanonicalDegree`, 27.
  * `h⁰(ω) = g`: `SerreDuality.Duality`, 66 (or `DualizingDimensionDualityZero`, 28).
  * **Invertibility of ω for a smooth curve**: every route is hundreds of modules.
    * `GenusCurve.SmoothCurveDifferentials.isInvertible_dualizingSheafOverField_of_isCurve`: 650.
    * `VanishingResults.DualizingSheafSmoothCurve` (`ω ≅ Ω`): 440.
    * `GorensteinDualizingInvertible`: 288.
    * `DualizingSheafInvertible` (algebraically closed field only): 158.
    * `GenusCurve.DualizingDegree`: 378.
    * `DifferentialsDegreeGenus` (`deg Ω = 2g − 2`, Tag 0C1A): 774.

    A cheaper route would be: `ω` torsion free ⇒ locally free
    (`isTorsionFree_iff_isFiniteLocallyFree`, Tag 0CC4, built), with rank ≤ 1 from
    `DualizingSheafRank` (27). But there is no theorem that `dualizingSheafOverField` is an
    `IsDualizingModule` (which would give torsion-freeness via `DualizingModuleTorsionFree`, 8).
    The direct argument `Hom(T, ω) = H¹(T)^∨ = 0` for the torsion subsheaf `T` is not formalized.
  * So the canonical bundle is left as the named Prop **`Genus2CanonicalExistence`**.
* **Riemann–Roch pieces that are cheap** (all built, or 1 module):
  * `finrank_sub_finrank_eq_invertibleCurveDegree_add_genus` (`GenusCurve/RiemannRoch`);
  * `invertibleCurveDegree_tensorPower_eq_mul_of_isCurve` (`AmpleDegreeCriterion/CurveInputs`);
  * `isZero_cohomologyOverField_one_of_geometricallyIntegral`: Tag 0B90 over any field for
    geometrically integral curves (`Curves/LargeDegreeVanishingField`, the one module built);
  * `isIso_globalSections_of_geometricallyIntegral`, `geometricallyReduced_of_smooth`.
* **The pencil morphism.** `PencilDegree` (Tag 0CCR: a `g¹_d` gives `φ : X → ℙ¹` nonconstant of
  degree `≤ d`) needs only 2 unbuilt modules. `LinearSeriesMorphism`, `LinearSeriesChartRatio`
  and `LinearSeriesGenericPoint` (germ ratios at the generic point) are built. This is the
  natural input for the second named Prop (§4).

## 2. The algebra (`DeuringG7Genus2ExistAlg`, Mathlib only, fully proved)

`F / K` is a field extension (the function field). `x ∈ F`, and `V : ℕ → Submodule K F`.

* **`linearIndependent_pow_pow_mul`**: `x^i (i < m)` and `x^j y (j < n)` are `K`-independent
  when `x` is transcendental and `y ∉ K(x)`.
* **`exists_relation`**: if `x^i (i ≤ 6)`, `x^j y (j ≤ 3)` and `y²` lie in a space of dimension
  `≤ 11`, then `y² + h(x) y = f(x)` with `deg h ≤ 3`, `deg f ≤ 6`. The 11 independent vectors
  span the space.
* **`exists_not_mem_adjoin`**: if `dim V ≥ 5` and `V ∩ K(x) ⊆ ⟨1, x, x², x³⟩`, some `y ∈ V` is
  not in `K(x)`.
* **`nonempty_algEquiv_adjoinRoot`**: if `x` is transcendental, `[F : K(x)] ≤ 2`, `y ∉ K(x)` and
  `y² + h y = f`, then `F ≃ₐ[K] AdjoinRoot (quadEqn h f)` over `RatFunc K`.
  * `ratFuncHom` is `RatFunc K → F`, `X ↦ x`, with image `K(x)`.
  * `quadEqn` is irreducible: a root in `K(x)` would put `y` or `−h − y` in `K(x)`.
  * The lift is injective (field), and surjective because `{1, y}` is a `K(x)`-basis of `F`.
* **`PencilData`** packages
  * `x` transcendental, `[F : K(x)] ≤ 2`;
  * `1 ∈ V 0`, `1, x ∈ V 1`, `V a · V b ⊆ V (a + b)`;
  * `dim V 3 ≥ 5`, `dim V 6 ≤ 11`;
  * the pole condition `V 3 ∩ K(x) ⊆ ⟨1, x, x², x³⟩`.

  **`PencilData.exists_model`** gives `h, f` and the isomorphism: `y ∈ V 3 ∖ K(x)`, then
  `y² ∈ V 6`.
* **The pole condition from integrality.**
  * `exists_aeval_eq_of_isIntegralElem`: an element of `K(x)` integral over `K[x]` is a
    polynomial in `x`. `K[X]` is a UFD, hence integrally closed in `RatFunc K`.
  * `transcendental_inv`: `x⁻¹` is transcendental.
  * **`mem_cubicSpan_of_isIntegralElem`**: if `f ∈ K(x)`, `f` is integral over `K[x]`, and `f/x³`
    is integral over `K[x⁻¹]`, then `deg f ≤ 3`. Write `f = p(x)` and `f/x³ = q(x⁻¹)`. Then
    `reflect_d(p) = q·X^{d−3}`, and comparing constant coefficients gives `lc(p) = 0` if `d > 3`.
  * **`IntegralPencilData`** is `PencilData` with the pole condition replaced by these two
    integrality conditions (the geometric form, §4). `IntegralPencilData.toPencilData` converts
    one to the other.

Characteristic 2 is included: nothing above divides by 2, and `h` is allowed.

## 3. Riemann–Roch (`DeuringG7Genus2ExistRR`, fully proved)

Setting: `Y / K` smooth, proper, geometrically irreducible, an `IsCurve`, of genus 2, and `L`
invertible.

* `geometricallyIntegral`, `isIso_globalSections` (`H⁰(𝒪) = K`), `hdim`.
* `finrank_sub_finrank_eq`: `h⁰(L) − h¹(L) = deg L − 1`.
* **`finrank_tensorPower_eq`**: if `deg L = 2` and `n ≥ 2`, then `h⁰(L^{⊗n}) = 2n − 1`.
  * `deg L^{⊗n} = 2n ≥ 4 ≥ 2g − 1`, so `H¹ = 0` by 0B90 over any field.
  * Riemann–Roch then gives the dimension.
  * These are exactly `dim V 3 = 5`, `dim V 6 = 11`.

## 4. The two remaining named Props (`DeuringG7Genus2Exist`)

```lean
def Genus2CanonicalExistence (K) : Prop :=
  ∀ Y (s : Y ⟶ Spec K) [IsCurve K s] [Smooth s] [IsProper s] [GeometricallyIrreducible s],
    genus s = 2 → ∃ (L : Y.Modules) (_ : IsInvertible L),
      invertibleCurveDegree K s (hdim s) L = 2 ∧ finrank K (H⁰(Y, L)) = 2

def Genus2PencilFunctionField (K) : Prop :=
  ∀ Y s [...], genus s = 2 → ∀ L [IsInvertible L], deg L = 2 → h⁰(L) = 2 →
    (∀ n ≥ 2, h⁰(L^{⊗n}) = 2n − 1) →
    letI := functionFieldAlgebra K s; Nonempty (IntegralPencilData K Y.functionField)
```

Proved:
* `hasHypModel_of_pencilData`;
* `genus2ModelExistence_of_pencilExistence` (from the intermediate `Genus2PencilExistence`:
  `PencilData` on every genus-2 function field);
* `genus2PencilExistence_of_canonical_of_pencil`, which feeds `finrank_tensorPower_eq` into
  `Genus2PencilFunctionField`;
* **`genus2ModelExistence_of_canonical_of_pencil`**.

### 4.1 `Genus2CanonicalExistence`: what it needs

Take `L = ω = dualizingSheafOverField s`.

* Invertibility of `ω`: see §1, hundreds of modules on the existing routes. The cheap route is
  torsion-free ⇒ locally free (Tag 0CC4, built), plus rank 1, plus torsion-freeness via
  `Hom(T, ω) ≅ H¹(T)^∨ = 0` for the torsion subsheaf (`DualizingSheafDuality`, 17 unbuilt).
  Estimate 0.3–0.6k lines plus ≈ 30–70 module builds.
* `deg ω = 2`: `DualizingCanonicalDegree` (27 unbuilt), `deg ω = −2χ(𝒪) = 2g − 2`.
* `h⁰(ω) = 2`: `SerreDuality.Duality` (66 unbuilt) or `DualizingDimensionDualityZero` (28).

By `finrank_sub_finrank_eq`, `h⁰(L) = 2` is equivalent to `h¹(L) = 1` for `deg L = 2`. By Serre
duality (clause (5), `h¹(L) = dim Hom(L, ω)`) this says `L ≅ ω` once `ω` is invertible of
degree 2. Over `𝔽_q` there is no point-counting shortcut,
because a genus-2 curve may have no rational point.

### 4.2 `Genus2PencilFunctionField`: what it needs

Let `s₀, s₁` be a basis of `H⁰(L)`.

1. **Germ embedding** `H⁰(L^{⊗n}) ↪ K(Y)`, `t ↦ t_η/s₀^n_η`, multiplicative. `L_η` is a
   1-dimensional `K(Y)`-space. The product compatibility is the generic-point case of
   `SectionProduct.StalkMultiple` / `GenusOne.sectionOrd_mul`, which are built. This gives `V n`
   with `1 ∈ V 0, V 1`, `x = s₁/s₀ ∈ V 1`, `V a·V b ⊆ V (a+b)`, and `dim V n = h⁰(L^{⊗n})`
   (injectivity of germs on an integral scheme).
2. **`x` transcendental, `[K(Y) : K(x)] ≤ 2`.** The pencil `(L, ⟨s₀, s₁⟩)` is a `g¹_2`.
   Tag 0CCR (`PencilDegree.degreeOver_le_or_constant_of_isRegular`, 2 unbuilt modules) gives
   `φ : Y → ℙ¹` nonconstant of degree `≤ 2` (the constant case needs `H⁰(𝒪) ≠ K`, excluded).
   `LinearSeriesGenericPoint` / `LinearSeriesChartRatio` identify `φ^♯(T₁/T₀)` with the germ
   ratio `s₁/s₀ = x`. Also needed: `degreeOver φ = [K(Y) : K(T)]`.
3. **Integrality.** `φ` is finite (proper and quasi-finite). So `Γ(Y_{s₀}, 𝒪) = Γ(φ⁻¹𝔸¹, 𝒪)` is
   finite over `K[x]`. `V 3 ⊆ Γ(Y_{s₀}, 𝒪)` since `t/s₀³` is regular where `s₀ ≠ 0`.
   Symmetrically, `f/x³ = t/s₁³ ∈ Γ(Y_{s₁}, 𝒪)` is integral over `K[x⁻¹]`.

Estimate: 1.5–2.5k lines (1: 0.4–0.7k, 2: 0.5–1k, 3: 0.5–0.8k).

## 5. Build

`nice -n 10 lake build RamanujanWeil.Arith.DeuringG7Genus2ExistAxioms`. ExistAlg about 15 s.
ExistRR and Exist about 100 s each, mostly import loading.

## 6. Update: `Genus2CanonicalExistence` PROVED (2026-11-10)

`Arith/DeuringG7Genus2Canon.lean` proves

```lean
theorem genus2CanonicalExistence : Genus2CanonicalExistence K      -- every field K
theorem genus2ModelExistence_of_pencil (hP : Genus2PencilFunctionField K) :
    Genus2ModelExistence K
```

The one remaining named Prop on the route to `Genus2ModelExistence K` is
**`Genus2PencilFunctionField K`** (§4.2, unchanged).

**The route.** It differs from §4.1: it does not use torsion-free ⇒ locally free.
Take `L = ω = dualizingSheafOverField s`.

* **Invertibility.** Smooth over a field ⇒ regular (`isRegular_of_smooth_over_field`) ⇒
  Gorenstein (`isGorenstein_of_isRegular`). Irreducible ⇒ equidimensional
  (`Equidimensional.of_preirreducibleSpace`). With dimension 1, Stacks 0BS6 (1),
  `isInvertible_dualizingSheafOverField_of_isGorenstein`, gives `ω` invertible and locally free of
  rank 1.
* **`deg ω = 2`.** Stacks 0BS6 (2), `curveDegree_dualizingSheafOverField_eq_neg_two_mul_of_isGorenstein`,
  gives `deg ω = −2χ(𝒪)`. `eulerCharacteristic_unit_eq_one_sub_genus` gives `χ(𝒪) = 1 − g`.
  Together, `deg ω = 2g − 2` (`invertibleCurveDegree_dualizing`).
* **`h⁰(ω) = 2`.** Apply the duality of dimensions at `ℰ = 𝒪`,
  `finrank_cohomologyOverField_zero_dualTensorDualizingSheafOverField_eq_one`, and read it through
  `𝒪^∨ ⊗ ω ≅ 𝒪 ⊗ ω ≅ ω` (`unitDualIso`, `tensorProductLeftUnitor`; `dualUnitTensorDualizingIso`).
  This gives `h⁰(ω) = h¹(𝒪) = g` (`finrank_dualizing_zero`).

The finite-field and point-count alternative was not needed. The statement holds over every
field.

**Stacks builds.** These modules were built one at a time under `nice -n 10`:
`GorensteinCurveRiemannRoch`, `DualizingSheafHom`, `DualizingDimensionDuality`,
`DualizingRiemannRoch`, `PencilDegree` (Tag 0CCR, for §4.2), and their unbuilt dependencies.
That is 300 modules, about 2 h serial.

**Audit.** `RamanujanWeil/Arith/DeuringG7Genus2FinalAxioms.lean`. Everything depends only on
`[propext, Classical.choice, Quot.sound]`.

### 6.1 What remains: `Genus2PencilFunctionField`

Sub-steps (a)–(c) of §4.2 are open. `PencilDegree` is now built. Notes for the next attempt:

* `degreeOver` is a `Module.finrank`, so `degreeOver p ≤ 2` does not by itself give
  finite-dimensionality. `FiniteDimensional K(ℙ¹) K(Y)` must be proved separately.
* The germ embedding (a) can reuse the graded section ring of `GenusOne/SectionRing*`
  (`Stacks.GradedSections.sectionRing`, `sectionGerm`, `Stacks.SectionProduct`). It is built on
  `Stacks.TensorPowers.natTensorPow`, so it needs a bridge to `Invertible.tensorPower`.
* Pure algebra cannot replace the geometric inputs (b)/(c). A counterexample: on `ℙ¹`, take
  `V₀ = K`, `V₁ = ⟨1, x⟩` and `V_n = L(n∞ + (n−2)·0)` for `n ≥ 2`. This satisfies every algebraic
  axiom of `PencilData` (with `dim V_n = 2n − 1`) except the pole condition.
  * Pole-side remark: `V₃ ∩ K(x)` is the cubic span whenever some `y ∈ V₃ ∖ K(x)` exists, by a
    dimension count. So (c) could be replaced by the single condition `V₃ ⊄ K(x)`, but that is not
    obviously easier to prove geometrically.

## 7. Update: `Genus2PencilFunctionField` PROVED, hence `Genus2ModelExistence` (2026-11-10)

```lean
theorem Pencil.genus2PencilFunctionField : Genus2PencilFunctionField K   -- every field K
theorem Pencil.genus2ModelExistence : Genus2ModelExistence K             -- every field K
```

No named Prop remains on step C. No existing file was edited. There is no `sorry`, `admit`,
`native_decide` or `axiom`. Audit: `RamanujanWeil/Arith/DeuringG7Genus2PencilAxioms.lean`;
everything depends only on `[propext, Classical.choice, Quot.sound]`.

| File | Content |
|---|---|
| `Arith/DeuringG7Genus2PencilAlg.lean` | Mathlib only: `GradedPencil` and `toIntegralPencilData` |
| `Arith/DeuringG7Genus2PencilChart.lean` | sections of an invertible module on two charts, read in `K(Y)` |
| `Arith/DeuringG7Genus2PencilGeom.lean` | the graded pencil of a base-point-free pencil on a curve |
| `Arith/DeuringG7Genus2Pencil.lean` | base-point removal, the degree of `L'`, assembly |
| `Arith/DeuringG7Genus2PencilAxioms.lean` | audit |

**The route.** It avoids Tag 0CCR and the finiteness of `φ : Y → ℙ¹`, which §4.2 and §6.1
planned to use. Base-point freeness carries the whole argument.

* **Algebra (`GradedPencil`).** Take `x ≠ 0` and `V n ⊆ F`, with `1 ∈ V 0`, `1, x ∈ V 1`,
  `V a V b ⊆ V (a+b)` and each `V n` finite dimensional. Assume base-point freeness:
  `f, x f ∈ V (n+1) ⇒ f ∈ V n` for `n ≥ 1`. Assume `dim V n = a n − 1` for `n ≥ n₀`.
  * **Surjectivity (`le_sup_map`).** `V (m+2) = V (m+1) + x V (m+1)`. The two summands meet
    inside `x V m`, so a dimension count gives equality.
  * **Integrality.** `⋃ V n` is the `K[x]`-span of a single `V B`, so it is finitely
    generated. Every element is therefore integral over `K[x]`
    (`isIntegral_of_smul_mem_submodule`).
  * **`x` is transcendental.** Otherwise `⋃ V n` would be finite dimensional.
  * **`a ≥ 2`.** `1, …, xⁿ ∈ V n`.
  * **`[F : K(x)] ≤ a`.** Assume every `f` is `p/q` with `p, q` in one `V m`. Clear
    denominators, then count `x^j Q v`.
  * **Dual pencil (`inv`).** `x⁻¹` with `x⁻ⁿ V n` satisfies the same axioms. This gives
    integrality over `K[x⁻¹]`.
* **Two charts (`Chart.Data`).** Let `M` be invertible on an integral `Y`, and let `G_a, G_b` be
  sections that are nowhere zero on a cover `U_a, U_b`. Then `θ T = (T/G_a)_η` is injective,
  and its image is `{f ∈ 𝒪(U_a)_η | ρ⁻¹ f ∈ 𝒪(U_b)_η}`, where `ρ = (G_b/G_a)_η`. The proof
  glues the two local sections with `sheaf_glue_pair`.
* **On the curve (`Setup`).** For a pencil `t₀, t₁` without common zero, set
  `V n = {f | f ∈ 𝒪(U₀)_η, x⁻ⁿ f ∈ 𝒪(U₁)_η}`. The `GradedPencil` axioms are then immediate.
  * `V n ≅ H⁰(L^{⊗n})` for `n ≥ 1`. This is `Chart.Data` with `G = tᵢⁿ`, together with
    `(t₁ⁿ/t₀ⁿ) = (t₁/t₀)ⁿ` (`ratio_powSec`).
  * **Generation (`exists_div`).** If `L` is ample, `U₀` is affine:
    `Y ≅ Proj Γ_*(Y, L)` (0C6J, `isIso_projHomOfIsAmple`). Its functions are fractions
    `T/t₀ᵐ` (01PW, `chartRingMap_bijective`), and `K(Y) = Frac 𝒪(U₀)`.
* **Assembly.** A basis of `H⁰(L)` lifts to generating sections of an invertible `L' → L`
  (Stacks 0CC4, `hasGeneratingInvertibleLift_seriesSections`). Then `deg L' = 2`:
  * `≤ 2` by 0B40 (5);
  * `≤ 0` would make `L'` trivial (0B40 (4)), but `h⁰(L') ≥ 2`;
  * `= 1` contradicts `GradedPencil.two_le`, using `h⁰(L'^{⊗n}) = n − 1` for `n ≥ 3` (RR + 0B90).

  With `deg L' = 2`, `dim V n = 2n − 1` for `n ≥ 2`, which gives `IntegralPencilData`.

No new Stacks modules were built.
