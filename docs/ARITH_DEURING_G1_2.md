# A3-ord, G1 session 2: the concrete Jacobian (G1.0) and the Abel–Jacobi isomorphism (G1.1)

This continues `docs/ARITH_DEURING_G1.md` §2. This session proves **G1.0** (the concrete Jacobian
`J_W`, with the G2 facts) and **G1.1** (the Abel–Jacobi map `aj_W : E_W ⟶ J_W` is an
isomorphism), both **unconditionally**. G1.1′ (Frobenius compatibility) and G1.2 (rigidity) are
not started.

All new files are axiom-clean: only `propext`, `Classical.choice`, `Quot.sound`, with no
`sorry`/`admit`/`native_decide`/`axiom`. The audit file is
`RamanujanWeil/Arith/DeuringG1Axioms2.lean`. No existing file was edited.

| File | Lines | Imports |
|---|---|---|
| `Arith/DeuringG1Jac.lean` | 503 | `DeuringG2`, `DeuringG1Coord`, Stacks `CurvePicard.AbelJacobi` |
| `Arith/DeuringG1Abel.lean` | 313 | Stacks `AbelJacobi`, `NormalizedRepresentable`, `HilbertFunctorRepresentableAmbientRankOne`, `FibreDegreeAdd` |
| `Arith/DeuringG1RR.lean` | 181 | `DeuringG1Abel` + 10 prebuilt Stacks modules (fibre cohomology, Tag 0B90) |
| `Arith/DeuringG1Point.lean` | 79 | `DeuringG1Jac`, `DeuringG1RR` |
| `Arith/DeuringG1Axioms2.lean` | audit | `DeuringG1Point` |

Stacks modules built this session (each alone): `PicardScheme.CurvePicard.AbelJacobi`,
`Picard.HilbertFunctorRepresentableAmbientRankOne`.

Build: `nice -n 10 lake build RamanujanWeil.Arith.DeuringG1Axioms2` (each file 2–4 min, mostly
import loading).

## 1. G1.0: the concrete Jacobian (`DeuringG1Jac.lean`)

Namespace `…Deuring.Geom` (general) and `…Deuring.Geom.Jac` (Weierstrass).

| Name | Statement |
|---|---|
| `charPoly_of_jacobianData` | `DeuringG2.exists_jacobian_charPoly_twisted` for a **given** Jacobian: hypotheses `A, GrpObj, IsAbelianVariety, E : A(Ω) ≃+ Pic⁰, F, IsMonHom F, dim A = g, F = Ψ^* on points, F kills tangent vectors`; conclusion `χ_F.nextCoeff = N₁ − 1 − q` and `q`-symmetry. Body reused verbatim. |
| `Jac.Ew W`, `Jac.gw W` | `E_W = fieldBaseChange (projOf W) K̄` and `E_W ⟶ Spec K̄` (the curve of `DeuringG2` and of `Coord.geomFamily`). |
| `Jac.JacSite W` | `structure` with `B : BigFppfSite`, `hX : B.Contains E_W`, `hk : B.Contains (Spec K̄)`. |
| `Jac.nonempty_jacSite` | `Nonempty (JacSite W)` (`BigFppfSite.exists_containing`). |
| `Jac.zeroPt W` | the zero section `O : Spec K̄ ⟶ E_W`; `zeroPt_eq_geomFamily_zero : zeroPt W = (Coord.geomFamily W).zero` (rfl). |
| `JacSite.f`, `o_comp` | the structure map as a site morphism; `O ≫ f = 𝟙`. Instances `IsCurve`, `Smooth`, `IsProper`, `GeometricallyIrreducible`, `IsProjectiveVariety` on `S.B.inclusion.map S.f`, and `(picardFunctor …).IsRepresentable`. |
| `JacSite.J` | `(jacobianGrp S.B S.hX S.hk S.f O _).X`; `isAbelianVariety_J`. |
| `JacSite.aj` | `abelJacobi S.B S.hX S.hk S.f O _ : curveOver … ⟶ S.J`. |
| `JacSite.frob`, `JacSite.Ψ` | `arithmeticFrobenius ^ 1` and `galoisBaseChangeIso … frob` (the `DeuringG2` choices). |
| **`JacSite.twist_eq`** | `Ψ.hom = Coord.twistFrob W`: G2's `Ψ` is G1.3's twisted Frobenius. |
| `JacSite.Ψ_comp` | `Ψ ≫ f = f ≫ absoluteFrobeniusPow (Spec K̄) p _ n`. |
| `JacSite.π` | `jacobianFrobenius … Ψ.hom …`; `isMonHom_π`. |
| `JacSite.dim_J` | `abelianVarietyDimension S.J = 1`. |
| **`JacSite.charPoly_π`** | `endCharPoly S.J S.π = X² − C t · X + C q`, `t = traceOfFrob W`. |
| **`JacSite.frobeniusJacobian`** | `(S.J, S.π)` packaged as `FrobeniusJacobian W` (`frobeniusJacobian_A/π` are `rfl`). |
| **`JacSite.frob_quadratic`** | `π² − tπ + q = 0` in `End(J_W)`. |
| **`JacSite.endDegree_π`** | `deg π = q`. |

## 2. G1.1: `aj` is an isomorphism in genus one

### 2a. `Hilb¹_{X/S} = X` (`DeuringG1Abel.lean`, namespace `Abel.Hilb`, any separated `X / S`)

| Name | Statement |
|---|---|
| `pointFamily hd x` | the graph of `x : T ⟶ X` as a `HilbertFamily X T d`, given `hd : d = 1`. |
| `isIso_family` | a degree-one family maps isomorphically to `T` (Stacks' `isIso_of_isFiniteLocallyFreeOfRank_one`). |
| `familySection` | the section `T ⟶ X` of a degree-one family. |
| `pointIdeal_familySection`, `familySection_pointFamily` | the two round trips (via `Scheme.Hom.ker_comp_of_isIso`, `ker_subschemeι`, `toImage_imageι`). |
| **`representsSelf hd`** | `RepresentsHilbertFunctorOfRank X X d` with universal family the diagonal. |

### 2b. The Abel–Jacobi map (`DeuringG1Abel.lean`, namespace `Abel`, Stacks' curve setting)

Setting: `B, hX, hk, f, σ, hσ` with `IsCurve`, `GeometricallyIrreducible`, `Smooth`, `IsProper`,
`IsProjectiveVariety`, representable Picard functor, and `hg : genus = 1`.

| Name | Statement |
|---|---|
| `DegreeOneNormalized` | Prop: every point of the Picard functor with fibre degree `1` is in `curveNormalized` (fibres have `H¹ = 0`, `dim H⁰ = 1`). **Proved** in `DeuringG1RR` for genus one. |
| `hilbSelf hg` | `X` as `Hilb^g_{X/k}` (`representsSelf` at `d = genus = 1`). |
| `basePt`, `constPt T` | `c₀` as `baseObj ⟶ X`, and `T ⟶ Spec k ⟶ X`. |
| `univ`, `constClass T` | `[𝒪(Δ)]` and `[c₀]_T = (constPt T)^*[𝒪(Δ)]`. |
| `familyClass_constantFamily` | the class of `{c₀} × X` is `[c₀]_X`. |
| **`jacobianHomAddEquiv_comp_abelJacobi`** | the `Pic⁰`-point of `m ≫ aj` is `m^*[𝒪(Δ)] − [c₀]_T`. |
| `mem_degreeOne_add_constClass` | `ζ ∈ Pic⁰(T) ⇒ ζ + [c₀]_T` has fibre degree `1`. |
| **`bijective_comp_abelJacobi`** | given `DegreeOneNormalized`: `m ↦ m ≫ aj`, `(T ⟶ X) → (T ⟶ J)`, is bijective for every test scheme `T` (Stacks' `exists_map_universalClass_eq`, `eq_of_map_universalClass_eq`, Tag 0B9X, at `H = X`). |
| **`isIso_abelJacobi`** | given `DegreeOneNormalized`: `IsIso (abelJacobi …)` (Yoneda at `T = Pic⁰` and `T = X`). |

### 2c. The Riemann–Roch input (`DeuringG1RR.lean`)

| Name | Statement |
|---|---|
| `finrank_fibreCohomology_one_eq_zero_of_large` | verbatim copy of Stacks' `Stacks.AbelMap.finrank_fibreCohomology_one_eq_zero` (`Picard/AbelMapSmooth.lean`, whose module needs 36 unbuilt modules; the proof's own imports are all prebuilt): `χ(L_t) = d + 1 − g`, `d ≥ 2g − 1` ⇒ `h¹(L_t) = 0`, via Tag 0B90 over `κ(t)^alg`. |
| **`degreeOneNormalized hg`** | `DegreeOneNormalized` for genus one: `fibreDegree = 1` and `fibreEuler 0 = 1 − g = 0` give `χ = 1`; Tag 0B90 (`isZero_cohomologyOverField_one_of_two_mul_genus_sub_one_le_invertibleCurveDegree`) gives `h¹ = 0`, so `h⁰ = 1`. |
| **`isIso_abelJacobi_of_genus_eq_one`** | **G1.1, unconditional**: for a geometrically irreducible smooth projective curve of genus one with a rational point, `abelJacobi : X ⟶ Pic⁰_{X/k}` is an isomorphism. |

### 2d. For `W` (`DeuringG1Point.lean`)

| Name | Statement |
|---|---|
| `Abel.constPt_baseObj`, **`Abel.jacobianHomAddEquiv_basePt_comp_abelJacobi`** | `aj(c₀) = 0` in `Pic⁰(Spec k)`. |
| `JacSite.genus_f` | `genus (S.B.inclusion.map S.f) = 1`. |
| **`JacSite.isIso_aj`** (instance), **`JacSite.ajIso`** | `aj_W : E_W ≅ J_W` over `Spec K̄`. |
| `JacSite.jacobianHomAddEquiv_zero_comp_aj` | `aj_W(O) = 0`. |

## 3. What remains of G1

* **G1.1′, Frobenius compatibility** (0.3–0.6k). `aj ≫ π = φ ≫ aj`, `φ = geometricFrobeniusBaseChangePow`.
  Route now available: `π = jacobianFrobenius` is characterized on `T`-points by
  `jacobianHomAddEquiv_comp_jacobianFrobenius` (twisted pullback of the class), and `aj` on
  `T`-points by `jacobianHomAddEquiv_comp_abelJacobi` above. Both sides of
  `aj ≫ π = φ ≫ aj` are maps out of `X`, so by `jacobianHomAddEquiv` injectivity it suffices to
  compare classes at `T = X`: the twisted pullback of `[𝒪(Δ)] − [c₀]` against
  `φ^*([𝒪(Δ)] − [c₀])`. With `ajIso` the morphism-level `point_ext` lemma is no longer needed for
  this direction (the comparison is on the universal point).
* **G1.2, rigidity in dimension 1** (0.4–1k). Cheapest route now: transport through `ajIso`. A
  pointed isomorphism `α : E_{W'} ≅ E_W` induces `e = aj'⁻¹ ≫ α ≫ aj`; it is a homomorphism
  iff pullback along `α` is additive on `Pic⁰`, which on `T`-points is
  `jacobianHomAddEquiv_comp_abelJacobi` plus `classifyingMap_add`.
* **Pointedness in `η` form.** `aj(c₀) = 0` is proved on `Pic⁰`; the `η[J] = toUnit ≫ …` form
  needs the identification `post.obj baseObj = 𝟙_` and of the group law of `jacobianGrp`
  (`jacobianHomAddEquiv` is additive), ~50 lines.
* **G1.4, assembly** (0.2–0.4k), unchanged.

**Remaining G1 total: about 1.0–2.3k lines** (was 2.5–5.2k). The main risk (G1.1) is gone.
