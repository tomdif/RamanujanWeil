# M6: point bookkeeping, fibre counts and the assembly `IharaIdentity p + M4b ⇒ τ(p)² ≤ 4p¹¹`

Status 2026-11-08. This is milestone M6 of `docs/REALIZATION_PLAN.md` §5, together with gap 2
(`RealizesWeierstrass`) of M4a.
No `sorry`, `admit`, `native_decide` or `axiom`.

**Conditional only on one frozen Prop, `R1StalkCharpolyFibre` (M4b).**

## Files (namespace `RamanujanWeil.Ihara`)

| File | Imports | Content |
|---|---|---|
| `Ihara/IharaStatement.lean` | Endgame + Mathlib | `wc`, `traceOfFrob`, `IharaIdentity` (verbatim from `scratch/ProbeInterfaces.lean`), `weierstrassSum`, `weierstrassSum_eq_of_ihara` |
| `Ihara/PointsCount.lean` | Stacks `FieldValuedPointCount` | weighted closed-point sum = sum over `X(K)` (any `X/𝔽_q`) |
| `Ihara/PointsBase.lean` | FamilyGeometry + PointsCount + IharaStatement | `W_p(K) ≃ {c ∈ K⁵ : Δ(c) ≠ 0}`, `fibreCurve`, residue embeddings, **part A** |
| `Ihara/PointsExtension.lean` | CurveH1Core + SymWeights + IharaStatement (Mathlib only) | `ExtensionTraces`, M4a-form ⇒ all finite extensions, `powSum = frobPowerSum` |
| `Ihara/PointsFibre.lean` | SymSheaf + PointsBase + PointsExtension | **frozen M4b Prop** `R1StalkCharpolyFibre`, **part B**, stalk traces at `y_c` |
| `Ihara/Assembly.lean` | PointsFibre + FamilyPackage + Bridge | **`S_eq_pointSum`**, **`deligneBound_of_ihara_M4b`** |
| `Ihara/PointsCurve.lean` | Stacks `WeierstrassCubicCharts` + `FieldValuedPointCount` | `E(K) ≃ W(K)` for `E = projOf W` (`fvpEquivPoint`) |
| `Ihara/PointsRealizes.lean` | CurveH1Weierstrass + PointsCurve | **`realizesWeierstrass_projOf`** (M4a gap 2, unconditional) |
| `Ihara/PointsAxioms.lean` | Assembly + PointsRealizes | `#print axioms` audit |

## (A) Point bookkeeping on the base

The generic statement is in `PointsCount.lean`. Take `f : X ⟶ Spec k` locally of finite type and
quasi-compact over a finite field `k`, and `K/k` finite. Then:

```lean
noncomputable def fvpPoint (g : fieldValuedPoints f K) : closedPoints X     -- the closed point under g
theorem residueDegree_fvpPoint_dvd : residueDegree f (fvpPoint f K g).1 ∣ finrank k K
theorem finsum_closedPoints_eq {M} [NonAssocSemiring M] (G : closedPoints X → M) :
    ∑ᶠ (x : closedPoints X) (_ : residueDegree f x.1 ∣ finrank k K), (residueDegree f x.1 : M) * G x =
      ∑ᶠ g : fieldValuedPoints f K, G (fvpPoint f K g)
```

The proof uses Stacks' `fieldValuedPointsEquiv` (`X(K) ≃ Σ x, k-embeddings κ(x) → K`) and
`natCard_residueEmbeddings`, which counts `deg x` embeddings when `deg x ∣ n`. The fibres of
`fvpPoint` are the Frobenius orbits.

On `W_p` (`PointsBase.lean`, namespace `…Ihara.Family`), for any field `K` over `𝔽_p`:

```lean
def fvpEquiv p K : fieldValuedPoints (toSpecK p) K ≃ {c : Fin 5 → K // (wc c).Δ ≠ 0}
def fvpOf p K c hc : fieldValuedPoints (toSpecK p) K      -- Spec of evalHom c : 𝔽_p[a][1/Δ] → K
def coords p g : Fin 5 → K ;  theorem coords_fvpOf : coords p (fvpOf p K c hc) = c
theorem curve_map_ringOf : (curve p).map (ringOf p g) = wc (coords p g)
def fibreCurve p (y : base p) : WeierstrassCurve κ(y) := (curve p).map (residueMapOf y)
def residueEmb p g : κ(pt g) →+* K                        -- the embedding from fieldValuedPointsEquiv
theorem fibreCurve_map_residueEmb : (fibreCurve p (pt g)).map (residueEmb p g) = wc (coords p g)
open scoped Classical in
theorem finsum_closedPoints_eq_sum (n) (hn : finrank (ZMod p) K = n) (G : closedPoints (base p) → M) [Fintype K] :
    ∑ᶠ (y) (_ : residueDegree (toSpecK p) y.1 ∣ n), (residueDegree (toSpecK p) y.1 : M) * G y =
      ∑ c : {c : Fin 5 → K // (wc c).Δ ≠ 0}, G (fvpPoint (toSpecK p) K (fvpOf p K c.1 c.2))
```

`fibreCurve` uses Stacks' `residueMapOf`. That is the map in
`isPullback_fromSpecResidueField`, which identifies the fibre of `proj p` at `y` with
`projOf (fibreCurve p y)`. M4b can therefore use it directly.

## (B) Fibre count

`PointsExtension.lean`:

```lean
def ExtensionTraces {k : Type} [Field k] (W : WeierstrassCurve k) (q : ℤ) : Prop :=
  ∀ (L : Type) [Field L] [Finite L] [Algebra k L],
    traceOfFrob (W.baseChange L) = powSum (traceOfFrob W) q (Module.finrank k L)
theorem extensionTraces_of_extension [Fintype k] (W)
    (h : ∀ n (hn : 1 ≤ n), (#W(FiniteField.Extension k (ringChar k) n) : ℤ) =
      #k ^ n + 1 - frobPowerSum (#k + 1 - #W(k)) #k n) : ExtensionTraces W #k
theorem powSum_eq_frobPowerSum : powSum a q m = frobPowerSum a q m
```

The hypothesis `h` is literally the first conjunct of M4a's
`natCard_point_extension_eq_of_weierstrass`. The transport to arbitrary `L` goes through
`FiniteField.algEquivExtension` and `natCard_point_congr`.

`PointsFibre.lean`:

```lean
theorem Family.natCard_residueField : Nat.card κ(y) = p ^ residueDegree (toSpecK p) y   -- y closed
theorem powSum_fibre_eq_traceOfFrob (g : fieldValuedPoints (Family.toSpecK p) K)
    (hE : ExtensionTraces (fibreCurve p (pt g)) (p ^ deg (pt g))) :
    powSum (traceOfFrob (fibreCurve p (pt g))) (p ^ deg (pt g)) (finrank (ZMod p) K / deg (pt g)) =
      traceOfFrob (wc (coords p g))                                   -- = pⁿ + 1 − #E_c(𝔽_{pⁿ})
```

The proof makes `K` a `κ(y)`-algebra through `residueEmb`. The tower law gives
`[K:κ(y)] = n/deg y`, and `(fibreCurve).baseChange K = wc c` by `fibreCurve_map_residueEmb`.

### Frozen M4b interface

```lean
def R1StalkCharpolyFibre (p B ℓ) [site instances] : Prop :=
  ∀ y : closedPoints (Wp p B).1,
    traceOfFrob (Family.fibreCurve p y.1) ^ 2 ≤ 4 * (p : ℤ) ^ residueDegree (toSpecK p B) y.1 ∧
    (LAdicSheaf.rationalStalkFrobenius B (Wp p B) ℓ (R1 p B ℓ) y.1
        (finite_residueField (toSpecK p B) y.1 y.2)).charpoly =
      X ^ 2 - C ((traceOfFrob (Family.fibreCurve p y.1) : ℤ) : ℚ_[ℓ]) * X +
        C ((p : ℚ_[ℓ]) ^ residueDegree (toSpecK p B) y.1) ∧
    ExtensionTraces (Family.fibreCurve p y.1) ((p : ℤ) ^ residueDegree (toSpecK p B) y.1)
theorem R1StalkCharpolyFibre.toR1StalkCharpoly : R1StalkCharpolyFibre p B ℓ → R1StalkCharpoly p B ℓ
```

This is M5's `R1StalkCharpoly` with the same `y`, `q_y = p^{deg y}` and coordinates. It is
strengthened in two ways: the witness `a` is required to be `traceOfFrob` of the fibre curve, and
the fibre's point counts over all finite extensions are included.

The point counts cannot be derived from the first two conjuncts by elementary means: that would
need rationality of the zeta function of `E_y`. They come for free from M4a at `E_y`, which
yields all three conjuncts:

* `sq_le_four_mul_card_of_weierstrass` gives Hasse;
* `charpoly_weierstrassH1` gives the `H¹` charpoly with `a = #κ + 1 − #E(κ) = traceOfFrob`, using
  `#κ(y) = p^{deg y}` from `natCard_residueField`;
* `natCard_point_extension_eq_of_weierstrass` followed by `extensionTraces_of_extension` gives
  the extension counts. Rewrite `q` with `ExtensionTraces.congr_q` and `natCard_residueField`.

What M4b still has to do:

* Transport the charpoly from `H¹(E_y)` to the stalk of `R¹`: fibre identification
  `isPullback_fromSpecResidueField` plus proper base change (see `IHARA_FAMILY.md`, "Interface
  for M4b").
* Discharge M4a's remaining hypotheses at `E_y`: `HasFirstBettiTwo` (gap 1, waiting on the
  438-module build) and geometric connectedness (gap 3).
* Gap 2, `RealizesWeierstrass`, is now proved below.

`stalkTrace_symR1_fvpOf` combines `exists_stalkTrace_symR1` (M5) with part B. It identifies the
two `a`'s by comparing the coefficient of `X` in the two charpolys. For `c ∈ K⁵` with
`Δ(c) ≠ 0` and `[K : 𝔽_p] = n`, it gives
`tr(π_{y_c}^{n/deg y_c} | Sym¹⁰ R¹) = symTrace 10 (traceOfFrob (wc c)) (pⁿ)`.

## (C) Assembly (`Assembly.lean`)

```lean
theorem S_eq_pointSum (hℓp : ℓ ≠ p) (H : R1StalkCharpolyFibre p B ℓ) (n : ℕ) (hn : 1 ≤ n) :
    pointSum B (Wp p B) ℓ (toSpecK p B) (symR1 p B ℓ) n = (weierstrassSum p n : ℚ_[ℓ])
theorem deligneBound_of_ihara_M4b (hℓp : ℓ ≠ p) (H : R1StalkCharpolyFibre p B ℓ)
    (hI : IharaIdentity p) : RamanujanTau.tau p ^ 2 ≤ 4 * (p : ℤ) ^ 11
```

`weierstrassSum p n` is the left side of `IharaIdentity`, so it is the frozen M1 sum `S n`. The
assembly chains the following, with `d = 5` and `p^{3n} = p^{(5−2)n}`:

1. `nonempty_padic_ringHom_complex` gives `ι`.
2. `lefschetzPackage_Wp` is applied with `isLisse_symR1`, `mixed_symR1` and `realizable_symR1`.
3. `congrQ (pow_one p)`.
4. `congrP S_eq_pointSum`.
5. `elim_deligne` hands off to `deligne_of_package p 5`.

## M4a gap 2: `realizesWeierstrass_projOf` (`PointsCurve.lean`, `PointsRealizes.lean`)

```lean
def chartAlgHomEquiv : (W.toAffine.CoordinateRing →ₐ[k] K) ≃ {xy : K × K // (W.baseChange K).toAffine.Equation xy.1 xy.2}
def fvpChartEquiv : {g : E(K) // pt g ∈ D₊(z)} ≃ (W.toAffine.CoordinateRing →ₐ[k] K)
instance uniqueOffChart : Unique {g : E(K) // pt g ∉ D₊(z)}
def fvpEquivPoint [W.IsElliptic] : fieldValuedPoints (projectionOf W) K ≃ (W.baseChange K).toAffine.Point
theorem natCard_fieldValuedPoints_projOf [W.IsElliptic] : #E(K) = #W(K)
theorem realizesWeierstrass_projOf [Fintype k] [W.IsElliptic] (B : BigEtaleSite.{u}) :
    RealizesWeierstrass (weierstrassScheme W B) (projectionOf W) W
```

These hold for any field `K/k`, and `k` is an arbitrary field. The proof has two parts:

* **Points in the chart.** A point landing in `D₊(z)` factors through `chartZ` by
  `IsOpenImmersion.lift`. Because `Spec` is fully faithful, the factorisation is a `k`-algebra map
  out of `AdjoinRoot W.polynomial`, that is, an affine solution. Solutions are nonsingular by
  `equation_iff_nonsingular`.
* **Points off the chart.** The complement of `D₊(z)` is the image of `zeroOf` (`range_zeroOf`).
  The residue field there is `k`: the section `zeroOf` makes `k → κ(0)` surjective. So exactly
  one `K`-point lies over it.

`#W(K)` is Mathlib's `Point`, which already includes `0`.

## Gaps

**Inside M6 there are none.** The only hypothesis is `R1StalkCharpolyFibre` (M4b). Its pieces
and estimates:

* **Transport `charpoly(H¹(E_y)) → charpoly(stalk of R¹)`.** This is
  `higherDirectImageStalkInput_higherDirectImageShriek` plus the fibre side instances, as
  described in `IHARA_FAMILY.md`. Estimate: 1–2k lines.
* **M4a gap 1, `HasFirstBettiTwo` at `E_y`.** This is being worked on concurrently
  (`CurveH1Betti*`).
* **M4a gap 3, geometric connectedness at `E_y`.** Estimate: 200–500 lines.
* **M4a gap 2, `RealizesWeierstrass` at `E_y`.** Closed: `realizesWeierstrass_projOf` applies to
  `W = fibreCurve p y` over `κ(y)`.

## Build and audit

`nice -n 10 lake build RamanujanWeil.Ihara.PointsAxioms` exited with status 0 on 2026-11-08. It
builds IharaStatement, PointsCount, PointsBase, PointsExtension, PointsFibre, Assembly,
PointsCurve and PointsRealizes, and no extra Stacks modules were needed. All 20 audited names
print `[propext, Classical.choice, Quot.sound]`; `powSum_eq_frobPowerSum` prints no axioms. The
audited names include `S_eq_pointSum`, `deligneBound_of_ihara_M4b`, `realizesWeierstrass_projOf`,
`fvpEquivPoint` and `finsum_closedPoints_eq_sum`.

The Weil-closure files take about 3–7 min each, almost all of it import loading. Each runs as a
single `lean` process with a physical footprint of about 1–5 GB.

Line counts:

| File | Lines |
|---|---|
| IharaStatement | 47 |
| PointsCount | 108 |
| PointsBase | 219 |
| PointsExtension | 77 |
| PointsFibre | 176 |
| Assembly | 71 |
| PointsCurve | 290 |
| PointsRealizes | 32 |
| PointsAxioms | 28 |
| **Total** | **1048** |
