# M4a: Frobenius on `H¹` of a genus-one curve over `𝔽_q`

Status 2026-11-08. Fibrewise half of milestone M4 of `docs/REALIZATION_PLAN.md` §5.

Files (namespace `RamanujanWeil.Ihara`):

| File | Imports | Content |
|---|---|---|
| `RamanujanWeil/Ihara/CurveH1Core.lean` | Mathlib only | `frobPowerSum`, the 1- and 2-dimensional linear algebra, the exclusion of `det = −q`, Hasse bound, Lagrange for `W(𝔽_{q³}) ≤ W(𝔽_{q⁶})` |
| `RamanujanWeil/Ihara/CurveH1.lean` | Core + M2 (`WeilPackageTrace`) + Bridge + Weil (`DeligneWeilConjecture`, `ConstantDegreeZeroCohomology`, `RepresentationSheafTrivialConstant`, `ConstantSystemLocalFactor`, `RationalPoincareDuality`) | `H⁰`, `H²`, trace formula for every `n`, purity, the main theorems for an abstract curve and in Weierstrass form |
| `RamanujanWeil/Ihara/CurveH1Weierstrass.lean` | CurveH1 + Stacks Weierstrass family | Stacks' plane cubic `projOf W` as a `B`-scheme, proper, smooth of rel. dim. 1, pointed; `charpoly_weierstrassH1` |
| `RamanujanWeil/Ihara/CurveH1Axioms.lean` | Weierstrass | `#print axioms` audit |

No `sorry`, `admit`, `native_decide` or `axiom`. See "Gaps" for the three named hypotheses.

## Frozen interface

Standing context of `CurveH1.lean`: `B : BigEtaleSite.{u}`, `X : B.Scheme`, `k : Type u` a finite
field (`[Field k] [Fintype k]`, `q = Fintype.card k`), `f : X.1 ⟶ Spec (.of k)` with
`[IsProper f] [Smooth f] [SmoothOfRelativeDimension 1 f]`, `ℓ` prime with `[Fact (ℓ ≠ ringChar k)]`,
and geometric connectedness
`[ConnectedSpace ↥(pullback (Over.mk f).hom (specAlgebraMap k (AlgebraicClosure k)))]`
(`X` itself is then connected: `connectedSpace_of_connectedSpace_pullback`). Cohomology is Axiom's
`Weil.rationalCohomology B X f ℓ ν` with the geometric Frobenius `Weil.rationalFrobenius B X f ℓ ν`.
`hpt : ∃ s : Spec (.of k) ⟶ X.1, s ≫ f = 𝟙 _` is a `k`-point.

```lean
-- #X(k_n), Weil's official count (0 at n = 0)
noncomputable def curvePointCount (n : ℕ) : ℕ :=
  if h : n = 0 then 0 else haveI : NeZero n := ⟨h⟩; pointCountOfDegree f n

def frobPowerSum (a q : ℤ) : ℕ → ℤ        -- s_n = αⁿ + βⁿ, roots of X² − aX + q
  | 0 => 2 | 1 => a | n + 2 => a * frobPowerSum a q (n + 1) - q * frobPowerSum a q n

-- named hypotheses (Props, not axioms)
def HasFirstBettiTwo : Prop := finrank ℚ_[ℓ] (Weil.rationalCohomology B X f ℓ 1) = 2
def RealizesWeierstrass (W : WeierstrassCurve k) : Prop :=
  ∀ n : ℕ, ∀ hn : 1 ≤ n, haveI : NeZero n := ⟨by omega⟩
    curvePointCount X f n =
      Nat.card (W.baseChange (FiniteField.Extension k (ringChar k) n)).toAffine.Point

theorem rationalFrobenius_zero_eq_id : Weil.rationalFrobenius B X f ℓ 0 = LinearMap.id
theorem finrank_rationalCohomology_zero : finrank ℚ_[ℓ] (Weil.rationalCohomology B X f ℓ 0) = 1
theorem charpoly_rationalFrobenius_two (hpt) :
    (Weil.rationalFrobenius B X f ℓ 2).charpoly = Polynomial.X - C (Fintype.card k : ℚ_[ℓ])
theorem curvePointCount_eq_alternating (n) (hn : n ≠ 0) :
    (curvePointCount X f n : ℚ_[ℓ]) = tr(F₀ⁿ) - tr(F₁ⁿ) + tr(F₂ⁿ)
theorem trace_rationalFrobenius_one_pow (hpt) (n) (hn : 1 ≤ n) :
    LinearMap.trace ℚ_[ℓ] _ (Weil.rationalFrobenius B X f ℓ 1 ^ n) =
      (Fintype.card k : ℚ_[ℓ]) ^ n + 1 - curvePointCount X f n
theorem norm_sq_eq_card_of_isRoot (ι : ℚ_[ℓ] →+* ℂ) (z : ℂ)
    (hz : ((Weil.rationalFrobenius B X f ℓ 1).charpoly.map ι).IsRoot z) : ‖z‖ ^ 2 = Fintype.card k

-- abstract curve form
theorem charpoly_rationalFrobenius_one (hpt) (hb1 : finrank … H¹ = 2)
    (hdvd : curvePointCount X f 3 ∣ curvePointCount X f 6) :
    (Weil.rationalFrobenius B X f ℓ 1).charpoly =
      Polynomial.X ^ 2 - C (((Fintype.card k : ℤ) + 1 - curvePointCount X f 1 : ℤ) : ℚ_[ℓ]) *
        Polynomial.X + C (Fintype.card k : ℚ_[ℓ])
theorem trace_rationalFrobenius_one_pow_eq_frobPowerSum (hpt) (hb1) (hdvd) (n) :
    tr(F₁ⁿ) = frobPowerSum (q + 1 − #X(k)) q n
theorem curvePointCount_eq_sub_frobPowerSum (hpt) (hb1) (hdvd) (n) (hn : 1 ≤ n) :
    (curvePointCount X f n : ℤ) = q ^ n + 1 − frobPowerSum (q + 1 − #X(k)) q n
theorem sq_le_four_mul_card (hpt) (hb1) : (q + 1 − #X(k))² ≤ 4q        -- Hasse, bonus

-- Weierstrass form (M4a headline)
theorem charpoly_rationalFrobenius_one_of_weierstrass (hpt) (W : WeierstrassCurve k)
    (hb1 : HasFirstBettiTwo X f ℓ) (hW : RealizesWeierstrass X f W) :
    (Weil.rationalFrobenius B X f ℓ 1).charpoly =
      Polynomial.X ^ 2 - C (((Fintype.card k : ℤ) + 1 - Nat.card W.toAffine.Point : ℤ) : ℚ_[ℓ]) *
        Polynomial.X + C (Fintype.card k : ℚ_[ℓ])
theorem natCard_point_extension_eq_of_weierstrass (hpt) W hb1 hW (n) (hn : 1 ≤ n) :
    (#W(k_n) : ℤ) = q ^ n + 1 − frobPowerSum a q n  ∧  tr(F₁ⁿ) = frobPowerSum a q n
      -- a = q + 1 − Nat.card W.toAffine.Point, k_n = FiniteField.Extension k (ringChar k) n
theorem sq_le_four_mul_card_of_weierstrass (hpt) W hb1 hW : a ^ 2 ≤ 4 * q
```

`frobPowerSum_eq_add_pow : α + β = a → α β = q → (frobPowerSum a q n : R) = αⁿ + βⁿ` (any
commutative ring) turns `s_n` into `αⁿ + βⁿ`.

`CurveH1Weierstrass.lean` (Stacks' plane cubic, namespace `RamanujanWeil.Ihara`, any
`W : WeierstrassCurve k` with `[W.IsElliptic]`):

```lean
theorem contains_projOf (B : BigEtaleSite.{u}) : B.Contains (projOf W)
noncomputable abbrev weierstrassScheme (B) : B.Scheme := B.obj (projOf W) (contains_projOf W B)
instance : SmoothOfRelativeDimension 1 (projectionOf W)     -- from Δ a unit
theorem exists_section_projectionOf : ∃ s, s ≫ projectionOf W = 𝟙 _   -- (0 : 1 : 0)
theorem charpoly_weierstrassH1 (B) (ℓ) [Fact ℓ.Prime] [Fact (ℓ ≠ ringChar k)]
    [ConnectedSpace ↥(pullback (Over.mk (projectionOf W)).hom (specAlgebraMap k (AlgebraicClosure k)))]
    (hb1 : HasFirstBettiTwo (weierstrassScheme W B) (projectionOf W) ℓ)
    (hW : RealizesWeierstrass (weierstrassScheme W B) (projectionOf W) W) :
    (Weil.rationalFrobenius B (weierstrassScheme W B) (projectionOf W) ℓ 1).charpoly =
      X ^ 2 − C (q + 1 − Nat.card W.toAffine.Point) * X + C q
```

Conventions: geometric Frobenius (Axiom's), so the eigenvalues on `H²` are `q` and on `H⁰` are `1`.
`#E(k)` is Mathlib's `Nat.card W.toAffine.Point`, which already contains the point at infinity
(same convention as `WeierstrassCurve.localPolynomial` and as `traceOfFrob` of the plan).

## How it is proved

* **`H⁰`**: Weil's `ConstantDegreeZeroCohomology` (we built that module and its two Stacks
  dependencies `Duality.LAdicTowerLimit`, `Duality.LAdicTowerTrace`; three files, ~2 min).
* **`H²`**: `rationalFrobenius_top_representationSheaf_one_of_rationalPoint` (Poincaré duality at
  the rational point, prebuilt) for the sheaf `ℱ_𝟏` of the trivial representation; the hypothesis
  "Frobenius = id on `H⁰(ℱ_𝟏)`" and the conclusion are moved between `ℱ_𝟏` and the constant sheaf
  through `charpoly_rationalGeometricCompactlySupportedFrobenius_representationSheaf_one_eq` and
  Cayley–Hamilton on one-dimensional spaces (`eq_smul_id_of_charpoly_eq`).
* **Trace formula, all `n`**: M2's `alternating_trace_pow_eq_pointSum` (Tag 03V0 +
  log-derivative) for the constant sheaf, with `dim X ≤ 1`
  (`topologicalKrullDim_eq_of_smoothOfRelativeDimension_over_field`), the stalk Frobenius of the
  constant sheaf being the identity on a line (`Weil.rationalStalkEnd_constantSystem`), and
  `pointSum = #X(k_n)` via Stacks' `natCard_fieldValuedPoints`.
* **Purity**: `Weil.satisfiesWeilEstimate` (Deligne) in degree 1: `‖z‖² = q`.
* **`det = q` without cup-product alternation** (`charpoly_eq_of_pure_of_traces`, Mathlib only).
  With `dim H¹ = 2`, `charpoly = X² − tX + c`; `t = q + 1 − N₁ ∈ ℤ`, and `tr F² = t² − 2c` makes
  `c ∈ ℚ`; purity gives `|c| = q`, so `c = ±q`. If `c = −q`, the roots are `z, −z̄`
  (`z z̄ = q = −z z₂`), so `t = z − z̄` is purely imaginary and real, `t = 0`; then
  `tr F³ = 0`, `tr F⁶ = 2q³`, i.e. `N₃ = q³ + 1`, `N₆ = (q³ − 1)²`. Since `N₃ ∣ N₆`
  and `(q³ − 1)² = (q³ + 1)(q³ − 3) + 4`, `q³ + 1 ∣ 4`, impossible for `q ≥ 2`.
  (Checked: the plan's `n = 1, 2` version `(q + 1) ∣ (q − 1)²` fails to exclude `q = 3`, since
  `4 ∣ 4`; `n = 3, 6` works for every `q ≥ 2`.)
* **`N₃ ∣ N₆` for a Weierstrass curve**: Lagrange in Mathlib's group `W(𝔽_{q⁶})` for the injective
  `Point.map` along a `k`-embedding `𝔽_{q³} → 𝔽_{q⁶}` (`natCard_point_extension_dvd`).

So the alternation of the cup product is **not needed**; the duality/alternation tree
(`DeligneFunctionalEquation`, 31 unbuilt files) is not used.

## Gaps (named hypotheses) and estimates

1. **`HasFirstBettiTwo`** (`dim H¹(E_k̄, ℚ_ℓ) = 2`). The math is in Stacks:
   `Stacks.EtaleCohomology.LAdicSheaf.finrank_rationalGeometricCompactlySupportedCohomology_constant_one`
   (`Trace/ConstantCurveH1Trace.lean`: `dim = 2 · genus X_k̄`, Tag 0C1Z) plus
   `genus_projectionOf = 1` (`Stacks/WeierstrassFamilyFibres.lean`, prebuilt) and invariance of the
   genus under the base-change isomorphism `E_k̄ ≅ projOf (W.baseChange k̄)`. **Blocker is build
   size, not mathematics**: `ConstantCurveH1Trace` has a closure of **438 unbuilt** Stacks files
   (Jacobian / abelian variety torsion / Künneth). Estimate once built: 300–600 lines (base change
   of `Proj` along `k → k̄`, matching the hypotheses of the Stacks theorem). Building: several CPU
   hours single-process.
2. **`RealizesWeierstrass`** (`#E(k_n) = #W(k_n)` with Mathlib's `Point`). Elementary but not
   in any library: `k`-morphisms `Spec k_n ⟶ projOf W` ↔ affine solutions in the chart `D₊(z)`
   (`chartZ`, coordinate ring = Mathlib's `CoordinateRing`) plus the zero section
   (`WeierstrassCubicCharts`: complement of the zero section is `D₊(z)`, the charts cover);
   nonsingularity from `Δ` a unit. Estimate **600–1200 lines**, medium risk. This is also the
   fibre half of M6.
3. **Geometric connectedness** `ConnectedSpace (E ×_k k̄)`: from `E_k̄ ≅ projOf (W.baseChange k̄)`
   and `H⁰(O) = k̄` (`finrank_structureSheafCohomology_projectionOf_zero`, prebuilt) or
   irreducibility of the cubic. Estimate 200–500 lines (shares the base-change isomorphism with 1).

Not needed: cup-product alternation, Weil pairing, functional equation.

## Build and audit

`nice -n 10 lake build RamanujanWeil.Ihara.CurveH1Axioms` (exit 0, 2026-11-08); it builds Core →
CurveH1 → CurveH1Weierstrass. Single `lean` process; CurveH1 takes ~3–4 min, mostly imports.
Every audited declaration (24, listed in `CurveH1Axioms.lean`) reports
`[propext, Classical.choice, Quot.sound]` (`frobPowerSum_eq_add_pow`: `[propext, Quot.sound]`).

Line counts: Core 467, CurveH1 456, CurveH1Weierstrass 73, Axioms 32 (1028 total).
