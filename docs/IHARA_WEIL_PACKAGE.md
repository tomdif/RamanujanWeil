# M2: Weil II + trace formula packaged as a `LefschetzPackage`

Status 2026-11-08. Milestone M2 of `docs/REALIZATION_PLAN.md`, §5.

Files (namespace `RamanujanWeil.Ihara`):

| File | Imports | Content |
|---|---|---|
| `RamanujanWeil/Ihara/WeilPackageCore.lean` | Mathlib only | frozen `structure LefschetzPackage`, `congrP`, `congrQ`, `elim_deligne` (hand-off to M1) |
| `RamanujanWeil/Ihara/WeilPackageTrace.lean` | Core + Stacks `LAdicTraceFormulaFinal`, `LFunctionTraceCriterion`, `CohomologicalInterpretation` | `pointSum`, Lefschetz identity for every power of Frobenius |
| `RamanujanWeil/Ihara/WeilPackage.lean` | Trace + Stacks Weil II assembly (Laumon inputs) + Nagata | unconditional Weil II lemma, `lefschetzPackageOfLissePure`, headline theorems |
| `RamanujanWeil/Ihara/WeilPackageAxioms.lean` | WeilPackage | `#print axioms` audit |

No `sorry`, `admit`, `native_decide` or `axiom`. Nothing is assumed beyond what is stated below:
**there is no gap hypothesis in M2.** The trace formula over all `𝔽_{qⁿ}` did not have to be
assumed. It comes from Tag 03V0 by log-derivative.

## Frozen interface

```lean
structure LefschetzPackage (K : Type*) [Field K] (ι : K →+* ℂ) (Q : ℕ) (w : ℤ) (d : ℕ)
    (P : ℕ → K) where
  rank : Fin (2 * d + 1) → ℕ
  frob : ∀ i, Matrix (Fin (rank i)) (Fin (rank i)) K
  weight_le : ∀ (i : Fin (2 * d + 1)) (z : ℂ), ((frob i).charpoly.map ι).IsRoot z →
    ‖z‖ ≤ (Q : ℝ) ^ (((w : ℝ) + (i : ℕ)) / 2)
  trace_eq : ∀ n : ℕ, 1 ≤ n →
    ∑ i : Fin (2 * d + 1), (-1 : K) ^ (i : ℕ) * (frob i ^ n).trace = P n
```

The cohomology is stored as matrices, not as types. This keeps the structure universe-clean,
because Stacks' `Hⁱ_c` lives in a large universe while M1 wants `V : Fin (2d+1) → Type`.
`L.V i := Fin (L.rank i) → K` and `L.F i := Matrix.toLin' (L.frob i)` recover the
endomorphism form. The characteristic polynomial and the traces of powers are unchanged
(`charpoly_F`, `trace_F_pow`).

Adapters:

* `LefschetzPackage.congrP (h : ∀ n, 1 ≤ n → P n = P' n) : LefschetzPackage K ι Q w d P'`
  rewrites the point side (M6 uses this).
* `LefschetzPackage.congrQ (h : Q = Q')`, e.g. for `p ^ 1 = p`.
* **Hand-off to M1:**
  ```lean
  theorem LefschetzPackage.elim_deligne {K : Type} [Field K] {ι : K →+* ℂ} {p d : ℕ}
      {S : ℕ → ℤ} (L : LefschetzPackage K ι p 10 d (fun n => (S n : K))) {C : Prop}
      (h : ∀ (V : Fin (2 * d + 1) → Type) [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
        [∀ i, FiniteDimensional K (V i)] (F : ∀ i, Module.End K (V i)),
        (∀ i z, ((F i).charpoly.map ι).IsRoot z → ‖z‖ ≤ (p : ℝ) ^ (((10 : ℝ) + (i : ℕ)) / 2)) →
        (∀ n : ℕ, 1 ≤ n → ∑ i : Fin (2 * d + 1),
            (-1 : K) ^ (i : ℕ) * LinearMap.trace K (V i) (F i ^ n) = (S n : K)) → C) : C
  ```
  Usage: `L.elim_deligne fun V _ _ _ F hw htr => deligne_of_package p d hd K ι V F hw S htr hS`.
  This call was typechecked against a verbatim copy of the `deligne_of_package` binder list,
  passed in as a hypothesis (scratch check, see below).

## Headline statements (`WeilPackage.lean`)

Standing context: the same as Stacks / `scratch/ProbeWeilII.lean`. That is `B : BigEtaleSite.{u}`,
the three site instances, `X : B.Scheme` with `[IsNoetherian X.1]`, `k` a finite field
(`Fintype`), `f : X.1 ⟶ Spec k` with `[LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f]`,
`ℓ` prime.

```lean
theorem satisfiesWeightBound (kbar) [IsAlgClosure k kbar] (p q) [Fact p.Prime] [CharP k p]
    (hcard : Fintype.card k = p ^ q) (hℓ : ℓ ≠ p) (ι : ℚ_[ℓ] →+* ℂ) :
    LAdicSheaf.SatisfiesWeightBound B ℓ kbar p q hcard ι X f      -- Weil II 3.3.1, unconditional

theorem alternating_trace_pow_eq_pointSum (j : CompactificationOf (Over.mk f)) kbar p q hcard
    (hℓp : ℓ ≠ p) (d) (hdim : topologicalKrullDim X.1 ≤ d) (F) {n} (hn : n ≠ 0) :
    ∑ᶠ i : ℤ, (if Even i then 1 else -1) *
      LinearMap.trace ℚ_[ℓ] (Hⁱ_c) ((Frobᵢ).hom ^ n) = pointSum B X ℓ f F n

noncomputable def lefschetzPackageOfLissePure (j) kbar p q hcard (hℓp : ℓ ≠ p)
    (ι : ℚ_[ℓ] →+* ℂ) (d : ℕ) (hdim : topologicalKrullDim X.1 ≤ d)
    (F : LAdicSheaf B X ℓ) (w : ℤ) (hF : F.IsLisse)
    (hmix : LAdicSheaf.IsPointwiseMixedOfWeightLE B X ℓ f F (p ^ q) ι w)
    (hreal : LAdicSheaf.IsIotaRealizable B X ℓ f F ι) :
    LefschetzPackage ℚ_[ℓ] ι (p ^ q) w d (pointSum B X ℓ f F)

theorem lefschetzPackage_of_lisse_pure  ... : Nonempty (LefschetzPackage ℚ_[ℓ] ι (p ^ q) w d (pointSum B X ℓ f F))
theorem lefschetzPackage_of_lisse_pure' ...   -- same, with j from Nagata (IsCofiltered.nonempty), kbar := AlgebraicClosure k
```

In the package, `rank i = finrank Hⁱ_c` and `frob i` is the matrix of
`rationalGeometricCompactlySupportedFrobenius … ((i : ℕ) : ℤ)` in `Module.finBasis`, where
`Hⁱ_c = rationalGeometricCompactlySupportedCohomology B X ℓ f j kbar F i`.

### How each field is proved

* **Finite-dimensionality, and vanishing outside `0 ≤ i ≤ 2·dim X`:** `LAdicSheaf.traceFormula`
  (Tag 03V2), parts 1 and 2. The dimension `d'` it returns satisfies `d' ≤ d` because of `hdim`.
* **Trace identity for every n ≥ 1:** take the `Tⁿ` coefficient of the log-derivative of both
  sides of `LAdicSheaf.rationalLFunction_eq_gradedCharSeries_compactSupportFrobenius` (Tag 03V0).
  On the left, `FrobeniusMatrices.coeff_logDerivative_lFunction` gives a Finset sum, which is
  turned into the finsum `pointSum`. On the right we use `coeff_logDerivative_gradedCharSeries'`.
  This is a local re-proof of Stacks' `coeff_logDerivative_gradedCharSeries`, because
  `Trace/AdicCompactSupportCharSeries.olean` is not in the prebuilt `.lake` and we must not
  rebuild dependencies. The proof uses only the public API of `LFunctionTraceCriterion` and
  `CohomologicalInterpretation`. The ℤ-indexed finsum is then reindexed to `Fin (2d+1)`
  (`finsum_int_eq_sum_fin`), and `if Even i then 1 else -1` becomes `(-1)^i`.
* **Weights:** `satisfiesWeightBound` gives `IsCharpolyNormMixedOfWeightLE (p^q) ι (w+i)`, that is
  `∃ w' ≤ w + i, ‖z‖ = (p^q)^(w'/2)`. Since `p^q ≥ 1`, this implies `‖z‖ ≤ (p^q)^((w+i)/2)`.

## Conventions (checked against Stacks)

* **Weights on `Hⁱ_c` are `≤ w + i`** (`SatisfiesWeightBound`, Weil II 3.3.1), for the
  geometric Frobenius `rationalGeometricCompactlySupportedFrobenius` and `Q = #k = p^q`.
* **"Pure / mixed of weight ≤ w" is per a single fixed `ι`**, and it is an upper bound:
  `IsPointwiseMixedOfWeightLE B X ℓ f F Q ι w` means that for every closed `y` and every root `z` of
  `charpoly(π_y | F_ȳ ⊗ ℚ_ℓ)` mapped along `ι`, there is an integer `w' ≤ w` with
  `‖z‖ = Q^(deg y · w'/2)`. Realizability (`IsIotaRealizable`) is also relative to one `ι`.
  M1 only needs one `ι`. For an integer-charpoly sheaf such as Sym¹⁰ (M5), both properties hold
  for every `ι`. An `ι` exists by `RamanujanWeil.nonempty_padic_ringHom_complex` (`Bridge.lean`).
  That lemma is not imported here, to keep the Weil closure out of these files.
* `deligne_of_package` wants `‖z‖ ≤ p^((10+i)/2)`. Take `w = 10`, `q = 1` (base `𝔽_p`), then
  `congrQ (pow_one p)` and `congrP` to the integer sum `S`.

## Exact form of the point side

```lean
noncomputable def pointSum (F : LAdicSheaf B X ℓ) (n : ℕ) : ℚ_[ℓ] :=
  ∑ᶠ (x : closedPoints X.1) (_ : residueDegree f x.1 ∣ n),
    (residueDegree f x.1 : ℚ_[ℓ]) *
      LinearMap.trace ℚ_[ℓ] _
        (LAdicSheaf.rationalStalkFrobenius B X ℓ F x.1 (finite_residueField f x.1 x.2) ^
          (n / residueDegree f x.1))
```

The sum runs over **closed points** `x` with `deg x = [κ(x):k]` dividing `n`, each weighted by
`deg x`. Each term is the trace of the `(n/deg x)`-th power of the geometric Frobenius of `κ(x)`
on the rational stalk at `geometricPointAt X x`. This is the closed-point form. The
`X(𝔽_{qⁿ})` form, in which each closed point of degree `e ∣ n` contributes `e` rational points,
is **not** proved here. That translation is M6's job.

## What M3–M6 must supply to get `LefschetzPackage ℚ_[ℓ] ι p 10 5 (fun n => (S n : ℚ_[ℓ]))`

With `X = W_p = Spec 𝔽_p[a₁..a₆][1/Δ]`, `k = 𝔽_p` (so `q = 1`), `F = Sym¹⁰ R¹π_*ℚ_ℓ`:

1. **M3:** `W_p` as a `B.Scheme` with `IsNoetherian`, `f` locally of finite type, quasi-compact
   and separated, and `topologicalKrullDim W_p.1 ≤ 5`. Also `R¹` with `IsLisse`.
2. **M5:** `F : LAdicSheaf B W_p ℓ` with `F.IsLisse`,
   `IsPointwiseMixedOfWeightLE B W_p ℓ f F (p ^ 1) ι 10` and `IsIotaRealizable B W_p ℓ f F ι`,
   together with the stalk traces
   `tr(π_x^m | F_x̄) = symTrace 10 (α_x^m + β_x^m) (p^{deg x · m})`.
3. `ℓ ≠ p`, `ι : ℚ_[ℓ] →+* ℂ`, `hcard : Fintype.card (ZMod p) = p ^ 1`, `[CharP (ZMod p) p]`.
4. **M6:** `∀ n ≥ 1, pointSum B W_p ℓ f F n = (S n : ℚ_[ℓ])`, with
   `S n = Σ_{c ∈ 𝔽_{pⁿ}⁵, Δ≠0} symTrace 10 (traceOfFrob (wc c)) (pⁿ)`.

Then `(lefschetzPackageOfLissePure … 5 hdim F 10 hF hmix hreal).congrQ (pow_one p) |>.congrP hM6`
followed by `.elim_deligne` (with `IharaIdentity` as `hS`) gives M1's conclusion.

## Build and audit

`nice -n 10 lake build RamanujanWeil.Ihara.WeilPackageAxioms` (it builds Core → Trace → Package).
Memory: the physical footprint of a single `lean` process was about 1.3 GB. RSS reads 11–12 GB,
but almost all of that is mmapped `.olean` pages. A single file takes about 3–4 minutes, mostly
spent loading imports.

`lake build RamanujanWeil.Ihara.WeilPackageAxioms` finished with exit 0 (2026-11-08). Every one
of the following reported `[propext, Classical.choice, Quot.sound]`:
`LefschetzPackage.elim_deligne`, `LefschetzPackage.congrP`,
`coeff_logDerivative_rationalLFunction`, `alternating_trace_pow_eq_pointSum`,
`satisfiesWeightBound`, `lefschetzPackageOfLissePure`, `lefschetzPackage_of_lisse_pure`,
`lefschetzPackage_of_lisse_pure'`.

M1 compatibility check: a throwaway file applied
`L.elim_deligne fun V _ _ _ F hw htr => M1 p d hd K ι V F hw S htr hS`, where `M1` was a
hypothesis holding a verbatim copy of the binder list of `deligne_of_package`. It compiled with
exit 0.

Line count: Core 117, Trace 173, Package 155, Axioms 13, for 458 lines in total.
