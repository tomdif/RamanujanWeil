# Scouting report: discharging the realization hypothesis behind Deligne's bound τ(p)² ≤ 4p¹¹

Status 2026-11-08. This is a scouting report. Nothing below is formalized beyond two probe files
(`scratch/ProbeWeilII.lean`, which compiles axiom-clean, and `scratch/ProbeInterfaces.lean`, which
checks statements and contains one `sorry` placeholder). The numerical identities were checked
with PARI/gp and, independently, with plain Python (`scripts/scout/`).

## TL;DR

* **The geometric half is much cheaper than expected.** AxiomMath/Stacks already proves, with
  all inputs discharged, **Weil II for lisse ℓ-adic sheaves on any separated finite-type
  `X/𝔽_q`**: the weights on `Hⁱ_c` are `≤ w + i`. The probe
  `scratch/ProbeWeilII.lean :: Stacks.EtaleCohomology.probe_satisfiesWeightBound` compiles with
  `[propext, Classical.choice, Quot.sound]`. Stacks also proves the sheaf L-function/trace formula
  (Tag 03V0), the stalks of `Rʳg_!` at closed points (proper base change with Frobenius),
  smooth-proper local constancy (Tag 0GLI), lisse ⇒ representation, tensor products of lisse
  sheaves, and **the universal Weierstrass family over `Spec ℤ[a₁..a₆][1/Δ]`, shown proper and
  smooth of relative dimension 1 with genus-1 fibres.**
* **Recommended route (R3, "Ihara route").** Take `F = Sym¹⁰ R¹π_*ℚ_ℓ` on the 5-dimensional base
  `W_{𝔽_p} = Spec 𝔽_p[a₁..a₆][1/Δ]`. Only the weight *upper bound* is needed: no purity of
  `H¹_!`, no Poincaré duality on the base, no compactification, no Kuga–Sato, no Hecke
  correspondences. The single arithmetic input is the **level-1 Ihara–Birch identity**
  (numerically verified, exact):

  ```
  Σ_{c ∈ 𝔽_q⁵, Δ(c) ≠ 0}  h₁₀(a(E_c), q)  =  q³ (q − 1) (−1 − (αⁿ + βⁿ)),   q = pⁿ, every n ≥ 1, every p,
  ```

  where `h₁₀(a,q) = Σ_j (−q)^j C(10−j,j) a^{10−2j}` (the trace of Sym¹⁰), `a(E) = q + 1 − #E(𝔽_q)`,
  and `α, β` are the roots of `X² − τ(p)X + p¹¹`.
* **The bottleneck is arithmetic, and it is large.** Proving the identity for all `q = pⁿ` means
  formalizing (A2) the Eichler–Selberg trace formula for `S₁₂(SL₂ℤ)` and (A3)
  Deuring–Waterhouse–Schoof (counting elliptic curves over `𝔽_q` with a given trace via Hurwitz
  class numbers). Mathlib has neither Hecke operators, binary-form class numbers, isogenies nor
  endomorphism rings. **Each of A2 and A3 is a multi-month project, and A3 may take a year or
  more.** Every route has to bridge the q-expansion of Δ and Frobenius traces somewhere. In this
  route that bridge is A2+A3; in the Kuga–Sato route it is the Eichler–Shimura congruence
  relation plus a comparison theorem, which is strictly larger.
* **Recommended first milestone: M1** (the Mathlib-only endgame, ~1–1.5k lines, low risk). It is
  followed by the geometric milestones M2–M6 (~10–19k lines in total). Together they replace
  `TauRealization` with the elementary, numerically checkable hypothesis `IharaIdentity p`.
  This is a solid intermediate result whatever happens to A2/A3.

---

## 1. Inventory (exact names; `.lake/packages/{Stacks,Weil,mathlib}`)

### 1a. Axiom/Stacks: weights, trace formula, direct images, duality

All in namespace `Stacks.EtaleCohomology`, under
`StacksFrontier/AlgebraicGeometry/EtaleCohomology/` (abbreviated `EC/`).

| What | Lean name | File | Status |
|---|---|---|---|
| Tag 03VH (Weil II) for `ℱ_ρ` with ρ satisfying Deligne's conclusions: `Hⁱ_c` weights `≤ i`; `= i` for smooth proper `X` | `LAdicSheaf.weightBound` | `EC/Trace/WeilIIWeightBound.lean` | proved. The task's guess "LAdicSheaf.weightBound" is this; ρ must be weight 0 with companions (`HasDeligneConclusions`, `EC/Trace/DeligneConjectureConclusions.lean`), so it is **not** the form we want |
| **Weil II 3.3.1 for any lisse sheaf**: `F` lisse, pointwise ι-mixed `≤ w`, ι-realizable ⇒ every root of charpoly of Frobenius on `Hⁱ_c(X_k̄, F)` has weight `≤ w + i`, for every `X` separated of finite type over `𝔽_q` | def `LAdicSheaf.SatisfiesWeightBound` (`EC/Trace/WeilIIDevissage.lean:90`); theorem `LAdicSheaf.satisfiesWeightBound_of_laumonInputs` (`EC/Trace/WeilIIAssembly.lean:148`) | | **proved unconditionally**: the three inputs are discharged inside `weightBound_of_absIrr'` (`EC/Trace/WeilIIFinalAssemblyAbsIrrCharNe.lean`). Our probe re-assembles it: `scratch/ProbeWeilII.lean :: probe_satisfiesWeightBound`, axioms `[propext, Classical.choice, Quot.sound]` |
| Pointwise mixedness | `LAdicSheaf.IsPointwiseMixedOfWeightLE` | `EC/Trace/PointwiseMixedSheaf.lean:67` | def |
| Weight predicate on an endomorphism | `IsCharpolyNormMixedOfWeightLE q ι i f := ∀ z root, ∃ w ≤ i, ‖z‖ = q^{w/2}` | `EC/Trace/CharpolyRootsExact.lean:186` | def |
| ι-realizability | `LAdicSheaf.IsIotaRealizable` | `EC/Trace/IotaRealizableSheaf.lean:109` | def (holds for integer charpolys) |
| **Trace formula for any ℚ_ℓ-sheaf** (Tag 03V2): finiteness, `0 ≤ i ≤ 2 dim X`, `Σ_{x∈X(k)} tr(π_x|F_x̄) = Σ(−1)ⁱ tr(π|Hⁱ_c)` | `LAdicSheaf.traceFormula` | `EC/Trace/LAdicTraceFormulaFinal.lean:86` | proved |
| **L-function of a ℚ_ℓ-sheaf** (Tag 03V0): `L(X,F) = ∏ᵢ det(1 − πT | Hⁱ_c)^{(−1)^{i+1}}` | `LAdicSheaf.rationalLFunction_eq_gradedCharSeries_compactSupportFrobenius`; def `LAdicSheaf.rationalLFunction` (Euler product, `EC/Trace/LFunctionRationalSheaf.lean:149`) | same file :135 | proved. This gives the trace identity for **all** Frobenius powers on one fixed set of cohomology spaces |
| `Rʳg_!` as an ℓ-adic sheaf | `LAdicSheaf.higherDirectImageShriek` | `EC/Trace/LAdicHigherDirectImageShriek.lean:170` | def |
| Stalk of `Rʳg_!G` at a closed point `w` = Frobenius of `κ(w)` on `Hʳ_c(U_w, G)` (charpoly) | `LAdicSheaf.higherDirectImageStalkInput_higherDirectImageShriek` (inputs discharged in `WeilIIAssembly.lean:123`) | `EC/Trace/LAdicHigherDirectImageShriekStalk.lean:380` | proved |
| `Rʳg_!G` pointwise mixed `≤ w + r` (fibres of dim ≤ 1) | `LAdicSheaf.isPointwiseMixedOfWeightLE_higherDirectImage` | `EC/Trace/WeilIIDimensionStep.lean:79` | proved, given the dim-1 weight bound (available) |
| Lisse locus of `Rʳg_!` (a nonempty open) | `LAdicSheaf.higherDirectImageLisseLocusInput_higherDirectImageShriek` | WeilIIAssembly | proved. Lisse on all of `W` needs the smooth proper case (next row) |
| Smooth proper ⇒ `Rⁱf_*` (torsion, finite type) locally constant (Tag 0GLI) | `isFiniteTypeLocallyConstantModuleSheaf_rightDerived_of_smooth_of_isProper` | `EC/SmoothProperHigherDirectImageLocallyConstant.lean:322` | proved, torsion level only. An ℓ-adic `IsLisse` wrapper is **missing** |
| Same for proper smooth curves, `ℤ/ℓ` | `isFiniteTypeLocallyConstant_rightDerivedConstantUnit_of_isUnit` | `EC/Duality/ProperCurveHigherDirectImageLisse.lean` | proved |
| Lisse ⇒ isogenous to `ℱ_ρ`, ρ continuous `π₁ → GL_r(ℚ_ℓ)` | `LAdicSheaf.exists_representationSheaf_isogeny_of_isLisse` | `EC/LAdicSheaves/LisseRepresentation.lean:492` | proved |
| `ℱ_ρ` and its stalk charpoly = charpoly ρ(Frob_y) | `LAdicSheaf.representationSheaf`, `charpoly_rationalStalkFrobenius_representationSheaf_eq` | `EC/LAdicSheaves/RepresentationSheaf.lean`, `PointwiseMixedSheaf.lean` | proved |
| Tensor products of lisse sheaves (Kronecker ρ⊗ρ'), trace multiplicative | `kroneckerRepresentation`, `trace_kroneckerRepresentation` | `EC/LAdicSheaves/RepresentationTensor.lean` | proved. **No Sym^k** |
| Poincaré duality on curves (ℤ/ℓ, lisse), Weil pairing on `H¹` equivariant with factor `c`, Frobenius on `H²` of a curve is `q` | `isDualityPerfect_unitSheaf`, `Stacks.Picard.exists_extPairing_of_comp_eq`, `constantExtRestriction_geometricFrobeniusBaseChange_two_of_curve` | `EC/Duality/CurvePoincareDuality.lean`, `CurveExtWeilPairing.lean`, `CurveTopDegreeFrobenius.lean`; also `CurveLisseDuality.lean` | proved at torsion level. This is the toolkit for `det(Frob | H¹(E)) = q` |
| Weil RH for smooth proper `X` (constant coefficients) | `Weil.satisfiesWeilEstimate` | Weil package | proved (used by `Bridge.lean`) |
| Artin comparison / Betti numbers under good reduction | `Weil/AlgebraicGeometry/ComplexPoints/*`, `EtaleCohomology/Trace/BettiNumberGoodReduction.lean` | Weil | constant coefficients only |

### 1b. Elliptic curves

* **Mathlib** (`Mathlib/AlgebraicGeometry/EllipticCurve/`): `WeierstrassCurve`, `IsElliptic`, `Δ`,
  `j`, `VariableChange`, group law on `W.toAffine.Point` (also Jacobian/Projective), division
  polynomials, `exists_variableChange_of_j_eq` (separably closed field, `IsomOfJ.lean`),
  `ModelsWithJ`, `NormalForms`, `Reduction`, `LFunction` (with `a = q + 1 − Nat.card
  W.toAffine.Point`). **Missing:** Hasse bound, Frobenius endomorphism, isogenies, dual isogeny,
  endomorphism rings, Tate modules, Weil pairing, supersingularity, Deuring, any counting of
  isomorphism classes over `𝔽_q`.
* **Stacks** (`StacksFrontier/AlgebraicGeometry/Stacks/`, namespace
  `AlgebraicGeometry.ModuliEllipticCurves`): `Weierstrass.base/total/projection/family`,
  `projOf C`, `projectionOf C`, `isProper_projectionOf` (`WeierstrassFamilyProper.lean`),
  `smoothOfRelativeDimension_projectionOf` (`WeierstrassFamilySmooth.lean:417`),
  `isElliptic_familyOf` (`WeierstrassFamilyElliptic.lean:113`, genus-1 fibres via
  `finrank_structureSheafCohomology`), S-points of the cubic (`WeierstrassCubicPoints.lean`),
  fibres (`WeierstrassFamilyFibres.lean`), coordinate changes and torsor
  (`WeierstrassCoordinateChange*.lean`), automorphisms (`WeierstrassCubicAutomorphisms.lean`),
  `𝓜₁,₁` as a groupoid-valued object with algebraicity conditions
  (`ModuliEllipticCurves*.lean`). Not yet built in our `.lake`; it is a small closure.
  `Stacks.Picard`: the Jacobian degree inputs are only partly present
  (`EC/Picard/CurveTrace.lean` takes `deg` as a hypothesis). `NumberTheory/Drinfeld/SupersingularCurve.lean`
  is one explicit curve over 𝔽₂ and is irrelevant here.
* The étale `H¹` of an elliptic curve is not identified with a Tate module anywhere, and that
  identification is not needed.

### 1c. Modular curves and moduli

Stacks has `𝓜₁,₁` (descent, key fact, smooth cover by the Weierstrass family), properness and
separation pieces (`ModuliProperness/`, `ModuliSeparation/`) and coarse moduli
(`WellNighAffineModuliSpace*`). It has **nothing** on level structures, `Y(N)`, the Legendre
family as a family, Kuga–Sato varieties, compactifications at cusps, or Hecke correspondences.
None of this is needed for R3.

### 1d. Modular forms

Mathlib has `ModularForm`, `CuspForm`, level-1 dimension formula
(`LevelOne/DimensionFormula.lean`), `Delta.lean`, `Discriminant.lean`, `DedekindEta.lean`,
Eisenstein series, Petersson, q-expansions, and Hecke's coefficient bound (`Bounds.lean`).
**Missing:** Hecke operators, Eichler–Selberg, Hurwitz class numbers, binary quadratic form
reduction theory, mock modular forms. `RamanujanWeil.Tau` has `τ` as the coefficient of the
q-expansion of `q∏(1−qⁿ)²⁴` (decidable). `~/RamanujanTau`, on a different toolchain, has Hecke
multiplicativity of τ, but R3 does not need it, because the identity is phrased with
`s_n = αⁿ+βⁿ` defined by recursion.

---

## 2. Numerics (scripts in `scripts/scout/`, outputs in `*.out`)

| Script | Identity checked | Range | Result |
|---|---|---|---|
| `ihara_level1.gp` | short Weierstrass: `Σ_{A,B∈𝔽_q, 4A³+27B²≠0} h₁₀(a,q) = (q−1)(−1 − s_n)` | `q = p`, 5 ≤ p ≤ 61; `q = p²`, p = 5,7,11,13; `q = 125` | **exact equality, all cases** |
| `ihara_level1.gp` | **full 5-parameter**: `Σ_{c∈𝔽_q⁵, Δ≠0} h₁₀(a,q) = q³(q−1)(−1 − s_n)` | q = 2, 3, 4, 5, 8, 9 (p = 2, 3 included) | **exact equality, all cases** |
| `ihara_bruteforce.py` (no PARI; naive point counts, τ from the product) | the short-Weierstrass identity at `q = p` | 5 ≤ p ≤ 59 | exact equality |
| `legendre_probe.gp` | Legendre `y² = x(x−1)(x−λ)`: `S_L(p) = Σ_{λ≠0,1} h₁₀(a_λ,p)` | odd p < 200 | `S_L(p) = −3 − 3τ(p) − a_p(g)`, where `g` is the unique newform in `S₁₂^new(Γ₀(4))` (q-coefficients `1, 0, −516, 0, −10530, …`). PARI gives `mfdim([4,12]) = 4`, new part 1, and `mfdim([2,12]) = 2` with no level-2 newforms, so `S₁₂(Γ₀(4)) = 3·[Δ] + [g]` |
| `eichler_selberg_check.gp` | Eichler–Selberg, weight 12, level 1: `Σ_{t²≤4n} h₁₀(t,n) H(4n−t²) = −2τ(n) − Σ_{dd'=n} min(d,d')¹¹` (`H(0) = −1/12`) | n ≤ 300 | exact |
| same | Deuring over prime fields: `#{(A,B): a = t} = (p−1)·H(4p−t²)/2` | 5 ≤ p ≤ 101 | exact |
| same | the same count over `𝔽_{p²}` | q = 25, 49 | **fails exactly at the supersingular traces p ∣ t**, as expected. Schoof's supersingular counts are genuinely needed for n ≥ 2 |
| `ordinary_locus_probe.gp` | `Σ_{p∤t} h₁₀(t,q) H(4q−t²) + 2s_n` | p ≤ 13, n ≤ 6 | equals `−2 + c·p^{5n}` with `c` depending on p and on the parity of n (weight 10). This is the ordinary-locus variant (§4, A3′) |

Conventions: `h_k(a,q) = Σ_j (−q)^j C(k−j,j) a^{k−2j}`, which is `tr Sym^k` of a 2×2 matrix with
trace `a` and determinant `q`. `s_n = αⁿ + βⁿ`, with `s₀ = 2`, `s₁ = τ(p)`,
`s_{n+1} = τ(p)s_n − p¹¹s_{n−1}`. In particular `s_n = τ(pⁿ) − p¹¹τ(p^{n−2})`.

So the precise level-1 statement (Ihara 1967; Birch 1968 for prime fields) is
`Σ_{E/𝔽_q} h₁₀(a_E,q)/#Aut(E) = −1 − s_n`. The constant is `−1` and the sign of τ is negative.
The negative sign is what makes the endgame work (§3).

---

## 3. Why the weight *upper bound* suffices (the endgame argument, M1)

Let `d = dim W = 5`, `F = Sym¹⁰R¹π_*ℚ_ℓ`, pointwise of weight ≤ 10. By Weil II (probe) every
eigenvalue of Frobenius on `Hⁱ_c(W_{𝔽̄_p}, F)` has absolute value `≤ p^{(10+i)/2}` along ι.
Tag 03V0 together with the Euler product gives, for every `n ≥ 1`,
`Σᵢ(−1)ⁱ tr(Fⁿ | Hⁱ_c) = S(n) := Σ_{c ∈ 𝔽_{pⁿ}⁵, Δ≠0} h₁₀(a_c, pⁿ)`.
By the Ihara identity,
`S(n) = −(p⁴β)ⁿ − (p⁴α)ⁿ + (p³β)ⁿ + (p³α)ⁿ − p^{4n} + p^{3n}`.

Suppose `τ(p)² > 4p¹¹`. Then α and β are real, `αβ = p¹¹`, and without loss of generality
`|β| > p^{5.5} > |α|`. The base `λ₀ = p⁴β` is strictly larger in absolute value than every other
base on the right, so its coefficient is exactly `−1`. By uniqueness of exponential-polynomial
expansions (Vandermonde), `Σᵢ(−1)ⁱ mult_{Hⁱ_c}(λ₀) = −1`. Hence λ₀ is an eigenvalue on some
**odd** `Hⁱ_c` with `i ≤ 2d−1 = 9`. That gives `|p⁴β| ≤ p^{19/2}`, so `|β| ≤ p^{11/2}`, a
contradiction. (For a base of dimension `d` the exponent is `p^{d−1}` and the same computation
closes with `i ≤ 2d−1`.)

Consequences: no purity, no `H¹_!`, no duality on the base, no compactification, and no vanishing
of `H⁰_c`/`H²_c` are needed. The sign matters. A `+` coefficient would only place λ₀ in an even
degree and would give `|β| ≤ p⁶`, which is useless.

The statement of M1 typechecks (with `sorry`, as a statement check) in
`scratch/ProbeInterfaces.lean`, as `RamanujanWeil.Plan.deligne_of_package`.

---

## 4. Routes compared

### R1. Kuga–Sato (Deligne/Scholl). Not recommended.

Missing pieces: `Y(N)` (N ≥ 3) as a fine moduli scheme with its universal curve; the
compactification and Néron polygons at cusps; Deligne's desingularization of the 10-fold fibre
power; the action of `(ℤ/N)² ⋊ μ₂` and `S₁₀` and the projector cutting out the Δ-part of `H¹¹`;
Hecke correspondences in characteristic p and the **Eichler–Shimura congruence relation**
`T_p = F + V`. On top of that comes the identification of the `T_p`-eigenvalue with τ(p), which
needs either (a) the Eichler–Shimura isomorphism over ℂ with Artin comparison for **local
systems** (Weil only has constant coefficients, and has to be Hecke-equivariant) or (b) a trace
formula anyway. Estimate ≥ 100k lines, multi-year. Strictly dominates R3 in cost, because it
still needs a bridge to q-expansions.

### R2. Legendre / level-N sheaf route. Not recommended.

The sheaf side is identical to R3. The point sum, however, has an extra newform:
`S_L(p) = −3 − 3τ(p) − a_p(g)` with `g ∈ S₁₂^new(Γ₀(4))`. So it needs Eichler–Selberg for `Γ(2)`
(or `Γ₀(4)`) plus Deuring with level-2 structure. Having a curve as base buys nothing, since
Stacks' Weil II already works in every dimension.

### R3. Universal Weierstrass family over the 5-dimensional level-1 base. **Recommended.**

The level-1 base gives exactly `−1 − s_n` with no other cusp forms. The 5-parameter form works
uniformly for p = 2, 3, which `Bridge.lean` needs because it ranges over all primes. Stacks
already has the family with properness, smoothness and genus-1 fibres.

### R3′ variants considered

* **⊗¹⁰ instead of Sym¹⁰** (avoids `det = q`). The moment `Σ a¹⁰` contains `C_j q^j h_{10−2j}`
  terms with polynomial parts up to `q^{10}`. If `β = ±p^m` these could collide with the dominant
  exponential, which would then need a separate argument. Sym¹⁰ is cleaner. Keep ⊗¹⁰ as the
  fallback if the determinant milestone stalls.
* **Ordinary locus `U = {Hasse ≠ 0}`** (avoids Schoof's supersingular counts). On `U` the sum is
  `q³(q−1)/2 · Σ_{p∤t} h₁₀(t,q)H(4q−t²)` by ordinary Deuring. Numerically this equals
  `−q³(q−1)(s_n + 1) + (weight-10 terms)` (`ordinary_locus_probe.out`), which suffices for §3.
  But proving that the defect has weight ≤ 10 requires the `p∣t` part of Eichler–Selberg through
  `H(p²M)` recursions with a Kronecker twist. That is arithmetic of comparable difficulty to
  Schoof. Decide this at milestone A3.
* **Avoiding n ≥ 2.** Not possible. A single trace identity (n = 1) cannot isolate eigenvalues.
  The L-function argument needs every n.

---

## 5. Recommended route R3: milestones with frozen interfaces

Each milestone is one agent-sized chunk with a frozen Lean statement. G = geometric (Stacks/Weil),
A = arithmetic (Mathlib + Tau). The G milestones depend only on the interface
`IharaIdentity p`, so the A milestones can run in parallel.

Frozen arithmetic interface (typechecks; `scratch/ProbeInterfaces.lean`):

```lean
def symTrace (k : ℕ) (a q : ℤ) : ℤ :=
  ∑ j ∈ range (k / 2 + 1), (-q) ^ j * ((k - j).choose j : ℤ) * a ^ (k - 2 * j)
def tauPowerSum (p : ℕ) : ℕ → ℤ        -- s_n = αⁿ+βⁿ
  | 0 => 2 | 1 => τ p | n + 2 => τ p * tauPowerSum p (n + 1) - p ^ 11 * tauPowerSum p n
def wc (c : Fin 5 → F) : WeierstrassCurve F := ⟨c 0, c 1, c 2, c 3, c 4⟩
noncomputable def traceOfFrob (W : WeierstrassCurve F) : ℤ := Nat.card F + 1 - Nat.card W.toAffine.Point
noncomputable def IharaIdentity (p : ℕ) [Fact p.Prime] : Prop :=
  ∀ n, 1 ≤ n → (letI := Fintype.ofFinite (GaloisField p n); open Classical in
    ∑ c ∈ ({c : Fin 5 → GaloisField p n | (wc c).Δ ≠ 0} : Finset _),
      symTrace 10 (traceOfFrob (wc c)) (p ^ n) = p ^ (3 * n) * (p ^ n - 1) * (-1 - tauPowerSum p n))
```

### Geometric half (G): `IharaIdentity` ⇒ Deligne bound

| # | Milestone | Frozen statement (sketch) | Lines | Risk |
|---|---|---|---|---|
| **M1** | **Endgame (Mathlib only)**: exponential-polynomial uniqueness (Vandermonde), ι-traces of powers equal power sums of charpoly roots, and the dominant-term/sign argument of §3 | `deligne_of_package (p) (d) (hd : 2 ≤ d) (K) (ι : K →+* ℂ) (V : Fin (2d+1) → Type) (F) (hw : roots ≤ p^((10+i)/2)) (S) (htr : ∀ n≥1, Σᵢ (−1)ⁱ tr(F i ^ n) = S n) (hS : ∀ n≥1, S n = p^((d−2)n)(pⁿ−1)(−1−s_n)) : τ p ^ 2 ≤ 4 p ^ 11` (checked statement in the probe) | 1–1.5k | low |
| M2 | **Package from Stacks**: (i) unconditional Weil II (the probe, made a lemma); (ii) from `rationalLFunction_eq_gradedCharSeries_compactSupportFrobenius`, by log-derivative of both sides: `∀ n≥1, Σ_{x closed, deg x ∣ n} deg x · tr(π_xⁿ/ᵈᵉᵍ ˣ \| F_x̄) = Σᵢ(−1)ⁱ tr(πⁿ \| Hⁱ_c)`; (iii) packaging `Hⁱ_c` for `0 ≤ i ≤ 2 dim X` as the `V i` of M1 | `lefschetzPackage_of_lisse (F lisse, mixed ≤ w, realizable) : Package p (dim X) …` with `S n := Σ_{x, deg x∣n} deg x · tr(π_x^{n/deg x})` | 1–2k | low–medium (power-series algebra over `gradedCharSeries`; the dimension bound `topologicalKrullDim W = 5`) |
| M3 | **The family and R¹ over 𝔽_p**: `W_p := Spec 𝔽_p[a₁..a₆][1/Δ]` as a `B.Scheme`, the base change of `Weierstrass.familyOf` (proper, smooth rel. dim 1, by Stacks for any elliptic `C`); `R¹ := higherDirectImageShriek … (CompactificationOf.ofProper) (constant) 1`; **lisse on all of `W_p`** (ℓ-adic upgrade of Tag 0GLI / `ProperCurveHigherDirectImageLisse`); `W_p` connected, noetherian, dimension 5 | `isLisse_R1 : (R1 p ℓ).IsLisse` | 1.5–3k | medium (the `IsLisse` tower definition, `B`-site size bookkeeping, building the Weierstrass closure) |
| M4 | **Stalks of R¹**: at closed `x` with `κ(x) = 𝔽_{p^d}`, `charpoly(π_x \| R¹_x̄) = X² − a_x X + p^d`, with `a_x = p^d + 1 − #E_x(κ(x))`. Ingredients: the stalk theorem; the fibre of `projectionOf` at `x` is `projOf (C.map residue)`; `H⁰ = ℚ_ℓ` with π = 1 and `H² = ℚ_ℓ` with π = q (`CurveTopDegreeFrobenius`); `dim H¹ = 2`; the fibre trace formula; **`det = q`** via the Frobenius-equivariant Weil pairing (`CurveExtWeilPairing`) plus alternation of cup product on `H¹` | `charpoly_R1_stalk (x) : … = X^2 - C (a_x) * X + C (p^deg x)` | 2.5–5k | **medium–high** (det; alternation of cup product may be missing; fallback: the group-theoretic argument `a = 0 ∧ det = −q ⇒ (q+1) ∣ (q−1)²` with Mathlib's group law, plus a hand check at q = 3) |
| M5 | **Sym¹⁰**: lisse `R¹` ⇒ ρ (`exists_representationSheaf_isogeny_of_isLisse`); `Sym¹⁰ρ` as an explicit 11×11 matrix representation (continuous); `F := representationSheaf (Sym¹⁰ρ)`; stalk charpoly roots `α^iβ^{10−i}`, so trace `= symTrace 10 a q`, pointwise mixed `≤ 10`, ι-realizable (integer charpoly); transport of stalk charpolys across the ℓ^N-isogeny | `stalkTrace_F (x) (m) : tr(π_x^m \| F_x̄) = symTrace 10 (α_x^m+β_x^m) (p^{deg x · m})`, `isLisse_F`, `mixed_F`, `realizable_F` | 1.5–3k | medium |
| M6 | **Point-count bookkeeping**: closed points of `W_p` of degree `d ∣ n` ↔ Frobenius orbits in `{c ∈ 𝔽_{pⁿ}⁵ : Δ(c) ≠ 0}`; `κ(x)`-points of the fibre ↔ Mathlib `W.toAffine.Point` (+ ∞) (`WeierstrassCubicPoints`); `#E_x(𝔽_{pⁿ}) = pⁿ + 1 − (α_x^{n/d} + β_x^{n/d})` (fibre L-function / Axiom's zeta) | `S_eq_weierstrassSum (n ≥ 1) : S n = Σ_{c ∈ 𝔽_{pⁿ}⁵, Δ≠0} symTrace 10 (traceOfFrob (wc c)) (pⁿ)` | 2.5–5k | medium |
| — | **Assembly** | `deligneBound_of_ihara : (∀ p, p.Prime → IharaIdentity p) → RamanujanTau.DeligneBound` | 0.2k | low |

**G total: ~10–19k lines** (allow ×1.5 for Stacks API friction). Each milestone is 1–3 weeks of
agent work. Compiles are slow (~8 min per file importing the Weil closure), so batch the probes.

### Arithmetic half (A): prove `IharaIdentity p` for every p

| # | Milestone | Content | Lines | Risk |
|---|---|---|---|---|
| A1 | **Hurwitz class numbers** | Positive definite binary forms, `SL₂(ℤ)` reduction, `H(N)` with weights 1/2, 1/3 and `H(0) = −1/12`; equivalently `Σ_{O ⊇ ℤ[(N+√−N)/2]} h(O)/(#O^×/2)`; the relation `H(p²M)` vs `H(M)`, `H(M/p²)` | 3–6k | medium (decidable for small N, so sanity values can be checked by `decide`) |
| A2 | **Eichler–Selberg for `S₁₂(SL₂ℤ)`** at `n = pᵐ`: `Σ_t h₁₀(t,n)H(4n−t²) = −2τ(n) − Σ_{dd'=n} min(d,d')¹¹` | Needs Hecke operators on `M₁₂` (absent from Mathlib) and one proof of ES. Options: (a) Zagier's weight-3/2 nonholomorphic Eisenstein series, Rankin–Cohen bracket with θ, holomorphic projection; (b) Zagier 1990 / Popa: period polynomials plus the Eichler–Shimura isomorphism at level 1 (periods of Δ, Manin–Choie Hecke elements on `W₁₀`) | 20–50k | **high, multi-month** |
| A3 | **Deuring–Waterhouse–Schoof** over `𝔽_q`, `q = pⁿ`: weighted number of Weierstrass tuples with trace t is `q³(q−1)·H(4q−t²)/2` for p ∤ t (ordinary), plus Schoof's explicit supersingular counts for p ∣ t (verified numerically to differ at q = 25, 49) | Frobenius endomorphism, isogenies and degrees, `End(E)` as an order in `ℚ(π)`, the bijection with ideal classes (Waterhouse via Tate's isogeny theorem for elliptic curves over finite fields, or Deuring lifting with CM theory), supersingular theory (quaternion orders, Eichler mass formula `Σ 1/#Aut = (p−1)/24`) | 40–100k | **very high, likely the longest pole (≥ 6–12 months)** |
| A4 | **Assembly** | `Σ_t h₁₀(t,q)·N(t,q)` with A2 at `q` and `q/p²` (`s_n = τ(pⁿ) − p¹¹τ(p^{n−2})`), A3, and the coordinate-change torsor count `#{c : E_c ≅ E} = q³(q−1)/#Aut E` (Stacks has `WeierstrassCoordinateChangeTorsor`) | 2–4k | medium |

**A total: ~65–160k lines.** That is of the same order as Axiom's whole Weil-conjectures effort
in places, and is the honest risk: **A2 and A3 are each multi-month projects, and A3 may take a
year or more.** Supersingular counting for n ≥ 2 is the most dangerous single piece. The A3′
ordinary-locus variant trades it for a twisted class-number identity that is not obviously easier.

### Overall

* Full formalization: ~75–180k lines. A "Weil II for sheaves" milestone is **not** needed; it is
  already there. The open-ended risk sits entirely on the arithmetic side.
* Intermediate deliverable (G only, ~10–19k lines): `deligneBound_of_ihara`. This replaces the
  geometric `TauRealization` (Kuga–Sato existence plus Eichler–Shimura, unverifiable by
  computation) with `IharaIdentity`: a statement about finite sums over `𝔽_{pⁿ}⁵` and the
  q-expansion of Δ, checked exactly by `scripts/scout` for all q ≤ 9 in full 5-parameter form,
  q = p ≤ 61 and q ∈ {25, 49, 121, 125, 169} in short form. Small instances (q ≤ 5) may even be
  provable by `decide` as sanity lemmas.

## 6. Which milestone to start first

**M1** (endgame). It is pure Mathlib plus `RamanujanWeil.Tau`, compiles in seconds rather than
minutes (no Weil closure), has a frozen and already-typechecked statement
(`scratch/ProbeInterfaces.lean`), and is the only place where the "upper bound plus negative sign
suffices" argument has to be made rigorous. In parallel, someone can start **A1** (Hurwitz class
numbers, Mathlib only) as a low-risk entry into the arithmetic half. Then do M2 (Weil II plus
L-function package; the probe is already its first lemma), then M3 → M4 → M5 → M6.

## 7. Files from this scouting session

* `docs/REALIZATION_PLAN.md`: this file.
* `scripts/scout/ihara_level1.gp` (+ `.out`): level-1 Ihara identity, short and 5-parameter forms.
* `scripts/scout/ihara_bruteforce.py` (+ `.out`): independent check without PARI.
* `scripts/scout/legendre_probe.gp` (+ `.out`): Legendre decomposition `−3 − 3τ(p) − a_p(g)`.
* `scripts/scout/eichler_selberg_check.gp` (+ `.out`): ES at n ≤ 300, prime-field Deuring,
  supersingular discrepancies at q = 25, 49.
* `scripts/scout/ordinary_locus_probe.gp` (+ `.out`): ordinary-locus defect has weight 10.
* `scratch/ProbeWeilII.lean` (+ `.out`): unconditional Weil II for lisse sheaves, axiom-clean.
* `scratch/ProbeInterfaces.lean` (+ `.out`): frozen interface statements (one `sorry`, a
  statement check only).

All PARI runs used `default(nbthreads,1)`, one niced process. The Lean probes ran as one niced
`lake env lean`, peak RSS about 3 GB.
