# Weil bridge: Deligne's bound for τ(p) from Axiom's Weil RH

## What is proved

`RamanujanWeil.deligneBound_of_realization` (file `RamanujanWeil/Bridge.lean`):

```lean
theorem RamanujanWeil.deligneBound_of_realization
    (hR : ∀ p : ℕ, p.Prime → Nonempty (TauRealization.{u} p)) :
    ∀ p : ℕ, p.Prime → (RamanujanTau.tau p) ^ 2 ≤ 4 * (p : ℤ) ^ 11
```

The conclusion is textually the field `RamanujanTau.DeligneBound.bound` of
`~/RamanujanTau/RamanujanTau/Deligne.lean`, and `RamanujanTau.tau` is a verbatim copy of
`~/RamanujanTau/RamanujanTau/Basic.lean` (`RamanujanWeil/Tau.lean`; no change was needed for the
toolchain bump v4.30 → v4.34.0-rc2). The class `RamanujanTau.DeligneBound` is restated verbatim
and discharged by `deligneBound_instance_of_realization`. Variants:

* `tau_sq_le_of_realization (R : TauRealization p) : τ(p)^2 ≤ 4 p^11` (per prime);
* `deligneBound_of_realization'` (data-valued hypothesis `∀ p, p.Prime → TauRealization p`);
* `norm_map_trace_le_of_stable` (any weight): for `X` smooth proper over `k`, `q = #k`, any `ν`, any
  `F_ν`-stable `W ⊆ H^ν(X_k̄, ℚ_ℓ)` and any `ι : ℚ_ℓ →+* ℂ`,
  `‖ι (tr F_ν|_W)‖ ≤ dim W · q^(ν/2)`;
* `int_sq_le_of_stable`: if that trace is an integer `t`, then `t² ≤ (dim W)² q^ν`.

## The hypothesis `TauRealization p`

Stated entirely in Axiom's API (`Weil/Definitions.lean`):

* a big étale site `B : BigEtaleSite.{u}`, a finite field `k` with `Fintype.card k = p`;
* `X : B.Scheme` with `f : X.1 ⟶ Spec (.of k)`, `[IsProper f]`, `[Smooth f]`;
* a prime `ℓ` with `Fact (ℓ ≠ ringChar k)`;
* `W : Submodule ℚ_[ℓ] (Weil.rationalCohomology B X f ℓ 11)`, i.e. a subspace of
  `H^11(X_k̄, ℚ_ℓ)`, stable under `Weil.rationalFrobenius B X f ℓ 11`;
* `Module.finrank ℚ_[ℓ] W = 2`;
* `LinearMap.trace (F_11|_W) = (τ p : ℚ_ℓ)`.

There is no size condition on τ anywhere: the only analytic content is Axiom's
`Weil.satisfiesWeilEstimate` (Deligne's theorem), used through
`Weil.satisfiesWeilEstimate_iff_forall_isCharpolyPureOfWeight`. The dimension 2 is essential:
it is the `d` in `|τ(p)| ≤ d · p^{11/2}`.

**Frobenius convention.** Axiom's `rationalFrobenius` is the *geometric* Frobenius. On the
Δ-part of H^11 its characteristic polynomial is `X² − τ(p)X + p¹¹`, so trace = τ(p). With the
arithmetic Frobenius the eigenvalues are inverted and the trace would be τ(p)/p¹¹; the hypothesis
is therefore stated (and only correct) for the geometric Frobenius.

## The argument

1. (`LinearAlgebra.lean`, pure Mathlib) For a `φ`-stable `W`, every complex root (along `ι`) of
   `charpoly(φ|_W)` is a root of `charpoly(φ)`: base change to `ℂ` via `ι`, take an eigenvector of
   `(φ|_W)_ℂ`, push it into `ℂ ⊗ V` (injective because `ℂ` is flat over the field), and use
   `charpoly_baseChange`.
2. `ι(tr φ|_W) = tr((φ|_W)_ℂ) = Σ roots`, with `dim W` roots counted with multiplicity
   (ℂ algebraically closed), each of absolute value `q^{ν/2}` by Axiom's Weil RH. Triangle
   inequality: `‖ι(tr)‖ ≤ dim W · q^{ν/2}`.
3. An embedding `ι : ℚ_ℓ →+* ℂ` exists (`#ℚ_ℓ ≤ 𝔠`; Axiom's
   `RingHom.exists_comp_algebraMap_eq_of_countable` + `Padic.cardinalMk_le_continuum`).
   `ι` fixes integers, so `|τ(p)| ≤ 2 p^{11/2}`; square.

## Non-vacuity (literature; cited from memory, NOT checked)

The hypothesis is the standard geometric input ("Eichler–Shimura–Deligne"):

* P. Deligne, *Formes modulaires et représentations ℓ-adiques*, Sém. Bourbaki 355 (1969):
  the ℓ-adic Galois representation of Δ is cut out of the parabolic cohomology
  `H¹_p(M_N, Sym^10 R¹π_*ℚ_ℓ)`, which he embeds in `H^11` of a desingularized Kuga–Sato variety;
  the Eichler–Shimura congruence relation gives char poly of geometric Frobenius at `p ∤ Nℓ`
  equal to `X² − τ(p)X + p¹¹`.
* A. J. Scholl, *Motives for modular forms*, Invent. Math. 100 (1990): the Kuga–Sato variety
  `W_10` (10-fold fibre power of the universal elliptic curve over a modular curve of level
  `N ≥ 3`, compactified and desingularized) is smooth and projective over `ℤ[1/N]`, with a
  projector cutting out the motive of weight-12 forms.
* B. Conrad's appendix ("The Shimura construction in weight 2 and higher weights") to
  "Modular forms and the Ramanujan conjecture" (attribution as given in the task; unchecked).

For a given prime `p`, take `N ∈ {3, 4}` prime to `p`, `X` = reduction mod `p` of `W_10`
(smooth proper over `𝔽_p`, by good reduction), `ℓ ≠ p`, and `W` = one copy of the Δ-eigensystem
inside the Δ-isotypic part of `H^11(X_{𝔽̄_p}, ℚ_ℓ)` (identified with `H^11` of the generic fibre by
smooth proper base change). At level `N` the Δ-isotypic part may be `V_Δ ⊗ M` with `M` an
oldform multiplicity space and Galois acting trivially on `M`; any `V_Δ ⊗ m` is a 2-dimensional
Frobenius-stable subspace with trace τ(p), so one copy suffices.

What is NOT formalized: the Kuga–Sato variety, its smoothness/properness, Eichler–Shimura,
the identification of Axiom's `rationalCohomology` (compactly supported, constant system,
`AlgebraicClosure k`) with the cohomology used in the literature. These are exactly the content of
`TauRealization`.

## Evidence level

* **Lean, kernel-checked, conditional on `TauRealization`** at every prime; Weil RH itself is
  fully formalized by Axiom (`Weil.satisfiesWeilEstimate`, axiom-clean per their README and per
  `#print axioms` below).
* `#print axioms` on every headline: `[propext, Classical.choice, Quot.sound]`
  (see `RamanujanWeil/Axioms.lean`).
* No `sorry`, `admit`, `native_decide`, or new axioms. Sanity values `τ 2 = -24`, `τ 3 = 252`,
  `τ 5 = 4830` by `decide +kernel`.
* Caveat: Axiom's Weil code (~980 modules) is AI-written and, per its README, not yet
  human-reviewed; our bridge trusts the *statements* `rationalCohomology`, `rationalFrobenius`,
  `SatisfiesWeilEstimate` to mean what their docstrings say.

## Build log (2026-11-07/08, 14-core Mac)

* Toolchain `leanprover/lean4:v4.34.0-rc2` (same as Weil). `lakefile.toml` requires
  `AxiomMath/Weil` at rev `27cdb2049be62ee2911429b47f54774078450e32`, which pins
  `AxiomMath/Stacks` `012108f6…` and Mathlib `16edf57de793…` (plausible is `d9598f07`).
* `lake update` + automatic Mathlib cache download: ~6 min.
* Stacks/Weil have no cache: the import closure of
  `Weil.AlgebraicGeometry.EtaleCohomology.Trace.DeligneWeilConjecture` (+ `Weil.FieldTheory.IsAlgClosed.Classification`)
  is **20,460 non-Mathlib modules** (Stacks has ~63k files). Built from source with one niced
  `lake build` of only those two targets, under an external SIGSTOP/SIGCONT throttle scoped to
  that lake's own `lean` children (Lake 5 has no `-j`): 3–4 workers, ~7 GB running-RSS soft cap.
  Total wall time **≈ 20.7 h** (74,650 s over 6 resumable runs: early runs were killed by the
  RSS guard; individual modules such as
  `StacksFrontier/AlgebraicGeometry/EtaleCohomology/Colimits/LimitHigherDirectImageFixedBase.lean`
  briefly need several GB each).
* Disk: `.lake` = **24 GB** (Mathlib 7.1 GB, Stacks 16 GB). Lake's per-module
  `ir/*.setup.json` files would have added ~35 GB (≈1.7 MB each); they are compiler inputs, not part of
  the up-to-date check (verified with `lake build --no-build`), so finished ones were pruned
  during the build. Deleting `ir/*.c` instead DOES force rebuilds.
* Our package: `RamanujanWeil.Bridge` 483 s (mostly importing the closure), root 133 s,
  `Tau`/`LinearAlgebra` seconds. `lake build RamanujanWeil RamanujanWeil.Axioms`: exit 0.
* No toolchain friction in our files: `Tau.lean` compiled unchanged on v4.34.0-rc2.
