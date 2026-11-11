# RamanujanWeil

[![Repository checks](https://github.com/tomdif/RamanujanWeil/actions/workflows/repository-checks.yml/badge.svg)](https://github.com/tomdif/RamanujanWeil/actions/workflows/repository-checks.yml)

Lean 4 developments toward **Deligne’s bound for Ramanujan’s τ**:

```text
τ(p)² ≤ 4p¹¹    for every prime p.
```

**The bound is still conditional.** The project formalizes two routes from
Axiom’s Weil results to this inequality, and records the remaining arithmetic
and geometric inputs as named hypotheses. No `sorry`, `native_decide`, or new
axiom declarations are used. Headline axiom audits expect only `propext`,
`Classical.choice`, and `Quot.sound`; those audits do not discharge explicit
hypotheses.

**[Weil bridge](docs/WEIL_BRIDGE.md) · [Arithmetic route](docs/ARITH_ROUTE.md) ·
[Deuring assembly](docs/ARITH_DEURING_FINAL.md) ·
[Verification](docs/verification/publication_2026_11_11.json)**

## The two routes

| Route | Proved reduction | Remaining input |
|---|---|---|
| Geometric realization | `deligneBound_of_realization` applies the Weil estimate to a two-dimensional Frobenius-stable subspace of degree-11 cohomology with trace `τ(p)` | Construct `TauRealization p` for every prime |
| Ihara–Birch and Deuring | The geometric estimate, Eichler–Selberg trace formula, Kronecker–Hurwitz identity, and per-class Deuring multiplicity count are proved | Ordinary isogeny-class uniqueness (`MultLeOneAll`), or ordinary trace existence |

The second route reduces uniqueness to finiteness of the relevant principally
polarized quotient surfaces. It has proved Jacobian construction, isogeny and
class-lattice steps, the Riemann–Roch stabilizer bridge, genus-2 models,
Jacobian functoriality, and the one-dimensional invariant-section count.
The latest source also supplies ample descent and reduces Heisenberg
nondegeneracy to the Abel–Jacobi comparison.

## Current proof frontier

Updated 2026-11-11. These are the remaining inputs on the geometric-finiteness
route; older milestone documents retain their dated development history.

| Input | What remains | Source / guide |
|---|---|---|
| `PicClassBridgeAll` | Restrict Picard classes to the affine chart and compare with Mathlib’s ideal class group; this supplies Abel–Jacobi compatibility and the Heisenberg input | [AJ and Heisenberg](docs/ARITH_DEURING_G7_AJHEIS.md) |
| `LevelSectionDescent` | Construct the module descent and identify global sections with the level-subgroup invariants | [Level descent](docs/ARITH_DEURING_G7_LEVELDESCENT.md) |
| `ThetaJacobianModel` | Theta-divisor dichotomy, Frobenius stability, Jacobian identification, and the two remaining Frobenius properties | [Five precise inputs](docs/ARITH_DEURING_G7_THETAJ.md) |
| `Genus2FrobDescent` | Hyperelliptic presentation rigidity and fixed-generator descent; Lang’s model-change step is proved | [Genus-2 descent](docs/ARITH_DEURING_G7_G2DESCENT.md), [rigidity reduction](RamanujanWeil/Arith/DeuringG7G2Desc2Canon.lean) |

`GlueAmpleDescent` is discharged using Stacks 0B5V;
[ample descent](docs/ARITH_DEURING_G7_AMPLE.md) corrects an earlier note that
this theorem was unavailable. `ThetaHeisenbergAll` follows from
`AbelJacobiAll`; it is not an additional independent input once the class-group
bridge is proved. `ThetaJacobianModel` and `Genus2FrobDescent` together imply
[principal finiteness](docs/ARITH_DEURING_G7_PRINCIPAL.md).

## Build and audit

With `elan` installed:

```sh
git clone https://github.com/tomdif/RamanujanWeil.git
cd RamanujanWeil
lake exe cache get
python3 scripts/verify_lean.py
python3 scripts/check_repository.py
```

The pinned toolchain is Lean `v4.34.0-rc2`. The
[manifest](lake-manifest.json) fixes AxiomMath/Weil at `27cdb20`, Stacks at
`012108f`, and Mathlib at `16edf57`. Do not update dependencies when reproducing
the recorded proof snapshot.

The import closure exceeds 25,000 build jobs. A fresh Stacks/Weil build can take
many hours and requires substantial memory and disk space. Some dependency
modules have used more than 6 GB individually. GitHub runs source and
link checks. The 2026-11-11 full build passed (30,382 jobs), and all 62 public
audit declarations used only the expected standard axioms. Source hashes and
outputs are in the [publication record](docs/verification/publication_2026_11_11.json).

The verifier builds `RamanujanWeil` and `RamanujanWeil.Axioms`, then checks
62 declarations across the Weil bridge and latest reductions in one process.
It rejects unexpected axioms and saves logs under
`/tmp/ramanujan-weil-verification` (override with `--output-dir`).
To inspect the reductions individually:

```sh
lake env lean RamanujanWeil/Arith/DeuringG7AJHeisAxioms.lean
lake env lean RamanujanWeil/Arith/DeuringG7AmpleDescentAxioms.lean
lake env lean RamanujanWeil/Arith/DeuringG7ThetaJAxioms.lean
lake env lean RamanujanWeil/Arith/DeuringG7G2Desc2CanonAxioms.lean
```

## Relationship to RamanujanLean

[RamanujanLean](https://github.com/tomdif/RamanujanLean) uses Lean
`v4.30.0-rc2`; this package uses the newer toolchain required by Weil/Stacks.
[Tau.lean](RamanujanWeil/Tau.lean) copies its computable τ definition, keeping
the namespace and statement identical. The repositories are not yet a single
importable dependency graph. Closing the mathematical inputs and reconciling
the toolchains are both required before downstream results in RamanujanLean
can consume an unconditional Deligne theorem.
