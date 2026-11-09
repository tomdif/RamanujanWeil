# A3-ord progress: geometric steps G2, G3, G4 (session of 2026-11-08)

This continues `docs/ARITH_DEURING_PLAN.md`. The algebraic end (D-ALG, D-ASM) is unchanged.
This session started the geometric side, working only against Stacks/Mathlib APIs. All new files
are axiom-clean: only `propext`, `Classical.choice`, `Quot.sound`, with no
`sorry`/`admit`/`native_decide`/`axiom`. The audit is `RamanujanWeil/Arith/DeuringGAxioms.lean`.

## 0. Framework decision (refines plan §4)

**All of Stacks' Tate-module, characteristic-polynomial and kernel-count theorems are stated over
an algebraically closed field.** (`tateModule A ℓ` is built from the rational points `A(k)`.)
So "the abelian variety of `W / 𝔽_q`" is taken over `k̄ = AlgebraicClosure 𝔽_q`, as follows.

* `A_W` = the Jacobian of the geometric curve `E_k̄ = (projOf W) ×_k k̄`. Its Frobenius `π_W` is
  the endomorphism induced by the twisted Frobenius `Ψ = id × Spec(x ↦ x^q)` of `E_k̄`. This is
  Weil's set-up, which Stacks uses for RH (`Stacks.Zeta.exists_jacobianFrobenius_data`).
* The `𝔽_q`-structure is remembered only through `π_W`: `Hom_{𝔽_q}(E, E')` will be the
  homomorphisms `A_W ⟶ A_W'` that commute with `π`. Proving that this is the correct notion is
  Galois descent, and it moves into G1/G9, where `Stab_G(W) ≅ Aut_{π}(A_W)` has to be shown
  anyway.
* **G1 is not a prerequisite for G2.** The point count comes from the closed points of `E_k̄`
  fixed by `Ψ` (`#W(𝔽_q)`). It goes through Stacks' `natCard_fixedSections_…` together with the
  repo's `natCard_fieldValuedPoints_projOf`. It does not use the Abel map `E ≅ Jac E`.

## 1. Proved this session

### `RamanujanWeil/Arith/DeuringG3.lean` (G3, injectivity; ~250 lines)

These results hold for `k` algebraically closed, `A`, `B` abelian varieties over `k`, `dim A = 1`
and `ℓ` invertible in `k`.

| Name | Statement |
|---|---|
| `point_ext` | Two `k`-points with the same image point are equal. |
| `eq_one_of_infinite_pointKer` | A homomorphism `α : A ⟶ B` that kills infinitely many `k`-points is trivial. Its kernel is closed, a proper closed subset of the curve `A` is finite (`Stacks.Topology.Dimension.finite_of_isClosed_of_ne_univ`), and `Stacks.Varieties.overHom_ext_of_points` finishes. |
| `eq_one_of_tateModuleMap_eq_zero` | `T_ℓ α = 0 ⇒ α = 0`. |
| `tateModuleMap_injective` | `Hom(A,B) → Hom_{ℤ_ℓ}(T_ℓ A, T_ℓ B)` is injective. |
| `eq_one_of_zpow_eq_one` | `Hom(A,B)` is torsion free. |
| `tateModuleMap_endPolyEval` | `T_ℓ(R(α)) = R(T_ℓ α)` for `R ∈ ℤ[X]`. |
| `endPolyEval_eq_one_of_endCharPoly_eq` | **Cayley–Hamilton in `End(A)`**: if `χ_α = R` with `R ∈ ℤ[X]`, then `R(α) = 0`. |
| `exists_prime_isUnit` | Every field has a prime `ℓ` invertible in it. |

### `RamanujanWeil/Arith/DeuringG4.lean` (G4 on `End`, dimension one; ~190 lines)

| Name | Statement |
|---|---|
| `endCharPoly_eq_of_dim_one` | `χ_α = X² − (Tr α) X + deg α`. |
| `endDegree_zpow_mul_zpow` | `deg(mα + n) = m² deg α + mn Tr α + n²` for all `m, n ∈ ℤ`. Computed as `det(m T_ℓα + n)` in a basis of the rank-2 Tate module. |
| `trace_sq_le_four_mul_endDegree` | **Hasse for every endomorphism**: `(Tr α)² ≤ 4 deg α`. |
| `endDegree_eq_zero_iff` | `deg α = 0 ↔ α = 0`. With the previous row, `deg` is a positive definite integral quadratic form on `End(A)`. |
| `endDegree_one`, `infinite_points`, `finite_of_finite_ker_of_finite_range`, `quadratic_ext` | helpers |

Multiplicativity `deg(αβ) = deg α deg β` and `deg(nα) = n² deg α` are already Stacks'
`endDegree_comp` and `endDegree_zpow`.

### `RamanujanWeil/Arith/DeuringG2.lean` (G2; ~390 lines)

| Name | Statement |
|---|---|
| `exists_jacobian_charPoly_twisted` | General statement: a smooth proper curve `C / 𝔽̄_p` with a twisted Frobenius `Ψ` (`Ψ ≫ φ = F^f`) has a Jacobian `A` of dimension `genus` with Frobenius `F`, such that `χ_F.nextCoeff = N₁ − 1 − q` (`N₁` = closed points fixed by `Ψ`) and `χ_F` is `q`-symmetric. Stacks proves this only inside `weilTraceInput`, for an anonymous `χ`. Here the argument is redone with `χ := endCharPoly A F`, using the zeta roots, the Weil pairing and `exists_charpoly_levelMatrix_eq_of_normForm`. |
| `natCard_fixedClosedPoints_weierstrass` | For `E = projOf W`: the closed points of `E_k̄` fixed by `Ψ` number `#W(𝔽_q)` (Mathlib's `Point`). |
| `FrobeniusJacobian W` (structure) | `A : Over (Spec k̄)`, `GrpObj`, `IsAbelianVariety`, `π : A ⟶ A`, `IsMonHom π`, `dim A = 1`, `χ_π = X² − tX + q`, with `t = traceOfFrob W`. |
| **`nonempty_frobeniusJacobian`** | Every elliptic `W / 𝔽_q` has one. |
| **`FrobeniusJacobian.frob_quadratic`** | **G2: `π² − tπ + q = 0` in `End(A)`** (`endPolyEval π (X² − tX + q) = 1`). |
| `FrobeniusJacobian.endDegree_π` | `deg π = q`. |

Together with G4, this gives Hasse's bound `t² ≤ 4q` a second time, from the positivity of the
degree rather than from étale cohomology.

### `RamanujanWeil/Arith/DeuringG3Div.lean` (G3, divisibility)

| Name | Statement |
|---|---|
| `exists_isMonHom_zpow_comp_eq` | Let `n` be invertible in `k`. If `α : A ⟶ B` kills `A(k)[n]`, then `α = [n] ≫ β` for a homomorphism `β`. This holds in any dimension. `[n]` is étale and surjective, hence an effective epimorphism (Mathlib `Sites/Fpqc`). `α` descends because `A ×_{[n]} A` is reduced (étale over `A`), and `β` is a homomorphism because it is multiplicative on `k`-points of the reduced `A ⊗ A`. |
| `exists_zpow_eq_point`, `comp_zpow_id` | helpers |

### `RamanujanWeil/Arith/DeuringG3Sat.lean` (G3, saturation)

| Name | Statement |
|---|---|
| `comp_eq_one_of_tateModuleMap_dvd` | If `T_ℓ α ∈ ℓ^m · Hom(T_ℓA, T_ℓB)`, then `α` kills `A(k)[ℓ^m]`. |
| `exists_eq_comp_of_tateModuleMap_dvd` | If `T_ℓ α ∈ ℓ^m · Hom(T_ℓA, T_ℓB)`, then `α = [ℓ^m] ≫ β` with `β` a homomorphism. So the cokernel of `Hom(A,B) → Hom(T_ℓA, T_ℓB)` is `ℓ`-torsion free, in any dimension. |

## 2. Remaining G3/G4 pieces (refined estimates)

* **G3, finite generation and `Hom ⊗ ℤ_ℓ ↪ Hom(T_ℓ)`** (0.6–1.2k). Saturation is done
  (`DeuringG3Sat`). Two pieces remain:
  * finite generation of `M^div = (M ⊗ ℚ) ∩ Hom` for finitely generated `M`. Silverman III.7.4
    gets it from the discreteness of `{deg < 1}`. For `End(A)` the positive-definite quadratic
    `deg` is already available (G4). For `Hom(A,B)` it needs G4 on `Hom` together with a
    quadratic-form structure, which requires a nonzero `B ⟶ A` (G7), or the `End(A × B)` trick;
  * the Mumford/Silverman approximation argument: `ℤ`-independent elements give
    `ℤ_ℓ`-independent `T_ℓ`-images, hence rank ≤ 4.

  Mathlib's `ZLattice`/discrete-subgroup API should cover "discrete ⇒ finitely generated".
* **G4 for `Hom(A,B)`, `A ≠ B`** (0.4–0.8k). Define `deg α := degreeOver α.left` when `α` is
  dominant and `0` otherwise. Multiplicativity follows from
  `AlgebraicGeometry.degreeOver_comp_of_pos`; positivity in dimension one comes from the
  infinite-kernel lemma (a non-dominant `α` has the whole curve as kernel). Being a quadratic
  form needs a nonzero `B ⟶ A`, i.e. G7.
* **G2 extras** (0.2–0.5k). `π` commutes with every `π`-equivariant `α` by definition of
  `Hom_{𝔽_q}`. `ℤ[π] ⊆ End(A)` is an order of discriminant `t² − 4q < 0` when `p ∤ t`, by G4
  plus `frob_quadratic`.
* **G2 for the *existential* Jacobian.** `nonempty_frobeniusJacobian` only gives `Nonempty`. Later
  steps should fix `A_W := (nonempty_frobeniusJacobian W).some`. G1 then has to identify
  `Aut_π(A_W)` with `Stab_G(W)` for this choice. Nothing else in the data depends on the choice,
  because `exists_jacobianFrobenius_data` hides the big site.

## 3. Revised risks: G1, G6, G7

* **G1 (3–6k, medium; unchanged).** Needed only for `rel_iff`/`card_stab`, not for G2–G4. New
  observation: everything now lives over `k̄`. So G1(b,c) becomes "`W' ∈ G•W` (over `𝔽_q`) ⟺
  there is a `π`-equivariant isomorphism `A_W ≅ A_W'`", which includes Galois descent of
  isomorphisms. The descent is easy for elliptic curves: a `k̄`-isomorphism of Weierstrass
  cubics commuting with Frobenius has `(u, r, s, t) ∈ 𝔽_q`. That still needs the Abel map
  `E_k̄ ≅ A_W`.
* **G6 (quotients) — risk lowered from high to medium–high.** Two Stacks facts, found this
  session, change the picture:
  1. Mathlib `AlgebraicGeometry/Sites/Fpqc.lean`: every quasi-compact, flat, surjective morphism
     is an **effective epimorphism**. This is what made `DeuringG3Div` cheap. A quotient
     `A → A'` with kernel `G`, once it exists, gives all the factorization properties for free.
  2. Stacks `Spaces/Quotients/GroupActionQuotient.lean` proves **Stacks 06PH**: for a free
     action of a flat, locally finitely presented group algebraic space `G`, the quotient `X/G`
     is an algebraic space, and `X → X/G` is an fppf `G`-torsor.

  So `A/G` exists as an algebraic space. What is missing: (i) the quotient is a scheme (a group
  algebraic space, proper over a field, is a scheme, Stacks 0B8G/0B8H; not checked in Stacks
  yet); (ii) it is an abelian variety (proper, geometrically integral, group law descends; the
  group-law descent is like `DeuringG3Div`). Revised estimate for G6 via 06PH: **4–8k**, against
  the original 5–12k; Vélu stays the fallback.
* **G7 (Tate) — still very high, but the obstruction is now located.** Tate's argument for
  `Hom(E, E')` needs quotients of the **surface** `E × E'` by `π`-stable subgroups (G6 in
  dimension 2, which 06PH covers uniformly in dimension) and the **finiteness of
  `π`-equivariant isomorphism classes** of the quotients `(E×E')/G_n`. In this framework the
  quotients are abelian surfaces over `k̄` with a Frobenius, which is a `π`-twisted form
  (Weil descent datum). Finiteness of such classes is the real open input. The candidate
  route: polarize with the product principal polarization pushed forward (needs dual abelian
  varieties, which are absent), or bound the degree of an embedding (needs `AbelianVarietyProjective`
  plus Hilbert-scheme finiteness over `𝔽_q`). Estimate unchanged, **10–25k**.
  * Partial de-risking: the `End` case of Tate (`End(E) ⊗ ℤ_ℓ ≅ End_π(T_ℓ E)`) needs only
    quotients `E/G` (**curves**). Their finiteness is free, since there are finitely many
    Weierstrass equations over `𝔽_q`, provided G1 identifies `π`-equivariant isomorphism
    classes with `VariableChange`-orbits. This `End`-Tate gives `End(E) ⊇ ℤ[π]` of finite
    index, but not "equal trace ⇒ isogenous".

## 4. Checkpoint status

All six new files compile, and `lake build RamanujanWeil.Arith.DeuringGAxioms` succeeds:
`DeuringG3`, `DeuringG4`, `DeuringG2`, `DeuringG3Div`, `DeuringG3Sat`, `DeuringGAxioms`,
about 1.07k lines. Every audited theorem depends only on `[propext, Classical.choice,
Quot.sound]`. The new files are not imported from `RamanujanWeil.lean`, because existing files
were not edited.

Build cost: each file needs about 1–4 minutes of wall time, mostly import loading. The required
Stacks modules `GroupScheme.AbelianVariety.CharPoly` and `Variety.RationalPointsHomExt` were
built once this session; everything else was already prebuilt.

## 5. Next steps (in order)

1. G3 finite generation + `Hom ⊗ ℤ_ℓ ↪ Hom(T_ℓ)` + rank ≤ 4 (0.6–1.2k).
2. G4 on `Hom(A,B)` via `degreeOver` (0.4–0.8k).
3. G1(a) Abel map `E_k̄ ≅ Pic¹ ≅ A_W` in genus 1 (Stacks `AbelJacobi`, `Picard/AbelMap*`) and
   G1(b,c) with Galois descent (3–6k).
4. G6 via Stacks 06PH. First check for "proper group algebraic space over a field is a scheme"
   in Stacks (grep `0B8G`, `GroupAlgebraicSpace`).
5. G5 (p-part, ordinary): needs `exists_isMonHom_zpow_comp_eq` for `n = p`, where `A[p]` is
   **not reduced**. So "kills `k`-points" must become "kills the torsion scheme", proved using
   the ordinary splitting `A[p] = μ_p × ℤ/p`.
