# A3-ord, G6: quotients of abelian varieties by finite subgroups

Status (2026-11-09): **G6 is done in every dimension and characteristic, for any finite locally
free subgroup scheme.** The étale case (finite subgroup `H ⊆ A(k)`) includes kernel = `H`, degree
= `#H`, and the universal property. The files are axiom-clean (`DeuringG6Axioms.lean`). Nothing
else in the project imports them yet, and no existing file was edited.

## 1. Route chosen

We did not need "a proper group algebraic space is a scheme" (Stacks 0B8G), Vélu's formulas, or
gluing of invariant rings by hand. Stacks already proves the scheme-level statement:

* **Stacks 07S7** (`AlgebraicGeometry.nonempty_finiteFlatQuotient_actionGroupoid_of_geometry`,
  `Spaces/FreeGroupSchemeQuotient.lean`). It applies to a *free* action of a finite locally free
  group scheme `G/S` on `X/S` with `X → S` projective. It gives a scheme `M` and a map `X → M`
  that is finite locally free and surjective, whose kernel pair is `G ×_S X` (`FiniteFlatQuotient`).
* An abelian variety is projective (`isProjective_of_isAbelianVariety`, Stacks 0BFA). So every
  orbit lies in an affine open, via `hasAffineFinitePointsInFibres_of_isProjective`.
* A finite locally free surjection is an **effective epimorphism** (Mathlib `Sites/Fpqc`). So
  every morphism that is constant on `G`-orbits, as tested on `T`-points, descends (§2).

The steps after that are formal:

1. **Group law on `B = A/G`.** `μ_A ≫ q` descends along `q ⊗ q`, which is again flat,
   quasi-compact and surjective. The inverse and unit are handled the same way. This needs `A`
   commutative (`isCommMonObj_of_isProper_of_geometricallyIntegral`). The group axioms are
   checked on points coming from `A` (`hom_ext₁/₂/₃`, `hom_ext_unit_left/right`).
2. **`B` is an abelian variety.** Each property comes from Stacks or Mathlib:
   * locally of finite type: fppf-local on the source (Stacks 036O);
   * separated: a group scheme over a field (047L);
   * universally closed and quasi-compact: `q` is surjective;
   * connected: image of `A`;
   * reduced: flat descent (`isReduced_of_flat_of_surjective`), hence geometrically reduced
     because `k` is perfect;
   * then `isAbelianVariety_of_isProper_of_connectedSpace_of_geometricallyReduced`.
3. **Kernel.** The kernel pair gives `x ≫ q = 1 ↔ x` factors through `j`, for all `T`-points.
4. **Universal property.** A homomorphism `α` with `j ≫ α = 1` is constant on orbits, so it
   descends to `β`. `β` is a homomorphism (checked through the epimorphism `q ⊗ q`), and it is
   unique because `q` is an epimorphism.
5. **Degree.**
   * `q` has rank `deg q` (Stacks `isFiniteLocallyFreeOfRank_degreeOver`).
   * The base change of `q` along `q` is `G ×_k A → A`, which is also the base change of `G → k`.
   * Fibre ranks are unique, so `deg q = rank G`.
6. **Étale case.** The constant group scheme `H_k` (Stacks 03YW, `constantGroupSchemeModObj`)
   acts on `A` by translations, and `j(g) = g • 1`.
   * The action commutes with right multiplication. The pieces where a point is constant give
     this, so `j` is a homomorphism and the action is translation through `j`.
   * The action is free: a `k`-point is determined after pulling back to any nonempty `k`-scheme.
     Hence `j` is mono.
   * The `k`-points of `H_k` are exactly the constant points (`Spec k` is a disjoint union of the
     pieces, so some piece is nonempty). So `ker q(k) = H`.
   * `rank H_k = #H`: new here, since Stacks records only the unranked statement.

## 2. Files and main statements (namespace `RamanujanWeil.Arith.Deuring.Geom.G6`)

| file | lines | content |
|---|---|---|
| `DeuringG6Quot.lean` | ~390 | `TranslationQuotient j`, `nonempty_translationQuotient` (07S7), descent `exists_desc_of_fqs`, `comp_q_eq_iff`, `grpObj` (instance), `isMonHom_q`, `isCommMonObj`, `comp_q_eq_one_iff'`, `exists_isMonHom_desc`, `desc_unique`. Works over any base scheme `S` |
| `DeuringG6AbVar.lean` | ~90 | `TranslationQuotient.isAbelianVariety` |
| `DeuringG6Degree.lean` | ~85 | `rank_unique`, `isFiniteLocallyFreeOfRank_q`, `degreeOver_q` (`deg q = rank G`) |
| `DeuringG6Etale.lean` | ~265 | `eq_of_toUnit_comp_eq`, `translate`, `translateHom`, `constModObj`, `smul_mul_right`, `constJ` (+ `isMonHom`, `mono`, `isTranslation`), `exists_eq_constantGroupSchemePoint`, **`exists_quotient_by_finite_subgroup`** |
| `DeuringG6ConstRank.lean` | ~150 | `isFiniteLocallyFreeOfRank_constantGroupScheme` (rank `#H`), **`exists_quotient_by_finite_subgroup'`**: the étale case together with rank, degree, kernel and universal property |
| `DeuringG6Sub.lean` | ~80 | `translationModObj`, **`exists_quotient_by_subgroupScheme`**: any finite locally free `j : G ↪ A` (needed for the p-part, G5) |
| `DeuringG6Axioms.lean` | | `#print axioms` audit |

Statement of `exists_quotient_by_finite_subgroup'`. Let `k` be algebraically closed, `A` an
abelian variety over `k`, and `H ≤ A(k)` a finite subgroup. Then there exist `B`, `GrpObj B`,
`IsAbelianVariety k B`, and `q : A ⟶ B` such that:

* `q` is a homomorphism;
* `q` is finite locally free of rank `#H` and surjective;
* `degreeOver q.left = #H`;
* for every `x : A(k)`, `x ≫ q = 1 ↔ x ∈ H`;
* every homomorphism `α : A ⟶ C` with `h ≫ α = 1` for all `h ∈ H` factors as
  `α = q ≫ β` for a unique homomorphism `β`.

There is no hypothesis relating `#H` to `char k`, and no dimension restriction. In particular
this covers abelian surfaces `E × E'`, which G7 needs.

## 3. How G6 feeds G7/G8 and what remains

* **G7 (Tate).** The quotients `(A×B)/G_n` by `π`-stable subgroups come from
  `exists_quotient_by_finite_subgroup'`. Still to do:
  * descend the Frobenius `π` to `B`. Use the universal property applied to `π ≫ q`, which
    kills `G` because `G` is `π`-stable. About 0.1k lines.
  * the finiteness of isomorphism classes of the quotients. This is the real open input and is
    unchanged by this work.
* **G8 (iii)** (`L(E₀/G)`). Use the kernel, degree and universal property. To identify the
  lattice index with `#G`, the remaining work is to compose with the divisibility statement in
  `DeuringG3Div`. About 0.3–0.6k lines.
* **G5 (p-part).** `exists_quotient_by_subgroupScheme` gives quotients by non-reduced subgroup
  schemes such as `μ_p ⊆ A[p]`. Still missing: constructing those subgroup schemes as
  `GrpObj`s with a mono into `A`, for example the kernel of Frobenius or the connected part of
  `A[p]`. About 0.5–1.5k lines.
* **Optional.** Uniqueness of the quotient up to unique isomorphism. This is immediate from the
  universal property plus `desc_unique`, but not packaged.

Measured cost: about 1.1k lines in total. Each file compiles in 20–60 s of wall time. We built
four missing Stacks oleans once: `ConstantAction`, `ConstantFiniteLocallyFree`, `GenericRank`,
and a reused `FieldTarget`.
