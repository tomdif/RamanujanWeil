# A3-ord, G5: `surj_class`, every lattice class is realized in the isogeny class (2026-11-09)

This is the blueprint and status of the `surj_class` field of
`DeuringClassLattice K t P` (`Arith/DeuringMultCount.lean`), which is G8(iii) in
`ARITH_DEURING_MULT.md` §6.4. New files, audited in `RamanujanWeil/Arith/DeuringG5Axioms.lean`:

| File | Content |
|---|---|
| `Arith/DeuringG5Alg.lean` | pure algebra: `exists_intertwiner` (the `p`-part is empty), `IsFrobFamily`, `conj_of_isFrobFamily`, `colVec`, `isFrobFamily_of_injective`, `det_smul_mem_span_colVec` |
| `Arith/DeuringG5Kernel.lean` | geometry over `k̄`: the descended Frobenius `GlueS.πB`, the cofactor `GlueS.sMap` (`q ≫ s = [n]`, `s ≫ q = [n]`), **the kernel-lattice theorem** (`comp_sMap_mem`, `exists_comp_sMap_eq`, `comp_sMap_injective`, `comm_iff_comp_sMap`), `dim_B`, `q_ne_one` |
| `Arith/DeuringG5Surj.lean` | `lin`, `MinimalOrder`, `CyclicTorsion`, `gammaOf`, **`kernelLattice_iff`**, **`realize`**, named **`WeierstrassDescent`**, **`surjClass_of_descent`** |
| `Arith/DeuringG5Cyclic.lean` | **`cyclicTorsion_of_minimalOrder`** (`CyclicTorsion` is now a theorem), `lin_eq_one_iff`, **`surjClass_of_descent_minimal`** (`surj_class` from `WeierstrassDescent` + `MinimalOrder` only) |

No existing file was edited. No `sorry`, `admit`, `native_decide` or `axiom`.

## 1. The exact statement needed

`Λ` is fixed by G8 (`G8.exists_latticeMatrix`): with a base curve `W₀ ∈ C` and a site `S₀`,

```
∀ W (hW : W.Δ ≠ 0), traceOfFrob W = t →
  ∃ (S : JacSite W) (b : Basis (Fin 2) ℤ (homPi π₀ π_S)), (Λ W).1 = toMatrix b b (piAct π₀ π_S)
```

so `Λ(E) = Hom_π(E₀, E)` with an **arbitrary chosen site** `S` of `W` and arbitrary basis `b`.
`surj_class` asks: `∀ M ∈ TrDet t q, ∃ W ∈ C, ∃ g ∈ GL₂(ℤ), g Λ(W) g⁻¹ = M`. Two consequences:

* **The site is not under our control.** Whatever curve `W` we produce, its Jacobian is
  computed in the site that `Λ` chose. So the geometric input must give the identification
  `(J_{W,S}, π_S) ≅ (E₀/Γ, π_Γ)` for **every** site `S` of `W` (built into
  `WeierstrassDescent`).
* **`End_π(E₀)` must be `ℤ[π]` (important correction).** `Hom_π(E₀, E)` is a module over
  `O₀ = End_π(E₀)` by precomposition. If `O₀ ⊋ ℤ[π]`, then every `Λ(E)` is an `O₀`-module, and
  the class of the companion matrix (the lattice `ℤ[π]` itself) is **never** realized. In that
  case `surj_class` is false. So the base curve `W₀` in G8's `exists_latticeMatrix` cannot be
  arbitrary: it has to be chosen with `End_π(J_{W₀}) = ℤ[π]` (`MinimalOrder`). Such a curve
  exists in every ordinary class (Deuring/Waterhouse: all orders `ℤ[π] ⊆ O ⊆ O_K` occur). This
  is the "descend to the curve with `End = ℤ[π]`" step of route L, and it is a hypothesis of
  the assembly, not of G5 itself (§5, `ExistsMinimalBase`).

## 2. Algebra: the `p`-part is empty in the ordinary case (`DeuringG5Alg`, proved)

`exists_intertwiner`: if `M, M₁ ∈ M₂(ℤ)` have the same trace and determinant and the prime `p`
does not divide `disc = tr² − 4 det`, there is `X` with `M₁ X = X M` and `p ∤ det X`.

Proof. `P_v = [v | Mv]` satisfies `M P_v = P_v C` (`C` the companion matrix, Cayley–Hamilton).
`det P_v` is the binary form `c x² + (d−a) x y − b y²` of discriminant `disc`. So `p` cannot
divide its values at `(1,0), (0,1), (1,1)` simultaneously. Then `X = P₁ · adj(P)`, with
`det X = det P₁ · det P`.

For `q = p^f` and `p ∤ t`, `disc = t² − 4q ≡ t² (mod p)`, so the hypothesis holds. **Every
`ℤ[π]`-lattice class is represented by a sublattice of `L(E₀)` of index prime to `p`.** So the
connected/inseparable part (`μ_p`-type kernels, the canonical subgroup, connected–étale
splitting) is **not needed** for `surj_class`. All kernels are étale, of order prime to `p`, and
the G6 étale quotient `exists_quotient_by_finite_subgroup'` (via G7 `Glue`) suffices.
(Conceptually: `ℤ_p[π] ≅ ℤ_p × ℤ_p` is maximal, so all `ℤ_p[π]`-lattices are principal.)

Linear algebra: `colVec b X` (the columns of `X` in a basis `b` of `L`) span a `f`-stable
sublattice `L'` (`map_colVec`), with `det X · L ⊆ L'` (`det_smul_mem_span_colVec`). If
`Φ : V ↪ L` intertwines `F` and `f` and has range `L'`, then `V` has a basis on which `F` has
matrix `M` (`isFrobFamily_of_injective`), so `F`'s matrix on **any** basis is
`GL₂(ℤ)`-conjugate to `M` (`conj_of_isFrobFamily`).

## 3. Geometry over `k̄`: kernel lattices (`DeuringG5Kernel`, proved)

Setting: `A₀, A` one-dimensional, `Γ ⊆ A(k)` finite, `π`-stable, killed by `n` (`n` invertible
in `k`), `G : Glue Γ` (`q : A → B = A/Γ`).

* `GlueS.πB`: `π` descends (`q ≫ π_B = π ≫ q`), and any descended endomorphism equals it
  (`eq_πB`).
* `GlueS.sMap`: `s : B → A` with `q ≫ s = [n]`, `s ≫ q = [n]`, `s ≫ π = π_B ≫ s`; `dim B = 1`.
* **Kernel-lattice theorem.** `g ↦ g ≫ s` is a bijection from homomorphisms `A₀ ⟶ B` onto
  `{β : A₀ ⟶ A | β(A₀(k)[n]) ⊆ Γ}` (`comp_sMap_mem`, `exists_comp_sMap_eq` via G3-div
  `exists_isMonHom_zpow_comp_eq`, `comp_sMap_injective` via G7-dual `cancel_of_ne_one`).
  Equivariance is preserved and reflected (`comm_iff_comp_sMap`). So
  `Hom_π(A₀, A/Γ) ≅ L_Γ = {β ∈ Hom_π(A₀, A) : β(A₀[n]) ⊆ Γ}` as `ℤ[π]`-modules.

## 4. Realization over `k̄` and the named inputs (`DeuringG5Surj`)

Base curve conditions (on `(A₀, π₀)`):

```lean
def MinimalOrder : Prop := ∀ e : A₀ ⟶ A₀, IsMonHom e → e ≫ π₀ = π₀ ≫ e → ∃ a b : ℤ, e = lin π₀ a b
def CyclicTorsion (n : ℤ) : Prop :=
  ∃ P : Pt A₀, P ^ n = 1 ∧ (∀ x, x ^ n = 1 → ∃ a b, x = P ≫ lin π₀ a b) ∧
    ∀ a b, P ≫ lin π₀ a b = 1 → n ∣ a ∧ n ∣ b
```

(`lin π₀ a b = [a] + π₀^b`, written multiplicatively `(𝟙)^a * π₀^b`.) `CyclicTorsion n` says
that `A₀(k)[n]` is free of rank one over `ℤ[π₀]/n`.

`gammaOf P L' = {P ≫ β : β ∈ L'}`. **`kernelLattice_iff`** (proved): given `MinimalOrder`,
`CyclicTorsion n` and a `π`-stable `L' ⊇ n·End_π(A₀)`, `L_{gammaOf P L'} = L'`.

**`realize`** (proved): for `M`, a basis `b₁` of `End_π(A₀)` with matrix `M₁`, `M₁ X = X M`,
`det X` invertible in `k`, `MinimalOrder` and `CyclicTorsion (det X)`, there is a finite
`π₀`-stable `Γ` killed by `det X` such that for every `(B', π')` equivariantly isomorphic to the
quotient `(A₀/Γ, π_Γ)`, the matrix of `π'` on **any** basis of `Hom_π(A₀, B')` is conjugate to
`M`.

**`WeierstrassDescent K` (named, the geometric heart).** For elliptic `W₀/𝔽_q`, a site `S₀`, a
finite `π₀`-stable `Γ ⊆ J₀(K̄)` killed by `n` prime to `p`, the G6 quotient `G` and a descended
`π_B`: there is an elliptic `W/𝔽_q` with `a_W = a_{W₀}` such that **for every site `S` of
`W`**, `(J_{W,S}, π_S) ≅ (G.B, π_B)` as group objects, equivariantly.

**`surjClass_of_descent`** (proved): `WeierstrassDescent K`, `MinimalOrder` and
`CyclicTorsion n` (all `n` prime to `p`) for `(J_{W₀}, π₀)`, `W₀ ∈ C`, ordinary `t`, and any
`Λ` with the G8 specification give

```lean
∀ M : TrDet t (Nat.card K), ∃ W, IsogClassPred C W ∧ ∃ g : GL2, g • Λ W = M
```

This is exactly the `surj_class` field. Class membership is proved: `e ≫ s : J_W → J₀` is a
nontrivial equivariant homomorphism, which is an `IsogStep`.

## 4a. Cyclic torsion (`DeuringG5Cyclic`, proved, 2026-11-09 second session)

```lean
theorem cyclicTorsion_of_minimalOrder (hA₀ : abelianVarietyDimension A₀ = 1)
    (hmin : MinimalOrder π₀) (hind : ∀ a b : ℤ, lin π₀ a b = 1 → a = 0 ∧ b = 0)
    (n : ℤ) (hn : IsUnit (n : k)) : CyclicTorsion π₀ n
```

`hind` (`ℤ[π] ↪ End`) holds for every Frobenius Jacobian (`lin_eq_one_iff`, from G8's
`eq_zero_of_zpow_mul_zpow_eq_one` and `t² < 4q`). Proof:

* **prime `ℓ`** (`exists_annTriv_prime`): `A₀(k)[ℓ]` is an `𝔽_ℓ`-vector space
  (`AddCommGroup.zmodModule`) and `π₀` acts linearly. `exists_cyclic_or_scalar` (pure algebra,
  Mathlib's `LinearMap.exists_eq_smul_id_of_forall_notLinearIndependent`): either some `v` has
  `v, π₀v` independent, or `π₀` is a scalar `c` on `A₀[ℓ]`. (Lean note: the `ZMod ℓ`-module
  structure must be a *variable* of that lemma; with a `letI` from `zmodModule` in the same
  proof, coercions of `toZModLinearMap` fail with "function expected".) Then `π₀ − c = [ℓ] ≫ e` (G3-div), `e` commutes with `π₀`
  (cancel `[ℓ]`, G7-dual `cancel_of_ne_one`), so `e = a + bπ₀` by `MinimalOrder` and
  `(ℓb − 1)π₀ + (ℓa + c) = 0`, contradicting `hind`.
* **prime powers** (`ann_of_root`): a point `P` with `ℓ^{j}P = v` has trivial annihilator in
  `ℤ[π₀]/ℓ^{j+1}` (induction on `j`, dividing `a`, `b` by `ℓ` each step).
* **coprime products** (`annTriv_mul`): `P + Q`; then `Nat.recOnPrimeCoprime`.
* **generation** (`gen_of_ann`): `(ℤ/N)² → A₀[N]`, `(a, b) ↦ (a + bπ₀)P` is injective, and both
  sides have `N²` elements (Stacks `nonempty_torsionBy_addEquiv_of_isUnit`, any `N` invertible in
  `k`), so it is onto. No CRT on torsion groups is needed.

`surjClass_of_descent_minimal` is `surjClass_of_descent` with the `CyclicTorsion` hypothesis
discharged.

## 5. Remaining named Props and estimates

| Prop | Content | Route | Estimate |
|---|---|---|---|
| `WeierstrassDescent K` | `𝔽_q`-model of `J₀/Γ` in Weierstrass form, with `(J_W, π_W) ≅ (J₀/Γ, π_Γ)` for every site | (a) Weierstrass model over `K̄`: `B` is a genus-one curve with origin; `h⁰(nO) = n` from G1RR-style Riemann–Roch (Tag 0B90 already used for degree 1), embedding by `|3O|` → plane cubic → `familyIsoEquiv` gives a `WeierstrassCurve K̄`. (b) `π_B` as a twisted Frobenius: `π_B = aj ∘ φ ∘ aj⁻¹` must be shown to come from a semilinear `Ψ` on the model; with G1.1′ this is the statement that the coordinate change `γ` with `γ·W'^{(q)} = W'` exists. (c) Lang/Hilbert 90 for `VariableChange(K̄)` (solve `u^{q−1} = c` and Artin–Schreier `r^q − r = c`, all solvable in `K̄`) to make `W'` `𝔽_q`-rational, then `geomIsoEquiv` / `frobIsoEquiv`. (d) site independence: `JacSite.J` for two sites containing `E_W` are equivariantly isomorphic (Yoneda on representing objects). | 2–3.5k; (a) ~1–1.5k is the riskiest; (d) 0.2–0.4k |
| ~~`CyclicTorsion π₀ n`~~ | **proved** (§4a, `cyclicTorsion_of_minimalOrder`, ~300 lines) | n/a | done |
| `MinimalOrder π₀` | base curve with `End_π(E₀) = ℤ[π]` | Existence in each class (`ExistsMinimalBase`): from any `E₁` with `End = O ⊋ ℤ[π]`, quotient by a suitable cyclic `π`-stable subgroup of order `f = [O : ℤ[π]]` prime to `p`; this uses the same kernel-lattice machinery (§3) plus `WeierstrassDescent` | 0.5–1k on top of the above |

What G5 no longer needs: the `p`-part (connected–étale splitting, Frobenius kernels, the
non-reduced quotient `exists_quotient_by_subgroupScheme`), ℓ-adic Tate modules, and Vélu.

**Total remaining for `surj_class`: ~2.5–4.5k lines**, dominated by `WeierstrassDescent`(a)–(b).
`surj_class` now depends on exactly two inputs: `WeierstrassDescent K` (geometry) and
`MinimalOrder` for the chosen base curve (which is itself `ExistsMinimalBase`, again through
`WeierstrassDescent` and the kernel lattices). The reduction (~950 lines) is complete and
axiom-clean.

Note on (d), site independence. The obvious route is `J_S ≅ E_W ≅ J_{S'}` via the two
Abel–Jacobi isomorphisms (`JacSite.ajIso`, both curve objects are `Over.mk (gw W)`), which is
`π`-equivariant by `JacSite.π_eq`. What is missing is that this pointed isomorphism is a
homomorphism: G1's `Rigid.isMonHom_transport` proves rigidity only for two curves in the
**same** site (through the Picard functor of that site), and Stacks has no general
"pointed morphism of abelian varieties is a homomorphism". Either a general rigidity lemma
(~0.3–0.5k) or a comparison of Picard functors across sites is needed.

## 6. Coordination with G8

* `surjClass_of_descent` / `surjClass_of_descent_minimal` take G8's `Λ` specification verbatim (`homPi`, `piAct`,
  `JacSite.frobeniusJacobian`), so it plugs into whatever `DeuringClassLattice` G8 builds from
  `exists_latticeMatrix`. **G8 must choose `W₀` with `MinimalOrder`** (§1). `rel_iff` and
  `card_stab` also need this (G8(ii) surjectivity
  `Hom_π(E, E') ≅ Hom_{ℤ[π]}(L E, L E')` fails without `End_π(E₀) = ℤ[π]`).
* With `MinimalOrder`, the G8 basis of `End_π(E₀)` can be taken to be `(1, π₀)`, with
  companion matrix. `surjClass_of_descent` works with any basis.

## 7. Axiom audit and build notes

`nice -n 10 lake build RamanujanWeil.Arith.DeuringG5Axioms` (21 `#print axioms`, now importing
`DeuringG5Cyclic`): every audited declaration depends only on
`[propext, Classical.choice, Quot.sound]`.

Fixes to the predecessor's `DeuringG5Surj`: `γ` renamed (it is a reserved token there), a
redundant `exact` removed, and `surjClass_of_descent` runs under
`set_option maxHeartbeats 800000` (the final `hreal' b` unifies two `homPi` types over concrete
Jacobians and unfolds `JacSite.frobeniusJacobian`; removing the `set J₀` does not help).
