# A3-ord, G7-D-geom: the theta group of 𝒪(N·O), constructed (2026-11-10)

This continues `ARITH_DEURING_G7D.md` (§3, item **D-geom**). New files only, audited in
`RamanujanWeil/Arith/DeuringG7DGeomAxioms.lean`:

| File | Imports | Content |
|---|---|---|
| `Arith/DeuringG7DGeomTrans.lean` | Mathlib only | translations `τ_P = t_P^*` on the function field `F(E)`, with `τ_P ∘ τ_Q = τ_{P+Q}` |
| `Arith/DeuringG7DGeomTheta.lean` | Trans, WeilHeis | the theta group `𝒢(L)` as a `CentralExt` with kernel `F^×`; `L(N·O)` |
| `Arith/DeuringG7DGeomKer.lean` | Theta | `K(L) = E[N]` via Abel–Jacobi (Mathlib's `toClass`), given the named divisor bridge; Heisenberg seam |
| `Arith/DeuringG7DGeomFamily.lean` | Ker, DFinal, Ihara.PointsCurve | the constructed `ThetaFamily S.J ℓ`; `PrincipallyPolarized`; the split seam |
| `Arith/DeuringG7DGeomAxioms.lean` | | audit |

## 0. Summary

The theta group is now a **constructed object**, not an existential. It is built from the elliptic
curve itself, using the cheapest path the survey suggested: divisors and functions.

* The function field `K = F(E)` of `E = W⁄F` is Mathlib's `FunctionField`. Translations
  `τ_P : K ≃ₐ[F] K` are built through the **generic point** `ξ ∈ E(K)`, so their composition law
  is the associativity of Mathlib's group `E(K)`. No addition formula is expanded.
* `𝒢(𝒪(D))` is the stabilizer of the Riemann–Roch space `V = L(D)` in `K^× ⋊ E(F)`, where
  `(f, P)` acts by `V ↦ f · τ_P(V)`. Its kernel is `F^×`. That is `Γ(𝒪)^× = F^×`, proved by
  integrality.
* `ThetaFamily S.J ℓ` is **`thetaFamilyOf`**: `G_n = 𝒢(𝒪(ℓⁿ⁺¹·O))` on `E = W̄⁄k̄`, transported to
  `J_W[ℓⁿ⁺¹]`. It takes three small named inputs (`DGeomGaps`), listed in §4.
* The seam `ThetaDescentFiniteness` is split as recommended: **`ThetaLevelDescent`** (descent)
  and **`PrincipalFiniteness`** (Θ + J + C). Both are stated for the constructed families and
  the concrete `PrincipallyPolarized` predicate.

```lean
theorem thetaDescentFiniteness_of_split (hG : DGeomGapsAll K) (hD : ThetaLevelDescent K)
    (hP : PrincipalFiniteness K) : ThetaDescentFiniteness K
theorem deligneBound_of_split (h : DGeomSplitAll) : RamanujanTau.DeligneBound
```

## 1. Translations (`DeuringG7DGeomTrans`, fully proved)

Setting: `W : Affine F` elliptic, `E = W⁄F`, `R = F[E]`, `K = F(E)`.

* `coordHom x y h : R →ₐ[F] L` is the universal property of `R`: an `L`-point `(x, y)` gives
  `X ↦ x, Y ↦ y`. Maps out of `R` are determined by `X, Y` (`rg_algHom_ext`), and maps out of
  `K` likewise (`kf_algHom_ext`).
* **`coordHom_injective`**: if `x` is transcendental, `p + qY ↦ 0` makes `x` a root of the norm
  `p² − pq(a₁X + a₃) − q²(X³ + …)` (Mathlib's `norm_smul_basis`). So the norm is `0`, and
  hence `p + qY = 0`.
* `genPt = ξ = (x, y) ∈ E(K)`. `transcendental_genX` holds because `F[X] ⊆ R ⊆ K`.
* `transPt P = ξ + P_K`. It is never `0`, because `ξ` is not defined over `F`.
* **`transcendental_transX`**: suppose `x(ξ + P_K)` were algebraic. Then so is `y`
  (`isIntegral_y`), so `ξ + P_K` lifts to `E(F')`, with `F'` the algebraic closure of `F` in `K`.
  Then `ξ = (ξ + P_K) + (−P)_K` lifts too, which contradicts the transcendence of `x`.
* `trans P = τ_P : K →ₐ[F] K` is `IsFractionRing.liftAlgHom` of `X ↦ x(ξ + P), Y ↦ y(ξ + P)`.
  **`map_trans_genPt`**: `τ_P(ξ) = ξ + P_K`.
* **`trans_comp`**: `τ_P ∘ τ_Q = τ_{P+Q}`. Apply `Point.map` (a group homomorphism fixing
  `E(F)`):
  `(τ_P τ_Q)(ξ) = τ_P(ξ + Q_K) = ξ + P_K + Q_K`.
  `trans_zero` gives `τ_0 = id`, and `transAut : Multiplicative E(F) →* (K ≃ₐ[F] K)`.

## 2. The theta group (`DeuringG7DGeomTheta`, fully proved)

**Why the model is correct.** Let `L = 𝒪(D)` with `D = N·O` and `N ≥ 2`.

* An isomorphism `t_P^*L ≅ L` is multiplication by an `f` with `div f = t_P^*D − D`.
* `τ_P L(D) = L(t_P^*D)`, and `f · L(D') = L(D' − div f)`.
* `|N·O|` is base-point free for `N ≥ 2`, so `L(D')` determines the degree-`N` divisor
  `D' ~ D`.

Hence `div f = t_P^*D − D ⟺ f · τ_P(L(D)) = L(D)`, and Mumford's
`𝒢(L) = {(P, φ : t_P^*L ≅ L)}` is the stabilizer below. Its law
`(f, P)(g, Q) = (f · τ_P g, P + Q)` is the composition of the isomorphisms.

* `unitsTrans : E(F) →* MulAut K^×` gives the semidirect product `Amb = K^× ⋊ E(F)`.
  `thetaAct (f, P) = f · τ_P(−)` is multiplicative (`thetaAct_mul`).
* **`thetaGroup V`** is the stabilizer of a subspace `V`. **`thetaKer V`** is its image in
  `E(F)`, the subgroup `K(L)`.
* **`const_of_map_mulLeft`**: suppose `F = F̄`, `1 ∈ V` and `dim V < ∞`. If `f · V = V`, then
  `f ∈ F`. (The powers of `f` lie in `V`, so `f` is integral.) This is `Γ(𝒪)^× = F^×`.
* **`thetaExt V : CentralExt (thetaGroup V) (thetaKer V) (Additive Fˣ)`** is the extension
  `1 → F^× → 𝒢 → K(L) → 0`. Exactness is `const_of_map_mulLeft`, and centrality holds because
  `τ_P` fixes constants.
* `rrSpace W N = L(N·O) = span{xⁱ : 2i ≤ N} ∪ {xʲy : 2j + 3 ≤ N}`. It is finite-dimensional
  and contains `1`. **`thetaExtN W N`** is `𝒢(𝒪(N·O))`.

## 3. `K(L) = E[N]` and the Heisenberg seam (`DeuringG7DGeomKer`)

* **`isPrincipal_XYIdeal'_pow_iff`** (proved; Abel–Jacobi in Mathlib's form):
  `m_Q^N` is principal `⟺ N·Q = 0`. It follows from `ClassGroup.mk_eq_one_iff` and from
  Mathlib's injective homomorphism `Point.toClass : E(F) → Cl(F[E])`.
* **`RRStabilizerBridge W N`** (named). For `Q = (x, y) ≠ O`:
  `−Q ∈ K(L(N·O)) ⟺ m_Q^N` is principal.
  Mathematically, `f · τ_{−Q} L(N·O) = L(N·O)` iff `div f = N[Q] − N[O]` iff `(f) = m_Q^N` as
  fractional ideals of `F[E]`; the order at `O` is forced by degree `0`. What is missing is a
  divisor/valuation theory on Mathlib's Weierstrass curves: `ord_Q` at every point, including
  `O`, and the compatibility `ord_Q(τ_P f) = ord_{Q+P}(f)`.
* **`thetaKer_eq_torsion`** (proved from the bridge): `K(L) = E[N]`, i.e. `t_P^*L ≅ L ⟺ N·P = 0`.
* **`ThetaHeisenberg W N`** (named): the center of `𝒢(𝒪(N·O))` lies over `O`. In other words,
  the commutator pairing, which is the Weil pairing `e_N`, is nondegenerate.
* `CentralExtTransport.transport` moves a central extension of `K` along `K ≃+ K'`.

## 4. The constructed theta family (`DeuringG7DGeomFamily`)

* `Wbar W = W⁄k̄`. The points of `W̄⁄k̄` are those of `W⁄k̄` definitionally, which is the target
  of `Ihara.fvpEquivPoint`.
* `curvePtFvp` (proved) reads a section `z` of `E_W → Spec k̄` as a `k̄`-valued point of the
  Weierstrass scheme.
* **`AbelJacobiMathlib S`** (named): there is an additive bijection `e : E(k̄) ≃+ J_W(k̄)` with
  `e(fvpEquivPoint (curvePtFvp z)) = z ≫ aj`. It says that Mathlib's chord–tangent law is the
  Jacobian's law under `P ↦ 𝒪(P − O)`. G1 has `aj` as an isomorphism of schemes; what is
  missing is the comparison of the two group laws.
* `torEquiv` restricts `e` to `N`-torsion.
* **`DGeomGaps W S ℓ`** is `AbelJacobiMathlib ∧ ∀ n, RRStabilizerBridge ∧ ∀ n, ThetaHeisenberg`.
* **`thetaFamilyOf h : ThetaFamily S.J ℓ`** has `G n = 𝒢(𝒪(ℓⁿ⁺¹·O))` (`thetaFamilyOf_G`,
  `rfl`), with `K(L) = E[ℓⁿ⁺¹]` transported by `e` to `J_W[ℓⁿ⁺¹]`.

### The Θ interface: `PrincipallyPolarized`

```lean
def PrincipallyPolarized (k) (B : Over (Spec (.of k))) : Prop :=
  ∃ (L : B.left.Modules) (_ : Stacks.Ample.IsInvertibleModule B.left L),
    Stacks.Ample.IsAmple B.left L ∧ Module.finrank k Γ(L, ⊤) = 1
```

Here `Γ(L, ⊤)` is a `k`-module through `B → Spec k`, by Stacks' `globalSectionsModule`, the
structure used by the genus-2 pencil files. This predicate is **the interface** between descent
and Θ. Θ must prove that such a `B` is a Jacobian (or a product).

## 5. The split seam

* **`ThetaLevelDescent K`** (descent, named). Take the constructed `thetaFamilyOf` for `J_W`
  and `J_{W'}`, and a level structure (`GraphLevel`) over `graph(v_n)`. Then every
  `B_n = (J × J')/Γ_n` (G6 `Glue`) is `PrincipallyPolarized`.
  Mathematically: Mumford §23 Thm 2 descends `L ⊠ L'` to `B_n`, with
  `𝒢(L_n) = Z(Γ̃)/Γ̃`, which is trivial by `centralizer_of_antiIsom`.
* **`PrincipalFiniteness K`** (Θ + J + C, named). A `π`-equivariant family of principally
  polarized `B_n` has `n ≠ m` with `B_n ≅ B_m` equivariantly.
* **`thetaDescentFiniteness_of_split`**: `DGeomGapsAll ∧ ThetaLevelDescent ∧
  PrincipalFiniteness ⇒ ThetaDescentFiniteness` (proved). **`deligneBound_of_split`** applies it
  at every finite field.

## 6. What remains

| Item | Content | Estimate |
|---|---|---|
| `RRStabilizerBridge` | valuations `ord_Q` on `F(E)` at all points (affine via the Dedekind `F[E]`, `O` via degree); `ord_Q ∘ τ_P = ord_{Q+P}`; `L(D)` determines `D` for base-point-free `D` | 1.5–2.5k |
| `ThetaHeisenberg` | nondegeneracy of `e^L` (Weil pairing via functions, or `|K(L)| = deg(Λ_L)` + Riemann–Roch) | 1–2k |
| `AbelJacobiMathlib` | Mathlib's chord–tangent law agrees with `J_W(k̄) = Pic⁰(E_W)` under `aj` | 1–1.5k |
| `ThetaLevelDescent` | module descent along the G6 `Glue` quotient (equivariant structures, Mumford §12), and `𝒢(L_B) = Z(Γ̃)/Γ̃`; ampleness and `h⁰ = 1` of `L_n` | 2.5–4k |
| `PrincipalFiniteness` | Θ (4–7k), J (2–4k), C-descent (0.5–1k), C-Jac (other agent) | as in `ARITH_DEURING_G7D.md` §3 |

The `F(E)` model is not the `L ≅ t_x^*L` of Stacks' `Pic`. Bridging the two is part of
`ThetaLevelDescent`: the level subgroup acts on the actual module `L ⊠ L'` on `J × J'`. The
transfer is through `aj` and the G1 Picard identification.

## 7. Audit

`nice -n 10 lake build RamanujanWeil.Arith.DeuringG7DGeomAxioms` succeeds (2026-11-10). All 16
audited declarations depend only on `[propext, Classical.choice, Quot.sound]`; `transport` uses
only `[propext, Quot.sound]`. The audited declarations include:
* `trans_comp`;
* `const_of_map_mulLeft`;
* `thetaExt`;
* `thetaKer_eq_torsion`;
* `thetaFamilyOf`;
* `thetaDescentFiniteness_of_split`;
* `deligneBound_of_split`.

There is no `sorry`, `admit`, `native_decide` or `axiom`. No existing file was edited, and
`RamanujanWeil.lean` is unchanged.

Build times: Trans, Theta and Ker take ≈ 10 s each (Mathlib and WeilHeis only). Family takes
≈ 4 min, mostly import loading.
