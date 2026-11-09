# A3-ord, G1 session 3: Frobenius compatibility (G1.1′), rigidity (G1.2) and the G1 assembly (G1.4)

This continues `docs/ARITH_DEURING_G1_2.md` §3. This session proves **G1.1′** (the Abel–Jacobi
map intertwines the Frobenii), **`aj(O) = 0` in `η` form**, **G1.2** (rigidity in dimension
one, by transport through `aj`), and **G1.4** (Ψ-equivariant pointed isomorphisms of the cubics
= π-equivariant isomorphisms of group objects of the concrete Jacobians), all
**unconditionally**. No named Prop hypothesis is introduced.

All new files are axiom-clean: only `propext`, `Classical.choice`, `Quot.sound`, with no
`sorry`/`admit`/`native_decide`/`axiom`. The audit file is
`RamanujanWeil/Arith/DeuringG1Axioms3.lean`. No existing file was edited.

| File | Imports |
|---|---|
| `Arith/DeuringG1Frob.lean` | `DeuringG1Point`, Stacks `Picard.SymmetricPower.AbelMap`, `Picard.HilbertFamilyPicardClass` (both prebuilt) |
| `Arith/DeuringG1Rigid.lean` | `DeuringG1Frob` |
| `Arith/DeuringG1Assembly.lean` | `DeuringG1Rigid` |
| `Arith/DeuringG1Axioms3.lean` | audit |

Build: `nice -n 10 lake build RamanujanWeil.Arith.DeuringG1Axioms3` (each file about 3–5 min,
mostly import loading). No new Stacks module had to be built.

## 1. G1.1′: `aj ≫ π = φ ≫ aj` (`DeuringG1Frob.lean`)

### 1a. Inverse images of graphs (namespace `Frob`, any base `S`)

| Name | Statement |
|---|---|
| **`Frob.pointIdeal_comap_of_comm`** | Let `h : X'_{T'} ⟶ X_T` satisfy `h ≫ pr₁ = pr₁ ≫ Ψ` (`Ψ` a monomorphism) and `h ≫ pr₂ = pr₂ ≫ g`. If `x' ≫ Ψ = g ≫ x`, then `(pointIdeal X T x).comap h = pointIdeal X' T' x'` (when the graph of `x` is a closed immersion). Proof: `ker_fst_of_isClosedImmersion` and an explicit inverse of `T' ⟶ T' ×_{X_T} …`, using that `Ψ` is mono. |
| `Frob.schemePullbackClass_sub` | pullback of Picard classes commutes with `−`. |

### 1b. The general statement (any pointed curve with a twisted Frobenius)

Setting: Stacks' `JacobianFrobenius` setting (`Ψ ≫ f = f ≫ F^n_k`, `IsSepClosed k`,
representable Picard functor) plus `φ : X ⟶ X` over `k`.

| Name | Statement |
|---|---|
| **`Frob.abelJacobi_comp_jacobianFrobenius`** | `[Mono Ψ]`, `φ ≫ f = f`, `φ ≫ Ψ = F^n_X`, `σ ≫ Ψ = F^n_k ≫ σ` ⟹ `abelJacobi ≫ jacobianFrobenius Ψ = Over.homMk φ ≫ abelJacobi`. |

Proof: compare the classes at the universal point `T = X` (`jacobianHomAddEquiv` is injective).
The left side is `Θ_X^*([Δ] − [c₀ × X])` (`jacobianHomAddEquiv_comp_jacobianFrobenius`), the
right side `(1 × φ)^*([Δ] − [c₀ × X])` (`classifyingMap_comp`). By 1a both inverse images of `Δ`
are the graph of `φ` (`Θ_X = Ψ × F^n_X` and `φ ≫ Ψ = F^n_X`), and both inverse images of
`{c₀} × X` are `{c₀} × X` (`Ψ` fixes `c₀`, `φ` is over `k`). Stacks'
`schemePullbackClass_picardClass_of_eq_comap` (Tag 0C4U) turns the ideal equalities into
equalities of classes. No `K̄`-point argument and no morphism-level `point_ext` is needed.

### 1c. For a Weierstrass curve (namespace `Jac`)

| Name | Statement |
|---|---|
| `geomFrob W` | `φ_W = geometricFrobeniusBaseChangePow (Yw W) K̄ p f _ 1`, the `K̄`-linear Frobenius of `E_W`; `geomFrob_comp_gw`. |
| `twist_comp_geomFrob`, `geomFrob_comp_twist` | `Ψ_W ≫ φ_W = F^f = φ_W ≫ Ψ_W`. |
| `isDominant_absoluteFrobeniusPow`, `isDominant_geomFrob` | the absolute Frobenius is the identity on points, so `φ_W = F ≫ Ψ⁻¹` is dominant. |
| `isReduced_Ew`, `isSeparated_gw` | `E_W` is reduced, `E_W ⟶ Spec K̄` separated. |
| `twist_comp_gw`, `frob_comp_specAlgebraMap` | `Ψ_W` lies over `F_{K̄}`; `F_{K̄}` fixes `Spec K̄ ⟶ Spec k`. |
| **`zeroPt_comp_twist`** | `O ≫ Ψ_W = F_{K̄} ≫ O`: the twisted Frobenius fixes the zero section. |
| **`twist_comm_iff_geomFrob_comm`** | for `α : E_{W'} ⟶ E_W` over `K̄`: `α ≫ Ψ_W = Ψ_{W'} ≫ α ↔ α ≫ φ_W = φ_{W'} ≫ α`. (⇒) cancel the iso `Ψ_W`; (⇐) both sides agree after the dominant `φ_{W'}` and over `Spec K̄`, so Mathlib's `ext_of_isDominant_of_isSeparated` applies. |
| `JacSite.geomFrobO` | `φ_W` in `Over (Spec K̄)`. |
| **`JacSite.aj_comp_π`** | **G1.1′**: `S.aj ≫ S.π = S.geomFrobO ≫ S.aj`. |
| `JacSite.π_eq` | `S.π = inv S.aj ≫ S.geomFrobO ≫ S.aj`. |

## 2. `aj(O) = 0` in `η` form (`DeuringG1Frob.lean`)

| Name | Statement |
|---|---|
| `Abel.basePtO` | `c₀` as `𝟙_ (Over (Spec k)) ⟶ X` (the image of `basePt` under `Over.post`; `post.obj baseObj` is `𝟙_` definitionally); `basePtO_left : (basePtO …).left = σ`. |
| **`Abel.basePtO_comp_abelJacobi`** | genus one: `basePtO ≫ abelJacobi = η[J]`. From `jacobianHomAddEquiv_basePt_comp_abelJacobi` and `η = 1` in the hom-group of the unit (`Hom.one_def`, `toUnit_unique`). |
| `JacSite.zeroO`, `zeroO_left` | `O` as a point over `Spec K̄`. |
| **`JacSite.zeroO_comp_aj`** | `S.zeroO ≫ S.aj = η[S.J]`. |

## 3. G1.2: rigidity in dimension one (`DeuringG1Rigid.lean`, namespace `Rigid`)

Setting: two curves `X, X'` in the **same** big fppf site, each with Stacks' instances, base
points `σ, σ'`, genus one; `α : X' ⟶ X` an isomorphism over `k` with `σ' ≫ α = σ`.

| Name | Statement |
|---|---|
| `transportBase T` | `β_T = α⁻¹ × 1_T : X_T ⟶ X'_T`; `_fst`, `_snd`, `baseChangeMap_transportBase` (naturality). |
| `transportPresheafMap`, `transportMap` | `β^*` on `T ↦ Pic(X'_T)`, and its sheafification `N : Pic_{X'/k} ⟶ Pic_{X/k}` (same construction as Stacks' `twistedPicardMap`); `transportMap_toPicardFunctor`, `transportMap_naturality`. |
| `transportMap_add`, `_zero`, `_sub` | `N` is additive (Tag 0B9N surjectivity, as for `twistedPicardMap_add`). |
| `transportHom`, `post_map_transportHom` | `α` as a morphism of test schemes. |
| **`transportMap_univ`** | `N[𝒪(Δ')] = α^*[𝒪(Δ)]` in `Pic_{X/k}(X')`: both are the graph of `α` (`Frob.pointIdeal_comap_of_comm` twice). |
| **`transportMap_constClass`** | `N[c₀']_T = [c₀]_T` (uses `σ' ≫ α = σ`). |
| `transport` | `e = aj'⁻¹ ≫ α ≫ aj : J' ⟶ J`; `abelJacobi_comp_transport`. |
| **`jacobianHomAddEquiv_comp_transport`** | on `T`-points, `z ↦ z ≫ e` is `N`. Every `z : T ⟶ J'` is `m ≫ aj'` (`bijective_comp_abelJacobi` + `degreeOneNormalized`), and then both sides are `(m ≫ α)^*[Δ] − [c₀]_T`. |
| `degreeZeroHomAddEquiv_comp_transport`, **`isMonHom_transport_site`** | the same at site level; `e₀ = post⁻¹(e)` is a homomorphism (`η` and `μ` checked on points, as in Stacks' `isMonHom_twistedJacobianHom`). |
| **`isMonHom_transport`** | **G1.2**: `IsMonHom (aj'⁻¹ ≫ α ≫ aj)`. |

So "every pointed morphism of the curve fixing `O` is a homomorphism" is proved in the form
needed: for a pointed **isomorphism** of genus-one curves, the induced map of Jacobians is a
homomorphism; the case `X = X'` gives pointed automorphisms. (A non-invertible pointed
endomorphism is not needed by G1.4; the same proof works with `β_T = (graph-pullback)` but would
need the pullback of `[𝒪(Δ)]` along a non-flat `α × 1`, which is not set up here.)

## 4. G1.4: assembly (`DeuringG1Assembly.lean`)

| Name | Statement |
|---|---|
| `conj_comm_iff_of_comm` | category lemma: if `aj ≫ π = φ ≫ aj`, `aj' ≫ π' = φ' ≫ aj'` (isos), then `(aj'⁻¹ ≫ a ≫ aj) ≫ π = π' ≫ (aj'⁻¹ ≫ a ≫ aj) ↔ a ≫ φ = φ' ≫ a`. |
| `Jac.PairSite W W'`, `nonempty_pairSite` | a big fppf site containing `E_W`, `E_{W'}`, `Spec K̄`. |
| `PairSite.fL/fR`, `JL/JR`, `ajL/ajR`, `πL/πR`, `φL/φR` | the two curves, Jacobians, Abel–Jacobi isomorphisms, Frobenii and geometric Frobenii, all written with the **same** site terms `P.B`, `P.hk` (instances `iL1`–`iR6` re-export the `JacSite` instances). They are definitionally `P.left.J`, `P.left.π`, … for `P.left = ⟨P.B, P.hX, P.hk⟩`; writing them uniformly avoids instance-search failures and very slow unification between `P.left.B` and `P.right.B`. |
| `PairSite.ajL_comp_πL`, `ajR_comp_πR` | G1.1′ for both curves (direct instances of `Frob.abelJacobi_comp_jacobianFrobenius`). |
| `PairSite.JacIso` | `{e : J_{W'} ≅ J_W // IsMonHom e.hom ∧ e.hom ≫ π_W = π_{W'} ≫ e.hom}`. |
| `jacHom`, `jacHom_eq`, **`isMonHom_jacHom`**, **`jacHom_comm`** | `jacHom α = Rigid.transport … = aj'⁻¹ ≫ α ≫ aj`; it is a homomorphism (G1.2) and `π`-equivariant (G1.1′ + `twist_comm_iff_geomFrob_comm`). |
| `toJacIso`, `ofJacIso` | `α ↦ aj'⁻¹ ≫ α ≫ aj`, and `e ↦ aj' ≫ e ≫ aj⁻¹` (pointed by `basePtO_comp_abelJacobi` + `IsMonHom.one_hom`: `zeroPt_comp_curveHomOfJac`; `Ψ`-equivariant: `curveHomOfJac_comm`). |
| **`PairSite.frobIsoEquiv`** | **G1.4**: `Coord.FrobIso W W' ≃ P.JacIso`. |
| **`PairSite.mem_orbit_iff_nonempty_jacIso`** | `W' ∈ VariableChange(K) • W ↔ Nonempty P.JacIso` (with `Coord.mem_orbit_iff_nonempty_frobIso`). |
| **`JacSite.card_stabilizer_eq_card_jacAut`** | `#Stab_{VariableChange K}(W) = #S.diag.JacIso`: the `π`-equivariant automorphisms of the group object `J_W` (`S.diag = ⟨S.B, S.hX, S.hX, S.hk⟩`), via `Coord.card_stabilizer_eq_card_frobAut`. |

### The interface to `DeuringLattice`

`DeuringLattice K t` (`Arith/DeuringAssembly.lean`) consumes, per elliptic `W` with trace `t`:

* `rel_iff`: `W' ∈ orbit W ↔ ∃ g : GL₂(ℤ), g • Λ W = Λ W'`;
* `card_stab`: `#Stab_{VariableChange K}(W) = #Stab_{GL₂(ℤ)}(Λ W)`;
* `surj`.

G1 now supplies the geometric halves:
`W' ∈ orbit W ↔ Nonempty (π-equivariant group isomorphism J_{W'} ≅ J_W)` and
`#Stab(W) = #Aut_π(J_W)`, for the concrete Jacobians `J_W = Pic⁰_{E_W/K̄}` with
`π_W = jacobianFrobenius` (whose char. poly is `X² − tX + q`, `JacSite.charPoly_π`). What
`rel_iff`/`card_stab` still need is the **lattice side**, G3–G8 of `ARITH_DEURING_PLAN.md`:
`Λ W` = matrix of `π` on `Hom(J₀, J_W)` and
`{π-equivariant isos J_{W'} ≅ J_W} ↔ {g : g Λ_W g⁻¹ = Λ_{W'}}` (`Hom_{ℤ[π]}`-lattice
isomorphisms; Tate's theorem G7 and the `p`-part G5). Nothing on that side is touched here.

One technical point for G9: the Jacobians of different `W` live on different sites; the
comparisons above take a common `PairSite`. `Λ W` should therefore be defined from data that
does not depend on the site (e.g. via an isomorphism-invariant of `(J_W, π_W)`), or with a
lemma identifying `JacSite.J` across sites containing each other (Yoneda; not needed so far).

## 5. What remains of G1

Nothing of G1.0–G1.4 as specified in `ARITH_DEURING_G1.md` §2 remains: the statement
`FrobIso W W' ≃ {e : J_{W'} ≅ J_W // IsMonHom e.hom ∧ e.hom ≫ π_W = π_{W'} ≫ e.hom}` is
`PairSite.frobIsoEquiv`. Optional follow-ups (not required by `DeuringLattice`):

* rigidity for non-invertible pointed morphisms `J' ⟶ J` (all isogenies are homomorphisms):
  0.3–0.6k lines (needs the pullback of `[𝒪(Δ)]` along `α × 1` for finite flat `α`, or the
  rigidity lemma for `J' × J' → J`);
* identification of `JacSite.J` across nested sites (Yoneda on the representing objects), for a
  site-independent `Λ W`: 0.2–0.4k lines.
