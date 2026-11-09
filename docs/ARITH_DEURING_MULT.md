# A3-ord: the concrete isogeny-class count `mult`, Tate uniqueness, and the per-class interface (2026-11-09)

This continues `ARITH_DEURING_APPROX.md` (the approximate endgame
`deligneBound_of_DeuringMult_unique`) and `ARITH_DEURING_G7.md` (Tate modulo
`QuotientFiniteness`). New files, audited in `RamanujanWeil/Arith/DeuringMultAxioms.lean`:

| File | Content |
|---|---|
| `Arith/DeuringMultDef.lean` | `IsogStep`, `isogSetoid`, `IsogClass`, `isogClassCount`, `mult`, `TateFiniteness(All)`, `isogStep_of_trace`, `isogClassCount_le_one`, **`mult_le_one`** |
| `Arith/DeuringMultCount.lean` | `DeuringClassLattice`, `locusMapP_bijective`, `orbitMassP_eq_matMass`, `card_pred_eq_mass`, `card_class_eq`, `card_ell_eq_sum`, `card_ell_eq_mult`, `DeuringClassLatticeAll`, **`deuringMultiplicity_of_classLattice`** |
| `Arith/DeuringG7Dual.lean` | `frobHom_comp_ne_one`, `frobHomNe_trans`, `FrobHomDual` (named), `tate_frobHomNe_both` |
| `Ihara/FinalDeuringTate.lean` | **`deligneBound_of_DeuringMult_tate`**, **`deligneBound_of_classLattice_tate`** |

No existing file was edited. The files contain no `sorry`, `admit`, `native_decide` or `axiom`.

## 1. The definition of `mult`

Over `K = 𝔽_q`, with `Ell K t = {W : WeierstrassCurve K // Δ ≠ 0 ∧ a_W = t}`:

```lean
def IsogStep (W W' : WeierstrassCurve K) : Prop :=
  W' ∈ orbit (VariableChange K) W ∨
    ∃ (_ : W.IsElliptic) (_ : W'.IsElliptic) (S : Jac.JacSite W) (S' : Jac.JacSite W'),
      FrobHomNe S.frobeniusJacobian S'.frobeniusJacobian ∨
        FrobHomNe S'.frobeniusJacobian S.frobeniusJacobian
def isogSetoid K t : Setoid (Ell K t) := Relation.EqvGen.setoid (fun x y => IsogStep x.1 y.1)
def isogClassCount K t : ℕ := Nat.card (Quotient (isogSetoid K t))
def mult p n t : ℕ := isogClassCount (GaloisField p n) t
```

Design choices:

* **The concrete Jacobian, not `FrobeniusJacobian`.** A `FrobeniusJacobian W` is any
  1-dimensional abelian variety with an endomorphism of characteristic polynomial
  `X² − a_W X + q`. It depends on `W` only through `a_W`, so an existential over it would make
  every pair of curves of the same trace "isogenous" through `𝟙`. That would be vacuous, and all
  the content would move into `DeuringMultiplicity`. `IsogStep` instead uses
  `S.J = Pic⁰_{E_W/K̄}` with the Frobenius `S.π` induced by the twisted Frobenius of `E_W`
  (G1.0, `JacSite`). It quantifies existentially over the auxiliary fppf site `S`, since the
  Jacobian for two different sites has not been proved isomorphic.
* **Isomorphic curves are glued in directly** (first disjunct). This makes every class a union of
  `VariableChange`-orbits (`isogClassPred_smul_iff`), which the per-class torsor count needs. It
  does so without proving that isomorphic curves have equivariantly isomorphic Jacobians (a G1
  statement).
* **Equivalence closure.** Neither reflexivity of the hom part (`𝟙 ≠ 1`), nor transitivity
  across different sites, nor symmetry of a single direction (G7-dual) is proved, so the class
  relation is `Relation.EqvGen` of the symmetrized step. It is an equivalence by construction.
  Mathematically it equals `𝔽_q`-isogeny.

## 2. Tate uniqueness: `mult ≤ 1`

```lean
def TateFiniteness (K) [Field K] [Fintype K] : Prop :=
  ∀ (W W' : WeierstrassCurve K) [W.IsElliptic] [W'.IsElliptic] (S : Jac.JacSite W)
    (S' : Jac.JacSite W'), traceOfFrob W' = traceOfFrob W →
    ¬ (ringChar K : ℤ) ∣ traceOfFrob W → traceOfFrob W ^ 2 < 4 * (Nat.card K : ℤ) →
    QuotientFiniteness (S.J ⊗ S'.J) (πA S.π S'.π)
def TateFinitenessAll : Prop :=
  ∀ (p) [Fact p.Prime] (n), 1 ≤ n → TateFiniteness (GaloisField p n)   -- Fintype.ofFinite

theorem mult_le_one (hfin : TateFinitenessAll) (n) (hn : 1 ≤ n) (t) (hp : ¬ (p:ℤ) ∣ t)
    (hlt : t ^ 2 < 4 * (p:ℤ) ^ n) : mult p n t ≤ 1
```

Proof: for `x, y ∈ Ell K t`, take Jacobian sites (`nonempty_jacSite`). `tate_exists_frobHom`
then gives a nontrivial equivariant hom in one direction, which is `IsogStep x y`. So the quotient
is a subsingleton. **G7-dual is not used**: the relation is symmetrized. The hypothesis covers
only the concrete Jacobians (the true Frobenius of an `𝔽_q`-structure), where
`QuotientFiniteness` is true (finitely many `𝔽_q`-forms in an isogeny class of abelian surfaces,
G7 doc §4–5), and only ordinary traces with `t² < 4q`.

## 3. G7-dual

**Not needed for `mult ≤ 1`, and not needed for the headline as stated.** It is needed inside
the per-class interface: G8 needs `Hom_π(E₀, E) ≠ 0` for every `E` in the class, not just a
zig-zag of homs.

Proved (`DeuringG7Dual.lean`): `frobHom_comp_ne_one` (degree is multiplicative, G4
`homDegree_comp`, so a composite of nonzero homs is nonzero), `frobHomNe_trans`, and
`tate_frobHomNe_both`: `FrobHomDual` + Tate ⇒ homs both ways.

Named: `FrobHomDual := ∀ K W W' (J J' : FrobeniusJacobian _), FrobHomNe J J' → FrobHomNe J' J`.

Cheapest route assessment:

* *Separable part via the G6 quotient.* For `α : E → E'` nonzero, `K = ker α(k̄)` is finite
  (`eq_one_of_infinite_pointKer`), and π-stable when α is equivariant. Let `q : E → E/K` be the
  G6 quotient, with `α = q ≫ ᾱ` (universal property). Since `K ⊆ E[N]`, `N = #K`, we have
  `[N] = q ≫ s`. **If** `ᾱ` is an isomorphism, `β = ᾱ⁻¹ ≫ s` is the dual up to `[N]`, and it is
  equivariant because `q` is an epimorphism. Two missing pieces: `ᾱ` bijective on `k̄`-points
  (easy, ~150 lines) ⇒ `deg ᾱ = p^r` (needs separable-degree = point count, Stacks has
  `degreeOver` but not "separable degree = generic fibre cardinality"), and
  `deg ᾱ = 1 ⇒ ᾱ` iso (birational morphism of smooth proper curves; `isIso_of_bijective_functionFieldMap`
  in `StacksFrontier/.../InseparableFactorizationChain.lean` gives most of it). ~0.5–0.8k.
* *Inseparable part.* `ᾱ` purely inseparable of degree `p^r`. Inverting it up to isogeny needs a
  map `E' → E/K` of degree `p^r`, i.e. Verschiebung, or the factorization of `F^r` through
  `ᾱ`. Stacks has the chain factorization into degree-`p` steps
  (`exists_chain_isInseparableDegreePrime`) and the curve ↔ function-field correspondence
  (`exists_hom_functionFieldMap_eq`). Each degree-`p` inseparable step `X → Y` has
  `k(X)^p ⊆ k(Y)`, which gives a `k`-morphism `Y → X^{(p)}`, not `Y → X`. To land back in `X`
  one needs `X^{(p)} ≅ X` over `k̄` up to isogeny. For our curves that is supplied by π (deg
  `q`, π·π̄ = q): `X^{(q)} ≅ X` via the `𝔽_q`-structure. **Estimate 0.8–1.5k**, matching the
  plan's 0.8–2k. The quotient trick removes the étale part but not the inseparable one.
* *Ordinary shortcut (unverified).* For `p ∤ t`, one of `π`, `π̄ = t − π` is purely
  inseparable and the other is étale. In principle this lets one replace the general Verschiebung
  by `π̄`. The argument still identifies the inseparable kernel of `ᾱ` with a subgroup of the
  connected part of `E'[p^r]`, which needs kernels as group schemes. That is not available in
  the points-only G6 API, so this is not obviously cheaper.

## 4. The per-class lattice interface

```lean
structure DeuringClassLattice (K) [Field K] [Finite K] (t : ℤ) (P : WeierstrassCurve K → Prop) where
  Λ : WeierstrassCurve K → TrDet t (Nat.card K)
  rel_iff : ∀ W W', P W → P W' → (W' ∈ orbit (VariableChange K) W ↔ ∃ g : GL2, g • Λ W = Λ W')
  card_stab : ∀ W, P W → Nat.card (stabilizer (VariableChange K) W) = Nat.card (stabilizer GL2 (Λ W))
  surj_class : ∀ M : TrDet t (Nat.card K), ∃ W, P W ∧ ∃ g : GL2, g • Λ W = M

def DeuringClassLatticeAll (p) : Prop :=
  ∀ n, 1 ≤ n → ∀ t, ¬ (p:ℤ) ∣ t → t ^ 2 < 4 * (p:ℤ) ^ n →
    ∀ C : IsogClass (GaloisField p n) t,
      Nonempty (DeuringClassLattice (GaloisField p n) t (IsogClassPred C))

theorem deuringMultiplicity_of_classLattice (hL : DeuringClassLatticeAll p) :
    DeuringMultiplicity hurwitz p (mult p)
```

This is `DeuringLattice` with every field restricted to one class `P`. The global `surj`, which
contains Deuring/Honda existence, is replaced by `surj_class`: every `GL₂(ℤ)`-class of
`TrDet t q` is realized **by a curve isogenous to a given one**. That is G8(iii) and needs no
existence. Proof: the `ordinaryDeuring_of_lattice` pattern per class
(`locusMapP_bijective` → `orbitMassP_eq_matMass` → `matMass_eq_hurwitz`), the torsor count
`finsum_eq_finsum_orbits` applied to the indicator of `P` (`card_pred_eq_mass`), then
`#Ell = Σ_C #C` (`card_ell_eq_sum`, fibres of the class map).

## 5. Headline

`deligneBound_of_DeuringMult_unique` takes `mult : ℕ → ℕ → ℤ → ℕ` with no primality instance, so
the headline passes `multAll p n t := if h : p.Prime then @mult p ⟨h⟩ n t else 0`. At a prime it
agrees with `mult p`.

```lean
theorem RamanujanWeil.Ihara.deligneBound_of_DeuringMult_tate (hfin : TateFinitenessAll)
    (hM : ∀ (p : ℕ) [Fact p.Prime], DeuringMultiplicity hurwitz p (mult p)) :
    RamanujanTau.DeligneBound

theorem RamanujanWeil.Ihara.deligneBound_of_classLattice_tate (hfin : TateFinitenessAll)
    (hL : ∀ (p : ℕ) [Fact p.Prime], DeuringClassLatticeAll p) :
    RamanujanTau.DeligneBound
```

## 6. What the per-class geometric content (G8 / G5) still needs

For a class `C` pick `E₀ ∈ C`. To be honest about route L: one also needs `End_π(E₀) = ℤ[π]`
(the maximal-to-minimal-order step). In general `End_π(E₀)` is an order `O ⊇ ℤ[π]`, and
the lattices `Hom_π(E₀, E)` are then `O`-modules, not arbitrary `ℤ[π]`-lattices. Route L
(plan §4) handles this by first descending to the curve with `End = ℤ[π]`, which is G8(iii)
applied to `E₀` and its `[O : ℤ[π]]`-quotients. The fields:

1. **`Λ` (G8(i), ~0.5–1k).** `L(E) = Hom_π(E₀, E)`, a free `ℤ`-module of rank 2. Rank ≥ 2
   comes from `ℤ[π]·α`, α ≠ 0, and needs `Hom_π(E₀, E) ≠ 0`: Tate one direction + **G7-dual**
   (+ `frobHomNe_trans` along the zig-zag; **the sites must also be matched**, i.e. Jacobians
   for different sites must be equivariantly isomorphic, ~0.2–0.4k from representability).
   Rank ≤ 2 comes from G3 (`homAV_tensor_injective`, `finrank_le_of_anisotropic_of_saturated`).
   `Λ W` is the matrix of `π` on a basis; trace/det from `frob_quadratic`.
2. **`rel_iff` (G1 + G8(ii), ~1–2k).** `E ≅_K E'` ⇔ `(J_E, π) ≅ (J_{E'}, π')` equivariantly
   (G1: `DeuringG1Coord.mem_orbit_iff_nonempty_frobIso` + Jacobian functoriality, which the
   G1{Frob,Rigid,Assembly} work in progress targets) ⇔ `L(E) ≅ L(E')` as `ℤ[π]`-modules
   (G8(ii): `Hom_π(E, E') ≅ Hom_{ℤ[π]}(L E, L E')`, needs `End_π(E₀) = ℤ[π]` and the
   `⊗ ℤ_ℓ` statement G7-End/Hom, 0.4–0.8k).
3. **`card_stab` (G1 + G8(ii), ~0.3k on top of 2).** `#Aut_K(E) = #Aut_π(J_E) = #(ℤ[π]-module
   automorphisms of L E) = #Stab_{GL₂(ℤ)}(Λ E)`. G1Coord has `card_stabilizer_eq_card_frobAut`.
4. **`surj_class` (G8(iii) = G5 quotients, ~1.5–3k).** For each `ℤ[π]`-lattice `M ⊆ L(E₀)⊗ℚ`
   of full rank, scale into `L(E₀)` and form `E₀/G` with `G = ker` of the corresponding
   finite π-stable subgroup scheme (étale part via G6 `exists_quotient_by_finite_subgroup'`,
   the `p`-part via the canonical subgroup and Frobenius). Then show `E₀/G` is an `𝔽_q`-form
   (descend `π` via the universal property), is a Weierstrass curve over `𝔽_q` (needs descent
   from `K̄` to `𝔽_q`, the hardest part, G5), and has `L(E₀/G) ≅ M`.

Total for the per-class interface: **~4–8k lines**, plus G7-dual (0.8–1.5k). With
`QuotientFiniteness` (12–30k, G7 doc §4), that is the whole remaining A3-ord cost for the
Deligne headline.

## 7. Remaining named Props

| Prop | Where | Status |
|---|---|---|
| `TateFinitenessAll` | `DeuringMultDef` | `QuotientFiniteness` for concrete Jacobian pairs; 12–30k |
| `DeuringClassLatticeAll p` (or directly `DeuringMultiplicity hurwitz p (mult p)`) | `DeuringMultCount` | §6; 4–8k + G7-dual |
| `FrobHomDual` | `DeuringG7Dual` | not a hypothesis of the headline; an input to §6.1; 0.8–1.5k |

Build check: `nice -n 10 lake build RamanujanWeil.Arith.DeuringMultAxioms` succeeds (2026-11-09).
All 17 audited theorems depend only on `[propext, Classical.choice, Quot.sound]`. Sizes: Def 194,
Count 232, G7Dual 86, FinalDeuringTate 50 lines. Each file takes 10–16 min to build on this
machine, almost all of it loading imports.
