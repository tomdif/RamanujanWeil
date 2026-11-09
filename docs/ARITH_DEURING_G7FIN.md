# A3-ord, G7-fin: is there a cheap route to `QuotientFiniteness`? Route decision and first layer (2026-11-09)

This continues `ARITH_DEURING_G7.md` (Tate's gluing argument modulo `QuotientFiniteness`),
`ARITH_DEURING_MULT.md` (`TateFinitenessAll ⇒ mult ≤ 1`) and `ARITH_DEURING_G8.md`. New files,
audited in `RamanujanWeil/Arith/DeuringG7FinAxioms.lean`:

| File | Imports | Content |
|---|---|---|
| `Arith/DeuringG7FinAlg.lean` | G7Alg, Mathlib | odd prime with no root; Hensel for square roots of units mod `ℓⁿ⁺¹`; **norm form onto units**; **equivariant gluings with any prescribed determinant** |
| `Arith/DeuringG7FinCore.lean` | MultDef, G7FinAlg | `GraphFiniteness`, **`PolGraphFiniteness`** (named), weaker than `QuotientFiniteness`; the G7 core from it; `TateFinitenessPol(All)`; **`mult_le_one_pol`** |
| `Arith/DeuringG7FinProd.lean` | G7Tate | **product case of the genus-2 route**: `exists_common_factor_of_prodIso`, `comp_iso_fst_equivariant` |
| `Arith/DeuringG7FinAxioms.lean` | | audit |

No existing file was edited. No `sorry`, `admit`, `native_decide` or `axiom`.

## 0. Decision

**There is no much cheaper route.** Every candidate in (a)–(c) either reduces to the statement
being proved, or needs class-field / CM / modular-polynomial input that costs more than the
finiteness theorem. The detailed evidence is in §2. The decision is **(d), the polarization
route, in its most economical form**:

* Use only **graph quotients** `B_n = (E × E')/graph(u_n)`.
* Choose the gluings `u_n` **anti-isometric** for the Weil pairings. Then `graph(u_n)` is
  maximal isotropic, and `ℓⁿ⁺¹(λ_E × λ_{E'})` descends to a **principal** polarization on `B_n`.
* The remaining geometric input is then exactly **finiteness of principally polarized abelian
  surfaces over `𝔽_q`**. This needs no Zarhin trick, no bounded-degree polarizations and no
  arbitrary π-stable subgroups.

The first layer is built (§3). The hypothesis of the headline chain is now the **weaker**
`TateFinitenessPolAll` (`mult_le_one_pol`). The remaining work is the principally polarized
finiteness theorem, estimated at **15–25k lines** (§4). The doc §4 estimate of 12–30k stands; the
savings from restricting to principal graph quotients are real but modest, about 1–3k.

## 1. What the gluing argument actually consumes (idea (b), first half)

Re-reading `exists_frobHom_of_quotientFiniteness`:

1. It uses `QuotientFiniteness` **only** for the family `Γ_n = graph(u_n)`. The `u_n` are any
   `π`-equivariant isomorphisms `E[ℓⁿ⁺¹] ≅ E'[ℓⁿ⁺¹]`, and they need not be compatible in `n`.
   So the hypothesis can be restricted to graph quotients, with the `u_n` chosen in any
   prescribed nonempty class (`GraphFiniteness π π' ℓ S`, §3).
2. From an equivariant isomorphism `B_n ≅ B_m` it uses only the following. If
   `Hom_π(E, E') = Hom_π(E', E) = 0`, then an equivariant hom `f : B_n → B_m` maps
   `i_n(E)` into `i_m(E)` and `i'_n(E')` into `i'_m(E')`. So it maps `i_n(E) ∩ i'_n(E')`, which
   has `ℓ^{2(n+1)}` points, into the corresponding set of size `ℓ^{2(m+1)}`. Hence **one
   equivariant hom `B_n → B_m` with `n > m` and kernel smaller than `ℓ^{2(n−m)}`** would already
   suffice (`card_tor_le` only uses injectivity of `f`).
3. **None of the weakenings removes the moduli input.** Under `Hom = 0`, every isogeny
   `B_n → B_m` lies in `(End E × End E') ⊗ ℚ` after composing with `q_n`, `q_m`, and has kernel
   at least `ℓ^{2(n−m)}`. So "bounded-kernel isogenies exist" is equivalent to the conclusion.
   Any pigeonhole needs a **complete** finite invariant of `(B_n, π_n)`, that is, a point of a
   moduli space of finite type over `𝔽_q`.

## 2. The candidate routes

### (a) Are the `B_n` products of elliptic curves? Hom lattices and Steinitz classes

* **Under the contradiction hypothesis the `B_n` are never equivariant products.** Suppose
  `B_n ≅ C₁ × C₂` with `π` diagonal, and let `ε₁, ε₂` be the projector idempotents. With
  `Hom = 0`, `i_n(E)` lies in `ker p'_n` on points, so it is stable under both `ε_j`, and the same
  holds for `i'_n(E')`. So `i_n(E) ∩ i'_n(E') = ⊕_j ε_j i_n(E) ∩ ε_j i'_n(E')`. If some `C_j`
  received nonzero equivariant maps from both `E` and `E'`, then `FrobHomDual` (now reduced to
  `RadicialDual`, G8 doc §1) would give `Hom_π(E', E) ≠ 0`. Otherwise every summand is 0, but the
  intersection has `ℓ^{2(n+1)} > 1` points. So **"every `B_n` is a product" is equivalent to the
  conclusion.** The product theorems that are true (Shioda–Mitani, Kani: abelian surfaces
  isogenous to `E²` with `E` CM are products) presuppose `B ~ E²`, which is Tate.
* **Hom lattices cannot see the gluing.** Under `Hom = 0`, every equivariant `E → B_n` lands in
  `ker p'_n = i_n(E)` on points. So `Hom_π(E, B_n) = End_π(E) · i_n` and
  `Hom_π(E', B_n) = End_π(E') · i'_n` **for every `n`**. Any invariant built from
  `Hom_π(E₀, B)` as an `O`-module (rank, Steinitz class, ideal class) is constant along the
  family. The functor `B ↦ (Hom_π(E, B), Hom_π(E', B))` is not conservative on this family, and
  the family is non-isomorphic exactly when the theorem fails. Jordan–Zassenhaus finiteness of
  ideal classes is therefore useless here: it would only apply after the equivalence of
  categories (Deligne's ordinary equivalence, or Kani), which itself needs Tate.
* **Verdict: ✗.**

### (b) Counting `𝔽_q`-points and `B_n[ℓ^∞]`

* `#B_n(𝔽_{q^r}) = #E(𝔽_{q^r}) · #E'(𝔽_{q^r})` for every `n` (isogeny invariance).
* As a group, `B_n(𝔽_{q^r})[ℓ^∞] ≅ Λ_n / (π^r − 1)Λ_n`, where `Λ_n = T_ℓ B_n`. Here `ℓ` is inert
  (chosen so that `X² − tX + q` has no root mod `ℓ`), so `ℤ_ℓ[π]` is the unramified quadratic
  DVR. Every `Λ_n` is free of rank 2 over it, so all these groups are **isomorphic for all `n`**.
  The same holds at every other prime. Point counts and group structures carry no information
  about `n` (G7 doc F3, confirmed).
* The weaker consumption (§1.2) does not help either (§1.3).
* **Verdict: ✗.**

### (c) Avoiding Tate for `mult ≤ 1`

* **Signed cancellation: the claim is sound.**
  * With the per-class lattice structure (`DeuringClassLattice`), every count of the form
    `Σ_{E of trace t} F(E)`, where `F` depends only on the `π`-module structure of the Tate
    modules, the endomorphism order, or the number of rational `N`-isogenies or `N`-torsion
    points, factors as `m(t) · (per-class mass)`.
  * Independent global counts that are elementary give one linear identity each:
    * the total number of curves;
    * point counts on genus-0 modular curves `X_1(N)`, `X_0(N)` (finitely many `N`), via Tate
      normal forms.
  * So one gets **finitely many** identities `Σ_t (m(t) − 1) w_N(t) = 0`, while there are about
    `4√q` unknowns `m(t) ∈ ℕ`.
  * Higher moments `Σ_t N(t) t^{2k}` are elementary only while `S_{2k+2} = 0` (`k ≤ 4`, Birch),
    and their proofs need fibre-power point counts.
  * Exact (KH-ord) still needs the supersingular count (G7 doc §2).
  * The approximate endgame needs `Σ_t |m(t) − 1| H(4q − t²) ≲ q^{1/2}` (the error is
    `≈ q⁹ Σ|m − 1| H`). A signed identity gives no such bound.
  * **Confirmed: counting alone cannot force `m ≤ 1`.**
* **ℓ-isogeny graph / kernels of `π − λ` at split `ℓ`.** These are rational `ℓ`-isogenies
  `E → E/ker(π − λ)`, i.e. the action of the prime `𝔩 | ℓ` of `ℤ[π]`. The graph they generate
  is the `Pic(O)`-orbit of `E` (plus vertical steps in the volcano). That every curve of trace
  `t` lies in one orbit is the transitivity half of Deuring's correspondence, the statement
  itself. Free action is already the per-class count. **✗.**
* **Upper bound via CM polynomials.** The `j`-invariants with `End ⊇ O` are roots of `H_O mod p`,
  or of the diagonal modular polynomials `Φ_N(X, X)` (Kronecker), giving
  `m(t) h(O) ≤ deg = h(O)`. This needs `Φ_N ∈ ℤ[X, Y]` (q-expansions of `j`) and Deuring
  lifting, or Kronecker congruences with multiplicities. **≥ 10–20k, ✗.**
* **Existence instead of uniqueness.** Honda/Deuring CM lifting, **≥ 20k** (G7 doc §2). **✗.**

### (d) The polarization route: the most economical honest version

Set `A = E × E'` and `N = ℓⁿ⁺¹`, and choose `u_n` with `det_{e,e'}(u_n) = c_n := −s_n/s'_n`,
where the Weil pairing gives `e_N(e_n(1,0), e_n(0,1)) = ζ^{s_n}` and similarly for `E'`.

1. **(built, §3)** Such equivariant `u_n` exist: the equivariant isomorphisms are
   `u₀ ∘ (a + bπ)`, and `det(a + bπ) = a² + tab + qb²` takes every unit value mod `ℓⁿ⁺¹`.
2. `graph(u_n)` is maximal isotropic for `e_N^{λ_E × λ_{E'}}`, so `N·(λ_E × λ_{E'})` descends to
   a principal polarization `λ_n` on `B_n`, with `π_n^∨ λ_n π_n = q λ_n` (Mumford §23,
   Thm. 2). Over the product `A = E × E'` this is concrete:
   * `q_n^* Θ_n ≡ N(E × 0 + 0 × E')`.
   * `H⁰(B_n, Θ_n)` is the line of `Γ̃_n`-invariants in the Schrödinger representation
     `H⁰(E, O(N[0])) ⊗ H⁰(E', O(N[0]))` of the finite Heisenberg group of `(E × E')[N]`.
   * Numerically, `i_n(E) + i'_n(E') ≡ N Θ_n` in `NS(B_n)`.
3. Finiteness of `(B_n, λ_n, π_n)` up to equivariant isomorphism, by one of:
   * **F2′ (genus 2).** `Θ_n` is an effective divisor with `Θ_n² = 2` and `K_B = 0`, so
     `p_a = 2`.
     * If it is reducible, `Θ_n = C₁ + C₂` with `C₁ · C₂ = 1` and `B_n ≅ C₁ × C₂`. The product
       case is **killed directly** by the argument of (a): no finiteness is needed, only
       `FrobHomDual`.
     * If it is irreducible, it is a smooth genus-2 curve `C_n`, `π`-stable up to a 2-torsion
       translation, defined over `𝔽_q`, with `Jac(C_n) ≅ B_n` (Stacks `jacobianGrp` plus the
       Albanese property).
     * Genus-2 curves over `𝔽_q` are finite (hyperelliptic models `y² + h y = f`, `deg ≤ 6`, via
       Riemann–Roch on curves). An `𝔽_q`-isomorphism `C_n ≅ C_m` gives `B_n ≅ B_m`
       equivariantly by functoriality of `Pic⁰`.
   * **F1′ (explicit 4Θ).** The `16 = 4²` invariant sections of `q_n^*(4Θ_n)` embed `B_n` into
     `ℙ¹⁵` (Lefschetz, transported to `A` through the Heisenberg description in 2). They can be
     chosen `𝔽_q`-rationally by Lang's theorem for `GL₁₆`. The image has degree
     `(4Θ)² = 32` and is cut out by forms of degree `≤ 32`. Finitely many such subvarieties
     exist over `𝔽_q`. Rigidity then turns an equality of images into an equivariant
     isomorphism of the `B_n`.

## 3. What is proved (this session)

`DeuringG7FinAlg.lean` (Mathlib + G7Alg only):

* `exists_odd_prime_no_root`: the prime of `exists_prime_no_root` is odd (it divides
  `4(4q − t²) − 1`).
* `int_exists_sq_dvd`, `isSquare_of_isUnit_of_isSquare_red`: Hensel for square roots of units
  mod `ℓⁿ⁺¹`, `ℓ` odd.
* `disc_not_square`, `exists_sq_sub_disc_mul_sq`, **`exists_normForm_eq`**: if `X² − tX + q`
  has no root mod `ℓ`, then `a² + tab + qb²` represents every unit mod `ℓⁿ⁺¹`.
  * Mod `ℓ` via `FiniteField.exists_root_sum_quadratic` applied to `X² − D Y² = 4c`.
  * Lifting by Hensel in `X` or in `Y`, according to whether `X₀ = 0`.
* `mat`, `mat_comp`, `isUnit_det_mat`, `coordMat`, **`exists_equivariant_addEquiv_det`**: for
  any coordinates `e, e'` and any unit `c` there is a `φ`-equivariant `u : M ≅ M'` with
  `det(e' ∘ u ∘ e⁻¹) = c`.

`DeuringG7FinCore.lean`:

```lean
def GraphFiniteness (π π') (ℓ) (S : ∀ n, Set (Tor E (ℓ^(n+1)) ≃+ Tor E' (ℓ^(n+1)))) : Prop :=
  ∀ u (hu : equivariant), (∀ n, u n ∈ S n) → ∀ G : ∀ n, Glue (Γ ℓ u n),
    ∃ n m, n ≠ m ∧ ∃ e : (G n).B ≅ (G m).B, IsMonHom e.hom ∧ e.hom ≫ πB_m = πB_n ≫ e.hom
def PolGraphFiniteness (π π') (ℓ) : Prop :=          -- the named hypothesis
  ∀ (e : Coords E ℓ) (e' : Coords E' ℓ), ∃ c, (∀ n, IsUnit (c n)) ∧
    GraphFiniteness π π' ℓ (detClass e e' c)
```

* `graphFiniteness_of_quotientFiniteness`, `polGraphFiniteness_of_quotientFiniteness`: both
  are **implied by** `QuotientFiniteness`, so they are genuinely weaker.
* `exists_frobHom_of_graphFiniteness`: the G7 core from `GraphFiniteness`.
* **`tate_exists_frobHom_pol`**: Tate for Frobenius Jacobians from `PolGraphFiniteness` at every
  odd `ℓ` invertible in `𝔽̄_q`.
* `TateFinitenessPol K`, `TateFinitenessPolAll`, `tateFinitenessPol_of_tateFiniteness`,
  `tateFinitenessPolAll_of_tateFinitenessAll`, `isogStep_of_trace_pol`,
  `isogClassCount_le_one_pol`, **`mult_le_one_pol`**:

```lean
theorem mult_le_one_pol (hfin : TateFinitenessPolAll) (p) [Fact p.Prime] (n) (hn : 1 ≤ n)
    (t : ℤ) (hp : ¬ (p:ℤ) ∣ t) (hlt : t ^ 2 < 4 * (p:ℤ) ^ n) : mult p n t ≤ 1
```

So every downstream consumer of `TateFinitenessAll` (through `mult_le_one`) can take the weaker
`TateFinitenessPolAll` instead. Since `FinalDeuringTate` cannot be edited, a new
headline wrapper is a one-line change for whoever next touches the endgame:
`deligneBound_of_DeuringMult_unique` with `mult_le_one_pol`.

Why `PolGraphFiniteness` is true: §2(d).2. For any coordinates, `c_n = −s_n/s'_n` makes every
`u_n ∈ detClass` anti-isometric, and principally polarized surfaces over `𝔽_q` are finite.

`DeuringG7FinProd.lean` (step Θ's product case, §2(a)):
* `exists_common_factor_of_prodIso`: if `B_n ≅ C₁ × C₂` as group objects and `E[ℓⁿ⁺¹] ≠ 0`,
  then for some `j` both `i_n ≫ e ≫ pr_j` and `i'_n ≫ e ≫ pr_j` are nontrivial.
* `comp_iso_fst_equivariant`: these maps are equivariant when `e` intertwines `π_n` with the
  diagonal `ρ₁ × ρ₂`. With `FrobHomDual` this gives a nonzero equivariant `E ⟶ E'`, so the
  product case of F2′ needs no finiteness.

## 4. Remaining named Props and estimates

| Prop | Where | Content | Estimate |
|---|---|---|---|
| **`TateFinitenessPolAll`** (replaces `TateFinitenessAll` for `mult ≤ 1`) | `DeuringG7FinCore` | finiteness of principally polarizable graph quotients of `J_W × J_{W'}` | see below |
| `FrobHomDual` / `RadicialDual` | G7Dual / G7Dual2 | unchanged; also used by the F2′ product kill | 0.8–1.3k |

Breakdown for `TateFinitenessPolAll`, route F2′ (preferred: it reuses Stacks' Jacobians and
needs only curve finiteness at the end):

| Step | Content | Estimate |
|---|---|---|
| W | Weil pairing on `J[N]` for Jacobians: alternating, Galois/`π`-compatible (`e(πx, πy) = e(x,y)^q`), perfect, and a coordinate expression `s_n` | 1.5–3k (Stacks `Picard/WeilPairing` is abstract only) |
| D | descent of `N(λ_E × λ_{E'})` along the G6 quotient `q_n`: Heisenberg group of `O(N[0])` on an elliptic curve (Riemann–Roch on curves), invariant line, and `q_n^*` / `q_{n*}^Γ` on line bundles over the G6 quotient | 4–7k |
| Θ | `h⁰(Θ_n) = 1`, effective `Θ_n` with `Θ_n² = 2`; reducible ⇒ product (killed by the argument of §2(a), 0.4–0.7k); irreducible ⇒ smooth genus 2 | 4–7k (intersection theory on an abelian surface, adjunction) |
| J | `Jac(Θ_n) ≅ B_n`, equivariant (Albanese / universal property of `jacobianGrp`, `π`-stability up to 2-torsion translation) | 2–4k |
| C | genus-2 curves over `𝔽_q`: finitely many up to `𝔽_q`-isomorphism (hyperelliptic models), and `C ≅ C' ⇒ Jac C ≅ Jac C'` equivariantly | 1.5–3k |
| **Total** | | **15–25k** |

F1′ has the same W + D, then Lefschetz on `A` (2–4k), the projective embedding as a closed
immersion (2–4k; absent from Stacks/Mathlib), Lang's theorem for `GL_N(𝔽̄_q)` (0.5–1k), and
bounded-degree finiteness plus rigidity (2–3k). That is **16–27k**, and it lands in no reusable
API. **Recommendation: F2′.** Do steps W and C first: both are self-contained and reusable
(Weil pairing, curve finiteness). D and Θ are the high-risk core.

**If the budget does not allow 15–25k**, the honest alternative is to keep
`TateFinitenessPolAll` as the single named geometric hypothesis of A3-ord's uniqueness half. It
is a standard textbook fact (finitely many principally polarized abelian surfaces over a finite
field), strictly weaker than the previous `TateFinitenessAll`, and stated only about graph
quotients of the concrete Jacobians.

## 5. Audit

`nice -n 10 lake build RamanujanWeil.Arith.DeuringG7FinAxioms` succeeds (2026-11-09). All 20
audited declarations depend only on `[propext, Classical.choice, Quot.sound]`. Sizes: FinAlg 341,
FinCore 268, FinProd ≈95, Axioms 27 lines.
