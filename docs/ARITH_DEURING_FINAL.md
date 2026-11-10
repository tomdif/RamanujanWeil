# A3-ord, final: route re-examination and the Tate-free per-class count (2026-11-10)

This continues `ARITH_DEURING_G7FIN.md` (route F2′, steps W / D / Θ / J / C),
`ARITH_DEURING_APPROX.md` (approximate endgame) and `ARITH_DEURING_CLASSLATTICE.md`.
New files only, audited in `RamanujanWeil/Arith/DeuringFinalAxioms.lean`:

| File | Content |
|---|---|
| `Arith/DeuringFinalSite.lean` | site independence of concrete Jacobians; nonzero equivariant homs both ways **inside one isogeny class**, with no finiteness input |
| `Arith/DeuringFinalLattice.lean` | `Λ`, `surj_class` and the class lattice restricted to the class; **`deuringMultiplicity_uncond`** |
| `Arith/DeuringFinal.lean` | `MultLeOneAll`, `OrdinaryTraceExistence`; **`deligneBound_of_multLeOne`**, **`deligneBound_of_ordinaryTraceExistence`**, `deligneBound_of_tatePol'` |
| `Arith/DeuringFinalAxioms.lean` | `#print axioms` audit |

## 0. Decision

1. **A finding that changes the dependency picture.** The per-class count
   `deuringMultiplicity_of_props` was *not* Tate-free, contrary to what the brief assumed.
   `ClassLattice.exists_latticeMatrix_global` and `link_global` used `TateFinitenessPol` to get
   nonzero homomorphisms `J_{W₀} ⟶ J_W` for **every** curve `W` of trace `t`. The structure
   `DeuringClassLattice K t P` only ever looks at curves in `P` (one class). Inside a class the
   homomorphisms exist by definition of the class (the equivalence closure of `IsogStep`).
   Re-assembling with all hypotheses restricted to the class removes Tate from the count:

   ```lean
   theorem Final.deuringMultiplicity_uncond (p) [Fact p.Prime] :
       DeuringMultiplicity hurwitz p (mult p)          -- no hypothesis
   ```

   So `N(t) = q³(q−1)·mult(t)·H(4q−t²)/2` is now an unconditional theorem for every ordinary `t`.
   As a result, **either half of Deuring's correspondence alone** gives Deligne:

   ```lean
   theorem deligneBound_of_multLeOne (h : MultLeOneAll) : RamanujanTau.DeligneBound
   theorem deligneBound_of_ordinaryTraceExistence (h : OrdinaryTraceExistence) :
       RamanujanTau.DeligneBound
   ```

   `TateFinitenessPolAll ⇒ MultLeOneAll` (`multLeOneAll_of_tatePol`), so the old headline is a
   corollary (`deligneBound_of_tatePol'`).

2. **Existence (`m ≥ 1`) is not cheap.** The brief's observation is right: with existence,
   every term of `Σ(m−1)H` is `≥ 0`, the signed identity becomes an `ℓ¹` bound, and
   `deligneBound_of_DeuringMult_exists` applies. That is now literally
   `deligneBound_of_ordinaryTraceExistence`. But proving `OrdinaryTraceExistence` needs CM theory
   (§2). **Decision: keep the Tate route (D / Θ / J / C-Jac) for `MultLeOneAll`.** Record
   `OrdinaryTraceExistence` as an equally valid alternative single hypothesis. Neither is cheap.
   The Tate route is the cheaper of the two: 11–19k remaining, against ≥ 20k for CM lifting.

3. **No cheaper sufficient statement was found** for the endgame budget
   `Σ_{p∤t} |m(t) − 1|·H(4q − t²) = O((n+1)^k √q)` (§2.1).

## 1. What is proved this session

### 1.1 `DeuringFinalSite`

* **`exists_siteIso S T`**: for two Jacobian sites of the same `W`,
  `e = aj_S⁻¹ ≫ aj_T : J_S ≅ J_T` is an equivariant group isomorphism.
  * It is pointed, so it is a homomorphism by rigidity (`Descent.isMonHom_of_pointed'`).
  * It is `π`-equivariant by G1.1′ (`aj_comp_π`).
  * This is the pattern of `Descent.exists_jacIso`, applied with target `T.J`.
* `frobHomNe_of_iso`, **`frobHomNe_transport`**: `FrobHomNe` does not depend on the sites.
  `frobHomNe_of_equivIso`: equivariant isomorphisms are nonzero.
* `HomRel G` ("nonzero equivariant hom between global-site Jacobians") is an equivalence
  (`homRel_equivalence`):
  * reflexive: the identity;
  * symmetric: the proved `Radicial.frobHomDual`;
  * transitive: `frobHomNe_trans`, from G4 degrees.
* `HomRel` contains `IsogStep` (`homRel_of_isogStep`):
  * the change-of-variables disjunct by G1 (`mem_orbit_iff_global`);
  * the Jacobian disjunct by site transport.
* Hence **`frobHomNe_both_class`**: curves in one class have nonzero equivariant homs both ways.

### 1.2 `DeuringFinalLattice`

* `exists_latticeMatrix_cls`: the `Λ` field on the class.
* `surjClass_of_descent_cls`: G5's `surjClass_of_descent` with the `Λ` hypothesis restricted to
  the class. It is the same proof; the realized quotient `W₀/Γ` is placed in `C` before `Λ` is
  used. `CyclicTorsion` is discharged by `cyclicTorsion_of_minimalOrder`.
* `classLattice_cls`: `classLattice_fam` with `hΛ`, `hl` restricted to `P`.
* `nonempty_classLattice_of_base_uncond`, `nonempty_classLattice_uncond`,
  `deuringClassLatticeAll_uncond`, **`deuringMultiplicity_uncond`**. The inputs are:
  * the link from `PLink.primeToPLink`, which is proved;
  * descent from `WModel.weierstrassDescent`, proved;
  * the minimal base from `MinBase.existsMinimalBase`, proved.

### 1.3 `DeuringFinal`

`MultLeOneAll`, `OrdinaryTraceExistence` (named Props), `one_le_mult_of_exists`, and the three
headlines above.

## 2. Why existence is not cheap (evidence)

Fix an ordinary trace `t` at level `n`, `q = pⁿ`, and write `π = (t + √(t² − 4q))/2`,
`K = ℚ(π)`. Then `p = 𝔭𝔭̄` splits in `K`, and `(π) = 𝔭ⁿ` (ordinary ⇔ `p ∤ t`).

* **Reduction to one curve per field.** The per-class count (now unconditional) says: once one
  curve with Frobenius `π` exists, every order `ℤ[π] ⊆ O ⊆ O_K` occurs as `End`, each `h(O)`
  times. In particular, some curve `E₀` has `End = O_K`.
  * Its `p`-Frobenius isogeny `E₀ → E₀^{(p)}` has kernel `E₀[𝔭]`. So `j ↦ j^p` is the action
    of `[𝔭] ∈ Pic(O_K)`.
  * That action is free, by the per-class count. So `j(E₀)` has degree `ord[𝔭]` over `𝔽_p`.
  * Every trace with field `K` at every level is then a twist of a base change of `E₀`.

  So `OrdinaryTraceExistence` is equivalent to: **every imaginary quadratic `K` in which `p`
  splits is the CM field of some ordinary curve over `𝔽̄_p`.** This is Deuring's reduction
  theorem. All known proofs reduce a CM curve from characteristic 0, either via CM theory of
  `ℂ/𝔞` and good reduction, or via Honda–Tate's CM lifting. Both are ≥ 20k lines here (G7 doc §2).
* **Counting at a single `t` (positivity).** Every count that can be computed elementarily is a
  sum over isomorphism classes of a function of the Tate-module / endomorphism / torsion data.
  These are:
  * the total number of curves;
  * `X₀(N)` and `X₁(N)` for genus 0;
  * Kronecker–Hurwitz.

  By the per-class count, each such sum factors as `Σ_t m(t)·w(t)`. So each gives **one linear
  identity** `Σ_t (m(t) − 1)·w(t) = 0`, or `O(√q)`, in about `4√q` unknowns. A finite family of
  such identities cannot force `m(t₀) ≥ 1` at a prescribed `t₀`, or `m ≥ 1` on most of the
  mass.
  * Scale check: each `t` carries mass `H(4q − t²) ≍ √q·L(1, χ)`, comparable to the whole error
    budget `O((n+1)^k √q)`.
  * So the budget tolerates only `O_n(1)` bad traces. An exchange `m(t₁) = 0`, `m(t₂) = 2`
    with `H(t₁) ≈ H(t₂)` is invisible to every linear identity.
* **Higher moments.** `Σ_t N(t)·h_{2k}(t)` for `k ≤ 4` (no cusp forms) are elementary only
  through fibre-power point counts (Birch), and are again linear in `m`. A quadratic identity
  (`Σ_t N(t)²`, pairs with equal point counts) would bound `Σ(m − 1)²`. Computing it needs the
  trace distribution itself.
* **Explicit CM constructions.**
  * Explicit models exist only for the 13 class-number-one discriminants.
  * Roots of `H_D mod p` need the Hilbert class polynomial, i.e. CM theory over `ℚ(j)`.
  * Kronecker's `Φ_N(X, X)` needs `Φ_N ∈ ℤ[X, Y]` and reduction mod `p`. That is the upper-bound
    route, ≥ 10–20k.
* **Verdict: ✗.** `OrdinaryTraceExistence` stays a named Prop with a proved headline. It is not
  the recommended route.

### 2.1 The weaker budget statement

The endgame needs `D(n) := Σ_{p∤t} |m(t) − 1|·H = O((n+1)^k √q)`. Since
`|m − 1| = (m − 1) + 2·[m = 0]` and `Σ(m − 1)H = O(n²√q)` (Kronecker–Hurwitz and
`N_ord ≤ q⁵`, as in `ordinaryDeuringApprox_of_mult_exists`), `D(n) = O(√q)` is **equivalent** to
the *missing mass* bound `Σ_{m(t)=0} H(4q − t²) = O((n+1)^k √q)`. That bound is strictly weaker
than existence but has the same difficulty: by §2 it says that all but `O_n(1)` fields `K`, by
mass, are realized. No argument for it avoids CM theory either. It is therefore not formalized
as a separate Prop.

## 3. What remains

**Single named hypothesis on the recommended route:** `MultLeOneAll`, implied by
`TateFinitenessPolAll` (`multLeOneAll_of_tatePol`). The remaining work is unchanged from
`ARITH_DEURING_G7FIN.md` §4 / `ARITH_DEURING_G7_WC.md` §3:

| Step | Content | Estimate |
|---|---|---|
| D | theta group `𝒢(𝒪(N[0]))` on `E`, `AltPairing.ofTheta` for `J_W`, `J_{W'}` with a common `ζ`; descent of `N(λ_E × λ_{E'})` along the graph quotient | 4–6.5k |
| Θ | `h⁰(Θ) = 1`, `Θ² = 2`; reducible ⇒ product (killed, `DeuringG7FinProd`); irreducible ⇒ smooth genus 2 | 4–7k |
| J | `Jac(Θ) ≅ B_n` equivariantly | 2–4k |
| C-Jac | `C ≅ C′ ⇒ Jac C ≅ Jac C′` equivariantly | 0.6–1.2k |
| C (other agent) | `Genus2CanonicalExistence`, `Genus2PencilFunctionField` | in progress |

**Alternative single hypothesis:** `OrdinaryTraceExistence`. It is Tate-free and also suffices
(`deligneBound_of_ordinaryTraceExistence`), at ≥ 20k lines (CM lifting / Deuring reduction).

What the new count buys the Tate route: `deligneBound_of_multLeOne` consumes **only**
`mult ≤ 1`. Any future proof of uniqueness can therefore be plugged in directly, including one
that bypasses `TateFinitenessPolAll` (for example a modular-polynomial upper bound). Before this
session, every such proof also had to re-supply Tate for the per-class count.

## 4. Audit

`nice -n 10 lake build RamanujanWeil.Arith.DeuringFinalAxioms` succeeds (2026-11-10). All 16
audited declarations depend only on `[propext, Classical.choice, Quot.sound]`, including:
* `deuringMultiplicity_uncond`;
* `deligneBound_of_multLeOne`;
* `deligneBound_of_ordinaryTraceExistence`;
* `deligneBound_of_tatePol'`.

There is no `sorry`, `admit`, `native_decide` or `axiom`. No existing file was edited.

Sizes: FinalSite 167, FinalLattice 280, Final 81, FinalAxioms 23 lines. Build times: FinalSite
≈ 310 s, FinalLattice ≈ 290 s (mostly import loading), Final ≈ 160 s.

`exists_latticeMatrix_cls` is stated through an opaque family (`exists_latticeMatrix_famP`). A
direct statement on `G.site` timed out in `whnf`, so it carries `maxHeartbeats 1600000`, and so
does `nonempty_classLattice_of_base_uncond`.
