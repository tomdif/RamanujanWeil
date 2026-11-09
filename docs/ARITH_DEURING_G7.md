# A3-ord, G7: Tate's isogeny theorem — route, blueprint, status (2026-11-09)

This continues `docs/ARITH_DEURING_PLAN.md` (G7, G8), `ARITH_DEURING_PROGRESS{,2}.md`,
`ARITH_DEURING_G1.md` and `ARITH_DEURING_G6.md`. The new files are
`RamanujanWeil/Arith/DeuringG7{Alg,Prod,Tate}.lean`, audited in `DeuringG7Axioms.lean`. No
existing file was edited.

## 0. Summary

1. **The `End` case of Tate is free for ordinary curves (no quotients, no finiteness).** For
   `E` with `t² < 4q`, `End_π(V_ℓE) = ℚ_ℓ[π]` is 2-dimensional. `End_π(E) ⊇ ℤ[π]` has rank 2,
   and its image in `End(T_ℓE)` is saturated (G3, `homAV_saturated`). A saturated full-rank
   sublattice equals the lattice, so `End_π(E) ⊗ ℤ_ℓ = End_π(T_ℓE)`. The same argument gives
   `Hom_π(E,E') ⊗ ℤ_ℓ = Hom_π(T_ℓE, T_ℓE')` as soon as `Hom_π(E,E') ≠ 0` and
   `Hom_π(E',E) ≠ 0`. So the main session's claim holds, and is even stronger: the only new
   geometric input of G7 is **"equal trace ⇒ `Hom_π(E,E') ≠ 0` or `Hom_π(E',E) ≠ 0`."**
2. **Correction to the main-session analysis: the frozen interface also needs existence.**
   `DeuringLattice.surj` asks, for every `M ∈ TrDet t q`, for a curve `W` with
   `traceOfFrob W = t`. `TrDet t q` is never empty (it contains the companion matrix), so `surj`
   includes **Deuring/Honda existence: every ordinary `t` with `t² < 4q` is the trace of some
   `E/𝔽_q`**. Neither Tate uniqueness nor G8(iii), which starts from a curve `E₀` of trace `t`,
   gives that. See §2 for how much this costs.
3. **Route chosen for uniqueness: Tate's gluing argument on `E × E'`, with a points-only proof
   and one named finiteness hypothesis.** Everything except the finiteness is now proved,
   axiom-clean (§3, §5).
   * `DeuringG7Alg`: π-equivariant `u_n : E[ℓⁿ] ≅ E'[ℓⁿ]` by pure algebra, at a prime `ℓ`
     where `X² − tX + q` has no root.
   * `DeuringG7Prod`: `E × E'` is an abelian variety.
   * `DeuringG7Tate`: `QuotientFiniteness (E×E') π ⇒ Hom_π(E,E') ≠ 0 ∨ Hom_π(E',E) ≠ 0`.
4. **Single hardest lemma: `QuotientFiniteness`.** Finitely many `π`-equivariant isomorphism
   classes among the quotients `(E×E')/Γ_n`, that is, finiteness of `𝔽_q`-forms of abelian
   surfaces in an isogeny class. Neither Stacks nor Mathlib has polarizations of abelian
   varieties, dual abelian varieties, Riemann–Roch on abelian varieties, or Hilbert schemes of
   `ℙᴺ` of finite type. Honest estimate **12–30k lines** (§4).

## 1. What downstream actually consumes

`DeuringLattice K t` (`Arith/DeuringAssembly.lean`) has three fields: `rel_iff`, `card_stab`
and `surj`. In route L (plan §4), with `E₀` the curve with `End E₀ = ℤ[π]`:

| field | needs | G7 input |
|---|---|---|
| `rel_iff`, `card_stab` | G1 + G8(ii): `Hom_π(E,E') ≅ Hom_{ℤ[π]}(L E, L E')` for all `E, E'` of trace `t` | **uniqueness**: `Hom_π(E₀, E) ≠ 0` for every `E` of trace `t`, so that `L(E) = Hom(E₀,E)` has rank 2. Then the `Hom ⊗ ℤ_ℓ` statement comes free (§0.1) |
| `surj` | G8(iii): every lattice is `L(E₀/G)` | **existence** of some `E` of trace `t`, so that `E₀` exists |

With uniqueness and existence, `m(t) = 1`. Uniqueness alone gives `m(t) ∈ {0, 1}`.

## 2. Existence (Deuring/Honda) vs uniqueness (Tate) vs counting

* **Counting alone fails** (plan §3, route X): per-class masses are all `H(4q−t²)/2`, so
  `m(t) = 0` at one trace and `m(t') = 2` at another cancel in every lattice-invariant count.
* **Existence + uniqueness via counting.** With route L inside one class,
  `N(t) = m(t)·q³(q−1)H(4q−t²)/2`. The repo's `TorsorCount` and the fact that each `j` has
  `𝔽_q`-twist mass 1 give
  `Σ_{p∤t} N(t) = q³(q−1)·#{ordinary j ∈ 𝔽_q}`. If one also has the identity

      (KH-ord)   Σ_{p∤t, t²<4q} H(4q − t²) = 2·#{ordinary j ∈ 𝔽_q},

  then `Σ_{p∤t} (m(t) − 1)·H(4q−t²) = 0`. Either `m ≤ 1` (Tate) or `m ≥ 1` (existence)
  then forces `m ≡ 1`. Numerics (`scratchpad/g7/kh.gp`, PARI `qfbhclassno`):
  `2q − Σ_{p∤t} H(4q−t²)` is constant in `n`. It equals 2, 2, 2, 2, 4, 2, 4, 4, 6 for
  `p = 2, …, 23` and `n ≤ 7` (`q ≤ 2·10⁶`), i.e. `2·#SS(𝔽_p)`. This agrees with N6.
  **But exact (KH-ord) needs the exact supersingular count `#{SS j ∈ 𝔽_q}`.** That is a
  class-number statement itself (for `q = p` it is essentially `H(4p)`), so this is the
  supersingular half of Deuring. **Not cheaper.**
* **O(1) version (approximate endgame only).** Kronecker–Hurwitz
  `Σ_t H(4N − t²) = 2σ(N) − Σ_{d|N} min(d, N/d)` at `N = pⁿ`, together with the `H(p²N)`
  recursion (`HurwitzPrimeSquare`, whose weight-12 analogue is already used in
  `AssemblyError`), gives `Σ_{p∤t} H = 2q + O_p(1)`. With `#SS ≤ p·q⁴`
  (`supersingularCountBound`), **either** uniqueness **or** existence yields
  `|Σ_t (N(t) − M(t)) h₁₀(t,q)| = O(q⁹)`. That suffices for `IharaApprox` (error
  `< q^{e+6.5}`, `e = 3`), but not for the exact frozen `OrdinaryDeuring`.
  * Cost: weight-2 Kronecker–Hurwitz via Popa–Zagier with `w = 0` (period polynomials are
    constants and `S₂ = 0`, so no analytic input). This is plausibly 1.5–4k lines reusing
    `ESOrbit`/`ESPropA`, plus 0.5–1k for the weight-0 copy of the `AssemblyError` recursion.
* **Existence directly.** Every ordinary `t` occurs (Deuring 1941, Waterhouse Thm 4.1). Known
  proofs go through Honda's CM lifting: a CM elliptic curve over a number field with
  `End = O_K` reduced at a prime over `p`, plus Shimura–Taniyama for the Frobenius. In
  elementary form: the Hilbert class polynomial `H_D(X)` has a root mod `p` with Frobenius trace
  `t`. That needs CM theory over ℂ (`j(O)` algebraic, class field theory), **≥ 20k lines.
  Not recommended.**
* **Recommendation.**
  * Exact `OrdinaryDeuring`: Tate uniqueness (this file, plus finiteness) **plus**
    (KH-ord exact = Kronecker–Hurwitz + supersingular `j`-count). The supersingular count is
    then the only other class-number input. Alternatively, accept existence as a second named
    hypothesis.
  * `IharaApprox` / Deligne bound: Tate uniqueness **or** existence, plus the O(1)
    Kronecker–Hurwitz. Uniqueness is the cheaper of the two.

## 3. The proof of uniqueness modulo finiteness (as formalized)

Setting: `k = 𝔽̄_q`, `E, E'` 1-dimensional abelian varieties with `π, π'`,
`π² − tπ + q = 0 = π'² − tπ' + q`, and `t² < 4q`.

1. **Choice of `ℓ`** (`exists_prime_no_root`). `J(t²−4q | 4(4q−t²) − 1) = −1`: multiply by
   `J(4|·) = 1`, and `−4N ≡ −1`. A prime divisor `ℓ` has `(t²−4q / ℓ) = −1`, so `X² − tX + q`
   has no root mod `ℓ`. In particular `ℓ ∤ q`, so `ℓ ≠ p`.
2. **Gluing data** (`exists_equivariant_addEquiv`). `E[ℓⁿ] ≅ (ℤ/ℓⁿ)²` (Stacks), and `π`
   satisfies `P² − tP + q = 0` on it. Since `f mod ℓ` has no root, `P mod ℓ` is not scalar,
   so one of `e₁`, `e₂`, `e₁ + e₂` is a cyclic vector (`det[v | Pv]` is a unit). So `P` is
   conjugate to the companion matrix, and `E[ℓⁿ] ≅ E'[ℓⁿ]` π-equivariantly. No Tate module,
   trace or compatibility in `n` is used.
3. **Gluing** (`DeuringG7Tate`). `A = E ⊗ E'` (`isAbelianVariety_tensor`),
   `π_A = lift(fst ≫ π, snd ≫ π')`, `Γ_n = {(x, u_n x)}` (finite, `π_A`-stable),
   `q_n : A → B_n` (G6, `exists_quotient_by_finite_subgroup'`), and
   `π_n`, `i_n = (x ↦ (x,0)) ≫ q_n`, `i'_n`, `p_n`, `p'_n` (with `q_n ≫ p_n = fst ≫ [ℓⁿ⁺¹]`),
   all from the universal property.
4. **Points lemmas.**
   * `q_n` is surjective on `k`-points: `[ℓⁿ⁺¹]_A = q_n ≫ s_n`, `s_n ≫ q_n = [ℓⁿ⁺¹]_{B_n}`,
     and `B_n(k)` is divisible.
   * `w ≫ p'_n = 1 ⇒ w ∈ i_n(E(k))`, and `w ≫ p_n = 1 ⇒ w ∈ i'_n(E'(k))`.
   * `i_n(E(k)) ∩ i'_n(E'(k)) = i_n(E[ℓⁿ⁺¹])`, and `i_n` is injective on points, so the
     intersection has `ℓ^{2(n+1)}` points.
5. **Conclusion.** If every π-equivariant homomorphism `E → E'` and `E' → E` is trivial, then
   for an equivariant iso `e : B_n ≅ B_m`, `i_n ≫ e ≫ p'_m = 1` and `i'_n ≫ e ≫ p_m = 1`. So
   `e` maps the intersection into the intersection, and `e⁻¹` maps it back. Hence
   `ℓ^{2(n+1)} = ℓ^{2(m+1)}` and `n = m`. **So `QuotientFiniteness` gives a nonzero
   equivariant hom in one direction.**
6. **(To do, 0.3–0.8k.)** Bridge to `FrobeniusJacobian W` (G2): the relation on points from
   `frob_quadratic`, and dimension 1. Turning "one direction" into "both" uses G3-dual (plan
   0.8–2k), or the quotient trick: for `α : E' → E` nonzero with finite kernel `K` étale,
   `[#K] = α ≫ β` by the G6 universal property applied to `E' → E'/K ≅ E`.

## 4. The finiteness theorem: options and honest costs

`QuotientFiniteness A π_A` (stated in `DeuringG7Tate.lean`): among quotients `A/Γ_n` by finite
`π`-stable étale subgroups, with induced `π_n`, two are equivariantly isomorphic. It is true for
the Frobenius of an `𝔽_q`-structure and false in general (e.g. `π = 𝟙`), so it is stated as a
hypothesis on the specific `(A, π_A)`.

| Option | Ingredients | Stacks/Mathlib status | Estimate |
|---|---|---|---|
| F1 Hilbert scheme | descend a polarization to bounded degree (Zarhin or `λ_E × bλ_{E'}`, see below), `L³` very ample (Lefschetz), fixed Hilbert polynomial, `Hilb_P(ℙᴺ)` of finite type ⇒ finitely many `𝔽_q`-points | Stacks has the **theorem of the cube** (`Cube/TheoremOfTheCube.lean`, 0BF4/0BFE) and Hilbert schemes of curves and points (`Picard/Hilbert*`). **No** theorem of the square on `Pic`, dual abelian variety, polarization, `χ(L) = (Lᵍ)/g!`, Lefschetz, or Hilbert scheme of `ℙᴺ`. `isProjective_of_isAbelianVariety` comes from 0BF7 (quasi-projectivity of group schemes via an ample divisor complement) + 0B45; **there is no degree or embedding-dimension bound, uniform or not** | 20–40k |
| F2 Genus-2 curves (gluing, Frey–Kani) | choose `u_n` anti-symplectic (`e'(ux,uy) = e(x,y)⁻¹`, possible after scaling by `b` with `−b⁻¹ ∈ det(u₀)·N(K_ℓ^×)`). Then `B_n` is principally polarized; a ppas over `k̄` is `Jac(C)`, `g(C) = 2`, or `E₁ × E₂`; genus-2 curves over `𝔽_q` are finitely many (`y² + h(x)y = f(x)`, `deg ≤ 6`); forms are finite since `Aut(B,λ)` is finite | Weil pairing exists only abstractly (`Picard/WeilPairing.lean`). The Jacobian exists (`jacobianGrp`), but there is no theta divisor, Torelli-type decomposition, or hyperelliptic models | 25–45k |
| F3 Point-count bound | — | `#B_n(𝔽_{qʳ})` is the same for all `n`; that does not bound isomorphism classes | **fails** |
| F4 Avoid surfaces | — | the `B_n` are not products when `Hom = 0` (`A₁ ∩ A₂ = E[ℓⁿ]`), so curve-finiteness cannot replace it | **fails** |
| F5 CM lifting (route C) | — | — | ≥ 30k |

Polarization descent detail for F1/F2. On the graph of `u : V_ℓE → V_ℓE'`, the pairing
`e × e'` restricts to `e^{1 + det u}`. With `λ_E × bλ_{E'}` the condition is `1 + b·det u = 0`.
`det u` ranges over a coset of the open subgroup `N(K_ℓ^×)` of index ≤ 2 in `ℚ_ℓ^×`, so a
positive integer `b` exists. So `B_n` gets a principal (F2) or bounded-degree (F1)
polarization. Our formalized `u_n` are arbitrary equivariant isos and need not be isotropic. The
statement of `QuotientFiniteness` does not mention polarizations, so its proof is free to
re-choose `u_n`, at the cost of reproving step 2 with the isotropy constraint (+0.3k).

**Single hardest lemma (both F1 and F2):** an abelian surface over `𝔽̄_p` carries an ample line
bundle of degree bounded uniformly along the family `B_n`, together with the resulting
finiteness. Concretely, for F1: `L` ample on an abelian variety ⇒ `L³` very ample with
`h⁰ = 3ᵍ·√deg φ_L`. That is Mumford §17 (Lefschetz), which needs the theorem of the square,
`K(L)` finite, and vanishing/Riemann–Roch on abelian varieties. None of these is in Stacks.

**Recommendation.** Leave `QuotientFiniteness` as the one named hypothesis for G7. Spend
effort on G8, the bridge (§3.6) and G1. Treat finiteness as a separate, long project (F1 is
the more reusable).

## 5. Status of the Lean files (this session)

All files are axiom-clean: `#print axioms` gives at most `[propext, Classical.choice,
Quot.sound]`. They contain no `sorry`, `admit`, `native_decide` or `axiom`. Build with
`nice -n 10 lake build RamanujanWeil.Arith.DeuringG7Axioms`; this takes about 6 min, mostly
loading imports.

| File | Lines | Imports | Main statements |
|---|---|---|---|
| `DeuringG7Alg.lean` | 229 | Mathlib only | `jacobiSym_neg_eq_neg_one`, **`exists_prime_no_root`**, `isUnit_of_castHom_ne_zero`, `mul_cycMat`, `exists_isUnit_det_cycMat`, **`exists_conj_companion`**, `exists_companion_addEquiv`, **`exists_equivariant_addEquiv`** |
| `DeuringG7Prod.lean` | 39 | G6, Stacks `Cube.GeometricallyIntegralProduct` | **`isAbelianVariety_tensor`** |
| `DeuringG7Tate.lean` | 521 | G7Prod, G3Div | **`QuotientFiniteness`** (def), `Glue` (G6 quotient package), `Glue.cancel`, `Glue.exists_comp_q_eq` (surjective on points), `Γ` (graph), `πA`, `Glue.{i,i',p,p',πB}` and their Frobenius compatibilities, `Glue.exists_eq_of_comp_p'`, `Glue.exists_eq_of_comp_p`, `Glue.i_injective`, `Glue.mem_inter_iff`, `card_tor_le`, **`exists_frobHom_of_quotientFiniteness`** |
| `DeuringG7Bridge.lean` | 116 | G7Tate, G7Alg, G2 | `comp_endPolyEval_quadratic`, `isUnit_of_no_root`, **`tate_exists_frobHom`** |
| `DeuringG7Axioms.lean` | 20 | | audit |

### Headline

```lean
theorem tate_exists_frobHom {K} [Field K] [Fintype K] {W W' : WeierstrassCurve K}
    [W.IsElliptic] [W'.IsElliptic] (J : FrobeniusJacobian W) (J' : FrobeniusJacobian W')
    (ht : traceOfFrob W' = traceOfFrob W) (hlt : traceOfFrob W ^ 2 < 4 * (Nat.card K : ℤ))
    (hfin : QuotientFiniteness (J.A ⊗ J'.A) (πA J.π J'.π)) :
    (∃ α : J.A ⟶ J'.A, IsMonHom α ∧ α ≫ J'.π = J.π ≫ α ∧ α ≠ 1) ∨
      (∃ β : J'.A ⟶ J.A, IsMonHom β ∧ β ≫ J.π = J'.π ≫ β ∧ β ≠ 1)
```

It holds for every `t` with `t² < 4q`, ordinary or not. The one named hypothesis is:

```lean
def QuotientFiniteness (A : Over (Spec (.of k))) [GrpObj A] (πA : A ⟶ A) : Prop :=
  ∀ (Γ : ℕ → Subgroup (Pt A)) (B : ℕ → Over (Spec (.of k))) [∀ n, GrpObj (B n)]
    (q : ∀ n, A ⟶ B n) (πB : ∀ n, B n ⟶ B n),
    (∀ n, Finite (Γ n)) → (∀ n, ∀ x ∈ Γ n, x ≫ πA ∈ Γ n) →
    (∀ n, IsAbelianVariety k (B n)) → (∀ n, IsMonHom (q n)) → (∀ n, IsMonHom (πB n)) →
    (∀ n, q n ≫ πB n = πA ≫ q n) →
    (∀ n, IsFiniteLocallyFreeOfRank (q n).left (Nat.card (Γ n))) →
    (∀ n, Surjective (q n).left) → (∀ n x, x ≫ q n = 1 ↔ x ∈ Γ n) →
    ∃ n m, n ≠ m ∧ ∃ e : B n ≅ B m, IsMonHom e.hom ∧ e.hom ≫ πB m = πB n ≫ e.hom
```

Why it is true for `A = J × J'` with `π_A = π × π'`:
* `q_n` is finite locally free of rank `#Γ_n`, and its geometric kernel has `#Γ_n` points. So
  `ker q_n` is the constant group `Γ_n`, and `B_n ≅ A/Γ_n` canonically.
* `π_n` is determined by `q_n ≫ π_n = π_A ≫ q_n`, because `q_n` is an epimorphism.
* `π`-stable means Galois-stable, so `(B_n, π_n)` is the Frobenius of an `𝔽_q`-form.
* There are finitely many `𝔽_q`-forms in an isogeny class.

The étale-kernel hypotheses rule out infinitesimal π-stable kernels, which need not be
`𝔽_q`-rational.

## 6. Remaining work for G7 and estimates

| Item | What | Estimate | Risk |
|---|---|---|---|
| **G7-fin** | prove `QuotientFiniteness (J×J') (π×π')`, route F1 or F2 (§4) | **12–30k** (F1 20–40k if polarization theory is built in full generality; a surface-only shortcut gets to the low end) | very high |
| G7-dual | one direction ⇒ both (`Hom_π(E',E) ≠ 0 ⇒ Hom_π(E,E') ≠ 0`); the same as PROGRESS2's G3-dual (separable part via `DeuringG3Div` descent, inseparable part via a Frobenius factorization) | 0.8–2k | medium |
| G7-End/Hom ⊗ ℤ_ℓ | `Hom_π(E,E') ⊗ ℤ_ℓ ≅ Hom_π(T_ℓE, T_ℓE')` from `homAV_tensor_injective` + `homAV_saturated` + rank count (commutant of a non-scalar `2×2` is rank 2; `ℤ[π]·α` has rank 2). Needs `HomDualHyp`, i.e. G7-dual | 0.4–0.8k | low |
| Existence (for `surj`) | either Honda/Deuring CM lifting (≥ 20k), or exact (KH-ord) = Kronecker–Hurwitz + exact supersingular `j`-count (class-number input of A3-ss size). Not needed for `IharaApprox` if paired with O(1) KH (1.5–4k) | see §2 | high |

**Total for G7 as stated in the plan (uniqueness + `⊗ ℤ_ℓ`): 13–33k**, almost all of it the
finiteness theorem. That matches the plan's 10–25k for the non-finiteness part being small:
the gluing argument came out at about 0.9k lines, far below the plan's share. **The
`DeuringLattice.surj` existence gap is new** and has to be budgeted separately (§2).
