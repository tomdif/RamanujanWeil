# A3-ord, G7: `PrincipalFiniteness` reduced to Θ + J and C-descent (2026-11-10)

This continues `ARITH_DEURING_G7DGEOM.md` §5 (the seam `PrincipalFiniteness`),
`ARITH_DEURING_G7D.md` §3, `ARITH_DEURING_G7FIN.md` §2(d), `ARITH_DEURING_G7_GENUS2.md` (step C,
proved) and `ARITH_DEURING_G7_CJAC.md` (C-Jac, proved). New files only:

| File | Imports | Content |
|---|---|---|
| `Arith/DeuringG7PrincipalFinModel.lean` | DGeomFamily, CJacBase, Genus2Pencil | `IsJacobianOf`, `Genus2JacModel`, `ProdJacModel`, **`ThetaJacobianModel`** (Θ + J, named), `Genus2Curve`, **`Genus2FrobDescent`** (C-descent, named) |
| `Arith/DeuringG7PrincipalFin.lean` | Model | `finite_weierstrassCurve`, `exists_equivIso_of_genus2`, `exists_equivIso_of_prod`, **`principalFiniteness_of_thetaJacobianModel`** |
| `Arith/DeuringG7ThetaSwap.lean` | Mathlib only | algebraic core of "Frobenius cannot swap the factors of a product theta divisor" |
| `Arith/DeuringG7PrincipalFinAxioms.lean` | all | audit |

```lean
theorem principalFiniteness_of_thetaJacobianModel (hΘ : ThetaJacobianModel K)
    (hD : Genus2FrobDescent K) : DGeom.PrincipalFiniteness K
```

C and C-Jac are consumed in full. No new named Prop remains on their side.

## 0. Route decision, and two findings about the seam

**Route.** The proved C (finitely many hyperelliptic models over `𝔽_q`) and C-Jac fix the shape of
the argument: every `B_n` gets a finite invariant, and equal invariants give equivariantly
isomorphic `B_n`. The routes that avoid Θ were checked and rejected:

* **Bounded-degree embeddings** (`|3Θ|` into `ℙ⁸`, or F1′'s `ℙ¹⁵`, plus a Hilbert-scheme count).
  This needs Riemann–Roch and vanishing on abelian surfaces, Lefschetz, and closed-immersion
  criteria, none of which are in Stacks. It also still needs the `𝔽_q`-structure (finding 2), so
  it saves nothing.
* **Zarhin / point counts / Hom lattices.** These were ruled out in `ARITH_DEURING_G7FIN.md` §2.

So the cheapest route remains F2′ (Θ, then J, then C), with the gap placed at the cleanest
interface: **a curve over `k̄` with a twisted Frobenius `Ψ`**, which is exactly the input format
of C-Jac.

**Finding 1: the product case is *not* killed inside `PrincipalFiniteness`.**
`DeuringG7FinProd` kills the product case only under the contradiction hypothesis
`Hom_π(E, E') = 0`, which is available inside `exists_frobHom_of_graphFiniteness`.
`PrincipalFiniteness` has no such hypothesis, and products really do occur (Tate holds, so `E`
and `E'` are isogenous). The reduction therefore handles the diagonal product case by its own
pigeonhole, over pairs of Weierstrass curves. That pigeonhole is free: `WeierstrassCurve K ≃ K⁵`.

* The **swap** case (`π` exchanging the two factors) is genuinely impossible: it forces `t = 0`,
  but `p ∤ t`. The algebraic core of this is proved (§3).

**Finding 2: `PrincipallyPolarized` carries no Frobenius compatibility.** The predicate is "some
invertible ample `L` with `h⁰ = 1` on `B_n` over `k̄`". C-descent needs the theta divisor, up to
translation, to be Frobenius-stable.

* Here this is still true. `B_n` lies in an ordinary isogeny class (`E ~ E'`, so
  `End⁰(B_n) = M₂(ℚ(π))`), `π` is central there, so all of `NS(B_n)` is Frobenius-fixed.
  The gap Props are therefore true as stated.
* But their proof must use this fact. It does not follow from the predicate.
* Recommendation for whoever finishes `ThetaLevelDescent`: also record
  `Ψ`-compatibility of `L_n`. It is automatic from Mumford descent of the Frobenius-compatible
  `L ⊠ L'`. Then C-descent can take it as input instead of reproving it.

## 1. The interfaces (`DeuringG7PrincipalFinModel`)

* `frobSpec K = absoluteFrobeniusPow (Spec k̄) p _ (cardExp K)` is the base map of G1's twisted
  Frobenius (`JacSite.Ψ_comp`).
* **`IsJacobianOf s Ψ hΨ σ hσ B π_B`.** Take any big fppf site `S` containing `X` and `Spec k̄`,
  and any `f` with `S.inclusion.map f = s`, together with the curve instances and
  representability. Then there is `e : Pic⁰_{X/k̄} ≅ B` with `IsMonHom e.hom` and
  `e.hom ≫ π_B = jacobianFrobenius(Ψ) ≫ e.hom`.
  * It quantifies over sites because C-Jac compares two curves inside one site. The Jacobian does
    not depend on the site.
* **`Genus2JacModel K B π_B`** is the output of Θ + J. It consists of:
  * a curve `X / k̄`: `IsCurve`, geometrically irreducible, smooth, proper, a projective variety and
    a projective morphism, with `genus = 2`;
  * an automorphism `Ψ` with `Ψ ≫ s = s ≫ F`;
  * a point `σ`;
  * the proof `IsJacobianOf`.
* **`ProdJacModel K B π_B`** consists of elliptic `W₁, W₂` over `K` such that, for all Jacobian
  sites, `(B, π_B) ≅ (J_{W₁} ⊗ J_{W₂}, π₁ ⊗ π₂)`.
* **`ThetaJacobianModel K`** (Θ + J, named). Take the hypotheses of `PrincipalFiniteness`, and `n`
  with `PrincipallyPolarized k̄ (G n).B`. Then `(B_n, π_n)` has a `Genus2JacModel` or a
  `ProdJacModel`.
* **`Genus2Curve K`** is a smooth proper geometrically irreducible genus-2 curve over `K`.
* **`Genus2FrobDescent K`** (C-descent, named). Let `X / k̄` be a curve of genus 2 with an
  automorphism `Ψ` over `F`. Then there are a `C : Genus2Curve K` and `β : X ≅ C_k̄` over `k̄` with
  `β ≫ (id × Spec frob) = Ψ ≫ β`.

## 2. The reduction (`DeuringG7PrincipalFin`, fully proved)

* `equivProd`, **`finite_weierstrassCurve`**: `WeierstrassCurve R ≃ R⁵`.
* **`exists_equivIso_of_genus2`.** Suppose two genus-2 models descend (via `β`, `β'`) to curves
  `C ≅ C'` over `K`.
  1. `CJac.exists_baseChange_iso` base-changes `φ : C ≅ C'` to `α` over `k̄`. The map `α` commutes
     with every Galois twist.
  2. `α' = β ≫ α ≫ β'⁻¹ : X ≅ X'` lies over `k̄` and satisfies `α' ≫ Ψ' = Ψ ≫ α'`.
  3. Take a common site for `{X, X', Spec k̄}` (`BigFppfSite.exists_containing`), with
     `f = homMk s`. Representability comes from `isRepresentable_picardFunctor_of_isSepClosed`.
  4. `CJac.exists_equivariant_jacobianIso` gives `Jac X ≅ Jac X'`. Both models' `IsJacobianOf`,
     taken in that site, give the comparisons with `B` and `B'`.
  5. `CJac.exists_equivIso_of_jac` composes the three isomorphisms.
* **`exists_equivIso_of_prod`.** If the two models have the same `(W₁, W₂)`, fix sites
  `S₁`, `S₂`. Then `e⁻¹ ≫ e'` works (`IsEquivJacIso.symm/trans`).
* **`principalFiniteness_of_thetaJacobianModel`.** Each `n` gets an invariant in the finite type
  `HypModel K ⊕ (WeierstrassCurve K)²`:
  * genus-2 case: the hyperelliptic model of the descended curve
    (`Pencil.genus2ModelExistence`, proved);
  * product case: `(W₁, W₂)`.

  Pigeonhole (`Finite.exists_ne_map_eq_of_infinite`) gives `n ≠ m` with equal invariants. Equal
  models give `C_n ≅ C_m` (`exists_iso_of_hypModel`, Tag 0BY1, using regularity from
  smoothness), and then `exists_equivIso_of_genus2`. Equal pairs give
  `exists_equivIso_of_prod`. Mixed cases cannot occur.

Composed with the existing seam:
`DGeomGapsAll ∧ ThetaLevelDescent ∧ ThetaJacobianModel ∧ Genus2FrobDescent ⇒`
`ThetaDescentFiniteness ⇒ Deligne` (`thetaDescentFiniteness_of_split`).

## 3. The swap case (`DeuringG7ThetaSwap`, core proved)

**`two_mul_trace_mul_card_smul_eq_zero`.** Let `M` be an abelian group with `π² − tπ + q = 0`, and
let `φ` be injective with `π ∘ φ = −φ ∘ π`. Then `2tq · x = 0` for all `x`.

* For `M = B(k̄)`, `φ = (x, y) ↦ (x, −y)` and `π` the swap, this contradicts the existence of
  points of order `ℓᴺ` (`ℓ ∤ 2tq`).
* So the product case of Θ is diagonal.
* Still part of `ThetaJacobianModel`: the geometric glue. That is, points of
  `C₁ ⊗ C₂`, the relation on `B_n(k̄)` (from `E × E'` through the surjective `q_n`), and high-order
  `ℓ`-power points. Estimate ≈ 0.2 k.

## 4. What remains

| Named Prop | Content | Estimate |
|---|---|---|
| **`ThetaJacobianModel K`** (Θ + J) | **Θ.** `Θ_n = Z(s)` is an effective Cartier divisor with `p_a = 2`, from adjunction with `K_B = 0` and `Θ² = 2 = 2χ(L)` (Riemann–Roch on abelian surfaces, or Mumford's `χ(L)² = deg φ_L`, which is `1` here). If irreducible, it is smooth of genus 2: a singular irreducible `Θ` would have geometric genus `≤ 1`, and an abelian surface is not generated by a rational or elliptic curve with `Θ² = 2`. If reducible, `Θ = C₁ + C₂` with `C₁·C₂ = 1` and `B ≅ C₁ × C₂`. Frobenius stability of `NS` (finding 2) gives a `Ψ`-stable translate. The product is diagonal (§3), and its factors are elliptic curves over `K` with Weierstrass models (Lang). **J.** The Albanese map `Jac(Θ) → B` is an isomorphism: an isogeny of degree `Θ²/2 = 1`, or Torelli for `Θ` principal. It is equivariant for `jacobianFrobenius(Ψ)`. Plus site independence of `jacobianGrp`. | Θ 4–6k, J 2–3.5k (Stacks has `ThetaPolarization` for the converse direction only, and no Albanese universal property) |
| **`Genus2FrobDescent K`** (C-descent) | Galois descent along `k̄/𝔽_q` for a projective genus-2 curve with a twisted Frobenius. Finite `Aut` makes the descent datum continuous. Alternatively: `k̄(X)^Ψ` via Lang's theorem for `GL_N` (`H¹(Ẑ, GL_N(k̄)) = 1`), then the regular projective model, then base-change compatibility. | 0.6–1.2k |

The total remaining for `PrincipalFiniteness` is ≈ 7–11k lines, with Θ the high-risk core. This
is unchanged from the `ARITH_DEURING_G7D.md` estimate minus C and C-Jac, which are now
consumed.

## 5. Audit

`nice -n 10 lake build RamanujanWeil.Arith.DeuringG7PrincipalFinAxioms` (2026-11-10). All audited
declarations depend only on `[propext, Classical.choice, Quot.sound]`:

* `finite_weierstrassCurve`
* `exists_equivIso_of_genus2`
* `exists_equivIso_of_prod`
* `principalFiniteness_of_thetaJacobianModel`
* `two_mul_trace_mul_card_smul_eq_zero`

There is no `sorry`, `admit`, `native_decide` or `axiom`. No existing file was edited, and
`RamanujanWeil.lean` is unchanged.

Build time is ≈ 5 min per file, almost all of it import loading.
