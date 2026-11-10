# A3-ord, G7 C-descent: `Genus2FrobDescent` (2026-11-10)

Target: `Genus2FrobDescent K` (`Arith/DeuringG7PrincipalFinModel.lean`,
`docs/ARITH_DEURING_G7_PRINCIPAL.md` §1). A smooth proper geometrically irreducible genus-2
curve `X / k̄` with a twisted Frobenius `Ψ` (`Ψ ≫ s = s ≫ F`) is the base change of a genus-2
curve `C / K`, with `Ψ` becoming `id × Spec(frob)`.

**Result.**

```lean
theorem genus2FrobDescent_of_canonical_of_fixed
    (hC : Genus2FrobCanonical K) (hF : Genus2FixedDescent K) : Genus2FrobDescent K
```

What is proved is the middle step: the function-field Frobenius, a hyperelliptic presentation,
and Lang's theorem for the model group. Two named Props remain: the geometric input
(canonical stability) and the scheme-level output (descent once the generators are fixed). No
existing file was edited. There is no `sorry`, `admit`, `native_decide` or `axiom`. Audit:
`RamanujanWeil/Arith/DeuringG7Genus2DescentAxioms.lean`; everything depends only on
`[propext, Classical.choice, Quot.sound]`.

| File | Imports | Content |
|---|---|---|
| `Arith/DeuringG7Genus2DescentLang.lean` | `DeuringDescentLang` (Mathlib + `frobQ`) | `Pres`, `MobForm`, the two moves, Lang for the model group, descent of the coefficients |
| `Arith/DeuringG7Genus2Descent.lean` | Lang, `PrincipalFinModel`, Stacks `DimensionFormula/FunctionField` | `frobFF`, semilinearity, `exists_pres`, the named Props, the reduction |
| `Arith/DeuringG7Genus2DescentAxioms.lean` | both | audit |

## 1. The route

This is the suggested route, done on the function field. Let `L = k̄(X)` and `τ = Ψ^♯`.

1. `τ` is a `σ`-semilinear ring endomorphism of `L`, with `τ(c) = c^q` on `k̄`.
2. `L` has a hyperelliptic presentation, `y² + h(x) y = f(x)` with `L = k̄(x, y)`.
3. (Named: **canonical stability**.) `τ` acts by a model change.
4. Lang's theorem for the model group `{x ↦ (αx+β)/(γx+δ), y ↦ (ey + p(x))/(γx+δ)³}`, done by
   hand, makes `x` and `y` `τ`-fixed. The fixed relation then has coefficients in `K`.
5. (Named: **fixed-generator descent**.) `C` is the regular projective model of
   `K(x)[y]/(y² + h₀ y − f₀)`, with `β : X ≅ C_k̄`.

## 2. Lang's theorem for the model group (`DeuringG7Genus2DescentLang`, fully proved)

Setting: `L / K̄` is a field, and `τ : L →+* L` satisfies `IsFrobSemilinear K τ`
(`τ c = c^q`).

* **`Pres x y h f`**:
  * `y² + h(x) y = f(x)`, with `deg h ≤ 3` and `deg f ≤ 6`;
  * `x` is transcendental over `K̄`;
  * `y ∉ K̄(x)`.
* **`MobForm K τ x y`**: `τ x (c x + d) = a x + b` and `τ y (c x + d)³ = e y + p(x)`, with
  `ad − bc ≠ 0`, `e ≠ 0` and `deg p ≤ 3`.
* **`AffForm`** and **`FixForm`** are the special cases `c = 0`, and `τ x = x`.
* `Pres.change`: let `K̄(x₁) = K̄(x)` and `y₁ = r y + s`, with `r, s ∈ K̄(x)` and `r ≠ 0`.
  Then the new relation transfers `Pres`, and `K̄(x₁, y₁) = K̄(x, y)`.
* **Moves.**
  * `pres_inv` takes `x₁ = 1/(x − z)` and `y₁ = y x₁³`. It uses `invPoly n z p = X^n p(z + 1/X)`,
    which is a polynomial of degree `≤ n` (`aeval_invPoly`).
  * `pres_aff` takes `x₁ = u x + v` and `y₁ = e y + p(x)`, composing with the inverse linear
    polynomial.
* **Lang, in three steps.**
  1. `affForm_of_mobForm`. Take `z` a root of `−c z^{q+1} − d z^q + a z + b`, which has degree
     `q + 1` when `c ≠ 0` (a `τ`-fixed point of `ℙ¹`). Inverting at `z` gives
     `τ x₁ = ((cz+d) x₁ + c)/(a − c z^q)`, with `a − cz^q ≠ 0` and `cz + d ≠ 0` from
     `ad − bc ≠ 0`.
  2. `fixForm_of_affForm`. Take `U^q = U u⁻¹` and `V^q = V − U^q w`; then `x₁ = U x + V` is fixed.
  3. `fixed_of_fixForm`. Take `E^q = E e⁻¹` and `P_i^q = P_i − E^q b_i` for `i ≤ 3`; then
     `y₁ = E y + P(x)` is fixed.

  Each step solves `x^q = a x + b` or `u^{q−1} = a` (`exists_pow_card_eq`, `exists_unit_pow`,
  from `DeuringDescentLang`). Composite: **`exists_fixed_of_mobForm`**.
* **`exists_model_of_fixed`**. Apply `τ` to the relation (`τ_aeval`) and subtract. This gives
  `(h − h^σ)(x) y = (f − f^σ)(x)`. Since `y ∉ K̄(x)`, `h^σ = h`. By transcendence, `f^σ = f`.
  Fixed coefficients lie in `K` (`frobQ_eq_iff`, `eq_map_of_map_frobQ_eq`).
* **`exists_descended_model`** returns `τ`-fixed `x', y'` together with:
  * `Pres x' y' (h₀_K̄) (f₀_K̄)`, with `h₀, f₀ ∈ K[X]` of degrees `≤ 3`, `≤ 6`;
  * `K̄(x', y') = K̄(x, y)`.

## 3. The scheme interface (`DeuringG7Genus2Descent`, proved parts)

* `frobFF s Ψ = Ψ.functionFieldMap` (Stacks `Scheme.Hom.functionFieldMap`).
* **`isFrobSemilinear_frobFF`.** The proof combines:
  * `frobSpec = Spec(frob)` (`specMap_eq_absoluteFrobeniusPow`);
  * `frob c = c^q` (`iterateFrobeniusEquiv_def`, `card_eq_ringChar_pow`);
  * `functionFieldMap_germToFunctionField`, `ΓSpecIso_inv_naturality` and `comp_appTop`,
    applied to `Ψ ≫ s = s ≫ F`.
* **`e₂_eq_top`**: if `[L : K̄(x)] ≤ 2` and `y ∉ K̄(x)`, then `{1, y}` is a `K̄(x)`-basis, so
  `K̄(x, y) = L`.
* **`exists_pres`**: from the proved `PencilData` on `k̄(X)`
  (`genus2PencilExistence_of_canonical_of_pencil genus2CanonicalExistence
  genus2PencilFunctionField`), via `exists_not_mem_adjoin` and `exists_relation` as in
  `PencilData.exists_model`.

## 4. What remains: two named Props

| Named Prop | Content | Estimate |
|---|---|---|
| **`Genus2FrobCanonical K`** (canonical stability) | Let `(x, y)` be any presentation with `k̄(x, y) = k̄(X)`. Then `MobForm K (frobFF s Ψ) x y`. Proof sketch: the pole divisor `D` of `x` is a `g¹₂`, hence `≅ ω` (`h⁰ = 2`, `deg = 2`, Serre duality as in `DeuringG7Genus2Canon`). `Ψ^*` preserves the class of `ω`, which forces `k̄(τx) = k̄(x)`, i.e. Möbius. Also `y ∈ H⁰(3D) = ⟨1,x,x²,x³,y⟩` (integrality of `y` over `k̄[x]` and of `y/x³` over `k̄[1/x]`, from the bounds; `h⁰(3D) = 5`), and `τ H⁰(3D) = (cx+d)⁻³ H⁰(3D)`. Inputs: the orders of vanishing (`Scheme.ord`, `OrderOfVanishing`) or the Riemann–Roch spaces `V_n` of `Genus2.PencilGeom`, and their behaviour under the scheme automorphism `Ψ`. | 0.6–1.2k |
| **`Genus2FixedDescent K`** (descent with fixed generators) | Given `Ψ^♯`-fixed generators `x, y` with a relation over `K`, produce `C`, `β`. Steps: (a) `F₀ = K(x)[y]/(…)` is f.g. of transcendence degree 1, and `C` is its normal projective model (`FunctionFieldCategories`, 0BY1 essential surjectivity), smooth because `K` is perfect. (b) Compute the function field of `C_k̄`: `k̄(C_k̄) ≅ k̄ ⊗_K F₀ ≅ k̄(X)`. (c) `β` comes from `exists_iso_of_functionFieldEquiv` (0BY1 uniqueness), with `C_k̄` regular since it is smooth. (d) Genus 2 and geometric irreducibility of `C` (`GenusCurve/BaseChange`, `β`). (e) Frobenius compatibility: `β ≫ gBC(frob)` and `Ψ ≫ β` agree after `Spec k̄(X) → X` (`functionFieldMap_fromSpecStalk`), so they are equal (`X` reduced, `C_k̄` separated, `isDominant_fromSpecStalk_genericPoint`). | 0.8–1.5k; (b) is the main cost |

The Props are smaller than `Genus2FrobDescent`. In `Genus2FrobCanonical`, Lang's theorem, the
semilinearity and the existence of the presentation are already discharged. In
`Genus2FixedDescent`, the twisted Frobenius is already the standard one on generators defined
over `K`, so no cocycle remains.

## 5. Build

`nice -n 10 lake build RamanujanWeil.Arith.DeuringG7Genus2DescentAxioms`. DescentLang takes about 6 s.
Descent and Axioms take about 2–3 min each, mostly import loading (`PrincipalFinModel`). No new
Stacks modules were built.
