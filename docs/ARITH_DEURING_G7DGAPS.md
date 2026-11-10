# A3-ord, G7-D-gaps: the divisor bridge is proved (2026-11-10)

This continues `ARITH_DEURING_G7DGEOM.md` §6, which listed the three inputs bundled in
`DGeomGaps`. **`RRStabilizerBridge` is now a theorem** for every `N ≥ 2`, which covers every level
`N = ℓⁿ⁺¹` used by `thetaFamilyOf`. `ThetaHeisenberg` and `AbelJacobiMathlib` are still named
inputs. New files only, audited in `RamanujanWeil/Arith/DeuringG7DGapsAxioms.lean`:

| File | Content |
|---|---|
| `Arith/DeuringG7DGapsVal.lean` | the valuation `vR`/`vK` at `O` via the norm degree; `L(N·O) = {r ∈ R : vR r ≤ e^N}` |
| `Arith/DeuringG7DGapsConj.lean` | the conjugation `σ = [−1]^*` of `F[E]`; `σ(m_Q) = m_{−Q}`; the degree of `m_Q^N` |
| `Arith/DeuringG7DGapsTransl.lean` | Mathlib's addition formula for `ξ − Q`; `τ_{−Q} L(N·O) ⊆ m_Q^{−N}`, regular at `O` |
| `Arith/DeuringG7DGapsBridge.lean` | **`rrStabilizerBridge : 2 ≤ N → RRStabilizerBridge W N`** |
| `Arith/DeuringG7DGapsAll.lean` | `dGeomGaps_of`, `dGeomGapsAll_of`, `deligneBound_of_gaps` |
| `Arith/DeuringG7DGapsAxioms.lean` | audit |

## 0. The route taken

We use no general divisor theory. Points are handled in two ways:

* **Affine points** use Mathlib's fractional ideals of the coordinate ring `R = F[E]` and the units
  `m_Q = XYIdeal' Q`. The key fact is Mathlib's `XYIdeal_neg_mul`: `m_{−Q} · m_Q = (x − x_Q)`.
* **The point `O`** uses a single valuation, `vR r = exp(deg_X N_{R/F[X]}(r))`. Mathlib's
  `degree_norm_smul_basis` gives `deg N(p + qY) = max(2 deg p, 2 deg q + 3)`. The two terms have
  different parities, so they never cancel and the valuation is ultrametric. It extends to
  `vK` on `K = F(E)` through `Valuation.extendToLocalization`.

We never need `ord_Q ∘ τ_P = ord_{Q+P}` in general. What we use is the explicit pole structure of
`τ_{−Q} x` and `τ_{−Q} y`, read from Mathlib's chord formula for `ξ + (−Q)_K`. The "degree of a
principal divisor is zero" step is replaced by taking norms with the conjugation `σ`.

## 1. Valuation at `O` (`Val`, `Conj`)

* `vR : Valuation R ℤᵐ⁰`, with `vR x = e²`, `vR y = e³` and `vR c = 1` for `c ∈ F^×`.
  `exists_const_of_vR_le_one` says: if `r ≠ 0` and `vR r ≤ 1`, then `r ∈ F`.
* **`rrSpace_eq_LN`**: `L(N·O) = {r ∈ R : vR r ≤ e^N}`. Here `rrSpace` is the span of
  `xⁱ, xʲy` from `DeuringG7DGeomTheta`.
* `conj` is the `F[X]`-algebra map `Y ↦ −Y − a₁X − a₃`. It satisfies `N(σ r) = N r`, so
  `vR(r σ r) = (vR r)²`. It also satisfies `map_conj_XYIdeal : σ(m_Q) = m_{−Q}`.
* **`vR_of_pow_eq_span`**: if `m_Q^N = (r)`, then `vR r = e^N`. Proof: applying `σ` and
  multiplying gives `(r σ r) = ((x − x_Q)^N)`.
* **`pow_eq_span_of_le`**: if `m_Q^N ≤ (r)` and `vR r ≥ e^N`, then `m_Q^N = (r)`. Proof: write
  `m_Q^N = (r) I`. Then `((x − x_Q)^N) = (r σ r) · I σ(I)`, and the valuation forces the cofactor
  to be a unit, so `I σ(I) = (1)`.

## 2. Translations (`Transl`)

Let `Q = (x₀, y₀)` and `P = −Q = (x₀, y₁)`. Put `ℓ = (y − y₁)/(x − x₀)`. Then:

* `transX_neg`: `τ x = ℓ² + a₁ℓ − a₂ − x − x₀`;
* `transY_neg`: `τ y = −(ℓ(τx − x) + y) − a₁τx − a₃`.

These are Mathlib's `add_of_X_ne`, applied using the transcendence of `x`.

* **`lam_mem`**: `ℓ ∈ m_Q⁻¹`. This holds because `y − y₁ ∈ m_P` and `(x − x₀)⁻¹ ∈ (m_P m_Q)⁻¹`.
  It follows that `τ x ∈ m_Q^{−2}` and `τ y ∈ m_Q^{−3}`, and hence
  **`trans_rr_mem`**: `τ L(N·O) ⊆ m_Q^{−N}`.
* **`vK_transX_le_one`**: `τ x · (x − x₀)² = x₀x² + Ax + B + Cy` modulo the curve equation. The
  right side has `vK ≤ e⁴`, so `τ x` is regular at `O`.
* **`vK_transY_le_one`**: `τ y` satisfies the Weierstrass equation over `τ x`. By the strict
  ultrametric inequality it is regular at `O`.
* Together these give **`vK_trans_rr_le_one`**.

## 3. The bridge (`Bridge`)

```lean
theorem rrStabilizerBridge {N : ℕ} (hN : 2 ≤ N) : RRStabilizerBridge W N
```

* **(⇐)** Suppose `m_Q^N = (r)`. Then `r · τ V ⊆ m_Q^N m_Q^{−N} = R`, with `vK ≤ e^N`, so
  `r · τ V ⊆ V`. Both spaces have the same dimension, so `(r, −Q) ∈ 𝒢(V)`.
* **(⇒)** Suppose `f · τ V = V`. Then:
  * `f ∈ V ⊆ R`;
  * `f⁻¹ ∈ τ V ⊆ m_Q^{−N}`, so `m_Q^N ≤ (f)`;
  * some `w ∈ V` has `vK w = e^N`, namely `x^k` or `x^k y` (`exists_rr_exact`). This uses
    `N ≥ 2` and gives `vR f ≥ e^N`;
  * `pow_eq_span_of_le` then gives `m_Q^N = (f)`.

For `N = 1` the bridge is false. Then `L(O) = F` is stabilized by every translation, while `m_Q`
is never principal. The hypothesis `2 ≤ N` is therefore necessary, and every level `ℓⁿ⁺¹` meets it.

No `IsAlgClosed` assumption is needed. (`one_mem_rrSpace` and the finite-dimensionality instance of
`DeuringG7DGeomTheta` silently carry `[IsAlgClosed F]`, so they were reproved without it.)

## 4. Assembly (`All`)

* `dGeomGaps_of : ℓ.Prime → AbelJacobiMathlib W S → (∀ n, ThetaHeisenberg (Wbar W) (ℓⁿ⁺¹)) →
  DGeomGaps W S ℓ`.
* `AbelJacobiAll K` and `ThetaHeisenbergAll K` are named. Together they give
  `dGeomGapsAll_of : … → DGeomGapsAll K`.
* `deligneBound_of_gaps : DGapsSplitAll → RamanujanTau.DeligneBound`, where `DGapsSplitAll` is
  AJ + Heisenberg + `ThetaLevelDescent` + `PrincipalFiniteness` at every finite field.

## 5. What remains

| Item | Why it is not cheap | Estimate |
|---|---|---|
| `ThetaHeisenberg` (Weil-pairing nondegeneracy on `E[ℓⁿ⁺¹]`) | Every route needs `#E[N] = N²` for `char ∤ N`, which Mathlib does not have. On top of that it needs either the Galois theory of `[N]^*` (Silverman III.8.1) or the irreducibility of `L(N·O)` under `𝒢` (Mumford §23). Note that it is false when `char ∣ N` (ordinary curves), so any proof must use `IsUnit ℓ`. A cheap partial step: Schur's lemma plus `N ≥ 3` reduces it to the irreducibility of the `𝒢`-module `L(N·O)`. | 1.5–2.5k |
| `AbelJacobiMathlib` | This needs a bridge from line bundles on the scheme `E_W` to `F(E)`-divisors. Concretely, one must show `𝒪(P) ⊗ 𝒪(Q) ⊗ 𝒪(R) ≅ 𝒪(3·O)` for collinear `P, Q, R` via the line function. There is nothing in the repository yet connecting `Pic` of `projOf W` with Mathlib's `ClassGroup`/`Point`. Rigidity alone does not help, because the Mathlib law is not given by a scheme morphism. | 1.5–3k |

## 6. Audit

`nice -n 10 lake build RamanujanWeil.Arith.DeuringG7DGapsAxioms` succeeds (2026-11-10; `All` 322 s,
`Axioms` 150 s, mostly import loading; Val/Conj/Transl/Bridge ≈ 10 s each). All 21 audited
declarations, including `rrStabilizerBridge`, `dGeomGapsAll_of` and `deligneBound_of_gaps`, depends only on `[propext, Classical.choice, Quot.sound]`. There is no `sorry`,
`admit`, `native_decide` or `axiom`. No existing file was edited, and `RamanujanWeil.lean` is
unchanged.
