# A2 (Eichler–Selberg): the analytic input, P10–P12

Companion to `docs/ARITH_ES_PLAN.md` and `docs/ARITH_ES_PROGRESS3.md`. Status 2026-11-08.

**Milestone A2 is closed.** `EichlerPeriodInput` (`Arith/ESInput.lean`) is proved axiom-clean.
Together with the algebraic part (`ESMain`), this gives Eichler–Selberg at every prime power for the
Hurwitz class number, unconditionally:

```lean
theorem RamanujanWeil.Arith.ES.Analytic.eichlerPeriodInput : EichlerPeriodInput
theorem RamanujanWeil.Arith.ES.Analytic.eichlerSelberg_all :
    ∀ (p : ℕ) [Fact p.Prime], EichlerSelbergPrimePow Hurwitz.hurwitz p
theorem RamanujanWeil.Ihara.deligneBound_of_Deuring          -- Ihara/FinalES.lean
    (hD : ∀ (p : ℕ) [Fact p.Prime], OrdinaryDeuring hurwitz p) : RamanujanTau.DeligneBound
```

So the Deligne bound for `τ` now depends on one arithmetic hypothesis: A3-ord (ordinary
Deuring–Waterhouse).

## 1. Files

All files are new. No existing file was edited. The `Arith` files live in namespace
`RamanujanWeil.Arith.ES.Analytic`.

| file | lines | content |
|---|---|---|
| `Arith/ESAnalyticTau.lean` | 279 | `|τ(m)|rᵐ ≤ r·e^{24r/(1−r)}`; the operator identity `T_pT_m = T_{pm} + p¹¹[p∣m]T_{m/p}`; the full Hecke relation `Σ_{a∣(n,k)} a¹¹τ(nk/a²) = τ(n)τ(k)` |
| `Arith/ESAnalyticSeries.lean` | 213 | q-series `G c`; termwise derivative; `F̃ = G(cj 0)`; `D^jF̃ = G(cj j)` on ℍ (`j ≤ 11`); `G(cj 11) = (2πi)¹¹Δ`; `Δ(−1/z) = z¹²Δ(z)`; `F̃(z+1) = F̃(z)`; `conj F̃(z) = F̃(−z̄)` |
| `Arith/ESAnalyticBol.lean` | 231 | Bol's identity for holomorphic `f`; `f^{(n+1)} = 0` on ℍ implies `f` is a polynomial of degree ≤ n; `rhoc_poly` |
| `Arith/ESAnalyticModel.lean` | 286 | `E = ℍ → ℂ`, slash action `sl`, `IsSlash`, `ι` (injective, equivariant), `F̃|T = F̃`, `ι ρ = F̃ − F̃|S`, parity |
| `Arith/ESAnalyticHecke.lean` | 211 | root-of-unity sum, reindexing, `Σ_{heckeSet n} F̃|N = τ(n)F̃` |
| `Arith/ESAnalyticNum.lean` | 165 | `f(y) = F̃(iy)`; `|f(y) − e^{−2πy}| ≤ e^{−4πy}/5`; `e^{−π/3} ∈ [0.35, 0.352]` |
| `Arith/ESAnalytic.lean` | 186 | `ρ ∈ W₁₀⊗ℂ`; the identity on the imaginary axis; `Re ρ₈ > 1`, `Im ρ₉ > 1`; `eichlerData`; headline |
| `Arith/ESAxioms4.lean` | 37 | audit (27 declarations) |
| `Ihara/FinalES.lean`, `FinalESAxioms.lean` | 31 | `deligneBound_of_Deuring` |

In total about 1.64k lines, against the 4–8k estimate in PROGRESS3 §3.

## 2. The model (conventions checked against `ESInput`)

* `E := Hs → ℂ`, where `Hs = {z : ℂ | 0 < z.im}` is used as a subtype.
* `sl M f z = (cz + d)¹⁰ · f((az + b)/(cz + d))` when `det M > 0`, and `0` otherwise. There is no
  determinant factor.
  * `IsSlash` holds because of the cocycle `j(MN, z) = j(M, Nz)·j(N, z)` and
    `(MN)z = M(Nz)` (`jf_mul`, `mobC_mul`).
  * `sl (−1) = id` holds because `(−1)¹⁰ = 1`.
* `ι P = (z ↦ Σⱼ Pⱼ zʲ)`. Equivariance `ι(P ᵥ* cmat M) = sl M (ι P)` reduces to
  `Σᵢ act M j i · zⁱ = (az + b)ʲ(cz + d)¹⁰⁻ʲ`. That is `act_hom` transported from ℚ to ℂ through
  `Polynomial.funext` and `aeval` (`act_hom_C`).
* `F = F̃|ℍ` with `F̃(z) = Σ τ(m) m⁻¹¹ e^{2πimz}`.
  * `F_T`: `mobC T z = z + 1`.
  * `F_hecke`: for `N = [[a, b], [0, d]]`, `sl N F̃ (z) = d¹⁰ F̃((az + b)/d)`.
* `ρ_eq`: `sl S F̃ (z) = z¹⁰ F̃(−1/z)`.

## 3. P10: convergence and the Hecke relation

* **Bound on `τ`.** Define `Dom p P :⇔ ∀ n, |pₙ| ≤ Pₙ`. This relation is multiplicative.
  `q∏(1 − qᵏ)²⁴` is dominated by `q∏(1 + qᵏ)²⁴`, and evaluating the latter at `r` gives
  `|τ(m)|rᵐ ≤ r ∏(1 + rᵏ)²⁴ ≤ r·exp(24r/(1 − r))`. The truncations come from the existing
  bridge (`PN_coeff`).
  * For each `x < 1`, `Σ|τ(m)|xᵐ < ∞` (`bd_tau`). This gives convergence on all of ℍ.
  * With `r = 1/14`, the same bound gives the explicit tails in P12.
* **Termwise differentiation.** This is `hasDerivAt_tsum_of_isPreconnected` on the half-plane
  `{Im w > Im z/2}`, with the uniform bound `‖c'ₘ‖·e^{−πm Im z}`.
* **The Hecke relation.** Let `(T_n c)(k) = Σ_{a∣(n,k)} a¹¹ c(nk/a²)`.
  * `hecke_comp`: for every sequence `c`, every prime `p` and every `m ≥ 1`,
    `T_m c(pk) + [p∣k]p¹¹T_m c(k/p) = T_{pm}c(k) + [p∣m]p¹¹T_{m/p}c(k)`. Write all four sums as
    sums of `g(a) = a¹¹c(pmk/a²)` over `(pm).divisors`. The two shifted sums are exactly the terms
    with `p ∣ a`. For `p ∤ a`, the conditions `a ∣ pk` and `a ∣ k` coincide.
  * `tau_hecke`: strong induction on `n` with `p = minFac n`, using `tau_master` twice.
* **`F̃|T^∞ₙ = τ(n)F̃`.**
  * The root-of-unity sum gives `Σ_{b<d} d¹⁰F̃((az + b)/d) = Σ_k τ(dk)k⁻¹¹e^{2πiakz}`.
  * Two reindexings follow, `m = dk` and `K = ak` (`Function.Injective.hasSum_iff`).
  * The `K`-th coefficient of the sum over `a ∣ n` is `Tₙτ(K)/K¹¹ = τ(n)τ(K)/K¹¹`.
  * `sum_heckeSet` converts `heckeSet n` to `Σ_{a∣n} Σ_{b<n/a}`.

## 4. P11: Bol's identity and polynomiality

* `bol` states `D^{n+1}[zⁿf(−1/z)] = f^{(n+1)}(−1/z)/z^{n+2}` on ℍ, for every `f` holomorphic on
  ℍ. The proof is a strong induction with base cases `n = 0, 1`. The step uses
  `D[z^{n+2}f(−1/z)] = (n+2)z^{n+1}f(−1/z) + zⁿf′(−1/z)` together with the hypotheses at `n + 1`
  (for `f`) and at `n` (for `f′`). Iterated derivatives are global `iteratedDeriv`, transported
  along `EqOn` on the open set ℍ (`Set.EqOn.iteratedDeriv_of_isOpen`). `iteratedDeriv_add` and
  `iteratedDeriv_sub` apply through `DifferentiableOn.contDiffOn`.
* `poly_of_iteratedDeriv_eq_zero` is by induction. The induction applies the claim to `f′`, takes
  an explicit antiderivative polynomial, and uses `IsOpen.exists_eq_add_of_deriv_eq` (ℍ is convex).
* `D¹¹ρ = 0` on ℍ:
  `D¹¹F̃(z) − D¹¹F̃(−1/z)/z¹² = (2πi)¹¹[Δ(z) − Δ(−1/z)/z¹²] = 0`. Here
  `D¹¹F̃ = G(cj 11) = (2πi)¹¹ Σ τ(m)qᵐ = (2πi)¹¹Δ`, by `hasSum_cusp` and
  `qExpansion_discriminant_coeff`. Modularity comes from `isModular_of`.
* `ρ_conj`: `ρ(−z̄) = conj ρ(z)` on ℍ. The coefficient vector
  `((−1)ʲρⱼ − conj ρⱼ)ⱼ` therefore vanishes at `−(n+1)i` for every `n`, so it is zero.

## 5. P12: certified `ρ₈ ≠ 0`, `ρ₉ ≠ 0`

We use three evaluations and no `T̃₂` computation.

* `ρ ∈ W₁₀⊗ℂ` (`rhoV_S`, `rhoV_U`, the same proofs as `EichlerData.ρ_S/ρ_U`). By `W_decomp`,
  `ρ = ρ₁₀e0 + ρ₈p⁺ + ρ₉p⁻`.
* On `z = iy`: `ρ(iy) = F̃(iy) + y¹⁰F̃(i/y)`, and `F̃(it) = f(t) ∈ ℝ`. Taking real parts gives
  `R_eq`:

  ```
  f(y) + y¹⁰f(1/y) = Re ρ₁₀·(−1 − y¹⁰) + Re ρ₈·(y² + 3y⁴ + 3y⁶ + y⁸)
                     − Im ρ₉·(y + 25/4 y³ + 21/2 y⁵ + 25/4 y⁷ + y⁹)
  ```

  No parity input is needed here. (PROGRESS3 §3 wrote the odd polynomial with alternating signs.
  Along `iy` all of its signs are `+`.)
* Bounds:
  * `|f(y) − x| ≤ x²/5` whenever `x = e^{−2πy} ≤ 1/20`. The tail for `m ≥ 2` is at most
    `(r·e^{24r/(1−r)}/2048)(x/r)²/(1 − x/r)` with `r = 1/14`, and `e^{24/13} ≤ e² < 7.39`.
  * `e^{−π/3} ∈ [0.35, 0.352]`, from `π ∈ (3.1415, 3.1416)`, `e ∈ (2.7182818283, 2.7182818286)`
    and `e^t ∈ [1 + t, 1 + t + t²]` for `t = π/3 − 1`.
  * The five values used are `e^{−2πy} = (e^{−π/3})^k` for `y = 1, 2, 1/2, 3/2, 2/3` (k = 6, 12, 3,
    9, 4).
* `rho_bounds : 1 < Re ρ₈ ∧ 1 < Im ρ₉` follows by `linarith` from the three identities at
  `y = 1, 2, 3/2` and the interval bounds. The exact interval solution, computed with
  `scratchpad/es4/lp.py`, is `Re ρ₈ ∈ [18.2, 19.9]`, `Im ρ₉ ∈ [5.9, 6.5]`,
  `Re ρ₁₀ ∈ [−1.03, −0.95]`. High-precision values are `18.99161…`, `6.15632…` and `−0.98943…`
  (`num.py`; mpmath, 40 digits).

## 6. Build and audit

```
nice -n 10 lake build RamanujanWeil.Arith.ESAxioms4 RamanujanWeil.Ihara.FinalESAxioms
```

Every audited declaration prints `[propext, Classical.choice, Quot.sound]`. This covers 27
declarations in `ESAxioms4`, plus `eichlerSelberg_all` and `deligneBound_of_Deuring`.

The new files contain no `sorry`, `admit`, `native_decide` or `axiom`. Each file elaborates in
about 10 s. The new files are not yet listed in `RamanujanWeil.lean`, which is left unedited.
