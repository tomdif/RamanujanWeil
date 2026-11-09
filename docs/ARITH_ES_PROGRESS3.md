# A2 (Eichler–Selberg via Popa–Zagier): progress log, third session

Companion to `docs/ARITH_ES_PLAN.md` and `docs/ARITH_ES_PROGRESS.md`; plan numbering (P1–P13).
Status 2026-11-08. **The algebraic part of A2 is complete.** What remains is one analytic
input, stated as a single structure (`EichlerData`, §3).

## 1. Done this session (all axiom-clean)

New files in `RamanujanWeil/Arith/`, namespace `RamanujanWeil.Arith.ES`, 1.67k lines. No existing
file was edited.

| file | lines | content |
|---|---|---|
| `ESOrbit.lean` | 344 | `tpow`, orbit sums `oS`, the canonical representative `rep`, orbit regrouping |
| `ESPropA.lean` | 453 | **P8**: the period relations, acyclicity, values on `c = 0` and `d = 0`, `propA_orbit` |
| `ESEigen.lean` | 397 | **P8/P9**: `propA_action`, `e0` eigenvalue `σ₁₁(n)`, trace on `W₁₀` in coordinates |
| `ESInput.lean` | 247 | the analytic interface `EichlerData`; conjugation argument; `traceSum = σ₁₁ + 2τ` |
| `ESMain.lean` | 203 | **P13 (algebraic)**: `esSum`/`hypTerm` form, conditional `EichlerSelbergPrimePow` |
| `ESAxioms3.lean` | 30 | audit |

`lake build RamanujanWeil.Arith.ESAxioms3` prints `[propext, Classical.choice, Quot.sound]` for all
21 audited theorems. The new files have no `sorry`, `admit`, `native_decide` or `axiom`, and they
build without warnings.

### Headline

```lean
theorem eichlerSelbergPrimePow_of_input (h : EichlerPeriodInput) (p : ℕ) (hp : p.Prime) :
    RamanujanWeil.ArithPlan.EichlerSelbergPrimePow Hurwitz.hurwitz p
theorem eichlerSelberg_all_of_input (h : EichlerPeriodInput) :
    ∀ (p : ℕ) [Fact p.Prime], EichlerSelbergPrimePow Hurwitz.hurwitz p
```

The second theorem has exactly the `hES` shape that `Ihara.deligneBound_of_ES_Deuring` takes
(`Ihara/FinalArith.lean`). That file is not imported here, because these files use Mathlib and
`Arith` only.

The proof also gives the general-`n` form:

```lean
theorem esSum_general (h : TauEigenPeriod) {n : ℕ} (hn : 1 ≤ n) :
    esSum Hurwitz.hurwitz n = -2 * τ(n) - Σ_{0<a∣n} min(a, n/a)¹¹
```

### P8: property (A), via orbit sums (`ESOrbit`, `ESPropA`)

This replaces PZ Theorem A, Lemma 3, and Theorem B(b). It does not use P7 (`cS_ptC_eq_neg_one`)
at all.

* **Orbit sums.** Define `oS f M = Σ_{k∈ℤ} f(TᵏM) + f(−TᵏM)` (a `finsum`). The lemma
  `fibre_sum_eq_oS` identifies it with the fibre sum over `{N | rep N = rep M}`. Then
  `sum_smul_eq_zero_of_oS` (*orbit regrouping*) says: if `N ↦ F|N` is invariant under `TᵏN` and
  `−N`, and every orbit sum of `f` vanishes, then `Σ f(N)·F|N = 0`. This is PZ (10), in the form
  in which it is used.
* Let `xiC N = T̃(N) − T̃(S⁻¹N)` be the coefficient function of `(1−S)T̃`, and `aO = oS xiC`, so
  `aO = a(K)`.
  * `aO_S : a(M) + a(MS) = 0`. Proof: the pointwise symmetrised identity `rel1_pt` (from (16a),
    closed by `ring_nf` on explicit entries) gives `(1−S)T̃(1+S) ≡ −(1−S)H`, with
    `H = (1+U+U²)F(1+S)`. Then `oS_hF` shows that `(1−S)(1+U+U²)` has zero orbit sums. This
    takes three `T`-shifts: `U⁻²S⁻¹ = −T`, `U⁻¹ = S⁻¹T⁻¹`, `U⁻¹S⁻¹ = U⁻²T`.
  * `aO_U : a(M) + a(MU) + a(MU²) = 0`. This is pointwise (`rel2_pt`, from (16b)).
  * `aO_rec : a(M) = a(MT) + a(MT′)`.
  * `aO_bd`: `a(M) ≠ 0` implies `|c|, |d| ≤ det M`, by `ptC_support`.
  * `aO_pos` and `aO_cd` (**acyclicity**): `a(M) = 0` when `cd ≠ 0`. Proof: induction on
    `2n + 1 − (c + d)` for a positive second row; other sign patterns reduce to it via `M ↦ MS`
    or `M ↦ −M`.
* **Value on `c = 0`, by direct evaluation** (`aO_c0`, `sum_winW`). On the orbit of
  `[[a,b],[0,d]]` only `T₁(c=0)`, `T₃` and `T₄` at `S⁻¹·` contribute. They contribute the window
  `w3(a−d, x, 0) + w4(0,x,a,d) + w4(0,x,d,a)` in `x = −b`. This window has length `d`, is `1`
  inside, and its endpoints sum to `1` (`½+½`; for `a = d` the endpoints are `⅔ + ⅓`). So
  every residue class mod `d` sums to `1`.
  `aO_d0 : a(M) = −1` for `d = 0`, via `aO_S`.
* **(A), orbit form**, where `T^∞ₙ` is `tinf n = [c=0, det=n, 0≤b<d]` and
  `rhsC n N = tinf n N − tinf n (N S⁻¹)`:

  ```lean
  theorem propA_orbit {n : ℤ} (hn : 0 < n) {M : M2} (hM : M.det = n) :
      oS xiC M = oS (rhsC n) M
  ```
* **(A), action form** (`ESEigen`). This applies to any module `E` over a characteristic-0
  field with `IsSlash sl`, meaning `sl 1 = sl (−1) = id` and `sl(MN) = sl N ∘ sl M` for
  `det M, det N > 0`:

  ```lean
  theorem propA_action [CharZero K] (h : IsSlash sl) {F : E} (hF : sl T F = F) {n : ℕ} (hn : 1 ≤ n) :
      ∑ N ∈ boxM n, (ptCd n N : K) • sl N (F - sl S F) =
        ∑ N ∈ heckeSet n, (sl N F - sl S (sl N F))
  ```

  Here `heckeSet n = {[[a,b],[0,d]] : ad = n, 0 ≤ b < d}` (`mem_heckeSet`).

### P9 (`ESEigen`)

```lean
theorem actR_Ttilde_e0 {n : ℕ} (hn : 1 ≤ n) : actR (Ttilde n) e0 = sig11 n • e0
  -- sig11 n = Σ_{0<a∣n} (n/a)¹¹; from propA_action on V₁₀ with F = Y¹⁰
theorem traceSum_eq_coords (n : ℕ) :
    traceSum n = actR (Ttilde n) e0 10 + actR (Ttilde n) pplus 8 + actR (Ttilde n) pminus 9
```

The second theorem is the trace on `W₁₀` in the basis `wBasis = (e0, p⁺, p⁻)`.

Unconditionally, therefore, `traceSum n = σ₁₁(n) + (p⁺|T̃ₙ)₈ + (p⁻|T̃ₙ)₉`. ES at `n` is
*equivalent* to the cuspidal diagonal summing to `2τ(n)`.

The plan's P9 items "`εT̃ε` satisfies (A)" and "`ker(T̃₂ + 24)`" turned out to be unnecessary.
Complex conjugation replaces `ε`: for a real cusp form `ρ|ε = ρ̄`, and `T̃ₙ` is rational. The
conjugation argument (`TauEigenPeriod.diag`) extracts the two diagonal entries directly. It
uses `W_decomp`, the rational structure of `W₁₀` transported to `ℂ` through `ℚ`-linear
functionals (`Module.forall_dual_apply_eq_zero_iff`).

### P13, algebraic part (`ESMain`)

* `gegenbauer : (d − a)·p₁₀(a + d, ad) = d¹¹ − a¹¹`
* `symTr10_two : p₁₀(2a, a²) = 11a¹⁰`
* `hyp_minus_sig : hypW(a,d)·p₁₀(a+d, ad) − d¹¹ = −min(a,d)¹¹ + [a = d]·(11/6)a¹⁰`
* `par_sum`: the parabolic terms `Σ_{t² = 4n} p₁₀(t,n) = 22·Σ_{a² = n} a¹⁰`. They cancel the
  scalar terms because `hurwitz 0 = −1/12`.
* `hypTerm_eq`: at `n = pᵐ`, `Σ_{0<a∣n} min(a, n/a)¹¹ = hypTerm p m`, using
  `Nat.divisors_prime_pow`.

## 2. The analytic input left open (the only remaining A2 hypothesis)

```lean
structure EichlerData where
  E : Type
  [instG : AddCommGroup E]
  [instM : Module ℂ E]
  sl : M2 → E →ₗ[ℂ] E                      -- P10: (f|M)(z) = (cz+d)¹⁰ f(Mz) on ℍ → ℂ
  isSlash : IsSlash sl                     -- sl 1 = sl (-1) = id, sl (MN) = sl N ∘ sl M (det > 0)
  ι : (Fin 11 → ℂ) →ₗ[ℂ] E                 -- P ↦ (z ↦ Σ_j P_j zʲ)
  ι_inj : Function.Injective ι
  ι_equiv : ∀ M : M2, 0 < M.det → ∀ P, ι (P ᵥ* cmat M) = sl M (ι P)
  F : E                                    -- Eichler integral F̃ = Σ τ(m) m⁻¹¹ qᵐ
  F_T : sl T F = F
  F_hecke : ∀ n : ℕ, 1 ≤ n → ∑ N ∈ heckeSet n, sl N F = (τ n : ℂ) • F
  ρ : Fin 11 → ℂ                           -- P11 (Bol): F̃|(1 − S) is a polynomial
  ρ_eq : ι ρ = F - sl S F
  ρ_conj : ∀ j : Fin 11, starRingEnd ℂ (ρ j) = (-1) ^ (j : ℕ) * ρ j   -- F̃(−z̄) = conj F̃(z)
  ρ_8 : ρ 8 ≠ 0                            -- P12: p⁺-coordinate (numerically 18.9916)
  ρ_9 : ρ 9 ≠ 0                            -- P12: p⁻-coordinate (numerically 6.15632·i)
def EichlerPeriodInput : Prop := Nonempty EichlerData
```

Everything else is proved: membership `ρ ∈ W₁₀ ⊗ ℂ`, the eigen-relation `ρ|T̃ₙ = τ(n)ρ` (via
(A)), and the trace. The intermediate Prop `TauEigenPeriod` is the algebraic shadow of
`EichlerData`: `∃ ρ ∈ W₁₀⊗ℂ`, with `heckeC n ρ = τ(n)ρ` for all `n ≥ 1`, parity, and
`ρ₈, ρ₉ ≠ 0`. The analytic side may target either one (`tauEigenPeriod_of_input`).

Checks that the interface is realisable:

* `T^∞` normalisation: `Σ_{ad=n, b<d} d¹⁰ F̃((az+b)/d) = τ(n)F̃`. This uses the Hecke relation
  `Σ_{a∣(n,N)} a¹¹ τ(nN/a²) = τ(n)τ(N)`.
* `ι` equivariance holds on `ℍ` because `cz + d ≠ 0`.
* The parity condition holds because `τ` is real.
* The coordinates `ρ₈ = 18.99`, `ρ₉ = 6.156i` come from `es/check3.py`.

## 3. Estimates for P10–P12, against this interface

| piece | content | estimate |
|---|---|---|
| P10 | `E = ℍ → ℂ`, slash action and `IsSlash` (cocycle `j(MN,z) = j(M,Nz) j(N,z)`), `ι`, injectivity (polynomial zero on `ℍ`), equivariance | 0.3–0.5k |
| P10 | `F̃` as a `tsum`, convergence from `\|τ(m)\| ≤ e^{24/13}·14^{m−1}` or Mathlib `qExpansion`; `F̃(z+1) = F̃(z)` | 0.3–0.6k |
| P10 | Hecke: the root-of-unity sum `Σ_{b<d} e^{2πimb/d} = d·[d∣m]`, `tsum` regrouping, and the τ Hecke relation (multiplicativity plus the prime-power recurrence, both from `TauHecke*` / `tau_master`) | 0.8–1.5k |
| P11 | Bol for `z¹⁰e^{a/z}` (or `D¹¹ρ = 0` via `F̃⁽¹¹⁾ = c·Δ` and `Δ\|₁₂S = Δ`); termwise differentiation; `g⁽¹¹⁾ = 0` on `ℍ` implies a polynomial of degree ≤ 10 | 1.5–3k |
| P11 | parity `conj ρ_j = (−1)ʲρ_j` from `F̃(−z̄) = conj F̃(z)` | 0.1–0.2k |
| P12 | certified `ρ₈ ≠ 0`, `ρ₉ ≠ 0`, from `R(y) = ρ(iy)` at `y = 1, 2` (plan §2 P12) | 1–2.5k |

Two remarks on P12:

* For real `y`, `R(y) = ρ₁₀(−y¹⁰−1) + ρ₈y²(y²+1)³ + i·Im(ρ₉)·p̃⁻(y)`, where
  `p̃⁻(y) = y − 25/4·y³ + 21/2·y⁵ − 25/4·y⁷ + y⁹` is `p⁻` read along the imaginary axis (the
  odd monomials contribute `i^j y^j`). So two real evaluations separate the even and odd parts
  only together with `ρ₁₀ = −(36/691)ρ₈`. That relation is the `ker(T̃₂+24)` computation (P9
  item, now optional, about 0.2k with a `decide`-checked 11×11 matrix `T̃₂`).
* Alternatively, evaluate `R` at three points.

**Remaining A2 total: about 4–8k lines, all analytic.** The algebraic side is finished.

## 4. Numerical checks (scratch `…/scratchpad/es3/`)

* `orb.py`: `oS((1−S)T̃ₙ)(M) = [c=0] − [d=0]` for every orbit with `|c|, |d| ≤ n + 2`, `n ≤ 12`.
  This is the exact form of `propA_orbit`, checked before the Lean proof.
* `eig.py`, `n ∈ {1,…,6,8,9}`:
  * `e0|T̃ₙ = σ₁₁(n)e0`;
  * `(p⁺|T̃ₙ)₈ = (p⁻|T̃ₙ)₉ = τ(n)`;
  * `p⁻|T̃ₙ = τ(n)p⁻`;
  * `tr_V = (e0T̃)₁₀ + (p⁺T̃)₈ + (p⁻T̃)₉`.

## 5. Build

`nice -n 10 lake build RamanujanWeil.Arith.ESAxioms3`. Each new file elaborates in under 15 s.
The heaviest steps are `rel1_pt` and `rel2_pt` (`ring_nf` over 8 and 12 expanded `ptC`
evaluations).
