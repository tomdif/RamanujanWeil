# A2 blueprint: Eichler–Selberg for S₁₂(SL₂ℤ) via Popa–Zagier

Status 2026-11-08. This document chooses a route and lists every lemma, each checked
numerically. It also records the first algebraic Lean files, which are axiom-clean.
Scripts are in the session scratch directory `…/scratchpad/es/` (§5).

## 0. Decision

**Route PZ**: A. Popa and D. Zagier, *An elementary proof of the Eichler–Selberg trace
formula*, arXiv:1711.00327 (J. reine angew. Math., 2019). It is the 2017 completion of Zagier's
1990/93 period-polynomial programme, and it is strictly better than all three candidates in the
brief.

* The **class-number side is purely algebraic**. One explicit, finitely supported element
  `T̃ₙ ∈ ℚ[Mₙ/±1]` (PZ eq. (15)) has three properties:
  * (B) `T̃(1+S) ∈ (1+U+U²)R` and `T̃(1+U+U²) ∈ (1+S)R`. Consequence:
    `tr(T̃ | W) = tr(T̃ | V)`.
  * (C) the per-trace coefficient sums of `T̃` are minus Hurwitz class numbers. Consequence:
    `tr(T̃ | V) = −Σ_t p₁₀(t,n) H(4n−t²)`.
  * (A) the Choie–Zagier/Merel condition `(1−S)T̃ − T^∞(1−S) ∈ (1−T)R`. Consequence: `T̃` acts
    on period polynomials as the Hecke operator `T_n`.

  This replaces Zagier's 1990 "hardest single lemma" (ARITH_ROUTE §3, A2 step 5), and it needs
  no conjugacy-class counting of reduced matrices beyond one fundamental-domain count.
* **The analytic input is minimal.** No L-functions, Mellin transforms, path integrals,
  Petersson products, or Eichler–Shimura bijectivity are needed. Because dim S₁₂ = 1, we need
  only:
  1. the Eichler integral `F̃ = Σ τ(m) m⁻¹¹ qᵐ`, which is pure q-series;
  2. Bol's identity, used only for exponentials `z¹⁰e^{a/z}`, to show `ρ = F̃|(1−S)` is a
     polynomial;
  3. two certified numerical nonvanishings: `ρ` has nonzero components along both `p⁺` and `p⁻`.
     This replaces "`ρ⁻ ≠ 0` via `L(Δ,10) ≠ 0`" and removes any need for RamanujanTau's
     L-function files.
* **General `n` costs nothing extra.** The argument is uniform in `n`, so we prove ES for every
  `n ≥ 1` and specialise to `n = pᵐ`.

Rejected routes:

* **(a) Zagier 1990.** It needs the trace of `T̃ₙ` on W computed via reduced matrices, which is
  superseded by PZ Theorem 1.
* **(b) Classical Eichler/Selberg.** The class-number side is as easy as in PZ: our A1 forms plus
  the matrix↔form bijection. The other side needs an analytic trace (Selberg kernel, or a
  Lefschetz formula on differentials), with no period shortcut.
* **(c) Cohen–Zagier holomorphic projection.** It needs the modularity of the weight-3/2
  non-holomorphic Zagier series ℋ.

The user-suggested shortcut ("algebraic class-number formula on W⁻, plus λ(n) = τ(n) via one
analytic input") is exactly what PZ make possible. One correction: an algebraic argument cannot
show that λ⁺ = λ⁻ on the two cuspidal lines of W. Every purely algebraic fact is consistent with
`ρ⁻ = 0`, and this was checked: the hypothetical world has the same traces. So the one analytic
input must be the nonvanishing of **both** components of `ρ_Δ`, as in §2 P12. The certified
numerics are robust: `R(2)/R(1) = 11842` versus `68` or `68.29` if either component vanished.

## 1. The proof in one page

Notation:

* `V = V₁₀` is the space of homogeneous polynomials of degree 10, with the right action
  `P|M (X,Y) = P(aX+bY, cX+dY)`. Matrices are taken modulo ±1.
* `S = [[0,−1],[1,0]]`, `U = [[1,−1],[1,0]]`, `T = [[1,1],[0,1]] = −US`.
* `W = ker(1+S) ∩ ker(1+U+U²)`.
* `p₁₀(t,n) = symTrace 10 t n`.
* `H` is extended by `H(0) = −1/12` and `H(−u²) = −u/2`, and is 0 for other negative arguments.

1. `tr(M | V) = p₁₀(tr M, det M)` **[P1, done]**. Since `dim W = 3` and `V = A + B` **[P2, done]**,
   (B) gives `tr(T̃ₙ | W) = tr(T̃ₙ | V)` **[P2+P9a, done modulo (B)]**.
2. (C) is a per-trace identity: `Σ_{M∈supp T̃ₙ, tr M=t} c_M = −H(4n−t²)` for elliptic `t`, with
   explicit hyperbolic and parabolic values. It gives
   `tr(T̃ₙ | V) = −Σ_{t∈ℤ} p₁₀(t,n) H(4n−t²) =: CN(n)`.
3. By (A), `e0 = X¹⁰−Y¹⁰ = Y¹⁰|(S−1)` is an eigenvector with eigenvalue `σ₁₁(n)`. Also
   `ρ := F̃|(1−S)` and `ρ|ε` are eigenvectors with eigenvalue `τ(n)`, and lie in W (Bol plus the
   group-ring identities). Here `ε = diag(−1,1)`; `εT̃ε` also satisfies (A).
4. `T̃₂` acts on W with eigenvalues 2049, −24, −24. Its −24-eigenspace is
   `⟨b₀ := p⁺ − (36/691)e0, p⁻⟩` (explicit linear algebra). Writing `ρ = βb₀ + γp⁻`, the
   numerics give `β ≠ 0` and `γ ≠ 0`. So `b₀` and `p⁻` are both `τ(n)`-eigenvectors, and
   `{e0, b₀, p⁻}` is an eigenbasis of W.
5. Therefore `tr(T̃ₙ | W) = σ₁₁(n) + 2τ(n) = CN(n)`. Splitting off the hyperbolic and parabolic
   terms, `Σ_{t²≤4n} p₁₀(t,n)H(4n−t²) = −2τ(n) − Σ_{d∣n} min(d,n/d)¹¹`, which is
   `esSum H n = −2τ(n) − hypTerm` at `n = pᵐ`. That is `EichlerSelbergPrimePow hurwitz p`
   (exact, not just approx).

## 2. Lemma list (statements; ✔ = Lean, axiom-clean; ☐ = planned)

All files are in `RamanujanWeil/Arith/`, namespace `RamanujanWeil.Arith.ES`. Each file imports
only Mathlib, the earlier ES files, and later `Tau`, TauHecke* and Hurwitz*.

### P1 `ESAction.lean` ✔ (212 lines)
- `M2` is a structure `⟨a,b,c,d⟩ : ℤ⁴` with `Mul`, `One`, `Neg`, `Monoid`, `det`, `tr`, and
  `det_mul`. It defines `S U T eps`, and `T_eq_neg_U_mul_S`.
- `act M : Matrix (Fin 11) (Fin 11) ℚ` has entries
  `act M j i = [XⁱY¹⁰⁻ⁱ](aX+bY)ʲ(cX+dY)¹⁰⁻ʲ`.
- `act_hom`: `Σᵢ act M j i xⁱy¹⁰⁻ⁱ = (ax+by)ʲ(cx+dy)¹⁰⁻ʲ`.
- `act_mul`: `act (M*N) = act M * act N`.
- `act_neg`: `act (−M) = act M`.
- `trace_act`: `tr (act M) = symTr10 (tr M) (det M)`. `symTr10` is verbatim
  `Ihara.symTrace 10`; the file does not import Ihara.

### P2 `ESPeriod.lean` ✔ (432 lines)
- `rAct M = vecMulLinear (act M)`, with `rAct_mul : rAct (M*N) = rAct N ∘ rAct M`, plus `rAct_neg`
  and `rAct_one`.
- `ev`, `ev_rAct`, `eq_of_ev`: the polynomial-evaluation characterisation.
- `litS`, `litU`, `litU2` are the explicit matrices, with `rAct_S/U/U2` and `vecMul_litS/U/U2`.
- `Aker = ker(1+S)` (dim 6), `Bker = ker(1+U+U²)` (dim 8), and `Wper = Aker ⊓ Bker`.
- `sup_eq_top : Aker ⊔ Bker = ⊤`, via the explicit decompositions `decA i + decB i = eᵢ`, checked
  by `decide +kernel`.
- `e0_mem`, `pplus_mem`, `pminus_mem`, and `eq_of_mem_Wper : P = P₁₀e0 + P₈p⁺ + P₉p⁻`.
- `Wper_eq_span` and `finrank_Wper : finrank Wper = 3`.
- `trace_eq_trace_restrict_inf`, the abstract linear algebra behind PZ Prop. 3: if `A ⊔ B = ⊤`
  and `f(A) ⊆ B`, `f(B) ⊆ A`, then `tr f = tr(f|_{A⊓B})`. The proof uses relative complements
  `A⊓Q` and `B⊓Q` and the idempotent trick `tr(fp) = tr(pfp) = 0`.

### P3 `ESGroupRing.lean` ✔ (77 lines)
- `R = MonoidAlgebra ℚ M2`.
- `actR : R → End V` is an anti-homomorphism, via `MonoidAlgebra.lift` into `(End V)ᵐᵒᵖ`.
- `actR_of`, `actR_single`, `actR_mul`, `actR_add`, `actR_smul`, `actR_sum`, `actR_one`.
- `trace_actR_sum : tr(·|Σ cᵢMᵢ) = Σ cᵢ symTr10(tr Mᵢ, det Mᵢ)`.

### P4 `ESTtilde.lean` ✔ (80 lines) + ☐ P4b
- `w3`, `w4` are the PZ boundary weights (1, ½, ¼, ⅙). `ptC M` is the coefficient of `M` in PZ
  (15). `Ttilde n = Σ_{M∈[−n,n]⁴, det=n} ptC M · M`.
- `trace_Ttilde : tr(·|T̃ₙ) = traceSum n`.
- `traceSum_small : traceSum 1,2,3 = 3, 2001, 177652`, i.e. `σ₁₁(n) + 2τ(n)`, by
  `decide +kernel`. This is a guard that the Lean weights are PZ's.
- ☐ P4b `ptC_support`: `ptC M ≠ 0 ∧ det M = n ≥ 1 → |a|,|b|,|c|,|d| ≤ n` (checked n ≤ 40).
  Needed so that the box truncation is the full `T̃ₙ` when we prove (B)/(C)/(A) pointwise.
  The bound follows from `n = ad − bc` together with the second-line sign conditions: each
  term is a sum of nonnegative products. PZ Lemma 4(a) gives the finiteness. Estimate: 150–300
  lines.

### P9a `ESTraceW.lean` ✔ (89 lines)
- `nf` normalises the sign. `EqPM x y :⇔ mapDomain nf x = mapDomain nf y`, i.e. equality in
  `ℚ[M/±1]`, and `actR_nf`.
- `PropB x :⇔ x(1+S) ≡ (1+U+U²)y₁ ∧ x(1+U+U²) ≡ (1+S)y₂` (mod ±).
- `trace_eq_trace_Wper : PropB x → tr(·|x) on V = tr on Wper`. This is PZ Prop. 3 in full.

### P5 ☐ `ESPropB.lean`: (B) for `T̃ₙ` via PZ (16). Estimate 2–4k lines; risk medium (tedious)
- (16a) `T̃ = −F − UFS − U²F + T₁(1−S)`.
- (16b) `T̃ = −G − SGU + T₁(1−U) + (1/12)[a−d=c=−b; d≤0<a](1−U)`.

  Here `F = ⟨0≤a−d≤c; a−d≤−b | d≤b<0<c⟩`, `G = ⟨0≤a−d≤c; a−d≤−b; a≤−b−c | a≤0; b<0<c⟩*`,
  and `T₁ = ⟨a−d≤−b≤c | 0≤c<a⟩` (weights as in PZ §4). These give
  `T̃πS = −(1+U+U²)FπS` and `T̃πU = −(1+S)GπU`, hence `PropB (Ttilde n)`.
- Lean shape: both sides are finite sums. Compare coefficients pointwise as functions of
  `M ∈ ℤ⁴/±`, using the coefficient of `γξγ'` at `M` = coefficient of `ξ` at `γ⁻¹Mγ'⁻¹`.
  Prove each pointwise identity by PZ's own region decomposition (T₃,₁ = T₃,₁ₐ + T₃,₁ᵦ, …),
  closing each region with `omega`/`split_ifs`. Do not brute-force `split_ifs` on everything:
  that is about 2⁴⁰ branches.
- Verified: (16a), (16b), and (B) itself as exact `ℚ[M_n/±]` identities, for
  n = 1–10, 12, 16, 25, 27, 32, 49 (`check2.py`, `check4.py`).

### P6 ☐ `ESPropC.lean`: per-trace sums = class numbers. Estimate 2–4k lines
- Lemma 4: (15) equals (14), i.e. `T̃ = −E + H + X − SXS + Y − U²YU + Z − U²ZU`, with:
  - `E = Σ_{M elliptic, c>0} χ_F(z_M)M` (fundamental domain `F = {0≤Re z≤½, |z−1|≥1}`, angle
    weights); in matrix terms `E = ⟨0≤a−d≤−b; a−d≤c | b<0<c⟩`;
  - `H = ⟨a−d≤−b≤c | c=0<a⟩`;
  - `X = ⟨0≤a−d; −b≤c | b<0<d⟩`;
  - `Y = ⟨a−d≤−b≤c | 0<c<a⟩`;
  - `Z = ⟨a−d≤c≤−b | 0<a; 0<c⟩`.

  This is a pointwise identity, like P5. Verified for n ≤ 12, 16, 25, 27, 32, 49.
- The conjugation terms `ξ − γξγ⁻¹` have zero per-trace sums: reindex by `M ↦ γMγ⁻¹`, which is
  a bijection on `{det = n, tr = t}`. Pure algebra.
- `E_count`: for `t² < 4n`, `Σ_{M∈E, tr M=t} χ(M) = H(4n−t²)` (`hurwitz`). Proof via the
  Γ-equivariant bijection `M ↦ [c, d−a, −b]` (disc `t²−4n`). The F-conditions read:
  `−A ≤ B ≤ 0` and `C ≥ −B`. Split:
  - F⁺ = `{C ≥ A}`, the reduced forms with `B ≤ 0`;
  - F⁻ = `{C ≤ A}`, which `S` maps to reduced forms with `B ≥ 0`.

  Boundary weights ½ and ⅓ then match `wt6/6`. Reuse `HurwitzBasic.redPairs/wt6` and
  `hurwitz_eq_hurwitzClasses`. Verified (`check4.py`, every t, n ≤ 49 sampled).
- Hyperbolic/parabolic: only `H` contributes. The per-trace sum at `t = a+d`, `ad = n`, `a < d`
  is `d−a` (and ⅙ for a scalar). Hence
  `traceSum n = −Σ_{t²<4n} p₁₀ H − ... = σ₁₁(n) + 2τ(n)` once combined with P13. The precise form
  `traceSum n = −Σ_{t∈ℤ} p₁₀(t,n) H_ext(4n−t²)` is verified for n ≤ 32 (`check1.py`, column
  `Ctrace = CN`).

### P7 ☐ `ESCosets.lean`: `⟨T̃ₙ, K⟩ = −1` for every right coset `K = MΓ`. Estimate 1.5–3k lines
- PZ Theorem B(a): under (B), `K ↦ ⟨T,K⟩` is invariant under left multiplication by `S` and
  `U`, using `T_K πS = U T_{U²K} πS` and `T_K πU = S T_{SK} πU`.
- Smith normal form for 2×2 integer matrices: `MΓ = γ·diag(a, am)Γ`. Elementary, about 200
  lines.
- Homogeneity: `T̃_{a²m}` restricted to multiples of `a` is `a·T̃_m`. The inequalities are
  homogeneous.
- The computation at `K₀ = diag(1,m)Γ`: `T₃` contributes 0, `T₄` contributes ½ + ½, and
  `T₁ − T₁U` contributes 0. This is PZ's three-line estimate.
- Verified: every coset sum is −1, with `#cosets = σ₁(n)` hit, for n ≤ 12, 16, 25, 27, 32, 49.

### P8 ☐ `ESPropA.lean`: (B) + P7 ⇒ (A). Estimate 2.5–5k lines; risk medium
- Lemma 1 (Choie–Zagier): `ξ ∈ I = πS R + πU R ⟺ (1−S)ξ ∈ (1−T)R`.
- Lemma 2 (acyclicity): `ker πS ∩ ker πU = 0` on R. Proof: `c(M) = c(TM) + c(T′M)`, and an
  infinite strictly increasing chain is impossible.
- Theorem A: `T ∈ A_Δ ⇒ (1−S)T ≡ α·T_Δ^∞(1−S)`. The proof uses the function `a(K)` on
  `Γ∞\M`, transitivity of Γ on `Γ\Δ` (Smith form again), and `S,T` generating Γ.
- Theorem B(b), `α = −β`, via PZ's explicit `A, A′` and `1 − T⁻ⁿ = (1+…+T⁻ⁿ⁺¹)(1−S) + S(1−U²)`.
  Corollary 2 then gives `PropA (Ttilde n)`.
- Verified: (A) as exact identities (all `Γ∞`-orbit sums vanish) for n ≤ 12, 16, 25, 27, 32, 49.
- Fallback, if P8 bogs down: prove (A) directly as Merel's condition on cusps. A first attempt
  at a "(16a)-shaped" direct proof failed: `(1−S)(UF+T₁) − T^∞ ∉ (1−T)R`, see `check6.py`.

### P9 ☐ `ESEigen.lean`: algebraic consequences on V. Estimate 0.5–1k lines
- (A) ⇒ `e0|T̃ₙ = σ₁₁(n)e0`, because `Y¹⁰|(1−T) = 0` and `Y¹⁰|T^∞ = σ₁₁(n)Y¹⁰`.
- `εT̃ε` satisfies (A).
- `T̃₂` on `Wper`: `ker(T̃₂+24) = ⟨p⁺ − 36/691·e0, p⁻⟩`, by `decide +kernel` on 11×11 rationals.
  Verified (`check5.py`).

### P10 ☐ `ESEichler.lean`: Eichler integral and Hecke on functions. Estimate 2–4k lines
- `F̃(z) = Σ τ(m)m⁻¹¹e^{2πimz}`. Convergence comes from Mathlib `hasSum_qExpansion` +
  `TauHeckeBridge.qExpansion_discriminant_coeff`.
- The slash action `(f|M)(z) = (cz+d)¹⁰f(Mz)` for integer M with det > 0, with right-action and
  cocycle lemmas.
- `F̃|T = F̃` and `F̃|T^∞ₙ = τ(n)F̃`. The latter uses the root-of-unity sum (generalising
  `TauHeckeOperator`) and the Hecke relation `τ(m)τ(n) = Σ_{d∣(m,n)} d¹¹τ(mn/d²)`. That relation
  is derived from `tau_master` by induction: first multiplicativity, then prime powers.
  Verified for m, n < 25.

### P11 ☐ `ESBol.lean`: ρ is a polynomial in W. Estimate 2–4k lines
- Bol for exponentials: `(d/dz)ⁿ⁺¹[zⁿe^{a/z}] = (−a)ⁿ⁺¹z⁻ⁿ⁻²e^{a/z}`, by induction using
  `φₙ′ = nφₙ₋₁ − aφₙ₋₂`.
- Termwise iterated derivatives of the series on ℍ (`iteratedDerivWithin_tsum`), giving
  `D¹¹ρ = 0`. Then `g⁽¹¹⁾ = 0` on ℍ implies `g` is a polynomial of degree ≤ 10.
- `ρ|(1+S) = 0` because `S²` acts trivially. `ρ|(1+U+U²) = 0` because
  `(1−S)(1+U+U²) ≡ (1−T⁻¹)(1+ST⁻¹) + (T−1)S` mod ± (verified symbolically) and `F̃|T = F̃`.
- Identify ρ with its coefficient vector, using equality on ℍ (an infinite set).
- Verified: ρ, fitted from 11 points, matches at a 12th point to 1e−37. Its coefficients are
  `ρ = −0.98943(X¹⁰−1) + 18.9916·p⁺ + 6.15632i·p⁻`, so `β/α = −691/36` (`check3.py`).

### P12 ☐ `ESNonvanish.lean`: certified numerics. Estimate 1.5–3k lines
- Explicit bound `|τ(m)| ≤ e^{24/13}·14^{m−1}`. Proof: coefficientwise domination of
  `∏(1−qᵏ)²⁴` by `∏(1+qᵏ)²⁴`, evaluated at `1/14`, on the list-based `Tau.lean` product.
- On the imaginary axis, `R(y) := ρ(iy) = f(y) + y¹⁰f(1/y)` with `f(y) = Σ τ(m)m⁻¹¹e^{−2πmy}`.
  Then `R(1) = 2f(1) ∈ [0.0037, 0.0038]` and `R(2) ∈ [44.0, 44.5]`, using exact `τ(m)` for
  `m ≤ 12`, the tail bound, and Mathlib `π`/`exp` bounds.
- If `β = 0`, then `R(2)/R(1) = p⁻(2i)/p⁻(i) = 68`. If `γ = 0`, then it is
  `b₀(2i)/b₀(i) = 68.29`. The certified ratio is `> 10⁴`. Numerically `R(1) = 0.0037348`,
  `R(2) = 44.2288`, ratio 11842 (`check5.py`).

### P13 ☐ `ESMain.lean`: assembly. Estimate 0.5–1k lines
- `es_trace : traceSum n = σ₁₁(n) + 2τ(n)`, from P2/P9a/P5 (trace on W), P9/P11/P12 (eigenbasis),
  and P6.
- `eichlerSelberg (n ≥ 1)`: `Σ_{t²≤4n} symTrace 10 t n · hurwitz(4n−t²) = −2τ(n) − Σ_{d∣n} min(d,n/d)¹¹`.
- `eichlerSelbergPrimePow_hurwitz (p) : RamanujanWeil.ArithPlan.EichlerSelbergPrimePow hurwitz p`.
  This is stated against the frozen name in `AssemblyVocab.lean`, the other agent's file, once
  it exists. ES does not define `esSum`, `hypTerm`, or the other frozen names.

## 3. Line estimates (refined)

| piece | status | lines |
|---|---|---|
| P1–P4, P9a (V, W, trace lemma, group ring, `T̃ₙ`, Prop. 3) | **done** | 0.9k |
| P4b support bound | ☐ | 0.15–0.3k |
| P5 (B) via (16) | ☐ | 2–4k |
| P6 (C): Lemma 4 + fundamental-domain count vs `hurwitz` | ☐ | 2–4k |
| P7 coset sums + Smith form | ☐ | 1.5–3k |
| P8 (A) via PZ Theorems A/B | ☐ | 2.5–5k |
| P9 eigen-algebra on W | ☐ | 0.5–1k |
| P10 Eichler integral, slash, Hecke on q-series | ☐ | 2–4k |
| P11 Bol for exponentials, ρ ∈ W | ☐ | 2–4k |
| P12 certified nonvanishing | ☐ | 1.5–3k |
| P13 assembly | ☐ | 0.5–1k |
| **total A2** | | **15–30k** (algebraic 9–18k, analytic 6–12k) |

This is within the ARITH_ROUTE estimate (15–35k), with the risk moved:

* The hardest parts are now the purely combinatorial P5/P6/P8. They are `omega`-checkable, but
  long.
* No analytic lemma is deep. The worst is the termwise differentiation in P11.

`EichlerSelbergApprox` would save nothing: the class-number side is exact by construction.

## 4. Recommended order

P4b → P6 (gives `traceSum n = CN(n)`, which is unconditional and useful as a target check) → P5
→ P7 → P8 → P9 → P10 → P11 → P12 → P13. P10–P12 (analytic) are independent of P5–P8 and can run
in parallel with them.

## 5. Numerical evidence (scratch `…/scratchpad/es/`)

`common.py` (actions, PZ `T̃ₙ`, class numbers, τ), `gr.py` (group ring mod ±):

* `check1.py`, for n = 1–9, 16, 25, 27, 32:
  - dim W = 3, and `T̃ₙ` preserves W;
  - `tr_V = tr_W = Σ c_M p₁₀ = −Σ_t p₁₀ H_ext = σ₁₁ + 2τ`;
  - the eigenvalues on W are `{σ₁₁(n), τ(n), τ(n)}`.
* `check2.py`, for n ≤ 9, 12, 16, 25, 27, 32, 49:
  - (B) as group-ring identities;
  - every right-coset sum is −1 (σ₁(n) cosets);
  - (A), with all `Γ∞`-orbit sums 0;
  - per-trace sums `= −H(4n−t²)` (elliptic) and `−2H_ext` for `|t|` hyperbolic;
  - (16a).
* `check4.py`, n ≤ 12, 16, 25, 27, 32, 49: Lemma 4 ((14)=(15)), the E-count `= H(4n−t²)` for
  every elliptic t, and (16b).
* `check5.py`:
  - the Hecke relation for τ;
  - `dim A, B, A+B = 6, 8, 11`;
  - e0, p⁺, p⁻ ∈ W, with ε-parities;
  - the `T̃₂` eigenvectors;
  - `R(1)`, `R(2)` and the ratios;
  - ES in `esSum` form for n ≤ 200.
* `check3.py`: ρ is a polynomial; decomposition `(α,β,γ)`. `check6.py`: the failed direct-(A)
  shortcut.
* Lean sanity: `traceSum_small` (n = 1, 2, 3) by `decide +kernel`.

## 6. Files and build

`nice -n 10 lake build RamanujanWeil.Arith.ESAxioms` builds ESAction, ESPeriod, ESGroupRing,
ESTtilde and ESTraceW (each 5–10 s). It prints `[propext, Classical.choice, Quot.sound]` for
`act_mul`, `act_neg`, `trace_act`, `sup_eq_top`, `eq_of_mem_Wper`, `finrank_Wper`,
`trace_eq_trace_restrict_inf`, `trace_actR_sum`, `trace_Ttilde`, `traceSum_small` and
`trace_eq_trace_Wper`. There is no `sorry`, `admit`, `native_decide` or `axiom`. The files are
not yet listed in `RamanujanWeil.lean`.
