# Arithmetic route to `IharaIdentity`: decision memo

> **Status 2026-11-09:** superseded in part. Exact Deuring is no longer needed (docs/ARITH_DEURING_APPROX.md); the current frontier and open named Props (`TateFinitenessPolAll`, `RadicialDual`, `DeuringClassLatticeAll`) are listed in README.md. Progress: ARITH_DEURING_G1*, G5, G6, G7, G7FIN, G8, MULT.


Status 2026-11-08. This is a scouting memo. Nothing here is formalized. The interfaces below were
typechecked with `sorry` in a scratch file outside the repo
(`ArithInterfaces.lean`: 0 errors, 8 `sorry`, one niced `lake env lean`, about 9 s). The numerical
claims were checked with PARI/gp (`default(nbthreads,1)`). The scripts and their outputs are listed
in §6.

## TL;DR

1. **The exact identity is stronger than the endgame needs.** `deligne_of_package` only needs the
   coefficient of the single base `p⁴β` in `S(n)`, and `|p⁴β| > p^{9.5}` under a violation. Any error
   term `O((n+1)^k · p^{19n/2})` is therefore harmless. With a growth lemma for exponential
   polynomials (Mathlib only, about 1k lines), `IharaIdentity` can be replaced by **`IharaApprox`**.
2. **`IharaApprox` removes the supersingular half of Deuring.** On the supersingular tuples
   (`p ∣ a_c`), Hasse gives `|h₁₀| ≤ C q⁵`. The count of those tuples is `≤ C q⁴`, by an elementary
   proof: `a ≡ N(Hasse invariant) mod p`, then Schwartz–Zippel. So their total contribution is
   `O(q⁹)`, which falls inside the error. What is left is
   **Deuring–Waterhouse for ordinary curves only** (`p ∤ t`). Schoof's supersingular counts, the
   quaternion orders and the Eichler mass formula are no longer needed.
3. **The ordinary sum is tied to τ by Eichler–Selberg plus one Hurwitz relation.** The relation is
   `H(p²N) = (p+1−(−N/p))H(N) − pH(N/p²)`. Put `E(m) = Σ_{p∤t} h₁₀ H + 2s_m`. Then
   `E(m) = p¹⁰E(m−2) + μ(m)`, where μ is built from the hyperbolic terms. This is checked exactly,
   and `|E(m)| = O(p^{5m})`. ES only has to be exact on the elliptic terms
   (`EichlerSelbergApprox`).
4. **Recommended route R-ord:** M1′ (approximate endgame), then the supersingular bound, then the
   assembly algebra, then A2 (ES via Eichler integrals and Zagier's period method), then A3-ord
   (ordinary Deuring–Waterhouse). **The long pole is still A3-ord, at 30–60k lines.** Dropping
   Schoof saves about 10–40k lines from the plan's 40–100k for A3. The new pieces (M1′, SS, ALG and the τ port) cost about 5–11k.
5. **No route avoids Deuring.** The geometric machinery bounds weights. It never produces class
   numbers. Its only "free count" is the supersingular bound in point 2.
6. **First milestone (no overlap with Hurwitz or Torsor): M1′**, frozen in §4. It is Mathlib only,
   costs 0.8–1.5k lines, and is low risk.

---

## 1. What the endgame actually needs (question e)

`false_of_package` (`Ihara/Endgame.lean`) uses `hS` in exactly one way: the net multiplicity of
`zw = p^{e+1}β` in `S` is `−1`. Weakenings, from most to least useful:

| Weakening | Sufficient? | Why |
|---|---|---|
| `S n = main n + O((n+1)^k (√p)^{(2e+13)n})`, two-sided | **yes** | `G = S − main` is an exponential polynomial (traces of powers minus six bases). A growth bound kills every base with `‖z‖ > p^{e+6.5}`, and `‖zw‖ = p^{e+1}‖β‖ > p^{e+6.5}`. So the coefficient of `zw` in `S` is −1, and the rest of the proof is unchanged |
| identity only for `n ∈ mℕ` (an arithmetic progression) | yes | apply the argument to `zᵐ`. Every z with `zᵐ = zwᵐ` has `|z| = |zw|`. It saves nothing, because the arithmetic is uniform in `q` |
| identity for infinitely many `n` | only with Skolem–Mahler–Lech | not worth formalizing |
| a single `n` (e.g. prime fields only) | **no** | one linear relation cannot isolate an eigenvalue |
| a one-sided inequality `S ≤ main + O(…)` | not in general | a dominant base with a negative coefficient satisfies it |
| ordinary locus only | **yes, with the growth version** | on the arithmetic side we keep `W` and bound the supersingular part (§2). No new geometry is needed |

Consequences: the constant `−1` and the hyperbolic and parabolic terms of ES are irrelevant. They
are `O(q^{4}·q^{5.5})` after multiplying by `q³(q−1)`. So are Schoof's supersingular counts.

## 2. Routes compared (question 1)

| Route | Content | Verdict |
|---|---|---|
| (a) plan A2 + full A3 | ES at `pᵐ` + Deuring–Waterhouse–Schoof incl. supersingular | 65–160k. The supersingular piece (quaternions, Eichler mass, `n ≥ 2` traces `±√q, ±2√q, …`) is avoidable |
| **R-ord** = (a) − Schoof + (e) | ES (elliptic terms exact) + HR + ordinary Deuring + elementary supersingular bound + M1′ | **recommended**, about 50–100k in total, A3-ord the pole |
| (b) A2 via Zagier periods | see §3 A2 | the cheapest proof of ES known to me. The analytic input shrinks to the **Eichler integral** (no path integrals) |
| (c) holomorphic projection / Cohen–Zagier | Zagier's weight-3/2 Eisenstein series `ℋ` on Γ₀(4), Rankin–Cohen with θ, Sturm's holomorphic projection, trace to level 1 | the modularity of `ℋ` alone is a large analytic project. RamanujanTau's η-multiplier/`T(Q²)` work (`HalfHecke/`) does not cover non-holomorphic weight 3/2. Not recommended |
| (d) avoid Deuring by direct counting | linearity of the Weierstrass equation in `c` turns moments into counts of `k`-tuples of plane points on a common cubic. For `k = 10` that is a restatement. Matrix counting (Latimer–MacDuffee) only *re-encodes* `H`. Gekeler's local factors presuppose Deuring | **no route found**. The geometric side gives weight bounds, never class numbers. Other families (Legendre, level-N) add newforms (`S_L = −3−3τ−a_p(g)`) and need ES at higher level |
| (d′) geometric side for the supersingular locus | Weil II on `Z = {Hasse = 0}`, dim 4, gives `S_Z(n)` bases `≤ p⁹` | works, but the elementary Schwartz–Zippel bound is cheaper and needs no Stacks build |

Why the ordinary sum closes up (route R-ord). Write `A(m) = Σ_{t²≤4pᵐ} h₁₀(t,pᵐ)H(4pᵐ−t²)` and
`O(m)` for its `p ∤ t` part. Then `h₁₀(pt', pᵐ) = p¹⁰h₁₀(t', p^{m−2})`. For `m ≥ 3`, `p ∤ t'` gives
`(−N/p) = (t'²/p) = 1` (also at `p = 2`: `t'² ≡ 1 mod 8`). HR then turns the `p ∣ t` part into
`p¹⁰[(p+1)A(m−2) − O(m−2) − p¹¹A(m−4)]` for `m ≥ 4`. With `s_m = τ(pᵐ) − p¹¹τ(p^{m−2})` all τ terms
cancel, which leaves `E(m) = p¹⁰E(m−2) + μ(m)` with `μ = −λ_m + p¹⁰(p+1)λ_{m−2} − p²¹λ_{m−4}` (or the ES
errors). Since `p¹⁰·p^{5.5(m−2)} < p^{5.5m}`, we get `|E(m)| ≤ C(m+1)^k p^{5.5m}`. Then

`S(n) = q³(q−1)·½·O(n) + S_ss(n) = q³(q−1)(−s_n) + q³(q−1)E(n)/2 + O(q⁹)`

which is `IharaApprox`. (The supersingular weighted mass is about `q⁵`. On the full identity it equals
`−(c/2)q⁵`, with `c` depending on `p` and on the parity of `n`, matching `ordinary_locus_probe.out`.)

## 3. Recommended route: milestones and honest sizes (question 2)

| # | Milestone | Owner/overlap | Frozen interface (§4) | Lines | Risk |
|---|---|---|---|---|---|
| **M1′** | growth lemma + approximate endgame | none (Mathlib + `Endgame.lean`) | `coeff_eq_zero_of_growth`, `deligne_of_package_approx`, `iharaApprox_of_iharaIdentity` | 0.8–1.5k | low |
| M1′b | rewire `Final`: `deligneBound_of_iharaApprox_all` (copy of `Assembly.lean`, swap the M1 call) | none, but needs the Weil closure (>6 GB) | `(∀ p, IharaApprox p) → DeligneBound` | 0.1–0.3k | low |
| SS | `p ∣ a ⟺ Hasse(c) = 0` (p odd; `a₁ = 0` for p = 2) and `#ss ≤ C q⁴` | none | `dvd_traceOfFrob_iff`, `supersingularCountBound` | 2–4k | low–medium |
| ALG | `ordSum_error(_of_approx)`, `iharaApprox_of_arith` | uses the Hurwitz agent's `H` only as a parameter | §4 | 1.5–3k | low |
| τ | port `tau_hecke_recurrence` (RamanujanTau `HeckeQExp.lean`, toolchain 4.30→4.34). The import closure is 112 modules, about 17k lines, mostly incidental; a pruned port is about 1–3k | none | `TauHeckeRecurrence` | 1–3k | low–medium |
| A1′ | `HurwitzPrimeSquare` for `Arith.hurwitz` (`H(p²N)` via index-`p` superlattices of forms) | **Hurwitz agent** | `HurwitzPrimeSquare`, `HurwitzConventions` | 2–5k | medium |
| A2 | ES at `pᵐ` (approximate form suffices) via Eichler integrals + Zagier periods | none | `EichlerSelbergApprox` | 15–35k | **high** |
| A3-ord | ordinary Deuring–Waterhouse, 5-parameter form | uses `TorsorCount.sum_trace_eq_sum_orbits` | `OrdinaryDeuring` | 30–60k | **very high** |

**A2 breakdown (Eichler-integral version of Zagier 1990).**
1. Set `F̃ = Σ τ(n)n^{−11}qⁿ`. Bol's identity `D¹¹(F|₋₁₀γ) = (D¹¹F)|₁₂γ`, together with "`D¹¹g = 0` on
   ℍ ⇒ g is a polynomial of degree ≤ 10", shows that `ρ = F̃|₋₁₀(1−S)` lies in `V₁₀`. ρ then
   satisfies the Manin relations by group algebra and `F̃|T = F̃`. This needs **no path integrals**
   (2–4k).
2. Hecke equivariance `ρ_{T_n f} = ρ_f|T̃_n` follows from the Choie–Zagier condition
   `(1−S)T̃_n ≡ T_n^∞(1−S) mod (1−T)`. This is algebraic, once the q-expansion action of `T_n^∞` on
   periodic functions is known. That action is RamanujanTau's `qExpansion_hecke` computation, run at
   weight −10 (2–4k).
3. `ρ⁻_Δ ≠ 0`. The odd coefficients are `Λ(Δ, j)`, `j = 2, 4, …, 10` (Mathlib `ModularForm.LFunction`:
   `Λ_eq_mellin`). For the nonvanishing, `RamanujanTau.tauL_ne_zero_of_ge`
   (`EdgeNonvanishing/Main.lean:211`) gives `L(Δ,10) ≠ 0` (1–2k).
4. Construct the Manin/Heilbronn elements `T̃_n`, prove `dim W₁₀⁻ = 1` (finite linear algebra), and
   get the eigenvalue `τ(n)` on `W⁻` (4–8k).
5. **The hardest single lemma of A2:** Zagier's evaluation of the trace of `T̃_n` on `W⁻`
   (equivalently on `W` together with the ε-twisted trace) as `−½Σ_t h₁₀(t,n)H(4n−t²)` plus
   hyperbolic and parabolic terms, which may now be bounded instead of evaluated (6–15k). Risk: the
   combinatorics of reduced matrices of determinant `n`. Only the elliptic classes must be exact.

**A3-ord breakdown.** Steps 1–2 are 8–15k lines. Step 3 is 6–12k. Steps 4–5 are 15–30k.
1. Isogenies of Weierstrass curves over `𝔽̄_q` (rational group maps), degree, dual isogeny, and
   `#E(𝔽_q) = deg(1−π)`.
2. `π² − tπ + q = 0` in `End(E)`. The repo already has the cohomological version
   (`charpoly_weierstrassH1'`, `natCard_point_extension_eq_weierstrassH1'`). Stacks has the Tate-module
   trace of Jacobian endomorphisms (`trace_tateModuleMap_jacobianPullback`,
   `abelianVarietyTrace_jacobianPullback`, Tag 03U1).
3. For `p ∤ t`, `End(E)` is an order `O ⊇ ℤ[π]` in `ℚ(√(t²−4q))`.
4. **The hardest single lemma of the whole project:** Waterhouse Thm 4.5 for ordinary curves. Every
   order `O ⊇ ℤ[π]` occurs, and `Pic(O)` acts freely and transitively on the curves with
   `End = O` and Frobenius π. This needs Tate's isogeny theorem over finite fields, or Deuring
   lifting, or Deligne's ordinary equivalence.
5. `Σ_O h(O)/#O^× ·2 = H(4q−t²)`. This needs class numbers of orders versus forms; part of it is in
   the Hurwitz agent's work.

## 4. Frozen interfaces (typechecked; scratch `ArithInterfaces.lean`, namespace `RamanujanWeil.ArithPlan`)

`H : ℕ → ℚ` is a parameter. The intended instance is `RamanujanWeil.Arith.hurwitz`
(`Arith/HurwitzBasic.lean`, `H 0 = −1/12`). `symTrace`, `tauPowerSum`, `wc`, `traceOfFrob` and
`weierstrassSum` are the repo's definitions.

```lean
-- M1′ (first milestone)
theorem coeff_eq_zero_of_growth (T : Finset ℂ) (c : ℂ → ℂ) (R C : ℝ) (k : ℕ)
    (h : ∀ n : ℕ, 1 ≤ n → ‖∑ z ∈ T, c z * z ^ n‖ ≤ C * ((n : ℝ) + 1) ^ k * R ^ n) :
    ∀ z ∈ T, R < ‖z‖ → c z = 0
theorem deligne_of_package_approx (p : ℕ) [Fact p.Prime] (d : ℕ) (K : Type) [Field K] (ι : K →+* ℂ)
    (V : Fin (2 * d + 1) → Type) [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
    [∀ i, FiniteDimensional K (V i)] (F : ∀ i, Module.End K (V i))
    (hw : ∀ i z, ((F i).charpoly.map ι).IsRoot z → ‖z‖ ≤ (p : ℝ) ^ (((10 : ℝ) + (i : ℕ)) / 2))
    (S : ℕ → ℤ)
    (htr : ∀ n : ℕ, 1 ≤ n →
      ∑ i : Fin (2 * d + 1), (-1 : K) ^ (i : ℕ) * LinearMap.trace K (V i) (F i ^ n) = (S n : K))
    (hS : ∃ C : ℝ, ∃ k : ℕ, ∀ n : ℕ, 1 ≤ n →
      |((S n - (p : ℤ) ^ ((d - 2) * n) * ((p : ℤ) ^ n - 1) * (-1 - tauPowerSum p n) : ℤ) : ℝ)| ≤
        C * ((n : ℝ) + 1) ^ k * Real.sqrt p ^ ((2 * (d - 2) + 13) * n)) :
    RamanujanTau.tau p ^ 2 ≤ 4 * (p : ℤ) ^ 11
def IharaApprox (p : ℕ) [Fact p.Prime] : Prop :=
  ∃ C : ℝ, ∃ k : ℕ, ∀ n : ℕ, 1 ≤ n →
    |((weierstrassSum p n - (p : ℤ) ^ (3 * n) * ((p : ℤ) ^ n - 1) * (-1 - tauPowerSum p n) : ℤ) : ℝ)| ≤
      C * ((n : ℝ) + 1) ^ k * Real.sqrt p ^ (19 * n)
theorem iharaApprox_of_iharaIdentity (p : ℕ) [Fact p.Prime] (h : IharaIdentity p) : IharaApprox p

-- vocabulary
def kron (D : ℤ) (p : ℕ) : ℤ :=          -- Kronecker (D/p); p = 2 via D mod 8, else jacobiSym
  if p = 2 then (if D % 2 = 0 then 0 else if D % 8 = 1 ∨ D % 8 = 7 then 1 else -1) else jacobiSym D p
def hypTerm (p m : ℕ) : ℤ := ∑ j ∈ range (m + 1), ((min (p ^ j) (p ^ (m - j)) : ℕ) : ℤ) ^ 11
def esSum (H : ℕ → ℚ) (q : ℕ) : ℚ :=
  ∑ t ∈ Icc (-(2 * (q : ℤ))) (2 * q) with t ^ 2 ≤ 4 * (q : ℤ),
    (symTrace 10 t q : ℚ) * H (4 * (q : ℤ) - t ^ 2).toNat
def ordSum (H : ℕ → ℚ) (p m : ℕ) : ℚ :=      -- same, restricted to ¬ (p : ℤ) ∣ t, at q = p ^ m

-- A1′ (Hurwitz agent)
def HurwitzConventions (H : ℕ → ℚ) : Prop := H 0 = -1 / 12 ∧ ∀ N : ℕ, N % 4 = 1 ∨ N % 4 = 2 → H N = 0
def HurwitzPrimeSquare (H : ℕ → ℚ) (p : ℕ) : Prop :=
  ∀ N : ℕ, N % 4 = 0 ∨ N % 4 = 3 →
    H (p ^ 2 * N) = ((p : ℚ) + 1 - kron (-(N : ℤ)) p) * H N - (if p ^ 2 ∣ N then (p : ℚ) * H (N / p ^ 2) else 0)

-- A2
def EichlerSelbergPrimePow (H : ℕ → ℚ) (p : ℕ) : Prop :=
  ∀ m : ℕ, esSum H (p ^ m) = -2 * (RamanujanTau.tau (p ^ m) : ℚ) - hypTerm p m
def EichlerSelbergApprox (H : ℕ → ℚ) (p : ℕ) : Prop :=
  ∃ C : ℝ, ∃ k : ℕ, ∀ m : ℕ,
    |((esSum H (p ^ m) + 2 * (RamanujanTau.tau (p ^ m) : ℚ) : ℚ) : ℝ)| ≤ C * ((m : ℝ) + 1) ^ k * Real.sqrt p ^ (11 * m)
def TauHeckeRecurrence (p : ℕ) : Prop :=
  ∀ r : ℕ, 1 ≤ r → RamanujanTau.tau (p ^ (r + 1)) =
    RamanujanTau.tau p * RamanujanTau.tau (p ^ r) - (p : ℤ) ^ 11 * RamanujanTau.tau (p ^ (r - 1))

-- A3-ord (traceCount p n t = #{c ∈ 𝔽_{pⁿ}⁵ | Δ ≠ 0 ∧ traceOfFrob (wc c) = t})
def OrdinaryDeuring (H : ℕ → ℚ) (p : ℕ) [Fact p.Prime] : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ t : ℤ, ¬ (p : ℤ) ∣ t →
    (traceCount p n t : ℚ) = (p : ℚ) ^ (3 * n) * ((p : ℚ) ^ n - 1) *
      (if t ^ 2 < 4 * (p : ℤ) ^ n then H (4 * (p : ℤ) ^ n - t ^ 2).toNat else 0) / 2

-- SS (elementary)
theorem dvd_traceOfFrob_iff (p) [Fact p.Prime] (n) (hn : 1 ≤ n) (c : Fin 5 → GaloisField p n)
    (hc : (wc c).Δ ≠ 0) :
    ((p : ℤ) ∣ traceOfFrob (wc c) ↔ if p = 2 then c 0 = 0 else hasseInv p c = 0)
    -- hasseInv p c = coeff_{x^{p−1}} (4x³ + b₂x² + 2b₄x + b₆)^{(p−1)/2}
def SupersingularCountBound (p) [Fact p.Prime] : Prop :=
  ∃ C : ℕ, ∀ n ≥ 1, #{c : Fin 5 → GaloisField p n | Δ ≠ 0 ∧ (p : ℤ) ∣ traceOfFrob (wc c)} ≤ C * p ^ (4 * n)
def HasseAll (p) [Fact p.Prime] : Prop :=        -- already unconditional in the repo (Weil closure)
  ∀ n ≥ 1, ∀ c, (wc c).Δ ≠ 0 → traceOfFrob (wc c) ^ 2 ≤ 4 * (p : ℤ) ^ n

-- ALG
theorem ordSum_error_of_approx (H) (p) [Fact p.Prime] (h0 : HurwitzConventions H)
    (hES : EichlerSelbergApprox H p) (hHR : HurwitzPrimeSquare H p) (hT : TauHeckeRecurrence p) :
    ∃ C : ℝ, ∃ k : ℕ, ∀ m : ℕ,
      |((ordSum H p m + 2 * (tauPowerSum p m : ℚ) : ℚ) : ℝ)| ≤ C * ((m : ℝ) + 1) ^ k * Real.sqrt p ^ (11 * m)
theorem iharaApprox_of_arith (H) (p) [Fact p.Prime] (h0 : HurwitzConventions H)
    (hD : OrdinaryDeuring H p) (hES : EichlerSelbergPrimePow H p) (hHR : HurwitzPrimeSquare H p)
    (hT : TauHeckeRecurrence p) (hss : SupersingularCountBound p) (hH : HasseAll p) : IharaApprox p
```

(The scratch file spells out the `letI Fintype` / `Classical` boilerplate in full, exactly as
`IharaStatement.lean` does.)

## 5. Already available, though the plan estimated it as large (question 3)

| Plan item | Already there | Where |
|---|---|---|
| A4 torsor count (2–4k) | **done** by the other agent | `Arith/TorsorCount.lean`: `card_isoClass_mul_card_stabilizer`, `sum_trace_eq_sum_orbits` |
| Hasse bound / Frobenius charpoly on `H¹` (part of A3) | unconditional in the repo | `sq_le_four_mul_card_weierstrassH1'` + `h1RankFormula` (`CurveH1BettiStacks.lean`), `charpoly_weierstrassH1'`, `natCard_point_extension_eq_weierstrassH1'` |
| Hecke operators on `S_k(SL₂ℤ)` (A2 prerequisite, "absent") | **RamanujanTau**, unconditional | `HeckeQExp.lean`: `RamanujanTau.Hecke.heckeLin`, `qExpansion_hecke`, `tau_hecke_recurrence`, `tau_mul_coprime`, `tau_master`; `TauModular.lean`: `qExpansion_discriminant_eq` |
| `dim S₁₂ = 1`, Δ, Sturm | Mathlib | `CuspForm.rank_eq_one_of_weight_eq_twelve`, `CuspForm.exists_smul_discriminant_of_weight_eq_twelve`, `ModularForm.sturm_bound_levelOne`, `ModularForm.discriminant` |
| periods `r_k(Δ)` ∝ `Λ(Δ,k+1)` | Mathlib L-function of a modular form | `NumberTheory/ModularForms/LFunction.lean`: `Λ_eq_mellin`, `differentiable_Λ`, `isStrongFEPair` |
| `L(Δ, j) ≠ 0` (needed for `ρ⁻_Δ ≠ 0`) | RamanujanTau | `EdgeNonvanishing/Main.lean:211` `tauL_ne_zero_of_ge` (Re s ≥ 13/2); FE `HeckeL/Basic.lean:130` |
| Hasse invariant of a Weierstrass curve | RamanujanTau (formal-group side) | `HasseInv/Weierstrass.lean` `HasseInv.hasseH` (same normalization as `hasseInv` above), `HasseInv/Elliptic.lean` `aH_formalGroup_eq_hasseH`. The point-count congruence `a ≡ N(H) mod p` is **not** there |
| Schwartz–Zippel | Mathlib | `MvPolynomial.schwartz_zippel_totalDegree` |
| Hecke rings | Mathlib, definitions only | `NumberTheory/HeckeRing/Defs.lean` (no action on forms) |
| Frobenius on Jacobians, Tate-module traces, Weil pairing | Stacks | `Stacks.PicardFunctor.jacobianFrobenius`, `trace_tateModuleMap_jacobianPullback`, `abelianVarietyTrace_jacobianPullback`, `Stacks.Picard.eq_zero_of_smul_eigen_of_weilPairing` |
| isogenies between curves, `End(E)`, CM, supersingularity, Deuring | **nowhere** (Mathlib, Stacks, Weil, RamanujanTau) | `Drinfeld/SupersingularCurve.lean` is an unrelated 𝔽₂ example. RamanujanTau `CanonicalIsogeny/` is formal-group Lubin theory, not curve isogenies |

## 6. Numerical evidence

Scripts are in the session scratch directory `…/scratchpad/scout/`: `arith_route_check.gp`,
`v3c_growth.gp`, and their `.out` files.

* **V1** HR `H(p²N) = (p+1−(−N/p))H(N) − p[p²∣N]H(N/p²)`, for `N ≡ 0,3 (4)`, `p ≤ 13`, `N ≤ 3000`,
  with PARI `kronecker`: exact.
* **V2** 5-parameter ordinary Deuring `N(t,q) = q³(q−1)H(4q−t²)/2` for `p ∤ t`: exact for
  `q ∈ {2,3,4,5,7,8,9,11,13,16}`, which includes p = 2, 3. Also `p ∣ a_c ⟺ Hasse(c) = 0` for p odd,
  and `⟺ a₁ = 0` for p = 2, on every nonsingular tuple. `#ss = (1/2, 2/3, 3/4, 4/5, 6/7, 7/8, 8/9,
  20/11, 12/13, 15/16)·q⁴`.
* **V3** ES `A(m) = −2τ(pᵐ) − λ(m)` holds for `p ≤ 13`, `pᵐ ≤ 2·10⁷`. The recursion
  `E(m) = p¹⁰E(m−2) + μ(m)` holds exactly for `m ≥ 4`. The ratio `|E(m)|/((m+1)p^{5.5m})` decreases
  to 0, for example `p = 3`: 1.5, 0.58, 0.22, 0.10, … This is consistent with `E(m) = O(p^{5m})`.

## 7. Recommendation and first milestone

**Adopt R-ord.** The target changes from `IharaIdentity` to `IharaApprox`. This drops Schoof and all
supersingular theory, and ES needs to be exact only on its elliptic terms. The project's risk then
sits in two places: A3-ord (Waterhouse Thm 4.5, ordinary) and Zagier's trace evaluation in A2.

**First milestone: M1′** (no overlap with `Arith/Hurwitz*` or `Arith/Torsor*`). Create a new file
`RamanujanWeil/Ihara/EndgameApprox.lean` that imports only `Endgame.lean`, `IharaStatement.lean`
and Mathlib, and prove:
1. `coeff_eq_zero_of_growth`. Let `M` be the largest modulus with a nonzero coefficient. The Cesàro
   mean of `|Σ_{|z|=M} c_z (z/M)ⁿ|²` tends to `Σ|c_z|² > 0`, because `(1/N)Σ_{n<N}(u/v)ⁿ → 0` for
   `|u| = |v|`, `u ≠ v`. This contradicts `O((n+1)^k (R/M)ⁿ) → 0`. About 400–800 lines.
2. `deligne_of_package_approx`. Rerun `false_of_package` with the six bases and the error bases
   merged into `T`. Apply the growth lemma to `S − main` at `zw` (`‖zw‖² = p^{2e+2}β² > p^{2e+13}`),
   then finish with the existing odd-degree argument. About 300–500 lines.
3. `iharaApprox_of_iharaIdentity` (trivial). Later, in a Weil-closure file,
   `deligneBound_of_iharaApprox_all` as a copy of `Assembly.lean`/`Final.lean`.

Next, in parallel and still without overlap: **SS** (`dvd_traceOfFrob_iff` and
`supersingularCountBound`; Mathlib plus a quadratic-character point count), and **ALG**
(`ordSum_error_of_approx`, abstract in `H`). Ask the Hurwitz agent for `HurwitzPrimeSquare` and
`HurwitzConventions` on `Arith.hurwitz`.
