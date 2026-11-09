# A2 (Eichler–Selberg via Popa–Zagier): progress log

Companion to `docs/ARITH_ES_PLAN.md`; the plan's numbering (P1–P13) is used throughout.
Status 2026-11-08, second session.

## 1. Done this session (all axiom-clean)

New files in `RamanujanWeil/Arith/` (namespace `RamanujanWeil.Arith.ES`), about 2.2k lines:

| file | lines | content |
|---|---|---|
| `ESRegions.lean` | 188 | PZ regions `T₁…T₄, H, Y, A₁, B₁, E, X, Z, Z₃` as coefficient functions; Lemma 4 split identities |
| `ESSupport.lean` | 196 | **P4b**: support bounds |
| `ESPerTrace.lean` | 163 | per-trace sums `trSum`, conjugation invariance, `trSum_ptC` |
| `ESEllipticCount.lean` | 346 | fundamental-domain count `Σ_{tr=t} E = H(4n−t²)` |
| `ESPropC.lean` | 256 | **P6 / property (C)** assembled |
| `ESPropBRegions.lean` | 263 | **P5**: PZ (16a), (16b) as pointwise identities |
| `ESPropB.lean` | 224 | **P5**: (16a)/(16b) in `ℚ[M₂(ℤ)]`, property (B), `tr_W = tr_V` |
| `ESCosets.lean` | 271 | **P7**: coset sums `cS`, invariances from (16a)/(16b) |
| `ESCosetsMain.lean` | 274 | **P7**: homogeneity, `diag(1,m)Γ`, Euclid descent, `⟨T̃ₙ, K⟩ = −1` |
| `ESAxioms2.lean` | 33 | audit |

`lake build RamanujanWeil.Arith.ESAxioms2` prints `[propext, Classical.choice, Quot.sound]` for
all 24 audited theorems. There is no `sorry`, `admit`, `native_decide` or `axiom` in the new files,
and they build without warnings. No existing file was edited.

### P4b — support bound (`ESSupport.lean`)

```lean
def EntBd (K : ℤ) (M : M2) : Prop := |M.a| ≤ K ∧ |M.b| ≤ K ∧ |M.c| ≤ K ∧ |M.d| ≤ K
theorem ptC_support {M : M2} {n : ℤ} (hdet : M.det = n) (h : ptC M ≠ 0) : EntBd n M
```

So `Ttilde n` (the `[−n,n]⁴` box) is the full `T̃ₙ` of PZ (15). The same bound is proved for each
region (`regT1_bd … regZ3_bd`, `regF_bd`, `regG_bd`, `regQ_bd`). Each proof is one `nlinarith`
call after writing `n = ad − bc` as a sum of non-negative products. Size: 0.2k lines, against an
estimate of 0.15–0.3k.

### P6 — property (C) (`ESRegions`, `ESPerTrace`, `ESEllipticCount`, `ESPropC`)

**PZ Lemma 4.** PZ's split identities hold as exact identities of coefficient functions, for
**every** integer matrix and with no sign ambiguity:

* `regZ_eq : Z(M) = X(−SMS) + A₁(M)`
* `regZ_conjU : Z(−UMU²) = Z₃(M) + T₂(M)`
* `regX_eq : X = B₁ + Z₃ + Y(−U·U²)`
* `regT1_eq : T₁ = Y + H`
* `regE_eq : E = A₁ + T₃ + B₁ + T₄`

Here `conjS M = −SMS` and `conjU M = −UMU²` preserve `det` and `tr`. `trSum n t f` is the
`finsum` over `det = n, tr = t`, and it is invariant under both conjugations. From this,

```lean
theorem trSum_ptC (n t : ℤ) : trSum n t ptC = trSum n t regH - trSum n t regE
```

**Fundamental-domain count.** `six_regE` is the pointwise identity
`6E = R⁻ + ½(R⁰ + R⁰∘S) + R⁺∘S + ½(Rᵉ∘S + Rᵉ∘T)`. Here `R(M) = [Q_M reduced]·wt6(Q_M)` with
`Q_M = [c, d−a, −b]`, and `conjT M = T⁻¹MT`. A bijection with `Hurwitz.redPairs` then gives:

```lean
theorem trSum_regR {n t : ℤ} {N : ℕ} (hN : (N : ℤ) = 4 * n - t ^ 2) : trSum n t regR = (H6 N : ℚ)
theorem trSum_regE {n t : ℤ} {N : ℕ} (hN : (N : ℤ) = 4 * n - t ^ 2) (hpos : 0 < N) :
    trSum n t regE = Hurwitz.hurwitz N
theorem trSum_regE_nonell {n t : ℤ} (h : 4 * n ≤ t ^ 2) : trSum n t regE = 0
```

**Hyperbolic/parabolic part.** Only `H` contributes, and `sum_w3_hyp` evaluates its sum over `b`:

```lean
def hypW (a d : ℤ) : ℚ := if a < d then ((d - a : ℤ) : ℚ) else if a = d then 1 / 6 else 0
theorem sum_trSum_regH (n : ℕ) (hn : 1 ≤ n) (g : ℤ → ℚ) :
    ∑ t ∈ Icc (-(2 * (n : ℤ))) (2 * n), g t * trSum n t regH =
      ∑ a ∈ Icc (1 : ℤ) n, if a ∣ (n : ℤ) then hypW a ((n : ℤ) / a) * g (a + (n : ℤ) / a) else 0
```

**Property (C).** The result is stated with the A1 `hurwitz`:

```lean
theorem traceSum_eq_trSum (n : ℕ) :
    traceSum n = ∑ t ∈ Icc (-(2 * (n : ℤ))) (2 * n), (symTr10 t n : ℚ) * trSum n t ptC
theorem traceSum_classNumber (n : ℕ) (hn : 1 ≤ n) :
    traceSum n =
      (∑ a ∈ Icc (1 : ℤ) n,
        if a ∣ (n : ℤ) then hypW a ((n : ℤ) / a) * (symTr10 (a + (n : ℤ) / a) n : ℚ) else 0) -
      ∑ t ∈ Icc (-(2 * (n : ℤ))) (2 * n),
        if t ^ 2 < 4 * (n : ℤ) then (symTr10 t n : ℚ) * Hurwitz.hurwitz (4 * (n : ℤ) - t ^ 2).toNat
        else 0
```

This is the plan's `traceSum n = −Σ_t p₁₀(t,n) H_ext(4n−t²)`. Each split pair `a < d = n/a`
contributes `(d − a)·p₁₀(a+d, n)`, which is `p₁₀·(−2H_ext(−u²))` after symmetrising `t ↦ −t`.
A square `n = a²` contributes `p₁₀(2a, n)/6`, which is `−2H(0)`.

Sanity check at n = 1: `11/6 − (−1·½ + 2·(−1)·⅓) = 3 = traceSum 1`.

Size: about 0.95k lines, against an estimate of 2–4k. Avoiding sign bookkeeping
(`conjS = −SMS` etc.) and the six-term fundamental-domain identity kept it small.

### P5 — property (B) (`ESPropBRegions`, `ESPropB`)

With suitable fixed signs, PZ (16a) and (16b) hold **exactly** in `ℚ[M₂(ℤ)]`, not just modulo
`±`. This was found numerically (`es2/p16.py`) and proved pointwise:

```lean
theorem ptC_16a (M : M2) :
    ptC M = -regF M - regF (mapA M) - regF (mapB M) + regT1 M - regT1 (mapC M)
    -- mapA M = −U⁻¹MS⁻¹, mapB M = −U⁻²M, mapC M = MS⁻¹
theorem ptC_16b (M : M2) :
    ptC M = -regG M - regG (mapD M) + regT1 M - regT1 (mapE M) + (regQ M - regQ (mapE M)) / 12
    -- mapD M = −S⁻¹MU⁻¹, mapE M = MU⁻¹
theorem Ttilde_16a (n : ℕ) :
    Ttilde n = -elt n regF - ofM (-U) * elt n regF * ofM S - ofM (-(U * U)) * elt n regF +
      elt n regT1 - elt n regT1 * ofM S
theorem Ttilde_16b (n : ℕ) :
    Ttilde n = -elt n regG - ofM (-S) * elt n regG * ofM U + elt n regT1 -
      elt n regT1 * ofM U + (1 / 12 : ℚ) • (elt n regQ - elt n regQ * ofM U)
def PropBact (x : R) : Prop :=
  (∃ y, actR (x * oneS) = actR (oneU * y)) ∧ (∃ y, actR (x * oneU) = actR (oneS * y))
theorem propBact_Ttilde (n : ℕ) : PropBact (Ttilde n)          -- y₁ = −F(1+S), y₂ = −G(1+U+U²)
theorem trace_eq_trace_Wper' {x : R} (hx : PropBact x) : tr(actR x | V) = tr(actR x | Wper)
theorem trace_Wper_Ttilde (n : ℕ) : tr(actR (Ttilde n) | Wper) = traceSum n
```

`PropBact` is property (B) stated as operator identities on `V₁₀`, using `S² = U³ = −1`. It is
exactly what PZ Prop. 3 consumes. It sidesteps `ESTraceW.EqPM`, because `nf` is not
±-invariant on matrices with zero second row. `trace_eq_trace_Wper'` re-proves Prop. 3 from it in
about 30 lines, by copying `ESTraceW`.

Proof technique: `es_signs [L₁, …, L₅]` does trichotomy case analysis on ≤ 5 linear forms, then
`simp (disch := omega)` evaluates every weight. The main cases follow PZ's decomposition, split by
second-line signs: `d ≤ b` reduces to `eW = w4 + w4`; for `b < d ≤ 0`, `a ≤ 0` vs `a > 0`.

Size: about 0.5k lines, against an estimate of 2–4k.

### P7 — coset sums (`ESCosets`, `ESCosetsMain`)

```lean
noncomputable def cS (f : M2 → ℚ) (A : M2) : ℚ := ∑ᶠ γ : M2, if γ.det = 1 then f (A * γ) else 0
theorem cS_ptC_16a {A : M2} (hA : A.det ≠ 0) :
    cS ptC A = -(cS regF A + cS regF (Ui * A) + cS regF (Ui * Ui * A))
theorem cS_ptC_16b {A : M2} (hA : A.det ≠ 0) : cS ptC A = -(cS regG A + cS regG (Si * A))
theorem cS_ptC_U / cS_ptC_S / cS_ptC_T : cS ptC (g * A) = cS ptC A      -- g = U, S, T
theorem cS_ptC_Pk / cS_ptC_Lk (k : ℤ) : ... [[1,k],[0,1]] / [[1,0],[k,1]] ...
theorem ptC_scale (hg : 0 < g) (M : M2) : ptC (scale g M) = ptC M
theorem cS_ptC_K0 {m : ℤ} (hm : 1 ≤ m) : cS ptC ⟨1, 0, 0, m⟩ = -1
theorem cS_ptC_eq_neg_one {A : M2} (hdet : 0 < A.det) : cS ptC A = -1   -- PZ Theorem 4(b)
```

`cS ptC A` is PZ's `⟨T̃, AΓ⟩`. Both `±γ` are summed, but `ptC` sees only the normalised member
of each pair `±Aγ`. The steps:

* **Left invariance.** It comes straight from the exact (16a)/(16b). The `T₁(1−S)`, `T₁(1−U)`
  and `Q(1−U)` terms have zero coset sums by right invariance.
* **Reduction to a diagonal coset.** This is a Euclid descent on `|a|` using left moves
  `S, [[1,k],[0,1]], [[1,0],[k,1]]` and arbitrary right moves. It needs no Smith-form theorem
  and no Mathlib generation lemma.
* **Diagonal value.** Homogeneity reduces `diag(g, gm)` to `diag(1, m)`. There PZ's three-line
  estimate gives the value: `T₂ = T₁U`, `T₃` is empty by `nlinarith`, and `T₄` is exactly
  `{[[0,−1],[m,0]], [[1,−1],[m,0]]}` with weights ½ + ½. The case `m = 1` is `decide +kernel`
  over `[−1,1]⁴`.

Size: 0.55k lines, against an estimate of 1.5–3k.

## 2. What remains (refined estimates)

| piece | status | estimate |
|---|---|---|
| P1–P4, P9a | done (session 1) | 0.9k |
| P4b, P5, P6, P7 | **done** (this session) | 2.2k actual |
| P8 (A) via PZ Thms A/B (Lemma 1, Lemma 2 acyclicity, Thm A, Thm B(b)) | ☐ | 2–4k |
| P9 eigen-algebra on W (`e0` eigenvalue, `εT̃ε`, `T̃₂` kernel) | ☐ | 0.5–1k |
| P10 Eichler integral / Hecke on q-series | ☐ | 2–4k |
| P11 Bol for exponentials, ρ ∈ W | ☐ | 2–4k |
| P12 certified nonvanishing | ☐ | 1.5–3k |
| P13 assembly | ☐ | 0.4–0.8k |
| **remaining** | | **8–17k** (algebraic 2.5–5k, analytic 5.5–11k) |

### Notes for P8 (property (A))

What is available now: (B) as exact identities (16a)/(16b), the coset sums `≡ −1` (P7), and
property (C).

* **The target, sign-robustly.** (A) is needed on function spaces (P10/P11), not only on `V₁₀`.
  State it as a class-function identity: `x ≡ y` iff `∀ M, x(M) + x(−M) = y(M) + y(−M)`. Any
  representation in which `−1` acts trivially respects `≡`. Prove it by pairing `±M` over a
  symmetric finset, as sketched for `actR`. Avoid `ESTraceW.nf`: it is not ±-invariant when
  `c = d = 0`.
* **(A) as orbit sums.** `(1−T)y = L` is solvable (`y(M) = Σ_{k ≥ 0} L(T^{−k}M)`) iff every left
  `Γ∞`-orbit sum of `L = (1−S)T̃ − T^∞(1−S)` vanishes (PZ (10)). So (A) is a statement about the
  finite sums `Σ_k L([[a+kc, b+kd],[c,d]])`.
* **PZ Theorem A route.** `a(K) = ⟨(1−S)T̃, K⟩` on `Γ∞\M` satisfies `a(K) + a(KS) = 0` and
  `a(K) + a(KU) + a(KU²) = 0`. These follow from (B) and the easy direction of Lemma 1:
  `(1−S)π_S ≡ 0` and `(1−S)π_U = (1−T⁻¹)π_U`. Hence `a(K) = a(KT) + a(KT′)`, and acyclicity
  (PZ Lemma 2) forces `supp a ⊂ M∞ ∪ M∞S`. Then `ã(K) = ã(KS) = ã(KT)` is constant on each
  double coset. Theorem B(b) (`α = −β = 1`) is the last piece.
* **Possible shortcut for B(b).** Compute `ã` directly on the upper-triangular orbits
  `[[a, b+kd],[0,d]]`. Only `T₁` (at `c = 0`) and `T̃` at `[[0,−d],[a, b+kd]]` contribute, so
  this replaces PZ's abstract construction of `A, A′`.
* **Estimate.** 2–4k lines: Lemma 2 about 0.3k, the orbit-function analysis about 1k,
  B(b) or the direct `ã` computation about 0.5–1k, and the ± bookkeeping about 0.5k.

### Notes for P13

`traceSum_classNumber` together with `trace_Wper_Ttilde` already give
`tr(T̃ₙ | W₁₀) = hyperbolic − Σ_{t²<4n} p₁₀ H`. Two further steps produce the plan's ES form:
`(d−a)p₁₀(a+d, ad) = d¹¹ − a¹¹`, and `p₁₀(2a, a²) = 11a¹⁰` cancels against `2·p₁₀·H(0)`.
Both are elementary.

## 3. Numerical scripts added (scratch `…/scratchpad/es2/`)

* `pw.py`: the Lemma 4 split identities, pointwise on `[−7,7]⁴`.
* `forms.py`: the six-term fundamental-domain identity on `[−9,9]³`.
* `bnd.py`: maximal entries of each region at `det = n` (all ≤ n).
* `p16.py`, `p16b.py`: the sign choices making (16a)/(16b) exact, and the closed forms
  `T₁S`, `UFS`, `U²F`, `T₁U = T₂`, `SGU`, `QU`.
