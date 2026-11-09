# A3-ord, approximate form: dropping Deuring/Honda existence (2026-11-09)

This continues `docs/ARITH_DEURING_G7.md` (§2, "O(1) version"). New files, no existing file
edited:

| File | Content |
|---|---|
| `RamanujanWeil/Arith/DeuringApproxKH.lean` | right-coset decomposition, **Kronecker–Hurwitz** (all `n ≥ 1`), weight-0 recursion, `ordSum0_bound` |
| `RamanujanWeil/Arith/DeuringApproxCount.lean` | `Δ` as a polynomial, `#{Δ = 0} ≤ D₀q⁴`, `card_ordinary_lower` |
| `RamanujanWeil/Arith/DeuringApprox.lean` | `OrdinaryDeuringApprox`, `iharaApprox_of_deuringApprox` |
| `RamanujanWeil/Arith/DeuringApproxMult.lean` | `DeuringMultiplicity`, `KroneckerHurwitz{Lower,Upper}`, existence and uniqueness variants |
| `RamanujanWeil/Ihara/FinalDeuringApprox.lean` | headlines |
| `RamanujanWeil/Arith/DeuringApproxAxioms.lean` | `#print axioms` audit |

## 0. Summary

```lean
-- Ihara/FinalDeuringApprox.lean
theorem deligneBound_of_DeuringApprox
    (hD : ∀ (p : ℕ) [Fact p.Prime], OrdinaryDeuringApprox hurwitz p) :
    RamanujanTau.DeligneBound

theorem deligneBound_of_DeuringMult_unique (mult : ℕ → ℕ → ℤ → ℕ)
    (hM : ∀ (p : ℕ) [Fact p.Prime], DeuringMultiplicity hurwitz p (mult p))
    (huniq : ∀ (p : ℕ) [Fact p.Prime], ∀ n : ℕ, 1 ≤ n → ∀ t : ℤ, ¬ (p : ℤ) ∣ t →
      t ^ 2 < 4 * (p : ℤ) ^ n → mult p n t ≤ 1) :
    RamanujanTau.DeligneBound

theorem deligneBound_of_DeuringMult_exists (mult : ℕ → ℕ → ℤ → ℕ)
    (hM : ∀ (p : ℕ) [Fact p.Prime], DeuringMultiplicity hurwitz p (mult p))
    (hex : ∀ (p : ℕ) [Fact p.Prime], ∀ n : ℕ, 1 ≤ n → ∀ t : ℤ, ¬ (p : ℤ) ∣ t →
      t ^ 2 < 4 * (p : ℤ) ^ n → 1 ≤ mult p n t) :
    RamanujanTau.DeligneBound
```

with

```lean
-- Arith/DeuringApprox.lean
def OrdinaryDeuringApprox (H : ℕ → ℚ) (p : ℕ) [Fact p.Prime] : Prop :=
  ∃ C : ℝ, ∃ k : ℕ, ∀ n : ℕ, 1 ≤ n →
    ∑ t ∈ (tset p n).filter (fun t => ¬ (p : ℤ) ∣ t),
      |(((traceCount p n t : ℚ) -
          (p : ℚ) ^ (3 * n) * ((p : ℚ) ^ n - 1) * H (nArg p n t) / 2 : ℚ) : ℝ)| ≤
      C * ((n : ℝ) + 1) ^ k * Real.sqrt p ^ (9 * n)

-- Arith/DeuringApproxMult.lean
def DeuringMultiplicity (H : ℕ → ℚ) (p : ℕ) [Fact p.Prime] (mult : ℕ → ℤ → ℕ) : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ t : ℤ, ¬ (p : ℤ) ∣ t → t ^ 2 < 4 * (p : ℤ) ^ n →
    (traceCount p n t : ℚ) =
      (p : ℚ) ^ (3 * n) * ((p : ℚ) ^ n - 1) * (mult n t : ℚ) *
        H (4 * (p : ℤ) ^ n - t ^ 2).toNat / 2
```

(`tset p n = {t : t² ≤ 4pⁿ}`, `nArg p n t = (4pⁿ − t²).toNat`, both from
`AssemblyRecursion.lean`.) Everything else is proved: Eichler–Selberg (`eichlerSelberg_all`),
Hasse, the supersingular count, Kronecker–Hurwitz and the ordinary tuple count.

**Deuring/Honda existence is no longer needed.** Uniqueness alone (`m ≤ 1`) suffices, and so
does existence alone (`m ≥ 1`). `OrdinaryDeuring ⇒ OrdinaryDeuringApprox` with `C = 0`
(`ordinaryDeuringApprox_of_exact`), and `deligneBound_of_Deuring'` re-derives the old headline
through the new one.

Axiom audit (`nice -n 10 lake build RamanujanWeil.Arith.DeuringApproxAxioms`): every one of the
26 audited results depends on `[propext, Classical.choice, Quot.sound]` only. There is no
`sorry`, `admit`, `native_decide` or `axiom`.

## 1. How `OrdinaryDeuring` was consumed, and the error budget (checked)

`OrdinaryDeuring` is used in exactly one place, `ordinary_part` (`AssemblyIhara.lean`). That
lemma rewrites the ordinary part of `S(n) = weierstrassSum p n` as `q³(q−1)/2 · ordSum H p n`
exactly. `iharaApprox_of_ordError` then decomposes

  `S(n) − q³(q−1)(−1 − s_n) = q³(q−1)/2·E(n) + q³(q−1) + S_ss(n)`

and bounds each piece by `(n+1)^k (√p)^{19n}`, the `IharaApprox` budget:
* `E(n) = ordSum + 2s_n` is bounded by `C(n+1)²(√p)^{11n}` (ES + `HurwitzPrimeSquare` + Hecke,
  `ordSum_error`), so the first piece is `O(q⁴·q^{11/2}) = O(q^{19/2})`;
* `S_ss` has `≤ p·q⁴` terms of size `≤ 2876q⁵`, so it is `O(q⁹)`.

With approximate Deuring there is one more piece:
`R(n) = Σ_{p∤t} (N(t) − q³(q−1)H/2)·h₁₀(t,q)`. Because `|h₁₀(t,q)| ≤ 2876q⁵` for `t² ≤ 4q`
(`abs_symTrace_ten_le`), `|R| ≤ 2876 q⁵ · Σ|N − main| ≤ 2876 C (n+1)^k q^{19/2}`. **The
`IharaApprox` budget therefore allows an `ℓ¹` count defect of `O((n+1)^k q^{9/2})`**, which is
what `OrdinaryDeuringApprox` states. `iharaApprox_of_deuringApprox_ordError` is a copy of
`iharaApprox_of_ordError` with this fourth piece added.

**Check of the proposed plan.** The plan was "missing mass `O_p(1)`". The budget is more
generous than that. With `m − 1` of constant sign,

  `Σ_{p∤t}|N(t) − main(t)| = q³(q−1)/2 · Σ_{p∤t} |m(t) − 1|·H(4q−t²)`,

so the missing mass `Σ|m−1|H` may be as large as `O((n+1)^k √q)`. The proved Kronecker–Hurwitz
bound gives `O((n+1)²√q)`. It does not give `O(1)`: the `λ(pᵐ)` terms enter the weight-0
recursion and the bound proved is `|O₀(m) − 2pᵐ| ≤ C(m+1)²(√p)ᵐ`. That still fits. The plan is
**confirmed, with the bound needed relaxed to `O((n+1)^k √q)`**. Two refinements:

1. **Which direction of KH is needed depends on the variant.**
   * Existence (`m ≥ 1`): `Σ|d| = N_ord − q³(q−1)/2·O₀`. This needs a **lower** bound
     `O₀ ≥ 2q − CX` and the trivial `N_ord ≤ q⁵`. The defect is then `≤ q⁴ + q⁴CX/2`.
   * Uniqueness (`m ≤ 1`): `Σ|d| = q³(q−1)/2·O₀ − N_ord`. This needs an **upper** bound
     `O₀ ≤ 2q + CX` and a lower bound `N_ord ≥ q⁵ − C'q⁴`. The latter is the nonsingular count
     (Schwartz–Zippel on `Δ`, `card_ordinary_lower`) minus the supersingular count. The defect is
     then `≤ C'q⁴ + q⁴CX/2`.

   Here `X = (n+1)^k(√p)ⁿ`, `N_ord = Σ_{p∤t} N(t) = #{c : Δ ≠ 0, p ∤ a_c}` (Hasse,
   `sum_traceCount_ord`), and `O₀ = Σ_{p∤t,t²≤4q} H(4q−t²)`.
2. With `n ≥ 1`, no parabolic term `t² = 4q` has `p ∤ t`. So `O₀(n)` is exactly the ordinary
   class-number mass `Σ_{p∤t, t²<4q} H(4q − t²)`.

## 2. Kronecker–Hurwitz from the Popa–Zagier core (no analytic input)

**The ES files are not parametrized by weight.** `Fin 11`, `symTr10` and `W₁₀` are hard-coded in
`ESInput`, `ESEigen`, `ESTraceW`, `ESAnalytic*`. But their **weight-free core already exists**:
* `trSum_ptC`: `Σ_{tr=t} T̃ = Σ_{tr=t} H − Σ_{tr=t} E`;
* `trSum_regE`: `Σ_{tr=t} E = H(4n − t²)`;
* `sum_trSum_regH`: the hyperbolic sum, for an **arbitrary** weight function `g`;
* `sum_trSum_eq_box`;
* `cS_ptC_eq_neg_one`: `⟨T̃ₙ, AΓ⟩ = −1` for every right coset (PZ Thm 4(b)).

At weight 2 (`w = 0`, `g ≡ 1`) the trace of `T̃ₙ` on `V₀` is `Σ_{det=n} T̃ₙ(M)`. Instead of going
through the period space (`W₀ = 0` because `S₂ = 0`), we sum the coset identity over the right
cosets. **This is the only new mathematics:**

* `cosetKey M = (gcd(a,b), (cx + dy) mod (n/g))` and `cosetRep n (g,c) = [[g,0],[c,n/g]]`;
* `cosetCof_spec`: `M = cosetRep · γ` with `det γ = 1` (explicit Bezout cofactor);
* `cosetKey_rep_mul`: `cosetKey (cosetRep k · γ) = k` (uniqueness of the Hermite form);
* `sum_fiber_ptC`: the fibre sum over one key equals `cS ptC (cosetRep k) = −1`;
* `card_cosetKeys`: `#keys = Σ_{0<a∣n} n/a = σ(n)`;
* `sum_box_ptC`: `Σ_{det M = n} T̃ₙ(M) = −σ(n)`.

Combining these with `hypW(a,d) = d − min(a,d) + [a=d]/6` and the parabolic count gives

```lean
theorem kroneckerHurwitz (n : ℕ) (hn : 1 ≤ n) :
    ∑ t ∈ Icc (-(2 * (n : ℤ))) (2 * n) with t ^ 2 ≤ 4 * (n : ℤ),
        Hurwitz.hurwitz (4 * (n : ℤ) - t ^ 2).toNat =
      ∑ a ∈ (Icc (1 : ℤ) n).filter (· ∣ (n : ℤ)),
        ((2 * ((n : ℤ) / a) - min a ((n : ℤ) / a) : ℤ) : ℚ)
```

This is Hurwitz's `Σ_t H(4n − t²) = 2σ(n) − λ(n)` with `H(0) = −1/12`. Sanity check `n = 1`:
`H(4) + 2H(3) + 2H(0) = 1/2 + 2/3 − 1/6 = 1 = 2 − 1`. At prime powers (`esSum0_hurwitz`):
`A₀(m) = 2σ(pᵐ) − λ₀(m)`, with `λ₀(m) = Σ_j min(pʲ, p^{m−j}) ≤ (m+1)(√p)ᵐ`.

**Subtracting the `p ∣ t` terms.** `ordSum0_rec` is the weight-0 copy of `ordSum_rec`. It uses
the same reindexing and `HurwitzPrimeSquare` lemmas (`sum_dvd_reindex`, `hr_ord`, `hr_dvd`,
`nArg_scale`), with `p¹⁰ ↦ 1` and `p¹¹ ↦ p`:

  `O₀(m+4) = A₀(m+4) − (p+1)A₀(m+2) + O₀(m+2) + pA₀(m)`.

Since `σ(p^{m+4}) − (p+1)σ(p^{m+2}) + pσ(pᵐ) = p^{m+4} − p^{m+2}`, the quantity
`E₀(m) = O₀(m) − 2pᵐ` satisfies

  `E₀(m+4) = E₀(m+2) − λ₀(m+4) + (p+1)λ₀(m+2) − pλ₀(m)`,

with forcing `≤ 4(m+5)(√p)^{m+4}`. `growth0` then gives

```lean
theorem ordSum0_bound (p) [Fact p.Prime] :
    ∃ C : ℝ, ∀ m : ℕ,
      |((ordSum0 p Hurwitz.hurwitz m - 2 * (p : ℚ) ^ m : ℚ) : ℝ)| ≤
        C * ((m : ℝ) + 1) ^ 2 * Real.sqrt p ^ m
```

and hence `kroneckerHurwitzLower_hurwitz`, `kroneckerHurwitzUpper_hurwitz` with `k = 2`.
Numerically `2q − O₀(n) = 2·#SS(𝔽_p)` is constant in `n`, so the true error is `O(1)`
(G7 §2, `scratchpad/g7/kh.gp`). The proved `O((m+1)²√q)` is weaker but sufficient. Making it
exact would need the exact supersingular `j`-count, which is not needed here.

## 3. Dependency picture

```
deligneBound_of_DeuringMult_unique          deligneBound_of_DeuringMult_exists
  │ hM : DeuringMultiplicity hurwitz p m       │ hM : DeuringMultiplicity hurwitz p m
  │ huniq : m ≤ 1  (Tate uniqueness)           │ hex : m ≥ 1  (Deuring/Honda existence)
  ├ kroneckerHurwitzUpper_hurwitz  ✔           ├ kroneckerHurwitzLower_hurwitz  ✔
  ├ card_ordinary_lower  ✔ (Schwartz–Zippel    ├ N_ord ≤ q⁵  ✔ (trivial)
  │   on Δ + card_dvd_traceOfFrob_le)          │
  └──────────────┬─────────────────────────────┘
                 ▼
  OrdinaryDeuringApprox hurwitz p      (⇐ OrdinaryDeuring, C = 0)
                 │  + eichlerSelberg_all ✔, hurwitzPrimeSquare ✔, tauHeckeRecurrence ✔,
                 │    supersingularCountBound ✔, hasseAll ✔  (iharaApprox_of_deuringApprox)
                 ▼
  IharaApprox p  ──deligneBound_of_iharaApprox_all ✔──▶  RamanujanTau.DeligneBound
```

**Named Props that remain** (all at `H = hurwitz`, for every prime `p`):
1. `DeuringMultiplicity hurwitz p m`: the per-class lattice count, i.e. route L of
   `DeuringAssembly` **without** `surj`. Each ordinary isogeny class of trace `t` contributes
   `q³(q−1)H(4q−t²)/2` tuples (G1 + G8(ii) per class; plan §4).
2. **One of** `m ≤ 1` (Tate uniqueness: G7, done modulo `QuotientFiniteness` + the bridge
   §3.6/G7-dual) **or** `m ≥ 1` (Deuring/Honda existence, ≥ 20k lines; not recommended).

**No class-number Prop remains:** the Kronecker–Hurwitz bound is proved. So the recommended
route to Deligne is: G1 + G8(ii) per-class count, plus Tate uniqueness (`QuotientFiniteness`
+ G7-dual), plus this file.

Note on `DeuringMultiplicity`: `m(t)` is existentially free. The interface only asks that
`N(t)` be a natural multiple `m(t)` of the class mass, which is how route L produces it (sum over
the classes of trace `t`, each class contributing `q³(q−1)·Σ_{E ∈ class} 1/#Aut E =
q³(q−1)H/2`). The trivial choice `m(t) := N(t)/(q³(q−1)H/2)` is not a natural number in general,
so the hypothesis has content.

## 4. Lean statistics

| File | Lines | Main results |
|---|---|---|
| `DeuringApproxKH.lean` | ~570 | `cosetCof_spec`, `cosetKey_rep_mul`, `sum_fiber_ptC`, `sum_box_ptC`, **`kroneckerHurwitz`**, `ordSum0_rec`, `esSum0_hurwitz`, `growth0`, **`ordSum0_bound`** |
| `DeuringApproxCount.lean` | ~125 | `deltaPoly`, `deltaPoly_ne_zero`, `card_singular_le`, **`card_ordinary_lower`** |
| `DeuringApprox.lean` | ~300 | **`OrdinaryDeuringApprox`**, `ordinaryDeuringApprox_of_exact`, `ordinary_part_traces`, **`iharaApprox_of_deuringApprox`** |
| `DeuringApproxMult.lean` | ~370 | **`DeuringMultiplicity`**, `KroneckerHurwitz{Lower,Upper}` (+ `_hurwitz`), `sum_traceCount_ord`, **`ordinaryDeuringApprox_of_mult_{exists,unique}`** (+ `_hurwitz`) |
| `Ihara/FinalDeuringApprox.lean` | ~75 | **`deligneBound_of_DeuringApprox`**, **`deligneBound_of_DeuringMult_{unique,exists}`**, `deligneBound_of_Deuring'` |
