# ALG milestone: the R-ord assembly (DONE, axiom-clean) and the conditional headline

`docs/ARITH_ROUTE.md` milestone **ALG** (`ordSum_error`, `ordSum_error_of_approx`,
`iharaApprox_of_arith`), the shared vocabulary for the Eichler–Selberg agent, `HasseAll` for every
prime, and the conditional headline

```lean
theorem RamanujanWeil.Ihara.deligneBound_of_ES_Deuring
    (hES : ∀ (p : ℕ) [Fact p.Prime], EichlerSelbergPrimePow hurwitz p)
    (hD : ∀ (p : ℕ) [Fact p.Prime], OrdinaryDeuring hurwitz p) : RamanujanTau.DeligneBound
```

(`hurwitz = RamanujanWeil.Arith.Hurwitz.hurwitz`). All frozen statements are proved with the text
of `scratch/ArithInterfaces.lean` unchanged; `AssemblyAxioms.lean` restates them verbatim as
`example`s closed by the proved theorems.

| File | Closure | Content |
|---|---|---|
| `RamanujanWeil/Arith/AssemblyVocab.lean` | Mathlib + `IharaStatement` | verbatim `hypTerm`, `esSum`, `ordSum`, `EichlerSelbergPrimePow`, `EichlerSelbergApprox`, `traceCount`, `OrdinaryDeuring`, `HasseAll` (for the ES agent to import) |
| `RamanujanWeil/Arith/AssemblyRecursion.lean` | Mathlib + `TauHecke` | reindexing `t = pt'`, the two HR evaluations, `ordSum_rec` |
| `RamanujanWeil/Arith/AssemblyError.lean` | same | `tauPowerSum_add_two`, `errSum_rec`, `growth_of_rec`, `abs_hypTerm_le`, `ordSum_error_core`, **`ordSum_error`**, **`ordSum_error_of_approx`** |
| `RamanujanWeil/Arith/AssemblyIhara.lean` | + `SupersingularBound`, `EndgameApprox` | `abs_symTrace_ten_le`, `ordinary_part`, `iharaApprox_of_ordError`, **`iharaApprox_of_arith`**, `iharaApprox_of_arith_approx` |
| `RamanujanWeil/Arith/AssemblyAxioms.lean` | | frozen-statement `example`s + `#print axioms` |
| `RamanujanWeil/Ihara/HasseAll.lean` | Weil closure | **`hasseAll : HasseAll p`** for every prime `p` |
| `RamanujanWeil/Ihara/FinalArith.lean` | Weil closure | `iharaApprox_of_ES_Deuring`, `iharaApprox_of_ESApprox_Deuring`, **`deligneBound_of_ES_Deuring`**, `deligneBound_of_ESApprox_Deuring` |
| `RamanujanWeil/Ihara/FinalArithAxioms.lean` | | `#print axioms` |

Every `#print axioms` gives `[propext, Classical.choice, Quot.sound]`. No sorry, no
`native_decide`, no new axioms.

## The algebra (V3b, proved)

Notation: `q = pᵐ`, `A(m) = esSum H (pᵐ)`, `O(m) = ordSum H p m`, `P(m) = A(m) − O(m)` (the
`p ∣ t` part), `λ(m) = hypTerm p m`, `s_m = tauPowerSum p m`, `τ_m = τ(pᵐ)`.

1. **Reindexing** (`sum_dvd_reindex`): `Σ_{t² ≤ 4p^{m+2}, p ∣ t} g(t) = Σ_{t'² ≤ 4pᵐ} g(pt')`, and
   `h₁₀(pt', p^{m+2}) = p¹⁰ h₁₀(t', pᵐ)` (`hq_scale`), `4p^{m+2} − p²t'² = p²(4pᵐ − t'²)`.
2. **HR on the two parts** (only `HurwitzPrimeSquare`; `4q − t² ≡ 0, 3 mod 4` is automatic, so
   `HurwitzConventions` is never used):
   - `hr_ord`: `p ∤ t`, `q = p^{k+1}`: `(−N/p) = 1` (`p` odd: `−N ≡ t²`, `jacobiSym.sq_one'`;
     `p = 2`: `t² ≡ 1 mod 8`) and `p² ∤ N`, so `H(p²N) = p·H(N)`;
   - `hr_dvd`: `t = pu`, `q = p^{k+2}`: `(−N/p) = 0`, `p² ∣ N`, so
     `H(p²N) = (p+1)H(N) − p·H(4pᵏ − u²)`.
3. **`ordSum_rec`**: `O(m+4) = A(m+4) − p¹⁰((p+1)A(m+2) − O(m+2) − p¹¹A(m))`.
4. **`tauPowerSum_add_two`** (Hecke recurrence): `s_{m+2} = τ_{m+2} − p¹¹τ_m`.
5. **`errSum_rec`**: with `E(m) = O(m) + 2s_m` and `ε(m) = A(m) + 2τ_m`,
   `E(m+4) = p¹⁰E(m+2) + ε(m+4) − p¹⁰(p+1)ε(m+2) + p²¹ε(m)`. All τ terms cancel. Under exact ES,
   `ε = −λ` and this is the memo's `μ(m) = −λ(m) + p¹⁰(p+1)λ(m−2) − p²¹λ(m−4)`.

Checked first numerically (exact rationals, `scratchpad/asm/rec.py`): ES `A(m) = −2τ_m − λ(m)` and
the recursion hold exactly for `p = 2, 3, 5`, `pᵐ ≤ 6561`, `m ≥ 4`.

## The bounds (V3c, proved)

* `abs_hypTerm_le`: `|λ(m)| ≤ (m+1)(√p)^{11m}` (`min(pʲ, p^{m−j})² ≤ pᵐ`).
* `μ`-bound: `|ε(k)| ≤ D(k+1)^K(√p)^{11k}` for all `k` gives
  `|μ(m+4)| ≤ 4D(m+5)^K(√p)^{11(m+4)}` (`p¹⁰(p+1)p^{11(m+2)/2} ≤ 2p^{11(m+4)/2}`).
* `growth_of_rec`: `E(m+4) = s²⁰E(m+2) + μ(m+4)`, `s = √p ≥ 1`, gives
  `|E(m)| ≤ C(m+1)^{K+1}s^{11m}` with `C = |E 0| + … + |E 3| + 4D`
  (induction; `(m+3)^{K+1} + (m+5)^K ≤ (m+5)^{K+1}`, and `s²⁰s^{11(m+2)} ≤ s^{11(m+4)}`).
* `ordSum_error`: `K = 1`, `D = 1`, exponent `2` as frozen. `ordSum_error_of_approx`: exponent
  `K + 1`, where `K` comes from `EichlerSelbergApprox`.

## `IharaApprox` (proved)

`ordinary_part`: under `HasseAll` every `a_c` lies in the summation range, so grouping by trace
(`sum_fiberwise_of_maps_to'`) and `OrdinaryDeuring` give
`Σ_{Δ ≠ 0, p ∤ a_c} h₁₀(a_c, q) = q³(q−1)/2 · O(n)`. The `if t² < 4q` in `OrdinaryDeuring` is
always true on the ordinary set (`t² = 4pⁿ`, `n ≥ 1` would force `p ∣ t`). Then

`S(n) − q³(q−1)(−1 − s_n) = q³(q−1)/2 · E(n) + q³(q−1) + S_ss(n)`,

with `|q³(q−1)/2·E(n)| ≤ C(n+1)^k(√p)^{19n}`, `q³(q−1) ≤ q⁴ ≤ (√p)^{19n}`, and
`|S_ss(n)| ≤ #ss · 2876q⁵ ≤ 2876·C_ss·(√p)^{18n}` (`abs_symTrace_ten_le`: `|h₁₀(a,q)| ≤ 2876q⁵`
for `a² ≤ 4q`, from the explicit expansion of `symTrace 10`; `#ss ≤ C_ss p^{4n}` from
`SupersingularCountBound`). So `IharaApprox p` holds with constant `C + 1 + 2876·C_ss` and the same
`k`. `iharaApprox_of_ordError` takes the ordinary error bound as a hypothesis, which gives both
the exact-ES (`iharaApprox_of_arith`) and approximate-ES variants.

## `HasseAll` and the headline (Weil closure)

`hasseAll`: for `c` with `Δ ≠ 0`, `(wc c).IsElliptic` from `hc.isUnit`;
`sq_le_four_mul_card_weierstrassH1' (wc c) (BigEtaleSite.containing (Spec (.of (ZMod p)))) ℓ
h1RankFormula (realizesWeierstrass_projOf _ _)` with a prime `ℓ > p` (as in `Final.lean`), and
`Nat.card (GaloisField p n) = pⁿ`.

`deligneBound_of_ES_Deuring` = `deligneBound_of_iharaApprox_all` ∘ `iharaApprox_of_arith` with
`hurwitzConventions`, `hurwitzPrimeSquare`, `tauHeckeRecurrence`, `supersingularCountBound`,
`hasseAll`. `deligneBound_of_ESApprox_Deuring` is the same with `EichlerSelbergApprox`.

**What remains for unconditional Deligne via this route:** `EichlerSelbergPrimePow hurwitz p`
(or `EichlerSelbergApprox`), milestone A2, and `OrdinaryDeuring hurwitz p`, milestone A3-ord.

## Deviations from the frozen text

None in the statements. Notes:
* `HurwitzConventions H` (`h0`) is a hypothesis of `ordSum_error`, `ordSum_error_of_approx` and
  `iharaApprox_of_arith` but is not used (unused-variable linter warnings only).
* `ordSum_error` does not need ES exactly, only `|A(m) + 2τ(pᵐ)| = O((m+1)(√p)^{11m})`
  (`ordSum_error_core`).
* `TauHeckeRecurrence` and `SupersingularCountBound` are not repeated in `AssemblyVocab.lean`;
  they already exist verbatim in `TauHecke.lean` and `SupersingularBound.lean` (same namespace).
