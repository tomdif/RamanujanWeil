# A1′: Hurwitz conventions and the prime-square relation

Status: **done and axiom-clean**. Every headline declaration depends only on `propext`,
`Classical.choice` and `Quot.sound`. There is no `sorry`, `admit`, `native_decide` or `axiom`
(the audit is `RamanujanWeil/Arith/HurwitzPrimeSquareAxioms.lean`).

Build: `nice -n 10 lake build RamanujanWeil.Arith.HurwitzPrimeSquareAxioms`. Each file takes
roughly 20 to 50 s. The new modules are **not** listed in `RamanujanWeil.lean`, because existing
files were not edited. They import Mathlib and the Hurwitz files only.

## Statements (frozen text, `RamanujanWeil/Arith/ArithVocab.lean`, namespace `RamanujanWeil.ArithPlan`)

`kron`, `HurwitzConventions` and `HurwitzPrimeSquare` are copied verbatim from
`scratch/ArithInterfaces.lean`; a `diff` against the scratch file shows no differences. The file
imports only `Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol`.

```lean
theorem RamanujanWeil.Arith.Hurwitz.hurwitzConventions :
    ArithPlan.HurwitzConventions hurwitz
theorem RamanujanWeil.Arith.Hurwitz.hurwitzPrimeSquare (p : ℕ) (hp : p.Prime) :
    ArithPlan.HurwitzPrimeSquare hurwitz p
```

Both are proved for the computable reduced-form `hurwitz` of `Arith/HurwitzBasic.lean`.

### Edge cases (the frozen statement is correct as written)

* **`N = 0`.** Here `p²·0 = 0`, `kron 0 p = 0`, `p² ∣ 0` and `0 / p² = 0`. The formula reads
  `H(0) = (p+1)·H(0) − p·H(0)`, which holds for any value of `H(0)`. In particular it holds with
  `H(0) = −1/12`. This case is proved separately.
* **`p = 2`.** The hypothesis `N ≡ 0, 3 (mod 4)` is essential. Without it the formula is false:
  for example `H(4·1) = 1/2`, but the right side is `(3 − kron(−1, 2))·H(1) = 0`. The proof uses
  the hypothesis in exactly one place, the `p = 2` case of `card_cond_eq_one`.
* **`p² ∣ N`, so `p ∣ N`.** Here `kron(−N, p) = 0` (`kron_eq_zero_of_dvd`), so the
  `−p·H(N/p²)` term of the frozen statement equals the classical `−(p − (−N/p))·H(N/p²)` term.

## Proof (orbit masses)

Write `mass_G(X, w) = Σ_{O ∈ X/G} w(O)/#Stab(O)` (`wmass`), let `h(N) = mass(Form N)`, so that
`hurwitz N = 2h(N)` for `N ≥ 1` (`hurwitz_eq_two_hm`), and let `T = ℙ¹(𝔽_p)`.

1. `mass(Form N × T) = (p+1)·h(N)`. This is the fibre formula with fibres `≅ T` and
   `#T = p + 1` (`card_P1`).
2. **Induction.** `G = SL₂(ℤ)` acts transitively on `T`. So `mass(Form N × T)` equals the
   `Γ⁰`-mass of `Form N`, where `Γ⁰ = Stab[1:0] = {p ∣ γ₀₁}` (`wmass_induced`).
3. **Conjugation by `diag(1,p)`.** The map `f ↦ (a, pb, p²c)` is a bijection from `Form N` onto
   `{g ∈ Form(p²N) : p ∣ b, p² ∣ c}`, equivariant along
   `γ ↦ [[α, β/p], [pγ', δ]] : Γ⁰ ≃ Γ₀ = Stab[0:1]` (`wmass_equivariant`, `phiEquiv`,
   `sigmaEquiv`).
4. **Superlattices.** Let `Y₂ = {(g, t) : g ∈ Form(p²N), g integral on ℤ² + ℤ·u/p}`, where
   `t = [u]`. Its fibre over `[0:1]` is the set in step 3, so `(p+1) h(N) = mass(Y₂)`
   (`mass_Y2`). Projecting to `g` gives `mass(Y₂) = Σ_{[g]} r(g)/#Stab(g)`, where
   `r(g) = #{t : cond g t}` (`mass_Y2_eq`).
5. **Local counts at `p`** (`HurwitzPrimeSquareCount.lean`):
   * `card_cond_eq_one`: if `g` is `p`-primitive, then `r(g) = 1`. For `p` odd, uniqueness holds
     because two lines would force `p ∣ 2a, b, 2c`, and existence comes from an explicit root.
     For `p = 2` it is a `decide` over `(ℤ/4)⁴`, using `N ≡ 0, 3 (mod 4)`.
   * `cond_scale_iff`: if `g = p·f`, then `r(g)` is the number of roots of `f` on `T`.
   * `card_cond'_prim`: for `f` `p`-primitive with `disc f = −N`, `#roots = 1 + kron(−N, p)`.
     For `p` odd this is the quadratic-formula count via `legendreSym` and `jacobiSym`. For
     `p = 2` it is a `decide` over `(ℤ/8)³`.
   * `card_cond'_of_dvd`: if `p ∣ f`, then `#roots = p + 1`.
6. **Assembly** (`mass_rr`, `mass_rr'`, `hm_prime_square`): splitting along `f ↦ p·f`
   (`Form N → Form(p²N)` and `Form(N/p²) → Form N`) gives
   `(p+1) h(N) = h(p²N) + kron(−N,p)·h(N) + p·[p² ∣ N]·h(N/p²)`. Multiplying by 2 gives the
   frozen statement.

## Files

| File | Lines | Content |
|---|---|---|
| `Arith/ArithVocab.lean` | 30 | frozen `kron`, `HurwitzConventions`, `HurwitzPrimeSquare` |
| `Arith/HurwitzPrimeSquareMass.lean` | 335 | generic `wmass`; `wmass_eq_of_equiv`, `wmass_equivariant`, `Fib` + `wmass_induced`, `wmass_add`/`wmass_const_mul`, `card_fiber_orbit_mul`, `wmass_fiber` |
| `Arith/HurwitzPrimeSquareP1.lean` | 337 | `V2 p = 𝔽_p²` with `γ • v = v γ⁻¹`; `P1 p = ℙ(V2 p)`; `ptZ`, `smul_ptZ`, `ptZ_eq_ptZ`, `enumP_bijective`, `card_P1`, `card_subtype_eq`, `exists_smul_t0`, `mem_stabilizer_t0/t1` |
| `Arith/HurwitzPrimeSquareCount.lean` | 520 | `condZ`/`cond`/`cond'`, lift independence, equivariance, the counts above, `kron_eq_zero_of_dvd` |
| `Arith/HurwitzPrimeSquare.lean` | 491 | finiteness (`finite_stabilizer`, `finite_classes`), `scaleForm`, `upForm`/`downForm`, `sigmaEquiv`, `Y2`, `mass_Y2`, `mass_Y2_eq`, `rr_eq`, `mass_rr`, `mass_rr'`, `hm_prime_square`, the two headline theorems |
| `Arith/HurwitzPrimeSquareAxioms.lean` | 29 | `#print axioms` and `example`s checking the frozen types |

The total is about 1.7k lines. The `ARITH_ROUTE.md` estimate was 2–5k.

## Numerical pre-check

The script `check.py` is in the session scratchpad under `hr/`; its full path is in the session
report. It uses the same reduced-form `H` as Lean. For `p ∈ {2,3,5,7}` and `N < 400`
(`N ≡ 0, 3 mod 4`) it verified:

* the frozen formula;
* `r(g) = 1` for `p`-primitive `g` of discriminant `−p²N`, on reduced forms and some
  `SL₂(ℤ)`-translates;
* `#roots = 1 + kron(−N, p)` for `p`-primitive `f` of discriminant `−N`.

No failures were found.
