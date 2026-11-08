# Arithmetic half: A1 (Hurwitz class numbers) and the A4 torsor count

Status: both pieces are **done and axiom-clean** (`propext`, `Classical.choice`, `Quot.sound` only;
no `sorry`/`admit`/`native_decide`/`axiom`). See `RamanujanWeil/Arith/ArithA1Axioms.lean`.

Build: `nice -n 10 lake build RamanujanWeil.Arith.ArithA1Axioms` (each file elaborates in roughly
10 to 15 s). The Hurwitz files import only Mathlib. `TorsorCount.lean` imports
`RamanujanWeil.Ihara.IharaStatement` for `wc` and `traceOfFrob`. Loading those prebuilt oleans
takes about 40 s; nothing is rebuilt. The new modules are **not** yet listed in
`RamanujanWeil.lean`, because existing files were not edited. Add
`import RamanujanWeil.Arith.ArithA1Axioms` there to include them in the default target.

## Files

| File | Content |
|---|---|
| `RamanujanWeil/Arith/HurwitzBasic.lean` | `QF`, `disc`, `eval`, `IsReduced`, the `SL(2,ℤ)` action, `Form N`, and the computable `H6`/`hurwitz` |
| `RamanujanWeil/Arith/HurwitzReduction.lean` | Reduction theory: existence, entry bound, 81-case check, uniqueness, stabilizer orders |
| `RamanujanWeil/Arith/HurwitzOrbit.lean` | Orbit-count and class-count definitions, the main equalities, `H = 0` for `N ≡ 1,2 (4)`, sanity values, and the Kronecker–Hurwitz check |
| `RamanujanWeil/Arith/TorsorCount.lean` | A4: `wc` bijection, `#G`, point-count/trace invariance, orbit–stabilizer torsor count, and the orbit decomposition of the Weierstrass sum |
| `RamanujanWeil/Arith/ArithA1Axioms.lean` | `#print axioms` for the headline results |

## A1: Hurwitz class numbers

### Conventions

* `QF = (a, b, c) : ℤ³`, `f(x,y) = ax² + bxy + cy²`, `disc f = b² − 4ac`.
* Action (left): `(γ • f)(x, y) = f((x, y)·γ)`. For `γ = [[p,q],[r,s]]`,
  `γ • f = (f(p,q), 2apr + b(ps+qr) + 2cqs, f(r,s))`. The `MulAction SL(2,ℤ) QF` instance uses
  Mathlib's `Matrix.SpecialLinearGroup`. Orbits are the usual proper-equivalence classes,
  because transpose is a bijection of `SL₂(ℤ)`.
* `Form N = {f // disc f = −N ∧ disc f < 0 ∧ a > 0}`, the positive definite forms. This set is
  empty for `N = 0` and is an `SL(2,ℤ)`-set.
* `IsReduced f :⇔ −a < b ≤ a ≤ c ∧ (a = c → b ≥ 0)`. `isReduced_iff` shows that for `a > 0` this
  equals the textbook condition `|b| ≤ a ≤ c`, `b ≥ 0` if `|b| = a` or `a = c`. The
  `omega`-friendly form is used as the definition.

### Definitions

* `H6 N : ℕ = Σ_{(a,b) ∈ redPairs N} wt6(a, b, (b²+N)/4a)`. `redPairs N` consists of the pairs
  with `1 ≤ a ≤ √N`, `|b| ≤ √N`, `4a ∣ b²+N` and the form reduced. The weight is
  `wt6 = 3` for `(a,0,a)`, `2` for `(a,a,a)`, and `6` otherwise.
* `hurwitz N : ℚ = if N = 0 then −1/12 else H6 N / 6`. This is computable.
* `hurwitzOrbit N = ∑ᶠ O : orbitRel.Quotient SL(2,ℤ) (Form N), 2 / Nat.card (stabilizer SL(2,ℤ) O.out)`.
* `hurwitzClasses N = ∑ᶠ O, classWeight O`, where `classWeight O` is `1/2` if `O` contains a
  form with `b = 0, a = c`, `1/3` if `O` contains a form with `b = a = c`, and `1` otherwise.

### Headline results

```lean
theorem hurwitz_eq_hurwitzOrbit {N : ℕ} (hN : 0 < N) : hurwitz N = hurwitzOrbit N
theorem hurwitz_eq_hurwitzClasses {N : ℕ} (hN : 0 < N) : hurwitz N = hurwitzClasses N
theorem hurwitz_zero : hurwitz 0 = -1 / 12
theorem hurwitz_eq_zero_of_mod_four {N : ℕ} (h : N % 4 = 1 ∨ N % 4 = 2) : hurwitz N = 0
theorem hurwitz_values : hurwitz 3 = 1/3 ∧ hurwitz 4 = 1/2 ∧ hurwitz 7 = 1 ∧ hurwitz 8 = 1 ∧
  hurwitz 11 = 1 ∧ hurwitz 12 = 4/3 ∧ hurwitz 15 = 2 ∧ hurwitz 16 = 3/2 ∧ hurwitz 20 = 2 ∧
  hurwitz 23 = 3                                   -- H6 values by `decide +kernel`
theorem kronecker_hurwitz_check : ∀ n ∈ Finset.Icc 1 20, khLHS12 n = khRHS12 n  -- decide +kernel
lemma khLHS12_eq (n) : (khLHS12 n : ℚ) = 12 * Σ_{t ∈ [-2n,2n], t² ≤ 4n} hurwitz (4n − t²)
```

Here `khRHS12 n = 12·(2σ(n) − Σ_{d∣n} min(d, n/d))`. Kronecker–Hurwitz is only checked
numerically for `n ≤ 20`, as requested. It is not proved in general.

### Reduction theory (the proof)

* `exists_reduced`: by strong induction on `a`. Apply `[[1,0],[k,1]]` with
  `k = (a−b) div 2a` to get `b ∈ (−a, a]`. If `c < a`, apply `S = [[0,1],[−1,0]]`, which gives
  `(c, −b, a)`, and recurse. If `a = c` and `b < 0`, finish with `S`.
* `entries_bound`: if `f` and `γ • f` are both reduced, every entry of `γ` lies in `{−1,0,1}`.
  1. Use `f(x,y) ≥ a|x|² − a|x||y| + c|y|²` and `X² − XY + Y² ≥ 1` (resp. `≥ 3` if `max ≥ 2`).
  2. Together these give `a(γ•f) = a(f)`, i.e. `min f = a`, attained only at `|x|,|y| ≤ 1`.
  3. Equal discriminants then give `4a·c(γ•f) ≤ 4ac + a²`. The value `f(r,s)` is larger outside
     `|s| ≤ 1 ∧ (|r| ≤ 1 ∨ s = 0)`. When `s = 0`, the determinant gives `|r| = 1`.
* `reduced_cases`: this is the remaining finite check, `interval_cases` over 81 matrices followed
  by `omega`. If `γ • f` is reduced, then `γ • f = f`, and `γ = ±1` unless `f` is `(a,0,a)` or
  `(a,a,a)`.
* `reduced_unique`, `card_stabilizer_reduced` (`#Stab = 4 / 6 / 2`): `Stab(f)` injects via its
  entries onto `stabSet f ⊆ {−1,0,1}⁴`. In the special cases, `stabSet` is scale-invariant and is
  computed by `decide` at `(1,0,1)` and `(1,1,1)`.
* Orbit side: `toClass : Red N → Classes N` is bijective, and `#Stab` is constant on orbits by
  `stabilizer_smul_eq_stabilizer_map_conj`. `pairEquiv` matches `redPairs N` with the reduced forms.

## A4: coordinate-change torsor count

`G = WeierstrassCurve.VariableChange K` with Mathlib's `MulAction G (WeierstrassCurve K)`, written
`C • W`. `K` is any finite field, so characteristics 2 and 3 are included. There are no
characteristic hypotheses anywhere.

```lean
def wcEquiv : (Fin 5 → K) ≃ WeierstrassCurve K        -- toFun = wc, so G acts on K⁵ through wc
theorem card_vc [Finite K] : Nat.card (VariableChange K) = (Nat.card K - 1) * Nat.card K ^ 3
theorem card_point_smul [Finite K] (C W) : Nat.card (C • W).toAffine.Point = Nat.card W.toAffine.Point
theorem traceOfFrob_smul [Finite K] (C W) : traceOfFrob (C • W) = traceOfFrob W
theorem card_isoClass_mul_card_stabilizer [Finite K] (c : Fin 5 → K) (hc : (wc c).Δ ≠ 0) :
    Nat.card {c' : Fin 5 → K // (wc c').Δ ≠ 0 ∧ wc c' ∈ orbit (VariableChange K) (wc c)} *
      Nat.card (stabilizer (VariableChange K) (wc c)) = (Nat.card K - 1) * Nat.card K ^ 3
theorem finsum_eq_finsum_orbits [Finite K] {R} [Field R] [CharZero R] (φ : WeierstrassCurve K → R)
    (hφ : ∀ C W, φ (C • W) = φ W) :
    ∑ᶠ W, φ W = ((q-1) q³ : ℕ) * ∑ᶠ O, φ O.out / Nat.card (stabilizer G O.out)
theorem sum_trace_eq_sum_orbits [Fintype K] [DecidableEq K] {R} [Field R] [CharZero R] (F : ℤ → R) :
    ∑ c ∈ univ.filter (fun c => (wc c).Δ ≠ 0), F (traceOfFrob (wc c)) =
      ((Fintype.card K - 1) * Fintype.card K ^ 3 : ℕ) *
        ∑ᶠ O : orbitRel.Quotient G (WeierstrassCurve K),
          if O.out.Δ ≠ 0 then F (traceOfFrob O.out) / Nat.card (stabilizer G O.out) else 0
```

Design notes:

* `wc c = ⟨c 0, c 1, c 2, c 3, c 4⟩ = (a₁, a₂, a₃, a₄, a₆)`, and `wcEquiv` inverts it with
  `![a₁,a₂,a₃,a₄,a₆]`. Every Weierstrass curve is some `wc c`, so the `G`-action never leaves the
  image of `wc`. `Δ(C • W) = u⁻¹²Δ(W)` makes "elliptic" `G`-invariant (`Δ_smul_ne_zero_iff`).
* The stabilizer `Stab_G(W)` is the automorphism group of `(W, O)` as a Weierstrass model.
  Identifying it with `Aut(E)` of the abstract curve uses the classical fact that every
  isomorphism of Weierstrass models is a coordinate change. That fact is not needed here,
  because the A4 identity is stated with `Stab_G`.
* Point-count invariance (Mathlib had none) is proved by an explicit map
  `(C•W)(K) → W(K)`, `(x,y) ↦ (u²x + r, u³y + u²sx + t)`, valid for **every** curve, singular
  ones included. Nonsingularity transfers via `E_W = u⁶E_{C•W}`,
  `∂ₓ' = u⁻⁴(∂ₓ − s∂_y)` and `∂_y' = u⁻³∂_y`. The map is injective, and the same map for `C⁻¹`
  gives the reverse inequality on `Nat.card`. `W(K)` is `Finite` (`point_finite`) by injecting
  into `Option (K × K)`.
* The statements use `Nat.card` and `finsum` over the orbit space, with no `Fintype` instances.

## Numerical sanity

The script `torsor_check.py` (and its output `torsor_check.out`) is in the session scratchpad
under `arith/`; its full path is in the session report. For p = 5 and 7 it
enumerates `𝔽_p⁵`, computes the `G`-orbits with Mathlib's `variableChange` formulas, and checks
four things:

1. Every orbit stays elliptic and has constant trace.
2. `#orbit · #Stab = (p−1)p³`.
3. `#{c : a(E_c) = t} = (p−1)p³ Σ_{a_O = t} 1/#Stab(O)` for all `t`.
4. The Deuring–Eichler cross-link to A1, `Σ_{a_O = t} 1/#Aut(O) = H(4p − t²)/2`.

The orbit counts are 12 for p = 5 and 18 for p = 7. All checks pass ("ALL OK").

## What remains

* **Kronecker–Hurwitz / Eichler–Selberg** (A2) are only checked numerically (`n ≤ 20`).
* **Deuring/Eichler class-number count** (A3), `Σ_{E/𝔽_q, a(E)=t} 1/#Aut E = H(4q − t²)/2`
  (ordinary `t`, plus supersingular corrections), is not attempted. Combined with
  `sum_trace_eq_sum_orbits`, it turns the Weierstrass sum into `Σ_t F(t)·H(4q−t²)`.
* The `H(p²M)` vs `H(M)` relation and the `Σ_{O} h(O)/(#O^×/2)` order-sum formula from §A1 of
  the plan are not done.
* `Stab_G(W) ≅ Aut(E)` for the abstract curve is not formalized (see the design note above).
