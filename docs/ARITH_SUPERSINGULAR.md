# SS milestone: the supersingular count bound (DONE, axiom-clean)

`docs/ARITH_ROUTE.md` milestone **SS**, the frozen statements `hasseInv`, `dvd_traceOfFrob_iff`,
`SupersingularCountBound` and `supersingularCountBound` from `scratch/ArithInterfaces.lean`. All of
them are now proved, with the statements unchanged, in namespace `RamanujanWeil.ArithPlan`.

| File | Content |
|---|---|
| `RamanujanWeil/Arith/SupersingularTrace.lean` | `hasseInv` (verbatim), the Hasse digit lemma, the point count, `a mod p`, and `dvd_traceOfFrob_iff` |
| `RamanujanWeil/Arith/SupersingularBound.lean` | the generic Hasse polynomial, its degree and nonvanishing, Schwartz–Zippel, `SupersingularCountBound` (verbatim), and `supersingularCountBound` |
| `RamanujanWeil/Arith/SupersingularAxioms.lean` | `#print axioms`. Every declaration gives `[propext, Classical.choice, Quot.sound]` |

The imports are Mathlib and `RamanujanWeil.Ihara.IharaStatement` only. The proof is about 600
lines, with no sorry and no `native_decide`.

## Statements

```lean
theorem dvd_traceOfFrob_iff (p : ℕ) [Fact p.Prime] (n : ℕ) (hn : 1 ≤ n)
    (c : Fin 5 → GaloisField p n) (hc : (wc c).Δ ≠ 0) :
    letI : Fintype (GaloisField p n) := Fintype.ofFinite _
    ((p : ℤ) ∣ traceOfFrob (wc c) ↔ if p = 2 then c 0 = 0 else hasseInv p c = 0)

theorem supersingularCountBound (p : ℕ) [Fact p.Prime] : SupersingularCountBound p
-- with C = p:  #{c ∈ 𝔽_q⁵ : Δ ≠ 0 ∧ p ∣ a_c} ≤ p · q⁴   (q = pⁿ)
```

The general versions hold over any finite field `F` with `CharP F p`:
`dvd_traceOfFrob_iff_of_finite` and `card_dvd_traceOfFrob_le`.

## Proof

1. **Point count** (`natCard_point`). Mathlib's `nonsingularPointEquiv` and
   `equation_iff_nonsingular_of_Δ_ne_zero` give `#E = #{(x,y) : Equation} + 1`. Hence
   `(a : F) = −#{(x,y) : Equation}` (`traceOfFrob_cast`).
2. **p odd** (`traceOfFrob_cast_odd`).
   - The substitution `y ↦ 2y + a₁x + a₃` turns the equation into `y² = f(x)`, where
     `f = 4x³ + b₂x² + 2b₄x + b₆`.
   - Euler's criterion (`quadraticChar_card_sqrts` and `quadraticChar_eq_pow_of_char_ne_two'`) gives
     `#{y} ≡ 1 + f(x)^{(q−1)/2}`.
   - `Σ_{x∈𝔽_q} g(x) = −coeff_{q−1} g` whenever `deg g < 2(q−1)` (`sum_eval_eq_neg_coeff`, from
     `FiniteField.sum_pow_units`).
   - Together these give `(a : 𝔽_q) = coeff_{x^{q−1}} f^{(q−1)/2}`.
3. **Digit lemma** (`hasseCoeff_succ`). Let `A_k = coeff_{x^{pᵏ−1}} f^{(pᵏ−1)/2}` for any cubic `f`
   in characteristic `p`. Then `A_{k+1} = A_k · A_1^{pᵏ}`.
   - Write `f^{(p^{k+1}−1)/2} = f^{(pᵏ−1)/2} · (f^{(p−1)/2})^{pᵏ}`, and expand the second factor
     with `map_iterateFrobenius_expand`.
   - Only the index `t = p − 1` survives. If `t ≤ p − 2`, the remaining index is `≥ 2pᵏ − 1`, which
     exceeds `3(pᵏ−1)/2`. If `t ≥ p`, the index overshoots.
   - So `A_n = 0 ⟺ A_1 = hasseInv p c = 0` (`hasseCoeff_eq_zero_iff`).
4. **p = 2** (`traceOfFrob_cast_two`).
   - The involution `(x,y) ↦ (x, negY x y)` on affine points satisfies
     `#aff ≡ #fixed (mod 2)` (`Equiv.Perm.card_fixedPoints_modEq`).
   - The fixed points are the `x` with `a₁x + a₃ = 0`, each with exactly one `y`, because
     Frobenius is bijective.
   - So `(a : F) = −1` if `a₁ ≠ 0`. If `a₁ = 0`, it is `0`, because `Δ ≠ 0` forces `a₃ ≠ 0`
     (`delta_eq_zero_two`).
5. **Count** (`card_dvd_traceOfFrob_le`). The bad set lies in the zero set of a polynomial `P`.
   For `p = 2`, `P = X₀`, of degree 1. For `p` odd, `P = hassePoly F p := hasseInv p (X₀,…,X₄)`,
   which has the following properties:
   - It evaluates to `hasseInv p c` (`eval_hassePoly`).
   - Its total degree is `≤ ((p−1)/2)·2 ≤ p`. The coefficients of `f` have degree `≤ 2`
     (`totalDegree_coeff_pow_le`).
   - It is nonzero, because at `c = (0,1,0,0,0)` we get `f = x²(4x+4)` and
     `hasseInv = 4^{(p−1)/2} ≠ 0`.

   `MvPolynomial.schwartz_zippel_totalDegree` with `S = 𝔽_q` then gives `≤ deg·q⁴ ≤ p·q⁴`.

## Numerical check

The script is `…/scratchpad/ss/check.py` (session scratch, not in the repo). It checks random
tuples with `Δ ≠ 0` over q = 2, 4, 8, 3, 9, 27, 5, 25, 7. For p odd, it confirms both
`a mod p = A_q(c)` and `p ∣ a ⟺ A_p(c) = 0`. For p = 2, it confirms `2 ∣ a ⟺ a₁ = 0`. No
counterexamples were found.

## Deviations

- None in the statements. `hasseInv`, `SupersingularCountBound` and the statement of
  `dvd_traceOfFrob_iff` are character-for-character the frozen ones.
- New helper definitions are `hasseCubic`, `hasseCoeff` and `hassePoly`. The explicit constant is
  `C = p`.
