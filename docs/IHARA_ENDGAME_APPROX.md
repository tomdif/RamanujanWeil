# M1′: the approximate Ihara endgame (`deligne_of_package_approx`), proved

Status (2026-11-08): **proved, sorry-free**, standard axioms only (see the audit below).

Files:
- `RamanujanWeil/Ihara/EndgameApprox.lean`. Namespace `RamanujanWeil.Ihara`. Imports
  `RamanujanWeil.Ihara.IharaStatement` (itself only `Endgame.lean` + Mathlib, needed for
  `weierstrassSum`/`IharaIdentity`) and two Mathlib analysis files. Not Weil. Builds in about 10 s.
- `RamanujanWeil/Ihara/FinalApprox.lean` (M1′b, Weil closure). A near-copy of
  `Assembly.lean` + `M4b.lean` + `Final.lean` with the M1 call swapped for M1′.
- `RamanujanWeil/Ihara/EndgameApproxAxioms.lean`, the `#print axioms` audit.

Build: `cd ~/RamanujanWeil && nice -n 10 lake build RamanujanWeil.Ihara.EndgameApproxAxioms`.

## Headline results

- `deligneBound_of_iharaApprox_all : (∀ (p : ℕ) [Fact p.Prime], IharaApprox p) → RamanujanTau.DeligneBound`.
- `deligneBound_of_iharaApprox_prime (p) [Fact p.Prime] (h : IharaApprox p) : τ(p)² ≤ 4p¹¹`.
  The big étale site and `ℓ ≠ p` are chosen inside the proof, as in `Final.lean`. M4b is
  discharged by `r1StalkCharpolyFibre`.
- `deligne_of_package_approx` is the frozen statement from `scratch/ArithInterfaces.lean`,
  verbatim.
- `IharaApprox` is the frozen definition, verbatim. It uses the repo's `weierstrassSum`.
  `iharaApprox_of_iharaIdentity` is also verbatim (proof: `C = 0`, `k = 0`).
- `coeff_eq_zero_of_growth` is the frozen statement plus a hypothesis `(hR : 0 ≤ R)`. See the deviation below.

## Deviation from the frozen statements

`coeff_eq_zero_of_growth` as frozen is **false** when `R < 0`. Counterexample: `T = {0}`,
`c ≡ 1`, `R = −1`, `C = 0`. For `n ≥ 1` the sum is `0 ≤ 0`, and `R < ‖0‖`, but `c 0 = 1`.
The counterexample is formalized as `coeff_eq_zero_of_growth_frozen_false`. The repo version adds
`(hR : 0 ≤ R)` after `k`. The only use has `R = (√p)^{2e+13} > 0`. Everything else matches the
frozen text exactly, including the binders of `deligne_of_package_approx` and the body of `IharaApprox`.

Additions that are not in the frozen file: `tendsto_cesaro_geom`, `coeff_eq_zero_of_tendsto`,
`tendsto_succ_pow_mul_pow`, `false_of_package_approx`, `deligne_of_package_approx_gen`
(`1 < p`, free `e` with `d ≤ e + 2`, `Type*`), `deligne_of_package_iharaApprox` (the `d = 5`
hand-off with `S = weierstrassSum`), `no_package_approx_of_violation`, `deligneBound_of_iharaApprox_M4b`
and `deligneBound_of_iharaApprox`.

## Proof outline

1. `coeff_eq_zero_of_tendsto` (Cesàro extraction). Suppose `‖u‖ = M > 0` on `U` and
   `g(n) = Σ_U d_u (u/M)ⁿ → 0`. Fix `w`. Then `g(n)(w/M)^{−n} = Σ d_u (u/w)ⁿ → 0`, since the
   multiplier is unimodular. Its Cesàro means also tend to 0 (`Filter.Tendsto.cesaro_smul`). The
   mean of `(u/w)ⁿ` is `1` for `u = w`. For `u ≠ w` it is `O(1/N)`, because the geometric sum is
   bounded by `2/‖u/w − 1‖` (`tendsto_cesaro_geom`). So the means tend to `d_w`, and `d_w = 0`.
2. `coeff_eq_zero_of_growth`. Suppose some `c_z ≠ 0` with `‖z‖ > R`. Let `M` be the largest
   modulus with `c_z ≠ 0`, and pick `R < R' = (R+M)/2 < M`. Then
   `‖Σ c_z (z/M)ⁿ‖ ≤ |C|(n+1)^k (R'/M)ⁿ → 0`. The layers of modulus `< M` tend to 0. So the top
   layer tends to 0, and step 1 kills the coefficient of the maximizer. Contradiction.
3. `false_of_package_approx`. This repeats `false_of_package`, except that `hzero` (exact
   vanishing) is replaced by `Σ_T (c_z − dd_z) zⁿ = S n − main n`, of norm
   `≤ C(n+1)^k ((√p)^{2e+13})ⁿ`. The growth lemma applies at `zw = p^{e+1}β`, because
   `‖zw‖² = p^{2e+2}β² > p^{2e+13} = ((√p)^{2e+13})²`. The net multiplicity of `zw` is −1, and the
   odd-degree weight contradiction from M1 finishes the proof unchanged.
4. `deligne_of_package_approx_gen` and `deligne_of_package_approx`: the real roots of
   `X² − τX + p¹¹` under a violation, exactly as in `deligne_of_package_gen`.
5. `FinalApprox.lean`: `lefschetzPackage_Wp` and `S_eq_pointSum` (M6) give the `Sym¹⁰ R¹` package
   with alternating traces `weierstrassSum p n`. `elim_deligne` hands it to
   `deligne_of_package_iharaApprox`. `d = 5` gives the exponents `3n` and `19n` by `rfl`.
