# M1: Ihara endgame (`deligne_of_package`), proved

Status (2026-11-08): **proved, sorry-free**, with standard axioms only.

Files:
- `RamanujanWeil/Ihara/Endgame.lean` (418 lines). Namespace `RamanujanWeil.Ihara`.
  Imports Mathlib and `RamanujanWeil.Tau` only, not Weil.
- `RamanujanWeil/Ihara/EndgameAxioms.lean`, the `#print axioms` audit.

Build: `cd ~/RamanujanWeil && nice -n 10 lake build RamanujanWeil.Ihara.Endgame RamanujanWeil.Ihara.EndgameAxioms`.
The build exits with status 0 and no warnings, in about 9 s for the file.
Every audited declaration depends on `[propext, Classical.choice, Quot.sound]`.
The exception is `tauPowerSum_two`, which depends only on `[propext]`.

## Frozen statement

`RamanujanWeil.Ihara.deligne_of_package` is copied character for character from
`scratch/ProbeInterfaces.lean` (`RamanujanWeil.Plan.deligne_of_package`), including the `hd : 2 ≤ d`
binder, which the proof does not use. The definitions `symTrace` and `tauPowerSum` are also verbatim copies.
`wc`, `traceOfFrob` and `IharaIdentity` were not copied, because M1 does not use them.

## Variants that weaken the hypotheses

- `deligne_of_package'` is the frozen statement without `hd`. It holds for every `d`.
- `deligne_of_package_gen` replaces `[Fact p.Prime]` with `1 < p`. It takes the exponent `e` in
  `S n = p^(e n)(pⁿ−1)(−1−s_n)` as a free parameter, and needs only `d ≤ e + 2`. Universes are generalized to `Type*`.
- `false_of_package` is the core lemma. Given real `α, β` with `α+β = τ`, `αβ = p¹¹` and
  `β² > p¹¹`, no package can exist.
- `no_package_of_violation` is the contrapositive sanity form.

## Proof outline (plan §3)

1. `trace_pow_restrict_maxGenEigenspace` and `trace_pow_eq_sum_maxGenEigenspace`: over `ℂ`,
   `tr(fⁿ) = Σ_μ dim(maxGenEigenspace μ)·μⁿ`. The proof uses the internal direct sum of generalized
   eigenspaces (`iSup_maxGenEigenspace_eq_top`, `LinearMap.trace_eq_sum_trace_restrict'`) and
   `trace_comp_eq_mul_of_commute_of_isNilpotent`, which applies because `f|−μ` is nilpotent.
2. `exists_trace_pow_decomp`: base change along `ι` (`ι.toAlgebra`, `trace_baseChange`,
   `baseChange_pow`, `charpoly_baseChange`). It gives finite data `(s, m)` with `ι tr(fⁿ) = Σ m μ μⁿ`.
   Every `μ` with `m μ ≠ 0` is a root of `charpoly(f).map ι`.
3. `coeff_eq_zero_of_sum_pow_eq_zero`: if `Σ_{z∈T} c_z zⁿ = 0` for all `n ≥ 1`, then `c_z = 0` for `z ≠ 0`.
   The proof applies Dedekind independence of characters (`linearIndependent_monoidHom`) to
   `powersHom ℂ z : Multiplicative ℕ →* ℂ`. Multiplying by `z` shifts the range to `n ≥ 0`.
4. `tauPowerSum_eq`: `s_n = αⁿ + βⁿ` by the recurrence.
5. Endgame. Suppose `τ² > 4p¹¹`. Take the real roots `(τ ± √(τ²−4p¹¹))/2` and let `β` be the root of
   larger absolute value, so `β² > p¹¹ > α²`. With `Q = pᵉ`, the right side is
   `−(pQ)ⁿ + Qⁿ − (pQα)ⁿ − (pQβ)ⁿ + (Qα)ⁿ + (Qβ)ⁿ`. Comparing squares shows that `w = pQβ` differs
   from the other five bases. By uniqueness, `w` has net multiplicity
   `Σ_i (−1)^i m_i(w) = −1`, so `m_i(w) ≠ 0` for some odd `i ≤ 2d−1`.
   Then `‖w‖² ≤ p^(10+i) ≤ p^(2e+13)`. But `‖w‖² = p^(2e+2)β² > p^(2e+13)`, a contradiction.
