# RamanujanWeil

Deligne's bound `τ(p)² ≤ 4·p¹¹` for Ramanujan's τ, proved in Lean 4 from the **Weil Riemann hypothesis
formalized by Axiom** ([AxiomMath/Weil](https://github.com/AxiomMath/Weil), pinned at `27cdb20`),
conditional on the Eichler–Shimura–Deligne realization of `Δ` (`TauRealization`).

* `RamanujanWeil.deligneBound_of_realization :
   (∀ p, p.Prime → Nonempty (TauRealization p)) → ∀ p, p.Prime → τ p ^ 2 ≤ 4 * p ^ 11`
* `TauRealization p`: a smooth proper scheme `X/𝔽_p`, a prime `ℓ ≠ p`, and a 2-dimensional
  geometric-Frobenius-stable subspace of `H¹¹(X_𝔽̄_p, ℚ_ℓ)` on which Frobenius has trace `τ(p)`
  (no size condition; the only analytic input is `Weil.satisfiesWeilEstimate`).
* `τ` is a verbatim copy of `RamanujanTau/Basic.lean` from
  [RamanujanLean](https://github.com/tomdif/RamanujanLean), so the conclusion is exactly the
  `DeligneBound` hypothesis used there (e.g. by Hafner's positive-proportion theorem).

Axioms of every headline: `[propext, Classical.choice, Quot.sound]` (`RamanujanWeil/Axioms.lean`).
No `sorry`, no `native_decide`, no new axioms. Details: [docs/WEIL_BRIDGE.md](docs/WEIL_BRIDGE.md).

## Second route: Ihara–Birch (no realization hypothesis)

`RamanujanWeil.Ihara.deligneBound_of_ihara_all :
   (∀ (p : ℕ) [Fact p.Prime], IharaIdentity p) → RamanujanTau.DeligneBound`
(per prime: `deligneBound_of_ihara_prime`). The geometric side is fully formalized: Weil II
(Stacks) applied to `Sym¹⁰R¹f_!ℚ_ℓ` on the moduli of Weierstrass cubics over `𝔽_p`, proper base
change to the fibres, `H¹` of each elliptic fibre (Stacks Tag 0C1Z), and the point bookkeeping.
The **only** remaining hypothesis is `IharaIdentity p`
(`RamanujanWeil/Ihara/IharaStatement.lean`), an elementary identity about finite fields:

  Σ_{c ∈ 𝔽_{pⁿ}⁵, Δ(c) ≠ 0} symTrace₁₀(pⁿ + 1 − #E_c(𝔽_{pⁿ}), pⁿ) = p³ⁿ(pⁿ − 1)(−1 − αⁿ − βⁿ),

with `α, β` the roots of `X² − τ(p)X + p¹¹` (checked numerically, `scripts/scout/`). Proving it is
the arithmetic half (Eichler–Selberg trace formula, class numbers, Deuring) and is not done.
Axioms: `[propext, Classical.choice, Quot.sound]` (`RamanujanWeil/Ihara/FinalAxioms.lean`).
Weaker sufficient hypothesis (`RamanujanWeil/Ihara/FinalApprox.lean`):
`deligneBound_of_iharaApprox_all : (∀ (p : ℕ) [Fact p.Prime], IharaApprox p) → DeligneBound`, where
`IharaApprox p` allows an error `O((n+1)^k·p^{19n/2})` in the identity. With it the supersingular
tuples (`p ∣ a_c`) only need a size bound, proved in `Arith/SupersingularBound.lean`
(`#{c : p ∣ a_c} ≤ p·q⁴`). Route for the remaining arithmetic: `docs/ARITH_ROUTE.md`.
Current frontier (`RamanujanWeil/Ihara/FinalES.lean`):
`deligneBound_of_Deuring : (∀ p [Fact p.Prime], OrdinaryDeuring hurwitz p) → RamanujanTau.DeligneBound`.
**Eichler–Selberg for `S₁₂(SL₂ℤ)` at all `n` is proved unconditionally**
(`Arith/ESAnalytic.lean`, `eichlerSelberg_all`; Popa–Zagier route, Eichler integral + Bol + a
certified numerical non-vanishing of Δ's period polynomial). Also proved: Hurwitz class numbers and
`H(p²N)`, Weierstrass orbit count, supersingular bound, Hasse for all tuples, τ Hecke recurrence.
Exact Deuring is no longer needed (`RamanujanWeil/Ihara/FinalDeuringApprox.lean`,
`docs/ARITH_DEURING_APPROX.md`): `deligneBound_of_DeuringMult_unique` needs only a per-class count
`DeuringMultiplicity` (`N(t) = q³(q−1)·m(t)·H(4q−t²)/2`) plus `m(t) ≤ 1` (Tate uniqueness); the
`_exists` variant takes `m(t) ≥ 1` instead. Kronecker–Hurwitz is proved (`Arith/DeuringApproxKH.lean`).
Open: the per-class lattice count (G1 Jacobian/Abel done, G6 quotients done) and Tate uniqueness
(G7: proved modulo the named finiteness hypothesis `QuotientFiniteness`; `docs/ARITH_DEURING_G7.md`).
Milestone docs: `docs/IHARA_*.md`. Building the Ihara closure needs >6 GB for two Stacks modules
(`ConstantCurveFrobeniusGram`, `Perfect.RelativeDescentAffineDictionary`).

Build: `lake exe cache get && lake build RamanujanWeil RamanujanWeil.Axioms`. Stacks/Weil have no
cache; the import closure is ~20k modules (≈20 h on a 14-core Mac, ~24 GB `.lake`).
