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

Build: `lake exe cache get && lake build RamanujanWeil RamanujanWeil.Axioms`. Stacks/Weil have no
cache; the import closure is ~20k modules (≈20 h on a 14-core Mac, ~24 GB `.lake`).
