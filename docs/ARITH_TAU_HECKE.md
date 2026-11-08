# ARITH: the Hecke recurrence for τ (unconditional, axiom-clean)

**Statement** (`RamanujanWeil/Arith/TauHecke.lean`, namespace `RamanujanWeil.ArithPlan`):

```lean
def TauHeckeRecurrence (p : ℕ) : Prop :=
  ∀ r : ℕ, 1 ≤ r → RamanujanTau.tau (p ^ (r + 1)) =
    RamanujanTau.tau p * RamanujanTau.tau (p ^ r) - (p : ℤ) ^ 11 * RamanujanTau.tau (p ^ (r - 1))

theorem tauHeckeRecurrence (p : ℕ) (hp : p.Prime) : TauHeckeRecurrence p
```

`RamanujanTau.tau` is the list-based definition in `RamanujanWeil/Tau.lean`.
Also proved: `tau_master` (`τ(p)τ(n) = τ(pn) + p¹¹[p∣n]τ(n/p)`, every prime `p`, every `n`).

**Axioms** (`RamanujanWeil/Arith/TauHeckeAxioms.lean`): `tauHeckeRecurrence`, `tau_master`,
`qExpansion_discriminant_coeff`, `qExpansion_hecke` each depend on
`[propext, Classical.choice, Quot.sound]`. No sorry / native_decide / axiom.

## Route

1. **Hecke operator** (`TauHeckeCore`, `TauHeckeOperator`):
   `T_p f(z) = p^{k−1} f(pz) + p⁻¹ Σ_{j<p} f((z+j)/p)` is `T`- and `S`-invariant (involution
   `j ↦ −j⁻¹ mod p`), holomorphic, zero at `i∞`, so it is a ℂ-linear endomorphism `heckeLin p`
   of `CuspForm 𝒮ℒ k`. A root-of-unity sum gives the q-expansion action
   `(T_p f)_m = f_{pm} + p^{k−1}[p ∣ m] f_{m/p}` (`qExpansion_hecke`).
2. **Bridge** (`TauHeckeBridge`): `(qExpansion 1 Δ).coeff n = tau n`. Formal half: list
   operations of `Tau.lean` = power-series ring operations, truncations agree mod `X^{d+1}`, so
   `tau n = [qⁿ] q(∏_{k<N}(1−q^{k+1}))²⁴` for `N ≥ n`. Analytic half: Mathlib's
   `discriminant_cuspFunction_eqOn` + locally uniform convergence of polynomial partial products
   + Weierstrass on iterated derivatives at 0.
3. **Eigenform** (`TauHecke`): Mathlib's `CuspForm.exists_smul_discriminant_of_weight_eq_twelve`
   (dim S₁₂ = 1) gives `T_p Δ = c • Δ`; coefficient 1 pins `c = τ(p)`; coefficient `n` gives the
   master identity; `n = p^r` gives the recurrence.

Mathlib 16edf57 has no Hecke operators; it does provide Δ = η²⁴ as a `CuspForm 𝒮ℒ 12`,
`discriminant_cuspFunction_eqOn`, dim S₁₂ = 1, the q-expansion API (`hasSum_qExpansion`,
`qExpansion_coeff_unique`, `qExpansion_smul`) and `multipliableLocallyUniformlyOn_one_sub_pow`.

## What was ported from ~/RamanujanTau (v4.30 → v4.34.0-rc2)

| new file | source | changes |
|---|---|---|
| `TauHeckeCore.lean` (155) | `HeckeCore.lean` | namespace + narrowed imports only |
| `TauHeckeOperator.lean` (225) | `HeckeForm.lean` + first half of `HeckeQExp.lean` | two `denom` proofs (`SpecialLinearGroup.map` no longer simp-unfolds; now `change … ; push_cast`), `heckeH_zero` final step, `hasSum_hecke` final `convert` → `HasSum.congr_fun`, `CuspForm.add_apply` → `add_apply` |
| `TauHeckeBridge.lean` (264) | `TauBridge.lean` + `DiscriminantQExpansion.lean` | replaced `qfacInf`/`FourSquares.π`/`MockTheta5.Bailey.qfac` (closure ~100 modules) by a local finite `qfac` + stabilization lemma; uses Mathlib's `discriminant_cuspFunction_eqOn` instead of the source `DiscriminantBridge` |
| `TauHecke.lean` (79) | `HeckeEigenform`, `HeckeOperator` (`HeckeData`), second half of `HeckeQExp`, `HeckeTheory` | collapsed the `HeckeData`/`TauHeckeMaster` class interface into one direct proof |
| `TauHeckeAxioms.lean` (9) | — | `#print axioms` |

Total: **732 lines** (vs. ~17k-line / 112-module import closure of `HeckeQExp` in the source).
Imports: Mathlib modules + `RamanujanWeil.Tau` only. Files are not added to `RamanujanWeil.lean`
(no existing files edited); build with `lake build RamanujanWeil.Arith.TauHeckeAxioms`.
Only remaining warnings: deprecation of `if_pos`/`if_neg`.
