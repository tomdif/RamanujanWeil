# M5: `F = Sym¹⁰ R¹` on `W_p` (frozen interface)

Status 2026-11-08. Milestone M5 of `docs/REALIZATION_PLAN.md` §5.
Conditional on **one** named hypothesis, `R1StalkCharpoly` (the frozen M4 interface, below).
No `sorry`, `admit`, `native_decide` or `axiom`.

## Files (namespace `RamanujanWeil.Ihara`)

| File | Imports | Content |
|---|---|---|
| `RamanujanWeil/Ihara/SymCore.lean` | Endgame (for `symTrace`) + Mathlib | `symMat n : M₂(R) → M_{n+1}(R)` (matrix of `Symⁿ` on binary forms), `symMat_mul`, `symMat_one`, `symHom`, `continuous_symMat`, `trace_symMat_ten`, `symTraceR`, `Int.cast_symTrace` |
| `RamanujanWeil/Ihara/SymWeights.lean` | SymCore + Stacks `CharpolyTracePowers` (Newton) | Cayley–Hamilton traces, `powSum`, `charpoly_symMat_ten` (eigenvalues `αᵇβ¹⁰⁻ᵇ`), `norm_sq_eq_of_sq_le` (Hasse ⟹ `‖α‖² = q`) |
| `RamanujanWeil/Ihara/SymSheaf.lean` | SymWeights + FamilyR1 + FamilyConnected + Stacks (`LisseRepresentation`, `PointwiseMixedSheaf`, `IotaRealizableSheaf`, `WeilIICurveSheafBound`, `RepresentationSheafTracePow`) | `symRep`, `R1Rep`, `symR1`, `R1StalkCharpoly`, the four headline theorems |
| `RamanujanWeil/Ihara/SymAxioms.lean` | SymSheaf | `#print axioms` audit |

No Stacks modules had to be built (all used ones were prebuilt).

## Construction

* `symMat n g` is `E(g)ᵀ`, where `E(g)_{c,b}` is the coefficient of `X₀ᶜX₁ⁿ⁻ᶜ` in
  `(g₀₀X₀+g₀₁X₁)ᵇ(g₁₀X₀+g₁₁X₁)ⁿ⁻ᵇ` (explicit binomial sum `symEntry`). Multiplicativity comes
  from `σ_{gh} = σ_h ∘ σ_g` for the substitution `σ_g` on `MvPolynomial (Fin 2) R`, compared on the
  monomial basis. `trace_symMat_ten` (`tr Sym¹⁰ g = symTrace 10 (tr g) (det g)`) is a `norm_num`
  plus `ring` identity.
* `basePt p B := geometricPointAt _ (arbitrary point)`. `W_p` is connected (`FamilyConnected`).
* `R1Rep p B ℓ` is a structure holding the output of Stacks'
  `LAdicSheaf.exists_representationSheaf_isogeny_of_isLisse`: `r`, continuous
  `ρ : π₁(W_p, x̄) →* GL (Fin r) ℚ_[ℓ]`, `φ : R1 ⟶ ℱ_ρ`, `ψ : ℱ_ρ ⟶ R1`, and `N` with
  `φ≫ψ = ℓᴺ•𝟙` and `ψ≫φ = ℓᴺ•𝟙`. `nonempty_r1Rep (hℓp : ℓ ≠ p)` holds via `isLisse_R1`.
* `symRep ρ := (Units.map (symHom 10)).comp ρ` (continuous: `continuous_symRep`).
* `symSheafOf ρ hρ` is `ℱ_{Sym¹⁰ρ}` if `r = 2` (pattern match). Otherwise it is the trivial
  rank-1 sheaf, so the definition stays total. That branch is never reached under the
  hypothesis (`R1Rep.rank_eq_two`).
* **`symR1 p B ℓ : LAdicSheaf.{0,1} B (Wp p B) ℓ`** is `symSheafOf` of the chosen `R1Rep` when one
  exists. Otherwise (only possible for `ℓ = p`) it is a junk lisse sheaf. `symR1_eq hℓp` unfolds
  it.

## Frozen M4 hypothesis (to be discharged by M4b)

```lean
def R1StalkCharpoly (p) [Fact p.Prime] (B : BigEtaleSite.{0}) (ℓ) [Fact ℓ.Prime] [site instances] : Prop :=
  ∀ y : closedPoints (Wp p B).1, ∃ a : ℤ,
    a ^ 2 ≤ 4 * (p : ℤ) ^ residueDegree (toSpecK p B) y.1 ∧
    (LAdicSheaf.rationalStalkFrobenius B (Wp p B) ℓ (R1 p B ℓ) y.1
        (finite_residueField (toSpecK p B) y.1 y.2)).charpoly =
      Polynomial.X ^ 2 - Polynomial.C (a : ℚ_[ℓ]) * Polynomial.X +
        Polynomial.C ((p : ℚ_[ℓ]) ^ residueDegree (toSpecK p B) y.1)
```

This is the natural output of M4a (`CurveH1.lean`). `charpoly_weierstrassH1` gives the charpoly
`X² − aX + q` with `a = q + 1 − #W(κ(y))`, and `sq_le_four_mul_card_of_weierstrass` gives Hasse,
`a² ≤ 4q`. Both hold for the fibre curve over `κ(y)` with `q = #κ(y) = p^{deg y}`. M4b
transports both to the stalk of `R¹` (see `IHARA_FAMILY.md`, "Interface for M4b"). The Hasse
conjunct is what makes `F` pure: `a ∈ ℝ` and `a² ≤ 4q` give `|α| = |β| = q^{1/2}`
(`norm_sq_eq_of_sq_le`). No separate Weil-RH input is needed in M5.

## Headline theorems (`SymSheaf.lean`)

Context: `(p) [Fact p.Prime] (B : BigEtaleSite.{0}) (ℓ) [Fact ℓ.Prime]` with the three M2/M3
site-instance families.

```lean
theorem isLisse_symR1 : (symR1 p B ℓ).IsLisse                                   -- unconditional

theorem mixed_symR1 (hℓp : ℓ ≠ p) (H : R1StalkCharpoly p B ℓ) (ι : ℚ_[ℓ] →+* ℂ) :
    LAdicSheaf.IsPointwiseMixedOfWeightLE B (Wp p B) ℓ (toSpecK p B) (symR1 p B ℓ) (p ^ 1) ι 10

theorem realizable_symR1 (hℓp : ℓ ≠ p) (H : R1StalkCharpoly p B ℓ) (ι : ℚ_[ℓ] →+* ℂ) :
    LAdicSheaf.IsIotaRealizable B (Wp p B) ℓ (toSpecK p B) (symR1 p B ℓ) ι   -- witness F' = F

theorem stalkTrace_symR1 (hℓp : ℓ ≠ p) (H : R1StalkCharpoly p B ℓ)
    (y : closedPoints (Wp p B).1) (m : ℕ) (t : ℤ)
    (ht : LinearMap.trace ℚ_[ℓ] _ (rationalStalkFrobenius … (R1 p B ℓ) y.1 … ^ m) = (t : ℚ_[ℓ])) :
    LinearMap.trace ℚ_[ℓ] _ (rationalStalkFrobenius … (symR1 p B ℓ) y.1 … ^ m) =
      ((symTrace 10 t ((p : ℤ) ^ (residueDegree (toSpecK p B) y.1 * m)) : ℤ) : ℚ_[ℓ])

theorem exists_stalkTrace_symR1 (hℓp : ℓ ≠ p) (H : R1StalkCharpoly p B ℓ) (y) :
    ∃ a : ℤ, a ^ 2 ≤ 4 * p ^ deg y ∧ charpoly(π_y | R¹) = X² − aX + p^{deg y} ∧
      ∀ m, tr(π_yᵐ | R¹) = powSum a (p ^ deg y) m ∧
           tr(π_yᵐ | F) = symTrace 10 (powSum a (p ^ deg y) m) (p ^ (deg y * m))
```

`powSum a q` is `s₀ = 2`, `s₁ = a`, `s_{m+2} = a s_{m+1} − q s_m` (= `αᵐ + βᵐ`). It agrees with
`frobPowerSum` of `CurveH1Core` by the same recurrence. M5 does not import that file.

## Use in M6

```lean
lefschetzPackage_Wp p B ℓ hℓp ι (symR1 p B ℓ) 10 (isLisse_symR1 p B ℓ)
  (mixed_symR1 p B ℓ hℓp H ι) (realizable_symR1 p B ℓ hℓp H ι)
```

(`FamilyPackage.lean`) gives a `LefschetzPackage ℚ_[ℓ] ι (p^1) 10 5 (pointSum B (Wp p B) ℓ (toSpecK p B) (symR1 p B ℓ))`.
For each closed point `x` and `m = n / deg x`, M6 rewrites the summand of `pointSum` with
`exists_stalkTrace_symR1`, giving `symTrace 10 (s_m(a_x, q_x)) (p^{deg x · m})`. Here
`a_x = q_x + 1 − #E_x(κ(x))`, which comes from M4b.

## Gaps

There is no gap inside M5. The single named hypothesis is `R1StalkCharpoly` (M4b). Estimate for
M4b: 1–2k lines. It covers fibre identification, constant-sheaf pullback and the residue-field
data listed in `IHARA_FAMILY.md`, plus transport of `sq_le_four_mul_card_of_weierstrass`.

## Build and audit

Build with `nice -n 10 lake build RamanujanWeil.Ihara.SymAxioms`. SymSheaf takes about 2–6 min,
almost all of it import loading. The `R1Rep` structure needs `maxHeartbeats 1000000`, because
the field types are heavy to whnf.

`lake build RamanujanWeil.Ihara.SymAxioms` finished with exit 0 on 2026-11-08 and built no
extra Stacks modules. SymSheaf took 328 s. All 14 audited names print
`[propext, Classical.choice, Quot.sound]`: `symMat_mul`, `continuous_symMat`,
`trace_symMat_ten`, `charpoly_symMat_ten`, `norm_sq_eq_of_sq_le`, `continuous_symRep`,
`nonempty_r1Rep`, `symR1`, `R1Rep.charpoly_frob`, `isLisse_symR1`, `exists_stalkTrace_symR1`,
`stalkTrace_symR1`, `mixed_symR1`, `realizable_symR1`.

Line counts: SymCore 231, SymWeights 143, SymSheaf 344, SymAxioms 18 (736 in total).
