# M4b: stalks of `R¹` = `H¹` of the fibre curves; `IharaIdentity p ⇒ τ(p)² ≤ 4p¹¹`

Status 2026-11-08. Closes the frozen M4b interface `R1StalkCharpolyFibre` of
`docs/IHARA_POINTS.md`. No `sorry`, `admit`, `native_decide` or `axiom`; **no remaining named
hypothesis**.

| File | Imports | Content |
|---|---|---|
| `RamanujanWeil/Ihara/M4bFibre.lean` | PointsFibre, PointsRealizes, CurveH1Betti, Stacks `Trace.WeilIIAssembly`, `Trace.CompactSupportSchemeIsoTransport`, Weil `Trace.ConnectedComponentsCharpoly` (all prebuilt) | transport lemma, stalk = fibre `H¹`, M4b modulo `H1RankFormula` |
| `RamanujanWeil/Ihara/M4b.lean` | M4bFibre, CurveH1BettiStacks, Assembly | `r1StalkCharpolyFibre`, **`deligneBound_of_ihara`** |
| `RamanujanWeil/Ihara/M4bAxioms.lean` | M4b | `#print axioms` audit |

## Headline statements

```lean
-- standing context: p prime, B : BigEtaleSite.{0}, ℓ prime, the three site-instance families
theorem r1StalkCharpolyFibre (hℓp : ℓ ≠ p) : R1StalkCharpolyFibre p B ℓ
theorem deligneBound_of_ihara (hℓp : ℓ ≠ p) (hI : IharaIdentity p) :
    RamanujanTau.tau p ^ 2 ≤ 4 * (p : ℤ) ^ 11
```

Intermediate (M4bFibre):

```lean
-- any B, finite field k, ℓ ≠ char k; g : X' ⟶ X with B.inclusion.map g an iso, f, f' proper
theorem charpoly_rationalFrobenius_eq_of_isIso (hf : B.inclusion.map g ≫ f = f') (ν) :
    (Weil.rationalFrobenius B X' f' ℓ ν).charpoly = (Weil.rationalFrobenius B X f ℓ ν).charpoly
abbrev κw (y : (Wp p B).1) : Type := (Wp p B).1.residueField y
theorem charpoly_rationalStalkFrobenius_R1_eq (y : closedPoints (Wp p B).1)
    [Fintype (κw p B y.1)] [Fact (ℓ ≠ ringChar (κw p B y.1))] :
    (LAdicSheaf.rationalStalkFrobenius B (Wp p B) ℓ (R1 p B ℓ) y.1 _).charpoly =
      (Weil.rationalFrobenius B (weierstrassScheme (Family.fibreCurve p y.1) B)
        (projectionOf (Family.fibreCurve p y.1)) ℓ 1).charpoly
theorem r1StalkCharpolyFibre_of_h1RankFormula (hS : H1RankFormula.{0}) (hℓp : ℓ ≠ p) :
    R1StalkCharpolyFibre p B ℓ
```

## Proof of the transport (all library pieces existed)

1. **Proper base change with Frobenius**: Stacks
   `LAdicSheaf.higherDirectImageStalkInput_higherDirectImageShriek`, inputs
   `lowerShriekConstructibilityInput B` and `lerayFrobeniusComparison` (exactly as in
   `Trace/WeilIIAssembly.lean`), applied to `g = π`, `jg = jπ`, `fW = toSpecK`, `k̄ = AlgebraicClosure κ(y)`,
   `p = ringChar κ(y)`, `n = (FiniteField.card κ(y) _).choose` (Weil's choices). `R1` is
   definitionally `higherDirectImageShriekFamily B ℓ π jπ constE 1`. Output: the stalk charpoly is
   that of `H¹_c` of the scheme fibre `E_y = E ×_{W_p} Spec κ(y)` (in `B` by the size bound) with
   coefficients `ι⁻¹ℤ_ℓ`, for an unknown compactification `j_w`.
2. **Coefficients and compactification**: Weil's `charpoly_frobenius_inverseImage_constantSystem`
   (`constantSystemToInverseImage : ℤ_ℓ ≅ ι⁻¹ℤ_ℓ`, Tag 0F7I independence) turns this into
   `charpoly (Weil.rationalFrobenius B E_y (fiberToSpecResidueField) ℓ 1)`.
3. **Scheme isomorphism**: `isPullback_fromSpecResidueField` gives
   `isoPullback.inv : E_y ≅ projOf (fibreCurve p y)` over `κ(y)`;
   `charpoly_rationalFrobenius_eq_of_isIso` (Stacks
   `rationalGeometricCompactlySupportedCohomologyIsoOfIsIso_hom_frobenius` with the compactification
   `(ofProper f).restrictOpen g`, Weil's bridge once more for `g⁻¹ℤ_ℓ`, and
   `charpoly_eq_of_comm_iso`) moves the charpoly to `weierstrassScheme (fibreCurve p y) B`.

Then M4a at `E_y/κ(y)` (`charpoly_weierstrassH1'`, `natCard_point_extension_eq_weierstrassH1'`,
`sq_le_four_mul_card_weierstrassH1'` with `realizesWeierstrass_projOf`) gives the three conjuncts,
with `#κ(y) = p^{deg y}` (`Family.natCard_residueField`), `ringChar κ(y) = p`, and
`extensionTraces_of_extension` + `congr_q`. `H1RankFormula` is discharged by `h1RankFormula`
(CurveH1BettiStacks, Tag 0C1Z).

Elaboration notes: `κ(y)` appears in two syntactic forms (`Scheme.residueField` and the unfolded
`IsLocalRing.ResidueField (stalk)`); instance search on the unfolded form times out, so the proof
pins `k := κw p B y.1` explicitly and restates `IsProper (fiberToSpecResidueField)` with target
`Spec (.of κw)`.

## Build and audit

`nice -n 10 lake build RamanujanWeil.Ihara.M4bAxioms`: exit 0 (2026-11-08); M4bFibre 321 s,
M4b 342 s (almost all import loading), no extra Stacks/Weil modules built. All 9 audited names
(`charpoly_rationalFrobenius_eq_of_isIso`, `contains_fiber`, `isElliptic_fibreCurve`,
`charpoly_rationalStalkFrobenius_R1_eq`, `ringChar_residueField_Wp`,
`r1StalkCharpolyFibre_of_h1RankFormula`, `h1RankFormula`, `r1StalkCharpolyFibre`,
`deligneBound_of_ihara`) print `[propext, Classical.choice, Quot.sound]`.

Line counts: M4bFibre 206, M4b 44, M4bAxioms 14.

What remains for an unconditional `τ(p)² ≤ 4p¹¹` from this file: only `IharaIdentity p` (the
frozen M1 point-count identity), plus choosing a `B` with the three site-instance families.
