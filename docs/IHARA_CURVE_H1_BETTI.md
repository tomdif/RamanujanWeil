# M4a gaps 1 and 3: geometric connectedness and `dim H¹ = 2` for the Weierstrass cubic

Status 2026-11-08. Follow-up to `docs/IHARA_CURVE_H1.md` (M4a). Gap 2 (`RealizesWeierstrass`) is
not touched here.

| File | Imports | Content |
|---|---|---|
| `RamanujanWeil/Ihara/CurveH1BettiConnected.lean` | `CurveH1Weierstrass`, Stacks `GenusOne.Basic`, `GenusCurve.BaseChange`, `WeierstrassFamilyFibres` (all prebuilt) | gap 3, unconditional; base change of `Hⁿ(𝒪)`, genus, curve structure along `k → K` |
| `RamanujanWeil/Ihara/CurveH1Betti.lean` | `CurveH1BettiConnected` | gap 1 reduced to the named Stacks statement `H1RankFormula`; `charpoly_weierstrassH1'` |
| `RamanujanWeil/Ihara/CurveH1BettiAxioms.lean` | `CurveH1Betti` | `#print axioms` audit (15 declarations) |

No `sorry`, `admit`, `native_decide` or `axiom`. No existing file was edited.

## Gap 3: geometric connectedness (DONE, unconditional)

```lean
-- any proper f : X ⟶ Spec k, any field extension K/k
theorem finrank_structureSheafCohomology_baseChange (n : ℕ) :
    finrank K (structureSheafCohomology (pullback.snd f (specAlgebraMap k K)) n) =
      finrank k (structureSheafCohomology f n)
theorem connectedSpace_baseChange_of_finrank_zero (h0 : finrank k (structureSheafCohomology f 0) = 1) :
    ConnectedSpace ↥(pullback f (specAlgebraMap k K))
theorem isCurve_baseChange_of_finrank_zero [SmoothOfRelativeDimension 1 f] (h0 : …) :
    IsCurve K (pullback.snd f (specAlgebraMap k K))
theorem genus_pullback_snd : genus (pullback.snd f (specAlgebraMap k K)) = genus f
instance smoothOfRelativeDimension_pullback_snd (n) (f g) [SmoothOfRelativeDimension n f] :
    SmoothOfRelativeDimension n (pullback.snd f g)

-- W any Weierstrass curve over a field (no Δ hypothesis for connectedness)
theorem connectedSpace_projOf_baseChange (K) :
    ConnectedSpace ↥(pullback (Over.mk (projectionOf W)).hom (specAlgebraMap k K))
instance connectedSpace_weierstrass_geometric :
    ConnectedSpace ↥(pullback (Over.mk (projectionOf W)).hom (specAlgebraMap k (AlgebraicClosure k)))
theorem genus_projOf_baseChange (K) : genus (pullback.snd (Over.mk (projectionOf W)).hom …) = 1
theorem isCurve_projOf_baseChange [W.IsElliptic] (K) : IsCurve K (pullback.snd … )
```

The instance is literally the hypothesis form of `charpoly_weierstrassH1`
(`[ConnectedSpace ↥(pullback (Over.mk (projectionOf W)).hom (specAlgebraMap k (AlgebraicClosure k)))]`),
so that hypothesis is now discharged by instance search.

Proof: flat base change along a field extension (`finrank_cohomologyOverField_baseChange_field`,
Stacks `FlatBaseChangeCohomology/FieldExtension`) moves `H⁰(E, 𝒪) = k`
(`finrank_structureSheafCohomology_projectionOf_zero`) to `H⁰(E_K, 𝒪) = K`; then
`GenusOne.connectedSpace` (a nontrivial idempotent of `Γ(E_K, 𝒪) = K` would split `E_K`;
Stacks `ProperGeomConnected`) gives connectedness, and `GenusOne.isCurve` (smooth + connected ⇒
integral, `Stacks.Chow.isIntegral_of_connectedSpace_of_smooth`; dimension one from smoothness)
gives `IsCurve K E_K`. ~115 lines; the M4a estimate was 200–500.

## Gap 1: `HasFirstBettiTwo` (reduced to one named Stacks statement)

```lean
/-- Statement of Stacks' `LAdicSheaf.finrank_rationalGeometricCompactlySupportedCohomology_constant_one`
(Tag 0C1Z, Trace/ConstantCurveH1Trace.lean), every hypothesis of that theorem as a binder. -/
def H1RankFormula : Prop :=
  ∀ (B : BigEtaleSite.{u}) (X : B.Scheme) (ℓ : ℕ) [IsNoetherian X.1] [Fact ℓ.Prime]
    {k : Type u} [Field k] [Fintype k] (f : X.1 ⟶ Spec (.of k)) [IsProper f]
    (kbar : Type u) [Field kbar] [Algebra k kbar] (p q : ℕ) [Fact p.Prime] [CharP k p]
    (_hcard : Fintype.card k = p ^ q) [IsAlgClosed kbar]
    [IsCurve kbar (pullback.snd (Over.mk f).hom (specAlgebraMap k kbar))]
    [Smooth (pullback.snd …)] [IsProper (pullback.snd …)],
    IsUnit (ℓ : kbar) →
      finrank ℚ_[ℓ] (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f
          (CompactificationOf.ofProper f) kbar (LAdicSheaf.constantSystem B X ℓ) ((1 : ℕ) : ℤ)) =
        2 * genus (pullback.snd (Over.mk f).hom (specAlgebraMap k kbar))

theorem isUnit_natCast_of_ne_ringChar (K) (ℓ) [Fact ℓ.Prime] [Fact (ℓ ≠ ringChar k)]
    (hp : (ringChar k).Prime) : IsUnit (ℓ : K)
-- X : B.Scheme, f proper + smooth of rel. dim 1 over F_q, H⁰(X, 𝒪) = k
theorem finrank_rationalCohomology_one_eq_two_mul_genus (hS : H1RankFormula) (h0) :
    finrank ℚ_[ℓ] (Weil.rationalCohomology B X f ℓ 1) = 2 * genus f
theorem hasFirstBettiTwo_of_genus_eq_one (hS) (h0) (hg : genus f = 1) : HasFirstBettiTwo X f ℓ
-- W elliptic over F_q
theorem hasFirstBettiTwo_weierstrass (hS : H1RankFormula) :
    HasFirstBettiTwo (weierstrassScheme W B) (projectionOf W) ℓ
theorem charpoly_weierstrassH1' (hS : H1RankFormula)
    (hW : RealizesWeierstrass (weierstrassScheme W B) (projectionOf W) W) :
    (Weil.rationalFrobenius B (weierstrassScheme W B) (projectionOf W) ℓ 1).charpoly =
      X ^ 2 − C (q + 1 − Nat.card W.toAffine.Point) * X + C q
theorem natCard_point_extension_eq_weierstrassH1' (hS) (hW) (n) (hn : 1 ≤ n) : … -- #W(k_n), tr F₁ⁿ
theorem sq_le_four_mul_card_weierstrassH1' (hS) (hW) : (q + 1 − #W(k))² ≤ 4q
```

So for the Weierstrass cubic, M4a now needs only `[W.IsElliptic]`, `RealizesWeierstrass` (gap 2)
and `H1RankFormula`, which is not a mathematical gap: it is the exact statement of a Stacks theorem
that exists, unmodified, in `.lake/packages/Stacks`, and whose proof is one term:

```lean
-- RamanujanWeil/Ihara/CurveH1BettiStacks.lean (NOT created: does not build under the 6 GB cap)
import RamanujanWeil.Ihara.CurveH1Betti
import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.ConstantCurveH1Trace
theorem h1RankFormula : H1RankFormula.{u} :=
  fun B X ℓ _ _ _ _ _ f _ kbar _ _ p q _ _ hcard _ _ _ _ hℓ =>
    Stacks.EtaleCohomology.LAdicSheaf.finrank_rationalGeometricCompactlySupportedCohomology_constant_one
      B X ℓ f kbar p q hcard hℓ
theorem charpoly_weierstrassH1'' (hW : RealizesWeierstrass …) : … :=
  charpoly_weierstrassH1' W B ℓ h1RankFormula hW
```

(ready as `scratchpad/betti/CurveH1BettiStacks.lean.pending`; not compiled, so the binder
pattern of the `fun` may need adjusting — the statement itself was elaborated against the same
Stacks definitions, and `CurveH1Betti` checks that it specializes to `Weil.rationalCohomology`
with `kbar = AlgebraicClosure k`, `p = ringChar k`, `q = cardExp k`.)

How gap 1 is closed from it (all compiled): `Weil.rationalCohomology B X f ℓ 1` unfolds to
Stacks' `rationalGeometricCompactlySupportedCohomology … (AlgebraicClosure k) … ((1:ℕ):ℤ)`;
the hypotheses `IsCurve k̄ X_k̄` and `Smooth X_k̄` come from gap 3's `isCurve_baseChange_of_finrank_zero`,
`IsNoetherian X` from `Weil.isNoetherian_of_isProper`, `#k = pᵉ` from M4a's `card_eq_ringChar_pow`,
`ℓ ∈ k̄ˣ` from `isUnit_natCast_of_ne_ringChar`, and `genus X_k̄ = genus X = 1` from
`genus_baseChange` and `genus_projectionOf`. The M4a estimate was 300–600 lines; it took ~100.

## The build (why `H1RankFormula` is still a hypothesis)

`ConstantCurveH1Trace`'s closure had **436 unbuilt** Stacks modules. Built with ONE
`nice -n 10 lake build StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.ConstantCurveH1Trace`,
detached, with a watchdog (`scratchpad/betti/watchdog2.py`): throttles the lake's `lean` children to
3–5 running (SIGSTOP/SIGCONT, oldest first), to 1 if `memory_pressure` free < 25 %, to 0 if < 12 %,
and SIGKILLs any of them whose physical footprint (`top -stats mem`, = `footprint`) exceeds 6 GB.

* Wall time **58.5 min** (10:54 → 11:53 AST); **405 of 436** modules built; free memory stayed ≥ 46 %.
* **Two modules exceed the 6 GB cap and were killed**, blocking 29 dependents (incl. the target):
  * `EtaleCohomology.Trace.ConstantCurveFrobeniusGram` (118 lines; direct import of
    `ConstantCurveH1Trace`): killed at 6.7 GB in the build, and again at 6.5 GB solo with
    `LEAN_NUM_THREADS=1`. The footprint is dirty heap (`footprint`: 4.7 GB "IOAccelerator" dirty
    + page tables), not mmapped `.olean`s (clean). Bisection with scratch copies: imports ≈ 1 GB;
    statement only ≈ 1.6 GB; `have hex := fun n => exists_constantLevelCohomology_transition …`
    ≈ 2.6 GB; with `choose ψ hψ using …` instead ≈ 5 GB; plus the `let`s ≈ 5.6 GB; plus the
    `hsq` statement > 6 GB. `ConstantCurveH1Trace.towerFacts_constant_one` has the identical
    `choose`/`hsq` pattern, so it very likely exceeds 6 GB as well.
  * `Perfect.RelativeDescentAffineDictionary` (183 lines, derived-category naturality): killed at
    6.3 GB. On the path `ConstantCurveH1Trace → Picard.TorsionSmoothProjectiveCurve.Unconditional →
    Picard.Jacobian.PicardSchemeOfCurve → Perfect.TensorFinitelyPresentedPerfect → … →
    RelativeDescentAffineDictionaryNatural → RelativeDescentAffineDictionary` (Pic(X_k̄)[ℓ] ≅
    (ℤ/ℓ)^{2g} needs the Picard scheme), so it cannot be avoided by re-proving the trace file.

**To finish** (needs a cap above 6 GB; peak unknown, est. 8–12 GB, one `lean` at a time, ~10–20
min for the 31 remaining modules): `scratchpad/betti/finish_build.sh` (`MAXRUN=1`,
`LIMIT_MB=14336`), then create `CurveH1BettiStacks.lean` from the pending file and build it. That
yields `charpoly_weierstrassH1''` assuming only `[W.IsElliptic]` and `RealizesWeierstrass`.
Alternative under the 6 GB cap: re-prove `towerFacts_constant_one` without `choose` (≈2.5 GB
saving measured) in a new file — but `RelativeDescentAffineDictionary` would still block
`Unconditional`, so this alone does not suffice.

## Build and audit

`nice -n 10 lake build RamanujanWeil.Ihara.CurveH1BettiAxioms` (exit 0, 585 s wall incl. `CurveH1Betti`, 2026-11-08). `CurveH1BettiConnected`
built by lake in 183 s; `CurveH1Betti` compiles in ~4–5 min (`lake env lean`, exit 0), almost all
imports. Every audited declaration reports `[propext, Classical.choice, Quot.sound]`.

Line counts: Connected 115, Betti 160, Axioms 21.
