# A3-ord, G7: `GlueAmpleDescent` proved (2026-11-10)

This closes item 4 of `ARITH_DEURING_G7_LEVELDESCENT.md` (§2, the named Prop `GlueAmpleDescent`).
New files only:

| File | Imports | Content |
|---|---|---|
| `Arith/DeuringG7AmpleDescent.lean` | LevelDescent, Stacks `AmpleFiniteSurjective.Basic`, finite locally free API | `glueAmpleDescent`, the seams and Deligne with ample descent discharged |
| `Arith/DeuringG7AmpleDescentAxioms.lean` | | audit |

```lean
theorem glueAmpleDescent : GlueAmpleDescent.{u}
theorem isAmple_iff_isAmple_pullback_glue (G : Glue Γ) (M : G.B.left.Modules) [...] :
    Stacks.Ample.IsAmple G.B.left M ↔
      Stacks.Ample.IsAmple A.left ((Scheme.Modules.pullback G.q.left).obj M)
theorem thetaLevelDescentGood_of_levelSectionDescent' (hD : LevelSectionDescent K) :
    ThetaLevelDescentGood K
theorem thetaLevelDescentΨ_of_levelSectionDescentΨ' (hD : LevelSectionDescentΨ K) :
    ThetaLevelDescentΨ K
theorem deligneBound_of_levelDescent' (h : LevelDescentSplitAll') : RamanujanTau.DeligneBound
```

## 0. Finding: Stacks 0B5V *is* in the pinned Stacks

The level-descent doc said 0B5V was absent. It is present, both directions, at this pin:
`Stacks.AmpleFiniteSurjective.isAmple_iff_isAmple_modulePullback`
(`StacksFrontier/AlgebraicGeometry/AmpleFiniteSurjective/Basic.lean`, tagged `@[stacks 0B5V]`):

> `R` Noetherian, `p : X ⟶ Spec R` proper, `f : Y ⟶ X` finite and surjective, `L` invertible on
> `X` (`Stacks.Ample.IsInvertibleModule`): `IsAmple X L ↔ IsAmple Y (f^* L)`.

* The converse there is the source's cohomological proof: 0B5U, dévissage 01YM, 01YO, 01YP, the
  projection formula 01E8 and 089W.
* The predicate is the same `Stacks.Ample.IsAmple` that `GlueAmpleDescent` uses.
* The pullback `modulePullback f.toLRSHom.toShHom` is `Scheme.Modules.pullback f` by `rfl`.

So no norm construction and no trace/#Γ splitting is needed. The 0.5–1k line estimate goes down to
about 100 lines of glue.

## 1. The proof (`DeuringG7AmpleDescent`)

Apply 0B5V with `R = k`, `p = B.hom`, `f = q.left`. Its hypotheses come from:

* **`IsFinite q.left`** (`isFinite_glue_q`). `Glue.rank` says `q.left` is finite locally free of
  rank `#Γ`. By `IsFiniteLocallyFreeOfRank.isFiniteLocallyFree` and
  `isFiniteLocallyFree_iff_isFinite_flat_locallyOfFinitePresentation`, it is finite, flat and of
  locally finite presentation.
* **`IsProper B.hom`** (`isProper_glue_B`). It comes from `Glue.ab` through
  `IsAbelianVariety → IsProperVariety → IsProper`.
* **`Surjective q.left`** is `Glue.surj`.
* **`IsNoetherianRing k`**: `k` is a field.

`IsAlgClosed k` and the group structures are not used. The statement holds for any finite
surjective `q` to a proper `k`-scheme.

## 2. Effect on the chain

* `GlueAmpleDescent` is now a theorem, so the ample-descent input drops out of
  `thetaLevelDescentGood_of_levelSectionDescent` and `thetaLevelDescentΨ_of_levelSectionDescentΨ`.
* **`LevelDescentSplitAll'`** is `LevelDescentSplitAll` without its `GlueAmpleDescent.{0}`
  conjunct:
  `∀ 𝔽_q, DGeomGapsAll ∧ LevelSectionDescent ∧ PrincipalFiniteness`.
  `levelDescentSplitAll_of'` gives the original split, and `deligneBound_of_levelDescent'` gives
  Deligne.

**What remains** on this branch is unchanged apart from item 4: `LevelSectionDescent` (items 1, 2
and 5: linearization, module descent and the function-field/module bridge), `DGeomGapsAll`, and
`PrincipalFiniteness`.

## 3. Audit

`lake build RamanujanWeil.Arith.DeuringG7AmpleDescentAxioms`: every declaration depends only on
`[propext, Classical.choice, Quot.sound]`. This includes the Stacks inputs
`isAmple_of_isAmple_modulePullback` and `isAmple_iff_isAmple_modulePullback`.
