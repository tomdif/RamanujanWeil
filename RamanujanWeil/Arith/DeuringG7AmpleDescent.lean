import RamanujanWeil.Arith.DeuringG7LevelDescent
import StacksFrontier.AlgebraicGeometry.AmpleFiniteSurjective.Basic
import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.FiniteFlat
import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteLocallyFreeOfRank

/-!
# A3-ord, G7: `GlueAmpleDescent` proved (Stacks 0B5V for the G6 quotient)

`docs/ARITH_DEURING_G7_AMPLE.md`. The named Prop `GlueAmpleDescent` of
`DeuringG7LevelDescent` (ampleness descends along a G6 quotient `q : A → B = A/Γ`) is proved
outright.

The pinned Stacks *does* contain Stacks Tag 0B5V in both directions, as
`Stacks.AmpleFiniteSurjective.isAmple_iff_isAmple_modulePullback`
(`StacksFrontier/AlgebraicGeometry/AmpleFiniteSurjective/Basic.lean`): for `f : Y ⟶ X` finite and
surjective, `X` proper over a Noetherian ring `R`, an invertible `L` on `X` is ample iff `f^* L`
is. Its converse is the source's cohomological argument (0B5U + dévissage 01YM + projection
formula), so neither the norm nor a trace splitting is needed. What is supplied here:

* `q.left` is finite: `Glue.rank` (finite locally free of rank `#Γ`) gives finite + flat + l.f.p.
  (`isFiniteLocallyFree_iff_isFinite_flat_locallyOfFinitePresentation`);
* `B → Spec k` is proper: `IsAbelianVariety` extends `IsProperVariety`, which extends `IsProper`;
* `k` is a field, hence a Noetherian ring;
* `Scheme.Modules.pullback f = modulePullback f.toLRSHom.toShHom` holds by `rfl`.

## Main results

* `isFinite_glue_q`: the G6 quotient map is finite.
* `isAmple_of_isAmple_pullback_glue`: **ampleness descends along `q`**.
* `glueAmpleDescent`: **`GlueAmpleDescent`**, with no hypothesis.
* `thetaLevelDescentGood_of_levelSectionDescent'`, `thetaLevelDescentΨ_of_levelSectionDescentΨ'`:
  the descent seams with the ample-descent input discharged.
* `LevelDescentSplitAll'` and `deligneBound_of_levelDescent'`: the Deligne split without
  `GlueAmpleDescent`; `levelDescentSplitAll_of'` shows it implies the original split.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory
  CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

universe u

noncomputable section

namespace RamanujanWeil.Arith.Deuring.Geom.G7.AmpleDescent

open Stacks.Groupoids RamanujanWeil.Arith.Deuring.Geom.G7
  RamanujanWeil.Arith.Deuring.Geom.G7.DGeom RamanujanWeil.Arith.Deuring.Geom.G7.LevelDescent

section

variable {k : Type u} [Field k] {A : Over (Spec (.of k))} [GrpObj A] {Γ : Subgroup (Pt A)}

/-- **The G6 quotient map is finite**: it is finite locally free of rank `#Γ`. -/
theorem isFinite_glue_q (G : Glue Γ) : IsFinite G.q.left := by
  have := G.rank
  exact ((Stacks.Morphisms.isFiniteLocallyFree_iff_isFinite_flat_locallyOfFinitePresentation
    G.q.left).mp
      (Stacks.Morphisms.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree G.q.left (Nat.card Γ))).1

/-- The quotient `B` is proper over `k`. -/
theorem isProper_glue_B (G : Glue Γ) : IsProper G.B.hom := by
  have := G.ab
  infer_instance

/-- **Ampleness descends along the G6 quotient** (Stacks 0B5V, `⟸`). -/
theorem isAmple_of_isAmple_pullback_glue (G : Glue Γ) (M : G.B.left.Modules)
    [Stacks.Ample.IsInvertibleModule G.B.left M]
    [Stacks.Ample.IsInvertibleModule A.left ((Scheme.Modules.pullback G.q.left).obj M)]
    (h : Stacks.Ample.IsAmple A.left ((Scheme.Modules.pullback G.q.left).obj M)) :
    Stacks.Ample.IsAmple G.B.left M := by
  have := isFinite_glue_q G
  have := isProper_glue_B G
  have := G.surj
  exact Stacks.AmpleFiniteSurjective.isAmple_of_isAmple_modulePullback G.q.left M k G.B.hom h

/-- Both directions at the G6 quotient: `M` is ample iff `q^* M` is. -/
theorem isAmple_iff_isAmple_pullback_glue (G : Glue Γ) (M : G.B.left.Modules)
    [Stacks.Ample.IsInvertibleModule G.B.left M]
    [Stacks.Ample.IsInvertibleModule A.left ((Scheme.Modules.pullback G.q.left).obj M)] :
    Stacks.Ample.IsAmple G.B.left M ↔
      Stacks.Ample.IsAmple A.left ((Scheme.Modules.pullback G.q.left).obj M) := by
  have := isFinite_glue_q G
  exact ⟨fun h => Stacks.AmpleFiniteSurjective.isAmple_modulePullback_of_isFinite G.q.left M h,
    isAmple_of_isAmple_pullback_glue G M⟩

end

/-- **`GlueAmpleDescent`, proved.** -/
theorem glueAmpleDescent : GlueAmpleDescent.{u} :=
  fun _ _ _ _ _ _ _ G M _ _ h => isAmple_of_isAmple_pullback_glue G M h

variable {K : Type u} [Field K] [Fintype K]

/-- `ThetaLevelDescentGood` from module descent alone. -/
theorem thetaLevelDescentGood_of_levelSectionDescent' (hD : LevelSectionDescent K) :
    ThetaLevelDescentGood K :=
  thetaLevelDescentGood_of_levelSectionDescent hD glueAmpleDescent

/-- `ThetaLevelDescentΨ` from the Frobenius-compatible module descent alone. -/
theorem thetaLevelDescentΨ_of_levelSectionDescentΨ' (hD : LevelSectionDescentΨ K) :
    ThetaLevelDescentΨ K :=
  thetaLevelDescentΨ_of_levelSectionDescentΨ hD glueAmpleDescent

/-- The level-descent split without the (now proved) ample-descent input. -/
def LevelDescentSplitAll' : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (n : ℕ), 1 ≤ n →
    letI : Fintype (GaloisField p n) := Fintype.ofFinite _
    DGeomGapsAll (GaloisField p n) ∧ LevelSectionDescent (GaloisField p n) ∧
      PrincipalFiniteness (GaloisField p n)

/-- The reduced split gives the original one. -/
theorem levelDescentSplitAll_of' (h : LevelDescentSplitAll') : LevelDescentSplitAll :=
  ⟨glueAmpleDescent, h⟩

/-- **Deligne's bound from D-geom inputs, module descent and Θ + J + C** (ample descent is
proved). -/
theorem deligneBound_of_levelDescent' (h : LevelDescentSplitAll') : RamanujanTau.DeligneBound :=
  deligneBound_of_levelDescent (levelDescentSplitAll_of' h)

end RamanujanWeil.Arith.Deuring.Geom.G7.AmpleDescent
