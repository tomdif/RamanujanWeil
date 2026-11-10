import RamanujanWeil.Arith.DeuringG7Genus2Exist
import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.GorensteinCurveRiemannRoch
import StacksFrontier.AlgebraicGeometry.Duality.GorensteinSchemes.Regular
import StacksFrontier.AlgebraicGeometry.Variety.Smooth.Regular
import StacksFrontier.AlgebraicGeometry.ReflexiveHull.UnitDual
import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.Rank
import StacksFrontier.Topology.Dimension.Equidimensional

/-!
# A3-ord, G7-C: the canonical bundle of a genus-2 curve (`Genus2CanonicalExistence`, proved)

`docs/ARITH_DEURING_G7_GENUS2.md` §4.1. Let `Y / K` be smooth, proper, geometrically irreducible,
a curve, of genus 2, and `ω = H^{-1}(s^×𝒪_{Spec K})` the dualizing sheaf of Stacks 0BS2. Then

* `ω` is invertible and finite locally free of rank 1: `Y` is regular
  (`isRegular_of_smooth_over_field`), hence Gorenstein (`isGorenstein_of_isRegular`),
  irreducible hence equidimensional, of dimension 1, so Stacks 0BS6 (1)
  (`isInvertible_dualizingSheafOverField_of_isGorenstein`) applies;
* `deg ω = −2 χ(𝒪) = −2 (1 − g) = 2`: Stacks 0BS6 (2)
  (`curveDegree_dualizingSheafOverField_eq_neg_two_mul_of_isGorenstein`) and
  `χ(𝒪) = 1 − g` (`eulerCharacteristic_unit_eq_one_sub_genus`);
* `h⁰(ω) = h¹(𝒪) = g = 2`: the duality of dimensions at `ℰ = 𝒪`
  (`finrank_cohomologyOverField_zero_dualTensorDualizingSheafOverField_eq_one`), read through
  `𝒪^∨ ⊗ ω ≅ 𝒪 ⊗ ω ≅ ω` (`unitDualIso`, `tensorProductLeftUnitor`).

Hence **`genus2CanonicalExistence : Genus2CanonicalExistence K`** for every field `K`.
-/

universe u

open AlgebraicGeometry CategoryTheory

namespace RamanujanWeil.Arith.Deuring.Geom.G7.Genus2.Exist

variable {K : Type u} [Field K] {Y : Scheme.{u}} (s : Y ⟶ Spec (.of K)) [IsCurve K s]
  [Smooth s] [IsProper s] [GeometricallyIrreducible s]

theorem g2_isGorenstein {K : Type u} [Field K] {Y : Scheme.{u}} (s : Y ⟶ Spec (.of K))
    [Smooth s] : IsGorenstein Y :=
  isGorenstein_of_isRegular Y (isRegular_of_smooth_over_field s)

theorem g2_equidimensional {K : Type u} [Field K] {Y : Scheme.{u}} (s : Y ⟶ Spec (.of K))
    [IsCurve K s] : TopologicalSpace.Equidimensional Y :=
  have : IsIntegral Y := (IsCurve.toIsVariety (k := K) (f := s)).toIsIntegral
  TopologicalSpace.Equidimensional.of_preirreducibleSpace Y

theorem g2_topologicalKrullDim_eq_one {K : Type u} [Field K] {Y : Scheme.{u}}
    (s : Y ⟶ Spec (.of K)) [IsCurve K s] : topologicalKrullDim Y = 1 :=
  IsCurve.topologicalKrullDim_eq_one (k := K) (f := s)

omit [GeometricallyIrreducible s] in
/-- **Stacks 0BS6 (1)** for a smooth curve: `ω` is invertible, of rank one. -/
theorem dualizing_isInvertible_and_rank :
    SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2
        (Stacks.Duality.dualizingSheafOverField s) ∧
      SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
        (Stacks.Duality.dualizingSheafOverField s) 1 :=
  Stacks.Duality.isInvertible_dualizingSheafOverField_of_isGorenstein s (g2_isGorenstein s)
    (g2_equidimensional s) (g2_topologicalKrullDim_eq_one s)

/-- `𝒪^∨ ⊗ ω ≅ ω`. -/
noncomputable def dualUnitTensorDualizingIso :
    (((Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨Y.sheaf.obj, Presheaf.isSheaf_of_isSheaf_comp _ (Y.sheaf.obj)
            (forget₂ CommRingCat RingCat) (Y.ringCatSheaf.property)⟩).obj
        ((Stacks.SheafOfModules.dualSheaf Y.sheaf.obj Y.ringCatSheaf.property
          (SheafOfModules.unit Y.ringCatSheaf)))).obj
      ((Stacks.Duality.dualizingSheafOverField s))) ≅
      Stacks.Duality.dualizingSheafOverField s :=
  Stacks.SheafOfModules.Invertible.tensorProductIso Y.presheaf Y.ringCatSheaf.property
      (Stacks.AlgebraicGeometry.ReflexiveModules.unitDualIso Y)
      (Iso.refl (Stacks.Duality.dualizingSheafOverField s)) ≪≫
    Stacks.SheafOfModules.Invertible.tensorProductLeftUnitor Y.presheaf Y.ringCatSheaf.property
      (Stacks.Duality.dualizingSheafOverField s)

omit [Smooth s] [GeometricallyIrreducible s] in
/-- `h⁰(ω) = g`. -/
theorem finrank_dualizing_zero :
    Module.finrank K (cohomologyOverField K s (Stacks.Duality.dualizingSheafOverField s) 0) =
      genus s := by
  have : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (SheafOfModules.unit Y.ringCatSheaf) 1 := SheafOfModules.isFiniteLocallyFreeOfRank_unit Y
  rw [← finrank_cohomologyOverField_eq_of_iso K s (dualUnitTensorDualizingIso s) 0,
    finrank_cohomologyOverField_zero_dualTensorDualizingSheafOverField_eq_one s (hdim s)
      (SheafOfModules.unit Y.ringCatSheaf) 1,
    finrank_cohomologyOverField_one_unit_eq_genus]

/-- `deg ω = 2g − 2`. -/
theorem invertibleCurveDegree_dualizing
    [SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2
      (Stacks.Duality.dualizingSheafOverField s)] :
    invertibleCurveDegree K s (hdim s) (Stacks.Duality.dualizingSheafOverField s) =
      2 * (genus s : ℤ) - 2 := by
  have hr := (dualizing_isInvertible_and_rank s).2
  have := isIso_globalSections s
  have h2 := curveDegree_dualizingSheafOverField_eq_neg_two_mul_of_isGorenstein s
    (g2_isGorenstein s) (g2_equidimensional s) (g2_topologicalKrullDim_eq_one s)
  have h1 := eulerCharacteristic_unit_eq_one_sub_genus K s (hdim s)
  rw [invertibleCurveDegree_eq_curveDegree]
  calc _ = _ := h2
    _ = -2 * (1 - (genus s : ℤ)) := congrArg (fun z => -2 * z) h1
    _ = _ := by ring

/-- **The canonical bundle of a genus-2 curve** (Stacks 0BS6 (1)(2)(3) + 0BY8): an invertible
module of degree 2 with `h⁰ = 2`, over any field. -/
theorem genus2CanonicalExistence : Genus2CanonicalExistence K := by
  intro Y s _ _ _ _ hg
  obtain ⟨hinv, -⟩ := dualizing_isInvertible_and_rank s
  refine ⟨Stacks.Duality.dualizingSheafOverField s, hinv, ?_, ?_⟩
  · rw [invertibleCurveDegree_dualizing s, hg]
    norm_num
  · rw [finrank_dualizing_zero s, hg]

/-- **`Genus2ModelExistence` from the canonical pencil alone.** The canonical-bundle input is now
proved (`genus2CanonicalExistence`); the one remaining named Prop is
`Genus2PencilFunctionField K`. -/
theorem genus2ModelExistence_of_pencil (hP : Genus2PencilFunctionField K) :
    Genus2ModelExistence K :=
  genus2ModelExistence_of_canonical_of_pencil genus2CanonicalExistence hP

end RamanujanWeil.Arith.Deuring.Geom.G7.Genus2.Exist
