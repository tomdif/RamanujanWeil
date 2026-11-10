import StacksFrontier.AlgebraicGeometry.Curves.LargeDegreeVanishingField
import StacksFrontier.AlgebraicGeometry.AmpleDegreeCriterion.CurveInputs
import StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.RiemannRoch
import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.ProperGlobalSections
import StacksFrontier.RingTheory.Smooth.GeometricallyReducedFibres

/-!
# A3-ord, G7-C: Riemann–Roch on a genus-2 curve for the powers of a degree-2 bundle

`docs/ARITH_DEURING_G7_GENUS2.md` §3. Let `Y / K` be a smooth proper geometrically irreducible
curve of genus 2 and `L` an invertible module of degree 2 (the canonical bundle is the case of
interest). Then

* `h⁰(L) − h¹(L) = 1` (`finrank_zero_sub_finrank_one_eq_one`);
* `h⁰(L^{⊗n}) = 2n − 1` for `n ≥ 2` (**`finrank_tensorPower_eq`**): Riemann–Roch
  (`finrank_sub_finrank_eq_invertibleCurveDegree_add_genus`), `deg L^{⊗n} = 2n`
  (`invertibleCurveDegree_tensorPower_eq_mul_of_isCurve`), and `H¹ = 0` in degree `≥ 2g − 1 = 3`
  (Stacks 0B90 over an arbitrary field, `isZero_cohomologyOverField_one_of_geometricallyIntegral`).

These are the dimensions `dim V₃ = 5`, `dim V₆ = 11` of `PencilData`.
-/

universe u

open CategoryTheory Limits AlgebraicGeometry
open Stacks.SheafOfModules.Invertible (tensorPower tensorPower_isInvertible)

namespace RamanujanWeil.Arith.Deuring.Geom.G7.Genus2.Exist

variable {K : Type u} [Field K] {Y : Scheme.{u}} (s : Y ⟶ Spec (.of K)) [IsCurve K s]
  [Smooth s] [IsProper s] [GeometricallyIrreducible s]

omit [IsCurve K s] [IsProper s] in
theorem geometricallyIntegral : GeometricallyIntegral s :=
  have : GeometricallyReduced s := geometricallyReduced_of_smooth s
  GeometricallyIntegral.of_geometricallyReduced_of_geometricallyIrreducible s

omit [IsCurve K s] in
theorem isIso_globalSections : IsIso ((Scheme.ΓSpecIso (.of K)).inv ≫ s.appTop) :=
  have := geometricallyIntegral s
  isIso_globalSections_of_geometricallyIntegral K s

omit [IsCurve K s] [Smooth s] [IsProper s] [GeometricallyIrreducible s] in
theorem hdim [IsCurve K s] : topologicalKrullDim Y ≤ 1 :=
  (IsCurve.topologicalKrullDim_eq_one (k := K) (f := s)).le

/-- **Riemann–Roch on a genus-2 curve.** `h⁰(L) − h¹(L) = deg L − 1`. -/
theorem finrank_sub_finrank_eq (hg : genus s = 2) (L : Y.Modules)
    [SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 L] :
    (Module.finrank K (cohomologyOverField K s L 0) : ℤ) -
        (Module.finrank K (cohomologyOverField K s L 1) : ℤ) =
      invertibleCurveDegree K s (hdim s) L - 1 := by
  have := isIso_globalSections s
  rw [finrank_sub_finrank_eq_invertibleCurveDegree_add_genus K s (hdim s) L, hg]
  push_cast
  ring

/-- **`h⁰(L^{⊗n}) = 2n − 1`** for `deg L = 2` and `n ≥ 2` on a genus-2 curve. -/
theorem finrank_tensorPower_eq (hg : genus s = 2) (L : Y.Modules)
    [SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 L]
    (hL : invertibleCurveDegree K s (hdim s) L = 2) (n : ℕ) (hn : 2 ≤ n) :
    (Module.finrank K (cohomologyOverField K s
      (tensorPower Y.toRingedSpace.presheaf (structureSheafRing Y.toRingedSpace).property L n)
        0) : ℤ) = 2 * n - 1 := by
  have := geometricallyIntegral s
  have hinv := tensorPower_isInvertible Y.toRingedSpace.presheaf
    (structureSheafRing Y.toRingedSpace).property L n
  have hdeg := invertibleCurveDegree_tensorPower_eq_mul_of_isCurve K s (hdim s) L n
  rw [hL] at hdeg
  have hz := isZero_cohomologyOverField_one_of_geometricallyIntegral K s _ hinv (by
    rw [hg]
    refine le_of_le_of_eq ?_ hdeg.symm
    push_cast
    omega)
  have hrr := finrank_sub_finrank_eq s hg (tensorPower Y.toRingedSpace.presheaf
    (structureSheafRing Y.toRingedSpace).property L n)
  have : Subsingleton (cohomologyOverField K s (tensorPower Y.toRingedSpace.presheaf
      (structureSheafRing Y.toRingedSpace).property L n) 1) :=
    (ModuleCat.subsingleton_of_isZero hz)
  rw [Module.finrank_zero_of_subsingleton (M := cohomologyOverField K s
    (tensorPower Y.toRingedSpace.presheaf (structureSheafRing Y.toRingedSpace).property L n) 1),
    hdeg] at hrr
  linear_combination hrr

end RamanujanWeil.Arith.Deuring.Geom.G7.Genus2.Exist
