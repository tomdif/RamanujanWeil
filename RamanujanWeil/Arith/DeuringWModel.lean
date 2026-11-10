import RamanujanWeil.Arith.DeuringWModelGenus
import RamanujanWeil.Arith.DeuringDescent
import StacksFrontier.AlgebraicGeometry.Curves.GenusOne.WeierstrassEquation

/-!
# `WeierstrassModel k` for every algebraically closed field `k`

`docs/ARITH_DEURING_WMODEL.md`. A one-dimensional abelian variety `B` over an algebraically
closed field `k` is proper, smooth of relative dimension one (Mathlib `smooth_of_grpObj`,
`isCurve_of_dim_one`, Stacks `smoothOfRelativeDimension_one_of_isCurve`), has `h⁰(𝒪_B) = 1`
(`finrank_structureSheafCohomology_zero`) and genus one (`DeuringWModelGenus.genus_eq_one`), and
has the rational point `η`. Stacks' `GenusOne.exists_weierstrassCurve_iso` (Riemann–Roch on
`𝒪(3η)`) then gives the pointed Weierstrass model.

Consequently `Descent.weierstrassDescent_of_model` holds unconditionally:
`weierstrassDescent : G5.WeierstrassDescent K` for every finite field `K`.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory
open AlgebraicGeometry.ModuliEllipticCurves AlgebraicGeometry.ModuliEllipticCurves.Weierstrass
open scoped CategoryTheory.MonObj

universe u

namespace RamanujanWeil.Arith.Deuring.WModel

open RamanujanWeil.Arith.Deuring.Geom Stacks.Groupoids

/-- **`WeierstrassModel k` for every algebraically closed field `k`.** -/
theorem weierstrassModel_of_isAlgClosed (k : Type u) [Field k] [IsAlgClosed k] :
    Descent.WeierstrassModel k := by
  intro B _ _ hB
  have : IsCurve k B.hom := isCurve_of_dim_one hB
  have : GrpObj (Over.mk B.hom) := inferInstanceAs (GrpObj B)
  have : Smooth B.hom := smooth_of_grpObj (K := k) B.hom
  have : SmoothOfRelativeDimension 1 B.hom := smoothOfRelativeDimension_one_of_isCurve k B.hom
  have hp : η[B].left ≫ B.hom = 𝟙 _ := Over.w η[B]
  obtain ⟨C, hC, e, he, hz⟩ := GenusOne.exists_weierstrassCurve_iso B.hom
    (finrank_structureSheafCohomology_zero B) (genus_eq_one B hB) η[B].left hp
  refine ⟨C, hC, e.symm, ?_, ?_⟩
  · rw [Iso.symm_hom, ← he, Iso.inv_hom_id_assoc]
  · rw [Iso.symm_hom, ← hz, Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- **`WeierstrassModel K̄`** for the algebraic closure of any field. -/
theorem weierstrassModel (K : Type u) [Field K] :
    Descent.WeierstrassModel (AlgebraicClosure K) :=
  weierstrassModel_of_isAlgClosed (AlgebraicClosure K)

/-- **`G5.WeierstrassDescent K`, unconditionally**, for every finite field `K`. -/
theorem weierstrassDescent (K : Type u) [Field K] [Fintype K] : G5.WeierstrassDescent K :=
  Descent.weierstrassDescent_of_model (weierstrassModel K)

end RamanujanWeil.Arith.Deuring.WModel
