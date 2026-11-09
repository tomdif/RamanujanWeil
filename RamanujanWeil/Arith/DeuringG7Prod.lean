import RamanujanWeil.Arith.DeuringG6ConstRank
import StacksFrontier.AlgebraicGeometry.Cube.GeometricallyIntegralProduct

/-!
# A3-ord, G7: the product `A × B` of abelian varieties, and its points

For abelian varieties `A`, `B` over a field `k`, the cartesian product `A ⊗ B` in
`Over (Spec k)` (fibre product over `Spec k`) is an abelian variety (`isAbelianVariety_tensor`),
with the product group structure (Mathlib `GrpObj.tensorObj`). Its `T`-points are pairs of
`T`-points (`pointsMulEquiv`), compatibly with the group law.

This is the object `E × E'` on which Tate's argument (`DeuringG7Tate`) takes quotients.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory
  CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

universe u

namespace RamanujanWeil.Arith.Deuring.Geom.G7

variable {k : Type u} [Field k]

/-- **The product of two abelian varieties is an abelian variety.** -/
theorem isAbelianVariety_tensor (A B : Over (Spec (.of k))) [GrpObj A] [GrpObj B]
    [IsAbelianVariety k A] [IsAbelianVariety k B] : IsAbelianVariety k (A ⊗ B) := by
  have hhom : (A ⊗ B).hom = pullback.fst A.hom B.hom ≫ A.hom := rfl
  have hGI : GeometricallyIntegral (A ⊗ B).hom := by
    rw [hhom]; infer_instance
  have : IsProper (A ⊗ B).hom := by rw [hhom]; infer_instance
  have : GeometricallyReduced (A ⊗ B).hom := inferInstance
  have : IsIntegral (A ⊗ B).left := by
    exact hGI.geometrically_isIntegral (𝟙 _) (𝟙 _) (A ⊗ B).hom
      (IsPullback.of_horiz_isIso ⟨by simp⟩)
  have : ConnectedSpace (A ⊗ B).left := inferInstance
  exact isAbelianVariety_of_isProper_of_connectedSpace_of_geometricallyReduced k (A ⊗ B)

end RamanujanWeil.Arith.Deuring.Geom.G7
