import RamanujanWeil.Arith.DeuringG1Jac
import RamanujanWeil.Arith.DeuringG1RR

/-!
# A3-ord, G1.1 for the concrete Jacobian: `aj_W : E_W ≅ J_W`

`docs/ARITH_DEURING_G1_2.md`. For an elliptic Weierstrass curve `W / 𝔽_q` and a Jacobian site
`S : JacSite W`, the Abel–Jacobi map `S.aj : E_W ⟶ J_W`, `P ↦ 𝒪(P − O)`, is an isomorphism
over `Spec K̄` (`JacSite.isIso_aj`, from `Abel.isIso_abelJacobi_of_genus_eq_one`), and it sends
the zero section `O` to the zero class (`Abel.jacobianHomAddEquiv_basePt_comp_abelJacobi`,
for any pointed genus-one curve).
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u

noncomputable section

namespace RamanujanWeil.Arith.Deuring.Geom

namespace Abel

open Stacks.PicardFunctor

variable {k : Type u} [Field k] (B : BigFppfSite.{u}) {X : Scheme.{u}} (hX : B.Contains X)
  (hk : B.Contains (Spec (.of k))) (f : B.obj hX ⟶ B.obj hk)
  [IsCurve k (B.inclusion.map f)] [GeometricallyIrreducible (B.inclusion.map f)]
  [Smooth (B.inclusion.map f)] [IsProper (B.inclusion.map f)]
  [IsProjectiveVariety k (B.inclusion.map f)]
  (σ : Spec (.of k) ⟶ X) (hσ : σ ≫ B.inclusion.map f = 𝟙 (Spec (.of k)))
  [(picardFunctor B hX hk f).IsRepresentable] (hg : genus (B.inclusion.map f) = 1)

theorem constPt_baseObj : constPt B hX hk f σ hσ (baseObj B hk) = basePt B hX hk f σ hσ := by
  rw [constPt]
  have : toBaseObj B hk (baseObj B hk) = 𝟙 _ := Over.OverMorphism.ext rfl
  rw [this, Category.id_comp]

include hg in
/-- **`aj(c₀) = 0`**: the point of `Pic⁰` of the base point composed with `aj` is zero. -/
theorem jacobianHomAddEquiv_basePt_comp_abelJacobi :
    ((jacobianHomAddEquiv B hX hk f σ hσ (baseObj B hk)
        (Additive.ofMul ((Over.post (X := B.obj hk) B.inclusion).map (basePt B hX hk f σ hσ) ≫
          abelJacobi B hX hk f σ hσ))) : (picardFunctor B hX hk f).obj (op (baseObj B hk))) = 0 := by
  rw [jacobianHomAddEquiv_comp_abelJacobi B hX hk f σ hσ hg, constClass,
    constPt_baseObj, sub_self]

end Abel

namespace Jac.JacSite

open AlgebraicGeometry.ModuliEllipticCurves.Weierstrass RamanujanWeil.Ihara Stacks.PicardFunctor

variable {k : Type u} [Field k] [Fintype k] {W : WeierstrassCurve k} [W.IsElliptic]
  (S : JacSite W)

/-- `E_W` has genus one, in the site's notation. -/
theorem genus_f : genus (S.B.inclusion.map S.f) = 1 := genus_projOf_baseChange W _

/-- **G1.1 for `W`: the Abel–Jacobi map `aj_W : E_W ⟶ J_W` is an isomorphism.** -/
instance isIso_aj : IsIso S.aj :=
  Abel.isIso_abelJacobi_of_genus_eq_one S.B S.hX S.hk S.f (zeroPt W) S.o_comp S.genus_f

/-- **The Abel–Jacobi isomorphism `E_W ≅ J_W`** over `Spec K̄`. -/
def ajIso : curveOver S.B S.hX S.hk S.f ≅ S.J := asIso S.aj

theorem ajIso_hom : S.ajIso.hom = S.aj := rfl

/-- `aj_W(O) = 0` on `Pic⁰`. -/
theorem jacobianHomAddEquiv_zero_comp_aj :
    ((jacobianHomAddEquiv S.B S.hX S.hk S.f (zeroPt W) S.o_comp (baseObj S.B S.hk)
        (Additive.ofMul ((Over.post (X := S.B.obj S.hk) S.B.inclusion).map
          (Abel.basePt S.B S.hX S.hk S.f (zeroPt W) S.o_comp) ≫ S.aj))) :
        (picardFunctor S.B S.hX S.hk S.f).obj (op (baseObj S.B S.hk))) = 0 :=
  Abel.jacobianHomAddEquiv_basePt_comp_abelJacobi S.B S.hX S.hk S.f (zeroPt W) S.o_comp S.genus_f

end Jac.JacSite

end RamanujanWeil.Arith.Deuring.Geom
