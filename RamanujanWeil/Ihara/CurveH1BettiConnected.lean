import RamanujanWeil.Ihara.CurveH1Weierstrass
import StacksFrontier.AlgebraicGeometry.Curves.GenusOne.Basic
import StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.BaseChange
import StacksFrontier.AlgebraicGeometry.Stacks.WeierstrassFamilyFibres

/-!
# Gap 3 of M4a: the plane cubic is geometrically connected (and a curve over `k̄`)

For a proper scheme `f : X ⟶ Spec k` and a field extension `K/k`, the dimensions of the
cohomology groups of the structure sheaf do not change under base change to `K`
(`finrank_structureSheafCohomology_baseChange`, flat base change, Stacks' `FieldExtension`).
Hence `H⁰(X, 𝒪_X) = k` gives `H⁰(X_K, 𝒪) = K`, so `X_K` is connected
(`connectedSpace_baseChange_of_finrank_zero`, via `GenusOne.connectedSpace`: a nontrivial
idempotent of `Γ(X_K, 𝒪)` would split `X_K`), and, if `f` is smooth of relative dimension one,
`X_K` is a curve over `K` (`isCurve_baseChange_of_finrank_zero`).

For a Weierstrass curve `W` over a field, `H⁰(projOf W, 𝒪) = k`
(`finrank_structureSheafCohomology_projectionOf_zero`), so `E_k̄ = projOf W ×_k k̄` is connected:
this is the instance `connectedSpace_weierstrass_geometric` used by `charpoly_weierstrassH1`.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
  AlgebraicGeometry.ModuliEllipticCurves.Weierstrass Stacks.Frobenius

universe u

namespace RamanujanWeil.Ihara

set_option backward.isDefEq.respectTransparency.types false in
/-- Smoothness of relative dimension `n` is stable under base change (instance form of Mathlib's
`smoothOfRelativeDimension_isStableUnderBaseChange`). -/
instance smoothOfRelativeDimension_pullback_snd {X Y S : Scheme.{u}} (n : ℕ) (f : X ⟶ S)
    (g : Y ⟶ S) [SmoothOfRelativeDimension n f] : SmoothOfRelativeDimension n (pullback.snd f g) :=
  haveI := smoothOfRelativeDimension_isStableUnderBaseChange (n := n)
  MorphismProperty.pullback_snd (P := @SmoothOfRelativeDimension n) f g inferInstance

section General

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f]
  (K : Type u) [Field K] [Algebra k K]

/-- **Flat base change along a field extension** for the cohomology of the structure sheaf of a
proper scheme: `dim_K Hⁿ(X_K, 𝒪) = dim_k Hⁿ(X, 𝒪)`. -/
theorem finrank_structureSheafCohomology_baseChange (n : ℕ) :
    Module.finrank K (structureSheafCohomology (pullback.snd f (specAlgebraMap k K)) n) =
      Module.finrank k (structureSheafCohomology f n) := by
  have h := IsPullback.of_hasPullback f (specAlgebraMap k K)
  calc
    Module.finrank K (structureSheafCohomology (pullback.snd f (specAlgebraMap k K)) n)
        = Module.finrank K (cohomologyOverField K (pullback.snd f (specAlgebraMap k K))
            (SheafOfModules.unit (pullback f (specAlgebraMap k K)).ringCatSheaf) n) :=
      (structureSheafCohomologyIsoCohomologyOverField K _ n).toLinearEquiv.finrank_eq
    _ = Module.finrank K (cohomologyOverField K (pullback.snd f (specAlgebraMap k K))
          ((Scheme.Modules.pullback (pullback.fst f (specAlgebraMap k K))).obj
            (SheafOfModules.unit X.ringCatSheaf)) n) :=
      (finrank_cohomologyOverField_eq_of_iso K _ (Scheme.Modules.pullbackUnitIso _) n).symm
    _ = Module.finrank k (cohomologyOverField k f (SheafOfModules.unit X.ringCatSheaf) n) :=
      finrank_cohomologyOverField_baseChange_field k K _ _ f h _ n
    _ = Module.finrank k (structureSheafCohomology f n) :=
      (structureSheafCohomologyIsoCohomologyOverField k f n).toLinearEquiv.finrank_eq.symm

/-- **Geometric connectedness from `H⁰(X, 𝒪_X) = k`**: `X_K` is connected for every extension
`K/k`. -/
theorem connectedSpace_baseChange_of_finrank_zero
    (h0 : Module.finrank k (structureSheafCohomology f 0) = 1) :
    ConnectedSpace ↥(pullback f (specAlgebraMap k K)) :=
  GenusOne.connectedSpace (pullback.snd f (specAlgebraMap k K))
    ((finrank_structureSheafCohomology_baseChange f K 0).trans h0)

/-- **`X_K` is a curve over `K`** when `f` is smooth of relative dimension one and
`H⁰(X, 𝒪_X) = k`. -/
theorem isCurve_baseChange_of_finrank_zero [SmoothOfRelativeDimension 1 f]
    (h0 : Module.finrank k (structureSheafCohomology f 0) = 1) :
    IsCurve K (pullback.snd f (specAlgebraMap k K)) :=
  GenusOne.isCurve (pullback.snd f (specAlgebraMap k K))
    ((finrank_structureSheafCohomology_baseChange f K 0).trans h0)

/-- The genus is invariant under extension of the ground field. -/
theorem genus_pullback_snd :
    genus (pullback.snd f (specAlgebraMap k K)) = genus f :=
  genus_baseChange k K _ _ f (IsPullback.of_hasPullback f (specAlgebraMap k K))

end General

section Weierstrass

variable {k : Type u} [Field k] (W : WeierstrassCurve k)

/-- **Gap 3 of M4a**: the plane cubic of any Weierstrass equation over a field `k` stays connected
over every extension `K/k` (no hypothesis on `Δ`). -/
theorem connectedSpace_projOf_baseChange (K : Type u) [Field K] [Algebra k K] :
    ConnectedSpace ↥(pullback (Over.mk (projectionOf W)).hom (specAlgebraMap k K)) :=
  connectedSpace_baseChange_of_finrank_zero (projectionOf W) K
    (finrank_structureSheafCohomology_projectionOf_zero W)

/-- `E_k̄` is connected: the instance assumed by `charpoly_weierstrassH1`. -/
instance connectedSpace_weierstrass_geometric :
    ConnectedSpace ↥(pullback (Over.mk (projectionOf W)).hom
      (specAlgebraMap k (AlgebraicClosure k))) :=
  connectedSpace_projOf_baseChange W (AlgebraicClosure k)

/-- `E_K` has genus one for every extension `K/k`. -/
theorem genus_projOf_baseChange (K : Type u) [Field K] [Algebra k K] :
    genus (pullback.snd (Over.mk (projectionOf W)).hom (specAlgebraMap k K)) = 1 :=
  (genus_pullback_snd (projectionOf W) K).trans (genus_projectionOf W)

/-- `E_K` is a curve over `K` for `W` elliptic. -/
theorem isCurve_projOf_baseChange [W.IsElliptic] (K : Type u) [Field K] [Algebra k K] :
    IsCurve K (pullback.snd (Over.mk (projectionOf W)).hom (specAlgebraMap k K)) :=
  isCurve_baseChange_of_finrank_zero (projectionOf W) K
    (finrank_structureSheafCohomology_projectionOf_zero W)

end Weierstrass

end RamanujanWeil.Ihara
