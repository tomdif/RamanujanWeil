import RamanujanWeil.Arith.DeuringG1Abel
import StacksFrontier.AlgebraicGeometry.Picard.AbelMapFibreEuler
import StacksFrontier.AlgebraicGeometry.TwoAffineCech.FibreDims
import StacksFrontier.AlgebraicGeometry.CurveDegreeTensor.Devissage
import StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.BaseChange
import StacksFrontier.AlgebraicGeometry.EulerCharTruncation.Basic
import StacksFrontier.AlgebraicGeometry.PicardScheme.Jacobian.RiemannRochEffective
import StacksFrontier.AlgebraicGeometry.Curves.LinearSeries
import StacksFrontier.AlgebraicGeometry.Curves.LargeDegreeVanishing
import StacksFrontier.AlgebraicGeometry.Chow.ZeroSchemePullback.Basic
import StacksFrontier.AlgebraicGeometry.InvertiblePullback.Basic

/-!
# A3-ord, G1.1: degree-one classes on a genus-one curve are normalized

This discharges `Abel.DegreeOneNormalized`, the Riemann–Roch input of `DeuringG1Abel`, so the
Abel–Jacobi map of a genus-one curve is an isomorphism unconditionally
(`isIso_abelJacobi_of_genus_eq_one`).

For a point `ξ` of the Picard functor with fibre degree `1` and a point `t` of the base, the fibre
Euler characteristic is `χ(L_t) = deg + χ(𝒪_t) = 1 + (1 − g) = 1` (Stacks' `fibreEuler_zero`).
`H¹(X_t, L_t) = 0` since `deg = 1 ≥ 2g − 1`: this is [Stacks, Tag 0B90] over an algebraic
closure of `κ(t)`. The fibrewise reduction `finrank_fibreCohomology_one_eq_zero_of_large` is a
verbatim copy of Stacks' `Stacks.AbelMap.finrank_fibreCohomology_one_eq_zero`
(`Picard/AbelMapSmooth.lean`), whose module is not prebuilt and needs 36 unbuilt modules; its
own imports are all prebuilt. Then `h⁰ = χ + h¹ = 1`.

## Main results

* `finrank_fibreCohomology_one_eq_zero_of_large` (copy of Stacks).
* **`degreeOneNormalized`**: `Abel.DegreeOneNormalized` holds for curves of genus one.
* **`isIso_abelJacobi_of_genus_eq_one`**: for a geometrically irreducible smooth projective
  curve of genus one with a rational point, the Abel–Jacobi map `X ⟶ Pic⁰_{X/k}` is an
  isomorphism.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace
open Stacks.FibreCohomology (fibreCohomology)
open Stacks.AbelMap

universe u

noncomputable section

namespace RamanujanWeil.Arith.Deuring.Geom.Abel

open AlgebraicGeometry.SheafOfModules

section FibreVanishing

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
  [IsCurve k f] [GeometricallyIrreducible f] [Smooth f] [IsProper f]

/-- **`H¹` vanishes on the fibre of an invertible module of fibre degree at least `2g − 1`.**
A verbatim copy of Stacks' `Stacks.AbelMap.finrank_fibreCohomology_one_eq_zero`. -/
theorem finrank_fibreCohomology_one_eq_zero_of_large
    (hvan1 : ∀ (K : Type u) [Field K] [IsAlgClosed K] {Z : Scheme.{u}} (fZ : Z ⟶ Spec (.of K))
      [IsProper fZ] [IsCurve K fZ] (M : Z.Modules)
      (hM : SheafOfModules.IsInvertible Z.sheaf.obj Z.ringCatSheaf.property M),
      2 * (genus fZ : ℤ) - 1 ≤ @invertibleCurveDegree K _ Z fZ _
        (IsCurve.topologicalKrullDim_eq_one (k := K) (f := fZ)).le M hM →
      IsZero (cohomologyOverField K fZ M 1))
    {T : Scheme.{u}} (a : T ⟶ Spec (.of k)) (L : (pullback f a).Modules)
    [SheafOfModules.IsInvertible (pullback f a).sheaf.obj (pullback f a).ringCatSheaf.property L]
    {d : ℕ} (hd : 2 * (genus f : ℤ) - 1 ≤ d) (t : T)
    (hχ : (Module.finrank (T.residueField t) (fibreCohomology (pullback.snd f a) L t 0) : ℤ) -
      Module.finrank (T.residueField t) (fibreCohomology (pullback.snd f a) L t 1) =
        d + 1 - genus f) :
    Module.finrank (T.residueField t) (fibreCohomology (pullback.snd f a) L t 1) = 0 := by
  let K := AlgebraicClosure (T.residueField t)
  let φ : T.residueField t ⟶ CommRingCat.of K :=
    CommRingCat.ofHom (algebraMap (T.residueField t) K)
  let fY := pullback.snd f a
  have : IsProper fY := MorphismProperty.of_isPullback (IsPullback.of_hasPullback f a) ‹_›
  have : L.IsQuasicoherent := isQuasicoherent_of_isInvertible L
  let b := Spec.map φ ≫ T.fromSpecResidueField t
  let gZ := pullback.fst fY b
  let fZ : pullback fY b ⟶ Spec (.of K) := pullback.snd fY b
  have hZ : IsPullback gZ fZ fY b := IsPullback.of_hasPullback _ _
  let M := (Scheme.Modules.pullback gZ).obj L
  have e0 := Stacks.FibreCohomology.finrank_eq_of_isPullback fY L t φ gZ fZ hZ M (Iso.refl _) 0
  have e1 := Stacks.FibreCohomology.finrank_eq_of_isPullback fY L t φ gZ fZ hZ M (Iso.refl _) 1
  let : Algebra k K := (Spec.preimage (b ≫ a)).hom.toAlgebra
  have hb : Spec.map (CommRingCat.ofHom (algebraMap k K)) = b ≫ a := Spec.map_preimage _
  have hZX : IsPullback (gZ ≫ pullback.fst f a) fZ f
      (Spec.map (CommRingCat.ofHom (algebraMap k K))) := by
    rw [hb]
    exact hZ.paste_horiz (IsPullback.of_hasPullback f a)
  have : IsProper fZ := isProper_of_isPullback f _ fZ hZX
  have : IsIntegral (pullback fY b) := isIntegral_of_isPullback f _ fZ hZX
  have : IsIso ((Scheme.ΓSpecIso (.of K)).inv ≫ fZ.appTop) :=
    isIso_globalSections_of_isPullback f _ fZ hZX
  have h1 : topologicalKrullDim (pullback fY b : Scheme.{u}) = 1 :=
    topologicalKrullDim_eq_one_of_isPullback f _ fZ hZX
  have : IsCurve K fZ := isCurve_of_topologicalKrullDim_eq_one K fZ h1
  have hgen : genus fZ = genus f := genus_baseChange k K _ fZ f hZX
  have hM : SheafOfModules.IsInvertible (pullback fY b).sheaf.obj
      (pullback fY b).ringCatSheaf.property M := Stacks.Divisors.pullback_isInvertible gZ L
  have hdim : topologicalKrullDim (pullback fY b : Scheme.{u}) ≤ 1 := h1.le
  have hdeg : @invertibleCurveDegree K _ _ fZ _ hdim M hM = d := by
    rw [@invertibleCurveDegree_eq_sub_of_isZero K _ _ fZ _ hdim M hM
      (isZero_cohomologyOverField_of_two_le' K fZ hdim M)
      (isZero_cohomologyOverField_of_two_le' K fZ hdim _),
      finrank_cohomologyOverField_unit_zero_eq_one fZ,
      ← genus_eq_finrank_cohomologyOverField_unit_one' K fZ, hgen, e0, e1, hχ]
    ring
  have hvan := hvan1 K fZ M hM (by rw [hgen]; exact hdeg ▸ hd)
  rw [← e1]
  have := ModuleCat.subsingleton_of_isZero hvan
  exact Module.finrank_zero_of_subsingleton


end FibreVanishing

section Normalized

open Stacks.PicardFunctor Stacks.PicardCurve

variable {k : Type u} [Field k] (B : BigFppfSite.{u}) {X : Scheme.{u}} (hX : B.Contains X)
  (hk : B.Contains (Spec (.of k))) (f : B.obj hX ⟶ B.obj hk)
  [IsCurve k (B.inclusion.map f)] [GeometricallyIrreducible (B.inclusion.map f)]
  [Smooth (B.inclusion.map f)] [IsProper (B.inclusion.map f)]
  [IsProjectiveVariety k (B.inclusion.map f)]
  (σ : Spec (.of k) ⟶ X) (hσ : σ ≫ B.inclusion.map f = 𝟙 (Spec (.of k)))

/-- **Degree-one classes on a genus-one curve are normalized** (Riemann–Roch on the fibres). -/
theorem degreeOneNormalized (hg : genus (B.inclusion.map f) = 1) :
    DegreeOneNormalized B hX hk f σ hσ := by
  intro T ξ hξ t
  have hO := isIso_c_of_isCurve B hX hk f σ hσ
  have hdeg : fibreDegree B hX hk f σ hσ hO T ξ t = 1 := hξ t
  have h0 := fibreEuler_zero B hX hk f σ hσ hO T t
  have hdeg' : fibreDegree B hX hk f σ hσ hO T ξ t =
      fibreEuler B hX hk f σ hσ hO T ξ t - fibreEuler B hX hk f σ hσ hO T 0 t := rfl
  rw [hg] at h0
  have hχ : fibreEuler B hX hk f σ hσ hO T ξ t = 1 := by
    rw [hdeg', h0] at hdeg
    push_cast at hdeg
    linarith
  obtain ⟨x, rfl⟩ := surjective_toPicardFunctorHom B hX hk f σ hσ hO T ξ
  have hr : ∀ n, fibreRank B hX hk f σ hσ hO T (toPicardFunctorHom B hX hk f T x) t n =
      Module.finrank ((B.inclusion.obj T.left).residueField t)
        (fibreCohomology (pullback.snd (B.inclusion.map f) (B.inclusion.map T.hom)) (rep x) t n) :=
    fun n => fibreRank_toPicardFunctorHom B hX hk f σ hσ hO T x t n
  have hχ' : (Module.finrank ((B.inclusion.obj T.left).residueField t)
        (fibreCohomology (pullback.snd (B.inclusion.map f) (B.inclusion.map T.hom)) (rep x) t 0) :
          ℤ) -
      Module.finrank ((B.inclusion.obj T.left).residueField t)
        (fibreCohomology (pullback.snd (B.inclusion.map f) (B.inclusion.map T.hom)) (rep x) t 1) =
        (1 : ℕ) + 1 - genus (B.inclusion.map f) := by
    rw [← hr, ← hr, hg]
    exact hχ
  have : AlgebraicGeometry.SheafOfModules.IsInvertible
      (pullback (B.inclusion.map f) (B.inclusion.map T.hom)).sheaf.obj
      (pullback (B.inclusion.map f) (B.inclusion.map T.hom)).ringCatSheaf.property (rep x) :=
    (Stacks.Picard.picardRepresentative _ x).property
  have h1 := finrank_fibreCohomology_one_eq_zero_of_large (B.inclusion.map f)
    (fun K _ _ _ fZ _ _ M hM hd =>
      isZero_cohomologyOverField_one_of_two_mul_genus_sub_one_le_invertibleCurveDegree K fZ M hM
        hd)
    (B.inclusion.map T.hom) (rep x) (d := 1) (by rw [hg]; norm_num) t hχ'
  refine ⟨(hr 1).trans h1, ?_⟩
  rw [hr 0]
  rw [h1] at hχ'
  push_cast at hχ'
  rw [hg] at hχ'
  push_cast at hχ'
  omega

variable [(picardFunctor B hX hk f).IsRepresentable]

/-- **G1.1: the Abel–Jacobi map of a genus-one curve is an isomorphism.** For a geometrically
irreducible smooth projective curve `X` of genus one over `k` with a rational point `c₀`,
`aj : X ⟶ Pic⁰_{X/k}`, `c ↦ 𝒪(c − c₀)`, is an isomorphism. -/
theorem isIso_abelJacobi_of_genus_eq_one (hg : genus (B.inclusion.map f) = 1) :
    IsIso (abelJacobi B hX hk f σ hσ) :=
  isIso_abelJacobi B hX hk f σ hσ hg (degreeOneNormalized B hX hk f σ hσ hg)

end Normalized

end RamanujanWeil.Arith.Deuring.Geom.Abel
