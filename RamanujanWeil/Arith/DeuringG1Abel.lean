import StacksFrontier.AlgebraicGeometry.PicardScheme.CurvePicard.AbelJacobi
import StacksFrontier.AlgebraicGeometry.PicardScheme.CurvePicard.NormalizedRepresentable
import StacksFrontier.AlgebraicGeometry.Picard.HilbertFunctorRepresentableAmbientRankOne
import StacksFrontier.AlgebraicGeometry.PicardScheme.CurvePicard.FibreDegreeAdd

/-!
# A3-ord, G1.1: the Abel–Jacobi map of a genus-one curve is an isomorphism

`docs/ARITH_DEURING_G1.md` §2, G1.1. Let `X` be a geometrically irreducible smooth projective
curve of genus one over a field `k`, with a rational point `c₀`, on a big fppf site `B` where
its Picard functor is representable, and let `J = Pic⁰_{X/k}`, `aj : X ⟶ J`,
`c ↦ 𝒪(c − c₀)` (Stacks' `abelJacobi`).

## Main results

* `Hilb.representsSelf` (any separated `X / S`): `X` represents its degree-one Hilbert functor,
  a degree-one family being the graph of a unique section. The inverse uses Stacks'
  `isIso_of_isFiniteLocallyFreeOfRank_one`; the universal family is the diagonal.
* `DegreeOneNormalized`: **the one Stacks-level input not proved here.** Every point of the
  Picard functor whose fibres have degree one is *normalized* (fibres have `H¹ = 0` and
  `dim H⁰ = 1`). This is Riemann–Roch for degree-one line bundles on genus-one curves over the
  residue fields of the base (`h⁰ − h¹ = 1`, `h¹(L) = h⁰(K ⊗ L⁻¹) = 0` as `deg(K ⊗ L⁻¹) = −1`),
  in Stacks' fibrewise language (`normalizedSubfunctor`).
* `jacobianHomAddEquiv_comp_abelJacobi`: the point of `Pic⁰` of `m ≫ aj` for `m : T ⟶ X` is
  `m^*[Δ] − [c₀]_T`.
* **`bijective_comp_abelJacobi`**: under `DegreeOneNormalized`, `m ↦ m ≫ aj` is a bijection
  `(T ⟶ X) ≃ (T ⟶ J)` for every test scheme `T`. The proof is Stacks' normalized-open theory
  (`exists_map_universalClass_eq`, `eq_of_map_universalClass_eq`, [Stacks, Tag 0B9X]) applied
  to `H = X = Hilb¹`, together with translation by `[c₀]`.
* **`isIso_abelJacobi`**: under `DegreeOneNormalized`, `aj` is an isomorphism.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u

noncomputable section

namespace RamanujanWeil.Arith.Deuring.Geom.Abel

/-! ### `Hilb¹_{X/S} = X` -/

namespace Hilb

open Stacks.Hilbert

variable {S : Scheme.{u}} (X : Over S) [IsSeparated X.hom]

/-- The graph of a relative point, as a degree-`d` family (`d = 1`). -/
def pointFamily {T : Over S} {d : ℕ} (hd : d = 1) (x : T ⟶ X) : HilbertFamily X T d where
  ideal := pointIdeal X T x
  isFiniteLocallyFreeOfRank := by
    have := isClosedImmersion_pointGraph_of_isSeparated X T x
    subst hd
    exact isFiniteLocallyFreeOfRank_pointIdeal X T x

/-- A degree-one family maps isomorphically to the base. -/
theorem isIso_family {T : Over S} {d : ℕ} (hd : d = 1) (D : HilbertFamily X T d) :
    IsIso (D.ideal.subschemeι ≫ ((Over.pullback T.hom).obj X).hom) := by
  subst hd
  exact Stacks.Morphisms.isIso_of_isFiniteLocallyFreeOfRank_one _ D.isFiniteLocallyFreeOfRank

/-- The section `T ⟶ X` cut out by a degree-one family. -/
def familySection {T : Over S} {d : ℕ} (hd : d = 1) (D : HilbertFamily X T d) : T ⟶ X :=
  have := isIso_family X hd D
  Over.homMk (inv (D.ideal.subschemeι ≫ ((Over.pullback T.hom).obj X).hom) ≫
      D.ideal.subschemeι ≫ pullback.fst X.hom T.hom) (by
    rw [Category.assoc, Category.assoc, pullback.condition, ← Category.assoc D.ideal.subschemeι]
    exact IsIso.inv_hom_id_assoc _ _)

theorem pointGraph_familySection {T : Over S} {d : ℕ} (hd : d = 1) (D : HilbertFamily X T d) :
    haveI := isIso_family X hd D
    pointGraph X T (familySection X hd D) =
      inv (D.ideal.subschemeι ≫ ((Over.pullback T.hom).obj X).hom) ≫ D.ideal.subschemeι := by
  haveI := isIso_family X hd D
  apply pullback.hom_ext
  · simp only [pointGraph, pullback.lift_fst, familySection, Over.homMk_left, Category.assoc]
  · rw [pointGraph_comp_snd, Category.assoc]
    exact (IsIso.inv_hom_id _).symm

theorem pointIdeal_familySection {T : Over S} {d : ℕ} (hd : d = 1) (D : HilbertFamily X T d) :
    pointIdeal X T (familySection X hd D) = D.ideal := by
  haveI := isIso_family X hd D
  rw [pointIdeal, pointGraph_familySection, Scheme.Hom.ker_comp_of_isIso,
    Scheme.IdealSheafData.ker_subschemeι]

theorem familySection_pointFamily {T : Over S} {d : ℕ} (hd : d = 1) (x : T ⟶ X) :
    familySection X hd (pointFamily X hd x) = x := by
  haveI := isIso_family X hd (pointFamily X hd x)
  apply Over.OverMorphism.ext
  let g := pointGraph X T x
  have hq : inv ((pointFamily X hd x).ideal.subschemeι ≫ ((Over.pullback T.hom).obj X).hom) =
      g.toImage := by
    apply IsIso.inv_eq_of_inv_hom_id
    show g.toImage ≫ g.imageι ≫ pullback.snd X.hom T.hom = 𝟙 _
    rw [← Category.assoc, Scheme.Hom.toImage_imageι]
    exact pointGraph_comp_snd X T x
  have hl : (familySection X hd (pointFamily X hd x)).left =
      inv ((pointFamily X hd x).ideal.subschemeι ≫ ((Over.pullback T.hom).obj X).hom) ≫
        (pointFamily X hd x).ideal.subschemeι ≫ pullback.fst X.hom T.hom := rfl
  rw [hl, hq]
  change g.toImage ≫ g.imageι ≫ pullback.fst X.hom T.hom = x.left
  rw [← Category.assoc, Scheme.Hom.toImage_imageι]
  exact pullback.lift_fst _ _ _

/-- **`X` represents its degree-one Hilbert functor** (with `d = 1` given as a hypothesis, to
allow ranks that are only propositionally `1`). -/
def representsSelf {d : ℕ} (hd : d = 1) : RepresentsHilbertFunctorOfRank X X d where
  family {T} :=
    { toFun := pointFamily X hd
      invFun := familySection X hd
      left_inv := familySection_pointFamily X hd
      right_inv := fun D => HilbertFamily.ext (pointIdeal_familySection X hd D) }
  naturality {T' T} g x := by
    haveI := isClosedImmersion_pointGraph_of_isSeparated X T x
    exact (pointIdeal_comap_familyBaseChangeMap X g x).symm

theorem representsSelf_family_ideal {d : ℕ} (hd : d = 1) {T : Over S} (x : T ⟶ X) :
    ((representsSelf X hd).family x).ideal = pointIdeal X T x := rfl

end Hilb

/-! ### The Abel–Jacobi map of a genus-one curve -/

section AbelIso

open Stacks.PicardFunctor

variable {k : Type u} [Field k] (B : BigFppfSite.{u}) {X : Scheme.{u}} (hX : B.Contains X)
  (hk : B.Contains (Spec (.of k))) (f : B.obj hX ⟶ B.obj hk)
  [IsCurve k (B.inclusion.map f)] [GeometricallyIrreducible (B.inclusion.map f)]
  [Smooth (B.inclusion.map f)] [IsProper (B.inclusion.map f)]
  [IsProjectiveVariety k (B.inclusion.map f)]
  (σ : Spec (.of k) ⟶ X) (hσ : σ ≫ B.inclusion.map f = 𝟙 (Spec (.of k)))

/-- **The genus-one Riemann–Roch input (Stacks-level, not proved here).** Every point of the
Picard functor of the curve all of whose fibres have degree one is normalized: its fibres
have `H¹ = 0` and `dim H⁰ = 1`. For a curve of genus one this is Riemann–Roch on the fibres
`X_{κ(t)}`, which are genus-one curves over the residue fields `κ(t)`. -/
def DegreeOneNormalized : Prop :=
  ∀ (T : BigFppfOver B (Spec (.of k)) hk) (ξ : (picardFunctor B hX hk f).obj (op T)),
    ξ ∈ (curveDegreeSubfunctor B hX hk f σ hσ 1).obj (op T) →
      ξ ∈ (curveNormalized B hX hk f σ hσ).obj (op T)

variable [(picardFunctor B hX hk f).IsRepresentable] (hg : genus (B.inclusion.map f) = 1)

/-- `X = Hilb^g_{X/k}` for `g = 1`, in the form used by Stacks' normalized-open theory. -/
def hilbSelf : Stacks.Hilbert.RepresentsHilbertFunctorOfRank (Over.mk (B.inclusion.map f))
    (Over.mk (B.inclusion.map (curveObj B hX hk f).hom)) (genus (B.inclusion.map f)) :=
  Hilb.representsSelf (Over.mk (B.inclusion.map f)) hg

include hσ in
/-- The base point `c₀`, as a point of the test scheme `X` over the base. -/
def basePt : baseObj B hk ⟶ curveObj B hX hk f :=
  Over.homMk (B.inclusion.preimage (X := B.obj hk) (Y := B.obj hX) σ) (by
    apply B.inclusion.map_injective
    rw [Functor.map_comp, Functor.map_preimage]
    show _ = B.inclusion.map (𝟙 (B.obj hk))
    rw [CategoryTheory.Functor.map_id]
    exact hσ)

/-- The constant point `T ⟶ Spec k ⟶ X` at `c₀`. -/
def constPt (T : BigFppfOver B (Spec (.of k)) hk) : T ⟶ curveObj B hX hk f :=
  toBaseObj B hk T ≫ basePt B hX hk f σ hσ

theorem comp_constPt {T T' : BigFppfOver B (Spec (.of k)) hk} (m : T' ⟶ T) :
    m ≫ constPt B hX hk f σ hσ T = constPt B hX hk f σ hσ T' := by
  rw [constPt, constPt, ← Category.assoc]
  congr 1
  exact Over.OverMorphism.ext (Over.w m)

theorem testMap_constPt :
    (testMap B hk (constPt B hX hk f σ hσ (curveObj B hX hk f)) :
      curveOver B hX hk f ⟶ curveOver B hX hk f) = constantPoint B hX hk f σ hσ := by
  apply Over.OverMorphism.ext
  show B.inclusion.map (f ≫ B.inclusion.preimage (X := B.obj hk) (Y := B.obj hX) σ) =
    B.inclusion.map f ≫ σ
  rw [Functor.map_comp, Functor.map_preimage]

/-- The universal class `[𝒪(Δ)]` on `X ×_k X`. -/
abbrev univ : (picardFunctor B hX hk f).obj (op (curveObj B hX hk f)) :=
  universalClass B hX hk f (curveObj B hX hk f) (hilbSelf B hX hk f hg)

/-- The class `[c₀]_T` of the constant section, over a test scheme `T`. -/
abbrev constClass (T : BigFppfOver B (Spec (.of k)) hk) : (picardFunctor B hX hk f).obj (op T) :=
  (picardFunctor B hX hk f).map (constPt B hX hk f σ hσ T).op (univ B hX hk f hg)

theorem familyClass_diagonalFamily :
    familyClass B hX hk f (curveObj B hX hk f) (diagonalFamily B hX hk f) =
      univ B hX hk f hg := rfl

theorem familyClass_constantFamily :
    familyClass B hX hk f (curveObj B hX hk f) (constantFamily B hX hk f σ hσ) =
      constClass B hX hk f σ hσ hg (curveObj B hX hk f) := by
  rw [constClass, ← familyClass_family B hX hk f (curveObj B hX hk f) (hilbSelf B hX hk f hg)]
  have h : (hilbSelf B hX hk f hg).family
      (testMap B hk (constPt B hX hk f σ hσ (curveObj B hX hk f))) =
      Hilb.pointFamily (Over.mk (B.inclusion.map f)) hg (constantPoint B hX hk f σ hσ) := by
    rw [testMap_constPt]
    rfl
  rw [h]
  rfl

/-- The fibres of a class of the form `m^* [𝒪(Δ)]` have degree one. -/
theorem mem_degreeOne_map_univ {T : BigFppfOver B (Spec (.of k)) hk}
    (m : T ⟶ curveObj B hX hk f) :
    (picardFunctor B hX hk f).map m.op (univ B hX hk f hg) ∈
      (curveDegreeSubfunctor B hX hk f σ hσ 1).obj (op T) := by
  intro t
  rw [← familyClass_family B hX hk f (curveObj B hX hk f) (hilbSelf B hX hk f hg) m]
  have h := curveFibreDegree_familyClass B hX hk f σ hσ T
    ((hilbSelf B hX hk f hg).family (testMap B hk m)) t
  exact h.trans (by exact_mod_cast hg)

/-- **The point of `Pic⁰` of `m ≫ aj`** is `m^*[𝒪(Δ)] − [c₀]_T`. -/
theorem jacobianHomAddEquiv_comp_abelJacobi {T : BigFppfOver B (Spec (.of k)) hk}
    (m : T ⟶ curveObj B hX hk f) :
    ((jacobianHomAddEquiv B hX hk f σ hσ T
        (Additive.ofMul ((Over.post (X := B.obj hk) B.inclusion).map m ≫
          abelJacobi B hX hk f σ hσ))) : (picardFunctor B hX hk f).obj (op T)) =
      (picardFunctor B hX hk f).map m.op (univ B hX hk f hg) -
        constClass B hX hk f σ hσ hg T := by
  rw [abelJacobi, classifyingMap_comp, jacobianHomAddEquiv_classifyingMap]
  show (toPicardFunctor B hX hk f).app (op T) (picardMap B hX hk f m _) = _
  rw [toPicardFunctor_app_naturality, ← toPicardFunctorHom_apply, map_sub,
    toPicardFunctorHom_apply, toPicardFunctorHom_apply]
  change (picardFunctor B hX hk f).map m.op
      (familyClass B hX hk f _ (diagonalFamily B hX hk f) -
        familyClass B hX hk f _ (constantFamily B hX hk f σ hσ)) = _
  rw [familyClass_diagonalFamily B hX hk f hg, familyClass_constantFamily B hX hk f σ hσ hg]
  rw [show ∀ a b, (picardFunctor B hX hk f).map m.op (a - b) =
      (picardFunctor B hX hk f).map m.op a - (picardFunctor B hX hk f).map m.op b from
    fun a b => map_sub (AddMonoidHom.mk' ((picardFunctor B hX hk f).map m.op)
      (picardFunctor_map_add B hX hk f m)) a b]
  rw [constClass, constClass, ← picardFunctor_map_comp_apply, comp_constPt]

include hg in
/-- `ζ + [c₀]_T` has degree one when `ζ` has degree zero. -/
theorem mem_degreeOne_add_constClass {T : BigFppfOver B (Spec (.of k)) hk}
    (ζ : degreeZeroAddSubgroup B hX hk f σ hσ T) :
    (ζ : (picardFunctor B hX hk f).obj (op T)) + constClass B hX hk f σ hσ hg T ∈
      (curveDegreeSubfunctor B hX hk f σ hσ 1).obj (op T) := by
  intro t
  have h0 : fibreDegree B hX hk f σ hσ (isIso_baseChangeProj_c_of_isCurve B hX hk f σ hσ) T
      (ζ : (picardFunctor B hX hk f).obj (op T)) t = 0 := ζ.2 t
  have h1 : fibreDegree B hX hk f σ hσ (isIso_baseChangeProj_c_of_isCurve B hX hk f σ hσ) T
      (constClass B hX hk f σ hσ hg T) t = 1 :=
    mem_degreeOne_map_univ B hX hk f σ hσ hg (constPt B hX hk f σ hσ T) t
  show fibreDegree B hX hk f σ hσ (isIso_baseChangeProj_c_of_isCurve B hX hk f σ hσ) T _ t = 1
  rw [fibreDegree_add, h0, h1, zero_add]

include hg in
/-- **`m ↦ m ≫ aj` is a bijection `(T ⟶ X) ≃ (T ⟶ J)`** for every test scheme `T`, granted
`DegreeOneNormalized`. -/
theorem bijective_comp_abelJacobi (hN : DegreeOneNormalized B hX hk f σ hσ)
    (T : BigFppfOver B (Spec (.of k)) hk) :
    Function.Bijective (fun m : T ⟶ curveObj B hX hk f =>
      (Over.post (X := B.obj hk) B.inclusion).map m ≫ abelJacobi B hX hk f σ hσ) := by
  constructor
  · intro m m' h
    have h' := congrArg (fun ψ => ((jacobianHomAddEquiv B hX hk f σ hσ T (Additive.ofMul ψ)) :
      (picardFunctor B hX hk f).obj (op T))) h
    simp only at h'
    rw [jacobianHomAddEquiv_comp_abelJacobi B hX hk f σ hσ hg,
      jacobianHomAddEquiv_comp_abelJacobi B hX hk f σ hσ hg, sub_left_inj] at h'
    exact eq_of_map_universalClass_eq B hX hk f σ hσ _ (hilbSelf B hX hk f hg) m m' h'
      (hN T _ (mem_degreeOne_map_univ B hX hk f σ hσ hg m))
  · intro ψ
    set ζ := jacobianHomAddEquiv B hX hk f σ hσ T (Additive.ofMul ψ)
    obtain ⟨m, hm⟩ := exists_map_universalClass_eq B hX hk f σ hσ _ (hilbSelf B hX hk f hg) T _
      (hN T _ (mem_degreeOne_add_constClass B hX hk f σ hσ hg ζ))
    refine ⟨m, ?_⟩
    show (Over.post (X := B.obj hk) B.inclusion).map m ≫ abelJacobi B hX hk f σ hσ = ψ
    have h2 : jacobianHomAddEquiv B hX hk f σ hσ T (Additive.ofMul
        ((Over.post (X := B.obj hk) B.inclusion).map m ≫ abelJacobi B hX hk f σ hσ)) = ζ :=
      Subtype.ext (by
        rw [jacobianHomAddEquiv_comp_abelJacobi B hX hk f σ hσ hg, hm, add_sub_cancel_right])
    exact Additive.ofMul.injective (EquivLike.injective _ h2)

include hg in
/-- **G1.1: the Abel–Jacobi map of a genus-one curve is an isomorphism**, granted
`DegreeOneNormalized`. -/
theorem isIso_abelJacobi (hN : DegreeOneNormalized B hX hk f σ hσ) :
    IsIso (abelJacobi B hX hk f σ hσ) := by
  obtain ⟨m, hm⟩ := (bijective_comp_abelJacobi B hX hk f σ hσ hg hN
    (picardSchemeDegreeComponent B hX hk f σ hσ 0)).2 (𝟙 _)
  change (Over.post (X := B.obj hk) B.inclusion).map m ≫ abelJacobi B hX hk f σ hσ = 𝟙 _ at hm
  let g : (Over.post (X := B.obj hk) B.inclusion).obj (curveObj B hX hk f) ⟶
      (Over.post (X := B.obj hk) B.inclusion).obj (curveObj B hX hk f) :=
    abelJacobi B hX hk f σ hσ ≫ (Over.post (X := B.obj hk) B.inclusion).map m
  let n : curveObj B hX hk f ⟶ curveObj B hX hk f :=
    Over.homMk (B.inclusion.preimage g.left) (by
      apply B.inclusion.map_injective
      rw [Functor.map_comp]
      erw [Functor.map_preimage]
      exact Over.w g)
  have hn : (Over.post (X := B.obj hk) B.inclusion).map n = g :=
    Over.OverMorphism.ext (Functor.map_preimage B.inclusion g.left)
  have h1 : (Over.post (X := B.obj hk) B.inclusion).map n ≫ abelJacobi B hX hk f σ hσ =
      (Over.post (X := B.obj hk) B.inclusion).map (𝟙 _) ≫ abelJacobi B hX hk f σ hσ := by
    rw [hn, CategoryTheory.Functor.map_id]
    erw [Category.id_comp]
    dsimp only [g]
    erw [Category.assoc, hm]
    exact Category.comp_id _
  have hn1 : n = 𝟙 _ := (bijective_comp_abelJacobi B hX hk f σ hσ hg hN (curveObj B hX hk f)).1 h1
  refine ⟨⟨(Over.post (X := B.obj hk) B.inclusion).map m, ?_, hm⟩⟩
  show g = 𝟙 _
  rw [← hn, hn1, CategoryTheory.Functor.map_id]

end AbelIso

end RamanujanWeil.Arith.Deuring.Geom.Abel
