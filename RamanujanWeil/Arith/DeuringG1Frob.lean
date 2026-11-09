import RamanujanWeil.Arith.DeuringG1Point
import StacksFrontier.AlgebraicGeometry.Picard.SymmetricPower.AbelMap
import StacksFrontier.AlgebraicGeometry.Picard.HilbertFamilyPicardClass

/-!
# A3-ord, G1.1′: the Abel–Jacobi map intertwines the Frobenii

`docs/ARITH_DEURING_G1_3.md`. Let `X / k` be a pointed smooth projective curve, `Ψ : X ⟶ X` a
twisted Frobenius (`Ψ ≫ f = f ≫ F^n_k`) fixing the base point, and `φ : X ⟶ X` a `k`-morphism
with `φ ≫ Ψ = F^n_X`. Then the Frobenius `π = jacobianFrobenius Ψ` of `J = Pic⁰_{X/k}` satisfies

  `aj ≫ π = φ ≫ aj`   (`Frob.abelJacobi_comp_jacobianFrobenius`).

The proof compares the two classes at the universal point `T = X`: both are the class of the
graph of `φ` minus the class of `{c₀} × X` on `X ×_k X`. The comparison of ideal sheaves is
`Frob.pointIdeal_comap_of_comm`: the inverse image of the graph of `x` along a map of base
changes covering a monomorphism `Ψ` is the graph of the unique `x'` with `x' ≫ Ψ = g ≫ x`.

For `W / 𝔽_q` and `S : JacSite W` (`φ` the `K̄`-linear geometric Frobenius
`geometricFrobeniusBaseChangePow`):

* `JacSite.aj_comp_π`: `S.aj ≫ S.π = geomFrobO W ≫ S.aj`;
* `Jac.twist_comm_iff_geomFrob_comm`: a `K̄`-morphism `α : E_{W'} ⟶ E_W` commutes with the
  twisted Frobenii `Ψ` iff it commutes with the geometric Frobenii `φ` (one direction uses
  that `E_{W'}` is reduced and `φ` is dominant);
* `JacSite.basePt_comp_aj`: `O ≫ aj = η[J]` (pointedness in `η` form).
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
open Stacks.Frobenius
open scoped CategoryTheory.MonObj

universe u

noncomputable section

namespace RamanujanWeil.Arith.Deuring.Geom

namespace Frob

open Stacks.Hilbert

/-- **Inverse image of the graph of a point.** Let `h : X'_{T'} ⟶ X_T` cover `Ψ : X' ⟶ X` (a
monomorphism) and `g : T' ⟶ T`. If `x' ≫ Ψ = g ≫ x`, the inverse image along `h` of the ideal
of the graph of `x` is the ideal of the graph of `x'`. -/
theorem pointIdeal_comap_of_comm {S : Scheme.{u}} {X X' T T' : Over S}
    (h : ((Over.pullback T'.hom).obj X').left ⟶ ((Over.pullback T.hom).obj X).left)
    (Ψ : X'.left ⟶ X.left) [Mono Ψ] (g : T'.left ⟶ T.left)
    (hfst : h ≫ pullback.fst X.hom T.hom = pullback.fst X'.hom T'.hom ≫ Ψ)
    (hsnd : h ≫ pullback.snd X.hom T.hom = pullback.snd X'.hom T'.hom ≫ g)
    (x : T ⟶ X) (x' : T' ⟶ X') (hx : x'.left ≫ Ψ = g ≫ x.left)
    [IsClosedImmersion (pointGraph X T x)] :
    (pointIdeal X T x).comap h = pointIdeal X' T' x' := by
  have hw : pointGraph X' T' x' ≫ h = g ≫ pointGraph X T x := by
    apply pullback.hom_ext
    · rw [Category.assoc, hfst, ← Category.assoc, pointGraph_comp_fst, hx, Category.assoc,
        pointGraph_comp_fst]
    · rw [Category.assoc, hsnd, ← Category.assoc, pointGraph_comp_snd, Category.id_comp,
        Category.assoc, pointGraph_comp_snd, Category.comp_id]
  have hcond : pullback.fst h (pointGraph X T x) ≫ h =
      pullback.snd h (pointGraph X T x) ≫ pointGraph X T x := pullback.condition
  have hsg : pullback.fst h (pointGraph X T x) ≫ pullback.snd X'.hom T'.hom ≫ g =
      pullback.snd h (pointGraph X T x) := by
    have := congrArg (· ≫ pullback.snd X.hom T.hom) hcond
    simp only [Category.assoc, hsnd, pointGraph_comp_snd, Category.comp_id] at this
    exact this
  have hfg : pullback.fst h (pointGraph X T x) ≫ pullback.fst X'.hom T'.hom ≫ Ψ =
      pullback.snd h (pointGraph X T x) ≫ x.left := by
    have := congrArg (· ≫ pullback.fst X.hom T.hom) hcond
    simp only [Category.assoc, hfst, pointGraph_comp_fst] at this
    exact this
  have he : IsIso (pullback.lift (pointGraph X' T' x') g hw) := by
    refine ⟨⟨pullback.fst h (pointGraph X T x) ≫ pullback.snd X'.hom T'.hom, ?_, ?_⟩⟩
    · rw [pullback.lift_fst_assoc, pointGraph_comp_snd]
    · apply pullback.hom_ext
      · rw [Category.assoc, pullback.lift_fst, Category.id_comp]
        apply pullback.hom_ext
        · rw [Category.assoc, pointGraph_comp_fst, ← cancel_mono Ψ]
          simp only [Category.assoc]
          rw [hx, reassoc_of% hsg, hfg]
        · rw [Category.assoc, pointGraph_comp_snd, Category.comp_id]
      · rw [Category.assoc, pullback.lift_snd, Category.id_comp, Category.assoc, hsg]
  show (pointGraph X T x).ker.comap h = (pointGraph X' T' x').ker
  rw [← Scheme.IdealSheafData.ker_fst_of_isClosedImmersion (pointGraph X T x) h,
    ← Scheme.Hom.ker_comp_of_isIso (pullback.lift (pointGraph X' T' x') g hw)
      (pullback.fst h (pointGraph X T x)), pullback.lift_fst]

/-- Pullback of Picard classes of schemes commutes with differences. -/
theorem schemePullbackClass_sub {Y Z : Scheme.{u}} (h : Y ⟶ Z) (a b : Stacks.Picard.ofScheme Z) :
    Stacks.Picard.schemePullbackClass h (a - b) =
      Stacks.Picard.schemePullbackClass h a - Stacks.Picard.schemePullbackClass h b :=
  map_sub (Stacks.Picard.schemePullbackClassHom h) a b

/-! ### G1.1′ for a pointed curve with a twisted Frobenius -/

section Curve

open Stacks.PicardFunctor

variable {k : Type u} [Field k] (B : BigFppfSite.{u}) {X : Scheme.{u}} (hX : B.Contains X)
  (hk : B.Contains (Spec (.of k))) (f : B.obj hX ⟶ B.obj hk) (p : ℕ) [Fact p.Prime]
  (hS : IsInCharacteristic (Spec (.of k)) p) (n : ℕ) (Ψ : X ⟶ X)
  (hΨ : Ψ ≫ B.inclusion.map f = B.inclusion.map f ≫ absoluteFrobeniusPow (Spec (.of k)) p hS n)
  [IsCurve k (B.inclusion.map f)] [GeometricallyIrreducible (B.inclusion.map f)]
  [Smooth (B.inclusion.map f)] [IsProper (B.inclusion.map f)]
  [IsProjectiveVariety k (B.inclusion.map f)]
  (σ : Spec (.of k) ⟶ X) (hσ : σ ≫ B.inclusion.map f = 𝟙 (Spec (.of k)))

/-- A `k`-endomorphism of the curve, as an endomorphism of the test scheme `X`. -/
def curveObjHom (φ : X ⟶ X) (hφf : φ ≫ B.inclusion.map f = B.inclusion.map f) :
    curveObj B hX hk f ⟶ curveObj B hX hk f :=
  Over.homMk (B.inclusion.preimage (X := B.obj hX) (Y := B.obj hX) φ) (by
    apply B.inclusion.map_injective
    rw [Functor.map_comp]
    erw [Functor.map_preimage]
    exact hφf)

theorem post_map_curveObjHom (φ : X ⟶ X) (hφf : φ ≫ B.inclusion.map f = B.inclusion.map f) :
    (Over.post (X := B.obj hk) B.inclusion).map (curveObjHom B hX hk f φ hφf) =
      (Over.homMk φ hφf : curveOver B hX hk f ⟶ curveOver B hX hk f) :=
  Over.OverMorphism.ext (B.inclusion.map_preimage (X := B.obj hX) (Y := B.obj hX) φ)

variable [(picardFunctor B hX hk f).IsRepresentable] [IsSepClosed k]

omit [GeometricallyIrreducible (B.inclusion.map f)] [IsProper (B.inclusion.map f)]
  [IsProjectiveVariety k (B.inclusion.map f)] [IsSepClosed k]
  [(picardFunctor B hX hk f).IsRepresentable] in
/-- The class of the graph of `φ`, as a degree-one family over the second factor. -/
abbrev graphFamily (φ : X ⟶ X) (hφf : φ ≫ B.inclusion.map f = B.inclusion.map f) :
    Stacks.Hilbert.HilbertFamily (curveOver B hX hk f)
      (Over.mk (B.inclusion.map (curveObj B hX hk f).hom)) 1 :=
  Abel.Hilb.pointFamily (curveOver B hX hk f) rfl (Over.homMk φ hφf)

set_option maxHeartbeats 1000000 in
include hσ in
/-- **G1.1′, general form.** If `φ` is a `k`-endomorphism of `X` with `φ ≫ Ψ = F^n_X`, and `Ψ`
is a monomorphism fixing the base point, then `aj ≫ π_Ψ = φ ≫ aj`. -/
theorem abelJacobi_comp_jacobianFrobenius [Mono Ψ] (φ : X ⟶ X)
    (hφf : φ ≫ B.inclusion.map f = B.inclusion.map f) (hXp : IsInCharacteristic X p)
    (hφΨ : φ ≫ Ψ = absoluteFrobeniusPow X p hXp n)
    (hσΨ : σ ≫ Ψ = absoluteFrobeniusPow (Spec (.of k)) p hS n ≫ σ) :
    abelJacobi B hX hk f σ hσ ≫ jacobianFrobenius B hX hk f p hS n Ψ hΨ σ hσ =
      (Over.homMk φ hφf : curveOver B hX hk f ⟶ curveOver B hX hk f) ≫
        abelJacobi B hX hk f σ hσ := by
  set T := curveObj B hX hk f
  set Θ := twistedBaseChangeMap B hX hk f p hS n Ψ hΨ T
  set m := curveObjHom B hX hk f φ hφf
  have := isClosedImmersion_pointGraph_of_isSeparated (curveOver B hX hk f)
    (curveOver B hX hk f) (𝟙 _)
  have := isClosedImmersion_pointGraph_of_isSeparated (curveOver B hX hk f)
    (curveOver B hX hk f) (constantPoint B hX hk f σ hσ)
  -- the four inverse images
  have hconst : (B.inclusion.map f ≫ σ) ≫ Ψ =
      absoluteFrobeniusPow X p hXp n ≫ B.inclusion.map f ≫ σ := by
    rw [Category.assoc, hσΨ, ← Category.assoc, ← Category.assoc]
    exact congrArg (· ≫ σ) (absoluteFrobeniusPow_naturality (B.inclusion.map f) p hXp hS n).symm
  have hΘΔ : (pointIdeal (curveOver B hX hk f) (curveOver B hX hk f) (𝟙 _)).comap Θ =
      (graphFamily B hX hk f φ hφf).ideal :=
    pointIdeal_comap_of_comm (X := curveOver B hX hk f) (X' := curveOver B hX hk f)
      (T := curveOver B hX hk f) (T' := curveOver B hX hk f) Θ Ψ _ (twistedBaseChangeMap_fst B hX hk f p hS n Ψ hΨ T)
      (twistedBaseChangeMap_snd B hX hk f p hS n Ψ hΨ T) _ _ (by
        show φ ≫ Ψ = _ ≫ 𝟙 _
        rw [hφΨ, Category.comp_id]
        rfl)
  have hΘc : (pointIdeal (curveOver B hX hk f) (curveOver B hX hk f)
      (constantPoint B hX hk f σ hσ)).comap Θ =
      (constantFamily B hX hk f σ hσ).ideal :=
    pointIdeal_comap_of_comm (X := curveOver B hX hk f) (X' := curveOver B hX hk f)
      (T := curveOver B hX hk f) (T' := curveOver B hX hk f) Θ Ψ _ (twistedBaseChangeMap_fst B hX hk f p hS n Ψ hΨ T)
      (twistedBaseChangeMap_snd B hX hk f p hS n Ψ hΨ T) _ _ hconst
  have hmΔ : (pointIdeal (curveOver B hX hk f) (curveOver B hX hk f) (𝟙 _)).comap
      (baseChangeMap B hX hk f m) = (graphFamily B hX hk f φ hφf).ideal :=
    pointIdeal_comap_of_comm (X := curveOver B hX hk f) (X' := curveOver B hX hk f)
      (T := curveOver B hX hk f) (T' := curveOver B hX hk f) (baseChangeMap B hX hk f m) (𝟙 _) (B.inclusion.map m.left)
      (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _) _ _ (by
        show φ ≫ 𝟙 _ = B.inclusion.map (B.inclusion.preimage (X := B.obj hX) (Y := B.obj hX) φ) ≫
          𝟙 _
        erw [Functor.map_preimage]
        rfl)
  have hmc : (pointIdeal (curveOver B hX hk f) (curveOver B hX hk f)
      (constantPoint B hX hk f σ hσ)).comap (baseChangeMap B hX hk f m) =
      (constantFamily B hX hk f σ hσ).ideal :=
    pointIdeal_comap_of_comm (X := curveOver B hX hk f) (X' := curveOver B hX hk f)
      (T := curveOver B hX hk f) (T' := curveOver B hX hk f) (baseChangeMap B hX hk f m) (𝟙 _) (B.inclusion.map m.left)
      (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _) _ _ (by
        show (B.inclusion.map f ≫ σ) ≫ 𝟙 _ =
          B.inclusion.map (B.inclusion.preimage (X := B.obj hX) (Y := B.obj hX) φ) ≫
            B.inclusion.map f ≫ σ
        erw [Functor.map_preimage]
        rw [Category.comp_id, ← Category.assoc, hφf])
  -- the classes
  have iΔ := (diagonalFamily B hX hk f).isEffectiveCartierDivisor_ideal
  have iC := (constantFamily B hX hk f σ hσ).isEffectiveCartierDivisor_ideal
  have iG := (graphFamily B hX hk f φ hφf).isEffectiveCartierDivisor_ideal
  have key : Stacks.Picard.schemePullbackClass Θ (abelJacobiClass B hX hk f σ hσ) =
      picardMap B hX hk f m (abelJacobiClass B hX hk f σ hσ) := by
    rw [abelJacobiClass, schemePullbackClass_sub, picardMap, schemePullbackClass_sub]
    have e1 := @Stacks.Divisors.schemePullbackClass_picardClass_of_eq_comap _ _ Θ
      (diagonalFamily B hX hk f).ideal (graphFamily B hX hk f φ hφf).ideal iΔ iG hΘΔ.symm
    have e2 := @Stacks.Divisors.schemePullbackClass_picardClass_of_eq_comap _ _ Θ
      (constantFamily B hX hk f σ hσ).ideal (constantFamily B hX hk f σ hσ).ideal iC iC
      hΘc.symm
    have e3 := @Stacks.Divisors.schemePullbackClass_picardClass_of_eq_comap _ _
      (baseChangeMap B hX hk f m)
      (diagonalFamily B hX hk f).ideal (graphFamily B hX hk f φ hφf).ideal iΔ iG hmΔ.symm
    have e4 := @Stacks.Divisors.schemePullbackClass_picardClass_of_eq_comap _ _
      (baseChangeMap B hX hk f m)
      (constantFamily B hX hk f σ hσ).ideal (constantFamily B hX hk f σ hσ).ideal iC iC
      hmc.symm
    exact (congrArg₂ (· - ·) e1 e2).trans (congrArg₂ (· - ·) e3 e4).symm
  apply Additive.ofMul.injective
  apply (jacobianHomAddEquiv B hX hk f σ hσ T).injective
  apply Subtype.ext
  have L := jacobianHomAddEquiv_comp_jacobianFrobenius B hX hk f p hS n Ψ hΨ σ hσ T
    (abelJacobi B hX hk f σ hσ)
  have R := classifyingMap_comp B hX hk f σ hσ m (abelJacobiClass B hX hk f σ hσ)
    (hasDegreeZero_familyClass_sub B hX hk f σ hσ _ _ _)
  rw [post_map_curveObjHom] at R
  rw [← post_map_curveObjHom B hX hk f φ hφf]
  refine L.trans ?_
  change _ = ((jacobianHomAddEquiv B hX hk f σ hσ T (Additive.ofMul
    ((Over.post (X := B.obj hk) B.inclusion).map m ≫ classifyingMap B hX hk f σ hσ T
      (abelJacobiClass B hX hk f σ hσ) (hasDegreeZero_familyClass_sub B hX hk f σ hσ _ _ _))))
        : (picardFunctor B hX hk f).obj (op T))
  rw [classifyingMap_comp, jacobianHomAddEquiv_classifyingMap]
  change _ = (toPicardFunctor B hX hk f).app (op T) _
  rw [← key, ← twistedPicardMap_toPicardFunctor]
  congr 1
  change ((jacobianHomAddEquiv B hX hk f σ hσ T (Additive.ofMul (classifyingMap B hX hk f σ hσ T
    (abelJacobiClass B hX hk f σ hσ) (hasDegreeZero_familyClass_sub B hX hk f σ hσ _ _ _))))
      : (picardFunctor B hX hk f).obj (op T)) = _
  rw [jacobianHomAddEquiv_classifyingMap]
  rfl

end Curve

end Frob


/-! ### Pointedness in `η` form -/

namespace Abel

open Stacks.PicardFunctor

section Eta

variable {k : Type u} [Field k] (B : BigFppfSite.{u}) {X : Scheme.{u}} (hX : B.Contains X)
  (hk : B.Contains (Spec (.of k))) (f : B.obj hX ⟶ B.obj hk)
  [IsCurve k (B.inclusion.map f)] [GeometricallyIrreducible (B.inclusion.map f)]
  [Smooth (B.inclusion.map f)] [IsProper (B.inclusion.map f)]
  [IsProjectiveVariety k (B.inclusion.map f)]
  (σ : Spec (.of k) ⟶ X) (hσ : σ ≫ B.inclusion.map f = 𝟙 (Spec (.of k)))
  [(picardFunctor B hX hk f).IsRepresentable] (hg : genus (B.inclusion.map f) = 1)

/-- The base point `c₀` as a point `𝟙_ ⟶ X` of the curve over `k`. -/
def basePtO : 𝟙_ (Over (Spec (.of k))) ⟶ curveOver B hX hk f :=
  (Over.post (X := B.obj hk) B.inclusion).map (basePt B hX hk f σ hσ)

theorem basePtO_left : (basePtO B hX hk f σ hσ).left = σ :=
  B.inclusion.map_preimage (X := B.obj hk) (Y := B.obj hX) σ

include hg in
/-- **`aj(c₀) = 0` in `η` form**: `c₀ ≫ aj = η[J]`. -/
theorem basePtO_comp_abelJacobi :
    basePtO B hX hk f σ hσ ≫ abelJacobi B hX hk f σ hσ = η[(jacobianGrp B hX hk f σ hσ).X] := by
  have h0 := jacobianHomAddEquiv_basePt_comp_abelJacobi B hX hk f σ hσ hg
  have h1 : ((jacobianHomAddEquiv B hX hk f σ hσ (baseObj B hk)
      (Additive.ofMul (η[(jacobianGrp B hX hk f σ hσ).X] :
        (Over.post (X := B.obj hk) B.inclusion).obj (baseObj B hk) ⟶ _))) :
        (picardFunctor B hX hk f).obj (op (baseObj B hk))) = 0 := by
    have : (η[(jacobianGrp B hX hk f σ hσ).X] :
        (Over.post (X := B.obj hk) B.inclusion).obj (baseObj B hk) ⟶ _) = 1 := by
      rw [CategoryTheory.Hom.one_def, CartesianMonoidalCategory.toUnit_unique
        (CartesianMonoidalCategory.toUnit _) (𝟙 _), Category.id_comp]
    rw [this]
    exact congrArg Subtype.val (map_zero (jacobianHomAddEquiv B hX hk f σ hσ (baseObj B hk)))
  exact Additive.ofMul.injective ((jacobianHomAddEquiv B hX hk f σ hσ (baseObj B hk)).injective
    (Subtype.ext (h0.trans h1.symm)))

end Eta

end Abel

/-! ### For a Weierstrass curve -/

namespace Jac

open AlgebraicGeometry.ModuliEllipticCurves AlgebraicGeometry.ModuliEllipticCurves.Weierstrass
open RamanujanWeil.Ihara Stacks.PicardFunctor Stacks.EtaleCohomology

attribute [local instance] RamanujanWeil.Ihara.fact_ringChar_prime

/-- The `n`-fold absolute Frobenius is the identity on points, hence dominant. -/
theorem isDominant_absoluteFrobeniusPow (Z : Scheme.{u}) (p : ℕ) [Fact p.Prime]
    (hZ : IsInCharacteristic Z p) (n : ℕ) : IsDominant (absoluteFrobeniusPow Z p hZ n) := by
  have h : ∀ z, (absoluteFrobeniusPow Z p hZ n).base z = z := by
    intro z
    induction n with
    | zero => rfl
    | succ m ih =>
      rw [absoluteFrobeniusPow, pow_succ, End.mul_def]
      show (End.asHom (End.of (absoluteFrobenius Z p hZ) ^ m)).base
        ((absoluteFrobenius Z p hZ).base z) = z
      rw [absoluteFrobenius_apply]
      exact ih
  exact ⟨Function.Surjective.denseRange fun z => ⟨z, h z⟩⟩

variable {k : Type u} [Field k] [Fintype k]

theorem charP_k : CharP k (ringChar k) := ringChar.charP k

/-- **The `K̄`-linear geometric Frobenius** `φ_W = F_{E/k} × id` of `E_W`. -/
abbrev geomFrob (W : WeierstrassCurve k) : Ew W ⟶ Ew W :=
  haveI := charP_k (k := k)
  geometricFrobeniusBaseChangePow (Yw W) (AlgebraicClosure k) (ringChar k) (cardExp k)
    card_eq_ringChar_pow 1

theorem geomFrob_comp_gw (W : WeierstrassCurve k) : geomFrob W ≫ gw W = gw W :=
  haveI := charP_k (k := k)
  geometricFrobeniusBaseChangePow_snd (Yw W) (AlgebraicClosure k) (ringChar k) (cardExp k)
    card_eq_ringChar_pow 1

theorem isInChar_Ew (W : WeierstrassCurve k) : IsInCharacteristic (Ew W) (ringChar k) :=
  haveI := charP_k (k := k)
  isInCharacteristic_fieldBaseChange (Yw W) (AlgebraicClosure k) (ringChar k)

/-- `Ψ_W ≫ φ_W = F^f_{E_W}`. -/
theorem twist_comp_geomFrob (W : WeierstrassCurve k) :
    (JacSite.Ψ (W := W)).hom ≫ geomFrob W =
      absoluteFrobeniusPow (Ew W) (ringChar k) (isInChar_Ew W) (cardExp k) := by
  haveI := charP_k (k := k)
  have h := galoisBaseChange_comp_geometricFrobeniusBaseChangePow (Yw W) (AlgebraicClosure k)
    (ringChar k) (cardExp k) card_eq_ringChar_pow 1 _
    (arithmeticFrobenius_pow_apply (AlgebraicClosure k) (ringChar k) (cardExp k)
      card_eq_ringChar_pow 1)
  rw [mul_one] at h
  exact h

/-- `φ_W ≫ Ψ_W = F^f_{E_W}`. -/
theorem geomFrob_comp_twist (W : WeierstrassCurve k) :
    geomFrob W ≫ (JacSite.Ψ (W := W)).hom =
      absoluteFrobeniusPow (Ew W) (ringChar k) (isInChar_Ew W) (cardExp k) := by
  rw [← cancel_epi (JacSite.Ψ (W := W)).hom, ← Category.assoc, twist_comp_geomFrob,
    absoluteFrobeniusPow_naturality (JacSite.Ψ (W := W)).hom (ringChar k) (isInChar_Ew W)
      (isInChar_Ew W) (cardExp k)]

theorem geomFrob_eq (W : WeierstrassCurve k) :
    geomFrob W = absoluteFrobeniusPow (Ew W) (ringChar k) (isInChar_Ew W) (cardExp k) ≫
      (JacSite.Ψ (W := W)).inv := by
  rw [← geomFrob_comp_twist, Category.assoc, Iso.hom_inv_id, Category.comp_id]

instance isDominant_geomFrob (W : WeierstrassCurve k) : IsDominant (geomFrob W) := by
  rw [geomFrob_eq]
  haveI := isDominant_absoluteFrobeniusPow (Ew W) (ringChar k) (isInChar_Ew W) (cardExp k)
  infer_instance

variable (W : WeierstrassCurve k) [W.IsElliptic]

instance isReduced_Ew : IsReduced (Ew W) := by
  have hc : IsCurve (AlgebraicClosure k) (gw W) := isCurve_projOf_baseChange W _
  exact @isReduced_of_isIntegral _ hc.toIsVariety.toIsIntegral

instance isSeparated_gw : IsSeparated (gw W) :=
  (isCurve_projOf_baseChange W (AlgebraicClosure k)).toIsVariety.toIsSeparated

/-- `Ψ_W` lies over the `q`-power Frobenius of `Spec K̄`. -/
theorem twist_comp_gw : (JacSite.Ψ (W := W)).hom ≫ gw W =
    gw W ≫ absoluteFrobeniusPow (Spec (.of (AlgebraicClosure k))) (ringChar k)
      JacSite.specIsInChar (cardExp k) :=
  (Classical.choice (nonempty_jacSite W)).Ψ_comp

/-- The `q`-power Frobenius of `Spec K̄` fixes `Spec K̄ ⟶ Spec k`. -/
theorem frob_comp_specAlgebraMap :
    absoluteFrobeniusPow (Spec (.of (AlgebraicClosure k))) (ringChar k) JacSite.specIsInChar
        (cardExp k) ≫ specAlgebraMap k (AlgebraicClosure k) =
      specAlgebraMap k (AlgebraicClosure k) := by
  rw [← specMap_eq_absoluteFrobeniusPow
    (JacSite.frob : AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k).toAlgHom.toRingHom _ _
      JacSite.specIsInChar (fun a => by
        simp only [JacSite.frob, pow_one]
        exact iterateFrobeniusEquiv_def _ _ _ a)]
  rw [← Spec.map_comp]
  congr 1
  ext a
  exact (JacSite.frob : AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k).commutes a

/-- **`Ψ_W` fixes the zero section**: `O ≫ Ψ = F_{K̄} ≫ O`. -/
theorem zeroPt_comp_twist : zeroPt W ≫ (JacSite.Ψ (W := W)).hom =
    absoluteFrobeniusPow (Spec (.of (AlgebraicClosure k))) (ringChar k) JacSite.specIsInChar
      (cardExp k) ≫ zeroPt W := by
  apply pullback.hom_ext
  · rw [Category.assoc, Category.assoc]
    show zeroPt W ≫ galoisBaseChange (Yw W) (AlgebraicClosure k) JacSite.frob ≫
        pullback.fst (Yw W).hom (specAlgebraMap k (AlgebraicClosure k)) =
      _ ≫ zeroPt W ≫ pullback.fst (Yw W).hom (specAlgebraMap k (AlgebraicClosure k))
    rw [galoisBaseChange_comp_fst, zeroPt, pullback.lift_fst, ← Category.assoc,
      frob_comp_specAlgebraMap]
  · rw [Category.assoc, Category.assoc]
    show zeroPt W ≫ (JacSite.Ψ (W := W)).hom ≫ gw W = _ ≫ zeroPt W ≫ gw W
    rw [twist_comp_gw, ← Category.assoc, show zeroPt W ≫ gw W = 𝟙 _ from pullback.lift_snd _ _ _,
      Category.id_comp, Category.comp_id]

/-- **`Ψ`-equivariance ⟺ `φ`-equivariance** for a `K̄`-morphism `α : E_{W'} ⟶ E_W`. The
direction `⇐` uses that `E_{W'}` is reduced, `E_W` separated and `φ_{W'}` dominant. -/
theorem twist_comm_iff_geomFrob_comm {W W' : WeierstrassCurve k} [W.IsElliptic]
    [W'.IsElliptic] (α : Ew W' ⟶ Ew W) (hα : α ≫ gw W = gw W') :
    α ≫ (JacSite.Ψ (W := W)).hom = (JacSite.Ψ (W := W')).hom ≫ α ↔
      α ≫ geomFrob W = geomFrob W' ≫ α := by
  have hnat := absoluteFrobeniusPow_naturality α (ringChar k) (isInChar_Ew W') (isInChar_Ew W)
    (cardExp k)
  constructor
  · intro h
    rw [← cancel_mono (JacSite.Ψ (W := W)).hom, Category.assoc, Category.assoc,
      geomFrob_comp_twist, h, reassoc_of% (geomFrob_comp_twist W'), hnat]
  · intro h
    refine ext_of_isDominant_of_isSeparated (gw W) ?_ (geomFrob W') ?_
    · rw [Category.assoc, Category.assoc, twist_comp_gw W, reassoc_of% hα, hα, twist_comp_gw W']
    · rw [reassoc_of% (geomFrob_comp_twist W'), hnat, ← reassoc_of% h, geomFrob_comp_twist]

namespace JacSite

variable {W} (S : JacSite W)

/-- `φ_W` as an endomorphism of `E_W` over `Spec K̄`. -/
def geomFrobO : curveOver S.B S.hX S.hk S.f ⟶ curveOver S.B S.hX S.hk S.f :=
  Over.homMk (geomFrob W) (geomFrob_comp_gw W)

/-- **G1.1′ for `W`: `aj_W ≫ π_W = φ_W ≫ aj_W`.** -/
theorem aj_comp_π : S.aj ≫ S.π = S.geomFrobO ≫ S.aj :=
  Frob.abelJacobi_comp_jacobianFrobenius S.B S.hX S.hk S.f (ringChar k) specIsInChar (cardExp k)
    Ψ.hom S.Ψ_comp (zeroPt W) S.o_comp (geomFrob W) (geomFrob_comp_gw W) (isInChar_Ew W)
    (geomFrob_comp_twist W) (zeroPt_comp_twist W)

/-- `aj_W⁻¹ ≫ π_W` form: `π_W = aj⁻¹ ≫ φ ≫ aj`. -/
theorem π_eq : S.π = inv S.aj ≫ S.geomFrobO ≫ S.aj := by
  rw [← aj_comp_π, IsIso.inv_hom_id_assoc]

/-- The zero section `O` as a point `𝟙_ ⟶ E_W` over `Spec K̄`. -/
abbrev zeroO : 𝟙_ (Over (Spec (.of (AlgebraicClosure k)))) ⟶ curveOver S.B S.hX S.hk S.f :=
  Abel.basePtO S.B S.hX S.hk S.f (zeroPt W) S.o_comp

theorem zeroO_left : S.zeroO.left = zeroPt W :=
  Abel.basePtO_left S.B S.hX S.hk S.f (zeroPt W) S.o_comp

/-- **`aj_W(O) = 0` in `η` form**: `O ≫ aj_W = η[J_W]`. -/
theorem zeroO_comp_aj : S.zeroO ≫ S.aj = η[S.J] :=
  Abel.basePtO_comp_abelJacobi S.B S.hX S.hk S.f (zeroPt W) S.o_comp S.genus_f

end JacSite

end Jac

end RamanujanWeil.Arith.Deuring.Geom
