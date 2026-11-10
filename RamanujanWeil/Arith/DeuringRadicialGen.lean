import RamanujanWeil.Arith.DeuringG7Dual2
import StacksFrontier.AlgebraicGeometry.Variety.MiracleFlatEtale
import StacksFrontier.AlgebraicGeometry.Morphisms.Etale.LocusBaseChange
import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.UnramifiedLocusBaseChange
import StacksFrontier.AlgebraicGeometry.FiniteLocallyFreeRank.AlgClosedField
import StacksFrontier.AlgebraicGeometry.FiniteLocallyFreeRank.BaseChange
import StacksFrontier.AlgebraicGeometry.GroupScheme.AbelianVariety.ZPowFiniteLocallyFree
import StacksFrontier.AlgebraicGeometry.Curves.SeparableClosedPoint
import StacksFrontier.AlgebraicGeometry.Curves.InseparableFrobeniusChainAssembly

/-!
# RadicialDual, step (a): generic étaleness and the fibre count for curves

`docs/ARITH_DEURING_RADICIAL.md`. Let `k` be algebraically closed.

* `etaleAt_genericPoint_of_formallyUnramified`: a dominant morphism of integral schemes, locally
  of finite type, whose extension of function fields is formally unramified (e.g. separable) is
  étale at the generic point (the stalks there are fields; Stacks' miracle-flatness criterion).
* `exists_closedPoint_etaleAt`: then it is étale at some closed point (Jacobson).
* `exists_lift_point`: a surjective morphism of `k`-schemes locally of finite type is surjective
  on `k`-points.
* **`finrank_le_one_of_injective`** (the fibre count): let `v : C ⟶ Y` be a dominant morphism of
  proper curves over `k` with `Y` normal, whose extension of function fields is formally
  unramified (separable). If `v` is injective on `k`-points, then `[k(C) : k(Y)] ≤ 1`.
  Proof: `v` is finite locally free of rank `d = deg v` (Stacks 0CCK/0CCL); it is étale on an
  open containing the generic point; the image of the non-étale locus is a closed set missing the
  generic point of `Y`; over a closed point `y` outside it the fibre is finite étale of rank `d`
  over `k`, so it has `d` sections (`card_sections_of_etale_of_isAlgClosed`), which are `d`
  distinct `k`-points of `C` over `y`.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace RamanujanWeil.Arith.Deuring.Radicial

section GenericEtale

variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]

/-- The stalk map at the generic point is formally unramified when the extension of function
fields is. -/
theorem formallyUnramified_stalkMap_of_functionFieldMap (g : X ⟶ Y) [IsDominant g]
    (h : (functionFieldMap g).FormallyUnramified) :
    (g.stalkMap (genericPoint X)).hom.FormallyUnramified := by
  unfold functionFieldMap at h
  rw [CommRingCat.hom_comp] at h
  exact RingHom.FormallyUnramified.of_comp h

/-- **Generic étaleness.** A dominant morphism of integral schemes, locally of finite type, whose
extension of function fields is formally unramified, is étale at the generic point. -/
theorem etaleAt_genericPoint_of_formallyUnramified (g : X ⟶ Y) [IsDominant g]
    [LocallyOfFiniteType g] [IsLocallyNoetherian Y]
    (h : (functionFieldMap g).FormallyUnramified) : EtaleAt g (genericPoint X) := by
  have hgen : g.base (genericPoint X) = genericPoint Y := map_genericPoint_of_isDominant g
  have hunr : UnramifiedAt g (genericPoint X) :=
    (unramifiedAt_iff_formallyUnramified_stalkMap g _).2
      (formallyUnramified_stalkMap_of_functionFieldMap g h)
  have : IsRegularLocalRing (X.presheaf.stalk (genericPoint X)) :=
    inferInstanceAs (IsRegularLocalRing X.functionField)
  have : IsRegularLocalRing (Y.presheaf.stalk (g.base (genericPoint X))) := by
    rw [hgen]; exact inferInstanceAs (IsRegularLocalRing Y.functionField)
  refine etaleAt_of_unramifiedAt_of_ringKrullDim_eq g _ hunr ?_
  rw [hgen]
  exact (ringKrullDim_eq_zero_of_field X.functionField).trans
    (ringKrullDim_eq_zero_of_field Y.functionField).symm

omit [IsIntegral X] [IsIntegral Y] in
/-- A morphism étale at some point of a Jacobson scheme is étale at some closed point. -/
theorem exists_closedPoint_etaleAt (g : X ⟶ Y) [JacobsonSpace X] {x : X} (h : EtaleAt g x) :
    ∃ y ∈ closedPoints X, EtaleAt g y := by
  obtain ⟨y, hy, hyc⟩ := nonempty_inter_closedPoints (Z := {y : X | EtaleAt g y}) ⟨x, h⟩
    (isOpen_setOf_etaleAt g).isLocallyClosed
  exact ⟨y, hyc, hy⟩

/-- A separable extension gives a formally unramified algebra map. -/
theorem formallyUnramified_algebraMap_of_isSeparable (K L : Type*) [Field K] [Field L]
    [Algebra K L] [Algebra.IsSeparable K L] : (algebraMap K L).FormallyUnramified :=
  RingHom.formallyUnramified_algebraMap.2 (Algebra.FormallyUnramified.of_isSeparable K L)

end GenericEtale

section Points

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- **Surjective morphisms are surjective on `k`-points.** -/
theorem exists_lift_point {X Z : Scheme.{u}} (πX : X ⟶ Spec (.of k)) (πZ : Z ⟶ Spec (.of k))
    [LocallyOfFiniteType πX] [LocallyOfFiniteType πZ] (u : X ⟶ Z) (hu : u ≫ πZ = πX)
    (hs : Function.Surjective u.base) (c : Spec (.of k) ⟶ Z) (hc : c ≫ πZ = 𝟙 _) :
    ∃ b : Spec (.of k) ⟶ X, b ≫ πX = 𝟙 _ ∧ b ≫ u = c := by
  have := LocallyOfFiniteType.jacobsonSpace πX
  set z : Z := c.base (IsLocalRing.closedPoint k)
  have hz : z ∈ closedPoints Z := ((pointEquivClosedPoint πZ) ⟨c, hc⟩).2
  have hzc : IsClosed ({z} : Set Z) := hz
  obtain ⟨x, hx⟩ := hs z
  obtain ⟨b, hbF, hbc⟩ := nonempty_inter_closedPoints (Z := u.base ⁻¹' {z}) ⟨x, hx⟩
    (hzc.preimage u.base.hom.continuous).isLocallyClosed
  have hbc' : IsClosed ({b} : Set X) := hbc
  refine ⟨pointOfClosedPoint πX b hbc', pointOfClosedPoint_comp πX b hbc', ?_⟩
  refine ext_of_apply_closedPoint_eq πZ ?_ hc ?_
  · rw [Category.assoc, hu, pointOfClosedPoint_comp]
  · exact (congrArg u.base (pointOfClosedPoint_apply πX b hbc' _)).trans hbF

end Points

section FibreCount

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- Equal ring maps give equal degrees. -/
theorem finrank_congr_ringHom {R S : Type u} [Field R] [Field S] {φ ψ : R →+* S} (h : φ = ψ) :
    (letI := φ.toAlgebra; Module.finrank R S) = (letI := ψ.toAlgebra; Module.finrank R S) := by
  subst h; rfl

/-- **The fibre count.** A dominant morphism of proper curves over an algebraically closed field,
with normal target and formally unramified (separable) extension of function fields, which is
injective on `k`-points, has degree at most one. -/
theorem finrank_le_one_of_injective {C Y : Scheme.{u}} (πC : C ⟶ Spec (.of k))
    (πY : Y ⟶ Spec (.of k)) [IsCurve k πC] [IsCurve k πY] [IsProper πC] [IsProper πY]
    [IsNormal Y] [IsIntegral C] [IsIntegral Y] (v : C ⟶ Y) (hv : v ≫ πY = πC) [IsDominant v]
    (hsep : (functionFieldMap v).FormallyUnramified)
    (hinj : ∀ c₁ c₂ : Spec (.of k) ⟶ C, c₁ ≫ πC = 𝟙 _ → c₂ ≫ πC = 𝟙 _ → c₁ ≫ v = c₂ ≫ v →
      c₁ = c₂) :
    letI := (functionFieldMap v).toAlgebra
    Module.finrank Y.functionField C.functionField ≤ 1 := by
  classical
  have hrange := nontrivial_range_of_isDominant_of_isCurve πC πY v hv
  have hnc : ¬ ∃ y : Y, ∀ x : C, v.base x = y := by
    rintro ⟨y, hy⟩
    obtain ⟨_, ⟨a, rfl⟩, _, ⟨b, rfl⟩, hab⟩ := hrange
    exact hab ((hy a).trans (hy b).symm)
  have : LocallyOfFiniteType v := locallyOfFiniteType_of_isCurve_comp k πC πY v hv
  have hrank := isFiniteLocallyFreeOfRank_degreeOver_of_not_constant πC πY v hv hnc
  set d := degreeOver v with hd
  have hdeg : d = (letI := (functionFieldMap v).toAlgebra;
      Module.finrank Y.functionField C.functionField) := by
    rw [hd, degreeOver]
    exact finrank_congr_ringHom
      (Geom.functionFieldMap_eq_dominantFunctionFieldMap' v).symm
  rw [← hdeg]
  have hflf := Stacks.Morphisms.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree v d
  have : IsFinite v := Stacks.Morphisms.IsFiniteLocallyFree.isFinite v
  have : Flat v := Stacks.Morphisms.IsFiniteLocallyFree.flat v
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian πY
  have : LocallyOfFinitePresentation v :=
    Stacks.Morphisms.IsFiniteLocallyFree.locallyOfFinitePresentation v
  have : JacobsonSpace Y := LocallyOfFiniteType.jacobsonSpace πY
  -- étale at the generic point
  have het := etaleAt_genericPoint_of_formallyUnramified v hsep
  have hgen : v.base (genericPoint C) = genericPoint Y := map_genericPoint_of_isDominant v
  -- the image of the non-étale locus
  set Z : Set C := {x | ¬ EtaleAt v x}
  have hZ : IsClosed Z := (isOpen_setOf_etaleAt v).isClosed_compl
  set W : Set Y := v.base '' Z
  have hW : IsClosed W := v.isClosedMap _ hZ
  have hWgen : genericPoint Y ∉ W := by
    rintro ⟨z, hz, hzy⟩
    have hpre := preimage_genericPoint_of_locallyQuasiFinite v hgen
    have : z ∈ v.base ⁻¹' ({genericPoint Y} : Set Y) := hzy
    rw [hpre] at this
    exact hz (by rw [Set.mem_singleton_iff.mp this]; exact het)
  obtain ⟨y, hyW, hyc⟩ := nonempty_inter_closedPoints (Z := Wᶜ) ⟨_, hWgen⟩
    hW.isOpen_compl.isLocallyClosed
  -- the fibre over `y`
  set σ : Spec (.of k) ⟶ Y := pointOfClosedPoint πY y hyc
  have hσ : σ ≫ πY = 𝟙 _ := pointOfClosedPoint_comp πY y hyc
  have sq := IsPullback.of_hasPullback v σ
  have hrank' : Stacks.Morphisms.IsFiniteLocallyFreeOfRank (pullback.snd v σ) d :=
    Stacks.Morphisms.IsFiniteLocallyFreeOfRank.of_isPullback sq
  have het' : Etale (pullback.snd v σ) := by
    rw [etale_iff_forall_etaleAt]
    intro x'
    refine (etaleAt_iff_of_isPullback sq (Or.inl inferInstance) x').1 ?_
    by_contra hx
    apply hyW
    refine ⟨(pullback.fst v σ).base x', hx, ?_⟩
    rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply]
    exact pointOfClosedPoint_apply πY y hyc _
  have hcard := Stacks.Morphisms.card_sections_of_etale_of_isAlgClosed _ d hrank' het'
  rw [← hcard]
  -- all sections coincide
  have hsub : Subsingleton {s : Spec (.of k) ⟶ pullback v σ // s ≫ pullback.snd v σ = 𝟙 _} := by
    constructor
    rintro ⟨s₁, hs₁⟩ ⟨s₂, hs₂⟩
    have hpt : ∀ s : Spec (.of k) ⟶ pullback v σ, s ≫ pullback.snd v σ = 𝟙 _ →
        (s ≫ pullback.fst v σ) ≫ v = σ := fun s hs => by
      rw [Category.assoc, pullback.condition, ← Category.assoc, hs, Category.id_comp]
    have hover : ∀ s : Spec (.of k) ⟶ pullback v σ, s ≫ pullback.snd v σ = 𝟙 _ →
        (s ≫ pullback.fst v σ) ≫ πC = 𝟙 _ := fun s hs => by
      rw [← hv, ← Category.assoc, hpt s hs, hσ]
    have h1 : s₁ ≫ pullback.fst v σ = s₂ ≫ pullback.fst v σ :=
      hinj _ _ (hover s₁ hs₁) (hover s₂ hs₂) ((hpt s₁ hs₁).trans (hpt s₂ hs₂).symm)
    exact Subtype.ext (pullback.hom_ext h1 (hs₁.trans hs₂.symm))
  exact Finite.card_le_one_iff_subsingleton.mpr hsub

end FibreCount

end RamanujanWeil.Arith.Deuring.Radicial
