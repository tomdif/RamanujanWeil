import StacksFrontier.AlgebraicGeometry.Stacks.WeierstrassCubicCharts
import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.FieldValuedPointCount

/-!
# M4a gap 2 / M6: `K`-points of the plane cubic `projOf W` are Mathlib's `W(K)`

Let `W` be an elliptic Weierstrass curve over a field `k` and `K` a field over `k`. The `K`-valued
points over `k` of Stacks' plane cubic `E = projOf W ⊂ ℙ²_k`
(`Stacks.EtaleCohomology.fieldValuedPoints (projectionOf W) K`) are in bijection with Mathlib's
`(W.baseChange K).toAffine.Point` (`fvpEquivPoint`):

* a point whose image lies in the chart `D₊(z)` factors uniquely through the open immersion
  `chartZ W : Spec k[W] ⟶ E` (coordinate ring `k[W] = W.toAffine.CoordinateRing`,
  `IsOpenImmersion.lift`), i.e. is a `k`-algebra map `k[W] → K` (`Spec` fully faithful), i.e. an
  affine solution `(x, y) ∈ K²` of the Weierstrass equation (`chartAlgHomEquiv`), which is
  nonsingular because `Δ` is a unit (`equation_iff_nonsingular`);
* the complement of `D₊(z)` is the image of the zero section `(0 : 1 : 0)` (`range_zeroOf`), a
  `k`-rational point; its residue field is `k`, so exactly one `K`-point lies over it.

Consequences:
* `natCard_fieldValuedPoints_projOf`: `#E(K) = #W(K)` for every field `K/k`;
* **`realizesWeierstrass_projOf`** (in `PointsRealizes.lean`): M4a gap 2, `RealizesWeierstrass (weierstrassScheme W B)
  (projectionOf W) W`, holds for every elliptic `W` over every finite field (no hypothesis).
-/

open CategoryTheory AlgebraicGeometry Stacks.EtaleCohomology
open AlgebraicGeometry.ModuliEllipticCurves.Weierstrass

universe u

namespace RamanujanWeil.Ihara

noncomputable section

variable {k : Type u} [Field k] (W : WeierstrassCurve k) (K : Type u) [Field K] [Algebra k K]

/-! ### The affine chart: `k`-algebra maps `k[W] → K` are affine solutions -/

theorem eval₂_polynomial_eq (x y : K) :
    W.toAffine.polynomial.eval₂ (Polynomial.eval₂RingHom (algebraMap k K) x) y =
      (W.baseChange K).toAffine.polynomial.evalEval x y := by
  rw [WeierstrassCurve.Affine.evalEval_polynomial]
  simp only [WeierstrassCurve.Affine.polynomial, Polynomial.eval₂_add, Polynomial.eval₂_sub,
    Polynomial.eval₂_mul, Polynomial.eval₂_pow, Polynomial.eval₂_C, Polynomial.eval₂_X,
    Polynomial.coe_eval₂RingHom, Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_pow]
  simp only [WeierstrassCurve.baseChange, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂,
    WeierstrassCurve.map_a₃, WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆]
  ring

theorem algebraMap_coordinateRing_eq (r : k) :
    algebraMap k W.toAffine.CoordinateRing r = AdjoinRoot.of _ (Polynomial.C r) := rfl

/-- `k`-algebra maps out of `k[W]` are determined by the images of `x` and `y`. -/
theorem algHom_ext_coord {ψ₁ ψ₂ : W.toAffine.CoordinateRing →ₐ[k] K}
    (hX : ψ₁ (AdjoinRoot.of _ Polynomial.X) = ψ₂ (AdjoinRoot.of _ Polynomial.X))
    (hY : ψ₁ (AdjoinRoot.root _) = ψ₂ (AdjoinRoot.root _)) : ψ₁ = ψ₂ := by
  refine AlgHom.coe_ringHom_injective (AdjoinRoot.ringHom_ext ?_ hY)
  refine Polynomial.ringHom_ext (fun r => ?_) hX
  show ψ₁ (AdjoinRoot.of _ (Polynomial.C r)) = ψ₂ (AdjoinRoot.of _ (Polynomial.C r))
  rw [← algebraMap_coordinateRing_eq, ψ₁.commutes, ψ₂.commutes]

/-- The `k`-algebra map `k[W] → K` of an affine solution `(x, y)`. -/
def chartRingHomOf (xy : {xy : K × K // (W.baseChange K).toAffine.Equation xy.1 xy.2}) :
    W.toAffine.CoordinateRing →+* K :=
  AdjoinRoot.lift (Polynomial.eval₂RingHom (algebraMap k K) xy.1.1) xy.1.2
    (by rw [eval₂_polynomial_eq]; exact xy.2)

/-- The `k`-algebra map `k[W] → K` of an affine solution `(x, y)`. -/
def chartAlgHomOf (xy : {xy : K × K // (W.baseChange K).toAffine.Equation xy.1 xy.2}) :
    W.toAffine.CoordinateRing →ₐ[k] K :=
  { chartRingHomOf W K xy with
    commutes' := fun r => by
      show chartRingHomOf W K xy (algebraMap k W.toAffine.CoordinateRing r) = _
      rw [chartRingHomOf, algebraMap_coordinateRing_eq, AdjoinRoot.lift_of]
      simp }

theorem chartAlgHomOf_X (xy : {xy : K × K // (W.baseChange K).toAffine.Equation xy.1 xy.2}) :
    chartAlgHomOf W K xy (AdjoinRoot.of _ Polynomial.X) = xy.1.1 := by
  show chartRingHomOf W K xy (AdjoinRoot.of _ Polynomial.X) = _
  rw [chartRingHomOf, AdjoinRoot.lift_of]
  simp

theorem chartAlgHomOf_root (xy : {xy : K × K // (W.baseChange K).toAffine.Equation xy.1 xy.2}) :
    chartAlgHomOf W K xy (AdjoinRoot.root _) = xy.1.2 := by
  show chartRingHomOf W K xy (AdjoinRoot.root _) = _
  rw [chartRingHomOf, AdjoinRoot.lift_root]

/-- `k`-algebra maps `k[W] → K` are the affine solutions `(x, y) ∈ K²` of `W`. -/
def chartAlgHomEquiv :
    (W.toAffine.CoordinateRing →ₐ[k] K) ≃
      {xy : K × K // (W.baseChange K).toAffine.Equation xy.1 xy.2} where
  toFun ψ := ⟨(ψ (AdjoinRoot.of _ Polynomial.X), ψ (AdjoinRoot.root _)), by
    have hcomp : ψ.toRingHom.comp (AdjoinRoot.of W.toAffine.polynomial) =
        Polynomial.eval₂RingHom (algebraMap k K) (ψ (AdjoinRoot.of _ Polynomial.X)) := by
      refine Polynomial.ringHom_ext (fun r => ?_) (by simp)
      simp only [RingHom.comp_apply, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C]
      rw [← algebraMap_coordinateRing_eq]
      exact ψ.commutes r
    show (W.baseChange K).toAffine.polynomial.evalEval _ _ = 0
    rw [← eval₂_polynomial_eq, ← hcomp]
    have h := Polynomial.hom_eval₂ W.toAffine.polynomial (AdjoinRoot.of W.toAffine.polynomial)
      ψ.toRingHom (AdjoinRoot.root _)
    rw [AdjoinRoot.eval₂_root, map_zero] at h
    exact h.symm⟩
  invFun xy := chartAlgHomOf W K xy
  left_inv ψ := algHom_ext_coord W K (chartAlgHomOf_X W K _) (chartAlgHomOf_root W K _)
  right_inv xy := Subtype.ext (Prod.ext (chartAlgHomOf_X W K xy) (chartAlgHomOf_root W K xy))

/-! ### `K`-points in the chart `D₊(z)` -/

/-- The point of `E` underlying a `K`-point. -/
abbrev fvpPt (g : fieldValuedPoints (projectionOf W) K) : projOf W :=
  (fieldValuedPointsEquiv (projectionOf W) K g).1

theorem fvpPt_mem_of {U : Set (projOf W)} (g : fieldValuedPoints (projectionOf W) K)
    (a : Spec (.of K)) (h : g.1 a ∈ U) : fvpPt W K g ∈ U := by
  rw [Subsingleton.elim a (IsLocalRing.closedPoint K)] at h
  exact h

theorem fvpPt_eq (g : fieldValuedPoints (projectionOf W) K) (a : Spec (.of K)) :
    g.1 a = fvpPt W K g := by
  rw [Subsingleton.elim a (IsLocalRing.closedPoint K)]
  rfl

/-- The chart `D₊(z)`. -/
abbrev chartOpen : (projOf W).Opens := basicOpenOf W (coordOf W 2)

theorem range_subset_chartZ (g : fieldValuedPoints (projectionOf W) K)
    (hg : fvpPt W K g ∈ chartOpen W) : Set.range g.1 ⊆ Set.range (chartZ W) := by
  rintro _ ⟨a, rfl⟩
  rw [fvpPt_eq]
  have : fvpPt W K g ∈ (chartZ W).opensRange := by rw [opensRange_chartZ]; exact hg
  exact this

theorem algHom_commutes_of_spec (h : Spec (.of K) ⟶ Spec (.of W.toAffine.CoordinateRing))
    (hh : h ≫ Spec.map (CommRingCat.ofHom (algebraMap k W.toAffine.CoordinateRing)) =
      Spec.map (CommRingCat.ofHom (algebraMap k K))) (r : k) :
    (Spec.preimage h).hom (algebraMap k W.toAffine.CoordinateRing r) = algebraMap k K r := by
  have h1 : Spec.map (CommRingCat.ofHom (algebraMap k W.toAffine.CoordinateRing) ≫
      Spec.preimage h) = Spec.map (CommRingCat.ofHom (algebraMap k K)) := by
    rw [Spec.map_comp, Spec.map_preimage, hh]
  have h2 := congrArg CommRingCat.Hom.hom (Spec.map_injective h1)
  exact RingHom.congr_fun h2 r

/-- The factorization of a `K`-point in `D₊(z)` through the chart. -/
def chartLift (g : fieldValuedPoints (projectionOf W) K) (hg : fvpPt W K g ∈ chartOpen W) :
    Spec (.of K) ⟶ Spec (.of W.toAffine.CoordinateRing) :=
  IsOpenImmersion.lift (chartZ W) g.1 (range_subset_chartZ W K g hg)

theorem chartLift_fac (g : fieldValuedPoints (projectionOf W) K) (hg : fvpPt W K g ∈ chartOpen W) :
    chartLift W K g hg ≫ chartZ W = g.1 :=
  IsOpenImmersion.lift_fac _ _ _

/-- `K`-points with image in `D₊(z)` are `k`-algebra maps `k[W] → K`. -/
def fvpChartEquiv :
    {g : fieldValuedPoints (projectionOf W) K // fvpPt W K g ∈ chartOpen W} ≃
      (W.toAffine.CoordinateRing →ₐ[k] K) where
  toFun g :=
    { (Spec.preimage (chartLift W K g.1 g.2)).hom with
      commutes' := algHom_commutes_of_spec W K _ (by
        rw [← chartZ_projectionOf, ← Category.assoc, chartLift_fac]
        exact g.1.2) }
  invFun ψ := ⟨⟨Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ chartZ W, by
      rw [Category.assoc, chartZ_projectionOf, ← Spec.map_comp]
      congr 1
      ext r
      exact ψ.commutes r⟩, by
    have : (Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ chartZ W) default ∈
        (chartZ W).opensRange := ⟨Spec.map (CommRingCat.ofHom ψ.toRingHom) default, by simp⟩
    rw [opensRange_chartZ] at this
    exact fvpPt_mem_of W K (U := (chartOpen W : Set (projOf W))) _ default this⟩
  left_inv g := by
    refine Subtype.ext (Subtype.ext ?_)
    show Spec.map (CommRingCat.ofHom (Spec.preimage (chartLift W K g.1 g.2)).hom) ≫ chartZ W =
      g.1.1
    rw [CommRingCat.ofHom_hom, Spec.map_preimage, chartLift_fac]
  right_inv ψ := by
    refine AlgHom.coe_ringHom_injective ?_
    show (Spec.preimage (chartLift W K _ _)).hom = ψ.toRingHom
    rw [chartLift, ← IsOpenImmersion.lift_uniq _ _ _ (Spec.map (CommRingCat.ofHom ψ.toRingHom)) rfl,
      Spec.preimage_map, CommRingCat.hom_ofHom]

/-! ### `K`-points off the chart: the zero section -/

/-- The point `(0 : 1 : 0)` of `E`. -/
abbrev zeroPt : projOf W := zeroOf W (default : Spec (.of k))

theorem eq_zeroPt_of_not_mem (x : projOf W) (hx : x ∉ chartOpen W) : x = zeroPt W := by
  have : x ∈ Set.range (zeroOf W) := by
    rw [range_zeroOf]
    exact hx
  obtain ⟨a, rfl⟩ := this
  rw [Subsingleton.elim a default]

theorem zeroPt_not_mem : zeroPt W ∉ chartOpen W := by
  have : zeroPt W ∈ Set.range (zeroOf W) := ⟨_, rfl⟩
  rw [range_zeroOf] at this
  exact this

/-- The `k`-point `(0 : 1 : 0)` as an element of `E(k)`. -/
def zeroFvp : fieldValuedPoints (projectionOf W) k :=
  ⟨zeroOf W, by
    rw [zeroOf_projectionOf, Algebra.algebraMap_self, CommRingCat.ofHom_id, Spec.map_id]⟩

/-- If `κ(x)` embeds into `k` over `k`, the structure map `k → κ(x)` is surjective. -/
theorem surjective_fieldToResidue_of_emb (x : projOf W)
    (τ : residueEmbeddings (projectionOf W) k x) :
    Function.Surjective (fieldToResidue (projectionOf W) x).hom := by
  intro a
  refine ⟨τ.1.hom a, τ.1.hom.injective ?_⟩
  have h := RingHom.congr_fun (congrArg CommRingCat.Hom.hom τ.2) (τ.1.hom a)
  simpa only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom,
    Algebra.algebraMap_self, RingHom.id_apply] using h

/-- The structure map `k → κ(0)` is surjective (`κ(0) = k`). -/
theorem surjective_fieldToResidue_zeroPt :
    Function.Surjective (fieldToResidue (projectionOf W) (zeroPt W)).hom := by
  have hx : (fieldValuedPointsEquiv (projectionOf W) k (zeroFvp W)).1 = zeroPt W := by
    exact (fvpPt_eq W k (zeroFvp W) default).symm
  have := surjective_fieldToResidue_of_emb W _
    (fieldValuedPointsEquiv (projectionOf W) k (zeroFvp W)).2
  rwa [hx] at this

/-- Exactly one `K`-point lies over `(0 : 1 : 0)`. -/
theorem subsingleton_residueEmbeddings_zeroPt :
    Subsingleton (residueEmbeddings (projectionOf W) K (zeroPt W)) := by
  refine ⟨fun σ₁ σ₂ => Subtype.ext ?_⟩
  ext a
  obtain ⟨b, rfl⟩ := surjective_fieldToResidue_zeroPt W a
  have h₁ := RingHom.congr_fun (congrArg CommRingCat.Hom.hom σ₁.2) b
  have h₂ := RingHom.congr_fun (congrArg CommRingCat.Hom.hom σ₂.2) b
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at h₁ h₂
  rw [h₁, h₂]

/-- The `K`-point `Spec K → Spec k → E` through `(0 : 1 : 0)`. -/
def zeroFvpK : fieldValuedPoints (projectionOf W) K :=
  ⟨Spec.map (CommRingCat.ofHom (algebraMap k K)) ≫ zeroOf W, by
    rw [Category.assoc, zeroOf_projectionOf, Category.comp_id]⟩

theorem zeroFvpK_not_mem : fvpPt W K (zeroFvpK W K) ∉ chartOpen W := by
  have : fvpPt W K (zeroFvpK W K) = zeroPt W := by
    refine (fvpPt_eq W K _ default).symm.trans ?_
    show (Spec.map (CommRingCat.ofHom (algebraMap k K)) ≫ zeroOf W) default = zeroOf W default
    rw [Scheme.Hom.comp_apply]
    exact congrArg _ (Subsingleton.elim _ _)
  rw [this]
  exact zeroPt_not_mem W

instance uniqueOffChart :
    Unique {g : fieldValuedPoints (projectionOf W) K // fvpPt W K g ∉ chartOpen W} where
  default := ⟨zeroFvpK W K, zeroFvpK_not_mem W K⟩
  uniq g := by
    have hs := subsingleton_residueEmbeddings_zeroPt W K
    have hsig : ∀ s₁ s₂ : Σ x : projOf W, residueEmbeddings (projectionOf W) K x,
        s₁.1 = zeroPt W → s₂.1 = zeroPt W → s₁ = s₂ := by
      rintro ⟨x₁, σ₁⟩ ⟨x₂, σ₂⟩ h₁ h₂
      dsimp only at h₁ h₂
      subst h₁ h₂
      rw [Subsingleton.elim σ₁ σ₂]
    refine Subtype.ext ((fieldValuedPointsEquiv (projectionOf W) K).injective (hsig _ _
      (eq_zeroPt_of_not_mem W _ g.2) (eq_zeroPt_of_not_mem W _ (zeroFvpK_not_mem W K))))

/-! ### Assembly -/

/-- Affine solutions are nonsingular (`Δ` is a unit). -/
def equationEquivNonsingular [W.IsElliptic] :
    {xy : K × K // (W.baseChange K).toAffine.Equation xy.1 xy.2} ≃
      {xy : K × K // (W.baseChange K).toAffine.Nonsingular xy.1 xy.2} :=
  haveI : (W.baseChange K).IsElliptic := inferInstanceAs (W.map (algebraMap k K)).IsElliptic
  Equiv.subtypeEquivRight fun _ => WeierstrassCurve.Affine.equation_iff_nonsingular

open scoped Classical in
/-- **`E(K) ≃ W(K)`** for the plane cubic `E = projOf W` of an elliptic `W` over `k` and any field
`K/k`: `K`-valued points over `k` are Mathlib's points (affine solutions plus `0`). -/
def fvpEquivPoint [W.IsElliptic] :
    fieldValuedPoints (projectionOf W) K ≃ (W.baseChange K).toAffine.Point :=
  (Equiv.sumCompl fun g => fvpPt W K g ∈ chartOpen W).symm.trans <|
    (Equiv.sumCongr ((fvpChartEquiv W K).trans ((chartAlgHomEquiv W K).trans
        (equationEquivNonsingular W K))) (Equiv.ofUnique _ PUnit.{u + 1})).trans <|
      (Equiv.optionEquivSumPUnit _).symm.trans
        ((W.baseChange K).toAffine.nonsingularPointEquiv.symm)

/-- `#E(K) = #W(K)`. -/
theorem natCard_fieldValuedPoints_projOf [W.IsElliptic] :
    Nat.card (fieldValuedPoints (projectionOf W) K) = Nat.card (W.baseChange K).toAffine.Point :=
  Nat.card_congr (fvpEquivPoint W K)

end

end RamanujanWeil.Ihara
