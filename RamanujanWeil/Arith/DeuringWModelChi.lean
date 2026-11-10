import StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.GenusDisjointUnion
import StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.EulerCharacteristicComparison
import StacksFrontier.AlgebraicGeometry.Variety.Curve.PullbackDegree
import StacksFrontier.AlgebraicGeometry.AffineMorphismEuler.Basic
import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.ProperGlobalSections
import StacksFrontier.AlgebraicGeometry.AffineBaseChange.StructureSheaf
import StacksFrontier.AlgebraicGeometry.AffineBaseChangeIso.Reduction
import StacksFrontier.AlgebraicGeometry.AffineQcohPushforward.Basic
import StacksFrontier.AlgebraicGeometry.EulerCharIso.Basic

/-!
# `WeierstrassModel`, step 1: the Euler characteristic is multiplicative along a split cover

Let `q : A ⟶ B` be a finite locally free morphism of rank `d` between proper curves over a field
`k`, and suppose its kernel pair `W = A ×_B A` **splits**: there are `d` open (and affine)
immersions `s_i : A ⟶ W`, sections of the first projection `p`, with disjoint images covering
`W`. Then

`χ(A, 𝒪_A) = d · χ(B, 𝒪_B)`.

This is the argument of Stacks' `AlgebraicGeometry.genus_sub_one_eq_of_isGalois`
(`Curves/EtaleCoverGenus.lean`, whose module has 69 unbuilt dependencies), with the Galois
hypothesis replaced by the explicit splitting. All ingredients are prebuilt:

* `ℰ = q_* 𝒪_A` is finite locally free of rank `d`; `deg(q^* ℰ) = deg(q) · deg(ℰ)` (Tag 0AYZ,
  `curveDegree_pullback_eq_degreeOver_mul`);
* affine base change `q^* q_* 𝒪_A ≅ p_* 𝒪_W` (Tag 02KG; the definition
  `pullbackPushforwardUnitIso` of the unbuilt `AffineBaseChangeProjection` is reproduced here from
  its prebuilt ingredients);
* `𝒪_W ≅ ∏ (s_i)_* 𝒪_A` (`structureSheafDisjointCoverIso`), so `h^n(W) = d · h^n(A)`;
* so `deg(q^* ℰ) = 0`, hence `deg ℰ = 0`, i.e. `χ(B, ℰ) = d χ(B)`, while `χ(B, ℰ) = χ(A)`.

With `h⁰ = 1` on both sides this reads `1 − g_A = d (1 − g_B)` (`one_sub_genus_eq_mul`).
-/

open CategoryTheory CategoryTheory.Limits

universe u

namespace RamanujanWeil.Arith.Deuring.WModel

open AlgebraicGeometry

/-- The Euler characteristic `χ(X, 𝒪_X) = Σ (-1)ⁿ hⁿ(X, 𝒪_X)` of a scheme over a field. -/
noncomputable def chi (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) : ℤ :=
  ∑ᶠ n : ℕ, (-1 : ℤ) ^ n *
    (Module.finrank k (cohomologyOverField k f (SheafOfModules.unit X.ringCatSheaf) n) : ℤ)

/-- **Affine base change at the structure sheaf** (copy of Stacks'
`AffineBaseChangeProjection.pullbackPushforwardUnitIso`, whose module is not prebuilt): for a
cartesian square with `u` affine, `g^* u_* 𝒪_{Y'} ≅ p_* 𝒪_{X'}`. -/
noncomputable def pullbackPushforwardUnitIso {X' X Y' Y : Scheme.{u}} {p : X' ⟶ X} {f : X' ⟶ Y'}
    {g : X ⟶ Y} {u : Y' ⟶ Y} (hw : IsPullback p f g u) [IsAffineHom u] :
    (Scheme.Modules.pullback g).obj ((Scheme.Modules.pushforward u).obj
        (SheafOfModules.unit Y'.ringCatSheaf : Y'.Modules)) ≅
      (Scheme.Modules.pushforward p).obj
        (SheafOfModules.unit X'.ringCatSheaf : X'.Modules) :=
  haveI := Stacks.AlgebraicGeometry.AffineQcohPushforward.isQuasicoherent_unit Y'
  haveI := Stacks.AlgebraicGeometry.AffineBaseChangeIso.isIso_baseChangeNatTrans_of_isAffineHom
    hw.flip (SheafOfModules.unit Y'.ringCatSheaf : Y'.Modules)
  asIso ((Stacks.AlgebraicGeometry.AffinePushforward.baseChangeNatTrans hw.flip.w).app
      (SheafOfModules.unit Y'.ringCatSheaf : Y'.Modules)) ≪≫
    (Scheme.Modules.pushforward p).mapIso (Stacks.AlgebraicGeometry.AffineBaseChange.pullbackUnitIso f)

section Split

variable (k : Type u) [Field k] {A B W : Scheme.{u}} (πA : A ⟶ Spec (.of k))
  [IsProper πA] {p : W ⟶ A}
  {ι : Type u} [Fintype ι] (s : ι → (A ⟶ W)) [∀ i, IsOpenImmersion (s i)]
  [∀ i, IsAffineHom (s i)]

/-- **The cohomology of a split cover.** If `W` is the disjoint union of the images of open,
affine immersions `s_i : A ⟶ W` with `s_i ≫ p = 𝟙`, then `hⁿ(W, 𝒪) = #ι · hⁿ(A, 𝒪)`. -/
theorem finrank_cohomologyOverField_split (hs : ∀ i, s i ≫ p = 𝟙 A)
    (hcover : ∀ w : W, ∃ i x, (s i).base x = w)
    (hdisj : Pairwise fun i j ↦ Disjoint (Set.range (s i).base) (Set.range (s j).base))
    (n : ℕ) :
    Module.finrank k (cohomologyOverField k (p ≫ πA)
        (SheafOfModules.unit W.ringCatSheaf) n) =
      Fintype.card ι * Module.finrank k (cohomologyOverField k πA
        (SheafOfModules.unit A.ringCatSheaf) n) := by
  classical
  set fW := p ≫ πA
  let F : ι → W.Modules := fun i =>
    (Scheme.Modules.pushforward (s i)).obj (SheafOfModules.unit A.ringCatSheaf)
  have ecov : SheafOfModules.unit W.ringCatSheaf ≅ ∏ᶜ F :=
    structureSheafDisjointCoverIso (fun _ => A) s hcover hdisj
  have hcomp : ∀ i, s i ≫ fW = πA := fun i => by
    simp only [fW, ← Category.assoc, hs, Category.id_comp]
  have := Stacks.AlgebraicGeometry.AffineQcohPushforward.isQuasicoherent_unit A
  have hpush (i : ι) : Module.finrank k (cohomologyOverField k fW (F i) n) =
      Module.finrank k (cohomologyOverField k πA (SheafOfModules.unit A.ringCatSheaf) n) := by
    refine (finrank_cohomologyOverField_pushforward_of_isAffineHom k (s i) fW
      (SheafOfModules.unit A.ringCatSheaf) n).symm.trans ?_
    rw [hcomp]
  have hfin (i : ι) : FiniteDimensional k (cohomologyOverField k fW (F i) n) := by
    have := Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_unit k πA
    have : FiniteDimensional k (cohomologyOverField k πA
        (SheafOfModules.unit A.ringCatSheaf) n) :=
      finiteDimensional_cohomologyOverField_of_isProper k πA _ n
    have e := cohomologyOverFieldPushforwardIsoOfIsAffineHom k (s i) fW
      (SheafOfModules.unit A.ringCatSheaf) n
    rw [hcomp] at e
    exact Module.Finite.equiv e.toLinearEquiv
  calc Module.finrank k (cohomologyOverField k fW (SheafOfModules.unit W.ringCatSheaf) n)
      = Module.finrank k (cohomologyOverField k fW (∏ᶜ F) n) :=
        (cohomologyOverFieldIso k fW ecov n).toLinearEquiv.finrank_eq
    _ = ∑ i, Module.finrank k (cohomologyOverField k fW (F i) n) :=
        finrank_cohomologyOverField_pi k fW F n hfin
    _ = ∑ _i : ι, Module.finrank k (cohomologyOverField k πA
          (SheafOfModules.unit A.ringCatSheaf) n) :=
        Finset.sum_congr rfl fun i _ => hpush i
    _ = Fintype.card ι * Module.finrank k (cohomologyOverField k πA
          (SheafOfModules.unit A.ringCatSheaf) n) := by
        rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]

end Split

/-- **`χ(A) = d · χ(B)` for a split finite locally free cover of rank `d`.** -/
theorem chi_eq_mul (k : Type u) [Field k] {A B W : Scheme.{u}} (πA : A ⟶ Spec (.of k))
    (πB : B ⟶ Spec (.of k)) [IsProper πA] [IsProper πB] [IsCurve k πA] [IsCurve k πB]
    (q : A ⟶ B) (hq : q ≫ πB = πA) (d : ℕ) (hd : 0 < d)
    [hqd : Stacks.Morphisms.IsFiniteLocallyFreeOfRank q d]
    (hnc : ¬ ∃ y : B, ∀ x : A, q.base x = y)
    {p f : W ⟶ A} (hw : IsPullback p f q q)
    {ι : Type u} [Fintype ι] (hι : Fintype.card ι = d) (s : ι → (A ⟶ W))
    [∀ i, IsOpenImmersion (s i)] [∀ i, IsAffineHom (s i)]
    (hs : ∀ i, s i ≫ p = 𝟙 A)
    (hcover : ∀ w : W, ∃ i x, (s i).base x = w)
    (hdisj : Pairwise fun i j ↦ Disjoint (Set.range (s i).base) (Set.range (s j).base)) :
    chi k πA = d * chi k πB := by
  classical
  subst hq
  have : IsAffineHom p := MorphismProperty.IsStableUnderBaseChange.of_isPullback hw.flip
    inferInstance
  set E := (Scheme.Modules.pushforward q).obj (SheafOfModules.unit A.ringCatSheaf)
  have : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E d := hqd.toIsFiniteLocallyFreeOfRank
  have hdeg := (Scheme.Modules.fiberRank_eq_of_isFiniteLocallyFreeOfRank E d
    (genericPoint B)).symm.trans
    (fiberRank_pushforward_unit_genericPoint_eq_degreeOver k (q ≫ πB) πB q rfl hnc)
  have h0 := curveDegree_pullback_eq_degreeOver_mul k (q ≫ πB) πB q rfl hnc E d
  rw [← hdeg] at h0
  simp only [curveDegree] at h0
  have hpb := pullbackPushforwardUnitIso hw
  have h1 : ∀ n : ℕ, Module.finrank k (cohomologyOverField k (q ≫ πB)
      ((Scheme.Modules.pullback q).obj E) n) =
      d * Module.finrank k (cohomologyOverField k (q ≫ πB)
        (SheafOfModules.unit A.ringCatSheaf) n) := by
    intro n
    have := Stacks.AlgebraicGeometry.AffineQcohPushforward.isQuasicoherent_unit W
    refine ((cohomologyOverFieldIso k (q ≫ πB) hpb n).toLinearEquiv.finrank_eq).trans ?_
    refine (finrank_cohomologyOverField_pushforward_of_isAffineHom k p (q ≫ πB)
      (SheafOfModules.unit W.ringCatSheaf) n).symm.trans ?_
    rw [finrank_cohomologyOverField_split k (q ≫ πB) s hs hcover hdisj n, hι]
  have h2 : ∀ n : ℕ, Module.finrank k (cohomologyOverField k πB E n) =
      Module.finrank k (cohomologyOverField k (q ≫ πB)
        (SheafOfModules.unit A.ringCatSheaf) n) := by
    intro n
    have := Stacks.AlgebraicGeometry.AffineQcohPushforward.isQuasicoherent_unit A
    exact (finrank_cohomologyOverField_pushforward_of_isAffineHom k q πB _ n).symm
  simp only [h1, h2] at h0
  have hmul : (∑ᶠ n : ℕ, (-1 : ℤ) ^ n * ((d * Module.finrank k (cohomologyOverField k (q ≫ πB)
      (SheafOfModules.unit A.ringCatSheaf) n) : ℕ) : ℤ)) =
      d * ∑ᶠ n : ℕ, (-1 : ℤ) ^ n * (Module.finrank k (cohomologyOverField k (q ≫ πB)
        (SheafOfModules.unit A.ringCatSheaf) n) : ℤ) := by
    rw [mul_finsum]
    exact finsum_congr fun n => by push_cast; ring
  try simp only [Functor.id_obj] at h0
  rw [hmul, sub_self] at h0
  have hdpos : (0 : ℤ) < d := by exact_mod_cast hd
  have := h0.symm
  rcases mul_eq_zero.1 this with h | h
  · exact absurd h hdpos.ne'
  · unfold chi; linarith

/-- **`1 − g_A = d (1 − g_B)`** for a split finite locally free cover of rank `d` between proper
geometrically integral curves. -/
theorem one_sub_genus_eq_mul (k : Type u) [Field k] {A B W : Scheme.{u}} (πA : A ⟶ Spec (.of k))
    (πB : B ⟶ Spec (.of k)) [IsProper πA] [IsProper πB] [IsCurve k πA] [IsCurve k πB]
    [GeometricallyIntegral πA] [GeometricallyIntegral πB]
    (q : A ⟶ B) (hq : q ≫ πB = πA) (d : ℕ) (hd : 0 < d)
    [Stacks.Morphisms.IsFiniteLocallyFreeOfRank q d]
    (hnc : ¬ ∃ y : B, ∀ x : A, q.base x = y)
    {p f : W ⟶ A} (hw : IsPullback p f q q)
    {ι : Type u} [Fintype ι] (hι : Fintype.card ι = d) (s : ι → (A ⟶ W))
    [∀ i, IsOpenImmersion (s i)] [∀ i, IsAffineHom (s i)]
    (hs : ∀ i, s i ≫ p = 𝟙 A)
    (hcover : ∀ w : W, ∃ i x, (s i).base x = w)
    (hdisj : Pairwise fun i j ↦ Disjoint (Set.range (s i).base) (Set.range (s j).base)) :
    1 - (genus πA : ℤ) = d * (1 - (genus πB : ℤ)) := by
  have hg : ∀ (Y : Scheme.{u}) (g : Y ⟶ Spec (.of k)) [IsProper g] [GeometricallyIntegral g]
      (_hY : topologicalKrullDim Y ≤ 1), 1 - (genus g : ℤ) = chi k g := by
    intro Y g _ _ hY
    have hiso := isIso_globalSections_of_geometricallyIntegral k g
    let : Algebra k Γ(Y, ⊤) := ((Scheme.ΓSpecIso (.of k)).inv ≫ g.appTop).hom.toAlgebra
    have h1 : Module.finrank k Γ(Y, ⊤) = 1 := by
      have hb : Function.Bijective (algebraMap k Γ(Y, ⊤)) :=
        (ConcreteCategory.isIso_iff_bijective _).1 hiso
      rw [← (LinearEquiv.ofBijective (Algebra.linearMap k Γ(Y, ⊤)) hb).finrank_eq,
        Module.finrank_self]
    exact one_sub_genus_eq_eulerCharacteristic_unit k g hY h1
  rw [hg A πA (IsCurve.topologicalKrullDim_eq_one (f := πA)).le,
    hg B πB (IsCurve.topologicalKrullDim_eq_one (f := πB)).le]
  exact chi_eq_mul k πA πB q hq d hd hnc hw hι s hs hcover hdisj

end RamanujanWeil.Arith.Deuring.WModel
