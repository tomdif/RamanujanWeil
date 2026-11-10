import Mathlib.AlgebraicGeometry.Group.Abelian

/-!
# A3-ord, descent: rigidity for proper group schemes over an algebraically closed field

`docs/ARITH_DEURING_DESCENT.md` §1. Let `k` be algebraically closed and `G` a proper group scheme
over `k` with `G ×_k G` integral (e.g. an abelian variety), and `H` any separated group scheme
locally of finite type over `k`.

* **`eq_of_rigid`** (the rigidity lemma): a morphism `c : G × G ⟶ H` with `c(e, y) = e` and
  `c(x, e) = e` is constant, `c = e`. This is Mathlib's proof of
  `isCommMonObj_of_isProper_of_isIntegral_tensorObj_of_isAlgClosed` (Zariski's main theorem plus
  irreducibility of the fibres `{x} × G`), with the commutator replaced by an arbitrary `c` and
  the target `G` replaced by `H`.
* **`isMonHom_of_pointed`**: every pointed morphism `f : G ⟶ H` (`η ≫ f = η`) is a homomorphism.
  Apply `eq_of_rigid` to `c(x, y) = f(xy) · (f(x) f(y))⁻¹`.

This is the site-independent replacement of G1.2: no Picard functor is involved, so it applies to
any pointed morphism between abelian varieties, for instance from a concrete Jacobian to a G6
quotient.
-/

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.MonObj

universe u

namespace RamanujanWeil.Arith.Deuring.Descent

open AlgebraicGeometry

variable {K : Type u} [Field K]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **The rigidity lemma.** Let `G` be a proper group scheme over an algebraically closed field
with `G ×_k G` integral, and `H` a separated group scheme locally of finite type. A morphism
`c : G ⊗ G ⟶ H` with `c(e, y) = e` and `c(x, e) = e` is constantly `e`. -/
theorem eq_of_rigid [IsAlgClosed K] (G H : Over (Spec (.of K))) [IsProper G.hom]
    [IsIntegral (G ⊗ G).left] [GrpObj G] [GrpObj H] [IsSeparated H.hom]
    [LocallyOfFiniteType H.hom] (c : G ⊗ G ⟶ H)
    (h₁ : η[G] ▷ G ≫ c = toUnit _ ≫ η[H]) (h₂ : G ◁ η[G] ≫ c = toUnit _ ≫ η[H]) :
    c = toUnit _ ≫ η[H] := by
  let S := Spec (.of K)
  let point : S := IsLocalRing.closedPoint K
  have hpoint : IsClosed {point} := isClosed_discrete _
  have : Nonempty G.left := ⟨η[G].left point⟩
  have : IsProper (G ⊗ G).hom := by dsimp; infer_instance
  have : JacobsonSpace (G ⊗ G).left := LocallyOfFiniteType.jacobsonSpace (Y := Spec _) (G ⊗ G).hom
  have : Surjective G.hom := ⟨Function.surjective_to_subsingleton (α := G.left) (β := Spec _) _⟩
  have : IsProper (fst G G).left := by dsimp; infer_instance
  have : Surjective (fst G G).left := by dsimp; infer_instance
  have : IsSeparated (fst G H).left := by dsimp; infer_instance
  have : LocallyOfFiniteType (fst G H).left := by dsimp; infer_instance
  have : IsClosedImmersion ((lift η[G] η[H]).left ≫ (fst G H).left) := by
    rw [← Over.comp_left, lift_fst]; infer_instance
  have : IsClosedImmersion (lift η[G] η[H]).left := .of_comp _ (g := (fst G H).left)
  let γ : G ⊗ G ⟶ G ⊗ H := lift (fst _ _) c
  have hγfst : γ.left ≫ (fst G H).left = (fst G G).left := by
    rw [← Over.comp_left]; simp [γ]
  have : IsProper (γ.left ≫ (fst G H).left) := by rw [hγfst]; infer_instance
  have : IsProper γ.left := .of_comp _ (fst G H).left
  ext1
  have hsub : γ.left '' ((fst G G).left ⁻¹' {η[G].left point}) ⊆
      {(lift η[G] η[H]).left point} := by
    rw [Set.image_subset_iff, ← Set.sdiff_eq_empty, ← Set.not_nonempty_iff_eq_empty]
    intro hne
    obtain ⟨c₀, ⟨hc₁, hc₂⟩, hc₃⟩ := nonempty_inter_closedPoints hne <| by
      rw [Set.sdiff_eq_compl_inter, ← Set.image_singleton, ← Set.image_singleton];
      refine (IsOpen.isLocallyClosed ?_).inter (IsClosed.isLocallyClosed ?_)
      · exact (((lift η[G] η[H]).left.isClosedMap _ hpoint).preimage γ.left.continuous).isOpen_compl
      · exact (η[G].left.isClosedMap _ hpoint).preimage (fst G G).left.continuous
    obtain ⟨⟨c', hc⟩, e⟩ := (pointEquivClosedPoint (G ⊗ G).hom).surjective ⟨c₀, hc₃⟩
    obtain rfl : c' point = c₀ := congr(($e).1)
    let fc : 𝟙_ (Over S) ⟶ 𝟙_ (Over S) ⊗ G := lift (𝟙 _) (Over.homMk c' hc ≫ snd G G)
    have : c' ≫ pullback.fst G.hom G.hom = η[G].left :=
      ext_of_apply_closedPoint_eq G.hom (by simpa) (by simp) (by simpa)
    have H₁ : c' = fc.left ≫ (η[G] ▷ G).left := by dsimp; ext <;> simp [fc, S, this]
    have H₂ : fc ≫ η[G] ▷ G ≫ γ = lift η[G] η[H] := by
      ext1
      · simp [fc, γ, S]
      · simp only [γ, Category.assoc, lift_snd]
        rw [h₁, ← Category.assoc, toUnit_unique (fc ≫ toUnit _) (𝟙 _), Category.id_comp]
    exact hc₂ <| by simp [H₁, H₂, ← Scheme.Hom.comp_apply, Category.assoc, ← Over.comp_left]
  obtain ⟨U, hηU, hU⟩ := exists_finite_imageι_comp_morphismRestrict_of_finite_image_preimage
    γ.left (fst G H).left (η[G].left point) (by
      rw [hγfst]
      exact (Set.finite_singleton _).subset hsub)
  have hfin (x : U) : ((pullback.fst G.hom H.hom) ⁻¹' {x.1} ∩ Set.range ⇑γ.left).Finite := by
    refine ((((γ.left.imageι ≫ (fst G H).left) ∣_ U).finite_preimage_singleton x).image
      (Scheme.Opens.ι _ ≫ γ.left.imageι)).subset ?_
    have : U.ι ⁻¹' {x.1} = {x} := by ext; simp
    rw [← this, ← Set.preimage_comp, ← TopCat.coe_comp, ← Scheme.Hom.comp_base,
      morphismRestrict_ι, ← Category.assoc, Scheme.Hom.comp_base (_ ≫ _) (fst G H).left,
      TopCat.coe_comp, Set.preimage_comp, Set.image_preimage_eq_inter_range]
    simp only [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, Scheme.Opens.range_ι]
    dsimp
    rw [Set.image_preimage_eq_inter_range, Scheme.IdealSheafData.range_subschemeι,
      Scheme.Hom.support_ker, ← Set.inter_assoc, ← Set.preimage_inter,
      Set.singleton_inter_of_mem x.2, IsClosed.closure_eq
      (by exact γ.left.isClosedMap.isClosed_range)]
  have hxe : (fst G G ≫ (ρ_ _).inv ≫ G ◁ η[G]) ≫ γ = fst G G ≫ (ρ_ _).inv ≫ G ◁ η[H] := by
    ext1
    · simp [γ]
    · simp only [γ, Category.assoc, lift_snd, whiskerLeft_snd]
      rw [h₂]
      simp only [← Category.assoc]
      congr 1
      exact toUnit_unique _ _
  have : LocallyOfFiniteType (c.left ≫ H.hom) := by rw [Over.w]; infer_instance
  refine ext_of_apply_eq H.hom _
    ((fst G G).left ⁻¹ᵁ U).isOpen.isLocallyClosed
    (((fst G G).left ⁻¹ᵁ U).isOpen.dense ?_) ?_ ?_
  · exact .preimage ⟨_, hηU⟩ (fst G G).left.surjective
  · intro y hyU hy
    have hx : IsClosed {(fst G G).left y} := by simpa using (fst G G).left.isClosedMap _ hy
    let x : 𝟙_ _ ⟶ G := Over.homMk (pointOfClosedPoint G.hom _ hx) (by simp)
    let xs : (G ⊗ G).left := (fst G G ≫ (ρ_ _).inv ≫ G ◁ η[G]).left y
    let xe : (G ⊗ H).left := (fst G G ≫ (ρ_ _).inv ≫ G ◁ η[H]).left y
    have hfy : (fst G G).left y ∈ U := hyU
    have : γ.left y = xe := by
      refine subsingleton_image_closure_of_finite_of_isPreirreducible
        (hx.preimage (fst G G).left.continuous).isLocallyClosed ?_ γ.left.continuous
        γ.left.isClosedMap ((hfin ⟨_, hfy⟩).subset (Set.image_subset_iff.mpr fun z hz ↦
          ⟨by
            show (pullback.fst G.hom H.hom) (γ.left z) = (fst G G).left y
            have h2 : (pullback.fst G.hom H.hom) (γ.left z) = (γ.left ≫ (fst G H).left) z := rfl
            rw [h2, hγfst]
            exact hz, Set.mem_range_self _⟩)) ?_ ?_
      · let α : G ⊗ G ⟶ G ⊗ G := toUnit _ ≫ x ⊗ₘ 𝟙 _
        convert!
          ((IrreducibleSpace.isIrreducible_univ _).image α.left
              α.left.continuous.continuousOn).isPreirreducible
        rw [Over.tensorHom_left]
        simp [Set.range_comp, Scheme.Pullback.range_map, x]
      · exact ⟨y, subset_closure (by simp), rfl⟩
      · refine ⟨xs, subset_closure ?_, ?_⟩
        · simp [xs, ← Scheme.Hom.comp_apply, -Scheme.Hom.comp_base]
        · simp only [xs, xe, ← Scheme.Hom.comp_apply, ← Over.comp_left, hxe]
    convert! congr((snd G H).left $this) using 1
    · simp [γ, ← Scheme.Hom.comp_apply]
    · simp [xe, ← Scheme.Hom.comp_apply, -Scheme.Hom.comp_base]
  · simp

/-- **Pointed morphisms are homomorphisms.** Let `G` be a proper group scheme over an
algebraically closed field with `G ×_k G` integral, and `H` a separated group scheme locally of
finite type. Every `f : G ⟶ H` with `η ≫ f = η` is a homomorphism. -/
theorem isMonHom_of_pointed [IsAlgClosed K] {G H : Over (Spec (.of K))} [IsProper G.hom]
    [IsIntegral (G ⊗ G).left] [GrpObj G] [GrpObj H] [IsSeparated H.hom]
    [LocallyOfFiniteType H.hom] (f : G ⟶ H) (hf : η[G] ≫ f = η[H]) : IsMonHom f := by
  have hη : ∀ {X : Over (Spec (.of K))} (g : X ⟶ 𝟙_ _), g ≫ η[G] = 1 := by
    intro X g
    rw [Hom.one_def, toUnit_unique g (toUnit X)]
  have hone : ∀ {X : Over (Spec (.of K))}, (1 : X ⟶ G) ≫ f = 1 := by
    intro X
    rw [Hom.one_def, Hom.one_def, Category.assoc, hf]
  let c : G ⊗ G ⟶ H := (μ[G] ≫ f) * ((fst G G ≫ f) * (snd G G ≫ f))⁻¹
  have hμ : μ[G] = fst G G * snd G G := by
    rw [Hom.mul_def, lift_fst_snd, Category.id_comp]
  have hc : c = toUnit _ ≫ η[H] := by
    refine eq_of_rigid G H c ?_ ?_
    · simp only [c, hμ, comp_mul, GrpObj.comp_inv, ← Category.assoc, whiskerRight_fst,
        whiskerRight_snd]
      rw [hη, _root_.one_mul, hone, _root_.one_mul, mul_inv_cancel]
      rfl
    · simp only [c, hμ, comp_mul, GrpObj.comp_inv, ← Category.assoc, whiskerLeft_fst,
        whiskerLeft_snd]
      rw [hη, _root_.mul_one, hone, _root_.mul_one, mul_inv_cancel]
      rfl
  refine ⟨hf, ?_⟩
  have h1 : c = 1 := hc
  have h2 : μ[G] ≫ f = (fst G G ≫ f) * (snd G G ≫ f) := mul_inv_eq_one.mp h1
  rw [h2, Hom.mul_def]
  congr 1

end RamanujanWeil.Arith.Deuring.Descent
