import RamanujanWeil.Arith.DeuringWModelChi
import RamanujanWeil.Arith.DeuringG6ConstRank
import RamanujanWeil.Arith.DeuringG7Dual2
import StacksFrontier.AlgebraicGeometry.GroupScheme.AbelianVariety.TorsionDegree
import StacksFrontier.AlgebraicGeometry.Curves.InseparableFrobeniusChainAssembly
import StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.CohomologyComparison
import StacksFrontier.AlgebraicGeometry.EulerCharAdditivity.Basic

/-!
# `WeierstrassModel`, step 2: a one-dimensional abelian variety has genus one

Let `k` be algebraically closed and `A` a one-dimensional abelian variety over `k`. For a finite
subgroup `H ⊆ A(k)`, the G6 quotient `q : A ⟶ A/H` (`DeuringG6Quot`, Stacks 07S7) is finite
locally free of rank `#H` with kernel pair `H_k ×_k A`, which is the disjoint union of `#H`
copies of `A` (Stacks' `isColimit_constantGroupSchemeTensorCofan`). So `DeuringWModelChi` gives

`1 − g(A) = #H · (1 − g(A/H))`,     `A/H` again a one-dimensional abelian variety.

`A(k)[ℓ] ≅ (ℤ/ℓ)²` for primes `ℓ ≠ char k` (Stacks `nonempty_torsionBy_addEquiv_of_isUnit`), so
`#H` can be any `ℓ²`. Then:

* `g ≥ 1`: `g(A) = 0` would give `#H · (1 − g(A/H)) = 1` with `#H ≥ 4`;
* `g ≤ 1`: if `g(A) ≥ 2` then `g(A/H) ≥ 2` and `g(A) − 1 ≥ #H`, false for `#H > g(A)`.

Hence **`genus A.hom = 1`** (`genus_eq_one`), with `genus` Stacks' `dim_k H¹(A, 𝒪_A)`. Also
`h⁰(A, 𝒪_A) = 1` (`finrank_structureSheafCohomology_zero`).
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory
  CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

universe u

namespace RamanujanWeil.Arith.Deuring.WModel

open RamanujanWeil.Arith.Deuring.Geom RamanujanWeil.Arith.Deuring.Geom.G6
  RamanujanWeil.Arith.Deuring.Dual2 Stacks.Groupoids

/-! ### The summands of `H_S ×_S U` -/

section Legs

variable {S : Scheme.{u}} {H : Type u} [Group H] (U : Over S)

/-- The underlying scheme of `H_S ×_S U` is the coproduct of the summands. -/
noncomputable def legsIsColimit :
    IsColimit (Cofan.mk (constantGroupSchemeObj H S ⊗ U).left
      fun h => (constantGroupSchemeLeg U h).left) :=
  isColimitCofanMkObjOfIsColimit (Over.forget S) (fun _ : H => U) (constantGroupSchemeLeg U)
    (isColimit_constantGroupSchemeTensorCofan (G := H) U)

/-- The comparison with the canonical coproduct. -/
noncomputable def legsIso : (constantGroupSchemeObj H S ⊗ U).left ≅ ∐ fun _ : H => U.left :=
  (legsIsColimit U).coconePointUniqueUpToIso (coproductIsCoproduct _)

theorem leg_comp_legsIso (h : H) :
    (constantGroupSchemeLeg U h).left ≫ (legsIso U).hom = Sigma.ι (fun _ : H => U.left) h :=
  (legsIsColimit U).comp_coconePointUniqueUpToIso_hom (coproductIsCoproduct _) ⟨h⟩

theorem leg_eq (h : H) :
    (constantGroupSchemeLeg U h).left = Sigma.ι (fun _ : H => U.left) h ≫ (legsIso U).inv := by
  rw [← leg_comp_legsIso, Category.assoc, Iso.hom_inv_id, Category.comp_id]

instance isOpenImmersion_leg (h : H) : IsOpenImmersion (constantGroupSchemeLeg U h).left := by
  rw [leg_eq]; infer_instance

instance isClosedImmersion_leg (h : H) : IsClosedImmersion (constantGroupSchemeLeg U h).left := by
  have := isClosedImmersion_sigmaι (fun _ : H => U.left) h
  rw [leg_eq]; infer_instance

instance isAffineHom_leg (h : H) : IsAffineHom (constantGroupSchemeLeg U h).left := inferInstance

theorem leg_cover (w : (constantGroupSchemeObj H S ⊗ U).left) :
    ∃ h x, (constantGroupSchemeLeg U h).left.base x = w := by
  obtain ⟨⟨h, x⟩, hx⟩ := (sigmaMk fun _ : H => U.left).surjective ((legsIso U).hom.base w)
  refine ⟨h, x, ?_⟩
  rw [sigmaMk_mk] at hx
  rw [leg_eq, Scheme.Hom.comp_apply, hx, ← Scheme.Hom.comp_apply, Iso.hom_inv_id]
  rfl

theorem leg_disjoint :
    Pairwise fun h h' : H => Disjoint (Set.range (constantGroupSchemeLeg U h).left.base)
      (Set.range (constantGroupSchemeLeg U h').left.base) := by
  intro h h' hne
  rw [Set.disjoint_left]
  rintro _ ⟨x, rfl⟩ ⟨y, hy⟩
  have e := congrArg (legsIso U).hom.base hy
  rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, leg_comp_legsIso,
    leg_comp_legsIso] at e
  obtain ⟨rfl, -⟩ := Sigma.mk.inj_iff.mp ((sigmaι_eq_iff _ _ _ _ _).mp e)
  exact hne rfl

end Legs

/-! ### The genus formula for `A ⟶ A/H` -/

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- **`1 − g(A) = #H · (1 − g(A/H))`.** -/
theorem exists_one_sub_genus_eq_mul (A : Over (Spec (.of k))) [GrpObj A]
    [AlgebraicGeometry.IsAbelianVariety k A] (hA : abelianVarietyDimension A = 1)
    (H : Subgroup (𝟙_ (Over (Spec (.of k))) ⟶ A)) [Finite H] :
    ∃ (B : Over (Spec (.of k))) (_ : GrpObj B) (_ : AlgebraicGeometry.IsAbelianVariety k B),
      abelianVarietyDimension B = 1 ∧
      1 - (genus A.hom : ℤ) = Nat.card H * (1 - (genus B.hom : ℤ)) := by
  classical
  have : Fintype H := Fintype.ofFinite H
  have : IsCommMonObj A := isCommMonObj_of_isProper_of_geometricallyIntegral A
  let := constModObj H
  have : Stacks.Morphisms.IsFiniteLocallyFree
      (constantGroupSchemeObj H (Spec (.of k))).hom :=
    isFiniteLocallyFree_constantGroupScheme H (Spec (.of k))
  have : Stacks.Morphisms.IsFiniteLocallyFreeOfRank
      (constantGroupSchemeObj H (Spec (.of k))).hom (Nat.card H) :=
    isFiniteLocallyFreeOfRank_constantGroupScheme H (Spec (.of k))
  obtain ⟨Q⟩ := nonempty_translationQuotient (constJ H) (isTranslation_constJ H)
    (hasAffineFinitePointsInFibres_of_isProjective A.hom (isProjective_of_isAbelianVariety k A))
  have hB := Q.isAbelianVariety
  have hq := Q.isFiniteLocallyFreeOfRank_q (Nat.card H)
  -- `A/H` is one-dimensional: `[#H] = q ≫ β`
  set n : ℤ := (Nat.card H : ℤ)
  have hn : n ≠ 0 := by
    have : 0 < Nat.card H := Nat.card_pos
    omega
  have hα : ∀ h ∈ H, h ≫ ((𝟙 A : A ⟶ A) ^ n) = 1 := fun h hh => by
    rw [GrpObj.comp_zpow, Category.comp_id]
    have : (⟨h, hh⟩ : H) ^ Nat.card H = 1 := pow_card_eq_one'
    have h2 : h ^ Nat.card H = 1 := congrArg Subtype.val this
    rw [show n = ((Nat.card H : ℕ) : ℤ) from rfl, zpow_natCast, h2]
  have hjα : constJ H ≫ ((𝟙 A : A ⟶ A) ^ n) = 1 := by
    refine hom_ext_of_constantGroupSchemePoint (𝟙 _) fun h => ?_
    have e := pullback_fst_comp_eq H (𝟙 _) h
    rw [Category.comp_id] at e
    have e2 := constantGroupSchemePoint_constJ H h
    rw [MonObj.comp_one, ← Category.assoc, e, Category.assoc, Category.assoc,
      reassoc_of% e2, hα _ h.2, MonObj.comp_one]
  obtain ⟨β, hβ, hqβ⟩ := Q.exists_isMonHom_desc _ hjα
  have hNA : (𝟙 A : A ⟶ A) ^ n ≠ 1 := zpow_id_ne_one hA n hn
  have hsurjN : Surjective ((𝟙 A : A ⟶ A) ^ n).left := surjective_of_ne_one hA hA _ hNA
  have hs : Surjective β.left := by
    have : Surjective (Q.q ≫ β).left := by rw [hqβ]; exact hsurjN
    rw [Over.comp_left] at this
    exact Surjective.of_comp Q.q.left β.left
  have hdimB : abelianVarietyDimension Q.B = 1 :=
    (dim_eq_of_surjective Q.q β Q.surjective hs).symm.trans hA
  refine ⟨Q.B, inferInstance, hB, hdimB, ?_⟩
  have := isCurve_of_dim_one hA
  have := isCurve_of_dim_one hdimB
  have hnc : ¬ ∃ y : Q.B.left, ∀ x : A.left, Q.q.left.base x = y := by
    rintro ⟨y, hy⟩
    have := nontrivial_of_isCurve Q.B.hom
    obtain ⟨a, b, hab⟩ := exists_pair_ne Q.B.left
    obtain ⟨a', rfl⟩ := Q.surjective.surj a
    obtain ⟨b', rfl⟩ := Q.surjective.surj b
    exact hab ((hy a').trans (hy b').symm)
  have hcard : Fintype.card H = Nat.card H := Nat.card_eq_fintype_card.symm
  exact one_sub_genus_eq_mul k A.hom Q.B.hom Q.q.left (Over.w Q.q) (Nat.card H) Nat.card_pos
    hnc Q.isPullback.flip hcard (fun h : H => (constantGroupSchemeLeg A h).left)
    (fun h => by rw [← Over.comp_left, constantGroupSchemeLeg_snd]; rfl)
    (leg_cover A) (leg_disjoint A)

/-! ### Large finite subgroups -/

/-- A prime `ℓ` larger than `N` and the characteristic is invertible in `k`. -/
theorem exists_prime_isUnit (N : ℕ) : ∃ ℓ : ℕ, ℓ.Prime ∧ N < ℓ ∧ IsUnit (ℓ : k) := by
  obtain ⟨ℓ, hle, hℓ⟩ := Nat.exists_infinite_primes (N + ringChar k + 1)
  refine ⟨ℓ, hℓ, by omega, ?_⟩
  rw [isUnit_iff_ne_zero]
  intro h0
  rw [ringChar.spec] at h0
  rcases hℓ.eq_one_or_self_of_dvd _ h0 with h1 | h1
  · exact CharP.ringChar_ne_one h1
  · omega

/-- **Finite subgroups of `A(k)` of arbitrarily large order** (`A(k)[ℓ] ≅ (ℤ/ℓ)²`). -/
theorem exists_large_subgroup (A : Over (Spec (.of k))) [GrpObj A]
    [AlgebraicGeometry.IsAbelianVariety k A] (hA : abelianVarietyDimension A = 1) (N : ℕ) :
    ∃ H : Subgroup (𝟙_ (Over (Spec (.of k))) ⟶ A), Finite H ∧ N < Nat.card H ∧
      2 ≤ Nat.card H := by
  have : IsCommMonObj A := isCommMonObj_of_isProper_of_geometricallyIntegral A
  obtain ⟨ℓ, hℓ, hNℓ, hu⟩ := exists_prime_isUnit (k := k) N
  obtain ⟨e⟩ := nonempty_torsionBy_addEquiv_of_isUnit (k := k) A ℓ hu
  have : NeZero ℓ := ⟨hℓ.ne_zero⟩
  let T := AddSubgroup.torsionBy (Additive (𝟙_ (Over (Spec (.of k))) ⟶ A)) (ℓ : ℤ)
  let H : Subgroup (𝟙_ (Over (Spec (.of k))) ⟶ A) := Subgroup.toAddSubgroup.symm T
  have eH : H ≃ T := Equiv.subtypeEquiv Additive.ofMul fun _ => Iff.rfl
  have hT : Nat.card T = ℓ ^ 2 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_fun, Nat.card_zmod, Nat.card_eq_fintype_card,
      Fintype.card_fin, hA]
  have hH : Nat.card H = ℓ ^ 2 := (Nat.card_congr eH).trans hT
  have hfin : Finite H := Nat.finite_of_card_ne_zero (by rw [hH]; exact pow_ne_zero _ hℓ.ne_zero)
  refine ⟨H, hfin, ?_, ?_⟩
  · rw [hH]; nlinarith [hℓ.two_le]
  · rw [hH]; nlinarith [hℓ.two_le]

/-! ### The genus -/

theorem one_le_genus (A : Over (Spec (.of k))) [GrpObj A]
    [AlgebraicGeometry.IsAbelianVariety k A] (hA : abelianVarietyDimension A = 1) :
    1 ≤ genus A.hom := by
  by_contra h0
  have hg : genus A.hom = 0 := by omega
  obtain ⟨H, hfin, -, h2⟩ := exists_large_subgroup A hA 0
  obtain ⟨B, _, _, -, he⟩ := exists_one_sub_genus_eq_mul A hA H
  rw [hg, Nat.cast_zero, sub_zero] at he
  have h1 := Int.eq_one_of_mul_eq_one_right (Nat.cast_nonneg _) he.symm
  omega

/-- **A one-dimensional abelian variety over an algebraically closed field has genus one.** -/
theorem genus_eq_one (A : Over (Spec (.of k))) [GrpObj A]
    [AlgebraicGeometry.IsAbelianVariety k A] (hA : abelianVarietyDimension A = 1) :
    genus A.hom = 1 := by
  have h1 := one_le_genus A hA
  by_contra hne
  have h2 : 2 ≤ genus A.hom := by omega
  obtain ⟨H, hfin, hN, -⟩ := exists_large_subgroup A hA (genus A.hom)
  obtain ⟨B, _, _, hB, he⟩ := exists_one_sub_genus_eq_mul A hA H
  have hB1 := one_le_genus B hB
  set d : ℤ := ((Nat.card H : ℕ) : ℤ)
  set gA : ℤ := ((genus A.hom : ℕ) : ℤ)
  set gB : ℤ := ((genus B.hom : ℕ) : ℤ)
  have hd : gA < d := by simp only [d, gA]; exact_mod_cast hN
  have hgA : 2 ≤ gA := by simp only [gA]; exact_mod_cast h2
  have hgB : 1 ≤ gB := by simp only [gB]; exact_mod_cast hB1
  rcases eq_or_lt_of_le hgB with hgB1 | hgB2
  · rw [← hgB1] at he; linarith
  · nlinarith

/-- **`h⁰(A, 𝒪_A) = 1`** for an abelian variety. -/
theorem finrank_structureSheafCohomology_zero (A : Over (Spec (.of k))) [GrpObj A]
    [AlgebraicGeometry.IsAbelianVariety k A] :
    Module.finrank k (structureSheafCohomology A.hom 0) = 1 := by
  rw [(structureSheafCohomologyIsoCohomologyOverField k A.hom 0).toLinearEquiv.finrank_eq,
    finrank_cohomologyOverField_zero_unit_eq_finrank_globalSections k A.hom]
  have hiso := isIso_globalSections_of_geometricallyIntegral k A.hom
  let : Algebra k Γ(A.left, ⊤) := ((Scheme.ΓSpecIso (.of k)).inv ≫ A.hom.appTop).hom.toAlgebra
  have hb : Function.Bijective (algebraMap k Γ(A.left, ⊤)) :=
    (ConcreteCategory.isIso_iff_bijective _).1 hiso
  rw [← (LinearEquiv.ofBijective (Algebra.linearMap k Γ(A.left, ⊤)) hb).finrank_eq,
    Module.finrank_self]

end RamanujanWeil.Arith.Deuring.WModel
