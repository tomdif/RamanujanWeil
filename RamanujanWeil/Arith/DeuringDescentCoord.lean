import RamanujanWeil.Arith.DeuringDescentLang
import RamanujanWeil.Arith.DeuringG1Coord

/-!
# A3-ord, descent: a plane cubic over `K̄` with a twisted Frobenius descends to `𝔽_q`

`docs/ARITH_DEURING_DESCENT.md` §3. Let `K = 𝔽_q`, `σ = (x ↦ x^q)` on `K̄`, and `C` a
Weierstrass curve over `K̄`.

* `substOf_mul`, **`changeMap_comp`**, `coordMap_comp`: the isomorphisms of plane cubics of
  coordinate changes compose like the group `VariableChange` (`E_{abC} → E_{bC} → E_C` is the
  isomorphism of `ab`).
* **`exists_descent`**: let `T : E_C ⟶ E_C` be a `σ`-semilinear automorphism fixing the point at
  infinity (a "twisted Frobenius"). Then there are a Weierstrass curve `W` over `K` with
  `W.Δ ≠ 0` (if `C` is elliptic) and a pointed `K̄`-isomorphism `D : E_{W_K̄} ⟶ E_C` with
  `frobOf σ ≫ D = D ≫ T`. Proof: lift `T` through the pullback square of `E_{C^σ} → E_C` to a
  pointed `K̄`-isomorphism `E_C ≅ E_{C^σ}`, i.e. a coordinate change `γ` with `γ • C^σ = C`;
  Lang's theorem (`DeuringDescentLang`) gives `δ` with `δ^σ = δγ`, and `W_K̄ = δ • C`.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MvPolynomial
open AlgebraicGeometry.ModuliEllipticCurves AlgebraicGeometry.ModuliEllipticCurves.Weierstrass

universe u

namespace RamanujanWeil.Arith.Deuring.Descent

open RamanujanWeil.Arith.Deuring.Geom RamanujanWeil.Arith.Deuring.Geom.Coord

attribute [local instance] MvPolynomial.gradedAlgebra

section Ring

variable {R : Type u} [CommRing R]

theorem substOf_mul (a b : WeierstrassCurve.VariableChange R) :
    (substOf a).comp (substOf b) = substOf (a * b) := by
  refine MvPolynomial.algHom_ext fun i => ?_
  fin_cases i <;>
    simp [substOf, WeierstrassCurve.VariableChange.mul_def, map_add, map_mul, map_pow] <;> ring

/-- **The isomorphisms of coordinate changes compose.** -/
theorem changeMap_comp (a b : WeierstrassCurve.VariableChange R) (C : WeierstrassCurve R) :
    changeMap a (b • C) ≫ changeMap b C =
      eqToHom (congrArg projOf (mul_smul a b C).symm) ≫ changeMap (a * b) C := by
  have e : changeMap a (b • C) ≫ changeMap b C =
      Proj.map ((changeHom a (b • C)).comp (changeHom b C))
        (HomogeneousIdeal.irrelevant_le_map_comp (irrelevant_le_map_changeHom b C)
          (irrelevant_le_map_changeHom a (b • C))) :=
    (Proj.map_comp _ _ _ _).symm
  have h₁ : substGradedHom (a * b) (cubicOf C) ∈ (cubicIdealOf (a • (b • C))).toIdeal := by
    rw [← mul_smul]; exact substOf_cubicOf_mem (a * b) C
  have hf : (changeHom a (b • C)).comp (changeHom b C) = coordHom (substGradedHom (a * b)) h₁ := by
    refine GradedRingHom.ext fun x => ?_
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
    show Ideal.Quotient.mk _ (substOf a (substOf b p)) = Ideal.Quotient.mk _ (substOf (a * b) p)
    rw [← AlgHom.comp_apply, substOf_mul]
  rw [e]
  exact map_eq_eqToHom_comp_map (mul_smul a b C) (substGradedHom (a * b)) h₁
    (substOf_cubicOf_mem (a * b) C) _ (changeHom (a * b) C) hf rfl _
    (irrelevant_le_map_changeHom (a * b) C)

theorem coordMap_comp (a b : WeierstrassCurve.VariableChange R) {C₀ C₁ C₂ : WeierstrassCurve R}
    (h₁ : a • C₁ = C₂) (h₂ : b • C₀ = C₁) :
    coordMap a h₁ ≫ coordMap b h₂ = coordMap (a * b) (by rw [mul_smul, h₂, h₁]) := by
  subst h₁ h₂
  simp only [coordMap, eqToHom_refl, Category.id_comp]
  exact changeMap_comp a b C₀

/-- The twist of `E_{δ • C}` along `φ`, read through `δ`, factors through `E_{C^φ}`. -/
theorem frob_coordMap (φ : R ≃+* R) (δ γ : WeierstrassCurve.VariableChange R)
    {C : WeierstrassCurve R} (hγ : γ • C.map (φ : R →+* R) = C)
    (hδ : δ.map (φ : R →+* R) = δ * γ) {C₂ : WeierstrassCurve R} (h : δ • C = C₂)
    (h₂ : C₂.map (φ : R →+* R) = C₂) :
    frobOf φ C₂ h₂ ≫ coordMap δ h = coordMap δ h ≫ coordMap γ hγ ≫ mapMap C (φ : R →+* R) := by
  subst h
  rw [← Category.assoc, coordMap_comp]
  have hδ' : (δ.map (φ : R →+* R)) • C.map (φ : R →+* R) = δ • C := by
    rw [WeierstrassCurve.map_variableChange]
    exact h₂
  rw [coordMap_congr _ hδ' hδ.symm]
  simp only [frobOf, coordMap, eqToHom_refl, Category.id_comp, Category.assoc]
  rw [mapMap_changeMap]
  simp only [eqToHom_trans_assoc]

end Ring

section Finite

variable {K : Type u} [Field K] [Fintype K]

local notation "K̄" => AlgebraicClosure K


/-- `σ = x ↦ x^q` as a ring automorphism of `K̄`. -/
noncomputable abbrev σq (K : Type u) [Field K] [Fintype K] :
    AlgebraicClosure K ≃+* AlgebraicClosure K := (frobAlg K).toRingEquiv

local notation "φq" => ((σq K : AlgebraicClosure K ≃+* AlgebraicClosure K) :
  AlgebraicClosure K →+* AlgebraicClosure K)

/-- **Descent of a plane cubic with a twisted Frobenius.** -/
theorem exists_descent (C : WeierstrassCurve K̄) [C.IsElliptic] (T : projOf C ⟶ projOf C) [IsIso T]
    (hT : T ≫ projectionOf C =
      projectionOf C ≫ Spec.map (CommRingCat.ofHom φq))
    (hz : zeroOf C ≫ T =
      Spec.map (CommRingCat.ofHom φq) ≫ zeroOf C) :
    ∃ (W : WeierstrassCurve K) (_ : W.Δ ≠ 0) (D : FamilyIso (familyOf (W.map (algebraMap K K̄)))
      (familyOf C)),
      frobOf (σq K) _ (map_frobAlg W) ≫ D.iso.hom = D.iso.hom ≫ T := by
  have hpb := isPullback_mapMap C φq
  have := isIso_mapMap C (σq K)
  let T' : projOf C ⟶ projOf (C.map φq) := hpb.lift T (projectionOf C) hT
  have hT'1 : T' ≫ mapMap C  φq = T := hpb.lift_fst _ _ _
  have hT'2 : T' ≫ projectionOf (C.map φq) = projectionOf C := hpb.lift_snd _ _ _
  have hT'eq : T' = T ≫ inv (mapMap C φq) := by rw [← hT'1, Category.assoc, IsIso.hom_inv_id,
    Category.comp_id]
  have : IsIso T' := by rw [hT'eq]; infer_instance
  have hz' : zeroOf C ≫ T' = zeroOf (C.map φq) := by
    apply hpb.hom_ext
    · rw [Category.assoc, hT'1, hz, zeroOf_mapMap]
    · rw [Category.assoc, hT'2, zeroOf_projectionOf, zeroOf_projectionOf]
  let α : FamilyIso (familyOf C) (familyOf (C.map φq)) :=
    { iso := @asIso _ _ _ _ T' this
      iso_map := hT'2
      zero_iso := hz' }
  have hφQ : φq = Descent.frobQ := frobAlg_toRingHom
  let γ := (familyIsoEquiv (C.map φq) C α).1
  have hγ : γ • C.map  φq = C := (familyIsoEquiv (C.map φq) C α).2
  have hαγ : T' = coordMap γ hγ := familyIsoEquiv_hom (C.map φq) C α
  have hγQ : γ • C.map Descent.frobQ = C := by rw [← hφQ]; exact hγ
  obtain ⟨δ, hδ, hfix⟩ := exists_frobFixed_smul C γ hγQ
  obtain ⟨W, hW⟩ := exists_map_eq_of_map_frobQ_eq (δ • C) hfix
  have hδφ : δ.map  φq = δ * γ := by rw [hφQ]; exact hδ
  refine ⟨W, ?_, familyIsoOfVariableChange δ hW.symm, ?_⟩
  · intro h0
    have h1 : (W.map (algebraMap K K̄)).Δ = 0 := by rw [WeierstrassCurve.map_Δ, h0, map_zero]
    rw [hW, WeierstrassCurve.variableChange_Δ] at h1
    exact (mul_ne_zero (pow_ne_zero _ (Units.ne_zero _)) C.isUnit_Δ.ne_zero) h1
  · show frobOf (σq K) _ (map_frobAlg W) ≫ coordMap δ hW.symm = coordMap δ hW.symm ≫ T
    rw [frob_coordMap (σq K) δ γ hγ hδφ hW.symm (map_frobAlg W), ← hαγ, hT'1]

end Finite

end RamanujanWeil.Arith.Deuring.Descent
