import RamanujanWeil.Arith.DeuringG7ThetaJTwist
import RamanujanWeil.Arith.DeuringWModel
import RamanujanWeil.Arith.DeuringG7PrincipalFinModel

/-!
# A3-ord, G7 Θ + J: the product case, proved

`docs/ARITH_DEURING_G7_THETAJ.md` §3. Let `(B, π_B)` carry a twist `ψ` (`IsTwist`), such that
**every endomorphism of `B` is defined over `𝔽_q`**: `α ≫ ψ = ψ ≫ α` (`FrobDefined`). Then:

* `comm_π_of_frobDefined`: `π_B` is central in `End(B)`
  (`α π ψ = α F = F α = π ψ α = π α ψ`, and `ψ` is invertible).
* **`exists_factor_model`**: a direct factor `C` of `B` (`j : C → B`, `p : B → C`, `j ≫ p = 𝟙`),
  with `dim C = 1`, is `(J_W, π_W)` for a Weierstrass curve `W / 𝔽_q`. The idempotent `p ≫ j`
  commutes with `π_B` and `ψ`, so `ψ` restricts to a twist `j ≫ ψ ≫ p` of
  `(C, j ≫ π_B ≫ p)`. Then the descent of `DeuringDescent` applies (`exists_curve'` and
  `exists_jacIso'` are its steps 3–4, restated for any one-dimensional abelian variety in place of
  a quotient `G.B`), with the Weierstrass model `WModel.weierstrassModel` (proved).
* **`prodJacModel_of_prodIso`**: a group isomorphism `B ≅ C₁ ⊗ C₂` with `dim C_i = 1` gives a
  `ProdJacModel K B π_B`. Centrality forces `π_B` to be diagonal, so no swap case arises.

This is the whole product branch of `ThetaJacobianModel`. Only the theta-divisor dichotomy itself
(`DeuringG7ThetaJ.ThetaDichotomy`) and `FrobDefined` (`FrobeniusDefined`) remain upstream.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory
  CartesianMonoidalCategory MonObj
open AlgebraicGeometry.ModuliEllipticCurves AlgebraicGeometry.ModuliEllipticCurves.Weierstrass
open scoped CategoryTheory.MonObj

universe u

noncomputable section

namespace RamanujanWeil.Arith.Deuring.Geom.G7.ThetaJ

open RamanujanWeil.Arith.Deuring.Geom RamanujanWeil.Arith.Deuring.Geom.Jac
  RamanujanWeil.Arith.Deuring.Geom.G7 RamanujanWeil.Arith.Deuring.Geom.Coord RamanujanWeil.Ihara
  RamanujanWeil.Arith.Deuring.Descent Stacks.Frobenius Stacks.Groupoids

attribute [local instance] RamanujanWeil.Ihara.fact_ringChar_prime

variable {K : Type u} [Field K] [Fintype K]

/-- **All endomorphisms of `B` are defined over `𝔽_q`**: they commute with the twist `ψ`. -/
def FrobDefined (B : Over (Spec (.of (AlgebraicClosure K)))) [GrpObj B] (ψ : B.left ≅ B.left) : Prop :=
  ∀ α : B ⟶ B, IsMonHom α → α.left ≫ ψ.hom = ψ.hom ≫ α.left

/-! ### Descent of a one-dimensional abelian variety with a twist (steps 3–4 of `Descent`) -/

section Descend

variable {X : Over (Spec (.of (AlgebraicClosure K)))} [GrpObj X] [AlgebraicGeometry.IsAbelianVariety (AlgebraicClosure K) X]

/-- `Descent.exists_curve` for any one-dimensional abelian variety `X` with a twist. -/
theorem exists_curve' (hM : WeierstrassModel (AlgebraicClosure K)) (hdim : abelianVarietyDimension X = 1)
    (πX : X ⟶ X) (ψB : X.left ≅ X.left) (h1 : ψB.hom ≫ X.hom = X.hom ≫ Fq K)
    (hη : η[X].left ≫ ψB.hom = Fq K ≫ η[X].left) (hπ : πX.left ≫ ψB.hom = FX X) :
    ∃ (W : WeierstrassCurve K) (hW : W.Δ ≠ 0) (ε : Ew W ⟶ X.left), IsIso ε ∧
      ε ≫ X.hom = gw W ∧ Jac.zeroPt W ≫ ε = η[X].left ∧
      geomFrob W ≫ ε = ε ≫ πX.left := by
  obtain ⟨C, hC, ρ, hρ, hρz⟩ := hM X hdim
  let T : projOf C ⟶ projOf C := ρ.hom ≫ ψB.hom ≫ ρ.inv
  have hρ' : ρ.inv ≫ projectionOf C = X.hom := by rw [← hρ, Iso.inv_hom_id_assoc]
  have hρz' : η[X].left ≫ ρ.inv = zeroOf C := by
    rw [← hρz, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have hT : T ≫ projectionOf C =
      projectionOf C ≫ Spec.map (CommRingCat.ofHom ((σq K : (AlgebraicClosure K) ≃+* (AlgebraicClosure K)) : (AlgebraicClosure K) →+* (AlgebraicClosure K))) := by
    simp only [T, Category.assoc]
    rw [hρ', h1, reassoc_of% hρ, specMap_σq]
  have hz : zeroOf C ≫ T =
      Spec.map (CommRingCat.ofHom ((σq K : (AlgebraicClosure K) ≃+* (AlgebraicClosure K)) : (AlgebraicClosure K) →+* (AlgebraicClosure K))) ≫ zeroOf C := by
    simp only [T]
    rw [reassoc_of% hρz, reassoc_of% hη, hρz', specMap_σq]
  obtain ⟨W, hW, D, hD⟩ := exists_descent C T hT hz
  have : W.IsElliptic := ⟨isUnit_iff_ne_zero.mpr hW⟩
  let g : Ew W ⟶ projOf (W.map (algebraMap K (AlgebraicClosure K))) := (geomIsoHom W).hom
  let d : projOf (W.map (algebraMap K (AlgebraicClosure K))) ⟶ projOf C := D.iso.hom
  have : IsIso g := inferInstanceAs (IsIso (geomIsoHom W).hom)
  have : IsIso d := inferInstanceAs (IsIso D.iso.hom)
  let ε : Ew W ⟶ X.left := g ≫ d ≫ ρ.hom
  have hDm : d ≫ projectionOf C = projectionOf (W.map (algebraMap K (AlgebraicClosure K))) := D.iso_map
  have hDz : zeroOf (W.map (algebraMap K (AlgebraicClosure K))) ≫ d = zeroOf C := D.zero_iso
  have hD' : frobOf (σq K) _ (map_frobAlg W) ≫ d = d ≫ T := hD
  have hGz : Jac.zeroPt W ≫ g = zeroOf (W.map (algebraMap K (AlgebraicClosure K))) := (geomIso W).zero_iso
  have hGp : g ≫ projectionOf (W.map (algebraMap K (AlgebraicClosure K))) = gw W := geomIsoHom_projectionOf W
  have hg : (JacSite.Ψ (W := W)).hom ≫ g = g ≫ frobOf (σq K) _ (map_frobAlg W) := by
    rw [JacSite.twist_eq]; exact galoisBaseChange_comp_geomIso W
  have hΨ : (JacSite.Ψ (W := W)).hom ≫ ε = ε ≫ ψB.hom := by
    have hT' : T ≫ ρ.hom = ρ.hom ≫ ψB.hom := by
      simp only [T, Category.assoc, Iso.inv_hom_id, Category.comp_id]
    simp only [ε, Category.assoc]
    rw [reassoc_of% hg, reassoc_of% hD', hT']
  have hΨ' : (JacSite.Ψ (W := W)).inv ≫ ε = ε ≫ ψB.inv := by
    rw [Iso.inv_comp_eq, reassoc_of% hΨ, Iso.hom_inv_id, Category.comp_id]
  have hF : FX X ≫ ψB.inv = πX.left := by rw [← hπ, Category.assoc, Iso.hom_inv_id,
    Category.comp_id]
  refine ⟨W, hW, ε, inferInstance, ?_, ?_, ?_⟩
  · simp only [ε, Category.assoc]
    rw [hρ, hDm, hGp]
  · simp only [ε]
    rw [reassoc_of% hGz, reassoc_of% hDz, hρz]
  · rw [geomFrob_eq, Category.assoc, hΨ']
    have := absoluteFrobeniusPow_naturality (X := Ew W) (Y := X.left) ε (ringChar K)
      (isInChar_Ew W) (isInChar_of_hom X.hom JacSite.specIsInChar) (cardExp K)
    rw [reassoc_of% this, hF]

/-- `Descent.exists_jacIso` for any `X`. -/
theorem exists_jacIso' (πX : X ⟶ X) {W : WeierstrassCurve K} [W.IsElliptic]
    (ε : Ew W ⟶ X.left) [IsIso ε] (hε : ε ≫ X.hom = gw W)
    (hz : Jac.zeroPt W ≫ ε = η[X].left) (hφ : geomFrob W ≫ ε = ε ≫ πX.left)
    (S : JacSite W) : ∃ e : S.J ≅ X, IsMonHom e.hom ∧ e.hom ≫ πX = S.π ≫ e.hom := by
  let e : S.J ≅ X := (asIso S.aj).symm ≪≫ Over.isoMk (asIso ε) hε
  have he : e.hom.left = (inv S.aj).left ≫ ε := rfl
  have h0 : η[S.J].left ≫ (inv S.aj).left = Jac.zeroPt W := by
    rw [← S.zeroO_comp_aj, Over.comp_left, Category.assoc, aj_inv_left, Category.comp_id]
    exact S.zeroO_left
  refine ⟨e, ?_, ?_⟩
  · refine isMonHom_of_pointed' _ ?_
    ext1
    rw [Over.comp_left, he, reassoc_of% h0, hz]
  · ext1
    have hπ : S.π.left = (inv S.aj).left ≫ geomFrob W ≫ S.aj.left := by
      rw [S.π_eq]; rfl
    rw [Over.comp_left, Over.comp_left, he, hπ]
    simp only [Category.assoc]
    rw [reassoc_of% (aj_inv_left S), hφ]

end Descend

/-! ### Direct factors -/

section Factor

variable {B : Over (Spec (.of (AlgebraicClosure K)))} [GrpObj B] {πB : B ⟶ B} [IsMonHom πB]
  {ψ : B.left ≅ B.left}

/-- **`π_B` is central** when every endomorphism is defined over `𝔽_q`. -/
theorem comm_π_of_frobDefined (hψ : IsTwist πB ψ) (hdef : FrobDefined B ψ) (α : B ⟶ B)
    [IsMonHom α] : α ≫ πB = πB ≫ α := by
  ext1
  rw [Over.comp_left, Over.comp_left, ← cancel_mono ψ.hom, Category.assoc, hψ.π_ψ,
    Category.assoc, hdef α inferInstance, ← Category.assoc, hψ.π_ψ, FX_nat]

theorem frobDefined_inv (hdef : FrobDefined B ψ) (α : B ⟶ B) [IsMonHom α] :
    α.left ≫ ψ.inv = ψ.inv ≫ α.left := by
  rw [Iso.eq_inv_comp, ← Category.assoc, ← hdef α inferInstance, Category.assoc,
    Iso.hom_inv_id, Category.comp_id]

variable {C : Over (Spec (.of (AlgebraicClosure K)))} [GrpObj C] [AlgebraicGeometry.IsAbelianVariety (AlgebraicClosure K) C]
  (j : C ⟶ B) (p : B ⟶ C) [IsMonHom j] [IsMonHom p]

/-- The restriction `j ≫ ψ ≫ p` of the twist to a direct factor. -/
def factorTwist (hjp : j ≫ p = 𝟙 C) (hdef : FrobDefined B ψ) : C.left ≅ C.left where
  hom := j.left ≫ ψ.hom ≫ p.left
  inv := j.left ≫ ψ.inv ≫ p.left
  hom_inv_id := by
    have hjp' : j.left ≫ p.left = 𝟙 _ := by rw [← Over.comp_left, hjp]; rfl
    have h := hdef (p ≫ j) inferInstance
    rw [Over.comp_left] at h
    simp only [Category.assoc]
    rw [← Category.assoc p.left, ← Category.assoc ψ.hom, ← h, Category.assoc,
      Iso.hom_inv_id_assoc]
    simp only [Category.assoc, reassoc_of% hjp', Category.id_comp, hjp']
  inv_hom_id := by
    have hjp' : j.left ≫ p.left = 𝟙 _ := by rw [← Over.comp_left, hjp]; rfl
    have h := frobDefined_inv hdef (p ≫ j)
    rw [Over.comp_left] at h
    simp only [Category.assoc]
    rw [← Category.assoc p.left, ← Category.assoc ψ.inv, ← h, Category.assoc,
      Iso.inv_hom_id_assoc]
    simp only [Category.assoc, reassoc_of% hjp', Category.id_comp, hjp']

/-- The induced Frobenius `j ≫ π_B ≫ p` of the factor. -/
abbrev factorπ : C ⟶ C := j ≫ πB ≫ p

theorem p_factorπ (hjp : j ≫ p = 𝟙 C) (hψ : IsTwist πB ψ) (hdef : FrobDefined B ψ) :
    p ≫ factorπ (πB := πB) j p = πB ≫ p := by
  have hc := comm_π_of_frobDefined hψ hdef (p ≫ j)
  calc p ≫ j ≫ πB ≫ p = ((p ≫ j) ≫ πB) ≫ p := by simp only [Category.assoc]
    _ = (πB ≫ p ≫ j) ≫ p := by rw [hc]
    _ = πB ≫ p := by rw [Category.assoc, Category.assoc, hjp, Category.comp_id]

theorem isTwist_factor (hjp : j ≫ p = 𝟙 C) (hψ : IsTwist πB ψ) (hdef : FrobDefined B ψ) :
    IsTwist (factorπ (πB := πB) j p) (factorTwist j p hjp hdef) where
  base := by
    change (j.left ≫ ψ.hom ≫ p.left) ≫ C.hom = C.hom ≫ Fq K
    rw [Category.assoc, Category.assoc, Over.w p, hψ.base, ← Category.assoc, Over.w j]
  one := by
    change η[C].left ≫ j.left ≫ ψ.hom ≫ p.left = Fq K ≫ η[C].left
    have hj : η[C].left ≫ j.left = η[B].left := by
      rw [← Over.comp_left, IsMonHom.one_hom]
    have hp : η[B].left ≫ p.left = η[C].left := by
      rw [← Over.comp_left, IsMonHom.one_hom]
    rw [reassoc_of% hj, reassoc_of% hψ.one, hp]
  π_ψ := by
    change (j ≫ πB ≫ p).left ≫ j.left ≫ ψ.hom ≫ p.left = FX C
    have hjp' : j.left ≫ p.left = 𝟙 _ := by rw [← Over.comp_left, hjp]; rfl
    have h1 : (j ≫ πB ≫ p).left ≫ j.left = j.left ≫ πB.left := by
      have hc := comm_π_of_frobDefined hψ hdef (p ≫ j)
      have : (j ≫ πB ≫ p ≫ j) = j ≫ πB := by
        calc
          j ≫ πB ≫ p ≫ j = j ≫ ((p ≫ j) ≫ πB) := by rw [hc]
          _ = (j ≫ p) ≫ j ≫ πB := by simp only [Category.assoc]
          _ = j ≫ πB := by rw [hjp, Category.id_comp]
      have := congrArg CommaMorphism.left this
      simpa only [Over.comp_left, Category.assoc] using this
    rw [reassoc_of% h1, reassoc_of% hψ.π_ψ, FX_nat (X := B) (Y := C) p.left,
      ← Category.assoc, hjp', Category.id_comp]
  ψ_π := by
    change (j.left ≫ ψ.hom ≫ p.left) ≫ (j ≫ πB ≫ p).left = FX C
    have hjp' : j.left ≫ p.left = 𝟙 _ := by rw [← Over.comp_left, hjp]; rfl
    have h1 : p.left ≫ (j ≫ πB ≫ p).left = πB.left ≫ p.left := by
      have := congrArg CommaMorphism.left (p_factorπ j p hjp hψ hdef)
      simpa only [Over.comp_left, Category.assoc] using this
    simp only [Category.assoc]
    rw [h1, reassoc_of% hψ.ψ_π, FX_nat (X := B) (Y := C) p.left,
      ← Category.assoc, hjp', Category.id_comp]

/-- **A one-dimensional direct factor of `B` is a Frobenius Jacobian over `𝔽_q`.** -/
theorem exists_factor_model (hjp : j ≫ p = 𝟙 C) (hψ : IsTwist πB ψ) (hdef : FrobDefined B ψ)
    (hdim : abelianVarietyDimension C = 1) :
    ∃ (W : WeierstrassCurve K) (_ : W.IsElliptic), ∀ S : JacSite W, ∃ e : S.J ≅ C,
      IsMonHom e.hom ∧ e.hom ≫ factorπ (πB := πB) j p = S.π ≫ e.hom := by
  have ht := isTwist_factor j p hjp hψ hdef
  obtain ⟨W, hW, ε, hεi, hε, hz, hφ⟩ := exists_curve' (WModel.weierstrassModel K) hdim
    (factorπ (πB := πB) j p) (factorTwist j p hjp hdef) ht.base ht.one ht.π_ψ
  have : W.IsElliptic := ⟨isUnit_iff_ne_zero.mpr hW⟩
  exact ⟨W, this, fun S => exists_jacIso' _ ε hε hz hφ S⟩

end Factor

/-! ### The product model -/

open RamanujanWeil.Arith.Deuring.Geom.G7.PrincipalFin in
/-- **The product branch of `ThetaJacobianModel`.** If every endomorphism of `(B, π_B, ψ)` is
defined over `𝔽_q` and `B ≅ C₁ ⊗ C₂` as group objects with `dim C_i = 1`, then `(B, π_B)` has a
product model `J_{W₁} × J_{W₂}`. -/
theorem prodJacModel_of_prodIso {B : Over (Spec (.of (AlgebraicClosure K)))} [GrpObj B] {πB : B ⟶ B}
    [IsMonHom πB] {ψ : B.left ≅ B.left} (hψ : IsTwist πB ψ) (hdef : FrobDefined B ψ)
    {C₁ C₂ : Over (Spec (.of (AlgebraicClosure K)))} [GrpObj C₁] [GrpObj C₂]
    [AlgebraicGeometry.IsAbelianVariety (AlgebraicClosure K) C₁] [AlgebraicGeometry.IsAbelianVariety (AlgebraicClosure K) C₂]
    (h₁ : abelianVarietyDimension C₁ = 1) (h₂ : abelianVarietyDimension C₂ = 1)
    (e : B ≅ C₁ ⊗ C₂) [IsMonHom e.hom] : Nonempty (ProdJacModel K B πB) := by
  let j₁ : C₁ ⟶ B := ι₁ ≫ e.inv
  let p₁ : B ⟶ C₁ := e.hom ≫ fst C₁ C₂
  let j₂ : C₂ ⟶ B := ι₂ ≫ e.inv
  let p₂ : B ⟶ C₂ := e.hom ≫ snd C₁ C₂
  have hjp₁ : j₁ ≫ p₁ = 𝟙 C₁ := by
    simp only [j₁, p₁, Category.assoc, Iso.inv_hom_id_assoc, ι₁, lift_fst]
  have hjp₂ : j₂ ≫ p₂ = 𝟙 C₂ := by
    simp only [j₂, p₂, Category.assoc, Iso.inv_hom_id_assoc, ι₂, lift_snd]
  obtain ⟨W₁, hW₁, hm₁⟩ := exists_factor_model j₁ p₁ hjp₁ hψ hdef h₁
  obtain ⟨W₂, hW₂, hm₂⟩ := exists_factor_model j₂ p₂ hjp₂ hψ hdef h₂
  have hp₁ := p_factorπ j₁ p₁ hjp₁ hψ hdef
  have hp₂ := p_factorπ j₂ p₂ hjp₂ hψ hdef
  refine ⟨⟨W₁, W₂, hW₁, hW₂, fun S₁ S₂ => ?_⟩⟩
  obtain ⟨e₁, he₁, hπ₁⟩ := hm₁ S₁
  obtain ⟨e₂, he₂, hπ₂⟩ := hm₂ S₂
  refine ⟨(tensorIso e₁ e₂) ≪≫ e.symm, ?_, ?_⟩
  · change IsMonHom ((e₁.hom ⊗ₘ e₂.hom) ≫ e.inv)
    infer_instance
  · change ((e₁.hom ⊗ₘ e₂.hom) ≫ e.inv) ≫ πB = (S₁.π ⊗ₘ S₂.π) ≫ (e₁.hom ⊗ₘ e₂.hom) ≫ e.inv
    rw [← cancel_mono e.hom]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    apply CartesianMonoidalCategory.hom_ext
    · have h : e.inv ≫ πB ≫ e.hom ≫ fst C₁ C₂ =
          fst C₁ C₂ ≫ factorπ (πB := πB) j₁ p₁ := by
        have hp := congrArg (fun f => e.inv ≫ f) hp₁
        simpa only [p₁, Category.assoc, Iso.inv_hom_id_assoc] using hp.symm
      simp only [Category.assoc]
      rw [h]
      simp only [Category.assoc, tensorHom_fst, tensorHom_fst_assoc, hπ₁]
    · have h : e.inv ≫ πB ≫ e.hom ≫ snd C₁ C₂ =
          snd C₁ C₂ ≫ factorπ (πB := πB) j₂ p₂ := by
        have hp := congrArg (fun f => e.inv ≫ f) hp₂
        simpa only [p₂, Category.assoc, Iso.inv_hom_id_assoc] using hp.symm
      simp only [Category.assoc]
      rw [h]
      simp only [Category.assoc, tensorHom_snd, tensorHom_snd_assoc, hπ₂]

end RamanujanWeil.Arith.Deuring.Geom.G7.ThetaJ

end
