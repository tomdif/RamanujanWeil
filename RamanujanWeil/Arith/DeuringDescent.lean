import RamanujanWeil.Arith.DeuringDescentTwist
import RamanujanWeil.Arith.DeuringDescentCoord
import RamanujanWeil.Arith.DeuringG5Surj
import RamanujanWeil.Arith.DeuringG1Frob

/-!
# A3-ord, G5: Weierstrass descent of quotients of Frobenius Jacobians

`docs/ARITH_DEURING_DESCENT.md`. This file proves the named Prop `G5.WeierstrassDescent K` of
`DeuringG5Surj` from one geometric input, the named Prop

* `WeierstrassModel k`: a one-dimensional abelian variety over an algebraically closed field `k`
  is, as a pointed `k`-scheme, the plane cubic of an elliptic Weierstrass curve over `k`

(Riemann–Roch on a genus-one curve; Stacks' `exists_familyIso_familyOf`).

Route (`K = 𝔽_q`, `K̄` its algebraic closure, `F = Fq K` the `q`-power Frobenius of `Spec K̄`):

1. On `J₀ = J_{W₀}` the twisted Frobenius `Ψ_{W₀}` transports through `aj` to a semilinear
   automorphism `ΨJ` with `π₀ ≫ ΨJ = ΨJ ≫ π₀ = F_{J₀}` (absolute Frobenius) (`ΨJ_*`).
2. `ΨJ` descends to a semilinear automorphism `ΨB` of `B = J₀/Γ` (`DeuringDescentTwist`,
   via the universal property of `G` and rigidity), with `π_B ≫ ΨB = F_B`.
3. In a Weierstrass model `ρ : E_C ≅ B`, `ΨB` becomes a twisted Frobenius `T` of `E_C`; Lang's
   theorem descends `(E_C, T)` to `(E_W, Ψ_W)` for a Weierstrass curve `W / 𝔽_q`
   (`DeuringDescentCoord.exists_descent`).
4. For every Jacobian site `S` of `W`, `e = aj_S⁻¹ ≫ ε : J_{W,S} ≅ B` is pointed, hence a
   homomorphism by rigidity (`DeuringDescentRigid`), and `π`-equivariant by G1.1′. No comparison
   of sites is needed.
5. `traceOfFrob W = traceOfFrob W₀`: both quadratic relations hold for `π₀` modulo `Γ`, so
   `(t₀ − t_W) n π₀ = 0`, and `deg π₀ = q ≠ 0`.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory
  CartesianMonoidalCategory MonObj
open AlgebraicGeometry.ModuliEllipticCurves AlgebraicGeometry.ModuliEllipticCurves.Weierstrass
open scoped CategoryTheory.MonObj

universe u

noncomputable section

namespace RamanujanWeil.Arith.Deuring.Descent

open RamanujanWeil.Arith.Deuring.Geom RamanujanWeil.Arith.Deuring.Geom.Jac
  RamanujanWeil.Arith.Deuring.Geom.G7 RamanujanWeil.Arith.Deuring.Geom.Coord
  RamanujanWeil.Ihara Stacks.Frobenius Stacks.Groupoids

/-- **The Weierstrass model of a one-dimensional abelian variety (named input).** -/
def WeierstrassModel (k : Type u) [Field k] : Prop :=
  ∀ (B : Over (Spec (.of k))) [GrpObj B] [AlgebraicGeometry.IsAbelianVariety k B],
    abelianVarietyDimension B = 1 →
    ∃ (C : WeierstrassCurve k) (_ : C.IsElliptic) (ρ : projOf C ≅ B.left),
      ρ.hom ≫ B.hom = projectionOf C ∧ zeroOf C ≫ ρ.hom = η[B].left

theorem isInChar_of_hom {X Y : Scheme.{u}} (f : X ⟶ Y) {p : ℕ} (hY : IsInCharacteristic Y p) :
    IsInCharacteristic X p := by
  show (p : Γ(X, ⊤)) = 0
  have : f.appTop.hom (p : Γ(Y, ⊤)) = f.appTop.hom 0 := congrArg _ hY
  rwa [map_natCast, map_zero] at this

attribute [local instance] RamanujanWeil.Ihara.fact_ringChar_prime

variable {K : Type u} [Field K] [Fintype K]

local notation "K̄" => AlgebraicClosure K

/-- The `q`-power Frobenius of `Spec K̄`. -/
abbrev Fq (K : Type u) [Field K] [Fintype K] :
    Spec (.of (AlgebraicClosure K)) ⟶ Spec (.of (AlgebraicClosure K)) :=
  absoluteFrobeniusPow (Spec (.of (AlgebraicClosure K))) (ringChar K) JacSite.specIsInChar
    (cardExp K)

theorem specMap_σq :
    Spec.map (CommRingCat.ofHom ((σq K : K̄ ≃+* K̄) : K̄ →+* K̄)) = Fq K :=
  specMap_eq_absoluteFrobeniusPow _ _ _ _ fun a => by
    show (frobAlg K) a = _
    rw [FiniteField.coe_frobeniusAlgEquivOfAlgebraic, card_eq_ringChar_pow]

instance isIso_Fq : IsIso (Fq K) := by
  rw [← specMap_σq]
  have : IsIso (CommRingCat.ofHom ((σq K : K̄ ≃+* K̄) : K̄ →+* K̄)) :=
    (σq K).toCommRingCatIso.isIso_hom
  infer_instance

/-- The absolute Frobenius of a `K̄`-scheme. -/
abbrev FX (X : Over (Spec (.of K̄))) : X.left ⟶ X.left :=
  absoluteFrobeniusPow X.left (ringChar K) (isInChar_of_hom X.hom JacSite.specIsInChar)
    (cardExp K)

theorem FX_nat {X Y : Over (Spec (.of K̄))} (f : X.left ⟶ Y.left) :
    FX X ≫ f = f ≫ FX Y :=
  absoluteFrobeniusPow_naturality f _ _ _ _

theorem Fq_point {X : Over (Spec (.of K̄))} (x : Pt X) : Fq K ≫ x.left = x.left ≫ FX X :=
  absoluteFrobeniusPow_naturality x.left _ _ _ _

/-! ### 1. The twisted Frobenius of a concrete Jacobian -/

section Jacobian

variable {W : WeierstrassCurve K} [W.IsElliptic] (S : JacSite W)

/-- `ΨJ = aj⁻¹ ≫ Ψ_W ≫ aj`, a semilinear automorphism of `J_W`. -/
def ΨJ : S.J.left ⟶ S.J.left := (inv S.aj).left ≫ (JacSite.Ψ (W := W)).hom ≫ S.aj.left

theorem aj_inv_left : S.aj.left ≫ (inv S.aj).left = 𝟙 _ := by
  rw [← Over.comp_left, IsIso.hom_inv_id]; rfl

theorem inv_aj_left : (inv S.aj).left ≫ S.aj.left = 𝟙 _ := by
  rw [← Over.comp_left, IsIso.inv_hom_id]; rfl

instance isIso_ΨJ : IsIso (ΨJ S) :=
  ⟨⟨(inv S.aj).left ≫ (JacSite.Ψ (W := W)).inv ≫ S.aj.left, by
    simp only [ΨJ, Category.assoc]
    rw [reassoc_of% (aj_inv_left S), Iso.hom_inv_id_assoc, inv_aj_left], by
    simp only [ΨJ, Category.assoc]
    rw [reassoc_of% (aj_inv_left S), Iso.inv_hom_id_assoc, inv_aj_left]⟩⟩

theorem ΨJ_hom : ΨJ S ≫ S.J.hom = S.J.hom ≫ Fq K := by
  have h1 : S.aj.left ≫ S.J.hom = gw W := Over.w S.aj
  have h2 : (inv S.aj).left ≫ gw W = S.J.hom := Over.w (inv S.aj)
  simp only [ΨJ, Category.assoc]
  rw [h1, twist_comp_gw W, reassoc_of% h2]

theorem π_ΨJ : S.π.left ≫ ΨJ S = FX S.J := by
  have hπ : S.π.left = (inv S.aj).left ≫ geomFrob W ≫ S.aj.left := by
    rw [S.π_eq]; rfl
  rw [hπ, ΨJ]
  simp only [Category.assoc]
  rw [reassoc_of% (aj_inv_left S), reassoc_of% (geomFrob_comp_twist W)]
  have := absoluteFrobeniusPow_naturality (X := Ew W) (Y := S.J.left) S.aj.left (ringChar K)
    (isInChar_Ew W)
    (isInChar_of_hom S.J.hom JacSite.specIsInChar) (cardExp K)
  rw [this, reassoc_of% (inv_aj_left S)]

theorem ΨJ_π : ΨJ S ≫ S.π.left = FX S.J := by
  have hπ : S.π.left = (inv S.aj).left ≫ geomFrob W ≫ S.aj.left := by
    rw [S.π_eq]; rfl
  rw [hπ, ΨJ]
  simp only [Category.assoc]
  rw [reassoc_of% (aj_inv_left S), reassoc_of% (twist_comp_geomFrob W)]
  have := absoluteFrobeniusPow_naturality (X := Ew W) (Y := S.J.left) S.aj.left (ringChar K)
    (isInChar_Ew W)
    (isInChar_of_hom S.J.hom JacSite.specIsInChar) (cardExp K)
  rw [this, reassoc_of% (inv_aj_left S)]

theorem η_ΨJ : η[S.J].left ≫ ΨJ S = Fq K ≫ η[S.J].left := by
  have h0 : η[S.J].left ≫ (inv S.aj).left = Jac.zeroPt W := by
    rw [← S.zeroO_comp_aj, Over.comp_left, Category.assoc, aj_inv_left, Category.comp_id]
    exact S.zeroO_left
  have h1 : Jac.zeroPt W ≫ S.aj.left = η[S.J].left :=
    (congrArg (· ≫ S.aj.left) S.zeroO_left).symm.trans
      (by rw [← Over.comp_left, S.zeroO_comp_aj])
  rw [ΨJ, reassoc_of% h0, ← h1, reassoc_of% (zeroPt_comp_twist W)]

end Jacobian

/-! ### 2. The twisted Frobenius of the quotient -/

section Quotient

variable {W₀ : WeierstrassCurve K} [W₀.IsElliptic] (S₀ : JacSite W₀)
  {Γ : Subgroup (Pt S₀.J)} [Finite Γ] (hπΓ : ∀ x ∈ Γ, x ≫ S₀.π ∈ Γ) (G : Glue Γ)

include hπΓ in
theorem exists_ΨB :
    ∃ ψB : G.B.left ≅ G.B.left, ψB.hom ≫ G.B.hom = G.B.hom ≫ Fq K ∧
      G.q.left ≫ ψB.hom = ΨJ S₀ ≫ G.q.left := by
  have hΓ' : ∀ x ∈ Γ, ∃ y ∈ Γ, x.left ≫ inv (ΨJ S₀) = inv (Fq K) ≫ y.left := by
    intro x hx
    refine ⟨x ≫ S₀.π, hπΓ x hx, ?_⟩
    rw [IsIso.comp_inv_eq, Category.assoc, IsIso.eq_inv_comp, Over.comp_left, Category.assoc,
      π_ΨJ, Fq_point]
  have hΓ : ∀ x ∈ Γ, ∃ y ∈ Γ, x.left ≫ ΨJ S₀ = Fq K ≫ y.left := by
    have := inv_mem_of_finite (inv (Fq K)) (inv (ΨJ S₀)) hΓ'
    simpa only [IsIso.inv_inv] using this
  exact exists_desc_iso (Fq K) G (ΨJ S₀) (ΨJ_hom S₀) (η_ΨJ S₀) hΓ hΓ'

variable {S₀ hπΓ G}

omit [Finite Γ] in
theorem πB_ΨB (πB : G.B ⟶ G.B) (hq : G.q ≫ πB = S₀.π ≫ G.q) (ψB : G.B.left ≅ G.B.left)
    (h2 : G.q.left ≫ ψB.hom = ΨJ S₀ ≫ G.q.left) : πB.left ≫ ψB.hom = FX G.B := by
  have := epi_q G
  rw [← cancel_epi G.q.left, ← Category.assoc, ← Over.comp_left, hq, Over.comp_left,
    Category.assoc, h2, ← Category.assoc, π_ΨJ, FX_nat]

omit [Finite Γ] in
theorem η_ΨB (ψB : G.B.left ≅ G.B.left) (h2 : G.q.left ≫ ψB.hom = ΨJ S₀ ≫ G.q.left) :
    η[G.B].left ≫ ψB.hom = Fq K ≫ η[G.B].left := by
  have h : η[G.B] = η[S₀.J] ≫ G.q := (IsMonHom.one_hom G.q).symm
  rw [h, Over.comp_left, Category.assoc, h2, ← Category.assoc, η_ΨJ, Category.assoc]

end Quotient

/-! ### 3. Descent to a Weierstrass curve over `𝔽_q` -/

section Descend

variable {W₀ : WeierstrassCurve K} [W₀.IsElliptic] {S₀ : JacSite W₀}
  {Γ : Subgroup (Pt S₀.J)} {G : Glue Γ}

/-- **The Weierstrass curve over `𝔽_q`**: given a Weierstrass model of `B`, there are `W / 𝔽_q`
and a pointed `K̄`-isomorphism `ε : E_W ≅ B` with `φ_W ≫ ε = ε ≫ π_B`. -/
theorem exists_curve (hM : WeierstrassModel K̄) (hdim : abelianVarietyDimension G.B = 1)
    (πB : G.B ⟶ G.B) (ψB : G.B.left ≅ G.B.left) (h1 : ψB.hom ≫ G.B.hom = G.B.hom ≫ Fq K)
    (hη : η[G.B].left ≫ ψB.hom = Fq K ≫ η[G.B].left) (hπ : πB.left ≫ ψB.hom = FX G.B) :
    ∃ (W : WeierstrassCurve K) (hW : W.Δ ≠ 0) (ε : Ew W ⟶ G.B.left), IsIso ε ∧
      ε ≫ G.B.hom = gw W ∧ Jac.zeroPt W ≫ ε = η[G.B].left ∧
      geomFrob W ≫ ε = ε ≫ πB.left := by
  obtain ⟨C, hC, ρ, hρ, hρz⟩ := hM G.B hdim
  let T : projOf C ⟶ projOf C := ρ.hom ≫ ψB.hom ≫ ρ.inv
  have hρ' : ρ.inv ≫ projectionOf C = G.B.hom := by rw [← hρ, Iso.inv_hom_id_assoc]
  have hρz' : η[G.B].left ≫ ρ.inv = zeroOf C := by
    rw [← hρz, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have hT : T ≫ projectionOf C =
      projectionOf C ≫ Spec.map (CommRingCat.ofHom ((σq K : K̄ ≃+* K̄) : K̄ →+* K̄)) := by
    simp only [T, Category.assoc]
    rw [hρ', h1, reassoc_of% hρ, specMap_σq]
  have hz : zeroOf C ≫ T =
      Spec.map (CommRingCat.ofHom ((σq K : K̄ ≃+* K̄) : K̄ →+* K̄)) ≫ zeroOf C := by
    simp only [T]
    rw [reassoc_of% hρz, reassoc_of% hη, hρz', specMap_σq]
  obtain ⟨W, hW, D, hD⟩ := exists_descent C T hT hz
  have : W.IsElliptic := ⟨isUnit_iff_ne_zero.mpr hW⟩
  let g : Ew W ⟶ projOf (W.map (algebraMap K K̄)) := (geomIsoHom W).hom
  let d : projOf (W.map (algebraMap K K̄)) ⟶ projOf C := D.iso.hom
  have : IsIso g := inferInstanceAs (IsIso (geomIsoHom W).hom)
  have : IsIso d := inferInstanceAs (IsIso D.iso.hom)
  let ε : Ew W ⟶ G.B.left := g ≫ d ≫ ρ.hom
  have hDm : d ≫ projectionOf C = projectionOf (W.map (algebraMap K K̄)) := D.iso_map
  have hDz : zeroOf (W.map (algebraMap K K̄)) ≫ d = zeroOf C := D.zero_iso
  have hD' : frobOf (σq K) _ (map_frobAlg W) ≫ d = d ≫ T := hD
  have hGz : Jac.zeroPt W ≫ g = zeroOf (W.map (algebraMap K K̄)) := (geomIso W).zero_iso
  have hGp : g ≫ projectionOf (W.map (algebraMap K K̄)) = gw W := geomIsoHom_projectionOf W
  have hg : (JacSite.Ψ (W := W)).hom ≫ g = g ≫ frobOf (σq K) _ (map_frobAlg W) := by
    rw [JacSite.twist_eq]; exact galoisBaseChange_comp_geomIso W
  have hΨ : (JacSite.Ψ (W := W)).hom ≫ ε = ε ≫ ψB.hom := by
    have hT' : T ≫ ρ.hom = ρ.hom ≫ ψB.hom := by
      simp only [T, Category.assoc, Iso.inv_hom_id, Category.comp_id]
    simp only [ε, Category.assoc]
    rw [reassoc_of% hg, reassoc_of% hD', hT']
  have hΨ' : (JacSite.Ψ (W := W)).inv ≫ ε = ε ≫ ψB.inv := by
    rw [Iso.inv_comp_eq, reassoc_of% hΨ, Iso.hom_inv_id, Category.comp_id]
  have hF : FX G.B ≫ ψB.inv = πB.left := by rw [← hπ, Category.assoc, Iso.hom_inv_id,
    Category.comp_id]
  refine ⟨W, hW, ε, inferInstance, ?_, ?_, ?_⟩
  · simp only [ε, Category.assoc]
    rw [hρ, hDm, hGp]
  · simp only [ε]
    rw [reassoc_of% hGz, reassoc_of% hDz, hρz]
  · rw [geomFrob_eq, Category.assoc, hΨ']
    have := absoluteFrobeniusPow_naturality (X := Ew W) (Y := G.B.left) ε (ringChar K)
      (isInChar_Ew W) (isInChar_of_hom G.B.hom JacSite.specIsInChar) (cardExp K)
    rw [reassoc_of% this, hF]

/-- **Every Jacobian site of `W` gives an equivariant group isomorphism `J_{W,S} ≅ B`.** -/
theorem exists_jacIso (πB : G.B ⟶ G.B) {W : WeierstrassCurve K} [W.IsElliptic]
    (ε : Ew W ⟶ G.B.left) [IsIso ε] (hε : ε ≫ G.B.hom = gw W)
    (hz : Jac.zeroPt W ≫ ε = η[G.B].left) (hφ : geomFrob W ≫ ε = ε ≫ πB.left)
    (S : JacSite W) : ∃ e : S.J ≅ G.B, IsMonHom e.hom ∧ e.hom ≫ πB = S.π ≫ e.hom := by
  let e : S.J ≅ G.B := (asIso S.aj).symm ≪≫ Over.isoMk (asIso ε) hε
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

/-! ### 4. The trace -/

section Trace

variable {W₀ : WeierstrassCurve K} [W₀.IsElliptic] {S₀ : JacSite W₀}
  {Γ : Subgroup (Pt S₀.J)} {G : Glue Γ}

/-- `x ≫ R(α)` for `R = X² − tX + q`, on points. -/
theorem quad_pt {X : Over (Spec (.of K̄))} [GrpObj X] [AlgebraicGeometry.IsAbelianVariety K̄ X]
    (α : X ⟶ X) [IsMonHom α] (t q : ℤ)
    (h : endPolyEval α (Polynomial.X ^ 2 - Polynomial.C t * Polynomial.X + Polynomial.C q) = 1)
    (x : Pt X) : (x ≫ α ≫ α) / (x ≫ α) ^ t * x ^ q = 1 := by
  have : IsCommMonObj X := isCommMonObj_of_isProper_of_geometricallyIntegral X
  rw [← comp_endPolyEval_quadratic, h, Hom.one_def, Hom.one_def, ← Category.assoc]
  congr 1
  exact toUnit_unique _ _

/-- **The traces agree.** -/
theorem trace_eq {W : WeierstrassCurve K} [W.IsElliptic] (S : JacSite W) (n : ℤ) (hn : n ≠ 0)
    (hΓn : ∀ h ∈ Γ, h ^ n = 1) (πB : G.B ⟶ G.B) [IsMonHom πB] (hq : G.q ≫ πB = S₀.π ≫ G.q)
    (e : S.J ≅ G.B) [IsMonHom e.hom] (he : e.hom ≫ πB = S.π ≫ e.hom) :
    traceOfFrob W = traceOfFrob W₀ := by
  have : IsCommMonObj S₀.J := isCommMonObj_of_isProper_of_geometricallyIntegral _
  set t := traceOfFrob W
  set t₀ := traceOfFrob W₀
  set q : ℤ := (Nat.card K : ℤ)
  have hB : ∀ y : Pt G.B, (y ≫ πB ≫ πB) / (y ≫ πB) ^ t * y ^ q = 1 := by
    intro y
    have h := congrArg (· ≫ e.hom) (quad_pt S.π t q S.frob_quadratic (y ≫ e.inv))
    simp only [MonObj.mul_comp, GrpObj.div_comp, GrpObj.zpow_comp, MonObj.one_comp,
      Category.assoc] at h
    rw [← he, ← reassoc_of% he] at h
    simpa only [Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id] using h
  have hq' : ∀ {Z : Over (Spec (.of K̄))} (h : G.B ⟶ Z), S₀.π ≫ G.q ≫ h = G.q ≫ πB ≫ h := by
    intro Z h; rw [← Category.assoc, ← hq, Category.assoc]
  have hmem : ∀ x : Pt S₀.J, (x ≫ S₀.π) ^ ((t₀ - t) * n) = 1 := by
    intro x
    have h0 := quad_pt S₀.π t₀ q S₀.frob_quadratic x
    have h1 : ((x ≫ S₀.π ≫ S₀.π) / (x ≫ S₀.π) ^ t * x ^ q) ≫ G.q = 1 := by
      have := hB (x ≫ G.q)
      simp only [MonObj.mul_comp, GrpObj.div_comp, GrpObj.zpow_comp, Category.assoc, hq', ← hq]
      simpa only [Category.assoc] using this
    have h2 := hΓn _ ((G.ker _).1 h1)
    have h0' : (x ≫ S₀.π ≫ S₀.π) * x ^ q = (x ≫ S₀.π) ^ t₀ := by
      rw [div_mul_eq_mul_div, div_eq_one] at h0; exact h0
    have h3 : (x ≫ S₀.π ≫ S₀.π) / (x ≫ S₀.π) ^ t * x ^ q = (x ≫ S₀.π) ^ (t₀ - t) := by
      rw [div_mul_eq_mul_div, h0', zpow_sub, div_eq_mul_inv]
    rw [zpow_mul, ← h3]
    exact h2
  set m := (t₀ - t) * n with hm
  have hg1 : S₀.π ^ m = 1 := by
    have := infinite_points (A := S₀.J) S₀.dim_J
    refine eq_one_of_infinite_pointKer S₀.dim_J _ ?_
    have : pointKer (S₀.π ^ m) = Set.univ := by
      ext x
      simp only [pointKer, Set.mem_ofPred_eq, Set.mem_univ, iff_true]
      rw [GrpObj.comp_zpow]
      exact hmem x
    rw [this]
    exact Set.infinite_univ
  have hd := endDegree_zpow_mul_zpow S₀.dim_J S₀.π m 0
  simp only [hg1, zpow_zero, _root_.mul_one, Int.cast_zero, mul_zero, zero_mul, add_zero,
    ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow] at hd
  rw [endDegree_one S₀.dim_J, S₀.endDegree_π] at hd
  have hq0 : ((Nat.card K : ℕ) : ℚ) ≠ 0 := by
    have : 0 < Nat.card K := Nat.card_pos
    exact_mod_cast this.ne'
  have hm0 : m = 0 := by
    have : ((m : ℚ)) ^ 2 = 0 := by
      have h' : (m : ℚ) ^ 2 * ((Nat.card K : ℕ) : ℚ) = 0 := by push_cast at hd ⊢; linarith
      exact (mul_eq_zero.mp h').resolve_right hq0
    exact_mod_cast pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this
  rw [hm] at hm0
  have := (mul_eq_zero.mp hm0).resolve_right hn
  linarith

end Trace

/-! ### 5. `WeierstrassDescent` -/

/-- **`WeierstrassDescent K` from the Weierstrass model of one-dimensional abelian varieties.** -/
theorem weierstrassDescent_of_model (hM : WeierstrassModel (AlgebraicClosure K)) :
    G5.WeierstrassDescent K := by
  intro W₀ _ S₀ Γ hfin hπΓ n hn hΓn G πB hπB hq
  have : Finite Γ := hfin
  have hn0 : n ≠ 0 := by rintro rfl; simp at hn
  have hdim : abelianVarietyDimension G.B = 1 := G5.GlueS.dim_B G n hΓn S₀.dim_J hn0
  obtain ⟨ψB, h1, h2⟩ := @exists_ΨB K _ _ W₀ _ S₀ Γ hfin hπΓ G
  obtain ⟨W, hW, ε, hεi, hε, hz, hφ⟩ :=
    exists_curve hM hdim πB ψB h1 (η_ΨB ψB h2) (πB_ΨB πB hq ψB h2)
  have : W.IsElliptic := ⟨isUnit_iff_ne_zero.mpr hW⟩
  refine ⟨W, hW, ?_, fun S => exists_jacIso πB ε hε hz hφ S⟩
  obtain ⟨S⟩ := nonempty_jacSite W
  obtain ⟨e, he1, he2⟩ := exists_jacIso πB ε hε hz hφ S
  exact trace_eq S n hn0 hΓn πB hq e he2

end RamanujanWeil.Arith.Deuring.Descent
