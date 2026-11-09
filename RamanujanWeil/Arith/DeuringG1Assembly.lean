import RamanujanWeil.Arith.DeuringG1Rigid

/-!
# A3-ord, G1.4: `Ψ`-equivariant pointed isomorphisms of cubics = `π`-equivariant isomorphisms
# of Jacobians

`docs/ARITH_DEURING_G1_3.md`. For elliptic `W, W' / 𝔽_q` and a big fppf site containing
`E_W`, `E_{W'}` and `Spec K̄` (`Jac.PairSite W W'`, which always exists), with Jacobian sites
`P.left : JacSite W`, `P.right : JacSite W'`:

* **`Jac.PairSite.frobIsoEquiv`**:
  `Coord.FrobIso W W' ≃ {e : J_{W'} ≅ J_W // IsMonHom e.hom ∧ e.hom ≫ π_W = π_{W'} ≫ e.hom}`,
  `α ↦ aj'⁻¹ ≫ α ≫ aj`, inverse `e ↦ aj' ≫ e ≫ aj⁻¹`.
* **`Jac.PairSite.mem_orbit_iff_nonempty_jacIso`**: `W' ∈ VariableChange(K) • W` iff there is a
  `π`-equivariant isomorphism of group objects `J_{W'} ≅ J_W`.
* **`Jac.JacSite.card_stabilizer_eq_card_jacAut`**: `#Stab_{VariableChange K}(W)` is the
  number of `π_W`-equivariant automorphisms of the group object `J_W`.

These are the G1 inputs of `DeuringLattice.rel_iff` and `DeuringLattice.card_stab`: what
remains for those fields is the lattice side (G3–G8), i.e. identifying `π`-equivariant
isomorphisms of Jacobians with `GL₂(ℤ)`-conjugacies of the Frobenius matrices `Λ`.

Ingredients: G1.1 (`JacSite.ajIso`), G1.1′ (`JacSite.aj_comp_π`), the `Ψ`/`φ` comparison
(`Jac.twist_comm_iff_geomFrob_comm`), pointedness in `η` form (`JacSite.zeroO_comp_aj`), and G1.2
(`Rigid.isMonHom_transport`).
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
open scoped CategoryTheory.MonObj

universe u

noncomputable section

namespace RamanujanWeil.Arith.Deuring.Geom

/-- Conjugating a commutation relation by isomorphisms `aj, aj'`. -/
theorem conj_comm_iff_of_comm {C : Type*} [Category C] {A A' J J' : C} (aj : A ⟶ J) (aj' : A' ⟶ J')
    [IsIso aj] [IsIso aj'] (a : A' ⟶ A) (φ : A ⟶ A) (φ' : A' ⟶ A') (π : J ⟶ J) (π' : J' ⟶ J')
    (h : aj ≫ π = φ ≫ aj) (h' : aj' ≫ π' = φ' ≫ aj') :
    (inv aj' ≫ a ≫ aj) ≫ π = π' ≫ (inv aj' ≫ a ≫ aj) ↔ a ≫ φ = φ' ≫ a := by
  have hπ' : π' ≫ inv aj' = inv aj' ≫ φ' := by
    rw [IsIso.eq_inv_comp, reassoc_of% h', IsIso.hom_inv_id, Category.comp_id]
  have L : (inv aj' ≫ a ≫ aj) ≫ π = inv aj' ≫ (a ≫ φ) ≫ aj := by
    simp only [Category.assoc, h]
  have R : π' ≫ (inv aj' ≫ a ≫ aj) = inv aj' ≫ (φ' ≫ a) ≫ aj := by
    rw [← Category.assoc, hπ']
    simp only [Category.assoc]
  rw [L, R]
  constructor
  · intro H
    exact (cancel_mono aj).1 ((cancel_epi (inv aj')).1 H)
  · intro H
    rw [H]

namespace Jac

open AlgebraicGeometry.ModuliEllipticCurves AlgebraicGeometry.ModuliEllipticCurves.Weierstrass
open RamanujanWeil.Ihara Stacks.PicardFunctor

variable {k : Type u} [Field k] [Fintype k]

/-- A big fppf site containing `E_W`, `E_{W'}` and `Spec K̄`. -/
structure PairSite (W W' : WeierstrassCurve k) where
  /-- The site. -/
  B : BigFppfSite.{u}
  /-- It contains `E_W`. -/
  hX : B.Contains (Ew W)
  /-- It contains `E_{W'}`. -/
  hX' : B.Contains (Ew W')
  /-- It contains `Spec K̄`. -/
  hk : B.Contains (Spec (.of (AlgebraicClosure k)))

/-- Pair sites exist. -/
theorem nonempty_pairSite (W W' : WeierstrassCurve k) : Nonempty (PairSite W W') := by
  let S₀ : Set Scheme.{u} := {Ew W, Ew W', Spec (.of (AlgebraicClosure k))}
  have : Small.{u} S₀ := by dsimp [S₀]; infer_instance
  obtain ⟨B, hB⟩ := BigFppfSite.exists_containing S₀
  exact ⟨⟨B, hB _ (by simp [S₀]), hB _ (by simp [S₀]), hB _ (by simp [S₀])⟩⟩

namespace PairSite

attribute [local instance] RamanujanWeil.Ihara.fact_ringChar_prime

variable {W W' : WeierstrassCurve k} (P : PairSite W W') [W.IsElliptic] [W'.IsElliptic]

/-- The Jacobian site of `W`. -/
abbrev left : JacSite W := ⟨P.B, P.hX, P.hk⟩

/-- The Jacobian site of `W'`. -/
abbrev right : JacSite W' := ⟨P.B, P.hX', P.hk⟩

/-- `E_W ⟶ Spec K̄` in the site. -/
def fL : P.B.obj P.hX ⟶ P.B.obj P.hk := ObjectProperty.homMk (gw W)

/-- `E_{W'} ⟶ Spec K̄` in the site. -/
def fR : P.B.obj P.hX' ⟶ P.B.obj P.hk := ObjectProperty.homMk (gw W')

instance iL1 : IsCurve (AlgebraicClosure k) (P.B.inclusion.map P.fL) := P.left.isCurve_f
instance iL2 : Smooth (P.B.inclusion.map P.fL) := P.left.smooth_f
instance iL3 : IsProper (P.B.inclusion.map P.fL) := P.left.isProper_f
instance iL4 : GeometricallyIrreducible (P.B.inclusion.map P.fL) :=
  P.left.geometricallyIrreducible_f
instance iL5 : IsProjectiveVariety (AlgebraicClosure k) (P.B.inclusion.map P.fL) :=
  P.left.isProjectiveVariety_f
instance iL6 : (picardFunctor P.B P.hX P.hk P.fL).IsRepresentable := P.left.isRepresentable
instance iR1 : IsCurve (AlgebraicClosure k) (P.B.inclusion.map P.fR) := P.right.isCurve_f
instance iR2 : Smooth (P.B.inclusion.map P.fR) := P.right.smooth_f
instance iR3 : IsProper (P.B.inclusion.map P.fR) := P.right.isProper_f
instance iR4 : GeometricallyIrreducible (P.B.inclusion.map P.fR) :=
  P.right.geometricallyIrreducible_f
instance iR5 : IsProjectiveVariety (AlgebraicClosure k) (P.B.inclusion.map P.fR) :=
  P.right.isProjectiveVariety_f
instance iR6 : (picardFunctor P.B P.hX' P.hk P.fR).IsRepresentable := P.right.isRepresentable

theorem oL : zeroPt W ≫ P.B.inclusion.map P.fL = 𝟙 _ := P.left.o_comp
theorem oR : zeroPt W' ≫ P.B.inclusion.map P.fR = 𝟙 _ := P.right.o_comp
theorem gL : genus (P.B.inclusion.map P.fL) = 1 := P.left.genus_f
theorem gR : genus (P.B.inclusion.map P.fR) = 1 := P.right.genus_f
theorem ΨL : (JacSite.Ψ (W := W)).hom ≫ P.B.inclusion.map P.fL = P.B.inclusion.map P.fL ≫
    absoluteFrobeniusPow (Spec (.of (AlgebraicClosure k))) (ringChar k) JacSite.specIsInChar
      (cardExp k) := P.left.Ψ_comp
theorem ΨR : (JacSite.Ψ (W := W')).hom ≫ P.B.inclusion.map P.fR = P.B.inclusion.map P.fR ≫
    absoluteFrobeniusPow (Spec (.of (AlgebraicClosure k))) (ringChar k) JacSite.specIsInChar
      (cardExp k) := P.right.Ψ_comp

/-- `J_W` (the same object as `P.left.J`). -/
abbrev JL : Over (Spec (.of (AlgebraicClosure k))) :=
  (jacobianGrp P.B P.hX P.hk P.fL (zeroPt W) P.oL).X
/-- `J_{W'}` (the same object as `P.right.J`). -/
abbrev JR : Over (Spec (.of (AlgebraicClosure k))) :=
  (jacobianGrp P.B P.hX' P.hk P.fR (zeroPt W') P.oR).X

/-- `aj_W`. -/
abbrev ajL : curveOver P.B P.hX P.hk P.fL ⟶ P.JL := abelJacobi P.B P.hX P.hk P.fL (zeroPt W) P.oL
/-- `aj_{W'}`. -/
abbrev ajR : curveOver P.B P.hX' P.hk P.fR ⟶ P.JR :=
  abelJacobi P.B P.hX' P.hk P.fR (zeroPt W') P.oR

instance isIso_ajL : IsIso P.ajL :=
  Abel.isIso_abelJacobi_of_genus_eq_one P.B P.hX P.hk P.fL (zeroPt W) P.oL P.gL
instance isIso_ajR : IsIso P.ajR :=
  Abel.isIso_abelJacobi_of_genus_eq_one P.B P.hX' P.hk P.fR (zeroPt W') P.oR P.gR

/-- `aj_W` as an isomorphism. -/
abbrev ajLIso : curveOver P.B P.hX P.hk P.fL ≅ P.JL := @asIso _ _ _ _ P.ajL P.isIso_ajL
/-- `aj_{W'}` as an isomorphism. -/
abbrev ajRIso : curveOver P.B P.hX' P.hk P.fR ≅ P.JR := @asIso _ _ _ _ P.ajR P.isIso_ajR

/-- `π_W`. -/
abbrev πL : P.JL ⟶ P.JL :=
  jacobianFrobenius P.B P.hX P.hk P.fL (ringChar k) JacSite.specIsInChar (cardExp k)
    (JacSite.Ψ (W := W)).hom P.ΨL (zeroPt W) P.oL
/-- `π_{W'}`. -/
abbrev πR : P.JR ⟶ P.JR :=
  jacobianFrobenius P.B P.hX' P.hk P.fR (ringChar k) JacSite.specIsInChar (cardExp k)
    (JacSite.Ψ (W := W')).hom P.ΨR (zeroPt W') P.oR

/-- `φ_W` over `K̄`. -/
abbrev φL : curveOver P.B P.hX P.hk P.fL ⟶ curveOver P.B P.hX P.hk P.fL :=
  Over.homMk (geomFrob W) (geomFrob_comp_gw W)
/-- `φ_{W'}` over `K̄`. -/
abbrev φR : curveOver P.B P.hX' P.hk P.fR ⟶ curveOver P.B P.hX' P.hk P.fR :=
  Over.homMk (geomFrob W') (geomFrob_comp_gw W')

/-- G1.1′ for `W`. -/
theorem ajL_comp_πL : P.ajL ≫ P.πL = P.φL ≫ P.ajL :=
  Frob.abelJacobi_comp_jacobianFrobenius P.B P.hX P.hk P.fL (ringChar k) JacSite.specIsInChar
    (cardExp k) (JacSite.Ψ (W := W)).hom P.ΨL (zeroPt W) P.oL (geomFrob W) (geomFrob_comp_gw W)
    (isInChar_Ew W) (geomFrob_comp_twist W) (zeroPt_comp_twist W)

/-- G1.1′ for `W'`. -/
theorem ajR_comp_πR : P.ajR ≫ P.πR = P.φR ≫ P.ajR :=
  Frob.abelJacobi_comp_jacobianFrobenius P.B P.hX' P.hk P.fR (ringChar k) JacSite.specIsInChar
    (cardExp k) (JacSite.Ψ (W := W')).hom P.ΨR (zeroPt W') P.oR (geomFrob W')
    (geomFrob_comp_gw W') (isInChar_Ew W') (geomFrob_comp_twist W') (zeroPt_comp_twist W')

/-- **The `π`-equivariant isomorphisms of group objects `J_{W'} ≅ J_W`.** -/
abbrev JacIso : Type u :=
  {e : P.JR ≅ P.JL // IsMonHom e.hom ∧ e.hom ≫ P.πL = P.πR ≫ e.hom}

/-- A pointed isomorphism `E_{W'} ≅ E_W`, as a morphism of curves over `K̄`. -/
abbrev curveHom (α : Coord.FrobIso W W') :
    curveOver P.B P.hX' P.hk P.fR ⟶ curveOver P.B P.hX P.hk P.fL :=
  Over.homMk α.1.iso.hom α.1.iso_map

instance isIso_frobIso (α : Coord.FrobIso W W') :
    IsIso (C := Scheme.{u}) (X := Ew W') (Y := Ew W) α.1.iso.hom :=
  ⟨⟨α.1.iso.inv, α.1.iso.hom_inv_id, α.1.iso.inv_hom_id⟩⟩

/-- `α` as an isomorphism of curves over `K̄`. -/
def curveIsoMk (α : Coord.FrobIso W W') :
    curveOver P.B P.hX' P.hk P.fR ≅ curveOver P.B P.hX P.hk P.fL where
  hom := P.curveHom α
  inv := Over.homMk α.1.iso.inv ((Iso.inv_comp_eq α.1.iso).2 α.1.iso_map.symm)
  hom_inv_id := Over.OverMorphism.ext (by
      simp only [Over.comp_left, Over.homMk_left, Over.id_left]
      exact α.1.iso.hom_inv_id)
  inv_hom_id := Over.OverMorphism.ext (by
      simp only [Over.comp_left, Over.homMk_left, Over.id_left]
      exact α.1.iso.inv_hom_id)

/-- `α ↦ aj'⁻¹ ≫ α ≫ aj` (G1.2's `Rigid.transport`). -/
def jacHom (α : Coord.FrobIso W W') : P.JR ⟶ P.JL :=
  Rigid.transport P.B P.hX P.hX' P.hk P.fL P.fR α.1.iso.hom α.1.iso_map (zeroPt W') P.oR
    (zeroPt W) P.oL P.gR

theorem jacHom_eq (α : Coord.FrobIso W W') : P.jacHom α = inv P.ajR ≫ P.curveHom α ≫ P.ajL := by
  rw [IsIso.eq_inv_comp, jacHom]
  have h := Rigid.abelJacobi_comp_transport P.B P.hX P.hX' P.hk P.fL P.fR α.1.iso.hom
    α.1.iso_map (zeroPt W') P.oR (zeroPt W) P.oL P.gR
  convert h using 2

theorem curveIsoMk_hom (α : Coord.FrobIso W W') : (P.curveIsoMk α).hom = P.curveHom α := rfl

theorem jacIso_hom (α : Coord.FrobIso W W') :
    (P.ajRIso.symm ≪≫ P.curveIsoMk α ≪≫ P.ajLIso).hom = P.jacHom α := by
  rw [jacHom_eq]
  simp only [Iso.trans_hom, Iso.symm_hom, asIso_inv, asIso_hom, curveIsoMk_hom]

theorem isMonHom_jacHom (α : Coord.FrobIso W W') : IsMonHom (P.jacHom α) := by
  rw [jacHom]
  exact Rigid.isMonHom_transport P.B P.hX P.hX' P.hk P.fL P.fR α.1.iso.hom α.1.iso_map (zeroPt W')
    P.oR (zeroPt W) P.oL P.gL P.gR α.1.zero_iso

theorem jacHom_comm (α : Coord.FrobIso W W') :
    P.jacHom α ≫ P.πL = P.πR ≫ P.jacHom α := by
  have h2 : α.1.iso.hom ≫ (JacSite.Ψ (W := W)).hom =
      (JacSite.Ψ (W := W')).hom ≫ α.1.iso.hom := by
    rw [JacSite.twist_eq, JacSite.twist_eq]
    exact α.2
  have h3 := (twist_comm_iff_geomFrob_comm (W := W) (W' := W') α.1.iso.hom α.1.iso_map).1 h2
  have h4 : P.curveHom α ≫ P.φL = P.φR ≫ P.curveHom α := Over.OverMorphism.ext (by
    simp only [Over.comp_left, Over.homMk_left]
    exact h3)
  rw [jacHom_eq]
  convert (conj_comm_iff_of_comm P.ajL P.ajR (P.curveHom α) P.φL P.φR P.πL P.πR P.ajL_comp_πL
    P.ajR_comp_πR).2 h4 using 2

/-- `α ↦ aj'⁻¹ ≫ α ≫ aj`. -/
def toJacIso (α : Coord.FrobIso W W') : P.JacIso :=
  ⟨P.ajRIso.symm ≪≫ P.curveIsoMk α ≪≫ P.ajLIso,
    by rw [jacIso_hom]; exact P.isMonHom_jacHom α,
    by rw [jacIso_hom]; exact P.jacHom_comm α⟩

theorem toJacIso_hom (α : Coord.FrobIso W W') : (P.toJacIso α).1.hom = P.jacHom α :=
  P.jacIso_hom α

/-- `e ↦ aj' ≫ e ≫ aj⁻¹`, as a morphism of curves over `K̄`. -/
def curveHomOfJac (e : P.JacIso) :
    curveOver P.B P.hX' P.hk P.fR ⟶ curveOver P.B P.hX P.hk P.fL :=
  P.ajR ≫ e.1.hom ≫ inv P.ajL

theorem curveHomOfJac_def (e : P.JacIso) :
    P.curveHomOfJac e = P.ajR ≫ e.1.hom ≫ inv P.ajL := rfl

/-- `O` as a point over `K̄`. -/
abbrev zL : 𝟙_ (Over (Spec (.of (AlgebraicClosure k)))) ⟶ curveOver P.B P.hX P.hk P.fL :=
  Abel.basePtO P.B P.hX P.hk P.fL (zeroPt W) P.oL
abbrev zR : 𝟙_ (Over (Spec (.of (AlgebraicClosure k)))) ⟶ curveOver P.B P.hX' P.hk P.fR :=
  Abel.basePtO P.B P.hX' P.hk P.fR (zeroPt W') P.oR

theorem zeroO_comp_curveHomOfJac (e : P.JacIso) : P.zR ≫ P.curveHomOfJac e = P.zL := by
  have := e.2.1
  have h1 : P.zR ≫ P.ajR = η[P.JR] :=
    Abel.basePtO_comp_abelJacobi P.B P.hX' P.hk P.fR (zeroPt W') P.oR P.gR
  have h2 : P.zL ≫ P.ajL = η[P.JL] :=
    Abel.basePtO_comp_abelJacobi P.B P.hX P.hk P.fL (zeroPt W) P.oL P.gL
  have h3 : η[P.JR] ≫ e.1.hom = η[P.JL] := IsMonHom.one_hom e.1.hom
  calc P.zR ≫ P.curveHomOfJac e = ((P.zR ≫ P.ajR) ≫ e.1.hom) ≫ inv P.ajL := by
        simp only [curveHomOfJac_def, Category.assoc]
    _ = P.zL := by rw [h1, h3, ← h2, Category.assoc, IsIso.hom_inv_id, Category.comp_id]

theorem zeroPt_comp_curveHomOfJac (e : P.JacIso) :
    zeroPt W' ≫ (P.curveHomOfJac e).left = zeroPt W := by
  have h := congrArg (fun t => Over.Hom.left t) (P.zeroO_comp_curveHomOfJac e)
  simp only [Over.comp_left] at h
  rw [Abel.basePtO_left, Abel.basePtO_left] at h
  exact h

theorem curveHomOfJac_comm (e : P.JacIso) :
    (P.curveHomOfJac e).left ≫ Coord.twistFrob W =
      Coord.twistFrob W' ≫ (P.curveHomOfJac e).left := by
  rw [← JacSite.twist_eq, ← JacSite.twist_eq]
  refine (twist_comm_iff_geomFrob_comm _ (Over.w (P.curveHomOfJac e))).2 ?_
  have hL : inv P.ajL ≫ P.φL = P.πL ≫ inv P.ajL := by
    rw [IsIso.inv_comp_eq, ← Category.assoc, P.ajL_comp_πL, Category.assoc, IsIso.hom_inv_id,
      Category.comp_id]
  have h : P.curveHomOfJac e ≫ P.φL = P.φR ≫ P.curveHomOfJac e := by
    rw [curveHomOfJac_def]
    simp only [Category.assoc, hL, reassoc_of% e.2.2, reassoc_of% P.ajR_comp_πR]
  have h' := congrArg (fun t => Over.Hom.left t) h
  simp only [Over.comp_left, Over.homMk_left] at h'
  exact h'

/-- `aj' ≫ e ≫ aj⁻¹` as an isomorphism. -/
def curveIsoOfJac (e : P.JacIso) :
    curveOver P.B P.hX' P.hk P.fR ≅ curveOver P.B P.hX P.hk P.fL where
  hom := P.curveHomOfJac e
  inv := P.ajL ≫ e.1.inv ≫ inv P.ajR
  hom_inv_id := by
    rw [curveHomOfJac_def]
    simp only [Category.assoc, IsIso.inv_hom_id_assoc, Iso.hom_inv_id_assoc, IsIso.hom_inv_id]
  inv_hom_id := by
    rw [curveHomOfJac_def]
    simp only [Category.assoc, IsIso.inv_hom_id_assoc, Iso.inv_hom_id_assoc, IsIso.hom_inv_id]

theorem curveIsoOfJac_hom (e : P.JacIso) : (P.curveIsoOfJac e).hom = P.curveHomOfJac e := rfl

/-- `e ↦ aj' ≫ e ≫ aj⁻¹`. -/
def ofJacIso (e : P.JacIso) : Coord.FrobIso W W' :=
  ⟨⟨(Over.forget _).mapIso (P.curveIsoOfJac e), Over.w (P.curveHomOfJac e),
    P.zeroPt_comp_curveHomOfJac e⟩, P.curveHomOfJac_comm e⟩

theorem ofJacIso_hom (e : P.JacIso) :
    (P.ofJacIso e).1.iso.hom = (P.curveHomOfJac e).left := rfl

/-- **G1.4**: `Ψ`-equivariant pointed isomorphisms `E_{W'} ≅ E_W` are the `π`-equivariant
isomorphisms of group objects `J_{W'} ≅ J_W`. -/
def frobIsoEquiv : Coord.FrobIso W W' ≃ P.JacIso where
  toFun := P.toJacIso
  invFun := P.ofJacIso
  left_inv α := by
    apply Subtype.ext
    apply Coord.familyIso_ext
    rw [ofJacIso_hom]
    have : P.curveHomOfJac (P.toJacIso α) = P.curveHom α := by
      rw [curveHomOfJac_def, toJacIso_hom, jacHom_eq]
      simp only [Category.assoc, IsIso.hom_inv_id, Category.comp_id, IsIso.hom_inv_id_assoc]
    rw [this]
    rfl
  right_inv e := by
    apply Subtype.ext
    apply Iso.ext
    rw [toJacIso_hom, jacHom_eq]
    have : P.curveHom (P.ofJacIso e) = P.curveHomOfJac e :=
      Over.OverMorphism.ext (P.ofJacIso_hom e)
    rw [this, curveHomOfJac_def]
    simp only [IsIso.inv_hom_id_assoc, Category.assoc, IsIso.inv_hom_id, Category.comp_id]

/-- **`W' ≅ W` over `K` iff `J_{W'} ≅ J_W` as group objects, compatibly with Frobenius.** -/
theorem mem_orbit_iff_nonempty_jacIso :
    W' ∈ MulAction.orbit (WeierstrassCurve.VariableChange k) W ↔ Nonempty P.JacIso := by
  rw [Coord.mem_orbit_iff_nonempty_frobIso, P.frobIsoEquiv.nonempty_congr]

end PairSite

namespace JacSite

variable {W : WeierstrassCurve k} [W.IsElliptic] (S : JacSite W)

/-- The diagonal pair site of a Jacobian site. -/
abbrev diag : PairSite W W := ⟨S.B, S.hX, S.hX, S.hk⟩

/-- **`#Stab_{VariableChange K}(W) = #Aut_π(J_W)`**: the stabilizer of `W` is the group of
`π`-equivariant automorphisms of the group object `J_W` (`S.diag.JacIso`, whose objects are
`S.J` and whose Frobenius is `S.π`). -/
theorem card_stabilizer_eq_card_jacAut :
    Nat.card (MulAction.stabilizer (WeierstrassCurve.VariableChange k) W) =
      Nat.card S.diag.JacIso := by
  rw [Coord.card_stabilizer_eq_card_frobAut]
  exact Nat.card_congr S.diag.frobIsoEquiv

end JacSite

end Jac

end RamanujanWeil.Arith.Deuring.Geom
