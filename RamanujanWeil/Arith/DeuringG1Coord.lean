import RamanujanWeil.Arith.DeuringG1Descent
import StacksFrontier.AlgebraicGeometry.Stacks.WeierstrassCubicAutomorphisms
import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.ArithmeticFrobeniusInverse

/-!
# A3-ord, G1.3: pointed isomorphisms of the geometric cubics are Frobenius-fixed coordinate changes

`docs/ARITH_DEURING_PROGRESS2.md` §3c, sub-lemma G1.3. Let `K = 𝔽_q`, `K̄ = AlgebraicClosure K`,
and for a Weierstrass equation `W` over `K` let `E_W = projOf W ×_{Spec K} Spec K̄` be the
geometric plane cubic (Stacks' `fieldBaseChange`), pointed by `(0 : 1 : 0)`, with its twisted
Frobenius `Ψ_W = id × Spec(x ↦ x^q)` (Stacks' `galoisBaseChange`, the `Ψ` of `DeuringG2`).

## Main results

* `familyIsoEquiv` (any commutative ring `R`): isomorphisms of pointed plane cubics
  `E_{C'} ≅ E_C` over `Spec R` are in bijection with `{γ : VariableChange R // γ • C = C'}`.
  This repackages Stacks' `exists_unique_variableChange` as an `Equiv`.
* `frobOf_comp_coordMap`, `frobOf_comm_iff`: for a ring automorphism `σ` of `R` fixing `C` and
  `C'`, the twist `frobOf σ` (the morphism `E_C ⟶ E_C` over `Spec σ`) conjugates the
  isomorphism of `γ` to the isomorphism of `γ.map σ`. So the isomorphism of `γ` commutes with the
  twists iff `γ.map σ = γ`.
* `galoisBaseChange_comp_geomIso`: under `E_W ≅ projOf (W_K̄)` (`familyOfMapIso`), the
  twisted Frobenius `Ψ_W` is `frobOf` of the `q`-power Frobenius.
* **`geomIsoEquiv`**: pointed isomorphisms `E_{W'} ≅ E_W` over `Spec K̄` commuting with `Ψ` are
  in bijection with the Frobenius-fixed `γ : VariableChange K̄` with `γ • W_K̄ = W'_K̄`.
* **`mem_orbit_iff_nonempty_frobIso`**: `W' ∈ VariableChange(K) • W` iff there is a pointed
  `Ψ`-equivariant isomorphism `E_{W'} ≅ E_W`.
* **`card_stabilizer_eq_card_frobAut`**: `#Stab_{VariableChange K}(W)` is the number of pointed
  `Ψ`-equivariant automorphisms of `E_W`.

No ellipticity is needed here. Together with `DeuringG1Descent`, this reduces the frozen fields
`rel_iff`/`card_stab` to the statement that `Ψ`-equivariant pointed isomorphisms of the geometric
cubics correspond to `π`-equivariant isomorphisms of their Jacobians (G1.1 + G1.2).
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.ModuliEllipticCurves AlgebraicGeometry.ModuliEllipticCurves.Weierstrass

universe u

namespace RamanujanWeil.Arith.Deuring.Geom.Coord

attribute [local instance] MvPolynomial.gradedAlgebra

/-- Conjugating a commutation relation by isomorphisms. -/
theorem conj_comm_iff {𝒞 : Type*} [Category 𝒞] {X X' Y Y' : 𝒞} (a : X' ≅ Y') (b : X ≅ Y)
    (α : X' ⟶ X) (F : Y ⟶ Y) (F' : Y' ⟶ Y') :
    α ≫ (b.hom ≫ F ≫ b.inv) = (a.hom ≫ F' ≫ a.inv) ≫ α ↔
      F' ≫ (a.inv ≫ α ≫ b.hom) = (a.inv ≫ α ≫ b.hom) ≫ F := by
  constructor
  · intro H
    calc F' ≫ a.inv ≫ α ≫ b.hom = a.inv ≫ ((a.hom ≫ F' ≫ a.inv) ≫ α) ≫ b.hom := by simp
      _ = a.inv ≫ (α ≫ b.hom ≫ F ≫ b.inv) ≫ b.hom := by rw [H]
      _ = (a.inv ≫ α ≫ b.hom) ≫ F := by simp
  · intro H
    calc α ≫ b.hom ≫ F ≫ b.inv = a.hom ≫ ((a.inv ≫ α ≫ b.hom) ≫ F) ≫ b.inv := by simp
      _ = a.hom ≫ (F' ≫ a.inv ≫ α ≫ b.hom) ≫ b.inv := by rw [H]
      _ = (a.hom ≫ F' ≫ a.inv) ≫ α := by simp

/-! ### Pointed isomorphisms of plane cubics over a ring -/

section Ring

variable {R : Type u} [CommRing R]

/-- Isomorphisms of pointed families are determined by their morphism of total spaces. -/
theorem familyIso_ext {T : Scheme.{u}} {E F : PointedFamily T} {α β : FamilyIso E F}
    (h : α.iso.hom = β.iso.hom) : α = β := by
  cases α
  cases β
  congr 1
  exact Iso.ext h

/-- The morphism `E_{C'} ⟶ E_C` of a coordinate change `γ` with `γ • C = C'`. -/
noncomputable def coordMap (γ : WeierstrassCurve.VariableChange R) {C C' : WeierstrassCurve R}
    (h : γ • C = C') : projOf C' ⟶ projOf C :=
  eqToHom (congrArg projOf h.symm) ≫ changeMap γ C

instance isIso_coordMap (γ : WeierstrassCurve.VariableChange R) {C C' : WeierstrassCurve R}
    (h : γ • C = C') : IsIso (coordMap γ h) :=
  IsIso.comp_isIso' inferInstance (isIso_changeMap γ C)

theorem coordMap_congr {γ₁ γ₂ : WeierstrassCurve.VariableChange R} {C C' : WeierstrassCurve R}
    (h₁ : γ₁ • C = C') (h₂ : γ₂ • C = C') (e : γ₁ = γ₂) : coordMap γ₁ h₁ = coordMap γ₂ h₂ := by
  subst e
  rfl

/-- The pointed isomorphism `E_{C'} ≅ E_C` of a coordinate change `γ` with `γ • C = C'`. -/
noncomputable def familyIsoOfVariableChange (γ : WeierstrassCurve.VariableChange R)
    {C C' : WeierstrassCurve R} (h : γ • C = C') : FamilyIso (familyOf C') (familyOf C) where
  iso := @asIso _ _ _ _ (coordMap γ h) (isIso_coordMap γ h)
  iso_map := by
    show coordMap γ h ≫ projectionOf C = projectionOf C'
    rw [coordMap, Category.assoc, changeMap_projectionOf]
    exact eqToHom_comp_projectionOf h
  zero_iso := by
    show zeroOf C' ≫ coordMap γ h = zeroOf C
    subst h
    rw [coordMap, eqToHom_refl, Category.id_comp]
    exact zeroOf_changeMap γ C

@[simp]
theorem familyIsoOfVariableChange_hom (γ : WeierstrassCurve.VariableChange R)
    {C C' : WeierstrassCurve R} (h : γ • C = C') :
    (familyIsoOfVariableChange γ h).iso.hom = coordMap γ h :=
  rfl

/-- **Pointed isomorphisms of plane cubics are coordinate changes**: `E_{C'} ≅ E_C` over
`Spec R` correspond to `γ` with `γ • C = C'` (Stacks' `exists_unique_variableChange`). -/
noncomputable def familyIsoEquiv (C C' : WeierstrassCurve R) :
    FamilyIso (familyOf C') (familyOf C) ≃
      {γ : WeierstrassCurve.VariableChange R // γ • C = C'} where
  toFun α := ⟨(exists_unique_variableChange C C' α).exists.choose,
    (exists_unique_variableChange C C' α).exists.choose_spec.fst⟩
  invFun γ := familyIsoOfVariableChange γ.1 γ.2
  left_inv α :=
    familyIso_ext (exists_unique_variableChange C C' α).exists.choose_spec.snd.symm
  right_inv γ := Subtype.ext
    ((exists_unique_variableChange C C' (familyIsoOfVariableChange γ.1 γ.2)).unique
      (exists_unique_variableChange C C' (familyIsoOfVariableChange γ.1 γ.2)).exists.choose_spec
      ⟨γ.2, rfl⟩)

theorem familyIsoEquiv_hom (C C' : WeierstrassCurve R) (α : FamilyIso (familyOf C') (familyOf C)) :
    α.iso.hom = coordMap (familyIsoEquiv C C' α).1 (familyIsoEquiv C C' α).2 := by
  conv_lhs => rw [← (familyIsoEquiv C C').symm_apply_apply α]
  rfl

/-! ### Twisting by a ring automorphism -/

/-- `mapMap` is an isomorphism along a ring isomorphism. -/
theorem isIso_mapMap {S : Type u} [CommRing S] (C : WeierstrassCurve R) (e : R ≃+* S) :
    IsIso (mapMap C (e : R →+* S)) := by
  rw [← familyOfMapIso_inv_fst]
  have : IsIso (CommRingCat.ofHom (e : R →+* S)) := e.toCommRingCatIso.isIso_hom
  exact IsIso.comp_isIso' (Iso.isIso_inv (familyOfMapIso C (e : R →+* S)).iso)
    (pullback_fst_iso_of_right_iso _ _)

theorem polyGradedMap_comp' {S S' : Type u} [CommRing S] [CommRing S'] (φ : R →+* S)
    (ψ : S →+* S') :
    (Stacks.ProjectiveCohomology.polyGradedMap (Fin 3) ψ).comp
        (Stacks.ProjectiveCohomology.polyGradedMap (Fin 3) φ) =
      Stacks.ProjectiveCohomology.polyGradedMap (Fin 3) (ψ.comp φ) :=
  GradedRingHom.ext fun p => MvPolynomial.map_map φ ψ p

/-- Changing coefficients in two steps. -/
theorem mapMap_comp' {S S' : Type u} [CommRing S] [CommRing S'] (C : WeierstrassCurve R)
    (φ : R →+* S) (ψ : S →+* S') :
    mapMap (C.map φ) ψ ≫ mapMap C φ =
      eqToHom (congrArg projOf (C.map_map φ ψ)) ≫ mapMap C (ψ.comp φ) := by
  have h₂ : Stacks.ProjectiveCohomology.polyGradedMap (Fin 3) (ψ.comp φ) (cubicOf C) ∈
      (cubicIdealOf ((C.map φ).map ψ)).toIdeal := by
    rw [C.map_map φ ψ]
    exact map_cubicOf_mem C (ψ.comp φ)
  have e : mapMap (C.map φ) ψ ≫ mapMap C φ =
      Proj.map ((mapHom (C.map φ) ψ).comp (mapHom C φ))
        (HomogeneousIdeal.irrelevant_le_map_comp (irrelevant_le_map_mapHom C φ)
          (irrelevant_le_map_mapHom (C.map φ) ψ)) :=
    (Proj.map_comp _ _ _ _).symm
  rw [e]
  refine (map_eq_eqToHom_comp_map (C.map_map φ ψ).symm _ h₂ (map_cubicOf_mem C (ψ.comp φ)) _ _
    ?_ rfl _ _)
  refine GradedRingHom.ext fun x => ?_
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [GradedRingHom.comp_apply, mapHom, mapHom, coordHom_mk, coordHom_mk, coordHom_mk,
    ← polyGradedMap_comp', GradedRingHom.comp_apply]

theorem mapMap_congr {S : Type u} [CommRing S] (C : WeierstrassCurve R) {φ₁ φ₂ : R →+* S}
    (e : φ₁ = φ₂) :
    mapMap C φ₁ = eqToHom (congrArg projOf (congrArg C.map e)) ≫ mapMap C φ₂ := by
  subst e
  exact (Category.id_comp _).symm

variable (σ : R ≃+* R)

/-- The twist `E_C ⟶ E_C` over `Spec σ` of a Weierstrass equation fixed by `σ`. -/
noncomputable def frobOf (C : WeierstrassCurve R) (hC : C.map (σ : R →+* R) = C) :
    projOf C ⟶ projOf C :=
  eqToHom (congrArg projOf hC.symm) ≫ mapMap C (σ : R →+* R)

instance isIso_frobOf (C : WeierstrassCurve R) (hC : C.map (σ : R →+* R) = C) :
    IsIso (frobOf σ C hC) := by
  have := isIso_mapMap C σ
  unfold frobOf
  infer_instance

theorem changeMap_eqToHom (γ : WeierstrassCurve.VariableChange R) {D D' : WeierstrassCurve R}
    (e : D = D') :
    changeMap γ D ≫ eqToHom (congrArg projOf e) =
      eqToHom (congrArg projOf (congrArg (γ • ·) e)) ≫ changeMap γ D' := by
  subst e
  simp

theorem smul_map_eq (γ : WeierstrassCurve.VariableChange R) {C C' : WeierstrassCurve R}
    (h : γ • C = C') (hC : C.map (σ : R →+* R) = C) (hC' : C'.map (σ : R →+* R) = C') :
    γ.map (σ : R →+* R) • C = C' := by
  calc γ.map (σ : R →+* R) • C = γ.map (σ : R →+* R) • C.map (σ : R →+* R) := by rw [hC]
    _ = (γ • C).map (σ : R →+* R) := WeierstrassCurve.map_variableChange C γ _
    _ = C' := by rw [h, hC']

/-- **The twist conjugates the isomorphism of `γ` to that of `γ.map σ`.** -/
theorem frobOf_comp_coordMap (γ : WeierstrassCurve.VariableChange R) {C C' : WeierstrassCurve R}
    (h : γ • C = C') (hC : C.map (σ : R →+* R) = C) (hC' : C'.map (σ : R →+* R) = C') :
    frobOf σ C' hC' ≫ coordMap γ h =
      coordMap (γ.map (σ : R →+* R)) (smul_map_eq σ γ h hC hC') ≫ frobOf σ C hC := by
  subst h
  simp only [frobOf, coordMap, eqToHom_refl, Category.id_comp, Category.assoc]
  rw [mapMap_changeMap, reassoc_of% (changeMap_eqToHom (γ.map (σ : R →+* R)) hC.symm)]
  simp only [eqToHom_trans_assoc]

/-- **The isomorphism of `γ` commutes with the twists iff `γ` is fixed by `σ`.** -/
theorem frobOf_comm_iff (γ : WeierstrassCurve.VariableChange R) {C C' : WeierstrassCurve R}
    (h : γ • C = C') (hC : C.map (σ : R →+* R) = C) (hC' : C'.map (σ : R →+* R) = C') :
    frobOf σ C' hC' ≫ coordMap γ h = coordMap γ h ≫ frobOf σ C hC ↔
      γ.map (σ : R →+* R) = γ := by
  rw [frobOf_comp_coordMap σ γ h hC hC']
  constructor
  · intro H
    have H' := (cancel_mono (frobOf σ C hC)).mp H
    exact variableChange_eq_of_changeIso_eq (smul_map_eq σ γ h hC hC').symm h.symm H'
  · intro e
    rw [coordMap_congr _ h e]

/-- `frobOf_comm_iff`, read through `familyIsoEquiv`. -/
theorem frobOf_comm_iff_familyIsoEquiv {C C' : WeierstrassCurve R}
    (hC : C.map (σ : R →+* R) = C) (hC' : C'.map (σ : R →+* R) = C')
    (β : FamilyIso (familyOf C') (familyOf C)) :
    frobOf σ C' hC' ≫ β.iso.hom = β.iso.hom ≫ frobOf σ C hC ↔
      ((familyIsoEquiv C C' β).1).map (σ : R →+* R) = (familyIsoEquiv C C' β).1 := by
  have hβ := ((familyIsoEquiv C C').symm_apply_apply β).symm
  generalize familyIsoEquiv C C' β = γ at hβ ⊢
  subst hβ
  exact frobOf_comm_iff σ γ.1 γ.2 hC hC'

end Ring

/-! ### The geometric cubic over `K̄` and its twisted Frobenius -/

section Geometric

variable {K : Type u} [Field K] [Fintype K]

local notation "K̄" => AlgebraicClosure K

/-- `Spec K̄ ⟶ Spec K`. -/
noncomputable abbrev specBar (K : Type u) [Field K] : Spec (.of (AlgebraicClosure K)) ⟶ Spec (.of K) :=
  Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K)))

/-- The geometric cubic `E_W = projOf W ×_K K̄`, pointed by `(0 : 1 : 0)`, as a family over
`Spec K̄`. Its total space is Stacks' `fieldBaseChange (Over.mk (projectionOf W)) K̄`. -/
noncomputable abbrev geomFamily (W : WeierstrassCurve K) : PointedFamily (Spec (.of K̄)) :=
  (familyOf W).pullback (specBar K)

/-- The `q`-power Frobenius of `K̄` as a `K`-automorphism. -/
noncomputable abbrev frobAlg (K : Type u) [Field K] [Fintype K] :
    AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K :=
  FiniteField.frobeniusAlgEquivOfAlgebraic K (AlgebraicClosure K)

/-- **The twisted Frobenius `Ψ_W = id × Spec(x ↦ x^q)` of `E_W`** (Stacks' `galoisBaseChange`). -/
noncomputable abbrev twistFrob (W : WeierstrassCurve K) :
    (geomFamily W).total ⟶ (geomFamily W).total :=
  Stacks.Frobenius.galoisBaseChange (Over.mk (projectionOf W)) K̄ (frobAlg K)

theorem frobAlg_toRingHom : ((frobAlg K).toRingEquiv : K̄ →+* K̄) = Descent.frobQ := by
  ext x
  show (frobAlg K) x = x ^ Fintype.card K
  rw [FiniteField.coe_frobeniusAlgEquivOfAlgebraic]

theorem map_frobAlg (W : WeierstrassCurve K) :
    (W.map (algebraMap K K̄)).map ((frobAlg K).toRingEquiv : K̄ →+* K̄) = W.map (algebraMap K K̄) := by
  rw [WeierstrassCurve.map_map]
  congr 1
  ext a
  exact (frobAlg K).commutes a

/-- `E_W ≅ projOf W_K̄` over `Spec K̄` (Stacks' `familyOfMapIso`). -/
noncomputable abbrev geomIso (W : WeierstrassCurve K) :
    FamilyIso (geomFamily W) (familyOf (W.map (algebraMap K K̄))) :=
  familyOfMapIso W (algebraMap K K̄)

/-- The isomorphism of total spaces of `geomIso`, typed with `projOf`. -/
noncomputable def geomIsoHom (W : WeierstrassCurve K) :
    (geomFamily W).total ≅ projOf (W.map (algebraMap K K̄)) :=
  (geomIso W).iso

omit [Fintype K] in
theorem geomIsoHom_mapMap (W : WeierstrassCurve K) :
    (geomIsoHom W).hom ≫ mapMap W (algebraMap K K̄) =
      pullback.fst (projectionOf W) (specBar K) :=
  familyOfMapIso_hom_mapMap W _

omit [Fintype K] in
theorem geomIsoHom_projectionOf (W : WeierstrassCurve K) :
    (geomIsoHom W).hom ≫ projectionOf (W.map (algebraMap K K̄)) =
      pullback.snd (projectionOf W) (specBar K) :=
  familyOfMapIso_hom_projectionOf W _

theorem twistFrob_fst (W : WeierstrassCurve K) :
    twistFrob W ≫ pullback.fst (projectionOf W) (specBar K) =
      pullback.fst (projectionOf W) (specBar K) :=
  Stacks.Frobenius.galoisBaseChange_comp_fst (Over.mk (projectionOf W)) K̄ (frobAlg K)

theorem twistFrob_snd (W : WeierstrassCurve K) :
    twistFrob W ≫ pullback.snd (projectionOf W) (specBar K) =
      pullback.snd (projectionOf W) (specBar K) ≫
        Spec.map (CommRingCat.ofHom ((frobAlg K).toRingEquiv : K̄ →+* K̄)) :=
  Stacks.Frobenius.galoisBaseChange_comp_snd (Over.mk (projectionOf W)) K̄ (frobAlg K)

/-- **The twisted Frobenius in coordinates**: `Ψ_W` corresponds to `frobOf` of the `q`-power
Frobenius under `E_W ≅ projOf W_K̄`. -/
theorem galoisBaseChange_comp_geomIso (W : WeierstrassCurve K) :
    twistFrob W ≫ (geomIsoHom W).hom =
      (geomIsoHom W).hom ≫ frobOf (frobAlg K).toRingEquiv _ (map_frobAlg W) := by
  have hψφ : ((frobAlg K).toRingEquiv : K̄ →+* K̄).comp (algebraMap K K̄) = algebraMap K K̄ := by
    ext a
    exact (frobAlg K).commutes a
  refine (isPullback_mapMap W (algebraMap K K̄)).hom_ext ?_ ?_
  · simp only [frobOf, Category.assoc]
    rw [geomIsoHom_mapMap, twistFrob_fst, mapMap_comp', mapMap_congr W hψφ,
      eqToHom_trans_assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp,
      geomIsoHom_mapMap]
  · simp only [frobOf, Category.assoc]
    rw [geomIsoHom_projectionOf, twistFrob_snd, mapMap_projectionOf,
      reassoc_of% (eqToHom_comp_projectionOf (map_frobAlg W)),
      reassoc_of% (geomIsoHom_projectionOf W)]
    rfl

/-- The Frobenius-fixed coordinate changes carrying `W_K̄` to `W'_K̄`. -/
abbrev FrobFixedChange (W W' : WeierstrassCurve K) : Type u :=
  {γ : WeierstrassCurve.VariableChange K̄ //
    γ ∈ (Descent.frobFixed : Subgroup (WeierstrassCurve.VariableChange K̄)) ∧
      γ • W.map (algebraMap K K̄) = W'.map (algebraMap K K̄)}

/-- The pointed isomorphisms `E_{W'} ≅ E_W` over `Spec K̄` commuting with `Ψ`. -/
abbrev FrobIso (W W' : WeierstrassCurve K) : Type u :=
  {α : FamilyIso (geomFamily W') (geomFamily W) //
    α.iso.hom ≫ twistFrob W = twistFrob W' ≫ α.iso.hom}

/-- Transport of pointed isomorphisms along `E_W ≅ projOf W_K̄`. -/
noncomputable def toCoordIso (W W' : WeierstrassCurve K) :
    FamilyIso (geomFamily W') (geomFamily W) ≃
      FamilyIso (familyOf (W'.map (algebraMap K K̄))) (familyOf (W.map (algebraMap K K̄))) where
  toFun α := ((geomIso W').symm.trans α).trans (geomIso W)
  invFun β := ((geomIso W').trans β).trans (geomIso W).symm
  left_inv α := familyIso_ext (by
    simp only [FamilyIso.trans_iso, FamilyIso.symm_iso, Iso.trans_hom, Iso.symm_hom,
      Category.assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id, Category.comp_id])
  right_inv β := familyIso_ext (by
    simp only [FamilyIso.trans_iso, FamilyIso.symm_iso, Iso.trans_hom, Iso.symm_hom,
      Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id])

theorem twistFrob_eq (W : WeierstrassCurve K) :
    twistFrob W = (geomIsoHom W).hom ≫ frobOf (frobAlg K).toRingEquiv _ (map_frobAlg W) ≫
      (geomIsoHom W).inv := by
  rw [← Category.assoc]
  exact (Iso.eq_comp_inv _).mpr (galoisBaseChange_comp_geomIso W)

omit [Fintype K] in
theorem toCoordIso_hom (W W' : WeierstrassCurve K)
    (α : FamilyIso (geomFamily W') (geomFamily W)) :
    (toCoordIso W W' α).iso.hom = (geomIsoHom W').inv ≫ α.iso.hom ≫ (geomIsoHom W).hom := by
  simp only [toCoordIso, Equiv.coe_fn_mk, FamilyIso.trans_iso, FamilyIso.symm_iso,
    Iso.trans_hom, Iso.symm_hom, Category.assoc]
  rfl

theorem twist_comm_iff_coord (W W' : WeierstrassCurve K)
    (α : FamilyIso (geomFamily W') (geomFamily W)) :
    α.iso.hom ≫ twistFrob W = twistFrob W' ≫ α.iso.hom ↔
      frobOf (frobAlg K).toRingEquiv _ (map_frobAlg W') ≫ (toCoordIso W W' α).iso.hom =
        (toCoordIso W W' α).iso.hom ≫ frobOf (frobAlg K).toRingEquiv _ (map_frobAlg W) := by
  rw [toCoordIso_hom, twistFrob_eq W, twistFrob_eq W']
  exact conj_comm_iff (geomIsoHom W') (geomIsoHom W) α.iso.hom _ _

/-- **G1.3**: pointed `Ψ`-equivariant isomorphisms `E_{W'} ≅ E_W` over `Spec K̄` are the
Frobenius-fixed coordinate changes over `K̄` carrying `W_K̄` to `W'_K̄`. -/
noncomputable def geomIsoEquiv (W W' : WeierstrassCurve K) : FrobIso W W' ≃ FrobFixedChange W W' :=
  (Equiv.subtypeEquiv (p := fun α => α.iso.hom ≫ twistFrob W = twistFrob W' ≫ α.iso.hom)
    (q := fun β => frobOf (frobAlg K).toRingEquiv _ (map_frobAlg W') ≫ β.iso.hom =
        β.iso.hom ≫ frobOf (frobAlg K).toRingEquiv _ (map_frobAlg W))
    (toCoordIso W W') (twist_comm_iff_coord W W')).trans <|
  (Equiv.subtypeEquiv
    (q := fun γ : {γ : WeierstrassCurve.VariableChange K̄ //
        γ • W.map (algebraMap K K̄) = W'.map (algebraMap K K̄)} =>
      γ.1.map ((frobAlg K).toRingEquiv : K̄ →+* K̄) = γ.1)
    (familyIsoEquiv (W.map (algebraMap K K̄)) (W'.map (algebraMap K K̄)))
    (frobOf_comm_iff_familyIsoEquiv (frobAlg K).toRingEquiv _ _)).trans
    { toFun := fun γ => ⟨γ.1.1, by
        show γ.1.1.map Descent.frobQ = γ.1.1
        rw [← frobAlg_toRingHom]
        exact γ.2, γ.1.2⟩
      invFun := fun γ => ⟨⟨γ.1, γ.2.2⟩, by
        show γ.1.map ((frobAlg K).toRingEquiv : K̄ →+* K̄) = γ.1
        rw [frobAlg_toRingHom]
        exact γ.2.1⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

/-- **`W'` is `K`-isomorphic to `W` iff `E_{W'} ≅ E_W` by a pointed `Ψ`-equivariant
isomorphism.** -/
theorem mem_orbit_iff_nonempty_frobIso (W W' : WeierstrassCurve K) :
    W' ∈ MulAction.orbit (WeierstrassCurve.VariableChange K) W ↔ Nonempty (FrobIso W W') := by
  rw [Descent.mem_orbit_iff_exists_frobFixed, (geomIsoEquiv W W').nonempty_congr]
  exact ⟨fun ⟨γ, h1, h2⟩ => ⟨⟨γ, h1, h2⟩⟩, fun ⟨γ⟩ => ⟨γ.1, γ.2.1, γ.2.2⟩⟩

/-- **`#Stab_{VariableChange K}(W)` is the number of pointed `Ψ`-equivariant automorphisms of
`E_W`.** -/
theorem card_stabilizer_eq_card_frobAut (W : WeierstrassCurve K) :
    Nat.card (MulAction.stabilizer (WeierstrassCurve.VariableChange K) W) =
      Nat.card (FrobIso W W) := by
  rw [Descent.card_stabilizer_eq_frobFixed, Nat.card_congr (geomIsoEquiv W W)]
  exact Nat.card_congr
    { toFun := fun γ => ⟨γ.1, γ.2.2, γ.2.1⟩
      invFun := fun γ => ⟨γ.1, γ.2.2, γ.2.1⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

end Geometric

end RamanujanWeil.Arith.Deuring.Geom.Coord
