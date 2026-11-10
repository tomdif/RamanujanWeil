import RamanujanWeil.Arith.DeuringG8IntIso
import RamanujanWeil.Arith.DeuringClassLatticeAlg
import RamanujanWeil.Arith.DeuringG1Assembly
import RamanujanWeil.Arith.DeuringG7FinCore
import RamanujanWeil.Arith.DeuringRadicialDual
import RamanujanWeil.Arith.DeuringMultCount
import RamanujanWeil.Arith.DeuringMinBase
import RamanujanWeil.Arith.DeuringWModel

/-!
# A3-ord: assembling `DeuringClassLattice` (Λ, `rel_iff`, `card_stab`, `surj_class`)

`docs/ARITH_DEURING_CLASSLATTICE.md` §3–4.

* **One site for all curves** (`GlobalSite`): `K` is finite, so there are only a set's worth of
  curves `E_W`, and one big fppf site contains all of them and `Spec K̄`
  (`BigFppfSite.exists_containing`). All Jacobians `J_W`, the base `J₀` and all pair sites are
  taken there, so `PairSite.left`/`right` are the chosen Jacobian sites **definitionally** and no
  site-independence statement is needed.
* `Λ` (`exists_latticeMatrix_global`): from `TateFinitenessPol` (weaker than `TateFiniteness`)
  and the proved `FrobHomDual`.
* **`rel_iff`**: G1 (`mem_orbit_iff_nonempty_jacIso`) + G8(ii)
  (`G8Int.nonempty_iso_iff`) + matrices (`conj_of_linearEquiv`, `linearEquiv_of_conj`).
* **`card_stab`**: G1 (`card_stabilizer_eq_card_jacAut`) + G8(ii) (`G8Int.card_aut_eq`) +
  `stabEquiv`.
* `surj_class`: G5 `surjClass_of_descent_minimal`.

Named inputs:

* **`PrimeToPLink K`** (new): two concrete Jacobians of the same ordinary trace that are linked
  by a nonzero equivariant homomorphism are linked by one of degree prime to `p`
  (`α ≫ β = [n]`, `p ∤ n`). This is the `p`-part of G8(ii).
* `ExistsMinimalBase K`: each ordinary isogeny class contains `W₀` with `End_π(J_{W₀}) = ℤ[π]`
  (G5 §5; stated for every Jacobian site of `W₀`).
* `WeierstrassDescent K` (G5), `TateFinitenessPol K` (G7).

Headline: **`deuringClassLatticeAll_of_props`** and **`deuringMultiplicity_of_props`**.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory MulAction
  WeierstrassCurve
open scoped CategoryTheory.MonObj

set_option linter.unusedSectionVars false

universe u

namespace RamanujanWeil.Arith.Deuring.ClassLattice

open RamanujanWeil.Ihara RamanujanWeil.Arith RamanujanWeil.Arith.Deuring
  RamanujanWeil.Arith.Deuring.Geom RamanujanWeil.Arith.Deuring.Geom.G7
  RamanujanWeil.Arith.Deuring.Geom.G7.Fin RamanujanWeil.Arith.Deuring.Mult
  RamanujanWeil.Arith.Deuring.G8 RamanujanWeil.Arith.Deuring.G5
  RamanujanWeil.Arith.Deuring.G8Int Stacks.Groupoids RamanujanWeil.ArithPlan
  RamanujanWeil.Arith.Hurwitz

section Site

variable (K : Type u) [Field K] [Fintype K]

/-- **A global site**: one big fppf site containing every `E_W` and `Spec K̄`. -/
structure GlobalSite where
  /-- The site. -/
  B : BigFppfSite.{u}
  /-- It contains every `E_W`. -/
  hX : ∀ W : WeierstrassCurve K, B.Contains (Jac.Ew W)
  /-- It contains `Spec K̄`. -/
  hk : B.Contains (Spec (.of (AlgebraicClosure K)))

/-- Global sites exist (`K` is finite, so the curves form a small set). -/
theorem nonempty_globalSite : Nonempty (GlobalSite K) := by
  let S₀ : Set Scheme.{u} := Set.range (fun W : WeierstrassCurve K => Jac.Ew W) ∪
    {Spec (.of (AlgebraicClosure K))}
  have : Small.{u} S₀ := by dsimp [S₀]; infer_instance
  obtain ⟨B, hB⟩ := BigFppfSite.exists_containing S₀
  exact ⟨⟨B, fun W => hB _ (Or.inl ⟨W, rfl⟩), hB _ (Or.inr rfl)⟩⟩

variable {K}

/-- The Jacobian site of `W` inside the global site. -/
abbrev GlobalSite.site (G : GlobalSite K) (W : WeierstrassCurve K) : Jac.JacSite W :=
  ⟨G.B, G.hX W, G.hk⟩

/-- The pair site of `W`, `W'` inside the global site. -/
abbrev GlobalSite.pair (G : GlobalSite K) (W W' : WeierstrassCurve K) : Jac.PairSite W W' :=
  ⟨G.B, G.hX W, G.hX W', G.hk⟩

end Site

section Props

variable (K : Type u) [Field K] [Fintype K]

/-- **The `p`-part of G8(ii) (named).** Two concrete Jacobians of the same ordinary trace,
linked by a nonzero equivariant homomorphism `J ⟶ J'`, are linked by equivariant
`α : J ⟶ J'`, `β : J' ⟶ J` with `α ≫ β = [n]`, `n` prime to `p`.

True: for ordinary `E`, `p ∤ [O_K : ℤ[π]]` (since `disc ℤ[π] = t² − 4q ≡ t² ≢ 0 mod p`), and the
degree form on `Hom(E, E')` has content dividing a product of conductors, hence prime to `p`;
a primitive positive form represents an integer prime to `p`, and an isogeny `α` of degree `n`
has `α ≫ α̂ = [n]` (Deuring lifting, or the action of `Pic(O)`: the class of the prime `𝔭 | p`
of `O` contains ideals prime to `p`). -/
def PrimeToPLink : Prop :=
  ∀ (W W' : WeierstrassCurve K) [W.IsElliptic] [W'.IsElliptic] (S : Jac.JacSite W)
    (S' : Jac.JacSite W'), traceOfFrob W' = traceOfFrob W →
    ¬ (ringChar K : ℤ) ∣ traceOfFrob W → traceOfFrob W ^ 2 < 4 * (Nat.card K : ℤ) →
    FrobHomNe S.frobeniusJacobian S'.frobeniusJacobian →
    Link S.frobeniusJacobian.π S'.frobeniusJacobian.π

/-- **A minimal base in every ordinary isogeny class (named, G5 §5).** Every isogeny class of
ordinary trace `t` contains `W₀` with `End_π(J_{W₀}) = ℤ[π]`, for every Jacobian site. -/
def ExistsMinimalBase : Prop :=
  ∀ t : ℤ, ¬ (ringChar K : ℤ) ∣ t → t ^ 2 < 4 * (Nat.card K : ℤ) → ∀ C : IsogClass K t,
    ∃ W₀ : WeierstrassCurve K, IsogClassPred C W₀ ∧
      ∀ [W₀.IsElliptic] (S : Jac.JacSite W₀), MinimalOrder S.frobeniusJacobian.π

end Props

section Fam

variable {K : Type u} [Field K] [Fintype K]

/-- A choice of Frobenius Jacobian for every elliptic `W`. -/
abbrev JacFam (K : Type u) [Field K] [Fintype K] :=
  ∀ (W : WeierstrassCurve K) [W.IsElliptic], FrobeniusJacobian W

/-- The concrete Jacobians in a global site. -/
noncomputable abbrev GlobalSite.fam (G : GlobalSite K) : JacFam K :=
  fun W => (G.site W).frobeniusJacobian

variable (J : JacFam K) {t : ℤ}

/-- **The `Λ` field** for a family of Jacobians with homomorphisms both ways to `J W₀`. -/
theorem exists_latticeMatrix_fam {W₀ : WeierstrassCurve K} [W₀.IsElliptic]
    (ht₀ : traceOfFrob W₀ = t) (hlt : t ^ 2 < 4 * (Nat.card K : ℤ))
    (hhom : ∀ (W : WeierstrassCurve K) [W.IsElliptic], traceOfFrob W = t →
      FrobHomNe (J W₀) (J W) ∧ FrobHomNe (J W) (J W₀)) :
    ∃ Λ : WeierstrassCurve K → TrDet t (Nat.card K),
      ∀ (W : WeierstrassCurve K) (hW : W.Δ ≠ 0), traceOfFrob W = t →
        haveI : W.IsElliptic := ⟨isUnit_iff_ne_zero.mpr hW⟩
        ∃ b : Module.Basis (Fin 2) ℤ (homPi (J W₀).π (J W).π),
          (Λ W).1 = LinearMap.toMatrix b b (piAct (J W₀).π (J W).π) := by
  classical
  let M₀ : TrDet t (Nat.card K) := ⟨!![0, -(Nat.card K : ℤ); 1, t], by
    simp [Matrix.trace_fin_two], by simp [Matrix.det_fin_two]⟩
  have key : ∀ (W : WeierstrassCurve K) (hW : W.Δ ≠ 0), traceOfFrob W = t →
      haveI : W.IsElliptic := ⟨isUnit_iff_ne_zero.mpr hW⟩
      ∃ M : TrDet t (Nat.card K), ∃ b : Module.Basis (Fin 2) ℤ (homPi (J W₀).π (J W).π),
          M.1 = LinearMap.toMatrix b b (piAct (J W₀).π (J W).π) := by
    intro W hW htW
    have : W.IsElliptic := ⟨isUnit_iff_ne_zero.mpr hW⟩
    have ht : traceOfFrob W = traceOfFrob W₀ := htW.trans ht₀.symm
    have hlt' : traceOfFrob W₀ ^ 2 < 4 * (Nat.card K : ℤ) := by rw [ht₀]; exact hlt
    obtain ⟨h₁, h₂⟩ := hhom W htW
    obtain ⟨-, b, htr, hdet⟩ := frobLattice_trDet (J W₀) (J W) ht hlt' h₁ h₂
    exact ⟨⟨_, htr.trans ht₀, hdet⟩, b, rfl⟩
  refine ⟨fun W => if h : W.Δ ≠ 0 ∧ traceOfFrob W = t then (key W h.1 h.2).choose else M₀, ?_⟩
  intro W hW htW
  simp only [dif_pos (show W.Δ ≠ 0 ∧ traceOfFrob W = t from ⟨hW, htW⟩)]
  exact (key W hW htW).choose_spec

/-- `PostHomSurj` for any target, from a link and the minimal order. -/
theorem postHomSurj_fam {W₀ : WeierstrassCurve K} [W₀.IsElliptic] (ht₀ : traceOfFrob W₀ = t)
    (hmin : MinimalOrder (J W₀).π) (hlt : t ^ 2 < 4 * (Nat.card K : ℤ))
    (W W' : WeierstrassCurve K) [W.IsElliptic] [W'.IsElliptic]
    (hl : Link (J W₀).π (J W).π) : PostHomSurj (J W₀).π (J W).π (J W').π := by
  have hχ₀ := (J W₀).charPoly_eq
  rw [ht₀] at hχ₀
  have hind := lin_eq_one_iff (J W₀).dim_eq (J W₀).π t (Nat.card K) hχ₀ hlt
  obtain ⟨hπ₀, -, -⟩ := charPoly_data (J W₀).dim_eq (J W₀).π t (Nat.card K) hχ₀
  exact postHomSurj_of_link (J W₀).dim_eq (J W).dim_eq hmin hind t _ hπ₀ hlt hl

/-- **`rel_iff`** for a family: given G1 (`hG1`), G8(ii) and matrices. -/
theorem rel_iff_fam {W₀ : WeierstrassCurve K} [W₀.IsElliptic] (ht₀ : traceOfFrob W₀ = t)
    (hmin : MinimalOrder (J W₀).π) (hlt : t ^ 2 < 4 * (Nat.card K : ℤ))
    (Λ : WeierstrassCurve K → TrDet t (Nat.card K))
    (W W' : WeierstrassCurve K) [W.IsElliptic] [W'.IsElliptic]
    (b : Module.Basis (Fin 2) ℤ (homPi (J W₀).π (J W).π))
    (hb : (Λ W).1 = LinearMap.toMatrix b b (piAct (J W₀).π (J W).π))
    (b' : Module.Basis (Fin 2) ℤ (homPi (J W₀).π (J W').π))
    (hb' : (Λ W').1 = LinearMap.toMatrix b' b' (piAct (J W₀).π (J W').π))
    (hl : Link (J W₀).π (J W).π) (hl' : Link (J W₀).π (J W').π)
    (hG1 : W' ∈ orbit (VariableChange K) W ↔
      Nonempty {e : (J W').A ≅ (J W).A // IsMonHom e.hom ∧ e.hom ≫ (J W).π = (J W').π ≫ e.hom}) :
    W' ∈ orbit (VariableChange K) W ↔ ∃ g : GL2, g • Λ W = Λ W' := by
  have hA₀ := (J W₀).dim_eq
  obtain ⟨x, hx⟩ := exists_ne_one_of_link hA₀ hl
  obtain ⟨x', hx'⟩ := exists_ne_one_of_link hA₀ hl'
  have hiso := nonempty_iso_iff hA₀ (J W).dim_eq (J W').dim_eq
    (postHomSurj_fam J ht₀ hmin hlt W' W hl') (postHomSurj_fam J ht₀ hmin hlt W W' hl)
    x hx x' hx'
  refine hG1.trans (hiso.trans ⟨fun ⟨f, hf⟩ => ?_, fun ⟨g, hg⟩ => ?_⟩)
  · obtain ⟨g, hg⟩ := conj_of_linearEquiv b' b _ _ f hf
    refine ⟨g⁻¹, inv_smul_eq_iff.mpr (Subtype.ext ?_).symm⟩
    rw [smul_val, hb, hb']
    exact hg
  · have h1 : g⁻¹ • Λ W' = Λ W := inv_smul_eq_iff.mpr hg.symm
    have h2 := congrArg Subtype.val h1
    rw [smul_val, hb, hb'] at h2
    exact linearEquiv_of_conj b' b _ _ g⁻¹ h2

/-- **`card_stab`** for a family: given G1 (`hG1`), G8(ii) and `stabEquiv`. -/
theorem card_stab_fam {W₀ : WeierstrassCurve K} [W₀.IsElliptic] (ht₀ : traceOfFrob W₀ = t)
    (hmin : MinimalOrder (J W₀).π) (hlt : t ^ 2 < 4 * (Nat.card K : ℤ))
    (Λ : WeierstrassCurve K → TrDet t (Nat.card K)) (W : WeierstrassCurve K) [W.IsElliptic]
    (b : Module.Basis (Fin 2) ℤ (homPi (J W₀).π (J W).π))
    (hb : (Λ W).1 = LinearMap.toMatrix b b (piAct (J W₀).π (J W).π))
    (hl : Link (J W₀).π (J W).π)
    (hG1 : Nat.card (stabilizer (VariableChange K) W) =
      Nat.card {e : (J W).A ≅ (J W).A // IsMonHom e.hom ∧ e.hom ≫ (J W).π = (J W).π ≫ e.hom}) :
    Nat.card (stabilizer (VariableChange K) W) = Nat.card (stabilizer GL2 (Λ W)) := by
  have hA₀ := (J W₀).dim_eq
  obtain ⟨x, hx⟩ := exists_ne_one_of_link hA₀ hl
  rw [hG1, ← Nat.card_congr (stabEquiv b _ (Λ W) hb)]
  exact card_aut_eq hA₀ (J W).dim_eq (postHomSurj_fam J ht₀ hmin hlt W W hl) x hx

/-- **`DeuringClassLattice` for a family of Jacobians.** All curve-dependent instances are
handled at the level of the opaque family `J`. G1 enters through `hG1` and `hG1'`. -/
theorem classLattice_fam {W₀ : WeierstrassCurve K} [W₀.IsElliptic] (ht₀ : traceOfFrob W₀ = t)
    (hmin : MinimalOrder (J W₀).π) (hlt : t ^ 2 < 4 * (Nat.card K : ℤ))
    (P : WeierstrassCurve K → Prop) (hP : ∀ W, P W → W.Δ ≠ 0 ∧ traceOfFrob W = t)
    (Λ : WeierstrassCurve K → TrDet t (Nat.card K))
    (hΛ : ∀ (W : WeierstrassCurve K) (hW : W.Δ ≠ 0), traceOfFrob W = t →
        haveI : W.IsElliptic := ⟨isUnit_iff_ne_zero.mpr hW⟩
        ∃ b : Module.Basis (Fin 2) ℤ (homPi (J W₀).π (J W).π),
          (Λ W).1 = LinearMap.toMatrix b b (piAct (J W₀).π (J W).π))
    (hl : ∀ (W : WeierstrassCurve K) [W.IsElliptic], traceOfFrob W = t →
      Link (J W₀).π (J W).π)
    (hG1 : ∀ (W W' : WeierstrassCurve K) [W.IsElliptic] [W'.IsElliptic],
      W' ∈ orbit (VariableChange K) W ↔ Nonempty {e : (J W').A ≅ (J W).A //
        IsMonHom e.hom ∧ e.hom ≫ (J W).π = (J W').π ≫ e.hom})
    (hG1' : ∀ (W : WeierstrassCurve K) [W.IsElliptic],
      Nat.card (stabilizer (VariableChange K) W) =
        Nat.card {e : (J W).A ≅ (J W).A // IsMonHom e.hom ∧ e.hom ≫ (J W).π = (J W).π ≫ e.hom})
    (hsurj : ∀ M : TrDet t (Nat.card K), ∃ W, P W ∧ ∃ g : GL2, g • Λ W = M) :
    Nonempty (DeuringClassLattice K t P) := by
  refine ⟨⟨Λ, ?_, ?_, hsurj⟩⟩
  · intro W W' hW hW'
    obtain ⟨hWΔ, htW⟩ := hP W hW
    obtain ⟨hWΔ', htW'⟩ := hP W' hW'
    haveI : W.IsElliptic := ⟨isUnit_iff_ne_zero.mpr hWΔ⟩
    haveI : W'.IsElliptic := ⟨isUnit_iff_ne_zero.mpr hWΔ'⟩
    obtain ⟨b, hb⟩ := hΛ W hWΔ htW
    obtain ⟨b', hb'⟩ := hΛ W' hWΔ' htW'
    exact rel_iff_fam J ht₀ hmin hlt Λ W W' b hb b' hb' (hl W htW) (hl W' htW') (hG1 W W')
  · intro W hW
    obtain ⟨hWΔ, htW⟩ := hP W hW
    haveI : W.IsElliptic := ⟨isUnit_iff_ne_zero.mpr hWΔ⟩
    obtain ⟨b, hb⟩ := hΛ W hWΔ htW
    exact card_stab_fam J ht₀ hmin hlt Λ W b hb (hl W htW) (hG1' W)

end Fam

section Global

variable {K : Type u} [Field K] [Fintype K] {t : ℤ}

omit [Field K] [Fintype K] in
/-- Transport of "equivariant group isomorphisms exist" along equalities of the objects, group
structures and endomorphisms. (Used to pass from the pair-site Jacobians of G1 to the family
`(G.site W).frobeniusJacobian`: each piece is definitionally equal, but unifying the whole subtype at once is too slow.) -/
theorem nonempty_equivIso_congr {C : Type*} [Category C] [CartesianMonoidalCategory C]
    {X X' Y Y' : C} (hX : X = X') (hY : Y = Y') {iX : GrpObj X} {iX' : GrpObj X'}
    {iY : GrpObj Y} {iY' : GrpObj Y'} (hiX : HEq iX iX') (hiY : HEq iY iY') {πX : X ⟶ X}
    {πX' : X' ⟶ X'} {πY : Y ⟶ Y} {πY' : Y' ⟶ Y'} (h1 : HEq πX πX') (h2 : HEq πY πY') :
    Nonempty {e : X ≅ Y // @IsMonHom C _ _ X Y iX.toMonObj iY.toMonObj e.hom ∧
      e.hom ≫ πY = πX ≫ e.hom} ↔
    Nonempty {e : X' ≅ Y' // @IsMonHom C _ _ X' Y' iX'.toMonObj iY'.toMonObj e.hom ∧
      e.hom ≫ πY' = πX' ≫ e.hom} := by
  subst hX hY; cases hiX; cases hiY; cases h1; cases h2; rfl

/-- G1 for the global site: isomorphism of curves. -/
theorem mem_orbit_iff_global (G : GlobalSite K) (W W' : WeierstrassCurve K) [W.IsElliptic]
    [W'.IsElliptic] :
    W' ∈ orbit (VariableChange K) W ↔ Nonempty {e : ((G.site W').frobeniusJacobian).A ≅ ((G.site W).frobeniusJacobian).A //
      IsMonHom e.hom ∧ e.hom ≫ ((G.site W).frobeniusJacobian).π = ((G.site W').frobeniusJacobian).π ≫ e.hom} :=
  (G.pair W W').mem_orbit_iff_nonempty_jacIso.trans
    (nonempty_equivIso_congr (X := (G.pair W W').JR) (X' := ((G.site W').frobeniusJacobian).A)
      (Y := (G.pair W W').JL) (Y' := ((G.site W).frobeniusJacobian).A) rfl rfl (iX := inferInstance)
      (iX' := ((G.site W').frobeniusJacobian).grp) (iY := inferInstance) (iY' := ((G.site W).frobeniusJacobian).grp) HEq.rfl HEq.rfl
      (πX := (G.pair W W').πR) (πX' := ((G.site W').frobeniusJacobian).π) (πY := (G.pair W W').πL)
      (πY' := ((G.site W).frobeniusJacobian).π) HEq.rfl HEq.rfl)

/-- G1 for the global site: automorphisms. -/
theorem card_stabilizer_global (G : GlobalSite K) (W : WeierstrassCurve K) [W.IsElliptic] :
    Nat.card (stabilizer (VariableChange K) W) = Nat.card {e : ((G.site W).frobeniusJacobian).A ≅ ((G.site W).frobeniusJacobian).A //
      IsMonHom e.hom ∧ e.hom ≫ ((G.site W).frobeniusJacobian).π = ((G.site W).frobeniusJacobian).π ≫ e.hom} :=
  (G.site W).card_stabilizer_eq_card_jacAut

/-- Both homomorphisms of G8(i) on the global site, from `TateFinitenessPol` and the (proved)
`FrobHomDual`. -/
theorem frobHomNe_both_global (hfin : TateFinitenessPol K) (G : GlobalSite K)
    {W₀ : WeierstrassCurve K} [W₀.IsElliptic] (ht₀ : traceOfFrob W₀ = t)
    (hp : ¬ (ringChar K : ℤ) ∣ t) (hlt : t ^ 2 < 4 * (Nat.card K : ℤ))
    (W : WeierstrassCurve K) [W.IsElliptic] (htW : traceOfFrob W = t) :
    FrobHomNe ((G.site W₀).frobeniusJacobian) ((G.site W).frobeniusJacobian) ∧ FrobHomNe ((G.site W).frobeniusJacobian) ((G.site W₀).frobeniusJacobian) := by
  have ht : traceOfFrob W = traceOfFrob W₀ := htW.trans ht₀.symm
  have hlt' : traceOfFrob W₀ ^ 2 < 4 * (Nat.card K : ℤ) := by rw [ht₀]; exact hlt
  have hp' : ¬ (ringChar K : ℤ) ∣ traceOfFrob W₀ := by rw [ht₀]; exact hp
  rcases tate_exists_frobHom_pol ((G.site W₀).frobeniusJacobian) ((G.site W).frobeniusJacobian) ht hlt'
      (hfin W₀ W (G.site W₀) (G.site W) ht hp' hlt') with h | h
  · exact ⟨h, Radicial.frobHomDual K W₀ W _ _ h⟩
  · exact ⟨Radicial.frobHomDual K W W₀ _ _ h, h⟩

/-- The prime-to-`p` link on the global site. -/
theorem link_global (hfin : TateFinitenessPol K) (hlink : PrimeToPLink K) (G : GlobalSite K)
    {W₀ : WeierstrassCurve K} [W₀.IsElliptic] (ht₀ : traceOfFrob W₀ = t)
    (hp : ¬ (ringChar K : ℤ) ∣ t) (hlt : t ^ 2 < 4 * (Nat.card K : ℤ))
    (W : WeierstrassCurve K) [W.IsElliptic] (htW : traceOfFrob W = t) :
    Link ((G.site W₀).frobeniusJacobian).π ((G.site W).frobeniusJacobian).π := by
  have ht : traceOfFrob W = traceOfFrob W₀ := htW.trans ht₀.symm
  have hlt' : traceOfFrob W₀ ^ 2 < 4 * (Nat.card K : ℤ) := by rw [ht₀]; exact hlt
  have hp' : ¬ (ringChar K : ℤ) ∣ traceOfFrob W₀ := by rw [ht₀]; exact hp
  exact hlink W₀ W (G.site W₀) (G.site W) ht hp' hlt'
    (frobHomNe_both_global hfin G ht₀ hp hlt W htW).1

/-- The `Λ` field on the global site, from `TateFinitenessPol`. -/
theorem exists_latticeMatrix_global (hfin : TateFinitenessPol K) (G : GlobalSite K)
    {W₀ : WeierstrassCurve K} [W₀.IsElliptic] (ht₀ : traceOfFrob W₀ = t)
    (hp : ¬ (ringChar K : ℤ) ∣ t) (hlt : t ^ 2 < 4 * (Nat.card K : ℤ)) :
    ∃ Λ : WeierstrassCurve K → TrDet t (Nat.card K),
      ∀ (W : WeierstrassCurve K) (hW : W.Δ ≠ 0), traceOfFrob W = t →
        haveI : W.IsElliptic := ⟨isUnit_iff_ne_zero.mpr hW⟩
        ∃ b : Module.Basis (Fin 2) ℤ (homPi ((G.site W₀).frobeniusJacobian).π ((G.site W).frobeniusJacobian).π),
          (Λ W).1 = LinearMap.toMatrix b b (piAct ((G.site W₀).frobeniusJacobian).π ((G.site W).frobeniusJacobian).π) :=
  exists_latticeMatrix_fam (fun W _ => (G.site W).frobeniusJacobian) ht₀ hlt
    (fun W _ htW => frobHomNe_both_global hfin G ht₀ hp hlt W htW)

set_option maxHeartbeats 3200000 in
/-- `surj_class` on the global site (G5). -/
theorem surjClass_global (hD : WeierstrassDescent K) (G : GlobalSite K)
    {W₀ : WeierstrassCurve K} [W₀.IsElliptic] (ht₀ : traceOfFrob W₀ = t)
    (hp : ¬ (ringChar K : ℤ) ∣ t) (hlt : t ^ 2 < 4 * (Nat.card K : ℤ))
    (hmin₀ : MinimalOrder ((G.site W₀).frobeniusJacobian).π) (C : IsogClass K t)
    (hC : IsogClassPred C W₀) (Λ : WeierstrassCurve K → TrDet t (Nat.card K))
    (hΛ : ∀ (W : WeierstrassCurve K) (hW : W.Δ ≠ 0), traceOfFrob W = t →
        haveI : W.IsElliptic := ⟨isUnit_iff_ne_zero.mpr hW⟩
        ∃ b : Module.Basis (Fin 2) ℤ (homPi ((G.site W₀).frobeniusJacobian).π ((G.site W).frobeniusJacobian).π),
          (Λ W).1 = LinearMap.toMatrix b b (piAct ((G.site W₀).frobeniusJacobian).π ((G.site W).frobeniusJacobian).π))
    (M : TrDet t (Nat.card K)) :
    ∃ W : WeierstrassCurve K, IsogClassPred C W ∧ ∃ g : GL2, g • Λ W = M :=
  surjClass_of_descent_minimal hD (G.site W₀) ht₀ hp hlt hmin₀ C hC Λ
    (fun W hW htW => ⟨G.site W, hΛ W hW htW⟩) M

set_option maxHeartbeats 1600000 in
/-- **`DeuringClassLattice` for one class**, from a minimal base curve in it. -/
theorem nonempty_classLattice_of_base (hfin : TateFinitenessPol K) (hlink : PrimeToPLink K)
    (hD : WeierstrassDescent K) (hp : ¬ (ringChar K : ℤ) ∣ t)
    (hlt : t ^ 2 < 4 * (Nat.card K : ℤ)) (C : IsogClass K t) (W₀ : WeierstrassCurve K)
    (hC : IsogClassPred C W₀)
    (hmin : ∀ [W₀.IsElliptic] (S : Jac.JacSite W₀), MinimalOrder S.frobeniusJacobian.π) :
    Nonempty (DeuringClassLattice K t (IsogClassPred C)) := by
  obtain ⟨G⟩ := nonempty_globalSite K
  obtain ⟨hW₀, ht₀⟩ := isogClassPred_spec hC
  haveI : W₀.IsElliptic := ⟨isUnit_iff_ne_zero.mpr hW₀⟩
  obtain ⟨Λ, hΛ⟩ := exists_latticeMatrix_global hfin G ht₀ hp hlt
  have hmin₀ : MinimalOrder ((G.site W₀).frobeniusJacobian).π := hmin (G.site W₀)
  have hl : ∀ (W : WeierstrassCurve K) [W.IsElliptic], traceOfFrob W = t →
      Link ((G.site W₀).frobeniusJacobian).π ((G.site W).frobeniusJacobian).π := fun W _ htW => link_global hfin hlink G ht₀ hp hlt W htW
  have hG1 : ∀ (W W' : WeierstrassCurve K) [W.IsElliptic] [W'.IsElliptic],
      W' ∈ orbit (VariableChange K) W ↔ Nonempty {e : ((G.site W').frobeniusJacobian).A ≅ ((G.site W).frobeniusJacobian).A //
        IsMonHom e.hom ∧ e.hom ≫ ((G.site W).frobeniusJacobian).π = ((G.site W').frobeniusJacobian).π ≫ e.hom} :=
    fun W W' _ _ => mem_orbit_iff_global G W W'
  have hG1' : ∀ (W : WeierstrassCurve K) [W.IsElliptic],
      Nat.card (stabilizer (VariableChange K) W) =
        Nat.card {e : ((G.site W).frobeniusJacobian).A ≅ ((G.site W).frobeniusJacobian).A //
          IsMonHom e.hom ∧ e.hom ≫ ((G.site W).frobeniusJacobian).π = ((G.site W).frobeniusJacobian).π ≫ e.hom} :=
    fun W _ => card_stabilizer_global G W
  have hsurj : ∀ M : TrDet t (Nat.card K), ∃ W, IsogClassPred C W ∧ ∃ g : GL2, g • Λ W = M :=
    surjClass_global hD G ht₀ hp hlt hmin₀ C hC Λ hΛ
  exact classLattice_fam (fun W _ => (G.site W).frobeniusJacobian) ht₀ hmin₀ hlt (IsogClassPred C)
    (fun W hW => isogClassPred_spec hW) Λ hΛ hl hG1 hG1' hsurj

/-- **`DeuringClassLattice` for every ordinary class over `K`**, from the named Props. -/
theorem nonempty_classLattice (hfin : TateFinitenessPol K) (hlink : PrimeToPLink K)
    (hD : WeierstrassDescent K) (hbase : ExistsMinimalBase K) (hp : ¬ (ringChar K : ℤ) ∣ t)
    (hlt : t ^ 2 < 4 * (Nat.card K : ℤ)) (C : IsogClass K t) :
    Nonempty (DeuringClassLattice K t (IsogClassPred C)) := by
  obtain ⟨W₀, hC, hmin⟩ := hbase t hp hlt C
  exact nonempty_classLattice_of_base hfin hlink hD hp hlt C W₀ hC hmin

/-- **`DeuringClassLattice` for every ordinary class over `K`**, given only `TateFinitenessPol`
and `PrimeToPLink`: `WeierstrassDescent` (`WModel.weierstrassDescent`) and the minimal base
(`MinBase.existsMinimalBase`) are theorems. -/
theorem nonempty_classLattice_of_tate (hfin : TateFinitenessPol K) (hlink : PrimeToPLink K)
    (hp : ¬ (ringChar K : ℤ) ∣ t) (hlt : t ^ 2 < 4 * (Nat.card K : ℤ)) (C : IsogClass K t) :
    Nonempty (DeuringClassLattice K t (IsogClassPred C)) :=
  nonempty_classLattice hfin hlink (WModel.weierstrassDescent K) (MinBase.existsMinimalBase K)
    hp hlt C

end Global

/-! ### The headline over all `𝔽_{pⁿ}` -/

section All

/-- `PrimeToPLink` over every `𝔽_{pⁿ}`. -/
def PrimeToPLinkAll : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (n : ℕ), 1 ≤ n →
    letI : Fintype (GaloisField p n) := Fintype.ofFinite _
    PrimeToPLink (GaloisField p n)

/-- **Headline: `DeuringClassLatticeAll` from `TateFinitenessPolAll` and `PrimeToPLinkAll`.** -/
theorem deuringClassLatticeAll_of_props (hfin : TateFinitenessPolAll)
    (hlink : PrimeToPLinkAll) (p : ℕ) [Fact p.Prime] : DeuringClassLatticeAll p := by
  intro n hn t hpt hlt
  let _ : Fintype (GaloisField p n) := Fintype.ofFinite _
  intro C
  have hcard : (Nat.card (GaloisField p n) : ℤ) = (p : ℤ) ^ n := by
    rw [GaloisField.card p n (by omega)]; push_cast; rfl
  exact nonempty_classLattice_of_tate (hfin p n hn) (hlink p n hn)
    (by rwa [ringChar_galoisField]) (by rw [hcard]; exact hlt) C

/-- **Headline: `DeuringMultiplicity` for the concrete `mult`, from `TateFinitenessPolAll` and
`PrimeToPLinkAll`.** -/
theorem deuringMultiplicity_of_props (hfin : TateFinitenessPolAll)
    (hlink : PrimeToPLinkAll) (p : ℕ) [Fact p.Prime] :
    DeuringMultiplicity hurwitz p (mult p) :=
  deuringMultiplicity_of_classLattice p (deuringClassLatticeAll_of_props hfin hlink p)

end All

end RamanujanWeil.Arith.Deuring.ClassLattice
