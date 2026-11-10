import RamanujanWeil.Arith.DeuringDescent
import RamanujanWeil.Arith.DeuringClassLattice
import RamanujanWeil.Arith.DeuringRadicialDual

/-!
# A3-ord, final: site independence and homomorphisms inside one isogeny class (no Tate)

`docs/ARITH_DEURING_FINAL.md` §3. The per-class lattice count (`DeuringClassLattice`) was assembled
in `DeuringClassLattice` from `TateFinitenessPol`, which was used only to produce nonzero
equivariant homomorphisms `J_{W₀} ⟶ J_W` and back for **every** curve `W` of trace `t`. Inside one
isogeny class `C` these homomorphisms exist by definition of the class, with no finiteness input:

* **`exists_siteIso`**: two Jacobian sites `S, T` of the same `W` have equivariantly isomorphic
  concrete Jacobians, `e = aj_S⁻¹ ≫ aj_T` (pointed, hence a homomorphism by rigidity, and
  `π`-equivariant by G1.1′). This is the pattern of `Descent.exists_jacIso`.
* `frobHomNe_transport`: `FrobHomNe` does not depend on the sites.
* **`frobHomNe_of_class`**: if `W₀` and `W` lie in the same isogeny class (the equivalence
  closure of `IsogStep`), then on a global site there are nonzero equivariant homomorphisms
  `J_{W₀} ⟶ J_W` (and back, by `Radicial.frobHomDual`). The relation "nonzero equivariant hom
  between global-site Jacobians" is an equivalence (identity, `frobHomDual`, `frobHomNe_trans`)
  containing `IsogStep` (G1 for the orbit disjunct, site transport for the other).
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory MulAction
  WeierstrassCurve
open scoped CategoryTheory.MonObj

set_option linter.unusedSectionVars false

universe u

noncomputable section

namespace RamanujanWeil.Arith.Deuring.Final

open RamanujanWeil.Ihara RamanujanWeil.Arith RamanujanWeil.Arith.Deuring
  RamanujanWeil.Arith.Deuring.Geom RamanujanWeil.Arith.Deuring.Geom.Jac
  RamanujanWeil.Arith.Deuring.Geom.G7 RamanujanWeil.Arith.Deuring.Mult
  RamanujanWeil.Arith.Deuring.ClassLattice RamanujanWeil.Arith.Deuring.Descent Stacks.Groupoids

attribute [local instance] RamanujanWeil.Ihara.fact_ringChar_prime

variable {K : Type u} [Field K] [Fintype K]

section Site

variable {W : WeierstrassCurve K} [W.IsElliptic]

/-- **Site independence of the concrete Jacobian.** -/
theorem exists_siteIso (S T : JacSite W) :
    ∃ e : S.J ≅ T.J, IsMonHom e.hom ∧ e.hom ≫ T.π = S.π ≫ e.hom := by
  let ε : Ew W ⟶ T.J.left := T.aj.left
  have : IsIso ε := inferInstanceAs (IsIso ((Over.forget _).map T.aj))
  have hε : ε ≫ T.J.hom = gw W := Over.w T.aj
  have hz : Jac.zeroPt W ≫ ε = η[T.J].left :=
    (congrArg (· ≫ T.aj.left) T.zeroO_left).symm.trans
      (by rw [← Over.comp_left, T.zeroO_comp_aj])
  have hφ : geomFrob W ≫ ε = ε ≫ T.π.left := by
    have h := congrArg CommaMorphism.left T.aj_comp_π
    simp only [Over.comp_left] at h
    exact h.symm
  let e : S.J ≅ T.J := (asIso S.aj).symm ≪≫ Over.isoMk (asIso ε) hε
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

end Site

section Transport

variable {W W' : WeierstrassCurve K} [W.IsElliptic] [W'.IsElliptic]

/-- Conjugating a nonzero equivariant homomorphism by equivariant isomorphisms. -/
theorem frobHomNe_of_iso {J₁ J₂ : FrobeniusJacobian W} {J₁' J₂' : FrobeniusJacobian W'}
    (e : J₂.A ≅ J₁.A) (he : IsMonHom e.hom) (heπ : e.hom ≫ J₁.π = J₂.π ≫ e.hom)
    (e' : J₁'.A ≅ J₂'.A) (he' : IsMonHom e'.hom) (heπ' : e'.hom ≫ J₂'.π = J₁'.π ≫ e'.hom)
    (h : FrobHomNe J₁ J₁') : FrobHomNe J₂ J₂' := by
  obtain ⟨α, hα, hαπ, hα1⟩ := h
  refine ⟨e.hom ≫ α ≫ e'.hom, inferInstance, ?_, ?_⟩
  · simp only [Category.assoc]
    rw [heπ', reassoc_of% hαπ, reassoc_of% heπ]
  · intro h1
    apply hα1
    haveI := he'
    have : α = e.inv ≫ (e.hom ≫ α ≫ e'.hom) ≫ e'.inv := by simp
    rw [this, h1, MonObj.one_comp, MonObj.comp_one]

/-- **`FrobHomNe` does not depend on the Jacobian sites.** -/
theorem frobHomNe_transport (S T : JacSite W) (S' T' : JacSite W')
    (h : FrobHomNe S.frobeniusJacobian S'.frobeniusJacobian) :
    FrobHomNe T.frobeniusJacobian T'.frobeniusJacobian := by
  obtain ⟨e, he, heπ⟩ := exists_siteIso T S
  obtain ⟨e', he', heπ'⟩ := exists_siteIso S' T'
  exact frobHomNe_of_iso (J₁ := S.frobeniusJacobian) (J₂ := T.frobeniusJacobian)
    (J₁' := S'.frobeniusJacobian) (J₂' := T'.frobeniusJacobian) e he heπ e' he' heπ' h

/-- An equivariant isomorphism is a nonzero equivariant homomorphism. -/
theorem frobHomNe_of_equivIso {J : FrobeniusJacobian W} {J' : FrobeniusJacobian W'}
    (e : J.A ≅ J'.A) (he : IsMonHom e.hom) (heπ : e.hom ≫ J'.π = J.π ≫ e.hom) :
    FrobHomNe J J' := by
  refine ⟨e.hom, he, heπ, fun h1 => id_ne_one J'.dim_eq ?_⟩
  rw [← e.inv_hom_id, h1, MonObj.comp_one]

end Transport

section Class

variable (G : GlobalSite K) {t : ℤ}

/-- The relation "nonzero equivariant homomorphism between the global-site Jacobians". -/
def HomRel (x y : Ell K t) : Prop :=
  ∀ (_ : x.1.IsElliptic) (_ : y.1.IsElliptic),
    FrobHomNe (G.site x.1).frobeniusJacobian (G.site y.1).frobeniusJacobian

theorem homRel_equivalence : Equivalence (HomRel G (t := t)) where
  refl x := fun _ _ => frobHomNe_of_equivIso (Iso.refl _) (by dsimp; infer_instance) (by simp)
  symm {x y} h := fun hy hx => Radicial.frobHomDual K x.1 y.1 _ _ (h hx hy)
  trans {x y z} h₁ h₂ := fun hx hz => by
    have hy : y.1.IsElliptic := ⟨isUnit_iff_ne_zero.mpr y.2.1⟩
    exact frobHomNe_trans (h₁ hx hy) (h₂ hy hz)

theorem homRel_of_isogStep {x y : Ell K t} (h : IsogStep x.1 y.1) : HomRel G x y := by
  intro _ _
  rcases h with ⟨g, hg⟩ | ⟨_, _, S, S', h | h⟩
  · -- `y = g • x`: G1 gives an equivariant isomorphism `J_y ≅ J_x`
    have hmem : y.1 ∈ orbit (VariableChange K) x.1 := ⟨g, hg⟩
    obtain ⟨⟨e, he, heπ⟩⟩ := (mem_orbit_iff_global G x.1 y.1).1 hmem
    exact Radicial.frobHomDual K y.1 x.1 _ _ (frobHomNe_of_equivIso e he heπ)
  · exact frobHomNe_transport S (G.site x.1) S' (G.site y.1) h
  · exact Radicial.frobHomDual K y.1 x.1 _ _
      (frobHomNe_transport S' (G.site y.1) S (G.site x.1) h)

theorem homRel_of_rel {x y : Ell K t} (h : isogSetoid K t x y) : HomRel G x y := by
  have h' : Relation.EqvGen (fun a b : Ell K t => IsogStep a.1 b.1) x y := h
  clear h
  induction h' with
  | rel a b hab => exact homRel_of_isogStep G hab
  | refl a => exact (homRel_equivalence G).refl a
  | symm a b _ ih => exact (homRel_equivalence G).symm ih
  | trans a b c _ _ ih1 ih2 => exact (homRel_equivalence G).trans ih1 ih2

/-- **Nonzero equivariant homomorphisms both ways inside one isogeny class** (no Tate). -/
theorem frobHomNe_both_class {W₀ W : WeierstrassCurve K} [W₀.IsElliptic] [W.IsElliptic]
    {C : IsogClass K t} (h₀ : IsogClassPred C W₀) (h : IsogClassPred C W) :
    FrobHomNe ((G.site W₀).frobeniusJacobian) ((G.site W).frobeniusJacobian) ∧
      FrobHomNe ((G.site W).frobeniusJacobian) ((G.site W₀).frobeniusJacobian) := by
  obtain ⟨hW₀, hmk₀⟩ := h₀
  obtain ⟨hW, hmk⟩ := h
  have hr : isogSetoid K t ⟨W₀, hW₀⟩ ⟨W, hW⟩ := Quotient.exact (hmk₀.trans hmk.symm)
  exact ⟨homRel_of_rel G (x := ⟨W₀, hW₀⟩) (y := ⟨W, hW⟩) hr inferInstance inferInstance,
    homRel_of_rel G (x := ⟨W, hW⟩) (y := ⟨W₀, hW₀⟩) ((isogSetoid K t).iseqv.symm hr)
      inferInstance inferInstance⟩

end Class

end RamanujanWeil.Arith.Deuring.Final
