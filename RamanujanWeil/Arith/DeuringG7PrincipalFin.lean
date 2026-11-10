import RamanujanWeil.Arith.DeuringG7PrincipalFinModel

/-!
# A3-ord, G7: `PrincipalFiniteness` from Θ + J and C-descent

`docs/ARITH_DEURING_G7_PRINCIPAL.md`. The reduction

```lean
theorem principalFiniteness_of_thetaJacobianModel (hΘ : ThetaJacobianModel K)
    (hD : Genus2FrobDescent K) : DGeom.PrincipalFiniteness K
```

consumes the proved steps C (`Pencil.genus2ModelExistence`, `exists_iso_of_hypModel`) and
C-Jac (`exists_baseChange_iso`, `exists_equivariant_jacobianIso`, `exists_equivIso_of_jac`).

* `equivProd`, `finite_weierstrassCurve`: Weierstrass curves over a finite field are finite in
  number (`W ↦ (a₁, a₂, a₃, a₄, a₆)`).
* **`exists_equivIso_of_genus2`**: two genus-2 Jacobian models whose curves descend to
  `K`-isomorphic curves have equivariantly isomorphic `(B, π_B)`. The descended isomorphism is
  base changed to `k̄` (it commutes with `id × Spec(frob)`), transported to the curves over `k̄`
  (it then commutes with the `Ψ`), and fed to C-Jac in a site containing both curves.
* **`exists_equivIso_of_prod`**: two product models with the same pair `(W₁, W₂)` have
  equivariantly isomorphic `(B, π_B)`.
* **`principalFiniteness_of_thetaJacobianModel`**: the pigeonhole over the finite type
  `HypModel K ⊕ (WeierstrassCurve K × WeierstrassCurve K)` of invariants.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory
  CartesianMonoidalCategory Stacks.Frobenius Stacks.PicardFunctor
open scoped CategoryTheory.MonObj

universe u

noncomputable section

namespace RamanujanWeil.Arith.Deuring.Geom.G7.PrincipalFin

open Stacks.Groupoids RamanujanWeil.Arith.Deuring.Geom RamanujanWeil.Arith.Deuring.Geom.G7
  RamanujanWeil.Arith.Deuring.Geom.G7.Fin RamanujanWeil.Ihara

attribute [local instance] RamanujanWeil.Ihara.fact_ringChar_prime

/-! ### Finitely many Weierstrass curves -/

/-- `WeierstrassCurve R ≃ R⁵`. -/
def equivProd (R : Type u) : WeierstrassCurve R ≃ R × R × R × R × R where
  toFun W := (W.a₁, W.a₂, W.a₃, W.a₄, W.a₆)
  invFun a := ⟨a.1, a.2.1, a.2.2.1, a.2.2.2.1, a.2.2.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem finite_weierstrassCurve (R : Type u) [Finite R] : Finite (WeierstrassCurve R) :=
  Finite.of_equiv _ (equivProd R).symm

variable {K : Type u} [Field K] [Fintype K]

/-! ### Two genus-2 models over isomorphic descended curves -/

/-- **Genus-2 case of the pigeonhole.** Let `M`, `M'` be genus-2 Jacobian models of `(B, π)` and
`(B', π')` whose curves are base changes of genus-2 curves `C`, `C'` over `K` (C-descent), and
suppose `C ≅ C'` over `K` (step C). Then `(B, π) ≅ (B', π')`. -/
theorem exists_equivIso_of_genus2 {B B' : Over (Spec (.of (AlgebraicClosure K)))} [GrpObj B]
    [GrpObj B'] {πB : B ⟶ B} {πB' : B' ⟶ B'} (M : Genus2JacModel K B πB)
    (M' : Genus2JacModel K B' πB') (C C' : Genus2Curve K)
    (β : M.X ≅ fieldBaseChange (Over.mk C.t) (AlgebraicClosure K))
    (hβ₁ : β.hom ≫ pullback.snd C.t (specAlgebraMap K (AlgebraicClosure K)) = M.s)
    (hβ₂ : β.hom ≫ galoisBaseChange (Over.mk C.t) (AlgebraicClosure K) (Jac.JacSite.frob (k := K)) =
      M.Ψ ≫ β.hom)
    (β' : M'.X ≅ fieldBaseChange (Over.mk C'.t) (AlgebraicClosure K))
    (hβ₁' : β'.hom ≫ pullback.snd C'.t (specAlgebraMap K (AlgebraicClosure K)) = M'.s)
    (hβ₂' : β'.hom ≫ galoisBaseChange (Over.mk C'.t) (AlgebraicClosure K)
      (Jac.JacSite.frob (k := K)) = M'.Ψ ≫ β'.hom)
    (φ : C.Y ≅ C'.Y) (hφ : φ.hom ≫ C'.t = C.t) :
    ∃ e : B ≅ B', IsMonHom e.hom ∧ e.hom ≫ πB' = πB ≫ e.hom := by
  obtain ⟨α, hα₁, hα₂⟩ := CJac.exists_baseChange_iso (AlgebraicClosure K) C.t C'.t φ hφ
  -- the isomorphism of the curves over `k̄`
  let α' : M.X ≅ M'.X := β ≪≫ α ≪≫ β'.symm
  have hβ'inv₁ : β'.inv ≫ M'.s = pullback.snd C'.t (specAlgebraMap K (AlgebraicClosure K)) := by
    rw [Iso.inv_comp_eq, hβ₁']
  have hβ'inv₂ : β'.inv ≫ M'.Ψ =
      galoisBaseChange (Over.mk C'.t) (AlgebraicClosure K) (Jac.JacSite.frob (k := K)) ≫ β'.inv := by
    rw [Iso.inv_comp_eq, ← Category.assoc, hβ₂', Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have hα'₁ : α'.hom ≫ M'.s = M.s := by
    change (β.hom ≫ α.hom ≫ β'.inv) ≫ M'.s = M.s
    rw [Category.assoc, Category.assoc, hβ'inv₁, hα₁, hβ₁]
  have hα'₂ : α'.hom ≫ M'.Ψ = M.Ψ ≫ α'.hom := by
    change (β.hom ≫ α.hom ≫ β'.inv) ≫ M'.Ψ = M.Ψ ≫ β.hom ≫ α.hom ≫ β'.inv
    rw [Category.assoc, Category.assoc, hβ'inv₂, ← Category.assoc α.hom, hα₂ (Jac.JacSite.frob (k := K)),
      Category.assoc, ← Category.assoc β.hom, hβ₂, Category.assoc]
  -- a common site
  let S₀ : Set Scheme.{u} := {M.X, M'.X, Spec (.of (AlgebraicClosure K))}
  have : Small.{u} S₀ := by dsimp [S₀]; infer_instance
  obtain ⟨S, hS⟩ := BigFppfSite.exists_containing S₀
  have hX : S.Contains M.X := hS _ (by simp [S₀])
  have hX' : S.Contains M'.X := hS _ (by simp [S₀])
  have hk : S.Contains (Spec (.of (AlgebraicClosure K))) := hS _ (by simp [S₀])
  let f : S.obj hX ⟶ S.obj hk := ObjectProperty.homMk M.s
  let f' : S.obj hX' ⟶ S.obj hk := ObjectProperty.homMk M'.s
  have hf : S.inclusion.map f = M.s := rfl
  have hf' : S.inclusion.map f' = M'.s := rfl
  have : IsCurve (AlgebraicClosure K) (S.inclusion.map f) := M.isCurve
  have : GeometricallyIrreducible (S.inclusion.map f) := M.geomIrred
  have : Smooth (S.inclusion.map f) := M.smooth
  have : IsProper (S.inclusion.map f) := M.proper
  have : IsProjectiveVariety (AlgebraicClosure K) (S.inclusion.map f) := M.projVar
  have : IsCurve (AlgebraicClosure K) (S.inclusion.map f') := M'.isCurve
  have : GeometricallyIrreducible (S.inclusion.map f') := M'.geomIrred
  have : Smooth (S.inclusion.map f') := M'.smooth
  have : IsProper (S.inclusion.map f') := M'.proper
  have : IsProjectiveVariety (AlgebraicClosure K) (S.inclusion.map f') := M'.projVar
  have : (picardFunctor S hX hk f).IsRepresentable :=
    Stacks.RigidifiedPicard.isRepresentable_picardFunctor_of_isSepClosed (AlgebraicClosure K)
      S hX hk f M.projMor
  have : (picardFunctor S hX' hk f').IsRepresentable :=
    Stacks.RigidifiedPicard.isRepresentable_picardFunctor_of_isSepClosed (AlgebraicClosure K)
      S hX' hk f' M'.projMor
  have hσ : M.σ ≫ S.inclusion.map f = 𝟙 _ := M.hσ
  have hσ' : M'.σ ≫ S.inclusion.map f' = 𝟙 _ := M'.hσ
  have hΨ : M.Ψ ≫ S.inclusion.map f = S.inclusion.map f ≫ frobSpec K := M.hΨ
  have hΨ' : M'.Ψ ≫ S.inclusion.map f' = S.inclusion.map f' ≫ frobSpec K := M'.hΨ
  obtain ⟨e₁, he₁, he₁π⟩ := M.jac S hX hk f hf
  obtain ⟨e₂, he₂, he₂π⟩ := M'.jac S hX' hk f' hf'
  have hJ := CJac.exists_equivariant_jacobianIso S hX hX' hk f f' M.σ hσ M'.σ hσ' α' hα'₁
    (ringChar K) (Jac.JacSite.specIsInChar (k := K)) (cardExp K) M.Ψ hΨ M'.Ψ hΨ' hα'₂
  exact CJac.exists_equivIso_of_jac ⟨e₁, he₁, he₁π⟩ ⟨e₂, he₂, he₂π⟩ hJ

/-! ### Two product models with the same factors -/

/-- **Product case of the pigeonhole.** Two product models with the same Weierstrass curves give
equivariantly isomorphic `(B, π_B)`. -/
theorem exists_equivIso_of_prod {B B' : Over (Spec (.of (AlgebraicClosure K)))} [GrpObj B]
    [GrpObj B'] {πB : B ⟶ B} {πB' : B' ⟶ B'} (M : ProdJacModel K B πB)
    (M' : ProdJacModel K B' πB') (h₁ : M.W₁ = M'.W₁) (h₂ : M.W₂ = M'.W₂) :
    ∃ e : B ≅ B', IsMonHom e.hom ∧ e.hom ≫ πB' = πB ≫ e.hom := by
  obtain ⟨W₁, W₂, i₁, i₂, jac⟩ := M
  obtain ⟨W₁', W₂', i₁', i₂', jac'⟩ := M'
  dsimp only at h₁ h₂
  subst h₁ h₂
  obtain ⟨S₁⟩ := Jac.nonempty_jacSite W₁
  obtain ⟨S₂⟩ := Jac.nonempty_jacSite W₂
  obtain ⟨e, he, heπ⟩ := jac S₁ S₂
  obtain ⟨e', he', he'π⟩ := jac' S₁ S₂
  have h := CJac.IsEquivJacIso.trans (CJac.IsEquivJacIso.symm (π := S₁.π ⊗ₘ S₂.π) (π' := πB)
    (e := e) ⟨he, heπ⟩) (π'' := πB') (e' := e') ⟨he', he'π⟩
  exact ⟨e.symm ≪≫ e', h⟩

/-! ### The reduction -/

/-- **`PrincipalFiniteness` from Θ + J and C-descent.** -/
theorem principalFiniteness_of_thetaJacobianModel (hΘ : ThetaJacobianModel K)
    (hD : Genus2FrobDescent K) : DGeom.PrincipalFiniteness K := by
  intro W W' _ _ S S' ht hp hlt ℓ hℓ hodd hk v hv G hP
  have := finite_weierstrassCurve K
  -- the invariant of each member
  have key : ∀ n, ∃ i : Genus2.HypModel K ⊕ (WeierstrassCurve K × WeierstrassCurve K),
      Sum.elim
        (fun a => ∃ (M : Genus2JacModel K (G n).B ((G n).πB S.π S'.π hv)) (C : Genus2Curve K)
          (β : M.X ≅ fieldBaseChange (Over.mk C.t) (AlgebraicClosure K)),
          β.hom ≫ pullback.snd C.t (specAlgebraMap K (AlgebraicClosure K)) = M.s ∧
          β.hom ≫ galoisBaseChange (Over.mk C.t) (AlgebraicClosure K)
            (Jac.JacSite.frob (k := K)) = M.Ψ ≫ β.hom ∧
          letI := C.isCurve
          letI := functionFieldAlgebra K C.t
          Nonempty (C.Y.functionField ≃ₐ[K] a.FunField))
        (fun w => ∃ M : ProdJacModel K (G n).B ((G n).πB S.π S'.π hv),
          M.W₁ = w.1 ∧ M.W₂ = w.2) i := by
    intro n
    rcases hΘ W W' S S' ht hp hlt ℓ hℓ hodd hk v hv G n (hP n) with hM | hM
    · have M := Classical.choice hM
      have := M.isCurve; have := M.geomIrred; have := M.smooth; have := M.proper
      have := M.isIso_Ψ
      obtain ⟨C, β, hβ₁, hβ₂⟩ := hD M.X M.s M.genus_eq M.Ψ M.hΨ
      have := C.isCurve; have := C.smooth; have := C.proper; have := C.geomIrred
      obtain ⟨a, ha⟩ := Genus2.Pencil.genus2ModelExistence (K := K) C.Y C.t C.genus_eq
      exact ⟨Sum.inl a, M, C, β, hβ₁, hβ₂, ha⟩
    · have M := Classical.choice hM
      exact ⟨Sum.inr (M.W₁, M.W₂), M, rfl, rfl⟩
  choose inv hinv using key
  obtain ⟨n, m, hnm, heq⟩ := Finite.exists_ne_map_eq_of_infinite inv
  refine ⟨n, m, hnm, ?_⟩
  have hn := hinv n
  have hm := hinv m
  rw [heq] at hn
  rcases hi : inv m with a | w
  · rw [hi] at hn hm
    obtain ⟨M, C, β, hβ₁, hβ₂, ⟨eC⟩⟩ := hn
    obtain ⟨M', C', β', hβ₁', hβ₂', ⟨eC'⟩⟩ := hm
    have := C.isCurve; have := C.smooth; have := C.proper
    have := C'.isCurve; have := C'.smooth; have := C'.proper
    obtain ⟨φ, hφ⟩ := Genus2.exists_iso_of_hypModel C.t C'.t (Genus2.isRegular_of_smooth_field C.t)
      (Genus2.isRegular_of_smooth_field C'.t) a eC eC'
    exact exists_equivIso_of_genus2 M M' C C' β hβ₁ hβ₂ β' hβ₁' hβ₂' φ hφ
  · rw [hi] at hn hm
    obtain ⟨M, h₁, h₂⟩ := hn
    obtain ⟨M', h₁', h₂'⟩ := hm
    exact exists_equivIso_of_prod M M' (h₁.trans h₁'.symm) (h₂.trans h₂'.symm)

end RamanujanWeil.Arith.Deuring.Geom.G7.PrincipalFin

end
