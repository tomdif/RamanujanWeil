import RamanujanWeil.Arith.DeuringDescent

/-!
# A3-ord, G7 Θ + J: the twisted Frobenius of a graph quotient `B_n`

`docs/ARITH_DEURING_G7_THETAJ.md` §2. Setting: `K = 𝔽_q`, `K̄ = 𝔽̄_q`, `F = Fq K` the `q`-power
Frobenius of `Spec K̄`, `F_X = FX X` the absolute `q`-power Frobenius of a `K̄`-scheme.

* **`IsTwist π ψ`**: `ψ` is a twisted Frobenius of `(X, π)`. That is, `ψ : X ≅ X` lies over `F`,
  fixes the origin up to `F`, and `π ≫ ψ = ψ ≫ π = F_X`. This is the shape of
  `Descent.ΨJ` (`π_ΨJ`, `ΨJ_π`), the semilinear automorphism `aj⁻¹ ≫ Ψ_W ≫ aj` of `J_W`.
* `isTwist_J`: `(J_W, π_W, ΨJ)` is a twist.
* **`isTwist_tensor`**: twists multiply: `ψ ×_F φ` is a twist of `(X ⊗ Y, π × π')`.
* **`exists_isTwist_glue`**: twists descend along a quotient `q : A → A/Γ` by a finite
  `π`-stable `Γ` (`Descent.exists_desc_iso`).
* **`exists_twist`**: every graph quotient `B_n = (J_W × J_{W'})/Γ_n` of `PrincipalFiniteness`
  carries a twist of `(B_n, π_n)`.

This is the `𝔽_q`-structure of `B_n`, needed by C-descent (a `Ψ`-stable theta divisor) and by the
product case (`DeuringG7ThetaJProd`).
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory
  CartesianMonoidalCategory MonObj
open scoped CategoryTheory.MonObj

universe u

noncomputable section

namespace RamanujanWeil.Arith.Deuring.Geom.G7.ThetaJ

open RamanujanWeil.Arith.Deuring.Geom RamanujanWeil.Arith.Deuring.Geom.Jac
  RamanujanWeil.Arith.Deuring.Geom.G7 RamanujanWeil.Arith.Deuring.Descent Stacks.Frobenius
  Stacks.Groupoids

attribute [local instance] RamanujanWeil.Ihara.fact_ringChar_prime

variable {K : Type u} [Field K] [Fintype K]

/-- **A twisted Frobenius of `(X, π)`**: a semilinear automorphism `ψ` over `F` fixing the
origin (up to `F`) with `π ≫ ψ = ψ ≫ π = F_X`. -/
structure IsTwist {X : Over (Spec (.of (AlgebraicClosure K)))} [GrpObj X]
    (πX : X ⟶ X) (ψ : X.left ≅ X.left) : Prop where
  base : ψ.hom ≫ X.hom = X.hom ≫ Fq K
  one : η[X].left ≫ ψ.hom = Fq K ≫ η[X].left
  π_ψ : πX.left ≫ ψ.hom = FX X
  ψ_π : ψ.hom ≫ πX.left = FX X

/-- `(J_W, π_W, aj⁻¹ ≫ Ψ_W ≫ aj)` is a twist. -/
theorem isTwist_J {W : WeierstrassCurve K} [W.IsElliptic] (S : JacSite W) :
    IsTwist S.π (asIso (ΨJ S)) :=
  ⟨ΨJ_hom S, η_ΨJ S, π_ΨJ S, ΨJ_π S⟩

section Tensor

variable {X Y : Over (Spec (.of (AlgebraicClosure K)))} [GrpObj X] [GrpObj Y]
  [AlgebraicGeometry.IsAbelianVariety (AlgebraicClosure K) X]
  [AlgebraicGeometry.IsAbelianVariety (AlgebraicClosure K) Y]
  {πX : X ⟶ X} {πY : Y ⟶ Y} [IsMonHom πX] [IsMonHom πY]
  {ψ : X.left ≅ X.left} {φ : Y.left ≅ Y.left}

/-- The product `ψ ×_F φ` of two semilinear automorphisms. -/
def tensorTwist (hX : IsTwist πX ψ) (hY : IsTwist πY φ) : (X ⊗ Y).left ≅ (X ⊗ Y).left :=
  asIso (pullback.map X.hom Y.hom X.hom Y.hom ψ.hom φ.hom (Fq K) hX.base.symm hY.base.symm)

theorem tensorTwist_fst (hX : IsTwist πX ψ) (hY : IsTwist πY φ) :
    (tensorTwist hX hY).hom ≫ pullback.fst X.hom Y.hom = pullback.fst X.hom Y.hom ≫ ψ.hom :=
  pullback.lift_fst _ _ _

theorem tensorTwist_snd (hX : IsTwist πX ψ) (hY : IsTwist πY φ) :
    (tensorTwist hX hY).hom ≫ pullback.snd X.hom Y.hom = pullback.snd X.hom Y.hom ≫ φ.hom :=
  pullback.lift_snd _ _ _

theorem FX_tensor_fst :
    FX (X ⊗ Y) ≫ pullback.fst X.hom Y.hom = pullback.fst X.hom Y.hom ≫ FX X :=
  FX_nat (X := X ⊗ Y) (Y := X) (pullback.fst X.hom Y.hom)

theorem FX_tensor_snd :
    FX (X ⊗ Y) ≫ pullback.snd X.hom Y.hom = pullback.snd X.hom Y.hom ≫ FX Y :=
  FX_nat (X := X ⊗ Y) (Y := Y) (pullback.snd X.hom Y.hom)

theorem πA_left_fst :
    (πA πX πY).left ≫ pullback.fst X.hom Y.hom = pullback.fst X.hom Y.hom ≫ πX.left := by
  have h : πA πX πY ≫ fst X Y = fst X Y ≫ πX := by simp [πA]
  have := congrArg CommaMorphism.left h
  simpa only [Over.comp_left, Over.fst_left] using this

theorem πA_left_snd :
    (πA πX πY).left ≫ pullback.snd X.hom Y.hom = pullback.snd X.hom Y.hom ≫ πY.left := by
  have h : πA πX πY ≫ snd X Y = snd X Y ≫ πY := by simp [πA]
  have := congrArg CommaMorphism.left h
  simpa only [Over.comp_left, Over.snd_left] using this

theorem η_tensor_fst : (η[X ⊗ Y]).left ≫ pullback.fst X.hom Y.hom = η[X].left := by
  have := congrArg CommaMorphism.left (IsMonHom.one_hom (fst X Y))
  simpa only [Over.comp_left, Over.fst_left] using this

theorem η_tensor_snd : (η[X ⊗ Y]).left ≫ pullback.snd X.hom Y.hom = η[Y].left := by
  have := congrArg CommaMorphism.left (IsMonHom.one_hom (snd X Y))
  simpa only [Over.comp_left, Over.snd_left] using this

/-- **Twists multiply.** -/
theorem isTwist_tensor (hX : IsTwist πX ψ) (hY : IsTwist πY φ) :
    IsTwist (πA πX πY) (tensorTwist hX hY) where
  base := by
    change (tensorTwist hX hY).hom ≫ pullback.fst X.hom Y.hom ≫ X.hom =
      (pullback.fst X.hom Y.hom ≫ X.hom) ≫ Fq K
    rw [reassoc_of% (tensorTwist_fst hX hY), hX.base, Category.assoc]
  one := by
    apply pullback.hom_ext
    · rw [Category.assoc, tensorTwist_fst, reassoc_of% η_tensor_fst, hX.one, Category.assoc,
        η_tensor_fst]
    · rw [Category.assoc, tensorTwist_snd, reassoc_of% η_tensor_snd, hY.one, Category.assoc,
        η_tensor_snd]
  π_ψ := by
    apply pullback.hom_ext
    · rw [Category.assoc, tensorTwist_fst, reassoc_of% πA_left_fst, hX.π_ψ, FX_tensor_fst]
    · rw [Category.assoc, tensorTwist_snd, reassoc_of% πA_left_snd, hY.π_ψ, FX_tensor_snd]
  ψ_π := by
    apply pullback.hom_ext
    · rw [Category.assoc, πA_left_fst, reassoc_of% (tensorTwist_fst hX hY), hX.ψ_π,
        FX_tensor_fst]
    · rw [Category.assoc, πA_left_snd, reassoc_of% (tensorTwist_snd hX hY), hY.ψ_π,
        FX_tensor_snd]

end Tensor

section Glue

variable {A : Over (Spec (.of (AlgebraicClosure K)))} [GrpObj A]
  [AlgebraicGeometry.IsAbelianVariety (AlgebraicClosure K) A]

/-- **Twists descend to quotients** by finite `π`-stable subgroups. -/
theorem exists_isTwist_glue {πA' : A ⟶ A} {ψ : A.left ≅ A.left} (h : IsTwist πA' ψ)
    {Γ : Subgroup (Pt A)} [Finite Γ] (hΓ : ∀ x ∈ Γ, x ≫ πA' ∈ Γ) (G : Glue Γ)
    (πB : G.B ⟶ G.B) (hq : G.q ≫ πB = πA' ≫ G.q) :
    ∃ ψB : G.B.left ≅ G.B.left, IsTwist πB ψB ∧ G.q.left ≫ ψB.hom = ψ.hom ≫ G.q.left := by
  have hΓ' : ∀ x ∈ Γ, ∃ y ∈ Γ, x.left ≫ inv ψ.hom = inv (Fq K) ≫ y.left := by
    intro x hx
    refine ⟨x ≫ πA', hΓ x hx, ?_⟩
    rw [IsIso.comp_inv_eq, Category.assoc, IsIso.eq_inv_comp, Over.comp_left, Category.assoc,
      h.π_ψ, Fq_point]
  have hΓ'' : ∀ x ∈ Γ, ∃ y ∈ Γ, x.left ≫ ψ.hom = Fq K ≫ y.left := by
    have := inv_mem_of_finite (inv (Fq K)) (inv ψ.hom) hΓ'
    simpa only [IsIso.inv_inv] using this
  obtain ⟨ψB, h1, h2⟩ := exists_desc_iso (Fq K) G ψ.hom h.base h.one hΓ'' hΓ'
  have := epi_q G
  refine ⟨ψB, ⟨h1, ?_, ?_, ?_⟩, h2⟩
  · have hη : η[G.B] = η[A] ≫ G.q := (IsMonHom.one_hom G.q).symm
    rw [hη, Over.comp_left, Category.assoc, h2, ← Category.assoc, h.one, Category.assoc]
  · rw [← cancel_epi G.q.left, ← Category.assoc, ← Over.comp_left, hq, Over.comp_left,
      Category.assoc, h2, ← Category.assoc, h.π_ψ, FX_nat]
  · rw [← cancel_epi G.q.left, reassoc_of% h2, ← Over.comp_left, hq, Over.comp_left,
      ← Category.assoc, h.ψ_π, FX_nat]

end Glue

/-- **Every graph quotient `B_n` carries a twisted Frobenius** of `(B_n, π_n)`. -/
theorem exists_twist {W W' : WeierstrassCurve K} [W.IsElliptic] [W'.IsElliptic]
    (S : JacSite W) (S' : JacSite W') {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓk : IsUnit (ℓ : (AlgebraicClosure K)))
    (v : ∀ n : ℕ, Tor S.J (ℓ ^ (n + 1)) ≃+ Tor S'.J (ℓ ^ (n + 1)))
    (hv : ∀ n x, v n (torAct S.π _ x) = torAct S'.π _ (v n x)) {n : ℕ} (G : Glue (Γ ℓ v n)) :
    ∃ ψ : G.B.left ≅ G.B.left, IsTwist (G.πB S.π S'.π hv) ψ := by
  have := isAbelianVariety_tensor S.J S'.J
  have := finite_Γ (E := S.J) (E' := S'.J) ℓ v hℓ hℓk n
  obtain ⟨ψ, hψ, -⟩ := exists_isTwist_glue (isTwist_tensor (isTwist_J S) (isTwist_J S'))
    (πA_mem_Γ ℓ v hv n) G (G.πB S.π S'.π hv) (G.q_πB hv)
  exact ⟨ψ, hψ⟩

end RamanujanWeil.Arith.Deuring.Geom.G7.ThetaJ

end
