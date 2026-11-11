import RamanujanWeil.Arith.DeuringG7ThetaJProd
import StacksFrontier.AlgebraicGeometry.RegularSectionSequence.Basic

/-!
# A3-ord, G7: `ThetaJacobianModel` reduced to five smaller named Props

`docs/ARITH_DEURING_G7_THETAJ.md`. Setting: `K = 𝔽_q`, `K̄ = 𝔽̄_q`, `F = Fq K`.

`ThetaJacobianModel K` (Θ + J) is split along its real seams. Two pieces are **proved** in
`DeuringG7ThetaJTwist` and `DeuringG7ThetaJProd`:

* the `𝔽_q`-structure of `B_n`: a twist `ψ_n` with `π_n ≫ ψ_n = ψ_n ≫ π_n = F` (`exists_twist`);
* the whole product branch: `B ≅ C₁ ⊗ C₂` with all endomorphisms defined over `𝔽_q` gives a
  `ProdJacModel` (`prodJacModel_of_prodIso`).

**Proved here.** `frobDefined_of_central`: if `π_n` is central and `F_B` is an epimorphism, then
every endomorphism commutes with `ψ_n`. The assembly is **`thetaJacobianModel_of_gaps`**.

**What remains**, as named Props:

* **`ThetaDichotomy K`** (Θ, geometric, Frobenius-free). Let `B` be a principally polarized
  abelian variety over `K̄` that is a quotient of a product of two elliptic curves with finite
  kernel. Then the theta divisor `Z(t)` (`t ∈ Γ(L)`, `t ≠ 0`) is a smooth projective
  geometrically irreducible curve of genus `2` (`ThetaCurveGeom`), or `B ≅ C₁ ⊗ C₂` with
  `dim C_i = 1`.
* **`ThetaFrobStable K`** (Θ, Frobenius). A theta curve has a `ψ`-stable translate.
* **`ThetaAlbanese K`** (J). For a `ψ`-stable theta curve `X ⊆ B` with `Ψ = ψ|_X`, we have
  `(B, π_B) ≅ (Pic⁰_X, F_Ψ)`, i.e. `IsJacobianOf`.
* **`FrobeniusCentral K`**: `π_n` is central in `End(B_n)` (ordinary isogeny class).
* **`AbsFrobEpi K`**: the absolute Frobenius of an abelian variety over `K̄` is an epimorphism of
  schemes (a reduced scheme).
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory
  CartesianMonoidalCategory MonObj
open scoped CategoryTheory.MonObj

universe u

noncomputable section

namespace RamanujanWeil.Arith.Deuring.Geom.G7.ThetaJ

open RamanujanWeil.Arith.Deuring.Geom RamanujanWeil.Arith.Deuring.Geom.Jac
  RamanujanWeil.Arith.Deuring.Geom.G7 RamanujanWeil.Arith.Deuring.Descent Stacks.Frobenius
  Stacks.Groupoids Stacks.PicardFunctor RamanujanWeil.Arith.Deuring.Geom.G7.PrincipalFin
  RamanujanWeil.Ihara

attribute [local instance] RamanujanWeil.Ihara.fact_ringChar_prime

variable (K : Type u) [Field K] [Fintype K]

/-! ### Theta curves -/

/-- Translation `x ↦ x · b` by a point `b`. -/
def transl {k : Type u} [Field k] {B : Over (Spec (.of k))} [GrpObj B] (b : Pt B) : B ⟶ B :=
  𝟙 B * (toUnit B ≫ b)

variable {K} in
/-- **`ι` embeds `X` as a translate of a theta divisor.** There are an invertible ample `L` with
`h⁰(L) = 1`, a section `t ≠ 0`, a point `b` and an isomorphism of `X` with the zero scheme
`Z(t)`, such that `ι` is `X ≅ Z(t) ↪ B` followed by the translation by `b`. -/
def IsThetaCurve (B : Over (Spec (.of (AlgebraicClosure K)))) [GrpObj B] {X : Scheme.{u}} (incl : X ⟶ B.left) : Prop :=
  letI : B.left.Over (Spec (.of (AlgebraicClosure K))) := ⟨B.hom⟩
  ∃ (L : B.left.Modules) (_ : Stacks.Ample.IsInvertibleModule B.left L),
    Stacks.Ample.IsAmple B.left L ∧
    (letI := Stacks.AlgebraicGeometry.ProjectiveSpaceGeneratingSections.globalSectionsModule (AlgebraicClosure K)
      B.left L
     Module.finrank (AlgebraicClosure K) Γ(L, ⊤) = 1) ∧
    ∃ (t : Γ(L, ⊤)) (_ : t ≠ 0) (b : Pt B)
      (j : X ≅ (Stacks.RegularSectionSequence.zeroScheme B.left L t).subscheme),
      incl = j.hom ≫ (Stacks.RegularSectionSequence.zeroScheme B.left L t).subschemeι ≫
        (transl b).left

variable {K} in
/-- **A theta curve of genus 2** in `B`: a translate `X ↪ B` of a theta divisor which is a smooth
projective geometrically irreducible curve of genus `2` over `K̄`, with a point. -/
structure ThetaCurveGeom (B : Over (Spec (.of (AlgebraicClosure K)))) [GrpObj B] where
  /-- The curve. -/
  X : Scheme.{u}
  /-- The embedding. -/
  incl : X ⟶ B.left
  isTheta : IsThetaCurve B incl
  isCurve : IsCurve (AlgebraicClosure K) (incl ≫ B.hom)
  geomIrred : GeometricallyIrreducible (incl ≫ B.hom)
  smooth : Smooth (incl ≫ B.hom)
  proper : IsProper (incl ≫ B.hom)
  projVar : IsProjectiveVariety (AlgebraicClosure K) (incl ≫ B.hom)
  projMor : IsProjectiveMorphism (incl ≫ B.hom)
  genus_eq : genus (incl ≫ B.hom) = 2
  /-- A point. -/
  σ : Spec (.of (AlgebraicClosure K)) ⟶ X
  hσ : σ ≫ incl ≫ B.hom = 𝟙 _

variable {K} in
/-- A `ψ`-stable theta curve: `Ψ = ψ|_X` lies over `F`. -/
theorem ThetaCurveGeom.hΨ {B : Over (Spec (.of (AlgebraicClosure K)))} [GrpObj B] (T : ThetaCurveGeom B)
    {ψ : B.left ≅ B.left} {Ψ : T.X ⟶ T.X} (h : Ψ ≫ T.incl = T.incl ≫ ψ.hom)
    (hψ : ψ.hom ≫ B.hom = B.hom ≫ Fq K) :
    Ψ ≫ (T.incl ≫ B.hom) = (T.incl ≫ B.hom) ≫ frobSpec K := by
  rw [← Category.assoc, h, Category.assoc, hψ, Category.assoc]

/-! ### The named Props -/

/-- **Θ, geometric (named).** Let `B` be a principally polarized abelian variety over `K̄`
receiving a surjective homomorphism with finite kernel (on points) from a product of two elliptic
curves, so `B` is an abelian surface. Then `B` has a theta curve of genus `2`, or `B ≅ C₁ ⊗ C₂`
for two elliptic curves `C_i`.

Mathematically: `Θ = Z(t)` has `Θ² = 2`, so it is reduced. If it is irreducible, then
`p_a(Θ) = 2` (adjunction, `K_B = 0`) and it is smooth, since an abelian surface is not generated
by a rational or elliptic curve with `Θ² = 2`. If it is reducible, `Θ = C₁ + C₂` with
`C₁ · C₂ = 1`, and addition `C₁ × C₂ → B` is an isomorphism. -/
def ThetaDichotomy : Prop :=
  ∀ (B : Over (Spec (.of (AlgebraicClosure K)))) [GrpObj B] [AlgebraicGeometry.IsAbelianVariety (AlgebraicClosure K) B]
    (E E' : Over (Spec (.of (AlgebraicClosure K)))) [GrpObj E] [GrpObj E']
    [AlgebraicGeometry.IsAbelianVariety (AlgebraicClosure K) E] [AlgebraicGeometry.IsAbelianVariety (AlgebraicClosure K) E'],
    abelianVarietyDimension E = 1 → abelianVarietyDimension E' = 1 →
    ∀ (f : E ⊗ E' ⟶ B), IsMonHom f → Surjective f.left →
      {x : Pt (E ⊗ E') | x ≫ f = 1}.Finite → DGeom.PrincipallyPolarized (AlgebraicClosure K) B →
      Nonempty (ThetaCurveGeom B) ∨
        ∃ (C₁ C₂ : Over (Spec (.of (AlgebraicClosure K)))) (_ : GrpObj C₁) (_ : GrpObj C₂)
          (_ : AlgebraicGeometry.IsAbelianVariety (AlgebraicClosure K) C₁)
          (_ : AlgebraicGeometry.IsAbelianVariety (AlgebraicClosure K) C₂),
          abelianVarietyDimension C₁ = 1 ∧ abelianVarietyDimension C₂ = 1 ∧
          ∃ e : B ≅ C₁ ⊗ C₂, IsMonHom e.hom

/-- **Θ, Frobenius (named): a theta curve has a `ψ`-stable translate.** This holds when all
endomorphisms of `B` are defined over `𝔽_q`.

Mathematically: `ψ^*L` is algebraically equivalent to `L`. Indeed, `a = λ_L⁻¹ λ_{ψ^*L}` is a
totally positive symmetric endomorphism fixed by `ψ`, and `L` is defined over some `𝔽_{q^r}`,
so `a^r = 1` and hence `a = 1`. So `ψ(Θ) = Θ + c`, and Lang (`ψ − 1 = π⁻¹ − 1` is onto on
points) gives `b` with `ψ(Θ + b) = Θ + b`. -/
def ThetaFrobStable : Prop :=
  ∀ (B : Over (Spec (.of (AlgebraicClosure K)))) [GrpObj B] [AlgebraicGeometry.IsAbelianVariety (AlgebraicClosure K) B]
    (πB : B ⟶ B) [IsMonHom πB] (ψ : B.left ≅ B.left), IsTwist πB ψ → FrobDefined B ψ →
    ∀ _ : ThetaCurveGeom B,
      ∃ (T' : ThetaCurveGeom B) (Ψ : T'.X ⟶ T'.X), IsIso Ψ ∧ Ψ ≫ T'.incl = T'.incl ≫ ψ.hom

/-- **J (named): a `ψ`-stable theta curve is the Jacobian, equivariantly.** For a theta curve
`X ⊆ B` with `Ψ = ψ|_X`, the pair `(B, π_B)` is `(Pic⁰_X, F_Ψ)` in every site.

Mathematically: `x ↦ (t_x^*L ⊗ L⁻¹)|_X` (or Albanese) is a homomorphism `B → Pic⁰_X`, by
rigidity, with degree `Θ²/2 = 1`. Since `aj ≫ e` is `ι` up to translation, it intertwines
`F_Ψ` with `π_B`. Both satisfy `(−) ≫ (twist) = F` with twists that differ by a translation. -/
def ThetaAlbanese : Prop :=
  ∀ (B : Over (Spec (.of (AlgebraicClosure K)))) [GrpObj B] [AlgebraicGeometry.IsAbelianVariety (AlgebraicClosure K) B]
    (πB : B ⟶ B) [IsMonHom πB] (ψ : B.left ≅ B.left) (hψ : IsTwist πB ψ)
    (T : ThetaCurveGeom B) (Ψ : T.X ⟶ T.X), IsIso Ψ → ∀ h : Ψ ≫ T.incl = T.incl ≫ ψ.hom,
      IsJacobianOf K (T.incl ≫ B.hom) Ψ (T.hΨ h hψ.base) T.σ T.hσ B πB

/-- **`π_n` is central in `End(B_n)` (named).** The isogeny class is ordinary, so every
homomorphism among `E, E'` (over `K̄`) commutes with Frobenius: `End⁰(B_n) = M₂(ℚ(π))`. -/
def FrobeniusCentral : Prop :=
  ∀ (W W' : WeierstrassCurve K) [W.IsElliptic] [W'.IsElliptic] (S : Jac.JacSite W)
    (S' : Jac.JacSite W'), traceOfFrob W' = traceOfFrob W →
    ¬ (ringChar K : ℤ) ∣ traceOfFrob W → traceOfFrob W ^ 2 < 4 * (Nat.card K : ℤ) →
    ∀ ℓ : ℕ, ℓ.Prime → ℓ ≠ 2 → IsUnit (ℓ : AlgebraicClosure K) →
      ∀ (v : ∀ n : ℕ, Tor S.J (ℓ ^ (n + 1)) ≃+ Tor S'.J (ℓ ^ (n + 1)))
        (hv : ∀ n x, v n (torAct S.π _ x) = torAct S'.π _ (v n x)) (n : ℕ)
        (G : Glue (Γ ℓ v n)) (α : G.B ⟶ G.B), IsMonHom α →
        α ≫ G.πB S.π S'.π hv = G.πB S.π S'.π hv ≫ α

/-- **The absolute Frobenius of an abelian variety over `K̄` is an epimorphism (named).** It is a
homeomorphism, and `f ↦ f^q` is injective on a reduced scheme. -/
def AbsFrobEpi : Prop :=
  ∀ (X : Over (Spec (.of (AlgebraicClosure K)))) [GrpObj X] [AlgebraicGeometry.IsAbelianVariety (AlgebraicClosure K) X], Epi (FX X)

/-! ### Proofs -/

variable {K}

/-- **Central + `F` epi ⇒ every endomorphism is defined over `𝔽_q`.**
`π ≫ α ≫ ψ = α ≫ π ≫ ψ = α ≫ F = F ≫ α = π ≫ ψ ≫ α`, and `π` is an epimorphism because
`π ≫ ψ = F`. -/
theorem frobDefined_of_central {B : Over (Spec (.of (AlgebraicClosure K)))} [GrpObj B] {πB : B ⟶ B}
    {ψ : B.left ≅ B.left} (hψ : IsTwist πB ψ) (hF : Epi (FX B))
    (hc : ∀ α : B ⟶ B, IsMonHom α → α ≫ πB = πB ≫ α) : FrobDefined B ψ := by
  intro α hα
  have hπ : Epi πB.left := by
    have h : πB.left = FX B ≫ ψ.inv := by
      rw [← hψ.π_ψ, Category.assoc, Iso.hom_inv_id, Category.comp_id]
    rw [h]
    exact epi_comp _ _
  rw [← cancel_epi πB.left, ← Category.assoc, ← Over.comp_left, ← hc α hα, Over.comp_left,
    Category.assoc, hψ.π_ψ]
  rw [← FX_nat (X := B) (Y := B) α.left, ← Category.assoc, hψ.π_ψ]

/-- **`ThetaJacobianModel` from the five smaller named Props.** -/
theorem thetaJacobianModel_of_gaps (hΘ : ThetaDichotomy K) (hS : ThetaFrobStable K)
    (hJ : ThetaAlbanese K) (hC : FrobeniusCentral K) (hE : AbsFrobEpi K) :
    ThetaJacobianModel K := by
  intro W W' _ _ S S' ht hp hlt ℓ hℓ hodd hk v hv G n hPP
  obtain ⟨ψ, hψ⟩ := exists_twist S S' hℓ hk v hv (G n)
  have hdef : FrobDefined (G n).B ψ :=
    frobDefined_of_central hψ (hE (G n).B)
      (hC W W' S S' ht hp hlt ℓ hℓ hodd hk v hv n (G n))
  have := isAbelianVariety_tensor S.J S'.J
  have hfin : {x : Pt (S.J ⊗ S'.J) | x ≫ (G n).q = 1}.Finite := by
    have := finite_Γ (E := S.J) (E' := S'.J) ℓ v hℓ hk n
    have h : {x : Pt (S.J ⊗ S'.J) | x ≫ (G n).q = 1} = ((Γ ℓ v n : Subgroup _) : Set _) :=
      Set.ext fun x => (G n).ker x
    rw [h]
    exact Set.toFinite _
  rcases hΘ (G n).B S.J S'.J S.dim_J S'.dim_J (G n).q inferInstance (G n).surj hfin hPP with
    hTheta | hProd
  · obtain ⟨T⟩ := hTheta
    left
    obtain ⟨T', Ψ, hΨi, hΨ⟩ := hS (G n).B ((G n).πB S.π S'.π hv) ψ hψ hdef T
    exact ⟨{
      X := T'.X
      s := T'.incl ≫ (G n).B.hom
      isCurve := T'.isCurve
      geomIrred := T'.geomIrred
      smooth := T'.smooth
      proper := T'.proper
      projVar := T'.projVar
      projMor := T'.projMor
      genus_eq := T'.genus_eq
      Ψ := Ψ
      isIso_Ψ := hΨi
      hΨ := T'.hΨ hΨ hψ.base
      σ := T'.σ
      hσ := T'.hσ
      jac := hJ (G n).B ((G n).πB S.π S'.π hv) ψ hψ T' Ψ hΨi hΨ }⟩
  · rcases hProd with ⟨C₁, C₂, _, _, _, _, h₁, h₂, e, he⟩
    right
    exact prodJacModel_of_prodIso hψ hdef h₁ h₂ e

end RamanujanWeil.Arith.Deuring.Geom.G7.ThetaJ

end
