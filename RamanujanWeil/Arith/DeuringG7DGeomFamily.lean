import RamanujanWeil.Arith.DeuringG7DGeomKer
import RamanujanWeil.Arith.DeuringG7DFinal
import RamanujanWeil.Ihara.PointsCurve
import StacksFrontier.AlgebraicGeometry.Constructions.ProjectiveSpaceGeneratingSections

/-!
# A3-ord, G7-D-geom (family): the constructed theta family on `J_W`, and the split seam

`docs/ARITH_DEURING_G7DGEOM.md` §4–§5. For `W / 𝔽_q` put `k̄ = 𝔽̄_q`, `W̄ = W⁄k̄` and
`E = W̄⁄k̄` (Mathlib's point group `E(k̄)`).

* `curvePtFvp`: a `k̄`-point of the scheme `E_W` (a section of `E_W → Spec k̄`) as a `k̄`-valued
  point of the Weierstrass scheme over `𝔽_q`, so that `Ihara.fvpEquivPoint` reads it in `E(k̄)`.
* **`AbelJacobiMathlib S`** (named): Mathlib's chord–tangent group `E(k̄)` is the group `J_W(k̄)`
  through Abel–Jacobi `P ↦ 𝒪(P − O)`: an additive `e` with `e(fvp z) = aj ∘ z`.
* `torEquiv`: `e` restricted to `ℓⁿ⁺¹`-torsion.
* **`thetaFamilyOf`**: the **constructed** `ThetaFamily S.J ℓ`, `G_n = 𝒢(𝒪(ℓⁿ⁺¹·O))` of
  `DeuringG7DGeomTheta`, an extension of `E[ℓⁿ⁺¹] = K(L)` (`thetaKer_eq_torsion`) transported to
  `J_W[ℓⁿ⁺¹]`; it needs the three named inputs `DGeomGaps` (Abel–Jacobi compatibility, the
  divisor bridge, the Heisenberg property).
* **`PrincipallyPolarized k B`** (the interface for Θ): an invertible, ample `L` on `B` with
  `h⁰(L) = dim_k Γ(B, L) = 1`.
* The seam of `DeuringG7DCore` split as recommended in `ARITH_DEURING_G7D.md` §3:
  * **`ThetaLevelDescent K`** (descent): a level structure in `𝒢_n ×_{k̄^×} 𝒢'_n` over
    `graph(v_n)`, for the constructed families, makes every `B_n` principally polarized;
  * **`PrincipalFiniteness K`** (Θ + J + C): a `π`-equivariant family of principally polarized
    graph quotients has two equivariantly isomorphic members.
* **`thetaDescentFiniteness_of_split`** and **`deligneBound_of_split`**.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory
  CartesianMonoidalCategory
open WeierstrassCurve WeierstrassCurve.Affine
open scoped CategoryTheory.MonObj

universe u

noncomputable section

namespace RamanujanWeil.Arith.Deuring.Geom.G7.DGeom

open Stacks.Groupoids RamanujanWeil.Arith.Deuring.Geom.G7 RamanujanWeil.Arith.Deuring.Geom.G7.Fin
  RamanujanWeil.Arith.Deuring.Geom.G7.Fin.Weil RamanujanWeil.Ihara Stacks.EtaleCohomology
  Stacks.PicardFunctor AlgebraicGeometry.ModuliEllipticCurves.Weierstrass

open scoped Classical

/-! ### Principal polarizations -/

/-- **A principally polarized `B` (the interface for Θ).** An invertible ample `𝒪_B`-module `L`
with `h⁰(L) = dim_k Γ(B, L) = 1` (the `k`-structure on sections is through `B → Spec k`). -/
def PrincipallyPolarized (k : Type u) [Field k] (B : Over (Spec (.of k))) : Prop :=
  letI : B.left.Over (Spec (.of k)) := ⟨B.hom⟩
  ∃ (L : B.left.Modules) (_ : Stacks.Ample.IsInvertibleModule B.left L),
    Stacks.Ample.IsAmple B.left L ∧
    letI := Stacks.AlgebraicGeometry.ProjectiveSpaceGeneratingSections.globalSectionsModule k
      B.left L
    Module.finrank k Γ(L, ⊤) = 1

variable {K : Type u} [Field K] [Fintype K]

/-! ### The curve over `k̄` and Abel–Jacobi -/

section Curve

variable (W₀ : WeierstrassCurve K) [W₀.IsElliptic]

/-- `W̄ = W⁄k̄`. Its points `(W̄⁄k̄)(k̄)` are `(W⁄k̄)(k̄)` (definitionally). -/
abbrev Wbar : Affine (AlgebraicClosure K) := W₀.baseChange (AlgebraicClosure K)

instance : (Wbar W₀).IsElliptic :=
  inferInstanceAs (WeierstrassCurve.IsElliptic (W₀.map (algebraMap K (AlgebraicClosure K))))

variable (S : Jac.JacSite W₀)

/-- A `k̄`-point of the scheme `E_W = projOf W ×_K k̄`, as a `k̄`-valued point of `projOf W`. -/
def curvePtFvp (z : 𝟙_ (Over (Spec (.of (AlgebraicClosure K)))) ⟶ curveOver S.B S.hX S.hk S.f) :
    fieldValuedPoints (projectionOf W₀) (AlgebraicClosure K) :=
  ⟨(z.left : Spec (.of (AlgebraicClosure K)) ⟶ Jac.Ew W₀) ≫ pullback.fst _ _, by
    change (z.left : Spec (.of (AlgebraicClosure K)) ⟶ Jac.Ew W₀) ≫ pullback.fst _ _ ≫
      (Jac.Yw W₀).hom = _
    rw [pullback.condition, ← Category.assoc]
    have h1 : (z.left : Spec (.of (AlgebraicClosure K)) ⟶ Jac.Ew W₀) ≫ Jac.gw W₀ = 𝟙 _ := by
      have h0 := Over.w z
      simp at h0
      exact h0
    rw [h1, Category.id_comp]⟩

/-- **Abel–Jacobi compatibility (named).** Mathlib's chord–tangent group on `E(k̄)` is `J_W(k̄)`
through `P ↦ aj(P) = 𝒪(P − O)`: there is an additive bijection `e : E(k̄) ≃+ J_W(k̄)` with
`e(P_z) = aj ∘ z` for every section `z` of `E_W`, where `P_z = fvpEquivPoint (curvePtFvp z)`. -/
def AbelJacobiMathlib : Prop :=
  ∃ e : ((Wbar W₀)⁄(AlgebraicClosure K)).Point ≃+ Additive (Pt S.J),
    ∀ z, e (fvpEquivPoint W₀ (AlgebraicClosure K) (curvePtFvp W₀ S z)) =
      Additive.ofMul (z ≫ S.aj)

/-- `e` restricted to `N`-torsion. -/
def torEquiv (e : ((Wbar W₀)⁄(AlgebraicClosure K)).Point ≃+ Additive (Pt S.J)) (N : ℕ) :
    AddSubgroup.torsionBy ((Wbar W₀)⁄(AlgebraicClosure K)).Point (N : ℤ) ≃+ Tor S.J N where
  toFun x := ⟨e x.1, by
    change (N : ℤ) • e x.1 = 0
    rw [← map_zsmul]
    exact (congrArg e ((Submodule.mem_torsionBy_iff _ _).1 x.2)).trans (map_zero e)⟩
  invFun y := ⟨e.symm y.1, by
    change (N : ℤ) • e.symm y.1 = 0
    rw [← map_zsmul]
    exact (congrArg e.symm ((Submodule.mem_torsionBy_iff _ _).1 y.2)).trans (map_zero e.symm)⟩
  left_inv x := Subtype.ext (e.symm_apply_apply x.1)
  right_inv y := Subtype.ext (e.apply_symm_apply y.1)
  map_add' x y := Subtype.ext (map_add e x.1 y.1)

/-- **The three named inputs of D-geom** for `(W, S)` at `ℓ`. -/
structure DGeomGaps (ℓ : ℕ) : Prop where
  aj : AbelJacobiMathlib W₀ S
  bridge : ∀ n : ℕ, RRStabilizerBridge (Wbar W₀) (ℓ ^ (n + 1))
  heis : ∀ n : ℕ, ThetaHeisenberg (Wbar W₀) (ℓ ^ (n + 1))

/-- **The constructed theta family** on `J_W`: `G_n = 𝒢(𝒪(ℓⁿ⁺¹·O))` (the stabilizer of
`L(ℓⁿ⁺¹·O)` in `k̄(E)^× ⋊ E(k̄)`), with kernel `k̄^×` and quotient `K(L) = E[ℓⁿ⁺¹] ≅ J_W[ℓⁿ⁺¹]`. -/
def thetaFamilyOf {ℓ : ℕ} (h : DGeomGaps W₀ S ℓ) : ThetaFamily S.J ℓ where
  G n := thetaGroup (Wbar W₀) (rrSpace (Wbar W₀) (ℓ ^ (n + 1)))
  grp _ := inferInstance
  H n := CentralExtTransport.transport (thetaExtN (Wbar W₀) (ℓ ^ (n + 1)))
    ((torsionEquivThetaKer (Wbar W₀) (h.bridge n)).symm.trans (torEquiv W₀ S h.aj.choose _))
  hZ n g hg := (CentralExtTransport.transport_p_eq_one _ _ g).2 (h.heis n g hg)

theorem thetaFamilyOf_G {ℓ : ℕ} (h : DGeomGaps W₀ S ℓ) (n : ℕ) :
    (thetaFamilyOf W₀ S h).G n = thetaGroup (Wbar W₀) (rrSpace (Wbar W₀) (ℓ ^ (n + 1))) := rfl

end Curve

/-! ### The split seam -/

section Seam

variable (K)

open RamanujanWeil.Ihara RamanujanWeil.Arith.Deuring.Mult

/-- The D-geom inputs for every curve over `K` and every odd `ℓ` invertible in `k̄`. -/
def DGeomGapsAll : Prop :=
  ∀ (W : WeierstrassCurve K) [W.IsElliptic] (S : Jac.JacSite W) (ℓ : ℕ), ℓ.Prime → ℓ ≠ 2 →
    IsUnit (ℓ : AlgebraicClosure K) → DGeomGaps W S ℓ

/-- **Descent (named): level structure ⇒ principally polarized `B_n`.** For the constructed theta
families, a level subgroup of `𝒢_n ×_{k̄^×} 𝒢'_n` over `graph(v_n)` descends `L ⊠ L'` along
`J × J' → B_n` (Mumford §23 Thm 2), with theta group `Z(Γ̃)/Γ̃`, trivial by
`centralizer_of_antiIsom`; so `B_n` is principally polarized. -/
def ThetaLevelDescent : Prop :=
  ∀ (W W' : WeierstrassCurve K) [W.IsElliptic] [W'.IsElliptic] (S : Jac.JacSite W)
    (S' : Jac.JacSite W') (ℓ : ℕ) (h : DGeomGaps W S ℓ) (h' : DGeomGaps W' S' ℓ)
    (v : ∀ n : ℕ, Tor S.J (ℓ ^ (n + 1)) ≃+ Tor S'.J (ℓ ^ (n + 1))),
    (∀ n, Nonempty (CentralExt.GraphLevel ((thetaFamilyOf W S h).H n)
      ((thetaFamilyOf W' S' h').H n) (v n))) →
    ∀ (G : ∀ n, Glue (Γ ℓ v n)) (n : ℕ), PrincipallyPolarized (AlgebraicClosure K) (G n).B

/-- **Θ + J + C (named): principally polarized ⇒ finitely many.** A `π`-equivariant family of
principally polarized graph quotients `B_n` (each the Jacobian of a genus-2 curve by Θ + J, or a
product, killed by `DeuringG7FinProd`) has two equivariantly isomorphic members (C, C-Jac). -/
def PrincipalFiniteness : Prop :=
  ∀ (W W' : WeierstrassCurve K) [W.IsElliptic] [W'.IsElliptic] (S : Jac.JacSite W)
    (S' : Jac.JacSite W'), traceOfFrob W' = traceOfFrob W →
    ¬ (ringChar K : ℤ) ∣ traceOfFrob W → traceOfFrob W ^ 2 < 4 * (Nat.card K : ℤ) →
    ∀ ℓ : ℕ, ℓ.Prime → ℓ ≠ 2 → IsUnit (ℓ : AlgebraicClosure K) →
      ∀ (v : ∀ n : ℕ, Tor S.J (ℓ ^ (n + 1)) ≃+ Tor S'.J (ℓ ^ (n + 1)))
        (hv : ∀ n x, v n (torAct S.π _ x) = torAct S'.π _ (v n x)) (G : ∀ n, Glue (Γ ℓ v n)),
        (∀ n, PrincipallyPolarized (AlgebraicClosure K) (G n).B) →
        ∃ n m, n ≠ m ∧ ∃ e : (G n).B ≅ (G m).B,
          IsMonHom e.hom ∧ e.hom ≫ (G m).πB S.π S'.π hv = (G n).πB S.π S'.π hv ≫ e.hom

variable {K}

/-- **The seam of `DeuringG7DCore`, from the split**: the constructed theta families
(`thetaFamilyOf`) witness `ThetaDescentFiniteness`, given the D-geom inputs, descent, and
Θ + J + C. -/
theorem thetaDescentFiniteness_of_split (hG : DGeomGapsAll K) (hD : ThetaLevelDescent K)
    (hP : PrincipalFiniteness K) : ThetaDescentFiniteness K := by
  intro W W' _ _ S S' ht hp hlt ℓ hℓ hodd hk
  refine ⟨thetaFamilyOf W S (hG W S ℓ hℓ hodd hk), thetaFamilyOf W' S' (hG W' S' ℓ hℓ hodd hk),
    ?_⟩
  intro v hv hL G
  exact hP W W' S S' ht hp hlt ℓ hℓ hodd hk v hv G
    (hD W W' S S' ℓ (hG W S ℓ hℓ hodd hk) (hG W' S' ℓ hℓ hodd hk) v hL G)

end Seam

/-- The split at every finite field. -/
def DGeomSplitAll : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (n : ℕ), 1 ≤ n →
    letI : Fintype (GaloisField p n) := Fintype.ofFinite _
    DGeomGapsAll (GaloisField p n) ∧ ThetaLevelDescent (GaloisField p n) ∧
      PrincipalFiniteness (GaloisField p n)

/-- **Deligne's bound from the split D-geom / descent / Θ + J + C seams.** -/
theorem deligneBound_of_split (h : DGeomSplitAll) : RamanujanTau.DeligneBound :=
  deligneBound_of_thetaDescent fun p _ n hn =>
    letI : Fintype (GaloisField p n) := Fintype.ofFinite _
    have h' := h p n hn
    thetaDescentFiniteness_of_split h'.1 h'.2.1 h'.2.2

end RamanujanWeil.Arith.Deuring.Geom.G7.DGeom
