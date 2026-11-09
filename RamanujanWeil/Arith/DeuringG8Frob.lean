import RamanujanWeil.Arith.DeuringG8Lattice
import RamanujanWeil.Arith.DeuringMatrix

/-!
# A3-ord, G8(i) for Frobenius Jacobians, and the start of G8(ii)

`docs/ARITH_DEURING_G8.md` §4–5.

* `frobLattice_trDet`: for Frobenius Jacobians `J₀`, `J` of curves with the same trace `t`,
  `t² < 4q`, and nontrivial equivariant homomorphisms both ways, `L = Hom_π(J₀, J)` has a
  `ℤ`-basis on which Frobenius has a matrix in `TrDet t q`.
* `frobLattice_trDet_of_tate`: the two homomorphisms come from Tate (`TateFiniteness`) and
  `FrobHomDual`; **no zig-zag along the class and no matching of Jacobian sites is needed**,
  since Tate applies directly to any pair of curves of the same ordinary trace and any sites.
* **`exists_latticeMatrix`** (the `Λ` field of `DeuringClassLattice`): given `TateFiniteness`
  and `FrobHomDual`, a fixed curve `W₀` of trace `t` and a site `S₀`, there is
  `Λ : WeierstrassCurve K → TrDet t q` such that for every `W` of trace `t`, `Λ W` is the
  matrix of Frobenius on a `ℤ`-basis of `Hom_π(J_{W₀}, J_W)` (for a chosen site of `W`).
* G8(ii), first steps: `finrank_endPi_eq_two` (`End_π(J₀)` has rank two; with
  `G8.exists_zpow_eq_of_comm` this is `End_π(J₀) ⊗ ℚ = ℚ(π)`), and `postHom`, the map
  `Hom_π(A, A') → Hom_ℤ(Hom_π(A₀, A), Hom_π(A₀, A'))`, `φ ↦ (γ ↦ γ ≫ φ)`, which is additive,
  **injective** as soon as `Hom_π(A₀, A) ≠ 0`, and commutes with Frobenius (`postHom_piAct`).
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory Polynomial
open scoped CategoryTheory.MonObj

universe u

namespace RamanujanWeil.Arith.Deuring.G8

open RamanujanWeil.Ihara RamanujanWeil.Arith.Deuring.Geom RamanujanWeil.Arith.Deuring.Geom.G7
  RamanujanWeil.Arith.Deuring.Mult Stacks.Groupoids RamanujanWeil.Arith.Deuring.Dual2

section Frob

variable {K : Type u} [Field K] [Fintype K]

/-- **G8(i) for Frobenius Jacobians.** -/
theorem frobLattice_trDet {W₀ W : WeierstrassCurve K} [W₀.IsElliptic] [W.IsElliptic]
    (J₀ : FrobeniusJacobian W₀) (J : FrobeniusJacobian W)
    (ht : traceOfFrob W = traceOfFrob W₀)
    (hlt : traceOfFrob W₀ ^ 2 < 4 * (Nat.card K : ℤ))
    (h₁ : FrobHomNe J₀ J) (h₂ : FrobHomNe J J₀) :
    Module.finrank ℤ (homPi J₀.π J.π) = 2 ∧
    ∃ b : Module.Basis (Fin 2) ℤ (homPi J₀.π J.π),
      (LinearMap.toMatrix b b (piAct J₀.π J.π)).trace = traceOfFrob W₀ ∧
        (LinearMap.toMatrix b b (piAct J₀.π J.π)).det = (Nat.card K : ℤ) := by
  obtain ⟨α, hα, hαπ, hα1⟩ := h₁
  obtain ⟨β, hβ, hβπ, hβ1⟩ := h₂
  have hχ₀ := J₀.charPoly_eq
  have hχ := J.charPoly_eq
  rw [ht] at hχ
  exact ⟨(finrank_homPi_eq_two J₀.dim_eq J.dim_eq J₀.π J.π _ _ hχ₀ hχ hlt α hα1 hαπ β hβ1
      hβπ).2.2,
    exists_basis_trDet J₀.dim_eq J.dim_eq J₀.π J.π _ _ hχ₀ hχ hlt α hα1 hαπ β hβ1 hβπ⟩

/-- **G8(i) from Tate and G7-dual**, for any two Frobenius Jacobians of the same trace. -/
theorem frobLattice_trDet_of_tate (hdual : FrobHomDual.{u}) {W₀ W : WeierstrassCurve K}
    [W₀.IsElliptic] [W.IsElliptic] (J₀ : FrobeniusJacobian W₀) (J : FrobeniusJacobian W)
    (ht : traceOfFrob W = traceOfFrob W₀)
    (hlt : traceOfFrob W₀ ^ 2 < 4 * (Nat.card K : ℤ))
    (hfin : QuotientFiniteness (J₀.A ⊗ J.A) (πA J₀.π J.π)) :
    Module.finrank ℤ (homPi J₀.π J.π) = 2 ∧
    ∃ b : Module.Basis (Fin 2) ℤ (homPi J₀.π J.π),
      (LinearMap.toMatrix b b (piAct J₀.π J.π)).trace = traceOfFrob W₀ ∧
        (LinearMap.toMatrix b b (piAct J₀.π J.π)).det = (Nat.card K : ℤ) := by
  obtain ⟨h₁, h₂⟩ := tate_frobHomNe_both hdual J₀ J ht hlt hfin
  exact frobLattice_trDet J₀ J ht hlt h₁ h₂

set_option maxHeartbeats 2000000 in
/-- **The `Λ` field of `DeuringClassLattice`** (G8(i)): given `TateFiniteness` and
`FrobHomDual`, every curve `W` of the ordinary trace `t` of a fixed `W₀` gets the matrix of
Frobenius on a `ℤ`-basis of `L(W) = Hom_π(J_{W₀}, J_W)`, an element of `TrDet t q`. -/
theorem exists_latticeMatrix (hfin : TateFiniteness K) (hdual : FrobHomDual.{u})
    {W₀ : WeierstrassCurve K} [W₀.IsElliptic] (S₀ : Jac.JacSite W₀) (t : ℤ)
    (ht₀ : traceOfFrob W₀ = t) (hp : ¬ (ringChar K : ℤ) ∣ t)
    (hlt : t ^ 2 < 4 * (Nat.card K : ℤ)) :
    ∃ Λ : WeierstrassCurve K → RamanujanWeil.Arith.Deuring.TrDet t (Nat.card K),
      ∀ (W : WeierstrassCurve K) (hW : W.Δ ≠ 0), traceOfFrob W = t →
        haveI : W.IsElliptic := ⟨isUnit_iff_ne_zero.mpr hW⟩
        ∃ (S : Jac.JacSite W) (b : Module.Basis (Fin 2) ℤ
            (homPi S₀.frobeniusJacobian.π S.frobeniusJacobian.π)),
          (Λ W).1 = LinearMap.toMatrix b b
            (piAct S₀.frobeniusJacobian.π S.frobeniusJacobian.π) := by
  classical
  -- the companion matrix as junk value
  let M₀ : RamanujanWeil.Arith.Deuring.TrDet t (Nat.card K) := ⟨!![0, -(Nat.card K : ℤ); 1, t], by
    simp [Matrix.trace_fin_two], by simp [Matrix.det_fin_two]⟩
  have key : ∀ (W : WeierstrassCurve K) (hW : W.Δ ≠ 0), traceOfFrob W = t →
      haveI : W.IsElliptic := ⟨isUnit_iff_ne_zero.mpr hW⟩
      ∃ M : RamanujanWeil.Arith.Deuring.TrDet t (Nat.card K), ∃ (S : Jac.JacSite W) (b : Module.Basis (Fin 2) ℤ
            (homPi S₀.frobeniusJacobian.π S.frobeniusJacobian.π)),
          M.1 = LinearMap.toMatrix b b
            (piAct S₀.frobeniusJacobian.π S.frobeniusJacobian.π) := by
    intro W hW htW
    have : W.IsElliptic := ⟨isUnit_iff_ne_zero.mpr hW⟩
    obtain ⟨S⟩ := Jac.nonempty_jacSite W
    have ht : traceOfFrob W = traceOfFrob W₀ := htW.trans ht₀.symm
    have hlt' : traceOfFrob W₀ ^ 2 < 4 * (Nat.card K : ℤ) := by rw [ht₀]; exact hlt
    have hp' : ¬ (ringChar K : ℤ) ∣ traceOfFrob W₀ := by rw [ht₀]; exact hp
    obtain ⟨-, b, htr, hdet⟩ := frobLattice_trDet_of_tate hdual S₀.frobeniusJacobian
      S.frobeniusJacobian ht hlt' (hfin W₀ W S₀ S ht hp' hlt')
    exact ⟨⟨_, htr.trans ht₀, hdet⟩, S, b, rfl⟩
  refine ⟨fun W => if h : W.Δ ≠ 0 ∧ traceOfFrob W = t then (key W h.1 h.2).choose else M₀, ?_⟩
  intro W hW htW
  simp only [dif_pos (show W.Δ ≠ 0 ∧ traceOfFrob W = t from ⟨hW, htW⟩)]
  exact (key W hW htW).choose_spec

/-- `exists_latticeMatrix` with G7-dual supplied by `RadicialDual`. -/
theorem exists_latticeMatrix_of_radicialDual (hfin : TateFiniteness K)
    (hR : RadicialDual.{u}) {W₀ : WeierstrassCurve K} [W₀.IsElliptic] (S₀ : Jac.JacSite W₀)
    (t : ℤ) (ht₀ : traceOfFrob W₀ = t) (hp : ¬ (ringChar K : ℤ) ∣ t)
    (hlt : t ^ 2 < 4 * (Nat.card K : ℤ)) :
    ∃ Λ : WeierstrassCurve K → RamanujanWeil.Arith.Deuring.TrDet t (Nat.card K),
      ∀ (W : WeierstrassCurve K) (hW : W.Δ ≠ 0), traceOfFrob W = t →
        haveI : W.IsElliptic := ⟨isUnit_iff_ne_zero.mpr hW⟩
        ∃ (S : Jac.JacSite W) (b : Module.Basis (Fin 2) ℤ
            (homPi S₀.frobeniusJacobian.π S.frobeniusJacobian.π)),
          (Λ W).1 = LinearMap.toMatrix b b
            (piAct S₀.frobeniusJacobian.π S.frobeniusJacobian.π) :=
  exists_latticeMatrix hfin (frobHomDual_of_radicialDual hR) S₀ t ht₀ hp hlt

end Frob

/-! ### G8(ii): first steps -/

section HomTransfer

variable {k : Type u} [Field k] [IsAlgClosed k] {A₀ A A' : Over (Spec (.of k))} [GrpObj A₀]
  [GrpObj A] [GrpObj A'] [AlgebraicGeometry.IsAbelianVariety k A₀]
  [AlgebraicGeometry.IsAbelianVariety k A] [AlgebraicGeometry.IsAbelianVariety k A']
  {π₀ : A₀ ⟶ A₀} {π : A ⟶ A} {π' : A' ⟶ A'} [IsMonHom π₀] [IsMonHom π] [IsMonHom π']

/-- `γ ↦ γ ≫ φ` on `Hom_π(A₀, A)`, for an equivariant `φ : A ⟶ A'`. -/
noncomputable def postHom (φ : homPi π π') : homPi π₀ π →ₗ[ℤ] homPi π₀ π' where
  toFun x := homPi.mk (hm (x : homAV A₀ A) ≫ hm (φ : homAV A A')) (by
    have hx : hm (x : homAV A₀ A) ≫ π = π₀ ≫ hm (x : homAV A₀ A) := x.2
    have hφ : hm (φ : homAV A A') ≫ π' = π ≫ hm (φ : homAV A A') := φ.2
    rw [Category.assoc, hφ, ← Category.assoc, hx, Category.assoc])
  map_add' x y := homPi.ext (by
    show (hm (x : homAV A₀ A) * hm (y : homAV A₀ A)) ≫ hm (φ : homAV A A') = _
    rw [MonObj.mul_comp]
    rfl)
  map_smul' n x := homPi.ext (by
    show (hm (x : homAV A₀ A) ^ n) ≫ hm (φ : homAV A A') = _
    rw [GrpObj.zpow_comp]
    rfl)

theorem hm_postHom (φ : homPi π π') (x : homPi π₀ π) :
    hm ((postHom φ x : homPi π₀ π') : homAV A₀ A') =
      hm (x : homAV A₀ A) ≫ hm (φ : homAV A A') := rfl

/-- **`postHom φ` is a `ℤ[π]`-module map**: it commutes with Frobenius. -/
theorem postHom_piAct (φ : homPi π π') (x : homPi π₀ π) :
    postHom φ (piAct π₀ π x) = piAct π₀ π' (postHom φ x) := by
  apply homPi.ext
  rw [hm_postHom, hm_piAct, hm_piAct, hm_postHom, Category.assoc, Category.assoc]
  congr 1
  exact (φ.2 : hm (φ : homAV A A') ≫ π' = π ≫ hm (φ : homAV A A')).symm

/-- `φ ↦ postHom φ` is additive. -/
noncomputable def postHomAdd : homPi π π' →+ (homPi π₀ π →ₗ[ℤ] homPi π₀ π') where
  toFun := postHom
  map_zero' := by
    apply LinearMap.ext
    intro x
    apply homPi.ext
    rw [hm_postHom, hm_zero, MonObj.comp_one]
    rfl
  map_add' φ ψ := by
    apply LinearMap.ext
    intro x
    apply homPi.ext
    rw [LinearMap.add_apply, hm_add, hm_postHom, hm_postHom, hm_postHom, hm_add, MonObj.comp_mul]

/-- **`Hom_π(A, A') ↪ Hom_{ℤ[π]}(L(A), L(A'))`**: injective as soon as `L(A) ≠ 0`
(`G8(ii)`, injectivity half). -/
theorem postHomAdd_injective (hA₀ : abelianVarietyDimension A₀ = 1)
    (hA : abelianVarietyDimension A = 1) (x : homPi π₀ π) (hx : hm (x : homAV A₀ A) ≠ 1) :
    Function.Injective (postHomAdd (π₀ := π₀) (π := π) (π' := π')) := by
  rw [injective_iff_map_eq_zero]
  intro φ hφ
  by_contra hne
  have hφ1 : hm (φ : homAV A A') ≠ 1 := fun h1 => hne (homPi.ext (by rw [h1]; rfl))
  apply comp_ne_one hA₀ hA (hm (x : homAV A₀ A)) (hm (φ : homAV A A')) hx hφ1
  have := congrArg (fun f : homPi π₀ π →ₗ[ℤ] homPi π₀ π' => hm ((f x : homPi π₀ π') :
    homAV A₀ A')) hφ
  exact this

end HomTransfer

section EndPi

variable {k : Type u} [Field k] [IsAlgClosed k] {A₀ : Over (Spec (.of k))} [GrpObj A₀]
  [AlgebraicGeometry.IsAbelianVariety k A₀]

/-- **`End_π(A₀)` is free of rank two** (`χ_π = X² − tX + q`, `t² < 4q`). -/
theorem finrank_endPi_eq_two (hA₀ : abelianVarietyDimension A₀ = 1) (π₀ : A₀ ⟶ A₀)
    [IsMonHom π₀] (t : ℤ) (q : ℕ)
    (hχ₀ : endCharPoly A₀ π₀ = Polynomial.X ^ 2 - C (t : ℚ) * Polynomial.X + C (q : ℚ)) (hdisc : t ^ 2 < 4 * (q : ℤ)) :
    Module.finrank ℤ (homPi π₀ π₀) = 2 :=
  (finrank_homPi_eq_two hA₀ hA₀ π₀ π₀ t q hχ₀ hχ₀ hdisc (𝟙 A₀) (id_ne_one hA₀) (by simp)
    (𝟙 A₀) (id_ne_one hA₀) (by simp)).2.2

end EndPi

section Surj

variable {k : Type u} [Field k] [IsAlgClosed k] {A₀ A A' : Over (Spec (.of k))} [GrpObj A₀]
  [GrpObj A] [GrpObj A'] [AlgebraicGeometry.IsAbelianVariety k A₀]
  [AlgebraicGeometry.IsAbelianVariety k A] [AlgebraicGeometry.IsAbelianVariety k A']
  {π₀ : A₀ ⟶ A₀} {π : A ⟶ A} {π' : A' ⟶ A'} [IsMonHom π₀] [IsMonHom π] [IsMonHom π']

/-- `L(A) ⊗ ℚ = ℚ(π)·α`: every `γ ∈ Hom_π(A₀, A)` has a nonzero multiple in `ℤα + ℤ(α ≫ π)`,
given a dual `β` (`α ≫ β = [n]`). -/
theorem exists_smul_eq_of_dual (hA₀ : abelianVarietyDimension A₀ = 1)
    (hA : abelianVarietyDimension A = 1) (t q : ℤ)
    (hπ₀ : endPolyEval π₀ (Polynomial.X ^ 2 - C t * Polynomial.X + C q) = 1) (hdisc : t ^ 2 < 4 * q)
    (α : A₀ ⟶ A) [IsMonHom α] (hα : α ≠ 1) (hαπ : α ≫ π = π₀ ≫ α)
    (β : A ⟶ A₀) [IsMonHom β] (n : ℤ) (hn : n ≠ 0) (hαβ : α ≫ β = (𝟙 A₀) ^ n)
    (hβπ : β ≫ π₀ = π ≫ β) (g₀ : homPi π₀ π) :
    ∃ N : ℤ, N ≠ 0 ∧ ∃ u v : ℤ,
      N • g₀ = u • homPi.mk α hαπ + v • piAct π₀ π (homPi.mk α hαπ) := by
  have hg₀ : hm (g₀ : homAV A₀ A) ≫ π = π₀ ≫ hm (g₀ : homAV A₀ A) := g₀.2
  have hcomm : (hm (g₀ : homAV A₀ A) ≫ β) ≫ π₀ = π₀ ≫ (hm (g₀ : homAV A₀ A) ≫ β) := by
    rw [Category.assoc, hβπ, ← Category.assoc, hg₀, Category.assoc]
  obtain ⟨N, a, b, hN, hNe⟩ :=
    exists_zpow_eq_of_comm hA₀ π₀ (hm (g₀ : homAV A₀ A) ≫ β) t q hπ₀ hdisc hcomm
  have hβα : β ≫ α = (𝟙 A) ^ n := comp_eq_zpow_symm hA₀ hA α hα β n hαβ
  have h1 : ((hm (g₀ : homAV A₀ A) ≫ β) ^ N) ≫ α = (π₀ ^ b * (𝟙 A₀) ^ a) ≫ α := by rw [hNe]
  rw [GrpObj.zpow_comp, Category.assoc, hβα, comp_zpow_id, MonObj.mul_comp, GrpObj.zpow_comp,
    GrpObj.zpow_comp, ← hαπ, Category.id_comp, ← zpow_mul] at h1
  refine ⟨n * N, mul_ne_zero hn hN, a, b, homPi.ext ?_⟩
  change hm (g₀ : homAV A₀ A) ^ (n * N) = α ^ a * (α ≫ π) ^ b
  rw [h1, mul_comm]

/-- **G8(ii), surjectivity up to `n`**: every `ℤ[π]`-linear map `f : L(A) → L(A')` is, after
multiplication by `n` (`α ≫ β = [n]`), of the form `g₀ ↦ g₀ ≫ φ` for an equivariant
`φ : A ⟶ A'`. With `postHomAdd_injective` this is
`Hom_π(A, A') ⊗ ℚ ≅ Hom_{ℚ(π)}(L(A) ⊗ ℚ, L(A') ⊗ ℚ)`. -/
theorem exists_postHom_eq_smul (hA₀ : abelianVarietyDimension A₀ = 1)
    (hA : abelianVarietyDimension A = 1) (t q : ℤ)
    (hπ₀ : endPolyEval π₀ (Polynomial.X ^ 2 - C t * Polynomial.X + C q) = 1) (hdisc : t ^ 2 < 4 * q)
    (α : A₀ ⟶ A) [IsMonHom α] (hα : α ≠ 1) (hαπ : α ≫ π = π₀ ≫ α)
    (β : A ⟶ A₀) [IsMonHom β] (n : ℤ) (hn : n ≠ 0) (hαβ : α ≫ β = (𝟙 A₀) ^ n)
    (hβπ : β ≫ π₀ = π ≫ β) (f : homPi π₀ π →ₗ[ℤ] homPi π₀ π')
    (hf : ∀ x, f (piAct π₀ π x) = piAct π₀ π' (f x)) :
    ∃ φ : homPi π π', postHom φ = n • f := by
  set g := hm ((f (homPi.mk α hαπ) : homPi π₀ π') : homAV A₀ A') with hg
  have hgπ : g ≫ π' = π₀ ≫ g := (f (homPi.mk α hαπ)).2
  let φ : homPi π π' := homPi.mk (β ≫ g) (by
    rw [Category.assoc, hgπ, ← Category.assoc, hβπ, Category.assoc])
  refine ⟨φ, ?_⟩
  set D := postHom φ - n • f with hD
  have hDa : D (homPi.mk α hαπ) = 0 := by
    rw [hD, LinearMap.sub_apply, sub_eq_zero]
    apply homPi.ext
    change α ≫ β ≫ g = g ^ n
    rw [← Category.assoc, hαβ, GrpObj.zpow_comp, Category.id_comp]
  have hDpi : ∀ x, D (piAct π₀ π x) = piAct π₀ π' (D x) := by
    intro x
    rw [hD, LinearMap.sub_apply, LinearMap.sub_apply, map_sub, postHom_piAct,
      LinearMap.smul_apply, LinearMap.smul_apply, hf, map_zsmul]
  have htf : ∀ (N : ℤ) (z : homPi π₀ π'), N ≠ 0 → N • z = 0 → z = 0 := by
    intro N z hN hz
    apply homPi.ext
    have h1 := congrArg (fun w : homPi π₀ π' => hm (w : homAV A₀ A')) hz
    change hm (z : homAV A₀ A') ^ N = 1 at h1
    exact eq_one_of_zpow_eq_one hA₀ _ N hN h1
  apply LinearMap.ext
  intro g₀
  rw [← sub_eq_zero]
  change D g₀ = 0
  obtain ⟨N, hN, u, v, huv⟩ :=
    exists_smul_eq_of_dual hA₀ hA t q hπ₀ hdisc α hα hαπ β n hn hαβ hβπ g₀
  apply htf N _ hN
  rw [← map_zsmul, huv, map_add, map_zsmul, map_zsmul, hDpi, hDa, map_zero, smul_zero,
    smul_zero, add_zero]

end Surj

end RamanujanWeil.Arith.Deuring.G8
