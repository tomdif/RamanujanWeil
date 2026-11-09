import RamanujanWeil.Arith.DeuringG8End

/-!
# A3-ord, G8(i): `L(E) = Hom_π(E₀, E)` is free of rank two, with Frobenius matrix in `TrDet t q`

`docs/ARITH_DEURING_G8.md` §3. Let `A₀`, `A` be one-dimensional abelian varieties over an
algebraically closed field with endomorphisms `π₀`, `π` of characteristic polynomial
`X² − tX + q`, `t² < 4q`, and suppose there are nonzero equivariant homomorphisms
`α : A₀ ⟶ A` and `β : A ⟶ A₀`. Then:

* `homPi π₀ π ⊆ homAV A₀ A` (the `ℤ`-module `Hom_π(A₀, A)`) is finitely generated and free of
  **rank two** (`finrank_homPi_eq_two`):
  * `≥ 2`: `α` and `α ≫ π` are independent, because `deg(a + bπ) = a² + abt + b²q > 0`;
  * `≤ 2`: `γ ↦ γ ≫ β` embeds it into `End_π(A₀)`, which has rank `≤ 2` by
    `G8.exists_zpow_eq_of_comm` (`End_π(A₀) ⊗ ℚ = ℚ(π₀)`).
* `piAct`: postcomposition with `π` on `Hom_π(A₀, A)`; it satisfies `X² − tX + q` and is not a
  scalar, so on any basis its matrix has **trace `t` and determinant `q`**
  (`exists_basis_trDet`).

For Frobenius Jacobians (`DeuringG2.FrobeniusJacobian`) the two homomorphisms come from Tate
(`tate_exists_frobHom`) plus G7-dual (`FrobHomDual`, or `Dual2.RadicialDual`):
`frobLattice_trDet`, `frobLattice_trDet_of_radicialDual`.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory Polynomial
open scoped CategoryTheory.MonObj

universe u

namespace RamanujanWeil.Arith.Deuring.G8

open RamanujanWeil.Arith.Deuring.Geom Stacks.Groupoids RamanujanWeil.Arith.Deuring.Dual2

section HomPi

variable {k : Type u} [Field k] [IsAlgClosed k] {A₀ A : Over (Spec (.of k))} [GrpObj A₀]
  [GrpObj A] [AlgebraicGeometry.IsAbelianVariety k A₀] [AlgebraicGeometry.IsAbelianVariety k A]

/-- The homomorphism underlying an element of `homAV`. -/
abbrev hm (x : homAV A₀ A) : A₀ ⟶ A := Additive.toMul (x : Additive (A₀ ⟶ A))

variable (π₀ : A₀ ⟶ A₀) (π : A ⟶ A) [IsMonHom π₀] [IsMonHom π]

/-- **`Hom_π(A₀, A)`**: the equivariant homomorphisms, as a `ℤ`-submodule of `homAV A₀ A`. -/
def homPi : Submodule ℤ (homAV A₀ A) where
  carrier := {x | hm x ≫ π = π₀ ≫ hm x}
  add_mem' := by
    intro x y hx hy
    have hx' : Additive.toMul (x : Additive (A₀ ⟶ A)) ≫ π =
        π₀ ≫ Additive.toMul (x : Additive (A₀ ⟶ A)) := hx
    have hy' : Additive.toMul (y : Additive (A₀ ⟶ A)) ≫ π =
        π₀ ≫ Additive.toMul (y : Additive (A₀ ⟶ A)) := hy
    show Additive.toMul ((x + y : homAV A₀ A) : Additive (A₀ ⟶ A)) ≫ π =
      π₀ ≫ Additive.toMul ((x + y : homAV A₀ A) : Additive (A₀ ⟶ A))
    rw [homAV.toMul_add, MonObj.mul_comp, MonObj.comp_mul, hx', hy']
  zero_mem' := by
    show (1 : A₀ ⟶ A) ≫ π = π₀ ≫ (1 : A₀ ⟶ A)
    rw [MonObj.one_comp, MonObj.comp_one]
  smul_mem' := by
    intro n x hx
    have hx' : Additive.toMul (x : Additive (A₀ ⟶ A)) ≫ π =
        π₀ ≫ Additive.toMul (x : Additive (A₀ ⟶ A)) := hx
    show Additive.toMul ((n • x : homAV A₀ A) : Additive (A₀ ⟶ A)) ≫ π =
      π₀ ≫ Additive.toMul ((n • x : homAV A₀ A) : Additive (A₀ ⟶ A))
    rw [homAV.toMul_zsmul, GrpObj.zpow_comp, GrpObj.comp_zpow, hx']

variable {π₀ π}

theorem mem_homPi {x : homAV A₀ A} : x ∈ homPi π₀ π ↔ hm x ≫ π = π₀ ≫ hm x := Iff.rfl

/-- The element of `Hom_π` given by an equivariant homomorphism. -/
noncomputable def homPi.mk (α : A₀ ⟶ A) [IsMonHom α] (h : α ≫ π = π₀ ≫ α) : homPi π₀ π :=
  ⟨homAV.mk α, h⟩

theorem homPi.ext {x y : homPi π₀ π} (h : hm (x : homAV A₀ A) = hm (y : homAV A₀ A)) : x = y :=
  Subtype.ext (homAV.ext_toMul h)

theorem hm_add (x y : homPi π₀ π) :
    hm ((x + y : homPi π₀ π) : homAV A₀ A) = hm (x : homAV A₀ A) * hm (y : homAV A₀ A) := rfl

theorem hm_zsmul (n : ℤ) (x : homPi π₀ π) :
    hm ((n • x : homPi π₀ π) : homAV A₀ A) = hm (x : homAV A₀ A) ^ n := rfl

theorem hm_zero : hm ((0 : homPi π₀ π) : homAV A₀ A) = 1 := rfl

variable (π₀ π) in
/-- **Postcomposition with `π`** on `Hom_π(A₀, A)`. -/
noncomputable def piAct : homPi π₀ π →ₗ[ℤ] homPi π₀ π where
  toFun x := homPi.mk (hm (x : homAV A₀ A) ≫ π) (by
    have hx : hm (x : homAV A₀ A) ≫ π = π₀ ≫ hm (x : homAV A₀ A) := x.2
    rw [hx, Category.assoc, hx])
  map_add' x y := homPi.ext (by
    show (hm (x : homAV A₀ A) * hm (y : homAV A₀ A)) ≫ π = _
    rw [MonObj.mul_comp]
    rfl)
  map_smul' n x := homPi.ext (by
    show (hm (x : homAV A₀ A) ^ n) ≫ π = _
    rw [GrpObj.zpow_comp]
    rfl)

theorem hm_piAct (x : homPi π₀ π) :
    hm ((piAct π₀ π x : homPi π₀ π) : homAV A₀ A) = hm (x : homAV A₀ A) ≫ π := rfl

end HomPi

/-! ### Finiteness, freeness and rank -/

section Rank

variable {k : Type u} [Field k] [IsAlgClosed k] {A₀ A : Over (Spec (.of k))} [GrpObj A₀]
  [GrpObj A] [AlgebraicGeometry.IsAbelianVariety k A₀] [AlgebraicGeometry.IsAbelianVariety k A]

theorem homPi_finite_free (hA₀ : abelianVarietyDimension A₀ = 1)
    (hA : abelianVarietyDimension A = 1) (hd : HomDualHyp A₀ A) (π₀ : A₀ ⟶ A₀) (π : A ⟶ A)
    [IsMonHom π₀] [IsMonHom π] :
    Module.Finite ℤ (homPi π₀ π) ∧ Module.Free ℤ (homPi π₀ π) := by
  obtain ⟨h1, h2, -⟩ := homAV_finite_free hA₀ hA hd
  have : IsNoetherian ℤ (homAV A₀ A) := isNoetherian_of_isNoetherianRing_of_finite ℤ _
  have : Module.Finite ℤ (homPi π₀ π) := Module.IsNoetherian.finite ℤ _
  exact ⟨this, inferInstance⟩

/-- Characteristic-polynomial data of an endomorphism `π` with `χ_π = X² − tX + q`. -/
theorem charPoly_data (hA : abelianVarietyDimension A = 1) (π : A ⟶ A) [IsMonHom π] (t : ℤ)
    (q : ℕ) (hχ : endCharPoly A π = Polynomial.X ^ 2 - C (t : ℚ) * Polynomial.X + C (q : ℚ)) :
    endPolyEval π (Polynomial.X ^ 2 - C t * Polynomial.X + C (q : ℤ)) = 1 ∧ endDegree A π = q ∧
      abelianVarietyTrace A π = t := by
  refine ⟨endPolyEval_eq_one_of_endCharPoly_eq hA π _ (by rw [hχ]; simp), ?_, ?_⟩
  · have h := coeff_zero_endCharPoly A π
    rw [hχ] at h
    simp at h
    exact_mod_cast h.symm
  · have h := endCharPoly_eq_of_dim_one hA π
    rw [hχ] at h
    have h1 := congrArg (fun f => Polynomial.coeff f 1) h
    simp at h1
    linarith

/-- `a + bπ = 0 ⇒ a = b = 0`, from `deg(a + bπ) = a² + abt + b²q` and `t² < 4q`. -/
theorem eq_zero_of_zpow_mul_zpow_eq_one (hA : abelianVarietyDimension A = 1) (π : A ⟶ A)
    [IsMonHom π] (t : ℤ) (q : ℕ) (hdeg : endDegree A π = q) (htr : abelianVarietyTrace A π = t)
    (hdisc : t ^ 2 < 4 * (q : ℤ)) (u v : ℤ) (h : π ^ v * (𝟙 A) ^ u = 1) : u = 0 ∧ v = 0 := by
  have hd := endDegree_zpow_mul_zpow hA π v u
  have : IsMonHom (π ^ v * (𝟙 A) ^ u) := isMonHom_mul _ _
  rw [h, endDegree_one hA, hdeg, htr] at hd
  have hd' : (0 : ℤ) = v ^ 2 * q + v * u * t + u ^ 2 := by exact_mod_cast hd
  have h4 : v ^ 2 * (4 * q - t ^ 2) = -(2 * u + v * t) ^ 2 := by linear_combination (-4) * hd'
  have hv : v = 0 := by
    by_contra hv
    have h5 : 0 < v ^ 2 := by positivity
    have h6 : 0 < v ^ 2 * (4 * q - t ^ 2) := mul_pos h5 (by linarith)
    nlinarith [sq_nonneg (2 * u + v * t)]
  subst hv
  refine ⟨?_, rfl⟩
  have hu : u ^ 2 = 0 := by linarith
  exact pow_eq_zero_iff (two_ne_zero) |>.mp hu

/-- **G8(i): `Hom_π(A₀, A)` is free of rank two.** -/
theorem finrank_homPi_eq_two (hA₀ : abelianVarietyDimension A₀ = 1)
    (hA : abelianVarietyDimension A = 1) (π₀ : A₀ ⟶ A₀) (π : A ⟶ A) [IsMonHom π₀] [IsMonHom π]
    (t : ℤ) (q : ℕ) (hχ₀ : endCharPoly A₀ π₀ = Polynomial.X ^ 2 - C (t : ℚ) * Polynomial.X + C (q : ℚ))
    (hχ : endCharPoly A π = Polynomial.X ^ 2 - C (t : ℚ) * Polynomial.X + C (q : ℚ)) (hdisc : t ^ 2 < 4 * (q : ℤ))
    (α : A₀ ⟶ A) [IsMonHom α] (hα : α ≠ 1) (hαπ : α ≫ π = π₀ ≫ α)
    (β : A ⟶ A₀) [IsMonHom β] (hβ : β ≠ 1) (hβπ : β ≫ π₀ = π ≫ β) :
    Module.Finite ℤ (homPi π₀ π) ∧ Module.Free ℤ (homPi π₀ π) ∧
      Module.finrank ℤ (homPi π₀ π) = 2 := by
  obtain ⟨hπ₀, -, -⟩ := charPoly_data hA₀ π₀ t q hχ₀
  obtain ⟨-, hdeg, htr⟩ := charPoly_data hA π t q hχ
  have hd : HomDualHyp A₀ A := Or.inr ⟨β, inferInstance, hβ⟩
  obtain ⟨hfin, hfree⟩ := homPi_finite_free hA₀ hA hd π₀ π
  obtain ⟨hfin₀, hfree₀⟩ := homPi_finite_free hA₀ hA₀ (homDualHyp_self hA₀) π₀ π₀
  refine ⟨hfin, hfree, le_antisymm ?_ ?_⟩
  · -- `≤ 2`: embed into `End_π(A₀)`
    let Φ : homPi π₀ π →ₗ[ℤ] homPi π₀ π₀ :=
      { toFun := fun x => homPi.mk (hm (x : homAV A₀ A) ≫ β) (by
          have hx : hm (x : homAV A₀ A) ≫ π = π₀ ≫ hm (x : homAV A₀ A) := x.2
          rw [Category.assoc, hβπ, ← Category.assoc, hx, Category.assoc])
        map_add' := fun x y => homPi.ext (by
          show (hm (x : homAV A₀ A) * hm (y : homAV A₀ A)) ≫ β = _
          rw [MonObj.mul_comp]; rfl)
        map_smul' := fun n x => homPi.ext (by
          show (hm (x : homAV A₀ A) ^ n) ≫ β = _
          rw [GrpObj.zpow_comp]; rfl) }
    have hΦ : Function.Injective Φ := by
      rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
      intro x hx
      by_contra hne
      have hx1 : hm (x : homAV A₀ A) ≠ 1 := fun h1 => hne (homPi.ext (by rw [h1]; rfl))
      apply comp_ne_one hA₀ hA (hm (x : homAV A₀ A)) β hx1 hβ
      exact congrArg (fun z : homPi π₀ π₀ => hm (z : homAV A₀ A₀)) hx
    have h1 := LinearMap.finrank_le_finrank_of_injective hΦ
    have h2 : Module.finrank ℤ (homPi π₀ π₀) ≤ 2 := by
      apply finrank_le_two_of_torsion_quotient (homPi.mk (𝟙 A₀) (by simp))
        (homPi.mk π₀ rfl)
      intro e
      obtain ⟨N, a, b, hN, hNe⟩ := exists_zpow_eq_of_comm hA₀ π₀ (hm (e : homAV A₀ A₀)) t q hπ₀
        hdisc e.2
      refine ⟨N, hN, a, b, homPi.ext ?_⟩
      rw [hm_zsmul, hm_add, hm_zsmul, hm_zsmul, hNe]
      show π₀ ^ b * (𝟙 A₀) ^ a = (𝟙 A₀) ^ a * π₀ ^ b
      exact mul_comm _ _
    exact h1.trans h2
  · -- `≥ 2`: `α`, `α ≫ π` are independent
    have hind : LinearIndependent ℤ ![homPi.mk α hαπ, piAct π₀ π (homPi.mk α hαπ)] := by
      rw [LinearIndependent.pair_iff]
      intro u v huv
      have h1 := congrArg (fun z : homPi π₀ π => hm (z : homAV A₀ A)) huv
      change α ^ u * (α ≫ π) ^ v = 1 at h1
      have h2 : α ≫ (π ^ v * (𝟙 A) ^ u) = 1 := by
        rw [MonObj.comp_mul, comp_zpow_id, GrpObj.comp_zpow, mul_comm, h1]
      have : IsMonHom (π ^ v * (𝟙 A) ^ u) := isMonHom_mul _ _
      have h3 : π ^ v * (𝟙 A) ^ u = 1 := by
        by_contra hne
        exact comp_ne_one hA₀ hA α _ hα hne h2
      exact eq_zero_of_zpow_mul_zpow_eq_one hA π t q hdeg htr hdisc u v h3
    have := hind.fintype_card_le_finrank
    simpa using this

/-- **G8(i), matrix form**: on a `ℤ`-basis of `Hom_π(A₀, A)` the matrix of `π` has trace `t`
and determinant `q`. -/
theorem exists_basis_trDet (hA₀ : abelianVarietyDimension A₀ = 1)
    (hA : abelianVarietyDimension A = 1) (π₀ : A₀ ⟶ A₀) (π : A ⟶ A) [IsMonHom π₀] [IsMonHom π]
    (t : ℤ) (q : ℕ) (hχ₀ : endCharPoly A₀ π₀ = Polynomial.X ^ 2 - C (t : ℚ) * Polynomial.X + C (q : ℚ))
    (hχ : endCharPoly A π = Polynomial.X ^ 2 - C (t : ℚ) * Polynomial.X + C (q : ℚ)) (hdisc : t ^ 2 < 4 * (q : ℤ))
    (α : A₀ ⟶ A) [IsMonHom α] (hα : α ≠ 1) (hαπ : α ≫ π = π₀ ≫ α)
    (β : A ⟶ A₀) [IsMonHom β] (hβ : β ≠ 1) (hβπ : β ≫ π₀ = π ≫ β) :
    ∃ b : Module.Basis (Fin 2) ℤ (homPi π₀ π),
      (LinearMap.toMatrix b b (piAct π₀ π)).trace = t ∧
        (LinearMap.toMatrix b b (piAct π₀ π)).det = q := by
  obtain ⟨hfin, hfree, hrank⟩ :=
    finrank_homPi_eq_two hA₀ hA π₀ π t q hχ₀ hχ hdisc α hα hαπ β hβ hβπ
  obtain ⟨hπ, hdeg, htr⟩ := charPoly_data hA π t q hχ
  let b : Module.Basis (Fin 2) ℤ (homPi π₀ π) := Module.finBasisOfFinrankEq ℤ _ hrank
  refine ⟨b, linearMap_trace_det_of_sq_eq b _ t q ?_ ?_⟩
  · -- `π² − tπ + q = 0` on `Hom_π`
    apply LinearMap.ext
    intro x
    have h1 : endPolyEval π (Polynomial.X * Polynomial.X + C (-t) * Polynomial.X + C (q : ℤ)) = 1 := by
      rw [← hπ]
      congr 1
      rw [Polynomial.C_neg]
      ring
    rw [endPolyEval_add, endPolyEval_add, endPolyEval_mul, endPolyEval_mul, endPolyEval_X,
      endPolyEval_C, endPolyEval_C] at h1
    have h2 := congrArg (fun f => hm (x : homAV A₀ A) ≫ f) h1
    simp only [MonObj.comp_mul, MonObj.comp_one, ← Category.assoc, comp_zpow_id, GrpObj.comp_zpow] at h2
    have hz : piAct π₀ π (piAct π₀ π x) + (-t) • piAct π₀ π x + (q : ℤ) • x = 0 := by
      apply homPi.ext
      change ((hm (x : homAV A₀ A) ≫ π) ≫ π) * (hm (x : homAV A₀ A) ≫ π) ^ (-t) *
        hm (x : homAV A₀ A) ^ ((q : ℕ) : ℤ) = 1
      exact h2
    simp only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.smul_apply,
      LinearMap.id_apply]
    rw [← sub_eq_zero, ← hz, neg_smul]
    abel
  · intro c hc
    have h1 := congrArg (fun f => hm ((f (homPi.mk α hαπ) : homPi π₀ π) : homAV A₀ A)) hc
    change α ≫ π = α ^ c at h1
    have h2 : α ≫ (π ^ (1 : ℤ) * (𝟙 A) ^ (-c)) = 1 := by
      rw [MonObj.comp_mul, comp_zpow_id, GrpObj.comp_zpow, zpow_one, h1, zpow_neg,
        mul_inv_cancel]
    have : IsMonHom (π ^ (1 : ℤ) * (𝟙 A) ^ (-c)) := isMonHom_mul _ _
    have h3 : π ^ (1 : ℤ) * (𝟙 A) ^ (-c) = 1 := by
      by_contra hne
      exact comp_ne_one hA₀ hA α _ hα hne h2
    have := (eq_zero_of_zpow_mul_zpow_eq_one hA π t q hdeg htr hdisc (-c) 1 h3).2
    exact one_ne_zero this

end Rank

end RamanujanWeil.Arith.Deuring.G8
