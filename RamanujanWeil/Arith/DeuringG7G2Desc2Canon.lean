import RamanujanWeil.Arith.DeuringG7Genus2Descent

/-!
# A3-ord, G7 C-descent: canonical stability from rigidity of the hyperelliptic model

`docs/ARITH_DEURING_G7_G2DESCENT.md` §6. Target: `Genus2FrobCanonical K`
(`Arith/DeuringG7Genus2Descent.lean`).

The Frobenius `τ = Ψ^♯` is a `σ`-semilinear **automorphism** of `L = k̄(X)`. It carries a
hyperelliptic presentation `(x, y; h, f)` to another one, `(τx, τy; h^σ, f^σ)`
(`pres_frob`, `e₂_frob_eq_top`). So canonical stability is the special case `x' = τ x`,
`y' = τ y` of the classical, Frobenius-free statement that any two hyperelliptic presentations
of a genus-2 function field differ by a model change:

* **`Genus2PresRigid K`** (named): for presentations `(x, y)`, `(x', y')` of `k̄(X)`,
  `x' (c x + d) = a x + b` and `y' (c x + d)³ = e y + p(x)` (`ad − bc ≠ 0`, `e ≠ 0`,
  `deg p ≤ 3`).

Proved here:

* `frobFF_bijective`: `Ψ^♯` is bijective (`Ψ` is an isomorphism, so its stalk map at the generic
  point is an isomorphism, and `Ψ` fixes the generic point).
* `frobQ_surjective`: `c ↦ c^q` is onto `K̄`.
* `pres_frob`, `e₂_frob_eq_top`: transport of presentations by any bijective semilinear `τ`.
* **`genus2FrobCanonical_of_presRigid`**: `Genus2PresRigid K → Genus2FrobCanonical K`.
* **`genus2FrobDescent_of_presRigid_of_fixed`**: `Genus2PresRigid K → Genus2FixedDescent K →
  Genus2FrobDescent K`.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Polynomial Stacks.Frobenius

universe u v

noncomputable section

namespace RamanujanWeil.Arith.Deuring.Geom.G7.Genus2Descent.Desc2

open RamanujanWeil.Arith.Deuring.Geom RamanujanWeil.Arith.Deuring.Geom.G7
  RamanujanWeil.Arith.Deuring.Geom.G7.PrincipalFin RamanujanWeil.Ihara
  RamanujanWeil.Arith.Deuring.Descent RamanujanWeil.Arith.Deuring.Geom.Descent
  RamanujanWeil.Arith.Deuring.Geom.G7.Genus2Descent

attribute [local instance] RamanujanWeil.Ihara.fact_ringChar_prime

set_option linter.unusedSectionVars false

/-! ## Transport of presentations by a bijective semilinear map -/

section Transport

variable {K : Type u} [Field K] [Fintype K]
variable {L : Type v} [Field L] [Algebra (AlgebraicClosure K) L]

local notation "ι" => algebraMap (AlgebraicClosure K) L

theorem frobQ_surjective : Function.Surjective (frobQ (K := K)) := by
  intro c
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq c (Fintype.card_pos (α := K))
  exact ⟨z, by rw [frobQ_apply, hz]⟩

variable {τ : L →+* L} (hτ : IsFrobSemilinear K τ)
include hτ

theorem τ_algebraMap (c : AlgebraicClosure K) : τ (ι c) = ι (frobQ c) := by
  rw [frobQ_apply]; exact hτ c

/-- The image of `K̄(x)` under `τ`, as an intermediate field. -/
def imageE (x : L) : IntermediateField (AlgebraicClosure K) L :=
  ((E K x).toSubfield.map τ).toIntermediateField (by
    intro c
    obtain ⟨c', rfl⟩ := frobQ_surjective (K := K) c
    exact ⟨ι c', (E K x).algebraMap_mem c', τ_algebraMap hτ c'⟩)

theorem E_frob_le (x : L) : E K (τ x) ≤ imageE hτ x := by
  rw [IntermediateField.adjoin_simple_le_iff]
  exact ⟨x, IntermediateField.mem_adjoin_simple_self _ x, rfl⟩

/-- The preimage of `K̄(τx, τy)` under `τ`, as an intermediate field. -/
def preimageE₂ (x y : L) : IntermediateField (AlgebraicClosure K) L :=
  ((E₂ K (τ x) (τ y)).toSubfield.comap τ).toIntermediateField (by
    intro c
    show τ (ι c) ∈ E₂ K (τ x) (τ y)
    rw [τ_algebraMap hτ]
    exact (E₂ K (τ x) (τ y)).algebraMap_mem _)

theorem E₂_le_preimage (x y : L) : E₂ K x y ≤ preimageE₂ hτ x y := by
  rw [IntermediateField.adjoin_le_iff]
  intro w hw
  rcases hw with rfl | rfl
  · exact IntermediateField.subset_adjoin _ _ (by simp)
  · exact IntermediateField.subset_adjoin _ _ (by simp)

/-- **`τ` carries a presentation to a presentation.** -/
theorem pres_frob {x y : L} {h f : (AlgebraicClosure K)[X]} (hP : Pres x y h f) :
    Pres (τ x) (τ y) (h.map frobQ) (f.map frobQ) where
  rel := by
    have := congrArg τ hP.rel
    rwa [map_add, map_mul, map_pow, τ_aeval hτ, τ_aeval hτ] at this
  deg_h := (natDegree_map_le).trans hP.deg_h
  deg_f := (natDegree_map_le).trans hP.deg_f
  trans := by
    rintro ⟨P, hP0, hPx⟩
    obtain ⟨Q, rfl⟩ := Polynomial.map_surjective _ (frobQ_surjective (K := K)) P
    apply hP.trans
    refine ⟨Q, fun hQ => hP0 (by rw [hQ, Polynomial.map_zero]), ?_⟩
    apply τ.injective
    rw [τ_aeval hτ, map_zero]
    exact hPx
  not_mem := by
    intro hy
    obtain ⟨w, hw, hwy⟩ := E_frob_le hτ x hy
    have : w = y := τ.injective hwy
    exact hP.not_mem (this ▸ hw)

/-- **`τ` carries a generating pair to a generating pair** (when `τ` is onto). -/
theorem e₂_frob_eq_top (hsurj : Function.Surjective τ) {x y : L} (hE : E₂ K x y = ⊤) :
    E₂ K (τ x) (τ y) = ⊤ := by
  rw [eq_top_iff]
  intro w _
  obtain ⟨w', rfl⟩ := hsurj w
  have : w' ∈ E₂ K x y := hE ▸ IntermediateField.mem_top
  exact E₂_le_preimage hτ x y this

end Transport

/-! ## `Ψ^♯` is bijective -/

section Bij

variable {K : Type u} [Field K] [Fintype K]

theorem isIso_stalkSpecializes {X : Scheme.{u}} {a b : X} (h : a ⤳ b) (hab : a = b) :
    IsIso (X.presheaf.stalkSpecializes h) := by
  subst hab
  rw [TopCat.Presheaf.stalkSpecializes_refl]
  infer_instance

theorem frobFF_bijective {X : Scheme.{u}} (s : X ⟶ Spec (.of (AlgebraicClosure K)))
    [IsCurve (AlgebraicClosure K) s] (Ψ : X ⟶ X) [IsIso Ψ] :
    Function.Bijective (frobFF s Ψ) := by
  haveI := isIntegral_of_isCurve s
  have h1 : IsIso (X.presheaf.stalkSpecializes (specializes_genericPoint_of_isDominant Ψ)) :=
    isIso_stalkSpecializes _ (genericPoint_eq_of_isDominant Ψ)
  have h2 : IsIso (Ψ.stalkMap (genericPoint X)) :=
    ((isIso_iff_isIso_stalkMap Ψ).mp inferInstance).2 _
  have : IsIso Ψ.functionFieldMap := by
    unfold Scheme.Hom.functionFieldMap
    infer_instance
  exact ConcreteCategory.bijective_of_isIso Ψ.functionFieldMap

end Bij

/-! ## The named Prop and the reduction -/

variable (K : Type u) [Field K] [Fintype K]

/-- **Rigidity of the hyperelliptic model (named).** Any two hyperelliptic presentations
`(x, y)`, `(x', y')` of the function field of a genus-2 curve over `k̄` differ by a model change:
`x' = (a x + b)/(c x + d)`, `y' = (e y + p(x))/(c x + d)³`.

This is Frobenius-free. Mathematically: `k̄(x)` and `k̄(x')` are fixed fields of the
hyperelliptic involution (the `g¹₂` is unique, `= |K_X|`), so `x'` is Möbius in `x`; and
`H⁰(3 K_X) = ⟨1, x, x², x³, y⟩`, which is mapped to `(c x + d)⁻³ H⁰(3 K_X)`. -/
def Genus2PresRigid : Prop :=
  ∀ (X : Scheme.{u}) (s : X ⟶ Spec (.of (AlgebraicClosure K)))
    [IsCurve (AlgebraicClosure K) s] [GeometricallyIrreducible s] [Smooth s] [IsProper s],
    genus s = 2 →
      letI := functionFieldAlgebra (AlgebraicClosure K) s
      ∀ (x y x' y' : X.functionField) (h f h' f' : (AlgebraicClosure K)[X]),
        Pres x y h f → E₂ K x y = ⊤ → Pres x' y' h' f' → E₂ K x' y' = ⊤ →
        ∃ a b c d : AlgebraicClosure K, a * d - b * c ≠ 0 ∧
          ∃ e : AlgebraicClosure K, e ≠ 0 ∧ ∃ p : (AlgebraicClosure K)[X], p.natDegree ≤ 3 ∧
            x' * (algebraMap _ _ c * x + algebraMap _ _ d) =
              algebraMap _ _ a * x + algebraMap _ _ b ∧
            y' * (algebraMap _ _ c * x + algebraMap _ _ d) ^ 3 =
              algebraMap _ _ e * y + aeval x p

/-- **Canonical stability from rigidity.** -/
theorem genus2FrobCanonical_of_presRigid (hR : Genus2PresRigid K) : Genus2FrobCanonical K := by
  intro X s _ _ _ _ hg Ψ _ hΨ
  letI := functionFieldAlgebra (AlgebraicClosure K) s
  intro x y h f hP hE
  have hτ := isFrobSemilinear_frobFF s Ψ hΨ
  exact hR X s hg x y _ _ h f _ _ hP hE (pres_frob hτ hP)
    (e₂_frob_eq_top hτ (frobFF_bijective s Ψ).2 hE)

/-- **C-descent from rigidity and fixed-generator descent.** -/
theorem genus2FrobDescent_of_presRigid_of_fixed (hR : Genus2PresRigid K)
    (hF : Genus2FixedDescent K) : Genus2FrobDescent K :=
  genus2FrobDescent_of_canonical_of_fixed K (genus2FrobCanonical_of_presRigid K hR) hF

end RamanujanWeil.Arith.Deuring.Geom.G7.Genus2Descent.Desc2
