import StacksFrontier.AlgebraicGeometry.Curves.NonsingularProjectiveModelUniqueness
import StacksFrontier.AlgebraicGeometry.MoreMorphisms.LocalCompleteIntersection.RegularSchemes
import StacksFrontier.AlgebraicGeometry.Descent.SchemeProperty.Regular
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.RingTheory.AdjoinRoot

/-!
# A3-ord, G7-C: genus-2 curves over a finite field are finite in number, modulo the model step

`docs/ARITH_DEURING_G7_WC.md`, step **C** of route F2′ (`docs/ARITH_DEURING_G7FIN.md` §4).

A genus-2 curve `Y / K` has a hyperelliptic model: its function field is
`K(x)[y]/(y² + h(x) y − f(x))` with `deg h ≤ 3`, `deg f ≤ 6` (the canonical map `Y → ℙ¹` has
degree 2 and `x` is the quotient of two canonical differentials). Over a finite `K` there are
finitely many such `(h, f)`, and Stacks' uniqueness of the nonsingular projective model
(`AlgebraicGeometry.exists_iso_of_functionFieldEquiv`, Tag 0BY1) turns equal models into
isomorphic curves. So finiteness reduces to the existence of the model.

* `HypModel K`: coefficient vectors `(h₀..h₃, f₀..f₆)`; `HypModel.hPoly`, `HypModel.fPoly`,
  `natDegree_hPoly_le`, `natDegree_fPoly_le`, `exists_hypModel_eq` (every pair of polynomials of
  degrees `≤ 3`, `≤ 6` is one), `finite_hypModel` for finite `K`.
* `HypModel.eqn`, `HypModel.FunField`: `y² + h y − f` over `K(x)` and its root algebra.
* `HasHypModel s`: the function field of `Y` is `K`-isomorphic to some `FunField m`.
* **`Genus2ModelExistence K`** (named, the Riemann–Roch step): every smooth proper
  geometrically irreducible curve of genus 2 over `K` has a hyperelliptic model.
* **`exists_iso_of_hypModel`**: two regular proper curves with the same model are isomorphic.
* **`exists_ne_iso_of_hasHypModel`**: in any sequence of regular proper curves over a finite
  field with hyperelliptic models, two are isomorphic over `K`.
* **`exists_ne_iso_of_genus_eq_two`**: the same for smooth proper geometrically irreducible
  curves of genus 2, from `Genus2ModelExistence K`.
-/

universe u

open AlgebraicGeometry CategoryTheory Polynomial

namespace RamanujanWeil.Arith.Deuring.Geom.G7.Genus2

variable {K : Type u} [Field K]

/-- **A hyperelliptic model** `y² + h(x) y = f(x)`, `deg h ≤ 3`, `deg f ≤ 6`, by coefficients. -/
@[ext]
structure HypModel (K : Type u) where
  /-- The coefficients of `h`. -/
  h : Fin 4 → K
  /-- The coefficients of `f`. -/
  f : Fin 7 → K

/-- `HypModel K ≃ K⁴ × K⁷`. -/
def HypModel.equivProd : HypModel K ≃ (Fin 4 → K) × (Fin 7 → K) where
  toFun m := (m.h, m.f)
  invFun p := ⟨p.1, p.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- **Finitely many models over a finite field.** -/
instance finite_hypModel [Finite K] : Finite (HypModel K) :=
  Finite.of_equiv _ HypModel.equivProd.symm

namespace HypModel

/-- `h(x)`. -/
noncomputable def hPoly (m : HypModel K) : K[X] := ∑ i : Fin 4, C (m.h i) * Polynomial.X ^ (i : ℕ)

/-- `f(x)`. -/
noncomputable def fPoly (m : HypModel K) : K[X] := ∑ i : Fin 7, C (m.f i) * Polynomial.X ^ (i : ℕ)

theorem natDegree_sum_le {n : ℕ} (a : Fin (n + 1) → K) :
    (∑ i : Fin (n + 1), C (a i) * Polynomial.X ^ (i : ℕ)).natDegree ≤ n := by
  refine natDegree_sum_le_of_forall_le _ _ fun i _ => ?_
  exact (natDegree_C_mul_X_pow_le _ _).trans (Nat.lt_succ_iff.1 i.2)

theorem natDegree_hPoly_le (m : HypModel K) : m.hPoly.natDegree ≤ 3 := natDegree_sum_le m.h

theorem natDegree_fPoly_le (m : HypModel K) : m.fPoly.natDegree ≤ 6 := natDegree_sum_le m.f

theorem sum_coeff_eq {n : ℕ} (p : K[X]) (hp : p.natDegree ≤ n) :
    ∑ i : Fin (n + 1), C (p.coeff i) * Polynomial.X ^ (i : ℕ) = p := by
  conv_rhs => rw [p.as_sum_range' (n + 1) (Nat.lt_succ_of_le hp)]
  rw [← Fin.sum_univ_eq_sum_range (fun i => monomial i (p.coeff i))]
  simp only [C_mul_X_pow_eq_monomial]

/-- Every pair of polynomials of degrees `≤ 3`, `≤ 6` is a model. -/
theorem exists_hypModel_eq (h f : K[X]) (hh : h.natDegree ≤ 3) (hf : f.natDegree ≤ 6) :
    ∃ m : HypModel K, m.hPoly = h ∧ m.fPoly = f :=
  ⟨⟨fun i => h.coeff i, fun i => f.coeff i⟩, sum_coeff_eq h hh, sum_coeff_eq f hf⟩

/-- The equation `y² + h(x) y − f(x)` over `K(x)`. -/
noncomputable def eqn (m : HypModel K) : (RatFunc K)[X] :=
  Polynomial.X ^ 2 + C (algebraMap K[X] (RatFunc K) m.hPoly) * Polynomial.X -
    C (algebraMap K[X] (RatFunc K) m.fPoly)

/-- **The function field of the model**, `K(x)[y]/(y² + h y − f)`, as a `K`-algebra. -/
abbrev FunField (m : HypModel K) : Type u := AdjoinRoot m.eqn

end HypModel

/-- The function field of `Y / K` is that of some hyperelliptic model. -/
def HasHypModel {Y : Scheme.{u}} (s : Y ⟶ Spec (.of K)) [IsCurve K s] : Prop :=
  letI := functionFieldAlgebra K s
  ∃ m : HypModel K, Nonempty (Y.functionField ≃ₐ[K] m.FunField)

/-- **The model step of C (named; the Riemann–Roch input).** Every smooth proper geometrically
irreducible curve of genus 2 over `K` has a hyperelliptic model with `deg h ≤ 3`,
`deg f ≤ 6`. Classical proof: `h⁰(K_Y) = 2` and `|K_Y|` is base point free of degree 2
(Riemann–Roch), so `x = ω₁/ω₂` has degree 2; `K(Y)/K(x)` is quadratic, and a generator `y`
integral over `K[x]` with pole order `≤ 3` at the two points over `x = ∞` gives the bounds. -/
def Genus2ModelExistence (K : Type u) [Field K] : Prop :=
  ∀ (Y : Scheme.{u}) (s : Y ⟶ Spec (.of K)) [IsCurve K s] [Smooth s] [IsProper s]
    [GeometricallyIrreducible s], genus s = 2 → HasHypModel s

/-- **Equal models give isomorphic curves** (Stacks 0BY1). -/
theorem exists_iso_of_hypModel {Y Y' : Scheme.{u}} (s : Y ⟶ Spec (.of K))
    (s' : Y' ⟶ Spec (.of K)) [IsCurve K s] [IsCurve K s'] [IsProper s] [IsProper s']
    (hY : IsRegular Y) (hY' : IsRegular Y') (m : HypModel K)
    (e : letI := functionFieldAlgebra K s; Y.functionField ≃ₐ[K] m.FunField)
    (e' : letI := functionFieldAlgebra K s'; Y'.functionField ≃ₐ[K] m.FunField) :
    ∃ φ : Y ≅ Y', φ.hom ≫ s' = s :=
  letI := functionFieldAlgebra K s
  letI := functionFieldAlgebra K s'
  exists_iso_of_functionFieldEquiv K s s' hY hY' (e.trans e'.symm)

/-- **Pigeonhole over the models.** Among infinitely many regular proper curves over a finite
field, each with a hyperelliptic model, two are isomorphic over `K`. -/
theorem exists_ne_iso_of_hasHypModel [Finite K] (Y : ℕ → Scheme.{u})
    (s : ∀ n, Y n ⟶ Spec (.of K)) [∀ n, IsCurve K (s n)] [∀ n, IsProper (s n)]
    (hreg : ∀ n, IsRegular (Y n)) (hm : ∀ n, HasHypModel (s n)) :
    ∃ n m, n ≠ m ∧ ∃ φ : Y n ≅ Y m, φ.hom ≫ s m = s n := by
  choose M hM using hm
  obtain ⟨n, m, hnm, hM'⟩ := Finite.exists_ne_map_eq_of_infinite M
  obtain ⟨e⟩ := hM n
  obtain ⟨e'⟩ := hM m
  refine ⟨n, m, hnm, ?_⟩
  rw [hM'] at e
  exact exists_iso_of_hypModel (s n) (s m) (hreg n) (hreg m) (M m) e e'

/-- A smooth scheme over a field is regular. -/
theorem isRegular_of_smooth_field {Y : Scheme.{u}} (s : Y ⟶ Spec (.of K)) [Smooth s] :
    IsRegular Y :=
  isRegular_of_smooth s inferInstance ((isRegular_spec_iff _).2 inferInstance)

/-- **Finiteness of genus-2 curves over `𝔽_q`**, modulo `Genus2ModelExistence`: among
infinitely many smooth proper geometrically irreducible curves of genus 2 over a finite field,
two are isomorphic over `K`. -/
theorem exists_ne_iso_of_genus_eq_two [Finite K] (hC : Genus2ModelExistence K)
    (Y : ℕ → Scheme.{u}) (s : ∀ n, Y n ⟶ Spec (.of K)) [∀ n, IsCurve K (s n)]
    [∀ n, Smooth (s n)] [∀ n, IsProper (s n)] [∀ n, GeometricallyIrreducible (s n)]
    (hg : ∀ n, genus (s n) = 2) :
    ∃ n m, n ≠ m ∧ ∃ φ : Y n ≅ Y m, φ.hom ≫ s m = s n :=
  exists_ne_iso_of_hasHypModel Y s (fun n => isRegular_of_smooth_field (s n))
    (fun n => hC (Y n) (s n) (hg n))

end RamanujanWeil.Arith.Deuring.Geom.G7.Genus2
