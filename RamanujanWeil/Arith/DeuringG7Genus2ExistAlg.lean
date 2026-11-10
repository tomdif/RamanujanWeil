import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.RingTheory.Polynomial.RationalRoot
import Mathlib.Algebra.Polynomial.Reverse

/-!
# A3-ord, G7-C: the algebra of the genus-2 model (function-field side)

`docs/ARITH_DEURING_G7_GENUS2.md`. Let `F / K` be a field extension, `x ∈ F` transcendental
over `K` with `[F : K(x)] ≤ 2`, and `V₀ ⊆ V₁ ⊆ …` finite-dimensional `K`-subspaces of `F` with
`1 ∈ V₀`, `1, x ∈ V₁`, `Vₐ·V_b ⊆ V_{a+b}` (the images of `H⁰(ω^{⊗n})` under `s ↦ s/ω₀ⁿ`).
If `dim V₃ ≥ 5`, `dim V₆ ≤ 11` and `V₃ ∩ K(x) ⊆ ⟨1, x, x², x³⟩` (the pole condition), then
`F ≅ K(x)[y]/(y² + h(x) y − f(x))` with `deg h ≤ 3`, `deg f ≤ 6`.

This file is pure algebra (Mathlib only).

* `linearIndependent_pow_pow_mul`: `x^i, x^j y` are `K`-independent when `x` is transcendental
  and `y ∉ K(x)`.
* `exists_relation`: if they lie with `y²` in a space of dimension `≤ 11`, then
  `y² + h(x) y = f(x)` with `deg h ≤ 3`, `deg f ≤ 6`.
* `exists_not_mem_adjoin`: a `y ∈ V₃ ∖ K(x)` from `dim V₃ ≥ 5` and the pole condition.
* `quadEqn`, **`nonempty_algEquiv_adjoinRoot`**: the `K`-algebra isomorphism
  `AdjoinRoot (y² + h y − f) ≃ₐ[K] F` over `RatFunc K`.
* `PencilData`, **`PencilData.exists_model`**: the packaged statement.
* `exists_aeval_eq_of_isIntegralElem` (`K[x]` is integrally closed in `K(x)`),
  `transcendental_inv`, **`mem_cubicSpan_of_isIntegralElem`**: the pole condition from
  integrality of `f` over `K[x]` and of `f/x³` over `K[x⁻¹]`;
  `IntegralPencilData`, `IntegralPencilData.toPencilData`.
-/

open Polynomial
open scoped nonZeroDivisors

namespace RamanujanWeil.Arith.Deuring.Geom.G7.Genus2.Exist

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

/-- `∑ i < n, c i X^i`. -/
noncomputable def finPoly {n : ℕ} (c : Fin n → K) : K[X] :=
  ∑ i : Fin n, C (c i) * X ^ (i : ℕ)

theorem coeff_finPoly {n : ℕ} (c : Fin n → K) (i : Fin n) : (finPoly c).coeff i = c i := by
  classical
  unfold finPoly
  rw [finsetSum_coeff]
  simp_rw [coeff_C_mul_X_pow]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    simp only [ite_eq_right_iff]
    exact fun h => absurd (Fin.ext h.symm) hj
  · simp

theorem aeval_finPoly {n : ℕ} (c : Fin n → K) (x : F) :
    aeval x (finPoly c) = ∑ i : Fin n, c i • x ^ (i : ℕ) := by
  unfold finPoly
  simp [map_sum, Algebra.smul_def]

theorem natDegree_finPoly_le {n : ℕ} (c : Fin (n + 1) → K) : (finPoly c).natDegree ≤ n := by
  refine natDegree_sum_le_of_forall_le _ _ fun i _ => ?_
  exact (natDegree_C_mul_X_pow_le _ _).trans (Nat.lt_succ_iff.1 i.2)

theorem mem_adjoin_of_eq {x y : F} (p q : K[X]) (hq : aeval x q ≠ 0)
    (h : aeval x p + aeval x q * y = 0) : y ∈ IntermediateField.adjoin K {x} := by
  rw [IntermediateField.mem_adjoin_simple_iff]
  refine ⟨-p, q, ?_⟩
  rw [map_neg, eq_div_iff hq]
  linear_combination h

/-- **`x^i` (`i < m`) and `x^j y` (`j < n`) are `K`-linearly independent** when `x` is
transcendental over `K` and `y ∉ K(x)`. -/
theorem linearIndependent_pow_pow_mul {x y : F} (hx : Transcendental K x)
    (hy : y ∉ IntermediateField.adjoin K {x}) (m n : ℕ) :
    LinearIndependent K
      (Sum.elim (fun i : Fin m => x ^ (i : ℕ)) (fun j : Fin n => x ^ (j : ℕ) * y)) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  rw [Fintype.sum_sum_type] at hg
  simp only [Sum.elim_inl, Sum.elim_inr] at hg
  set P := finPoly (fun i : Fin m => g (Sum.inl i))
  set Q := finPoly (fun j : Fin n => g (Sum.inr j))
  have hrel : aeval x P + aeval x Q * y = 0 := by
    rw [aeval_finPoly, aeval_finPoly, Finset.sum_mul, ← hg]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [smul_mul_assoc]
  have hQ : aeval x Q = 0 := by
    by_contra hQ
    exact hy (mem_adjoin_of_eq P Q hQ hrel)
  rw [hQ, zero_mul, add_zero] at hrel
  have hP0 := (transcendental_iff.1 hx) P hrel
  have hQ0 := (transcendental_iff.1 hx) Q hQ
  rintro (i | j)
  · rw [← coeff_finPoly (fun i : Fin m => g (Sum.inl i)) i]
    change P.coeff i = 0
    rw [hP0, coeff_zero]
  · rw [← coeff_finPoly (fun j : Fin n => g (Sum.inr j)) j]
    change Q.coeff j = 0
    rw [hQ0, coeff_zero]

/-- **The relation.** If `x^i` (`i ≤ 6`), `x^j y` (`j ≤ 3`) and `y²` lie in a `K`-subspace of
dimension `≤ 11`, then `y² + h(x) y = f(x)` with `deg h ≤ 3`, `deg f ≤ 6`. -/
theorem exists_relation {x y : F} (hx : Transcendental K x)
    (hy : y ∉ IntermediateField.adjoin K {x}) (W : Submodule K F) [FiniteDimensional K W]
    (hW : Module.finrank K W ≤ 11) (hxW : ∀ i ≤ 6, x ^ i ∈ W) (hxyW : ∀ j ≤ 3, x ^ j * y ∈ W)
    (hyW : y ^ 2 ∈ W) :
    ∃ h f : K[X], h.natDegree ≤ 3 ∧ f.natDegree ≤ 6 ∧ y ^ 2 + aeval x h * y = aeval x f := by
  set v : Fin 7 ⊕ Fin 4 → F :=
    Sum.elim (fun i : Fin 7 => x ^ (i : ℕ)) (fun j : Fin 4 => x ^ (j : ℕ) * y) with hv
  have hvW : ∀ k, v k ∈ W := by
    rintro (i | j)
    · exact hxW i (Nat.lt_succ_iff.1 i.2)
    · exact hxyW j (Nat.lt_succ_iff.1 j.2)
  let w : Fin 7 ⊕ Fin 4 → W := fun k => ⟨v k, hvW k⟩
  have hli : LinearIndependent K w := by
    refine LinearIndependent.of_comp W.subtype ?_
    exact linearIndependent_pow_pow_mul hx hy 7 4
  have hcard : Fintype.card (Fin 7 ⊕ Fin 4) = Module.finrank K W := by
    have := hli.fintype_card_le_finrank
    simp only [Fintype.card_sum, Fintype.card_fin] at this ⊢
    omega
  have hspan := hli.span_eq_top_of_card_eq_finrank hcard
  have hmem : (⟨y ^ 2, hyW⟩ : W) ∈ Submodule.span K (Set.range w) := by
    rw [hspan]; trivial
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun K).1 hmem
  have hc' : ∑ k, c k • v k = y ^ 2 := by
    have := congrArg W.subtype hc
    simpa [map_sum] using this
  rw [Fintype.sum_sum_type] at hc'
  simp only [hv, Sum.elim_inl, Sum.elim_inr] at hc'
  refine ⟨-finPoly (fun j : Fin 4 => c (Sum.inr j)), finPoly (fun i : Fin 7 => c (Sum.inl i)),
    by rw [natDegree_neg]; exact natDegree_finPoly_le _, natDegree_finPoly_le _, ?_⟩
  rw [map_neg, aeval_finPoly, aeval_finPoly, ← hc', neg_mul, Finset.sum_mul]
  simp only [smul_mul_assoc]
  abel

/-- `⟨1, x, x², x³⟩`. -/
def cubicSpan (K : Type*) {F : Type*} [Field K] [Field F] [Algebra K F] (x : F) :
    Submodule K F :=
  Submodule.span K (Set.range fun i : Fin 4 => x ^ (i : ℕ))

instance (x : F) : FiniteDimensional K (cubicSpan K x) :=
  FiniteDimensional.span_of_finite K (Set.finite_range _)

theorem finrank_cubicSpan_le (x : F) : Module.finrank K (cubicSpan K x) ≤ 4 := by
  unfold cubicSpan
  exact (finrank_range_le_card _).trans (by simp)

/-- **A generator from the pole condition.** If `dim V ≥ 5` and `V ∩ K(x) ⊆ ⟨1, x, x², x³⟩`,
some `y ∈ V` is not in `K(x)`. -/
theorem exists_not_mem_adjoin (x : F) (V : Submodule K F) [FiniteDimensional K V]
    (hV : 5 ≤ Module.finrank K V)
    (hpole : ∀ f ∈ V, f ∈ IntermediateField.adjoin K {x} → f ∈ cubicSpan K x) :
    ∃ y ∈ V, y ∉ IntermediateField.adjoin K {x} := by
  by_contra hcon
  push Not at hcon
  have hle : V ≤ cubicSpan K x := fun f hf => hpole f hf (hcon f hf)
  have := Submodule.finrank_mono hle
  have h4 := finrank_cubicSpan_le (K := K) x
  omega

/-! ### The isomorphism with `AdjoinRoot` -/

/-- `y² + h y − f` over `K(x)`, written exactly as `HypModel.eqn`. -/
noncomputable def quadEqn (h f : K[X]) : (RatFunc K)[X] :=
  Polynomial.X ^ 2 + C (algebraMap K[X] (RatFunc K) h) * Polynomial.X -
    C (algebraMap K[X] (RatFunc K) f)

theorem le_comap_nonZeroDivisors {x : F} (hx : Transcendental K x) :
    K[X]⁰ ≤ F⁰.comap (aeval x : K[X] →ₐ[K] F) := by
  intro p hp
  refine mem_nonZeroDivisors_of_ne_zero fun h0 => ?_
  exact nonZeroDivisors.ne_zero hp ((transcendental_iff.1 hx) p h0)

/-- `K(x) ≅ RatFunc K`: the map `RatFunc K → F`, `X ↦ x`. -/
noncomputable def ratFuncHom {x : F} (hx : Transcendental K x) : RatFunc K →ₐ[K] F :=
  RatFunc.liftAlgHom (aeval x : K[X] →ₐ[K] F) (le_comap_nonZeroDivisors hx)

theorem ratFuncHom_algebraMap {x : F} (hx : Transcendental K x) (p : K[X]) :
    ratFuncHom hx (algebraMap K[X] (RatFunc K) p) = aeval x p := by
  have := RatFunc.liftAlgHom_apply_div (aeval x : K[X] →ₐ[K] F) (le_comap_nonZeroDivisors hx)
    p 1
  rw [map_one, div_one, map_one, div_one] at this
  exact this

theorem ratFuncHom_mem_adjoin {x : F} (hx : Transcendental K x) (r : RatFunc K) :
    ratFuncHom hx r ∈ IntermediateField.adjoin K {x} := by
  rw [IntermediateField.mem_adjoin_simple_iff]
  exact ⟨r.num, r.denom, RatFunc.liftAlgHom_apply _ _ r⟩

theorem exists_ratFuncHom_eq {x : F} (hx : Transcendental K x) {z : F}
    (hz : z ∈ IntermediateField.adjoin K {x}) : ∃ r, ratFuncHom hx r = z := by
  rw [IntermediateField.mem_adjoin_simple_iff] at hz
  obtain ⟨p, q, rfl⟩ := hz
  refine ⟨algebraMap K[X] (RatFunc K) p / algebraMap K[X] (RatFunc K) q, ?_⟩
  rw [map_div₀, ratFuncHom_algebraMap, ratFuncHom_algebraMap]

theorem eval₂_quadEqn {x : F} (hx : Transcendental K x) (h f : K[X]) (z : F) :
    (quadEqn h f).eval₂ (ratFuncHom hx).toRingHom z = z ^ 2 + aeval x h * z - aeval x f := by
  unfold quadEqn
  simp only [eval₂_sub, eval₂_add, eval₂_mul, eval₂_pow, eval₂_X, eval₂_C, AlgHom.toRingHom_eq_coe,
    AlgHom.coe_toRingHom, ratFuncHom_algebraMap]

theorem irreducible_quadEqn {x y : F} (hx : Transcendental K x)
    (hy : y ∉ IntermediateField.adjoin K {x}) (h f : K[X])
    (hyeq : y ^ 2 + aeval x h * y = aeval x f) : Irreducible (quadEqn h f) := by
  have hdeg : (quadEqn h f).natDegree = 2 := by
    unfold quadEqn
    rw [add_sub_assoc]
    have hq : (C (algebraMap K[X] (RatFunc K) h) * Polynomial.X -
        C (algebraMap K[X] (RatFunc K) f)).natDegree < (Polynomial.X ^ 2 : (RatFunc K)[X]).natDegree := by
      rw [natDegree_X_pow]
      refine lt_of_le_of_lt (natDegree_sub_le _ _) ?_
      rw [natDegree_C, max_lt_iff]
      exact ⟨lt_of_le_of_lt ((natDegree_C_mul_le _ _).trans natDegree_X_le) (by norm_num),
        by norm_num⟩
    rw [natDegree_add_eq_left_of_natDegree_lt hq, natDegree_X_pow]
  refine irreducible_of_degree_le_three_of_not_isRoot (by rw [hdeg]; decide) fun r hr => ?_
  have h0 : (quadEqn h f).eval₂ (ratFuncHom hx).toRingHom ((ratFuncHom hx).toRingHom r) = 0 := by
    rw [eval₂_at_apply, hr.eq_zero, map_zero]
  rw [eval₂_quadEqn] at h0
  set z := (ratFuncHom hx).toRingHom r with hz
  have hfac : (z - y) * (z + y + aeval x h) = 0 := by linear_combination h0 - hyeq
  rcases mul_eq_zero.1 hfac with h1 | h1
  · apply hy
    rw [show y = z by linear_combination -h1]
    exact ratFuncHom_mem_adjoin hx r
  · apply hy
    rw [show y = -z - aeval x h by linear_combination h1]
    refine sub_mem (neg_mem (ratFuncHom_mem_adjoin hx r)) ?_
    rw [← ratFuncHom_algebraMap hx]
    exact ratFuncHom_mem_adjoin hx _

/-- **The model isomorphism.** If `x` is transcendental, `[F : K(x)] ≤ 2`, `y ∉ K(x)` and
`y² + h(x) y = f(x)`, then `F ≅ K(x)[T]/(T² + h T − f)` as `K`-algebras. -/
theorem nonempty_algEquiv_adjoinRoot {x y : F} (hx : Transcendental K x)
    (hy : y ∉ IntermediateField.adjoin K {x}) (h f : K[X])
    (hyeq : y ^ 2 + aeval x h * y = aeval x f)
    [FiniteDimensional (IntermediateField.adjoin K {x}) F]
    (hdeg : Module.finrank (IntermediateField.adjoin K {x}) F ≤ 2) :
    Nonempty (F ≃ₐ[K] AdjoinRoot (quadEqn h f)) := by
  have : Fact (Irreducible (quadEqn h f)) := ⟨irreducible_quadEqn hx hy h f hyeq⟩
  have hroot : (quadEqn h f).eval₂ (ratFuncHom hx).toRingHom y = 0 := by
    rw [eval₂_quadEqn]; linear_combination hyeq
  let ψ0 : AdjoinRoot (quadEqn h f) →+* F := AdjoinRoot.lift (ratFuncHom hx).toRingHom y hroot
  let ψ : AdjoinRoot (quadEqn h f) →ₐ[K] F :=
    { ψ0 with
      commutes' := fun c => by
        rw [AdjoinRoot.algebraMap_eq', RingHom.comp_apply]
        change AdjoinRoot.lift (ratFuncHom hx).toRingHom y hroot
          (AdjoinRoot.of _ (algebraMap K (RatFunc K) c)) = _
        rw [AdjoinRoot.lift_of]
        exact (ratFuncHom hx).commutes c }
  have hinj : Function.Injective ψ := ψ0.injective
  set E := IntermediateField.adjoin K {x}
  have hli : LinearIndependent E ![(1 : F), y] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have ht : t = 0 := by
      by_contra ht
      apply hy
      have ht' : (t : F) ≠ 0 := by exact_mod_cast ht
      have : y = -(s : F) / t := by
        rw [eq_div_iff ht']
        rw [Algebra.smul_def, Algebra.smul_def, mul_one] at hst
        change (s : F) + (t : F) * y = 0 at hst
        linear_combination hst
      rw [this]
      exact div_mem (neg_mem s.2) t.2
    subst ht
    rw [zero_smul, add_zero, smul_eq_zero] at hst
    exact ⟨hst.resolve_right one_ne_zero, rfl⟩
  have hcard : Fintype.card (Fin 2) = Module.finrank E F := by
    have := hli.fintype_card_le_finrank
    simp only [Fintype.card_fin] at this ⊢
    omega
  have hspan := hli.span_eq_top_of_card_eq_finrank hcard
  have hsurj : Function.Surjective ψ := by
    intro z
    have hz : z ∈ Submodule.span E (Set.range ![(1 : F), y]) := by rw [hspan]; trivial
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun E).1 hz
    rw [Fin.sum_univ_two] at hc
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Algebra.smul_def, mul_one] at hc
    obtain ⟨r0, hr0⟩ := exists_ratFuncHom_eq hx (c 0).2
    obtain ⟨r1, hr1⟩ := exists_ratFuncHom_eq hx (c 1).2
    refine ⟨AdjoinRoot.of _ r0 + AdjoinRoot.of _ r1 * AdjoinRoot.root _, ?_⟩
    change AdjoinRoot.lift (ratFuncHom hx).toRingHom y hroot
      (AdjoinRoot.of _ r0 + AdjoinRoot.of _ r1 * AdjoinRoot.root _) = z
    rw [map_add, map_mul, AdjoinRoot.lift_of, AdjoinRoot.lift_of, AdjoinRoot.lift_root, ← hc]
    change ratFuncHom hx r0 + ratFuncHom hx r1 * y = (c 0 : F) + (c 1 : F) * y
    rw [hr0, hr1]
  exact ⟨(AlgEquiv.ofBijective ψ ⟨hinj, hsurj⟩).symm⟩

/-! ### The pole condition from integrality (finiteness of the canonical map) -/

/-- `p(t⁻¹) t^N = (reflect N p)(t)` for `t ≠ 0`. -/
theorem aeval_inv_mul_pow {t : F} (ht : t ≠ 0) (N : ℕ) (p : K[X]) (hp : p.natDegree ≤ N) :
    aeval t⁻¹ p * t ^ N = aeval t (reflect N p) := by
  let : Invertible t := invertibleOfNonzero ht
  have := eval₂_reflect_mul_pow (algebraMap K F) t N (reflect N p)
    (natDegree_reflect_le.trans (max_le le_rfl hp))
  rw [reflect_reflect, invOf_eq_inv] at this
  exact this

theorem transcendental_inv {x : F} (hx : Transcendental K x) : Transcendental K x⁻¹ := by
  have hx0 : x ≠ 0 := fun h => hx (h ▸ isAlgebraic_zero)
  rw [transcendental_iff]
  intro q hq
  have h := aeval_inv_mul_pow (K := K) hx0 q.natDegree q le_rfl
  rw [hq, zero_mul] at h
  have := (transcendental_iff.1 hx) _ h.symm
  rwa [reflect_eq_zero_iff] at this

/-- **Integral elements of `K(x)` over `K[x]` are polynomials in `x`.** -/
theorem exists_aeval_eq_of_isIntegralElem {x : F} (hx : Transcendental K x) {z : F}
    (hz : z ∈ IntermediateField.adjoin K {x})
    (hi : (aeval x : K[X] →ₐ[K] F).toRingHom.IsIntegralElem z) : ∃ p : K[X], aeval x p = z := by
  obtain ⟨r, rfl⟩ := exists_ratFuncHom_eq hx hz
  obtain ⟨P, hPm, hP⟩ := hi
  have hcomp : (ratFuncHom hx).toRingHom.comp (algebraMap K[X] (RatFunc K)) =
      (aeval x : K[X] →ₐ[K] F).toRingHom :=
    RingHom.ext fun p => ratFuncHom_algebraMap hx p
  have hr : IsIntegral K[X] r := by
    refine ⟨P, hPm, (ratFuncHom hx).toRingHom.injective ?_⟩
    rw [hom_eval₂, hcomp, map_zero]
    exact hP
  obtain ⟨p, hp⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hr
  exact ⟨p, by rw [← hp, ratFuncHom_algebraMap]⟩

theorem mem_cubicSpan_of_natDegree_le {x : F} (p : K[X]) (hp : p.natDegree ≤ 3) :
    aeval x p ∈ cubicSpan K x := by
  rw [aeval_eq_sum_range' (n := 4) (by omega)]
  refine Submodule.sum_mem _ fun i hi => Submodule.smul_mem _ _ ?_
  exact Submodule.subset_span ⟨⟨i, Finset.mem_range.1 hi⟩, rfl⟩

/-- **The pole condition from integrality.** If `f ∈ K(x)` is integral over `K[x]` (regular
over `x ≠ ∞`) and `f/x³` is integral over `K[x⁻¹]` (pole of order `≤ 3` over `x = ∞`), then
`f ∈ ⟨1, x, x², x³⟩`. -/
theorem mem_cubicSpan_of_isIntegralElem {x : F} (hx : Transcendental K x) {f : F}
    (hf : f ∈ IntermediateField.adjoin K {x})
    (h0 : (aeval x : K[X] →ₐ[K] F).toRingHom.IsIntegralElem f)
    (h1 : (aeval x⁻¹ : K[X] →ₐ[K] F).toRingHom.IsIntegralElem (f * x⁻¹ ^ 3)) :
    f ∈ cubicSpan K x := by
  have hx0 : x ≠ 0 := fun h => hx (h ▸ isAlgebraic_zero)
  obtain ⟨p, rfl⟩ := exists_aeval_eq_of_isIntegralElem hx hf h0
  refine mem_cubicSpan_of_natDegree_le p ?_
  by_contra hd
  push Not at hd
  have hxi : x ∈ IntermediateField.adjoin K {x⁻¹} := by
    simpa using inv_mem (IntermediateField.mem_adjoin_simple_self K x⁻¹)
  have hadj : aeval x p * x⁻¹ ^ 3 ∈ IntermediateField.adjoin K {x⁻¹} :=
    mul_mem (by
      rw [show x = algebraMap (IntermediateField.adjoin K {x⁻¹}) F ⟨x, hxi⟩ from rfl,
        aeval_algebraMap_apply]
      exact SetLike.coe_mem _) (pow_mem
      (IntermediateField.mem_adjoin_simple_self K x⁻¹) 3)
  obtain ⟨q, hq⟩ := exists_aeval_eq_of_isIntegralElem (transcendental_inv hx) hadj h1
  set d := p.natDegree
  -- `reflect d p = q X^{d-3}`
  have hrel : aeval x⁻¹ (reflect d p) = aeval x⁻¹ (q * X ^ (d - 3)) := by
    rw [← aeval_inv_mul_pow (inv_ne_zero hx0) d p le_rfl, inv_inv, map_mul, map_pow, aeval_X, hq]
    rw [show d = 3 + (d - 3) by omega, pow_add]
    simp only [show 3 + (d - 3) - 3 = d - 3 by omega]
    field_simp
  have hpoly := (transcendental_iff.1 (transcendental_inv hx)) _
    (by rw [map_sub]; exact sub_eq_zero.2 hrel)
  rw [sub_eq_zero] at hpoly
  have hc := congrArg (fun r : K[X] => r.coeff 0) hpoly
  simp only [coeff_reflect, revAt_zero, coeff_mul_X_pow'] at hc
  split_ifs at hc with hle
  · omega
  have hp0 : p ≠ 0 := by rintro rfl; simp [d] at hd
  exact leadingCoeff_ne_zero.2 hp0 hc

/-! ### The packaged statement -/

/-- **Function-field data of a genus-2 curve** (`docs/ARITH_DEURING_G7_GENUS2.md` §2). For a
genus-2 curve with canonical sheaf `ω`, a basis `ω₀, ω₁` of `H⁰(ω)`, `x = ω₁/ω₀` and
`V n = {s/ω₀ⁿ : s ∈ H⁰(ω^{⊗n})}`:
* `x` is transcendental and `[F : K(x)] ≤ 2` (the canonical pencil has degree `deg ω = 2`);
* `1 ∈ V 0`, `1, x ∈ V 1`, `V a · V b ⊆ V (a + b)`;
* `dim V 3 ≥ 5` and `dim V 6 ≤ 11` (Riemann–Roch, `h⁰(ω^{⊗n}) = 2n − 1` for `n ≥ 2`);
* the pole condition `V 3 ∩ K(x) ⊆ ⟨1, x, x², x³⟩` (a rational function of `x` with poles only
  over `x = ∞`, of order `≤ 3`, is a cubic polynomial in `x`). -/
structure PencilData (K F : Type*) [Field K] [Field F] [Algebra K F] where
  /-- `x = ω₁/ω₀`. -/
  x : F
  /-- `V n = H⁰(ω^{⊗n})/ω₀ⁿ`. -/
  V : ℕ → Submodule K F
  transcendental : Transcendental K x
  finiteDimensional_adjoin : FiniteDimensional (IntermediateField.adjoin K {x}) F
  finrank_adjoin_le : Module.finrank (IntermediateField.adjoin K {x}) F ≤ 2
  one_mem_zero : (1 : F) ∈ V 0
  one_mem_one : (1 : F) ∈ V 1
  x_mem : x ∈ V 1
  mul_le : ∀ a b, V a * V b ≤ V (a + b)
  finiteDimensional_three : FiniteDimensional K (V 3)
  finiteDimensional_six : FiniteDimensional K (V 6)
  five_le_finrank_three : 5 ≤ Module.finrank K (V 3)
  finrank_six_le : Module.finrank K (V 6) ≤ 11
  pole : ∀ f ∈ V 3, f ∈ IntermediateField.adjoin K {x} → f ∈ cubicSpan K x

namespace PencilData

variable (D : PencilData K F)

theorem mul_mem {a b : ℕ} {u v : F} (hu : u ∈ D.V a) (hv : v ∈ D.V b) : u * v ∈ D.V (a + b) :=
  D.mul_le a b (Submodule.mul_mem_mul hu hv)

theorem mono {n : ℕ} {u : F} (hu : u ∈ D.V n) : u ∈ D.V (n + 1) := by
  simpa using D.mul_mem hu D.one_mem_one

theorem mono_le {m n : ℕ} (hmn : m ≤ n) {u : F} (hu : u ∈ D.V m) : u ∈ D.V n := by
  induction hmn with
  | refl => exact hu
  | step _ ih => exact D.mono ih

theorem pow_mem (i : ℕ) : D.x ^ i ∈ D.V i := by
  induction i with
  | zero => simpa using D.one_mem_zero
  | succ i ih => rw [pow_succ]; exact D.mul_mem ih D.x_mem

/-- **The model of a pencil datum.** -/
theorem exists_model (D : PencilData K F) :
    ∃ h f : K[X], h.natDegree ≤ 3 ∧ f.natDegree ≤ 6 ∧
      Nonempty (F ≃ₐ[K] AdjoinRoot (quadEqn h f)) := by
  have := D.finiteDimensional_three
  have := D.finiteDimensional_six
  have := D.finiteDimensional_adjoin
  obtain ⟨y, hyV, hy⟩ := exists_not_mem_adjoin D.x (D.V 3) D.five_le_finrank_three D.pole
  obtain ⟨h, f, hh, hf, hyeq⟩ := exists_relation D.transcendental hy (D.V 6) D.finrank_six_le
    (fun i hi => D.mono_le hi (D.pow_mem i))
    (fun j hj => by
      have := D.mul_mem (D.pow_mem j) hyV
      exact D.mono_le (by omega) this)
    (by rw [pow_two]; exact D.mul_mem hyV hyV)
  exact ⟨h, f, hh, hf, nonempty_algEquiv_adjoinRoot D.transcendental hy h f hyeq
    D.finrank_adjoin_le⟩

end PencilData

/-- **`PencilData` with the pole condition in its geometric form**: finiteness of the canonical
map `Y → ℙ¹` over both charts. Every `f ∈ V 3` is integral over `K[x]` (it is regular on
`Y_{s₀} = φ⁻¹(𝔸¹)`, which is finite over `𝔸¹ = Spec K[x]`), and `f/x³ = t/s₁³` is integral over
`K[x⁻¹]` (it is regular on `Y_{s₁}`, finite over `Spec K[x⁻¹]`). -/
structure IntegralPencilData (K F : Type*) [Field K] [Field F] [Algebra K F] where
  /-- `x = ω₁/ω₀`. -/
  x : F
  /-- `V n = H⁰(ω^{⊗n})/ω₀ⁿ`. -/
  V : ℕ → Submodule K F
  transcendental : Transcendental K x
  finiteDimensional_adjoin : FiniteDimensional (IntermediateField.adjoin K {x}) F
  finrank_adjoin_le : Module.finrank (IntermediateField.adjoin K {x}) F ≤ 2
  one_mem_zero : (1 : F) ∈ V 0
  one_mem_one : (1 : F) ∈ V 1
  x_mem : x ∈ V 1
  mul_le : ∀ a b, V a * V b ≤ V (a + b)
  finiteDimensional_three : FiniteDimensional K (V 3)
  finiteDimensional_six : FiniteDimensional K (V 6)
  five_le_finrank_three : 5 ≤ Module.finrank K (V 3)
  finrank_six_le : Module.finrank K (V 6) ≤ 11
  integral_affine : ∀ f ∈ V 3, (aeval x : K[X] →ₐ[K] F).toRingHom.IsIntegralElem f
  integral_infinity : ∀ f ∈ V 3,
    (aeval x⁻¹ : K[X] →ₐ[K] F).toRingHom.IsIntegralElem (f * x⁻¹ ^ 3)

/-- The integrality conditions give the pole condition. -/
def IntegralPencilData.toPencilData (D : IntegralPencilData K F) : PencilData K F where
  x := D.x
  V := D.V
  transcendental := D.transcendental
  finiteDimensional_adjoin := D.finiteDimensional_adjoin
  finrank_adjoin_le := D.finrank_adjoin_le
  one_mem_zero := D.one_mem_zero
  one_mem_one := D.one_mem_one
  x_mem := D.x_mem
  mul_le := D.mul_le
  finiteDimensional_three := D.finiteDimensional_three
  finiteDimensional_six := D.finiteDimensional_six
  five_le_finrank_three := D.five_le_finrank_three
  finrank_six_le := D.finrank_six_le
  pole f hf hfx := mem_cubicSpan_of_isIntegralElem D.transcendental hfx (D.integral_affine f hf)
    (D.integral_infinity f hf)

end RamanujanWeil.Arith.Deuring.Geom.G7.Genus2.Exist
