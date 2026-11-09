import Mathlib

/-!
# A3-ord, G8 (algebra): rank-two lattices with a quadratic endomorphism

Pure algebra used by `DeuringG8Lattice` (G8(i)). No geometry.

* `trace_det_of_sq_eq`: a `2 × 2` integer matrix `M` with `M² = tM − q` that is not a scalar
  matrix has trace `t` and determinant `q`.
* `linearMap_trace_det_of_sq_eq`: the same for an endomorphism of a free `ℤ`-module of rank two,
  read on any basis.
* `finrank_eq_two_of_torsion_quotient`: a finitely generated free `ℤ`-module containing two
  linearly independent elements `a, b` such that every element has a nonzero multiple in
  `ℤa + ℤb` has rank two.
* `exists_mul_eq_of_sq` (the "commutant" step of G8): in a commutative ring without additive
  torsion, if `x² = D < 0`, `y² = D' ≤ 0`, and `z = xy` satisfies `z² − τz + δ = 0` with
  `δ ≥ 0` and `δ = 0 ⇒ z = 0`, then `N·y = c·x` for some integers `N ≠ 0`, `c`.
-/

namespace RamanujanWeil.Arith.Deuring.G8

open Matrix

/-- **A non-scalar `2 × 2` root of `X² − tX + q` has trace `t` and determinant `q`.** -/
theorem trace_det_of_sq_eq (M : Matrix (Fin 2) (Fin 2) ℤ) (t q : ℤ)
    (hM : M * M = t • M - q • (1 : Matrix (Fin 2) (Fin 2) ℤ))
    (hns : ∀ c : ℤ, M ≠ c • (1 : Matrix (Fin 2) (Fin 2) ℤ)) :
    M.trace = t ∧ M.det = q := by
  have entry : ∀ i j : Fin 2, (M * M) i j = t * M i j - q * (1 : Matrix (Fin 2) (Fin 2) ℤ) i j :=
    fun i j => by rw [hM]; simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  have e00 := entry 0 0
  have e01 := entry 0 1
  have e10 := entry 1 0
  have e11 := entry 1 1
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply_eq,
    Matrix.one_apply_ne (show (0 : Fin 2) ≠ 1 by decide),
    Matrix.one_apply_ne (show (1 : Fin 2) ≠ 0 by decide), mul_one, mul_zero, sub_zero] at e00 e01 e10 e11
  rw [Matrix.trace_fin_two, Matrix.det_fin_two]
  -- `a + d = t`
  have hsum : M 0 0 + M 1 1 = t := by
    by_cases hb : M 0 1 = 0
    · by_cases hc : M 1 0 = 0
      · -- diagonal: `a ≠ d`
        have had : M 0 0 ≠ M 1 1 := by
          intro had
          apply hns (M 0 0)
          ext i j
          fin_cases i <;> fin_cases j <;>
            simp [Matrix.smul_apply, hb, hc, had]
        rw [hb, zero_mul, add_zero] at e00
        rw [hc, zero_mul, zero_add] at e11
        have h1 : (M 0 0 - M 1 1) * (M 0 0 + M 1 1 - t) = 0 := by linear_combination e00 - e11
        rcases mul_eq_zero.mp h1 with h | h
        · exact absurd (sub_eq_zero.mp h) had
        · linarith
      · have h1 : M 1 0 * (M 0 0 + M 1 1 - t) = 0 := by linear_combination e10
        rcases mul_eq_zero.mp h1 with h | h
        · exact absurd h hc
        · linarith
    · have h1 : M 0 1 * (M 0 0 + M 1 1 - t) = 0 := by linear_combination e01
      rcases mul_eq_zero.mp h1 with h | h
      · exact absurd h hb
      · linarith
  refine ⟨hsum, ?_⟩
  have hd : M 1 1 = t - M 0 0 := by linarith
  rw [hd]
  linear_combination -e00

/-- **The same for an endomorphism of a free `ℤ`-module of rank two**, read on a basis. -/
theorem linearMap_trace_det_of_sq_eq {L : Type*} [AddCommGroup L] (b : Module.Basis (Fin 2) ℤ L)
    (f : L →ₗ[ℤ] L) (t q : ℤ) (hf : f ∘ₗ f = t • f - q • LinearMap.id)
    (hns : ∀ c : ℤ, f ≠ c • LinearMap.id) :
    (LinearMap.toMatrix b b f).trace = t ∧ (LinearMap.toMatrix b b f).det = q := by
  apply trace_det_of_sq_eq _ t q
  · rw [← LinearMap.toMatrix_comp, hf, map_sub, map_smul, map_smul, LinearMap.toMatrix_id]
  · intro c hc
    apply hns c
    apply (LinearMap.toMatrix b b).injective
    rw [hc, map_smul, LinearMap.toMatrix_id]

/-- **Rank of a torsion extension.** If every element of `L` has a nonzero multiple in the
submodule `N`, then `L` and `N` have the same rank. -/
theorem finrank_eq_of_torsion {L : Type*} [AddCommGroup L] (N : Submodule ℤ L)
    (htor : ∀ x : L, ∃ n : ℤ, n ≠ 0 ∧ n • x ∈ N) :
    Module.finrank ℤ L = Module.finrank ℤ N := by
  have hq : Module.rank ℤ (L ⧸ N) = 0 := by
    rw [rank_eq_zero_iff]
    intro x
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective N x
    obtain ⟨n, hn, hy⟩ := htor y
    refine ⟨n, hn, ?_⟩
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
    exact hy
  have hrank := rank_quotient_add_rank_of_isDomain N
  rw [hq, zero_add] at hrank
  rw [Module.finrank, ← hrank, ← Module.finrank]

theorem mem_span_pair_of_eq {L : Type*} [AddCommGroup L] (a b x : L) (u v : ℤ)
    (h : x = u • a + v • b) : x ∈ Submodule.span ℤ (Set.range ![a, b]) := by
  rw [h]
  exact Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩))
    (Submodule.smul_mem _ _ (Submodule.subset_span ⟨1, rfl⟩))

/-- **Rank at most two from a torsion quotient.** -/
theorem finrank_le_two_of_torsion_quotient {L : Type*} [AddCommGroup L] (a b : L)
    (htor : ∀ x : L, ∃ n : ℤ, n ≠ 0 ∧ ∃ u v : ℤ, n • x = u • a + v • b) :
    Module.finrank ℤ L ≤ 2 := by
  rw [finrank_eq_of_torsion (Submodule.span ℤ (Set.range ![a, b])) (fun x => by
    obtain ⟨n, hn, u, v, h⟩ := htor x
    exact ⟨n, hn, mem_span_pair_of_eq a b _ u v h⟩)]
  exact (finrank_range_le_card (R := ℤ) (b := ![a, b])).trans (le_of_eq (Fintype.card_fin 2))

/-- **Rank two from a torsion quotient.** -/
theorem finrank_eq_two_of_torsion_quotient {L : Type*} [AddCommGroup L] (a b : L)
    (hab : LinearIndependent ℤ ![a, b])
    (htor : ∀ x : L, ∃ n : ℤ, n ≠ 0 ∧ ∃ u v : ℤ, n • x = u • a + v • b) :
    Module.finrank ℤ L = 2 := by
  rw [finrank_eq_of_torsion (Submodule.span ℤ (Set.range ![a, b])) (fun x => by
    obtain ⟨n, hn, u, v, h⟩ := htor x
    exact ⟨n, hn, mem_span_pair_of_eq a b _ u v h⟩), finrank_span_eq_card hab]
  simp

/-- **The commutant step.** In a commutative ring without additive torsion, with `x² = D < 0`,
`y² = D' ≤ 0` and `z = xy` a root of `X² − τX + δ` (`δ ≥ 0`, `δ = 0 ⇒ z = 0`), some nonzero
multiple of `y` is a multiple of `x`. -/
theorem exists_mul_eq_of_sq {R : Type*} [CommRing R]
    (htf : ∀ (n : ℤ) (w : R), n ≠ 0 → (n : R) * w = 0 → w = 0)
    (x y : R) (D D' τ δ : ℤ) (hD : D < 0) (hD' : D' ≤ 0) (hx : x * x = D) (hy : y * y = D')
    (hz : (x * y) * (x * y) - τ * (x * y) + δ = 0) (hδ : 0 ≤ δ)
    (hδ0 : δ = 0 → x * y = 0) :
    ∃ N c : ℤ, N ≠ 0 ∧ (N : R) * y = c * x := by
  have hzz : (x * y) * (x * y) = ((D * D' : ℤ) : R) := by
    push_cast
    calc (x * y) * (x * y) = (x * x) * (y * y) := by ring
      _ = _ := by rw [hx, hy]
  by_cases hτ : τ = 0
  · -- then `D D' + δ = 0`, so `δ = 0` and `z = 0`
    have h1 : ((D * D' + δ : ℤ) : R) = 0 := by
      rw [hτ] at hz
      push_cast at hz ⊢
      rw [← hz]
      push_cast at hzz
      rw [hzz]
      ring
    have hDD : 0 ≤ D * D' := by nlinarith
    have hz0 : x * y = 0 := by
      by_cases hδz : δ = 0
      · exact hδ0 hδz
      have hpos : 0 < D * D' + δ := by omega
      have h10 := htf (D * D' + δ) 1 hpos.ne' (by rw [mul_one]; exact h1)
      rw [← mul_one (x * y), h10, mul_zero]
    -- `D y = x (x y) = 0`
    have hDy : (D : R) * y = 0 := by
      rw [← hx]
      calc x * x * y = x * (x * y) := by ring
        _ = 0 := by rw [hz0, mul_zero]
    have hy0 := htf D y hD.ne hDy
    exact ⟨1, 0, one_ne_zero, by rw [hy0]; simp⟩
  · -- `τ z = z² + δ`, multiply by `x`
    refine ⟨τ * D, D * D' + δ, mul_ne_zero hτ hD.ne, ?_⟩
    have hτz : (τ : R) * (x * y) = ((D * D' + δ : ℤ) : R) := by
      push_cast at hzz ⊢
      rw [← hzz]
      linear_combination -hz
    calc ((τ * D : ℤ) : R) * y = x * ((τ : R) * (x * y)) := by
          push_cast; rw [← hx]; ring
      _ = _ := by rw [hτz]; ring

end RamanujanWeil.Arith.Deuring.G8
