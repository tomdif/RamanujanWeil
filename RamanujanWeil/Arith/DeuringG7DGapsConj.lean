import RamanujanWeil.Arith.DeuringG7DGapsVal

/-!
# A3-ord, G7-D-gaps (conjugation): `σ = [−1]^*` on `F[E]`, and the degree of `m_Q^N`

`docs/ARITH_DEURING_G7DGAPS.md` §1.

* **`conj`** `σ : F[E] → F[E]`, `Y ↦ −Y − a₁X − a₃` (an `F[X]`-algebra map), with
  `N(σ r) = N(r)` (`norm_conj`), hence `vR (σ r) = vR r`.
* **`map_conj_XYIdeal`**: `σ(m_Q) = m_{−Q}`, so `m_Q · σ(m_Q) = (X − x_Q)` (Mathlib's
  `XYIdeal_neg_mul`).
* **`vR_of_pow_eq_span`**: `m_Q^N = (r)` implies `vR r = e^N` (pole order `N` at `O`).
* **`pow_eq_span_of_le`**: `m_Q^N ≤ (r)` and `vR r ≥ e^N` imply `m_Q^N = (r)`.

Both follow by applying `σ` and multiplying: `(r)·σ(r) = (r σ(r))`, and
`m_Q^N σ(m_Q)^N = ((X − x_Q)^N)`, where `vR (X − x_Q)^N = e^{2N}`.
-/

noncomputable section

namespace RamanujanWeil.Arith.Deuring.Geom.G7.DGeom

open WeierstrassCurve WeierstrassCurve.Affine Polynomial
open scoped nonZeroDivisors Polynomial.Bivariate

universe u

set_option linter.unusedSectionVars false

variable {F : Type u} [Field F] (W : Affine F) [W.IsElliptic] [DecidableEq F]

/-! ### The conjugation -/

/-- `σ(Y) = −Y − a₁X − a₃`. -/
def conjY : Rg W := -(yR W) - AdjoinRoot.of _ (C (W⁄F).a₁ * X + C (W⁄F).a₃)

theorem eval₂_polynomial {S : Type*} [CommRing S] (f : F[X] →+* S) (z : S) :
    (W⁄F).polynomial.eval₂ f z = z ^ 2 + f (C (W⁄F).a₁ * X + C (W⁄F).a₃) * z -
      f (X ^ 3 + C (W⁄F).a₂ * X ^ 2 + C (W⁄F).a₄ * X + C (W⁄F).a₆) := by
  rw [Affine.polynomial]
  simp only [eval₂_add, eval₂_sub, eval₂_mul, eval₂_pow, eval₂_X, eval₂_C]

theorem conjY_root :
    (W⁄F).polynomial.eval₂ (Algebra.ofId F[X] (Rg W) : F[X] →+* Rg W) (conjY W) = 0 := by
  have h := AdjoinRoot.eval₂_root (W⁄F).polynomial
  rw [eval₂_polynomial] at h ⊢
  have : (Algebra.ofId F[X] (Rg W) : F[X] →+* Rg W) = AdjoinRoot.of _ := rfl
  rw [this]
  unfold conjY
  linear_combination h

/-- **The conjugation `σ = [−1]^*`** of `F[E]` over `F[X]`. -/
def conj : Rg W →ₐ[F[X]] Rg W :=
  AdjoinRoot.liftAlgHom _ (Algebra.ofId F[X] (Rg W)) (conjY W) (conjY_root W)

theorem conj_yR : conj W (yR W) = conjY W :=
  AdjoinRoot.liftAlgHom_root _ _ _ _

theorem conj_of (p : F[X]) : conj W (AdjoinRoot.of _ p) = AdjoinRoot.of _ p :=
  AdjoinRoot.liftAlgHom_of _ _ _ _ p

theorem conj_smul_basis (p q : F[X]) :
    conj W (p • (1 : Rg W) + q • CoordinateRing.mk (W⁄F) Y) =
      (p - q * (C (W⁄F).a₁ * X + C (W⁄F).a₃)) • (1 : Rg W) +
        (-q) • CoordinateRing.mk (W⁄F) Y := by
  have hY : CoordinateRing.mk (W⁄F) Y = yR W := AdjoinRoot.mk_X
  rw [map_add, map_smul, map_smul, map_one, hY, conj_yR, conjY]
  simp only [Algebra.smul_def, AdjoinRoot.algebraMap_eq, map_sub, map_mul, map_neg, mul_one]
  ring

/-- `N(σ r) = N(r)`. -/
theorem norm_conj (r : Rg W) : Algebra.norm F[X] (conj W r) = Algebra.norm F[X] r := by
  obtain ⟨p, q, rfl⟩ := CoordinateRing.exists_smul_basis_eq r
  rw [conj_smul_basis, CoordinateRing.norm_smul_basis, CoordinateRing.norm_smul_basis]
  ring

theorem conj_ne_zero {r : Rg W} (hr : r ≠ 0) : conj W r ≠ 0 := by
  intro h
  apply norm_ne_zero W hr
  rw [← norm_conj, h, Algebra.norm_eq_zero_iff]

theorem vR_conj (r : Rg W) : vR W (conj W r) = vR W r := by
  by_cases hr : r = 0
  · rw [hr, map_zero]
  rw [vR_of_ne W hr, vR_of_ne W (conj_ne_zero W hr), normDeg, normDeg, norm_conj]

theorem vR_mul_conj (r : Rg W) : vR W (r * conj W r) = vR W r ^ 2 := by
  rw [map_mul, vR_conj, sq]

/-! ### `σ(m_Q) = m_{−Q}` -/

theorem conj_XClass (x : F) : conj W (CoordinateRing.XClass (W⁄F) x) = CoordinateRing.XClass _ x := by
  rw [CoordinateRing.XClass, CoordinateRing.mk, AdjoinRoot.mk_C, conj_of]

theorem vR_XClass (x : F) : vR W (CoordinateRing.XClass (W⁄F) x) = WithZero.exp 2 := by
  have : CoordinateRing.XClass (W⁄F) x = (X - C x : F[X]) • (1 : Rg W) := by
    rw [CoordinateRing.smul, mul_one]; rfl
  rw [this, vR_smul_one W (X_sub_C_ne_zero x), natDegree_X_sub_C]; rfl

theorem map_conj_XYIdeal {x y : F} :
    Ideal.map (conj W) (CoordinateRing.XYIdeal (W⁄F) x (C y)) =
      CoordinateRing.XYIdeal (W⁄F) x (C ((W⁄F).negY x y)) := by
  have hX := conj_XClass W x
  have hYc : conj W (CoordinateRing.YClass (W⁄F) (C y)) =
      -CoordinateRing.YClass (W⁄F) (C ((W⁄F).negY x y)) -
        AdjoinRoot.of _ (C (W⁄F).a₁) * CoordinateRing.XClass (W⁄F) x := by
    simp only [CoordinateRing.YClass, CoordinateRing.XClass, CoordinateRing.mk, map_sub,
      AdjoinRoot.mk_X, AdjoinRoot.mk_C]
    rw [conj_yR, conj_of, conjY, Affine.negY]
    simp only [map_add, map_sub, map_mul, map_neg]
    ring
  simp only [CoordinateRing.XYIdeal]
  rw [Ideal.map_span, Set.image_pair, hX, hYc]
  apply le_antisymm
  · rw [Ideal.span_le]
    rintro z (rfl | rfl)
    · exact Ideal.subset_span (Set.mem_insert _ _)
    · rw [SetLike.mem_coe, Ideal.mem_span_pair]
      exact ⟨-AdjoinRoot.of _ (C (W⁄F).a₁), -1, by ring⟩
  · rw [Ideal.span_le]
    rintro z (rfl | rfl)
    · exact Ideal.subset_span (Set.mem_insert _ _)
    · rw [SetLike.mem_coe, Ideal.mem_span_pair]
      exact ⟨-AdjoinRoot.of _ (C (W⁄F).a₁), -1, by ring⟩

theorem XYIdeal_mul_map_conj {x y : F} (h : (W⁄F).Nonsingular x y) :
    CoordinateRing.XYIdeal (W⁄F) x (C y) *
        Ideal.map (conj W) (CoordinateRing.XYIdeal (W⁄F) x (C y)) =
      CoordinateRing.XIdeal (W⁄F) x := by
  rw [map_conj_XYIdeal, mul_comm, CoordinateRing.XYIdeal_neg_mul h]

theorem span_mul_map_conj (r : Rg W) :
    Ideal.span {r} * Ideal.map (conj W) (Ideal.span {r}) = Ideal.span {r * conj W r} := by
  rw [Ideal.map_span, Set.image_singleton, Ideal.span_singleton_mul_span_singleton]

theorem pow_mul_map_conj {x y : F} (h : (W⁄F).Nonsingular x y) (N : ℕ) :
    CoordinateRing.XYIdeal (W⁄F) x (C y) ^ N *
        Ideal.map (conj W) (CoordinateRing.XYIdeal (W⁄F) x (C y) ^ N) =
      Ideal.span {CoordinateRing.XClass (W⁄F) x ^ N} := by
  rw [Ideal.map_pow, ← mul_pow, XYIdeal_mul_map_conj W h, CoordinateRing.XIdeal,
    Ideal.span_singleton_pow]

/-! ### The degree of `m_Q^N` -/

theorem vR_eq_of_associated {a b : Rg W} (h : Associated a b) : vR W a = vR W b := by
  obtain ⟨u, rfl⟩ := h
  rw [map_mul, vR_eq_one_of_isUnit W u.isUnit, mul_one]

theorem vR_XClass_pow (x : F) (N : ℕ) :
    vR W (CoordinateRing.XClass (W⁄F) x ^ N) = WithZero.exp ((2 * N : ℕ) : ℤ) := by
  rw [map_pow, vR_XClass, ← WithZero.exp_nsmul, nsmul_eq_mul]
  push_cast; ring_nf

theorem XClass_pow_ne_zero (x : F) (N : ℕ) : CoordinateRing.XClass (W⁄F) x ^ N ≠ 0 :=
  pow_ne_zero _ (CoordinateRing.XClass_ne_zero x)

theorem normDeg_eq_of_vR_sq {r : Rg W} (hr : r ≠ 0) {n : ℕ}
    (h : vR W r ^ 2 = WithZero.exp ((2 * n : ℕ) : ℤ)) : normDeg W r = n := by
  rw [vR_of_ne W hr, ← WithZero.exp_nsmul, WithZero.exp_inj, nsmul_eq_mul] at h
  push_cast at h
  omega

/-- **`m_Q^N = (r)` ⟹ `vR r = e^N`**: a generator of `m_Q^N` has a pole of order exactly `N`
at `O` (the degree of a principal divisor is zero). -/
theorem vR_of_pow_eq_span {x y : F} (h : (W⁄F).Nonsingular x y) {N : ℕ} {r : Rg W}
    (hr : CoordinateRing.XYIdeal (W⁄F) x (C y) ^ N = Ideal.span {r}) :
    r ≠ 0 ∧ vR W r = WithZero.exp (N : ℤ) := by
  have key := pow_mul_map_conj W h N
  rw [hr, span_mul_map_conj, Ideal.span_singleton_eq_span_singleton] at key
  have hv := vR_eq_of_associated W key
  rw [vR_mul_conj, vR_XClass_pow] at hv
  have hr0 : r ≠ 0 := by
    rintro rfl
    rw [map_zero, sq, zero_mul] at hv
    exact WithZero.exp_ne_zero hv.symm
  refine ⟨hr0, ?_⟩
  rw [vR_of_ne W hr0, normDeg_eq_of_vR_sq W hr0 hv]

/-- **`m_Q^N ≤ (r)` and `vR r ≥ e^N` ⟹ `m_Q^N = (r)`**. Write `m_Q^N = (r)·I`; norms give
`((X − x)^N) = (r σ r)·I σ(I)` with `vR (r σ r) ≥ e^{2N} = vR (X − x)^N`, so `I σ(I) = (1)`. -/
theorem pow_eq_span_of_le {x y : F} (h : (W⁄F).Nonsingular x y) {N : ℕ} {r : Rg W} (hr : r ≠ 0)
    (hle : CoordinateRing.XYIdeal (W⁄F) x (C y) ^ N ≤ Ideal.span {r})
    (hv : WithZero.exp (N : ℤ) ≤ vR W r) :
    CoordinateRing.XYIdeal (W⁄F) x (C y) ^ N = Ideal.span {r} := by
  obtain ⟨I, hI⟩ : ∃ I : Ideal (Rg W),
      Ideal.span {r} * I = CoordinateRing.XYIdeal (W⁄F) x (C y) ^ N := by
    refine ⟨Submodule.comap (LinearMap.mulLeft (Rg W) r)
      (CoordinateRing.XYIdeal (W⁄F) x (C y) ^ N), le_antisymm ?_ ?_⟩
    · rw [Ideal.span_singleton_mul_le_iff]
      intro z hz
      exact hz
    · intro a ha
      obtain ⟨z, rfl⟩ := Ideal.mem_span_singleton'.1 (hle ha)
      rw [Ideal.mem_span_singleton_mul]
      refine ⟨z, ?_, mul_comm _ _⟩
      rw [Submodule.mem_comap, LinearMap.mulLeft_apply, mul_comm]
      exact ha
  have key : Ideal.span {r * conj W r} * (I * Ideal.map (conj W) I) =
      Ideal.span {CoordinateRing.XClass (W⁄F) x ^ N} := by
    rw [← pow_mul_map_conj W h N, ← hI, ← span_mul_map_conj, Ideal.map_mul, mul_mul_mul_comm]
  have hn0 : r * conj W r ≠ 0 := mul_ne_zero hr (conj_ne_zero W hr)
  have h1 : CoordinateRing.XClass (W⁄F) x ^ N ∈
      Ideal.span {r * conj W r} * (I * Ideal.map (conj W) I) := by
    rw [key]; exact Ideal.mem_span_singleton_self _
  obtain ⟨s, -, hs'⟩ := Ideal.mem_span_singleton_mul.1 h1
  have hs : s * (r * conj W r) = CoordinateRing.XClass (W⁄F) x ^ N := by rw [mul_comm]; exact hs'
  have hs0 : s ≠ 0 := by
    rintro rfl
    rw [zero_mul] at hs
    exact XClass_pow_ne_zero W x N hs.symm
  have hsv : vR W s ≤ 1 := by
    have e := congrArg (vR W) hs
    rw [map_mul, vR_mul_conj, vR_XClass_pow, vR_of_ne W hs0, vR_of_ne W hr] at e
    rw [vR_of_ne W hr, WithZero.exp_le_exp] at hv
    rw [← WithZero.exp_nsmul, ← WithZero.exp_add, WithZero.exp_inj, nsmul_eq_mul] at e
    rw [vR_of_ne W hs0, ← WithZero.exp_zero, WithZero.exp_le_exp]
    push_cast at e
    omega
  have hsu : IsUnit s := isUnit_of_vR_le_one W hs0 hsv
  have h2 : Ideal.span {r * conj W r} * (I * Ideal.map (conj W) I) =
      Ideal.span {r * conj W r} := by
    rw [key, ← hs, mul_comm, Ideal.span_singleton_mul_right_unit hsu]
  have h3 : r * conj W r ∈ Ideal.span {r * conj W r} * (I * Ideal.map (conj W) I) := by
    rw [h2]; exact Ideal.mem_span_singleton_self _
  obtain ⟨z, hz, hz'⟩ := Ideal.mem_span_singleton_mul.1 h3
  have hz1 : z = 1 := mul_left_cancel₀ hn0 (hz'.trans (mul_one _).symm)
  have hJ1 : I * Ideal.map (conj W) I = ⊤ := (Ideal.eq_top_iff_one _).2 (hz1 ▸ hz)
  have hI1 : I = ⊤ := top_unique (hJ1 ▸ Ideal.mul_le_inf.trans inf_le_left)
  rw [← hI, hI1, Ideal.mul_top]

end RamanujanWeil.Arith.Deuring.Geom.G7.DGeom
