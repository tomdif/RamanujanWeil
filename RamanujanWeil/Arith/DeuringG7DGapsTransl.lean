import RamanujanWeil.Arith.DeuringG7DGapsConj

/-!
# A3-ord, G7-D-gaps (translations): where `τ_{−Q} L(N·O)` has its poles

`docs/ARITH_DEURING_G7DGAPS.md` §2. Let `Q = (x₀, y₀) ≠ O`, `P = −Q = (x₀, y₁)`,
`τ = τ_P = t_P^*` and `ℓ = (y − y₁)/(x − x₀)`. Then (Mathlib's addition formula for `ξ + P`)

  `τ x = ℓ² + a₁ℓ − a₂ − x − x₀`,  `τ y = −(ℓ(τx − x) + y) − a₁ τx − a₃`.

* **Poles at affine points** (`trans_mem_Jpow`): with `J = m_Q⁻¹`, `ℓ ∈ J` because
  `(x − x₀) = m_P m_Q` (Mathlib's `XYIdeal_neg_mul`) and `y − y₁ ∈ m_P`; so `τ x ∈ J²`,
  `τ y ∈ J³`, and `τ L(N·O) ⊆ J^N = m_Q^{−N}`.
* **Regularity at `O`** (`vK_trans_le_one`): `τx = n/(x − x₀)²` where, modulo the curve equation,
  `n = x₀x² + Ax + B + Cy` has `vK n ≤ e⁴`; so `vK (τ x) ≤ 1`. Then `vK (τ y) ≤ 1` because `τ y`
  is integral over `F[τ x]` (the Weierstrass equation). So `vK (τ f) ≤ 1` on `L(N·O)`.
-/

noncomputable section

namespace RamanujanWeil.Arith.Deuring.Geom.G7.DGeom

open WeierstrassCurve WeierstrassCurve.Affine Polynomial
open scoped nonZeroDivisors Polynomial.Bivariate

universe u

set_option linter.unusedSectionVars false

open scoped Classical

variable {F : Type u} [Field F] (W : Affine F) [W.IsElliptic] [DecidableEq F]

local notation "Γ₀" => WithZero (Multiplicative ℤ)
local notation "FI" => FractionalIdeal (Rg W)⁰ (Kf W)

/-- `c ↦ c` in `F(E)`. -/
local notation "cK" => algebraMap F (Kf W)

variable {x₀ y₀ : F}

/-- `y₁ = y(−Q)`. -/
abbrev yN : F := (W⁄F).negY x₀ y₀

theorem nonsingular_neg' (h : (W⁄F).Nonsingular x₀ y₀) : (W⁄F).Nonsingular x₀ (yN W (x₀ := x₀) (y₀ := y₀)) :=
  (nonsingular_neg ..).2 h

/-- The slope `ℓ = (y − y₁)/(x − x₀)` of the line through `ξ` and `P = −Q`. -/
def lam : Kf W := (genY W - cK (yN W (x₀ := x₀) (y₀ := y₀))) / (genX W - cK x₀)

theorem genX_ne : genX W ≠ cK x₀ := fun e =>
  transcendental_genX W (e ▸ isAlgebraic_algebraMap x₀)

theorem genX_sub_ne_zero : genX W - cK x₀ ≠ 0 := sub_ne_zero.2 (genX_ne W)

theorem aK₁ : (W⁄(Kf W)).a₁ = cK W.a₁ := rfl
theorem aK₂ : (W⁄(Kf W)).a₂ = cK W.a₂ := rfl
theorem aK₃ : (W⁄(Kf W)).a₃ = cK W.a₃ := rfl
theorem aK₄ : (W⁄(Kf W)).a₄ = cK W.a₄ := rfl
theorem aK₆ : (W⁄(Kf W)).a₆ = cK W.a₆ := rfl

theorem genX_ne' : genX W ≠ (Algebra.ofId F (Kf W)) x₀ := genX_ne W

theorem ptX_add_of_X_ne {x₁ x₂ y₁ y₂ : Kf W} (h₁ : (W⁄(Kf W)).Nonsingular x₁ y₁)
    (h₂ : (W⁄(Kf W)).Nonsingular x₂ y₂) (hx : x₁ ≠ x₂) :
    ptX W (Point.some x₁ y₁ h₁ + Point.some x₂ y₂ h₂) =
      (W⁄(Kf W)).addX x₁ x₂ ((y₁ - y₂) / (x₁ - x₂)) := by
  rw [Point.add_of_X_ne hx]
  change (W⁄(Kf W)).addX x₁ x₂ ((W⁄(Kf W)).slope x₁ x₂ y₁ y₂) = _
  rw [Affine.slope_of_X_ne hx]

theorem ptY_add_of_X_ne {x₁ x₂ y₁ y₂ : Kf W} (h₁ : (W⁄(Kf W)).Nonsingular x₁ y₁)
    (h₂ : (W⁄(Kf W)).Nonsingular x₂ y₂) (hx : x₁ ≠ x₂) :
    ptY W (Point.some x₁ y₁ h₁ + Point.some x₂ y₂ h₂) =
      (W⁄(Kf W)).addY x₁ x₂ y₁ ((y₁ - y₂) / (x₁ - x₂)) := by
  rw [Point.add_of_X_ne hx]
  change (W⁄(Kf W)).addY x₁ x₂ y₁ ((W⁄(Kf W)).slope x₁ x₂ y₁ y₂) = _
  rw [Affine.slope_of_X_ne hx]

theorem transX_neg (h : (W⁄F).Nonsingular x₀ y₀) :
    transX W (-(Point.some x₀ y₀ h)) =
      lam W (x₀ := x₀) (y₀ := y₀) ^ 2 + cK W.a₁ * lam W (x₀ := x₀) (y₀ := y₀) - cK W.a₂ -
        genX W - cK x₀ := by
  rw [transX, transPt, bc, Point.neg_some, Point.baseChange, Point.map_some, genPt,
    ptX_add_of_X_ne W _ _ (genX_ne' W)]
  rfl

theorem transY_neg (h : (W⁄F).Nonsingular x₀ y₀) :
    transY W (-(Point.some x₀ y₀ h)) =
      -(lam W (x₀ := x₀) (y₀ := y₀) * (transX W (-(Point.some x₀ y₀ h)) - genX W) + genY W) -
        cK W.a₁ * transX W (-(Point.some x₀ y₀ h)) - cK W.a₃ := by
  rw [transX_neg]
  rw [transY, transPt, bc, Point.neg_some, Point.baseChange, Point.map_some, genPt,
    ptY_add_of_X_ne W _ _ (genX_ne' W)]
  rfl

/-! ### Poles at affine points: `τ_{−Q} L(N·O) ⊆ m_Q^{−N}` -/

/-- `m_Q` as a unit fractional ideal. -/
abbrev uQ (h : (W⁄F).Nonsingular x₀ y₀) : FIˣ := CoordinateRing.XYIdeal' h

/-- `J = m_Q⁻¹`. -/
abbrev Jinv (h : (W⁄F).Nonsingular x₀ y₀) : FI := ((uQ W h)⁻¹ : FIˣ)

theorem fi_add {I : FI} {a b : Kf W} (ha : a ∈ I) (hb : b ∈ I) : a + b ∈ I :=
  (I : Submodule (Rg W) (Kf W)).add_mem ha hb

theorem fi_sub {I : FI} {a b : Kf W} (ha : a ∈ I) (hb : b ∈ I) : a - b ∈ I :=
  (I : Submodule (Rg W) (Kf W)).sub_mem ha hb

theorem fi_neg {I : FI} {a : Kf W} (ha : a ∈ I) : -a ∈ I :=
  (I : Submodule (Rg W) (Kf W)).neg_mem ha

theorem fi_pow {I : FI} {a : Kf W} (ha : a ∈ I) (n : ℕ) : a ^ n ∈ I ^ n := by
  induction n with
  | zero =>
    rw [pow_zero, pow_zero]
    exact (FractionalIdeal.mem_one_iff _).2 ⟨1, map_one _⟩
  | succ n ih =>
    rw [pow_succ, pow_succ]
    exact FractionalIdeal.mul_mem_mul ih ha

theorem uQ_le_one (h : (W⁄F).Nonsingular x₀ y₀) : (uQ W h : FI) ≤ 1 := by
  rw [uQ, CoordinateRing.XYIdeal'_eq]; exact FractionalIdeal.coeIdeal_le_one

theorem one_le_J (h : (W⁄F).Nonsingular x₀ y₀) : (1 : FI) ≤ Jinv W h := by
  calc (1 : FI) = (uQ W h : FI) * Jinv W h := (Units.mul_inv _).symm
    _ ≤ 1 * Jinv W h := mul_le_mul_of_nonneg_right (uQ_le_one W h) zero_le
    _ = Jinv W h := one_mul _

theorem J_pow_mono (h : (W⁄F).Nonsingular x₀ y₀) {a b : ℕ} (hab : a ≤ b) :
    Jinv W h ^ a ≤ Jinv W h ^ b :=
  pow_le_pow_right₀ (one_le_J W h) hab

theorem rg_mem (h : (W⁄F).Nonsingular x₀ y₀) (k : ℕ) (r : Rg W) :
    algebraMap (Rg W) (Kf W) r ∈ Jinv W h ^ k :=
  one_le_pow₀ (one_le_J W h) ((FractionalIdeal.mem_one_iff _).2 ⟨r, rfl⟩)

theorem const_mem (h : (W⁄F).Nonsingular x₀ y₀) (k : ℕ) (c : F) : cK c ∈ Jinv W h ^ k := by
  rw [IsScalarTower.algebraMap_apply F (Rg W) (Kf W)]; exact rg_mem W h k _

theorem algebraMap_XClass (x : F) :
    algebraMap (Rg W) (Kf W) (CoordinateRing.XClass (W⁄F) x) = genX W - cK x := by
  have : CoordinateRing.XClass (W⁄F) x = xR W - algebraMap F (Rg W) x := by
    rw [CoordinateRing.XClass, CoordinateRing.mk, AdjoinRoot.mk_C, map_sub]; rfl
  rw [this, map_sub, ← IsScalarTower.algebraMap_apply]; rfl

theorem algebraMap_YClass (y : F) :
    algebraMap (Rg W) (Kf W) (CoordinateRing.YClass (W⁄F) (C y)) = genY W - cK y := by
  have : CoordinateRing.YClass (W⁄F) (C y) = yR W - algebraMap F (Rg W) y := by
    rw [CoordinateRing.YClass, CoordinateRing.mk, map_sub, AdjoinRoot.mk_X, AdjoinRoot.mk_C]; rfl
  rw [this, map_sub, ← IsScalarTower.algebraMap_apply]; rfl

/-- `m_P m_Q = (x − x₀)` with `P = −Q`. -/
theorem uP_mul_uQ (h : (W⁄F).Nonsingular x₀ y₀) :
    (CoordinateRing.XYIdeal' (nonsingular_neg' W h) : FI) * (uQ W h : FI) =
      FractionalIdeal.spanSingleton _ (genX W - cK x₀) := by
  rw [uQ, CoordinateRing.XYIdeal'_eq, CoordinateRing.XYIdeal'_eq, ← FractionalIdeal.coeIdeal_mul,
    CoordinateRing.XYIdeal_neg_mul h, CoordinateRing.XIdeal,
    FractionalIdeal.coeIdeal_span_singleton, algebraMap_XClass]

/-- **`ℓ ∈ m_Q⁻¹`**: the slope has at most a simple pole at `Q` and no other affine pole. -/
theorem lam_mem (h : (W⁄F).Nonsingular x₀ y₀) : lam W (x₀ := x₀) (y₀ := y₀) ∈ Jinv W h := by
  set d := genX W - cK x₀
  set S := FractionalIdeal.spanSingleton (Rg W)⁰ (d⁻¹)
  have e1 : FractionalIdeal.spanSingleton (Rg W)⁰ d * S = 1 := by
    rw [FractionalIdeal.spanSingleton_mul_spanSingleton, mul_inv_cancel₀ (genX_sub_ne_zero W),
      FractionalIdeal.spanSingleton_one]
  have hS : (CoordinateRing.XYIdeal' (nonsingular_neg' W h) : FI) * S = Jinv W h := by
    calc (CoordinateRing.XYIdeal' (nonsingular_neg' W h) : FI) * S =
        (CoordinateRing.XYIdeal' (nonsingular_neg' W h) : FI) * S * ((uQ W h : FI) * Jinv W h) := by
          rw [Units.mul_inv, mul_one]
      _ = ((CoordinateRing.XYIdeal' (nonsingular_neg' W h) : FI) * (uQ W h : FI)) * S *
          Jinv W h := by ring
      _ = Jinv W h := by rw [uP_mul_uQ, e1, one_mul]
  have hy : genY W - cK (yN W (x₀ := x₀) (y₀ := y₀)) ∈
      (CoordinateRing.XYIdeal' (nonsingular_neg' W h) : FI) := by
    rw [CoordinateRing.XYIdeal'_eq, FractionalIdeal.mem_coeIdeal]
    exact ⟨_, Ideal.subset_span (Set.mem_insert_of_mem _ rfl), algebraMap_YClass W _⟩
  rw [← hS, lam, div_eq_mul_inv]
  exact FractionalIdeal.mul_mem_mul hy (FractionalIdeal.mem_spanSingleton_self _ _)

theorem genX_mem (h : (W⁄F).Nonsingular x₀ y₀) (k : ℕ) : genX W ∈ Jinv W h ^ k := rg_mem W h k _
theorem genY_mem (h : (W⁄F).Nonsingular x₀ y₀) (k : ℕ) : genY W ∈ Jinv W h ^ k := rg_mem W h k _

theorem const_mul_mem (h : (W⁄F).Nonsingular x₀ y₀) {k : ℕ} (c : F) {z : Kf W}
    (hz : z ∈ Jinv W h ^ k) : cK c * z ∈ Jinv W h ^ k := by
  have := FractionalIdeal.mul_mem_mul (const_mem W h 0 c) hz
  rwa [pow_zero, one_mul] at this

/-- **`τ x ∈ m_Q^{−2}`**. -/
theorem transX_mem (h : (W⁄F).Nonsingular x₀ y₀) :
    transX W (-(Point.some x₀ y₀ h)) ∈ Jinv W h ^ 2 := by
  rw [transX_neg]
  have hl := lam_mem W h
  refine fi_sub W (fi_sub W (fi_sub W (fi_add W (fi_pow W hl 2) ?_) (const_mem W h 2 _))
    (genX_mem W h 2)) (const_mem W h 2 _)
  exact J_pow_mono W h (by norm_num : 1 ≤ 2) (by
    rw [pow_one]; exact (const_mul_mem W h (k := 1) _ (by rw [pow_one]; exact hl)) |>
      fun h' => by rwa [pow_one] at h')

/-- **`τ y ∈ m_Q^{−3}`**. -/
theorem transY_mem (h : (W⁄F).Nonsingular x₀ y₀) :
    transY W (-(Point.some x₀ y₀ h)) ∈ Jinv W h ^ 3 := by
  rw [transY_neg]
  have hl := lam_mem W h
  have hx := transX_mem W h
  have h3 : Jinv W h ^ 3 = Jinv W h * Jinv W h ^ 2 := by ring
  refine fi_sub W (fi_sub W (fi_neg W (fi_add W ?_ (genY_mem W h 3))) ?_) (const_mem W h 3 _)
  · rw [h3]
    exact FractionalIdeal.mul_mem_mul hl (fi_sub W hx (genX_mem W h 2))
  · exact J_pow_mono W h (by norm_num : 2 ≤ 3) (const_mul_mem W h _ hx)

/-- **`τ_{−Q} L(N·O) ⊆ m_Q^{−N}`**. -/
theorem trans_rr_mem (h : (W⁄F).Nonsingular x₀ y₀) {N : ℕ} {f : Kf W} (hf : f ∈ rrSpace W N) :
    trans W (-(Point.some x₀ y₀ h)) f ∈ Jinv W h ^ N := by
  have key : rrSpace W N ≤ Submodule.comap (trans W (-(Point.some x₀ y₀ h))).toLinearMap
      (((Jinv W h ^ N : FI) : Submodule (Rg W) (Kf W)).restrictScalars F) := by
    rw [rrSpace, Submodule.span_le]
    rintro _ (⟨i, hi, rfl⟩ | ⟨j, hj, rfl⟩)
    · change trans W _ (genX W ^ i) ∈ (Jinv W h ^ N : FI)
      rw [map_pow, trans_genX]
      have hi' : 2 * i ≤ N := hi
      exact J_pow_mono W h hi' (by rw [pow_mul]; exact fi_pow W (transX_mem W h) i)
    · change trans W _ (genX W ^ j * genY W) ∈ (Jinv W h ^ N : FI)
      rw [map_mul, map_pow, trans_genX, trans_genY]
      have hj' : 2 * j + 3 ≤ N := hj
      refine J_pow_mono W h hj' ?_
      rw [pow_add, pow_mul]
      exact FractionalIdeal.mul_mem_mul (fi_pow W (transX_mem W h) j) (transY_mem W h)
  exact key hf

/-! ### Regularity at `O`: `vK (τ_{−Q} f) ≤ 1` on `L(N·O)` -/

theorem le_one_of_mul_exp_le {a : Γ₀} {n : ℤ} (h : a * WithZero.exp n ≤ WithZero.exp n) :
    a ≤ 1 := by
  by_cases ha : a = 0
  · rw [ha]; exact zero_le
  rw [← WithZero.exp_log ha, ← WithZero.exp_add, WithZero.exp_le_exp] at h
  rw [← WithZero.exp_log ha, ← WithZero.exp_zero, WithZero.exp_le_exp]
  omega

theorem vK_const_mul_le (c : F) (z : Kf W) : vK W (cK c * z) ≤ vK W z := by
  rw [← Algebra.smul_def]; exact vK_smul_le W c z

theorem vK_genX_sub : vK W (genX W - cK x₀) = WithZero.exp 2 := by
  rw [Valuation.map_sub_eq_of_lt_left _ ((vK_const_le W x₀).trans_lt (by
    rw [vK_genX, ← WithZero.exp_zero, WithZero.exp_lt_exp]; norm_num)), vK_genX]

/-- The numerator of `τ x = n/(x − x₀)²`, reduced by the curve equation. -/
theorem transX_mul_sq (h : (W⁄F).Nonsingular x₀ y₀) :
    transX W (-(Point.some x₀ y₀ h)) * (genX W - cK x₀) ^ 2 =
      cK x₀ * genX W ^ 2 +
        cK (W.a₄ + x₀ ^ 2 + 2 * W.a₂ * x₀ - W.a₁ * yN W (x₀ := x₀) (y₀ := y₀)) * genX W +
        cK (W.a₆ + yN W (x₀ := x₀) (y₀ := y₀) ^ 2 + W.a₁ * x₀ * yN W (x₀ := x₀) (y₀ := y₀) -
          W.a₂ * x₀ ^ 2 - x₀ ^ 3) +
        cK (-W.a₃ - 2 * yN W (x₀ := x₀) (y₀ := y₀) - W.a₁ * x₀) * genY W := by
  have heq := equation_gen W
  rw [Affine.equation_iff, aK₁, aK₂, aK₃, aK₄, aK₆] at heq
  have hd := genX_sub_ne_zero W (x₀ := x₀)
  have hl : lam W (x₀ := x₀) (y₀ := y₀) * (genX W - cK x₀) =
      genY W - cK (yN W (x₀ := x₀) (y₀ := y₀)) := div_mul_cancel₀ _ hd
  have e : transX W (-(Point.some x₀ y₀ h)) * (genX W - cK x₀) ^ 2 =
      (lam W (x₀ := x₀) (y₀ := y₀) * (genX W - cK x₀)) ^ 2 +
        cK W.a₁ * (lam W (x₀ := x₀) (y₀ := y₀) * (genX W - cK x₀)) * (genX W - cK x₀) -
        (cK W.a₂ + genX W + cK x₀) * (genX W - cK x₀) ^ 2 := by
    rw [transX_neg]; ring
  rw [e, hl]
  simp only [map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat]
  linear_combination heq

/-- **`τ x` is regular at `O`.** -/
theorem vK_transX_le_one (h : (W⁄F).Nonsingular x₀ y₀) :
    vK W (transX W (-(Point.some x₀ y₀ h))) ≤ 1 := by
  have e := congrArg (vK W) (transX_mul_sq W h)
  rw [map_mul, map_pow, vK_genX_sub] at e
  refine le_one_of_mul_exp_le (n := 4) ?_
  have h4 : WithZero.exp (2 : ℤ) ^ 2 = WithZero.exp 4 := by
    rw [← WithZero.exp_nsmul]; norm_num
  rw [← h4, e]
  have hX2 : vK W (genX W ^ 2) = WithZero.exp 4 := by rw [map_pow, vK_genX, h4]
  have hle2 : WithZero.exp (2 : ℤ) ≤ WithZero.exp 4 := WithZero.exp_le_exp.2 (by norm_num)
  have hle3 : WithZero.exp (3 : ℤ) ≤ WithZero.exp 4 := WithZero.exp_le_exp.2 (by norm_num)
  have hle0 : (1 : Γ₀) ≤ WithZero.exp 4 := by rw [← WithZero.exp_zero, WithZero.exp_le_exp]; norm_num
  refine Valuation.map_add_le _ (Valuation.map_add_le _ (Valuation.map_add_le _ ?_ ?_) ?_) ?_
  · exact (vK_const_mul_le W _ _).trans hX2.le
  · exact (vK_const_mul_le W _ _).trans (by rw [vK_genX]; exact hle2)
  · exact (vK_const_le W _).trans hle0
  · exact (vK_const_mul_le W _ _).trans (by rw [vK_genY]; exact hle3)

/-- **`τ y` is regular at `O`**: it is integral over `F[τ x]`. -/
theorem vK_transY_le_one (h : (W⁄F).Nonsingular x₀ y₀) :
    vK W (transY W (-(Point.some x₀ y₀ h))) ≤ 1 := by
  set u := transX W (-(Point.some x₀ y₀ h))
  set t := transY W (-(Point.some x₀ y₀ h))
  have hu := vK_transX_le_one W h
  have heq := equation_trans W (-(Point.some x₀ y₀ h))
  rw [Affine.equation_iff, aK₁, aK₂, aK₃, aK₄, aK₆] at heq
  by_contra hlt
  rw [not_le] at hlt
  have ht0 : vK W t ≠ 0 := ne_of_gt (lt_trans zero_lt_one hlt)
  have hb : vK W ((cK W.a₁ * u + cK W.a₃) * t) ≤ vK W t := by
    rw [map_mul]
    calc vK W (cK W.a₁ * u + cK W.a₃) * vK W t ≤ 1 * vK W t := by
          refine mul_le_mul_left ?_ _
          exact Valuation.map_add_le _ ((vK_const_mul_le W _ _).trans hu) (vK_const_le W _)
      _ = vK W t := one_mul _
  have h2 : vK W t < vK W (t ^ 2) := by
    rw [map_pow, ← WithZero.exp_log ht0, ← WithZero.exp_nsmul, WithZero.exp_lt_exp]
    rw [← WithZero.exp_log ht0, ← WithZero.exp_zero, WithZero.exp_lt_exp] at hlt
    rw [nsmul_eq_mul]; push_cast; linarith
  have hL : vK W (t ^ 2 + (cK W.a₁ * u + cK W.a₃) * t) = vK W (t ^ 2) :=
    Valuation.map_add_eq_of_lt_left _ (hb.trans_lt h2)
  have hR : vK W (u ^ 3 + cK W.a₂ * u ^ 2 + cK W.a₄ * u + cK W.a₆) ≤ 1 := by
    refine Valuation.map_add_le _ (Valuation.map_add_le _ (Valuation.map_add_le _ ?_ ?_) ?_) ?_
    · rw [map_pow]; exact pow_le_one' hu _
    · exact (vK_const_mul_le W _ _).trans (by rw [map_pow]; exact pow_le_one' hu _)
    · exact (vK_const_mul_le W _ _).trans hu
    · exact vK_const_le W _
  have : t ^ 2 + (cK W.a₁ * u + cK W.a₃) * t = u ^ 3 + cK W.a₂ * u ^ 2 + cK W.a₄ * u + cK W.a₆ := by
    linear_combination heq
  rw [this] at hL
  exact absurd (hR.trans_lt (hlt.trans h2)) (by rw [hL]; exact lt_irrefl _)

/-- Functions regular at `O`, as an `F`-subspace. -/
def regO : Submodule F (Kf W) where
  carrier := {f | vK W f ≤ 1}
  add_mem' := by
    intro a b ha hb
    exact Valuation.map_add_le (vK W) (show vK W a ≤ 1 from ha) (show vK W b ≤ 1 from hb)
  zero_mem' := by change vK W 0 ≤ 1; rw [map_zero]; exact zero_le
  smul_mem' c _ hf := (vK_smul_le W c _).trans hf

theorem mem_regO {f : Kf W} : f ∈ regO W ↔ vK W f ≤ 1 := Iff.rfl

/-- **`τ_{−Q} L(N·O)` is regular at `O`.** -/
theorem vK_trans_rr_le_one (h : (W⁄F).Nonsingular x₀ y₀) {N : ℕ} {f : Kf W}
    (hf : f ∈ rrSpace W N) : vK W (trans W (-(Point.some x₀ y₀ h)) f) ≤ 1 := by
  have key : rrSpace W N ≤ Submodule.comap (trans W (-(Point.some x₀ y₀ h))).toLinearMap
      (regO W) := by
    rw [rrSpace, Submodule.span_le]
    rintro _ (⟨i, -, rfl⟩ | ⟨j, -, rfl⟩)
    · rw [SetLike.mem_coe, Submodule.mem_comap, mem_regO, AlgHom.toLinearMap_apply, map_pow,
        trans_genX, map_pow]
      exact pow_le_one' (vK_transX_le_one W h) _
    · rw [SetLike.mem_coe, Submodule.mem_comap, mem_regO, AlgHom.toLinearMap_apply, map_mul,
        map_pow, trans_genX, trans_genY, map_mul, map_pow]
      exact mul_le_one' (pow_le_one' (vK_transX_le_one W h) _) (vK_transY_le_one W h)
  exact key hf

end RamanujanWeil.Arith.Deuring.Geom.G7.DGeom
