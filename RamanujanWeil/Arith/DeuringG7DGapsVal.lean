import RamanujanWeil.Arith.DeuringG7DGeomKer
import Mathlib.RingTheory.Valuation.ExtendToLocalization

/-!
# A3-ord, G7-D-gaps (valuation at `O`): `ord_O` on `F(E)`, `L(N·O)`, and the conjugation

`docs/ARITH_DEURING_G7DGAPS.md` §1. Let `E = W⁄F`, `R = F[E]`, `K = F(E)`.

* **`vR`**: the valuation of `R` at the point at infinity, `vR r = exp(deg_X N(r))`, where
  `N : R → F[X]` is the norm. With Mathlib's `degree_norm_smul_basis`,
  `deg N(p + qY) = max(2 deg p, 2 deg q + 3)`, which is ultrametric because the two terms have
  different parities. So `vR x = e²`, `vR y = e³`, and `vR = 1` on `F^×`.
* **`vK`**: its extension to `K` (`Valuation.extendToLocalization`). It is `−ord_O`, i.e.
  `vK f ≤ 1` iff `f` is regular at `O`.
* **`rrSpace_eq_LN`**: `L(N·O) = {r ∈ R : vR r ≤ e^N}` (as a subspace of `K`).
* **`conj`**: the involution `σ : Y ↦ −Y − a₁X − a₃` of `R` (it is `[−1]^*`), with
  `N(r) = r · σ(r)` and `vR (σ r) = vR r`, and `σ(m_Q) = m_{−Q}`.
* **`isPrincipal_iff_vR`** (the degree argument): for `r ∈ R` with `m_Q^N ≤ (r)`,
  `m_Q^N = (r)` iff `vR r ≥ e^N`; and `m_Q^N = (r)` implies `vR r = e^N`. Taking norms, both reduce
  to `m_Q · σ(m_Q) = (X − x_Q)`.
-/

noncomputable section

namespace RamanujanWeil.Arith.Deuring.Geom.G7.DGeom

open WeierstrassCurve WeierstrassCurve.Affine Polynomial
open scoped nonZeroDivisors Polynomial.Bivariate

universe u

set_option linter.unusedSectionVars false

variable {F : Type u} [Field F] (W : Affine F) [W.IsElliptic] [DecidableEq F]

theorem withBot_nat_le {a b : ℕ} (h : (a : WithBot ℕ) ≤ (b : WithBot ℕ)) : a ≤ b := by
  exact_mod_cast h

theorem nat_eq_zero_of_exp_le_one {n : ℕ}
    (h : WithZero.exp ((n : ℕ) : ℤ) ≤ (1 : WithZero (Multiplicative ℤ))) : n = 0 := by
  rw [← WithZero.exp_zero, WithZero.exp_le_exp] at h
  omega

/-- The value group `ℤᵐ⁰`. -/
local notation "Γ₀" => WithZero (Multiplicative ℤ)

instance gaps_finite_Rg : Module.Finite F[X] (Rg W) :=
  Module.Finite.of_basis (CoordinateRing.basis _)

/-! ### The norm degree -/

/-- `deg_X N(r)`, the pole order of `r ∈ F[E]` at `O`. -/
def normDeg (r : Rg W) : ℕ := (Algebra.norm F[X] r).natDegree

theorem norm_ne_zero {r : Rg W} (hr : r ≠ 0) : Algebra.norm F[X] r ≠ 0 :=
  fun h => hr (Algebra.norm_eq_zero_iff.1 h)

theorem degree_norm_add_le (r s : Rg W) :
    (Algebra.norm F[X] (r + s)).degree ≤
      max (Algebra.norm F[X] r).degree (Algebra.norm F[X] s).degree := by
  obtain ⟨p, q, rfl⟩ := CoordinateRing.exists_smul_basis_eq r
  obtain ⟨p', q', rfl⟩ := CoordinateRing.exists_smul_basis_eq s
  have e : p • (1 : Rg W) + q • CoordinateRing.mk (W⁄F) Y + (p' • 1 + q' • CoordinateRing.mk _ Y) =
      (p + p') • 1 + (q + q') • CoordinateRing.mk (W⁄F) Y := by
    rw [add_smul, add_smul]; abel
  rw [e, CoordinateRing.degree_norm_smul_basis, CoordinateRing.degree_norm_smul_basis,
    CoordinateRing.degree_norm_smul_basis]
  have h1 : 2 • (p + p').degree ≤ max (2 • p.degree) (2 • p'.degree) := by
    have hd := degree_add_le p p'
    rcases le_total p.degree p'.degree with h | h
    · rw [max_eq_right h] at hd
      exact le_max_of_le_right (by rw [two_nsmul, two_nsmul]; exact add_le_add hd hd)
    · rw [max_eq_left h] at hd
      exact le_max_of_le_left (by rw [two_nsmul, two_nsmul]; exact add_le_add hd hd)
  have h2 : 2 • (q + q').degree + 3 ≤ max (2 • q.degree + 3) (2 • q'.degree + 3) := by
    have hd := degree_add_le q q'
    rcases le_total q.degree q'.degree with h | h
    · rw [max_eq_right h] at hd
      exact le_max_of_le_right (add_le_add_left
        (show 2 • (q + q').degree ≤ 2 • q'.degree by
          rw [two_nsmul, two_nsmul]; exact add_le_add hd hd) _)
    · rw [max_eq_left h] at hd
      exact le_max_of_le_left (add_le_add_left
        (show 2 • (q + q').degree ≤ 2 • q.degree by
          rw [two_nsmul, two_nsmul]; exact add_le_add hd hd) _)
  exact max_le (h1.trans (max_le (le_max_of_le_left (le_max_left _ _))
      (le_max_of_le_right (le_max_left _ _))))
    (h2.trans (max_le (le_max_of_le_left (le_max_right _ _))
      (le_max_of_le_right (le_max_right _ _))))

theorem normDeg_add_le {r s : Rg W} (hr : r ≠ 0) (hs : s ≠ 0) :
    normDeg W (r + s) ≤ max (normDeg W r) (normDeg W s) := by
  rw [normDeg, natDegree_le_iff_degree_le]
  refine (degree_norm_add_le W r s).trans (max_le ?_ ?_)
  · exact (degree_eq_natDegree (norm_ne_zero W hr)).le.trans
      (by exact_mod_cast le_max_left (normDeg W r) (normDeg W s))
  · exact (degree_eq_natDegree (norm_ne_zero W hs)).le.trans
      (by exact_mod_cast le_max_right (normDeg W r) (normDeg W s))

/-! ### The valuation `vR` on `F[E]` -/

/-- **The valuation of `F[E]` at `O`**: `r ↦ exp(deg N(r))` (so `vR x = e²`, `vR y = e³`). -/
def vR : Valuation (Rg W) Γ₀ where
  toFun r := if r = 0 then 0 else WithZero.exp ((normDeg W r : ℕ) : ℤ)
  map_zero' := if_pos rfl
  map_one' := by
    rw [if_neg one_ne_zero]
    simp [normDeg]
  map_mul' r s := by
    by_cases hr : r = 0
    · simp [hr]
    by_cases hs : s = 0
    · simp [hs]
    rw [if_neg (mul_ne_zero hr hs), if_neg hr, if_neg hs, ← WithZero.exp_add]
    congr 1
    simp only [normDeg, map_mul]
    rw [natDegree_mul (norm_ne_zero W hr) (norm_ne_zero W hs)]
    push_cast; ring
  map_add_le_max' r s := by
    by_cases hrs : r + s = 0
    · simp [hrs]
    by_cases hr : r = 0
    · simp [hr]
    by_cases hs : s = 0
    · simp [hs]
    simp only [if_neg hrs, if_neg hr, if_neg hs]
    rcases le_max_iff.1 (normDeg_add_le W hr hs) with h | h
    · exact le_max_of_le_left (WithZero.exp_le_exp.2 (by exact_mod_cast h))
    · exact le_max_of_le_right (WithZero.exp_le_exp.2 (by exact_mod_cast h))

theorem vR_of_ne {r : Rg W} (hr : r ≠ 0) : vR W r = WithZero.exp ((normDeg W r : ℕ) : ℤ) :=
  if_neg hr

theorem one_le_vR {r : Rg W} (hr : r ≠ 0) : 1 ≤ vR W r := by
  rw [vR_of_ne W hr, WithZero.one_le_exp_iff]
  exact Int.natCast_nonneg _

theorem vR_ne_zero {r : Rg W} (hr : r ≠ 0) : vR W r ≠ 0 := by
  rw [vR_of_ne W hr]; exact WithZero.exp_ne_zero

theorem degree_norm_smul_one (p : F[X]) :
    (Algebra.norm F[X] (p • (1 : Rg W))).degree = 2 • p.degree := by
  have := CoordinateRing.degree_norm_smul_basis (W' := W⁄F) p 0
  rw [zero_smul, add_zero] at this
  rw [this]
  simp

theorem vR_smul_one {p : F[X]} (hp : p ≠ 0) :
    vR W (p • (1 : Rg W)) = WithZero.exp ((2 * p.natDegree : ℕ) : ℤ) := by
  have h0 : p • (1 : Rg W) ≠ 0 := by
    intro h
    apply hp
    have := CoordinateRing.smul_basis_eq_zero (W' := W⁄F) (p := p) (q := 0)
      (by rw [zero_smul, add_zero]; exact h)
    exact this.1
  rw [vR_of_ne W h0, normDeg]
  congr 3
  apply natDegree_eq_of_degree_eq_some
  rw [degree_norm_smul_one, degree_eq_natDegree hp]
  norm_cast

theorem algebraMap_Rg (c : F) : algebraMap F (Rg W) c = (C c : F[X]) • (1 : Rg W) := by
  rw [Algebra.smul_def, mul_one, IsScalarTower.algebraMap_apply F F[X] (Rg W),
    Polynomial.algebraMap_apply]
  simp only [Algebra.algebraMap_self, RingHom.id_apply]

theorem xR_eq : xR W = (X : F[X]) • (1 : Rg W) := by
  rw [CoordinateRing.smul, mul_one]
  exact (AdjoinRoot.mk_C _).symm

theorem yR_eq : yR W = (0 : F[X]) • (1 : Rg W) + (1 : F[X]) • CoordinateRing.mk (W⁄F) Y := by
  rw [zero_smul, zero_add, one_smul]
  exact AdjoinRoot.mk_X.symm

theorem vR_xR : vR W (xR W) = WithZero.exp 2 := by
  rw [xR_eq, vR_smul_one W X_ne_zero, natDegree_X]; rfl

theorem vR_const {c : F} (hc : c ≠ 0) : vR W (algebraMap F (Rg W) c) = 1 := by
  rw [algebraMap_Rg, vR_smul_one W (C_ne_zero.2 hc), natDegree_C]; rfl

theorem vR_const_le (c : F) : vR W (algebraMap F (Rg W) c) ≤ 1 := by
  by_cases hc : c = 0
  · rw [hc, map_zero, map_zero]; exact zero_le'
  · exact (vR_const W hc).le

theorem vR_yR : vR W (yR W) = WithZero.exp 3 := by
  have h0 : yR W ≠ 0 := by
    intro h
    have := CoordinateRing.smul_basis_eq_zero (W' := W⁄F) (p := 0) (q := 1) (by rw [← yR_eq]; exact h)
    exact one_ne_zero this.2
  rw [vR_of_ne W h0, normDeg]
  congr 2
  have : (Algebra.norm F[X] (yR W)).natDegree = 3 := by
    apply natDegree_eq_of_degree_eq_some
    rw [yR_eq, CoordinateRing.degree_norm_smul_basis]
    simp
  rw [this]

/-- `vR r ≤ 1` with `r ≠ 0` forces `r ∈ F`: no non-constant function is regular at `O`. -/
theorem exists_const_of_vR_le_one {r : Rg W} (hr : r ≠ 0) (h : vR W r ≤ 1) :
    ∃ c : F, algebraMap F (Rg W) c = r := by
  rw [vR_of_ne W hr] at h
  have h0 : normDeg W r = 0 := nat_eq_zero_of_exp_le_one h
  obtain ⟨p, q, rfl⟩ := CoordinateRing.exists_smul_basis_eq r
  have hdeg := CoordinateRing.degree_norm_smul_basis (W' := W⁄F) p q
  rw [degree_eq_natDegree (norm_ne_zero W hr)] at hdeg
  change ((normDeg W _ : ℕ) : WithBot ℕ) = _ at hdeg
  rw [h0] at hdeg
  have hq : q = 0 := by
    by_contra hq
    have h3 : 2 • q.degree + 3 ≤ ((0 : ℕ) : WithBot ℕ) := hdeg ▸ le_max_right _ _
    rw [degree_eq_natDegree hq] at h3
    have h4 : ((2 * q.natDegree + 3 : ℕ) : WithBot ℕ) ≤ ((0 : ℕ) : WithBot ℕ) := by
      convert h3 using 1
      push_cast
      rw [nsmul_eq_mul]
      norm_num
    have := withBot_nat_le h4
    omega
  have hp : p.degree ≤ 0 := by
    by_cases hp : p = 0
    · rw [hp, degree_zero]; exact bot_le
    have h3 : 2 • p.degree ≤ ((0 : ℕ) : WithBot ℕ) := hdeg ▸ le_max_left _ _
    rw [degree_eq_natDegree hp] at h3 ⊢
    have h4 : ((2 * p.natDegree : ℕ) : WithBot ℕ) ≤ ((0 : ℕ) : WithBot ℕ) := by
      convert h3 using 1
      push_cast
      rw [nsmul_eq_mul]
      norm_num
    have h5 := withBot_nat_le h4
    have : p.natDegree = 0 := by omega
    rw [this]; rfl
  refine ⟨p.coeff 0, ?_⟩
  rw [hq, zero_smul, add_zero, algebraMap_Rg]
  conv_rhs => rw [eq_C_of_degree_le_zero hp]

theorem isUnit_of_vR_le_one {r : Rg W} (hr : r ≠ 0) (h : vR W r ≤ 1) : IsUnit r := by
  obtain ⟨c, rfl⟩ := exists_const_of_vR_le_one W hr h
  have hc : c ≠ 0 := by rintro rfl; exact hr (map_zero _)
  exact (IsUnit.mk0 c hc).map (algebraMap F (Rg W))

theorem vR_eq_one_of_isUnit {r : Rg W} (hr : IsUnit r) : vR W r = 1 := by
  obtain ⟨u, rfl⟩ := hr
  have h1 := one_le_vR W u.ne_zero
  have h2 := one_le_vR W (u⁻¹).ne_zero
  have h3 : vR W u * vR W (u⁻¹ : (Rg W)ˣ) = 1 := by
    rw [← map_mul, Units.mul_inv, map_one]
  refine le_antisymm ?_ h1
  calc vR W u = vR W u * 1 := (mul_one _).symm
    _ ≤ vR W u * vR W (u⁻¹ : (Rg W)ˣ) := mul_le_mul_right h2 _
    _ = 1 := h3

/-! ### The extension `vK` to `F(E)` -/

theorem le_primeCompl : (Rg W)⁰ ≤ (vR W).supp.primeCompl := by
  intro s hs
  change s ∉ (vR W).supp
  rw [Valuation.mem_supp_iff]
  exact vR_ne_zero W (nonZeroDivisors.ne_zero hs)

/-- **`−ord_O` on `F(E)`**: `vK f ≤ 1` iff `f` is regular at `O`. -/
def vK : Valuation (Kf W) Γ₀ := (vR W).extendToLocalization (le_primeCompl W) (Kf W)

theorem vK_algebraMap (r : Rg W) : vK W (algebraMap (Rg W) (Kf W) r) = vR W r :=
  Valuation.extendToLocalization_apply_map_apply _ _ _ r

theorem vK_genX : vK W (genX W) = WithZero.exp 2 := by
  rw [genX, vK_algebraMap, vR_xR]

theorem vK_genY : vK W (genY W) = WithZero.exp 3 := by
  rw [genY, vK_algebraMap, vR_yR]

theorem vK_const_le (c : F) : vK W (algebraMap F (Kf W) c) ≤ 1 := by
  rw [IsScalarTower.algebraMap_apply F (Rg W) (Kf W), vK_algebraMap]
  exact vR_const_le W c

theorem vK_const {c : F} (hc : c ≠ 0) : vK W (algebraMap F (Kf W) c) = 1 := by
  rw [IsScalarTower.algebraMap_apply F (Rg W) (Kf W), vK_algebraMap]
  exact vR_const W hc

theorem vK_smul_le (c : F) (f : Kf W) : vK W (c • f) ≤ vK W f := by
  rw [Algebra.smul_def, map_mul]
  calc vK W (algebraMap F (Kf W) c) * vK W f ≤ 1 * vK W f := mul_le_mul_left (vK_const_le W c) _
    _ = vK W f := one_mul _

/-! ### `L(N·O) = {r ∈ R : vR r ≤ e^N}` -/

/-- `{r ∈ F[E] : ord_O r ≥ −N}` as a subspace of `F(E)`. -/
def LN (N : ℕ) : Submodule F (Kf W) where
  carrier := {f | ∃ r : Rg W, algebraMap (Rg W) (Kf W) r = f ∧ vR W r ≤ WithZero.exp (N : ℤ)}
  zero_mem' := ⟨0, map_zero _, by rw [map_zero]; exact zero_le'⟩
  add_mem' := by
    rintro _ _ ⟨r, rfl, hr⟩ ⟨s, rfl, hs⟩
    exact ⟨r + s, map_add _ _ _, ((vR W).map_add r s).trans (max_le hr hs)⟩
  smul_mem' := by
    rintro c _ ⟨r, rfl, hr⟩
    refine ⟨algebraMap F (Rg W) c * r, ?_, ?_⟩
    · rw [map_mul, ← IsScalarTower.algebraMap_apply, Algebra.smul_def]
    · rw [map_mul]
      calc vR W (algebraMap F (Rg W) c) * vR W r ≤ 1 * vR W r := mul_le_mul_left (vR_const_le W c) _
        _ = vR W r := one_mul _
        _ ≤ _ := hr

theorem mem_LN {N : ℕ} {f : Kf W} :
    f ∈ LN W N ↔ ∃ r : Rg W, algebraMap (Rg W) (Kf W) r = f ∧ vR W r ≤ WithZero.exp (N : ℤ) :=
  Iff.rfl

theorem rrSpace_le_LN (N : ℕ) : rrSpace W N ≤ LN W N := by
  rw [rrSpace, Submodule.span_le]
  rintro _ (⟨i, hi, rfl⟩ | ⟨j, hj, rfl⟩)
  · refine ⟨xR W ^ i, by rw [map_pow]; rfl, ?_⟩
    rw [map_pow, vR_xR, ← WithZero.exp_nsmul, WithZero.exp_le_exp, nsmul_eq_mul]
    have : 2 * i ≤ N := hi
    omega
  · refine ⟨xR W ^ j * yR W, by rw [map_mul, map_pow]; rfl, ?_⟩
    rw [map_mul, map_pow, vR_xR, vR_yR, ← WithZero.exp_nsmul, ← WithZero.exp_add,
      WithZero.exp_le_exp, nsmul_eq_mul]
    have : 2 * j + 3 ≤ N := hj
    omega

theorem algebraMap_smul_basis (p q : F[X]) :
    algebraMap (Rg W) (Kf W) (p • (1 : Rg W) + q • CoordinateRing.mk (W⁄F) Y) =
      Polynomial.aeval (genX W) p + Polynomial.aeval (genX W) q * genY W := by
  rw [aeval_genX, aeval_genX, genY, ← map_mul, ← map_add, CoordinateRing.smul,
    CoordinateRing.smul, mul_one, AdjoinRoot.mk_X]
  rfl

theorem LN_le_rrSpace (N : ℕ) : LN W N ≤ rrSpace W N := by
  rintro _ ⟨r, rfl, hr⟩
  by_cases hr0 : r = 0
  · rw [hr0, map_zero]; exact Submodule.zero_mem _
  rw [vR_of_ne W hr0, WithZero.exp_le_exp] at hr
  have hN : normDeg W r ≤ N := by omega
  rw [normDeg, natDegree_le_iff_degree_le] at hN
  obtain ⟨p, q, rfl⟩ := CoordinateRing.exists_smul_basis_eq r
  rw [CoordinateRing.degree_norm_smul_basis] at hN
  rw [algebraMap_smul_basis]
  refine Submodule.add_mem _ ?_ ?_
  · rw [aeval_eq_sum_range]
    refine Submodule.sum_mem _ fun i hi => ?_
    by_cases hc : p.coeff i = 0
    · rw [hc, zero_smul]; exact Submodule.zero_mem _
    have hp : p ≠ 0 := fun h => hc (by rw [h, coeff_zero])
    have h3 : 2 • p.degree ≤ (N : WithBot ℕ) := (le_max_left _ _).trans hN
    rw [degree_eq_natDegree hp] at h3
    have h4 : ((2 * p.natDegree : ℕ) : WithBot ℕ) ≤ (N : WithBot ℕ) := by
      convert h3 using 1
      push_cast
      rw [nsmul_eq_mul]
      norm_num
    have h5 := withBot_nat_le h4
    have h6 := Finset.mem_range.1 hi
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Or.inl ⟨i, by
      change 2 * i ≤ N; omega, rfl⟩))
  · rw [aeval_eq_sum_range, Finset.sum_mul]
    refine Submodule.sum_mem _ fun i hi => ?_
    rw [smul_mul_assoc]
    by_cases hc : q.coeff i = 0
    · rw [hc, zero_smul]; exact Submodule.zero_mem _
    have hq : q ≠ 0 := fun h => hc (by rw [h, coeff_zero])
    have h3 : 2 • q.degree + 3 ≤ (N : WithBot ℕ) := (le_max_right _ _).trans hN
    rw [degree_eq_natDegree hq] at h3
    have h4 : ((2 * q.natDegree + 3 : ℕ) : WithBot ℕ) ≤ (N : WithBot ℕ) := by
      convert h3 using 1
      push_cast
      rw [nsmul_eq_mul]
      norm_num
    have h5 := withBot_nat_le h4
    have h6 := Finset.mem_range.1 hi
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Or.inr ⟨i, by
      change 2 * i + 3 ≤ N; omega, rfl⟩))

/-- **`L(N·O) = {r ∈ F[E] : vR r ≤ e^N}`.** -/
theorem rrSpace_eq_LN (N : ℕ) : rrSpace W N = LN W N :=
  le_antisymm (rrSpace_le_LN W N) (LN_le_rrSpace W N)

end RamanujanWeil.Arith.Deuring.Geom.G7.DGeom
