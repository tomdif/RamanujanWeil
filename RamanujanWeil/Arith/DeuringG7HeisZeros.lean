import RamanujanWeil.Arith.DeuringG7HeisEval

/-!
# A3-ord, G7 Heisenberg (zeros): zeros of functions in `L(N·O)`

`docs/ARITH_DEURING_G7_AJHEIS.md` §2. For `r ∈ R = F[E]`, with norm `N(r) = r · σ r ∈ F[X]`:

* `mul_conj_eq_norm`: `r · σ(r) = N(r)`;
* `evPt_conj`: `(σ r)(Z) = r(−Z)`;
* `isRoot_norm_of_evPt`: `r(Z) = 0 ⟹ N(r)(x(Z)) = 0`;
* **`exists_zero`** (`F = F̄`): a non-constant `r` vanishes at some affine point;
* `eq_or_eq_neg_of_ptX_eq`: two affine points with the same `x` are `Z' = ±Z`;
* **`right_eq_one_of_left_const`**: an element `(c, P)` of `𝒢(L(N·O))` with `c ∈ F` has
  `P = O` (`N ≥ 1`); the pole order of a generator of `m_Q^N` is `N`.
-/

noncomputable section

namespace RamanujanWeil.Arith.Deuring.Geom.G7.DGeom

open WeierstrassCurve WeierstrassCurve.Affine Polynomial
open scoped nonZeroDivisors Polynomial.Bivariate

universe u

set_option linter.unusedSectionVars false

open scoped Classical

variable {F : Type u} [Field F] (W : Affine F) [W.IsElliptic] [DecidableEq F]

local notation "cK" => algebraMap F (Kf W)
local notation "ιK" => algebraMap (Rg W) (Kf W)

/-! ### The norm -/

theorem yR_sq :
    yR W ^ 2 = -(AdjoinRoot.of _ (C (W⁄F).a₁ * X + C (W⁄F).a₃)) * yR W +
      AdjoinRoot.of _ (X ^ 3 + C (W⁄F).a₂ * X ^ 2 + C (W⁄F).a₄ * X + C (W⁄F).a₆) := by
  have h := AdjoinRoot.eval₂_root (W⁄F).polynomial
  rw [eval₂_polynomial] at h
  change yR W ^ 2 + AdjoinRoot.of _ _ * yR W - AdjoinRoot.of _ _ = 0 at h
  linear_combination h

/-- **`r · σ r = N(r)`.** -/
theorem mul_conj_eq_norm (r : Rg W) :
    r * conj W r = AdjoinRoot.of _ (Algebra.norm F[X] r) := by
  obtain ⟨p, q, rfl⟩ := CoordinateRing.exists_smul_basis_eq r
  rw [conj_smul_basis, CoordinateRing.norm_smul_basis]
  have hY : CoordinateRing.mk (W⁄F) Y = yR W := AdjoinRoot.mk_X
  simp only [hY, Algebra.smul_def, AdjoinRoot.algebraMap_eq, mul_one, map_sub, map_mul,
    map_pow, map_neg, map_add]
  linear_combination (norm := (simp only [map_add, map_mul, map_pow]; ring))
    (-(AdjoinRoot.of (W⁄F).polynomial q) ^ 2) * yR_sq W

/-- `σ` as an `F`-algebra map. -/
abbrev conjF : Rg W →ₐ[F] Rg W := (conj W).restrictScalars F

theorem ptX_neg (Z : (W⁄F).Point) : ptX W (-Z) = ptX W Z := by
  cases Z with
  | zero => rfl
  | some x y h => rw [Point.neg_some]; rfl

theorem ptY_neg {Z : (W⁄F).Point} (hZ : Z ≠ 0) :
    ptY W (-Z) = (W⁄F).negY (ptX W Z) (ptY W Z) := by
  cases Z with
  | zero => exact absurd rfl hZ
  | some x y h => rw [Point.neg_some]; rfl

/-- **`(σ r)(Z) = r(−Z)`.** -/
theorem evPt_conj {Z : (W⁄F).Point} (hZ : Z ≠ 0) (r : Rg W) :
    evPt W Z hZ (conjF W r) = evPt W (-Z) (neg_ne_zero.2 hZ) r := by
  have := rg_algHom_ext W (φ := (evPt W Z hZ).comp (conjF W)) (ψ := evPt W (-Z) (neg_ne_zero.2 hZ))
    (by
      change evPt W Z hZ (conj W (AdjoinRoot.of _ X)) = _
      rw [conj_of]
      change evPt W Z hZ (xR W) = evPt W (-Z) _ (xR W)
      rw [evPt_xR, evPt_xR, ptX_neg])
    (by
      change evPt W Z hZ (conj W (yR W)) = _
      rw [conj_yR, evPt_yR, ptY_neg W hZ, conjY, map_sub, map_neg, evPt_yR]
      have : evPt W Z hZ (AdjoinRoot.of _ (C (W⁄F).a₁ * X + C (W⁄F).a₃)) =
          (W⁄F).a₁ * ptX W Z + (W⁄F).a₃ := by
        rw [evPt, coordHom_of]; simp
      rw [this, negY]; ring)
  exact congrArg (fun χ => χ r) this

theorem evPt_of (Z : (W⁄F).Point) (hZ : Z ≠ 0) (p : F[X]) :
    evPt W Z hZ (AdjoinRoot.of _ p) = p.eval (ptX W Z) := by
  rw [evPt, coordHom_of, Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, Algebra.algebraMap_self,
    Polynomial.map_id]

/-- **A zero of `r` is a root of its norm.** -/
theorem isRoot_norm_of_evPt {Z : (W⁄F).Point} (hZ : Z ≠ 0) {r : Rg W} (hr : evPt W Z hZ r = 0) :
    (Algebra.norm F[X] r).IsRoot (ptX W Z) := by
  have := congrArg (evPt W Z hZ) (mul_conj_eq_norm W r)
  rw [map_mul, hr, zero_mul, evPt_of] at this
  exact this.symm

/-! ### Existence of a zero -/

/-- **A non-constant `r ∈ F[E]` has a zero** (`F` algebraically closed). -/
theorem exists_zero [IsAlgClosed F] {r : Rg W} (hnc : 1 ≤ normDeg W r) :
    ∃ (Z : (W⁄F).Point) (hZ : Z ≠ 0), evPt W Z hZ r = 0 := by
  set n := Algebra.norm F[X] r
  have hdeg : n.degree ≠ 0 := by
    intro h
    have := natDegree_eq_of_degree_eq_some h
    change normDeg W r = 0 at this
    omega
  obtain ⟨x₁, hx₁⟩ := IsAlgClosed.exists_root n hdeg
  set A : F := (W⁄F).a₁ * x₁ + (W⁄F).a₃
  set B : F := x₁ ^ 3 + (W⁄F).a₂ * x₁ ^ 2 + (W⁄F).a₄ * x₁ + (W⁄F).a₆
  have hq : (X ^ 2 + C A * X - C B : F[X]).degree ≠ 0 := by
    rw [show (X ^ 2 + C A * X - C B : F[X]) = X ^ 2 + (C A * X - C B) by ring]
    rw [degree_add_eq_left_of_degree_lt]
    · simp
    · rw [degree_X_pow]
      refine (degree_sub_le _ _).trans_lt (max_lt ?_ ?_)
      · exact (degree_C_mul_X_le A).trans_lt (by norm_num)
      · exact (degree_C_le).trans_lt (by norm_num)
  obtain ⟨y₁, hy₁⟩ := IsAlgClosed.exists_root _ hq
  have heq : (W⁄F).Equation x₁ y₁ := by
    rw [Affine.equation_iff]
    simp only [IsRoot.def, eval_sub, eval_add, eval_pow, eval_X, eval_mul, eval_C] at hy₁
    simp only [A, B] at hy₁
    linear_combination hy₁
  have hns : (W⁄F).Nonsingular x₁ y₁ := (equation_iff_nonsingular).1 heq
  set Z₁ : (W⁄F).Point := Point.some x₁ y₁ hns
  have hZ₁ : Z₁ ≠ 0 := Point.some_ne_zero _
  have hprod := congrArg (evPt W Z₁ hZ₁) (mul_conj_eq_norm W r)
  rw [map_mul, evPt_of] at hprod
  change _ = n.eval x₁ at hprod
  rw [hx₁.eq_zero] at hprod
  rcases mul_eq_zero.1 hprod with h0 | h0
  · exact ⟨Z₁, hZ₁, h0⟩
  · change evPt W Z₁ hZ₁ (conjF W r) = 0 at h0
    rw [evPt_conj] at h0
    exact ⟨_, _, h0⟩

/-! ### Points with the same `x` -/

theorem eq_or_eq_neg_of_ptX_eq {Z Z' : (W⁄F).Point} (hZ : Z ≠ 0) (hZ' : Z' ≠ 0)
    (hx : ptX W Z = ptX W Z') : Z = Z' ∨ Z = -Z' := by
  cases Z with
  | zero => exact absurd rfl hZ
  | some x y h =>
    cases Z' with
    | zero => exact absurd rfl hZ'
    | some x' y' h' =>
      change x = x' at hx
      rcases Y_eq_of_X_eq h.1 h'.1 hx with hy | hy
      · exact Or.inl (some_eq_some W hx hy)
      · right
        rw [Point.neg_some]
        exact some_eq_some W hx hy

/-! ### `(c, P) ∈ 𝒢` with `c` constant forces `P = O` -/

/-- Every nonzero point is `−Q` for an affine `Q = (x₀, y₀)`. -/
theorem exists_eq_neg_some {R : (W⁄F).Point} (hR : R ≠ 0) :
    ∃ (x₀ y₀ : F) (h : (W⁄F).Nonsingular x₀ y₀), R = -(Point.some x₀ y₀ h) := by
  have hQ : -R ≠ 0 := neg_ne_zero.2 hR
  exact ⟨_, _, nonsingular_pt W hQ, by rw [← eq_some_pt W hQ, neg_neg]⟩

/-- The `f` of `(f, P) ∈ 𝒢(L(N·O))` lies in `L(N·O)` (`f = (f, P) · 1`). -/
theorem left_mem_rrSpace {N : ℕ} {g : Amb W} (hg : g ∈ thetaGroup W (rrSpace W N)) :
    ((g.left : (Kf W)ˣ) : Kf W) ∈ rrSpace W N := by
  rw [mem_thetaGroup] at hg
  have := Submodule.mem_map_of_mem (f := thetaAct W g) (one_mem_rrSpace' W N)
  rw [hg, thetaAct_apply, map_one, mul_one] at this
  exact this

/-- **`(c, P) ∈ 𝒢(L(N·O))` with `c ∈ F` has `P = O`** (`N ≥ 2`): a function `f` with
`f · τ_P L(N·O) = L(N·O)`, `P ≠ O`, has a pole of order `≥ N` at `O`. -/
theorem right_eq_zero_of_left_const {N : ℕ} (hN : 2 ≤ N) {g : Amb W}
    (hg : g ∈ thetaGroup W (rrSpace W N)) {c : F}
    (hc : ((g.left : (Kf W)ˣ) : Kf W) = cK c) : g.right.toAdd = 0 := by
  by_contra hR
  obtain ⟨x₀, y₀, h, hR'⟩ := exists_eq_neg_some W hR
  rw [mem_thetaGroup] at hg
  set f : Kf W := ((g.left : (Kf W)ˣ) : Kf W)
  have hact : ∀ v, thetaAct W g v = f * trans W (-(Point.some x₀ y₀ h)) v := by
    intro v; rw [thetaAct_apply, hR']
  have hpre : ∀ w ∈ rrSpace W N, ∃ v ∈ rrSpace W N,
      f * trans W (-(Point.some x₀ y₀ h)) v = w := by
    intro w hw
    rw [← hg] at hw
    obtain ⟨v, hv, rfl⟩ := hw
    exact ⟨v, hv, (hact v).symm⟩
  obtain ⟨w, hw, hwv⟩ := exists_rr_exact W hN
  obtain ⟨v1, hv1, e1⟩ := hpre w hw
  have hv : WithZero.exp (N : ℤ) ≤ vK W f := by
    rw [← hwv, ← e1, map_mul]
    calc vK W f * vK W (trans W (-(Point.some x₀ y₀ h)) v1) ≤ vK W f * 1 :=
          mul_le_mul_right (vK_trans_rr_le_one W h hv1) _
      _ = vK W f := mul_one _
  rw [hc] at hv
  have h1 := hv.trans (vK_const_le W c)
  have : ((N : ℕ) : ℤ) ≤ 0 := by
    rw [← WithZero.exp_zero, WithZero.exp_le_exp] at h1
    exact h1
  omega

end RamanujanWeil.Arith.Deuring.Geom.G7.DGeom
