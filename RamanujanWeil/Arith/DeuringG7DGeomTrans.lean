import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.FieldTheory.AlgebraicClosure
import Mathlib.RingTheory.Norm.Basic

/-!
# A3-ord, G7-D-geom (translations): the translation automorphisms of the function field

`docs/ARITH_DEURING_G7DGEOM.md` §1. Let `W` be an elliptic curve over a field `F`, `E = W⁄F`,
`R = F[E]` its affine coordinate ring and `K = F(E)` its function field. For a point
`P ∈ E(F)` the translation `t_P : Q ↦ Q + P` acts on rational functions by pull-back,
`τ_P f = f ∘ t_P`. We build these as `F`-algebra automorphisms of `K` with the composition law
`τ_P ∘ τ_Q = τ_{P+Q}` through the **generic point**:

* `genX, genY : K` are the coordinate functions; `ξ = (genX, genY) ∈ E(K)` is the generic point
  (`genPt`).
* `coordHom`: the universal property of `R`: an `F`-algebra map `R → L` is the same as an
  `L`-point of the affine curve.
* `τ_P` is the `F`-algebra endomorphism of `K` sending `ξ` to `ξ + P_K` (`transPt`). It exists
  because `ξ + P_K` is affine and its `X`-coordinate is **transcendental** over `F`
  (`transcendental_transX`), which makes `R → K` injective (`coordHom_injective`, through the
  norm `N(p + qY) = p² − pq(a₁X + a₃) − q²(X³ + …)` of the coordinate ring).
* **`map_trans_genPt`**: `τ_P(ξ) = ξ + P_K`, and **`trans_add`**: `τ_P ∘ τ_Q = τ_{P+Q}`. Both
  follow from `Point.map` being a group homomorphism `E(K) → E(K)` fixing `E(F)`, so the
  composition law is the associativity of Mathlib's point group over `K`. No formula for the
  translated functions is ever expanded.
* `transAut : Multiplicative E(F) →* (K ≃ₐ[F] K)`.
-/

noncomputable section

namespace RamanujanWeil.Arith.Deuring.Geom.G7.DGeom

open WeierstrassCurve WeierstrassCurve.Affine Polynomial
open scoped Polynomial.Bivariate

universe u

variable {F : Type u} [Field F] (W : Affine F)

/-- The affine coordinate ring `F[E]` of `E = W⁄F`. -/
abbrev Rg : Type u := (W⁄F).CoordinateRing

/-- The function field `F(E)`. -/
abbrev Kf : Type u := (W⁄F).FunctionField

/-- `X ∈ F[E]`. -/
abbrev xR : Rg W := AdjoinRoot.of _ Polynomial.X

/-- `Y ∈ F[E]`. -/
abbrev yR : Rg W := AdjoinRoot.root _

/-- The coordinate function `x ∈ F(E)`. -/
def genX : Kf W := algebraMap (Rg W) (Kf W) (xR W)

/-- The coordinate function `y ∈ F(E)`. -/
def genY : Kf W := algebraMap (Rg W) (Kf W) (yR W)

/-! ### The universal property of the coordinate ring -/

section Universal

variable {L : Type*} [Field L] [Algebra F L]

theorem equation_iff_eval₂ (x y : L) :
    (W⁄L).Equation x y ↔
      ((W⁄F).polynomial).eval₂ (Polynomial.eval₂RingHom (algebraMap F L) x) y = 0 := by
  rw [Affine.equation_iff]
  simp only [Affine.polynomial, eval₂_add, eval₂_sub, eval₂_mul, eval₂_pow, eval₂_X, eval₂_C,
    coe_eval₂RingHom, Affine.baseChange, WeierstrassCurve.baseChange, WeierstrassCurve.map_a₁,
    WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₃, WeierstrassCurve.map_a₄,
    WeierstrassCurve.map_a₆, Algebra.algebraMap_self, RingHom.id_apply]
  constructor <;> intro h <;> linear_combination h

/-- **The universal property of `F[E]`**: an `L`-point `(x, y)` of the affine curve gives the
`F`-algebra map `X ↦ x, Y ↦ y`. -/
def coordHom (x y : L) (h : (W⁄L).Equation x y) : Rg W →ₐ[F] L where
  __ := AdjoinRoot.lift (Polynomial.eval₂RingHom (algebraMap F L) x) y
    ((equation_iff_eval₂ W x y).1 h)
  commutes' c := by
    change AdjoinRoot.lift _ _ _ (AdjoinRoot.of _ (Polynomial.C c)) = _
    rw [AdjoinRoot.lift_of]
    simp

@[simp] theorem coordHom_xR (x y : L) (h : (W⁄L).Equation x y) : coordHom W x y h (xR W) = x := by
  change AdjoinRoot.lift (Polynomial.eval₂RingHom (algebraMap F L) x) y
    ((equation_iff_eval₂ W x y).1 h) (AdjoinRoot.of _ Polynomial.X) = _
  rw [AdjoinRoot.lift_of]
  simp

@[simp] theorem coordHom_yR (x y : L) (h : (W⁄L).Equation x y) : coordHom W x y h (yR W) = y := by
  change AdjoinRoot.lift (Polynomial.eval₂RingHom (algebraMap F L) x) y
    ((equation_iff_eval₂ W x y).1 h) (AdjoinRoot.root _) = _
  rw [AdjoinRoot.lift_root]

/-- `F`-algebra maps out of `F[E]` agree when they agree on `X` and `Y`. -/
theorem rg_algHom_ext {A : Type*} [CommRing A] [Algebra F A] {φ ψ : Rg W →ₐ[F] A}
    (hx : φ (xR W) = ψ (xR W)) (hy : φ (yR W) = ψ (yR W)) : φ = ψ := by
  apply AlgHom.coe_ringHom_injective
  refine AdjoinRoot.ringHom_ext ?_ hy
  apply Polynomial.ringHom_ext
  · intro c
    change φ (algebraMap F (Rg W) c) = ψ (algebraMap F (Rg W) c)
    rw [φ.commutes, ψ.commutes]
  · exact hx

/-- Every `F`-algebra map out of `F[E]` is `coordHom` of its values on `X, Y`. -/
theorem equation_of_algHom (φ : Rg W →ₐ[F] L) : (W⁄L).Equation (φ (xR W)) (φ (yR W)) := by
  rw [equation_iff_eval₂]
  have h0 := congrArg (φ : Rg W →+* L) (AdjoinRoot.eval₂_root (W⁄F).polynomial)
  rw [map_zero, Polynomial.hom_eval₂] at h0
  have hc : Polynomial.eval₂RingHom (algebraMap F L) (φ (xR W)) =
      (φ : Rg W →+* L).comp (AdjoinRoot.of _) := by
    apply Polynomial.ringHom_ext
    · intro c
      change _ = φ (algebraMap F (Rg W) c)
      rw [φ.commutes]
      simp
    · simp
  rw [hc]
  exact h0

end Universal

/-! ### The generic point -/

section Generic

theorem equation_gen : (W⁄(Kf W)).Equation (genX W) (genY W) := by
  have := equation_of_algHom W (IsScalarTower.toAlgHom F (Rg W) (Kf W))
  simpa [genX, genY] using this

variable [W.IsElliptic]

instance isElliptic_baseChange (L : Type*) [Field L] [Algebra F L] : (W⁄L).IsElliptic := by
  exact inferInstanceAs (WeierstrassCurve.IsElliptic (WeierstrassCurve.map W (algebraMap F L)))

theorem nonsingular_gen : (W⁄(Kf W)).Nonsingular (genX W) (genY W) :=
  (equation_iff_nonsingular).1 (equation_gen W)

variable [DecidableEq F]

open scoped Classical in
/-- **The generic point** `ξ = (x, y) ∈ E(F(E))`. -/
def genPt : (W⁄(Kf W)).Point := .some _ _ (nonsingular_gen W)

theorem aeval_genX (p : F[X]) :
    Polynomial.aeval (genX W) p = algebraMap (Rg W) (Kf W) (AdjoinRoot.of _ p) := by
  induction p using Polynomial.induction_on with
  | C c =>
    rw [Polynomial.aeval_C]
    exact IsScalarTower.algebraMap_apply F (Rg W) (Kf W) c
  | add p q hp hq => rw [map_add, map_add, map_add, hp, hq]
  | monomial n c _ =>
    rw [map_mul, map_pow, Polynomial.aeval_X, map_mul, map_mul, map_pow, map_pow, Polynomial.aeval_C]
    congr 1

/-- `x` is transcendental over `F`: `F[X] ⊆ F[E] ⊆ F(E)`. -/
theorem transcendental_genX : Transcendental F (genX W) := by
  rintro ⟨p, hp0, hp⟩
  apply hp0
  have hinj : Function.Injective (AdjoinRoot.of (W⁄F).polynomial) :=
    AdjoinRoot.of.injective_of_degree_ne_zero (by
      rw [Affine.degree_polynomial]; exact two_ne_zero)
  rw [aeval_genX] at hp
  exact hinj ((IsFractionRing.injective (Rg W) (Kf W)) (hp.trans (map_zero _).symm) |>.trans
    (map_zero _).symm)


/-! ### Coordinates of points -/

/-- The `X`-coordinate of a point (junk `0` at infinity). -/
def ptX {L : Type*} [Field L] [Algebra F L] : (W⁄L).Point → L
  | .zero => 0
  | .some x _ _ => x

/-- The `Y`-coordinate of a point (junk `0` at infinity). -/
def ptY {L : Type*} [Field L] [Algebra F L] : (W⁄L).Point → L
  | .zero => 0
  | .some _ y _ => y

theorem nonsingular_pt {L : Type*} [Field L] [Algebra F L] {Q : (W⁄L).Point} (hQ : Q ≠ 0) :
    (W⁄L).Nonsingular (ptX W Q) (ptY W Q) := by
  cases Q with
  | zero => exact absurd rfl hQ
  | some x y h => exact h

theorem eq_some_pt {L : Type*} [Field L] [Algebra F L] {Q : (W⁄L).Point} (hQ : Q ≠ 0) :
    Q = .some _ _ (nonsingular_pt W hQ) := by
  cases Q with
  | zero => exact absurd rfl hQ
  | some x y h => rfl

/-! ### The injectivity criterion -/

theorem coordHom_of (L : Type*) [Field L] [Algebra F L] (x y : L) (h : (W⁄L).Equation x y)
    (p : F[X]) : coordHom W x y h (AdjoinRoot.of _ p) = Polynomial.aeval x p := by
  change AdjoinRoot.lift (Polynomial.eval₂RingHom (algebraMap F L) x) y
    ((equation_iff_eval₂ W x y).1 h) (AdjoinRoot.of _ p) = _
  rw [AdjoinRoot.lift_of]
  rfl

/-- **`R → L`, `X ↦ x`, `Y ↦ y`, is injective when `x` is transcendental.** If `p + qY ↦ 0`
then `x` is a root of the norm `p² − pq(a₁X + a₃) − q²(X³ + a₂X² + a₄X + a₆)`. -/
theorem coordHom_injective (L : Type*) [Field L] [Algebra F L] (x y : L)
    (h : (W⁄L).Equation x y) (hx : Transcendental F x) :
    Function.Injective (coordHom W x y h) := by
  rw [injective_iff_map_eq_zero]
  intro r hr
  obtain ⟨p, q, rfl⟩ := Affine.CoordinateRing.exists_smul_basis_eq r
  have hr' : Polynomial.aeval x p + Polynomial.aeval x q * y = 0 := by
    rw [map_add, Algebra.smul_def, Algebra.smul_def, map_mul, map_mul, map_one, mul_one] at hr
    have h1 := coordHom_of W L x y h p
    have h2 := coordHom_of W L x y h q
    have h3 := coordHom_yR W x y h
    have : (Affine.CoordinateRing.mk (W⁄F) Y) = yR W := AdjoinRoot.mk_X
    rw [this] at hr
    change coordHom W x y h (AdjoinRoot.of _ p) +
      coordHom W x y h (AdjoinRoot.of _ q) * coordHom W x y h (yR W) = 0 at hr
    rwa [h1, h2, h3] at hr
  have hN : Polynomial.aeval x (Algebra.norm F[X] (p • (1 : Rg W) + q • AdjoinRoot.mk _ Y)) = 0 := by
    rw [Affine.CoordinateRing.norm_smul_basis]
    rw [Affine.equation_iff] at h
    simp only [map_sub, map_mul, map_pow, map_add, Polynomial.aeval_X, Polynomial.aeval_C,
      Affine.baseChange, WeierstrassCurve.baseChange, WeierstrassCurve.map_a₁,
      WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₃, WeierstrassCurve.map_a₄,
      WeierstrassCurve.map_a₆, Algebra.algebraMap_self, RingHom.id_apply] at h ⊢
    linear_combination (Polynomial.aeval x q) ^ 2 * h +
      (Polynomial.aeval x p - Polynomial.aeval x q * y -
        Polynomial.aeval x q * (algebraMap F L W.a₁ * x + algebraMap F L W.a₃)) * hr'
  have hN0 : Algebra.norm F[X] (p • (1 : Rg W) + q • AdjoinRoot.mk _ Y) = 0 := by
    by_contra hne
    exact hx ⟨_, hne, hN⟩
  have : Module.Finite F[X] (Rg W) := Module.Finite.of_basis (Affine.CoordinateRing.basis _)
  exact Algebra.norm_eq_zero_iff.1 hN0


theorem some_eq_some {L : Type*} [Field L] [Algebra F L] {x y x' y' : L}
    {h : (W⁄L).Nonsingular x y} {h' : (W⁄L).Nonsingular x' y'} (hx : x = x') (hy : y = y') :
    (Point.some x y h : (W⁄L).Point) = Point.some x' y' h' := by
  subst hx hy; rfl

/-- `y` is integral over `F` when `x` is: it is a root of `Y² + (a₁x + a₃)Y − (x³ + …)`. -/
theorem isIntegral_y {L : Type*} [Field L] [Algebra F L] {x y : L} (h : (W⁄L).Equation x y)
    (hx : IsIntegral F x) : IsIntegral F y := by
  set F' := algebraicClosure F L
  have hxm : x ∈ F' := (mem_algebraicClosure_iff').2 hx
  let a : F' := ⟨algebraMap F L W.a₁ * x + algebraMap F L W.a₃,
    add_mem (mul_mem (F'.algebraMap_mem _) hxm) (F'.algebraMap_mem _)⟩
  let b : F' := ⟨x ^ 3 + algebraMap F L W.a₂ * x ^ 2 + algebraMap F L W.a₄ * x +
      algebraMap F L W.a₆, add_mem (add_mem (add_mem (pow_mem hxm 3)
        (mul_mem (F'.algebraMap_mem _) (pow_mem hxm 2))) (mul_mem (F'.algebraMap_mem _) hxm))
        (F'.algebraMap_mem _)⟩
  have hint : IsIntegral F' y := by
    refine ⟨Polynomial.X ^ 2 + (Polynomial.C a * Polynomial.X - Polynomial.C b), ?_, ?_⟩
    · refine (Polynomial.monic_X_pow 2).add_of_left ?_
      rw [Polynomial.degree_X_pow]
      refine lt_of_le_of_lt (Polynomial.degree_sub_le _ _) (max_lt ?_ ?_)
      · exact lt_of_le_of_lt (Polynomial.degree_C_mul_X_le _) (by norm_num)
      · exact lt_of_le_of_lt Polynomial.degree_C_le (by norm_num)
    · rw [Affine.equation_iff] at h
      simp only [Affine.baseChange, WeierstrassCurve.baseChange, WeierstrassCurve.map_a₁,
        WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₃, WeierstrassCurve.map_a₄,
        WeierstrassCurve.map_a₆] at h
      simp only [Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_mul,
        Polynomial.eval₂_pow, Polynomial.eval₂_X, Polynomial.eval₂_C]
      change y ^ 2 + ((algebraMap F L W.a₁ * x + algebraMap F L W.a₃) * y -
        (x ^ 3 + algebraMap F L W.a₂ * x ^ 2 + algebraMap F L W.a₄ * x + algebraMap F L W.a₆)) = 0
      linear_combination h
  exact isIntegral_trans y hint

end Generic

section Trans

variable [W.IsElliptic] [DecidableEq F]

open scoped Classical

/-- `P_K ∈ E(F(E))`, the base change of `P ∈ E(F)`. -/
abbrev bc (P : (W⁄F).Point) : (W⁄(Kf W)).Point := Point.baseChange F (Kf W) P

/-- The generic point is not defined over `F`. -/
theorem genPt_ne_bc (Q : (W⁄F).Point) : genPt W ≠ bc W Q := by
  cases Q with
  | zero => intro h; cases h
  | some a b hab =>
    intro h
    rw [bc, Point.baseChange, Point.map_some] at h
    injection h with hx
    exact transcendental_genX W (hx ▸ isAlgebraic_algebraMap a)

/-- **The translate of the generic point**, `ξ + P_K`. -/
def transPt (P : (W⁄F).Point) : (W⁄(Kf W)).Point := genPt W + bc W P

theorem transPt_ne_zero (P : (W⁄F).Point) : transPt W P ≠ 0 := by
  intro h
  apply genPt_ne_bc W (-P)
  rw [bc, map_neg, ← bc, eq_neg_iff_add_eq_zero]
  exact h

/-- `x(ξ + P_K) ∈ F(E)`. -/
abbrev transX (P : (W⁄F).Point) : Kf W := ptX W (transPt W P)

/-- `y(ξ + P_K) ∈ F(E)`. -/
abbrev transY (P : (W⁄F).Point) : Kf W := ptY W (transPt W P)

theorem equation_trans (P : (W⁄F).Point) : (W⁄(Kf W)).Equation (transX W P) (transY W P) :=
  (nonsingular_pt W (transPt_ne_zero W P)).1

/-- **`x(ξ + P_K)` is transcendental over `F`.** Otherwise `ξ + P_K` is defined over the
algebraic closure `F'` of `F` in `F(E)`, hence so is `ξ = (ξ + P_K) + (−P)_K`, but `x(ξ)` is
transcendental. -/
theorem transcendental_transX (P : (W⁄F).Point) : Transcendental F (transX W P) := by
  intro halg
  set F' := algebraicClosure F (Kf W)
  have hx : transX W P ∈ F' := (mem_algebraicClosure_iff).2 halg
  have hy : transY W P ∈ F' := (mem_algebraicClosure_iff').2
    (isIntegral_y W (equation_trans W P) halg.isIntegral)
  let ι : F' →ₐ[F] Kf W := IsScalarTower.toAlgHom F F' (Kf W)
  have hns : (W⁄F').Nonsingular ⟨_, hx⟩ ⟨_, hy⟩ :=
    (Affine.baseChange_nonsingular (W := W) ι.injective _ _).1
      (nonsingular_pt W (transPt_ne_zero W P))
  let Q' : (W⁄F').Point := .some _ _ hns
  have hQ' : Point.map ι Q' = transPt W P := by
    rw [Point.map_some]
    conv_rhs => rw [eq_some_pt W (transPt_ne_zero W P)]
    exact some_eq_some W rfl rfl
  have hQ'' : Point.map ι (Q' + Point.baseChange F F' (-P)) = genPt W := by
    rw [map_add, hQ', Point.map_baseChange, transPt, map_neg, add_neg_cancel_right]
  generalize Q' + Point.baseChange F F' (-P) = Q'' at hQ''
  cases Q'' with
  | zero => exact absurd hQ'' (by rw [genPt]; intro h; cases h)
  | some a b hab =>
    rw [Point.map_some, genPt] at hQ''
    injection hQ'' with hxa
    apply transcendental_genX W
    rw [← hxa]
    exact (mem_algebraicClosure_iff).1 a.2

/-- `F[E] → F(E)`, `(X, Y) ↦ ξ + P_K`. -/
def sigma (P : (W⁄F).Point) : Rg W →ₐ[F] Kf W :=
  coordHom W (transX W P) (transY W P) (equation_trans W P)

theorem sigma_injective (P : (W⁄F).Point) : Function.Injective (sigma W P) :=
  coordHom_injective W _ _ _ (equation_trans W P) (transcendental_transX W P)

/-- **The translation `τ_P = t_P^*` on `F(E)`**: `f ↦ f ∘ t_P`, the `F`-algebra map sending the
generic point `ξ` to `ξ + P`. -/
def trans (P : (W⁄F).Point) : Kf W →ₐ[F] Kf W :=
  IsFractionRing.liftAlgHom (sigma_injective W P)

theorem trans_algebraMap (P : (W⁄F).Point) (r : Rg W) :
    trans W P (algebraMap (Rg W) (Kf W) r) = sigma W P r :=
  IsFractionRing.lift_algebraMap (sigma_injective W P) r

theorem trans_genX (P : (W⁄F).Point) : trans W P (genX W) = transX W P := by
  rw [genX, trans_algebraMap, sigma, coordHom_xR]

theorem trans_genY (P : (W⁄F).Point) : trans W P (genY W) = transY W P := by
  rw [genY, trans_algebraMap, sigma, coordHom_yR]

/-- `F`-algebra maps out of `F(E)` agree when they agree on `x, y`. -/
theorem kf_algHom_ext {L : Type*} [Field L] [Algebra F L] {φ ψ : Kf W →ₐ[F] L}
    (hx : φ (genX W) = ψ (genX W)) (hy : φ (genY W) = ψ (genY W)) : φ = ψ := by
  apply AlgHom.coe_ringHom_injective
  apply IsFractionRing.ringHom_ext (A := Rg W)
  intro r
  have := rg_algHom_ext W (φ := φ.comp (IsScalarTower.toAlgHom F (Rg W) (Kf W)))
    (ψ := ψ.comp (IsScalarTower.toAlgHom F (Rg W) (Kf W))) hx hy
  exact congrArg (fun χ => χ r) this

/-- `F`-algebra maps `F(E) → F(E)` are determined by the image of the generic point. -/
theorem eq_of_map_genPt {φ ψ : Kf W →ₐ[F] Kf W}
    (h : Point.map φ (genPt W) = Point.map ψ (genPt W)) : φ = ψ := by
  rw [genPt, Point.map_some, Point.map_some] at h
  injection h with hx hy
  exact kf_algHom_ext W hx hy

/-- **`τ_P(ξ) = ξ + P_K`.** -/
theorem map_trans_genPt (P : (W⁄F).Point) : Point.map (trans W P) (genPt W) = transPt W P := by
  rw [genPt, Point.map_some]
  conv_rhs => rw [eq_some_pt W (transPt_ne_zero W P)]
  exact some_eq_some W (trans_genX W P) (trans_genY W P)

theorem map_id_genPt : Point.map (AlgHom.id F (Kf W)) (genPt W) = genPt W := by
  rw [genPt, Point.map_some]
  exact some_eq_some W rfl rfl

/-- `τ_0 = id`. -/
theorem trans_zero : trans W 0 = AlgHom.id F (Kf W) := by
  apply eq_of_map_genPt
  rw [map_trans_genPt, map_id_genPt, transPt]
  simp only [bc, map_zero, add_zero]

/-- **The composition law `τ_P ∘ τ_Q = τ_{P+Q}`**, i.e. `t_Q^* ∘ … `: it is the associativity of
the point group `E(F(E))`, through `Point.map` being a homomorphism fixing `E(F)`. -/
theorem trans_comp (P Q : (W⁄F).Point) : (trans W P).comp (trans W Q) = trans W (P + Q) := by
  apply eq_of_map_genPt
  rw [← Point.map_map, map_trans_genPt, transPt, map_add, map_trans_genPt, Point.map_baseChange,
    map_trans_genPt, transPt, transPt]
  simp only [bc, map_add, add_assoc]

theorem trans_trans (P Q : (W⁄F).Point) (f : Kf W) :
    trans W P (trans W Q f) = trans W (P + Q) f := by
  rw [← trans_comp]; rfl

/-- **The translation action** `E(F) → Aut_F(F(E))`, `P ↦ τ_P`. -/
def transAut : Multiplicative (W⁄F).Point →* (Kf W ≃ₐ[F] Kf W) where
  toFun P := AlgEquiv.ofAlgHom (trans W P.toAdd) (trans W (-P.toAdd))
    (by rw [trans_comp, add_neg_cancel, trans_zero])
    (by rw [trans_comp, neg_add_cancel, trans_zero])
  map_one' := by
    ext f
    change trans W 0 f = f
    rw [trans_zero]; rfl
  map_mul' P Q := by
    ext f
    change trans W (P.toAdd + Q.toAdd) f = trans W P.toAdd (trans W Q.toAdd f)
    rw [trans_trans]

theorem transAut_apply (P : (W⁄F).Point) (f : Kf W) :
    transAut W (Multiplicative.ofAdd P) f = trans W P f := rfl

end Trans


end RamanujanWeil.Arith.Deuring.Geom.G7.DGeom
