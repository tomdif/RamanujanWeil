import RamanujanWeil.Arith.DeuringG7Alg
import Mathlib.FieldTheory.Finite.Basic

/-!
# A3-ord, G7-fin (algebra): equivariant gluing isomorphisms with a prescribed determinant

`docs/ARITH_DEURING_G7FIN.md` §4. The polarization route to `QuotientFiniteness` (G7 doc §4,
F1/F2) needs the gluing isomorphisms `u_n : E[ℓⁿ⁺¹] ≅ E'[ℓⁿ⁺¹]` to be **anti-isometric** for the
Weil pairings, so that the graph `Γ_n` is maximal isotropic in `(E × E')[ℓⁿ⁺¹]` and the product
principal polarization `ℓⁿ⁺¹ · (λ_E × λ_{E'})` descends to a **principal** polarization of
`B_n = (E × E')/Γ_n`. In coordinates, anti-isometry is one condition `det u_n = c_n` on the
determinant, with `c_n` a unit fixed by the Weil pairings. This file shows by pure algebra that
**every unit determinant is attained by a `π`-equivariant isomorphism**:

* `exists_odd_prime_no_root`: the prime of `exists_prime_no_root` can be taken odd.
* `int_exists_sq_dvd` / `isSquare_of_isUnit_of_isSquare_castHom`: Hensel's lemma for square roots
  of units modulo `ℓⁿ⁺¹`, `ℓ` odd.
* `exists_normForm_eq`: if `X² − tX + q` has no root mod the odd prime `ℓ`, the norm form
  `a² + tab + qb²` takes every unit value modulo `ℓⁿ⁺¹` (norms from the unramified quadratic
  extension are surjective onto units).
* `exists_equivariant_addEquiv_det`: two groups `M, M' ≅ (ℤ/ℓⁿ⁺¹)²` with endomorphisms satisfying
  `φ² − tφ + q = 0` admit a `φ`-equivariant isomorphism whose matrix in **given** coordinates has
  **any prescribed unit determinant**. (The equivariant isomorphisms are `u₀ ∘ (a + bφ)`, with
  determinant `det u₀ · (a² + tab + qb²)`.)
-/

namespace RamanujanWeil.Arith.Deuring.Geom.G7.Fin

open Matrix Polynomial RamanujanWeil.Arith.Deuring.Geom.G7

/-! ## An odd prime with no root -/

/-- **An odd prime where `X² − tX + q` has no root** (as `exists_prime_no_root`, plus
`ℓ ≠ 2`: `ℓ` divides the odd number `4(4q − t²) − 1`). -/
theorem exists_odd_prime_no_root (t q : ℤ) (h : t ^ 2 < 4 * q) :
    ∃ ℓ : ℕ, ℓ.Prime ∧ ℓ ≠ 2 ∧ ∀ a : ZMod ℓ, a ^ 2 - (t : ZMod ℓ) * a + (q : ZMod ℓ) ≠ 0 := by
  set N : ℕ := (4 * q - t ^ 2).toNat with hNdef
  have hN : (N : ℤ) = 4 * q - t ^ 2 := Int.toNat_of_nonneg (by linarith)
  have hN1 : 1 ≤ N := by omega
  obtain ⟨ℓ, hℓ, hdvd, hJ⟩ :=
    jacobiSym.eq_neg_one_at_prime_divisor_of_eq_neg_one (jacobiSym_neg_eq_neg_one N hN1)
  refine ⟨ℓ, hℓ, ?_, fun a ha => ?_⟩
  · rintro rfl
    obtain ⟨k, hk⟩ := hdvd
    omega
  have := Fact.mk hℓ
  have hL : legendreSym ℓ (-(N : ℤ)) = -1 := by
    rw [jacobiSym.legendreSym.to_jacobiSym]; exact hJ
  rw [legendreSym.eq_neg_one_iff] at hL
  apply hL
  refine ⟨2 * a - t, ?_⟩
  have : ((-(N : ℤ) : ℤ) : ZMod ℓ) = (t : ZMod ℓ) ^ 2 - 4 * q := by
    rw [show (-(N : ℤ)) = t ^ 2 - 4 * q by rw [hN]; ring]; push_cast; ring
  rw [this]
  linear_combination (-4 : ZMod ℓ) * ha

/-! ## Hensel's lemma for square roots of units -/

/-- **Hensel for squares over `ℤ`.** If `ℓ` is an odd prime, `ℓ ∤ a` and `x₀² ≡ a (mod ℓ)`, then
`a` is a square modulo every power `ℓᵏ⁺¹`. -/
theorem int_exists_sq_dvd {ℓ : ℕ} (hℓ : ℓ.Prime) (hodd : ℓ ≠ 2) {a x₀ : ℤ}
    (ha : ¬ (ℓ : ℤ) ∣ a) (hx₀ : (ℓ : ℤ) ∣ x₀ ^ 2 - a) :
    ∀ k : ℕ, ∃ x : ℤ, (ℓ : ℤ) ^ (k + 1) ∣ x ^ 2 - a := by
  have hℓZ : Prime (ℓ : ℤ) := Nat.prime_iff_prime_int.mp hℓ
  intro k
  induction k with
  | zero => exact ⟨x₀, by simpa using hx₀⟩
  | succ k ih =>
    obtain ⟨x, d, hd⟩ := ih
    -- `ℓ ∤ 2x`
    have hx : ¬ (ℓ : ℤ) ∣ 2 * x := by
      intro h2
      rcases hℓZ.dvd_or_dvd h2 with h2 | h2
      · have : (ℓ : ℤ) ∣ 2 := h2
        have : ℓ ∣ 2 := by exact_mod_cast this
        exact hodd ((Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_two).1 this)
      · apply ha
        have h1 : (ℓ : ℤ) ∣ x ^ 2 := dvd_pow h2 two_ne_zero
        have h3 : (ℓ : ℤ) ∣ x ^ 2 - a := by
          rw [hd]; exact Dvd.dvd.mul_right (dvd_pow_self _ (Nat.succ_ne_zero k)) _
        have := dvd_sub h1 h3
        simpa using this
    have hcop : IsCoprime (2 * x) (ℓ : ℤ) :=
      ((Irreducible.coprime_iff_not_dvd hℓZ.irreducible).2 hx).symm
    obtain ⟨α, β, hαβ⟩ := hcop
    refine ⟨x + (ℓ : ℤ) ^ (k + 1) * (-d * α), d * β + (ℓ : ℤ) ^ k * (d * α) ^ 2, ?_⟩
    have hp1 : (ℓ : ℤ) ^ (k + 1 + 1) = (ℓ : ℤ) ^ (k + 1) * ℓ := pow_succ _ _
    have hp2 : (ℓ : ℤ) ^ (k + 1) = (ℓ : ℤ) ^ k * ℓ := pow_succ _ _
    rw [hp1]
    linear_combination hd + (-(ℓ : ℤ) ^ (k + 1) * d) * hαβ + (ℓ : ℤ) ^ (k + 1) * (d * α) ^ 2 * hp2

/-- `castHom : ZMod (ℓⁿ⁺¹) → ZMod ℓ`. -/
noncomputable abbrev red (ℓ n : ℕ) : ZMod (ℓ ^ (n + 1)) →+* ZMod ℓ :=
  ZMod.castHom (dvd_pow_self ℓ n.succ_ne_zero) (ZMod ℓ)

theorem red_intCast (ℓ n : ℕ) (k : ℤ) : red ℓ n (k : ZMod (ℓ ^ (n + 1))) = (k : ZMod ℓ) :=
  map_intCast _ k

/-- Every element of `ZMod (ℓⁿ⁺¹)` is the cast of an integer. -/
theorem exists_intCast_eq {N : ℕ} [NeZero N] (x : ZMod N) : ∃ k : ℤ, (k : ZMod N) = x :=
  ⟨(x.val : ℤ), by rw [Int.cast_natCast, ZMod.natCast_zmod_val]⟩

/-- **Hensel for units of `ℤ/ℓⁿ⁺¹`.** A unit whose reduction mod `ℓ` is a square is a square
(`ℓ` odd). -/
theorem isSquare_of_isUnit_of_isSquare_red {ℓ : ℕ} (hℓ : ℓ.Prime) (hodd : ℓ ≠ 2) {n : ℕ}
    (u : ZMod (ℓ ^ (n + 1))) (hu : IsUnit u) (hs : IsSquare (red ℓ n u)) : IsSquare u := by
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have : NeZero (ℓ ^ (n + 1)) := ⟨pow_ne_zero _ hℓ.ne_zero⟩
  obtain ⟨U, rfl⟩ := exists_intCast_eq u
  obtain ⟨s, hs⟩ := hs
  obtain ⟨x₀, rfl⟩ := exists_intCast_eq s
  rw [red_intCast] at hs
  have hU : ¬ (ℓ : ℤ) ∣ U := by
    intro h
    have h0 : (U : ZMod ℓ) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd U ℓ).2 h
    have hu' := hu.map (red ℓ n)
    rw [red_intCast, h0] at hu'
    exact not_isUnit_zero hu'
  have hx₀ : (ℓ : ℤ) ∣ x₀ ^ 2 - U := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]; push_cast; rw [hs]; ring
  obtain ⟨x, hx⟩ := int_exists_sq_dvd hℓ hodd hU hx₀ n
  refine ⟨(x : ZMod (ℓ ^ (n + 1))), ?_⟩
  have : ((x ^ 2 - U : ℤ) : ZMod (ℓ ^ (n + 1))) = 0 := by
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]; exact_mod_cast hx
  push_cast at this
  linear_combination -this

/-! ## Surjectivity of the norm form onto units -/

/-- `t² − 4q` is not a square mod `ℓ` when `X² − tX + q` has no root (`ℓ` odd). -/
theorem disc_not_square {ℓ : ℕ} [Fact ℓ.Prime] (hodd : ℓ ≠ 2) {t q : ℤ}
    (hroot : ∀ a : ZMod ℓ, a ^ 2 - (t : ZMod ℓ) * a + (q : ZMod ℓ) ≠ 0) (s : ZMod ℓ) :
    s ^ 2 ≠ (t : ZMod ℓ) ^ 2 - 4 * q := by
  intro hs
  have h2 : (2 : ZMod ℓ) ≠ 0 := by
    intro h
    have : ((2 : ℕ) : ZMod ℓ) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at this
    exact hodd ((Nat.prime_dvd_prime_iff_eq (Fact.out) Nat.prime_two).1 this)
  apply hroot ((t + s) / 2)
  field_simp
  linear_combination hs

/-- The two cases of `X² − D Y² = 4c` modulo `ℓⁿ⁺¹`. -/
theorem exists_sq_sub_disc_mul_sq {ℓ : ℕ} (hℓ : ℓ.Prime) (hodd : ℓ ≠ 2) {n : ℕ} {t q : ℤ}
    (hroot : ∀ a : ZMod ℓ, a ^ 2 - (t : ZMod ℓ) * a + (q : ZMod ℓ) ≠ 0)
    (c : ZMod (ℓ ^ (n + 1))) (hc : IsUnit c) :
    ∃ X Y : ZMod (ℓ ^ (n + 1)), X * X - ((t : ZMod (ℓ ^ (n + 1))) ^ 2 - 4 * q) * (Y * Y) = 4 * c := by
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have : NeZero (ℓ ^ (n + 1)) := ⟨pow_ne_zero _ hℓ.ne_zero⟩
  set D₀ : ZMod ℓ := (t : ZMod ℓ) ^ 2 - 4 * q with hD₀
  set c₀ := red ℓ n c with hc₀
  have hc₀0 : c₀ ≠ 0 := fun h => by
    have := hc.map (red ℓ n); rw [← hc₀, h] at this; exact not_isUnit_zero this
  have h2 : (2 : ZMod ℓ) ≠ 0 := by
    intro h
    have : ((2 : ℕ) : ZMod ℓ) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at this
    exact hodd ((Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_two).1 this)
  have hD0 : D₀ ≠ 0 := fun h => disc_not_square hodd hroot 0 (by rw [← hD₀, h]; ring)
  -- a solution mod `ℓ`
  obtain ⟨X₀, Y₀, h₀⟩ := FiniteField.exists_root_sum_quadratic (R := ZMod ℓ)
    (f := Polynomial.X ^ 2) (g := Polynomial.C (-D₀) * Polynomial.X ^ 2 - Polynomial.C (4 * c₀))
    (by rw [Polynomial.degree_X_pow]; rfl)
    (by
      rw [Polynomial.degree_sub_eq_left_of_degree_lt] <;>
        rw [Polynomial.degree_C_mul_X_pow 2 (neg_ne_zero.2 hD0)]
      · rfl
      · exact lt_of_le_of_lt Polynomial.degree_C_le (by decide))
    (by rw [ZMod.card]; exact hℓ.eq_two_or_odd.resolve_left hodd)
  simp only [Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_sub, Polynomial.eval_mul,
    Polynomial.eval_C] at h₀
  -- reduction facts
  have hredD : red ℓ n ((t : ZMod (ℓ ^ (n + 1))) ^ 2 - 4 * q) = D₀ := by
    simp only [map_sub, map_pow, map_mul, map_intCast, map_ofNat, D₀]
  have hunit : ∀ x : ZMod (ℓ ^ (n + 1)), red ℓ n x ≠ 0 → IsUnit x := fun x hx =>
    isUnit_of_castHom_ne_zero hℓ x hx
  by_cases hX₀ : X₀ = 0
  · -- `D Y₀² = −4c₀`: solve `D Y² = −4c` and take `X = 0`
    subst hX₀
    have hDu : IsUnit ((t : ZMod (ℓ ^ (n + 1))) ^ 2 - 4 * q) := hunit _ (by rw [hredD]; exact hD0)
    obtain ⟨Di, hDi⟩ := hDu.exists_right_inv
    set v : ZMod (ℓ ^ (n + 1)) := -4 * c * Di
    have hv : red ℓ n v = Y₀ ^ 2 := by
      have hDi' : D₀ * red ℓ n Di = 1 := by rw [← hredD, ← map_mul, hDi, map_one]
      simp only [v, map_mul, map_neg, map_ofNat, ← hc₀]
      have : -4 * c₀ = D₀ * Y₀ ^ 2 := by linear_combination h₀
      rw [this]; linear_combination Y₀ ^ 2 * hDi'
    have hvu : IsUnit v := hunit _ (by
      rw [hv]
      intro h
      have hY : Y₀ = 0 := pow_eq_zero_iff (two_ne_zero) |>.1 h
      apply hc₀0
      have h4 : (4 : ZMod ℓ) ≠ 0 := by
        have : (4 : ZMod ℓ) = 2 * 2 := by norm_num
        rw [this]; exact mul_ne_zero h2 h2
      subst hY
      have : 4 * c₀ = 0 := by linear_combination -h₀
      exact (mul_eq_zero.1 this).resolve_left h4)
    obtain ⟨Y, hY⟩ := isSquare_of_isUnit_of_isSquare_red hℓ hodd v hvu ⟨Y₀, by rw [hv]; ring⟩
    refine ⟨0, Y, ?_⟩
    rw [← hY]
    simp only [v]
    linear_combination (4 * c) * hDi
  · -- lift `Y₀`, solve for `X`
    set Y : ZMod (ℓ ^ (n + 1)) := ((Y₀.val : ℤ) : ZMod (ℓ ^ (n + 1)))
    have hYr : red ℓ n Y = Y₀ := by
      show red ℓ n (((Y₀.val : ℤ)) : ZMod (ℓ ^ (n + 1))) = Y₀
      rw [red_intCast, Int.cast_natCast, ZMod.natCast_zmod_val]
    set w : ZMod (ℓ ^ (n + 1)) := 4 * c + ((t : ZMod (ℓ ^ (n + 1))) ^ 2 - 4 * q) * (Y * Y)
    have hw : red ℓ n w = X₀ ^ 2 := by
      simp only [w, map_add, map_mul, map_ofNat, ← hc₀, hredD, hYr]
      linear_combination -h₀
    have hwu : IsUnit w := hunit _ (by rw [hw]; exact pow_ne_zero 2 hX₀)
    obtain ⟨X, hX⟩ := isSquare_of_isUnit_of_isSquare_red hℓ hodd w hwu ⟨X₀, by rw [hw]; ring⟩
    refine ⟨X, Y, ?_⟩
    rw [← hX]
    simp only [w]
    ring

/-- **Norms are surjective onto units.** If `X² − tX + q` has no root modulo the odd prime `ℓ`,
then every unit `c` of `ℤ/ℓⁿ⁺¹` is `a² + tab + qb²` for some `a, b`. -/
theorem exists_normForm_eq {ℓ : ℕ} (hℓ : ℓ.Prime) (hodd : ℓ ≠ 2) {n : ℕ} {t q : ℤ}
    (hroot : ∀ a : ZMod ℓ, a ^ 2 - (t : ZMod ℓ) * a + (q : ZMod ℓ) ≠ 0)
    (c : ZMod (ℓ ^ (n + 1))) (hc : IsUnit c) :
    ∃ a b : ZMod (ℓ ^ (n + 1)), a ^ 2 + (t : ZMod (ℓ ^ (n + 1))) * a * b + q * b ^ 2 = c := by
  obtain ⟨X, Y, hXY⟩ := exists_sq_sub_disc_mul_sq hℓ hodd hroot c hc
  have h2 : IsUnit (2 : ZMod (ℓ ^ (n + 1))) := isUnit_of_castHom_ne_zero hℓ _ (by
    rw [map_ofNat]
    intro h
    have : ((2 : ℕ) : ZMod ℓ) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at this
    exact hodd ((Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_two).1 this))
  obtain ⟨h, hh⟩ := h2.exists_right_inv
  refine ⟨(X - t * Y) * h, Y, ?_⟩
  linear_combination h ^ 2 * hXY +
    ((2 * h + 1) * (c - q * Y ^ 2) - h * t * Y * (X - t * Y)) * hh

/-! ## Equivariant isomorphisms with prescribed determinant -/

section Det

variable {N : ℕ}

/-- The matrix of an additive endomorphism of `(ℤ/N)²`. -/
noncomputable def mat (σ : (Fin 2 → ZMod N) →+ (Fin 2 → ZMod N)) : Matrix (Fin 2) (Fin 2) (ZMod N) :=
  LinearMap.toMatrix' (σ.toZModLinearMap N)

theorem mat_comp (σ τ : (Fin 2 → ZMod N) →+ (Fin 2 → ZMod N)) :
    mat (σ.comp τ) = mat σ * mat τ := by
  unfold mat
  rw [← LinearMap.toMatrix'_comp]
  rfl

theorem mat_id : mat (AddMonoidHom.id (Fin 2 → ZMod N)) = 1 := by
  unfold mat
  rw [← LinearMap.toMatrix'_id]
  rfl

theorem mat_mulVec (Z : Matrix (Fin 2) (Fin 2) (ZMod N)) :
    mat (Z.mulVecLin.toAddMonoidHom) = Z := by
  unfold mat
  rw [show (Z.mulVecLin.toAddMonoidHom).toZModLinearMap N = Z.mulVecLin from rfl]
  exact LinearMap.toMatrix'_toLin' Z

theorem isUnit_det_mat (σ : (Fin 2 → ZMod N) ≃+ (Fin 2 → ZMod N)) :
    IsUnit (mat σ.toAddMonoidHom).det := by
  have h : mat σ.toAddMonoidHom * mat σ.symm.toAddMonoidHom = 1 := by
    rw [← mat_comp, ← mat_id]
    congr 1
    ext x : 1
    simp
  exact isUnit_iff_exists_inv.2 ⟨(mat σ.symm.toAddMonoidHom).det, (by rw [← Matrix.det_mul, h, Matrix.det_one])⟩

/-- The matrix of `u : M ≃+ M'` in coordinates `e : M ≅ (ℤ/N)²`, `e' : M' ≅ (ℤ/N)²`. -/
noncomputable def coordMat {M M' : Type*} [AddCommGroup M] [AddCommGroup M']
    (e : M ≃+ (Fin 2 → ZMod N)) (e' : M' ≃+ (Fin 2 → ZMod N)) (u : M ≃+ M') :
    Matrix (Fin 2) (Fin 2) (ZMod N) :=
  mat ((e'.toAddMonoidHom.comp u.toAddMonoidHom).comp e.symm.toAddMonoidHom)

end Det

/-- **Equivariant isomorphisms with any prescribed unit determinant.** Let `M, M' ≅ (ℤ/ℓⁿ⁺¹)²`
(coordinates `e`, `e'`) carry endomorphisms `φ, φ'` with `φ² − tφ + q = 0`, and let
`X² − tX + q` have no root modulo the odd prime `ℓ`. For every unit `c` there is a
`φ`-equivariant isomorphism `u : M ≅ M'` with `det (e' ∘ u ∘ e⁻¹) = c`. -/
theorem exists_equivariant_addEquiv_det {ℓ : ℕ} (hℓ : ℓ.Prime) (hodd : ℓ ≠ 2) {n : ℕ}
    {M M' : Type*} [AddCommGroup M] [AddCommGroup M']
    (e : M ≃+ (Fin 2 → ZMod (ℓ ^ (n + 1)))) (e' : M' ≃+ (Fin 2 → ZMod (ℓ ^ (n + 1))))
    (φ : M →+ M) (φ' : M' →+ M') (t q : ℤ)
    (hφ : ∀ x, φ (φ x) - t • φ x + q • x = 0) (hφ' : ∀ x, φ' (φ' x) - t • φ' x + q • x = 0)
    (hroot : ∀ a : ZMod ℓ, a ^ 2 - (t : ZMod ℓ) * a + (q : ZMod ℓ) ≠ 0)
    (c : ZMod (ℓ ^ (n + 1))) (hc : IsUnit c) :
    ∃ u : M ≃+ M', (∀ x, u (φ x) = φ' (u x)) ∧ (coordMat e e' u).det = c := by
  obtain ⟨ψ, hψ⟩ := exists_companion_addEquiv hℓ e φ t q hφ hroot
  obtain ⟨ψ', hψ'⟩ := exists_companion_addEquiv hℓ e' φ' t q hφ' hroot
  set C := companion (t : (ZMod (ℓ ^ (n + 1)))) q
  -- the coordinate changes
  set σ₁ : (Fin 2 → (ZMod (ℓ ^ (n + 1)))) ≃+ (Fin 2 → (ZMod (ℓ ^ (n + 1)))) := ψ'.symm.trans e'
  set σ₂ : (Fin 2 → (ZMod (ℓ ^ (n + 1)))) ≃+ (Fin 2 → (ZMod (ℓ ^ (n + 1)))) := e.symm.trans ψ
  obtain ⟨d₁, hd₁⟩ := isUnit_det_mat σ₁
  obtain ⟨d₂, hd₂⟩ := isUnit_det_mat σ₂
  obtain ⟨cu, rfl⟩ := hc
  -- choose `Z = a + bC` with `det Z = c / (d₁ d₂)`
  obtain ⟨a, b, hab⟩ := exists_normForm_eq hℓ hodd hroot ((cu * d₁⁻¹ * d₂⁻¹ : (ZMod (ℓ ^ (n + 1)))ˣ) : (ZMod (ℓ ^ (n + 1))))
    (Units.isUnit _)
  set Z : Matrix (Fin 2) (Fin 2) (ZMod (ℓ ^ (n + 1))) := a • 1 + b • C
  have hZdet : Z.det = ((cu * d₁⁻¹ * d₂⁻¹ : (ZMod (ℓ ^ (n + 1)))ˣ) : (ZMod (ℓ ^ (n + 1)))) := by
    rw [← hab, Matrix.det_fin_two]
    simp [Z, C, companion]
    ring
  have hZu : IsUnit Z.det := by rw [hZdet]; exact Units.isUnit _
  have hZC : Z * C = C * Z := by
    simp only [Z, Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.one_mul, Matrix.mul_one]
  have hZi : Z * Z⁻¹ = 1 := Matrix.mul_nonsing_inv Z hZu
  have hiZ : Z⁻¹ * Z = 1 := Matrix.nonsing_inv_mul Z hZu
  let σZ : (Fin 2 → (ZMod (ℓ ^ (n + 1)))) ≃+ (Fin 2 → (ZMod (ℓ ^ (n + 1)))) :=
    { toFun := fun v => Z *ᵥ v
      invFun := fun v => Z⁻¹ *ᵥ v
      left_inv := fun v => by simp only [mulVec_mulVec, hiZ, one_mulVec]
      right_inv := fun v => by simp only [mulVec_mulVec, hZi, one_mulVec]
      map_add' := fun v w => mulVec_add Z v w }
  refine ⟨ψ.trans (σZ.trans ψ'.symm), fun x => ?_, ?_⟩
  · apply ψ'.injective
    simp only [AddEquiv.trans_apply, AddEquiv.apply_symm_apply, hψ', hψ]
    change Z *ᵥ (C *ᵥ ψ x) = C *ᵥ (Z *ᵥ ψ x)
    rw [mulVec_mulVec, mulVec_mulVec, hZC]
  · have hsplit : (e'.toAddMonoidHom.comp (ψ.trans (σZ.trans ψ'.symm)).toAddMonoidHom).comp
        e.symm.toAddMonoidHom =
        (σ₁.toAddMonoidHom.comp (Z.mulVecLin.toAddMonoidHom)).comp σ₂.toAddMonoidHom := by
      ext v : 1
      rfl
    rw [coordMat, hsplit, mat_comp, mat_comp, mat_mulVec, Matrix.det_mul, Matrix.det_mul,
      ← hd₁, ← hd₂, hZdet]
    simp only [Units.val_mul]
    rw [show (d₁ : (ZMod (ℓ ^ (n + 1)))) * ((cu : (ZMod (ℓ ^ (n + 1)))) * ((d₁⁻¹ : (ZMod (ℓ ^ (n + 1)))ˣ) : (ZMod (ℓ ^ (n + 1)))) * ((d₂⁻¹ : (ZMod (ℓ ^ (n + 1)))ˣ) : (ZMod (ℓ ^ (n + 1))))) * (d₂ : (ZMod (ℓ ^ (n + 1)))) =
        (cu : (ZMod (ℓ ^ (n + 1)))) * ((d₁ : (ZMod (ℓ ^ (n + 1)))) * ((d₁⁻¹ : (ZMod (ℓ ^ (n + 1)))ˣ) : (ZMod (ℓ ^ (n + 1))))) * ((d₂ : (ZMod (ℓ ^ (n + 1)))) * ((d₂⁻¹ : (ZMod (ℓ ^ (n + 1)))ˣ) : (ZMod (ℓ ^ (n + 1))))) by ring]
    simp

end RamanujanWeil.Arith.Deuring.Geom.G7.Fin
