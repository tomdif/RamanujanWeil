import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Algebra.Module.ZMod

/-!
# A3-ord, G7 (algebra): Frobenius-equivariant isomorphisms of torsion groups

Tate's argument for "equal trace ⇒ isogenous" (`docs/ARITH_DEURING_G7.md`) glues `E` and `E'`
along a `π`-equivariant isomorphism `u_n : E[ℓⁿ] ≅ E'[ℓⁿ]`. This file provides `u_n` by pure
algebra, for a prime `ℓ` at which `f = X² − tX + q` has **no root**:

* `exists_prime_no_root`: if `t² < 4q` there is a prime `ℓ` with `a² − ta + q ≠ 0` for every
  `a ∈ 𝔽_ℓ`. (Proof: `J(t² − 4q | 4(4q − t²) − 1) = −1`, then a prime divisor.)
* `exists_conj_companion`: a `2 × 2` matrix `P` over `ℤ/ℓⁿ` with `P² − tP + q = 0` is conjugate
  to the companion matrix `C = [[0, −q], [1, t]]` (a cyclic vector exists because `P mod ℓ` is
  not scalar: a scalar `a` would be a root of `f mod ℓ`).
* `exists_equivariant_addEquiv`: two groups `M ≅ M' ≅ (ℤ/ℓⁿ)²` with endomorphisms `φ, φ'`
  satisfying `φ² − tφ + q = 0` are `φ`-equivariantly isomorphic.

No Tate module, trace or characteristic polynomial is used: only `π² − tπ + q = 0` on points
(G2) and `E[ℓⁿ] ≅ (ℤ/ℓⁿ)²` (Stacks).
-/

namespace RamanujanWeil.Arith.Deuring.Geom.G7

open Matrix

/-! ## A prime at which `X² − tX + q` has no root -/

/-- `J(−N | 4N − 1) = −1` for `N ≥ 1`. -/
theorem jacobiSym_neg_eq_neg_one (N : ℕ) (hN : 1 ≤ N) :
    jacobiSym (-(N : ℤ)) (4 * N - 1) = -1 := by
  set b : ℕ := 4 * N - 1 with hb
  have hbodd : Odd b := ⟨2 * N - 1, by omega⟩
  have hb4 : b % 4 = 3 := by omega
  -- `J(4 | b) = 1`
  have h4 : jacobiSym 4 b = 1 := by
    have : (4 : ℤ) = 2 ^ 2 := by norm_num
    rw [this]
    apply jacobiSym.sq_one'
    rw [Int.gcd_comm]
    have : Int.gcd (b : ℤ) 2 = Nat.gcd b 2 := rfl
    rw [this]
    exact Nat.coprime_two_right.mpr hbodd
  have hmod : (4 * -(N : ℤ)) % (b : ℤ) = (-1 : ℤ) % (b : ℤ) := by
    rw [Int.emod_eq_emod_iff_emod_sub_eq_zero]
    have : (4 * -(N : ℤ)) - (-1) = -(b : ℤ) := by
      rw [hb]; push_cast [Nat.cast_sub (by omega : 1 ≤ 4 * N)]; ring
    rw [this]; simp
  calc jacobiSym (-(N : ℤ)) b = jacobiSym 4 b * jacobiSym (-(N : ℤ)) b := by rw [h4, one_mul]
    _ = jacobiSym (4 * -(N : ℤ)) b := (jacobiSym.mul_left _ _ _).symm
    _ = jacobiSym (-1) b := jacobiSym.mod_left' hmod
    _ = -1 := by rw [jacobiSym.at_neg_one hbodd, ZMod.χ₄_nat_three_mod_four hb4]

/-- **A prime where `X² − tX + q` has no root.** If `t² < 4q`, some prime `ℓ` has
`a² − ta + q ≠ 0` for all `a : ZMod ℓ`. -/
theorem exists_prime_no_root (t q : ℤ) (h : t ^ 2 < 4 * q) :
    ∃ ℓ : ℕ, ℓ.Prime ∧ ∀ a : ZMod ℓ, a ^ 2 - (t : ZMod ℓ) * a + (q : ZMod ℓ) ≠ 0 := by
  set N : ℕ := (4 * q - t ^ 2).toNat with hNdef
  have hN : (N : ℤ) = 4 * q - t ^ 2 := Int.toNat_of_nonneg (by linarith)
  have hN1 : 1 ≤ N := by omega
  obtain ⟨ℓ, hℓ, hdvd, hJ⟩ :=
    jacobiSym.eq_neg_one_at_prime_divisor_of_eq_neg_one (jacobiSym_neg_eq_neg_one N hN1)
  refine ⟨ℓ, hℓ, fun a ha => ?_⟩
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

/-! ## Units of `ℤ/ℓⁿ⁺¹` -/

/-- In `ZMod (ℓ ^ (n+1))`, an element with nonzero image in `ZMod ℓ` is a unit. -/
theorem isUnit_of_castHom_ne_zero {ℓ : ℕ} (hℓ : ℓ.Prime) {n : ℕ} (x : ZMod (ℓ ^ (n + 1)))
    (hx : ZMod.castHom (dvd_pow_self ℓ n.succ_ne_zero) (ZMod ℓ) x ≠ 0) : IsUnit x := by
  have : NeZero (ℓ ^ (n + 1)) := ⟨pow_ne_zero _ hℓ.ne_zero⟩
  rw [← ZMod.natCast_zmod_val x, ZMod.isUnit_iff_coprime]
  apply Nat.Coprime.pow_right
  rw [Nat.coprime_comm, hℓ.coprime_iff_not_dvd]
  intro hd
  apply hx
  rw [← ZMod.natCast_zmod_val x, map_natCast, ZMod.natCast_eq_zero_iff]
  exact hd

/-! ## Cyclic vectors -/

variable {R : Type*} [CommRing R]

/-- The companion matrix `[[0, −q], [1, t]]` of `X² − tX + q`. -/
def companion (t q : R) : Matrix (Fin 2) (Fin 2) R := !![0, -q; 1, t]

/-- The matrix with columns `v` and `P v`. -/
def cycMat (P : Matrix (Fin 2) (Fin 2) R) (v : Fin 2 → R) : Matrix (Fin 2) (Fin 2) R :=
  !![v 0, (P *ᵥ v) 0; v 1, (P *ᵥ v) 1]

theorem entry_rel {P : Matrix (Fin 2) (Fin 2) R} {t q : R}
    (hP : ∀ w, P *ᵥ (P *ᵥ w) - t • (P *ᵥ w) + q • w = 0) :
    P 0 0 * P 0 0 + P 0 1 * P 1 0 - t * P 0 0 + q = 0 ∧
    P 0 0 * P 0 1 + P 0 1 * P 1 1 - t * P 0 1 = 0 ∧
    P 1 0 * P 0 0 + P 1 1 * P 1 0 - t * P 1 0 = 0 ∧
    P 1 0 * P 0 1 + P 1 1 * P 1 1 - t * P 1 1 + q = 0 := by
  have a := congrFun (hP (Pi.single 0 1)) 0
  have b := congrFun (hP (Pi.single 1 1)) 0
  have c := congrFun (hP (Pi.single 0 1)) 1
  have d := congrFun (hP (Pi.single 1 1)) 1
  simp [mulVec, dotProduct, Fin.sum_univ_two] at a b c d
  exact ⟨a, b, c, d⟩

/-- `P · [v | Pv] = [v | Pv] · C`. -/
theorem mul_cycMat {P : Matrix (Fin 2) (Fin 2) R} {t q : R}
    (hP : ∀ w, P *ᵥ (P *ᵥ w) - t • (P *ᵥ w) + q • w = 0) (v : Fin 2 → R) :
    P * cycMat P v = cycMat P v * companion t q := by
  obtain ⟨h00, h01, h10, h11⟩ := entry_rel hP
  refine Matrix.ext fun i j => ?_
  rw [Matrix.mul_apply, Matrix.mul_apply]
  fin_cases i <;> fin_cases j <;>
    simp [Fin.sum_univ_two, cycMat, companion, mulVec, dotProduct] <;>
    first
    | ring1
    | linear_combination v 0 * h00 + v 1 * h01
    | linear_combination v 0 * h10 + v 1 * h11

/-- **Cyclic vector.** Over `ℤ/ℓⁿ⁺¹`, if `P² − tP + q = 0` and `X² − tX + q` has no root mod
`ℓ`, then some `[v | Pv]` is invertible. -/
theorem exists_isUnit_det_cycMat {ℓ : ℕ} (hℓ : ℓ.Prime) {n : ℕ}
    {P : Matrix (Fin 2) (Fin 2) (ZMod (ℓ ^ (n + 1)))} {t q : ℤ}
    (hP : ∀ w, P *ᵥ (P *ᵥ w) - (t : ZMod (ℓ ^ (n + 1))) • (P *ᵥ w) +
      (q : ZMod (ℓ ^ (n + 1))) • w = 0)
    (hroot : ∀ a : ZMod ℓ, a ^ 2 - (t : ZMod ℓ) * a + (q : ZMod ℓ) ≠ 0) :
    ∃ v, IsUnit (cycMat P v).det := by
  set φ := ZMod.castHom (dvd_pow_self ℓ n.succ_ne_zero) (ZMod ℓ)
  obtain ⟨h00, -, -, -⟩ := entry_rel hP
  by_contra hne
  push Not at hne
  have key : ∀ v, φ (cycMat P v).det = 0 := fun v => by
    by_contra h; exact hne v (isUnit_of_castHom_ne_zero hℓ _ h)
  have k1 := key ![1, 0]
  have k2 := key ![0, 1]
  have k3 := key ![1, 1]
  simp [cycMat, Matrix.det_fin_two, mulVec, dotProduct, Fin.sum_univ_two] at k1 k2 k3
  -- `k1 : φ (P 1 0) = 0`, `k2 : φ (P 0 1) = 0`, `k3 : φ (P 1 0 + P 1 1 - (P 0 0 + P 0 1)) = 0`
  apply hroot (φ (P 0 0))
  have e := congrArg φ h00
  simp only [map_add, map_sub, map_mul, map_intCast, map_zero, Fin.isValue] at e
  have e1 : φ (P 1 0) = 0 := by simpa using k1
  have e2 : φ (P 0 1) = 0 := by simpa using k2
  rw [e1, e2] at e
  linear_combination e

/-- **Conjugation to the companion matrix.** -/
theorem exists_conj_companion {ℓ : ℕ} (hℓ : ℓ.Prime) {n : ℕ}
    {P : Matrix (Fin 2) (Fin 2) (ZMod (ℓ ^ (n + 1)))} {t q : ℤ}
    (hP : ∀ w, P *ᵥ (P *ᵥ w) - (t : ZMod (ℓ ^ (n + 1))) • (P *ᵥ w) +
      (q : ZMod (ℓ ^ (n + 1))) • w = 0)
    (hroot : ∀ a : ZMod ℓ, a ^ 2 - (t : ZMod ℓ) * a + (q : ZMod ℓ) ≠ 0) :
    ∃ g : Matrix (Fin 2) (Fin 2) (ZMod (ℓ ^ (n + 1))), IsUnit g.det ∧
      P * g = g * companion (t : ZMod (ℓ ^ (n + 1))) q := by
  obtain ⟨v, hv⟩ := exists_isUnit_det_cycMat hℓ hP hroot
  exact ⟨_, hv, mul_cycMat hP v⟩

/-! ## Equivariant isomorphisms of `(ℤ/ℓⁿ)²`-groups -/

/-- **Normal form.** Let `M ≅ (ℤ/ℓⁿ⁺¹)²` carry an additive endomorphism `φ` with
`φ² − tφ + q = 0`, and let `X² − tX + q` have no root mod `ℓ`. Then `M ≅ (ℤ/ℓⁿ⁺¹)²` with `φ`
acting by the companion matrix. -/
theorem exists_companion_addEquiv {ℓ : ℕ} (hℓ : ℓ.Prime) {n : ℕ} {M : Type*} [AddCommGroup M]
    (e : M ≃+ (Fin 2 → ZMod (ℓ ^ (n + 1)))) (φ : M →+ M) (t q : ℤ)
    (hφ : ∀ x, φ (φ x) - t • φ x + q • x = 0)
    (hroot : ∀ a : ZMod ℓ, a ^ 2 - (t : ZMod ℓ) * a + (q : ZMod ℓ) ≠ 0) :
    ∃ ψ : M ≃+ (Fin 2 → ZMod (ℓ ^ (n + 1))), ∀ x,
      ψ (φ x) = companion (t : ZMod (ℓ ^ (n + 1))) q *ᵥ ψ x := by
  -- the matrix of `φ` in the coordinates `e`
  let L : (Fin 2 → ZMod (ℓ ^ (n + 1))) →ₗ[ZMod (ℓ ^ (n + 1))] (Fin 2 → ZMod (ℓ ^ (n + 1))) :=
    ((e.toAddMonoidHom.comp φ).comp e.symm.toAddMonoidHom).toZModLinearMap (ℓ ^ (n + 1))
  have hL : ∀ w, L w = e (φ (e.symm w)) := fun _ => rfl
  set P := LinearMap.toMatrix' L
  have hPv : ∀ w, P *ᵥ w = e (φ (e.symm w)) := fun w => by
    rw [LinearMap.toMatrix'_mulVec, hL]
  have hP : ∀ w, P *ᵥ (P *ᵥ w) - (t : ZMod (ℓ ^ (n + 1))) • (P *ᵥ w) + (q : ZMod (ℓ ^ (n + 1))) • w = 0 := fun w => by
    rw [hPv, hPv, AddEquiv.symm_apply_apply, Int.cast_smul_eq_zsmul, Int.cast_smul_eq_zsmul]
    have := congrArg e (hφ (e.symm w))
    rw [map_add, map_sub, map_zsmul, map_zsmul, AddEquiv.apply_symm_apply, map_zero] at this
    exact this
  obtain ⟨g, hg, hPg⟩ := exists_conj_companion hℓ hP hroot
  -- `ψ x = g⁻¹ (e x)`
  have hgi : g * g⁻¹ = 1 := Matrix.mul_nonsing_inv g hg
  have hig : g⁻¹ * g = 1 := Matrix.nonsing_inv_mul g hg
  let ψ : M ≃+ (Fin 2 → ZMod (ℓ ^ (n + 1))) :=
    { toFun := fun x => g⁻¹ *ᵥ e x
      invFun := fun y => e.symm (g *ᵥ y)
      left_inv := fun x => by
        simp only [mulVec_mulVec, hgi, one_mulVec, AddEquiv.symm_apply_apply]
      right_inv := fun y => by
        change g⁻¹ *ᵥ e (e.symm (g *ᵥ y)) = y
        rw [AddEquiv.apply_symm_apply, Matrix.mulVec_mulVec, hig, Matrix.one_mulVec]
      map_add' := fun x y => by simp only [map_add, mulVec_add] }
  refine ⟨ψ, fun x => ?_⟩
  change g⁻¹ *ᵥ e (φ x) = companion (t : ZMod (ℓ ^ (n + 1))) q *ᵥ (g⁻¹ *ᵥ e x)
  have h1 : e (φ x) = P *ᵥ e x := by rw [hPv, AddEquiv.symm_apply_apply]
  have h2 : g⁻¹ * P = companion (t : ZMod (ℓ ^ (n + 1))) q * g⁻¹ := by
    calc g⁻¹ * P = g⁻¹ * P * (g * g⁻¹) := by rw [hgi, mul_one]
      _ = g⁻¹ * (P * g) * g⁻¹ := by simp only [Matrix.mul_assoc]
      _ = g⁻¹ * (g * companion (t : ZMod (ℓ ^ (n + 1))) q) * g⁻¹ := by rw [hPg]
      _ = companion (t : ZMod (ℓ ^ (n + 1))) q * g⁻¹ := by
        rw [← Matrix.mul_assoc, hig, Matrix.one_mul]
  rw [h1, mulVec_mulVec, h2, ← mulVec_mulVec]

/-- **Equivariant isomorphism.** Two groups `M, M' ≅ (ℤ/ℓⁿ⁺¹)²` with endomorphisms satisfying
`φ² − tφ + q = 0`, where `X² − tX + q` has no root mod `ℓ`, are `φ`-equivariantly isomorphic. -/
theorem exists_equivariant_addEquiv {ℓ : ℕ} (hℓ : ℓ.Prime) {n : ℕ} {M M' : Type*}
    [AddCommGroup M] [AddCommGroup M']
    (e : M ≃+ (Fin 2 → ZMod (ℓ ^ (n + 1)))) (e' : M' ≃+ (Fin 2 → ZMod (ℓ ^ (n + 1))))
    (φ : M →+ M) (φ' : M' →+ M') (t q : ℤ)
    (hφ : ∀ x, φ (φ x) - t • φ x + q • x = 0) (hφ' : ∀ x, φ' (φ' x) - t • φ' x + q • x = 0)
    (hroot : ∀ a : ZMod ℓ, a ^ 2 - (t : ZMod ℓ) * a + (q : ZMod ℓ) ≠ 0) :
    ∃ u : M ≃+ M', ∀ x, u (φ x) = φ' (u x) := by
  obtain ⟨ψ, hψ⟩ := exists_companion_addEquiv hℓ e φ t q hφ hroot
  obtain ⟨ψ', hψ'⟩ := exists_companion_addEquiv hℓ e' φ' t q hφ' hroot
  refine ⟨ψ.trans ψ'.symm, fun x => ?_⟩
  apply ψ'.injective
  simp only [AddEquiv.trans_apply, AddEquiv.apply_symm_apply, hψ, hψ']

end RamanujanWeil.Arith.Deuring.Geom.G7
