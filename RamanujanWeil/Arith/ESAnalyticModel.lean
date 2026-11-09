import RamanujanWeil.Arith.ESAnalyticBol
import RamanujanWeil.Arith.ESInput

/-!
# A2 / ES-P10–P11: the function-space model of `EichlerData`

* `E = ℍ → ℂ` (`ℍ = Hs` as a subtype of `ℂ`), with the weight `−10` slash action
  `(f|M)(z) = (cz + d)¹⁰ f((az + b)/(cz + d))` for `det M > 0` (and `0` otherwise): `isSlash_sl`.
* `ι P = (z ↦ Σⱼ Pⱼ zʲ)`: injective (`ι_inj`) and equivariant (`ι_equiv`, from `act_hom`).
* `Fh = F̃|ℍ`: `F̃|T = F̃` (`Fh_T`).
* `ρ` = the coefficients of the polynomial of `rhoc_poly`: `ι ρ = F̃ − F̃|S` (`ι_rho`) and
  `conj ρⱼ = (−1)ʲρⱼ` (`rho_conj`).
-/

set_option autoImplicit false

namespace RamanujanWeil.Arith.ES.Analytic

open Complex Filter Set Finset
open RamanujanWeil.Arith.ES RamanujanWeil.Arith.ES.M2
open scoped Real Topology Matrix

/-- the model space. -/
abbrev EH : Type := Hs → ℂ

/-- `cz + d`. -/
def jf (M : M2) (z : ℂ) : ℂ := (M.c : ℂ) * z + M.d

/-- `(az + b)/(cz + d)`. -/
noncomputable def mobC (M : M2) (z : ℂ) : ℂ := ((M.a : ℂ) * z + M.b) / jf M z

lemma jf_ne_zero {M : M2} (hM : 0 < M.det) {z : ℂ} (hz : 0 < z.im) : jf M z ≠ 0 := by
  intro h
  have him := congrArg Complex.im h
  have hre := congrArg Complex.re h
  simp [jf] at him hre
  rcases him with hc | hc
  · rw [hc] at hre; simp at hre
    have : M.det = 0 := by simp [det, hc, hre]
    omega
  · linarith

lemma mobC_im {M : M2} (z : ℂ) :
    (mobC M z).im = (M.det : ℝ) * z.im / normSq (jf M z) := by
  rw [mobC, div_im]
  simp only [jf, add_re, add_im, mul_re, mul_im, intCast_re, intCast_im, zero_mul, sub_zero,
    add_zero, det]
  push_cast
  field_simp
  ring

lemma mobC_mem {M : M2} (hM : 0 < M.det) {z : ℂ} (hz : z ∈ Hs) : mobC M z ∈ Hs := by
  show 0 < (mobC M z).im
  rw [mobC_im]
  have h1 : 0 < normSq (jf M z) := normSq_pos.mpr (jf_ne_zero hM hz)
  have h2 : (0 : ℝ) < M.det := by exact_mod_cast hM
  have h3 : 0 < z.im := hz
  positivity

lemma jf_mul (M N : M2) {z : ℂ} (hN : jf N z ≠ 0) : jf (M * N) z = jf M (mobC N z) * jf N z := by
  simp only [jf, mobC, mul_c, mul_d] at hN ⊢
  push_cast
  field_simp
  ring

lemma mobC_mul (M N : M2) {z : ℂ} (hN : jf N z ≠ 0) (hMN : jf M (mobC N z) ≠ 0) :
    mobC (M * N) z = mobC M (mobC N z) := by
  have e := jf_mul M N hN
  have hMN' : jf (M * N) z ≠ 0 := by rw [e]; exact mul_ne_zero hMN hN
  rw [mobC, mobC, e]
  simp only [mobC] at hMN ⊢
  rw [div_eq_div_iff (mul_ne_zero hMN hN) hMN]
  simp only [jf, mul_a, mul_b] at hN hMN ⊢
  push_cast
  field_simp
  ring

/-- the weight `−10` slash action on `ℍ → ℂ`. -/
noncomputable def slF (M : M2) (f : EH) (z : Hs) : ℂ :=
  if h : 0 < M.det then jf M z ^ 10 * f ⟨mobC M z, mobC_mem h z.2⟩ else 0

noncomputable def sl (M : M2) : EH →ₗ[ℂ] EH where
  toFun := slF M
  map_add' f g := by
    funext z; simp only [slF, Pi.add_apply]; split_ifs <;> ring
  map_smul' c f := by
    funext z; simp only [slF, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; split_ifs <;> ring

lemma sl_apply {M : M2} (hM : 0 < M.det) (f : EH) (z : Hs) :
    sl M f z = jf M z ^ 10 * f ⟨mobC M z, mobC_mem hM z.2⟩ := by
  show slF M f z = _
  rw [slF, dif_pos hM]

lemma mobC_one (z : ℂ) : mobC 1 z = z := by simp [mobC, jf]

lemma mobC_negOne (z : ℂ) : mobC (-1) z = z := by
  simp [mobC, jf]

theorem isSlash_sl : IsSlash sl where
  one := by
    ext f z
    rw [sl_apply (by decide)]
    simp only [LinearMap.id_apply]
    have : (⟨mobC 1 z, mobC_mem (by decide) z.2⟩ : Hs) = z := Subtype.ext (mobC_one z)
    rw [this]; simp [jf]
  negOne := by
    ext f z
    rw [sl_apply (by decide)]
    simp only [LinearMap.id_apply]
    have : (⟨mobC (-1) z, mobC_mem (by decide) z.2⟩ : Hs) = z := Subtype.ext (mobC_negOne z)
    rw [this]; simp [jf]; norm_num
  mul := by
    intro M N hM hN
    have hMN : 0 < (M * N).det := by rw [det_mul]; positivity
    ext f z
    simp only [LinearMap.comp_apply]
    rw [sl_apply hMN, sl_apply hN, sl_apply hM]
    have hNz := jf_ne_zero hN z.2
    have hMz := jf_ne_zero hM (mobC_mem hN z.2)
    have e : (⟨mobC (M * N) z, mobC_mem hMN z.2⟩ : Hs) =
        ⟨mobC M (mobC N z), mobC_mem hM (mobC_mem hN z.2)⟩ :=
      Subtype.ext (mobC_mul M N hNz hMz)
    rw [e, jf_mul M N hNz]
    ring

/-! ### Polynomials -/

/-- `P ↦ (z ↦ Σⱼ Pⱼ zʲ)`. -/
noncomputable def evP (P : Fin 11 → ℂ) (z : ℂ) : ℂ := ∑ j : Fin 11, P j * z ^ (j : ℕ)

noncomputable def ιH : (Fin 11 → ℂ) →ₗ[ℂ] EH where
  toFun P z := evP P z
  map_add' P Q := by funext z; simp [evP, add_mul, Finset.sum_add_distrib]
  map_smul' c P := by funext z; simp [evP, Finset.mul_sum, mul_assoc]

/-- the polynomial with coefficient vector `P`. -/
noncomputable def polP (P : Fin 11 → ℂ) : Polynomial ℂ :=
  ∑ j : Fin 11, Polynomial.C (P j) * Polynomial.X ^ (j : ℕ)

lemma polP_eval (P : Fin 11 → ℂ) (z : ℂ) : (polP P).eval z = evP P z := by
  simp [polP, evP, Polynomial.eval_finset_sum]

lemma polP_coeff (P : Fin 11 → ℂ) (j : Fin 11) : (polP P).coeff j = P j := by
  simp only [polP, Polynomial.finset_sum_coeff, Polynomial.coeff_C_mul_X_pow]
  rw [Finset.sum_eq_single j]
  · simp
  · intro k _ hk; rw [if_neg]; exact fun h => hk (Fin.ext h.symm)
  · simp

/-- a coefficient vector vanishing along an injective sequence is zero. -/
lemma eq_zero_of_evP (P : Fin 11 → ℂ) (s : ℕ → ℂ) (hs : Function.Injective s)
    (h : ∀ n, evP P (s n) = 0) : P = 0 := by
  have hp : polP P = 0 := by
    apply Polynomial.eq_zero_of_infinite_isRoot
    refine Set.infinite_of_injective_forall_mem hs fun n => ?_
    show (polP P).IsRoot (s n)
    rw [Polynomial.IsRoot, polP_eval, h n]
  funext j
  rw [← polP_coeff P j, hp]; simp

lemma injective_upper : Function.Injective fun n : ℕ => ((n : ℂ) + 1) * I := by
  intro m n h
  have := congrArg Complex.im h
  simp at this
  exact_mod_cast this

lemma upper_mem (n : ℕ) : ((n : ℂ) + 1) * I ∈ Hs := by
  show 0 < (((n : ℂ) + 1) * I).im
  simp; positivity

theorem ιH_inj : Function.Injective ιH := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro P hP
  refine eq_zero_of_evP P _ injective_upper fun n => ?_
  have := congrFun hP ⟨_, upper_mem n⟩
  simpa [ιH] using this

/-- `act_hom` over `ℂ`, at `y = 1`. -/
lemma act_hom_C (M : M2) (j : Fin 11) (x : ℂ) :
    ∑ i : Fin 11, ((act M j i : ℚ) : ℂ) * x ^ (i : ℕ) =
      ((M.a : ℂ) * x + M.b) ^ (j : ℕ) * ((M.c : ℂ) * x + M.d) ^ (10 - (j : ℕ)) := by
  set p : Polynomial ℚ := ∑ i : Fin 11, Polynomial.C (act M j i) * Polynomial.X ^ (i : ℕ) -
    (Polynomial.C (M.a : ℚ) * Polynomial.X + Polynomial.C (M.b : ℚ)) ^ (j : ℕ) *
      (Polynomial.C (M.c : ℚ) * Polynomial.X + Polynomial.C (M.d : ℚ)) ^ (10 - (j : ℕ)) with hp
  have h0 : p = 0 := by
    apply Polynomial.funext
    intro q
    have := act_hom M j q 1
    simp only [one_pow, mul_one] at this
    simp [hp, Polynomial.eval_finset_sum, this]
  have h1 := congrArg (Polynomial.aeval x) h0
  simp only [hp, map_sub, map_sum, map_mul, map_pow, map_add, Polynomial.aeval_C,
    Polynomial.aeval_X, map_zero] at h1
  rw [sub_eq_zero] at h1
  simpa using h1

theorem ιH_equiv (M : M2) (hM : 0 < M.det) (P : Fin 11 → ℂ) :
    ιH (P ᵥ* cmat M) = sl M (ιH P) := by
  funext z
  rw [sl_apply hM]
  show evP (P ᵥ* cmat M) z = jf M z ^ 10 * evP P (mobC M z)
  have hj := jf_ne_zero hM z.2
  simp only [evP, Matrix.vecMul, dotProduct, cmat, Matrix.map_apply, Rat.coe_castHom,
    Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  have h := act_hom_C M j z
  simp only [mul_assoc, ← Finset.mul_sum]
  rw [h, mobC]
  have hj10 : (j : ℕ) ≤ 10 := Nat.lt_succ_iff.mp j.isLt
  rw [div_pow, show jf M z ^ 10 = jf M z ^ (j : ℕ) * jf M z ^ (10 - (j : ℕ)) by
    rw [← pow_add]; congr 1; omega]
  simp only [jf] at hj ⊢
  have hj' : (z : ℂ) * M.c + M.d ≠ 0 := by rwa [mul_comm]
  field_simp

/-- `F̃` as an element of the model. -/
noncomputable def Fh : EH := fun z => Fc z

lemma mobC_T (z : ℂ) : mobC T z = z + 1 := by simp [mobC, jf, T]

theorem Fh_T : sl T Fh = Fh := by
  funext z
  rw [sl_apply (by decide)]
  simp only [Fh, mobC_T, Fc, G_add_one]
  simp [jf, T]

lemma mobC_S (z : ℂ) : mobC S z = -1 / z := by simp [mobC, jf, S]

/-! ### The period polynomial `ρ` -/

/-- the coefficient vector of the period polynomial. -/
noncomputable def rhoV : Fin 11 → ℂ := fun j => (Classical.choose rhoc_poly).coeff j

lemma evP_rhoV {z : ℂ} (hz : z ∈ Hs) : evP rhoV z = rhoc z := by
  obtain ⟨hdeg, heq⟩ := Classical.choose_spec rhoc_poly
  rw [heq hz]
  simp only [evP, rhoV]
  rw [Polynomial.eval_eq_sum_range' (n := 11) (by omega)]
  exact (Fin.sum_univ_eq_sum_range (fun i => (Classical.choose rhoc_poly).coeff i * z ^ i) 11)

theorem ιH_rho : ιH rhoV = Fh - sl S Fh := by
  funext z
  rw [Pi.sub_apply, sl_apply (by decide)]
  show evP rhoV z = Fc z - jf S z ^ 10 * Fc (mobC S z)
  rw [evP_rhoV z.2, mobC_S]
  simp [rhoc, jf, S]

lemma neg_conj_mem {z : ℂ} (hz : z ∈ Hs) : -(starRingEnd ℂ) z ∈ Hs := by
  show 0 < (-(starRingEnd ℂ) z).im
  simp only [neg_im, conj_im, neg_neg]; exact hz

lemma rhoc_conj {z : ℂ} : rhoc (-(starRingEnd ℂ) z) = (starRingEnd ℂ) (rhoc z) := by
  have e1 : (-(starRingEnd ℂ) z) ^ 10 = (starRingEnd ℂ) z ^ 10 := by ring
  have e2 : -1 / -(starRingEnd ℂ) z = -(starRingEnd ℂ) (-1 / z) := by
    simp only [map_div₀, map_neg, map_one]; ring
  simp only [rhoc, map_sub, map_mul, map_pow, Fc_conj, e1, e2]

theorem rho_conj (j : Fin 11) : (starRingEnd ℂ) (rhoV j) = (-1) ^ (j : ℕ) * rhoV j := by
  set Q : Fin 11 → ℂ := fun j => (-1) ^ (j : ℕ) * rhoV j - (starRingEnd ℂ) (rhoV j)
  have hQ : Q = 0 := by
    refine eq_zero_of_evP Q (fun n => -(((n : ℂ) + 1) * I)) ?_ fun n => ?_
    · intro m n h; exact injective_upper (neg_injective h)
    · set z : ℂ := ((n : ℂ) + 1) * I
      have hz : z ∈ Hs := upper_mem n
      have e1 := evP_rhoV (neg_conj_mem hz)
      rw [rhoc_conj, ← evP_rhoV hz] at e1
      have hzc : -(starRingEnd ℂ) z = z := by simp [z]
      have hzc' : -z = (starRingEnd ℂ) z := by linear_combination hzc
      simp only [evP, map_sum, map_mul, map_pow] at e1
      simp only [evP, Q, sub_mul, Finset.sum_sub_distrib]
      rw [sub_eq_zero]
      rw [hzc] at e1
      calc ∑ j : Fin 11, (-1) ^ (j : ℕ) * rhoV j * (-z) ^ (j : ℕ)
          = ∑ j : Fin 11, rhoV j * z ^ (j : ℕ) := by
            refine Finset.sum_congr rfl fun j _ => ?_
            have h1 : ((-1 : ℂ) ^ (j : ℕ)) * (-1) ^ (j : ℕ) = 1 := by rw [← mul_pow]; norm_num
            rw [neg_pow z]; linear_combination (rhoV j * z ^ (j : ℕ)) * h1
        _ = _ := e1
        _ = ∑ j : Fin 11, (starRingEnd ℂ) (rhoV j) * (-z) ^ (j : ℕ) := by
            rw [hzc']
  have := congrFun hQ j
  simp only [Q, Pi.zero_apply, sub_eq_zero] at this
  exact this.symm

end RamanujanWeil.Arith.ES.Analytic
