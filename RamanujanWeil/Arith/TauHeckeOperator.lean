import RamanujanWeil.Arith.TauHeckeCore

/-!
# Hecke `T_p`, part 2: the operator on level-one cusp forms and its q-expansion action

Ported from `~/RamanujanTau/RamanujanTau/HeckeForm.lean` (all of it) and the first half of
`~/RamanujanTau/RamanujanTau/HeckeQExp.lean` (`hasSum_hecke`, `qExpansion_hecke`, `heckeLin`).

* `heckeCusp p : CuspForm 𝒮ℒ k → CuspForm 𝒮ℒ k` (modularity via `slash_action_generators_SL2Z`,
  holomorphy, vanishing at `i∞`), packaged ℂ-linearly as `heckeLin p`;
* `qExpansion_hecke`: `(T_p f)_m = f_{pm} + p^{k−1}·[p ∣ m]·f_{m/p}`.
-/

set_option autoImplicit false

namespace RamanujanWeil.ArithPlan.TauHecke
open Complex UpperHalfPlane ModularForm Filter Finset
open scoped MatrixGroups ModularForm Topology Manifold

variable {k : ℤ}

/-- a level-one cusp form, read on `ℂ`, satisfies `IsModular`. -/
lemma isModular_of (f : CuspForm 𝒮ℒ k) : IsModular k (f ∘ ofComplex) := by
  intro a b c d hdet z hz
  let A : SL(2, ℤ) := ⟨!![a, b; c, d], by simp [Matrix.det_fin_two]; linarith⟩
  let τ : ℍ := ⟨z, hz⟩
  have hinv : (f : ℍ → ℂ) ∣[k] A = f := by
    have := SlashInvariantFormClass.slash_action_eq f (A : GL (Fin 2) ℝ) ⟨A, rfl⟩
    simpa [ModularForm.SL_slash] using this
  have h := congrFun hinv τ
  rw [SL_slash_apply] at h
  have hden : denom A τ = c * z + d := by
    change ((c : ℝ) : ℂ) * z + ((d : ℝ) : ℂ) = _
    push_cast; ring
  have hcoe : ((A • τ : ℍ) : ℂ) = (a * z + b) / (c * z + d) := by
    rw [coe_specialLinearGroup_apply]; simp [A, τ]
  have hne : (c : ℂ) * z + d ≠ 0 := hden ▸ denom_ne_zero A τ
  simp only [Function.comp_apply]
  rw [← hcoe, ofComplex_apply, show ofComplex z = τ from ofComplex_apply_of_im_pos hz]
  rw [hden] at h
  rw [← h, mul_left_comm, ← zpow_add₀ hne, add_neg_cancel, zpow_zero, mul_one]

variable (p : ℕ) [hp : Fact p.Prime]

/-- `T_p f` as a function on `ℍ`. -/
noncomputable def heckeH (f : CuspForm 𝒮ℒ k) (τ : ℍ) : ℂ := heckeFun k (f ∘ ofComplex) p τ

lemma heckeH_S (f : CuspForm 𝒮ℒ k) : heckeH p f ∣[k] ModularGroup.S = heckeH p f := by
  funext τ
  rw [SL_slash_apply, ModularGroup.denom_S, heckeH, heckeH, modular_S_smul]
  have hz : 0 < (τ : ℂ).im := τ.im_pos
  have e : ((mk (-(τ : ℂ))⁻¹ τ.im_inv_neg_coe_pos : ℍ) : ℂ) = -1 / (τ : ℂ) := by
    simp [neg_div, inv_neg]
  rw [e, heckeFun_S (isModular_of f) hz]
  have hne : (τ : ℂ) ≠ 0 := ne_zero τ
  rw [mul_comm, ← mul_assoc, ← zpow_add₀ hne, neg_add_cancel, zpow_zero, one_mul]

lemma heckeH_T (f : CuspForm 𝒮ℒ k) : heckeH p f ∣[k] ModularGroup.T = heckeH p f := by
  funext τ
  rw [SL_slash_apply, heckeH, heckeH, modular_T_smul]
  have hden : denom ModularGroup.T τ = 1 := by
    change (((0 : ℤ) : ℝ) : ℂ) * (τ : ℂ) + (((1 : ℤ) : ℝ) : ℂ) = 1
    push_cast; ring
  rw [hden, one_zpow, mul_one, UpperHalfPlane.coe_vadd, ofReal_one, add_comm]
  exact heckeFun_add_one (isModular_of f) hp.out.pos τ.im_pos

lemma differentiableOn_g (f : CuspForm 𝒮ℒ k) :
    DifferentiableOn ℂ (f ∘ ofComplex) {z : ℂ | 0 < z.im} :=
  UpperHalfPlane.mdifferentiable_iff.mp (ModularFormClass.holo f)

lemma heckeH_holo (f : CuspForm 𝒮ℒ k) : MDiff (heckeH p f) := by
  rw [UpperHalfPlane.mdifferentiable_iff]
  have hpos := hp.out.pos
  have hd : DifferentiableOn ℂ (heckeFun k (f ∘ ofComplex) p) {z : ℂ | 0 < z.im} := by
    unfold heckeFun
    refine (DifferentiableOn.const_mul ?_ _).add (DifferentiableOn.const_mul ?_ _)
    · exact (differentiableOn_g f).comp (by fun_prop) fun z hz => im_nat_mul hz hpos
    · refine DifferentiableOn.fun_sum fun j _ => ?_
      exact (differentiableOn_g f).comp (by fun_prop) fun z hz => im_div_nat hz hpos
  refine hd.congr fun z hz => ?_
  simp [heckeH, ofComplex_apply_of_im_pos (show 0 < z.im from hz)]

/-- maps `ℍ → ℍ` given by a complex function preserving the upper half plane and sending `im → ∞`. -/
lemma tendsto_comp {φ : ℂ → ℂ} (hφ : ∀ z : ℂ, 0 < z.im → 0 < (φ z).im) (c : ℝ) (hc : 0 < c)
    (him : ∀ z : ℂ, 0 < z.im → (φ z).im = c * z.im) :
    Tendsto (fun τ : ℍ => ofComplex (φ τ)) atImInfty atImInfty := by
  rw [atImInfty, tendsto_comap_iff]
  have : (UpperHalfPlane.im ∘ fun τ : ℍ => ofComplex (φ τ)) = fun τ => c * τ.im := by
    funext τ
    simp only [Function.comp_apply]
    rw [ofComplex_apply_of_im_pos (hφ _ τ.im_pos)]
    exact him _ τ.im_pos
  rw [this]
  exact (tendsto_comap.const_mul_atTop hc)

lemma heckeH_zero (f : CuspForm 𝒮ℒ k) : IsZeroAtImInfty (heckeH p f) := by
  have hpos := hp.out.pos
  have hp' : (0 : ℝ) < p := by exact_mod_cast hpos
  have hf : Tendsto (f : ℍ → ℂ) atImInfty (𝓝 0) := by
    have := CuspFormClass.zero_at_infty f
    simpa [IsZeroAtImInfty, ZeroAtFilter] using this
  have h1 : Tendsto (fun τ : ℍ => f (ofComplex (p * (τ : ℂ)))) atImInfty (𝓝 0) :=
    hf.comp (tendsto_comp (fun z hz => im_nat_mul hz hpos) p hp' fun z _ => by simp)
  have h2 : ∀ j : ℕ, Tendsto (fun τ : ℍ => f (ofComplex (((τ : ℂ) + j) / p))) atImInfty (𝓝 0) :=
    fun j => hf.comp (tendsto_comp (fun z hz => im_div_nat hz hpos) (1 / p) (by positivity)
      fun z _ => by rw [div_natCast_im]; simp; ring)
  have := (h1.const_mul ((p : ℂ) ^ (k - 1))).add
    ((tendsto_finsetSum (range p) fun j _ => h2 j).const_mul ((p : ℂ)⁻¹))
  rw [IsZeroAtImInfty, ZeroAtFilter]
  convert this using 1
  · funext τ
    simp [heckeH, heckeFun]
  · simp

/-- **The Hecke operator `T_p`** on `CuspForm 𝒮ℒ k`. -/
noncomputable def heckeCusp (f : CuspForm 𝒮ℒ k) : CuspForm 𝒮ℒ k where
  toFun := heckeH p f
  slash_action_eq' A hA := by
    obtain ⟨A, rfl⟩ := hA
    exact SlashInvariantForm.slash_action_generators_SL2Z (heckeH_S p f) (heckeH_T p f) A
  holo' := heckeH_holo p f
  zero_at_cusps' hc := by
    rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc
    rw [OnePoint.isZeroAt_iff_forall_SL2Z hc]
    intro γ _
    rw [SlashInvariantForm.slash_action_generators_SL2Z (heckeH_S p f) (heckeH_T p f)]
    exact heckeH_zero p f

lemma heckeCusp_apply (f : CuspForm 𝒮ℒ k) (τ : ℍ) : heckeCusp p f τ = heckeH p f τ := rfl


open Function
open scoped Real

local notation "𝕢" => Periodic.qParam


/-- the q-expansion series of a level-one cusp form, read at any point of the upper half plane. -/
lemma hasSum_cusp (f : CuspForm 𝒮ℒ k) {w : ℂ} (hw : 0 < w.im) :
    HasSum (fun n => (qExpansion 1 f).coeff n * 𝕢 1 w ^ n) (f (ofComplex w)) := by
  have h := hasSum_qExpansion one_pos (SlashInvariantFormClass.periodic_comp_ofComplex f one_mem_strictPeriods_SL)
    (ModularFormClass.holo f) (CuspFormClass.zero_at_infty f).isBoundedAtImInfty (ofComplex w)
  rw [ofComplex_apply_of_im_pos hw] at h ⊢
  simpa [smul_eq_mul] using h

lemma qP_mul (p : ℕ) (z : ℂ) : 𝕢 1 (p * z) = 𝕢 1 z ^ p := by
  simp only [Periodic.qParam, ofReal_one, div_one]
  rw [← Complex.exp_nat_mul]; ring_nf

lemma qP_shift (p j : ℕ) (z : ℂ) :
    𝕢 1 ((z + j) / p) = 𝕢 1 (z / p) * cexp (2 * π * Complex.I / p) ^ j := by
  simp only [Periodic.qParam, ofReal_one, div_one]
  rw [← Complex.exp_nat_mul, ← Complex.exp_add]; ring_nf


lemma root_sum (n : ℕ) :
    ∑ j ∈ range p, (cexp (2 * π * Complex.I / p) ^ j) ^ n = if p ∣ n then (p : ℂ) else 0 := by
  have hζ := Complex.isPrimitiveRoot_exp p hp.out.ne_zero
  simp_rw [← pow_mul, mul_comm _ n, pow_mul]
  split_ifs with h
  · rw [(hζ.pow_eq_one_iff_dvd n).mpr h]; simp
  · have hc : n.Coprime p := (Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hp.out).mpr h))
    exact (hζ.pow_of_coprime n hc).geom_sum_eq_zero hp.out.one_lt

/-- reindexing a series supported on multiples of `p`. -/
lemma hasSum_mul_reindex {F : ℕ → ℂ} {s : ℂ} (hF : ∀ n, ¬ p ∣ n → F n = 0) :
    HasSum (fun m => F (p * m)) s ↔ HasSum F s := by
  have hinj : Injective (fun m : ℕ => p * m) := fun a b h => Nat.eq_of_mul_eq_mul_left hp.out.pos h
  refine hinj.hasSum_iff (fun n hn => hF n fun ⟨m, hm⟩ => hn ⟨m, hm.symm⟩)

/-- **The q-expansion of `T_p f`.** -/
theorem hasSum_hecke (f : CuspForm 𝒮ℒ k) (t : ℍ) :
    HasSum (fun m => ((qExpansion 1 f).coeff (p * m) +
      (p : ℂ) ^ (k - 1) * (if p ∣ m then (qExpansion 1 f).coeff (m / p) else 0)) * 𝕢 1 t ^ m)
      (heckeCusp p f t) := by
  set a := fun n => (qExpansion 1 f).coeff n
  have hpos := hp.out.pos
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast hpos.ne'
  have hz := t.im_pos
  -- the `f(pz)` part
  have hA : HasSum (fun m => (if p ∣ m then a (m / p) else 0) * 𝕢 1 t ^ m) (f (ofComplex (p * (t : ℂ)))) := by
    rw [← hasSum_mul_reindex p (fun n hn => by simp [hn])]
    have h0 := hasSum_cusp f (im_nat_mul hz hpos)
    simp_rw [qP_mul, ← pow_mul] at h0
    convert h0 using 2 with m
    simp [Nat.mul_div_cancel_left m hpos, a]
  -- the averaged translates
  have hB : HasSum (fun m => (p : ℂ) * a (p * m) * 𝕢 1 t ^ m)
      (∑ j ∈ range p, f (ofComplex (((t : ℂ) + j) / p))) := by
    have h0 := hasSum_sum (s := range p) fun j _ => hasSum_cusp f (im_div_nat (j := j) hz hpos)
    have e : ∀ n, ∑ j ∈ range p, (qExpansion 1 f).coeff n * 𝕢 1 (((t : ℂ) + j) / p) ^ n
        = a n * 𝕢 1 ((t : ℂ) / p) ^ n * (if p ∣ n then (p : ℂ) else 0) := fun n => by
      simp_rw [qP_shift, mul_pow, ← mul_sum, root_sum, a]; ring
    simp_rw [e] at h0
    rw [← hasSum_mul_reindex p (fun n hn => by simp [hn])] at h0
    convert h0 using 2 with m
    have : 𝕢 1 ((t : ℂ) / p) ^ (p * m) = 𝕢 1 t ^ m := by
      rw [pow_mul, ← qP_mul, mul_div_cancel₀ _ hp0]
    rw [this, if_pos (Nat.dvd_mul_right p m)]; ring
  have := (hA.mul_left ((p : ℂ) ^ (k - 1))).add (hB.mul_left (p : ℂ)⁻¹)
  exact this.congr_fun fun m => by field_simp; ring

/-- **The Hecke action on q-expansion coefficients.** -/
theorem qExpansion_hecke (f : CuspForm 𝒮ℒ k) (m : ℕ) :
    (qExpansion 1 (heckeCusp p f)).coeff m = (qExpansion 1 f).coeff (p * m) +
      (p : ℂ) ^ (k - 1) * (if p ∣ m then (qExpansion 1 f).coeff (m / p) else 0) := by
  have h := ModularFormClass.qExpansion_coeff_unique one_pos one_mem_strictPeriods_SL
    (fun t => by simpa [smul_eq_mul] using hasSum_hecke p f t) m
  rw [mul_ite, mul_zero]; exact h.symm

/-- `T_p` as a ℂ-linear endomorphism. -/
noncomputable def heckeLin : CuspForm 𝒮ℒ k →ₗ[ℂ] CuspForm 𝒮ℒ k where
  toFun := heckeCusp p
  map_add' f g := by
    ext t
    simp only [heckeCusp_apply, heckeH, heckeFun, add_apply, Function.comp_apply, sum_add_distrib]
    ring
  map_smul' c f := by
    ext t
    change heckeH p (c • f) t = c * heckeH p f t
    have e : ∀ x, (c • f) x = c * f x := fun _ => rfl
    simp only [heckeH, heckeFun, Function.comp_apply, e]
    rw [← Finset.mul_sum]; ring

end RamanujanWeil.ArithPlan.TauHecke
