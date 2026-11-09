import RamanujanWeil.Arith.ESAnalyticSeries

/-!
# A2 / ES-P11: Bol's identity and the period polynomial

* `bol` : for `f` holomorphic on `ℍ`,
  `D^{n+1}[zⁿ f(−1/z)] = f^{(n+1)}(−1/z) / z^{n+2}` on `ℍ` (strong induction on `n`, using
  `D[zⁿ f(−1/z)] = n z^{n−1} f(−1/z) + z^{n−2} f′(−1/z)`).
* `poly_of_iteratedDeriv_eq_zero` : a holomorphic `f` on `ℍ` with `f^{(n+1)} = 0` is a polynomial of
  degree `≤ n` there.
* `rhoc_poly` : `ρ(z) = F̃(z) − z¹⁰F̃(−1/z)` agrees on `ℍ` with a polynomial of degree `≤ 10`
  (`D¹¹F̃ = (2πi)¹¹Δ` and `Δ(−1/z) = z¹²Δ(z)`).
-/

set_option autoImplicit false

namespace RamanujanWeil.Arith.ES.Analytic

open Complex Filter Set
open scoped Real Topology

lemma ne_zero_of_Hs {z : ℂ} (hz : z ∈ Hs) : z ≠ 0 := by
  rintro rfl; simp [Hs] at hz

lemma inv_mem_Hs {z : ℂ} (hz : z ∈ Hs) : -1 / z ∈ Hs := by
  have h0 := ne_zero_of_Hs hz
  show 0 < (-1 / z).im
  rw [div_im]
  simp only [neg_re, one_re, neg_im, one_im, neg_zero, zero_mul, zero_div, zero_sub]
  have : 0 < normSq z := normSq_pos.mpr h0
  have hz' : 0 < z.im := hz
  rw [neg_mul, one_mul, neg_div, neg_neg]
  positivity

lemma hasDerivAt_neg_inv {z : ℂ} (hz : z ≠ 0) : HasDerivAt (fun w : ℂ => -1 / w) (1 / z ^ 2) z := by
  have := (hasDerivAt_inv hz).const_mul (-1 : ℂ)
  rw [show (fun w : ℂ => -1 / w) = fun y => -1 * y⁻¹ from funext fun w => div_eq_mul_inv _ _]
  exact this.congr_deriv (by rw [one_div]; ring)

/-- holomorphy is inherited by all derivatives. -/
lemma diffOn_iter {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f Hs) :
    ∀ k : ℕ, DifferentiableOn ℂ (iteratedDeriv k f) Hs
  | 0 => by simpa using hf
  | k + 1 => by rw [iteratedDeriv_succ]; exact (diffOn_iter hf k).deriv isOpen_Hs

lemma contDiffAt_of {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f Hs) {z : ℂ} (hz : z ∈ Hs) (n : ℕ) :
    ContDiffAt ℂ n f z :=
  (hf.contDiffOn (n := n) isOpen_Hs).contDiffAt (isOpen_Hs.mem_nhds hz)

lemma hasDerivAt_comp_inv {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f Hs) {z : ℂ} (hz : z ∈ Hs) :
    HasDerivAt (fun w => f (-1 / w)) (deriv f (-1 / z) / z ^ 2) z := by
  have h1 := ((hf _ (inv_mem_Hs hz)).differentiableAt
    (isOpen_Hs.mem_nhds (inv_mem_Hs hz))).hasDerivAt
  exact (h1.comp z (hasDerivAt_neg_inv (ne_zero_of_Hs hz))).congr_deriv (by ring)

lemma diffOn_comp_inv {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f Hs) :
    DifferentiableOn ℂ (fun w => f (-1 / w)) Hs :=
  fun _ hz => (hasDerivAt_comp_inv hf hz).differentiableAt.differentiableWithinAt

/-- `φₙ f (z) = zⁿ f(−1/z)`. -/
noncomputable def phi (n : ℕ) (f : ℂ → ℂ) (z : ℂ) : ℂ := z ^ n * f (-1 / z)

lemma diffOn_phi {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f Hs) (n : ℕ) :
    DifferentiableOn ℂ (phi n f) Hs :=
  (differentiableOn_pow n).mul (diffOn_comp_inv hf)

lemma hasDerivAt_phi {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f Hs) (n : ℕ) {z : ℂ} (hz : z ∈ Hs) :
    HasDerivAt (phi (n + 1) f)
      (((n + 1 : ℕ) : ℂ) * z ^ n * f (-1 / z) + z ^ (n + 1) * (deriv f (-1 / z) / z ^ 2)) z := by
  have := (hasDerivAt_pow (n + 1) z).fun_mul (hasDerivAt_comp_inv hf hz)
  simp only [Nat.add_sub_cancel] at this
  exact this

lemma hasDerivAt_phi0 {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f Hs) {z : ℂ} (hz : z ∈ Hs) :
    HasDerivAt (phi 0 f) (deriv f (-1 / z) / z ^ 2) z := by
  have := hasDerivAt_comp_inv hf hz
  unfold phi; simpa using this

lemma deriv_phi_succ_succ {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f Hs) (n : ℕ) :
    EqOn (deriv (phi (n + 2) f))
      (fun z => ((n + 2 : ℕ) : ℂ) * phi (n + 1) f z + phi n (deriv f) z) Hs := by
  intro z hz
  rw [(hasDerivAt_phi hf (n + 1) hz).deriv]
  have h0 := ne_zero_of_Hs hz
  simp only [phi]
  field_simp
  ring

lemma iter_const_mul (c : ℂ) (A : ℂ → ℂ) (k : ℕ) :
    iteratedDeriv k (fun z => c * A z) = fun z => c * iteratedDeriv k A z :=
  funext fun _ => iteratedDeriv_const_mul_field c A

lemma iter_add_on {A B : ℂ → ℂ} (hA : DifferentiableOn ℂ A Hs) (hB : DifferentiableOn ℂ B Hs)
    (k : ℕ) : EqOn (iteratedDeriv k (fun z => A z + B z))
      (fun z => iteratedDeriv k A z + iteratedDeriv k B z) Hs := fun _ hz =>
  iteratedDeriv_add (contDiffAt_of hA hz k) (contDiffAt_of hB hz k)

lemma iter_sub_on {A B : ℂ → ℂ} (hA : DifferentiableOn ℂ A Hs) (hB : DifferentiableOn ℂ B Hs)
    (k : ℕ) : EqOn (iteratedDeriv k (fun z => A z - B z))
      (fun z => iteratedDeriv k A z - iteratedDeriv k B z) Hs := fun _ hz =>
  iteratedDeriv_sub (contDiffAt_of hA hz k) (contDiffAt_of hB hz k)

/-- derivative of `g(−1/z)/zᵐ`. -/
lemma hasDerivAt_quot {g : ℂ → ℂ} (hg : DifferentiableOn ℂ g Hs) (m : ℕ) {z : ℂ} (hz : z ∈ Hs) :
    HasDerivAt (fun w => g (-1 / w) / w ^ m)
      (deriv g (-1 / z) / z ^ (m + 2) - (m : ℂ) * g (-1 / z) / z ^ (m + 1)) z := by
  have h0 := ne_zero_of_Hs hz
  refine ((hasDerivAt_comp_inv hg hz).fun_div (hasDerivAt_pow m z) (pow_ne_zero m h0)).congr_deriv ?_
  rcases m with _ | m
  · simp
  · simp only [Nat.add_sub_cancel]
    field_simp
    ring

/-- **Bol's identity** `D^{n+1}[zⁿ f(−1/z)] = f^{(n+1)}(−1/z)/z^{n+2}` on `ℍ`. -/
theorem bol : ∀ (n : ℕ) (f : ℂ → ℂ), DifferentiableOn ℂ f Hs →
    EqOn (iteratedDeriv (n + 1) (phi n f)) (fun z => iteratedDeriv (n + 1) f (-1 / z) / z ^ (n + 2)) Hs
  | 0, f, hf => by
    intro z hz
    rw [iteratedDeriv_one, iteratedDeriv_one, (hasDerivAt_phi0 hf hz).deriv]
  | 1, f, hf => by
    intro z hz
    have h0 := ne_zero_of_Hs hz
    -- `D[z f(−1/z)] = f(−1/z) + f′(−1/z)/z`
    have e1 : EqOn (deriv (phi 1 f)) (fun w => f (-1 / w) + deriv f (-1 / w) / w ^ 1) Hs := by
      intro w hw
      have hw0 := ne_zero_of_Hs hw
      rw [(hasDerivAt_phi hf 0 hw).deriv]
      field_simp; ring
    rw [iteratedDeriv_succ', iteratedDeriv_one, e1.deriv isOpen_Hs hz]
    have hd := (hasDerivAt_comp_inv hf hz).fun_add (hasDerivAt_quot (hf.deriv isOpen_Hs) 1 hz)
    rw [hd.deriv, iteratedDeriv_succ, iteratedDeriv_one]
    field_simp; ring
  | n + 2, f, hf => by
    intro z hz
    have h0 := ne_zero_of_Hs hz
    have hf' := hf.deriv isOpen_Hs
    rw [iteratedDeriv_succ', (deriv_phi_succ_succ hf n).iteratedDeriv_of_isOpen isOpen_Hs _ hz]
    rw [iter_add_on ((diffOn_phi hf (n + 1)).const_mul _) (diffOn_phi hf' n) _ hz]
    simp only [iter_const_mul]
    rw [bol (n + 1) f hf hz]
    -- the second term: `D^{n+2}[zⁿ f′(−1/z)] = D[f^{(n+2)}(−1/w)/w^{n+2}]`
    have hB : EqOn (iteratedDeriv (n + 1) (phi n (deriv f)))
        (fun w => iteratedDeriv (n + 2) f (-1 / w) / w ^ (n + 2)) Hs := by
      intro w hw
      rw [bol n (deriv f) hf' hw, ← iteratedDeriv_succ']
    have e2 : iteratedDeriv (n + 2) (phi n (deriv f)) z =
        deriv (iteratedDeriv (n + 1) (phi n (deriv f))) z := by rw [iteratedDeriv_succ]
    have e3 : iteratedDeriv (n + 2 + 1) f = deriv (iteratedDeriv (n + 2) f) := iteratedDeriv_succ
    rw [e2, hB.deriv isOpen_Hs hz, (hasDerivAt_quot (diffOn_iter hf (n + 2)) (n + 2) hz).deriv, e3]
    show ((n + 2 : ℕ) : ℂ) * (iteratedDeriv (n + 2) f (-1 / z) / z ^ (n + 3)) + _ = _
    push_cast
    field_simp
    ring

/-! ### Vanishing `(n+1)`-st derivative ⇒ polynomial -/

/-- the antiderivative of `Σ_{i<N} aᵢ Xⁱ`. -/
noncomputable def antider (a : ℕ → ℂ) (N : ℕ) : Polynomial ℂ :=
  ∑ i ∈ Finset.range N, Polynomial.C (a i / (i + 1)) * Polynomial.X ^ (i + 1)

lemma derivative_antider (a : ℕ → ℂ) (N : ℕ) :
    Polynomial.derivative (antider a N) = ∑ i ∈ Finset.range N, Polynomial.C (a i) * Polynomial.X ^ i := by
  unfold antider
  rw [Polynomial.derivative_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Polynomial.derivative_C_mul_X_pow, Nat.add_sub_cancel]
  congr 2
  push_cast
  field_simp

lemma natDegree_antider (a : ℕ → ℂ) (N : ℕ) : (antider a N).natDegree ≤ N := by
  unfold antider
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun i hi => ?_
  refine (Polynomial.natDegree_C_mul_X_pow_le _ _).trans ?_
  have := Finset.mem_range.mp hi; omega

lemma isPreconnected_Hs : IsPreconnected Hs := (convex_halfSpace_im_gt 0).isPreconnected

/-- **A holomorphic function on `ℍ` with vanishing `(n+1)`-st derivative is a polynomial of
degree `≤ n`.** -/
theorem poly_of_iteratedDeriv_eq_zero : ∀ (n : ℕ) (f : ℂ → ℂ), DifferentiableOn ℂ f Hs →
    EqOn (iteratedDeriv (n + 1) f) 0 Hs →
      ∃ p : Polynomial ℂ, p.natDegree ≤ n ∧ EqOn f (fun z => p.eval z) Hs
  | 0, f, hf, h0 => by
    rw [iteratedDeriv_one] at h0
    obtain ⟨a, ha⟩ := isOpen_Hs.exists_eq_add_of_deriv_eq isPreconnected_Hs hf
      (differentiableOn_const (0 : ℂ)) (fun z hz => by rw [h0 hz]; simp)
    exact ⟨Polynomial.C a, by simp, fun z hz => by rw [ha hz]; simp⟩
  | n + 1, f, hf, h0 => by
    have hf' := hf.deriv isOpen_Hs
    rw [iteratedDeriv_succ'] at h0
    obtain ⟨q, hq, hfq⟩ := poly_of_iteratedDeriv_eq_zero n (deriv f) hf' h0
    set P := antider (fun i => q.coeff i) (n + 1)
    have hP : Polynomial.derivative P = q := by
      rw [derivative_antider]
      exact (q.as_sum_range_C_mul_X_pow' (by omega)).symm
    obtain ⟨a, ha⟩ := isOpen_Hs.exists_eq_add_of_deriv_eq isPreconnected_Hs hf
      (Polynomial.differentiable P).differentiableOn (fun z hz => by
        rw [hfq hz, Polynomial.deriv, hP])
    refine ⟨P + Polynomial.C a, ?_, fun z hz => by rw [ha hz]; simp⟩
    refine (Polynomial.natDegree_add_le _ _).trans (max_le (natDegree_antider _ _) (by simp))

/-! ### The period polynomial -/

/-- `ρ(z) = F̃(z) − z¹⁰ F̃(−1/z)` on `ℂ`. -/
noncomputable def rhoc (z : ℂ) : ℂ := Fc z - z ^ 10 * Fc (-1 / z)

theorem iteratedDeriv_rhoc_eq_zero : EqOn (iteratedDeriv 11 rhoc) 0 Hs := by
  intro z hz
  have hFc := differentiableOn_Fc
  have e := iter_sub_on hFc (diffOn_phi hFc 10) 11 hz
  simp only [phi] at e
  rw [show rhoc = fun z => Fc z - z ^ 10 * Fc (-1 / z) from rfl, e]
  have hb := bol 10 Fc hFc hz
  simp only at hb
  rw [hb, iteratedDeriv_Fc 11 le_rfl hz, iteratedDeriv_Fc 11 le_rfl (inv_mem_Hs hz),
    G_cj11 hz, G_cj11 (inv_mem_Hs hz), Dc_S hz]
  have h0 := ne_zero_of_Hs hz
  simp only [Pi.zero_apply]
  field_simp
  ring

lemma differentiableOn_rhoc : DifferentiableOn ℂ rhoc Hs :=
  differentiableOn_Fc.sub (diffOn_phi differentiableOn_Fc 10)

/-- **`ρ` is a polynomial of degree `≤ 10`** on `ℍ`. -/
theorem rhoc_poly : ∃ p : Polynomial ℂ, p.natDegree ≤ 10 ∧ EqOn rhoc (fun z => p.eval z) Hs :=
  poly_of_iteratedDeriv_eq_zero 10 rhoc differentiableOn_rhoc iteratedDeriv_rhoc_eq_zero

end RamanujanWeil.Arith.ES.Analytic
