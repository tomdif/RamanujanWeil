import RamanujanWeil.Arith.ESPropB

/-!
# A2 / ES-P7: right-coset sums of `T̃ₙ` (docs/ARITH_ES_PLAN.md, §2 P7)

For a coefficient function `f : M2 → ℚ` and a matrix `A`, the right-coset sum is

  `cS f A = Σ_{γ ∈ M₂(ℤ), det γ = 1} f(Aγ)`,

i.e. PZ's `⟨T, AΓ⟩` (both `γ` and `−γ` occur; `ptC` sees at most one of `±Aγ`).

This file proves the invariances behind PZ Theorem 4(b) / Theorem B(a):

* `cS_mul_right` : `cS f (A h) = cS f A` for `det h = 1`;
* `cS_ptC_16a`   : `cS T̃ A = −(cS F A + cS F (U⁻¹A) + cS F (U⁻²A))`  (from (16a));
* `cS_ptC_16b`   : `cS T̃ A = −(cS G A + cS G (S⁻¹A))`                   (from (16b));
* `cS_ptC_U`, `cS_ptC_S`, `cS_ptC_T` : invariance of `A ↦ cS T̃ A` under `A ↦ UA, SA, TA`.
-/

open Finset

namespace RamanujanWeil.Arith.ES

open M2

/-- Right-coset sum `Σ_{det γ = 1} f(Aγ)`. -/
noncomputable def cS (f : M2 → ℚ) (A : M2) : ℚ :=
  ∑ᶠ γ : M2, if γ.det = 1 then f (A * γ) else 0

/-- Adjugate. -/
def adj (A : M2) : M2 := ⟨A.d, -A.b, -A.c, A.a⟩

lemma adj_mul (A : M2) : adj A * A = ⟨A.det, 0, 0, A.det⟩ := by
  ext <;> simp [adj, det] <;> ring

lemma mul_left_injective' {A : M2} (hA : A.det ≠ 0) : Function.Injective (fun γ : M2 => A * γ) := by
  intro x y h
  have h2 : adj A * (A * x) = adj A * (A * y) := by simp only at h; rw [h]
  rw [← mul_assoc, ← mul_assoc, adj_mul] at h2
  have ha := congrArg M2.a h2
  have hb := congrArg M2.b h2
  have hc := congrArg M2.c h2
  have hd := congrArg M2.d h2
  simp only [mul_a, mul_b, mul_c, mul_d, zero_mul, add_zero, zero_add] at ha hb hc hd
  ext
  · exact mul_left_cancel₀ hA ha
  · exact mul_left_cancel₀ hA hb
  · exact mul_left_cancel₀ hA hc
  · exact mul_left_cancel₀ hA hd

lemma cS_support {f : M2 → ℚ} {A : M2} (hA : A.det ≠ 0) (hf : FinDet A.det f) :
    (Function.support fun γ : M2 => if γ.det = 1 then f (A * γ) else 0).Finite := by
  refine (hf.preimage (mul_left_injective' hA).injOn).subset fun γ hγ => ?_
  simp only [Function.mem_support] at hγ
  split_ifs at hγ with h
  · exact ⟨by rw [det_mul, h, mul_one], hγ⟩
  · exact absurd rfl hγ

lemma cS_add {f g : M2 → ℚ} {A : M2} (hA : A.det ≠ 0) (hf : FinDet A.det f)
    (hg : FinDet A.det g) : cS (fun N => f N + g N) A = cS f A + cS g A := by
  unfold cS
  rw [← finsum_add_distrib (cS_support hA hf) (cS_support hA hg)]
  congr 1; funext γ; split_ifs <;> simp

lemma cS_sub {f g : M2 → ℚ} {A : M2} (hA : A.det ≠ 0) (hf : FinDet A.det f)
    (hg : FinDet A.det g) : cS (fun N => f N - g N) A = cS f A - cS g A := by
  unfold cS
  rw [← finsum_sub_distrib (cS_support hA hf) (cS_support hA hg)]
  congr 1; funext γ; split_ifs <;> simp

lemma cS_congr {f g : M2 → ℚ} (h : ∀ N, f N = g N) (A : M2) : cS f A = cS g A := by
  rw [funext h]

lemma det_eq_one_of_mul {h h' : M2} (hh : h * h' = 1) (hd : h.det = 1) : h'.det = 1 := by
  have := congrArg M2.det hh
  rw [det_mul, hd, one_mul] at this
  rw [this]; rfl

/-- Left translation by `g` and right translation by `h ∈ Γ`. -/
lemma cS_conj (f : M2 → ℚ) (g : M2) {h h' : M2} (hh : h * h' = 1) (hh' : h' * h = 1)
    (hd : h.det = 1) (A : M2) : cS (fun N => f (g * N * h)) A = cS f (g * A) := by
  unfold cS
  have hd' := det_eq_one_of_mul hh hd
  let e : M2 ≃ M2 :=
    { toFun := fun γ => γ * h'
      invFun := fun γ => γ * h
      left_inv := fun γ => by simp only; rw [mul_assoc, hh', mul_one]
      right_inv := fun γ => by simp only; rw [mul_assoc, hh, mul_one] }
  rw [← finsum_comp_equiv e]
  congr 1; funext γ
  simp only [e, Equiv.coe_fn_mk, det_mul, hd', mul_one]
  congr 1
  simp only [mul_assoc, hh', mul_one]

lemma cS_mul_right (f : M2 → ℚ) {h h' : M2} (hh : h * h' = 1) (hh' : h' * h = 1)
    (hd : h.det = 1) (A : M2) : cS f (A * h) = cS f A := by
  have hd' := det_eq_one_of_mul hh hd
  unfold cS
  let e : M2 ≃ M2 :=
    { toFun := fun γ => h' * γ
      invFun := fun γ => h * γ
      left_inv := fun γ => by simp only; rw [← mul_assoc, hh, one_mul]
      right_inv := fun γ => by simp only; rw [← mul_assoc, hh', one_mul] }
  rw [← finsum_comp_equiv e]
  congr 1; funext γ
  simp only [e, Equiv.coe_fn_mk, det_mul, hd', one_mul]
  rw [mul_assoc, ← mul_assoc h, hh, one_mul]

lemma cS_neg (f : M2 → ℚ) (A : M2) : cS f (-A) = cS f A := by
  have h1 : (-1 : M2) * -1 = 1 := by decide
  have h2 : (-1 : M2).det = 1 := by decide
  have : -A = A * -1 := by ext <;> simp
  rw [this, cS_mul_right f h1 h1 h2]

lemma cS_left (f : M2 → ℚ) (g A : M2) : cS (fun N => f (g * N)) A = cS f (g * A) := by
  have := cS_conj f g (h := 1) (h' := 1) (by decide) (by decide) (by decide) A
  simpa only [mul_one] using this

lemma cS_right (f : M2 → ℚ) {h h' : M2} (hh : h * h' = 1) (hh' : h' * h = 1)
    (hd : h.det = 1) (A : M2) : cS (fun N => f (N * h)) A = cS f A := by
  have := cS_conj f 1 hh hh' hd A
  simpa only [one_mul] using this

/-! ### Finiteness of transported regions -/

lemma FinDet.comp_inj {n : ℤ} {f : M2 → ℚ} (hf : FinDet n f) {ψ : M2 → M2}
    (hψ : Function.Injective ψ) (hd : ∀ M, (ψ M).det = M.det) : FinDet n (fun M => f (ψ M)) :=
  (hf.preimage hψ.injOn).subset fun M hM => ⟨by rw [hd]; exact hM.1, hM.2⟩

lemma mapA_inj : Function.Injective mapA := by
  intro x y h; simp only [mapA, M2.mk.injEq] at h; ext <;> omega
lemma mapB_inj : Function.Injective mapB := by
  intro x y h; simp only [mapB, M2.mk.injEq] at h; ext <;> omega
lemma mapC_inj : Function.Injective mapC := by
  intro x y h; simp only [mapC, M2.mk.injEq] at h; ext <;> omega
lemma mapD_inj : Function.Injective mapD := by
  intro x y h; simp only [mapD, M2.mk.injEq] at h; ext <;> omega
lemma mapE_inj : Function.Injective mapE := by
  intro x y h; simp only [mapE, M2.mk.injEq] at h; ext <;> omega

lemma fin_F (n : ℤ) : FinDet n regF := FinDet.of_bd fun _ h1 h2 => regF_bd h1 h2
lemma fin_G (n : ℤ) : FinDet n regG := FinDet.of_bd fun _ h1 h2 => regG_bd h1 h2
lemma fin_Q (n : ℤ) : FinDet n regQ := FinDet.of_bd fun _ h1 h2 => regQ_bd h1 h2

/-! ### Consequences of (16a), (16b) -/

lemma FinDet.neg {n : ℤ} {f : M2 → ℚ} (hf : FinDet n f) : FinDet n (fun M => -f M) :=
  hf.subset fun M hM => ⟨hM.1, fun h => hM.2 (by simp [h])⟩

lemma cS_neg_fun (f : M2 → ℚ) (A : M2) : cS (fun N => -f N) A = -cS f A := by
  unfold cS
  rw [← finsum_neg_distrib]
  congr 1; funext γ; split_ifs <;> simp

lemma cS_smul (r : ℚ) (f : M2 → ℚ) (A : M2) : cS (fun N => r * f N) A = r * cS f A := by
  unfold cS
  rw [mul_finsum]
  congr 1; funext γ; split_ifs <;> simp

lemma neg_mul' (X Y : M2) : -X * Y = -(X * Y) := by ext <;> simp <;> ring

lemma Si_S' : Si * S = 1 := Si_S
lemma det_Si : Si.det = 1 := by decide
lemma det_Ui : Ui.det = 1 := by decide

/-- From (16a): `⟨T̃, AΓ⟩ = −(⟨F, AΓ⟩ + ⟨F, U⁻¹AΓ⟩ + ⟨F, U⁻²AΓ⟩)`. -/
theorem cS_ptC_16a {A : M2} (hA : A.det ≠ 0) :
    cS ptC A = -(cS regF A + cS regF (Ui * A) + cS regF (Ui * Ui * A)) := by
  set n := A.det with hn
  have fA := (fin_F n).comp_inj mapA_inj det_mapA
  have fB := (fin_F n).comp_inj mapB_inj det_mapB
  have fC := (fin_T1 n).comp_inj mapC_inj det_mapC
  rw [cS_congr ptC_16a, cS_sub hA ((((fin_F n).neg.sub fA).sub fB).add (fin_T1 n)) fC,
    cS_add hA (((fin_F n).neg.sub fA).sub fB) (fin_T1 n), cS_sub hA ((fin_F n).neg.sub fA) fB,
    cS_sub hA (fin_F n).neg fA, cS_neg_fun]
  have eA : cS (fun N => regF (mapA N)) A = cS regF (Ui * A) := by
    have : ∀ N, regF (mapA N) = regF (-Ui * N * Si) := fun N => by rw [mul_assoc, mapA_eq]
    rw [cS_congr this, cS_conj regF (-Ui) Si_S S_Si det_Si, neg_mul', cS_neg]
  have eB : cS (fun N => regF (mapB N)) A = cS regF (Ui * Ui * A) := by
    have : ∀ N, regF (mapB N) = regF (-(Ui * Ui) * N) := fun N => by rw [mapB_eq]
    rw [cS_congr this, cS_left, neg_mul', cS_neg]
  have eC : cS (fun N => regT1 (mapC N)) A = cS regT1 A := by
    have : ∀ N, regT1 (mapC N) = regT1 (N * Si) := fun N => by rw [mapC_eq]
    rw [cS_congr this, cS_right regT1 Si_S S_Si det_Si]
  rw [eA, eB, eC]; ring

/-- From (16b): `⟨T̃, AΓ⟩ = −(⟨G, AΓ⟩ + ⟨G, S⁻¹AΓ⟩)`. -/
theorem cS_ptC_16b {A : M2} (hA : A.det ≠ 0) :
    cS ptC A = -(cS regG A + cS regG (Si * A)) := by
  set n := A.det with hn
  have fD := (fin_G n).comp_inj mapD_inj det_mapD
  have fE := (fin_T1 n).comp_inj mapE_inj det_mapE
  have fQE := (fin_Q n).comp_inj mapE_inj det_mapE
  have fQ' : FinDet n (fun M => (regQ M - regQ (mapE M)) / 12) :=
    ((fin_Q n).sub fQE).subset fun M hM => ⟨hM.1, fun h => hM.2 (by simp [h])⟩
  rw [cS_congr ptC_16b,
    cS_add hA ((((fin_G n).neg.sub fD).add (fin_T1 n)).sub fE) fQ',
    cS_sub hA (((fin_G n).neg.sub fD).add (fin_T1 n)) fE,
    cS_add hA ((fin_G n).neg.sub fD) (fin_T1 n), cS_sub hA (fin_G n).neg fD, cS_neg_fun]
  have eD : cS (fun N => regG (mapD N)) A = cS regG (Si * A) := by
    have : ∀ N, regG (mapD N) = regG (-Si * N * Ui) := fun N => by rw [mul_assoc, mapD_eq]
    rw [cS_congr this, cS_conj regG (-Si) Ui_U U_Ui det_Ui, neg_mul', cS_neg]
  have eE : cS (fun N => regT1 (mapE N)) A = cS regT1 A := by
    have : ∀ N, regT1 (mapE N) = regT1 (N * Ui) := fun N => by rw [mapE_eq]
    rw [cS_congr this, cS_right regT1 Ui_U U_Ui det_Ui]
  have eQ : cS (fun N => (regQ N - regQ (mapE N)) / 12) A = 0 := by
    have h1 : ∀ N, (regQ N - regQ (mapE N)) / 12 = (1 / 12 : ℚ) * (regQ N - regQ (mapE N)) :=
      fun N => by ring
    have : ∀ N, regQ (mapE N) = regQ (N * Ui) := fun N => by rw [mapE_eq]
    rw [cS_congr h1, cS_smul, cS_sub hA (fin_Q n) fQE, cS_congr this,
      cS_right regQ Ui_U U_Ui det_Ui, sub_self, mul_zero]
  rw [eD, eE, eQ]; ring

/-! ### Left invariance (PZ Theorem B(a)) -/

lemma det_mul_ne {g A : M2} (hg : g.det = 1) (hA : A.det ≠ 0) : (g * A).det ≠ 0 := by
  rw [det_mul, hg, one_mul]; exact hA

lemma det_U : U.det = 1 := by decide
lemma det_S : S.det = 1 := by decide
lemma det_T : T.det = 1 := by decide

/-- `⟨T̃, U·AΓ⟩ = ⟨T̃, AΓ⟩`. -/
theorem cS_ptC_U {A : M2} (hA : A.det ≠ 0) : cS ptC (U * A) = cS ptC A := by
  rw [cS_ptC_16a (det_mul_ne det_U hA), cS_ptC_16a hA]
  have e1 : Ui * (U * A) = A := by rw [← mul_assoc, Ui_U, one_mul]
  have e2 : Ui * Ui * (U * A) = Ui * A := by
    rw [mul_assoc, ← mul_assoc Ui U, Ui_U, one_mul]
  have e3 : Ui * Ui * A = -(U * A) := by
    rw [show Ui * Ui = -U by decide, neg_mul']
  rw [e1, e2, e3, cS_neg]; ring

/-- `⟨T̃, S·AΓ⟩ = ⟨T̃, AΓ⟩`. -/
theorem cS_ptC_S {A : M2} (hA : A.det ≠ 0) : cS ptC (S * A) = cS ptC A := by
  rw [cS_ptC_16b (det_mul_ne det_S hA), cS_ptC_16b hA]
  have e1 : Si * (S * A) = A := by rw [← mul_assoc, Si_S, one_mul]
  have e2 : Si * A = -(S * A) := by rw [show Si = -S by decide, neg_mul']
  rw [e1, e2, cS_neg]; ring

/-- `⟨T̃, T·AΓ⟩ = ⟨T̃, AΓ⟩`. -/
theorem cS_ptC_T {A : M2} (hA : A.det ≠ 0) : cS ptC (T * A) = cS ptC A := by
  rw [T_eq_neg_U_mul_S, neg_mul', cS_neg, mul_assoc, cS_ptC_U (det_mul_ne det_S hA),
    cS_ptC_S hA]

/-- Upper unipotent `[[1, k], [0, 1]]`. -/
def Pk (k : ℤ) : M2 := ⟨1, k, 0, 1⟩
/-- Lower unipotent `[[1, 0], [k, 1]]`. -/
def Lk (k : ℤ) : M2 := ⟨1, 0, k, 1⟩

lemma det_Pk (k : ℤ) : (Pk k).det = 1 := by simp [Pk, det]
lemma det_Lk (k : ℤ) : (Lk k).det = 1 := by simp [Lk, det]

theorem cS_ptC_Pk (k : ℤ) {A : M2} (hA : A.det ≠ 0) : cS ptC (Pk k * A) = cS ptC A := by
  induction k using Int.induction_on generalizing A with
  | zero => rw [show Pk 0 = 1 by decide, one_mul]
  | succ i ih =>
    rw [show Pk ((i : ℤ) + 1) = T * Pk i by ext <;> simp [Pk, T], mul_assoc,
      cS_ptC_T (det_mul_ne (det_Pk _) hA), ih hA]
  | pred i ih =>
    have h := cS_ptC_T (det_mul_ne (det_Pk (-(i : ℤ) - 1)) hA)
    rw [← mul_assoc, show T * Pk (-(i : ℤ) - 1) = Pk (-(i : ℤ)) by ext <;> simp [Pk, T],
      ih hA] at h
    exact h.symm

theorem cS_ptC_Lk (k : ℤ) {A : M2} (hA : A.det ≠ 0) : cS ptC (Lk k * A) = cS ptC A := by
  have e : Lk k * A = -(S * (Pk (-k) * (S * A))) := by
    ext <;> simp [Lk, Pk, S]
  rw [e, cS_neg, cS_ptC_S (det_mul_ne (det_Pk _) (det_mul_ne det_S hA)),
    cS_ptC_Pk _ (det_mul_ne det_S hA), cS_ptC_S hA]

end RamanujanWeil.Arith.ES
