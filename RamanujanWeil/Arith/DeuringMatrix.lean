import RamanujanWeil.Arith.HurwitzOrbit

/-!
# A3-ord, algebraic end: the matrix mass is `H(4q − t²)/2` (Latimer–MacDuffee, weighted)

This is the purely algebraic last step of the Deuring blueprint (`docs/ARITH_DEURING_PLAN.md`,
milestone D-ALG). Isomorphism classes of `ℤ[π]`-modules that are free of rank 2 over `ℤ`, with
`π² − tπ + q = 0`, are the `GL₂(ℤ)`-conjugacy classes of integer matrices `M` with `tr M = t`,
`det M = q`, and the automorphism group of the module is the centralizer of `M` in `GL₂(ℤ)`.

* `TrDet t q`: integer `2 × 2` matrices with trace `t` and determinant `q`, with
  `GL₂(ℤ) = (Matrix (Fin 2) (Fin 2) ℤ)ˣ` acting by conjugation `g • M = g M g⁻¹`.
* `matMass t q = Σ_{GL₂(ℤ)-classes} 1 / #Stab` (a `finsum` over the orbit space).
* **`matMass_eq_hurwitz`**: for `t² < 4q`, `matMass t q = H(4q − t²)/2`, with `H = hurwitz`.

Proof: `M = [[a, b], [c, d]] ↦ (c, d − a, −b)` (`formOfMat`, `f_M(v) = det(v, Mv)`) identifies
the matrices with `c > 0` with positive definite forms of discriminant `t² − 4q`, and is
equivariant for `γ ↦ (γᵀ)⁻¹` (`psi_smul`). Every class meets `c > 0` (conjugate by
`diag(1, −1)`), and any `g ∈ GL₂(ℤ)` conjugating one such matrix to another has `det g = 1`
(`det_eq_one_of_conj`: `4c · c' · det g = (2cs + (a−d)r)² + (4q − t²) r² > 0`). So the
`GL₂(ℤ)`-classes are the `SL₂(ℤ)`-classes of forms, stabilizers agree, and the mass is
`hurwitzOrbit / 2`.
-/

namespace RamanujanWeil.Arith.Deuring

open RamanujanWeil.Arith.Hurwitz Matrix MulAction
open scoped MatrixGroups

/-- Integer `2 × 2` matrices. -/
abbrev M2 := Matrix (Fin 2) (Fin 2) ℤ

/-- `GL₂(ℤ)` as the unit group of `M2`. -/
abbrev GL2 := M2ˣ

/-- Integer matrices with trace `t` and determinant `q`. -/
def TrDet (t q : ℤ) : Type := {M : M2 // M.trace = t ∧ M.det = q}

instance (t q : ℤ) : MulAction GL2 (TrDet t q) where
  smul g M := ⟨(g : M2) * M.1 * (↑g⁻¹ : M2), by rw [trace_units_conj]; exact M.2.1,
    by rw [det_units_conj]; exact M.2.2⟩
  one_smul M := Subtype.ext (by
    change ((1 : GL2) : M2) * M.1 * (↑(1 : GL2)⁻¹ : M2) = M.1
    simp)
  mul_smul g h M := Subtype.ext (by
    change ((g * h : GL2) : M2) * M.1 * (↑(g * h)⁻¹ : M2) =
      (g : M2) * ((h : M2) * M.1 * (↑h⁻¹ : M2)) * (↑g⁻¹ : M2)
    simp only [_root_.mul_inv_rev, Units.val_mul, Matrix.mul_assoc])

lemma smul_val {t q : ℤ} (g : GL2) (M : TrDet t q) : (g • M).1 = (g : M2) * M.1 * (↑g⁻¹ : M2) :=
  rfl

/-- **Matrix mass**: `Σ_{GL₂(ℤ)-conjugacy classes of M, tr M = t, det M = q} 1 / #Centralizer`. -/
noncomputable def matMass (t q : ℤ) : ℚ :=
  ∑ᶠ O : orbitRel.Quotient GL2 (TrDet t q), (1 : ℚ) / Nat.card (stabilizer GL2 O.out)

/-! ### Elementary facts -/

lemma trace_two (M : M2) : M.trace = M 0 0 + M 1 1 := Matrix.trace_fin_two M

lemma det_unit (g : GL2) : (g : M2).det = 1 ∨ (g : M2).det = -1 :=
  Int.isUnit_iff.mp (isUnits_det_units g)

/-- No matrix of trace `t`, determinant `q` with `t² < 4q` is triangular. -/
lemma entry10_ne_zero {t q : ℤ} (hlt : t ^ 2 < 4 * q) (M : TrDet t q) : M.1 1 0 ≠ 0 := by
  intro h
  have ht := M.2.1
  have hd := M.2.2
  rw [trace_two] at ht
  rw [det_fin_two, h, mul_zero, sub_zero] at hd
  have e : t ^ 2 - 4 * q = (M.1 0 0 - M.1 1 1) ^ 2 := by
    linear_combination (-(M.1 0 0 + M.1 1 1 + t)) * ht + 4 * hd
  nlinarith [sq_nonneg (M.1 0 0 - M.1 1 1)]

/-- The positivity identity behind `det_eq_one_of_conj`. -/
lemma det_pos_aux (a b c d c' p q' r s t Q : ℤ) (htr : a + d = t) (hdet : a * d - b * c = Q)
    (hlt : t ^ 2 < 4 * Q) (hc : 0 < c) (hc' : 0 < c') (hrs : r ≠ 0 ∨ s ≠ 0)
    (hid : c' * (p * s - q' * r) = c * s ^ 2 + (a - d) * r * s - b * r ^ 2) :
    0 < p * s - q' * r := by
  have e : 4 * c * (c * s ^ 2 + (a - d) * r * s - b * r ^ 2) =
      (2 * c * s + (a - d) * r) ^ 2 + (4 * Q - t ^ 2) * r ^ 2 := by
    rw [← htr, ← hdet]; ring
  have hpos : 0 < 4 * c * (c * s ^ 2 + (a - d) * r * s - b * r ^ 2) := by
    rw [e]
    rcases hrs with hr | hs
    · have : 0 < r ^ 2 := by positivity
      nlinarith [sq_nonneg (2 * c * s + (a - d) * r)]
    · rcases eq_or_ne r 0 with hr | hr
      · subst hr
        have : 0 < s ^ 2 := by positivity
        have : 0 < (2 * c * s) ^ 2 := by positivity
        nlinarith
      · have : 0 < r ^ 2 := by positivity
        nlinarith [sq_nonneg (2 * c * s + (a - d) * r)]
  rw [← hid] at hpos
  by_contra hneg
  push Not at hneg
  have : 4 * c * (c' * (p * s - q' * r)) ≤ 0 := by
    have h1 : 0 ≤ 4 * c * c' := by positivity
    nlinarith
  linarith

/-- **Orientation lemma.** If `g ∈ GL₂(ℤ)` conjugates `M` to `M'`, both with positive lower-left
entry, then `det g = 1`. (In particular the centralizer of such an `M` lies in `SL₂(ℤ)`.) -/
lemma det_eq_one_of_conj {t q : ℤ} (hlt : t ^ 2 < 4 * q) (g : GL2) (M M' : TrDet t q)
    (hc : 0 < M.1 1 0) (hc' : 0 < M'.1 1 0) (h : g • M = M') : (g : M2).det = 1 := by
  have hgM : (g : M2) * M.1 = M'.1 * (g : M2) := by
    rw [← h, smul_val, Matrix.mul_assoc, Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]
  have e10 := congrFun (congrFun hgM 1) 0
  have e11 := congrFun (congrFun hgM 1) 1
  simp only [Matrix.mul_apply, Fin.sum_univ_two] at e10 e11
  have ht := M.2.1
  have hd := M.2.2
  rw [trace_two] at ht
  rw [det_fin_two] at hd
  have hdg := det_unit g
  rw [det_fin_two] at hdg ⊢
  have hrs : (g : M2) 1 0 ≠ 0 ∨ (g : M2) 1 1 ≠ 0 := by
    by_contra hcon
    push Not at hcon
    rw [hcon.1, hcon.2] at hdg
    simp at hdg
  have hid : M'.1 1 0 * ((g : M2) 0 0 * (g : M2) 1 1 - (g : M2) 0 1 * (g : M2) 1 0) =
      M.1 1 0 * (g : M2) 1 1 ^ 2 + (M.1 0 0 - M.1 1 1) * (g : M2) 1 0 * (g : M2) 1 1 -
        M.1 0 1 * (g : M2) 1 0 ^ 2 := by
    linear_combination -((g : M2) 1 1 * e10) + (g : M2) 1 0 * e11
  have hpos := det_pos_aux _ _ _ _ _ _ _ _ _ _ _ ht hd hlt hc hc' hrs hid
  rcases hdg with h1 | h1
  · exact h1
  · linarith

/-! ### Matrices and forms -/

/-- `M = [[a, b], [c, d]] ↦ (c, d − a, −b)`, i.e. `f_M(x, y) = det((x, y)ᵀ, M (x, y)ᵀ)`. -/
def formOfMat (M : M2) : QF := ⟨M 1 0, M 1 1 - M 0 0, -M 0 1⟩

lemma disc_formOfMat (M : M2) : (formOfMat M).disc = M.trace ^ 2 - 4 * M.det := by
  simp only [formOfMat, QF.disc, trace_two, det_fin_two]; ring

/-- A matrix in `TrDet t q` is determined by its form. -/
lemma TrDet.ext_of_form {t q : ℤ} {M M' : TrDet t q} (h : formOfMat M.1 = formOfMat M'.1) :
    M = M' := by
  have ha := congrArg QF.a h
  have hb := congrArg QF.b h
  have hc := congrArg QF.c h
  simp only [formOfMat] at ha hb hc
  have ht := M.2.1
  have ht' := M'.2.1
  rw [trace_two] at ht ht'
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;> omega

variable {N : ℕ} {t q : ℤ}

lemma two_dvd_sub (hN : (N : ℤ) = 4 * q - t ^ 2) (f : Form N) : (2 : ℤ) ∣ t - f.1.b := by
  have hd := f.2.1
  unfold QF.disc at hd
  have hev : Even ((t - f.1.b) * (t + f.1.b)) :=
    ⟨2 * (q - f.1.a * f.1.c), by linear_combination (-1 : ℤ) * hd + hN⟩
  rcases Int.even_mul.mp hev with h | h
  · exact even_iff_two_dvd.mp h
  · have : t - f.1.b = (t + f.1.b) - 2 * f.1.b := by ring
    rw [this]
    exact dvd_sub (even_iff_two_dvd.mp h) (dvd_mul_right 2 _)

/-- The matrix `[[k, −c], [a, k + b]]`, `k = (t − b)/2`, of a form `(a, b, c)`. -/
def psiMat (t : ℤ) (f : QF) : M2 := !![(t - f.b) / 2, -f.c; f.a, (t - f.b) / 2 + f.b]

lemma formOfMat_psiMat (t : ℤ) (f : QF) : formOfMat (psiMat t f) = f := by
  simp only [formOfMat, psiMat]
  ext <;> simp

/-- The matrix of a positive definite form of discriminant `t² − 4q`. -/
def psi (hN : (N : ℤ) = 4 * q - t ^ 2) (f : Form N) : TrDet t q :=
  ⟨psiMat t f.1, by
    obtain ⟨k, hk⟩ := two_dvd_sub hN f
    have hk' : (t - f.1.b) / 2 = k := by rw [hk]; simp
    rw [trace_two]; simp only [psiMat, hk']; simp; linarith, by
    obtain ⟨k, hk⟩ := two_dvd_sub hN f
    have hk' : (t - f.1.b) / 2 = k := by rw [hk]; simp
    have hd := f.2.1
    unfold QF.disc at hd
    rw [det_fin_two]; simp only [psiMat, hk']; simp
    have h4 : 4 * (k * (k + f.1.b) + f.1.c * f.1.a) = 4 * q := by
      have ht : t = 2 * k + f.1.b := by linarith
      subst ht
      linear_combination hN - hd
    linarith⟩

lemma formOfMat_psi (hN : (N : ℤ) = 4 * q - t ^ 2) (f : Form N) :
    formOfMat (psi hN f).1 = f.1 :=
  formOfMat_psiMat t f.1

lemma psi_injective (hN : (N : ℤ) = 4 * q - t ^ 2) : Function.Injective (psi hN) := by
  intro f f' h
  apply Subtype.ext
  rw [← formOfMat_psi hN f, ← formOfMat_psi hN f', h]

lemma psi_entry10 (hN : (N : ℤ) = 4 * q - t ^ 2) (f : Form N) : (psi hN f).1 1 0 = f.1.a := by
  simp [psi, psiMat]

/-- `γ ↦ (γᵀ)⁻¹`, `SL₂(ℤ) → GL₂(ℤ)`, written out entrywise. -/
def theta (γ : SL(2, ℤ)) : GL2 where
  val := !![γ 1 1, -γ 1 0; -γ 0 1, γ 0 0]
  inv := !![γ 0 0, γ 1 0; γ 0 1, γ 1 1]
  val_inv := by
    have := det_entries γ
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;>
      linarith
  inv_val := by
    have := det_entries γ
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;>
      linarith

lemma theta_val (γ : SL(2, ℤ)) :
    ((theta γ : GL2) : M2) = !![γ 1 1, -γ 1 0; -γ 0 1, γ 0 0] := rfl

lemma theta_inv_val (γ : SL(2, ℤ)) :
    (↑(theta γ)⁻¹ : M2) = !![γ 0 0, γ 1 0; γ 0 1, γ 1 1] := rfl

lemma theta_injective : Function.Injective theta := by
  intro γ δ h
  have h' := congrArg (fun g : GL2 => (g : M2)) h
  simp only [theta_val] at h'
  ext i j
  have e00 := congrFun (congrFun h' 1) 1
  have e01 := congrFun (congrFun h' 1) 0
  have e10 := congrFun (congrFun h' 0) 1
  have e11 := congrFun (congrFun h' 0) 0
  simp at e00 e01 e10 e11
  fin_cases i <;> fin_cases j <;> simp <;> assumption

/-- **Equivariance**: `f_{θγ · M · (θγ)⁻¹} = γ • f_M`. -/
lemma formOfMat_theta_smul (γ : SL(2, ℤ)) (M : TrDet t q) :
    formOfMat (theta γ • M).1 = γ • formOfMat M.1 := by
  rw [smul_val, theta_val, theta_inv_val, smul_def, Matrix.eta_fin_two M.1]
  simp only [formOfMat, QF.act, QF.eval, Matrix.mul_fin_two]
  ext <;> simp <;> ring

lemma psi_smul (hN : (N : ℤ) = 4 * q - t ^ 2) (γ : SL(2, ℤ)) (f : Form N) :
    psi hN (γ • f) = theta γ • psi hN f := by
  apply TrDet.ext_of_form
  rw [formOfMat_theta_smul, formOfMat_psi, formOfMat_psi]
  rfl

/-- A `det = 1` unit is `theta` of an `SL₂(ℤ)` element. -/
lemma exists_theta_eq (g : GL2) (hg : (g : M2).det = 1) : ∃ γ : SL(2, ℤ), theta γ = g := by
  refine ⟨⟨!![(g : M2) 1 1, -(g : M2) 1 0; -(g : M2) 0 1, (g : M2) 0 0], ?_⟩, ?_⟩
  · rw [det_fin_two] at hg ⊢; simp; linarith
  · apply Units.ext
    ext i j; fin_cases i <;> fin_cases j <;> simp [theta]

/-! ### Orbits and stabilizers -/

/-- The positive definite form of a matrix with positive lower-left entry. -/
def formOfTrDet (hN : (N : ℤ) = 4 * q - t ^ 2) (hlt : t ^ 2 < 4 * q) (M : TrDet t q)
    (hM : 0 < M.1 1 0) : Form N :=
  ⟨formOfMat M.1, by rw [disc_formOfMat, M.2.1, M.2.2]; linarith,
    by rw [disc_formOfMat, M.2.1, M.2.2]; linarith, by simpa [formOfMat] using hM⟩

lemma psi_formOfTrDet (hN : (N : ℤ) = 4 * q - t ^ 2) (hlt : t ^ 2 < 4 * q) (M : TrDet t q)
    (hM : 0 < M.1 1 0) : psi hN (formOfTrDet hN hlt M hM) = M :=
  TrDet.ext_of_form (formOfMat_psi hN _)

/-- Every matrix class contains `psi f` for a positive definite form `f`. -/
lemma exists_psi_mem_orbit (hN : (N : ℤ) = 4 * q - t ^ 2) (hlt : t ^ 2 < 4 * q)
    (M : TrDet t q) : ∃ f : Form N, ∃ g : GL2, g • psi hN f = M := by
  rcases lt_or_gt_of_ne (entry10_ne_zero hlt M) with hneg | hpos
  · -- conjugate by `ε = diag(1, −1)`
    let ε : GL2 := ⟨!![1, 0; 0, -1], !![1, 0; 0, -1], by
      ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two], by
      ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]⟩
    have hε : 0 < (ε • M).1 1 0 := by
      change 0 < (!![1, 0; 0, -1] * M.1 * !![1, 0; 0, -1] : M2) 1 0
      rw [Matrix.eta_fin_two M.1]
      simp
      linarith
    refine ⟨formOfTrDet hN hlt (ε • M) hε, ε⁻¹, ?_⟩
    rw [psi_formOfTrDet, inv_smul_smul]
  · exact ⟨formOfTrDet hN hlt M hpos, 1, by rw [one_smul, psi_formOfTrDet]⟩

lemma card_stabilizer_smul_GL (g : GL2) (M : TrDet t q) :
    Nat.card (stabilizer GL2 (g • M)) = Nat.card (stabilizer GL2 M) := by
  rw [stabilizer_smul_eq_stabilizer_map_conj]
  exact Subgroup.card_map_of_injective (MulAut.conj g).injective

/-- Stabilizers match: `Stab_{GL₂(ℤ)}(psi f) ≅ Stab_{SL₂(ℤ)}(f)` via `theta`. -/
lemma card_stabilizer_psi (hN : (N : ℤ) = 4 * q - t ^ 2) (hlt : t ^ 2 < 4 * q) (f : Form N) :
    Nat.card (stabilizer GL2 (psi hN f)) = Nat.card (stabilizer SL(2, ℤ) f) := by
  symm
  refine Nat.card_congr (Equiv.ofBijective
    (fun γ => ⟨theta γ.1, by
      rw [mem_stabilizer_iff, ← psi_smul, (mem_stabilizer_iff.mp γ.2)]⟩) ⟨?_, ?_⟩)
  · intro γ δ h
    exact Subtype.ext (theta_injective (congrArg Subtype.val h))
  · rintro ⟨g, hg⟩
    have hpos : 0 < (psi hN f).1 1 0 := by rw [psi_entry10]; exact f.2.2.2
    have hdet := det_eq_one_of_conj hlt g _ _ hpos hpos (mem_stabilizer_iff.mp hg)
    obtain ⟨γ, rfl⟩ := exists_theta_eq g hdet
    refine ⟨⟨γ, ?_⟩, rfl⟩
    rw [mem_stabilizer_iff]
    apply psi_injective hN
    rw [psi_smul]
    exact mem_stabilizer_iff.mp hg

/-- The map on orbit spaces `SL₂(ℤ) \ Form N → GL₂(ℤ) \ TrDet t q`. -/
def classMap (hN : (N : ℤ) = 4 * q - t ^ 2) :
    Classes N → orbitRel.Quotient GL2 (TrDet t q) :=
  Quotient.map' (psi hN) (by
    rintro f f' ⟨γ, rfl⟩
    exact ⟨theta γ, (psi_smul hN γ f').symm⟩)

lemma classMap_mk (hN : (N : ℤ) = 4 * q - t ^ 2) (f : Form N) :
    classMap hN (Quotient.mk'' f) = Quotient.mk'' (psi hN f) := rfl

theorem classMap_bijective (hN : (N : ℤ) = 4 * q - t ^ 2) (hlt : t ^ 2 < 4 * q) :
    Function.Bijective (classMap hN) := by
  constructor
  · intro O O'
    induction O using Quotient.inductionOn' with | h f => ?_
    induction O' using Quotient.inductionOn' with | h f' => ?_
    intro h
    rw [classMap_mk, classMap_mk] at h
    obtain ⟨g, hg⟩ := Quotient.exact' h
    -- `hg : g • psi f' = psi f`
    have hdet := det_eq_one_of_conj hlt g _ _ (by rw [psi_entry10]; exact f'.2.2.2)
      (by rw [psi_entry10]; exact f.2.2.2) hg
    obtain ⟨γ, rfl⟩ := exists_theta_eq g hdet
    apply Quotient.sound'
    refine ⟨γ, psi_injective hN ?_⟩
    rw [psi_smul]
    exact hg
  · intro O
    induction O using Quotient.inductionOn' with | h M => ?_
    obtain ⟨f, g, hg⟩ := exists_psi_mem_orbit hN hlt M
    refine ⟨Quotient.mk'' f, ?_⟩
    rw [classMap_mk]
    exact Quotient.sound' ⟨g⁻¹, by rw [← hg]; exact inv_smul_smul g _⟩

/-- **Matrix mass = Hurwitz orbit mass / 2.** -/
theorem matMass_eq_hurwitzOrbit (hN : (N : ℤ) = 4 * q - t ^ 2) (hlt : t ^ 2 < 4 * q) :
    matMass t q = hurwitzOrbit N / 2 := by
  unfold matMass hurwitzOrbit
  rw [← finsum_comp_equiv (Equiv.ofBijective _ (classMap_bijective hN hlt))]
  rw [show (∑ᶠ O : Classes N, (2 : ℚ) / Nat.card (stabilizer SL(2, ℤ) O.out)) / 2 =
      ∑ᶠ O : Classes N, (1 : ℚ) / Nat.card (stabilizer SL(2, ℤ) O.out) by
    rw [div_eq_mul_inv, mul_comm, ← smul_eq_mul, smul_finsum]
    congr 1; ext O; rw [smul_eq_mul]; ring]
  congr 1
  ext O
  induction O using Quotient.inductionOn' with | h f => ?_
  simp only [Equiv.ofBijective_apply]
  congr 2
  -- both representatives lie in the classes of `psi f` resp. `f`
  have h1 : (classMap hN (Quotient.mk'' f)).out ∈ orbit GL2 (psi hN f) := by
    rw [classMap_mk]
    exact Quotient.exact'
      (Quotient.out_eq' (Quotient.mk'' (psi hN f) : orbitRel.Quotient GL2 (TrDet t q)))
  have h2 : (Quotient.mk'' f : Classes N).out ∈ orbit SL(2, ℤ) f :=
    Quotient.exact' (Quotient.out_eq' (Quotient.mk'' f : Classes N))
  obtain ⟨g, hg⟩ := h1
  obtain ⟨γ, hγ⟩ := h2
  rw [← hg, card_stabilizer_smul_GL, card_stabilizer_psi hN hlt, ← hγ, card_stabilizer_smul]

/-- **D-ALG (headline).** For `t² < 4q`,
`Σ_{GL₂(ℤ)-classes of M, tr M = t, det M = q} 1/#C_{GL₂(ℤ)}(M) = H(4q − t²)/2`. -/
theorem matMass_eq_hurwitz (hlt : t ^ 2 < 4 * q) :
    matMass t q = hurwitz (4 * q - t ^ 2).toNat / 2 := by
  have hN : (((4 * q - t ^ 2).toNat : ℕ) : ℤ) = 4 * q - t ^ 2 := Int.toNat_of_nonneg (by linarith)
  have hpos : 0 < (4 * q - t ^ 2).toNat := by omega
  rw [matMass_eq_hurwitzOrbit hN hlt, hurwitz_eq_hurwitzOrbit hpos]

end RamanujanWeil.Arith.Deuring
