import RamanujanWeil.Arith.ESSupport

/-!
# A2 / ES-P6b: per-trace sums of `T̃ₙ` reduce to `H − E` (docs/ARITH_ES_PLAN.md, §2 P6)

For `f : M2 → ℚ` let `trSum n t f = Σ_{det M = n, tr M = t} f M` (a `finsum`). It is invariant
under `f ↦ f ∘ conjS` and `f ↦ f ∘ conjU` (conjugations preserve `det` and `tr`), and additive
on functions with finite determinant-`n` support (`FinDet n`).

Main result (Popa–Zagier, Lemma 4 ⇒ property (C) up to the class-number count):

* `trSum_ptC : trSum n t ptC = trSum n t regH − trSum n t regE`.

Proof: `T̃ = T₁ − T₂ − T₃ − T₄`, `T₁ = Y + H`, `T₂ = U²ZU − Z₃`, `Z = SXS + A₁`,
`X = B₁ + Z₃ + U²YU`, `E = A₁ + T₃ + B₁ + T₄`; the conjugates have the same per-trace sums.
-/

namespace RamanujanWeil.Arith.ES

open M2

/-- Determinant-`n` support of `f` is finite. -/
def FinDet (n : ℤ) (f : M2 → ℚ) : Prop := {M : M2 | M.det = n ∧ f M ≠ 0}.Finite

/-- Restriction of `f` to `det = n`, `tr = t`. -/
def slice (n t : ℤ) (f : M2 → ℚ) (M : M2) : ℚ := if M.det = n ∧ M.tr = t then f M else 0

/-- The per-trace sum `Σ_{det M = n, tr M = t} f M`. -/
noncomputable def trSum (n t : ℤ) (f : M2 → ℚ) : ℚ := ∑ᶠ M, slice n t f M

lemma finite_entBd (K : ℤ) : {M : M2 | EntBd K M}.Finite := by
  have h : ((Set.Icc (-K) K ×ˢ Set.Icc (-K) K) ×ˢ (Set.Icc (-K) K ×ˢ Set.Icc (-K) K)).Finite :=
    ((Set.finite_Icc _ _).prod (Set.finite_Icc _ _)).prod
      ((Set.finite_Icc _ _).prod (Set.finite_Icc _ _))
  refine (h.image fun x => (⟨x.1.1, x.1.2, x.2.1, x.2.2⟩ : M2)).subset ?_
  rintro ⟨a, b, c, d⟩ ⟨ha, hb, hc, hd⟩
  refine ⟨((a, b), (c, d)), ?_, rfl⟩
  simp only [Set.mem_prod, Set.mem_Icc]
  exact ⟨⟨abs_le.mp ha, abs_le.mp hb⟩, abs_le.mp hc, abs_le.mp hd⟩

lemma FinDet.of_bd {n : ℤ} {f : M2 → ℚ} (h : ∀ M, M.det = n → f M ≠ 0 → EntBd n M) :
    FinDet n f :=
  (finite_entBd n).subset fun M hM => h M hM.1 hM.2

lemma FinDet.add {n : ℤ} {f g : M2 → ℚ} (hf : FinDet n f) (hg : FinDet n g) :
    FinDet n (fun M => f M + g M) := by
  refine (hf.union hg).subset fun M hM => ?_
  by_contra hc
  simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_and, not_not] at hc
  exact hM.2 (by show f M + g M = 0; rw [hc.1 hM.1, hc.2 hM.1, add_zero])

lemma FinDet.sub {n : ℤ} {f g : M2 → ℚ} (hf : FinDet n f) (hg : FinDet n g) :
    FinDet n (fun M => f M - g M) := by
  refine (hf.union hg).subset fun M hM => ?_
  by_contra hc
  simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_and, not_not] at hc
  exact hM.2 (by show f M - g M = 0; rw [hc.1 hM.1, hc.2 hM.1, sub_zero])

lemma FinDet.congr {n : ℤ} {f g : M2 → ℚ} (hf : FinDet n f) (h : ∀ M, f M = g M) :
    FinDet n g := by
  have : f = g := funext h
  rwa [← this]

lemma FinDet.comp {n : ℤ} {f : M2 → ℚ} (hf : FinDet n f) (e : M2 ≃ M2)
    (he : ∀ M, (e M).det = M.det) : FinDet n (fun M => f (e M)) := by
  refine (hf.preimage e.injective.injOn).subset fun M hM => ?_
  exact ⟨by rw [he]; exact hM.1, hM.2⟩

lemma slice_support {n t : ℤ} {f : M2 → ℚ} (hf : FinDet n f) :
    (Function.support (slice n t f)).Finite :=
  hf.subset fun M hM => by
    simp only [Function.mem_support, slice] at hM
    split_ifs at hM with h
    · exact ⟨h.1, hM⟩
    · exact absurd rfl hM

lemma trSum_add {n t : ℤ} {f g : M2 → ℚ} (hf : FinDet n f) (hg : FinDet n g) :
    trSum n t (fun M => f M + g M) = trSum n t f + trSum n t g := by
  unfold trSum
  rw [← finsum_add_distrib (slice_support hf) (slice_support hg)]
  congr 1; funext M
  simp only [slice]; split_ifs <;> simp

lemma trSum_sub {n t : ℤ} {f g : M2 → ℚ} (hf : FinDet n f) (hg : FinDet n g) :
    trSum n t (fun M => f M - g M) = trSum n t f - trSum n t g := by
  unfold trSum
  rw [← finsum_sub_distrib (slice_support hf) (slice_support hg)]
  congr 1; funext M
  simp only [slice]; split_ifs <;> simp

lemma trSum_congr {n t : ℤ} {f g : M2 → ℚ} (h : ∀ M, f M = g M) :
    trSum n t f = trSum n t g := by
  rw [funext h]

lemma trSum_comp {n t : ℤ} (f : M2 → ℚ) (e : M2 ≃ M2) (hd : ∀ M, (e M).det = M.det)
    (ht : ∀ M, (e M).tr = M.tr) : trSum n t (fun M => f (e M)) = trSum n t f := by
  unfold trSum
  rw [← finsum_comp_equiv e (f := slice n t f)]
  congr 1; funext M
  simp only [slice, hd, ht]

lemma trSum_conjS {n t : ℤ} (f : M2 → ℚ) : trSum n t (fun M => f (conjS M)) = trSum n t f :=
  trSum_comp f conjSEquiv det_conjS tr_conjS

lemma trSum_conjU {n t : ℤ} (f : M2 → ℚ) : trSum n t (fun M => f (conjU M)) = trSum n t f :=
  trSum_comp f conjUEquiv det_conjU tr_conjU

/-! ### Finiteness of the regions -/

lemma fin_T1 (n : ℤ) : FinDet n regT1 := FinDet.of_bd fun _ h1 h2 => regT1_bd h1 h2
lemma fin_T2 (n : ℤ) : FinDet n regT2 := FinDet.of_bd fun _ h1 h2 => regT2_bd h1 h2
lemma fin_T3 (n : ℤ) : FinDet n regT3 := FinDet.of_bd fun _ h1 h2 => regT3_bd h1 h2
lemma fin_T4 (n : ℤ) : FinDet n regT4 := FinDet.of_bd fun _ h1 h2 => regT4_bd h1 h2
lemma fin_A1 (n : ℤ) : FinDet n regA1 := FinDet.of_bd fun _ h1 h2 => regA1_bd h1 h2
lemma fin_B1 (n : ℤ) : FinDet n regB1 := FinDet.of_bd fun _ h1 h2 => regB1_bd h1 h2
lemma fin_Z3 (n : ℤ) : FinDet n regZ3 := FinDet.of_bd fun _ h1 h2 => regZ3_bd h1 h2
lemma fin_Y (n : ℤ) : FinDet n regY := FinDet.of_bd fun _ h1 h2 => regY_bd h1 h2
lemma fin_H (n : ℤ) : FinDet n regH := FinDet.of_bd fun _ h1 h2 => regH_bd h1 h2

lemma fin_YU (n : ℤ) : FinDet n (fun M => regY (conjU M)) :=
  (fin_Y n).comp conjUEquiv det_conjU

lemma fin_X (n : ℤ) : FinDet n regX :=
  (((fin_B1 n).add (fin_Z3 n)).add (fin_YU n)).congr fun M => (regX_eq M).symm

lemma fin_XS (n : ℤ) : FinDet n (fun M => regX (conjS M)) :=
  (fin_X n).comp conjSEquiv det_conjS

lemma fin_Z (n : ℤ) : FinDet n regZ :=
  ((fin_XS n).add (fin_A1 n)).congr fun M => (regZ_eq M).symm

lemma fin_ZU (n : ℤ) : FinDet n (fun M => regZ (conjU M)) :=
  (fin_Z n).comp conjUEquiv det_conjU

lemma fin_E (n : ℤ) : FinDet n regE :=
  ((((fin_A1 n).add (fin_T3 n)).add (fin_B1 n)).add (fin_T4 n)).congr fun M => (regE_eq M).symm

lemma fin_ptC (n : ℤ) : FinDet n ptC := FinDet.of_bd fun _ h1 h2 => ptC_support h1 h2

/-! ### Lemma 4 at the level of per-trace sums -/

/-- **PZ Lemma 4, per trace**: `Σ_{tr = t} T̃ₙ = Σ_{tr = t} H − Σ_{tr = t} E`. -/
theorem trSum_ptC (n t : ℤ) : trSum n t ptC = trSum n t regH - trSum n t regE := by
  have h0 : trSum n t ptC = trSum n t regT1 - trSum n t regT2 - trSum n t regT3 -
      trSum n t regT4 := by
    rw [trSum_congr ptC_eq, trSum_sub (((fin_T1 n).sub (fin_T2 n)).sub (fin_T3 n)) (fin_T4 n),
      trSum_sub ((fin_T1 n).sub (fin_T2 n)) (fin_T3 n), trSum_sub (fin_T1 n) (fin_T2 n)]
  have h1 : trSum n t regT1 = trSum n t regY + trSum n t regH := by
    rw [trSum_congr regT1_eq, trSum_add (fin_Y n) (fin_H n)]
  have h2 : trSum n t regZ = trSum n t regZ3 + trSum n t regT2 := by
    rw [← trSum_conjU regZ, trSum_congr regZ_conjU, trSum_add (fin_Z3 n) (fin_T2 n)]
  have h3 : trSum n t regZ = trSum n t regX + trSum n t regA1 := by
    rw [trSum_congr regZ_eq, trSum_add (fin_XS n) (fin_A1 n), trSum_conjS regX]
  have h4 : trSum n t regX = trSum n t regB1 + trSum n t regZ3 + trSum n t regY := by
    rw [trSum_congr regX_eq, trSum_add ((fin_B1 n).add (fin_Z3 n)) (fin_YU n),
      trSum_add (fin_B1 n) (fin_Z3 n), trSum_conjU regY]
  have h5 : trSum n t regE = trSum n t regA1 + trSum n t regT3 + trSum n t regB1 +
      trSum n t regT4 := by
    rw [trSum_congr regE_eq, trSum_add (((fin_A1 n).add (fin_T3 n)).add (fin_B1 n)) (fin_T4 n),
      trSum_add ((fin_A1 n).add (fin_T3 n)) (fin_B1 n), trSum_add (fin_A1 n) (fin_T3 n)]
  linarith

end RamanujanWeil.Arith.ES
