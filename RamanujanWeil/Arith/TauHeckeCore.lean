import Mathlib.NumberTheory.ModularForms.LevelOne.DimensionFormula
import Mathlib.NumberTheory.ModularForms.QExpansion
import Mathlib.NumberTheory.ModularForms.Discriminant
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Analysis.Complex.LocallyUniformLimit

/-!
# Hecke `T_p`, part 1: the elementary invariance computation

Ported from `~/RamanujanTau/RamanujanTau/HeckeCore.lean` (toolchain v4.30) with only the
namespace changed (`RamanujanTau.Hecke` ↦ `RamanujanWeil.ArithPlan.TauHecke`) and the import
narrowed from `Mathlib`.

For `g : ℂ → ℂ` weight-`k` modular on the upper half plane and a prime `p`,
`T_p g (z) = p^{k−1} g(pz) + p⁻¹ Σ_{j<p} g((z+j)/p)` is again invariant under
`T : z ↦ z+1` and `S : z ↦ −1/z` (the latter via the involution `j ↦ −j⁻¹ mod p`).
-/


set_option autoImplicit false

namespace RamanujanWeil.ArithPlan.TauHecke
open Finset Complex

variable (k : ℤ) (g : ℂ → ℂ)

/-- weight-`k` modularity of `g` on the upper half plane, in matrix-entry form. -/
def IsModular : Prop :=
  ∀ a b c d : ℤ, a * d - b * c = 1 → ∀ z : ℂ, 0 < z.im →
    g ((a * z + b) / (c * z + d)) = ((c : ℂ) * z + d) ^ k * g z

/-- `T_p g(z) = p^{k−1} g(pz) + p⁻¹ Σ_{j<p} g((z+j)/p)`. -/
noncomputable def heckeFun (p : ℕ) (z : ℂ) : ℂ :=
  (p : ℂ) ^ (k - 1) * g (p * z) + (p : ℂ)⁻¹ * ∑ j ∈ range p, g ((z + j) / p)

variable {k g}

lemma IsModular.add_one (hg : IsModular k g) {z : ℂ} (hz : 0 < z.im) : g (z + 1) = g z := by
  have := hg 1 1 0 1 (by norm_num) z hz
  simpa using this

lemma IsModular.add_nat (hg : IsModular k g) {z : ℂ} (hz : 0 < z.im) (n : ℕ) : g (z + n) = g z := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.cast_succ, ← add_assoc, hg.add_one (by simpa using hz), ih]

lemma IsModular.neg_inv (hg : IsModular k g) {w : ℂ} (hw : 0 < w.im) : g (-1 / w) = w ^ k * g w := by
  have := hg 0 (-1) 1 0 (by norm_num) w hw
  simpa using this

lemma im_div_nat {j : ℕ} {z : ℂ} (hz : 0 < z.im) {p : ℕ} (hp : 0 < p) : 0 < ((z + (j : ℕ)) / p).im := by
  rw [div_natCast_im]; simp only [add_im, natCast_im, add_zero]; positivity

lemma im_nat_mul {z : ℂ} (hz : 0 < z.im) {p : ℕ} (hp : 0 < p) : 0 < ((p : ℂ) * z).im := by
  simp only [mul_im, natCast_re, natCast_im, zero_mul, add_zero]; positivity

/-- **`T`-invariance.** -/
theorem heckeFun_add_one (hg : IsModular k g) {p : ℕ} (hp : 0 < p) {z : ℂ} (hz : 0 < z.im) :
    heckeFun k g p (z + 1) = heckeFun k g p z := by
  unfold heckeFun
  have h1 : g (p * (z + 1)) = g (p * z) := by
    rw [mul_add, mul_one, hg.add_nat (im_nat_mul hz hp)]
  have h2 : ∑ j ∈ range p, g ((z + 1 + j) / p) = ∑ j ∈ range p, g ((z + j) / p) := by
    have e : ∀ j : ℕ, (z + 1 + j) / p = (z + ((j + 1 : ℕ) : ℂ)) / p := fun j => by push_cast; ring
    simp_rw [e]
    have hp' : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
    have hlast : g ((z + (p : ℕ)) / p) = g ((z + ((0 : ℕ) : ℂ)) / p) := by
      rw [show (z + (p : ℕ)) / p = (z + ((0 : ℕ) : ℂ)) / p + 1 by field_simp; push_cast; ring]
      exact hg.add_one (im_div_nat hz hp)
    obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
    rw [sum_range_succ (fun j => g ((z + ((j + 1 : ℕ) : ℂ)) / ((q + 1 : ℕ) : ℂ))), sum_range_succ', hlast]
  rw [h1, h2]

/-! ### `S`-invariance -/

section S
variable {p : ℕ} [hp : Fact p.Prime]

/-- the involution `j ↦ −j⁻¹ (mod p)`. -/
def σ (p : ℕ) (j : ℕ) : ℕ := (-((j : ZMod p)⁻¹)).val

lemma σ_cast (j : ℕ) : ((σ p j : ℕ) : ZMod p) = -((j : ZMod p)⁻¹) := ZMod.natCast_zmod_val _

lemma ne_zero_of_mem {j : ℕ} (hj : j ∈ Ico 1 p) : (j : ZMod p) ≠ 0 := by
  rw [mem_Ico] at hj
  rw [Ne, ZMod.natCast_eq_zero_iff]
  exact fun h => absurd (Nat.le_of_dvd (by omega) h) (by omega)

lemma σ_mem {j : ℕ} (hj : j ∈ Ico 1 p) : σ p j ∈ Ico 1 p := by
  rw [mem_Ico]
  refine ⟨Nat.one_le_iff_ne_zero.mpr fun h0 => ?_, ZMod.val_lt _⟩
  have := σ_cast (p := p) j
  rw [h0, Nat.cast_zero, eq_comm, neg_eq_zero, inv_eq_zero] at this
  exact ne_zero_of_mem hj this

lemma σ_σ {j : ℕ} (hj : j ∈ Ico 1 p) : σ p (σ p j) = j := by
  rw [σ, σ_cast, inv_neg, inv_inv, neg_neg, ZMod.val_natCast_of_lt (mem_Ico.mp hj).2]

lemma σ_dvd {j : ℕ} (hj : j ∈ Ico 1 p) : p ∣ j * σ p j + 1 := by
  rw [← ZMod.natCast_eq_zero_iff]
  push_cast
  rw [σ_cast, mul_neg, mul_inv_cancel₀ (ne_zero_of_mem hj), neg_add_cancel]

/-- the key matrix identity: `g((−1/z + j)/p) = z^k g((z + j')/p)`. -/
lemma translate_S (hg : IsModular k g) {j : ℕ} (hj : j ∈ Ico 1 p) {z : ℂ} (hz : 0 < z.im) :
    g ((-1 / z + j) / p) = z ^ k * g ((z + (σ p j : ℕ)) / p) := by
  obtain ⟨m, hm⟩ := σ_dvd hj
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have hz0 : z ≠ 0 := fun h => by simp [h] at hz
  have hdet : (j : ℤ) * (-(σ p j : ℤ)) - (-(m : ℤ)) * p = 1 := by
    have : ((j * σ p j + 1 : ℕ) : ℤ) = ((p * m : ℕ) : ℤ) := by rw [hm]
    push_cast at this; linarith
  have h := hg j (-m) p (-(σ p j)) hdet ((z + (σ p j : ℕ)) / p) (im_div_nat hz hp.out.pos)
  have hmC : ((j : ℂ) * (σ p j : ℕ) + 1) = p * m := by exact_mod_cast hm
  have e1 : ((p : ℤ) : ℂ) * ((z + (σ p j : ℕ)) / p) + ((-(σ p j : ℤ) : ℤ) : ℂ) = z := by
    push_cast; field_simp; ring
  have e2 : (((j : ℤ) : ℂ) * ((z + (σ p j : ℕ)) / p) + ((-(m : ℤ) : ℤ) : ℂ)) /
      (((p : ℤ) : ℂ) * ((z + (σ p j : ℕ)) / p) + ((-(σ p j : ℤ) : ℤ) : ℂ)) = (-1 / z + j) / p := by
    rw [e1]; push_cast; field_simp; linear_combination hmC
  rw [e2, e1] at h
  exact h

/-- **`S`-invariance**: `T_p g(−1/z) = z^k · T_p g(z)`. -/
theorem heckeFun_S (hg : IsModular k g) {z : ℂ} (hz : 0 < z.im) :
    heckeFun k g p (-1 / z) = z ^ k * heckeFun k g p z := by
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have hz0 : z ≠ 0 := fun h => by simp [h] at hz
  have hpos := hp.out.pos
  have hzp : 0 < (z / p).im := by simpa using im_div_nat (j := 0) hz hpos
  -- the `g(pz)`-type terms
  have hA : g (p * (-1 / z)) = (z / p) ^ k * g (z / p) := by
    rw [← hg.neg_inv hzp]; congr 1; field_simp
  have hB : g ((-1 / z + ((0 : ℕ) : ℂ)) / p) = (p * z) ^ k * g (p * z) := by
    rw [← hg.neg_inv (im_nat_mul hz hpos)]; congr 1; simp only [Nat.cast_zero, add_zero]; field_simp
  -- the remaining translates are permuted by `σ`
  have hC : ∑ j ∈ Ico 1 p, g ((-1 / z + j) / p) = z ^ k * ∑ j ∈ Ico 1 p, g ((z + j) / p) := by
    rw [mul_sum]
    refine sum_nbij' (σ p) (σ p) (fun j hj => σ_mem hj) (fun j hj => σ_mem hj) (fun j hj => σ_σ hj)
      (fun j hj => σ_σ hj) (fun j hj => translate_S hg hj hz)
  have split : ∀ F : ℕ → ℂ, ∑ j ∈ range p, F j = F 0 + ∑ j ∈ Ico 1 p, F j := fun F => by
    rw [range_eq_Ico, sum_eq_sum_Ico_succ_bot hpos]
  unfold heckeFun
  rw [split, split (fun j => g ((z + j) / p)), hA, hB, hC]
  simp only [Nat.cast_zero, add_zero]
  rw [div_zpow, mul_zpow]
  have hpk : (p : ℂ) ^ (k - 1) = (p : ℂ) ^ k * (p : ℂ)⁻¹ := by
    rw [zpow_sub₀ hp0, zpow_one, div_eq_mul_inv]
  rw [hpk]
  field_simp
  ring

end S

end RamanujanWeil.ArithPlan.TauHecke
