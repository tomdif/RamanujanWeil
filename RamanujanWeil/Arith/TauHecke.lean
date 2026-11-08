import RamanujanWeil.Arith.TauHeckeOperator
import RamanujanWeil.Arith.TauHeckeBridge

/-!
# The Hecke recurrence for Ramanujan's `τ`

For every prime `p` and `r ≥ 1`:  `τ(p^{r+1}) = τ(p)τ(p^r) − p¹¹τ(p^{r−1})`.

Route (ported from `~/RamanujanTau`, `HeckeEigenform` / `HeckeOperator` / `HeckeQExp`):
* `T_p = heckeLin p` is a ℂ-linear endomorphism of `CuspForm 𝒮ℒ 12` with
  `(T_p f)_m = f_{pm} + p¹¹[p ∣ m] f_{m/p}` (`TauHeckeOperator`);
* `dim S₁₂ = 1` (Mathlib, `CuspForm.exists_smul_discriminant_of_weight_eq_twelve`) ⇒
  `T_p Δ = c • Δ`; coefficient `1` gives `c = τ(p)` (since `qExpansion(Δ)_n = τ(n)`,
  `TauHeckeBridge`);
* coefficient `n` gives the master identity `τ(p)τ(n) = τ(pn) + p¹¹[p ∣ n]τ(n/p)`, and
  `n = p^r` gives the recurrence.
-/

set_option autoImplicit false

namespace RamanujanWeil.ArithPlan

open ModularForm UpperHalfPlane TauHecke TauHeckeBridge
open scoped MatrixGroups

/-- The Hecke recurrence for `τ` at the prime `p` (frozen statement). -/
def TauHeckeRecurrence (p : ℕ) : Prop :=
  ∀ r : ℕ, 1 ≤ r → RamanujanTau.tau (p ^ (r + 1)) =
    RamanujanTau.tau p * RamanujanTau.tau (p ^ r) - (p : ℤ) ^ 11 * RamanujanTau.tau (p ^ (r - 1))

/-- `qExpansion` coefficients are ℂ-linear in the cusp form. -/
lemma qExpansion_coeff_smul (c : ℂ) (f : CuspForm 𝒮ℒ 12) (n : ℕ) :
    (qExpansion 1 ((c • f : CuspForm 𝒮ℒ 12) : ℍ → ℂ)).coeff n = c * (qExpansion 1 (f : ℍ → ℂ)).coeff n := by
  have h := qExpansion_smul
    (ModularFormClass.analyticAt_cuspFunction_zero f one_pos one_mem_strictPeriods_SL) c
  rw [show ((c • f : CuspForm 𝒮ℒ 12) : ℍ → ℂ) = c • (f : ℍ → ℂ) from rfl, h]
  simp

/-- **Mordell's master identity**: `τ(p)τ(n) = τ(pn) + p¹¹[p ∣ n]τ(n/p)` for every prime `p`. -/
theorem tau_master {p : ℕ} (hp : p.Prime) (n : ℕ) :
    RamanujanTau.tau p * RamanujanTau.tau n =
      RamanujanTau.tau (p * n) + (if p ∣ n then (p : ℤ) ^ 11 * RamanujanTau.tau (n / p) else 0) := by
  have := Fact.mk hp
  -- one-dimensionality: `T_p Δ = c • Δ`
  obtain ⟨c, hc⟩ :=
    CuspForm.exists_smul_discriminant_of_weight_eq_twelve (heckeLin p CuspForm.discriminant)
  have hT : ∀ m, (qExpansion 1 ((heckeLin p CuspForm.discriminant : CuspForm 𝒮ℒ 12) : ℍ → ℂ)).coeff m
      = (RamanujanTau.tau (p * m) : ℂ) +
        (p : ℂ) ^ (11 : ℕ) * (if p ∣ m then (RamanujanTau.tau (m / p) : ℂ) else 0) := by
    intro m
    rw [show (heckeLin p CuspForm.discriminant) = heckeCusp p CuspForm.discriminant from rfl,
      qExpansion_hecke, qExpansion_discriminant_coeff, qExpansion_discriminant_coeff]
    norm_num
  have hE : ∀ m, (qExpansion 1 ((heckeLin p CuspForm.discriminant : CuspForm 𝒮ℒ 12) : ℍ → ℂ)).coeff m
      = c * (RamanujanTau.tau m : ℂ) := by
    intro m; rw [← hc, qExpansion_coeff_smul, qExpansion_discriminant_coeff]
  have hp1 : ¬ p ∣ 1 := fun h => hp.ne_one (Nat.dvd_one.mp h)
  have hcval : c = (RamanujanTau.tau p : ℂ) := by
    have e := (hE 1).symm.trans (hT 1)
    simpa [RamanujanTau.tau_one, hp1] using e
  have en := (hE n).symm.trans (hT n)
  rw [hcval] at en
  by_cases hpn : p ∣ n
  · rw [if_pos hpn] at en ⊢; exact_mod_cast en
  · rw [if_neg hpn, add_zero] at ⊢; simp only [if_neg hpn, mul_zero, add_zero] at en
    exact_mod_cast en

/-- **The Hecke recurrence for `τ`**, at every prime `p`. -/
theorem tauHeckeRecurrence (p : ℕ) (hp : p.Prime) : TauHeckeRecurrence p := by
  intro r hr
  have h := tau_master hp (p ^ r)
  have hdvd : p ∣ p ^ r := dvd_pow_self p (by omega)
  have hdiv : p ^ r / p = p ^ (r - 1) := by
    obtain ⟨s, rfl⟩ : ∃ s, r = s + 1 := ⟨r - 1, by omega⟩
    rw [pow_succ, Nat.mul_div_cancel _ hp.pos, Nat.add_sub_cancel]
  rw [if_pos hdvd, hdiv, ← pow_succ'] at h
  rw [h]; ring

end RamanujanWeil.ArithPlan
