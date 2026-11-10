import RamanujanWeil.Arith.DeuringG7DGapsTransl

/-!
# A3-ord, G7-D-gaps (the divisor bridge): `RRStabilizerBridge W N` for `N ≥ 2`, proved

`docs/ARITH_DEURING_G7DGAPS.md` §3. For `Q = (x₀, y₀) ≠ O`, put `V = L(N·O)` and `τ = τ_{−Q}`.

**`rrStabilizerBridge`** (`2 ≤ N`): `−Q ∈ K(V)` iff `m_Q^N` is principal.

* (⇐) Let `m_Q^N = (r)`. Then `vR r = e^N` (`vR_of_pow_eq_span`), and `τ V ⊆ m_Q^{−N}` with
  `τ V` regular at `O` (`trans_rr_mem`, `vK_trans_rr_le_one`). So `r · τ V ⊆ R` has pole order
  `≤ N` at `O`, i.e. `r · τ V ⊆ L(N·O) = V` (`rrSpace_eq_LN`). Both sides have the same dimension,
  so `(r, −Q) ∈ 𝒢(V)`.
* (⇒) Let `f · τ V = V`. Then `f = f · τ 1 ∈ V ⊆ R`, `f⁻¹ ∈ τ V ⊆ m_Q^{−N}` (from `1 ∈ V`), so
  `m_Q^N ≤ (f)`. Also `vR f ≥ e^N`, because some `w ∈ V` has `vK w = e^N` (`exists_rr_exact`; here
  `N ≥ 2` is used) and `vK (τ v) ≤ 1`. Then `m_Q^N = (f)` by `pow_eq_span_of_le`.

(For `N = 1` the statement is false: `L(O) = F` is stabilized by every translation.)
-/

noncomputable section

namespace RamanujanWeil.Arith.Deuring.Geom.G7.DGeom

open WeierstrassCurve WeierstrassCurve.Affine Polynomial
open scoped nonZeroDivisors Polynomial.Bivariate

universe u

set_option linter.unusedSectionVars false

open scoped Classical

variable {F : Type u} [Field F] (W : Affine F) [W.IsElliptic] [DecidableEq F]

local notation "FI" => FractionalIdeal (Rg W)⁰ (Kf W)

/-- **A function in `L(N·O)` with a pole of order exactly `N`** (`N ≥ 2`): `x^k` or `x^k y`. -/
theorem exists_rr_exact {N : ℕ} (hN : 2 ≤ N) :
    ∃ w ∈ rrSpace W N, vK W w = WithZero.exp (N : ℤ) := by
  rcases Nat.even_or_odd N with ⟨k, hk⟩ | ⟨k, hk⟩
  · refine ⟨genX W ^ k, Submodule.subset_span (Or.inl ⟨k, by change 2 * k ≤ N; omega, rfl⟩), ?_⟩
    rw [map_pow, vK_genX, ← WithZero.exp_nsmul, nsmul_eq_mul]
    congr 1; omega
  · obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
    refine ⟨genX W ^ m * genY W, Submodule.subset_span (Or.inr ⟨m, by
      change 2 * m + 3 ≤ N; omega, rfl⟩), ?_⟩
    rw [map_mul, map_pow, vK_genX, vK_genY, ← WithZero.exp_nsmul, ← WithZero.exp_add,
      nsmul_eq_mul]
    congr 1; omega

theorem rrGens_finite' (N : ℕ) : (rrGens W N).Finite := by
  refine Set.Finite.union (Set.Finite.image _ ?_) (Set.Finite.image _ ?_)
  · exact (Set.finite_Iic N).subset fun i (hi : 2 * i ≤ N) => (by simp; omega)
  · exact (Set.finite_Iic N).subset fun i (hi : 2 * i + 3 ≤ N) => (by simp; omega)

instance finiteDimensional_rrSpace' (N : ℕ) : FiniteDimensional F (rrSpace W N) :=
  FiniteDimensional.span_of_finite F (rrGens_finite' W N)

theorem one_mem_rrSpace' (N : ℕ) : (1 : Kf W) ∈ rrSpace W N :=
  Submodule.subset_span (Or.inl ⟨0, by simp, by simp⟩)

theorem coe_uQ_pow {x₀ y₀ : F} (h : (W⁄F).Nonsingular x₀ y₀) (N : ℕ) :
    (((CoordinateRing.XYIdeal' h ^ N : FIˣ) : FI)) =
      ((CoordinateRing.XYIdeal (W⁄F) x₀ (C y₀) ^ N : Ideal (Rg W)) : FI) := by
  rw [Units.val_pow_eq_pow_val, CoordinateRing.XYIdeal'_eq, FractionalIdeal.coeIdeal_pow]

theorem Jinv_pow_mul_uQ_pow {x₀ y₀ : F} (h : (W⁄F).Nonsingular x₀ y₀) (N : ℕ) :
    Jinv W h ^ N * (CoordinateRing.XYIdeal' h : FI) ^ N = 1 := by
  rw [← mul_pow, Jinv, uQ, Units.inv_mul, one_pow]

/-- `(f, P) ↦ f · τ_P` on the stabilizer, for `P = −Q`. -/
theorem thetaAct_mk {x₀ y₀ : F} (h : (W⁄F).Nonsingular x₀ y₀) (u : (Kf W)ˣ) (v : Kf W) :
    thetaAct W (⟨u, Multiplicative.ofAdd (-(Point.some x₀ y₀ h))⟩ : Amb W) v =
      (u : Kf W) * trans W (-(Point.some x₀ y₀ h)) v := rfl

/-- **The divisor bridge, for `N ≥ 2`** (`RRStabilizerBridge`). -/
theorem rrStabilizerBridge {N : ℕ} (hN : 2 ≤ N) : RRStabilizerBridge W N := by
  intro x₀ y₀ h
  have hinjK := IsFractionRing.injective (Rg W) (Kf W)
  constructor
  · -- (⇒)
    rintro ⟨g, hg, hgr⟩
    rw [mem_thetaGroup] at hg
    set f : Kf W := ((g.left : (Kf W)ˣ) : Kf W) with hfdef
    have hact : ∀ v, thetaAct W g v = f * trans W (-(Point.some x₀ y₀ h)) v := by
      intro v; rw [thetaAct_apply, hgr]; rfl
    have hmap : ∀ v ∈ rrSpace W N, f * trans W (-(Point.some x₀ y₀ h)) v ∈ rrSpace W N := by
      intro v hv
      rw [← hact, ← hg]
      exact Submodule.mem_map_of_mem hv
    have hpre : ∀ w ∈ rrSpace W N, ∃ v ∈ rrSpace W N,
        f * trans W (-(Point.some x₀ y₀ h)) v = w := by
      intro w hw
      rw [← hg] at hw
      obtain ⟨v, hv, rfl⟩ := hw
      exact ⟨v, hv, (hact v).symm⟩
    have hfV : f ∈ rrSpace W N := by
      have := hmap 1 (one_mem_rrSpace' W N)
      rwa [map_one, mul_one] at this
    rw [rrSpace_eq_LN] at hfV
    obtain ⟨r, hrf, -⟩ := hfV
    have hf0 : f ≠ 0 := (g.left).ne_zero
    have hr0 : r ≠ 0 := by rintro rfl; rw [map_zero] at hrf; exact hf0 hrf.symm
    obtain ⟨v0, hv0, e0⟩ := hpre 1 (one_mem_rrSpace' W N)
    obtain ⟨w, hw, hwv⟩ := exists_rr_exact W hN
    obtain ⟨v1, hv1, e1⟩ := hpre w hw
    have hv : WithZero.exp (N : ℤ) ≤ vR W r := by
      rw [← hwv, ← e1, map_mul, ← hrf, vK_algebraMap]
      calc vR W r * vK W (trans W (-(Point.some x₀ y₀ h)) v1) ≤ vR W r * 1 :=
            mul_le_mul_right (vK_trans_rr_le_one W h hv1) _
        _ = vR W r := mul_one _
    have hle : CoordinateRing.XYIdeal (W⁄F) x₀ (C y₀) ^ N ≤ Ideal.span {r} := by
      intro a ha
      have ha' : algebraMap (Rg W) (Kf W) a ∈ (CoordinateRing.XYIdeal' h : FI) ^ N := by
        rw [← Units.val_pow_eq_pow_val, coe_uQ_pow, FractionalIdeal.mem_coeIdeal]
        exact ⟨a, ha, rfl⟩
      have hm := FractionalIdeal.mul_mem_mul (trans_rr_mem W h hv0) ha'
      rw [Jinv_pow_mul_uQ_pow, FractionalIdeal.mem_one_iff] at hm
      obtain ⟨s, hs⟩ := hm
      have : algebraMap (Rg W) (Kf W) a = algebraMap (Rg W) (Kf W) (r * s) := by
        rw [map_mul, hrf, hs, ← mul_assoc, e0, one_mul]
      rw [hinjK this]
      exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self r)
    have heq := pow_eq_span_of_le W h hr0 hle hv
    refine ⟨⟨algebraMap (Rg W) (Kf W) r, ?_⟩⟩
    rw [coe_uQ_pow, heq, FractionalIdeal.coeIdeal_span_singleton,
      FractionalIdeal.coe_spanSingleton]
  · -- (⇐)
    rintro ⟨⟨g, hg⟩⟩
    rw [coe_uQ_pow] at hg
    have hgm : g ∈ ((CoordinateRing.XYIdeal (W⁄F) x₀ (C y₀) ^ N : Ideal (Rg W)) : FI) := by
      rw [← FractionalIdeal.mem_coe, hg]; exact Submodule.mem_span_singleton_self g
    obtain ⟨r, hr, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 hgm
    have hspan : CoordinateRing.XYIdeal (W⁄F) x₀ (C y₀) ^ N = Ideal.span {r} := by
      apply (FractionalIdeal.coeIdeal_inj (K := Kf W)).1
      apply FractionalIdeal.coeToSubmodule_inj.1
      rw [hg, FractionalIdeal.coeIdeal_span_singleton, FractionalIdeal.coe_spanSingleton]
    obtain ⟨hr0, hvr⟩ := vR_of_pow_eq_span W h hspan
    have hf0 : algebraMap (Rg W) (Kf W) r ≠ 0 := by
      intro e; exact hr0 (hinjK (e.trans (map_zero (algebraMap (Rg W) (Kf W))).symm))
    set u : (Kf W)ˣ := Units.mk0 _ hf0
    let g' : Amb W := ⟨u, Multiplicative.ofAdd (-(Point.some x₀ y₀ h))⟩
    have hinj : Function.Injective (thetaAct W g') := by
      intro a b hab
      rw [thetaAct_mk, thetaAct_mk] at hab
      exact (trans W _).toRingHom.injective (mul_left_cancel₀ hf0 hab)
    refine ⟨g', ?_, rfl⟩
    rw [mem_thetaGroup]
    refine Submodule.eq_of_le_of_finrank_eq ?_
      (LinearEquiv.finrank_eq (Submodule.equivMapOfInjective _ hinj _)).symm
    rintro _ ⟨v, hv, rfl⟩
    rw [thetaAct_mk, rrSpace_eq_LN]
    have hf : algebraMap (Rg W) (Kf W) r ∈ (CoordinateRing.XYIdeal' h : FI) ^ N := by
      rw [← Units.val_pow_eq_pow_val, coe_uQ_pow, hspan, FractionalIdeal.mem_coeIdeal]
      exact ⟨r, Ideal.mem_span_singleton_self r, rfl⟩
    have hm := FractionalIdeal.mul_mem_mul (trans_rr_mem W h hv) hf
    rw [Jinv_pow_mul_uQ_pow, FractionalIdeal.mem_one_iff] at hm
    obtain ⟨s, hs⟩ := hm
    refine ⟨s, by rw [hs, mul_comm]; rfl, ?_⟩
    rw [← vK_algebraMap, hs, map_mul, vK_algebraMap, hvr]
    calc vK W (trans W (-(Point.some x₀ y₀ h)) v) * WithZero.exp (N : ℤ) ≤
        1 * WithZero.exp (N : ℤ) := mul_le_mul_left (vK_trans_rr_le_one W h hv) _
      _ = _ := one_mul _

end RamanujanWeil.Arith.Deuring.Geom.G7.DGeom
