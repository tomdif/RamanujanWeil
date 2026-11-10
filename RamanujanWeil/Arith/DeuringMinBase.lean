import RamanujanWeil.Arith.DeuringMinBaseAlg
import RamanujanWeil.Arith.DeuringWModel

/-!
# A3-ord, G5: every ordinary isogeny class contains a curve with `End_π = ℤ[π]`

`docs/ARITH_DEURING_MINBASE.md`. This is the statement `ExistsMinimalBase K` of
`Arith/DeuringClassLattice.lean` (stated here verbatim as `existsMinimalBase`, so that this file
does not depend on the class-lattice assembly).

Proof. Take any `W₁` in the class `C` and any Jacobian site, with Frobenius `π` on `J = J_{W₁}`.

* `MinBase.exists_minimalOrder_gen`: `π = c + Nω` with `End_π(J) = ℤ[ω]` and
  `N² ∣ t² − 4q`. Since `p ∣ q` and `p ∤ t`, `p ∤ N`, so `N` is invertible in `K̄`.
* `MinBase.exists_minimalOrder_quotient`: a cyclic `π`-stable `Γ ⊆ J[N]` with
  `End_π(J/Γ) = ℤ[π_Γ]`.
* `WModel.weierstrassDescent` (unconditional): `(J/Γ, π_Γ) ≅ (J_{W,S}, π_S)` for an elliptic
  `W/𝔽_q` of the same trace and **every** site `S` of `W`; `MinimalOrder` transfers along this
  equivariant isomorphism (`minimalOrder_of_iso`).
* `W` is in `C`: `e ≫ s : J_W → J_{W₁}` is a nonzero equivariant homomorphism (an `IsogStep`).
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.MonObj

universe u

namespace RamanujanWeil.Arith.Deuring.MinBase

open RamanujanWeil.Arith.Deuring.Geom RamanujanWeil.Arith.Deuring.Geom.G7
  RamanujanWeil.Arith.Deuring.Dual2 RamanujanWeil.Arith.Deuring.G8
  RamanujanWeil.Arith.Deuring.G5 Stacks.Groupoids RamanujanWeil.Ihara
  RamanujanWeil.Arith.Deuring.Mult

variable {K : Type u} [Field K] [Fintype K]

/-- **A minimal base curve in a given class, from Weierstrass descent.** -/
theorem exists_minimalBase_of_descent (hD : WeierstrassDescent K) (t : ℤ)
    (hp : ¬ (ringChar K : ℤ) ∣ t) (hlt : t ^ 2 < 4 * (Nat.card K : ℤ)) (C : IsogClass K t) :
    ∃ W₀ : WeierstrassCurve K, IsogClassPred C W₀ ∧
      ∀ [W₀.IsElliptic] (S : Jac.JacSite W₀), MinimalOrder S.frobeniusJacobian.π := by
  classical
  obtain ⟨x, rfl⟩ := Quotient.exists_rep C
  obtain ⟨W₁, hΔ₁, ht₁⟩ := x
  haveI : W₁.IsElliptic := ⟨isUnit_iff_ne_zero.mpr hΔ₁⟩
  obtain ⟨S₁⟩ := Jac.nonempty_jacSite W₁
  set J := S₁.frobeniusJacobian with hJ
  have hA := J.dim_eq
  have hχ := J.charPoly_eq
  have hdisc : traceOfFrob W₁ ^ 2 < 4 * ((Nat.card K : ℕ) : ℤ) := by rw [ht₁]; exact hlt
  obtain ⟨N, c, ω, hω, -, hNdvd, -, hπω, hmin, hindω⟩ :=
    exists_minimalOrder_gen hA J.π (traceOfFrob W₁) (Nat.card K) hχ hdisc
  -- `N` is prime to `p`
  set p := ringChar K
  haveI : CharP K p := ringChar.charP K
  obtain ⟨m, hpp, hcard⟩ := FiniteField.card K p
  have hpq : (p : ℤ) ∣ (Nat.card K : ℤ) := by
    rw [Nat.card_eq_fintype_card, hcard]; push_cast; exact dvd_pow_self _ m.ne_zero
  have hNp : ¬ (p : ℤ) ∣ N := by
    intro h
    apply hp
    rw [ht₁] at hNdvd
    have h1 : (p : ℤ) ∣ t ^ 2 - 4 * (Nat.card K : ℤ) :=
      (dvd_pow h two_ne_zero).trans hNdvd
    have h2 : (p : ℤ) ∣ t ^ 2 := by
      have := h1.add (dvd_mul_of_dvd_right hpq 4)
      simpa using this
    exact (Nat.prime_iff_prime_int.mp hpp).dvd_of_dvd_pow h2
  haveI : CharP (AlgebraicClosure K) p :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective p
  have hN : IsUnit (N : AlgebraicClosure K) := by
    refine Ne.isUnit ?_
    rw [Ne, CharP.intCast_eq_zero_iff (AlgebraicClosure K) p]
    exact hNp
  have hN0 : N ≠ 0 := by rintro rfl; simp at hN
  -- the quotient and its descent
  obtain ⟨Γ, hfin, hπΓ, hkill, hminB⟩ :=
    exists_minimalOrder_quotient hA J.π ω hmin hindω c N hπω hN
  obtain ⟨G⟩ := nonempty_glue Γ
  have hminG := hminB G (GlueS.πB G J.π hπΓ) (GlueS.q_πB G J.π hπΓ)
  obtain ⟨W, hΔ, htrW, hS⟩ := hD W₁ S₁ Γ hfin hπΓ N hN hkill G (GlueS.πB G J.π hπΓ)
    inferInstance (GlueS.q_πB G J.π hπΓ)
  haveI hell : W.IsElliptic := ⟨isUnit_iff_ne_zero.mpr hΔ⟩
  refine ⟨W, ?_, ?_⟩
  · -- `W` lies in the class of `W₁`
    refine ⟨⟨hΔ, htrW.trans ht₁⟩, ?_⟩
    apply Quotient.sound
    refine Relation.EqvGen.rel _ _ ?_
    obtain ⟨S⟩ := Jac.nonempty_jacSite W
    obtain ⟨e, he, hcomm⟩ := hS S
    haveI := he
    set s := GlueS.sMap G N hkill
    refine Or.inr ⟨hell, inferInstance, S, S₁, Or.inl ⟨e.hom ≫ s, inferInstance, ?_, ?_⟩⟩
    · rw [Category.assoc, GlueS.sMap_π G _ hkill J.π hπΓ, ← Category.assoc, hcomm,
        Category.assoc]
    · intro h1
      have hs1 : s = 1 := by
        rw [← Category.id_comp s, ← e.inv_hom_id, Category.assoc, h1, MonObj.comp_one]
      apply zpow_id_ne_one hA N hN0
      rw [← GlueS.q_sMap G N hkill]
      change G.q ≫ s = 1
      rw [hs1, MonObj.comp_one]
  · intro _ S
    obtain ⟨e, he, hcomm⟩ := hS S
    exact minimalOrder_of_iso _ _ e he hcomm hminG

/-- **`ExistsMinimalBase K`** (the statement of `ClassLattice.ExistsMinimalBase`), given
Weierstrass descent. -/
theorem existsMinimalBase_of_descent (hD : WeierstrassDescent K) :
    ∀ t : ℤ, ¬ (ringChar K : ℤ) ∣ t → t ^ 2 < 4 * (Nat.card K : ℤ) → ∀ C : IsogClass K t,
      ∃ W₀ : WeierstrassCurve K, IsogClassPred C W₀ ∧
        ∀ [W₀.IsElliptic] (S : Jac.JacSite W₀), MinimalOrder S.frobeniusJacobian.π :=
  fun t hp hlt C => exists_minimalBase_of_descent hD t hp hlt C

variable (K) in
/-- **`ExistsMinimalBase K`, unconditionally**: every ordinary isogeny class over a finite field
contains a Weierstrass curve whose concrete Jacobian has `End_π = ℤ[π]`, for every site. -/
theorem existsMinimalBase :
    ∀ t : ℤ, ¬ (ringChar K : ℤ) ∣ t → t ^ 2 < 4 * (Nat.card K : ℤ) → ∀ C : IsogClass K t,
      ∃ W₀ : WeierstrassCurve K, IsogClassPred C W₀ ∧
        ∀ [W₀.IsElliptic] (S : Jac.JacSite W₀), MinimalOrder S.frobeniusJacobian.π :=
  existsMinimalBase_of_descent (WModel.weierstrassDescent K)

end RamanujanWeil.Arith.Deuring.MinBase
