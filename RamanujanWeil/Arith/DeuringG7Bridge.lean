import RamanujanWeil.Arith.DeuringG7Tate
import RamanujanWeil.Arith.DeuringG7Alg
import RamanujanWeil.Arith.DeuringG2

/-!
# A3-ord, G7: Tate's theorem for Frobenius Jacobians, modulo `QuotientFiniteness`

For elliptic `W, W'` over `𝔽_q` with the **same trace** `t` (`t² < 4q`) and Frobenius Jacobians
`J, J'` (G2), `tate_exists_frobHom`: if `QuotientFiniteness (J × J') (π × π')` holds, then there is
a nontrivial `π`-equivariant homomorphism `J ⟶ J'` or `J' ⟶ J`, i.e. `E` and `E'` are
`𝔽_q`-isogenous.

Inputs: `π² − tπ + q = 0` on points (`frob_quadratic`, G2), `J[ℓⁿ] ≅ (ℤ/ℓⁿ)²` (Stacks), the prime
`ℓ` of `exists_prime_no_root` (automatically `ℓ ≠ p`), the equivariant isomorphisms of
`DeuringG7Alg`, and the gluing argument of `DeuringG7Tate`.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory
  CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

universe u

namespace RamanujanWeil.Arith.Deuring.Geom.G7

open Stacks.Groupoids

section Points

variable {k : Type u} [Field k] {G : Over (Spec (.of k))} [GrpObj G] [IsCommMonObj G]

/-- `R(α)` on points, for `R = X² − tX + q`. -/
theorem comp_endPolyEval_quadratic (α : G ⟶ G) [IsMonHom α] (t q : ℤ) (x : Pt G) :
    x ≫ endPolyEval α (Polynomial.X ^ 2 - Polynomial.C t * Polynomial.X + Polynomial.C q) =
      (x ≫ α ≫ α) / (x ≫ α) ^ t * x ^ q := by
  have hsub : ∀ R S : Polynomial ℤ, endPolyEval α (R - S) = endPolyEval α R / endPolyEval α S :=
    fun R S => by
      rw [eq_div_iff_mul_eq', ← endPolyEval_add, sub_add_cancel]
  rw [endPolyEval_add, hsub, pow_two, endPolyEval_mul, endPolyEval_mul, endPolyEval_X,
    endPolyEval_C, endPolyEval_C, MonObj.comp_mul, GrpObj.comp_div]
  simp only [GrpObj.comp_zpow, Category.comp_id]

end Points

section Bridge

variable {K : Type u} [Field K] [Fintype K]

/-- The prime `ℓ` of `exists_prime_no_root` is invertible in `𝔽̄_q`. -/
theorem isUnit_of_no_root (ℓ : ℕ) (hℓ : ℓ.Prime) (t : ℤ)
    (hroot : ∀ a : ZMod ℓ, a ^ 2 - (t : ZMod ℓ) * a + ((Nat.card K : ℤ) : ZMod ℓ) ≠ 0) :
    IsUnit (ℓ : AlgebraicClosure K) := by
  have hpK : CharP K (ringChar K) := ringChar.charP K
  obtain ⟨n, hp, hcard⟩ := FiniteField.card K (ringChar K)
  have hne : ℓ ≠ ringChar K := by
    intro h
    apply hroot 0
    have hd : ℓ ∣ Nat.card K := by
      rw [Nat.card_eq_fintype_card, hcard, h]; exact dvd_pow_self _ (PNat.ne_zero n)
    have : ((Nat.card K : ℤ) : ZMod ℓ) = 0 := by
      rw [Int.cast_natCast, ZMod.natCast_eq_zero_iff]; exact hd
    rw [this]; ring
  have hK : (ℓ : K) ≠ 0 := by
    rw [Ne, CharP.cast_eq_zero_iff K (ringChar K)]
    intro hd
    exact hne ((Nat.prime_dvd_prime_iff_eq hp hℓ).1 hd).symm
  rw [isUnit_iff_ne_zero]
  have : (algebraMap K (AlgebraicClosure K)) (ℓ : K) = ((ℓ : ℕ) : AlgebraicClosure K) :=
    map_natCast _ ℓ
  rw [← this]
  exact (map_ne_zero _).2 hK

open RamanujanWeil.Ihara in
/-- **G7 for elliptic curves over `𝔽_q`, modulo `QuotientFiniteness`.** Elliptic `W, W'` over
`𝔽_q` with the same trace `t`, `t² < 4q`, and Frobenius Jacobians `J, J'`: if the quotients of
`J × J'` satisfy `QuotientFiniteness`, there is a nontrivial `π`-equivariant homomorphism
`J ⟶ J'` or `J' ⟶ J`. -/
theorem tate_exists_frobHom {W W' : WeierstrassCurve K} [W.IsElliptic] [W'.IsElliptic]
    (J : FrobeniusJacobian W) (J' : FrobeniusJacobian W')
    (ht : traceOfFrob W' = traceOfFrob W) (hlt : traceOfFrob W ^ 2 < 4 * (Nat.card K : ℤ))
    (hfin : QuotientFiniteness (J.A ⊗ J'.A) (πA J.π J'.π)) :
    (∃ α : J.A ⟶ J'.A, IsMonHom α ∧ α ≫ J'.π = J.π ≫ α ∧ α ≠ 1) ∨
      (∃ β : J'.A ⟶ J.A, IsMonHom β ∧ β ≫ J.π = J'.π ≫ β ∧ β ≠ 1) := by
  set t := traceOfFrob W
  set q : ℤ := (Nat.card K : ℤ)
  obtain ⟨ℓ, hℓ, hroot⟩ := exists_prime_no_root t q hlt
  have hℓk := isUnit_of_no_root (K := K) ℓ hℓ t hroot
  -- the quadratic relation on torsion points
  have hrel : ∀ {V : WeierstrassCurve K} [V.IsElliptic] (I : FrobeniusJacobian V),
      traceOfFrob V = t → ∀ (N : ℕ) (x : Tor I.A N),
        torAct I.π N (torAct I.π N x) - t • torAct I.π N x + q • x = 0 := by
    intro V _ I hV N x
    apply pt_injective
    have h := congrArg (pt x ≫ ·) I.frob_quadratic
    simp only [MonObj.comp_one] at h
    rw [hV, comp_endPolyEval_quadratic] at h
    change pt x ≫ I.π ≫ I.π / (pt x ≫ I.π) ^ t * pt x ^ q = 1 at h
    change Additive.toMul (_ - _ + _) = (1 : Pt I.A)
    rw [toMul_add, toMul_sub, AddSubgroupClass.coe_zsmul, AddSubgroupClass.coe_zsmul, toMul_zsmul,
      toMul_zsmul]
    exact h
  have hu : ∀ n : ℕ, ∃ u : Tor J.A (ℓ ^ (n + 1)) ≃+ Tor J'.A (ℓ ^ (n + 1)),
      ∀ x, u (torAct J.π _ x) = torAct J'.π _ (u x) := by
    intro n
    obtain ⟨e⟩ := nonempty_torsionBy_pow_addEquiv J.A ℓ hℓk (n + 1)
    obtain ⟨e'⟩ := nonempty_torsionBy_pow_addEquiv J'.A ℓ hℓk (n + 1)
    rw [J.dim_eq] at e
    rw [J'.dim_eq] at e'
    exact exists_equivariant_addEquiv hℓ e e' (torAct J.π _) (torAct J'.π _) t q
      (hrel J rfl _) (hrel J' ht _) hroot
  choose u hu using hu
  exact exists_frobHom_of_quotientFiniteness ℓ u hu hℓ hℓk (by rw [J.dim_eq]; exact one_pos) hfin

end Bridge

end RamanujanWeil.Arith.Deuring.Geom.G7
