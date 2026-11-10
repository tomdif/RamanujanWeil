import RamanujanWeil.Arith.DeuringG5Cyclic

/-!
# A3-ord, G5: a quotient with `End_π = ℤ[π]` (over `k̄`)

`docs/ARITH_DEURING_MINBASE.md`. Setting: `k` algebraically closed, `A` a one-dimensional
abelian variety over `k`, `π ∈ End(A)` with characteristic polynomial `X² − tX + q`, `t² < 4q`.

1. **Integrality** (`coeffs`): if `E` commutes with `Ω` and `m E = a + bΩ`, the Cayley–Hamilton
   relations of `E` and `Ω` (`G8.postcompOf_sq`) give two integer equations
   (`a² − b² deg Ω − mσa + m² deg E = 0`, `2ab + b²τ − mσb = 0`, `σ = Tr E`, `τ = Tr Ω`).
2. **A monogenic generator of `End_π(A)`** (`exists_minimalOrder_gen`): there are `N > 0`, `c` and
   `ω ∈ End_π(A)` with `π = c + Nω`, `N² ∣ t² − 4q` and `End_π(A) = ℤ[ω]` (`MinimalOrder ω`).
   Take `N` maximal (`N² ∣ t² − 4q` bounds it). If `ℓ e = a + bω` with `ℓ` prime and
   `ℓ ∤ (a, b)`, integrality gives `ℓ ∣ b ⇒ ℓ ∣ a`, so `ℓ ∤ b`, and then
   `π = c' + Nℓ ω₁` with `ω₁ = v e + u ω` (`uℓ + vb = 1`), contradicting maximality.
   No `p`-adic or torsion-point argument is needed.
3. **The quotient** (`exists_minimalOrder_quotient`): with `N` invertible in `k`, let `Q`
   generate `A[N²]` over `ℤ[ω]/N²` (G5 `cyclicTorsion_of_minimalOrder` applied to `ω`),
   `P = N Q` and `Γ = ⟨P⟩` (cyclic of order `N`, `π`-stable since `π ≡ c` on `A[N]`). For any
   quotient `q : A → B = A/Γ` and `φ ∈ End_π(B)`, `φ̃ = q φ s ∈ End_π(A) = ℤ[ω]` sends `A[N]`
   and `Q` into `Γ`; this forces `φ̃ = x + yω` with `N ∣ x`, `N² ∣ y`, which is exactly
   `φ̃ = q (a + bπ_B) s`. So **`End_π(A/Γ) = ℤ[π_B]`**.
4. `minimalOrder_of_iso`: `MinimalOrder` is invariant under equivariant isomorphisms.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory Polynomial
open scoped CategoryTheory.MonObj IsMulCommutative

universe u

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace RamanujanWeil.Arith.Deuring.MinBase

open RamanujanWeil.Arith.Deuring.Geom RamanujanWeil.Arith.Deuring.Geom.G7
  RamanujanWeil.Arith.Deuring.Dual2 RamanujanWeil.Arith.Deuring.G8
  RamanujanWeil.Arith.Deuring.G5 Stacks.Groupoids

/-! ### Pure algebra -/

/-- The coefficient identity behind integrality. -/
theorem coeff_identity {T : Type*} [CommRing T] (O E : T) (τ δ σ ε m a b : ℤ)
    (hO : O * O - (τ : T) * O + (δ : T) = 0) (hE : E * E - (σ : T) * E + (ε : T) = 0)
    (hm : (m : T) * E = (a : T) + (b : T) * O) :
    ((a ^ 2 - b ^ 2 * δ - m * σ * a + m ^ 2 * ε : ℤ) : T) +
      ((2 * a * b + b ^ 2 * τ - m * σ * b : ℤ) : T) * O = 0 := by
  push_cast
  linear_combination (m : T) ^ 2 * hE - ((m : T) * E + a + b * O) * hm + (m : T) * σ * hm -
    (b : T) ^ 2 * hO

/-- In a commutative group, `x` in additive form (used to normalize products of powers). -/
theorem cg_ext {G : Type*} [CommGroup G] {x y : G}
    (h : Additive.ofMul x = Additive.ofMul y) : x = y := Additive.ofMul.injective h

section General

variable {k : Type u} [Field k] [IsAlgClosed k] {A : Over (Spec (.of k))} [GrpObj A]
  [AlgebraicGeometry.IsAbelianVariety k A]

theorem postcompHom_injective {E F : postcompSubring A} (h : postcompHom E = postcompHom F) :
    E = F := by
  apply Subtype.ext
  refine DFunLike.ext _ _ fun y => ?_
  apply Additive.toMul.injective
  have h1 := postcompHom_apply E (Additive.toMul y)
  have h2 := postcompHom_apply F (Additive.toMul y)
  rw [ofMul_toMul] at h1 h2
  exact h1.trans (by rw [h]; exact h2.symm)

set_option maxHeartbeats 1000000 in
/-- **Integrality.** If `E` commutes with `Ω` and `E^m = a + bΩ`, then
`a² − b² deg Ω − mσa + m² deg E = 0` and `2ab + b²τ − mσb = 0`. -/
theorem coeffs (hA : abelianVarietyDimension A = 1) (Ω E : A ⟶ A) [IsMonHom Ω] [IsMonHom E]
    (hc : E ≫ Ω = Ω ≫ E) (τ σ : ℤ) (hτ : abelianVarietyTrace A Ω = τ)
    (hσ : abelianVarietyTrace A E = σ) (hind : ∀ x y : ℤ, lin Ω x y = 1 → x = 0 ∧ y = 0)
    (m a b : ℤ) (h : E ^ m = lin Ω a b) :
    a ^ 2 - b ^ 2 * (endDegree A Ω : ℤ) - m * σ * a + m ^ 2 * (endDegree A E : ℤ) = 0 ∧
      2 * a * b + b ^ 2 * τ - m * σ * b = 0 := by
  obtain ⟨O, hO⟩ : ∃ O : postcompSubring A, O = postcompOf Ω := ⟨_, rfl⟩
  obtain ⟨F, hF⟩ : ∃ F : postcompSubring A, F = postcompOf E := ⟨_, rfl⟩
  have hO2 : O * O - (τ : postcompSubring A) * O + ((endDegree A Ω : ℤ) : postcompSubring A) = 0 := by
    rw [hO]; exact postcompOf_sq hA Ω τ hτ
  have hF2 : F * F - (σ : postcompSubring A) * F + ((endDegree A E : ℤ) : postcompSubring A) = 0 := by
    rw [hF]; exact postcompOf_sq hA E σ hσ
  have hOF : O * F = F * O := by
    rw [hO, hF, ← postcompOf_comp E Ω, ← postcompOf_comp Ω E]
    simp only [hc]
  have hlin : ∀ x y : ℤ, postcompHom ((x : postcompSubring A) + (y : postcompSubring A) * O) =
      lin Ω x y := by
    intro x y
    rw [postcompHom_add, postcompHom_mul, postcompHom_intCast, postcompHom_intCast, hO,
      postcompHom_postcompOf, comp_zpow_id]
    rfl
  have hm : (m : postcompSubring A) * F = (a : postcompSubring A) + (b : postcompSubring A) * O := by
    apply postcompHom_injective
    rw [hlin, postcompHom_mul, postcompHom_intCast, hF, postcompHom_postcompOf, comp_zpow_id, h]
  -- the commutative subring generated by `O` and `F`
  obtain ⟨T, hTdef⟩ : ∃ T : Subring (postcompSubring A),
      T = Subring.closure ({O, F} : Set (postcompSubring A)) := ⟨_, rfl⟩
  have hcomm' : ∀ a ∈ ({O, F} : Set (postcompSubring A)),
      ∀ b ∈ ({O, F} : Set (postcompSubring A)), a * b = b * a := by
    intro a ha b hb
    rcases ha with rfl | ha <;> rcases hb with rfl | hb
    · rfl
    · rw [Set.mem_singleton_iff.mp hb]; exact hOF
    · rw [Set.mem_singleton_iff.mp ha]; exact hOF.symm
    · rw [Set.mem_singleton_iff.mp ha, Set.mem_singleton_iff.mp hb]
  haveI : IsMulCommutative T := by rw [hTdef]; exact Subring.isMulCommutative_closure hcomm'
  let O' : T := ⟨O, by rw [hTdef]; exact Subring.subset_closure (by simp)⟩
  let F' : T := ⟨F, by rw [hTdef]; exact Subring.subset_closure (by simp)⟩
  have hO2' : O' * O' - (τ : T) * O' + ((endDegree A Ω : ℤ) : T) = 0 := Subtype.ext (by
    simp only [Subring.coe_add, AddSubgroupClass.coe_sub, Subring.coe_mul, Subring.coe_intCast,
      Subring.coe_zero]
    exact hO2)
  have hF2' : F' * F' - (σ : T) * F' + ((endDegree A E : ℤ) : T) = 0 := Subtype.ext (by
    simp only [Subring.coe_add, AddSubgroupClass.coe_sub, Subring.coe_mul, Subring.coe_intCast,
      Subring.coe_zero]
    exact hF2)
  have hm' : (m : T) * F' = (a : T) + (b : T) * O' := Subtype.ext (by
    simp only [Subring.coe_add, Subring.coe_mul, Subring.coe_intCast]
    exact hm)
  have key := coeff_identity O' F' τ (endDegree A Ω : ℤ) σ (endDegree A E : ℤ) m a b hO2' hF2' hm'
  have keyS : (((a ^ 2 - b ^ 2 * (endDegree A Ω : ℤ) - m * σ * a + m ^ 2 * (endDegree A E : ℤ) : ℤ) :
      postcompSubring A) + ((2 * a * b + b ^ 2 * τ - m * σ * b : ℤ) : postcompSubring A) * O) = 0 := by
    have := congrArg Subtype.val key
    simp only [Subring.coe_add, Subring.coe_mul, Subring.coe_intCast, Subring.coe_zero] at this
    exact this
  have h1 := congrArg postcompHom keyS
  have h0 : postcompHom (0 : postcompSubring A) = 1 := rfl
  rw [hlin, h0] at h1
  exact hind _ _ h1

/-- An endomorphism commuting with `ω` commutes with `a + bω`. -/
theorem comp_lin_comm (ω e : A ⟶ A) [IsMonHom ω] [IsMonHom e] (hc : e ≫ ω = ω ≫ e) (a b : ℤ) :
    e ≫ lin ω a b = lin ω a b ≫ e := by
  rw [lin_comp ω ω a b e hc, lin, MonObj.comp_mul, GrpObj.comp_zpow, GrpObj.comp_zpow,
    Category.comp_id]

/-- `w ≫ (a + bπ') = (a + bπ) ≫ w` for an equivariant homomorphism `w`. -/
theorem comp_lin_eq {B : Over (Spec (.of k))} [GrpObj B] [AlgebraicGeometry.IsAbelianVariety k B]
    (πA : A ⟶ A) (πB : B ⟶ B) [IsMonHom πA] [IsMonHom πB] (w : A ⟶ B) [IsMonHom w]
    (hw : w ≫ πB = πA ≫ w) (a b : ℤ) : w ≫ lin πB a b = lin πA a b ≫ w := by
  rw [lin_comp πA πB a b w hw, lin, MonObj.comp_mul, GrpObj.comp_zpow, GrpObj.comp_zpow,
    Category.comp_id]

/-- Products of powers of endomorphisms commuting with `ω` commute with `ω`. -/
theorem comm_zpow_mul (ω x y : A ⟶ A) [IsMonHom ω] [IsMonHom x] [IsMonHom y]
    (hx : x ≫ ω = ω ≫ x) (hy : y ≫ ω = ω ≫ y) (v u : ℤ) :
    (x ^ v * y ^ u) ≫ ω = ω ≫ (x ^ v * y ^ u) := by
  rw [MonObj.mul_comp, MonObj.comp_mul, GrpObj.zpow_comp x v ω, GrpObj.zpow_comp y u ω,
    GrpObj.comp_zpow, GrpObj.comp_zpow, hx, hy]

/-- Commuting with `c + Nω` (`N ≠ 0`) implies commuting with `ω`. -/
theorem comm_of_comm_lin (hA : abelianVarietyDimension A = 1) (ω e : A ⟶ A) [IsMonHom ω]
    [IsMonHom e] (c N : ℤ) (hN : N ≠ 0) (h : e ≫ lin ω c N = lin ω c N ≫ e) :
    e ≫ ω = ω ≫ e := by
  have h1 : e ≫ lin ω c N = e ^ c * (e ≫ ω) ^ N := by
    rw [lin, MonObj.comp_mul, GrpObj.comp_zpow, GrpObj.comp_zpow, Category.comp_id]
  have h2 : lin ω c N ≫ e = e ^ c * (ω ≫ e) ^ N := by
    rw [lin, MonObj.mul_comp, GrpObj.zpow_comp, GrpObj.zpow_comp, Category.id_comp]
  rw [h1, h2] at h
  have h3 : (e ≫ ω) ^ N = (ω ≫ e) ^ N := mul_left_cancel h
  have h4 : ((e ≫ ω) * (ω ≫ e) ^ (-1 : ℤ)) ^ N = 1 := by
    rw [zpow_neg_one, mul_zpow, inv_zpow, h3, mul_inv_cancel]
  have h5 := eq_one_of_zpow_eq_one hA ((e ≫ ω) * (ω ≫ e) ^ (-1 : ℤ)) N hN h4
  rw [zpow_neg_one] at h5
  exact mul_inv_eq_one.mp h5

/-- Torsion-freeness: `x ^ n = y ^ n ⇒ x = y` for homomorphisms, `n ≠ 0`. -/
theorem eq_of_zpow_eq (hA : abelianVarietyDimension A = 1) (x y : A ⟶ A) [IsMonHom x] [IsMonHom y]
    (n : ℤ) (hn : n ≠ 0) (h : x ^ n = y ^ n) : x = y := by
  have h4 : (x * y ^ (-1 : ℤ)) ^ n = 1 := by
    rw [zpow_neg_one, mul_zpow, inv_zpow, h, mul_inv_cancel]
  have h5 := eq_one_of_zpow_eq_one hA (x * y ^ (-1 : ℤ)) n hn h4
  rw [zpow_neg_one] at h5
  exact mul_inv_eq_one.mp h5

/-- `(𝟙^c * ω^N)^b * 𝟙^a = 𝟙^(a + bc) * ω^(Nb)`. -/
theorem lin_lin (ω : A ⟶ A) (a b c N : ℤ) :
    (lin ω c N) ^ b * (𝟙 A) ^ a = lin ω (a + b * c) (N * b) := by
  apply cg_ext
  simp only [lin, ofMul_mul, ofMul_zpow]
  module

/-- `a + b(c + Nω) = (a + bc) + Nb ω`. -/
theorem lin_of_lin (ω : A ⟶ A) (a b c N : ℤ) :
    lin (lin ω c N) a b = lin ω (a + b * c) (N * b) := by
  apply cg_ext
  simp only [lin, ofMul_mul, ofMul_zpow]
  module

/-! ### A monogenic generator of `End_π(A)` -/

/-- `π = c + nω` with `ω ∈ End_π(A)`. -/
def IsGen (π : A ⟶ A) (n : ℕ) : Prop :=
  ∃ (c : ℤ) (ω : A ⟶ A) (_ : IsMonHom ω), ω ≫ π = π ≫ ω ∧ π = lin ω c n

/-- `π = c + nω` forces `n² ∣ t² − 4q`. -/
theorem sq_dvd_of_isGen (hA : abelianVarietyDimension A = 1) (π : A ⟶ A) [IsMonHom π] (t q : ℤ)
    (htr : abelianVarietyTrace A π = t) (hdeg : (endDegree A π : ℤ) = q)
    (hind : ∀ x y : ℤ, lin π x y = 1 → x = 0 ∧ y = 0) (n : ℕ) (h : IsGen π n) :
    (n : ℤ) ^ 2 ∣ t ^ 2 - 4 * q := by
  obtain ⟨c, ω, hω, hc, hπ⟩ := h
  haveI := hω
  have hpow : ω ^ (n : ℤ) = lin π (-c) 1 := by
    rw [hπ, lin_of_lin]
    apply cg_ext
    simp only [lin, ofMul_mul, ofMul_zpow]
    module
  obtain ⟨σ, hσ⟩ := exists_int_trace hA ω
  obtain ⟨E1, E2⟩ := coeffs hA π ω hc t σ htr hσ hind n (-c) 1 hpow
  rw [hdeg] at E1
  refine ⟨σ ^ 2 - 4 * (endDegree A ω : ℤ), ?_⟩
  linear_combination 4 * E1 + ((n : ℤ) * σ + 2 * c + t) * E2

/-- **`End_π(A)` is monogenic**: `π = c + Nω` with `End_π(A) = ℤ[ω]`. -/
theorem exists_minimalOrder_gen (hA : abelianVarietyDimension A = 1) (π : A ⟶ A) [IsMonHom π]
    (t : ℤ) (q : ℕ)
    (hχ : endCharPoly A π = Polynomial.X ^ 2 - Polynomial.C (t : ℚ) * Polynomial.X +
      Polynomial.C (q : ℚ)) (hdisc : t ^ 2 < 4 * (q : ℤ)) :
    ∃ (N c : ℤ) (ω : A ⟶ A) (_ : IsMonHom ω), 0 < N ∧ N ^ 2 ∣ t ^ 2 - 4 * q ∧
      ω ≫ π = π ≫ ω ∧ π = lin ω c N ∧ MinimalOrder ω ∧
      ∀ x y : ℤ, lin ω x y = 1 → x = 0 ∧ y = 0 := by
  classical
  obtain ⟨hπ, hdeg, htr⟩ := charPoly_data hA π t q hχ
  have hind := lin_eq_one_iff hA π t q hχ hdisc
  have hdeg' : (endDegree A π : ℤ) = (q : ℤ) := by rw [hdeg]
  set D : ℤ := t ^ 2 - 4 * q with hD
  have hD0 : D ≠ 0 := by rw [hD]; linarith
  set Bd : ℕ := D.natAbs with hBd
  have hbound : ∀ n : ℕ, IsGen π n → n ≤ Bd := by
    intro n hn
    have h1 := sq_dvd_of_isGen hA π t q htr hdeg' hind n hn
    have h2 : ((n : ℤ) ^ 2).natAbs ∣ D.natAbs := Int.natAbs_dvd_natAbs.mpr h1
    rw [Int.natAbs_pow, Int.natAbs_natCast] at h2
    have h3 := Nat.le_of_dvd (Int.natAbs_pos.mpr hD0) h2
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · rw [h0]; exact Nat.zero_le _
    · calc n ≤ n ^ 2 := by nlinarith
        _ ≤ Bd := h3
  have h1gen : IsGen π 1 := ⟨0, π, inferInstance, rfl, by
    apply cg_ext; simp only [lin, ofMul_mul, ofMul_zpow, Nat.cast_one]; module⟩
  have h1B : 1 ≤ Bd := hbound 1 h1gen
  set N : ℕ := Nat.findGreatest (IsGen π) Bd with hNdef
  have hNgen : IsGen π N := Nat.findGreatest_spec h1B h1gen
  have hmax : ∀ n : ℕ, IsGen π n → n ≤ N := fun n hn =>
    Nat.le_findGreatest (hbound n hn) hn
  obtain ⟨c, ω, hω, hcω, hπω⟩ := hNgen
  haveI := hω
  have hNpos : 0 < N := by
    rcases Nat.eq_zero_or_pos N with h0 | h0
    · exfalso
      have := sq_dvd_of_isGen hA π t q htr hdeg' hind N ⟨c, ω, hω, hcω, hπω⟩
      rw [h0, Nat.cast_zero, zero_pow two_ne_zero, zero_dvd_iff] at this
      exact hD0 this
    · exact h0
  have hN0 : (N : ℤ) ≠ 0 := by exact_mod_cast hNpos.ne'
  -- `ℤ[ω] → End(A)` is injective
  have hindω : ∀ x y : ℤ, lin ω x y = 1 → x = 0 ∧ y = 0 := by
    intro x y hxy
    have h2 : lin π (N * x - c * y) y = (lin ω x y) ^ (N : ℤ) := by
      rw [hπω, lin_of_lin]
      apply cg_ext
      simp only [lin, ofMul_mul, ofMul_zpow]
      module
    rw [hxy, one_zpow] at h2
    obtain ⟨h3, h4⟩ := hind _ _ h2
    subst h4
    refine ⟨?_, rfl⟩
    simp only [mul_zero, sub_zero] at h3
    exact (mul_eq_zero.mp h3).resolve_left hN0
  refine ⟨N, c, ω, hω, by exact_mod_cast hNpos,
    sq_dvd_of_isGen hA π t q htr hdeg' hind N ⟨c, ω, hω, hcω, hπω⟩, hcω, hπω, ?_, hindω⟩
  -- `End_π(A) = ℤ[ω]`
  intro e he hce
  haveI := he
  have hceπ : e ≫ π = π ≫ e := by rw [hπω]; exact comp_lin_comm ω e hce c N
  obtain ⟨m₀, a₀, b₀, hm₀, he₀⟩ := exists_zpow_eq_of_comm hA π e t q hπ hdisc hceπ
  have he₀' : e ^ m₀ = lin ω (a₀ + b₀ * c) (N * b₀) := by
    rw [he₀, hπω]; exact lin_lin ω a₀ b₀ c N
  obtain ⟨τω, hτω⟩ := exists_int_trace hA ω
  have key : ∀ n : ℕ, ∀ m : ℤ, m.natAbs = n → m ≠ 0 → ∀ a b : ℤ, e ^ m = lin ω a b →
      ∃ a b : ℤ, e = lin ω a b := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
    intro m hmn hm0 a b hab
    by_cases h1 : n = 1
    · rcases Int.natAbs_eq m with h | h
      · rw [h, hmn, h1] at hab
        exact ⟨a, b, by simpa using hab⟩
      · rw [h, hmn, h1] at hab
        refine ⟨-a, -b, ?_⟩
        rw [← lin_neg, ← hab]
        simp
    · have hn0 : n ≠ 0 := by rintro rfl; exact hm0 (Int.natAbs_eq_zero.mp hmn)
      set ℓ := n.minFac with hℓdef
      have hℓ : ℓ.Prime := Nat.minFac_prime h1
      have hℓZ : Prime (ℓ : ℤ) := Nat.prime_iff_prime_int.mp hℓ
      have hℓ2 : 2 ≤ ℓ := hℓ.two_le
      obtain ⟨m', hm'⟩ : (ℓ : ℤ) ∣ m := by
        rw [← Int.natAbs_dvd_natAbs, Int.natAbs_natCast, hmn]; exact Nat.minFac_dvd n
      have hm'0 : m' ≠ 0 := by rintro rfl; simp at hm'; exact hm0 hm'
      have hlt : m'.natAbs < n := by
        rw [← hmn, hm', Int.natAbs_mul, Int.natAbs_natCast]
        have : 0 < m'.natAbs := Int.natAbs_pos.mpr hm'0
        nlinarith
      have hce' : (e ^ m') ≫ ω = ω ≫ (e ^ m') := by
        rw [GrpObj.zpow_comp, GrpObj.comp_zpow, hce]
      have he' : (e ^ m') ^ (ℓ : ℤ) = lin ω a b := by
        rw [← zpow_mul, mul_comm, ← hm', hab]
      by_cases hdiv : (ℓ : ℤ) ∣ a ∧ (ℓ : ℤ) ∣ b
      · obtain ⟨⟨a₁, rfl⟩, ⟨b₁, rfl⟩⟩ := hdiv
        rw [lin_mul] at he'
        have hℓ0 : (ℓ : ℤ) ≠ 0 := by exact_mod_cast hℓ.ne_zero
        exact ih _ hlt m' rfl hm'0 a₁ b₁ (eq_of_zpow_eq hA _ _ _ hℓ0 he')
      · exfalso
        obtain ⟨σ, hσ⟩ := exists_int_trace hA (e ^ m')
        obtain ⟨E1, -⟩ := coeffs hA ω (e ^ m') hce' τω σ hτω hσ hindω ℓ a b he'
        have hb : ¬ (ℓ : ℤ) ∣ b := by
          intro hb
          apply hdiv
          refine ⟨?_, hb⟩
          obtain ⟨b₁, rfl⟩ := hb
          have : (ℓ : ℤ) ∣ a ^ 2 := ⟨b₁ ^ 2 * ℓ * (endDegree A ω : ℤ) + σ * a -
            ℓ * (endDegree A (e ^ m') : ℤ), by linear_combination E1⟩
          exact hℓZ.dvd_of_dvd_pow this
        obtain ⟨u, v, huv⟩ := (Irreducible.coprime_iff_not_dvd hℓZ.irreducible).mpr hb
        set e' := e ^ m' with he'def
        have hω₁c : (e' ^ v * ω ^ u) ≫ ω = ω ≫ (e' ^ v * ω ^ u) :=
          comm_zpow_mul ω e' ω hce' rfl v u
        have hgen : IsGen π (N * ℓ) := by
          refine ⟨c - N * v * a, e' ^ v * ω ^ u, inferInstance, ?_, ?_⟩
          · rw [hπω]
            exact comp_lin_comm ω _ hω₁c c N
          · have h3 : lin (e' ^ v * ω ^ u) (c - N * v * a) ((N * ℓ : ℕ) : ℤ) =
                (𝟙 A) ^ (c - N * v * a) * (e' ^ (ℓ : ℤ)) ^ (v * N) * ω ^ (u * (N * ℓ)) := by
              apply cg_ext
              simp only [lin, ofMul_mul, ofMul_zpow, Nat.cast_mul]
              module
            rw [h3, he', hπω]
            apply cg_ext
            simp only [lin, ofMul_mul, ofMul_zpow]
            have hN1 : (N : ℤ) = (N : ℤ) * (u * ℓ + v * b) := by rw [huv, mul_one]
            have hNb : (N : ℤ) • Additive.ofMul ω =
                ((N : ℤ) * (u * ℓ + v * b)) • Additive.ofMul ω := by rw [← hN1]
            rw [hNb]
            module
        have := hmax _ hgen
        nlinarith
  exact key _ m₀ rfl hm₀ _ _ he₀'

/-! ### The quotient with minimal order -/

/-- **`MinimalOrder` is invariant under equivariant isomorphisms.** -/
theorem minimalOrder_of_iso {B B' : Over (Spec (.of k))} [GrpObj B] [GrpObj B']
    [AlgebraicGeometry.IsAbelianVariety k B] [AlgebraicGeometry.IsAbelianVariety k B']
    (πB : B ⟶ B) (π' : B' ⟶ B') [IsMonHom πB] [IsMonHom π'] (e : B' ≅ B)
    (he : IsMonHom e.hom) (hc : e.hom ≫ πB = π' ≫ e.hom) (hmin : MinimalOrder πB) :
    MinimalOrder π' := by
  intro φ' hφ' hφc
  haveI := hφ'
  haveI := he
  have hinv : πB ≫ e.inv = e.inv ≫ π' := by
    rw [Iso.eq_inv_comp, ← Category.assoc, hc, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have hc' : (e.inv ≫ φ' ≫ e.hom) ≫ πB = πB ≫ (e.inv ≫ φ' ≫ e.hom) := by
    simp only [Category.assoc]
    rw [hc, ← Category.assoc φ' π', hφc, Category.assoc, ← reassoc_of% hinv]
  obtain ⟨a, b, hab⟩ := hmin _ inferInstance hc'
  refine ⟨a, b, ?_⟩
  have h1 : e.hom ≫ lin πB a b = lin π' a b ≫ e.hom := comp_lin_eq π' πB e.hom hc a b
  have h2 : φ' = e.hom ≫ (e.inv ≫ φ' ≫ e.hom) ≫ e.inv := by simp
  rw [h2, hab, reassoc_of% h1, Iso.hom_inv_id, Category.comp_id]

/-- **A quotient with `End_π = ℤ[π]`.** Let `π = c + Nω` with `End_π(A) = ℤ[ω]` and `N`
invertible in `k`. Then there is a cyclic `π`-stable `Γ ⊆ A[N]` such that the descended
Frobenius of every quotient `A/Γ` has the minimal order. -/
theorem exists_minimalOrder_quotient (hA : abelianVarietyDimension A = 1) (π ω : A ⟶ A)
    [IsMonHom π] [IsMonHom ω] (hmin : MinimalOrder ω)
    (hind : ∀ x y : ℤ, lin ω x y = 1 → x = 0 ∧ y = 0) (c N : ℤ) (hπ : π = lin ω c N)
    (hN : IsUnit (N : k)) :
    ∃ Γ : Subgroup (Pt A), Finite Γ ∧ (∀ x ∈ Γ, x ≫ π ∈ Γ) ∧ (∀ h ∈ Γ, h ^ N = 1) ∧
      ∀ (G : Glue Γ) (πB : G.B ⟶ G.B) [IsMonHom πB], G.q ≫ πB = π ≫ G.q → MinimalOrder πB := by
  have hN0 : N ≠ 0 := by rintro rfl; simp at hN
  have hN2 : IsUnit ((N ^ 2 : ℤ) : k) := by push_cast; exact hN.pow 2
  obtain ⟨Q, hQ, -, hann⟩ := cyclicTorsion_of_minimalOrder hA hmin hind (N ^ 2) hN2
  set P : Pt A := Q ^ N with hPdef
  have hP : P ^ N = 1 := by rw [hPdef, ← zpow_mul, ← sq]; exact hQ
  -- `P` has trivial annihilator in `ℤ[ω]/N`
  have hannP : ∀ a b : ℤ, P ≫ lin ω a b = 1 → N ∣ a ∧ N ∣ b := by
    intro a b h
    have h1 : Q ≫ lin ω (N * a) (N * b) = 1 := by
      rw [comp_lin_mul, ← zpow_comp_lin, ← hPdef, h]
    obtain ⟨h2, h3⟩ := hann _ _ h1
    rw [sq] at h2 h3
    exact ⟨(mul_dvd_mul_iff_left hN0).mp h2, (mul_dvd_mul_iff_left hN0).mp h3⟩
  have hQa : ∀ a : ℤ, Q ≫ lin ω a 0 = Q ^ a := fun a => by rw [comp_lin, zpow_zero, mul_one]
  have hPa : ∀ a : ℤ, P ≫ lin ω a 0 = P ^ a := fun a => by rw [comp_lin, zpow_zero, mul_one]
  set Γ : Subgroup (Pt A) := Subgroup.zpowers P with hΓdef
  have hkill : ∀ h ∈ Γ, h ^ N = 1 := by
    intro h hh
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
    rw [← zpow_mul, mul_comm, zpow_mul, hP, one_zpow]
  have hfin : Finite Γ :=
    Set.Finite.to_subtype ((isOfFinOrder_iff_zpow_eq_one.mpr ⟨N, hN0, hP⟩).finite_zpowers)
  have hPω : (P ≫ ω) ^ N = 1 := by rw [← GrpObj.zpow_comp, hP, MonObj.one_comp]
  have hPπ : P ≫ π = P ^ c := by
    rw [hπ, comp_lin, hPω, mul_one]
  have hπΓ : ∀ x ∈ Γ, x ≫ π ∈ Γ := by
    intro x hx
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    exact Subgroup.mem_zpowers_iff.mpr ⟨c * j, by rw [GrpObj.zpow_comp, hPπ, zpow_mul]⟩
  refine ⟨Γ, hfin, hπΓ, hkill, ?_⟩
  intro G πB _ hqπ
  have hπB : πB = GlueS.πB G π hπΓ := GlueS.eq_πB G π hπΓ πB hqπ
  subst hπB
  set s := GlueS.sMap G N hkill with hs
  intro φ hφ hφc
  haveI := hφ
  -- `φ̃ = q φ s ∈ End_π(A) = ℤ[ω]`
  have hφπ : (G.q ≫ φ ≫ s) ≫ π = π ≫ (G.q ≫ φ ≫ s) := by
    simp only [Category.assoc]
    rw [GlueS.sMap_π G N hkill π hπΓ, ← Category.assoc φ, hφc, Category.assoc,
      ← Category.assoc G.q, GlueS.q_πB, Category.assoc]
  have hφω : (G.q ≫ φ ≫ s) ≫ ω = ω ≫ (G.q ≫ φ ≫ s) := by
    refine comm_of_comm_lin hA ω _ c N hN0 ?_
    rw [← hπ]; exact hφπ
  obtain ⟨x, y, hxy⟩ := hmin _ inferInstance hφω
  -- `φ̃` sends `A[N]` into `Γ`
  have hF1 : ∀ u : Pt A, u ^ N = 1 → u ≫ lin ω x y ∈ Γ := by
    intro u hu
    rw [← hxy, ← Category.assoc G.q]
    exact GlueS.comp_sMap_mem G N hkill (G.q ≫ φ) u hu
  -- `φ̃` sends `Q` into `Γ`
  have hF2 : Q ≫ lin ω x y ∈ Γ := by
    rw [← G.ker, ← hxy]
    have e1 : (Q ≫ G.q ≫ φ ≫ s) ≫ G.q = ((Q ≫ G.q) ≫ φ) ≫ (s ≫ G.q) := by
      simp only [Category.assoc]
    rw [e1, GlueS.sMap_q, comp_zpow_id, ← zpow_comp_hom, ← zpow_comp_hom, ← hPdef,
      (G.ker P).2 (Subgroup.mem_zpowers P), MonObj.one_comp]
  -- `N ∣ y`
  obtain ⟨z, hz⟩ := Subgroup.mem_zpowers_iff.mp (hF1 P hP)
  have hy : N ∣ y := by
    have h1 : P ≫ lin ω (x - z) (y - 0) = 1 := by
      rw [comp_lin_sub, ← hz, hPa, mul_inv_cancel]
    exact (by simpa using (hannP _ _ h1).2)
  obtain ⟨y₁, rfl⟩ := hy
  -- `N ∣ x`
  obtain ⟨w, hw⟩ := Subgroup.mem_zpowers_iff.mp (hF1 (P ≫ ω) hPω)
  have hx : N ∣ x := by
    have h1 : (P ≫ ω) ≫ lin ω x (N * y₁) = P ≫ lin ω 0 x := by
      have e1 := comp_lin_add_mul ω (P ≫ ω) N hPω x 0 0 y₁
      simp only [mul_zero, add_zero, zero_add] at e1
      rw [e1, comp_lin, comp_lin, zpow_zero, zpow_zero, mul_one, one_mul]
    have h2 : P ≫ lin ω (0 - w) (x - 0) = 1 := by
      rw [comp_lin_sub, ← h1, ← hw, hPa, mul_inv_cancel]
    exact (by simpa using (hannP _ _ h2).2)
  obtain ⟨x₁, rfl⟩ := hx
  -- `N ∣ y₁`
  obtain ⟨z', hz'⟩ := Subgroup.mem_zpowers_iff.mp hF2
  have hy₁ : N ∣ y₁ := by
    have h1 : Q ≫ lin ω (N * x₁ - N * z') (N * y₁ - 0) = 1 := by
      rw [comp_lin_sub, hQa, zpow_mul, ← hPdef, hz', mul_inv_cancel]
    obtain ⟨-, h2⟩ := hann _ _ h1
    rw [sub_zero, sq] at h2
    exact (mul_dvd_mul_iff_left hN0).mp h2
  obtain ⟨y₂, rfl⟩ := hy₁
  -- conclusion: `φ = (x₁ − c y₂) + y₂ π_B`
  refine ⟨x₁ - c * y₂, y₂, ?_⟩
  apply G.cancel
  apply GlueS.comp_sMap_injective G N hkill hA hN0
  rw [Category.assoc, hxy, comp_lin_eq π (GlueS.πB G π hπΓ) G.q (GlueS.q_πB G π hπΓ),
    Category.assoc, GlueS.q_sMap, comp_zpow_id, hπ, lin_of_lin]
  apply cg_ext
  simp only [lin, ofMul_mul, ofMul_zpow]
  module

end General

end RamanujanWeil.Arith.Deuring.MinBase
