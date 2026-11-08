import RamanujanWeil.Ihara.IharaStatement
import Mathlib.GroupTheory.GroupAction.Quotient

/-!
# A4: the coordinate-change torsor count

For a finite field `K` (any characteristic, `2` and `3` included) the group
`G = WeierstrassCurve.VariableChange K` of admissible changes of variables
`(X, Y) ↦ (u²X + r, u³Y + u²sX + t)` has order `(q − 1) q³` and acts on Weierstrass curves.

* `wcEquiv`: `wc : (Fin 5 → K) → WeierstrassCurve K` is a bijection, so the `G`-action on
  curves is an action on coefficient vectors `c ∈ K⁵` (it never leaves the image of `wc`).
* `card_vc`: `#G = (q − 1) q³`.
* `card_point_smul`, `traceOfFrob_smul`: point counts and `traceOfFrob` are `G`-invariant
  (proved by an explicit injection of affine points, for every curve, singular ones too).
* `card_isoClass_mul_card_stabilizer` (**torsor count**): for `Δ(wc c) ≠ 0`,
  `#{c' | Δ(wc c') ≠ 0 ∧ wc c' ∈ G • wc c} · #Stab(wc c) = (q − 1) q³`.
* `sum_trace_eq_sum_orbits` (**decomposition**): for `F : ℤ → R`, `R` a field of
  characteristic zero,
  `Σ_{c, Δ ≠ 0} F(a(E_c)) = (q − 1) q³ · Σ_{orbits O, Δ ≠ 0} F(a_O) / #Stab(O)`.
-/

open WeierstrassCurve MulAction

namespace RamanujanWeil.Arith

open RamanujanWeil.Ihara

section General

variable {K : Type*} [Field K]

/-- `wc` is a bijection `K⁵ ≃ WeierstrassCurve K` (`c ↦ (a₁,a₂,a₃,a₄,a₆) = (c 0,…,c 4)`). -/
def wcEquiv : (Fin 5 → K) ≃ WeierstrassCurve K where
  toFun := wc
  invFun W := ![W.a₁, W.a₂, W.a₃, W.a₄, W.a₆]
  left_inv c := by funext i; fin_cases i <;> rfl
  right_inv _ := rfl

@[simp] lemma wcEquiv_apply (c : Fin 5 → K) : wcEquiv c = wc c := rfl

/-- A change of variables of `C • W` transports nonsingular points to `W`. -/
lemma nonsingular_of_smul (C : VariableChange K) (W : WeierstrassCurve K) {x y : K}
    (h : (C • W).toAffine.Nonsingular x y) :
    W.toAffine.Nonsingular (C.u ^ 2 * x + C.r) (C.u ^ 3 * y + C.u ^ 2 * C.s * x + C.t) := by
  have hu : (C.u : K) ≠ 0 := C.u.ne_zero
  rw [Affine.nonsingular_iff'] at h ⊢
  obtain ⟨he, hd⟩ := h
  rw [Affine.equation_iff'] at he ⊢
  simp only [variableChange_a₁, variableChange_a₂, variableChange_a₃, variableChange_a₄,
    variableChange_a₆, Units.val_inv_eq_inv_val] at he hd
  have hW : ∀ W' : WeierstrassCurve K, W'.toAffine.a₁ = W'.a₁ ∧ W'.toAffine.a₂ = W'.a₂ ∧
      W'.toAffine.a₃ = W'.a₃ ∧ W'.toAffine.a₄ = W'.a₄ ∧ W'.toAffine.a₆ = W'.a₆ :=
    fun _ => ⟨rfl, rfl, rfl, rfl, rfl⟩
  simp only [(hW W).1, (hW W).2.1, (hW W).2.2.1, (hW W).2.2.2.1, (hW W).2.2.2.2] at *
  constructor
  · rw [← mul_eq_zero_of_right ((C.u : K) ^ 6) he]
    field_simp
    ring
  · by_contra hc
    push Not at hc
    obtain ⟨h1, h2⟩ := hc
    rcases hd with hd | hd
    · apply hd
      have : (C.u : K) ^ 4 * ((C.u : K)⁻¹ * (W.a₁ + 2 * C.s) * y -
          (3 * x ^ 2 + 2 * ((C.u : K)⁻¹ ^ 2 * (W.a₂ - C.s * W.a₁ + 3 * C.r - C.s ^ 2)) * x +
            (C.u : K)⁻¹ ^ 4 * (W.a₄ - C.s * W.a₃ + 2 * C.r * W.a₂ - (C.t + C.r * C.s) * W.a₁ +
              3 * C.r ^ 2 - 2 * C.s * C.t))) = 0 := by
        rw [← sub_eq_zero.mpr (show (0 : K) = 0 from rfl)]
        have key : (C.u : K) ^ 4 * ((C.u : K)⁻¹ * (W.a₁ + 2 * C.s) * y -
            (3 * x ^ 2 + 2 * ((C.u : K)⁻¹ ^ 2 * (W.a₂ - C.s * W.a₁ + 3 * C.r - C.s ^ 2)) * x +
              (C.u : K)⁻¹ ^ 4 * (W.a₄ - C.s * W.a₃ + 2 * C.r * W.a₂ - (C.t + C.r * C.s) * W.a₁ +
                3 * C.r ^ 2 - 2 * C.s * C.t))) =
            (W.a₁ * (C.u ^ 3 * y + C.u ^ 2 * C.s * x + C.t) -
              (3 * (C.u ^ 2 * x + C.r) ^ 2 + 2 * W.a₂ * (C.u ^ 2 * x + C.r) + W.a₄)) +
            C.s * (2 * (C.u ^ 3 * y + C.u ^ 2 * C.s * x + C.t) +
              W.a₁ * (C.u ^ 2 * x + C.r) + W.a₃) := by
          field_simp
          ring
        rw [key, h1, h2]; ring
      simpa [hu] using this
    · apply hd
      have key : (C.u : K) ^ 3 * (2 * y + (C.u : K)⁻¹ * (W.a₁ + 2 * C.s) * x +
          (C.u : K)⁻¹ ^ 3 * (W.a₃ + C.r * W.a₁ + 2 * C.t)) =
          2 * (C.u ^ 3 * y + C.u ^ 2 * C.s * x + C.t) + W.a₁ * (C.u ^ 2 * x + C.r) + W.a₃ := by
        field_simp
        ring
      have : (C.u : K) ^ 3 * (2 * y + (C.u : K)⁻¹ * (W.a₁ + 2 * C.s) * x +
          (C.u : K)⁻¹ ^ 3 * (W.a₃ + C.r * W.a₁ + 2 * C.t)) = 0 := by rw [key, h2]
      simpa [hu] using this

/-- The point map `(C • W)(K) → W(K)`, `(x, y) ↦ (u²x + r, u³y + u²sx + t)`, `O ↦ O`. -/
def pointMap (C : VariableChange K) (W : WeierstrassCurve K) :
    (C • W).toAffine.Point → W.toAffine.Point
  | .zero => .zero
  | .some _ _ h => .some _ _ (nonsingular_of_smul C W h)

lemma pointMap_injective (C : VariableChange K) (W : WeierstrassCurve K) :
    Function.Injective (pointMap C W) := by
  have hu : (C.u : K) ≠ 0 := C.u.ne_zero
  intro P Q hPQ
  cases P with
  | zero => cases Q with
    | zero => rfl
    | some => simp [pointMap] at hPQ
  | some x y h => cases Q with
    | zero => simp [pointMap] at hPQ
    | some x' y' h' =>
      simp only [pointMap, Affine.Point.some.injEq] at hPQ
      obtain ⟨hx, hy⟩ := hPQ
      have hx' : x = x' := by
        have : (C.u : K) ^ 2 * x = C.u ^ 2 * x' := by linear_combination hx
        exact mul_left_cancel₀ (pow_ne_zero 2 hu) this
      subst hx'
      have hy' : y = y' := by
        have : (C.u : K) ^ 3 * y = C.u ^ 3 * y' := by linear_combination hy
        exact mul_left_cancel₀ (pow_ne_zero 3 hu) this
      subst hy'
      rfl

/-- Affine points over a finite field form a finite type. -/
instance point_finite [Finite K] (W : WeierstrassCurve K) : Finite W.toAffine.Point := by
  refine Finite.of_injective (β := Option (K × K))
    (fun P => match P with
      | .zero => none
      | .some x y _ => some (x, y)) ?_
  intro P Q h
  cases P <;> cases Q <;> simp_all

/-- Point counts are invariant under change of variables. -/
theorem card_point_smul [Finite K] (C : VariableChange K) (W : WeierstrassCurve K) :
    Nat.card (C • W).toAffine.Point = Nat.card W.toAffine.Point := by
  apply le_antisymm (Nat.card_le_card_of_injective _ (pointMap_injective C W))
  have := Nat.card_le_card_of_injective _ (pointMap_injective C⁻¹ (C • W))
  rwa [inv_smul_smul] at this

/-- `traceOfFrob` is constant on `VariableChange`-orbits. -/
theorem traceOfFrob_smul [Finite K] (C : VariableChange K) (W : WeierstrassCurve K) :
    traceOfFrob (C • W) = traceOfFrob W := by
  unfold traceOfFrob
  rw [card_point_smul]

theorem traceOfFrob_of_mem_orbit [Finite K] {W W' : WeierstrassCurve K}
    (h : W' ∈ orbit (VariableChange K) W) : traceOfFrob W' = traceOfFrob W := by
  obtain ⟨C, rfl⟩ := h
  exact traceOfFrob_smul C W

lemma Δ_smul_ne_zero_iff (C : VariableChange K) (W : WeierstrassCurve K) :
    (C • W).Δ ≠ 0 ↔ W.Δ ≠ 0 := by
  rw [variableChange_Δ]
  simp

/-- `VariableChange K ≃ Kˣ × K × K × K`. -/
def vcEquiv : VariableChange K ≃ Kˣ × K × K × K where
  toFun C := (C.u, C.r, C.s, C.t)
  invFun p := ⟨p.1, p.2.1, p.2.2.1, p.2.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance vc_finite [Finite K] : Finite (VariableChange K) := Finite.of_equiv _ vcEquiv.symm

/-- `#G = (q − 1) q³`. -/
theorem card_vc [Finite K] :
    Nat.card (VariableChange K) = (Nat.card K - 1) * Nat.card K ^ 3 := by
  rw [Nat.card_congr vcEquiv, Nat.card_prod, Nat.card_prod, Nat.card_prod, Nat.card_units]
  ring

/-- Orbit–stabilizer for the coordinate-change action. -/
theorem card_orbit_mul_card_stabilizer [Finite K] (W : WeierstrassCurve K) :
    Nat.card (orbit (VariableChange K) W) * Nat.card (stabilizer (VariableChange K) W) =
      (Nat.card K - 1) * Nat.card K ^ 3 := by
  rw [← card_vc, ← Nat.card_prod, Nat.card_congr (orbitProdStabilizerEquivGroup _ W)]

/-- **Torsor count.** For `E = wc c` elliptic, the number of coefficient vectors `c'` with
`wc c'` elliptic and `G`-equivalent to `E`, times `#Aut(E) = #Stab_G(E)`, is `(q − 1) q³`. -/
theorem card_isoClass_mul_card_stabilizer [Finite K] (c : Fin 5 → K) (hc : (wc c).Δ ≠ 0) :
    Nat.card {c' : Fin 5 → K // (wc c').Δ ≠ 0 ∧ wc c' ∈ orbit (VariableChange K) (wc c)} *
        Nat.card (stabilizer (VariableChange K) (wc c)) =
      (Nat.card K - 1) * Nat.card K ^ 3 := by
  rw [← card_orbit_mul_card_stabilizer]
  congr 1
  refine Nat.card_congr (Equiv.subtypeEquiv wcEquiv fun c' => ?_)
  simp only [wcEquiv_apply, and_iff_right_iff_imp]
  rintro ⟨C, hC⟩
  rw [← hC, Δ_smul_ne_zero_iff]
  exact hc

/-- Class-equation form of a sum over curves of an orbit-invariant function. -/
theorem finsum_eq_finsum_orbits [Finite K] {R : Type*} [Field R] [CharZero R]
    (φ : WeierstrassCurve K → R)
    (hφ : ∀ (C : VariableChange K) (W : WeierstrassCurve K), φ (C • W) = φ W) :
    ∑ᶠ W : WeierstrassCurve K, φ W =
      ((Nat.card K - 1) * Nat.card K ^ 3 : ℕ) *
        ∑ᶠ O : orbitRel.Quotient (VariableChange K) (WeierstrassCurve K),
          φ O.out / Nat.card (stabilizer (VariableChange K) O.out) := by
  classical
  have : Finite (WeierstrassCurve K) := Finite.of_equiv _ wcEquiv
  let _ : Fintype (WeierstrassCurve K) := Fintype.ofFinite _
  let _ : Fintype (orbitRel.Quotient (VariableChange K) (WeierstrassCurve K)) := Fintype.ofFinite _
  let _ : ∀ O : orbitRel.Quotient (VariableChange K) (WeierstrassCurve K),
    Fintype (orbit (VariableChange K) O.out) := fun _ => Fintype.ofFinite _
  rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype, Finset.mul_sum,
    ← (selfEquivSigmaOrbits (VariableChange K) (WeierstrassCurve K)).symm.sum_comp,
    Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun O _ => ?_
  have hconst : ∀ x : orbit (VariableChange K) O.out,
      φ ((selfEquivSigmaOrbits (VariableChange K) (WeierstrassCurve K)).symm ⟨O, x⟩) = φ O.out := by
    rintro ⟨x, C, rfl⟩
    exact hφ C _
  rw [Finset.sum_congr rfl fun x _ => hconst x, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    ← card_orbit_mul_card_stabilizer O.out, Fintype.card_eq_nat_card]
  have hS : (Nat.card (stabilizer (VariableChange K) O.out) : R) ≠ 0 := by
    exact_mod_cast (Nat.card_pos (α := stabilizer (VariableChange K) O.out)).ne'
  push_cast
  field_simp

/-- **Decomposition of the Weierstrass sum by isomorphism classes.** For `F : ℤ → R`,
`Σ_{c ∈ K⁵, Δ(c) ≠ 0} F(a(E_c)) = (q−1)q³ · Σ_{G-orbits O, Δ ≠ 0} F(a_O) / #Stab(O)`. -/
theorem sum_trace_eq_sum_orbits [Fintype K] [DecidableEq K] {R : Type*} [Field R] [CharZero R]
    (F : ℤ → R) :
    ∑ c ∈ (Finset.univ.filter fun c : Fin 5 → K => (wc c).Δ ≠ 0), F (traceOfFrob (wc c)) =
      ((Fintype.card K - 1) * Fintype.card K ^ 3 : ℕ) *
        ∑ᶠ O : orbitRel.Quotient (VariableChange K) (WeierstrassCurve K),
          if O.out.Δ ≠ 0 then
            F (traceOfFrob O.out) / Nat.card (stabilizer (VariableChange K) O.out)
          else 0 := by
  classical
  have hφ : ∀ (C : VariableChange K) (W : WeierstrassCurve K),
      (if (C • W).Δ ≠ 0 then F (traceOfFrob (C • W)) else 0) =
        (if W.Δ ≠ 0 then F (traceOfFrob W) else 0) := by
    intro C W
    rw [traceOfFrob_smul]
    simp only [Δ_smul_ne_zero_iff]
  have := finsum_eq_finsum_orbits (fun W : WeierstrassCurve K =>
    if W.Δ ≠ 0 then F (traceOfFrob W) else 0) hφ
  rw [Fintype.card_eq_nat_card, Finset.sum_filter, ← finsum_eq_sum_of_fintype]
  rw [show (∑ᶠ c : Fin 5 → K, if (wc c).Δ ≠ 0 then F (traceOfFrob (wc c)) else 0) =
      ∑ᶠ W : WeierstrassCurve K, if W.Δ ≠ 0 then F (traceOfFrob W) else 0 from
    finsum_comp_equiv wcEquiv (f := fun W : WeierstrassCurve K =>
      if W.Δ ≠ 0 then F (traceOfFrob W) else 0)]
  rw [this]
  congr 1
  refine finsum_congr fun O => ?_
  split_ifs <;> simp

end General

end RamanujanWeil.Arith
