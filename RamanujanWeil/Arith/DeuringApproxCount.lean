import RamanujanWeil.Arith.SupersingularBound

/-!
# The ordinary tuple count: `#{c ∈ 𝔽_q⁵ : Δ ≠ 0, p ∤ a_c} ≥ q⁵ − C q⁴`

* `deltaPoly R` : the discriminant of the generic Weierstrass curve, an element of
  `R[a₁, a₂, a₃, a₄, a₆]`; `eval_deltaPoly`, `deltaPoly_map`;
* `deltaPoly_ne_zero` : it is nonzero over every field (witnesses `y² + xy = x³ + 1`,
  `Δ = −433`, in characteristic `3`, and `y² + y = x³`, `Δ = −27`, otherwise);
* `card_singular_le` : `#{c : Δ = 0} ≤ D₀ q⁴` (Schwartz–Zippel, `D₀ = deg Δ` over `ℤ`);
* **`card_ordinary_lower`** : `q⁵ ≤ #{c : Δ ≠ 0, p ∤ a_c} + (D₀ + p) q⁴` (with the supersingular
  count `card_dvd_traceOfFrob_le`).
-/

open Finset MvPolynomial

namespace RamanujanWeil.ArithPlan

open RamanujanWeil.Ihara

/-- The discriminant of the generic Weierstrass curve `wc (X₀, …, X₄)`. -/
noncomputable def deltaPoly (R : Type*) [CommRing R] : MvPolynomial (Fin 5) R :=
  (wc (fun i => (X i : MvPolynomial (Fin 5) R))).Δ

lemma eval_deltaPoly {R : Type*} [CommRing R] (c : Fin 5 → R) :
    eval c (deltaPoly R) = (wc c).Δ := by
  rw [deltaPoly, ← WeierstrassCurve.map_Δ]
  congr 1
  simp [wc, WeierstrassCurve.map]

lemma deltaPoly_map (R : Type*) [CommRing R] :
    MvPolynomial.map (Int.castRingHom R) (deltaPoly ℤ) = deltaPoly R := by
  rw [deltaPoly, deltaPoly, ← WeierstrassCurve.map_Δ]
  congr 1
  simp [wc, WeierstrassCurve.map]

/-- The degree bound, uniform in the coefficient ring. -/
lemma totalDegree_deltaPoly_le (R : Type*) [CommRing R] :
    (deltaPoly R).totalDegree ≤ (deltaPoly ℤ).totalDegree := by
  rw [← deltaPoly_map]
  exact Finset.sup_mono (support_map_subset _ _)

lemma delta_witness₁ (F : Type*) [Field F] : (wc (![1, 0, 0, 0, 1] : Fin 5 → F)).Δ = -433 := by
  have : wc (![1, 0, 0, 0, 1] : Fin 5 → F) = ⟨1, 0, 0, 0, 1⟩ := rfl
  rw [this]
  norm_num [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
    WeierstrassCurve.b₈]

lemma delta_witness₂ (F : Type*) [Field F] : (wc (![0, 0, 1, 0, 0] : Fin 5 → F)).Δ = -27 := by
  have : wc (![0, 0, 1, 0, 0] : Fin 5 → F) = ⟨0, 0, 1, 0, 0⟩ := rfl
  rw [this]
  norm_num [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
    WeierstrassCurve.b₈]

/-- `Δ` is a nonzero polynomial over every field of prime characteristic. -/
lemma deltaPoly_ne_zero (F : Type*) [Field F] (p : ℕ) [hp : Fact p.Prime] [CharP F p] :
    deltaPoly F ≠ 0 := by
  intro h
  by_cases h3 : p = 3
  · subst h3
    have e := eval_deltaPoly (![1, 0, 0, 0, 1] : Fin 5 → F)
    rw [h, map_zero, delta_witness₁] at e
    have : ((433 : ℕ) : F) = 0 := by push_cast; linear_combination e
    rw [CharP.cast_eq_zero_iff F 3] at this
    omega
  · have e := eval_deltaPoly (![0, 0, 1, 0, 0] : Fin 5 → F)
    rw [h, map_zero, delta_witness₂] at e
    have : ((3 ^ 3 : ℕ) : F) = 0 := by push_cast; linear_combination e
    rw [CharP.cast_eq_zero_iff F p] at this
    exact h3 ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_three).mp
      (hp.out.dvd_of_dvd_pow this))

/-- `D₀ = deg Δ` (over `ℤ`). -/
noncomputable def deltaDeg : ℕ := (deltaPoly ℤ).totalDegree

open scoped Classical in
/-- **Singular tuples**: `#{c : Δ(c) = 0} ≤ D₀ q⁴`. -/
theorem card_singular_le {F : Type*} [Field F] [Fintype F] (p : ℕ) [Fact p.Prime] [CharP F p] :
    #{c : Fin 5 → F | (wc c).Δ = 0} ≤ deltaDeg * Fintype.card F ^ 4 := by
  refine (card_le_card ?_).trans ((card_zero_set_le _ (deltaPoly_ne_zero F p)).trans ?_)
  · intro c hc
    simp only [mem_filter, mem_univ, true_and] at hc ⊢
    rw [eval_deltaPoly]; exact hc
  · exact Nat.mul_le_mul_right _ (totalDegree_deltaPoly_le F)

open scoped Classical in
/-- **The ordinary tuple count from below**: `q⁵ ≤ #{c : Δ ≠ 0, p ∤ a_c} + (D₀ + p) q⁴`. -/
theorem card_ordinary_lower {F : Type*} [Field F] [Fintype F] (p : ℕ) [Fact p.Prime]
    [CharP F p] :
    Fintype.card F ^ 5 ≤
      #{c : Fin 5 → F | (wc c).Δ ≠ 0 ∧ ¬ (p : ℤ) ∣ traceOfFrob (wc c)} +
        (deltaDeg + p) * Fintype.card F ^ 4 := by
  have hsing := card_singular_le (F := F) p
  have hss := card_dvd_traceOfFrob_le (F := F) p
  have huniv : (univ : Finset (Fin 5 → F)).card = Fintype.card F ^ 5 := by
    rw [card_univ, Fintype.card_fun, Fintype.card_fin]
  have h1 := card_filter_add_card_filter_not (s := (univ : Finset (Fin 5 → F)))
    (fun c => (wc c).Δ = 0)
  have h2 := card_filter_add_card_filter_not
    (s := (univ : Finset (Fin 5 → F)).filter (fun c => ¬ (wc c).Δ = 0))
    (fun c => (p : ℤ) ∣ traceOfFrob (wc c))
  rw [filter_filter, filter_filter] at h2
  have e1 : ((univ : Finset (Fin 5 → F)).filter
      (fun c => ¬ (wc c).Δ = 0 ∧ (p : ℤ) ∣ traceOfFrob (wc c))) =
      ({c : Fin 5 → F | (wc c).Δ ≠ 0 ∧ (p : ℤ) ∣ traceOfFrob (wc c)} : Finset _) := rfl
  have e2 : ((univ : Finset (Fin 5 → F)).filter
      (fun c => ¬ (wc c).Δ = 0 ∧ ¬ (p : ℤ) ∣ traceOfFrob (wc c))) =
      ({c : Fin 5 → F | (wc c).Δ ≠ 0 ∧ ¬ (p : ℤ) ∣ traceOfFrob (wc c)} : Finset _) := rfl
  rw [e1, e2] at h2
  rw [← huniv, ← h1, ← h2, add_mul]
  have : #({c : Fin 5 → F | (wc c).Δ = 0} : Finset _) =
      #((univ : Finset (Fin 5 → F)).filter (fun c => (wc c).Δ = 0)) := rfl
  omega

end RamanujanWeil.ArithPlan
