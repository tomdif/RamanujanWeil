import RamanujanWeil.Arith.DeuringDescentLang

/-!
# A3-ord, G7 C-descent: Lang's theorem for hyperelliptic model changes

`docs/ARITH_DEURING_G7_G2DESCENT.md` §2. Let `K = 𝔽_q`, `K̄` its algebraic closure, and `L` a
field over `K̄` (the function field `k̄(X)` of a genus-2 curve). Let `τ : L →+* L` be
`σ`-semilinear, `τ (c) = c^q` on `K̄` (the map `Ψ^♯` induced by a twisted Frobenius).

* **`Pres x y h f`**: a hyperelliptic presentation, `y² + h(x) y = f(x)`, `deg h ≤ 3`,
  `deg f ≤ 6`, `x` transcendental over `K̄`, `y ∉ K̄(x)`.
* **`MobForm K τ x y`**: `τ` acts by a model change,
  `τ x = (a x + b)/(c x + d)`, `τ y = (e y + p(x))/(c x + d)³` (`ad − bc ≠ 0`, `e ≠ 0`,
  `deg p ≤ 3`): this is "`Ψ` preserves the canonical map".
* Two elementary moves preserve `Pres` and `K̄(x, y)`: the inversion
  `x ↦ 1/(x − z)`, `y ↦ y/(x − z)³` (`pres_inv`, via `invPoly`, `X^n p(z + 1/X)`) and the
  affine change `x ↦ u x + v`, `y ↦ e y + p(x)` (`pres_aff`).
* **Lang's theorem for the model group, by hand** (`exists_fixed_of_mobForm`):
  1. a root `z` of `c z^{q+1} + d z^q − a z − b` (degree `q + 1` when `c ≠ 0`) is a
     `τ`-fixed point of `ℙ¹`; inverting at it makes `τ` affine on `x` (`affForm_of_mobForm`);
  2. `u^{q-1} = u_τ⁻¹` and `v^q = v − u^q v_τ` make `x` fixed (`fixForm_of_affForm`);
  3. `e'^{q-1} = e⁻¹` and `p_i^q = p_i − e'^q b_i` make `y` fixed (`fixed_of_fixForm`).
* **`exists_model_of_fixed`**: for `τ`-fixed `x, y`, applying `τ` to the relation and using
  `y ∉ K̄(x)` and the transcendence of `x` forces `h^σ = h`, `f^σ = f`: the model is defined
  over `K`.
* **`exists_descended_model`**: the composite.
-/

open Polynomial

universe u v

noncomputable section

namespace RamanujanWeil.Arith.Deuring.Geom.G7.Genus2Descent

open RamanujanWeil.Arith.Deuring.Descent RamanujanWeil.Arith.Deuring.Geom.Descent

/-! ## Polynomial preliminaries -/

section Poly

variable {F : Type*} [Field F]

/-- `X^n p(z + 1/X)`, a polynomial when `deg p ≤ n`. -/
def invPoly (n : ℕ) (z : F) (p : F[X]) : F[X] :=
  ∑ i ∈ Finset.range (n + 1), C (p.coeff i) * (C z * X + 1) ^ i * X ^ (n - i)

theorem natDegree_linear_le' (z : F) : (C z * X + 1 : F[X]).natDegree ≤ 1 :=
  (natDegree_add_le _ _).trans
    (max_le ((natDegree_C_mul_le _ _).trans natDegree_X_le) (by rw [natDegree_one]; omega))

theorem natDegree_invPoly_le (n : ℕ) (z : F) (p : F[X]) : (invPoly n z p).natDegree ≤ n := by
  refine natDegree_sum_le_of_forall_le _ _ fun i hi => ?_
  have hi' : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  refine natDegree_mul_le.trans ?_
  have h1 : (C (p.coeff i) * (C z * X + 1) ^ i).natDegree ≤ i := by
    refine (natDegree_C_mul_le _ _).trans (natDegree_pow_le.trans ?_)
    calc i * (C z * X + 1 : F[X]).natDegree ≤ i * 1 :=
          Nat.mul_le_mul_left _ (natDegree_linear_le' z)
      _ = i := mul_one i
  have h2 : (X ^ (n - i) : F[X]).natDegree ≤ n - i := natDegree_X_pow_le _
  omega

variable {A : Type*} [Field A] [Algebra F A]

theorem aeval_invPoly (n : ℕ) (z : F) {p : F[X]} (hp : p.natDegree ≤ n) {x t : A}
    (ht : t * (x - algebraMap F A z) = 1) :
    aeval t (invPoly n z p) = t ^ n * aeval x p := by
  have htx : algebraMap F A z * t + 1 = t * x := by linear_combination -ht
  rw [aeval_eq_sum_range' (Nat.lt_succ_of_le hp), Finset.mul_sum, invPoly, map_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  simp only [map_mul, map_pow, aeval_C, map_add, aeval_X, map_one, htx, Algebra.smul_def]
  rw [mul_pow, ← pow_mul_pow_sub t hi']
  ring

theorem natDegree_comp_linear_le {p : F[X]} {n : ℕ} (hp : p.natDegree ≤ n) (a b : F) :
    (p.comp (C a * (X - C b))).natDegree ≤ n := by
  refine natDegree_comp_le.trans ?_
  have : (C a * (X - C b)).natDegree ≤ 1 :=
    (natDegree_C_mul_le _ _).trans (by rw [natDegree_X_sub_C])
  calc p.natDegree * (C a * (X - C b)).natDegree ≤ n * 1 := Nat.mul_le_mul hp this
    _ = n := mul_one n

end Poly

/-! ## Presentations -/

set_option linter.unusedSectionVars false

variable {K : Type u} [Field K] [Fintype K]

local notation "K̄" => AlgebraicClosure K

variable {L : Type v} [Field L] [Algebra (AlgebraicClosure K) L]

local notation "ι" => algebraMap (AlgebraicClosure K) L

variable (K) in
/-- `K̄(x)`. -/
abbrev E (x : L) : IntermediateField (AlgebraicClosure K) L :=
  IntermediateField.adjoin (AlgebraicClosure K) {x}

variable (K) in
/-- `K̄(x, y)`. -/
abbrev E₂ (x y : L) : IntermediateField (AlgebraicClosure K) L :=
  IntermediateField.adjoin (AlgebraicClosure K) {x, y}

/-- **A hyperelliptic presentation** of `L`: `y² + h(x) y = f(x)`, `deg h ≤ 3`, `deg f ≤ 6`,
`x` transcendental, `y ∉ K̄(x)`. -/
structure Pres (x y : L) (h f : (AlgebraicClosure K)[X]) : Prop where
  rel : y ^ 2 + aeval x h * y = aeval x f
  deg_h : h.natDegree ≤ 3
  deg_f : f.natDegree ≤ 6
  trans : Transcendental (AlgebraicClosure K) x
  not_mem : y ∉ E K x

theorem aeval_mem_E (x : L) (p : (AlgebraicClosure K)[X]) : aeval x p ∈ E K x :=
  IntermediateField.algebra_adjoin_le_adjoin _ _ (aeval_mem_adjoin_singleton _ x)

theorem transcendental_of_mem {x x₁ : L} (hx : Transcendental (AlgebraicClosure K) x)
    (hmem : x ∈ E K x₁) : Transcendental (AlgebraicClosure K) x₁ := by
  intro h1
  have := IntermediateField.isAlgebraic_adjoin_simple h1.isIntegral
  exact hx ((IntermediateField.isAlgebraic_iff).mp
    (Algebra.IsAlgebraic.isAlgebraic (⟨x, hmem⟩ : E K x₁)))

theorem sub_algebraMap_ne_zero {x : L} (hx : Transcendental (AlgebraicClosure K) x)
    (z : AlgebraicClosure K) : x - ι z ≠ 0 := by
  intro h
  rw [sub_eq_zero] at h
  exact hx (h ▸ isAlgebraic_algebraMap z)

/-- **A change of presentation.** If `K̄(x₁) = K̄(x)` and `y₁ = r y + s` with `r ≠ 0`,
`r, s ∈ K̄(x)`, and the new relation holds, then `Pres` transfers and `K̄(x₁, y₁) = K̄(x, y)`. -/
theorem Pres.change {x y : L} {h f : (AlgebraicClosure K)[X]} (hP : Pres x y h f)
    {x₁ y₁ : L} {h₁ f₁ : (AlgebraicClosure K)[X]} (hE : E K x₁ = E K x) {r s : L} (hr : r ∈ E K x)
    (hr0 : r ≠ 0) (hs : s ∈ E K x) (hy : y₁ = r * y + s)
    (rel : y₁ ^ 2 + aeval x₁ h₁ * y₁ = aeval x₁ f₁) (deg_h : h₁.natDegree ≤ 3)
    (deg_f : f₁.natDegree ≤ 6) : Pres x₁ y₁ h₁ f₁ ∧ E₂ K x₁ y₁ = E₂ K x y := by
  have hxmem : x ∈ E K x₁ := hE ▸ IntermediateField.mem_adjoin_simple_self _ x
  have hyy : y = (y₁ - s) / r := by rw [hy]; field_simp; ring
  have hEx : E K x ≤ E₂ K x y :=
    IntermediateField.adjoin.mono _ _ _ (Set.singleton_subset_iff.mpr (Set.mem_insert _ _))
  have hEx₁ : E K x₁ ≤ E₂ K x₁ y₁ :=
    IntermediateField.adjoin.mono _ _ _ (Set.singleton_subset_iff.mpr (Set.mem_insert _ _))
  have hy₁mem : y₁ ∈ E₂ K x₁ y₁ := IntermediateField.subset_adjoin _ _ (by simp)
  have hymem : y ∈ E₂ K x y := IntermediateField.subset_adjoin _ _ (by simp)
  refine ⟨⟨rel, deg_h, deg_f, transcendental_of_mem hP.trans hxmem, ?_⟩, ?_⟩
  · intro hmem
    rw [hE] at hmem
    exact hP.not_mem (hyy ▸ div_mem (sub_mem hmem hs) hr)
  · apply le_antisymm
    · rw [IntermediateField.adjoin_le_iff]
      rintro w (rfl | rfl)
      · exact hEx (hE ▸ IntermediateField.mem_adjoin_simple_self _ w)
      · rw [hy]; exact add_mem (mul_mem (hEx hr) hymem) (hEx hs)
    · rw [IntermediateField.adjoin_le_iff]
      rintro w (rfl | rfl)
      · exact hEx₁ hxmem
      · rw [hyy]
        exact div_mem (sub_mem hy₁mem (hEx₁ (hE ▸ hs))) (hEx₁ (hE ▸ hr))

/-- **The inversion move** `x₁ = 1/(x − z)`, `y₁ = y x₁³`. -/
theorem pres_inv {x y : L} {h f : (AlgebraicClosure K)[X]} (hP : Pres x y h f)
    (z : AlgebraicClosure K) :
    Pres (x - ι z)⁻¹ (y * (x - ι z)⁻¹ ^ 3) (invPoly 3 z h) (invPoly 6 z f) ∧
      E₂ K (x - ι z)⁻¹ (y * (x - ι z)⁻¹ ^ 3) = E₂ K x y := by
  have hxz := sub_algebraMap_ne_zero hP.trans z
  set t := (x - ι z)⁻¹ with ht
  have ht1 : t * (x - ι z) = 1 := inv_mul_cancel₀ hxz
  have htmem : t ∈ E K x :=
    inv_mem (sub_mem (IntermediateField.mem_adjoin_simple_self _ x)
      (IntermediateField.algebraMap_mem _ z))
  have hEt : E K t = E K x := by
    apply le_antisymm
    · exact IntermediateField.adjoin_simple_le_iff.mpr htmem
    · refine IntermediateField.adjoin_simple_le_iff.mpr ?_
      have hx : x = ι z + t⁻¹ := by rw [ht, inv_inv]; ring
      rw [hx]
      exact add_mem (IntermediateField.algebraMap_mem _ z)
        (inv_mem (IntermediateField.mem_adjoin_simple_self _ t))
  refine hP.change hEt (pow_mem htmem 3) (pow_ne_zero _ (inv_ne_zero hxz)) (zero_mem _)
    (by ring) ?_ (natDegree_invPoly_le _ _ _) (natDegree_invPoly_le _ _ _)
  rw [aeval_invPoly 3 z hP.deg_h ht1, aeval_invPoly 6 z hP.deg_f ht1]
  linear_combination t ^ 6 * hP.rel

theorem aeval_lin {u : AlgebraicClosure K} (hu : u ≠ 0) (v : AlgebraicClosure K) (x : L) :
    aeval (ι u * x + ι v) (C u⁻¹ * (X - C v)) = x := by
  have : ι u ≠ 0 := (_root_.map_ne_zero _).mpr hu
  simp only [map_mul, aeval_C, map_sub, aeval_X, map_inv₀]
  field_simp
  ring

/-- **The affine move** `x₁ = u x + v`, `y₁ = e y + p(x)`. -/
theorem pres_aff {x y : L} {h f : (AlgebraicClosure K)[X]} (hP : Pres x y h f)
    {u : AlgebraicClosure K} (hu : u ≠ 0) (v : AlgebraicClosure K) {e : AlgebraicClosure K}
    (he : e ≠ 0) {p : (AlgebraicClosure K)[X]} (hp : p.natDegree ≤ 3) :
    Pres (ι u * x + ι v) (ι e * y + aeval x p)
        ((C e * h - 2 * p).comp (C u⁻¹ * (X - C v)))
        ((C (e ^ 2) * f - p ^ 2 + C e * h * p).comp (C u⁻¹ * (X - C v))) ∧
      E₂ K (ι u * x + ι v) (ι e * y + aeval x p) = E₂ K x y := by
  have hxm : x ∈ E K x := IntermediateField.mem_adjoin_simple_self _ x
  have hx₁m : ι u * x + ι v ∈ E K x :=
    add_mem (mul_mem (IntermediateField.algebraMap_mem _ u) hxm)
      (IntermediateField.algebraMap_mem _ v)
  have hE : E K (ι u * x + ι v) = E K x := by
    apply le_antisymm
    · exact IntermediateField.adjoin_simple_le_iff.mpr hx₁m
    · refine IntermediateField.adjoin_simple_le_iff.mpr ?_
      have hm := aeval_mem_E (K := K) (ι u * x + ι v) (C u⁻¹ * (X - C v))
      rwa [aeval_lin hu] at hm
  refine hP.change hE (IntermediateField.algebraMap_mem _ e) ((_root_.map_ne_zero _).mpr he)
    (aeval_mem_E (K := K) x p) rfl ?_ ?_ ?_
  · rw [aeval_comp, aeval_comp, aeval_lin hu]
    simp only [map_sub, map_mul, map_add, map_pow, aeval_C]
    simp only [map_ofNat]
    linear_combination (ι e) ^ 2 * hP.rel
  · refine natDegree_comp_linear_le ?_ _ _
    refine (natDegree_sub_le _ _).trans (max_le ((natDegree_C_mul_le _ _).trans hP.deg_h) ?_)
    refine natDegree_mul_le.trans ?_
    have : (2 : (AlgebraicClosure K)[X]).natDegree = 0 := natDegree_ofNat 2
    omega
  · refine natDegree_comp_linear_le ?_ _ _
    refine (natDegree_add_le _ _).trans (max_le ((natDegree_sub_le _ _).trans (max_le
      ((natDegree_C_mul_le _ _).trans hP.deg_f) ?_)) ?_)
    · exact natDegree_pow_le.trans (by omega)
    · refine natDegree_mul_le.trans ?_
      have := (natDegree_C_mul_le e h).trans hP.deg_h
      omega

/-! ## The Frobenius forms -/

variable (τ : L →+* L)

variable (K) in
/-- `τ` acts on `(x, y)` by a model change: `τ x = (a x + b)/(c x + d)`,
`τ y = (e y + p(x))/(c x + d)³`. -/
def MobForm (x y : L) : Prop :=
  ∃ a b c d : AlgebraicClosure K, a * d - b * c ≠ 0 ∧ ∃ e : AlgebraicClosure K, e ≠ 0 ∧
    ∃ p : (AlgebraicClosure K)[X], p.natDegree ≤ 3 ∧
      τ x * (ι c * x + ι d) = ι a * x + ι b ∧ τ y * (ι c * x + ι d) ^ 3 = ι e * y + aeval x p

variable (K) in
/-- `τ` is affine on `x`: `τ x = u x + v`, `τ y = e y + b(x)`. -/
def AffForm (x y : L) : Prop :=
  ∃ u w e : AlgebraicClosure K, u ≠ 0 ∧ e ≠ 0 ∧ ∃ b : (AlgebraicClosure K)[X],
    b.natDegree ≤ 3 ∧ τ x = ι u * x + ι w ∧ τ y = ι e * y + aeval x b

variable (K) in
/-- `τ` fixes `x`: `τ x = x`, `τ y = e y + b(x)`. -/
def FixForm (x y : L) : Prop :=
  ∃ e : AlgebraicClosure K, e ≠ 0 ∧ ∃ b : (AlgebraicClosure K)[X], b.natDegree ≤ 3 ∧
    τ x = x ∧ τ y = ι e * y + aeval x b

variable (K) in
/-- `τ` is `σ`-semilinear: `τ c = c^q` on `K̄`. -/
def IsFrobSemilinear : Prop :=
  ∀ c : AlgebraicClosure K, τ (ι c) = ι (c ^ Fintype.card K)

variable {τ}

theorem eq_map_of_map_frobQ_eq {p : (AlgebraicClosure K)[X]} (hp : p.map frobQ = p) :
    ∃ p₀ : K[X], p₀.map (algebraMap K (AlgebraicClosure K)) = p ∧ p₀.natDegree = p.natDegree := by
  have hl : p ∈ lifts (algebraMap K (AlgebraicClosure K)) := by
    rw [lifts_iff_coeff_lifts]
    intro n
    have : frobQ (p.coeff n) = p.coeff n := by rw [← coeff_map, hp]
    obtain ⟨a, ha⟩ := (frobQ_eq_iff _).mp this
    exact ⟨a, ha⟩
  obtain ⟨p₀, hp₀⟩ := (mem_lifts p).mp hl
  refine ⟨p₀, hp₀, ?_⟩
  rw [← hp₀, natDegree_map_eq_of_injective (algebraMap K (AlgebraicClosure K)).injective]

section Frob

variable (hτ : IsFrobSemilinear K τ)
include hτ

theorem τ_aeval (x : L) (p : (AlgebraicClosure K)[X]) :
    τ (aeval x p) = aeval (τ x) (p.map frobQ) := by
  have h1 : τ.comp ι = (algebraMap (AlgebraicClosure K) L).comp frobQ := by
    refine RingHom.ext fun c => ?_
    show τ (ι c) = ι (frobQ c)
    rw [frobQ_apply]; exact hτ c
  rw [aeval_def, aeval_def, eval₂_map, ← h1]
  exact hom_eval₂ p ι τ x

/-- **Step 1: a fixed point of `ℙ¹`.** Inverting at a `τ`-fixed point makes `τ` affine. -/
theorem affForm_of_mobForm {x y : L} {h f : (AlgebraicClosure K)[X]} (hP : Pres x y h f)
    (hF : MobForm K τ x y) :
    ∃ x₁ y₁ : L, ∃ h₁ f₁ : (AlgebraicClosure K)[X], Pres x₁ y₁ h₁ f₁ ∧ E₂ K x₁ y₁ = E₂ K x y ∧
      AffForm K τ x₁ y₁ := by
  obtain ⟨a, b, c, d, hdet, e, he, p, hp, hx, hy⟩ := hF
  set q := Fintype.card K with hq
  have hq2 : 2 ≤ q := two_le_card
  by_cases hc : c = 0
  · subst hc
    have hd : d ≠ 0 := by rintro rfl; simp at hdet
    have ha : a ≠ 0 := by rintro rfl; simp at hdet
    have hd' : ι d ≠ 0 := (_root_.map_ne_zero _).mpr hd
    simp only [map_zero, zero_mul, zero_add] at hx hy
    refine ⟨x, y, h, f, hP, rfl, a / d, b / d, e / d ^ 3, div_ne_zero ha hd,
      div_ne_zero he (pow_ne_zero _ hd), C (d ^ 3)⁻¹ * p,
      (natDegree_C_mul_le _ _).trans hp, ?_, ?_⟩
    · rw [map_div₀, map_div₀]; field_simp; linear_combination hx
    · rw [map_mul, aeval_C, map_div₀, map_pow, map_inv₀, map_pow]
      field_simp
      linear_combination hy
  · -- a root of `-c X^{q+1} - d X^q + a X + b`
    let P : (AlgebraicClosure K)[X] := C (-c) * X ^ (q + 1) + (C (-d) * X ^ q + C a * X + C b)
    have hdegP : P.degree = (q + 1 : ℕ) := by
      have h1 : (C (-c) * X ^ (q + 1) : (AlgebraicClosure K)[X]).degree = (q + 1 : ℕ) :=
        degree_C_mul_X_pow _ (neg_ne_zero.mpr hc)
      have h2 : (C (-d) * X ^ q + C a * X + C b : (AlgebraicClosure K)[X]).degree < (q + 1 : ℕ) := by
        refine lt_of_le_of_lt (b := (q : WithBot ℕ)) ?_ (by exact_mod_cast Nat.lt_succ_self q)
        refine (degree_add_le _ _).trans (max_le ((degree_add_le _ _).trans (max_le ?_ ?_)) ?_)
        · exact degree_C_mul_X_pow_le _ _
        · exact (degree_C_mul_X_le _).trans (by exact_mod_cast (by omega : 1 ≤ q))
        · exact degree_C_le.trans (by exact_mod_cast Nat.zero_le q)
      rw [degree_add_eq_left_of_degree_lt (h1 ▸ h2), h1]
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_root P (by rw [hdegP]; exact_mod_cast Nat.succ_ne_zero q)
    have hz' : -c * z ^ (q + 1) + (-d * z ^ q + a * z + b) = 0 := by
      have := hz; simp only [P, IsRoot, eval_add, eval_mul, eval_C, eval_pow, eval_X] at this
      exact this
    set Z := z ^ q with hZ
    have hzq : z ^ (q + 1) = Z * z := by rw [pow_succ]
    rw [hzq] at hz'
    set k := a - c * Z with hk
    have hk0 : k ≠ 0 := by
      intro h0
      have ha : a = c * Z := by rw [hk] at h0; linear_combination h0
      have hb : b = d * Z := by rw [ha] at hz'; linear_combination hz'
      apply hdet; rw [ha, hb]; ring
    have hu0 : c * z + d ≠ 0 := by
      intro h0
      have hd : d = -(c * z) := by linear_combination h0
      have hb : b = -(a * z) := by rw [hd] at hz'; linear_combination hz'
      apply hdet; rw [hd, hb]; ring
    obtain ⟨hP₁, hE₁⟩ := pres_inv hP z
    refine ⟨_, _, _, _, hP₁, hE₁, (c * z + d) / k, c / k, e / k ^ 3, div_ne_zero hu0 hk0,
      div_ne_zero he (pow_ne_zero _ hk0), C (k ^ 3)⁻¹ * invPoly 3 z p,
      (natDegree_C_mul_le _ _).trans (natDegree_invPoly_le _ _ _), ?_, ?_⟩
    all_goals
      have hxz := sub_algebraMap_ne_zero hP.trans z
      have hD : ι c * x + ι d ≠ 0 := by
        intro h0
        have : x = ι (-d / c) := by
          rw [map_div₀, map_neg]; field_simp [(_root_.map_ne_zero ι).mpr hc]; linear_combination h0
        exact hP.trans (this ▸ isAlgebraic_algebraMap _)
      have hk' : ι k ≠ 0 := (_root_.map_ne_zero _).mpr hk0
      have hroot : ι (-c * (Z * z) + (-d * Z + a * z + b)) = 0 := by rw [hz', map_zero]
      simp only [map_add, map_mul, map_neg] at hroot
      have key : (τ x - ι Z) * (ι c * x + ι d) = ι k * (x - ι z) := by
        rw [hk, map_sub, map_mul]; linear_combination hx + hroot
      have hτt : τ (x - ι z)⁻¹ = (ι c * x + ι d) * (x - ι z)⁻¹ * (ι k)⁻¹ := by
        rw [map_inv₀, map_sub, hτ z, ← hZ, (eq_mul_inv_iff_mul_eq₀ hD).mpr key, mul_inv, mul_inv,
          inv_inv]
        ring
    · rw [hτt, map_div₀, map_div₀, map_add, map_mul]
      field_simp
      ring
    · rw [map_mul, map_pow, hτt, map_mul, aeval_C, aeval_invPoly 3 z hp (inv_mul_cancel₀ hxz),
        map_div₀, map_pow, map_inv₀, map_pow]
      have hy' : τ y = (ι e * y + aeval x p) / (ι c * x + ι d) ^ 3 := by
        field_simp; linear_combination hy
      rw [hy']
      field_simp

/-- **Step 2: fix `x`.** `U^{q-1} = u⁻¹`, `V^q = V − U^q w`. -/
theorem fixForm_of_affForm {x y : L} {h f : (AlgebraicClosure K)[X]} (hP : Pres x y h f)
    (hF : AffForm K τ x y) :
    ∃ x₁ y₁ : L, ∃ h₁ f₁ : (AlgebraicClosure K)[X], Pres x₁ y₁ h₁ f₁ ∧ E₂ K x₁ y₁ = E₂ K x y ∧
      FixForm K τ x₁ y₁ := by
  obtain ⟨u, w, e, hu, he, b, hb, hx, hy⟩ := hF
  obtain ⟨U, hU⟩ := exists_unit_pow (K := K) (Units.mk0 u⁻¹ (inv_ne_zero hu))
  obtain ⟨V, hV⟩ := exists_pow_card_eq (K := K) 1 (-((U : AlgebraicClosure K) ^ Fintype.card K * w))
  have hU0 : (U : AlgebraicClosure K) ≠ 0 := U.ne_zero
  obtain ⟨hP₁, hE₁⟩ := pres_aff hP hU0 V one_ne_zero (p := 0) (by simp)
  simp only [map_one, one_mul, map_zero, add_zero] at hP₁ hE₁
  refine ⟨_, _, _, _, hP₁, hE₁, e, he, b.comp (C (U : AlgebraicClosure K)⁻¹ * (X - C V)),
    natDegree_comp_linear_le hb _ _, ?_, ?_⟩
  · rw [map_add, map_mul, hτ, hτ, hx, hV, hU]
    simp only [Units.val_mk0, map_add, map_mul, map_neg, map_inv₀, one_mul]
    have hu' : ι u ≠ 0 := (_root_.map_ne_zero _).mpr hu
    field_simp
    ring
  · rw [hy, aeval_comp, aeval_lin hU0]

/-- **Step 3: fix `y`.** `E^{q-1} = e⁻¹`, `P_i^q = P_i − E^q b_i`. -/
theorem fixed_of_fixForm {x y : L} {h f : (AlgebraicClosure K)[X]} (hP : Pres x y h f)
    (hF : FixForm K τ x y) :
    ∃ x₁ y₁ : L, ∃ h₁ f₁ : (AlgebraicClosure K)[X], Pres x₁ y₁ h₁ f₁ ∧ E₂ K x₁ y₁ = E₂ K x y ∧
      τ x₁ = x₁ ∧ τ y₁ = y₁ := by
  obtain ⟨e, he, b, hb, hx, hy⟩ := hF
  obtain ⟨Eu, hEu⟩ := exists_unit_pow (K := K) (Units.mk0 e⁻¹ (inv_ne_zero he))
  set E' : AlgebraicClosure K := (Eu : AlgebraicClosure K) with hE'
  have hE0 : E' ≠ 0 := Eu.ne_zero
  have hPc : ∀ i : ℕ, ∃ P : AlgebraicClosure K,
      P ^ Fintype.card K = 1 * P + -(E' ^ Fintype.card K * b.coeff i) :=
    fun i => exists_pow_card_eq (K := K) _ _
  choose P hPi using hPc
  let p : (AlgebraicClosure K)[X] := ∑ i ∈ Finset.range 4, C (P i) * X ^ i
  have hpdeg : p.natDegree ≤ 3 := by
    refine natDegree_sum_le_of_forall_le _ _ fun i hi => ?_
    exact (natDegree_C_mul_X_pow_le _ _).trans (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))
  have hpcoeff : ∀ n, p.coeff n = if n < 4 then P n else 0 := by
    intro n
    simp only [p, finsetSum_coeff, coeff_C_mul_X_pow]
    rw [Finset.sum_ite_eq]
    simp [Finset.mem_range]
  obtain ⟨hP₁, hE₁⟩ := pres_aff hP one_ne_zero 0 hE0 hpdeg
  simp only [map_one, one_mul, map_zero, add_zero] at hP₁ hE₁
  refine ⟨_, _, _, _, hP₁, hE₁, hx, ?_⟩
  have hpoly : C (E' ^ Fintype.card K) * b + p.map frobQ = p := by
    ext n
    rw [coeff_add, coeff_C_mul, coeff_map, hpcoeff, frobQ_apply]
    split_ifs with hn
    · rw [hPi n]; ring
    · rw [coeff_eq_zero_of_natDegree_lt (by omega : b.natDegree < n)]
      simp [zero_pow (by have := two_le_card (K := K); omega : Fintype.card K ≠ 0)]
  rw [map_add, map_mul, hτ, hy, τ_aeval hτ, hx]
  conv_rhs => rw [← hpoly]
  rw [hE', hEu]
  simp only [Units.val_mk0, map_add, map_mul, aeval_C, map_inv₀]
  have he' : ι e ≠ 0 := (_root_.map_ne_zero _).mpr he
  field_simp
  ring

/-- **Lang for the model group**: from a model-change Frobenius form to fixed generators. -/
theorem exists_fixed_of_mobForm {x y : L} {h f : (AlgebraicClosure K)[X]} (hP : Pres x y h f)
    (hF : MobForm K τ x y) :
    ∃ x₁ y₁ : L, ∃ h₁ f₁ : (AlgebraicClosure K)[X], Pres x₁ y₁ h₁ f₁ ∧ E₂ K x₁ y₁ = E₂ K x y ∧
      τ x₁ = x₁ ∧ τ y₁ = y₁ := by
  obtain ⟨x₁, y₁, h₁, f₁, hP₁, hE₁, hA⟩ := affForm_of_mobForm hτ hP hF
  obtain ⟨x₂, y₂, h₂, f₂, hP₂, hE₂, hB⟩ := fixForm_of_affForm hτ hP₁ hA
  obtain ⟨x₃, y₃, h₃, f₃, hP₃, hE₃, hx₃, hy₃⟩ := fixed_of_fixForm hτ hP₂ hB
  exact ⟨x₃, y₃, h₃, f₃, hP₃, hE₃.trans (hE₂.trans hE₁), hx₃, hy₃⟩

/-- **A fixed presentation is defined over `K`.** -/
theorem exists_model_of_fixed {x y : L} {h f : (AlgebraicClosure K)[X]} (hP : Pres x y h f)
    (hx : τ x = x) (hy : τ y = y) :
    ∃ h₀ f₀ : K[X], h₀.map (algebraMap K (AlgebraicClosure K)) = h ∧
      f₀.map (algebraMap K (AlgebraicClosure K)) = f ∧ h₀.natDegree ≤ 3 ∧ f₀.natDegree ≤ 6 := by
  have hrel' := congrArg τ hP.rel
  rw [map_add, map_mul, map_pow, τ_aeval hτ, τ_aeval hτ, hx, hy] at hrel'
  have hdiff : aeval x (h - h.map frobQ) * y = aeval x (f - f.map frobQ) := by
    rw [map_sub, map_sub]; linear_combination hP.rel - hrel'
  have hA : aeval x (h - h.map frobQ) = 0 := by
    by_contra hA
    apply hP.not_mem
    have : y = aeval x (f - f.map frobQ) / aeval x (h - h.map frobQ) := by
      rw [← hdiff]; field_simp
    rw [this]
    exact div_mem (aeval_mem_E (K := K) _ _) (aeval_mem_E (K := K) _ _)
  have hh : h.map frobQ = h := by
    by_contra hne
    exact hP.trans ⟨h - h.map frobQ, sub_ne_zero.mpr (Ne.symm hne), hA⟩
  rw [hA, zero_mul] at hdiff
  have hf : f.map frobQ = f := by
    by_contra hne
    exact hP.trans ⟨f - f.map frobQ, sub_ne_zero.mpr (Ne.symm hne), hdiff.symm⟩
  obtain ⟨h₀, hh₀, hdh⟩ := eq_map_of_map_frobQ_eq hh
  obtain ⟨f₀, hf₀, hdf⟩ := eq_map_of_map_frobQ_eq hf
  exact ⟨h₀, f₀, hh₀, hf₀, hdh ▸ hP.deg_h, hdf ▸ hP.deg_f⟩

/-- **Descent of a hyperelliptic presentation with a model-change Frobenius.** There are
`τ`-fixed `x', y'` generating the same field, with a relation `y'² + h₀(x') y' = f₀(x')` over
`K`. -/
theorem exists_descended_model {x y : L} {h f : (AlgebraicClosure K)[X]} (hP : Pres x y h f)
    (hF : MobForm K τ x y) :
    ∃ x' y' : L, ∃ h₀ f₀ : K[X],
      Pres x' y' (h₀.map (algebraMap K (AlgebraicClosure K)))
        (f₀.map (algebraMap K (AlgebraicClosure K))) ∧
      E₂ K x' y' = E₂ K x y ∧ τ x' = x' ∧ τ y' = y' ∧ h₀.natDegree ≤ 3 ∧ f₀.natDegree ≤ 6 := by
  obtain ⟨x₁, y₁, h₁, f₁, hP₁, hE₁, hx₁, hy₁⟩ := exists_fixed_of_mobForm hτ hP hF
  obtain ⟨h₀, f₀, hh₀, hf₀, hdh, hdf⟩ := exists_model_of_fixed hτ hP₁ hx₁ hy₁
  exact ⟨x₁, y₁, h₀, f₀, hh₀ ▸ hf₀ ▸ hP₁, hE₁, hx₁, hy₁, hdh, hdf⟩

end Frob

end RamanujanWeil.Arith.Deuring.Geom.G7.Genus2Descent
