import RamanujanWeil.Arith.HurwitzPrimeSquareMass
import RamanujanWeil.Arith.HurwitzOrbit

/-!
# The projective line `ℙ¹(𝔽_p)` as an `SL₂(ℤ)`-set

`V2 p = 𝔽_p²` (row vectors) with `γ • v = v·γ⁻¹`, and `P1 p = ℙ(V2 p)` with the induced action
(Mathlib's `Projectivization` action). An index-`p` sublattice `ℓ ⊂ ℤ²` corresponds to the line
`ℓ / pℤ²`; superlattices `L ⊃ ℤ²` of index `p` correspond to `pL`.

* `ptZ u`: the point of an integer vector `u ≢ 0 (mod p)`; `smul_ptZ`: `γ • [u] = [u γ⁻¹]`.
* `enumP : Option (𝔽_p) → P1 p`, `none ↦ [1 : 0]`, `some j ↦ [j : 1]`, is a bijection, so
  `#P1 = p + 1` and `card_subtype_eq` counts subsets point by point.
* transitivity (`exists_smul_t0`) and the stabilizers of `t0 = [1 : 0]` (`p ∣ γ₀₁`) and of
  `t1 = [0 : 1]` (`p ∣ γ₁₀`).
-/

namespace RamanujanWeil.Arith.Hurwitz

open QF Matrix MulAction
open scoped MatrixGroups LinearAlgebra.Projectivization

set_option linter.unusedSectionVars false

variable (p : ℕ)

/-- Row vectors over `𝔽_p`. -/
def V2 : Type := ZMod p × ZMod p

instance : AddCommGroup (V2 p) := inferInstanceAs (AddCommGroup (ZMod p × ZMod p))
instance : Module (ZMod p) (V2 p) := inferInstanceAs (Module (ZMod p) (ZMod p × ZMod p))

/-- The vector `(x, y)`. -/
def v2 (x y : ZMod p) : V2 p := (x, y)

variable {p}

/-- First coordinate. -/
def V2.x (v : V2 p) : ZMod p := Prod.fst (α := ZMod p) (β := ZMod p) v
/-- Second coordinate. -/
def V2.y (v : V2 p) : ZMod p := Prod.snd (α := ZMod p) (β := ZMod p) v

@[simp] lemma v2_x (x y : ZMod p) : (v2 p x y).x = x := rfl
@[simp] lemma v2_y (x y : ZMod p) : (v2 p x y).y = y := rfl

lemma V2.ext' {v w : V2 p} (hx : v.x = w.x) (hy : v.y = w.y) : v = w := Prod.ext hx hy

lemma V2.eta (v : V2 p) : v2 p v.x v.y = v := rfl

@[simp] lemma V2.zero_x : (0 : V2 p).x = 0 := rfl
@[simp] lemma V2.zero_y : (0 : V2 p).y = 0 := rfl
@[simp] lemma V2.add_x (v w : V2 p) : (v + w).x = v.x + w.x := rfl
@[simp] lemma V2.add_y (v w : V2 p) : (v + w).y = v.y + w.y := rfl
@[simp] lemma V2.smul_x (a : ZMod p) (v : V2 p) : (a • v).x = a * v.x := rfl
@[simp] lemma V2.smul_y (a : ZMod p) (v : V2 p) : (a • v).y = a * v.y := rfl

lemma v2_ne_zero {x y : ZMod p} : v2 p x y ≠ 0 ↔ ¬(x = 0 ∧ y = 0) := by
  constructor
  · rintro h ⟨rfl, rfl⟩; exact h rfl
  · intro h h0; exact h ⟨congrArg V2.x h0, congrArg V2.y h0⟩

/-- `γ • v = v·γ⁻¹ = (x δ − y γ', −x β + y α)` for `γ = [[α, β], [γ', δ]]`. -/
def smulV2 (γ : SL(2, ℤ)) (v : V2 p) : V2 p :=
  v2 p (v.x * (γ 1 1 : ZMod p) - v.y * (γ 1 0 : ZMod p))
    (-(v.x * (γ 0 1 : ZMod p)) + v.y * (γ 0 0 : ZMod p))

instance : DistribMulAction SL(2, ℤ) (V2 p) where
  smul := smulV2
  one_smul v := by
    change smulV2 1 v = v
    apply V2.ext' <;> simp [smulV2]
  mul_smul γ δ v := by
    change smulV2 (γ * δ) v = smulV2 γ (smulV2 δ v)
    have h := det_entries γ
    have h' := det_entries δ
    have e : ∀ i j, ((γ * δ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) i j =
        γ i 0 * δ 0 j + γ i 1 * δ 1 j := by
      intro i j
      rw [Matrix.SpecialLinearGroup.coe_mul, mul_apply, Fin.sum_univ_two]
    apply V2.ext' <;>
    · simp only [smulV2, v2_x, v2_y, e]
      push_cast
      ring
  smul_zero γ := by
    change smulV2 γ 0 = 0
    apply V2.ext' <;> simp [smulV2]
  smul_add γ v w := by
    change smulV2 γ (v + w) = smulV2 γ v + smulV2 γ w
    apply V2.ext' <;> simp only [smulV2, v2_x, v2_y, V2.add_x, V2.add_y] <;> ring

lemma smul_v2_def (γ : SL(2, ℤ)) (v : V2 p) : γ • v = smulV2 γ v := rfl

instance : SMulCommClass SL(2, ℤ) (ZMod p) (V2 p) where
  smul_comm γ a v := by
    rw [smul_v2_def, smul_v2_def]
    apply V2.ext' <;> simp only [smulV2, v2_x, v2_y, V2.smul_x, V2.smul_y] <;> ring

variable (p) [Fact p.Prime]

/-- The projective line `ℙ¹(𝔽_p)`, an `SL₂(ℤ)`-set. -/
abbrev P1 : Type := ℙ (ZMod p) (V2 p)

variable {p}

/-- The point `[u mod p]` of an integer vector `u ≢ 0 (mod p)`. -/
noncomputable def ptZ (u : ℤ × ℤ) (hu : ¬((p : ℤ) ∣ u.1 ∧ (p : ℤ) ∣ u.2)) : P1 p :=
  Projectivization.mk (ZMod p) (v2 p (u.1 : ZMod p) (u.2 : ZMod p)) (by
    rw [v2_ne_zero]
    rwa [ZMod.intCast_zmod_eq_zero_iff_dvd, ZMod.intCast_zmod_eq_zero_iff_dvd])

/-- `u·γ⁻¹` for an integer row vector. -/
def mulInv (γ : SL(2, ℤ)) (u : ℤ × ℤ) : ℤ × ℤ :=
  (u.1 * γ 1 1 - u.2 * γ 1 0, -(u.1 * γ 0 1) + u.2 * γ 0 0)

/-- `u·γ⁻¹·γ = u`. -/
lemma mulInv_mul (γ : SL(2, ℤ)) (u : ℤ × ℤ) :
    (mulInv γ u).1 * γ 0 0 + (mulInv γ u).2 * γ 1 0 = u.1 ∧
      (mulInv γ u).1 * γ 0 1 + (mulInv γ u).2 * γ 1 1 = u.2 := by
  have h := det_entries γ
  simp only [mulInv]
  constructor
  · linear_combination u.1 * h
  · linear_combination u.2 * h

lemma mulInv_ndvd (γ : SL(2, ℤ)) {u : ℤ × ℤ} (hu : ¬((p : ℤ) ∣ u.1 ∧ (p : ℤ) ∣ u.2)) :
    ¬((p : ℤ) ∣ (mulInv γ u).1 ∧ (p : ℤ) ∣ (mulInv γ u).2) := by
  rintro ⟨h1, h2⟩
  apply hu
  obtain ⟨e1, e2⟩ := mulInv_mul γ u
  rw [← e1, ← e2]
  exact ⟨dvd_add (dvd_mul_of_dvd_left h1 _) (dvd_mul_of_dvd_left h2 _),
    dvd_add (dvd_mul_of_dvd_left h1 _) (dvd_mul_of_dvd_left h2 _)⟩

lemma smul_ptZ (γ : SL(2, ℤ)) (u : ℤ × ℤ) (hu : ¬((p : ℤ) ∣ u.1 ∧ (p : ℤ) ∣ u.2)) :
    γ • ptZ u hu = ptZ (mulInv γ u) (mulInv_ndvd γ hu) := by
  unfold ptZ
  rw [Projectivization.smul_mk]
  congr 1
  rw [smul_v2_def]
  apply V2.ext' <;> simp [smulV2, mulInv]

/-- Points `[u] = [u']` give `u' ≡ a u (mod p)` with `p ∤ a`. -/
lemma ptZ_eq_ptZ {u u' : ℤ × ℤ} (hu : ¬((p : ℤ) ∣ u.1 ∧ (p : ℤ) ∣ u.2))
    (hu' : ¬((p : ℤ) ∣ u'.1 ∧ (p : ℤ) ∣ u'.2)) (h : ptZ u hu = ptZ u' hu') :
    ∃ a : ℤ, ¬(p : ℤ) ∣ a ∧ (p : ℤ) ∣ u'.1 - a * u.1 ∧ (p : ℤ) ∣ u'.2 - a * u.2 := by
  unfold ptZ at h
  rw [eq_comm, Projectivization.mk_eq_mk_iff'] at h
  obtain ⟨a, ha⟩ := h
  have hx := congrArg V2.x ha
  have hy := congrArg V2.y ha
  simp only [V2.smul_x, V2.smul_y, v2_x, v2_y] at hx hy
  refine ⟨(a.val : ℤ), ?_, ?_, ?_⟩
  · rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    intro h0
    push_cast at h0
    rw [ZMod.natCast_zmod_val] at h0
    apply hu'
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, ← ZMod.intCast_zmod_eq_zero_iff_dvd, ← hx, ← hy,
      h0]
    simp
  · rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [ZMod.natCast_zmod_val, ← hx]
    ring
  · rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [ZMod.natCast_zmod_val, ← hy]
    ring

/-- Every point is `[u]` for an integer vector. -/
lemma exists_ptZ (t : P1 p) : ∃ u hu, ptZ (p := p) u hu = t := by
  induction t using Projectivization.ind with
  | h v hv =>
  have hu : ¬((p : ℤ) ∣ ((v.x.val : ℤ), (v.y.val : ℤ)).1 ∧ (p : ℤ) ∣ ((v.x.val : ℤ),
      (v.y.val : ℤ)).2) := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, ← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
    rintro ⟨h1, h2⟩
    exact hv (V2.ext' h1 h2)
  refine ⟨_, hu, ?_⟩
  unfold ptZ
  congr 1
  apply V2.ext' <;> simp

/-! ### Enumeration -/

lemma ndvd_10 : ¬((p : ℤ) ∣ (1 : ℤ) ∧ (p : ℤ) ∣ (0 : ℤ)) := by
  rintro ⟨h, -⟩
  have := Int.eq_one_of_dvd_one (by positivity) h
  have hp := (Fact.out : p.Prime).one_lt
  omega

lemma ndvd_j1 (j : ℤ) : ¬((p : ℤ) ∣ j ∧ (p : ℤ) ∣ (1 : ℤ)) := by
  rintro ⟨-, h⟩
  have := Int.eq_one_of_dvd_one (by positivity) h
  have hp := (Fact.out : p.Prime).one_lt
  omega

/-- `t0 = [1 : 0]`. -/
noncomputable def t0 : P1 p := ptZ (1, 0) ndvd_10

/-- `t1 = [0 : 1]`. -/
noncomputable def t1 : P1 p := ptZ (0, 1) (ndvd_j1 0)

/-- `none ↦ [1 : 0]`, `some j ↦ [j : 1]`. -/
noncomputable def enumP : Option (ZMod p) → P1 p
  | none => t0
  | some j => ptZ ((j.val : ℤ), 1) (ndvd_j1 _)

lemma enumP_some (j : ZMod p) :
    enumP (some j) = Projectivization.mk (ZMod p) (v2 p j 1) (by
      rw [v2_ne_zero]; rintro ⟨-, h⟩; exact one_ne_zero h) := by
  simp only [enumP, ptZ]
  congr 1
  apply V2.ext' <;> simp

lemma enumP_none : enumP (p := p) none =
    Projectivization.mk (ZMod p) (v2 p 1 0) (by
      rw [v2_ne_zero]; rintro ⟨h, -⟩; exact one_ne_zero h) := by
  simp only [enumP, t0, ptZ]
  congr 1
  apply V2.ext' <;> simp

theorem enumP_bijective : Function.Bijective (enumP (p := p)) := by
  constructor
  · intro o o' h
    cases o with
    | none =>
      cases o' with
      | none => rfl
      | some j' =>
        rw [enumP_none, enumP_some, Projectivization.mk_eq_mk_iff'] at h
        obtain ⟨a, ha⟩ := h
        have hy := congrArg V2.y ha
        have hx := congrArg V2.x ha
        simp only [V2.smul_x, V2.smul_y, v2_x, v2_y, mul_one] at hx hy
        rw [hy, zero_mul] at hx
        exact absurd hx.symm one_ne_zero
    | some j =>
      cases o' with
      | none =>
        rw [enumP_none, enumP_some, Projectivization.mk_eq_mk_iff'] at h
        obtain ⟨a, ha⟩ := h
        have hy := congrArg V2.y ha
        simp only [V2.smul_y, v2_y, mul_zero] at hy
        exact (zero_ne_one hy).elim
      | some j' =>
        rw [enumP_some, enumP_some, Projectivization.mk_eq_mk_iff'] at h
        obtain ⟨a, ha⟩ := h
        have hy := congrArg V2.y ha
        have hx := congrArg V2.x ha
        simp only [V2.smul_x, V2.smul_y, v2_x, v2_y, mul_one] at hx hy
        rw [hy, one_mul] at hx
        rw [hx]
  · intro t
    induction t using Projectivization.ind with
    | h v hv =>
    by_cases hy : v.y = 0
    · have hx : v.x ≠ 0 := fun hx => hv (V2.ext' hx hy)
      refine ⟨none, ?_⟩
      rw [enumP_none, Projectivization.mk_eq_mk_iff']
      refine ⟨v.x⁻¹, V2.ext' ?_ ?_⟩
      · simp [hx]
      · simp [hy]
    · refine ⟨some (v.x / v.y), ?_⟩
      rw [enumP_some, Projectivization.mk_eq_mk_iff']
      refine ⟨v.y⁻¹, V2.ext' ?_ ?_⟩
      · simp only [V2.smul_x, v2_x]; field_simp
      · simp [hy]

/-- `#ℙ¹(𝔽_p) = p + 1`. -/
theorem card_P1 : Nat.card (P1 p) = p + 1 := by
  rw [← Nat.card_congr (Equiv.ofBijective _ (enumP_bijective (p := p))), Nat.card_eq_fintype_card,
    Fintype.card_option, ZMod.card]

instance : Finite (P1 p) := Nat.finite_of_card_ne_zero (by rw [card_P1]; omega)

open scoped Classical in
/-- Counting a subset of `ℙ¹(𝔽_p)` point by point. -/
theorem card_subtype_eq (P : P1 p → Prop) :
    Nat.card {t // P t} = (if P (enumP none) then 1 else 0) +
      Nat.card {j : ZMod p // P (enumP (some j))} := by
  classical
  rw [← Nat.card_congr ((Equiv.ofBijective _ (enumP_bijective (p := p))).subtypeEquiv
    (p := fun o => P (enumP o)) (fun o => Iff.rfl))]
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_subtype,
    Fintype.card_subtype, Finset.card_filter, Finset.card_filter, Fintype.sum_option]

/-! ### Transitivity and stabilizers -/

theorem exists_smul_t0 (t : P1 p) : ∃ γ : SL(2, ℤ), γ • t0 = t := by
  obtain ⟨o, rfl⟩ := (enumP_bijective (p := p)).2 t
  cases o with
  | none => exact ⟨1, one_smul _ _⟩
  | some j =>
    refine ⟨mkSL 1 (-1) (1 - (j.val : ℤ)) (j.val : ℤ) (by ring), ?_⟩
    rw [t0, smul_ptZ]
    simp only [enumP]
    congr 1
    simp [mulInv, mkSL]

theorem mem_stabilizer_t0 (γ : SL(2, ℤ)) : γ ∈ stabilizer SL(2, ℤ) (t0 (p := p)) ↔
    (p : ℤ) ∣ γ 0 1 := by
  rw [mem_stabilizer_iff, t0, smul_ptZ]
  unfold ptZ
  rw [Projectivization.mk_eq_mk_iff']
  simp only [mulInv]
  constructor
  · rintro ⟨a, ha⟩
    have hy := congrArg V2.y ha
    simp only [V2.smul_y, v2_y] at hy
    push_cast at hy
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    linear_combination hy
  · intro h
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd] at h
    refine ⟨(γ 1 1 : ZMod p), V2.ext' ?_ ?_⟩ <;> simp [h]

theorem mem_stabilizer_t1 (γ : SL(2, ℤ)) : γ ∈ stabilizer SL(2, ℤ) (t1 (p := p)) ↔
    (p : ℤ) ∣ γ 1 0 := by
  rw [mem_stabilizer_iff, t1, smul_ptZ]
  unfold ptZ
  rw [Projectivization.mk_eq_mk_iff']
  simp only [mulInv]
  constructor
  · rintro ⟨a, ha⟩
    have hx := congrArg V2.x ha
    simp only [V2.smul_x, v2_x] at hx
    push_cast at hx
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    linear_combination hx
  · intro h
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd] at h
    refine ⟨(γ 0 0 : ZMod p), V2.ext' ?_ ?_⟩ <;> simp [h]

end RamanujanWeil.Arith.Hurwitz
