import RamanujanWeil.Arith.HurwitzPrimeSquareCount

/-!
# A1′: the Hurwitz prime-square relation

`H(p²N) = (p + 1 − (−N/p)) H(N) − p·[p² ∣ N]·H(N/p²)` for `N ≡ 0, 3 (mod 4)`, for the reduced-form
Hurwitz class number `hurwitz` (`H = 2·mass`, `mass(X) = Σ_{O ∈ X/SL₂ℤ} 1/#Stab(O)`).

Proof (all masses are `wmass SL(2,ℤ)`, `h(N) = mass(Form N)`, `T = ℙ¹(𝔽_p)`):

1. `mass(Form N × T) = (p + 1)·h(N)` (`wmass_fiber`, fibres `≅ T`).
2. `mass(Form N × T) = mass_{Γ⁰}(Form N)`, `Γ⁰ = Stab(t₀) = {p ∣ γ₀₁}` (`wmass_induced`).
3. `f ↦ (a, pb, p²c)` is an equivariant bijection `Form N ≅ {g ∈ Form(p²N) : p ∣ b, p² ∣ c}`
   twisted by `γ ↦ diag(1,p)·γ·diag(1,p)⁻¹ : Γ⁰ ≅ Γ₀ = Stab(t₁)` (`wmass_equivariant`).
4. `Y₂ = {(g, t) : g ∈ Form(p²N), g integral on the superlattice of t}`;
   `mass(Y₂) = mass_{Γ₀}(fibre over t₁)` (`wmass_induced`) and
   `mass(Y₂) = Σ_{[g]} r(g)/#Stab(g)`, `r(g) = #{t : cond g t}` (`wmass_fiber`).
5. `r(g) = 1` for `p`-primitive `g` and `r(p f) = #{roots of f on T}`
   `= 1 + (−N/p)` (`f` primitive) or `p + 1` (`p ∣ f`).

Combining: `(p + 1) h(N) = h(p²N) + (−N/p) h(N) + p·[p² ∣ N] h(N/p²)`.
-/

namespace RamanujanWeil.Arith.Hurwitz

open QF Matrix MulAction
open scoped MatrixGroups

set_option linter.unusedSectionVars false

noncomputable section

/-! ### Finiteness -/

theorem finite_stabilizer {N : ℕ} (f : Form N) : Finite (stabilizer SL(2, ℤ) f) := by
  obtain ⟨γ, hγ⟩ := exists_reduced f
  have h := card_stabilizer_reduced (γ • f) hγ
  rw [card_stabilizer_smul] at h
  apply Nat.finite_of_card_ne_zero
  rw [h]
  split_ifs <;> norm_num

instance finite_classes (N : ℕ) : Finite (Classes N) := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · have : IsEmpty (Form 0) := ⟨fun f => by
      have h1 := f.2.1
      have h2 := f.2.2.1
      rw [h1] at h2
      simp at h2⟩
    infer_instance
  · have : Finite (Red N) := Finite.of_equiv _ (pairEquiv hN)
    exact Finite.of_surjective _ (toClass_bijective N).2

/-- `h(N) = mass(Form N)`. -/
noncomputable def hm (N : ℕ) : ℚ := wmass SL(2, ℤ) (Form N) (fun _ => 1)

theorem hurwitz_eq_two_hm {N : ℕ} (hN : 0 < N) : hurwitz N = 2 * hm N := by
  rw [hurwitz_eq_hurwitzOrbit hN, hurwitzOrbit, hm, wmass, mul_finsum]
  exact finsum_congr fun O => by ring

lemma finsum_const_eq {α : Type*} [Finite α] (c : ℚ) : ∑ᶠ _ : α, c = Nat.card α * c := by
  let _ := Fintype.ofFinite α
  rw [finsum_eq_sum_of_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    Nat.card_eq_fintype_card]

/-! ### Scaling by `p` -/

variable {p : ℕ} [Fact p.Prime]

lemma p_pos : 0 < (p : ℤ) := by exact_mod_cast (Fact.out : p.Prime).pos

lemma disc_scale (f : QF) : (scale p f).disc = (p : ℤ) ^ 2 * f.disc := by
  simp only [scale, disc]; ring

/-- `f ↦ p·f`, `Form N → Form (p²N)`. -/
def scaleForm (N : ℕ) (f : Form N) : Form (p ^ 2 * N) :=
  ⟨scale p f.1, by rw [disc_scale, f.2.1]; push_cast; ring, by
    rw [disc_scale]; exact mul_neg_of_pos_of_neg (by have := p_pos (p := p); positivity) f.2.2.1,
    by simp only [scale]; exact mul_pos p_pos f.2.2.2⟩

lemma scale_smul (γ : SL(2, ℤ)) (f : QF) : scale p (γ • f) = γ • scale p f := by
  rw [smul_def, smul_def]
  simp only [scale, act, eval, QF.mk.injEq]
  refine ⟨?_, ?_, ?_⟩ <;> ring

lemma scaleForm_smul (N : ℕ) (γ : SL(2, ℤ)) (f : Form N) :
    scaleForm (p := p) N (γ • f) = γ • scaleForm N f :=
  Subtype.ext (scale_smul γ f.1)

lemma scaleForm_injective (N : ℕ) : Function.Injective (scaleForm (p := p) N) := by
  intro f f' h
  have h' := congrArg Subtype.val h
  simp only [scaleForm, scale, QF.mk.injEq] at h'
  have hp0 : (p : ℤ) ≠ 0 := p_pos.ne'
  apply Subtype.ext
  ext
  · exact mul_left_cancel₀ hp0 h'.1
  · exact mul_left_cancel₀ hp0 h'.2.1
  · exact mul_left_cancel₀ hp0 h'.2.2

/-- A form of discriminant `−p²N` divisible by `p` is `p·f`. -/
lemma exists_scaleForm {N : ℕ} (g : Form (p ^ 2 * N))
    (h : (p : ℤ) ∣ g.1.a ∧ (p : ℤ) ∣ g.1.b ∧ (p : ℤ) ∣ g.1.c) :
    ∃ f : Form N, scaleForm N f = g := by
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩, ⟨c, hc⟩⟩ := h
  have hp0 : (p : ℤ) ≠ 0 := p_pos.ne'
  have hd := g.2.1
  have hg : g.1 = scale p ⟨a, b, c⟩ := by
    ext <;> simp [scale, ha, hb, hc]
  rw [hg, disc_scale] at hd
  push_cast at hd
  have hd' : QF.disc ⟨a, b, c⟩ = -(N : ℤ) := by
    have : (p : ℤ) ^ 2 * (QF.disc ⟨a, b, c⟩ + N) = 0 := by linear_combination hd
    rcases mul_eq_zero.mp this with h | h
    · exact absurd (pow_eq_zero_iff two_ne_zero |>.mp h) hp0
    · linarith
  have hpos := g.2.2.2
  rw [hg] at hpos
  simp only [scale] at hpos
  have ha0 : 0 < a := pos_of_mul_pos_right hpos p_pos.le
  have hdneg : QF.disc ⟨a, b, c⟩ < 0 := by
    have := g.2.2.1
    rw [hg, disc_scale] at this
    exact neg_of_mul_neg_right this (by positivity)
  exact ⟨⟨⟨a, b, c⟩, hd', hdneg, ha0⟩, Subtype.ext hg.symm⟩

/-! ### The conjugation `diag(1, p)` -/

/-- `f(x, py) = (a, pb, p²c)`. -/
def upQF (p : ℕ) (f : QF) : QF := ⟨f.a, p * f.b, p ^ 2 * f.c⟩

lemma disc_up (f : QF) : (upQF p f).disc = (p : ℤ) ^ 2 * f.disc := by
  simp only [upQF, disc]; ring

def upForm (N : ℕ) (f : Form N) : Form (p ^ 2 * N) :=
  ⟨upQF p f.1, by rw [disc_up, f.2.1]; push_cast; ring, by
    rw [disc_up]; exact mul_neg_of_pos_of_neg (by have := p_pos (p := p); positivity) f.2.2.1,
    f.2.2.2⟩

lemma cond_up (N : ℕ) (f : Form N) : cond (upForm (p := p) N f).1 (t1 (p := p)) := by
  rw [t1, cond_ptZ_iff]
  refine ⟨⟨f.1.c, ?_⟩, ⟨f.1.b, ?_⟩, ⟨2 * p * f.1.c, ?_⟩⟩ <;>
    simp only [upForm, upQF, eval] <;> ring

lemma dvd_of_cond_t1 {g : QF} (h : cond g (t1 (p := p))) :
    (p : ℤ) ∣ g.b ∧ (p : ℤ) ^ 2 ∣ g.c := by
  rw [t1, cond_ptZ_iff] at h
  obtain ⟨h0, h1, -⟩ := h
  simp only [eval] at h0 h1
  exact ⟨by simpa using h1, by simpa using h0⟩

/-- The inverse of `upForm` on forms integral at `t₁`. -/
def downForm (N : ℕ) (g : Form (p ^ 2 * N)) (h : cond g.1 (t1 (p := p))) : Form N :=
  ⟨⟨g.1.a, g.1.b / p, g.1.c / p ^ 2⟩, by
    obtain ⟨⟨b, hb⟩, ⟨c, hc⟩⟩ := dvd_of_cond_t1 h
    have hp0 : (p : ℤ) ≠ 0 := p_pos.ne'
    have hd := g.2.1
    simp only [disc, hb, hc] at hd ⊢
    rw [Int.mul_ediv_cancel_left _ hp0, Int.mul_ediv_cancel_left _ (pow_ne_zero 2 hp0)]
    push_cast at hd
    have : (p : ℤ) ^ 2 * (b ^ 2 - 4 * g.1.a * c + N) = 0 := by linear_combination hd
    rcases mul_eq_zero.mp this with h | h
    · exact absurd (pow_eq_zero_iff two_ne_zero |>.mp h) hp0
    · linarith, by
    obtain ⟨⟨b, hb⟩, ⟨c, hc⟩⟩ := dvd_of_cond_t1 h
    have hp0 : (p : ℤ) ≠ 0 := p_pos.ne'
    have hd := g.2.2.1
    simp only [disc, hb, hc] at hd ⊢
    rw [Int.mul_ediv_cancel_left _ hp0, Int.mul_ediv_cancel_left _ (pow_ne_zero 2 hp0)]
    have : (p : ℤ) ^ 2 * (b ^ 2 - 4 * g.1.a * c) < 0 := by linear_combination hd
    exact neg_of_mul_neg_right this (by positivity), g.2.2.2⟩

lemma up_down (N : ℕ) (g : Form (p ^ 2 * N)) (h : cond g.1 (t1 (p := p))) :
    upForm N (downForm N g h) = g := by
  obtain ⟨⟨b, hb⟩, ⟨c, hc⟩⟩ := dvd_of_cond_t1 h
  have hp0 : (p : ℤ) ≠ 0 := p_pos.ne'
  apply Subtype.ext
  ext
  · rfl
  · change (p : ℤ) * (g.1.b / p) = g.1.b
    rw [hb, Int.mul_ediv_cancel_left _ hp0]
  · change (p : ℤ) ^ 2 * (g.1.c / p ^ 2) = g.1.c
    rw [hc, Int.mul_ediv_cancel_left _ (pow_ne_zero 2 hp0)]

lemma down_up (N : ℕ) (f : Form N) :
    downForm N (upForm (p := p) N f) (cond_up N f) = f := by
  have hp0 : (p : ℤ) ≠ 0 := p_pos.ne'
  apply Subtype.ext
  ext
  · rfl
  · change (p : ℤ) * f.1.b / p = f.1.b
    rw [Int.mul_ediv_cancel_left _ hp0]
  · change (p : ℤ) ^ 2 * f.1.c / p ^ 2 = f.1.c
    rw [Int.mul_ediv_cancel_left _ (pow_ne_zero 2 hp0)]

/-- `β₀ = β / p` for `γ ∈ Stab(t₀)`. -/
lemma entry01 (h : stabilizer SL(2, ℤ) (t0 (p := p))) :
    h.1 0 1 = p * (h.1 0 1 / p) :=
  (Int.mul_ediv_cancel' ((mem_stabilizer_t0 h.1).mp h.2)).symm

lemma entry10 (h : stabilizer SL(2, ℤ) (t1 (p := p))) :
    h.1 1 0 = p * (h.1 1 0 / p) :=
  (Int.mul_ediv_cancel' ((mem_stabilizer_t1 h.1).mp h.2)).symm

/-- `γ ↦ diag(1,p) γ diag(1,p)⁻¹ = [[α, β/p], [pγ', δ]]`. -/
def sigmaFwd (h : stabilizer SL(2, ℤ) (t0 (p := p))) : stabilizer SL(2, ℤ) (t1 (p := p)) :=
  ⟨mkSL (h.1 0 0) (h.1 0 1 / p) (p * h.1 1 0) (h.1 1 1) (by
      have e := entry01 h
      have d := det_entries h.1
      linear_combination d + (h.1 1 0) * e), by
    rw [mem_stabilizer_t1]
    exact ⟨h.1 1 0, rfl⟩⟩

def sigmaBwd (h : stabilizer SL(2, ℤ) (t1 (p := p))) : stabilizer SL(2, ℤ) (t0 (p := p)) :=
  ⟨mkSL (h.1 0 0) (p * h.1 0 1) (h.1 1 0 / p) (h.1 1 1) (by
      have e := entry10 h
      have d := det_entries h.1
      linear_combination d + (h.1 0 1) * e), by
    rw [mem_stabilizer_t0]
    exact ⟨h.1 0 1, rfl⟩⟩

def sigmaEquiv : stabilizer SL(2, ℤ) (t0 (p := p)) ≃ stabilizer SL(2, ℤ) (t1 (p := p)) where
  toFun := sigmaFwd
  invFun := sigmaBwd
  left_inv h := by
    have hp0 : (p : ℤ) ≠ 0 := p_pos.ne'
    have e := entry01 h
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j
    · rfl
    · change (p : ℤ) * (h.1 0 1 / p) = h.1 0 1
      exact e.symm
    · change (p : ℤ) * h.1 1 0 / p = h.1 1 0
      rw [Int.mul_ediv_cancel_left _ hp0]
    · rfl
  right_inv h := by
    have hp0 : (p : ℤ) ≠ 0 := p_pos.ne'
    have e := entry10 h
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j
    · rfl
    · change (p : ℤ) * h.1 0 1 / p = h.1 0 1
      rw [Int.mul_ediv_cancel_left _ hp0]
    · change (p : ℤ) * (h.1 1 0 / p) = h.1 1 0
      exact e.symm
    · rfl

lemma up_smul (h : stabilizer SL(2, ℤ) (t0 (p := p))) (f : QF) :
    upQF p ((h : SL(2, ℤ)) • f) = (sigmaEquiv h : SL(2, ℤ)) • upQF p f := by
  have e := entry01 h
  change upQF p (act (h.1 0 0) (h.1 0 1) (h.1 1 0) (h.1 1 1) f) =
    act (h.1 0 0) (h.1 0 1 / p) (p * h.1 1 0) (h.1 1 1) (upQF p f)
  generalize h.1 0 1 / p = β₀ at e ⊢
  rw [e]
  simp only [upQF, act, eval, QF.mk.injEq]
  refine ⟨?_, ?_, ?_⟩ <;> ring

/-! ### The superlattice set `Y₂` -/

variable (p) in
/-- `Y₂ = {(g, t) : g integral on the index-p superlattice of t}`. -/
def Y2 (N : ℕ) : SubMulAction SL(2, ℤ) (Form (p ^ 2 * N) × P1 p) where
  carrier := {z | cond z.1.1 z.2}
  smul_mem' γ _ hz := cond_smul γ hz

variable (p) in
def sndHom (N : ℕ) : Form N × P1 p →[SL(2, ℤ)] P1 p where
  toFun := Prod.snd
  map_smul' _ _ := rfl

variable (p) in
def tau2 (N : ℕ) : Y2 p N →[SL(2, ℤ)] P1 p where
  toFun y := y.1.2
  map_smul' _ _ := rfl

lemma cond_of_fib2 (N : ℕ) (y : Fib (tau2 p N) t1) : cond y.1.1.1.1 (t1 (p := p)) := by
  obtain ⟨⟨⟨g, t⟩, h⟩, ht⟩ := y
  change t = t1 at ht
  subst ht
  exact h

/-- The twisted bijection of fibres `(f, t₀) ↦ ((a, pb, p²c), t₁)`. -/
def phiEquiv (N : ℕ) : Fib (sndHom p N) t0 ≃ Fib (tau2 p N) t1 where
  toFun z := ⟨⟨(upForm N z.1.1, t1), cond_up N z.1.1⟩, rfl⟩
  invFun y := ⟨(downForm N y.1.1.1 (cond_of_fib2 N y), t0), rfl⟩
  left_inv z := by
    apply Subtype.ext
    apply Prod.ext
    · exact down_up N z.1.1
    · exact z.2.symm
  right_inv y := by
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · exact up_down N _ (cond_of_fib2 N y)
    · exact (y.2 : y.1.1.2 = t1).symm

lemma phiEquiv_smul (N : ℕ) (h : stabilizer SL(2, ℤ) (t0 (p := p)))
    (z : Fib (sndHom p N) t0) :
    phiEquiv N (h • z) = sigmaEquiv h • phiEquiv N z := by
  apply Subtype.ext
  apply Subtype.ext
  apply Prod.ext
  · apply Subtype.ext
    exact up_smul h z.1.1.1
  · exact ((sigmaEquiv h).2 : (sigmaEquiv h : SL(2, ℤ)) • t1 = t1).symm

/-! ### The mass identity -/

lemma transitive_t1 (t : P1 p) : ∃ γ : SL(2, ℤ), γ • t1 = t := by
  obtain ⟨γ, hγ⟩ := exists_smul_t0 t
  obtain ⟨γ₁, hγ₁⟩ := exists_smul_t0 (t1 (p := p))
  refine ⟨γ * γ₁⁻¹, ?_⟩
  rw [mul_smul, ← hγ₁, inv_smul_smul, hγ]

/-- The fibre of `Form N × T → Form N`. -/
def fstFiberEquiv (N : ℕ) (f : Form N) : {y : Form N × P1 p // y.1 = f} ≃ P1 p where
  toFun y := y.1.2
  invFun t := ⟨(f, t), rfl⟩
  left_inv y := by obtain ⟨⟨f', t⟩, rfl⟩ := y; rfl
  right_inv _ := rfl

/-- `(p + 1)·h(N) = mass(Y₂)`. -/
theorem mass_Y2 (N : ℕ) :
    ((p : ℚ) + 1) * hm N = wmass SL(2, ℤ) (Y2 p N) (fun _ => 1) := by
  -- step 1: fibres of `Form N × T → Form N`
  have h1 : wmass SL(2, ℤ) (Form N × P1 p) (fun _ => 1) = ((p : ℚ) + 1) * hm N := by
    rw [wmass_fiber (Y := Form N × P1 p) Prod.fst (fun _ _ => rfl) finite_stabilizer
      (fun f => Finite.of_equiv (P1 p) (fstFiberEquiv N f).symm) _ (fun _ _ => rfl)]
    rw [hm, ← wmass_const_mul]
    refine wmass_congr fun f => ?_
    have : Finite {y : Form N × P1 p // y.1 = f} :=
      Finite.of_equiv (P1 p) (fstFiberEquiv N f).symm
    rw [finsum_const_eq, mul_one, mul_one, Nat.card_congr (fstFiberEquiv N f), card_P1]
    push_cast; ring
  rw [← h1, wmass_induced (sndHom p N) t0 exists_smul_t0 _ (fun _ _ => rfl),
    wmass_induced (tau2 p N) t1 transitive_t1 _ (fun _ _ => rfl)]
  exact wmass_equivariant sigmaEquiv (phiEquiv N) (phiEquiv_smul N) (fun _ => 1)
    (fun _ _ => rfl)

/-- Number of superlattices on which `g` is integral. -/
noncomputable def rr (N : ℕ) (g : Form (p ^ 2 * N)) : ℚ := Nat.card {t : P1 p // cond g.1 t}

/-- Number of roots of `f` on `ℙ¹(𝔽_p)`. -/
noncomputable def rr' (N : ℕ) (f : Form N) : ℚ := Nat.card {t : P1 p // cond' (p := p) f.1 t}

theorem mass_Y2_eq (N : ℕ) :
    wmass SL(2, ℤ) (Y2 p N) (fun _ => 1) = wmass SL(2, ℤ) (Form (p ^ 2 * N)) (rr N) := by
  have hF : ∀ g : Form (p ^ 2 * N), {y : Y2 p N // y.1.1 = g} ≃ {t : P1 p // cond g.1 t} :=
    fun g =>
    { toFun := fun y => ⟨y.1.1.2, by obtain ⟨⟨⟨g', t⟩, h⟩, rfl⟩ := y; exact h⟩
      invFun := fun t => ⟨⟨(g, t.1), t.2⟩, rfl⟩
      left_inv := fun y => by obtain ⟨⟨⟨g', t⟩, h⟩, rfl⟩ := y; rfl
      right_inv := fun _ => rfl }
  rw [wmass_fiber (Y := Y2 p N) (fun y => y.1.1) (fun _ _ => rfl) finite_stabilizer
    (fun g => Finite.of_equiv _ (hF g).symm) _ (fun _ _ => rfl)]
  refine wmass_congr fun g => ?_
  have : Finite {y : Y2 p N // y.1.1 = g} := Finite.of_equiv _ (hF g).symm
  rw [finsum_const_eq, mul_one, Nat.card_congr (hF g)]
  rfl

lemma rr'_smul (N : ℕ) (γ : SL(2, ℤ)) (f : Form N) :
    rr' (p := p) N (γ • f) = rr' (p := p) N f := by
  unfold rr'
  rw [form_smul_val, card_cond'_smul]

/-- `r(g) = 1 + Σ_{p f = g} (r'(f) − 1)`. -/
theorem rr_eq (N : ℕ) (hN : N % 4 = 0 ∨ N % 4 = 3) (g : Form (p ^ 2 * N)) :
    rr N g = 1 + ∑ᶠ f : {f : Form N // scaleForm N f = g}, (rr' (p := p) N f.1 - 1) := by
  by_cases hdiv : (p : ℤ) ∣ g.1.a ∧ (p : ℤ) ∣ g.1.b ∧ (p : ℤ) ∣ g.1.c
  · obtain ⟨f, rfl⟩ := exists_scaleForm g hdiv
    rw [finsum_eq_single _ (⟨f, rfl⟩ : {f' : Form N // scaleForm (p := p) N f' = scaleForm N f})
      (fun x hx => absurd (Subtype.ext (scaleForm_injective N x.2)) hx)]
    unfold rr rr'
    rw [show (scaleForm (p := p) N f).1 = scale p f.1 from rfl,
      Nat.card_congr (Equiv.subtypeEquivRight (cond_scale_iff f.1))]
    ring
  · have : IsEmpty {f : Form N // scaleForm (p := p) N f = g} :=
      ⟨fun f => hdiv (by rw [← f.2]; simp only [scaleForm, scale]; exact
        ⟨dvd_mul_right _ _, dvd_mul_right _ _, dvd_mul_right _ _⟩)⟩
    rw [finsum_of_isEmpty, add_zero]
    unfold rr
    rw [card_cond_eq_one (N := N) (by rw [g.2.1]; push_cast; ring) hN hdiv]
    norm_num

theorem mass_rr (N : ℕ) (hN : N % 4 = 0 ∨ N % 4 = 3) :
    wmass SL(2, ℤ) (Form (p ^ 2 * N)) (rr N) =
      hm (p ^ 2 * N) + wmass SL(2, ℤ) (Form N) (fun f => rr' (p := p) N f - 1) := by
  rw [wmass_congr (rr_eq N hN), wmass_add, hm]
  congr 1
  symm
  refine wmass_fiber (scaleForm N) (scaleForm_smul N) finite_stabilizer
    (fun g => ?_) _ (fun γ f => by rw [rr'_smul])
  have : Subsingleton {f : Form N // scaleForm (p := p) N f = g} :=
    ⟨fun x y => Subtype.ext (scaleForm_injective N (x.2.trans y.2.symm))⟩
  infer_instance

/-- `Σ_{[f]} (r'(f) − 1)/#Stab = (−N/p)·h(N) + p·[p² ∣ N]·h(N/p²)`. -/
theorem mass_rr' (N : ℕ) :
    wmass SL(2, ℤ) (Form N) (fun f => rr' (p := p) N f - 1) =
      (ArithPlan.kron (-(N : ℤ)) p : ℚ) * hm N +
        (if p ^ 2 ∣ N then (p : ℚ) * hm (N / p ^ 2) else 0) := by
  have hdiscf : ∀ {M : ℕ} (f : Form M), f.1.disc = -(M : ℤ) := fun f => f.2.1
  by_cases hpN : p ^ 2 ∣ N
  · obtain ⟨M, rfl⟩ := hpN
    have hk : ArithPlan.kron (-((p ^ 2 * M : ℕ) : ℤ)) p = 0 :=
      kron_eq_zero_of_dvd ⟨-(p * M : ℤ), by push_cast; ring⟩
    have hpos : 0 < p ^ 2 := pow_pos (Fact.out : p.Prime).pos 2
    rw [if_pos (dvd_mul_right _ _), Nat.mul_div_cancel_left _ hpos, hk, Int.cast_zero, zero_mul,
      zero_add, hm, ← wmass_const_mul]
    have hfib : ∀ f : Form (p ^ 2 * M), rr' (p := p) (p ^ 2 * M) f - 1 =
        ∑ᶠ f' : {f' : Form M // scaleForm (p := p) M f' = f}, ((p : ℚ) * 1) := by
      intro f
      by_cases hdiv : (p : ℤ) ∣ f.1.a ∧ (p : ℤ) ∣ f.1.b ∧ (p : ℤ) ∣ f.1.c
      · obtain ⟨f', rfl⟩ := exists_scaleForm f hdiv
        rw [finsum_eq_single _ (⟨f', rfl⟩ : {f'' : Form M // scaleForm (p := p) M f'' =
          scaleForm M f'}) (fun x hx => absurd (Subtype.ext (scaleForm_injective M x.2)) hx)]
        unfold rr'
        rw [card_cond'_of_dvd hdiv]
        push_cast; ring
      · have : IsEmpty {f' : Form M // scaleForm (p := p) M f' = f} :=
          ⟨fun f' => hdiv (by rw [← f'.2]; simp only [scaleForm, scale]; exact
            ⟨dvd_mul_right _ _, dvd_mul_right _ _, dvd_mul_right _ _⟩)⟩
        rw [finsum_of_isEmpty]
        unfold rr'
        have := card_cond'_prim (p := p) hdiv
        rw [hdiscf, hk] at this
        have h1 : (Nat.card {t : P1 p // cond' f.1 t} : ℚ) = 1 := by exact_mod_cast this
        rw [h1]; ring
    rw [wmass_congr hfib]
    symm
    refine wmass_fiber (scaleForm M) (scaleForm_smul M) finite_stabilizer
      (fun g => ?_) _ (fun _ _ => rfl)
    have : Subsingleton {f : Form M // scaleForm (p := p) M f = g} :=
      ⟨fun x y => Subtype.ext (scaleForm_injective M (x.2.trans y.2.symm))⟩
    infer_instance
  · rw [if_neg hpN, add_zero, hm, ← wmass_const_mul]
    refine wmass_congr fun f => ?_
    have hprim : ¬((p : ℤ) ∣ f.1.a ∧ (p : ℤ) ∣ f.1.b ∧ (p : ℤ) ∣ f.1.c) := by
      rintro ⟨⟨a, ha⟩, ⟨b, hb⟩, ⟨c, hc⟩⟩
      apply hpN
      have hd := hdiscf f
      simp only [disc, ha, hb, hc] at hd
      have : ((p ^ 2 : ℕ) : ℤ) ∣ (N : ℤ) := ⟨4 * a * c - b ^ 2, by push_cast; linarith⟩
      exact_mod_cast this
    have := card_cond'_prim (p := p) hprim
    rw [hdiscf] at this
    unfold rr'
    have h1 : (Nat.card {t : P1 p // cond' f.1 t} : ℚ) =
        1 + (ArithPlan.kron (-(N : ℤ)) p : ℚ) := by exact_mod_cast this
    rw [h1]; ring

/-- **The mass identity** `(p + 1) h(N) = h(p²N) + (−N/p) h(N) + p·[p² ∣ N] h(N/p²)`. -/
theorem hm_prime_square (N : ℕ) (hN : N % 4 = 0 ∨ N % 4 = 3) :
    ((p : ℚ) + 1) * hm N = hm (p ^ 2 * N) + (ArithPlan.kron (-(N : ℤ)) p : ℚ) * hm N +
      (if p ^ 2 ∣ N then (p : ℚ) * hm (N / p ^ 2) else 0) := by
  rw [mass_Y2, mass_Y2_eq, mass_rr N hN, mass_rr']
  ring

end

/-! ### The frozen statements -/

/-- **A1′ conventions.** -/
theorem hurwitzConventions : ArithPlan.HurwitzConventions hurwitz :=
  ⟨hurwitz_zero, fun _ h => hurwitz_eq_zero_of_mod_four h⟩

/-- **A1′: the Hurwitz prime-square relation** for every prime `p` (including `p = 2` and
`N = 0`, where both sides are `−1/12`). -/
theorem hurwitzPrimeSquare (p : ℕ) (hp : p.Prime) : ArithPlan.HurwitzPrimeSquare hurwitz p := by
  have : Fact p.Prime := ⟨hp⟩
  intro N hN
  rcases Nat.eq_zero_or_pos N with rfl | hNpos
  · have hk : ArithPlan.kron (-((0 : ℕ) : ℤ)) p = 0 := kron_eq_zero_of_dvd (by simp)
    rw [hk, if_pos (dvd_zero _), Nat.zero_div, mul_zero, hurwitz_zero]
    push_cast
    ring
  · have hpos : 0 < p ^ 2 := pow_pos hp.pos 2
    have h := hm_prime_square (p := p) N hN
    rw [hurwitz_eq_two_hm (Nat.mul_pos hpos hNpos), hurwitz_eq_two_hm hNpos]
    split_ifs with hdvd
    · rw [if_pos hdvd] at h
      have hM : 0 < N / p ^ 2 := Nat.div_pos (Nat.le_of_dvd hNpos hdvd) hpos
      rw [hurwitz_eq_two_hm hM]
      linear_combination (-2) * h
    · rw [if_neg hdvd] at h
      linear_combination (-2) * h

end RamanujanWeil.Arith.Hurwitz
