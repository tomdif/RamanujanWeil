import RamanujanWeil.Arith.HurwitzPrimeSquareP1
import RamanujanWeil.Arith.ArithVocab

/-!
# Local counts at `p`: superlattices and roots of a form on `ℙ¹(𝔽_p)`

For a form `g` and a line `t = [u] ∈ ℙ¹(𝔽_p)` (`u ∈ ℤ²`, `u ≢ 0 mod p`):

* `cond g t`: `g` is integral on the index-`p` superlattice `ℤ² + ℤ·u/p`, i.e.
  `p² ∣ g(u)`, `p ∣ B(e₁, u) = 2a u₁ + b u₂`, `p ∣ B(e₂, u) = b u₁ + 2c u₂` (`condZ`);
* `cond' f t`: `p ∣ f(u)` (`t` is a root of `f mod p`).

Both are independent of the lift `u` (`cond_ptZ_iff`, `cond'_ptZ_iff`) and `SL₂(ℤ)`-equivariant.
Counts:

* `card_cond_eq_one`: if `g` is `p`-primitive, `p² ∣ disc g` (and, for `p = 2`,
  `disc g = −4N` with `N ≡ 0, 3 mod 4`), exactly one superlattice works;
* `card_cond_scale`: for `g = p·f`, `cond g = cond' f`;
* `card_cond'_of_dvd`: `#{t : cond' f t} = p + 1` if `p ∣ f`;
* `card_cond'_prim`: `#{t : cond' f t} = 1 + (disc f / p)` (Kronecker) if `f` is `p`-primitive.
-/

namespace RamanujanWeil.Arith.Hurwitz

open QF Matrix MulAction
open scoped MatrixGroups

set_option linter.unusedSectionVars false

/-- The superlattice condition at an integer vector `u`. -/
def condZ (p : ℕ) (g : QF) (u : ℤ × ℤ) : Prop :=
  (p : ℤ) ^ 2 ∣ g.eval u.1 u.2 ∧ (p : ℤ) ∣ 2 * g.a * u.1 + g.b * u.2 ∧
    (p : ℤ) ∣ g.b * u.1 + 2 * g.c * u.2

variable {p : ℕ} [Fact p.Prime]

/-- `g` is integral on the index-`p` superlattice attached to `t`. -/
def cond (g : QF) (t : P1 p) : Prop := ∃ u hu, ptZ u hu = t ∧ condZ p g u

/-- `t` is a root of `f mod p`. -/
def cond' (f : QF) (t : P1 p) : Prop := ∃ u hu, ptZ u hu = t ∧ (p : ℤ) ∣ f.eval u.1 u.2

lemma condZ_of_ptZ_eq {g : QF} {u u' : ℤ × ℤ} (hu : ¬((p : ℤ) ∣ u.1 ∧ (p : ℤ) ∣ u.2))
    (hu' : ¬((p : ℤ) ∣ u'.1 ∧ (p : ℤ) ∣ u'.2)) (h : ptZ u hu = ptZ u' hu')
    (hc : condZ p g u) : condZ p g u' := by
  obtain ⟨a, -, ⟨k1, hk1⟩, ⟨k2, hk2⟩⟩ := ptZ_eq_ptZ hu hu' h
  obtain ⟨⟨m0, hm0⟩, ⟨m1, hm1⟩, ⟨m2, hm2⟩⟩ := hc
  have e1 : u'.1 = a * u.1 + p * k1 := by linarith
  have e2 : u'.2 = a * u.2 + p * k2 := by linarith
  refine ⟨⟨a ^ 2 * m0 + a * (k1 * m1 + k2 * m2) + g.eval k1 k2, ?_⟩,
    ⟨a * m1 + 2 * g.a * k1 + g.b * k2, ?_⟩, ⟨a * m2 + g.b * k1 + 2 * g.c * k2, ?_⟩⟩
  · rw [e1, e2]
    simp only [eval] at hm0 ⊢
    linear_combination a ^ 2 * hm0 + (p : ℤ) * a * k1 * hm1 + (p : ℤ) * a * k2 * hm2
  · rw [e1, e2]; linear_combination a * hm1
  · rw [e1, e2]; linear_combination a * hm2

lemma cond_ptZ_iff {g : QF} {u : ℤ × ℤ} (hu : ¬((p : ℤ) ∣ u.1 ∧ (p : ℤ) ∣ u.2)) :
    cond g (ptZ u hu) ↔ condZ p g u :=
  ⟨fun ⟨_, hu', h, hc⟩ => condZ_of_ptZ_eq hu' hu h hc, fun h => ⟨u, hu, rfl, h⟩⟩

lemma cond'_ptZ_iff {f : QF} {u : ℤ × ℤ} (hu : ¬((p : ℤ) ∣ u.1 ∧ (p : ℤ) ∣ u.2)) :
    cond' f (ptZ u hu) ↔ (p : ℤ) ∣ f.eval u.1 u.2 := by
  constructor
  · rintro ⟨u', hu', h, hc⟩
    obtain ⟨a, -, ⟨k1, hk1⟩, ⟨k2, hk2⟩⟩ := ptZ_eq_ptZ hu' hu h
    obtain ⟨m, hm⟩ := hc
    have e1 : u.1 = a * u'.1 + p * k1 := by linarith
    have e2 : u.2 = a * u'.2 + p * k2 := by linarith
    refine ⟨a ^ 2 * m + a * (k1 * (2 * f.a * u'.1 + f.b * u'.2) +
      k2 * (f.b * u'.1 + 2 * f.c * u'.2)) + p * f.eval k1 k2, ?_⟩
    rw [e1, e2]
    simp only [eval] at hm ⊢
    linear_combination a ^ 2 * hm
  · intro h; exact ⟨u, hu, rfl, h⟩

/-! ### Equivariance -/

lemma smul_eval (γ : SL(2, ℤ)) (g : QF) (x y : ℤ) :
    (γ • g).eval x y = g.eval (x * γ 0 0 + y * γ 1 0) (x * γ 0 1 + y * γ 1 1) := by
  rw [smul_def]; simp only [act, eval]; ring

lemma condZ_smul (γ : SL(2, ℤ)) (g : QF) (u : ℤ × ℤ) (h : condZ p g u) :
    condZ p (γ • g) (mulInv γ u) := by
  obtain ⟨e1, e2⟩ := mulInv_mul γ u
  obtain ⟨h0, h1, h2⟩ := h
  set x := (mulInv γ u).1
  set y := (mulInv γ u).2
  refine ⟨?_, ?_, ?_⟩
  · rw [smul_eval, e1, e2]; exact h0
  · have : 2 * (γ • g).a * x + (γ • g).b * y =
        γ 0 0 * (2 * g.a * (x * γ 0 0 + y * γ 1 0) + g.b * (x * γ 0 1 + y * γ 1 1)) +
          γ 0 1 * (g.b * (x * γ 0 0 + y * γ 1 0) + 2 * g.c * (x * γ 0 1 + y * γ 1 1)) := by
      rw [smul_def]; simp only [act, eval]; ring
    rw [this, e1, e2]
    exact dvd_add (dvd_mul_of_dvd_right h1 _) (dvd_mul_of_dvd_right h2 _)
  · have : (γ • g).b * x + 2 * (γ • g).c * y =
        γ 1 0 * (2 * g.a * (x * γ 0 0 + y * γ 1 0) + g.b * (x * γ 0 1 + y * γ 1 1)) +
          γ 1 1 * (g.b * (x * γ 0 0 + y * γ 1 0) + 2 * g.c * (x * γ 0 1 + y * γ 1 1)) := by
      rw [smul_def]; simp only [act, eval]; ring
    rw [this, e1, e2]
    exact dvd_add (dvd_mul_of_dvd_right h1 _) (dvd_mul_of_dvd_right h2 _)

lemma cond_smul (γ : SL(2, ℤ)) {g : QF} {t : P1 p} (h : cond g t) : cond (γ • g) (γ • t) := by
  obtain ⟨u, hu, rfl, hc⟩ := h
  exact ⟨_, mulInv_ndvd γ hu, (smul_ptZ γ u hu).symm, condZ_smul γ g u hc⟩

lemma cond'_smul (γ : SL(2, ℤ)) {f : QF} {t : P1 p} (h : cond' f t) :
    cond' (γ • f) (γ • t) := by
  obtain ⟨u, hu, rfl, hc⟩ := h
  refine ⟨_, mulInv_ndvd γ hu, (smul_ptZ γ u hu).symm, ?_⟩
  obtain ⟨e1, e2⟩ := mulInv_mul γ u
  rw [smul_eval, e1, e2]
  exact hc

lemma cond'_smul_iff (γ : SL(2, ℤ)) (f : QF) (t : P1 p) :
    cond' (γ • f) (γ • t) ↔ cond' f t := by
  refine ⟨fun h => ?_, cond'_smul γ⟩
  have := cond'_smul γ⁻¹ h
  rwa [inv_smul_smul, inv_smul_smul] at this

/-- The number of roots is an orbit invariant. -/
lemma card_cond'_smul (γ : SL(2, ℤ)) (f : QF) :
    Nat.card {t : P1 p // cond' (γ • f) t} = Nat.card {t : P1 p // cond' f t} :=
  Nat.card_congr ((MulAction.toPerm γ⁻¹ : Equiv.Perm (P1 p)).subtypeEquiv fun t => by
    change cond' (γ • f) t ↔ cond' f (γ⁻¹ • t)
    conv_lhs => rw [← smul_inv_smul γ t]
    exact cond'_smul_iff γ f _)

/-! ### Scaling by `p` -/

/-- `p · f`. -/
def scale (p : ℕ) (f : QF) : QF := ⟨p * f.a, p * f.b, p * f.c⟩

lemma cond_scale_iff (f : QF) (t : P1 p) : cond (scale p f) t ↔ cond' f t := by
  obtain ⟨u, hu, rfl⟩ := exists_ptZ t
  rw [cond_ptZ_iff, cond'_ptZ_iff]
  have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have he : (scale p f).eval u.1 u.2 = p * f.eval u.1 u.2 := by
    simp only [scale, eval]; ring
  unfold condZ
  rw [he, pow_two, mul_dvd_mul_iff_left hp0]
  constructor
  · exact fun h => h.1
  · intro h
    refine ⟨h, ⟨2 * f.a * u.1 + f.b * u.2, ?_⟩, ⟨f.b * u.1 + 2 * f.c * u.2, ?_⟩⟩ <;>
      simp only [scale] <;> ring

/-! ### Small arithmetic helpers -/

lemma prime_int : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp Fact.out

lemma eq_two_of_dvd_two (h : (p : ℤ) ∣ 2) : p = 2 := by
  have h' : p ∣ 2 := by exact_mod_cast h
  exact (Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).mp h'

lemma dvd_of_dvd_two_mul (hp2 : p ≠ 2) {a : ℤ} (h : (p : ℤ) ∣ 2 * a) : (p : ℤ) ∣ a := by
  rcases prime_int.dvd_or_dvd h with h | h
  · exact absurd (eq_two_of_dvd_two h) hp2
  · exact h

lemma sq_dvd_of_sq_dvd_four_mul (hp2 : p ≠ 2) {k m : ℤ} (hk : ¬(p : ℤ) ∣ k)
    (h : (p : ℤ) ^ 2 ∣ 4 * k * m) : (p : ℤ) ^ 2 ∣ m := by
  have h4 : ¬(p : ℤ) ∣ 4 * k := by
    intro h'
    rcases prime_int.dvd_or_dvd h' with h' | h'
    · have : (p : ℤ) ∣ 2 * 2 := by norm_num; exact h'
      exact hp2 (eq_two_of_dvd_two (dvd_of_dvd_two_mul hp2 this))
    · exact hk h'
  have hc : IsCoprime ((p : ℤ) ^ 2) (4 * k) :=
    ((Prime.coprime_iff_not_dvd prime_int).mpr h4).pow_left
  exact hc.dvd_of_dvd_mul_left h

lemma two_ne_zero_zmod (hp2 : p ≠ 2) : (2 : ZMod p) ≠ 0 := by
  intro h
  have : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
  rw [ZMod.natCast_eq_zero_iff] at this
  exact hp2 ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).mp this)

lemma intCast_eq_zero_iff {a : ℤ} : (a : ZMod p) = 0 ↔ (p : ℤ) ∣ a :=
  ZMod.intCast_zmod_eq_zero_iff_dvd a p

/-! ### Counting superlattices for a `p`-primitive form (`p` odd) -/

lemma ptZ_eq_of_det {u u' : ℤ × ℤ} (hu : ¬((p : ℤ) ∣ u.1 ∧ (p : ℤ) ∣ u.2))
    (hu' : ¬((p : ℤ) ∣ u'.1 ∧ (p : ℤ) ∣ u'.2)) (h : (p : ℤ) ∣ u.1 * u'.2 - u.2 * u'.1) :
    ptZ u hu = ptZ u' hu' := by
  unfold ptZ
  rw [Projectivization.mk_eq_mk_iff']
  rw [← intCast_eq_zero_iff] at h
  push_cast at h
  have hu'' : ¬((u'.1 : ZMod p) = 0 ∧ (u'.2 : ZMod p) = 0) := by
    rwa [intCast_eq_zero_iff, intCast_eq_zero_iff]
  by_cases h1 : (u'.1 : ZMod p) = 0
  · have h2 : (u'.2 : ZMod p) ≠ 0 := fun h2 => hu'' ⟨h1, h2⟩
    have h3 : (u.1 : ZMod p) = 0 := by
      rw [h1, mul_zero, sub_zero] at h
      exact (mul_eq_zero.mp h).resolve_right h2
    refine ⟨(u.2 : ZMod p) / u'.2, V2.ext' ?_ ?_⟩
    · simp [h1, h3]
    · simp only [V2.smul_y, v2_y]; field_simp
  · refine ⟨(u.1 : ZMod p) / u'.1, V2.ext' ?_ ?_⟩
    · simp only [V2.smul_x, v2_x]; field_simp
    · simp only [V2.smul_y, v2_y]; field_simp; linear_combination h

lemma dvd_all_of_two_cond (hp2 : p ≠ 2) {g : QF} {u u' : ℤ × ℤ} (hc : condZ p g u)
    (hc' : condZ p g u') (hΔ : ¬(p : ℤ) ∣ u.1 * u'.2 - u.2 * u'.1) :
    (p : ℤ) ∣ g.a ∧ (p : ℤ) ∣ g.b ∧ (p : ℤ) ∣ g.c := by
  obtain ⟨-, h1, h2⟩ := hc
  obtain ⟨-, h1', h2'⟩ := hc'
  have ea : 2 * g.a * (u.1 * u'.2 - u.2 * u'.1) =
      u'.2 * (2 * g.a * u.1 + g.b * u.2) - u.2 * (2 * g.a * u'.1 + g.b * u'.2) := by ring
  have eb : g.b * (u.1 * u'.2 - u.2 * u'.1) =
      u.1 * (2 * g.a * u'.1 + g.b * u'.2) - u'.1 * (2 * g.a * u.1 + g.b * u.2) := by ring
  have ec : 2 * g.c * (u.1 * u'.2 - u.2 * u'.1) =
      u.1 * (g.b * u'.1 + 2 * g.c * u'.2) - u'.1 * (g.b * u.1 + 2 * g.c * u.2) := by ring
  have da : (p : ℤ) ∣ 2 * g.a * (u.1 * u'.2 - u.2 * u'.1) := by
    rw [ea]; exact dvd_sub (dvd_mul_of_dvd_right h1 _) (dvd_mul_of_dvd_right h1' _)
  have db : (p : ℤ) ∣ g.b * (u.1 * u'.2 - u.2 * u'.1) := by
    rw [eb]; exact dvd_sub (dvd_mul_of_dvd_right h1' _) (dvd_mul_of_dvd_right h1 _)
  have dc : (p : ℤ) ∣ 2 * g.c * (u.1 * u'.2 - u.2 * u'.1) := by
    rw [ec]; exact dvd_sub (dvd_mul_of_dvd_right h2' _) (dvd_mul_of_dvd_right h2 _)
  refine ⟨?_, ?_, ?_⟩
  · exact dvd_of_dvd_two_mul hp2 ((prime_int.dvd_or_dvd da).resolve_right hΔ)
  · exact (prime_int.dvd_or_dvd db).resolve_right hΔ
  · exact dvd_of_dvd_two_mul hp2 ((prime_int.dvd_or_dvd dc).resolve_right hΔ)

lemma exists_condZ (hp2 : p ≠ 2) {g : QF} (hdisc : (p : ℤ) ^ 2 ∣ g.disc)
    (hprim : ¬((p : ℤ) ∣ g.a ∧ (p : ℤ) ∣ g.b ∧ (p : ℤ) ∣ g.c)) :
    ∃ u hu, cond g (ptZ (p := p) u hu) := by
  have hpd : (p : ℤ) ∣ g.disc := dvd_trans (dvd_pow_self _ two_ne_zero) hdisc
  by_cases ha : (p : ℤ) ∣ g.a
  · have hb : (p : ℤ) ∣ g.b := by
      have : g.b ^ 2 = g.disc + 4 * g.a * g.c := by unfold disc; ring
      have h' : (p : ℤ) ∣ g.b ^ 2 := by
        rw [this]; exact dvd_add hpd (dvd_mul_of_dvd_left (dvd_mul_of_dvd_right ha _) _)
      exact prime_int.dvd_of_dvd_pow h'
    have hc : ¬(p : ℤ) ∣ g.c := fun hc => hprim ⟨ha, hb, hc⟩
    refine ⟨(1, 0), ndvd_10, (cond_ptZ_iff _).mpr ⟨?_, ?_, ?_⟩⟩
    · have e : 4 * g.c * g.eval 1 0 = g.b ^ 2 - g.disc := by simp only [eval, disc]; ring
      apply sq_dvd_of_sq_dvd_four_mul hp2 hc
      rw [e]
      exact dvd_sub (pow_dvd_pow_of_dvd hb 2) hdisc
    · simpa using dvd_mul_of_dvd_right ha 2
    · simpa using hb
  · have hA : (g.a : ZMod p) ≠ 0 := by rwa [Ne, intCast_eq_zero_iff]
    have h2 := two_ne_zero_zmod hp2
    have hD : (g.b : ZMod p) ^ 2 - 4 * g.a * g.c = 0 := by
      have := (intCast_eq_zero_iff (p := p)).mpr hpd
      unfold disc at this; push_cast at this; exact this
    set xb : ZMod p := -(g.b : ZMod p) / (2 * g.a) with hxb
    have hxc : ((xb.val : ℤ) : ZMod p) = xb := by simp
    have h1 : (p : ℤ) ∣ 2 * g.a * (xb.val : ℤ) + g.b * 1 := by
      rw [← intCast_eq_zero_iff]; push_cast; rw [ZMod.natCast_zmod_val, hxb]
      field_simp; ring
    refine ⟨((xb.val : ℤ), 1), ndvd_j1 _, (cond_ptZ_iff _).mpr ⟨?_, h1, ?_⟩⟩
    · have e : 4 * g.a * g.eval (xb.val : ℤ) 1 = (2 * g.a * (xb.val : ℤ) + g.b * 1) ^ 2 - g.disc := by
        simp only [eval, disc]; ring
      apply sq_dvd_of_sq_dvd_four_mul hp2 ha
      rw [e]
      exact dvd_sub (pow_dvd_pow_of_dvd h1 2) hdisc
    · rw [← intCast_eq_zero_iff]; push_cast; rw [ZMod.natCast_zmod_val, hxb]
      field_simp
      linear_combination -hD

/-- **One superlattice** (`p` odd): a `p`-primitive form with `p² ∣ disc` is integral on exactly
one index-`p` superlattice. -/
theorem card_cond_odd (hp2 : p ≠ 2) {g : QF} (hdisc : (p : ℤ) ^ 2 ∣ g.disc)
    (hprim : ¬((p : ℤ) ∣ g.a ∧ (p : ℤ) ∣ g.b ∧ (p : ℤ) ∣ g.c)) :
    Nat.card {t : P1 p // cond g t} = 1 := by
  rw [Nat.card_eq_one_iff_unique]
  refine ⟨⟨fun t t' => Subtype.ext ?_⟩, ?_⟩
  · obtain ⟨u, hu, ht, hc⟩ := t.2
    obtain ⟨u', hu', ht', hc'⟩ := t'.2
    rw [← ht, ← ht']
    by_contra hne
    exact hprim (dvd_all_of_two_cond hp2 hc hc' fun hΔ => hne (ptZ_eq_of_det hu hu' hΔ))
  · obtain ⟨u, hu, h⟩ := exists_condZ hp2 hdisc hprim
    exact ⟨⟨_, h⟩⟩

/-! ### `p = 2` -/

lemma card_zmod2 (P : ZMod 2 → Prop) [DecidablePred P] :
    Nat.card {j : ZMod 2 // P j} = (if P 0 then 1 else 0) + (if P 1 then 1 else 0) := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.card_filter]
  rw [show (Finset.univ : Finset (ZMod 2)) = {0, 1} from rfl, Finset.sum_pair (by decide)]

lemma zmod4_check : ∀ A B C M : ZMod 4, B * B - A * C = -M → (M.val = 0 ∨ M.val = 3) →
    ¬(A.val % 2 = 0 ∧ C.val % 2 = 0) →
    (if A.val = 0 then 1 else 0) + (if C.val = 0 then 1 else 0) +
      (if (A + 2 * B + C).val = 0 then 1 else 0) = (1 : ℕ) := by
  decide

lemma val4 (a : ℤ) : (((a : ZMod 4).val : ℕ) : ℤ) = a % 4 := ZMod.val_intCast a

open scoped Classical in
/-- **One superlattice** (`p = 2`). -/
theorem card_cond_two {g : QF} {N : ℕ} (hdisc : g.disc = -(4 * (N : ℤ)))
    (hN : N % 4 = 0 ∨ N % 4 = 3) (hprim : ¬((2 : ℤ) ∣ g.a ∧ (2 : ℤ) ∣ g.b ∧ (2 : ℤ) ∣ g.c)) :
    Nat.card {t : P1 2 // cond g t} = 1 := by
  obtain ⟨a, b, c⟩ := g
  simp only [disc] at hdisc hprim
  have hb : (2 : ℤ) ∣ b := by
    have : b ^ 2 = 2 * (2 * (a * c - N)) := by linarith
    exact Int.prime_two.dvd_of_dvd_pow (Dvd.intro _ this.symm)
  obtain ⟨b', rfl⟩ := hb
  have hac : ¬((2 : ℤ) ∣ a ∧ (2 : ℤ) ∣ c) := fun h => hprim ⟨h.1, dvd_mul_right 2 b', h.2⟩
  have hid : b' * b' - a * c = -(N : ℤ) := by linarith
  rw [card_subtype_eq, card_zmod2]
  have e0 : cond (p := 2) ⟨a, 2 * b', c⟩ (enumP none) ↔ (4 : ℤ) ∣ a := by
    rw [enumP, t0, cond_ptZ_iff]
    simp only [condZ, eval]
    norm_num
  have e1 : cond (p := 2) ⟨a, 2 * b', c⟩ (enumP (some 0)) ↔ (4 : ℤ) ∣ c := by
    rw [enumP, cond_ptZ_iff]
    simp only [condZ, eval, ZMod.val_zero]
    norm_num
  have e2 : cond (p := 2) ⟨a, 2 * b', c⟩ (enumP (some 1)) ↔ (4 : ℤ) ∣ a + 2 * b' + c := by
    rw [enumP, cond_ptZ_iff]
    have : (1 : ZMod 2).val = 1 := rfl
    simp only [condZ, eval, this]
    norm_num
  simp only [e0, e1, e2]
  have h4 : ∀ x : ℤ, (4 : ℤ) ∣ x ↔ (x : ZMod 4).val = 0 := by
    intro x
    have := val4 x
    omega
  simp only [h4]
  push_cast
  have hM : (N : ZMod 4).val = 0 ∨ (N : ZMod 4).val = 3 := by
    rw [ZMod.val_natCast]; omega
  have hA := val4 a
  have hC := val4 c
  have hpar : ¬((a : ZMod 4).val % 2 = 0 ∧ (c : ZMod 4).val % 2 = 0) := by
    intro h
    apply hac
    omega
  have hcast : (b' : ZMod 4) * b' - a * c = -(N : ZMod 4) := by
    have := congrArg (fun x : ℤ => (x : ZMod 4)) hid
    push_cast at this
    exact this
  have := zmod4_check _ _ _ _ hcast hM hpar
  rw [← add_assoc]
  exact this

/-- **One superlattice.** -/
theorem card_cond_eq_one {g : QF} {N : ℕ} (hdisc : g.disc = -((p : ℤ) ^ 2 * N))
    (hN : N % 4 = 0 ∨ N % 4 = 3)
    (hprim : ¬((p : ℤ) ∣ g.a ∧ (p : ℤ) ∣ g.b ∧ (p : ℤ) ∣ g.c)) :
    Nat.card {t : P1 p // cond g t} = 1 := by
  by_cases hp2 : p = 2
  · subst hp2
    exact card_cond_two (by rw [hdisc]; push_cast; ring) hN hprim
  · exact card_cond_odd hp2 ⟨-(N : ℤ), by rw [hdisc]; ring⟩ hprim

/-! ### Counting roots -/

lemma card_cond'_of_dvd {f : QF} (h : (p : ℤ) ∣ f.a ∧ (p : ℤ) ∣ f.b ∧ (p : ℤ) ∣ f.c) :
    Nat.card {t : P1 p // cond' f t} = p + 1 := by
  rw [← card_P1 (p := p)]
  refine Nat.card_congr (Equiv.subtypeUnivEquiv fun t => ?_)
  obtain ⟨u, hu, rfl⟩ := exists_ptZ t
  rw [cond'_ptZ_iff]
  obtain ⟨ha, hb, hc⟩ := h
  simp only [eval]
  exact dvd_add (dvd_add (dvd_mul_of_dvd_left ha _) (dvd_mul_of_dvd_left
    (dvd_mul_of_dvd_left hb _) _)) (dvd_mul_of_dvd_left hc _)

lemma card_eq_one_of_iff {α : Type*} {P : α → Prop} (r : α) (h : ∀ j, P j ↔ j = r) :
    Nat.card {j // P j} = 1 := by
  rw [Nat.card_eq_one_iff_unique]
  refine ⟨⟨fun x y => Subtype.ext ?_⟩, ⟨⟨r, (h r).mpr rfl⟩⟩⟩
  rw [(h _).mp x.2, (h _).mp y.2]

lemma card_eq_zero_of_not {α : Type*} {P : α → Prop} (h : ∀ j, ¬P j) :
    Nat.card {j // P j} = 0 := by
  have : IsEmpty {j // P j} := ⟨fun x => h x.1 x.2⟩
  exact Nat.card_of_isEmpty

open scoped Classical in
/-- Roots of `a x² + b x + c` in `𝔽_p` (`p` odd), plus the point at infinity when `a = 0`. -/
lemma quad_count (hp2 : p ≠ 2) (a b c : ZMod p) (D : ℤ) (hD : (D : ZMod p) = b ^ 2 - 4 * a * c)
    (h : ¬(a = 0 ∧ b = 0 ∧ c = 0)) :
    (((if a = 0 then 1 else 0) + Nat.card {j : ZMod p // a * (j * j) + b * j + c = 0} : ℕ) : ℤ) =
      1 + legendreSym p D := by
  have h2 := two_ne_zero_zmod hp2
  have : NeZero (2 : ZMod p) := ⟨h2⟩
  by_cases ha : a = 0
  · subst ha
    simp only [zero_mul, zero_add, if_true]
    by_cases hb : b = 0
    · subst hb
      have hc : c ≠ 0 := fun hc => h ⟨rfl, rfl, hc⟩
      rw [card_eq_zero_of_not (by intro j; simpa using hc)]
      have : legendreSym p D = 0 := by
        rw [legendreSym.eq_zero_iff, hD]; ring
      rw [this]; norm_num
    · rw [card_eq_one_of_iff (-c / b) (fun j => ⟨fun hj => by field_simp; linear_combination hj,
        fun hj => by rw [hj]; field_simp; ring⟩)]
      have : legendreSym p D = 1 := by
        have hD0 : (D : ZMod p) ≠ 0 := by rw [hD]; simpa using hb
        rw [legendreSym.eq_one_iff p hD0, hD]
        exact ⟨b, by ring⟩
      rw [this]; norm_num
  · simp only [ha, if_false, zero_add]
    have hdisc : discrim a b c = (D : ZMod p) := by rw [hD, discrim]
    by_cases hD0 : (D : ZMod p) = 0
    · rw [card_eq_one_of_iff (-b / (2 * a))
        (quadratic_eq_zero_iff_of_discrim_eq_zero ha (by rw [hdisc, hD0]))]
      rw [(legendreSym.eq_zero_iff p D).mpr hD0]; norm_num
    · by_cases hsq : IsSquare (D : ZMod p)
      · obtain ⟨s, hs⟩ := hsq
        have hs0 : s ≠ 0 := by rintro rfl; exact hD0 (by rw [hs, mul_zero])
        have hne : (-b + s) / (2 * a) ≠ (-b - s) / (2 * a) := by
          intro he
          have h2a : (2 * a) ≠ 0 := mul_ne_zero h2 ha
          rw [div_left_inj' h2a] at he
          apply hs0
          have : 2 * s = 0 := by linear_combination he
          exact (mul_eq_zero.mp this).resolve_left h2
        have hcard : Nat.card {j : ZMod p // a * (j * j) + b * j + c = 0} = 2 := by
          rw [Nat.card_congr (Equiv.subtypeEquivRight (quadratic_eq_zero_iff ha
            (by rw [hdisc, hs]))), ← Set.ncard_pair hne, ← Nat.card_coe_set_eq]
          rfl
        rw [hcard, (legendreSym.eq_one_iff p hD0).mpr ⟨s, hs⟩]; norm_num
      · rw [card_eq_zero_of_not (quadratic_ne_zero_of_discrim_ne_sq (by
          intro s hs; exact hsq ⟨s, by rw [← hdisc, hs, sq]⟩))]
        rw [(legendreSym.eq_neg_one_iff p).mpr hsq]; norm_num

lemma enumP_none_eq : enumP (p := p) none = ptZ (1, 0) ndvd_10 := rfl
lemma enumP_some_eq (j : ZMod p) : enumP (some j) = ptZ ((j.val : ℤ), 1) (ndvd_j1 _) := rfl

open scoped Classical in
lemma card_cond'_eq (f : QF) :
    Nat.card {t : P1 p // cond' f t} =
      (if ((f.a : ZMod p)) = 0 then 1 else 0) +
        Nat.card {j : ZMod p // (f.a : ZMod p) * (j * j) + f.b * j + f.c = 0} := by
  rw [card_subtype_eq]
  congr 1
  · rw [enumP_none_eq, cond'_ptZ_iff, ← intCast_eq_zero_iff]
    simp [eval]
  · refine Nat.card_congr (Equiv.subtypeEquivRight fun j => ?_)
    rw [enumP_some_eq, cond'_ptZ_iff, ← intCast_eq_zero_iff]
    simp only [eval]
    push_cast
    rw [ZMod.natCast_zmod_val]
    constructor <;> intro h <;> linear_combination h

lemma val8 (a : ℤ) : (((a : ZMod 8).val : ℕ) : ℤ) = a % 8 := ZMod.val_intCast a

lemma zmod8_check : ∀ A B C : ZMod 8, ¬(A.val % 2 = 0 ∧ B.val % 2 = 0 ∧ C.val % 2 = 0) →
    (((if A.val % 2 = 0 then 1 else 0) + (if C.val % 2 = 0 then 1 else 0) +
      (if (A + B + C).val % 2 = 0 then 1 else 0) : ℕ) : ℤ) =
      1 + (if (B ^ 2 - 4 * A * C).val % 2 = 0 then 0 else
        if (B ^ 2 - 4 * A * C).val % 8 = 1 ∨ (B ^ 2 - 4 * A * C).val % 8 = 7 then 1 else -1) := by
  decide

open scoped Classical in
/-- **Roots on `ℙ¹(𝔽_p)`** of a `p`-primitive form: `1 + (disc f / p)`. -/
theorem card_cond'_prim {f : QF} (hprim : ¬((p : ℤ) ∣ f.a ∧ (p : ℤ) ∣ f.b ∧ (p : ℤ) ∣ f.c)) :
    (Nat.card {t : P1 p // cond' f t} : ℤ) = 1 + ArithPlan.kron f.disc p := by
  by_cases hp2 : p = 2
  · subst hp2
    rw [card_subtype_eq, card_zmod2]
    have e0 : cond' (p := 2) f (enumP none) ↔ (2 : ℤ) ∣ f.a := by
      rw [enumP_none_eq, cond'_ptZ_iff]; simp [eval]
    have e1 : cond' (p := 2) f (enumP (some 0)) ↔ (2 : ℤ) ∣ f.c := by
      rw [enumP_some_eq, cond'_ptZ_iff]; simp [eval]
    have e2 : cond' (p := 2) f (enumP (some 1)) ↔ (2 : ℤ) ∣ f.a + f.b + f.c := by
      rw [enumP_some_eq, cond'_ptZ_iff]
      have : (1 : ZMod 2).val = 1 := rfl
      simp [eval, this]
    simp only [e0, e1, e2]
    have hA := val8 f.a
    have hB := val8 f.b
    have hC := val8 f.c
    have hS := val8 (f.a + f.b + f.c)
    have hD := val8 f.disc
    have h2 : ∀ x : ℤ, (2 : ℤ) ∣ x ↔ (x : ZMod 8).val % 2 = 0 := by
      intro x; have := val8 x; omega
    have hprim' : ¬((f.a : ZMod 8).val % 2 = 0 ∧ (f.b : ZMod 8).val % 2 = 0 ∧
        (f.c : ZMod 8).val % 2 = 0) := by
      rwa [← h2, ← h2, ← h2]
    have := zmod8_check _ _ _ hprim'
    have hDc : (f.disc : ZMod 8) = (f.b : ZMod 8) ^ 2 - 4 * f.a * f.c := by
      unfold disc; push_cast; ring
    have hk : ArithPlan.kron f.disc 2 =
        (if (f.disc : ZMod 8).val % 2 = 0 then 0 else
          if (f.disc : ZMod 8).val % 8 = 1 ∨ (f.disc : ZMod 8).val % 8 = 7 then 1 else -1) := by
      unfold ArithPlan.kron
      simp only [if_true]
      have e1 : f.disc % 2 = 0 ↔ (f.disc : ZMod 8).val % 2 = 0 := by omega
      have e2 : f.disc % 8 = 1 ↔ (f.disc : ZMod 8).val % 8 = 1 := by omega
      have e3 : f.disc % 8 = 7 ↔ (f.disc : ZMod 8).val % 8 = 7 := by omega
      simp only [e1, e2, e3]
    rw [hk, hDc]
    have hS' : ((f.a + f.b + f.c : ℤ) : ZMod 8) = (f.a : ZMod 8) + f.b + f.c := by push_cast; ring
    simp only [h2, hS']
    push_cast at this ⊢
    linarith
  · rw [card_cond'_eq]
    have := quad_count hp2 (f.a : ZMod p) f.b f.c f.disc (by unfold disc; push_cast; ring)
      (by rwa [intCast_eq_zero_iff, intCast_eq_zero_iff, intCast_eq_zero_iff])
    rw [this]
    unfold ArithPlan.kron
    rw [if_neg hp2, jacobiSym.legendreSym.to_jacobiSym]

/-- `(D/p) = 0` when `p ∣ D`. -/
lemma kron_eq_zero_of_dvd {D : ℤ} (h : (p : ℤ) ∣ D) : ArithPlan.kron D p = 0 := by
  unfold ArithPlan.kron
  by_cases hp2 : p = 2
  · subst hp2
    have h' : (2 : ℤ) ∣ D := by exact_mod_cast h
    have : D % 2 = 0 := by omega
    simp [this]
  · rw [if_neg hp2, ← jacobiSym.legendreSym.to_jacobiSym, legendreSym.eq_zero_iff,
      intCast_eq_zero_iff]
    exact h

end RamanujanWeil.Arith.Hurwitz
