import RamanujanWeil.Arith.ESAnalyticModel

/-!
# A2 / ES-P10: the Hecke eigenrelation `F̃|T^∞ₙ = τ(n)·F̃`

`Σ_{ad = n, 0 ≤ b < d} d¹⁰ F̃((az + b)/d) = τ(n) F̃(z)` on `ℍ`:

* `root_sum_gen` : `Σ_{b<d} e^{2πimb/d} = d·[d ∣ m]`;
* `hasSum_inner` : `Σ_{b<d} d¹⁰F̃((az + b)/d) = Σ_k τ(dk) k⁻¹¹ e^{2πiakz}`;
* `coeff_hecke` : the `K`-th coefficient of the total is `Σ_{a ∣ (n,K)} τ(nK/a²)(a/K)¹¹ = τ(n)τ(K)/K¹¹`
  (`tau_hecke`);
* `Fh_hecke` : the `EichlerData.F_hecke` field.
-/

set_option autoImplicit false

namespace RamanujanWeil.Arith.ES.Analytic

open Complex Filter Set Finset RamanujanTau
open RamanujanWeil.Arith.ES RamanujanWeil.Arith.ES.M2
open scoped Real Topology

lemma root_sum_gen {d : ℕ} (hd : 0 < d) (m : ℕ) :
    ∑ b ∈ range d, cexp (2 * π * I * m * b / d) = if d ∣ m then (d : ℂ) else 0 := by
  have hζ := Complex.isPrimitiveRoot_exp d hd.ne'
  have e : ∀ b : ℕ, cexp (2 * π * I * m * b / d) = (cexp (2 * π * I / d) ^ m) ^ b := by
    intro b
    rw [← pow_mul, ← Complex.exp_nat_mul]; congr 1; push_cast; ring
  rw [Finset.sum_congr rfl fun b _ => e b]
  split_ifs with h
  · rw [(hζ.pow_eq_one_iff_dvd m).mpr h]; simp
  · have h1 : cexp (2 * π * I / d) ^ m ≠ 1 := fun h' => h ((hζ.pow_eq_one_iff_dvd m).mp h')
    rw [geom_sum_eq h1, ← pow_mul, mul_comm m d, pow_mul, hζ.pow_eq_one, one_pow, sub_self, zero_div]

lemma im_affine_pos {a b d : ℕ} (ha : 0 < a) (hd : 0 < d) {z : ℂ} (hz : 0 < z.im) :
    0 < (((a : ℂ) * z + b) / d).im := by
  rw [div_natCast_im]
  simp only [add_im, mul_im, natCast_re, natCast_im, zero_mul, add_zero]
  have : (0 : ℝ) < a := by exact_mod_cast ha
  have : (0 : ℝ) < d := by exact_mod_cast hd
  positivity

lemma qe_affine (a b d m : ℕ) (_hd : 0 < d) (z : ℂ) :
    qe (((a : ℂ) * z + b) / d) m = qe ((a : ℂ) * z / d) m * cexp (2 * π * I * m * b / d) := by
  rw [qe, qe, ← Complex.exp_add]; congr 1; ring

lemma cj0_apply (m : ℕ) : cj 0 m = (tau m : ℂ) / (m : ℂ) ^ 11 := by simp [cj]

/-- the inner sum over `b`, for fixed `a, d`. -/
theorem hasSum_inner {a d : ℕ} (ha : 0 < a) (hd : 0 < d) {z : ℂ} (hz : 0 < z.im) :
    HasSum (fun k : ℕ => (tau (d * k) : ℂ) / (k : ℂ) ^ 11 * qe z (a * k))
      (∑ b ∈ range d, (d : ℂ) ^ 10 * Fc (((a : ℂ) * z + b) / d)) := by
  have hd0 : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  have hb : ∀ b ∈ range d, HasSum (fun m => cj 0 m * qe (((a : ℂ) * z + b) / d) m)
      (Fc (((a : ℂ) * z + b) / d)) := fun b _ => hasSum_G (bd_cj (by norm_num)) (im_affine_pos ha hd hz)
  have hs := (hasSum_sum hb).mul_left ((d : ℂ) ^ 10)
  rw [← Finset.mul_sum]
  -- the summand, after the root-of-unity sum
  have e1 : (fun m => (d : ℂ) ^ 10 * ∑ b ∈ range d, cj 0 m * qe (((a : ℂ) * z + b) / d) m) =
      fun m => if d ∣ m then (d : ℂ) ^ 11 * cj 0 m * qe ((a : ℂ) * z / d) m else 0 := by
    funext m
    simp_rw [qe_affine a _ d m hd z, ← mul_assoc, ← Finset.mul_sum, root_sum_gen hd m]
    split_ifs <;> ring
  rw [e1] at hs
  -- reindex `m = d k`
  have hinj : Function.Injective fun k : ℕ => d * k := fun x y h => Nat.eq_of_mul_eq_mul_left hd h
  rw [← hinj.hasSum_iff (fun m hm => by
    rw [if_neg]; rintro ⟨k, rfl⟩; exact hm ⟨k, rfl⟩)] at hs
  refine (show (fun k : ℕ => (tau (d * k) : ℂ) / (k : ℂ) ^ 11 * qe z (a * k)) = _ from
    funext fun k => ?_) ▸ hs
  simp only [Function.comp_apply, if_pos (Nat.dvd_mul_right d k), cj0_apply]
  have eq : qe ((a : ℂ) * z / d) (d * k) = qe z (a * k) := by
    rw [qe, qe]; congr 1; push_cast; field_simp
  rw [eq]
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  have hk0 : (k : ℂ) ≠ 0 := by exact_mod_cast hk.ne'
  push_cast
  field_simp

/-- reindexing by `K = a k`. -/
theorem hasSum_inner' {a d : ℕ} (ha : 0 < a) (hd : 0 < d) {z : ℂ} (hz : 0 < z.im) :
    HasSum (fun K : ℕ => if a ∣ K then (tau (d * (K / a)) : ℂ) / ((K / a : ℕ) : ℂ) ^ 11 * qe z K else 0)
      (∑ b ∈ range d, (d : ℂ) ^ 10 * Fc (((a : ℂ) * z + b) / d)) := by
  have hinj : Function.Injective fun k : ℕ => a * k := fun x y h => Nat.eq_of_mul_eq_mul_left ha h
  rw [← hinj.hasSum_iff (fun K hK => by
    rw [if_neg]; rintro ⟨k, rfl⟩; exact hK ⟨k, rfl⟩)]
  convert hasSum_inner ha hd hz using 1
  funext k
  simp only [Function.comp_apply, if_pos (Nat.dvd_mul_right a k), Nat.mul_div_cancel_left _ ha]

/-- the `K`-th coefficient of `F̃|T^∞ₙ`. -/
theorem coeff_hecke {n : ℕ} (hn : 1 ≤ n) (K : ℕ) :
    ∑ a ∈ n.divisors, (if a ∣ K then (tau (n / a * (K / a)) : ℂ) / ((K / a : ℕ) : ℂ) ^ 11 else 0) =
      (tau n : ℂ) * cj 0 K := by
  rw [cj0_apply]
  rcases Nat.eq_zero_or_pos K with rfl | hK
  · simp [tau_zero]
  have hK0 : (K : ℂ) ≠ 0 := by exact_mod_cast hK.ne'
  have hT := tau_hecke n hn K
  unfold Tn at hT
  have hn0 : n ≠ 0 := by omega
  rw [← Finset.sum_filter]
  have hfil : n.divisors.filter (· ∣ K) = (Nat.gcd n K).divisors := by
    ext a; rw [mem_filter, mem_gcd_divisors hn0, Nat.mem_divisors]
    exact ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, hn0⟩, h.2⟩⟩
  rw [hfil]
  have e : ∀ a ∈ (Nat.gcd n K).divisors, (tau (n / a * (K / a)) : ℂ) / ((K / a : ℕ) : ℂ) ^ 11 =
      ((a : ℤ) ^ 11 * tau (n * K / (a * a)) : ℤ) / (K : ℂ) ^ 11 := by
    intro a ha
    rw [mem_gcd_divisors hn0] at ha
    have ha0 : 0 < a := Nat.pos_of_dvd_of_pos ha.1 (by omega)
    have ha0' : (a : ℂ) ≠ 0 := by exact_mod_cast ha0.ne'
    rw [Nat.div_mul_div_comm ha.1 ha.2, Nat.cast_div ha.2 ha0']
    push_cast
    field_simp
  rw [Finset.sum_congr rfl e, ← Finset.sum_div]
  rw [show (∑ a ∈ (Nat.gcd n K).divisors, (((a : ℤ) ^ 11 * tau (n * K / (a * a)) : ℤ) : ℂ)) =
      ((∑ a ∈ (Nat.gcd n K).divisors, (a : ℤ) ^ 11 * tau (n * K / (a * a)) : ℤ) : ℂ) by push_cast; rfl,
    hT]
  push_cast
  ring

/-- `Σ_{N ∈ heckeSet n} g N` as a double sum over `a ∣ n`, `0 ≤ b < n/a`. -/
theorem sum_heckeSet {β : Type*} [AddCommMonoid β] {n : ℕ} (hn : 1 ≤ n) (g : M2 → β) :
    ∑ N ∈ heckeSet n, g N =
      ∑ a ∈ n.divisors, ∑ b ∈ range (n / a), g ⟨a, b, 0, ((n / a : ℕ) : ℤ)⟩ := by
  rw [Finset.sum_sigma']
  have hn0 : n ≠ 0 := by omega
  -- membership in the Hecke set, in natural coordinates
  have key : ∀ N ∈ heckeSet n, ∃ a b d : ℕ, N = ⟨a, b, 0, d⟩ ∧ a * d = n ∧ b < d := by
    intro N hN
    rw [mem_heckeSet hn] at hN
    obtain ⟨hc, hdet, hd, hb0, hbd⟩ := hN
    obtain ⟨a, b, c, d⟩ := N
    simp only [det] at hc hdet hd hb0 hbd
    subst hc
    have had : a * d = n := by simpa using hdet
    have ha : 0 < a := pos_of_mul_pos_left (by rw [had]; omega) hd.le
    lift a to ℕ using ha.le
    lift b to ℕ using hb0
    lift d to ℕ using hd.le
    exact ⟨a, b, d, rfl, by exact_mod_cast had, by exact_mod_cast hbd⟩
  refine Finset.sum_nbij' (fun N => ⟨N.a.toNat, N.b.toNat⟩)
    (fun x => (⟨x.1, x.2, 0, ((n / x.1 : ℕ) : ℤ)⟩ : M2)) ?_ ?_ ?_ ?_ ?_
  · intro N hN
    obtain ⟨a, b, d, rfl, had, hbd⟩ := key N hN
    have ha : 0 < a := Nat.pos_of_ne_zero (by rintro rfl; omega)
    simp only [mem_sigma, Nat.mem_divisors, Finset.mem_range, Int.toNat_natCast]
    refine ⟨⟨⟨d, had.symm⟩, hn0⟩, ?_⟩
    rw [← had, Nat.mul_div_cancel_left _ ha]; exact hbd
  · intro x hx
    simp only [mem_sigma, Nat.mem_divisors, Finset.mem_range] at hx
    obtain ⟨⟨⟨d, hd⟩, _⟩, hb⟩ := hx
    have ha : 0 < x.1 := Nat.pos_of_ne_zero (by intro h; rw [h] at hd; omega)
    rw [mem_heckeSet hn]
    have hnd : n / x.1 = d := by rw [hd, Nat.mul_div_cancel_left _ ha]
    rw [hnd] at hb ⊢
    refine ⟨rfl, ?_, ?_, by positivity, show ((x.2 : ℕ) : ℤ) < ((d : ℕ) : ℤ) by exact_mod_cast hb⟩
    · simp only [det]; rw [hd]; push_cast; ring
    · have : 0 < d := by omega
      show (0 : ℤ) < ((d : ℕ) : ℤ)
      exact_mod_cast this
  · intro N hN
    obtain ⟨a, b, d, rfl, had, hbd⟩ := key N hN
    have ha : 0 < a := Nat.pos_of_ne_zero (by rintro rfl; omega)
    simp only [Int.toNat_natCast]
    rw [← had, Nat.mul_div_cancel_left _ ha]
  · intro x hx
    simp
  · intro N hN
    obtain ⟨a, b, d, rfl, had, hbd⟩ := key N hN
    have ha : 0 < a := Nat.pos_of_ne_zero (by rintro rfl; omega)
    simp only [Int.toNat_natCast]
    rw [← had, Nat.mul_div_cancel_left _ ha]

/-- **`F̃|T^∞ₙ = τ(n)·F̃`.** -/
theorem Fh_hecke (n : ℕ) (hn : 1 ≤ n) :
    ∑ N ∈ heckeSet n, sl N Fh = (tau n : ℂ) • Fh := by
  funext z
  rw [Finset.sum_apply, sum_heckeSet hn]
  have hz : 0 < (z : ℂ).im := z.2
  -- each term
  have e : ∀ a ∈ n.divisors, ∀ b ∈ range (n / a),
      sl (⟨a, b, 0, ((n / a : ℕ) : ℤ)⟩ : M2) Fh z =
        ((n / a : ℕ) : ℂ) ^ 10 * Fc (((a : ℂ) * z + b) / (n / a : ℕ)) := by
    intro a ha b _
    have ha0 : 0 < a := Nat.pos_of_mem_divisors ha
    have hd0 : 0 < n / a := Nat.div_pos (Nat.divisor_le ha) ha0
    have hdet : 0 < (⟨a, b, 0, ((n / a : ℕ) : ℤ)⟩ : M2).det := by
      simp only [det, mul_zero, sub_zero]
      exact mul_pos (by exact_mod_cast ha0) (by exact_mod_cast hd0)
    rw [sl_apply hdet]
    simp only [Fh, jf, mobC, Int.cast_natCast, Int.cast_zero, zero_mul, zero_add]
  rw [Finset.sum_congr rfl fun a ha => Finset.sum_congr rfl (e a ha)]
  -- the total as a `HasSum`
  have hall := hasSum_sum (s := n.divisors) fun a ha =>
    hasSum_inner' (Nat.pos_of_mem_divisors ha) (Nat.div_pos (Nat.divisor_le ha)
      (Nat.pos_of_mem_divisors ha)) hz
  have e2 : (fun K : ℕ => ∑ a ∈ n.divisors, if a ∣ K then (tau (n / a * (K / a)) : ℂ) /
      ((K / a : ℕ) : ℂ) ^ 11 * qe z K else 0) = fun K => (tau n : ℂ) * (cj 0 K * qe z K) := by
    funext K
    rw [← mul_assoc, ← coeff_hecke hn K, Finset.sum_mul]
    refine Finset.sum_congr rfl fun a _ => ?_
    split_ifs <;> ring
  rw [e2] at hall
  have h2 := (hasSum_G (bd_cj (j := 0) (by norm_num)) hz).mul_left (tau n : ℂ)
  rw [hall.unique h2]
  rfl

end RamanujanWeil.Arith.ES.Analytic
