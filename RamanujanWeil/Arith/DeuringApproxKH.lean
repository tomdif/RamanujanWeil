import RamanujanWeil.Arith.ESMain
import RamanujanWeil.Arith.ESCosetsMain
import RamanujanWeil.Arith.AssemblyRecursion
import RamanujanWeil.Arith.HurwitzPrimeSquare

/-!
# Kronecker–Hurwitz from the Popa–Zagier machinery (weight 2, no analytic input)

The weight-12 Eichler–Selberg proof (`ESPropC`, `ESCosetsMain`) contains a weight-free core:

* per trace, `Σ_{det = n, tr = t} T̃ₙ = Σ_{tr = t} H − Σ_{tr = t} E` (`trSum_ptC`), with
  `Σ_{tr = t} E = H(4n − t²)` (`trSum_regE`) and the hyperbolic sum `sum_trSum_regH` (any
  weight function `g`);
* every right coset `AΓ` (`Γ = SL₂(ℤ)`, `det A = n > 0`) has `⟨T̃ₙ, AΓ⟩ = −1`
  (`cS_ptC_eq_neg_one`).

Taking the weight `g ≡ 1` (i.e. `w = 0`, the trivial `V₀`) and summing over the `σ(n)` right
cosets gives `Σ_{det = n} T̃ₙ = −σ(n)` and hence the **Kronecker–Hurwitz class number relation**

  `Σ_{t² ≤ 4n} H(4n − t²) = Σ_{0 < a ∣ n} (2·(n/a) − min(a, n/a))`   (`H(0) = −1/12`),

i.e. `2σ(n) − λ(n)`. No analytic input is used (`S₂(SL₂ℤ) = 0` is implicit: `W₀ = 0`).

Main results:
* `sum_box_ptC` : `Σ_{det M = n} ptC M = −Σ_{0 < a ∣ n} n/a` (right-coset decomposition);
* **`kroneckerHurwitz`** (all `n ≥ 1`);
* `kroneckerHurwitz_primePow` : `A₀(m) = 2Σ_{j ≤ m} pʲ − λ₀(m)` with `A₀(m) = Σ_{t ∈ T(m)} H`;
* `ordSum0_rec` : the weight-0 analogue of `ordSum_rec`;
* **`ordSum0_bound`** : `|Σ_{p ∤ t, t² ≤ 4pᵐ} H(4pᵐ − t²) − 2pᵐ| ≤ C (m+1)² (√p)ᵐ`.
-/

open Finset

namespace RamanujanWeil.Arith.ES

open M2

/-! ### Right-coset decomposition of `{det M = n}` -/

/-- Hermite key of `M` for right `SL₂(ℤ)`-cosets: `(gcd(a, b), (c x + d y) mod (det/g))`, where
`a x + b y = g` (Bezout). -/
def cosetKey (M : M2) : ℤ × ℤ :=
  ((Int.gcd M.a M.b : ℤ),
    (M.c * Int.gcdA M.a M.b + M.d * Int.gcdB M.a M.b) % (M.det / (Int.gcd M.a M.b : ℤ)))

/-- The lower-triangular representative `[[g, 0], [c, n/g]]`. -/
def cosetRep (n : ℤ) (k : ℤ × ℤ) : M2 := ⟨k.1, 0, k.2, n / k.1⟩

/-- The cofactor `γ` with `cosetRep (det M) (cosetKey M) * γ = M`. -/
def cosetCof (M : M2) : M2 :=
  let g : ℤ := Int.gcd M.a M.b
  let x := Int.gcdA M.a M.b
  let y := Int.gcdB M.a M.b
  let d' := M.det / g
  let q := (M.c * x + M.d * y) / d'
  ⟨M.a / g, M.b / g, q * (M.a / g) - y, q * (M.b / g) + x⟩

/-- The set of keys `{(g, c) : 1 ≤ g, g ∣ n, 0 ≤ c < n/g}`. -/
def cosetKeys (n : ℕ) : Finset (ℤ × ℤ) :=
  ((Icc (1 : ℤ) n) ×ˢ (Icc (0 : ℤ) n)).filter (fun k => k.1 ∣ (n : ℤ) ∧ k.2 < (n : ℤ) / k.1)

lemma gcd_pos_of_det {M : M2} (h : M.det ≠ 0) : (0 : ℤ) < (Int.gcd M.a M.b : ℤ) := by
  have : Int.gcd M.a M.b ≠ 0 := by
    intro h0
    rw [Int.gcd_eq_zero_iff] at h0
    apply h; simp [det, h0.1, h0.2]
  exact_mod_cast Nat.pos_of_ne_zero this

/-- **Existence of the factorisation** `M = cosetRep · γ`, `det γ = 1`. -/
theorem cosetCof_spec {M : M2} (h : 0 < M.det) :
    (cosetCof M).det = 1 ∧ cosetRep M.det (cosetKey M) * cosetCof M = M := by
  obtain ⟨a, b, c, d⟩ := M
  simp only [cosetCof, cosetKey, cosetRep] at h ⊢
  set g : ℤ := (Int.gcd a b : ℤ) with hg
  have hg0 : 0 < g := gcd_pos_of_det (M := ⟨a, b, c, d⟩) h.ne'
  set x := Int.gcdA a b
  set y := Int.gcdB a b
  have hbez : g = a * x + b * y := Int.gcd_eq_gcd_ab a b
  obtain ⟨a', ha⟩ := Int.gcd_dvd_left a b
  obtain ⟨b', hb⟩ := Int.gcd_dvd_right a b
  rw [← hg] at ha hb
  have ha' : a / g = a' := by rw [ha, Int.mul_ediv_cancel_left _ hg0.ne']
  have hb' : b / g = b' := by rw [hb, Int.mul_ediv_cancel_left _ hg0.ne']
  have hx : a' * x + b' * y = 1 := by
    have : g * (a' * x + b' * y) = g * 1 := by linear_combination -hbez - x * ha - y * hb
    exact mul_left_cancel₀ hg0.ne' this
  have hdet : (⟨a, b, c, d⟩ : M2).det = g * (a' * d - b' * c) := by
    simp only [det]; rw [ha, hb]; ring
  have hd' : (⟨a, b, c, d⟩ : M2).det / g = a' * d - b' * c := by
    rw [hdet, Int.mul_ediv_cancel_left _ hg0.ne']
  rw [ha', hb', hd']
  set d' := a' * d - b' * c
  set e := c * x + d * y
  have hqe : d' * (e / d') + e % d' = e := Int.mul_ediv_add_emod e d'
  have hgd : g * d' / g = d' := Int.mul_ediv_cancel_left _ hg0.ne'
  refine ⟨?_, ?_⟩
  · simp only [det]; linear_combination hx
  · ext
    · simp only [mul_a]; rw [ha]; ring
    · simp only [mul_b]; rw [hb]; ring
    · simp only [mul_c]
      linear_combination a' * hqe + c * hx
    · simp only [mul_d]
      linear_combination b' * hqe + d * hx

lemma cosetRep_det {n : ℕ} {k : ℤ × ℤ} (hk : k ∈ cosetKeys n) :
    (cosetRep n k).det = n := by
  simp only [cosetKeys, mem_filter] at hk
  simp only [cosetRep, det, zero_mul, sub_zero]
  exact Int.mul_ediv_cancel' hk.2.1

/-- **Uniqueness**: the key of `cosetRep n k · γ` is `k`. -/
theorem cosetKey_rep_mul {n : ℕ} {k : ℤ × ℤ} (hk : k ∈ cosetKeys n) {γ : M2}
    (hγ : γ.det = 1) : cosetKey (cosetRep n k * γ) = k := by
  have hdetM : (cosetRep n k * γ).det = n := by rw [det_mul, cosetRep_det hk, hγ, mul_one]
  simp only [cosetKeys, mem_filter, mem_product, mem_Icc] at hk
  obtain ⟨⟨⟨hg1, _⟩, hc0, _⟩, hdvd, hclt⟩ := hk
  obtain ⟨g, c⟩ := k
  obtain ⟨α, β, γc, δ⟩ := γ
  simp only [det] at hγ
  simp only at hg1 hc0 hdvd hclt
  set d' := (n : ℤ) / g with hd'
  have hcop : Int.gcd α β = 1 :=
    Int.isCoprime_iff_gcd_eq_one.mp ⟨δ, -γc, by linear_combination hγ⟩
  have hM : cosetRep n (g, c) * ⟨α, β, γc, δ⟩ = ⟨g * α, g * β, c * α + d' * γc, c * β + d' * δ⟩ := by
    ext <;> simp [cosetRep, hd']
  have hdetM' : (⟨g * α, g * β, c * α + d' * γc, c * β + d' * δ⟩ : M2).det = n := by
    rw [← hM]; exact hdetM
  rw [hM]
  simp only [cosetKey]
  rw [hdetM']
  have hgcd : Int.gcd (g * α) (g * β) = g.natAbs := by
    rw [Int.gcd_mul_left, hcop, mul_one]
  rw [hgcd, Int.natCast_natAbs, abs_of_pos (by omega)]
  refine Prod.ext rfl ?_
  simp only
  set x := Int.gcdA (g * α) (g * β)
  set y := Int.gcdB (g * α) (g * β)
  have hbez : ((Int.gcd (g * α) (g * β) : ℕ) : ℤ) = g * α * x + g * β * y := Int.gcd_eq_gcd_ab _ _
  rw [hgcd, Int.natCast_natAbs, abs_of_pos (by omega)] at hbez
  have hx : α * x + β * y = 1 := by
    have : g * (α * x + β * y) = g * 1 := by linear_combination -hbez
    exact mul_left_cancel₀ (by omega) this
  have e : (c * α + d' * γc) * x + (c * β + d' * δ) * y = c + d' * (γc * x + δ * y) := by
    linear_combination c * hx
  rw [e, Int.add_mul_emod_self_left, Int.emod_eq_of_lt hc0 hclt]

lemma cosetKey_mem {n : ℕ} (hn : 1 ≤ n) {M : M2} (hM : M.det = n) : cosetKey M ∈ cosetKeys n := by
  have hpos : 0 < M.det := by rw [hM]; exact_mod_cast hn
  have hg0 := gcd_pos_of_det hpos.ne'
  have hdvd : (Int.gcd M.a M.b : ℤ) ∣ (n : ℤ) := by
    rw [← hM]
    exact dvd_sub (dvd_mul_of_dvd_left (Int.gcd_dvd_left _ _) _)
      (dvd_mul_of_dvd_left (Int.gcd_dvd_right _ _) _)
  simp only [cosetKeys, mem_filter, mem_product, mem_Icc, cosetKey, hM]
  generalize (Int.gcd M.a M.b : ℤ) = g at hg0 hdvd ⊢
  generalize M.c * Int.gcdA M.a M.b + M.d * Int.gcdB M.a M.b = e
  have hn0 : (0 : ℤ) < n := by exact_mod_cast hn
  have hgle : g ≤ n := Int.le_of_dvd hn0 hdvd
  have hd'pos : 0 < (n : ℤ) / g := Int.ediv_pos_of_pos_of_dvd hn0 hg0.le hdvd
  have hd'le : (n : ℤ) / g ≤ n := Int.ediv_le_self _ hn0.le
  have h1 := Int.emod_lt_of_pos e hd'pos
  have h2 := Int.emod_nonneg e hd'pos.ne'
  exact ⟨⟨⟨by omega, hgle⟩, h2, by omega⟩, hdvd, h1⟩

/-- One coset: `Σ_{det M = n, key M = k} ptC M = ⟨T̃ₙ, AΓ⟩ = −1`. -/
theorem sum_fiber_ptC {n : ℕ} (hn : 1 ≤ n) {k : ℤ × ℤ} (hk : k ∈ cosetKeys n) :
    ∑ M ∈ ((boxM n).filter (fun M => M.det = (n : ℤ))).filter (fun M => cosetKey M = k), ptC M = -1 := by
  set A := cosetRep n k
  have hAdet : A.det = n := cosetRep_det hk
  have hn0 : (0 : ℤ) < n := by exact_mod_cast hn
  set Bk := ((boxM n).filter (fun M => M.det = (n : ℤ))).filter (fun M => cosetKey M = k)
  have hmemBk : ∀ M ∈ Bk, M.det = n ∧ cosetKey M = k := by
    intro M hM; simp only [Bk, mem_filter] at hM; exact ⟨hM.1.2, hM.2⟩
  have hfac : ∀ M ∈ Bk, (cosetCof M).det = 1 ∧ A * cosetCof M = M := by
    intro M hM
    obtain ⟨h1, h2⟩ := hmemBk M hM
    have := cosetCof_spec (M := M) (by rw [h1]; exact hn0)
    rw [h1, h2] at this
    exact this
  rw [← cS_ptC_eq_neg_one (A := A) (by rw [hAdet]; exact hn0), cS,
    finsum_eq_sum_of_support_subset (s := Bk.image cosetCof)]
  · rw [sum_image]
    · refine sum_congr rfl fun M hM => ?_
      obtain ⟨h1, h2⟩ := hfac M hM
      rw [esIfPos h1, h2]
    · intro M₁ h₁ M₂ h₂ he
      have e1 := (hfac M₁ h₁).2
      have e2 := (hfac M₂ h₂).2
      rw [← e1, ← e2, he]
  · intro γ hγ
    rw [Function.mem_support] at hγ
    split_ifs at hγ with hdγ
    swap; · exact absurd rfl hγ
    have hdet : (A * γ).det = n := by rw [det_mul, hAdet, hdγ, mul_one]
    have hkey : cosetKey (A * γ) = k := cosetKey_rep_mul hk hdγ
    have hmem : A * γ ∈ Bk := by
      simp only [Bk, mem_filter]
      exact ⟨⟨mem_boxM.mpr (ptC_support hdet hγ), hdet⟩, hkey⟩
    rw [coe_image]
    refine ⟨A * γ, hmem, ?_⟩
    have := (hfac _ hmem).2
    exact mul_left_injective' (by rw [hAdet]; exact hn0.ne') this

/-- The number of right cosets: `Σ_{k} 1 = Σ_{0 < a ∣ n} n/a`. -/
lemma card_cosetKeys (n : ℕ) :
    ∑ _k ∈ cosetKeys n, (1 : ℚ) =
      ∑ a ∈ (Icc (1 : ℤ) n).filter (· ∣ (n : ℤ)), (((n : ℤ) / a : ℤ) : ℚ) := by
  rw [cosetKeys, sum_filter, sum_product, sum_filter]
  refine sum_congr rfl fun a ha => ?_
  by_cases hdvd : a ∣ (n : ℤ)
  · rw [esIfPos hdvd]
    have ha1 : 1 ≤ a := (mem_Icc.mp ha).1
    have hle : (n : ℤ) / a ≤ n := Int.ediv_le_self _ (by positivity)
    have hnn : 0 ≤ (n : ℤ) / a := Int.ediv_nonneg (by positivity) (by omega)
    have : ∀ c ∈ Icc (0 : ℤ) n, (if a ∣ (n : ℤ) ∧ c < (n : ℤ) / a then (1 : ℚ) else 0) =
        if c < (n : ℤ) / a then 1 else 0 := fun c _ => by simp [hdvd]
    rw [sum_congr rfl this, ← sum_filter, sum_const, nsmul_eq_mul, mul_one]
    have hf : (Icc (0 : ℤ) n).filter (fun c => c < (n : ℤ) / a) = Ico 0 ((n : ℤ) / a) := by
      ext c; simp only [mem_filter, mem_Icc, mem_Ico]; omega
    rw [hf, Int.card_Ico, sub_zero]
    exact_mod_cast Int.toNat_of_nonneg hnn
  · rw [esIfNeg hdvd]
    exact sum_eq_zero fun c _ => by simp [hdvd]

/-- **`Σ_{det M = n} T̃ₙ(M) = −σ(n)`** (sum over the `σ(n)` right cosets, each `−1`). -/
theorem sum_box_ptC (n : ℕ) (hn : 1 ≤ n) :
    ∑ M ∈ boxM n, (if M.det = n then ptC M * 1 else 0) =
      -∑ a ∈ (Icc (1 : ℤ) n).filter (· ∣ (n : ℤ)), (((n : ℤ) / a : ℤ) : ℚ) := by
  simp only [mul_one]
  rw [← sum_filter, ← sum_fiberwise_of_maps_to (t := cosetKeys n) (g := cosetKey)
    (fun M hM => cosetKey_mem hn (mem_filter.mp hM).2), ← card_cosetKeys, ← sum_neg_distrib]
  exact sum_congr rfl fun k hk => sum_fiber_ptC hn hk

/-! ### Kronecker–Hurwitz -/

/-- `hypW(a, d) = d − min(a, d) + [a = d]/6` for `a, d ≥ 1`. -/
lemma hypW_eq (a d : ℤ) :
    hypW a d = ((d - min a d : ℤ) : ℚ) + (if a = d then 1 / 6 else 0) := by
  unfold hypW
  rcases lt_trichotomy a d with h | h | h
  · rw [esIfPos h, esIfNeg h.ne, min_eq_left h.le]; simp
  · subst h; rw [esIfNeg (lt_irrefl a), esIfPos rfl, min_self]; simp
  · rw [esIfNeg (by omega : ¬ a < d), esIfNeg (by omega : ¬ a = d), min_eq_right h.le]; simp

/-- The parabolic count: `#{t : t² = 4n} = 2·#{0 < a ∣ n : a² = n}`. -/
lemma par_count (n : ℕ) (hn : 1 ≤ n) :
    ∑ t ∈ Icc (-(2 * (n : ℤ))) (2 * n), (if t ^ 2 = 4 * (n : ℤ) then (1 : ℚ) else 0) =
      ∑ a ∈ (Icc (1 : ℤ) n).filter (· ∣ (n : ℤ)), (if a * a = (n : ℤ) then 2 else 0) := by
  by_cases hsq : ∃ r : ℤ, 1 ≤ r ∧ r * r = n
  · obtain ⟨r, hr1, hrn⟩ := hsq
    have hrn' : r ≤ n := by nlinarith
    rw [Finset.sum_eq_add (2 * r) (-(2 * r)) (by omega)]
    · rw [Finset.sum_eq_single r]
      · rw [esIfPos (by rw [← hrn]; ring), esIfPos (by rw [← hrn]; ring), esIfPos hrn]
        norm_num
      · intro a ha hne
        simp only [Finset.mem_filter, Finset.mem_Icc] at ha
        rw [esIfNeg]
        intro h
        apply hne
        nlinarith
      · intro h
        exfalso; apply h
        simp only [Finset.mem_filter, Finset.mem_Icc]
        exact ⟨⟨hr1, hrn'⟩, ⟨r, hrn.symm⟩⟩
    · intro c _ hc
      rw [esIfNeg]
      intro h
      have : (c - 2 * r) * (c + 2 * r) = 0 := by rw [← hrn] at h; linear_combination h
      rcases mul_eq_zero.mp this with h1 | h1
      · exact hc.1 (by linarith)
      · exact hc.2 (by linarith)
    · intro h; exfalso; apply h; simp only [Finset.mem_Icc]; constructor <;> nlinarith
    · intro h; exfalso; apply h; simp only [Finset.mem_Icc]; constructor <;> nlinarith
  · push Not at hsq
    rw [Finset.sum_eq_zero, Finset.sum_eq_zero]
    · intro a ha
      simp only [Finset.mem_filter, Finset.mem_Icc] at ha
      rw [esIfNeg (hsq a ha.1.1)]
    · intro t _
      rw [esIfNeg]
      intro h
      obtain ⟨s, hs⟩ : Even t := by
        by_contra ho
        rw [Int.not_even_iff_odd] at ho
        obtain ⟨k, hk⟩ := ho
        subst hk
        ring_nf at h
        omega
      subst hs
      have hss : s * s = n := by nlinarith
      rcases le_or_gt 0 s with h0 | h0
      · exact hsq s (by nlinarith) hss
      · exact hsq (-s) (by nlinarith) (by rw [← hss]; ring)

/-- **Kronecker–Hurwitz class number relation** (Hurwitz 1885), for every `n ≥ 1`:
`Σ_{t² ≤ 4n} H(4n − t²) = Σ_{0 < a ∣ n} (2·(n/a) − min(a, n/a)) = 2σ(n) − λ(n)`,
with `H = hurwitz` (`H(0) = −1/12`). Proved from the weight-free core of Popa–Zagier. -/
theorem kroneckerHurwitz (n : ℕ) (hn : 1 ≤ n) :
    ∑ t ∈ Icc (-(2 * (n : ℤ))) (2 * n) with t ^ 2 ≤ 4 * (n : ℤ),
        Hurwitz.hurwitz (4 * (n : ℤ) - t ^ 2).toNat =
      ∑ a ∈ (Icc (1 : ℤ) n).filter (· ∣ (n : ℤ)),
        ((2 * ((n : ℤ) / a) - min a ((n : ℤ) / a) : ℤ) : ℚ) := by
  set D := (Icc (1 : ℤ) n).filter (· ∣ (n : ℤ)) with hD
  -- split elliptic / parabolic
  have hsplit : ∑ t ∈ Icc (-(2 * (n : ℤ))) (2 * n) with t ^ 2 ≤ 4 * (n : ℤ),
        Hurwitz.hurwitz (4 * (n : ℤ) - t ^ 2).toNat =
      (∑ t ∈ Icc (-(2 * (n : ℤ))) (2 * n), (1 : ℚ) * trSum n t regE) +
        (-1 / 12) * ∑ t ∈ Icc (-(2 * (n : ℤ))) (2 * n),
          (if t ^ 2 = 4 * (n : ℤ) then (1 : ℚ) else 0) := by
    rw [sum_filter, mul_sum, ← sum_add_distrib]
    refine sum_congr rfl fun t _ => ?_
    by_cases h1 : t ^ 2 < 4 * (n : ℤ)
    · rw [esIfPos h1.le, trSum_regE (N := (4 * (n : ℤ) - t ^ 2).toNat)
        (Int.toNat_of_nonneg (by omega)) (by omega), esIfNeg h1.ne]; ring
    · rw [trSum_regE_nonell (by omega)]
      by_cases h2 : t ^ 2 = 4 * (n : ℤ)
      · rw [esIfPos h2.le, esIfPos h2, h2, sub_self, Int.toNat_zero, hurwitz_zero']; ring
      · rw [esIfNeg (by omega), esIfNeg h2]; ring
  -- elliptic = hyperbolic − Σ ptC
  have hell : ∑ t ∈ Icc (-(2 * (n : ℤ))) (2 * n), (1 : ℚ) * trSum n t regE =
      (∑ t ∈ Icc (-(2 * (n : ℤ))) (2 * n), (fun _ => (1 : ℚ)) t * trSum n t regH) -
        ∑ t ∈ Icc (-(2 * (n : ℤ))) (2 * n), (fun _ => (1 : ℚ)) t * trSum n t ptC := by
    rw [← sum_sub_distrib]
    refine sum_congr rfl fun t _ => ?_
    rw [trSum_ptC]; ring
  rw [sum_trSum_regH n hn (fun _ => (1 : ℚ)),
    sum_trSum_eq_box ptC (fun M h1 h2 => ptC_support h1 h2) (fun _ => (1 : ℚ)),
    sum_box_ptC n hn] at hell
  rw [hsplit, hell, par_count n hn, ← sum_filter, ← hD, sub_neg_eq_add, mul_sum, ← sum_add_distrib,
    ← sum_add_distrib]
  refine sum_congr rfl fun a ha => ?_
  simp only [hD, mem_filter, mem_Icc] at ha
  obtain ⟨⟨ha1, _⟩, hdvd⟩ := ha
  have had : a * ((n : ℤ) / a) = n := Int.mul_ediv_cancel' hdvd
  rw [mul_one, hypW_eq]
  by_cases hsq : a = (n : ℤ) / a
  · rw [esIfPos hsq, esIfPos (by rw [← had, ← hsq])]; push_cast; ring
  · rw [esIfNeg hsq, esIfNeg (by intro h; apply hsq; nlinarith)]; push_cast; ring

end RamanujanWeil.Arith.ES

/-! ### Prime powers: the weight-0 ordinary sum -/

namespace RamanujanWeil.ArithPlan

open RamanujanWeil.Arith.ES

set_option linter.unusedSectionVars false

section Weight0

variable (p : ℕ) [hp : Fact p.Prime]

/-- `A₀(m) = Σ_{t² ≤ 4pᵐ} H(4pᵐ − t²)` (weight-0 analogue of `esSum`). -/
def esSum0 (H : ℕ → ℚ) (m : ℕ) : ℚ := ∑ t ∈ tset p m, H (nArg p m t)

/-- `O₀(m) = Σ_{t² ≤ 4pᵐ, p ∤ t} H(4pᵐ − t²)` (weight-0 analogue of `ordSum`). -/
def ordSum0 (H : ℕ → ℚ) (m : ℕ) : ℚ :=
  ∑ t ∈ (tset p m).filter (fun t => ¬ (p : ℤ) ∣ t), H (nArg p m t)

/-- The `p ∣ t` part of `A₀(m)`. -/
def psum0 (H : ℕ → ℚ) (m : ℕ) : ℚ :=
  ∑ t ∈ (tset p m).filter (fun t => (p : ℤ) ∣ t), H (nArg p m t)

lemma esSum0_split (H : ℕ → ℚ) (m : ℕ) : esSum0 p H m = ordSum0 p H m + psum0 p H m := by
  rw [esSum0, ordSum0, psum0, add_comm, sum_filter_add_sum_filter_not]

/-- **Weight-0 ordinary recursion** (from `HurwitzPrimeSquare` only):
`O₀(m+4) = A₀(m+4) − ((p+1)A₀(m+2) − O₀(m+2) − p·A₀(m))`. -/
theorem ordSum0_rec (H : ℕ → ℚ) (hHR : HurwitzPrimeSquare H p) (m : ℕ) :
    ordSum0 p H (m + 4) = esSum0 p H (m + 4) -
      (((p : ℚ) + 1) * esSum0 p H (m + 2) - ordSum0 p H (m + 2) - (p : ℚ) * esSum0 p H m) := by
  have e1 : psum0 p H (m + 2) = ∑ u ∈ tset p m, H (nArg p (m + 2) (p * u)) :=
    sum_dvd_reindex p m _
  have e2 : psum0 p H (m + 4) = ∑ t ∈ tset p (m + 2), H (p ^ 2 * nArg p (m + 2) t) := by
    rw [psum0, sum_dvd_reindex p (m + 2)]
    exact sum_congr rfl fun t ht => by rw [nArg_scale p ht]
  have e3 : ∑ t ∈ tset p (m + 2), H (p ^ 2 * nArg p (m + 2) t) =
      (((p : ℚ) + 1) * psum0 p H (m + 2) - (p : ℚ) * esSum0 p H m) +
        (p : ℚ) * ordSum0 p H (m + 2) := by
    rw [← sum_filter_add_sum_filter_not (tset p (m + 2)) (fun t => (p : ℤ) ∣ t)]
    congr 1
    · rw [sum_dvd_reindex p m, e1, esSum0, mul_sum, mul_sum, ← sum_sub_distrib]
      exact sum_congr rfl fun u hu => by rw [hr_dvd p H hHR m hu]
    · rw [ordSum0, mul_sum]
      refine sum_congr rfl fun t ht => ?_
      rw [mem_filter] at ht
      rw [hr_ord p H hHR (m + 1) ht.1 ht.2]
  have hA4 := esSum0_split p H (m + 4)
  have hA2 := esSum0_split p H (m + 2)
  rw [e3] at e2
  rw [hA4, hA2, e2]
  ring

/-- `σ₀(m) = Σ_{j ≤ m} pʲ = σ(pᵐ)`. -/
def sig0 (m : ℕ) : ℚ := ∑ j ∈ range (m + 1), (p : ℚ) ^ j

/-- `λ₀(m) = Σ_{j ≤ m} min(pʲ, p^{m−j})`. -/
def lam0 (m : ℕ) : ℚ := ∑ j ∈ range (m + 1), ((min (p ^ j) (p ^ (m - j)) : ℕ) : ℚ)

/-- **Kronecker–Hurwitz at prime powers**: `A₀(m) = 2σ(pᵐ) − λ₀(m)`. -/
theorem esSum0_hurwitz (m : ℕ) :
    esSum0 p RamanujanWeil.Arith.Hurwitz.hurwitz m = 2 * sig0 p m - lam0 p m := by
  have hn : 1 ≤ p ^ m := Nat.one_le_pow _ _ hp.out.pos
  have h := kroneckerHurwitz (p ^ m) hn
  have hl : esSum0 p RamanujanWeil.Arith.Hurwitz.hurwitz m =
      ∑ t ∈ Icc (-(2 * ((p ^ m : ℕ) : ℤ))) (2 * ((p ^ m : ℕ) : ℤ)) with
        t ^ 2 ≤ 4 * ((p ^ m : ℕ) : ℤ), RamanujanWeil.Arith.Hurwitz.hurwitz (4 * ((p ^ m : ℕ) : ℤ) - t ^ 2).toNat := rfl
  rw [hl, h, sum_int_divisors, Nat.divisors_prime_pow hp.out, sum_map, sig0, lam0]
  have href : ∑ j ∈ range (m + 1), (p : ℚ) ^ (m - j) = ∑ j ∈ range (m + 1), (p : ℚ) ^ j := by
    rw [← sum_range_reflect (fun j => (p : ℚ) ^ j) (m + 1)]
    exact sum_congr rfl fun j _ => by simp
  rw [← href, mul_sum, ← sum_sub_distrib]
  refine sum_congr rfl fun j hj => ?_
  have hjm : j ≤ m := Nat.lt_succ_iff.mp (mem_range.mp hj)
  simp only [Function.Embedding.coeFn_mk]
  have e1 : ((p ^ m : ℕ) : ℤ) / ((p ^ j : ℕ) : ℤ) = ((p ^ (m - j) : ℕ) : ℤ) := by
    rw [← Int.natCast_div, Nat.pow_div hjm hp.out.pos]
  rw [e1]
  push_cast
  ring

lemma sig0_rec (m : ℕ) :
    sig0 p (m + 4) - ((p : ℚ) + 1) * sig0 p (m + 2) + (p : ℚ) * sig0 p m =
      (p : ℚ) ^ (m + 4) - (p : ℚ) ^ (m + 2) := by
  simp only [sig0, sum_range_succ]
  ring

/-- `0 ≤ λ₀(m) ≤ (m+1)(√p)ᵐ`. -/
lemma lam0_bound (m : ℕ) :
    0 ≤ ((lam0 p m : ℚ) : ℝ) ∧ ((lam0 p m : ℚ) : ℝ) ≤ ((m : ℝ) + 1) * Real.sqrt p ^ m := by
  set s := Real.sqrt p
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hs2 : s ^ 2 = (p : ℝ) := Real.sq_sqrt (Nat.cast_nonneg p)
  have hterm : ∀ j ∈ range (m + 1), (((min (p ^ j) (p ^ (m - j)) : ℕ) : ℝ)) ≤ s ^ m := by
    intro j hj
    have hjm : j ≤ m := Nat.lt_succ_iff.mp (mem_range.mp hj)
    have hsq : (min (p ^ j) (p ^ (m - j))) * (min (p ^ j) (p ^ (m - j))) ≤ p ^ m := by
      calc _ ≤ p ^ j * p ^ (m - j) := Nat.mul_le_mul (min_le_left _ _) (min_le_right _ _)
        _ = p ^ m := by rw [← pow_add, Nat.add_sub_cancel' hjm]
    have hsqR : ((min (p ^ j) (p ^ (m - j)) : ℕ) : ℝ) ^ 2 ≤ (s ^ m) ^ 2 := by
      rw [← pow_mul, mul_comm, pow_mul, hs2, sq]; exact_mod_cast hsq
    exact (pow_le_pow_iff_left₀ (Nat.cast_nonneg _) (pow_nonneg hs0 _) two_ne_zero).mp hsqR
  simp only [lam0, Rat.cast_sum, Rat.cast_natCast]
  refine ⟨by positivity, ?_⟩
  calc ∑ j ∈ range (m + 1), (((min (p ^ j) (p ^ (m - j)) : ℕ) : ℝ))
      ≤ ∑ j ∈ range (m + 1), s ^ m := sum_le_sum hterm
    _ = ((m : ℝ) + 1) * s ^ m := by simp

/-- Growth for `E(m+4) = E(m+2) + μ(m+4)`, `|μ(m+4)| ≤ D (m+5) s^{m+4}`. -/
theorem growth0 (s : ℝ) (hs : 1 ≤ s) (E μ : ℕ → ℝ) (D : ℝ) (hD : 0 ≤ D)
    (hrec : ∀ m, E (m + 4) = E (m + 2) + μ (m + 4))
    (hμ : ∀ m, |μ (m + 4)| ≤ D * ((m : ℝ) + 5) * s ^ (m + 4)) :
    ∃ C : ℝ, ∀ m, |E m| ≤ C * ((m : ℝ) + 1) ^ 2 * s ^ m := by
  set C := |E 0| + |E 1| + |E 2| + |E 3| + D with hC
  have hC0 : 0 ≤ C := by positivity
  have hDC : D ≤ C := by
    have := abs_nonneg (E 0); have := abs_nonneg (E 1); have := abs_nonneg (E 2)
    have := abs_nonneg (E 3); linarith
  refine ⟨C, fun m => ?_⟩
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    rcases lt_or_ge m 4 with hm | hm
    · have hle : |E m| ≤ C := by
        have := abs_nonneg (E 0); have := abs_nonneg (E 1); have := abs_nonneg (E 2)
        have := abs_nonneg (E 3)
        interval_cases m <;> linarith
      have h1 : (1 : ℝ) ≤ ((m : ℝ) + 1) ^ 2 * s ^ m :=
        one_le_mul_of_one_le_of_one_le
          (one_le_pow₀ (by linarith [(Nat.cast_nonneg m : (0:ℝ) ≤ m)])) (one_le_pow₀ hs)
      calc |E m| ≤ C := hle
        _ = C * 1 := (mul_one C).symm
        _ ≤ C * (((m : ℝ) + 1) ^ 2 * s ^ m) := mul_le_mul_of_nonneg_left h1 hC0
        _ = _ := by ring
    · obtain ⟨n, rfl⟩ : ∃ n, m = n + 4 := ⟨m - 4, by omega⟩
      have ihn := ih (n + 2) (by omega)
      have hs0 : 0 ≤ s := by linarith
      have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      have h24 : s ^ (n + 2) ≤ s ^ (n + 4) := pow_le_pow_right₀ hs (by omega)
      have c2 : ((↑(n + 2) : ℝ) + 1) = (n : ℝ) + 3 := by push_cast; ring
      have c4 : ((↑(n + 4) : ℝ) + 1) = (n : ℝ) + 5 := by push_cast; ring
      rw [c2] at ihn
      rw [c4, hrec n]
      have hμn := hμ n
      have hS : 0 ≤ s ^ (n + 4) := pow_nonneg hs0 _
      have step : |E (n + 2) + μ (n + 4)| ≤
          C * ((n : ℝ) + 3) ^ 2 * s ^ (n + 4) + C * ((n : ℝ) + 5) * s ^ (n + 4) := by
        refine (abs_add_le _ _).trans (add_le_add (ihn.trans ?_) (hμn.trans ?_))
        · exact mul_le_mul_of_nonneg_left h24 (by positivity)
        · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hDC (by positivity)) hS
      refine step.trans ?_
      have : ((n : ℝ) + 3) ^ 2 + ((n : ℝ) + 5) ≤ ((n : ℝ) + 5) ^ 2 := by nlinarith
      have hCS : 0 ≤ C * s ^ (n + 4) := mul_nonneg hC0 hS
      nlinarith [mul_le_mul_of_nonneg_left this hCS]

/-- **The ordinary weight-0 sum**: `|O₀(m) − 2pᵐ| ≤ C (m+1)² (√p)ᵐ` for `H = hurwitz`
(i.e. `Σ_{p ∤ t, t² ≤ 4q} H(4q − t²) = 2q + O_p((log q)²√q)`). -/
theorem ordSum0_bound :
    ∃ C : ℝ, ∀ m : ℕ,
      |((ordSum0 p RamanujanWeil.Arith.Hurwitz.hurwitz m - 2 * (p : ℚ) ^ m : ℚ) : ℝ)| ≤
        C * ((m : ℝ) + 1) ^ 2 * Real.sqrt p ^ m := by
  set s := Real.sqrt p with hsdef
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.out.one_lt.le
  have hs : 1 ≤ s := by rw [hsdef]; exact Real.one_le_sqrt.mpr hp1
  have hs0 : 0 ≤ s := by linarith
  have hs2 : s ^ 2 = (p : ℝ) := Real.sq_sqrt (Nat.cast_nonneg p)
  let L : ℕ → ℝ := fun m => ((lam0 p m : ℚ) : ℝ)
  let μ : ℕ → ℝ := fun m => -L m + (s ^ 2 + 1) * L (m - 2) - s ^ 2 * L (m - 4)
  have hrec : ∀ m, ((ordSum0 p RamanujanWeil.Arith.Hurwitz.hurwitz (m + 4) - 2 * (p : ℚ) ^ (m + 4) : ℚ) : ℝ) =
      ((ordSum0 p RamanujanWeil.Arith.Hurwitz.hurwitz (m + 2) - 2 * (p : ℚ) ^ (m + 2) : ℚ) : ℝ) + μ (m + 4) := by
    intro m
    have h := ordSum0_rec p RamanujanWeil.Arith.Hurwitz.hurwitz (RamanujanWeil.Arith.Hurwitz.hurwitzPrimeSquare p hp.out) m
    rw [esSum0_hurwitz, esSum0_hurwitz, esSum0_hurwitz] at h
    have hsig := sig0_rec p m
    have e2 : m + 4 - 2 = m + 2 := by omega
    have e4 : m + 4 - 4 = m := by omega
    simp only [μ, L, e2, e4]
    rw [hs2]
    have hq : (ordSum0 p RamanujanWeil.Arith.Hurwitz.hurwitz (m + 4) - 2 * (p : ℚ) ^ (m + 4)) =
        (ordSum0 p RamanujanWeil.Arith.Hurwitz.hurwitz (m + 2) - 2 * (p : ℚ) ^ (m + 2)) +
          (-lam0 p (m + 4) + ((p : ℚ) + 1) * lam0 p (m + 2) - (p : ℚ) * lam0 p m) := by
      rw [h]; linear_combination 2 * hsig
    rw [hq]; push_cast; ring
  have hμ : ∀ m, |μ (m + 4)| ≤ 4 * ((m : ℝ) + 5) * s ^ (m + 4) := by
    intro m
    have e2 : m + 4 - 2 = m + 2 := by omega
    have e4 : m + 4 - 4 = m := by omega
    simp only [μ, e2, e4]
    obtain ⟨l4, u4⟩ := lam0_bound p (m + 4)
    obtain ⟨l2, u2⟩ := lam0_bound p (m + 2)
    obtain ⟨l0, u0⟩ := lam0_bound p m
    rw [← hsdef] at u4 u2 u0
    simp only [L]
    set a4 := ((lam0 p (m + 4) : ℚ) : ℝ)
    set a2 := ((lam0 p (m + 2) : ℚ) : ℝ)
    set a0 := ((lam0 p m : ℚ) : ℝ)
    set w := s ^ m
    have hw : 0 ≤ w := pow_nonneg hs0 _
    have p4 : s ^ (m + 4) = s ^ 4 * w := by rw [pow_add]; ring
    have p2 : s ^ (m + 2) = s ^ 2 * w := by rw [pow_add]; ring
    rw [p4] at u4 ⊢
    rw [p2] at u2
    have hn0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    push_cast at u4 u2 u0
    have hs2' : 1 ≤ s ^ 2 := one_le_pow₀ hs
    have hs4 : s ^ 4 = s ^ 2 * s ^ 2 := by ring
    have hA : (s ^ 2 + 1) * a2 ≤ 2 * s ^ 2 * (((m : ℝ) + 5) * (s ^ 2 * w)) := by
      have : a2 ≤ ((m : ℝ) + 5) * (s ^ 2 * w) :=
        u2.trans (mul_le_mul_of_nonneg_right (by linarith) (by positivity))
      calc (s ^ 2 + 1) * a2 ≤ (2 * s ^ 2) * a2 := mul_le_mul_of_nonneg_right (by linarith) l2
        _ ≤ 2 * s ^ 2 * (((m : ℝ) + 5) * (s ^ 2 * w)) := mul_le_mul_of_nonneg_left this (by positivity)
    have hB : s ^ 2 * a0 ≤ s ^ 2 * (((m : ℝ) + 5) * (s ^ 2 * w)) := by
      have : a0 ≤ ((m : ℝ) + 5) * (s ^ 2 * w) := by
        refine u0.trans ?_
        have : w ≤ s ^ 2 * w := le_mul_of_one_le_left hw hs2'
        nlinarith
      exact mul_le_mul_of_nonneg_left this (by positivity)
    have hC : a4 ≤ ((m : ℝ) + 5) * (s ^ 4 * w) := u4.trans (by nlinarith)
    rw [abs_le]
    constructor
    · nlinarith
    · nlinarith
  obtain ⟨C, hC⟩ := growth0 s hs
    (fun m => ((ordSum0 p RamanujanWeil.Arith.Hurwitz.hurwitz m - 2 * (p : ℚ) ^ m : ℚ) : ℝ)) μ 4 (by norm_num)
    hrec hμ
  exact ⟨C, hC⟩

end Weight0

end RamanujanWeil.ArithPlan

