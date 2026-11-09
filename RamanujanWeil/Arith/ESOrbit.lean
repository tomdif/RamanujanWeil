import RamanujanWeil.Arith.ESCosets

/-!
# A2 / ES-P8a: left `Γ∞`-orbit sums (docs/ARITH_ES_PLAN.md, §2 P8; docs/ARITH_ES_PROGRESS3.md)

Property (A) of Popa–Zagier, `(1 − S)T̃ − T^∞(1 − S) ∈ (1 − T)R` (modulo `±1`), is equivalent
(PZ (10)) to the vanishing of all left `Γ∞`-orbit sums, `Γ∞ = {±Tᵏ}`. Here:

* `tpow k M = Tᵏ M = [[a + kc, b + kd], [c, d]]`;
* `oS f M = Σ_{k ∈ ℤ} (f(TᵏM) + f(−TᵏM))`, the orbit sum of a coefficient function
  `f : M2 → ℚ` (a `finsum`; finite when `det M ≠ 0` and `f` has finite determinant support);
* `rep M`, a canonical representative of the orbit `±T^ℤ M` (sign normalisation, then reduction
  of the first row modulo the second);
* `sum_smul_eq_zero_of_oS` (**orbit regrouping**): if every orbit sum of `f` vanishes and
  `F|Tᵏ N = F|N`, `F|(−N) = F|N`, then `Σ_N f(N) · F|N = 0`. This is the form in which (A) is
  consumed (on `V₁₀`, and on any module of functions on which `T` fixes `F`).
-/

open Finset

namespace RamanujanWeil.Arith.ES

open M2

/-! ### Powers of `T` acting on the left -/

/-- `Tᵏ M`. -/
def tpow (k : ℤ) (M : M2) : M2 := ⟨M.a + k * M.c, M.b + k * M.d, M.c, M.d⟩

@[simp] lemma tpow_a (k : ℤ) (M : M2) : (tpow k M).a = M.a + k * M.c := rfl
@[simp] lemma tpow_b (k : ℤ) (M : M2) : (tpow k M).b = M.b + k * M.d := rfl
@[simp] lemma tpow_c (k : ℤ) (M : M2) : (tpow k M).c = M.c := rfl
@[simp] lemma tpow_d (k : ℤ) (M : M2) : (tpow k M).d = M.d := rfl

lemma det_tpow (k : ℤ) (M : M2) : (tpow k M).det = M.det := by simp only [tpow, det]; ring
lemma tpow_neg (k : ℤ) (M : M2) : tpow k (-M) = -tpow k M := by ext <;> simp <;> ring
lemma tpow_tpow (j k : ℤ) (M : M2) : tpow j (tpow k M) = tpow (j + k) M := by
  ext <;> simp <;> ring
lemma tpow_zero (M : M2) : tpow 0 M = M := by ext <;> simp
lemma tpow_mul (k : ℤ) (M N : M2) : tpow k M * N = tpow k (M * N) := by
  ext <;> simp <;> ring
lemma tpow_eq_Pk_mul (k : ℤ) (M : M2) : tpow k M = Pk k * M := by
  ext <;> simp [Pk]
lemma mul_neg' (X Y : M2) : X * -Y = -(X * Y) := by ext <;> simp <;> ring
lemma det_neg' (X : M2) : (-X).det = X.det := by simp only [det, neg_a, neg_b, neg_c, neg_d]; ring
lemma neg_neg' (X : M2) : -(-X) = X := by ext <;> simp

lemma cd_ne_of_det {M : M2} (h : M.det ≠ 0) : M.c ≠ 0 ∨ M.d ≠ 0 := by
  by_contra hc; push Not at hc; apply h; simp [det, hc.1, hc.2]

lemma tpow_injective {M : M2} (h : M.det ≠ 0) : Function.Injective (fun k => tpow k M) := by
  intro j k hjk
  have ha := congrArg M2.a hjk
  have hb := congrArg M2.b hjk
  simp only [tpow_a, tpow_b] at ha hb
  rcases cd_ne_of_det h with hc | hd
  · exact mul_right_cancel₀ hc (by linarith)
  · exact mul_right_cancel₀ hd (by linarith)

lemma neg_tpow_injective {M : M2} (h : M.det ≠ 0) : Function.Injective (fun k => -tpow k M) := by
  intro j k hjk
  apply tpow_injective h
  simp only at hjk ⊢
  rw [← neg_neg' (tpow j M), hjk, neg_neg']

/-! ### Orbit sums -/

/-- The left `±T^ℤ`-orbit sum `Σ_k f(TᵏM) + f(−TᵏM)`. -/
noncomputable def oS (f : M2 → ℚ) (M : M2) : ℚ := ∑ᶠ k : ℤ, (f (tpow k M) + f (-tpow k M))

lemma oS_support {f : M2 → ℚ} {M : M2} (hM : M.det ≠ 0) (hf : FinDet M.det f) :
    (Function.support fun k : ℤ => f (tpow k M) + f (-tpow k M)).Finite := by
  have h1 := hf.preimage (tpow_injective hM).injOn
  have h2 := hf.preimage (neg_tpow_injective hM).injOn
  refine (h1.union h2).subset fun k hk => ?_
  simp only [Function.mem_support] at hk
  by_cases h : f (tpow k M) = 0
  · right
    refine ⟨?_, fun h' => hk (by simp only at h'; rw [h, h', add_zero])⟩
    simp only; rw [det_neg', det_tpow]
  · left; exact ⟨det_tpow k M, h⟩

lemma oS_add {f g : M2 → ℚ} {M : M2} (hM : M.det ≠ 0) (hf : FinDet M.det f)
    (hg : FinDet M.det g) : oS (fun N => f N + g N) M = oS f M + oS g M := by
  unfold oS
  rw [← finsum_add_distrib (oS_support hM hf) (oS_support hM hg)]
  congr 1; funext k; ring

lemma oS_sub {f g : M2 → ℚ} {M : M2} (hM : M.det ≠ 0) (hf : FinDet M.det f)
    (hg : FinDet M.det g) : oS (fun N => f N - g N) M = oS f M - oS g M := by
  unfold oS
  rw [← finsum_sub_distrib (oS_support hM hf) (oS_support hM hg)]
  congr 1; funext k; ring

lemma oS_neg_fun (f : M2 → ℚ) (M : M2) : oS (fun N => -f N) M = -oS f M := by
  unfold oS
  rw [← finsum_neg_distrib]
  congr 1; funext k; ring

lemma oS_smul (r : ℚ) (f : M2 → ℚ) (M : M2) : oS (fun N => r * f N) M = r * oS f M := by
  unfold oS
  rw [mul_finsum]
  · congr 1; funext k; ring

/-- Orbit sums only see the `±`-symmetrisation `f(X) + f(−X)`. -/
lemma oS_hat_congr {f g : M2 → ℚ} (h : ∀ X, f X + f (-X) = g X + g (-X)) (M : M2) :
    oS f M = oS g M := by
  unfold oS; congr 1; funext k; exact h _

lemma oS_neg (f : M2 → ℚ) (M : M2) : oS f (-M) = oS f M := by
  unfold oS; congr 1; funext k; rw [tpow_neg, neg_neg']; ring

lemma oS_tpow (f : M2 → ℚ) (j : ℤ) (M : M2) : oS f (tpow j M) = oS f M := by
  unfold oS
  simp only [tpow_tpow]
  exact finsum_comp_equiv (Equiv.addRight j) (f := fun k => f (tpow k M) + f (-tpow k M))

lemma oS_mul_right (f : M2 → ℚ) (M g : M2) : oS f (M * g) = oS (fun N => f (N * g)) M := by
  unfold oS; congr 1; funext k
  show _ = f (tpow k M * g) + f (-tpow k M * g)
  rw [neg_mul', tpow_mul]

/-- Left translations by `g = h Tʲ` (resp. `−h Tʲ`) give the same orbit sums as `h`. -/
lemma oS_left (f : M2 → ℚ) {g h : M2} (j : ℤ) (hg : ∀ X, g * X = h * tpow j X) (M : M2) :
    oS (fun N => f (g * N)) M = oS (fun N => f (h * N)) M := by
  have : oS (fun N => f (g * N)) M = oS (fun N => f (h * N)) (tpow j M) := by
    unfold oS; congr 1; funext k
    show f (g * tpow k M) + f (g * -tpow k M) = f (h * tpow k (tpow j M)) + f (h * -tpow k (tpow j M))
    rw [mul_neg', mul_neg', hg, tpow_tpow, tpow_tpow, add_comm j k]
  rw [this, oS_tpow]

lemma oS_left_neg (f : M2 → ℚ) (g : M2) (M : M2) :
    oS (fun N => f (-g * N)) M = oS (fun N => f (g * N)) M := by
  apply oS_hat_congr; intro X
  show f (-g * X) + f (-g * -X) = f (g * X) + f (g * -X)
  rw [neg_mul', neg_mul', mul_neg', neg_neg']; ring

lemma FinDet.left {n : ℤ} {f : M2 → ℚ} (hf : FinDet n f) {g : M2} (hg : g.det = 1) :
    FinDet n (fun N => f (g * N)) :=
  hf.comp_inj (mul_left_injective' (by rw [hg]; norm_num)) fun N => by rw [det_mul, hg, one_mul]

lemma FinDet.right {n : ℤ} {f : M2 → ℚ} (hf : FinDet n f) {g : M2} (hg : g.det = 1) :
    FinDet n (fun N => f (N * g)) := by
  refine (hf.preimage (f := fun N => N * g) ?_).subset fun N hN => ⟨?_, hN.2⟩
  · intro x _ y _ hxy
    have h2 : adj g * g = 1 := by rw [adj_mul, hg]; rfl
    have h3 : g * adj g = 1 := by ext <;> simp [adj, det] at hg ⊢ <;> linarith
    calc x = x * g * adj g := by rw [mul_assoc, h3, mul_one]
      _ = y * g * adj g := by simp only at hxy; rw [hxy]
      _ = y := by rw [mul_assoc, h3, mul_one]
  · simp only; rw [det_mul, hg, mul_one]; exact hN.1

/-! ### A canonical representative of `±T^ℤ M` -/

/-- The sign-flip condition (lexicographic in `c, d, a, b`). -/
def sgnC (M : M2) : Prop :=
  M.c < 0 ∨ (M.c = 0 ∧ M.d < 0) ∨ (M.c = 0 ∧ M.d = 0 ∧ M.a < 0) ∨
    (M.c = 0 ∧ M.d = 0 ∧ M.a = 0 ∧ M.b < 0)

instance : DecidablePred sgnC := fun M => by unfold sgnC; infer_instance

/-- Sign normalisation. -/
def sgnM (M : M2) : M2 := if sgnC M then -M else M

/-- Reduction of the first row modulo the second. -/
def redM (M : M2) : M2 :=
  if M.c ≠ 0 then tpow (-(M.a / M.c)) M else if M.d ≠ 0 then tpow (-(M.b / M.d)) M else M

/-- Canonical representative of the orbit `±T^ℤ M`. -/
def rep (M : M2) : M2 := redM (sgnM M)

lemma sgnM_eq (M : M2) : sgnM M = M ∨ sgnM M = -M := by
  unfold sgnM; split_ifs <;> simp

lemma sgnC_tpow {k : ℤ} {M : M2} (h2 : ¬(M.c = 0 ∧ M.d = 0)) : sgnC (tpow k M) ↔ sgnC M := by
  unfold sgnC
  simp only [tpow_c, tpow_d, tpow_a, tpow_b]
  constructor <;> rintro (h | h | h | h)
  all_goals first | exact Or.inl h | exact Or.inr (Or.inl h) | exact absurd ⟨h.1, h.2.1⟩ h2

lemma sgnM_tpow (k : ℤ) (M : M2) : sgnM (tpow k M) = tpow k (sgnM M) := by
  by_cases h2 : M.c = 0 ∧ M.d = 0
  · have e : ∀ X : M2, X.c = 0 → X.d = 0 → tpow k X = X := fun X hc hd => by
      ext <;> simp [hc, hd]
    rw [e M h2.1 h2.2]
    rcases sgnM_eq M with h | h <;> rw [h]
    · rw [e M h2.1 h2.2]
    · rw [tpow_neg, e M h2.1 h2.2]
  · unfold sgnM
    by_cases hP : sgnC M
    · rw [esIfPos ((sgnC_tpow h2).mpr hP), esIfPos hP, tpow_neg]
    · rw [esIfNeg (mt (sgnC_tpow h2).mp hP), esIfNeg hP]

lemma sgnC_neg {M : M2} (hM : M ≠ ⟨0, 0, 0, 0⟩) : sgnC (-M) ↔ ¬sgnC M := by
  obtain ⟨a, b, c, d⟩ := M
  have h0 : ¬(a = 0 ∧ b = 0 ∧ c = 0 ∧ d = 0) := by
    rintro ⟨rfl, rfl, rfl, rfl⟩; exact hM rfl
  unfold sgnC
  simp only [neg_a, neg_b, neg_c, neg_d]
  omega

lemma sgnM_neg (M : M2) : sgnM (-M) = sgnM M := by
  by_cases hM : M = ⟨0, 0, 0, 0⟩
  · subst hM; rfl
  · unfold sgnM
    by_cases hP : sgnC M
    · rw [esIfNeg ((not_congr (sgnC_neg hM)).mpr (not_not.mpr hP)), esIfPos hP]
    · rw [esIfPos ((sgnC_neg hM).mpr hP), esIfNeg hP, neg_neg']

lemma redM_tpow (k : ℤ) (M : M2) : redM (tpow k M) = redM M := by
  unfold redM
  by_cases hc : M.c ≠ 0
  · rw [esIfPos (show (tpow k M).c ≠ 0 from hc), esIfPos hc]
    simp only [tpow_a, tpow_c]
    rw [tpow_tpow, Int.add_mul_ediv_right _ _ hc]; congr 1; ring
  · rw [esIfNeg (show ¬(tpow k M).c ≠ 0 from hc), esIfNeg hc]
    by_cases hd : M.d ≠ 0
    · rw [esIfPos (show (tpow k M).d ≠ 0 from hd), esIfPos hd]
      simp only [tpow_b, tpow_d]
      rw [tpow_tpow, Int.add_mul_ediv_right _ _ hd]; congr 1; ring
    · rw [esIfNeg (show ¬(tpow k M).d ≠ 0 from hd), esIfNeg hd]
      simp only [ne_eq, not_not] at hc hd
      ext <;> simp [hc, hd]

lemma redM_eq (M : M2) : ∃ k, redM M = tpow k M := by
  unfold redM
  split_ifs
  · exact ⟨_, rfl⟩
  · exact ⟨_, rfl⟩
  · exact ⟨0, (tpow_zero M).symm⟩

lemma rep_tpow (k : ℤ) (M : M2) : rep (tpow k M) = rep M := by
  unfold rep; rw [sgnM_tpow, redM_tpow]

lemma rep_neg (M : M2) : rep (-M) = rep M := by
  unfold rep; rw [sgnM_neg]

lemma rep_eq (M : M2) : ∃ k, rep M = tpow k M ∨ rep M = -tpow k M := by
  obtain ⟨k, hk⟩ := redM_eq (sgnM M)
  refine ⟨k, ?_⟩
  unfold rep; rw [hk]
  rcases sgnM_eq M with h | h
  · left; rw [h]
  · right; rw [h, tpow_neg]

lemma det_rep (M : M2) : (rep M).det = M.det := by
  obtain ⟨k, h | h⟩ := rep_eq M
  · rw [h, det_tpow]
  · rw [h, det_neg', det_tpow]

/-- The fibre `{N | rep N = rep M}` is the orbit `T^ℤ M ∪ −T^ℤ M`. -/
lemma rep_fibre (M : M2) :
    {N | rep N = rep M} = Set.range (fun k => tpow k M) ∪ Set.range (fun k => -tpow k M) := by
  ext N
  simp only [Set.mem_ofPred_eq, Set.mem_union, Set.mem_range]
  constructor
  · intro h
    obtain ⟨j, hj⟩ := rep_eq N
    obtain ⟨k, hk⟩ := rep_eq M
    -- `N = ±T^{-j} (rep N) = ±T^{-j} (±T^k M)`
    have hN : N = tpow (-j) (rep N) ∨ N = -tpow (-j) (rep N) := by
      rcases hj with hj | hj
      · left; rw [hj, tpow_tpow]; simp [tpow_zero]
      · right; rw [hj, tpow_neg, neg_neg', tpow_tpow]; simp [tpow_zero]
    rw [h] at hN
    rcases hN with hN | hN <;> rcases hk with hk | hk
    · left; exact ⟨-j + k, by rw [hN, hk, tpow_tpow]⟩
    · right; exact ⟨-j + k, by rw [hN, hk, tpow_neg, tpow_tpow]⟩
    · right; exact ⟨-j + k, by rw [hN, hk, tpow_tpow]⟩
    · left; exact ⟨-j + k, by rw [hN, hk, tpow_neg, neg_neg', tpow_tpow]⟩
  · rintro (⟨k, rfl⟩ | ⟨k, rfl⟩)
    · exact rep_tpow k M
    · rw [rep_neg, rep_tpow]

lemma disjoint_orbit {M : M2} (hM : M.det ≠ 0) :
    Disjoint (Set.range (fun k => tpow k M)) (Set.range (fun k => -tpow k M)) := by
  rw [Set.disjoint_left]
  rintro _ ⟨j, rfl⟩ ⟨k, hk⟩
  have hc := congrArg M2.c hk
  have hd := congrArg M2.d hk
  simp only [neg_c, neg_d, tpow_c, tpow_d] at hc hd
  rcases cd_ne_of_det hM with h | h <;> omega

/-- The fibre sum of `f` over the orbit of `M` is the orbit sum. -/
lemma fibre_sum_eq_oS {f : M2 → ℚ} {M : M2} (hM : M.det ≠ 0) (hf : FinDet M.det f) :
    ∑ᶠ (N : M2) (_ : N ∈ {N | rep N = rep M}), f N = oS f M := by
  have hfin : ∀ s : Set M2, (s ⊆ {N | N.det = M.det}) → (s ∩ Function.support f).Finite :=
    fun s hs => hf.subset fun N hN => ⟨hs hN.1, hN.2⟩
  rw [rep_fibre, finsum_mem_union' (disjoint_orbit hM)
      (hfin _ (by rintro _ ⟨k, rfl⟩; exact det_tpow k M))
      (hfin _ (by rintro _ ⟨k, rfl⟩; simp only [Set.mem_ofPred_eq]; rw [det_neg', det_tpow])),
    finsum_mem_range (tpow_injective hM), finsum_mem_range (neg_tpow_injective hM)]
  unfold oS
  have h1 := oS_support hM hf
  rw [finsum_add_distrib]
  · refine (hf.preimage (tpow_injective hM).injOn).subset fun k hk => ⟨det_tpow k M, hk⟩
  · refine (hf.preimage (neg_tpow_injective hM).injOn).subset fun k hk => ⟨?_, hk⟩
    rw [det_neg', det_tpow]

/-! ### Orbit regrouping -/

/-- **Orbit regrouping.** Let `sF : M2 → E` (think `N ↦ F|N`) be invariant under `N ↦ TᵏN` and
`N ↦ −N` on determinant `n`. If `f` is supported on determinant `n` and all its orbit sums
vanish, then `Σ_N f(N) · sF(N) = 0`. -/
theorem sum_smul_eq_zero_of_oS {K E : Type*} [Field K] [CharZero K] [AddCommGroup E] [Module K E]
    {n : ℤ} (hn : n ≠ 0) (sF : M2 → E)
    (hT : ∀ k N, N.det = n → sF (tpow k N) = sF N) (hneg : ∀ N, N.det = n → sF (-N) = sF N)
    {f : M2 → ℚ} (s : Finset M2) (hs : ∀ N, f N ≠ 0 → N ∈ s) (hdet : ∀ N ∈ s, N.det = n)
    (h : ∀ M, M.det = n → oS f M = 0) :
    ∑ N ∈ s, (f N : K) • sF N = 0 := by
  classical
  have hrep : ∀ N ∈ s, sF N = sF (rep N) := by
    intro N hN
    obtain ⟨k, hk | hk⟩ := rep_eq N
    · rw [hk, hT _ _ (hdet N hN)]
    · rw [hk, hneg _ (by rw [det_tpow]; exact hdet N hN), hT _ _ (hdet N hN)]
  rw [Finset.sum_congr rfl fun N hN => by rw [hrep N hN],
    ← Finset.sum_fiberwise_of_maps_to (g := rep) (t := s.image rep)
      (fun N hN => Finset.mem_image_of_mem _ hN)]
  refine Finset.sum_eq_zero fun r hr => ?_
  obtain ⟨N0, hN0, rfl⟩ := Finset.mem_image.mp hr
  have hfib : ∑ N ∈ s with rep N = rep N0, (f N : K) • sF (rep N) =
      ((∑ N ∈ s with rep N = rep N0, f N : ℚ) : K) • sF (rep N0) := by
    rw [Rat.cast_sum, Finset.sum_smul]
    refine Finset.sum_congr rfl fun N hN => ?_
    rw [(Finset.mem_filter.mp hN).2]
  rw [hfib]
  have hfd : FinDet N0.det f := by
    refine (s.finite_toSet).subset fun N hN => hs N hN.2
  have key : ∑ N ∈ s with rep N = rep N0, f N = oS f N0 := by
    rw [← fibre_sum_eq_oS (by rw [hdet N0 hN0]; exact hn) hfd]
    rw [finsum_mem_def]
    rw [finsum_eq_sum_of_support_subset _ (s := s)]
    · rw [Finset.sum_filter]
      refine Finset.sum_congr rfl fun N _ => ?_
      simp [Set.indicator_apply]
    · intro N hN
      rw [Function.mem_support, Set.indicator_apply] at hN
      split_ifs at hN
      · exact hs N hN
      · exact absurd rfl hN
  rw [key, h N0 (hdet N0 hN0), Rat.cast_zero, zero_smul]

end RamanujanWeil.Arith.ES
