import RamanujanWeil.Arith.DeuringG5Surj
import StacksFrontier.AlgebraicGeometry.GroupScheme.AbelianVariety.TorsionDegree

/-!
# A3-ord, G5: cyclic torsion from the minimal order

`docs/ARITH_DEURING_G5.md` §5. For a one-dimensional abelian variety `A₀` over an algebraically
closed field `k` with an endomorphism `π₀` such that `End_π(A₀) = ℤ[π₀]` (`MinimalOrder`) and
`ℤ[π₀] → End(A₀)` injective (`a + bπ₀ = 0 ⇒ a = b = 0`), the group `A₀(k)[n]` is free of rank
one over `ℤ[π₀]/n` for every `n` invertible in `k` (`cyclicTorsion_of_minimalOrder`).

Proof.
* `n = ℓ` prime: `A₀(k)[ℓ]` is an `𝔽_ℓ`-vector space and `π₀` acts linearly. If no `v` has
  `v, π₀ v` independent, `π₀` acts as a scalar `c` (Mathlib
  `LinearMap.exists_eq_smul_id_of_forall_notLinearIndependent`). Then `π₀ − c` kills `A₀[ℓ]`,
  so `π₀ − c = ℓ e` (G3-div) with `e` commuting with `π₀` (cancel `[ℓ]`, G7-dual), hence
  `e ∈ ℤ[π₀]` and `(1 − ℓb)π₀ ∈ ℤ`, impossible.
* `n = ℓ^j`: a point `P` with `ℓ^{j-1} P = v` has trivial annihilator in `ℤ[π₀]/ℓ^j`
  (`ann_of_root`, induction on `j`).
* coprime `n, m`: `P + Q` (`ann_mul`).
* generation: the annihilator condition makes `ℤ[π₀]/n → A₀[n]` injective, and both sides have
  `n²` elements (Stacks `nonempty_torsionBy_addEquiv_of_isUnit`), so it is onto (`gen_of_ann`).

With this, `surjClass_of_descent_minimal` removes the `CyclicTorsion` hypothesis from
`surjClass_of_descent`: for the concrete Jacobian of an elliptic `W₀`, injectivity of
`ℤ[π] → End` is G8's `eq_zero_of_zpow_mul_zpow_eq_one`.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.MonObj

universe u

namespace RamanujanWeil.Arith.Deuring.G5

open RamanujanWeil.Arith.Deuring.Geom RamanujanWeil.Arith.Deuring.Geom.G7
  RamanujanWeil.Arith.Deuring.Dual2 RamanujanWeil.Arith.Deuring.G8 Stacks.Groupoids

section General

variable {k : Type u} [Field k] [IsAlgClosed k]
  {A₀ : Over (Spec (.of k))} [GrpObj A₀] [AlgebraicGeometry.IsAbelianVariety k A₀]
  (π₀ : A₀ ⟶ A₀) [IsMonHom π₀]

/-! ### Arithmetic of `lin` -/

theorem comp_lin (P : Pt A₀) (a b : ℤ) : P ≫ lin π₀ a b = P ^ a * (P ≫ π₀) ^ b := by
  rw [lin, MonObj.comp_mul, GrpObj.comp_zpow, GrpObj.comp_zpow, Category.comp_id]

theorem lin_add (a b c d : ℤ) : lin π₀ a b * lin π₀ c d = lin π₀ (a + c) (b + d) := by
  simp only [lin, zpow_add]
  rw [mul_mul_mul_comm]

theorem lin_neg (a b : ℤ) : (lin π₀ a b)⁻¹ = lin π₀ (-a) (-b) := by
  simp only [lin, zpow_neg, mul_inv]

theorem zpow_comp_lin (P : Pt A₀) (n a b : ℤ) : (P ^ n) ≫ lin π₀ a b = (P ≫ lin π₀ a b) ^ n :=
  GrpObj.zpow_comp _ _ _

theorem comp_lin_mul (P : Pt A₀) (n a b : ℤ) :
    P ≫ lin π₀ (n * a) (n * b) = (P ≫ lin π₀ a b) ^ n := by
  rw [lin_mul, GrpObj.comp_zpow]

theorem comp_lin_sub (P : Pt A₀) (a b c d : ℤ) :
    P ≫ lin π₀ (a - c) (b - d) = (P ≫ lin π₀ a b) * (P ≫ lin π₀ c d)⁻¹ := by
  rw [comp_lin, comp_lin, comp_lin, zpow_sub, zpow_sub, mul_inv, mul_mul_mul_comm]

/-- Changing `a`, `b` modulo `n` does not change `P ≫ lin a b` when `P ^ n = 1`. -/
theorem comp_lin_add_mul (P : Pt A₀) (n : ℤ) (hP : P ^ n = 1) (a b s t : ℤ) :
    P ≫ lin π₀ (a + n * s) (b + n * t) = P ≫ lin π₀ a b := by
  rw [← lin_add, MonObj.comp_mul, comp_lin_mul, ← zpow_comp_lin, hP, MonObj.one_comp, mul_one]

/-! ### The annihilator condition -/

/-- `P` has trivial annihilator in `ℤ[π₀]/n`. -/
def AnnTriv (n : ℤ) (P : Pt A₀) : Prop :=
  P ^ n = 1 ∧ ∀ a b : ℤ, P ≫ lin π₀ a b = 1 → n ∣ a ∧ n ∣ b

variable {π₀}

theorem annTriv_one : AnnTriv π₀ 1 (1 : Pt A₀) :=
  ⟨one_zpow _, fun _ _ _ => ⟨one_dvd _, one_dvd _⟩⟩

/-- **Coprime orders combine.** -/
theorem annTriv_mul {n m : ℤ} (hnm : IsCoprime n m) {P Q : Pt A₀} (hP : AnnTriv π₀ n P)
    (hQ : AnnTriv π₀ m Q) : AnnTriv π₀ (n * m) (P * Q) := by
  obtain ⟨hPn, hPa⟩ := hP
  obtain ⟨hQm, hQa⟩ := hQ
  refine ⟨?_, fun a b h => ?_⟩
  · rw [mul_zpow, zpow_mul, hPn, one_zpow, mul_comm n m, zpow_mul, hQm, one_zpow, one_mul]
  · rw [MonObj.mul_comp] at h
    -- multiply by `m` to kill the `Q` part, by `n` to kill the `P` part
    have hm : P ≫ lin π₀ (m * a) (m * b) = 1 := by
      have := congrArg (· ^ m) h
      simp only [mul_zpow, one_zpow] at this
      rwa [← zpow_comp_lin π₀ Q, hQm, MonObj.one_comp, mul_one, ← comp_lin_mul] at this
    have hn : Q ≫ lin π₀ (n * a) (n * b) = 1 := by
      have := congrArg (· ^ n) h
      simp only [mul_zpow, one_zpow] at this
      rwa [← zpow_comp_lin π₀ P, hPn, MonObj.one_comp, one_mul, ← comp_lin_mul] at this
    obtain ⟨h1, h2⟩ := hPa _ _ hm
    obtain ⟨h3, h4⟩ := hQa _ _ hn
    have ha : n ∣ a := hnm.dvd_of_dvd_mul_left h1
    have hb : n ∣ b := hnm.dvd_of_dvd_mul_left h2
    have ha' : m ∣ a := hnm.symm.dvd_of_dvd_mul_left h3
    have hb' : m ∣ b := hnm.symm.dvd_of_dvd_mul_left h4
    exact ⟨hnm.mul_dvd ha ha', hnm.mul_dvd hb hb'⟩

/-- **Lifting along `ℓ`-power roots.** If `v` has trivial annihilator mod `ℓ` and `Q ^ ℓ^i = v`,
then `Q` has trivial annihilator mod `ℓ^(i+1)`. -/
theorem ann_of_root {ℓ : ℤ} {v : Pt A₀}
    (hv : ∀ a b : ℤ, v ≫ lin π₀ a b = 1 → ℓ ∣ a ∧ ℓ ∣ b) :
    ∀ (i : ℕ) (Q : Pt A₀), Q ^ (ℓ ^ i) = v →
      ∀ a b : ℤ, Q ≫ lin π₀ a b = 1 → ℓ ^ (i + 1) ∣ a ∧ ℓ ^ (i + 1) ∣ b := by
  intro i
  induction i with
  | zero =>
    intro Q hQ a b h
    rw [pow_zero, zpow_one] at hQ
    subst hQ
    simpa using hv a b h
  | succ i ih =>
    intro Q hQ a b h
    have hva : v ≫ lin π₀ a b = 1 := by
      rw [← hQ, zpow_comp_lin, h, one_zpow]
    obtain ⟨⟨a', rfl⟩, ⟨b', rfl⟩⟩ := hv a b hva
    have hQ' : (Q ^ ℓ) ^ (ℓ ^ i) = v := by
      rw [← zpow_mul, ← pow_succ']; exact hQ
    have h' : (Q ^ ℓ) ≫ lin π₀ a' b' = 1 := by
      rw [zpow_comp_lin, ← comp_lin_mul]; exact h
    obtain ⟨h1, h2⟩ := ih (Q ^ ℓ) hQ' a' b' h'
    rw [pow_succ' ℓ (i + 1)]
    exact ⟨mul_dvd_mul_left ℓ h1, mul_dvd_mul_left ℓ h2⟩

/-- **Generation from the annihilator condition, by counting.** -/
theorem gen_of_ann (hA₀ : abelianVarietyDimension A₀ = 1) (N : ℕ) (hN : IsUnit (N : k))
    {P : Pt A₀} (hP : AnnTriv π₀ (N : ℤ) P) :
    ∀ x : Pt A₀, x ^ (N : ℤ) = 1 → ∃ a b : ℤ, x = P ≫ lin π₀ a b := by
  classical
  obtain ⟨hPN, hann⟩ := hP
  have hN0 : N ≠ 0 := by rintro rfl; simp at hN
  haveI : NeZero N := ⟨hN0⟩
  have hmem : ∀ a b : ℤ, Additive.ofMul (P ≫ lin π₀ a b) ∈ Tor A₀ N := fun a b => by
    rw [mem_tor_iff, ← zpow_comp_lin, hPN, MonObj.one_comp]
  let φ : ZMod N × ZMod N → Tor A₀ N := fun ab =>
    ⟨Additive.ofMul (P ≫ lin π₀ (ab.1.val : ℤ) (ab.2.val : ℤ)), hmem _ _⟩
  have hinj : Function.Injective φ := by
    rintro ⟨a, b⟩ ⟨c, d⟩ h
    have h1 : P ≫ lin π₀ (a.val : ℤ) (b.val : ℤ) = P ≫ lin π₀ (c.val : ℤ) (d.val : ℤ) := by
      have := congrArg (fun z : Tor A₀ N => Additive.toMul (z : Additive (Pt A₀))) h
      simpa [φ] using this
    have h2 : P ≫ lin π₀ ((a.val : ℤ) - c.val) ((b.val : ℤ) - d.val) = 1 := by
      rw [comp_lin_sub, h1, mul_inv_cancel]
    obtain ⟨ha, hb⟩ := hann _ _ h2
    have e1 : ((a.val : ℤ) : ZMod N) = ((c.val : ℤ) : ZMod N) :=
      (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).2 (by
        have := dvd_neg.2 ha; rwa [neg_sub] at this)
    have e2 : ((b.val : ℤ) : ZMod N) = ((d.val : ℤ) : ZMod N) :=
      (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).2 (by
        have := dvd_neg.2 hb; rwa [neg_sub] at this)
    simp only [Int.cast_natCast, ZMod.natCast_zmod_val] at e1 e2
    rw [e1, e2]
  have hcardT : Nat.card (Tor A₀ N) = N ^ 2 := by
    obtain ⟨e⟩ := nonempty_torsionBy_addEquiv_of_isUnit (k := k) A₀ N hN
    rw [Nat.card_congr e.toEquiv, Nat.card_fun, Nat.card_zmod, hA₀, Nat.card_eq_fintype_card,
      Fintype.card_fin]
  have hfinT : Finite (Tor A₀ N) := by
    obtain ⟨e⟩ := nonempty_torsionBy_addEquiv_of_isUnit (k := k) A₀ N hN
    exact Finite.of_equiv _ e.symm.toEquiv
  have hcardS : Nat.card (ZMod N × ZMod N) = N ^ 2 := by
    rw [Nat.card_prod, Nat.card_zmod, sq]
  have hbij : Function.Bijective φ := hinj.bijective_of_nat_card_le (by rw [hcardT, hcardS])
  intro x hx
  obtain ⟨⟨a, b⟩, hab⟩ := hbij.2 ⟨Additive.ofMul x, (mem_tor_iff N x).2 hx⟩
  refine ⟨a.val, b.val, ?_⟩
  have := congrArg (fun z : Tor A₀ N => Additive.toMul (z : Additive (Pt A₀))) hab
  simpa [φ] using this.symm

/-- Linear algebra over `𝔽_ℓ`: an additive endomorphism of an `𝔽_ℓ`-vector space either has a
cyclic vector or is a scalar. -/
theorem exists_cyclic_or_scalar {M : Type*} [AddCommGroup M] (ℓ : ℕ) [Fact ℓ.Prime]
    [Module (ZMod ℓ) M] (φ : M →+ M) :
    (∃ v : M, ∀ a b : ℤ, a • v + b • φ v = 0 → (ℓ : ℤ) ∣ a ∧ (ℓ : ℤ) ∣ b) ∨
      ∃ c : ℕ, ∀ x : M, φ x = c • x := by
  by_cases h : ∃ v : M, ∀ a b : ℤ, a • v + b • φ v = 0 → (ℓ : ℤ) ∣ a ∧ (ℓ : ℤ) ∣ b
  · exact Or.inl h
  right
  push_neg at h
  let f := φ.toZModLinearMap ℓ
  have hdep : ∀ w : M, ¬ LinearIndependent (ZMod ℓ) ![w, f w] := by
    intro w hw
    obtain ⟨a, b, hab, hnd⟩ := h w
    rw [LinearIndependent.pair_iff] at hw
    have hz : (a : ZMod ℓ) • w + (b : ZMod ℓ) • f w = 0 := by
      rw [Int.cast_smul_eq_zsmul, Int.cast_smul_eq_zsmul]
      exact hab
    obtain ⟨h1, h2⟩ := hw _ _ hz
    exact hnd ((ZMod.intCast_zmod_eq_zero_iff_dvd a ℓ).1 h1)
      ((ZMod.intCast_zmod_eq_zero_iff_dvd b ℓ).1 h2)
  obtain ⟨c, hc⟩ := LinearMap.exists_eq_smul_id_of_forall_notLinearIndependent hdep
  refine ⟨c.val, fun x => ?_⟩
  have h1 : f x = (c • (1 : M →ₗ[ZMod ℓ] M)) x := by rw [hc]
  change φ x = c • x at h1
  rw [h1]
  calc c • x = ((c.val : ℕ) : ZMod ℓ) • x := by rw [ZMod.natCast_zmod_val]
    _ = c.val • x := Nat.cast_smul_eq_nsmul _ _ _

/-- **The prime case.** `MinimalOrder` + `ℤ[π₀] ↪ End(A₀)` give a point of order `ℓ` with trivial
annihilator in `ℤ[π₀]/ℓ`. -/
theorem exists_annTriv_prime (hA₀ : abelianVarietyDimension A₀ = 1) (hmin : MinimalOrder π₀)
    (hind : ∀ a b : ℤ, lin π₀ a b = 1 → a = 0 ∧ b = 0) (ℓ : ℕ) (hℓ : ℓ.Prime)
    (hℓk : IsUnit (ℓ : k)) : ∃ v : Pt A₀, AnnTriv π₀ (ℓ : ℤ) v := by
  classical
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  have hsmul : ∀ x : Tor A₀ ℓ, ℓ • x = 0 := fun x => by
    apply Subtype.ext
    have := x.2
    change ((ℓ : ℤ) • (x : Additive (Pt A₀)) = 0) at this
    rw [natCast_zsmul] at this
    simpa using this
  letI : Module (ZMod ℓ) (Tor A₀ ℓ) := AddCommGroup.zmodModule hsmul
  rcases exists_cyclic_or_scalar ℓ (torAct π₀ ℓ) with ⟨v, hv⟩ | ⟨c, hc⟩
  · refine ⟨G7.pt v, (mem_tor_iff ℓ (G7.pt v)).1 v.2, fun a b h => hv a b ?_⟩
    apply Subtype.ext
    apply Additive.toMul.injective
    change (G7.pt v) ^ a * (G7.pt v ≫ π₀) ^ b = 1
    rw [← comp_lin]; exact h
  exfalso
  have hkill : ∀ x : Pt A₀, x ^ (ℓ : ℤ) = 1 → x ≫ lin π₀ (-(c : ℤ)) 1 = 1 := by
    intro x hx
    have h1 := congrArg (fun z : Tor A₀ ℓ => Additive.toMul (z : Additive (Pt A₀)))
      (hc ⟨Additive.ofMul x, (mem_tor_iff ℓ x).2 hx⟩)
    change x ≫ π₀ = x ^ c at h1
    rw [comp_lin, zpow_one, h1, zpow_neg, ← zpow_natCast, inv_mul_cancel]
  have hℓk' : IsUnit (((ℓ : ℤ)) : k) := by simpa using hℓk
  have hℓ0 : (ℓ : ℤ) ≠ 0 := by exact_mod_cast hℓ.ne_zero
  obtain ⟨e, he, hle⟩ := exists_isMonHom_zpow_comp_eq (ℓ : ℤ) hℓk' (lin π₀ (-(c : ℤ)) 1) hkill
  haveI := he
  -- `[ℓ] ≫ g = g ^ ℓ` and `[ℓ]` commutes with `π₀`
  have hpre : ∀ (g : A₀ ⟶ A₀) [IsMonHom g], ((𝟙 A₀) ^ (ℓ : ℤ)) ≫ g = g ^ (ℓ : ℤ) := by
    intro g _
    rw [GrpObj.zpow_comp, Category.id_comp]
  have hcomm : e ≫ π₀ = π₀ ≫ e := by
    apply cancel_of_ne_one hA₀ hA₀ _ (zpow_id_ne_one hA₀ (ℓ : ℤ) hℓ0)
    rw [← Category.assoc, hle, lin_comm, ← Category.assoc, hpre π₀, ← comp_zpow_id,
      Category.assoc, hle]
  obtain ⟨a, b, rfl⟩ := hmin e he hcomm
  rw [hpre, ← lin_mul] at hle
  have h1 : lin π₀ ((ℓ : ℤ) * a + (c : ℤ)) ((ℓ : ℤ) * b - 1) = 1 := by
    have : lin π₀ ((ℓ : ℤ) * a + (c : ℤ)) ((ℓ : ℤ) * b - 1) =
        lin π₀ ((ℓ : ℤ) * a) ((ℓ : ℤ) * b) * (lin π₀ (-(c : ℤ)) 1)⁻¹ := by
      rw [lin_neg, lin_add]; congr 1 <;> ring
    rw [this, hle, mul_inv_cancel]
  have h2 := (hind _ _ h1).2
  have h3 : (ℓ : ℤ) ∣ 1 := ⟨b, by linarith⟩
  have h4 : ℓ ∣ 1 := by exact_mod_cast h3
  exact hℓ.one_lt.ne' (Nat.dvd_one.1 h4)

/-- **Existence of a point with trivial annihilator mod `N`.** -/
theorem exists_annTriv (hA₀ : abelianVarietyDimension A₀ = 1) (hmin : MinimalOrder π₀)
    (hind : ∀ a b : ℤ, lin π₀ a b = 1 → a = 0 ∧ b = 0) :
    ∀ N : ℕ, IsUnit (N : k) → ∃ P : Pt A₀, AnnTriv π₀ (N : ℤ) P := by
  intro N
  induction N using Nat.recOnPrimeCoprime with
  | zero => intro h; simp at h
  | prime_pow p j hp =>
    intro hu
    cases j with
    | zero => exact ⟨1, by simpa using annTriv_one (π₀ := π₀)⟩
    | succ j =>
      have hpk : IsUnit (p : k) := by
        rw [Nat.cast_pow] at hu; exact (isUnit_pow_iff (Nat.succ_ne_zero j)).1 hu
      obtain ⟨v, hv1, hv⟩ := exists_annTriv_prime hA₀ hmin hind p hp hpk
      have hp0 : ((p : ℤ) ^ j) ≠ 0 := pow_ne_zero _ (by exact_mod_cast hp.ne_zero)
      obtain ⟨P, hP⟩ := exists_zpow_eq_point ((p : ℤ) ^ j) hp0 v
      refine ⟨P, ?_, ?_⟩
      · rw [Nat.cast_pow, pow_succ, zpow_mul, hP, hv1]
      · intro a b h
        rw [Nat.cast_pow]
        exact ann_of_root hv j P hP a b h
  | coprime a b _ _ hab iha ihb =>
    intro hu
    rw [Nat.cast_mul] at hu
    obtain ⟨P, hP⟩ := iha (isUnit_of_mul_isUnit_left hu)
    obtain ⟨Q, hQ⟩ := ihb (isUnit_of_mul_isUnit_right hu)
    refine ⟨P * Q, ?_⟩
    rw [Nat.cast_mul]
    exact annTriv_mul (Nat.isCoprime_iff_coprime.2 hab) hP hQ

/-- **Cyclic torsion from the minimal order.** -/
theorem cyclicTorsion_of_minimalOrder (hA₀ : abelianVarietyDimension A₀ = 1)
    (hmin : MinimalOrder π₀) (hind : ∀ a b : ℤ, lin π₀ a b = 1 → a = 0 ∧ b = 0) (n : ℤ)
    (hn : IsUnit (n : k)) : CyclicTorsion π₀ n := by
  have hN : IsUnit ((n.natAbs : ℕ) : k) := by
    rcases Int.natAbs_eq n with h | h
    · rw [h, Int.cast_natCast] at hn; exact hn
    · rw [h, Int.cast_neg, Int.cast_natCast] at hn
      have := hn.neg
      rwa [neg_neg] at this
  obtain ⟨P, hP⟩ := exists_annTriv hA₀ hmin hind n.natAbs hN
  have hgen := gen_of_ann hA₀ n.natAbs hN hP
  obtain ⟨hP1, hann⟩ := hP
  rcases Int.natAbs_eq n with h | h
  · rw [h]; exact ⟨P, hP1, hgen, hann⟩
  · rw [h]
    refine ⟨P, by rw [zpow_neg, hP1, inv_one], fun x hx => hgen x ?_, fun a b hab => ?_⟩
    · rw [zpow_neg, inv_eq_one] at hx; exact hx
    · obtain ⟨h1, h2⟩ := hann a b hab
      exact ⟨neg_dvd.2 h1, neg_dvd.2 h2⟩

/-- `ℤ[π] → End(A)` is injective when `χ_π = X² − tX + q` with `t² < 4q`. -/
theorem lin_eq_one_iff {A : Over (Spec (.of k))} [GrpObj A] [AlgebraicGeometry.IsAbelianVariety k A]
    (hA : abelianVarietyDimension A = 1) (π : A ⟶ A) [IsMonHom π] (t : ℤ) (q : ℕ)
    (hχ : endCharPoly A π = Polynomial.X ^ 2 - Polynomial.C (t : ℚ) * Polynomial.X +
      Polynomial.C (q : ℚ)) (hdisc : t ^ 2 < 4 * (q : ℤ)) :
    ∀ a b : ℤ, lin π a b = 1 → a = 0 ∧ b = 0 := by
  intro a b h
  obtain ⟨-, hdeg, htr⟩ := charPoly_data hA π t q hχ
  exact eq_zero_of_zpow_mul_zpow_eq_one hA π t q hdeg htr hdisc a b (by rw [mul_comm]; exact h)

end General

/-! ### `surj_class` without the cyclic-torsion hypothesis -/

section Finite

open RamanujanWeil.Ihara RamanujanWeil.Arith.Deuring.Mult

variable {K : Type u} [Field K] [Fintype K]

/-- **`surj_class` (G5) from Weierstrass descent and the minimal order.** As
`surjClass_of_descent`, with `CyclicTorsion` discharged by `cyclicTorsion_of_minimalOrder`. -/
theorem surjClass_of_descent_minimal (hD : WeierstrassDescent K) {W₀ : WeierstrassCurve K}
    [W₀.IsElliptic] (S₀ : Jac.JacSite W₀) {t : ℤ} (ht₀ : traceOfFrob W₀ = t)
    (hp : ¬ (ringChar K : ℤ) ∣ t) (hlt : t ^ 2 < 4 * (Nat.card K : ℤ))
    (hmin : MinimalOrder S₀.frobeniusJacobian.π)
    (C : IsogClass K t) (hC : IsogClassPred C W₀)
    (Λ : WeierstrassCurve K → TrDet t (Nat.card K))
    (hΛ : ∀ (W : WeierstrassCurve K) (hW : W.Δ ≠ 0), traceOfFrob W = t →
        haveI : W.IsElliptic := ⟨isUnit_iff_ne_zero.mpr hW⟩
        ∃ (S : Jac.JacSite W) (b : Module.Basis (Fin 2) ℤ
            (homPi S₀.frobeniusJacobian.π S.frobeniusJacobian.π)),
          (Λ W).1 = LinearMap.toMatrix b b
            (piAct S₀.frobeniusJacobian.π S.frobeniusJacobian.π))
    (M : TrDet t (Nat.card K)) :
    ∃ W : WeierstrassCurve K, IsogClassPred C W ∧ ∃ g : GL2, g • Λ W = M := by
  have hind := lin_eq_one_iff S₀.frobeniusJacobian.dim_eq S₀.frobeniusJacobian.π t
    (Nat.card K) (by rw [← ht₀]; exact S₀.frobeniusJacobian.charPoly_eq) hlt
  exact surjClass_of_descent hD S₀ ht₀ hp hlt hmin
    (fun n hn => cyclicTorsion_of_minimalOrder S₀.frobeniusJacobian.dim_eq hmin hind n hn)
    C hC Λ hΛ M

end Finite

end RamanujanWeil.Arith.Deuring.G5
