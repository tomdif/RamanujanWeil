import RamanujanWeil.Arith.DeuringG7Genus2ExistAlg

/-!
# A3-ord, G7-C: the algebra of a base-point-free pencil (function-field side)

`docs/ARITH_DEURING_G7_GENUS2.md` §7. This file is pure algebra (Mathlib and
`DeuringG7Genus2ExistAlg` only). It replaces the two geometric inputs (b), (c) of §4.2
(Tag 0CCR and finiteness of the pencil map) by one algebraic consequence of base-point freeness
that is easy to prove on the curve.

Setting: `F / K` a field extension, `x ∈ F` nonzero, `V : ℕ → Submodule K F` with `1 ∈ V 0`,
`1, x ∈ V 1`, `V a · V b ⊆ V (a + b)`, all `V n` finite dimensional (`GradedPencil`), and

* **base-point freeness** (`GradedPencil.bpf`): `f ∈ V (n+1)`, `x f ∈ V (n+1)` ⇒ `f ∈ V n`
  (for `n ≥ 1`). Geometrically, `V n = H⁰(L^{⊗n})/s₀ⁿ` and `x = s₁/s₀` with `s₀, s₁` without
  common zero: `s₁ t = s₀ t'` forces `s₀ ∣ t`;
* **linear dimensions** `dim V n = a n − 1` for `n ≥ n₀` (Riemann–Roch in genus 2).

Proved:

* `GradedPencil.le_sup_map`: `V (m+2) = V (m+1) + x V (m+1)` once `m ≥ n₀` (dimension count:
  the intersection lies in `x V m` by base-point freeness);
* `GradedPencil.isIntegralElem`: every element of every `V n` is integral over `K[x]`
  (the union of the `V n` is the `K[x]`-span of one `V B`, finitely generated);
* `GradedPencil.transcendental`: `x` is transcendental (else the union is finite dimensional);
* `GradedPencil.two_le`: `a ≥ 2` (`1, x, …, xⁿ ∈ V n`);
* `GradedPencil.finrank_adjoin_le`: if every `f ∈ F` is a quotient of two elements of one `V m`,
  then `[F : K(x)] ≤ a` (a common denominator and the count `e (T+1) ≤ a (N+T) − 1`);
* `GradedPencil.inv`: the dual pencil `x⁻¹`, `x⁻ⁿ V n` (the chart at `s₁`), with the same axioms;
* **`GradedPencil.toIntegralPencilData`**: for `a = 2`, `IntegralPencilData`.
-/

open Polynomial Module

namespace RamanujanWeil.Arith.Deuring.Geom.G7.Genus2.Pencil

open Exist

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

/-- **A graded pencil** in a field extension `F / K`: the spaces `V n = H⁰(L^{⊗n})/s₀ⁿ` and the
ratio `x = s₁/s₀` of a base-point-free pencil `⟨s₀, s₁⟩ ⊆ H⁰(L)`. -/
structure GradedPencil (K F : Type*) [Field K] [Field F] [Algebra K F] where
  /-- `x = s₁/s₀`. -/
  x : F
  /-- `V n = H⁰(L^{⊗n})/s₀ⁿ`. -/
  V : ℕ → Submodule K F
  x_ne_zero : x ≠ 0
  one_mem_zero : (1 : F) ∈ V 0
  one_mem_one : (1 : F) ∈ V 1
  x_mem : x ∈ V 1
  mul_le : ∀ a b, V a * V b ≤ V (a + b)
  finiteDimensional : ∀ n, FiniteDimensional K (V n)
  /-- Base-point freeness: `s₁ t = s₀ t'` forces `s₀ ∣ t`. -/
  bpf : ∀ n, 1 ≤ n → ∀ f ∈ V (n + 1), x * f ∈ V (n + 1) → f ∈ V n

namespace GradedPencil

variable (P : GradedPencil K F)

theorem mul_mem {a b : ℕ} {u v : F} (hu : u ∈ P.V a) (hv : v ∈ P.V b) : u * v ∈ P.V (a + b) :=
  P.mul_le a b (Submodule.mul_mem_mul hu hv)

theorem mono {n : ℕ} {u : F} (hu : u ∈ P.V n) : u ∈ P.V (n + 1) := by
  simpa using P.mul_mem hu P.one_mem_one

theorem mono_le {m n : ℕ} (hmn : m ≤ n) {u : F} (hu : u ∈ P.V m) : u ∈ P.V n := by
  induction hmn with
  | refl => exact hu
  | step _ ih => exact P.mono ih

theorem le_of_le {m n : ℕ} (hmn : m ≤ n) : P.V m ≤ P.V n := fun _ hu => P.mono_le hmn hu

theorem pow_mem (i : ℕ) : P.x ^ i ∈ P.V i := by
  induction i with
  | zero => simpa using P.one_mem_zero
  | succ i ih => rw [pow_succ]; exact P.mul_mem ih P.x_mem

theorem x_mul_mem {n : ℕ} {u : F} (hu : u ∈ P.V n) : P.x * u ∈ P.V (n + 1) := by
  have := P.mul_mem P.x_mem hu
  rwa [add_comm] at this

theorem aeval_mem (p : K[X]) : aeval P.x p ∈ P.V p.natDegree := by
  rw [aeval_eq_sum_range]
  refine Submodule.sum_mem _ fun i hi => Submodule.smul_mem _ _ ?_
  exact P.mono_le (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)) (P.pow_mem i)

theorem aeval_mul_mem (p : K[X]) {n : ℕ} {u : F} (hu : u ∈ P.V n) :
    aeval P.x p * u ∈ P.V (p.natDegree + n) :=
  P.mul_mem (P.aeval_mem p) hu

theorem prod_mem {ι : Type*} (t : Finset ι) (g : ι → F) {m : ℕ} (hg : ∀ i ∈ t, g i ∈ P.V m) :
    ∏ i ∈ t, g i ∈ P.V (m * t.card) := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa using P.one_mem_zero
  | insert a t ha ih =>
    rw [Finset.prod_insert ha, Finset.card_insert_of_notMem ha,
      show m * (t.card + 1) = m + m * t.card by ring]
    exact P.mul_mem (hg a (Finset.mem_insert_self a t))
      (ih fun i hi => hg i (Finset.mem_insert_of_mem hi))

/-- Multiplication by `x`, as a `K`-linear map. -/
noncomputable def mulX : F →ₗ[K] F := LinearMap.mulLeft K P.x

theorem mulX_injective : Function.Injective P.mulX := fun a b h =>
  mul_left_cancel₀ P.x_ne_zero h

/-- **`1, x, …, xⁿ` are independent**, so `n + 1 ≤ dim V n`. -/
theorem succ_le_finrank (hx : Transcendental K P.x) (n : ℕ) :
    n + 1 ≤ finrank K (P.V n) := by
  have := P.finiteDimensional n
  have hli : LinearIndependent K (fun i : Fin (n + 1) =>
      (⟨P.x ^ (i : ℕ), P.mono_le (Nat.lt_succ_iff.1 i.2) (P.pow_mem i)⟩ : P.V n)) := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    have hg' : aeval P.x (finPoly g) = 0 := by
      rw [aeval_finPoly]
      have := congrArg Subtype.val hg
      simpa using this
    have := (transcendental_iff.1 hx) _ hg'
    rw [← coeff_finPoly g i, this, coeff_zero]
  simpa using hli.fintype_card_le_finrank

/-! ### The dimension count -/

section Dim

variable {a n₀ : ℕ} (hdim : ∀ n, n₀ ≤ n → (finrank K (P.V n) : ℤ) = a * n - 1)
include hdim

/-- **`V (m+2) = V (m+1) + x V (m+1)`** for `m ≥ n₀`, `m ≥ 1`: the two summands meet inside
`x V m` (base-point freeness), so the dimension of the sum is at least
`2 (a (m+1) − 1) − (a m − 1) = a (m+2) − 1`. -/
theorem le_sup_map {m : ℕ} (hm : n₀ ≤ m) (hm1 : 1 ≤ m) :
    P.V (m + 2) ≤ P.V (m + 1) ⊔ (P.V (m + 1)).map P.mulX := by
  have := P.finiteDimensional
  set A := P.V (m + 1)
  set B := (P.V (m + 1)).map P.mulX
  have hA : A ≤ P.V (m + 2) := P.le_of_le (by omega)
  have hB : B ≤ P.V (m + 2) := by
    rintro _ ⟨v, hv, rfl⟩
    exact P.x_mul_mem hv
  have hAB : A ⊔ B ≤ P.V (m + 2) := sup_le hA hB
  have hinf : A ⊓ B ≤ (P.V m).map P.mulX := by
    rintro _ ⟨h1, ⟨v, hv, rfl⟩⟩
    exact ⟨v, P.bpf m hm1 v hv h1, rfl⟩
  have : FiniteDimensional K ↥(A ⊔ B) := Submodule.finiteDimensional_of_le hAB
  have : FiniteDimensional K ↥B := Submodule.finiteDimensional_of_le hB
  have : FiniteDimensional K ↥(A ⊓ B) := Submodule.finiteDimensional_of_le (inf_le_left.trans hA)
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq A B
  have hBdim : finrank K B = finrank K A :=
    (LinearEquiv.finrank_eq (Submodule.equivMapOfInjective _ P.mulX_injective _)).symm
  have hinfdim : finrank K ↥(A ⊓ B) ≤ finrank K (P.V m) :=
    (Submodule.finrank_mono hinf).trans (Submodule.finrank_map_le _ _)
  refine (Submodule.eq_of_le_of_finrank_le hAB ?_).symm.le
  have h0 := hdim m hm
  have h1 := hdim (m + 1) (by omega)
  have h2 := hdim (m + 2) (by omega)
  zify at hsum hBdim hinfdim ⊢
  push_cast at h1 h2
  linarith

/-- Every `V n` lies in the `K`-span closure generated from `V B` by `x`: if `W ⊇ V B` is
stable under `x` then `W ⊇ V n` for all `n`, where `B = n₀ + 2`. -/
theorem le_of_mulX_le {W : Submodule K F} (hB : P.V (max n₀ 1 + 1) ≤ W)
    (hW : ∀ w ∈ W, P.x * w ∈ W) (n : ℕ) : P.V n ≤ W := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases hn : n ≤ max n₀ 1 + 1
    · exact (P.le_of_le hn).trans hB
    · obtain ⟨m, rfl⟩ : ∃ m : ℕ, n = m + 2 := ⟨n - 2, by omega⟩
      refine (P.le_sup_map hdim (m := m) (by omega) (by omega)).trans (sup_le (ih _ (by omega)) ?_)
      rintro _ ⟨v, hv, rfl⟩
      exact hW v (ih (m + 1) (by omega) hv)

/-- **Integrality over `K[x]`.** -/
theorem isIntegralElem (n : ℕ) {f : F} (hf : f ∈ P.V n) :
    (aeval P.x : K[X] →ₐ[K] F).toRingHom.IsIntegralElem f := by
  classical
  letI : Algebra K[X] F := (aeval P.x : K[X] →ₐ[K] F).toRingHom.toAlgebra
  have hsmul : ∀ (p : K[X]) (y : F), p • y = aeval P.x p * y := fun p y => Algebra.smul_def p y
  have := P.finiteDimensional
  set B := max n₀ 1 + 1
  let b := Module.finBasis K (P.V B)
  let N : Submodule K[X] F := Submodule.span K[X] (Set.range fun i => (b i : F))
  have hVN : ∀ k, ∀ y ∈ P.V k, y ∈ N := by
    intro k
    have hB : P.V B ≤ N.restrictScalars K := by
      intro y hy
      have hy' := b.sum_repr ⟨y, hy⟩
      have : y = ∑ i, (C (b.repr ⟨y, hy⟩ i) : K[X]) • (b i : F) := by
        calc y = ((⟨y, hy⟩ : P.V B) : F) := rfl
          _ = ((∑ i, b.repr ⟨y, hy⟩ i • b i : P.V B) : F) := by rw [hy']
          _ = _ := by
            simp only [Submodule.coe_sum, Submodule.coe_smul, hsmul, aeval_C,
              Algebra.smul_def]
      rw [this, Submodule.restrictScalars_mem]
      exact Submodule.sum_mem _ fun i _ =>
        Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self i))
    refine P.le_of_mulX_le hdim (W := N.restrictScalars K) hB (fun w hw => ?_) k
    have : P.x * w = (X : K[X]) • w := by rw [hsmul, aeval_X]
    rw [this]
    exact N.smul_mem X hw
  have hNV : ∀ y ∈ N, ∃ k, y ∈ P.V k := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨i, rfl⟩ := hy
      exact ⟨B, (b i).2⟩
    | zero => exact ⟨0, zero_mem _⟩
    | add y z _ _ hy hz =>
      obtain ⟨k, hk⟩ := hy
      obtain ⟨l, hl⟩ := hz
      exact ⟨max k l, add_mem (P.mono_le (le_max_left _ _) hk)
        (P.mono_le (le_max_right _ _) hl)⟩
    | smul p y _ hy =>
      obtain ⟨k, hk⟩ := hy
      exact ⟨p.natDegree + k, by rw [hsmul]; exact P.aeval_mul_mem p hk⟩
  have hNfg : N.FG := Submodule.fg_span (Set.finite_range _)
  have hN0 : N ≠ ⊥ := by
    intro h
    have := hVN 1 1 P.one_mem_one
    rw [h, Submodule.mem_bot] at this
    exact one_ne_zero this
  have hint : IsIntegral K[X] f := isIntegral_of_smul_mem_submodule N hN0 hNfg f fun y hy => by
    obtain ⟨k, hk⟩ := hNV y hy
    exact hVN _ _ (P.mul_mem hf hk)
  exact hint

/-- **`x` is transcendental.** If it were algebraic, `V n ⊆ K(x) · V B` would be bounded in
dimension, while `dim V n = a n − 1` grows. -/
theorem transcendental (ha : 1 ≤ a) : Transcendental K P.x := by
  classical
  intro halg
  have := P.finiteDimensional
  set E := IntermediateField.adjoin K {P.x}
  have hint : IsIntegral K P.x := halg.isIntegral
  have : FiniteDimensional K E := IntermediateField.adjoin.finiteDimensional hint
  set B := max n₀ 1 + 1
  let b := Module.finBasis K (P.V B)
  let N : Submodule E F := Submodule.span E (Set.range fun i => (b i : F))
  have : Module.Finite E N := Module.Finite.span_of_finite E (Set.finite_range _)
  have : Module.Finite K N := Module.Finite.trans E N
  have hxE : P.x ∈ E := IntermediateField.mem_adjoin_simple_self K P.x
  have hB : P.V B ≤ N.restrictScalars K := by
    intro y hy
    have hy' := b.sum_repr ⟨y, hy⟩
    have : y = ∑ i, (algebraMap K E (b.repr ⟨y, hy⟩ i)) • (b i : F) := by
      calc y = ((⟨y, hy⟩ : P.V B) : F) := rfl
        _ = ((∑ i, b.repr ⟨y, hy⟩ i • b i : P.V B) : F) := by rw [hy']
        _ = _ := by simp only [Submodule.coe_sum, Submodule.coe_smul, algebraMap_smul]
    rw [this, Submodule.restrictScalars_mem]
    exact Submodule.sum_mem _ fun i _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self i))
  have hle := fun n => P.le_of_mulX_le hdim (W := N.restrictScalars K) hB (fun w hw => by
    have : P.x * w = (⟨P.x, hxE⟩ : E) • w := rfl
    rw [this]
    exact N.smul_mem _ hw) n
  have : Module.Finite K (N.restrictScalars K) :=
    Module.Finite.equiv ((Submodule.restrictScalarsEquiv K E F N).symm.restrictScalars K)
  set C := finrank K (N.restrictScalars K)
  have hbound : ∀ n, finrank K (P.V n) ≤ C := fun n => Submodule.finrank_mono (hle n)
  have h1 := hdim (n₀ + C + 2) (by omega)
  have h2 := hbound (n₀ + C + 2)
  zify at h2 ha
  push_cast at h1
  nlinarith

/-- **The degree is at least two.** -/
theorem two_le (ha : 1 ≤ a) : 2 ≤ a := by
  have hx := P.transcendental hdim ha
  have h := P.succ_le_finrank hx (n₀ + 3)
  have h1 := hdim (n₀ + 3) (by omega)
  zify at h
  push_cast at h1
  by_contra hlt
  have : a = 1 := by omega
  subst this
  norm_num at h1
  omega

/-- **`[F : K(x)] ≤ a`**, if every element of `F` is a quotient of two elements of one `V m`.
A `K(x)`-independent family `v` is moved by a common denominator `Q` into one `V N`, and then
`x^j Q v` (`j ≤ T`) are `K`-independent in `V (N + T)`: `e (T + 1) ≤ a (N + T) − 1` for every
`T`, so `e ≤ a`. -/
theorem rank_adjoin_le (ha : 1 ≤ a)
    (hgen : ∀ f : F, ∃ m, ∃ p ∈ P.V m, ∃ q ∈ P.V m, q ≠ 0 ∧ f = p / q) :
    Module.rank (IntermediateField.adjoin K {P.x}) F ≤ a := by
  classical
  have hx := P.transcendental hdim ha
  have := P.finiteDimensional
  set E := IntermediateField.adjoin K {P.x}
  have hxE : P.x ∈ E := IntermediateField.mem_adjoin_simple_self K P.x
  have hcoe : ∀ r : K[X], ((aeval (⟨P.x, hxE⟩ : E) r : E) : F) = aeval P.x r := fun r =>
    (aeval_algebraMap_apply F (⟨P.x, hxE⟩ : E) r).symm
  refine rank_le fun s hs => ?_
  choose m p hp q hq hq0 hpq using hgen
  set M := s.sup m
  set N := M * s.card
  set Q := ∏ v ∈ s, q v
  have hqM : ∀ v ∈ s, q v ∈ P.V M := fun v hv => P.mono_le (Finset.le_sup hv) (hq v)
  have hQ0 : Q ≠ 0 := Finset.prod_ne_zero_iff.2 fun v _ => hq0 v
  have hw : ∀ v ∈ s, Q * v ∈ P.V N := by
    intro v hv
    have e1 := Finset.mul_prod_erase s q hv
    have hqv : v * q v = p v := by
      have := hpq v
      rwa [eq_div_iff (hq0 v)] at this
    have : Q * v = (∏ u ∈ s.erase v, q u) * p v := by
      rw [show Q = q v * ∏ u ∈ s.erase v, q u from e1.symm, ← hqv]
      ring
    rw [this]
    have h1 := P.mono_le (Finset.le_sup hv) (hp v)
    have h2 := P.prod_mem (s.erase v) q fun u hu => hqM u (Finset.mem_of_mem_erase hu)
    have h3 := P.mul_mem h2 h1
    refine P.mono_le (le_of_eq ?_) h3
    obtain ⟨c, hc⟩ : ∃ c, s.card = c + 1 := ⟨s.card - 1, by
      have : 1 ≤ s.card := Finset.card_pos.2 ⟨v, hv⟩
      omega⟩
    rw [Finset.card_erase_of_mem hv, hc, show c + 1 - 1 = c by omega]
    show M * c + M = M * s.card
    rw [hc]
    ring
  set T := a * N + n₀ with hTdef
  let g : s × Fin (T + 1) → P.V (N + T) := fun ij =>
    ⟨P.x ^ (ij.2 : ℕ) * (Q * ij.1),
      P.mono_le (by have := ij.2.2; omega) (P.mul_mem (P.pow_mem ij.2) (hw ij.1 ij.1.2))⟩
  have hli : LinearIndependent K g := by
    refine LinearIndependent.of_comp (P.V (N + T)).subtype ?_
    rw [Fintype.linearIndependent_iff]
    intro c hc ij
    have hc' : ∑ v : s, aeval P.x (finPoly fun j => c (v, j)) * (Q * v) = 0 := by
      rw [← hc, Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun v _ => ?_
      rw [aeval_finPoly, Finset.sum_mul]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [Function.comp_apply, Submodule.subtype_apply, g, smul_mul_assoc]
    have hsum : ∑ v : s, (aeval (⟨P.x, hxE⟩ : E) (finPoly fun j => c (v, j))) • (v : F) = 0 := by
      have h2 : Q * ∑ v : s, (aeval (⟨P.x, hxE⟩ : E) (finPoly fun j => c (v, j))) • (v : F) = 0 := by
        rw [Finset.mul_sum, ← hc']
        refine Finset.sum_congr rfl fun v _ => ?_
        simp only [Algebra.smul_def, IntermediateField.algebraMap_apply, hcoe]
        ring
      exact (mul_eq_zero.1 h2).resolve_left hQ0
    have hz := Fintype.linearIndependent_iff.1 hs _ hsum ij.1
    have hz' : aeval P.x (finPoly fun j => c (ij.1, j)) = 0 := by
      have := congrArg Subtype.val hz
      rwa [hcoe] at this
    have := (transcendental_iff.1 hx) _ hz'
    have h := coeff_finPoly (fun j => c (ij.1, j)) ij.2
    rw [this, coeff_zero] at h
    exact h.symm
  have hcard := hli.fintype_card_le_finrank
  rw [Fintype.card_prod, Fintype.card_coe, Fintype.card_fin] at hcard
  have hd := hdim (N + T) (by omega)
  by_contra hlt
  push Not at hlt
  have hlt' : a + 1 ≤ s.card := hlt
  zify at hcard hlt' ha
  push_cast at hd
  have hT : (T : ℤ) = a * N + n₀ := by rw [hTdef]; push_cast; ring
  have hT0 : (0 : ℤ) ≤ T + 1 := by have := Int.natCast_nonneg T; linarith
  have := mul_le_mul_of_nonneg_right hlt' hT0
  have hn0 : (0 : ℤ) ≤ n₀ := Int.natCast_nonneg n₀
  nlinarith

/-- **`K(x) ⊆ F` is finite of degree `≤ a`.** -/
theorem finiteDimensional_adjoin (ha : 1 ≤ a)
    (hgen : ∀ f : F, ∃ m, ∃ p ∈ P.V m, ∃ q ∈ P.V m, q ≠ 0 ∧ f = p / q) :
    FiniteDimensional (IntermediateField.adjoin K {P.x}) F :=
  rank_lt_aleph0_iff.mp ((P.rank_adjoin_le hdim ha hgen).trans_lt (Cardinal.natCast_lt_aleph0))

theorem finrank_adjoin_le (ha : 1 ≤ a)
    (hgen : ∀ f : F, ∃ m, ∃ p ∈ P.V m, ∃ q ∈ P.V m, q ≠ 0 ∧ f = p / q) :
    finrank (IntermediateField.adjoin K {P.x}) F ≤ a :=
  finrank_le_of_rank_le (P.rank_adjoin_le hdim ha hgen)

end Dim

/-! ### The dual pencil `x⁻¹`, `x⁻ⁿ V n` (the chart at `s₁`) -/

/-- **The dual pencil**: `x⁻¹` and `x⁻ⁿ V n = H⁰(L^{⊗n})/s₁ⁿ`. -/
noncomputable def inv : GradedPencil K F where
  x := P.x⁻¹
  V n := (P.V n).map (LinearMap.mulLeft K (P.x⁻¹ ^ n))
  x_ne_zero := inv_ne_zero P.x_ne_zero
  one_mem_zero := ⟨1, P.one_mem_zero, by simp⟩
  one_mem_one := ⟨P.x, P.x_mem, by simp [P.x_ne_zero]⟩
  x_mem := ⟨1, P.one_mem_one, by simp⟩
  mul_le a b := by
    refine Submodule.mul_le.2 fun u hu v hv => ?_
    obtain ⟨u0, hu0, rfl⟩ := hu
    obtain ⟨v0, hv0, rfl⟩ := hv
    refine ⟨u0 * v0, P.mul_mem hu0 hv0, ?_⟩
    simp only [LinearMap.mulLeft_apply, pow_add]
    ring
  finiteDimensional n := by
    have := P.finiteDimensional n
    infer_instance
  bpf n hn f hf hxf := by
    obtain ⟨g, hg, rfl⟩ := hf
    obtain ⟨h, hh, hgh⟩ := hxf
    simp only [LinearMap.mulLeft_apply] at hgh
    have hx0 := P.x_ne_zero
    have hg' : g = P.x * h := by
      have h1 : P.x⁻¹ ^ (n + 1) * h = P.x⁻¹ ^ (n + 1) * (P.x⁻¹ * g) := hgh.trans (by ring)
      have h2 := mul_left_cancel₀ (pow_ne_zero _ (inv_ne_zero hx0)) h1
      rw [h2]
      field_simp
    have hmem := P.bpf n hn h hh (hg' ▸ hg)
    refine ⟨h, hmem, ?_⟩
    simp only [LinearMap.mulLeft_apply]
    rw [hg', pow_succ]
    field_simp

theorem inv_x : P.inv.x = P.x⁻¹ := rfl

theorem mem_inv_V {n : ℕ} {f : F} (hf : f ∈ P.V n) : P.x⁻¹ ^ n * f ∈ P.inv.V n :=
  ⟨f, hf, rfl⟩

theorem finrank_inv_V (n : ℕ) : finrank K (P.inv.V n) = finrank K (P.V n) :=
  (LinearEquiv.finrank_eq (Submodule.equivMapOfInjective _
    (fun a b h => mul_left_cancel₀ (pow_ne_zero n (inv_ne_zero P.x_ne_zero)) h) _)).symm

/-! ### The packaged statement -/

/-- **`IntegralPencilData` from a graded pencil with `dim V n = 2n − 1` (`n ≥ 2`)** whose spaces
generate the field. -/
noncomputable def toIntegralPencilData
    (hdim : ∀ n, 2 ≤ n → (finrank K (P.V n) : ℤ) = 2 * n - 1)
    (hgen : ∀ f : F, ∃ m, ∃ p ∈ P.V m, ∃ q ∈ P.V m, q ≠ 0 ∧ f = p / q) :
    IntegralPencilData K F :=
  have hdim' : ∀ n, 2 ≤ n → (finrank K (P.V n) : ℤ) = ((2 : ℕ) : ℤ) * n - 1 := fun n hn => by
    rw [hdim n hn]; push_cast; ring
  have hdimi : ∀ n, 2 ≤ n → (finrank K (P.inv.V n) : ℤ) = ((2 : ℕ) : ℤ) * n - 1 :=
    fun n hn => by rw [P.finrank_inv_V]; exact hdim' n hn
  have := P.finiteDimensional
  { x := P.x
    V := P.V
    transcendental := P.transcendental hdim' (by norm_num)
    finiteDimensional_adjoin := P.finiteDimensional_adjoin hdim' (by norm_num) hgen
    finrank_adjoin_le := P.finrank_adjoin_le hdim' (by norm_num) hgen
    one_mem_zero := P.one_mem_zero
    one_mem_one := P.one_mem_one
    x_mem := P.x_mem
    mul_le := P.mul_le
    finiteDimensional_three := P.finiteDimensional 3
    finiteDimensional_six := P.finiteDimensional 6
    five_le_finrank_three := by have := hdim 3 (by norm_num); omega
    finrank_six_le := by have := hdim 6 (by norm_num); omega
    integral_affine := fun f hf => P.isIntegralElem hdim' 3 hf
    integral_infinity := fun f hf => by
      have h := P.inv.isIntegralElem hdimi 3 (P.mem_inv_V hf)
      rw [mul_comm]
      exact h }

end GradedPencil

end RamanujanWeil.Arith.Deuring.Geom.G7.Genus2.Pencil
