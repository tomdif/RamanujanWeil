import RamanujanWeil.Arith.DeuringPLinkField
import RamanujanWeil.Arith.DeuringG8IntIso

/-!
# `PrimeToPLink`, radicial case: a purely inseparable equivariant isogeny gives a link

`docs/ARITH_DEURING_PLINK.md` §3. Setting: `k` algebraically closed of characteristic `p`,
`X`, `Y` one-dimensional abelian varieties with endomorphisms `π_X`, `π_Y`; `Φ ∈ End(X)` commuting
with `π_X`, injective on `k`-points, with `Φ² − tΦ + q = 0`, `deg Φ = q = p^s`, `p ∤ t`;
`ι : X ⟶ Y` equivariant and injective on `k`-points.

**`link_of_injective`**: `Link π_X π_Y`. Write `Φ^m` for the `m`-fold composite, `V = t − Φ`.

* `deg ι = p^e`, `ι ≫ h = [p^e]` (`exists_dual_exact`).
* `Φ^* k(X) ⊆ k(X)^p` (`exists_functionFieldMap_eq_pow`), so `(Φ^m)^* k(X) ⊆ k(X)^{p^m}
  ⊆ ι^* k(Y)` for `m = e + 1`, and `Φ^m = ι ≫ ι''` (`exists_comp_eq_of_mem`). `ι''` is again
  injective on points, `deg ι'' = p^{e''}`, `ι'' ≫ h'' = [p^{e''}]`, and
  `p^e · p^{e''} = deg Φ^m = q^m`.
* `(h'' ≫ h) ≫ Φ^m = [q^m] = V^m ≫ Φ^m`, so `h'' ≫ h = V^m`.
* If `e = 0` or `e'' = 0`, `(ι, h)` or `(h'', ι'')` is already a link of degree `1`. Otherwise
  `α = ι + h''`, `β = ι'' + h` have
  `α ≫ β = Φ^m + [p^{e''}] + [p^e] + V^m = [t_m + p^{e''} + p^e]`, `t_m = Tr Φ^m ≡ t^m (mod p)`,
  which is prime to `p`.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory Polynomial
open scoped CategoryTheory.MonObj IsMulCommutative

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

universe u

namespace RamanujanWeil.Arith.Deuring.PLink

open Stacks.Groupoids RamanujanWeil.Arith.Deuring.Geom RamanujanWeil.Arith.Deuring.Dual2
  RamanujanWeil.Arith.Deuring.Radicial RamanujanWeil.Arith.Deuring.G8
  RamanujanWeil.Arith.Deuring.G8Int

/-! ### Algebra: `Φ^m + V^m` -/

section Alg

/-- The traces `t_m = Φ^m + V^m` for `Φ² − tΦ + q = 0`, `V = t − Φ`. -/
def trSeq (t q : ℤ) : ℕ → ℤ
  | 0 => 2
  | 1 => t
  | (n + 2) => t * trSeq t q (n + 1) - q * trSeq t q n

theorem trSeq_succ_succ (t q : ℤ) (n : ℕ) :
    trSeq t q (n + 1 + 1) = t * trSeq t q (n + 1) - q * trSeq t q n := rfl

/-- `t_{n+1} ≡ t^{n+1} (mod p)` when `p ∣ q`. -/
theorem trSeq_dvd (t q p : ℤ) (hq : p ∣ q) : ∀ n, p ∣ trSeq t q (n + 1) - t ^ (n + 1)
  | 0 => by
    have : trSeq t q (0 + 1) = t := rfl
    rw [this]; simp
  | (n + 1) => by
    have ih := trSeq_dvd t q p hq n
    have e : trSeq t q (n + 1 + 1) - t ^ (n + 1 + 1) =
        t * (trSeq t q (n + 1) - t ^ (n + 1)) - q * trSeq t q n := by
      rw [trSeq_succ_succ]; ring
    rw [e]
    exact dvd_sub (dvd_mul_of_dvd_right ih _) (dvd_mul_of_dvd_left hq _)

theorem pow_add_pow_comm {T : Type*} [CommRing T] (x : T) (t q : ℤ)
    (hx : x * x - (t : T) * x + (q : T) = 0) :
    ∀ n, x ^ n + ((t : T) - x) ^ n = (trSeq t q n : T) ∧
      x ^ (n + 1) + ((t : T) - x) ^ (n + 1) = (trSeq t q (n + 1) : T)
  | 0 => by
    have h0 : trSeq t q 0 = 2 := rfl
    have h1 : trSeq t q (0 + 1) = t := rfl
    rw [h0, h1]
    refine ⟨?_, ?_⟩ <;> push_cast <;> ring
  | (n + 1) => by
    obtain ⟨h0, h1⟩ := pow_add_pow_comm x t q hx n
    refine ⟨h1, ?_⟩
    rw [trSeq_succ_succ]
    push_cast
    rw [← h0, ← h1]
    linear_combination (x ^ n + ((t : T) - x) ^ n) * hx

/-- **`Φ^m + V^m = t_m` and `V^m Φ^m = q^m`**, in any ring. -/
theorem ring_identities {R : Type*} [Ring R] (x : R) (t q : ℤ)
    (hx : x * x - (t : R) * x + (q : R) = 0) (n : ℕ) :
    x ^ n + ((t : R) - x) ^ n = (trSeq t q n : R) ∧ ((t : R) - x) ^ n * x ^ n = (q : R) ^ n ∧
      x ^ n * ((t : R) - x) ^ n = (q : R) ^ n := by
  obtain ⟨T, hTdef⟩ : ∃ T : Subring R, T = Subring.closure ({x} : Set R) := ⟨_, rfl⟩
  haveI : IsMulCommutative T := by
    rw [hTdef]
    exact Subring.isMulCommutative_closure (fun a ha b hb => by
      rw [Set.mem_singleton_iff.mp ha, Set.mem_singleton_iff.mp hb])
  let x' : T := ⟨x, by rw [hTdef]; exact Subring.subset_closure (by simp)⟩
  have hx' : x' * x' - (t : T) * x' + (q : T) = 0 := Subtype.ext (by
    simp only [Subring.coe_add, AddSubgroupClass.coe_sub, Subring.coe_mul, Subring.coe_intCast,
      Subring.coe_zero]
    exact hx)
  have h1 := (pow_add_pow_comm x' t q hx' n).1
  have h2 : ((t : T) - x') ^ n * x' ^ n = (q : T) ^ n := by
    rw [← mul_pow]
    congr 1
    linear_combination (-1 : T) * hx'
  have h3 : x' ^ n * ((t : T) - x') ^ n = (q : T) ^ n := by rw [mul_comm]; exact h2
  refine ⟨?_, ?_, ?_⟩
  · have := congrArg Subtype.val h1
    simpa only [Subring.coe_add, AddSubgroupClass.coe_sub, Subring.coe_pow,
      Subring.coe_intCast] using this
  · have := congrArg Subtype.val h2
    simpa only [Subring.coe_mul, AddSubgroupClass.coe_sub, Subring.coe_pow,
      Subring.coe_intCast] using this
  · have := congrArg Subtype.val h3
    simpa only [Subring.coe_mul, AddSubgroupClass.coe_sub, Subring.coe_pow,
      Subring.coe_intCast] using this

end Alg

/-! ### Composition powers and the endomorphism ring -/

section Pow

variable {k : Type u} [Field k] {X : Over (Spec (.of k))} [GrpObj X]

/-- The `n`-fold composite `Φ ≫ ⋯ ≫ Φ`. -/
noncomputable def cpow (Φ : X ⟶ X) : ℕ → (X ⟶ X)
  | 0 => 𝟙 X
  | (n + 1) => cpow Φ n ≫ Φ

instance isMonHom_cpow (Φ : X ⟶ X) [IsMonHom Φ] : ∀ n, IsMonHom (cpow Φ n)
  | 0 => by unfold cpow; infer_instance
  | (n + 1) => by
    have := isMonHom_cpow Φ n
    unfold cpow; infer_instance

theorem cpow_comm (Φ π : X ⟶ X) (h : Φ ≫ π = π ≫ Φ) : ∀ n, cpow Φ n ≫ π = π ≫ cpow Φ n
  | 0 => by simp [cpow]
  | (n + 1) => by
    simp only [cpow, Category.assoc, h]
    rw [← Category.assoc, cpow_comm Φ π h n, Category.assoc]

theorem cpow_injective (Φ : X ⟶ X) (hinj : ∀ x : 𝟙_ (Over (Spec (.of k))) ⟶ X, x ≫ Φ = 1 → x = 1) :
    ∀ n, ∀ x : 𝟙_ (Over (Spec (.of k))) ⟶ X, x ≫ cpow Φ n = 1 → x = 1
  | 0 => fun x h => by simpa [cpow] using h
  | (n + 1) => fun x h => by
    apply cpow_injective Φ hinj n x
    apply hinj
    change x ≫ (cpow Φ n ≫ Φ) = 1 at h
    rw [← Category.assoc] at h
    exact h

variable [IsCommMonObj X]

theorem postcompOf_congr {f g : X ⟶ X} [IsMonHom f] [IsMonHom g] (h : f = g) :
    postcompOf f = postcompOf g := by
  subst h; rfl

theorem postcompOf_id : postcompOf (𝟙 X) = 1 := by
  haveI : IsMonHom (postcompHom (1 : postcompSubring X)) := by
    rw [postcompHom_one]; infer_instance
  rw [postcompOf_congr postcompHom_one.symm, postcompOf_postcompHom]

theorem postcompOf_cpow (Φ : X ⟶ X) [IsMonHom Φ] :
    ∀ n, postcompOf (cpow Φ n) = postcompOf Φ ^ n
  | 0 => by
    rw [pow_zero, ← postcompOf_id]
    exact postcompOf_congr rfl
  | (n + 1) => by
    have := postcompOf_comp (cpow Φ n) Φ
    rw [pow_succ', ← postcompOf_cpow Φ n, ← this]
    rfl

theorem postcompOf_mul' (f g : X ⟶ X) [IsMonHom f] [IsMonHom g] :
    haveI := isMonHom_mul f g
    postcompOf (f * g) = postcompOf f + postcompOf g := by
  haveI := isMonHom_mul f g
  have e : f * g = postcompHom (postcompOf f + postcompOf g) := by
    rw [postcompHom_add, postcompHom_postcompOf, postcompHom_postcompOf]
  haveI : IsMonHom (postcompHom (postcompOf f + postcompOf g)) := by rw [← e]; infer_instance
  rw [postcompOf_congr e, postcompOf_postcompHom]

theorem postcompOf_zpow_id (n : ℤ) :
    postcompOf ((𝟙 X) ^ n) = (n : postcompSubring X) := by
  have e : (𝟙 X) ^ n = postcompHom (n : postcompSubring X) := (postcompHom_intCast n).symm
  haveI : IsMonHom (postcompHom (n : postcompSubring X)) := by rw [← e]; infer_instance
  rw [postcompOf_congr e, postcompOf_postcompHom]

theorem eq_of_postcompOf_eq (f g : X ⟶ X) [IsMonHom f] [IsMonHom g]
    (h : postcompOf f = postcompOf g) : f = g := by
  rw [← postcompHom_postcompOf f, ← postcompHom_postcompOf g, h]

end Pow

/-! ### Degrees and function fields of composition powers -/

section Geom

variable {k : Type u} [Field k] [IsAlgClosed k] {X Y : Over (Spec (.of k))} [GrpObj X]
  [GrpObj Y] [AlgebraicGeometry.IsAbelianVariety k X] [AlgebraicGeometry.IsAbelianVariety k Y]

theorem homDegree_id (hX : abelianVarietyDimension X = 1) : homDegree (𝟙 X) = 1 := by
  have h := endDegree_zpow_id_eq_pow X 1
  rw [zpow_one, hX] at h
  rw [homDegree_eq_endDegree]
  norm_num at h
  exact_mod_cast h

theorem homDegree_cpow (hX : abelianVarietyDimension X = 1) (Φ : X ⟶ X) [IsMonHom Φ] :
    ∀ n, homDegree (cpow Φ n) = homDegree Φ ^ n
  | 0 => by simp only [cpow, pow_zero]; exact homDegree_id hX
  | (n + 1) => by
    simp only [cpow]
    rw [homDegree_comp hX hX hX, homDegree_cpow hX Φ n, pow_succ]

/-- `(Φ^{n+1})^* k(X) ⊆ k(X)^{p^{n+1}}` for `Φ` injective on points of degree `≠ 1`. -/
theorem functionFieldMap_cpow_eq_pow (p : ℕ) [hp : Fact p.Prime] [CharP k p]
    (hX : abelianVarietyDimension X = 1) (Φ : X ⟶ X) [IsMonHom Φ]
    (hinj : ∀ x : 𝟙_ (Over (Spec (.of k))) ⟶ X, x ≫ Φ = 1 → x = 1) (hdeg : homDegree Φ ≠ 1) :
    ∀ (n : ℕ) [IsDominant (cpow Φ (n + 1)).left] (y : X.left.functionField),
      ∃ w : X.left.functionField, functionFieldMap (cpow Φ (n + 1)).left y = w ^ p ^ (n + 1) := by
  haveI hΦd := isDominant_of_ne_one hX hX Φ (ne_one_of_injective hX Φ hinj)
  intro n
  induction n with
  | zero =>
    intro _ y
    have e : (cpow Φ (0 + 1)).left = Φ.left := by simp [cpow]
    rw [functionFieldMap_congr e, pow_one]
    exact exists_functionFieldMap_eq_pow p hX Φ hinj hdeg y
  | succ n ih =>
    intro _ y
    haveI : IsDominant (cpow Φ (n + 1)).left :=
      isDominant_of_ne_one hX hX _ (ne_one_of_injective hX _ (cpow_injective Φ hinj (n + 1)))
    have e : (cpow Φ (n + 1 + 1)).left = (cpow Φ (n + 1)).left ≫ Φ.left := by
      simp [cpow]
    rw [functionFieldMap_congr e, functionFieldMap_comp]
    obtain ⟨w, hw⟩ := exists_functionFieldMap_eq_pow p hX Φ hinj hdeg y
    obtain ⟨w', hw'⟩ := ih w
    refine ⟨w', ?_⟩
    rw [RingHom.comp_apply, hw, map_pow, hw', ← pow_mul, ← pow_succ]

end Geom

/-! ### The radicial case -/

section RC

variable {k : Type u} [Field k] [IsAlgClosed k] {X Y : Over (Spec (.of k))} [GrpObj X]
  [GrpObj Y] [AlgebraicGeometry.IsAbelianVariety k X] [AlgebraicGeometry.IsAbelianVariety k Y]

/-- `Φ² − tΦ + q = 0` in the endomorphism ring. -/
theorem postcompOf_quadratic (Φ : X ⟶ X) [IsMonHom Φ] (t q : ℤ)
    (hΦ : endPolyEval Φ (Polynomial.X ^ 2 - C t * Polynomial.X + C q) = 1) :
    postcompOf Φ * postcompOf Φ - (t : postcompSubring X) * postcompOf Φ +
      (q : postcompSubring X) = 0 := by
  have h2 := eq_zero_of_postcompHom_eq_one _ hΦ
  have h3 : aeval (postcompOf Φ) (Polynomial.X ^ 2 - C t * Polynomial.X + C q : ℤ[X]) =
      postcompOf Φ * postcompOf Φ - (t : postcompSubring X) * postcompOf Φ +
        (q : postcompSubring X) := by
    simp only [map_add, map_sub, map_mul, map_pow, aeval_X, aeval_C, algebraMap_int_eq,
      eq_intCast, map_intCast, sq]
  rw [← h3]
  exact h2

set_option maxHeartbeats 1600000 in
/-- **The radicial case.** An equivariant homomorphism `i₁ : X ⟶ Y` injective on `k`-points, with
`Φ ∈ ℤ[π_X]`-like data on `X` (injective on points, `Φ² − tΦ + p^s = 0`, `deg Φ = p^s`,
`p ∤ t`), gives a link `X ⟶ Y` of degree prime to `p`. -/
theorem link_of_injective (p : ℕ) [hp : Fact p.Prime] [CharP k p]
    (hX : abelianVarietyDimension X = 1) (hY : abelianVarietyDimension Y = 1)
    (t : ℤ) (s : ℕ) (hs : s ≠ 0) (hpt : ¬ (p : ℤ) ∣ t)
    (πX : X ⟶ X) (πY : Y ⟶ Y) [IsMonHom πX] [IsMonHom πY]
    (Φ : X ⟶ X) [IsMonHom Φ]
    (hΦ : endPolyEval Φ (Polynomial.X ^ 2 - C t * Polynomial.X + C ((p ^ s : ℕ) : ℤ)) = 1)
    (hΦdeg : homDegree Φ = p ^ s)
    (hΦinj : ∀ x : 𝟙_ (Over (Spec (.of k))) ⟶ X, x ≫ Φ = 1 → x = 1)
    (hΦπ : Φ ≫ πX = πX ≫ Φ)
    (i₁ : X ⟶ Y) [IsMonHom i₁] (hi₁π : i₁ ≫ πY = πX ≫ i₁)
    (hi₁inj : ∀ x : 𝟙_ (Over (Spec (.of k))) ⟶ X, x ≫ i₁ = 1 → x = 1) :
    Link πX πY := by
  classical
  have hi₁1 := ne_one_of_injective hX i₁ hi₁inj
  -- the exact dual of `i₁`
  obtain ⟨e, h, hdeg, hh, hi₁h, hi₁d, hpow⟩ := exists_dual_exact p hX hY i₁ hi₁inj
  -- `Φ^m = i₁ ≫ i₂`
  obtain ⟨m, hm⟩ : ∃ m : ℕ, m = e + 1 := ⟨_, rfl⟩
  have hcinj := cpow_injective Φ hΦinj m
  haveI := isDominant_of_ne_one hX hX (cpow Φ m) (ne_one_of_injective hX _ hcinj)
  have hq1 : homDegree Φ ≠ 1 := by
    rw [hΦdeg]
    exact (Nat.one_lt_pow hs hp.out.one_lt).ne'
  have hmem : ∀ y : X.left.functionField,
      functionFieldMap (cpow Φ m).left y ∈ (functionFieldMap i₁.left).range := by
    subst hm
    intro y
    obtain ⟨w, hw⟩ := functionFieldMap_cpow_eq_pow p hX Φ hΦinj hq1 e y
    rw [hw, pow_succ', pow_mul]
    exact hpow (w ^ p)
  obtain ⟨i₂, hi₂m, hi₁i₂⟩ := exists_comp_eq_of_mem hX hY hX i₁ hi₁inj (cpow Φ m) hmem
  have hi₂inj : ∀ x : 𝟙_ (Over (Spec (.of k))) ⟶ Y, x ≫ i₂ = 1 → x = 1 := by
    intro x hx
    obtain ⟨z, rfl⟩ := surj_of_injective hX hY i₁ hi₁inj x
    rw [Category.assoc, hi₁i₂] at hx
    rw [hcinj z hx, MonObj.one_comp]
  have hi₂1 := ne_one_of_injective hY i₂ hi₂inj
  obtain ⟨e₂, h₂, hdeg'', hh₂, hi₂h₂, -, -⟩ := exists_dual_exact p hY hX i₂ hi₂inj
  haveI := hh
  haveI := hi₂m
  haveI := hh₂
  -- degrees
  have hdegm : p ^ e * p ^ e₂ = (p ^ s) ^ m := by
    rw [← hdeg, ← hdeg'', ← homDegree_comp hX hY hX, hi₁i₂, homDegree_cpow hX Φ m, hΦdeg]
  -- equivariance
  have hhπ : h ≫ πX = πY ≫ h :=
    comm_of_comp_eq_zpow hX hY i₁ hi₁1 h _ hi₁h πX πY hi₁π
  have hi₂π : i₂ ≫ πX = πY ≫ i₂ := by
    apply cancel_of_ne_one hX hY i₁ hi₁1
    rw [← Category.assoc, hi₁i₂, cpow_comm Φ πX hΦπ m, ← Category.assoc, hi₁π, Category.assoc,
      hi₁i₂]
  have hh₂π : h₂ ≫ πY = πX ≫ h₂ :=
    comm_of_comp_eq_zpow hY hX i₂ hi₂1 h₂ _ hi₂h₂ πY πX hi₂π
  have hhi₁ : h ≫ i₁ = (𝟙 Y) ^ ((p ^ e : ℕ) : ℤ) := comp_eq_zpow_symm hX hY i₁ hi₁1 h _ hi₁h
  have hh₂i₂ : h₂ ≫ i₂ = (𝟙 X) ^ ((p ^ e₂ : ℕ) : ℤ) :=
    comp_eq_zpow_symm hY hX i₂ hi₂1 h₂ _ hi₂h₂
  have hunit : ∀ d : ℤ, ¬ (p : ℤ) ∣ d → IsUnit (d : k) := fun d hd => by
    rw [isUnit_iff_ne_zero, Ne, CharP.intCast_eq_zero_iff k p]
    exact hd
  -- degenerate cases
  by_cases he : e = 0
  · refine ⟨i₁, h, ((p ^ e : ℕ) : ℤ), hunit _ ?_, inferInstance, hh, hi₁π, hhπ, hi₁h⟩
    rw [he, pow_zero, Nat.cast_one]
    exact fun hd => hp.out.not_dvd_one (by exact_mod_cast Int.natCast_dvd_natCast.mp (by simpa using hd))
  by_cases he₂ : e₂ = 0
  · refine ⟨h₂, i₂, ((p ^ e₂ : ℕ) : ℤ), hunit _ ?_, hh₂, inferInstance, hh₂π, hi₂π,
      hh₂i₂⟩
    rw [he₂, pow_zero, Nat.cast_one]
    exact fun hd => hp.out.not_dvd_one (by exact_mod_cast Int.natCast_dvd_natCast.mp (by simpa using hd))
  -- the main case: `α = i₁ + h₂`, `β = i₂ + h`
  set R := postcompSubring X
  set P : R := postcompOf Φ with hP
  set q : ℤ := ((p ^ s : ℕ) : ℤ) with hq
  have hP2 : P * P - (t : R) * P + (q : R) = 0 := postcompOf_quadratic Φ t q hΦ
  obtain ⟨hsum, hprod, hprod'⟩ := ring_identities P t q hP2 m
  haveI : IsMonHom (h₂ ≫ h) := inferInstance
  set G : R := postcompOf (h₂ ≫ h) with hG
  -- `(h₂ ≫ h) ≫ Φ^m = [q^m]`
  have hGq : (h₂ ≫ h) ≫ cpow Φ m = (𝟙 X) ^ (q ^ m) := by
    rw [← hi₁i₂]
    calc (h₂ ≫ h) ≫ i₁ ≫ i₂ = h₂ ≫ (h ≫ i₁) ≫ i₂ := by simp only [Category.assoc]
      _ = h₂ ≫ ((𝟙 Y) ^ ((p ^ e : ℕ) : ℤ)) ≫ i₂ := by rw [hhi₁]
      _ = ((𝟙 X) ^ ((p ^ e : ℕ) : ℤ)) ≫ h₂ ≫ i₂ := by
        rw [← Category.assoc, ← zpow_id_comp_comm, Category.assoc]
      _ = (𝟙 X) ^ (q ^ m) := by
        rw [hh₂i₂, GrpObj.comp_zpow, Category.comp_id, ← zpow_mul]
        congr 1
        rw [hq]
        exact_mod_cast hdegm
  have hPm : postcompOf (cpow Φ m) = P ^ m := postcompOf_cpow Φ m
  -- hence `h₂ ≫ h = V^m`
  have hGeq : G = ((t : R) - P) ^ m := by
    have h1 : P ^ m * G = (q : R) ^ m := by
      rw [← hPm, hG, ← postcompOf_comp, postcompOf_congr hGq, postcompOf_zpow_id, Int.cast_pow]
    have h2 : P ^ m * (G - ((t : R) - P) ^ m) = 0 := by
      rw [mul_sub, h1, hprod', sub_self]
    have hEmem : G - ((t : R) - P) ^ m ∈ homSub X := by
      refine (homSub X).sub_mem (postcompOf_mem_homSub _) ((homSub X).pow_mem ?_ m)
      exact (homSub X).sub_mem (intCast_mem _ t) (postcompOf_mem_homSub Φ)
    haveI : IsMonHom (postcompHom (G - ((t : R) - P) ^ m)) := hEmem
    by_contra hne
    have hE1 : postcompHom (G - ((t : R) - P) ^ m) ≠ 1 := fun h0 =>
      hne (sub_eq_zero.mp (eq_zero_of_postcompHom_eq_one _ h0))
    apply comp_ne_one hX hX _ (cpow Φ m) hE1 (ne_one_of_injective hX _ hcinj)
    have h3 := postcompHom_mul (P ^ m) (G - ((t : R) - P) ^ m)
    rw [h2, ← hPm, postcompHom_postcompOf] at h3
    exact h3.symm
  -- the link
  haveI hαm : IsMonHom (i₁ * h₂) := isMonHom_mul _ _
  haveI hβm : IsMonHom (i₂ * h) := isMonHom_mul _ _
  have hcomp : (i₁ * h₂) ≫ (i₂ * h) = (cpow Φ m * (𝟙 X) ^ ((p ^ e₂ : ℕ) : ℤ)) *
      ((𝟙 X) ^ ((p ^ e : ℕ) : ℤ) * (h₂ ≫ h)) := by
    rw [MonObj.comp_mul, MonObj.mul_comp, MonObj.mul_comp, hi₁i₂, hh₂i₂, hi₁h]
  set d : ℤ := trSeq t q m + ((p ^ e₂ : ℕ) : ℤ) + ((p ^ e : ℕ) : ℤ) with hd
  haveI : IsMonHom (cpow Φ m * (𝟙 X) ^ ((p ^ e₂ : ℕ) : ℤ)) := isMonHom_mul _ _
  haveI : IsMonHom ((𝟙 X) ^ ((p ^ e : ℕ) : ℤ) * (h₂ ≫ h)) := isMonHom_mul _ _
  haveI : IsMonHom ((cpow Φ m * (𝟙 X) ^ ((p ^ e₂ : ℕ) : ℤ)) *
      ((𝟙 X) ^ ((p ^ e : ℕ) : ℤ) * (h₂ ≫ h))) := isMonHom_mul _ _
  have hαβ : (i₁ * h₂) ≫ (i₂ * h) = (𝟙 X) ^ d := by
    rw [hcomp]
    apply eq_of_postcompOf_eq
    rw [postcompOf_mul', postcompOf_mul', postcompOf_mul', hPm, postcompOf_zpow_id,
      postcompOf_zpow_id, postcompOf_zpow_id, ← hG, hGeq, hd]
    push_cast
    rw [← hsum]
    abel
  have hdp : ¬ (p : ℤ) ∣ d := by
    intro hdvd
    have hpq : (p : ℤ) ∣ q := by
      rw [hq]; push_cast; exact dvd_pow_self _ hs
    have htr := trSeq_dvd t q p hpq e
    have he1 : (p : ℤ) ∣ ((p ^ e : ℕ) : ℤ) := by push_cast; exact dvd_pow_self _ he
    have he2 : (p : ℤ) ∣ ((p ^ e₂ : ℕ) : ℤ) := by push_cast; exact dvd_pow_self _ he₂
    have htm : (p : ℤ) ∣ t ^ (e + 1) := by
      have := ((hdvd.sub he1).sub he2).sub htr
      rw [hd] at this
      have e3 : trSeq t q m + ((p ^ e₂ : ℕ) : ℤ) + ((p ^ e : ℕ) : ℤ) - ((p ^ e : ℕ) : ℤ) -
          ((p ^ e₂ : ℕ) : ℤ) - (trSeq t q (e + 1) - t ^ (e + 1)) = t ^ (e + 1) := by
        rw [hm]; ring
      rwa [e3] at this
    exact hpt ((Nat.prime_iff_prime_int.mp hp.out).dvd_of_dvd_pow htm)
  refine ⟨i₁ * h₂, i₂ * h, d, hunit d hdp, hαm, hβm, ?_, ?_, hαβ⟩
  · rw [MonObj.mul_comp, hi₁π, hh₂π, MonObj.comp_mul]
  · rw [MonObj.mul_comp, hi₂π, hhπ, MonObj.comp_mul]

end RC

end RamanujanWeil.Arith.Deuring.PLink
