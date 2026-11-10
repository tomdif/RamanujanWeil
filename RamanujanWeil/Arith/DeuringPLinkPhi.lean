import RamanujanWeil.Arith.DeuringPLinkRC
import StacksFrontier.AlgebraicGeometry.GroupScheme.AbelianVariety.TorsionDegree

/-!
# `PrimeToPLink`: the purely inseparable root of `X² − tX + q`, and transport along isogenies

`docs/ARITH_DEURING_PLINK.md` §4. Setting: `k` algebraically closed of characteristic `p`, `X` a
one-dimensional abelian variety with `π ∈ End(X)`, `π² − tπ + q = 0`, `q = p^s`, `p ∤ t`,
`deg π = deg V = q` where `V = t − π` (`vOf π t`). This is the predicate `Good π t q`.

* `card_torsion_le`: `#X(k)[p^b] ≤ p^b` (Stacks `exists_torsionBy_char_pow_addEquiv`, `f ≤ 1`).
* **`exists_phi`**: one of `π`, `V` is injective on `k`-points. Otherwise `π x = 0`, `V y = 0`
  with `x, y ≠ 0`; then `x, y ∈ X[q]`, and suitable multiples `x'`, `y'` have order `p`. Since
  `#X[p] ≤ p`, `y' ∈ ⟨x'⟩`, so `π y' = 0`; but `π y' = t y'` (as `V y' = 0`), and `p ∤ t`.
* `good_of_hom`: `Good` transports along nonzero equivariant homomorphisms (`deg` is
  multiplicative and `f` is an epimorphism).
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

section Alg

/-- If `x² − tx + q = 0` then `(t − x)² − t(t − x) + q = 0`. -/
theorem quad_conj {R : Type*} [Ring R] (x : R) (t q : ℤ)
    (hx : x * x - (t : R) * x + (q : R) = 0) :
    ((t : R) - x) * ((t : R) - x) - (t : R) * ((t : R) - x) + (q : R) = 0 := by
  have hc : x * (t : R) = (t : R) * x := ((Int.cast_commute t x).eq).symm
  have e : ((t : R) - x) * ((t : R) - x) - (t : R) * ((t : R) - x) + (q : R) =
      x * x - x * (t : R) + (q : R) := by
    simp only [sub_mul, mul_sub]
    abel
  rw [e, hc, hx]

end Alg

section Phi

variable {k : Type u} [Field k] [IsAlgClosed k] {X Z : Over (Spec (.of k))} [GrpObj X]
  [GrpObj Z] [AlgebraicGeometry.IsAbelianVariety k X] [AlgebraicGeometry.IsAbelianVariety k Z]

/-- `V = t − π`. -/
noncomputable def vOf (π : X ⟶ X) (t : ℤ) : X ⟶ X := π ^ (-1 : ℤ) * (𝟙 X) ^ t

instance isMonHom_vOf (π : X ⟶ X) [IsMonHom π] (t : ℤ) : IsMonHom (vOf π t) := by
  haveI : IsMonHom (π ^ (-1 : ℤ)) := isMonHom_zpow_of_isCommMonObj _ _
  exact isMonHom_mul _ _

theorem comp_vOf {πX : X ⟶ X} {πZ : Z ⟶ Z} [IsMonHom πX] [IsMonHom πZ] (t : ℤ) (f : X ⟶ Z)
    [IsMonHom f] (h : f ≫ πZ = πX ≫ f) : f ≫ vOf πZ t = vOf πX t ≫ f := by
  unfold vOf
  rw [MonObj.comp_mul, MonObj.mul_comp, GrpObj.comp_zpow, GrpObj.comp_zpow, GrpObj.zpow_comp,
    GrpObj.zpow_comp, h, Category.id_comp, Category.comp_id]

theorem postcompOf_zpow (f : X ⟶ X) [IsMonHom f] (n : ℤ) :
    haveI := isMonHom_zpow_of_isCommMonObj f n
    postcompOf (f ^ n) = n • postcompOf f := by
  haveI := isMonHom_zpow_of_isCommMonObj f n
  have e : f ^ n = postcompHom (n • postcompOf f) := by
    rw [postcompHom_zsmul, postcompHom_postcompOf]
  haveI : IsMonHom (postcompHom (n • postcompOf f)) := by rw [← e]; infer_instance
  rw [postcompOf_congr e, postcompOf_postcompHom]

theorem postcompOf_vOf (π : X ⟶ X) [IsMonHom π] (t : ℤ) :
    postcompOf (vOf π t) = (t : postcompSubring X) - postcompOf π := by
  haveI : IsMonHom (π ^ (-1 : ℤ)) := isMonHom_zpow_of_isCommMonObj _ _
  unfold vOf
  rw [postcompOf_mul', postcompOf_zpow, postcompOf_zpow_id, neg_one_zsmul]
  abel

/-- `V² − tV + q = 0`. -/
theorem endPolyEval_vOf (π : X ⟶ X) [IsMonHom π] (t q : ℤ)
    (hπ : endPolyEval π (Polynomial.X ^ 2 - C t * Polynomial.X + C q) = 1) :
    endPolyEval (vOf π t) (Polynomial.X ^ 2 - C t * Polynomial.X + C q) = 1 := by
  have h := quad_conj (postcompOf π) t q (postcompOf_quadratic π t q hπ)
  rw [← postcompOf_vOf] at h
  have h3 : aeval (postcompOf (vOf π t)) (Polynomial.X ^ 2 - C t * Polynomial.X + C q : ℤ[X]) =
      postcompOf (vOf π t) * postcompOf (vOf π t) -
        (t : postcompSubring X) * postcompOf (vOf π t) + (q : postcompSubring X) := by
    simp only [map_add, map_sub, map_mul, map_pow, aeval_X, aeval_C, algebraMap_int_eq,
      eq_intCast, map_intCast, sq]
  show postcompHom (aeval (postcompOf (vOf π t)) _) = 1
  rw [h3, h]
  rfl

/-- `R(α)` for `R = X² − tX + q`, as a homomorphism. -/
theorem endPolyEval_quadratic_eq (α : X ⟶ X) [IsMonHom α] (t q : ℤ) :
    endPolyEval α (Polynomial.X ^ 2 - C t * Polynomial.X + C q) =
      (α ≫ α) / (α ^ t) * (𝟙 X) ^ q := by
  have hsub : ∀ R S : Polynomial ℤ, endPolyEval α (R - S) = endPolyEval α R / endPolyEval α S :=
    fun R S => by
      rw [eq_div_iff_mul_eq', ← endPolyEval_add, sub_add_cancel]
  rw [endPolyEval_add, hsub, pow_two, endPolyEval_mul, endPolyEval_mul, endPolyEval_X,
    endPolyEval_C, endPolyEval_C, comp_zpow_id]

theorem comp_endPolyEval_quadratic_hom {πX : X ⟶ X} {πZ : Z ⟶ Z} [IsMonHom πX] [IsMonHom πZ]
    (t q : ℤ) (f : X ⟶ Z) [IsMonHom f] (h : f ≫ πZ = πX ≫ f) :
    f ≫ endPolyEval πZ (Polynomial.X ^ 2 - C t * Polynomial.X + C q) =
      endPolyEval πX (Polynomial.X ^ 2 - C t * Polynomial.X + C q) ≫ f := by
  simp only [endPolyEval_quadratic_eq, MonObj.comp_mul, MonObj.mul_comp, GrpObj.comp_div,
    GrpObj.div_comp, GrpObj.comp_zpow, GrpObj.zpow_comp, Category.assoc, Category.id_comp,
    Category.comp_id, reassoc_of% h, h]

/-- **The predicate on `(X, π)`**: `dim X = 1`, `π² − tπ + q = 0`, `deg π = deg (t − π) = q`. -/
structure Good (π : X ⟶ X) [IsMonHom π] (t : ℤ) (q : ℕ) : Prop where
  dim : abelianVarietyDimension X = 1
  poly : endPolyEval π (Polynomial.X ^ 2 - C t * Polynomial.X + C (q : ℤ)) = 1
  deg : homDegree π = q
  degV : homDegree (vOf π t) = q

/-- **`Good` transports along nonzero equivariant homomorphisms.** -/
theorem good_of_hom {πX : X ⟶ X} {πZ : Z ⟶ Z} [IsMonHom πX] [IsMonHom πZ] {t : ℤ} {q : ℕ}
    (hG : Good πX t q) (hZ : abelianVarietyDimension Z = 1) (f : X ⟶ Z) [IsMonHom f]
    (hf : f ≠ 1) (h : f ≫ πZ = πX ≫ f) : Good πZ t q := by
  have hX := hG.dim
  have hdf : homDegree f ≠ 0 := fun h0 => hf ((homDegree_eq_zero_iff hX hZ f).mp h0)
  refine ⟨hZ, ?_, ?_, ?_⟩
  · apply cancel_of_ne_one hX hZ f hf
    rw [comp_endPolyEval_quadratic_hom t _ f h, hG.poly, MonObj.one_comp, MonObj.comp_one]
  · have h1 := congrArg homDegree h
    rw [homDegree_comp hX hZ hZ, homDegree_comp hX hX hZ, hG.deg, mul_comm] at h1
    exact Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hdf) h1
  · have h1 := congrArg homDegree (comp_vOf t f h)
    rw [homDegree_comp hX hZ hZ, homDegree_comp hX hX hZ, hG.degV, mul_comm] at h1
    exact Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hdf) h1

/-- `#X(k)[p^b] ≤ p^b`. -/
theorem card_torsion_le (p : ℕ) [hp : Fact p.Prime] [CharP k p]
    (hX : abelianVarietyDimension X = 1) (b : ℕ) :
    Finite {z : 𝟙_ (Over (Spec (.of k))) ⟶ X // z ^ ((p ^ b : ℕ) : ℤ) = 1} ∧
      Nat.card {z : 𝟙_ (Over (Spec (.of k))) ⟶ X // z ^ ((p ^ b : ℕ) : ℤ) = 1} ≤ p ^ b := by
  obtain ⟨f, hf, hiso⟩ := exists_torsionBy_char_pow_addEquiv k X p hp.out.pos
  obtain ⟨e⟩ := hiso b
  haveI : NeZero (p ^ b) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  let ε : {z : 𝟙_ (Over (Spec (.of k))) ⟶ X // z ^ ((p ^ b : ℕ) : ℤ) = 1} ≃
      AddSubgroup.torsionBy (Additive (𝟙_ (Over (Spec (.of k))) ⟶ X)) ((p ^ b : ℕ) : ℤ) :=
    { toFun := fun z => ⟨Additive.ofMul z.1, (Submodule.mem_torsionBy_iff _ _).mpr (by
        rw [← ofMul_zpow, z.2, ofMul_one])⟩
      invFun := fun a => ⟨Additive.toMul a.1, by
        have h := (Submodule.mem_torsionBy_iff _ _).mp a.2
        rw [← toMul_zsmul, h, toMul_zero]⟩
      left_inv := fun z => rfl
      right_inv := fun a => rfl }
  let ε' := ε.trans e.toEquiv
  haveI : Finite {z : 𝟙_ (Over (Spec (.of k))) ⟶ X // z ^ ((p ^ b : ℕ) : ℤ) = 1} :=
    Finite.of_equiv _ ε'.symm
  refine ⟨inferInstance, ?_⟩
  rw [Nat.card_congr ε', Nat.card_eq_fintype_card, Fintype.card_fun, ZMod.card,
    Fintype.card_fin]
  rw [hX] at hf
  calc (p ^ b) ^ f ≤ (p ^ b) ^ 1 :=
        Nat.pow_le_pow_right (pow_pos hp.out.pos b) hf
    _ = p ^ b := pow_one _

/-- In a group, a nontrivial element killed by `p^s` has a multiple of order `p`. -/
theorem exists_pow_order_p {G : Type*} [Group G] (p : ℕ) (s : ℕ) (z : G) (hz : z ≠ 1)
    (hq : z ^ (p ^ s) = 1) : ∃ n : ℕ, z ^ n ≠ 1 ∧ (z ^ n) ^ p = 1 := by
  classical
  have hex : ∃ j, z ^ (p ^ j) = 1 := ⟨s, hq⟩
  set j := Nat.find hex with hj
  have hj0 : j ≠ 0 := by
    intro h0
    have := Nat.find_spec hex
    rw [← hj, h0, pow_zero, pow_one] at this
    exact hz this
  refine ⟨p ^ (j - 1), Nat.find_min hex (by omega), ?_⟩
  rw [← pow_mul, ← pow_succ, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hj0)]
  exact Nat.find_spec hex

set_option maxHeartbeats 800000 in
/-- **One of `π`, `t − π` is injective on `k`-points.** -/
theorem exists_phi (p : ℕ) [hp : Fact p.Prime] [CharP k p] (π : X ⟶ X) [IsMonHom π] (t : ℤ)
    (s : ℕ) (hpt : ¬ (p : ℤ) ∣ t) (hG : Good π t (p ^ s)) :
    ∃ Φ : X ⟶ X, ∃ _ : IsMonHom Φ,
      endPolyEval Φ (Polynomial.X ^ 2 - C t * Polynomial.X + C ((p ^ s : ℕ) : ℤ)) = 1 ∧
      homDegree Φ = p ^ s ∧ (∀ x : 𝟙_ (Over (Spec (.of k))) ⟶ X, x ≫ Φ = 1 → x = 1) ∧
      Φ ≫ π = π ≫ Φ := by
  classical
  by_cases hinj : ∀ x : 𝟙_ (Over (Spec (.of k))) ⟶ X, x ≫ π = 1 → x = 1
  · exact ⟨π, inferInstance, hG.poly, hG.deg, hinj, rfl⟩
  refine ⟨vOf π t, inferInstance, endPolyEval_vOf π t _ hG.poly, hG.degV, ?_,
    (comp_vOf t π rfl).symm⟩
  push Not at hinj
  obtain ⟨x, hx, hx1⟩ := hinj
  intro y hy
  by_contra hy1
  have hquad : ∀ z : 𝟙_ (Over (Spec (.of k))) ⟶ X,
      (z ≫ π ≫ π) / (z ≫ π) ^ t * z ^ ((p ^ s : ℕ) : ℤ) = 1 := fun z => by
    have h := congrArg (z ≫ ·) hG.poly
    simp only [MonObj.comp_one] at h
    rw [endPolyEval_quadratic_eq, MonObj.comp_mul, GrpObj.comp_div, GrpObj.comp_zpow,
      comp_zpow_id] at h
    rw [← Category.assoc]
    exact h
  -- `y ≫ π = y^t`
  have hyπ : y ≫ π = y ^ t := by
    have h := hy
    unfold vOf at h
    rw [MonObj.comp_mul, GrpObj.comp_zpow, comp_zpow_id, zpow_neg_one] at h
    exact inv_mul_eq_one.mp h
  -- `x, y ∈ X[q]`
  have hxq : x ^ ((p ^ s : ℕ) : ℤ) = 1 := by
    have h := hquad x
    rwa [← Category.assoc, hx, MonObj.one_comp, one_zpow, div_one,
      one_mul] at h
  have hyq : y ^ ((p ^ s : ℕ) : ℤ) = 1 := by
    have h := hquad y
    rwa [← Category.assoc, hyπ, GrpObj.zpow_comp, hyπ, div_self', one_mul] at h
  -- elements of order `p`
  obtain ⟨n, hxn, hxnp⟩ := exists_pow_order_p p s x hx1 (by exact_mod_cast hxq)
  obtain ⟨m, hym, hymp⟩ := exists_pow_order_p p s y hy1 (by exact_mod_cast hyq)
  set x' := x ^ n
  set y' := y ^ m
  have hx'π : x' ≫ π = 1 := by
    rw [show x' = x ^ (n : ℤ) by simp [x'], GrpObj.zpow_comp, hx, one_zpow]
  have hy'π : y' ≫ π = y' ^ t := by
    rw [show y' = y ^ (m : ℤ) by simp [y'], GrpObj.zpow_comp, hyπ, ← zpow_mul, ← zpow_mul,
      mul_comm]
  -- `#X[p] ≤ p` forces `y' ∈ ⟨x'⟩`
  obtain ⟨hfin, hcard⟩ := card_torsion_le p hG.dim 1
  have hy'mem : y' ∈ Subgroup.zpowers x' := by
    by_contra hnot
    have hord : orderOf x' = p := orderOf_eq_prime hxnp hxn
    set W : Set (𝟙_ (Over (Spec (.of k))) ⟶ X) := {z | z ^ ((p ^ 1 : ℕ) : ℤ) = 1}
    have hWfin : W.Finite := Set.finite_coe_iff.mp hfin
    have hsub : insert y' (Subgroup.zpowers x' : Set _) ⊆ W := by
      intro z hz
      rcases hz with rfl | ⟨j, rfl⟩
      · show y' ^ ((p ^ 1 : ℕ) : ℤ) = 1
        rw [pow_one, zpow_natCast]; exact hymp
      · show (x' ^ j) ^ ((p ^ 1 : ℕ) : ℤ) = 1
        rw [pow_one, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hxnp, one_zpow]
    have h1 := Set.ncard_le_ncard hsub hWfin
    rw [Set.ncard_insert_of_notMem hnot
      (hWfin.subset (fun z hz => hsub (Set.mem_insert_of_mem _ hz)))] at h1
    have h2 : (Subgroup.zpowers x' : Set (𝟙_ (Over (Spec (.of k))) ⟶ X)).ncard = p := by
      rw [← Nat.card_coe_set_eq, SetLike.coe_sort_coe, Nat.card_zpowers, hord]
    have h3 : W.ncard ≤ p := by
      rw [← Nat.card_coe_set_eq]
      exact hcard.trans (le_of_eq (pow_one p))
    omega
  obtain ⟨j, hj⟩ := hy'mem
  have hy't : y' ^ t = 1 := by
    rw [← hy'π, ← hj, GrpObj.zpow_comp, hx'π, one_zpow]
  have hord : orderOf y' = p := orderOf_eq_prime hymp hym
  have hdvd : (p : ℤ) ∣ t := by
    rw [← hord]
    exact orderOf_dvd_iff_zpow_eq_one.mpr hy't
  exact hpt hdvd

end Phi

end RamanujanWeil.Arith.Deuring.PLink
