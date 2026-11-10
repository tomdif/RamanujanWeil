import RamanujanWeil.Arith.DeuringG7DGeomTheta
import RamanujanWeil.Arith.DeuringG7DAlg
import Mathlib.RepresentationTheory.Invariants
import Mathlib.RingTheory.IntegralDomain
import Mathlib.LinearAlgebra.TensorProduct.Map
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# A3-ord, G7 level descent (representation theory): `h⁰(L_B) = 1` for the level subgroup

`docs/ARITH_DEURING_G7_LEVELDESCENT.md` §2. For `L ⊠ L'` on `E × E'` the global sections are
`V ⊗ V'` with `V = L(N·O) = H⁰(E, 𝒪(N·O))`, on which the theta group `𝒢(L) ×_{k^×} 𝒢(L')` acts.
Mumford descent identifies `H⁰(B, L_B)` with the invariants of the level subgroup `Γ̃`. This file
computes those invariants **exactly** (as natural numbers, in any characteristic prime to `#Γ`):

* **`finrank_eq_card_mul_finrank_invariants`** (abstract): a representation `s` of a finite abelian
  group `K` on `W`, with operators `g_y` conjugating `s` by a nondegenerate bicharacter
  `χ : K × K → k^×` (`g_y s(x) g_y⁻¹ = χ(y, x) s(x)`) and `#K` invertible, has
  `dim W = #K · dim W^K`. The proof is by isotypic projectors `P_y`, which are complete orthogonal
  idempotents permuted transitively by the `g_y`, so `W ≅ (W^K)^K` linearly.
* `thetaRep`: the theta group `𝒢(V)` of `DeuringG7DGeomTheta` acts on `V` by `v ↦ f · τ_P(v)`, the
  kernel `F^×` by scalars (`thetaRep_scalar`).
* **`finrank_rrSpace`**: `dim L(N·O) = N` for `N ≥ 1` (linear independence of `xⁱ, xʲy` from the
  `F[X]`-basis `{1, Y}` of `F[E]`).
* `levelRep`: a level structure `GraphLevel X X' u` with representations `ρ, ρ'` on which the
  kernels act by the same character gives a genuine representation `x ↦ ρ(σ x) ⊗ ρ'(σ' x)` of `K`
  on `V ⊗ V'` (the defects `c`, `−c` cancel).
* **`finrank_levelRep_invariants`**: `dim (V ⊗ V') = #K · dim (V ⊗ V')^{Γ̃}` when `X` is Heisenberg
  and the character is injective.
* **`finrank_thetaLevelRep_invariants_eq_one`**: for the theta groups of `𝒪(N·O)` on two curves and
  `#K = N²` invertible, **`dim (L(N·O) ⊗ L(N·O)')^{Γ̃} = 1`**.
-/

noncomputable section

namespace RamanujanWeil.Arith.Deuring.Geom.G7.LevelDescent

open Module

/-! ### The abstract dimension count -/

section Abstract

variable {k : Type*} [Field k] {W : Type*} [AddCommGroup W] [Module k W]
  {K : Type*} [AddCommGroup K] [Fintype K]

omit [Fintype K] in
/-- A character `K → k^×` is `1` at `0`. -/
theorem char_zero_eq_one (f : K → kˣ) (hf : ∀ x x', f (x + x') = f x * f x') : f 0 = 1 := by
  have h : f 0 * f 0 = f 0 * 1 := by rw [← hf, add_zero, mul_one]
  exact mul_left_cancel h

/-- **The sum of a nontrivial character vanishes.** -/
theorem sum_char_eq_zero (f : K → kˣ) (hf : ∀ x x', f (x + x') = f x * f x') {x₀ : K}
    (hx₀ : f x₀ ≠ 1) : ∑ x : K, (f x : k) = 0 := by
  let F : Multiplicative K →* k :=
    { toFun := fun x => (f (Multiplicative.toAdd x) : k)
      map_one' := by
        change ((f 0 : kˣ) : k) = 1
        rw [char_zero_eq_one f hf, Units.val_one]
      map_mul' := fun x y => by
        change ((f (Multiplicative.toAdd x + Multiplicative.toAdd y) : kˣ) : k) = _
        rw [hf, Units.val_mul] }
  have hF : F ≠ 1 := by
    intro h
    apply hx₀
    have := congrArg (fun φ : Multiplicative K →* k => φ (Multiplicative.ofAdd x₀)) h
    exact Units.ext this
  have := sum_hom_units_eq_zero F hF
  rw [← this]
  exact Fintype.sum_equiv Multiplicative.ofAdd _ _ (fun _ => rfl)

variable (s : Representation k (Multiplicative K) W) (χ : K → K → kˣ)

/-- **The isotypic projector** `P_y = #K⁻¹ Σₓ χ(y, x)⁻¹ s(x)`. -/
def isoProj (y : K) : Module.End k W :=
  (Fintype.card K : k)⁻¹ • ∑ x : K, (((χ y x)⁻¹ : kˣ) : k) • s (Multiplicative.ofAdd x)

theorem isoProj_def (y : K) : isoProj s χ y =
    (Fintype.card K : k)⁻¹ • ∑ x : K, (((χ y x)⁻¹ : kˣ) : k) • s (Multiplicative.ofAdd x) := rfl

variable {s χ}
variable (hχl : ∀ y y' x, χ (y + y') x = χ y x * χ y' x)
  (hχr : ∀ y x x', χ y (x + x') = χ y x * χ y x')
  (hnd₁ : ∀ y, y ≠ 0 → ∃ x, χ y x ≠ 1) (hnd₂ : ∀ x, x ≠ 0 → ∃ y, χ y x ≠ 1)

include hχr in
theorem s_mul_isoProj (x' y : K) :
    s (Multiplicative.ofAdd x') * isoProj s χ y = (χ y x' : k) • isoProj s χ y := by
  unfold isoProj
  rw [mul_smul_comm, Finset.mul_sum, smul_comm]
  congr 1
  rw [Finset.smul_sum]
  refine Fintype.sum_equiv (Equiv.addLeft x') _ _ fun x => ?_
  simp only [Equiv.coe_addLeft, mul_smul_comm, ← map_mul, ← ofAdd_add, smul_smul]
  congr 1
  rw [hχr, mul_inv, Units.val_mul, ← mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one,
    one_mul]


include hχl in
omit [Fintype K] in
theorem char_inv_mul (y y' x : K) : (χ y x)⁻¹ * χ y' x = χ (y' - y) x := by
  rw [show χ y' x = χ (y' - y) x * χ y x by rw [← hχl, sub_add_cancel], mul_comm (χ (y' - y) x),
    ← mul_assoc, inv_mul_cancel, one_mul]

include hχl in
omit [Fintype K] in
theorem char_zero_left (x : K) : χ 0 x = 1 :=
  char_zero_eq_one (fun y => χ y x) fun y y' => hχl y y' x

include hχr in
omit [Fintype K] in
theorem char_neg_right (y x : K) : χ y (-x) = (χ y x)⁻¹ := by
  rw [eq_inv_iff_mul_eq_one, mul_comm, ← hχr, add_neg_cancel]
  exact char_zero_eq_one (χ y) (hχr y)

open scoped Classical in
include hχl hχr hnd₁ in
/-- **The projectors are orthogonal idempotents.** -/
theorem isoProj_mul_isoProj (hK : (Fintype.card K : k) ≠ 0) (y y' : K) :
    isoProj s χ y * isoProj s χ y' = if y = y' then isoProj s χ y' else 0 := by
  have key : isoProj s χ y * isoProj s χ y' =
      ((Fintype.card K : k)⁻¹ * ∑ x : K, (χ (y' - y) x : k)) • isoProj s χ y' := by
    rw [isoProj_def s χ y, smul_mul_assoc, Finset.sum_mul]
    simp_rw [smul_mul_assoc, s_mul_isoProj hχr, smul_smul]
    rw [← Finset.sum_smul, smul_smul]
    congr 2
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← Units.val_mul, char_inv_mul hχl]
  rw [key]
  split_ifs with h
  · subst h
    simp_rw [sub_self, char_zero_left hχl, Units.val_one]
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, inv_mul_cancel₀ hK, one_smul]
  · obtain ⟨x₀, hx₀⟩ := hnd₁ (y' - y) (sub_ne_zero.2 (Ne.symm h))
    rw [sum_char_eq_zero (χ (y' - y)) (hχr _) hx₀, mul_zero, zero_smul]

include hχl hχr hnd₂ in
/-- **The projectors sum to the identity.** -/
theorem sum_isoProj (hK : (Fintype.card K : k) ≠ 0) : ∑ y : K, isoProj s χ y = 1 := by
  simp_rw [isoProj_def]
  rw [← Finset.smul_sum, Finset.sum_comm]
  simp_rw [← Finset.sum_smul]
  rw [Finset.sum_eq_single (0 : K)]
  · simp_rw [char_zero_eq_one (χ _) (hχr _), inv_one, Units.val_one]
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, ofAdd_zero, map_one, smul_smul,
      inv_mul_cancel₀ hK, one_smul]
  · intro x _ hx
    obtain ⟨y₀, hy₀⟩ := hnd₂ (-x) (neg_ne_zero.2 hx)
    have : ∑ y : K, (((χ y x)⁻¹ : kˣ) : k) = 0 := by
      simp_rw [← char_neg_right hχr]
      exact sum_char_eq_zero (fun y => χ y (-x)) (fun y y' => hχl y y' (-x)) hy₀
    rw [this, zero_smul]
  · intro h; exact absurd (Finset.mem_univ _) h

variable (g : K → (Module.End k W)ˣ)
  (hg : ∀ y x, (g y : Module.End k W) * s (Multiplicative.ofAdd x) =
    (χ y x : k) • (s (Multiplicative.ofAdd x) * g y))

include hχl hg in
/-- **The conjugating operators permute the projectors.** -/
theorem g_mul_isoProj (y z : K) :
    (g y : Module.End k W) * isoProj s χ z = isoProj s χ (z - y) * g y := by
  simp_rw [isoProj_def]
  rw [mul_smul_comm, smul_mul_assoc, Finset.mul_sum, Finset.sum_mul]
  congr 1
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [mul_smul_comm, hg, smul_smul, smul_mul_assoc]
  congr 1
  have : χ z x = χ (z - y) x * χ y x := by rw [← hχl, sub_add_cancel]
  rw [this, mul_inv, Units.val_mul, mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one,
    mul_one]

include hχl hχr in
theorem isoProj_zero_mem_invariants (w : W) : isoProj s χ 0 w ∈ s.invariants := by
  intro x
  have h := s_mul_isoProj (s := s) (χ := χ) hχr (Multiplicative.toAdd x) 0
  rw [ofAdd_toAdd, char_zero_left hχl, Units.val_one, one_smul] at h
  exact congrArg (fun φ : Module.End k W => φ w) h

include hχl in
theorem isoProj_zero_of_mem_invariants (hK : (Fintype.card K : k) ≠ 0) {v : W}
    (hv : v ∈ s.invariants) : isoProj s χ 0 v = v := by
  rw [isoProj_def]
  simp_rw [char_zero_left hχl, inv_one, Units.val_one, one_smul]
  rw [LinearMap.smul_apply, LinearMap.sum_apply,
    Finset.sum_congr rfl fun x _ => hv (Multiplicative.ofAdd x)]
  rw [Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul k, smul_smul,
    inv_mul_cancel₀ hK, one_smul]

include hχl hχr in
theorem range_isoProj_zero (hK : (Fintype.card K : k) ≠ 0) :
    LinearMap.range (isoProj s χ 0) = s.invariants := by
  ext v
  constructor
  · rintro ⟨w, rfl⟩
    exact isoProj_zero_mem_invariants hχl hχr w
  · intro hv
    exact ⟨v, isoProj_zero_of_mem_invariants hχl hK hv⟩

include hχl hχr hnd₁ hnd₂ hg in
/-- **`W ≅ (W^K)^K`**: the conjugating operators identify every isotypic piece with the
invariants. -/
theorem nonempty_linearEquiv_pi (hK : (Fintype.card K : k) ≠ 0) :
    Nonempty (W ≃ₗ[k] (K → LinearMap.range (isoProj s χ 0))) := by
  classical
  set P := isoProj s χ with hP
  have hgP : ∀ y, (g y : Module.End k W) * P y = P 0 * g y := fun y => by
    rw [g_mul_isoProj hχl g hg, sub_self]
  have hgP' : ∀ y, ((g y)⁻¹ : (Module.End k W)ˣ) * P 0 = P y * ((g y)⁻¹ : (Module.End k W)ˣ) :=
    fun y => by
      have h := congrArg (fun φ => (((g y)⁻¹ : (Module.End k W)ˣ) : Module.End k W) * φ *
        (((g y)⁻¹ : (Module.End k W)ˣ) : Module.End k W)) (hgP y)
      rw [← mul_assoc, Units.inv_mul, one_mul, mul_assoc, mul_assoc, Units.mul_inv, mul_one] at h
      exact h.symm
  have hPP : ∀ y y', P y * P y' = if y = y' then P y' else 0 :=
    isoProj_mul_isoProj hχl hχr hnd₁ hK
  have hP00 : P 0 * P 0 = P 0 := by rw [hPP]; simp
  let F : W →ₗ[k] (K → LinearMap.range (P 0)) := LinearMap.pi fun y =>
    LinearMap.codRestrict (LinearMap.range (P 0)) ((g y : Module.End k W) * P y) fun w =>
      ⟨(g y : Module.End k W) w, by rw [← Module.End.mul_apply, ← hgP]⟩
  let G : (K → LinearMap.range (P 0)) →ₗ[k] W := ∑ y : K,
    (((g y)⁻¹ : (Module.End k W)ˣ) : Module.End k W) ∘ₗ (LinearMap.range (P 0)).subtype ∘ₗ
      LinearMap.proj y
  have hcomm : ∀ y v, P y ((((g y)⁻¹ : (Module.End k W)ˣ) : Module.End k W) v) =
      (((g y)⁻¹ : (Module.End k W)ˣ) : Module.End k W) (P 0 v) := fun y v => by
    have := congrArg (fun φ : Module.End k W => φ v) (hgP' y)
    simp only [Module.End.mul_apply] at this
    exact this.symm
  have hPP' : ∀ y y' v, P y (P y' v) = if y = y' then P y' v else 0 := fun y y' v => by
    have := congrArg (fun φ : Module.End k W => φ v) (hPP y y')
    simp only [Module.End.mul_apply] at this
    rw [this]; split_ifs <;> rfl
  refine ⟨LinearEquiv.ofLinearMap F G ?_ ?_⟩
  · refine LinearMap.ext fun f => funext fun z => Subtype.ext ?_
    have hf : ∀ y, ((f y : LinearMap.range (P 0)) : W) = P 0 (f y) := fun y => by
      obtain ⟨w, hw⟩ := (f y).2
      rw [← hw, ← Module.End.mul_apply, hP00]
    have h1 : ∀ y, P z ((((g y)⁻¹ : (Module.End k W)ˣ) : Module.End k W) (f y)) =
        if z = y then (((g y)⁻¹ : (Module.End k W)ˣ) : Module.End k W) (f y) else 0 :=
      fun y => by
        rw [hf y, ← hcomm, hPP']
    change (g z : Module.End k W) (P z (G f)) = (f z : W)
    have hG : G f = ∑ y, (((g y)⁻¹ : (Module.End k W)ˣ) : Module.End k W) (f y) := by
      simp [G, LinearMap.sum_apply]
    rw [hG, map_sum]
    simp_rw [h1]
    rw [Finset.sum_ite_eq, ite_eq_left_iff.2 (fun h => absurd (Finset.mem_univ _) h), ← Module.End.mul_apply, Units.mul_inv,
      Module.End.one_apply]
  · refine LinearMap.ext fun w => ?_
    change G (F w) = w
    have hG : G (F w) = ∑ y, (((g y)⁻¹ : (Module.End k W)ˣ) : Module.End k W)
        ((g y : Module.End k W) (P y w)) := by
      simp only [G, LinearMap.sum_apply]; rfl
    rw [hG]
    have : ∀ y, (((g y)⁻¹ : (Module.End k W)ˣ) : Module.End k W)
        ((g y : Module.End k W) (P y w)) = P y w := fun y => by
      rw [← Module.End.mul_apply, Units.inv_mul, Module.End.one_apply]
    simp_rw [this]
    rw [← LinearMap.sum_apply, sum_isoProj hχl hχr hnd₂ hK, Module.End.one_apply]

include hχl hχr hnd₁ hnd₂ hg in
/-- **The dimension count** `dim W = #K · dim W^K`. -/
theorem finrank_eq_card_mul_finrank_invariants [FiniteDimensional k W]
    (hK : (Fintype.card K : k) ≠ 0) :
    finrank k W = Fintype.card K * finrank k s.invariants := by
  obtain ⟨e⟩ := nonempty_linearEquiv_pi hχl hχr hnd₁ hnd₂ g hg hK
  rw [e.finrank_eq, Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ, smul_eq_mul,
    (LinearEquiv.ofEq _ _ (range_isoProj_zero hχl hχr hK)).finrank_eq]

end Abstract

end RamanujanWeil.Arith.Deuring.Geom.G7.LevelDescent

namespace RamanujanWeil.Arith.Deuring.Geom.G7.LevelDescent

open Module

/-! ### The level representation on `V ⊗ V'` -/

section Level

open RamanujanWeil.Arith.Deuring.Geom.G7.Fin.Weil TensorProduct

variable {k : Type*} [Field k] {G G' K K' A : Type*} [Group G] [Group G'] [AddCommGroup K]
  [AddCommGroup K'] [AddCommGroup A] {X : CentralExt G K A} {X' : CentralExt G' K' A}
  {V V' : Type*} [AddCommGroup V] [Module k V] [AddCommGroup V'] [Module k V']
  (ρ : G →* Module.End k V) (ρ' : G' →* Module.End k V') (χ : Multiplicative A →* kˣ)
  {u : K ≃+ K'} (L : CentralExt.GraphLevel X X' u)

variable {ρ ρ' χ} (hρ : ∀ a, ρ (X.ι a) = (χ a : k) • 1) (hρ' : ∀ a, ρ' (X'.ι a) = (χ a : k) • 1)

include hρ hρ' in
theorem levelMap_add (x y : K) :
    TensorProduct.map (ρ (L.σ x)) (ρ' (L.σ' x)) * TensorProduct.map (ρ (L.σ y)) (ρ' (L.σ' y)) =
      TensorProduct.map (ρ (L.σ (x + y))) (ρ' (L.σ' (x + y))) := by
  rw [← TensorProduct.map_mul, ← map_mul, ← map_mul, L.hc, L.hc', map_mul, map_mul, hρ, hρ',
    mul_smul_comm, mul_smul_comm, mul_one, mul_one, TensorProduct.map_smul_left,
    TensorProduct.map_smul_right, smul_smul, ← Units.val_mul, ← map_mul, ← ofAdd_add,
    add_neg_cancel, ofAdd_zero, map_one, Units.val_one, one_smul]

include hρ hρ' in
theorem levelMap_zero :
    TensorProduct.map (ρ (L.σ 0)) (ρ' (L.σ' 0)) = 1 := by
  have h0 : L.σ 0 = X.ι (Multiplicative.ofAdd (L.c 0 0)) := by
    have := L.hc 0 0
    rw [add_zero] at this
    exact mul_left_cancel this
  have h0' : L.σ' 0 = X'.ι (Multiplicative.ofAdd (-L.c 0 0)) := by
    have := L.hc' 0 0
    rw [add_zero] at this
    exact mul_left_cancel this
  rw [h0, h0', hρ, hρ', TensorProduct.map_smul_left, TensorProduct.map_smul_right, smul_smul,
    ← Units.val_mul, ← map_mul, ← ofAdd_add, add_neg_cancel, ofAdd_zero, map_one, Units.val_one,
    one_smul, TensorProduct.map_one]

/-- **The level representation** `x ↦ ρ(σ x) ⊗ ρ'(σ' x)` of `K` on `V ⊗ V'`: the action of the
level subgroup `Γ̃ ⊆ G ×_A G'` on the sections of `L ⊠ L'`. The opposite defects cancel. -/
def levelRep : Representation k (Multiplicative K) (V ⊗[k] V') where
  toFun x := TensorProduct.map (ρ (L.σ (Multiplicative.toAdd x)))
    (ρ' (L.σ' (Multiplicative.toAdd x)))
  map_one' := levelMap_zero L hρ hρ'
  map_mul' _ _ := (levelMap_add L hρ hρ' _ _).symm

theorem levelRep_apply (x : K) : levelRep L hρ hρ' (Multiplicative.ofAdd x) =
    TensorProduct.map (ρ (L.σ x)) (ρ' (L.σ' x)) := rfl

variable (ρ) in
/-- The operator `ρ(g) ⊗ 1`, a unit. -/
def leftUnit (g : G) : (Module.End k (V ⊗[k] V'))ˣ where
  val := TensorProduct.map (ρ g) 1
  inv := TensorProduct.map (ρ g⁻¹) 1
  val_inv := by
    rw [← TensorProduct.map_mul, ← map_mul, mul_inv_cancel, map_one, mul_one,
      TensorProduct.map_one]
  inv_val := by
    rw [← TensorProduct.map_mul, ← map_mul, inv_mul_cancel, map_one, mul_one,
      TensorProduct.map_one]

/-- The bicharacter `χ(e(y, x))`. -/
def levelChar (χ : Multiplicative A →* kˣ) (X : CentralExt G K A) (y x : K) : kˣ :=
  χ (Multiplicative.ofAdd (X.pairing y x))

include hρ in
theorem leftUnit_mul_levelRep (y x : K) :
    ((leftUnit (V' := V') ρ (X.lift y) : (Module.End k (V ⊗[k] V'))ˣ) :
        Module.End k (V ⊗[k] V')) * levelRep L hρ hρ' (Multiplicative.ofAdd x) =
      (levelChar χ X y x : k) •
        (levelRep L hρ hρ' (Multiplicative.ofAdd x) * (leftUnit (V' := V') ρ (X.lift y) :
          Module.End k (V ⊗[k] V'))) := by
  have hcomm : X.lift y * L.σ x =
      X.ι (Multiplicative.ofAdd (X.pairing y x)) * L.σ x * X.lift y := by
    have h := X.pairing_eq (X.lift y) (L.σ x)
    rw [X.p_lift, L.hσ, toAdd_ofAdd, toAdd_ofAdd] at h
    rw [h, X.ι_commVal]
    simp only [CentralExt.comm]
    group
  change TensorProduct.map (ρ (X.lift y)) 1 * TensorProduct.map (ρ (L.σ x)) (ρ' (L.σ' x)) =
    (levelChar χ X y x : k) • (TensorProduct.map (ρ (L.σ x)) (ρ' (L.σ' x)) *
      TensorProduct.map (ρ (X.lift y)) 1)
  rw [← TensorProduct.map_mul, ← TensorProduct.map_mul, ← map_mul, hcomm, map_mul, map_mul, hρ]
  simp only [smul_mul_assoc, one_mul, mul_one]
  rw [TensorProduct.map_smul_left]
  rfl

variable (χ) in
include hρ hρ' in
/-- **`dim (V ⊗ V') = #K · dim (V ⊗ V')^{Γ̃}`** for a Heisenberg `X` and an injective character. -/
theorem finrank_levelRep_invariants [Fintype K] [FiniteDimensional k V] [FiniteDimensional k V']
    (hK : (Fintype.card K : k) ≠ 0) (hZ : ∀ g : G, (∀ h, g * h = h * g) → X.p g = 1)
    (hχ : Function.Injective χ) :
    finrank k V * finrank k V' =
      Fintype.card K * finrank k (levelRep L hρ hρ').invariants := by
  rw [← Module.finrank_tensorProduct]
  have hsk : ∀ x y, X.pairing y x = -X.pairing x y := fun x y => by
    rw [CentralExt.pairing_apply, CentralExt.pairing_apply, CentralExt.commVal_swap]
  have hχ1 : ∀ a : A, χ (Multiplicative.ofAdd a) = 1 → a = 0 := fun a ha => by
    rw [← map_one χ] at ha
    exact Multiplicative.ofAdd.injective (hχ ha)
  refine finrank_eq_card_mul_finrank_invariants (s := levelRep L hρ hρ') (χ := levelChar χ X)
    ?_ ?_ ?_ ?_ (fun y => leftUnit ρ (X.lift y)) (leftUnit_mul_levelRep L hρ hρ') hK
  · intro y y' x
    simp only [levelChar, map_add, AddMonoidHom.add_apply, ofAdd_add, map_mul]
  · intro y x x'
    simp only [levelChar, map_add, ofAdd_add, map_mul]
  · intro y hy
    by_contra h
    simp only [not_exists, not_not] at h
    exact hy (X.pairing_nondeg hZ y fun x => hχ1 _ (h x))
  · intro x hx
    by_contra h
    simp only [not_exists, not_not] at h
    refine hx (X.pairing_nondeg hZ x fun y => ?_)
    have := hχ1 _ (h y)
    rw [hsk] at this
    exact neg_eq_zero.1 this

end Level

end RamanujanWeil.Arith.Deuring.Geom.G7.LevelDescent

namespace RamanujanWeil.Arith.Deuring.Geom.G7.LevelDescent

open Module

/-! ### The theta group acting on `L(N·O)` -/

section Theta

open WeierstrassCurve WeierstrassCurve.Affine Polynomial RamanujanWeil.Arith.Deuring.Geom.G7.DGeom
open scoped Polynomial.Bivariate

universe u

variable {F : Type u} [Field F] (W : Affine F) [W.IsElliptic] [DecidableEq F]
  (V : Submodule F (Kf W))

theorem thetaAct_mem (g : thetaGroup W V) {v : Kf W} (hv : v ∈ V) :
    thetaAct W (g : Amb W) v ∈ V := by
  have h : V.map (thetaAct W (g : Amb W)) = V := g.2
  have := Submodule.mem_map_of_mem (f := thetaAct W (g : Amb W)) hv
  rwa [h] at this

/-- **The theta group acts on `V = H⁰(E, L)`**: `(f, P) · v = f · τ_P(v)`. -/
def thetaRep : thetaGroup W V →* Module.End F V where
  toFun g := (thetaAct W (g : Amb W)).restrict fun _ hv => thetaAct_mem W V g hv
  map_one' := by
    ext v
    change thetaAct W 1 v = v
    rw [thetaAct_one]; rfl
  map_mul' g h := by
    ext v
    change thetaAct W ((g : Amb W) * h) v = thetaAct W g (thetaAct W h v)
    rw [thetaAct_mul]; rfl

theorem thetaRep_apply (g : thetaGroup W V) (v : V) :
    ((thetaRep W V g v : V) : Kf W) = thetaAct W (g : Amb W) v := rfl

/-- **The kernel `F^×` acts by scalars.** -/
theorem thetaRep_scalar [IsAlgClosed F] [FiniteDimensional F V] (c : Fˣ) : thetaRep W V (thetaScalar W V c) = (c : F) • 1 := by
  ext v
  change thetaAct W (thetaScalar W V c : Amb W) v = (c : F) • (v : Kf W)
  rw [thetaAct_apply, thetaScalar_left, thetaScalar_right, toAdd_one, trans_zero,
    Algebra.smul_def]
  rfl

/-! ### `dim L(N·O) = N` -/

/-- The basis family of `L(N·O)`: `xⁱ` (`i ≤ N/2`) and `xʲy` (`j < (N − 1)/2`). -/
def rrFam (N : ℕ) : Fin (N / 2 + 1) ⊕ Fin ((N - 1) / 2) → Kf W
  | .inl i => genX W ^ (i : ℕ)
  | .inr j => genX W ^ (j : ℕ) * genY W

omit [W.IsElliptic] [DecidableEq F] in
theorem range_rrFam (N : ℕ) : Set.range (rrFam W N) = rrGens W N := by
  ext f
  constructor
  · rintro ⟨i | j, rfl⟩
    · exact Or.inl ⟨i, by have := i.2; simp only [Set.mem_ofPred_eq]; omega, rfl⟩
    · exact Or.inr ⟨j, by have := j.2; simp only [Set.mem_ofPred_eq]; omega, rfl⟩
  · rintro (⟨i, hi, rfl⟩ | ⟨j, hj, rfl⟩)
    · exact ⟨.inl ⟨i, by simp only [Set.mem_ofPred_eq] at hi; omega⟩, rfl⟩
    · exact ⟨.inr ⟨j, by simp only [Set.mem_ofPred_eq] at hj; omega⟩, rfl⟩

theorem algebraMap_smul_basis (p q : F[X]) :
    algebraMap (Rg W) (Kf W) (p • (1 : Rg W) + q • Affine.CoordinateRing.mk (W⁄F) Y) =
      Polynomial.aeval (genX W) p + Polynomial.aeval (genX W) q * genY W := by
  rw [aeval_genX, aeval_genX, Algebra.smul_def, Algebra.smul_def, mul_one, map_add, map_mul,
    show Affine.CoordinateRing.mk (W⁄F) Y = yR W from AdjoinRoot.mk_X]
  rfl

theorem linearIndependent_rrFam (N : ℕ) : LinearIndependent F (rrFam W N) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc
  set p : F[X] := ∑ i : Fin (N / 2 + 1), Polynomial.C (c (.inl i)) * X ^ (i : ℕ) with hp
  set q : F[X] := ∑ j : Fin ((N - 1) / 2), Polynomial.C (c (.inr j)) * X ^ (j : ℕ) with hq
  have hpq : p • (1 : Rg W) + q • Affine.CoordinateRing.mk (W⁄F) Y = 0 := by
    apply IsFractionRing.injective (Rg W) (Kf W)
    rw [map_zero, algebraMap_smul_basis, ← hc, Fintype.sum_sum_type]
    congr 1
    · rw [hp, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_mul, Polynomial.aeval_C, Polynomial.aeval_X_pow, Algebra.smul_def]
      rfl
    · rw [hq, map_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_mul, Polynomial.aeval_C, Polynomial.aeval_X_pow, Algebra.smul_def, mul_assoc]
      rfl
  obtain ⟨hp0, hq0⟩ := Affine.CoordinateRing.smul_basis_eq_zero hpq
  rintro (i | j)
  · have := congrArg (fun r : F[X] => r.coeff i) hp0
    simpa [hp, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow, Fin.val_inj] using this
  · have := congrArg (fun r : F[X] => r.coeff j) hq0
    simpa [hq, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow, Fin.val_inj] using this

/-- **`h⁰(𝒪(N·O)) = N`** for `N ≥ 1` (Riemann–Roch on an elliptic curve, from the explicit basis). -/
theorem finrank_rrSpace {N : ℕ} (hN : 1 ≤ N) : finrank F (rrSpace W N) = N := by
  rw [rrSpace, ← range_rrFam, finrank_span_eq_card (linearIndependent_rrFam W N),
    Fintype.card_sum, Fintype.card_fin, Fintype.card_fin]
  omega

end Theta

end RamanujanWeil.Arith.Deuring.Geom.G7.LevelDescent

namespace RamanujanWeil.Arith.Deuring.Geom.G7.LevelDescent

open Module

/-! ### `h⁰ = 1` for the theta groups of `𝒪(N·O)` -/

section ThetaLevel

open WeierstrassCurve WeierstrassCurve.Affine RamanujanWeil.Arith.Deuring.Geom.G7.DGeom
  RamanujanWeil.Arith.Deuring.Geom.G7.Fin.Weil TensorProduct

universe u

variable {F : Type u} [Field F] [IsAlgClosed F] [DecidableEq F]

/-- The tautological character `F^× → F^×` of the kernel `Additive F^×`. -/
def unitsChar (F : Type u) [Field F] : Multiplicative (Additive Fˣ) →* Fˣ where
  toFun a := Additive.toMul (Multiplicative.toAdd a)
  map_one' := rfl
  map_mul' _ _ := rfl

omit [IsAlgClosed F] [DecidableEq F] in
theorem unitsChar_injective : Function.Injective (unitsChar F) := fun _ _ h => h

variable (W W' : Affine F) [W.IsElliptic] [W'.IsElliptic] (N : ℕ)
  {K K' : Type*} [AddCommGroup K] [AddCommGroup K']
  {X : CentralExt (thetaGroup W (rrSpace W N)) K (Additive Fˣ)}
  {X' : CentralExt (thetaGroup W' (rrSpace W' N)) K' (Additive Fˣ)}

/-- An extension whose kernel is the scalar subgroup of `𝒢(L(N·O))` (true of `thetaExtN` and of
its transports). -/
def IsScalarKernel (X : CentralExt (thetaGroup W (rrSpace W N)) K (Additive Fˣ)) : Prop :=
  ∀ a, X.ι a = thetaScalar W (rrSpace W N) (Additive.toMul (Multiplicative.toAdd a))

variable {W W' N}

theorem thetaRep_ι (hX : IsScalarKernel W N X) (a : Multiplicative (Additive Fˣ)) :
    thetaRep W (rrSpace W N) (X.ι a) = (unitsChar F a : F) • 1 := by
  rw [hX, thetaRep_scalar]; rfl

variable {u : K ≃+ K'}

/-- **The level representation on `L(N·O) ⊗ L(N·O)'`**, the sections of `L ⊠ L'`. -/
def thetaLevelRep (hX : IsScalarKernel W N X) (hX' : IsScalarKernel W' N X')
    (L : CentralExt.GraphLevel X X' u) :=
  levelRep (ρ := thetaRep W (rrSpace W N)) (ρ' := thetaRep W' (rrSpace W' N))
    (χ := unitsChar F) L (thetaRep_ι hX) (thetaRep_ι hX')

/-- **The level invariants** `(L(N·O) ⊗ L(N·O)')^{Γ̃}`: by Mumford descent, `H⁰(B, L_B)`. -/
abbrev thetaLevelInv (hX : IsScalarKernel W N X) (hX' : IsScalarKernel W' N X')
    (L : CentralExt.GraphLevel X X' u) : Submodule F (rrSpace W N ⊗[F] rrSpace W' N) :=
  Representation.invariants (k := F) (G := Multiplicative K)
    (V := rrSpace W N ⊗[F] rrSpace W' N) (thetaLevelRep hX hX' L)

/-- **`h⁰(L_B) = 1`, algebraically.** For the theta groups of `𝒪(N·O)` on two elliptic curves,
`#K = N²` invertible in `F` and `X` Heisenberg, the level subgroup over a graph has a
**one-dimensional** space of invariants in `L(N·O) ⊗ L(N·O)'`. -/
theorem finrank_thetaLevelRep_invariants_eq_one [Fintype K] (hN : 1 ≤ N)
    (hX : IsScalarKernel W N X) (hX' : IsScalarKernel W' N X')
    (L : CentralExt.GraphLevel X X' u) (hcard : Fintype.card K = N ^ 2) (hNF : (N : F) ≠ 0)
    (hZ : ∀ g : thetaGroup W (rrSpace W N), (∀ h, g * h = h * g) → X.p g = 1) :
    finrank F (thetaLevelInv hX hX' L) = 1 := by
  have hK : (Fintype.card K : F) ≠ 0 := by
    rw [hcard, Nat.cast_pow]; exact pow_ne_zero _ hNF
  have h := finrank_levelRep_invariants (ρ := thetaRep W (rrSpace W N))
    (ρ' := thetaRep W' (rrSpace W' N)) (unitsChar F) L (thetaRep_ι hX) (thetaRep_ι hX') hK hZ
    unitsChar_injective
  rw [finrank_rrSpace W hN, finrank_rrSpace W' hN, hcard] at h
  have hpos : 0 < N ^ 2 := pow_pos hN 2
  have : N ^ 2 * 1 = N ^ 2 * finrank F (thetaLevelInv hX hX' L) := by
    rw [mul_one]; rw [sq] at h ⊢; exact h
  exact (Nat.eq_of_mul_eq_mul_left hpos this).symm

end ThetaLevel

end RamanujanWeil.Arith.Deuring.Geom.G7.LevelDescent
