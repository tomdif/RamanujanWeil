import RamanujanWeil.Arith.DeuringG7WeilAlg
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.Tactic.Group

/-!
# A3-ord, G7-W (construction): the commutator pairing of a central extension

`docs/ARITH_DEURING_G7_WC.md`, step **W**. The Weil pairing that the polarization route consumes
is the pairing of Mumford's descent criterion (Mumford, *Abelian varieties*, §23): the
**commutator pairing of the theta group** `𝒢(L)` of `L = 𝒪(N[0])` on an elliptic curve, a central
extension `1 → k̄^× → 𝒢(L) → E[N] → 0`. This file builds that pairing from the bare central
extension, as pure group theory, and lands it in the format of `DeuringG7WeilAlg`
(`ℤ/N`-valued, alternating, nondegenerate):

* `CentralExt G K A`: a central extension `0 → A → G → K → 0` (`A`, `K` additive, `G` a group).
* `CentralExt.commVal`: the commutator `g h g⁻¹ h⁻¹ ∈ A`; `commVal_mul_central_left/right`: it
  only depends on the images in `K`.
* **`CentralExt.pairing`**: `K →+ K →+ A`, bi-additive.
* **`CentralExt.pairing_self`** (alternating) and **`CentralExt.pairing_nondeg`**: nondegenerate
  when the center of `G` is exactly `A` (the Heisenberg property).
* **`CentralExt.zmodPairing`**: for `K` killed by `N` and an injective `χ : A[N] →+ ℤ/N`, an
  alternating nondegenerate `ℤ/N`-valued pairing (`IsAlt`, `IsNondeg`).
* `exists_injective_torsion_units_zmod`: such a `χ` on `(k^×)[N]`, from a primitive `N`-th root of
  unity. One `χ` for the common field `k̄` serves both curves `E`, `E'`, which is what makes the
  ratio `s/s'` meaningful.

What is *not* here (it is step D's theta group): the construction of `𝒢(𝒪(N[0]))` itself, i.e.
of the extension `1 → k̄^× → 𝒢 → E[N] → 0` and of the Heisenberg property `Z(𝒢) = k̄^×`.
-/

namespace RamanujanWeil.Arith.Deuring.Geom.G7.Fin.Weil

/-- A central extension `0 → A → G → K → 0`. -/
structure CentralExt (G K A : Type*) [Group G] [AddCommGroup K] [AddCommGroup A] where
  /-- The projection. -/
  p : G →* Multiplicative K
  surj : Function.Surjective p
  /-- The inclusion of the kernel. -/
  ι : Multiplicative A →* G
  inj : Function.Injective ι
  exact : ∀ g, p g = 1 ↔ ∃ a, ι a = g
  central : ∀ a g, ι a * g = g * ι a

namespace CentralExt

variable {G K A : Type*} [Group G] [AddCommGroup K] [AddCommGroup A] (X : CentralExt G K A)

/-- The group commutator. -/
def comm (g h : G) : G := g * h * g⁻¹ * h⁻¹

theorem p_comm (g h : G) : X.p (comm g h) = 1 := by
  simp only [comm, map_mul, map_inv]
  rw [mul_comm (X.p g) (X.p h)]
  group

theorem exists_comm (g h : G) : ∃ a, X.ι a = comm g h := (X.exact _).1 (X.p_comm g h)

/-- The commutator as an element of `A`. -/
noncomputable def commVal (g h : G) : A := Multiplicative.toAdd (X.exists_comm g h).choose

theorem ι_commVal (g h : G) : X.ι (Multiplicative.ofAdd (X.commVal g h)) = comm g h :=
  (X.exists_comm g h).choose_spec

theorem commVal_eq_iff (g h : G) (a : A) :
    X.commVal g h = a ↔ X.ι (Multiplicative.ofAdd a) = comm g h := by
  constructor
  · rintro rfl; exact X.ι_commVal g h
  · intro ha
    apply Multiplicative.ofAdd.injective
    apply X.inj
    rw [ha, X.ι_commVal]

theorem central' (a : Multiplicative A) (g : G) : g * X.ι a = X.ι a * g := (X.central a g).symm

theorem commVal_mul_central_left (g h : G) (a : Multiplicative A) :
    X.commVal (g * X.ι a) h = X.commVal g h := by
  rw [X.commVal_eq_iff, X.ι_commVal]
  have hz := X.central a h
  calc comm g h = g * (X.ι a * h) * (X.ι a)⁻¹ * g⁻¹ * h⁻¹ := by
        rw [hz]; simp only [comm]; group
    _ = comm (g * X.ι a) h := by simp only [comm]; group

theorem commVal_mul_central_right (g h : G) (a : Multiplicative A) :
    X.commVal g (h * X.ι a) = X.commVal g h := by
  rw [X.commVal_eq_iff, X.ι_commVal]
  have hz := X.central a g⁻¹
  calc comm g h = g * h * (X.ι a * g⁻¹) * (X.ι a)⁻¹ * h⁻¹ := by
        rw [hz]; simp only [comm]; group
    _ = comm g (h * X.ι a) := by simp only [comm]; group

/-- The commutator only depends on the images in `K`. -/
theorem commVal_congr {g g' h h' : G} (hg : X.p g = X.p g') (hh : X.p h = X.p h') :
    X.commVal g h = X.commVal g' h' := by
  obtain ⟨a, ha⟩ := (X.exact (g⁻¹ * g')).1 (by rw [map_mul, map_inv, hg, inv_mul_cancel])
  obtain ⟨b, hb⟩ := (X.exact (h⁻¹ * h')).1 (by rw [map_mul, map_inv, hh, inv_mul_cancel])
  have hg' : g' = g * X.ι a := by rw [ha]; group
  have hh' : h' = h * X.ι b := by rw [hb]; group
  rw [hg', hh', X.commVal_mul_central_left, X.commVal_mul_central_right]

theorem commVal_mul_left (g g' h : G) :
    X.commVal (g * g') h = X.commVal g' h + X.commVal g h := by
  rw [X.commVal_eq_iff, ofAdd_add, map_mul, X.ι_commVal, X.ι_commVal]
  have hw := X.central (Multiplicative.ofAdd (X.commVal g' h)) g
  rw [X.ι_commVal] at hw
  calc comm g' h * comm g h = g * comm g' h * h * g⁻¹ * h⁻¹ := by
        rw [← hw]; simp only [comm]; group
    _ = comm (g * g') h := by simp only [comm]; group

theorem commVal_swap (g h : G) : X.commVal h g = -X.commVal g h := by
  rw [X.commVal_eq_iff, ofAdd_neg, map_inv, X.ι_commVal]
  simp only [comm]; group

theorem commVal_self (g : G) : X.commVal g g = 0 := by
  rw [X.commVal_eq_iff, ofAdd_zero, map_one]
  simp only [comm]; group

/-- A lift of `x ∈ K` to `G`. -/
noncomputable def lift (x : K) : G := Function.surjInv X.surj (Multiplicative.ofAdd x)

theorem p_lift (x : K) : X.p (X.lift x) = Multiplicative.ofAdd x :=
  Function.surjInv_eq X.surj _

/-- **The commutator pairing** `K →+ K →+ A`. -/
noncomputable def pairing : K →+ K →+ A :=
  AddMonoidHom.mk'
    (fun x => AddMonoidHom.mk' (fun y => X.commVal (X.lift x) (X.lift y)) fun y y' => by
      rw [X.commVal_swap (X.lift (y + y')) (X.lift x),
        X.commVal_congr (g' := X.lift y * X.lift y') (h' := X.lift x) (by
          rw [map_mul, X.p_lift, X.p_lift, X.p_lift, ofAdd_add]) rfl,
        X.commVal_mul_left, X.commVal_swap (X.lift y) (X.lift x),
        X.commVal_swap (X.lift y') (X.lift x)]
      abel)
    fun x x' => by
      ext y
      simp only [AddMonoidHom.mk'_apply, AddMonoidHom.add_apply]
      rw [X.commVal_congr (g' := X.lift x * X.lift x') (hh := rfl) (by
          rw [map_mul, X.p_lift, X.p_lift, X.p_lift, ofAdd_add]),
        X.commVal_mul_left, add_comm]

theorem pairing_apply (x y : K) : X.pairing x y = X.commVal (X.lift x) (X.lift y) := rfl

/-- The pairing evaluated at arbitrary lifts. -/
theorem pairing_eq (g h : G) :
    X.pairing (Multiplicative.toAdd (X.p g)) (Multiplicative.toAdd (X.p h)) = X.commVal g h :=
  X.commVal_congr (by rw [p_lift]; rfl) (by rw [p_lift]; rfl)

/-- **The commutator pairing is alternating.** -/
theorem pairing_self (x : K) : X.pairing x x = 0 := X.commVal_self _

/-- **The commutator pairing is nondegenerate for a Heisenberg group** (center = `A`). -/
theorem pairing_nondeg (hZ : ∀ g : G, (∀ h, g * h = h * g) → X.p g = 1) (x : K)
    (hx : ∀ y, X.pairing x y = 0) : x = 0 := by
  have hc : ∀ h : G, X.lift x * h = h * X.lift x := by
    intro h
    have h0 := hx (Multiplicative.toAdd (X.p h))
    rw [show x = Multiplicative.toAdd (X.p (X.lift x)) by rw [p_lift]; rfl, X.pairing_eq,
      X.commVal_eq_iff, ofAdd_zero, map_one] at h0
    simp only [comm] at h0
    have := congrArg (· * h * X.lift x) h0.symm
    simpa [mul_assoc] using this
  have := hZ _ hc
  rw [p_lift] at this
  exact Multiplicative.ofAdd.injective this

theorem pairing_mem_torsion {N : ℕ} (hK : ∀ x : K, N • x = 0) (x y : K) :
    X.pairing x y ∈ AddSubgroup.torsionBy A (N : ℤ) := by
  change ((N : ℕ) : ℤ) • X.pairing x y = 0
  rw [natCast_zsmul, ← AddMonoidHom.nsmul_apply, ← map_nsmul, hK x, map_zero,
    AddMonoidHom.zero_apply]

/-- **The `ℤ/N`-valued commutator pairing**: for `K` killed by `N` and `χ : A[N] ↪ ℤ/N`. -/
noncomputable def zmodPairing {N : ℕ} (hK : ∀ x : K, N • x = 0)
    (χ : AddSubgroup.torsionBy A (N : ℤ) →+ ZMod N) : K →+ K →+ ZMod N :=
  AddMonoidHom.mk'
    (fun x => AddMonoidHom.mk'
      (fun y => χ ⟨X.pairing x y, X.pairing_mem_torsion hK x y⟩)
      fun y y' => by rw [← map_add]; congr 1; ext; simp)
    fun x x' => by ext y; simp only [AddMonoidHom.mk'_apply, AddMonoidHom.add_apply]
                   rw [← map_add]; congr 1; ext; simp

theorem zmodPairing_apply {N : ℕ} (hK : ∀ x : K, N • x = 0)
    (χ : AddSubgroup.torsionBy A (N : ℤ) →+ ZMod N) (x y : K) :
    ((X.zmodPairing hK χ x y : ZMod N)) = χ ⟨X.pairing x y, X.pairing_mem_torsion hK x y⟩ := rfl

theorem zmodPairing_isAlt {N : ℕ} (hK : ∀ x : K, N • x = 0)
    (χ : AddSubgroup.torsionBy A (N : ℤ) →+ ZMod N) : IsAlt (X.zmodPairing hK χ) := by
  intro x
  rw [zmodPairing_apply]
  convert χ.map_zero using 2
  ext
  exact X.pairing_self x

theorem zmodPairing_isNondeg {N : ℕ} (hK : ∀ x : K, N • x = 0)
    (χ : AddSubgroup.torsionBy A (N : ℤ) →+ ZMod N) (hχ : Function.Injective χ)
    (hZ : ∀ g : G, (∀ h, g * h = h * g) → X.p g = 1) : IsNondeg (X.zmodPairing hK χ) := by
  intro x hx
  refine X.pairing_nondeg hZ x fun y => ?_
  have h := hx y
  rw [zmodPairing_apply, ← χ.map_zero] at h
  exact congrArg Subtype.val (hχ h)

end CentralExt

/-- **A discrete logarithm on `(k^×)[N]`** from a primitive `N`-th root of unity. -/
theorem exists_injective_torsion_units_zmod {L : Type*} [CommRing L] [IsDomain L] {N : ℕ}
    [NeZero N] {ζ : L} (hζ : IsPrimitiveRoot ζ N) :
    ∃ χ : AddSubgroup.torsionBy (Additive Lˣ) (N : ℤ) →+ ZMod N, Function.Injective χ := by
  have hu : IsUnit ζ := hζ.isUnit (NeZero.ne N)
  have hζu : IsPrimitiveRoot hu.unit N := IsPrimitiveRoot.coe_units_iff.1 hζ
  have hmem : ∀ x : AddSubgroup.torsionBy (Additive Lˣ) (N : ℤ),
      Additive.toMul (x : Additive Lˣ) ∈ Subgroup.zpowers hu.unit := by
    intro x
    rw [hζu.zpowers_eq, mem_rootsOfUnity]
    have hx := x.2
    change ((N : ℕ) : ℤ) • (x : Additive Lˣ) = 0 at hx
    rw [natCast_zsmul] at hx
    exact congrArg Additive.toMul hx
  let ι : AddSubgroup.torsionBy (Additive Lˣ) (N : ℤ) →+ Additive (Subgroup.zpowers hu.unit) :=
    { toFun := fun x => Additive.ofMul ⟨Additive.toMul (x : Additive Lˣ), hmem x⟩
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  refine ⟨(hζu.zmodEquivZPowers.symm.toAddMonoidHom).comp ι, ?_⟩
  intro x y h
  have h' := hζu.zmodEquivZPowers.symm.injective h
  have := congrArg (fun z => ((Additive.toMul z : Subgroup.zpowers hu.unit) : Lˣ)) h'
  exact Subtype.ext this

end RamanujanWeil.Arith.Deuring.Geom.G7.Fin.Weil
