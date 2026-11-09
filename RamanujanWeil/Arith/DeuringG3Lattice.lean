import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.RingTheory.Filtration
import Mathlib.RingTheory.TensorProduct.Free
import Mathlib.RingTheory.TensorProduct.Basic

/-!
# A3-ord, G3 (lattice algebra): finite generation and `⊗ ℤ_ℓ`-injectivity from a definite form

Pure algebra behind Mumford §19 Thm 3 / Silverman III.7.4, isolated from the geometry.

Let `M` be an abelian group with a biadditive form `B : M →+ M →+ ℤ` that is *anisotropic*
(`B x x = 0 → x = 0`; e.g. the polar form of a positive definite degree), let `T` be a free
`ℤ_ℓ`-module of finite rank `r` and `τ : M →+ T` an additive map that is `ℓ`-*saturated*:
`τ x ∈ ℓ T ⇒ x ∈ ℓ M`. Then

* `finite_of_anisotropic_of_saturated`, `free_of_anisotropic_of_saturated`: `M` is a finitely
  generated free abelian group;
* `finrank_le_of_anisotropic_of_saturated`: `rank_ℤ M ≤ r`;
* `liftBaseChange_injective_of_anisotropic_of_saturated`: `M ⊗_ℤ ℤ_ℓ → T` is injective.

The proof is algebraic (no topology): the saturation `N'` of a finitely generated subgroup
`N = ⟨e₁, …, e_s⟩` embeds into `ℤ^s` by `x ↦ (B x eᵢ)ᵢ` (anisotropy), hence is finitely generated
and free; on a saturated free subgroup, `ℤ`-independence of a basis gives `ℤ_ℓ`-independence of
its `τ`-image (reduce coefficients mod `ℓ`, use saturation, then Krull's intersection theorem in
`ℤ_ℓ`).
-/

open Module

namespace RamanujanWeil.Arith.Deuring.Geom.Lattice

variable {M : Type*} [AddCommGroup M]

/-- The `ℤ`-saturation of a subgroup: the elements with a nonzero multiple in it. -/
def saturation (N : Submodule ℤ M) : Submodule ℤ M where
  carrier := {x | ∃ n : ℤ, n ≠ 0 ∧ n • x ∈ N}
  add_mem' := by
    rintro x y ⟨n, hn, hx⟩ ⟨m, hm, hy⟩
    refine ⟨n * m, mul_ne_zero hn hm, ?_⟩
    rw [smul_add, mul_comm n m, mul_smul, mul_comm m n, mul_smul]
    exact N.add_mem (N.smul_mem m hx) (N.smul_mem n hy)
  zero_mem' := ⟨1, one_ne_zero, by simp⟩
  smul_mem' := by
    rintro c x ⟨n, hn, hx⟩
    refine ⟨n, hn, ?_⟩
    rw [smul_comm]
    exact N.smul_mem c hx

theorem le_saturation (N : Submodule ℤ M) : N ≤ saturation N :=
  fun x hx => ⟨1, one_ne_zero, by simpa using hx⟩

section Form

variable (B : M →+ M →+ ℤ) (hB : ∀ x, B x x = 0 → x = 0)
include hB

/-- An anisotropic biadditive form forces torsion freeness. -/
theorem eq_zero_of_smul_eq_zero {n : ℤ} (hn : n ≠ 0) {x : M} (h : n • x = 0) : x = 0 := by
  apply hB
  have : B x (n • x) = 0 := by rw [h, map_zero]
  rw [map_zsmul, smul_eq_mul] at this
  exact (mul_eq_zero.mp this).resolve_left hn

/-- The pairing `x ↦ (B x (e i))ᵢ`, as a `ℤ`-linear map. -/
def pairing {ι : Type*} (e : ι → M) : M →ₗ[ℤ] (ι → ℤ) :=
  (AddMonoidHom.toIntLinearMap
    { toFun := fun x i => B x (e i)
      map_zero' := by ext i; simp
      map_add' := fun x y => by ext i; simp })

omit hB in
@[simp] theorem pairing_apply {ι : Type*} (e : ι → M) (x : M) (i : ι) :
    pairing B e x i = B x (e i) := rfl

/-- **The pairing with a generating family is injective on the saturation.** -/
theorem pairing_injOn {ι : Type*} (e : ι → M) :
    Set.InjOn (pairing B e) (saturation (Submodule.span ℤ (Set.range e))) := by
  intro x hx y hy hxy
  have hz : (x - y) ∈ saturation (Submodule.span ℤ (Set.range e)) :=
    (saturation _).sub_mem hx hy
  have h0 : ∀ i, B (x - y) (e i) = 0 := fun i => by
    have := congrFun hxy i
    simp only [pairing_apply] at this
    rw [map_sub, AddMonoidHom.sub_apply, this, sub_self]
  have hspan : ∀ w ∈ Submodule.span ℤ (Set.range e), B (x - y) w = 0 := by
    intro w hw
    induction hw using Submodule.span_induction with
    | mem w hw => obtain ⟨i, rfl⟩ := hw; exact h0 i
    | zero => simp
    | add a b _ _ ha hb => rw [map_add, ha, hb, add_zero]
    | smul c a _ ha => rw [map_zsmul, ha, smul_zero]
  obtain ⟨n, hn, hmem⟩ := hz
  have h1 := hspan _ hmem
  rw [map_zsmul, smul_eq_mul] at h1
  exact sub_eq_zero.mp (hB _ ((mul_eq_zero.mp h1).resolve_left hn))

/-- If every element of `M` has a nonzero multiple in the span of a finite family, `M` is a
finitely generated free abelian group. -/
theorem finite_free_of_forall_mem_saturation {ι : Type*} [Finite ι] (e : ι → M)
    (h : ∀ x, x ∈ saturation (Submodule.span ℤ (Set.range e))) :
    Module.Finite ℤ M ∧ Module.Free ℤ M := by
  have hinj : Function.Injective (pairing B e) := fun x y hxy => pairing_injOn B hB e (h x) (h y) hxy
  have : Module.Finite ℤ M := Module.Finite.of_injective _ hinj
  have : IsTorsionFree ℤ M :=
    hinj.moduleIsTorsionFree _ (fun r m => (pairing B e).map_smul r m)
  exact ⟨inferInstance, inferInstance⟩

/-- The saturation of a finitely generated subgroup is finitely generated and free. -/
theorem finite_free_saturation {ι : Type*} [Finite ι] (e : ι → M) :
    Module.Finite ℤ (saturation (Submodule.span ℤ (Set.range e))) ∧
      Module.Free ℤ (saturation (Submodule.span ℤ (Set.range e))) := by
  set S := saturation (Submodule.span ℤ (Set.range e))
  have hinj : Function.Injective ((pairing B e).comp S.subtype) := fun x y hxy =>
    Subtype.ext (pairing_injOn B hB e x.2 y.2 hxy)
  have : Module.Finite ℤ S := Module.Finite.of_injective _ hinj
  have : IsTorsionFree ℤ S :=
    hinj.moduleIsTorsionFree _ (fun r m => ((pairing B e).comp S.subtype).map_smul r m)
  exact ⟨inferInstance, inferInstance⟩

end Form

section Padic

variable {ℓ : ℕ} [Fact ℓ.Prime] {T : Type*} [AddCommGroup T] [Module ℤ_[ℓ] T]

/-- One step of the descent: a `ℤ_ℓ`-relation among the `τ`-images of a `ℤ`-basis of an
`ℓ`-saturated group has all coefficients in `ℓ ℤ_ℓ`. -/
theorem mem_maximalIdeal_of_relation {N : Type*} [AddCommGroup N] {ι : Type*} [Fintype ι]
    (b : Basis ι ℤ N) (τ : N →+ T)
    (hsat : ∀ x z, τ x = (ℓ : ℤ_[ℓ]) • z → ∃ y, x = (ℓ : ℤ) • y)
    (g : ι → ℤ_[ℓ]) (hg : ∑ i, g i • τ (b i) = 0) (i : ι) :
    g i ∈ IsLocalRing.maximalIdeal ℤ_[ℓ] := by
  classical
  set n : ι → ℤ := fun i => (PadicInt.zmodRepr (g i) : ℤ)
  have hd : ∀ i, ∃ w, g i - (n i : ℤ_[ℓ]) = (ℓ : ℤ_[ℓ]) * w := fun i => by
    have := PadicInt.sub_zmodRepr_mem (g i)
    rw [PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton'] at this
    obtain ⟨w, hw⟩ := this
    exact ⟨w, by simp only [n, Int.cast_natCast]; rw [← hw, mul_comm]⟩
  choose w hw using hd
  have hτ : τ (∑ i, n i • b i) = (ℓ : ℤ_[ℓ]) • (-∑ i, w i • τ (b i)) := by
    rw [map_sum]
    have : ∀ i, τ (n i • b i) = g i • τ (b i) - (ℓ : ℤ_[ℓ]) • (w i • τ (b i)) := fun i => by
      rw [map_zsmul, ← Int.cast_smul_eq_zsmul ℤ_[ℓ], smul_smul, ← sub_smul]
      congr 1
      linear_combination -(hw i)
    rw [Finset.sum_congr rfl (fun i _ => this i), Finset.sum_sub_distrib, hg, zero_sub,
      ← Finset.smul_sum, smul_neg]
  obtain ⟨y, hy⟩ := hsat _ _ hτ
  have hrep := congrArg (fun z => b.repr z i) hy
  simp only [map_sum, map_zsmul, Basis.repr_self, Finsupp.coe_finsetSum, Finset.sum_apply,
    Finsupp.coe_smul, Pi.smul_apply, Finsupp.single_apply, smul_eq_mul, mul_ite, mul_one,
    mul_zero] at hrep
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true] at hrep
  -- `n i = ℓ * (b.repr y i)`
  have hni : (n i : ℤ_[ℓ]) ∈ IsLocalRing.maximalIdeal ℤ_[ℓ] := by
    rw [PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton']
    refine ⟨(b.repr y i : ℤ_[ℓ]), ?_⟩
    rw [hrep]; push_cast; ring
  have hgi : g i = (n i : ℤ_[ℓ]) + (ℓ : ℤ_[ℓ]) * w i := by rw [← hw i]; ring
  rw [hgi]
  refine Ideal.add_mem _ hni ?_
  apply Ideal.mul_mem_right
  rw [PadicInt.maximalIdeal_eq_span_p]
  exact Ideal.mem_span_singleton_self _

/-- **Linear independence over `ℤ_ℓ`.** On an `ℓ`-saturated free abelian group, the `τ`-image
of a `ℤ`-basis is `ℤ_ℓ`-linearly independent. -/
theorem linearIndependent_of_saturated [IsTorsionFree ℤ_[ℓ] T] {N : Type*} [AddCommGroup N] {ι : Type*} [Fintype ι]
    (b : Basis ι ℤ N) (τ : N →+ T)
    (hsat : ∀ x z, τ x = (ℓ : ℤ_[ℓ]) • z → ∃ y, x = (ℓ : ℤ) • y) :
    LinearIndependent ℤ_[ℓ] (fun i => τ (b i)) := by
  classical
  rw [Fintype.linearIndependent_iff]
  have hℓ0 : (ℓ : ℤ_[ℓ]) ≠ 0 := by exact_mod_cast (Fact.out : ℓ.Prime).ne_zero
  have key : ∀ k : ℕ, ∀ g : ι → ℤ_[ℓ], ∑ i, g i • τ (b i) = 0 →
      ∀ i, g i ∈ IsLocalRing.maximalIdeal ℤ_[ℓ] ^ k := by
    intro k
    induction k with
    | zero => intro g _ i; simp
    | succ k ih =>
      intro g hg i
      have hm : ∀ j, ∃ c, g j = (ℓ : ℤ_[ℓ]) * c := fun j => by
        have := mem_maximalIdeal_of_relation b τ hsat g hg j
        rw [PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton'] at this
        obtain ⟨c, hc⟩ := this
        exact ⟨c, by rw [← hc, mul_comm]⟩
      choose c hc using hm
      have hc0 : ∑ j, c j • τ (b j) = 0 := by
        have : (ℓ : ℤ_[ℓ]) • ∑ j, c j • τ (b j) = 0 := by
          rw [Finset.smul_sum]
          simp_rw [smul_smul, ← hc]
          exact hg
        exact (smul_eq_zero_iff_right hℓ0).mp this
      rw [hc i, pow_succ']
      refine Ideal.mul_mem_mul ?_ (ih c hc0 i)
      rw [PadicInt.maximalIdeal_eq_span_p]
      exact Ideal.mem_span_singleton_self _
  intro g hg i
  have hbot := Ideal.iInf_pow_eq_bot_of_isLocalRing (IsLocalRing.maximalIdeal ℤ_[ℓ])
    (IsLocalRing.maximalIdeal.isMaximal ℤ_[ℓ]).ne_top
  have : g i ∈ (⨅ k : ℕ, IsLocalRing.maximalIdeal ℤ_[ℓ] ^ k) :=
    Ideal.mem_iInf.mpr fun k => key k g hg i
  rw [hbot] at this
  exact this

end Padic

section Main

variable {ℓ : ℕ} [Fact ℓ.Prime] {T : Type*} [AddCommGroup T] [Module ℤ_[ℓ] T]
  [Module.Free ℤ_[ℓ] T] [Module.Finite ℤ_[ℓ] T]
  (B : M →+ M →+ ℤ) (hB : ∀ x, B x x = 0 → x = 0) (τ : M →+ T)
  (hsat : ∀ x z, τ x = (ℓ : ℤ_[ℓ]) • z → ∃ y, x = (ℓ : ℤ) • y)
include hB hsat

/-- The saturation of a finitely generated subgroup has rank at most `rank T`. -/
theorem finrank_saturation_le {ι : Type*} [Finite ι] (e : ι → M) :
    haveI := (finite_free_saturation B hB e).1
    finrank ℤ (saturation (Submodule.span ℤ (Set.range e))) ≤ finrank ℤ_[ℓ] T := by
  set S := saturation (Submodule.span ℤ (Set.range e))
  obtain ⟨hfin, hfree⟩ := finite_free_saturation B hB e
  let b := Module.Free.chooseBasis ℤ S
  have : IsTorsionFree ℤ_[ℓ] T := inferInstance
  have hsatS : ∀ (x : S) z, (τ.comp S.subtype.toAddMonoidHom) x = (ℓ : ℤ_[ℓ]) • z →
      ∃ y : S, x = (ℓ : ℤ) • y := by
    intro x z hx
    obtain ⟨y, hy⟩ := hsat _ _ hx
    obtain ⟨n, hn, hnx⟩ := x.2
    have hyS : y ∈ S := by
      refine ⟨n * ℓ, mul_ne_zero hn (by exact_mod_cast (Fact.out : ℓ.Prime).ne_zero), ?_⟩
      rw [mul_smul, ← hy]; exact hnx
    exact ⟨⟨y, hyS⟩, Subtype.ext hy⟩
  have hli := linearIndependent_of_saturated b (τ.comp S.subtype.toAddMonoidHom) hsatS
  rw [finrank_eq_card_chooseBasisIndex]
  exact hli.fintype_card_le_finrank

/-- Linearly independent families in `M` have at most `rank T` elements. -/
theorem card_le_of_linearIndependent {ι : Type*} [Fintype ι] {e : ι → M}
    (he : LinearIndependent ℤ e) : Fintype.card ι ≤ finrank ℤ_[ℓ] T := by
  set S := saturation (Submodule.span ℤ (Set.range e))
  obtain ⟨hfin, hfree⟩ := finite_free_saturation B hB e
  have hmem : ∀ i, e i ∈ S := fun i =>
    le_saturation _ (Submodule.subset_span ⟨i, rfl⟩)
  let e' : ι → S := fun i => ⟨e i, hmem i⟩
  have he' : LinearIndependent ℤ e' := LinearIndependent.of_comp S.subtype he
  exact he'.fintype_card_le_finrank.trans (finrank_saturation_le B hB τ hsat e)

/-- **`M` is a finitely generated free abelian group.** -/
theorem finite_free_of_anisotropic_of_saturated : Module.Finite ℤ M ∧ Module.Free ℤ M := by
  obtain ⟨s, hs, hmax⟩ := exists_maximal_linearIndepOn ℤ (id : M → M)
  have hsfin : s.Finite := by
    by_contra hinf
    obtain ⟨t, hts, hcard⟩ := Set.Infinite.exists_subset_card_eq hinf (finrank ℤ_[ℓ] T + 1)
    have hli : LinearIndependent ℤ (fun x : (t : Set M) => (x : M)) :=
      (hs.mono hts).linearIndependent
    have := card_le_of_linearIndependent B hB τ hsat hli
    simp only [Finset.coe_sort_coe, Fintype.card_coe, hcard] at this
    omega
  have : Finite s := hsfin.to_subtype
  apply finite_free_of_forall_mem_saturation B hB (fun x : s => (x : M))
  intro x
  have : (id : M → M) '' s = Set.range (fun x : s => (x : M)) := by ext; simp
  by_cases hx : x ∈ s
  · exact le_saturation _ (Submodule.subset_span ⟨⟨x, hx⟩, rfl⟩)
  obtain ⟨a, ha, hax⟩ := hmax x hx
  refine ⟨a, ha, ?_⟩
  rw [← this]; exact hax

theorem finrank_le_of_anisotropic_of_saturated :
    finrank ℤ M ≤ finrank ℤ_[ℓ] T := by
  obtain ⟨hfin, hfree⟩ := finite_free_of_anisotropic_of_saturated B hB τ hsat
  let b := Module.Free.chooseBasis ℤ M
  rw [finrank_eq_card_chooseBasisIndex]
  exact card_le_of_linearIndependent B hB τ hsat b.linearIndependent

/-- **`M ⊗_ℤ ℤ_ℓ → T` is injective.** -/
theorem liftBaseChange_injective_of_anisotropic_of_saturated :
    Function.Injective ((τ.toIntLinearMap).liftBaseChange ℤ_[ℓ]) := by
  classical
  obtain ⟨hfin, hfree⟩ := finite_free_of_anisotropic_of_saturated B hB τ hsat
  let b := Module.Free.chooseBasis ℤ M
  let bb := Algebra.TensorProduct.basis ℤ_[ℓ] b
  have : IsTorsionFree ℤ_[ℓ] T := inferInstance
  have hli := linearIndependent_of_saturated b τ hsat
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro x hx
  rw [← bb.sum_repr x, map_sum] at hx
  simp only [map_smul, bb, Algebra.TensorProduct.basis_apply,
    LinearMap.liftBaseChange_one_tmul, AddMonoidHom.coe_toIntLinearMap] at hx
  have h0 := Fintype.linearIndependent_iff.mp hli _ hx
  apply bb.repr.injective
  ext i
  simpa [bb] using h0 i

end Main

end RamanujanWeil.Arith.Deuring.Geom.Lattice
