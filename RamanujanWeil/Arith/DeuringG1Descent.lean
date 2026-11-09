import Mathlib.AlgebraicGeometry.EllipticCurve.VariableChange
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# A3-ord, G1 (Galois descent for coordinate changes)

Let `K = 𝔽_q` and `K̄ = AlgebraicClosure K`, with `q`-power Frobenius `F : K̄ → K̄`. This file
proves the coordinate-level half of blueprint step G1(b,c) (`docs/ARITH_DEURING_PROGRESS2.md`):
an isomorphism of Weierstrass curves over `K̄` that commutes with Frobenius is defined over `K`.

* `mem_range_of_pow_card_eq`: the fixed points of `F` in `K̄` are exactly `K`;
* `exists_map_eq_of_frobFixed`: a `F`-fixed `VariableChange K̄` is the base change of a
  `VariableChange K`;
* **`mem_orbit_iff_exists_frobFixed`**: `W' ∈ VariableChange(K) • W` iff some `F`-fixed
  `C ∈ VariableChange K̄` has `C • W_K̄ = W'_K̄`;
* **`stabilizerEquivFrobFixed`**: `Stab_{VariableChange K}(W) ≃* {C ∈ Stab_{VariableChange K̄}(W_K̄) |
  F(C) = C}`, hence `card_stabilizer_eq_frobFixed`.

The remaining part of G1 identifies `F`-fixed elements of `Stab_{VariableChange K̄}(W_K̄)` with
the automorphisms of the Frobenius Jacobian `A_W` commuting with `π` (pointed automorphisms of
`E_K̄` are coordinate changes — Stacks `WeierstrassCubicIsoAction` — and the Abel map
`E_K̄ ≅ A_W` intertwines `Ψ` with `π`).
-/

open Polynomial WeierstrassCurve

namespace RamanujanWeil.Arith.Deuring.Geom.Descent

variable {K : Type*} [Field K] [Fintype K]

local notation "K̄" => AlgebraicClosure K

/-- The `q`-power Frobenius of `K̄`, `q = #K`, as a ring endomorphism. -/
noncomputable def frobQ : K̄ →+* K̄ := (FiniteField.frobeniusAlgHom K K̄).toRingHom

theorem frobQ_apply (x : K̄) : frobQ x = x ^ Fintype.card K := rfl

theorem frobQ_algebraMap (a : K) : frobQ (algebraMap K K̄ a) = algebraMap K K̄ a :=
  (FiniteField.frobeniusAlgHom K K̄).commutes a

/-- **The fixed points of the `q`-power Frobenius in `K̄` are the elements of `K`.** -/
theorem mem_range_of_pow_card_eq (x : K̄) (hx : x ^ Fintype.card K = x) :
    ∃ a : K, algebraMap K K̄ a = x := by
  classical
  set q := Fintype.card K
  have hq : 1 < q := Fintype.one_lt_card
  set P : K̄[X] := X ^ q - X
  have hdeg : P.natDegree = q := FiniteField.X_pow_card_sub_X_natDegree_eq K̄ hq
  have hP0 : P ≠ 0 := FiniteField.X_pow_card_sub_X_ne_zero K̄ hq
  have hroot : ∀ y : K̄, y ^ q = y → y ∈ P.roots.toFinset := fun y hy => by
    rw [Multiset.mem_toFinset, mem_roots hP0, IsRoot, eval_sub, eval_pow, eval_X, hy, sub_self]
  set S := Finset.univ.image (algebraMap K K̄)
  have hS : S.card = q := by
    rw [Finset.card_image_of_injective _ (algebraMap K K̄).injective, Finset.card_univ]
  by_contra hne
  have hxS : x ∉ S := by
    simp only [S, Finset.mem_image, Finset.mem_univ, true_and, not_exists]
    exact fun a ha => hne ⟨a, ha⟩
  have hsub : insert x S ⊆ P.roots.toFinset := by
    intro y hy
    rcases Finset.mem_insert.mp hy with rfl | hy
    · exact hroot _ hx
    · obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp hy
      apply hroot
      rw [← map_pow, FiniteField.pow_card]
  have h1 := Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem hxS, hS] at h1
  have h2 := (Multiset.toFinset_card_le P.roots).trans (card_roots' P)
  omega

/-- A `K̄`-element is in `K` iff it is fixed by the Frobenius. -/
theorem frobQ_eq_iff (x : K̄) : frobQ x = x ↔ ∃ a : K, algebraMap K K̄ a = x := by
  constructor
  · exact mem_range_of_pow_card_eq x
  · rintro ⟨a, rfl⟩; exact frobQ_algebraMap a

/-- **Descent of coordinate changes**: a Frobenius-fixed `VariableChange K̄` comes from `K`. -/
theorem exists_map_eq_of_frobFixed (C : VariableChange K̄) (h : C.map frobQ = C) :
    ∃ C₀ : VariableChange K, C₀.map (algebraMap K K̄) = C := by
  have hu : frobQ (C.u : K̄) = C.u := congrArg (fun D : VariableChange K̄ => (D.u : K̄)) h
  have hr : frobQ C.r = C.r := congrArg VariableChange.r h
  have hs : frobQ C.s = C.s := congrArg VariableChange.s h
  have ht : frobQ C.t = C.t := congrArg VariableChange.t h
  obtain ⟨u, hu⟩ := (frobQ_eq_iff _).mp hu
  obtain ⟨r, hr⟩ := (frobQ_eq_iff _).mp hr
  obtain ⟨s, hs⟩ := (frobQ_eq_iff _).mp hs
  obtain ⟨t, ht⟩ := (frobQ_eq_iff _).mp ht
  have hu0 : u ≠ 0 := by
    rintro rfl
    rw [map_zero] at hu
    exact C.u.ne_zero hu.symm
  refine ⟨⟨Units.mk0 u hu0, r, s, t⟩, ?_⟩
  ext
  · simp [hu]
  · simp [hr]
  · simp [hs]
  · simp [ht]

theorem map_frobFixed (C₀ : VariableChange K) :
    (C₀.map (algebraMap K K̄)).map frobQ = C₀.map (algebraMap K K̄) := by
  rw [VariableChange.map_map]
  congr 1
  ext a
  exact frobQ_algebraMap a

/-- The Frobenius-fixed coordinate changes over `K̄`. -/
noncomputable def frobFixed : Subgroup (VariableChange K̄) where
  carrier := {C | C.map frobQ = C}
  mul_mem' := fun {C D} hC hD => by
    show VariableChange.mapHom frobQ (C * D) = C * D
    rw [map_mul]
    exact congrArg₂ (· * ·) hC hD
  one_mem' := by
    show VariableChange.mapHom frobQ 1 = 1
    exact map_one _
  inv_mem' := fun {C} hC => by
    show VariableChange.mapHom frobQ C⁻¹ = C⁻¹
    rw [map_inv]
    exact congrArg (·⁻¹) hC

theorem mem_frobFixed_iff (C : VariableChange K̄) :
    C ∈ (frobFixed : Subgroup (VariableChange K̄)) ↔ ∃ C₀ : VariableChange K,
      C₀.map (algebraMap K K̄) = C :=
  ⟨exists_map_eq_of_frobFixed C, by rintro ⟨C₀, rfl⟩; exact map_frobFixed C₀⟩

/-- **G1(b), coordinate level**: `W'` is `K`-isomorphic to `W` iff a Frobenius-fixed coordinate
change over `K̄` carries `W_K̄` to `W'_K̄`. -/
theorem mem_orbit_iff_exists_frobFixed (W W' : WeierstrassCurve K) :
    W' ∈ MulAction.orbit (VariableChange K) W ↔
      ∃ C ∈ (frobFixed : Subgroup (VariableChange K̄)),
        C • W.map (algebraMap K K̄) = W'.map (algebraMap K K̄) := by
  constructor
  · rintro ⟨C₀, rfl⟩
    exact ⟨C₀.map (algebraMap K K̄), map_frobFixed C₀, map_variableChange _ _ _⟩
  · rintro ⟨C, hC, hW⟩
    obtain ⟨C₀, rfl⟩ := exists_map_eq_of_frobFixed C hC
    refine ⟨C₀, WeierstrassCurve.map_injective (algebraMap K K̄).injective ?_⟩
    show (C₀ • W).map (algebraMap K K̄) = W'.map (algebraMap K K̄)
    rw [← map_variableChange]
    exact hW

/-- The Frobenius-fixed part of the stabilizer of `W_K̄`. -/
noncomputable def frobFixedStab (W : WeierstrassCurve K) : Subgroup (VariableChange K̄) :=
  MulAction.stabilizer (VariableChange K̄) (W.map (algebraMap K K̄)) ⊓ frobFixed

/-- **G1(c), coordinate level**: `Stab_{VariableChange K}(W)` is the Frobenius-fixed part of
`Stab_{VariableChange K̄}(W_K̄)`. -/
noncomputable def stabMap (W : WeierstrassCurve K) :
    MulAction.stabilizer (VariableChange K) W →* frobFixedStab W where
  toFun C := ⟨(C : VariableChange K).map (algebraMap K K̄),
    ⟨by
      show _ • _ = _
      rw [map_variableChange, show (C : VariableChange K) • W = W from C.2],
     map_frobFixed _⟩⟩
  map_one' := Subtype.ext (map_one (VariableChange.mapHom (algebraMap K K̄)))
  map_mul' C D := Subtype.ext (map_mul (VariableChange.mapHom (algebraMap K K̄))
    (C : VariableChange K) D)

noncomputable def stabilizerEquivFrobFixed (W : WeierstrassCurve K) :
    MulAction.stabilizer (VariableChange K) W ≃* frobFixedStab W :=
  MulEquiv.ofBijective (stabMap W)
    ⟨fun C D h => Subtype.ext (VariableChange.map_injective (algebraMap K K̄).injective
        (congrArg Subtype.val h)),
     fun ⟨C, hstab, hfix⟩ => by
      obtain ⟨C₀, rfl⟩ := exists_map_eq_of_frobFixed C hfix
      refine ⟨⟨C₀, ?_⟩, rfl⟩
      show C₀ • W = W
      apply WeierstrassCurve.map_injective (algebraMap K K̄).injective
      show (C₀ • W).map (algebraMap K K̄) = W.map (algebraMap K K̄)
      rw [← map_variableChange]
      exact hstab⟩

theorem card_stabilizer_eq_frobFixed (W : WeierstrassCurve K) :
    Nat.card (MulAction.stabilizer (VariableChange K) W) = Nat.card (frobFixedStab W) :=
  Nat.card_congr (stabilizerEquivFrobFixed W).toEquiv

end RamanujanWeil.Arith.Deuring.Geom.Descent
