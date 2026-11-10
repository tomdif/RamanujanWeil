import StacksFrontier.AlgebraicGeometry.TensorPowerTrivialize.Basic
import StacksFrontier.AlgebraicGeometry.Chow.ChernCap42.DivisorOfSection
import StacksFrontier.AlgebraicGeometry.PullbackSections.Qcqs
import StacksFrontier.AlgebraicGeometry.NonvanishingSpelling.Basic
import Mathlib.AlgebraicGeometry.FunctionField

/-!
# A3-ord, G7-C: sections of an invertible module on two charts, read in the function field

`docs/ARITH_DEURING_G7_GENUS2.md` §7. Let `X` be an integral scheme, `M` an invertible
`𝒪_X`-module, `G_a, G_b` global sections of `M`, and `U_a, U_b` opens covering `X` with `G_a`
nowhere zero on `U_a` and `G_b` nowhere zero on `U_b`, both containing the generic point `η`.

A global section `T` of `M` gives the rational function `θ T = (T / G_a)_η ∈ K(X)`. With
`ρ = (G_b / G_a)_η` and `O_U = 𝒪(U)_η ⊆ K(X)`:

* `θ` is injective (`Chart.theta_injective`): a section of an invertible module on an integral
  scheme is determined by its germ at `η`;
* **`Chart.range_theta`**: the image of `θ` is exactly `{f ∈ O_{U_a} | ρ⁻¹ f ∈ O_{U_b}}`. The
  inclusion is the cocycle identity `T/G_a = (G_b/G_a)(T/G_b)`; the converse glues
  `f G_a` on `U_a` and `ρ⁻¹ f G_b` on `U_b` (they agree on `U_a ∩ U_b` because their germs at `η`
  agree and `X` is integral);
* `Chart.theta_smul`: `θ (r T) = r_η θ T` for a global function `r`.

This is the sheaf-theoretic input of the base-point-free pencil (`DeuringG7Genus2PencilAlg`):
for `M = L^{⊗n}`, `G_a = s₀ⁿ`, `G_b = s₁ⁿ`, `ρ = xⁿ`, so `H⁰(L^{⊗n}) ≅ {f ∈ O_a | x⁻ⁿ f ∈ O_b}`.
-/

universe u

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open Stacks.TensorPowerTrivialize (resTop trivEquiv)

namespace RamanujanWeil.Arith.Deuring.Geom.G7.Genus2.Pencil.Chart

variable {X : Scheme.{u}} [IsIntegral X]

/-- The germ at the generic point, as a ring map `Γ(X, U) → K(X)`. -/
noncomputable abbrev germη (U : X.Opens) (hU : genericPoint X ∈ U) :
    Γ(X, U) →+* X.functionField :=
  (X.presheaf.germ U (genericPoint X) hU).hom

/-- The functions on `U`, as a subring of the function field. -/
noncomputable abbrev O (U : X.Opens) (hU : genericPoint X ∈ U) : Subring X.functionField :=
  (germη U hU).range

theorem germη_res {U V : X.Opens} (h : V ≤ U) (hV : genericPoint X ∈ V) (r : Γ(X, U)) :
    germη V hV (X.presheaf.map (homOfLE h).op r) = germη U (h hV) r :=
  X.presheaf.germ_res_apply (homOfLE h) (genericPoint X) hV r

theorem germη_injective (U : X.Opens) (hU : genericPoint X ∈ U) :
    Function.Injective (germη U hU) :=
  germ_injective_of_isIntegral X (genericPoint X) hU

variable (M : X.Modules) [Stacks.Ample.IsInvertibleModule X M]

/-- **The ratio `T / G`** on an open `W` on which `G` does not vanish. -/
noncomputable def quot (G : Γ(M, ⊤)) {W : X.Opens}
    (hW : W ≤ Stacks.NonvanishingOpen.nonvanishingOpen X M G) (T : Γ(M, ⊤)) : Γ(X, W) :=
  (trivEquiv M G hW).symm (resTop M T W)

variable {M}

theorem quot_smul (G : Γ(M, ⊤)) {W : X.Opens}
    (hW : W ≤ Stacks.NonvanishingOpen.nonvanishingOpen X M G) (T : Γ(M, ⊤)) :
    quot M G hW T • resTop M G W = resTop M T W :=
  Stacks.TensorPowerTrivialize.trivEquiv_symm_smul M G hW _

theorem quot_unique (G : Γ(M, ⊤)) {W : X.Opens}
    (hW : W ≤ Stacks.NonvanishingOpen.nonvanishingOpen X M G) (T : Γ(M, ⊤)) (c : Γ(X, W))
    (hc : c • resTop M G W = resTop M T W) : quot M G hW T = c :=
  (trivEquiv M G hW).injective ((quot_smul G hW T).trans hc.symm)

theorem quot_self (G : Γ(M, ⊤)) {W : X.Opens}
    (hW : W ≤ Stacks.NonvanishingOpen.nonvanishingOpen X M G) : quot M G hW G = 1 :=
  quot_unique G hW G 1 (one_smul _ _)

theorem quot_res (G : Γ(M, ⊤)) {W W' : X.Opens}
    (hW : W ≤ Stacks.NonvanishingOpen.nonvanishingOpen X M G) (h : W' ≤ W) (T : Γ(M, ⊤)) :
    X.presheaf.map (homOfLE h).op (quot M G hW T) = quot M G (h.trans hW) T := by
  refine (quot_unique G (h.trans hW) T _ ?_).symm
  have := congrArg (M.presheaf.map (homOfLE h).op) (quot_smul G hW T)
  rwa [Stacks.TensorPowerTrivialize.map_smul_resTop,
    Stacks.TensorPowerTrivialize.res_resTop] at this

/-- **The cocycle identity** `T/G = (H/G)(T/H)`. -/
theorem quot_chain (G H : Γ(M, ⊤)) {W : X.Opens}
    (hG : W ≤ Stacks.NonvanishingOpen.nonvanishingOpen X M G)
    (hH : W ≤ Stacks.NonvanishingOpen.nonvanishingOpen X M H) (T : Γ(M, ⊤)) :
    quot M G hG T = quot M G hG H * quot M H hH T := by
  refine quot_unique G hG T _ ?_
  rw [mul_comm, mul_smul, quot_smul, quot_smul]

theorem quot_add (G : Γ(M, ⊤)) {W : X.Opens}
    (hW : W ≤ Stacks.NonvanishingOpen.nonvanishingOpen X M G) (T T' : Γ(M, ⊤)) :
    quot M G hW (T + T') = quot M G hW T + quot M G hW T' := by
  refine quot_unique G hW _ _ ?_
  rw [add_smul, quot_smul, quot_smul]
  exact (map_add _ T T').symm

theorem quot_rsmul (G : Γ(M, ⊤)) {W : X.Opens}
    (hW : W ≤ Stacks.NonvanishingOpen.nonvanishingOpen X M G) (r : Γ(X, ⊤)) (T : Γ(M, ⊤)) :
    quot M G hW (r • T) = X.presheaf.map (homOfLE le_top).op r * quot M G hW T := by
  refine quot_unique G hW _ _ ?_
  rw [mul_smul, quot_smul]
  exact (Scheme.Modules.map_smul M (homOfLE (le_top : W ≤ ⊤)) r T).symm

/-! ### The two-chart datum -/

/-- **Two charts for an invertible module**: global sections `G_a, G_b` nowhere zero on opens
`U_a, U_b` that cover `X` and contain the generic point. -/
structure Data (M : X.Modules) [Stacks.Ample.IsInvertibleModule X M] where
  Ga : Γ(M, ⊤)
  Gb : Γ(M, ⊤)
  Ua : X.Opens
  Ub : X.Opens
  hUa : Ua ≤ Stacks.NonvanishingOpen.nonvanishingOpen X M Ga
  hUb : Ub ≤ Stacks.NonvanishingOpen.nonvanishingOpen X M Gb
  cover : (⊤ : X.Opens) ≤ Ua ⊔ Ub
  ηa : genericPoint X ∈ Ua
  ηb : genericPoint X ∈ Ub

namespace Data

variable (D : Data M)

theorem ηab : genericPoint X ∈ D.Ua ⊓ D.Ub := ⟨D.ηa, D.ηb⟩

/-- `θ T = (T / G_a)_η`. -/
noncomputable def theta (T : Γ(M, ⊤)) : X.functionField :=
  germη D.Ua D.ηa (quot M D.Ga D.hUa T)

/-- `(T / G_b)_η`. -/
noncomputable def thetaB (T : Γ(M, ⊤)) : X.functionField :=
  germη D.Ub D.ηb (quot M D.Gb D.hUb T)

/-- `ρ = (G_b / G_a)_η`. -/
noncomputable def rho : X.functionField :=
  germη (D.Ua ⊓ D.Ub) D.ηab (quot M D.Ga (inf_le_left.trans D.hUa) D.Gb)

theorem theta_eq_germ_ab (T : Γ(M, ⊤)) :
    D.theta T = germη (D.Ua ⊓ D.Ub) D.ηab (quot M D.Ga (inf_le_left.trans D.hUa) T) := by
  rw [theta, ← germη_res inf_le_left D.ηab, quot_res]

theorem thetaB_eq_germ_ab (T : Γ(M, ⊤)) :
    D.thetaB T = germη (D.Ua ⊓ D.Ub) D.ηab (quot M D.Gb (inf_le_right.trans D.hUb) T) := by
  rw [thetaB, ← germη_res inf_le_right D.ηab, quot_res]

/-- **`θ T = ρ · θ_b T`**, the cocycle identity at `η`. -/
theorem theta_eq (T : Γ(M, ⊤)) : D.theta T = D.rho * D.thetaB T := by
  rw [theta_eq_germ_ab, thetaB_eq_germ_ab, rho, ← map_mul,
    ← quot_chain D.Ga D.Gb (inf_le_left.trans D.hUa) (inf_le_right.trans D.hUb)]

theorem rho_mul : D.rho * D.thetaB D.Ga = 1 := by
  rw [← theta_eq, theta, quot_self, map_one]

theorem rho_ne_zero : D.rho ≠ 0 := fun h => by
  have := D.rho_mul
  rw [h, zero_mul] at this
  exact zero_ne_one this

theorem theta_injective : Function.Injective D.theta := by
  intro T T' h
  rw [← sub_eq_zero]
  have hq : quot M D.Ga D.hUa (T - T') = 0 := by
    have h1 : quot M D.Ga D.hUa (T - T') + quot M D.Ga D.hUa T' = quot M D.Ga D.hUa T := by
      rw [← quot_add, sub_add_cancel]
    refine germη_injective D.Ua D.ηa ?_
    have h2 := congrArg (germη D.Ua D.ηa) h1
    rw [map_add] at h2
    rw [map_zero]
    have : D.theta T = D.theta T' := h
    unfold theta at this
    rw [this] at h2
    linear_combination h2
  have hres : resTop M (T - T') D.Ua = 0 := by
    rw [← quot_smul D.Ga D.hUa (T - T'), hq, zero_smul]
  have hM : Stacks.SheafOfModules.IsInvertible X.presheaf
      (structureSheafRing X.toRingedSpace).property M :=
    Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ _ inferInstance
  refine Stacks.ChernCap42.eq_zero_of_germ_eq_zero (x := genericPoint X) M _ ?_
  show (M.presheaf.germ ⊤ (genericPoint X) trivial).hom (T - T') = 0
  rw [← M.presheaf.germ_res_apply (homOfLE (le_top : D.Ua ≤ ⊤)) (genericPoint X) D.ηa]
  change (M.presheaf.germ D.Ua (genericPoint X) D.ηa).hom (resTop M (T - T') D.Ua) = 0
  rw [hres, map_zero]

theorem theta_add (T T' : Γ(M, ⊤)) : D.theta (T + T') = D.theta T + D.theta T' := by
  rw [theta, quot_add, map_add]; rfl

theorem theta_rsmul (r : Γ(X, ⊤)) (T : Γ(M, ⊤)) :
    D.theta (r • T) = germη ⊤ trivial r * D.theta T := by
  rw [theta, quot_rsmul, map_mul, germη_res]
  rfl

theorem theta_mem_O (T : Γ(M, ⊤)) : D.theta T ∈ O D.Ua D.ηa := ⟨_, rfl⟩

theorem rho_inv_mul_theta_mem_O (T : Γ(M, ⊤)) : D.rho⁻¹ * D.theta T ∈ O D.Ub D.ηb := by
  rw [theta_eq, ← mul_assoc, inv_mul_cancel₀ D.rho_ne_zero, one_mul]
  exact ⟨_, rfl⟩

/-- **Gluing**: every `f ∈ O_{U_a}` with `ρ⁻¹ f ∈ O_{U_b}` is `θ T`. -/
theorem exists_theta_eq {f : X.functionField} (ha : f ∈ O D.Ua D.ηa)
    (hb : D.rho⁻¹ * f ∈ O D.Ub D.ηb) : ∃ T : Γ(M, ⊤), D.theta T = f := by
  obtain ⟨φa, hφa⟩ := ha
  obtain ⟨φb, hφb⟩ := hb
  set σa : Γ(M, D.Ua) := φa • resTop M D.Ga D.Ua
  set σb : Γ(M, D.Ub) := φb • resTop M D.Gb D.Ub
  set qab := quot M D.Ga (inf_le_left.trans D.hUa) D.Gb
  have hfun : X.presheaf.map (homOfLE (inf_le_left : D.Ua ⊓ D.Ub ≤ D.Ua)).op φa =
      X.presheaf.map (homOfLE (inf_le_right : D.Ua ⊓ D.Ub ≤ D.Ub)).op φb * qab := by
    refine germη_injective _ D.ηab ?_
    rw [map_mul, germη_res, germη_res, hφa, hφb]
    show f = D.rho⁻¹ * f * D.rho
    field_simp [D.rho_ne_zero]
  have hagree : M.presheaf.map (homOfLE (inf_le_left : D.Ua ⊓ D.Ub ≤ D.Ua)).op σa =
      M.presheaf.map (homOfLE (inf_le_right : D.Ua ⊓ D.Ub ≤ D.Ub)).op σb := by
    simp only [σa, σb]
    rw [Stacks.TensorPowerTrivialize.map_smul_resTop, Stacks.TensorPowerTrivialize.map_smul_resTop,
      hfun, mul_smul, quot_smul]
  obtain ⟨y, hya, -⟩ := Stacks.AlgebraicGeometry.SectionsBaseChange.sheaf_glue_pair
    (⟨M.presheaf, M.isSheaf⟩ : TopCat.Sheaf Ab.{u} _) D.Ua D.Ub σa σb hagree
  refine ⟨M.presheaf.map (homOfLE D.cover).op y, ?_⟩
  have hT : resTop M (M.presheaf.map (homOfLE D.cover).op y) D.Ua = σa := by
    rw [← hya]
    show M.presheaf.map _ (M.presheaf.map _ y) = _
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
    rfl
  rw [theta, quot_unique D.Ga D.hUa _ φa hT.symm, hφa]

/-- **The image of `θ`**: `{f ∈ O_{U_a} | ρ⁻¹ f ∈ O_{U_b}}`. -/
theorem mem_range_theta_iff (f : X.functionField) :
    f ∈ Set.range D.theta ↔ f ∈ O D.Ua D.ηa ∧ D.rho⁻¹ * f ∈ O D.Ub D.ηb := by
  constructor
  · rintro ⟨T, rfl⟩
    exact ⟨D.theta_mem_O T, D.rho_inv_mul_theta_mem_O T⟩
  · rintro ⟨ha, hb⟩
    exact D.exists_theta_eq ha hb

end Data

end RamanujanWeil.Arith.Deuring.Geom.G7.Genus2.Pencil.Chart
