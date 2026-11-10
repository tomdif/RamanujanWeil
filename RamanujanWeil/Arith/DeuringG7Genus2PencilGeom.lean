import RamanujanWeil.Arith.DeuringG7Genus2PencilChart
import RamanujanWeil.Arith.DeuringG7Genus2PencilAlg
import StacksFrontier.AlgebraicGeometry.SectionRingChartBijective.Basic
import StacksFrontier.AlgebraicGeometry.SectionRingProjMorphism.ToSpecZero
import StacksFrontier.AlgebraicGeometry.SectionRingProjImmersion.Basic
import StacksFrontier.AlgebraicGeometry.Curves.GenusOne.TwistDimensions
import StacksFrontier.AlgebraicGeometry.Curves.LinearSeriesMorphism
import StacksFrontier.AlgebraicGeometry.Curves.NonsingularProjectiveModel
import StacksFrontier.AlgebraicGeometry.Constructions.ProjectiveSpaceGeneratingSections

/-!
# A3-ord, G7-C: the graded pencil of a base-point-free pencil on a curve

`docs/ARITH_DEURING_G7_GENUS2.md` §7. Let `Y` be an integral scheme over a field `K`, `L` an
invertible module and `t₀, t₁` global sections of `L` without common zero (`Setup`). Put
`a_i = t_i` in degree one of the section ring, `U_i = Y_{t_i}`, `x = (t₁/t₀)_η`,
`y = (t₀/t₁)_η = x⁻¹` and

  `V n = {f ∈ K(Y) | f ∈ 𝒪(U₀)_η, yⁿ f ∈ 𝒪(U₁)_η}`.

* `Setup.gradedPencil`: these form a `GradedPencil` (`DeuringG7Genus2PencilAlg`): the axioms
  (`1, x ∈ V 1`, multiplicativity, base-point freeness) are immediate from the definition.
* **`Setup.finrank_V`**: for `n ≥ 1`, `V n ≅ H⁰(L^{⊗n})` (`K`-linearly). The map is
  `T ↦ (T/t₀ⁿ)_η` (`Chart.Data.theta` for `M = L^{⊗n}`, `G_a = t₀ⁿ`, `G_b = t₁ⁿ`), and
  `(t₁ⁿ/t₀ⁿ)_η = xⁿ` (`Setup.rho_data`, from `ratio_powSec`).
* **`Setup.exists_div`**: if `L` is ample and `Y → Spec Γ(Y, 𝒪)` universally closed, every
  `f ∈ K(Y)` is a quotient of two elements of one `V m`: `U₀ = Y_{t₀}` is affine (the canonical
  map `Y → Proj Γ_*(Y, L)` is an isomorphism, Stacks 0C6J), its functions are the fractions
  `T/t₀ᵐ` (Stacks 01PW, `chartRingMap_bijective`), and `K(Y) = Frac 𝒪(U₀)`.
-/

universe u

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite Module
open Stacks.GradedSections (powSections sectionRing mul)
open Stacks.SectionProduct (globalSection)
open Stacks.TensorPowers (natTensorPow)
open Stacks.SectionExtension (powSec)
open Stacks.AmpleFiniteAvoidance (nvOpen grading)
open Stacks.AlgebraicGeometry.ProjChartFromRatios (secOf)
open Stacks.AlgebraicGeometry.ProjectiveSpaceGeneratingSections (twistOneSection baseRingHom)
open Stacks.SectionRingChartMap (ratio ratioR)

namespace RamanujanWeil.Arith.Deuring.Geom.G7.Genus2.Pencil

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory
  Stacks.SectionRingGeometric.schemePreadditive
  Stacks.SectionRingGeometric.schemeTensorRightAdditive

attribute [local implicit_reducible] Stacks.TensorPowers.natTensorPow

attribute [local instance] Stacks.AlgebraicGeometry.ProjectiveSpaceGeneratingSections.globalSectionsModule

open Chart

/-! ### Ratios of powers -/

section Powers

variable {Y : Scheme.{u}} (L : Y.Modules) [Stacks.Ample.IsInvertibleModule Y L]

/-- **`(hⁿ/gⁿ) = (h/g)ⁿ`** for degree-one sections `g, h`, on any open where `g` is nowhere
zero. -/
theorem ratio_powSec (g h : powSections L 1) {W : Y.Opens} (hW : W ≤ nvOpen L g) (n : ℕ)
    (hn : 1 ≤ n) :
    ratio L (powSec L g n) (Stacks.SectionRingChartMap.le_nvOpen_powSec L g hW n hn)
        (powSec L h n) = ratio L g hW h ^ n := by
  induction n, hn using Nat.le_induction with
  | base =>
    rw [← Stacks.SectionRingChartMap.ratioR_of, Stacks.SectionRingChartMap.of_powSec_eq_pow,
      Stacks.SectionRingChartMap.ratioR_congr L (by norm_num : 1 * 1 = 1) (powSec L g 1) g _ hW
        (by rw [Stacks.SectionRingChartMap.of_powSec_eq_pow, pow_one]),
      pow_one, pow_one, Stacks.SectionRingChartMap.ratioR_of]
  | succ n hn ih =>
    have hgn := Stacks.SectionRingChartMap.le_nvOpen_powSec L g hW n hn
    have hgg : W ≤ nvOpen L (mul (powSec L g n) g) :=
      Stacks.SectionRingChartMap.le_nvOpen_mul L hgn hW
    rw [← Stacks.SectionRingChartMap.ratioR_of, Stacks.SectionRingChartMap.of_powSec_eq_pow,
      Stacks.SectionRingChartMap.ratioR_congr L (by ring : 1 * (n + 1) = 1 * n + 1)
        (powSec L g (n + 1)) (mul (powSec L g n) g) _ hgg
        (by rw [Stacks.SectionRingChartMap.of_mul_eq, Stacks.SectionRingChartMap.of_powSec_eq_pow,
          Stacks.SectionRingChartMap.of_powSec_eq_pow, pow_succ]),
      pow_succ, Stacks.SectionRingChartMap.ratioR_mul L (powSec L g n) g hgn hW hgg
        (by rw [← Stacks.SectionRingChartMap.of_powSec_eq_pow]
            exact Stacks.ExternalGrading.of_mem_summand _ _)
        (Stacks.ExternalGrading.of_mem_summand _ _),
      ← Stacks.SectionRingChartMap.of_powSec_eq_pow, Stacks.SectionRingChartMap.ratioR_of,
      Stacks.SectionRingChartMap.ratioR_of, ih, pow_succ]

end Powers

/-! ### The setup -/

/-- A global section of `L`, read in degree one of the section ring. -/
noncomputable abbrev deg1 {Y : Scheme.{u}} (L : Y.Modules) (t : Γ(L, ⊤)) : powSections L 1 :=
  secOf L (twistOneSection L t)

theorem nvOpen_deg1 {Y : Scheme.{u}} (L : Y.Modules) [Stacks.Ample.IsInvertibleModule Y L]
    (t : Γ(L, ⊤)) :
    nvOpen L (deg1 L t) = Stacks.NonvanishingOpen.nonvanishingOpen Y L t := by
  rw [Stacks.AmpleFiniteAvoidance.nvOpen,
    Stacks.AlgebraicGeometry.ProjChartFromRatios.globalSection_secOf,
    Stacks.AlgebraicGeometry.ProjectiveSpaceGeneratingSections.nonvanishingOpen_twistOneSection]

/-- **A base-point-free pencil** `t₀, t₁` of an invertible module on an integral scheme, with the
generic point in both charts. -/
structure Setup (Y : Scheme.{u}) [IsIntegral Y] where
  L : Y.Modules
  [inv : Stacks.Ample.IsInvertibleModule Y L]
  t : Fin 2 → Γ(L, ⊤)
  hη : ∀ i, genericPoint Y ∈ nvOpen L (deg1 L (t i))
  cover : (⊤ : Y.Opens) ≤ nvOpen L (deg1 L (t 0)) ⊔ nvOpen L (deg1 L (t 1))

attribute [instance] Setup.inv

namespace Setup

variable {Y : Scheme.{u}} [IsIntegral Y] (S : Setup Y)

/-- `aᵢ = tᵢ` in degree one. -/
noncomputable abbrev a (i : Fin 2) : powSections S.L 1 := deg1 S.L (S.t i)

/-- `Uᵢ = Y_{tᵢ}`. -/
noncomputable abbrev U (i : Fin 2) : Y.Opens := nvOpen S.L (S.a i)

/-- `x = (t₁/t₀)_η`. -/
noncomputable def x : Y.functionField := germη (S.U 0) (S.hη 0) (ratio S.L (S.a 0) le_rfl (S.a 1))

/-- `y = (t₀/t₁)_η`. -/
noncomputable def y : Y.functionField := germη (S.U 1) (S.hη 1) (ratio S.L (S.a 1) le_rfl (S.a 0))

/-- The two charts of `L^{⊗1}` with the degree-one generators. -/
noncomputable def data1 : Chart.Data (natTensorPow S.L 1) where
  Ga := globalSection Y _ (S.a 0)
  Gb := globalSection Y _ (S.a 1)
  Ua := S.U 0
  Ub := S.U 1
  hUa := le_rfl
  hUb := le_rfl
  cover := S.cover
  ηa := S.hη 0
  ηb := S.hη 1

theorem x_mul_y : S.x * S.y = 1 := by
  have h := S.data1.rho_mul
  have hx : S.data1.rho = S.x := by
    have := S.data1.theta_eq_germ_ab S.data1.Gb
    exact this.symm.trans rfl
  rw [hx] at h
  exact h

theorem x_ne_zero : S.x ≠ 0 := left_ne_zero_of_mul_eq_one S.x_mul_y

theorem y_eq_inv : S.y = S.x⁻¹ := eq_inv_of_mul_eq_one_right S.x_mul_y

theorem x_mem_O : S.x ∈ O (S.U 0) (S.hη 0) := ⟨_, rfl⟩

theorem y_mem_O : S.y ∈ O (S.U 1) (S.hη 1) := ⟨_, rfl⟩

/-- **The two charts of `L^{⊗n}`** with the generators `t₀ⁿ, t₁ⁿ`. -/
noncomputable def data (n : ℕ) (hn : 1 ≤ n) : Chart.Data (natTensorPow S.L (1 * n)) where
  Ga := globalSection Y _ (powSec S.L (S.a 0) n)
  Gb := globalSection Y _ (powSec S.L (S.a 1) n)
  Ua := S.U 0
  Ub := S.U 1
  hUa := Stacks.SectionRingChartMap.le_nvOpen_powSec S.L (S.a 0) le_rfl n hn
  hUb := Stacks.SectionRingChartMap.le_nvOpen_powSec S.L (S.a 1) le_rfl n hn
  cover := S.cover
  ηa := S.hη 0
  ηb := S.hη 1

/-- **`ρ = (t₁ⁿ/t₀ⁿ)_η = xⁿ`.** -/
theorem rho_data (n : ℕ) (hn : 1 ≤ n) : (S.data n hn).rho = S.x ^ n := by
  have hW : S.U 0 ⊓ S.U 1 ≤ nvOpen S.L (S.a 0) := inf_le_left
  have h1 : (S.data n hn).rho = germη (S.U 0 ⊓ S.U 1) (S.data n hn).ηab
      (ratio S.L (powSec S.L (S.a 0) n)
        (Stacks.SectionRingChartMap.le_nvOpen_powSec S.L (S.a 0) hW n hn)
        (powSec S.L (S.a 1) n)) := rfl
  rw [h1, ratio_powSec S.L (S.a 0) (S.a 1) hW n hn, map_pow]
  congr 1
  have h2 := germη_res (X := Y) (inf_le_left : S.U 0 ⊓ S.U 1 ≤ S.U 0) (S.data n hn).ηab
    (ratio S.L (S.a 0) le_rfl (S.a 1))
  rw [x, ← h2]
  congr 1
  exact (Chart.quot_res (M := natTensorPow S.L 1) (globalSection Y _ (S.a 0)) le_rfl
    inf_le_left (globalSection Y _ (S.a 1))).symm

theorem rho_data_inv (n : ℕ) (hn : 1 ≤ n) : (S.data n hn).rho⁻¹ = S.y ^ n := by
  rw [rho_data, S.y_eq_inv, inv_pow]

/-- **The image of `θ` on `L^{⊗n}`**: `{f ∈ O(U₀) | yⁿ f ∈ O(U₁)}`. -/
theorem mem_range_theta_iff (n : ℕ) (hn : 1 ≤ n) (f : Y.functionField) :
    f ∈ Set.range (S.data n hn).theta ↔
      f ∈ O (S.U 0) (S.hη 0) ∧ S.y ^ n * f ∈ O (S.U 1) (S.hη 1) := by
  rw [(S.data n hn).mem_range_theta_iff, rho_data_inv]
  rfl

/-! ### The `K`-structure -/

variable {K : Type u} [Field K] [Y.Over (Spec (.of K))]

/-- The `K`-algebra structure on `K(Y)` from the structure morphism (`functionFieldAlgebra`). -/
@[instance_reducible]
noncomputable def algK : Algebra K Y.functionField :=
  ((germη ⊤ trivial).comp (baseRingHom K Y)).toAlgebra

attribute [local instance] algK

theorem algebraMap_eq (c : K) :
    algebraMap K Y.functionField c = germη ⊤ trivial (baseRingHom K Y c) := rfl

theorem algebraMap_mem_O (U : Y.Opens) (hU : genericPoint Y ∈ U) (c : K) :
    algebraMap K Y.functionField c ∈ O U hU :=
  ⟨Y.presheaf.map (homOfLE le_top).op (baseRingHom K Y c), by rw [germη_res]; rfl⟩

/-- **`V n = {f | f ∈ O(U₀), yⁿ f ∈ O(U₁)}`.** -/
noncomputable def V (n : ℕ) : Submodule K Y.functionField where
  carrier := {f | f ∈ O (S.U 0) (S.hη 0) ∧ S.y ^ n * f ∈ O (S.U 1) (S.hη 1)}
  add_mem' {f g} hf hg := ⟨add_mem hf.1 hg.1, by rw [mul_add]; exact add_mem hf.2 hg.2⟩
  zero_mem' := ⟨zero_mem _, by rw [mul_zero]; exact zero_mem _⟩
  smul_mem' c f hf := by
    refine ⟨?_, ?_⟩
    · rw [Algebra.smul_def]
      exact mul_mem (algebraMap_mem_O _ _ c) hf.1
    · rw [Algebra.smul_def, mul_left_comm]
      exact mul_mem (algebraMap_mem_O _ _ c) hf.2

theorem mem_V {n : ℕ} {f : Y.functionField} :
    f ∈ S.V (K := K) n ↔ f ∈ O (S.U 0) (S.hη 0) ∧ S.y ^ n * f ∈ O (S.U 1) (S.hη 1) := Iff.rfl

/-- `θ` on `L^{⊗n}`, `K`-linearly. -/
noncomputable def thetaLin (n : ℕ) (hn : 1 ≤ n) :
    Γ(natTensorPow S.L (1 * n), ⊤) →ₗ[K] Y.functionField where
  toFun := (S.data n hn).theta
  map_add' := (S.data n hn).theta_add
  map_smul' c T := by
    rw [RingHom.id_apply, Algebra.smul_def]
    exact (S.data n hn).theta_rsmul (baseRingHom K Y c) T

theorem range_thetaLin (n : ℕ) (hn : 1 ≤ n) :
    LinearMap.range (S.thetaLin (K := K) n hn) = S.V n := by
  ext f
  rw [LinearMap.mem_range, mem_V, ← S.mem_range_theta_iff n hn]
  rfl

theorem thetaLin_injective (n : ℕ) (hn : 1 ≤ n) : Function.Injective (S.thetaLin (K := K) n hn) :=
  (S.data n hn).theta_injective

/-- **`V n ≅ Γ(L^{⊗n})`**, `K`-linearly. -/
noncomputable def equivV (n : ℕ) (hn : 1 ≤ n) :
    Γ(natTensorPow S.L (1 * n), ⊤) ≃ₗ[K] S.V (K := K) n :=
  (LinearEquiv.ofInjective (S.thetaLin (K := K) n hn) (S.thetaLin_injective n hn)).trans
    (LinearEquiv.ofEq _ _ (S.range_thetaLin (K := K) n hn))

/-- **The graded pencil.** -/
noncomputable def gradedPencil
    (hfin : ∀ n, 1 ≤ n → FiniteDimensional K Γ(natTensorPow S.L (1 * n), ⊤)) :
    GradedPencil K Y.functionField where
  x := S.x
  V := S.V
  x_ne_zero := S.x_ne_zero
  one_mem_zero := ⟨one_mem _, by rw [pow_zero, one_mul]; exact one_mem _⟩
  one_mem_one := ⟨one_mem _, by rw [pow_one, mul_one]; exact S.y_mem_O⟩
  x_mem := ⟨S.x_mem_O, by rw [pow_one, mul_comm, S.x_mul_y]; exact one_mem _⟩
  mul_le a b := by
    refine Submodule.mul_le.2 fun f hf g hg => ⟨mul_mem hf.1 hg.1, ?_⟩
    rw [show S.y ^ (a + b) * (f * g) = (S.y ^ a * f) * (S.y ^ b * g) by ring]
    exact mul_mem hf.2 hg.2
  finiteDimensional n := by
    have h1 : ∀ m, 1 ≤ m → FiniteDimensional K (S.V (K := K) m) := fun m hm => by
      have := hfin m hm
      exact LinearEquiv.finiteDimensional (S.equivV m hm)
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · have := h1 1 le_rfl
      refine Submodule.finiteDimensional_of_le (S₂ := S.V 1) fun f hf => ⟨hf.1, ?_⟩
      have := mul_mem hf.2 S.y_mem_O
      rwa [pow_zero, one_mul, mul_comm, ← pow_one S.y] at this
    · exact h1 n hn
  bpf n _ f hf hxf := ⟨hf.1, by
    have := hxf.2
    rwa [← mul_assoc, pow_succ, mul_assoc _ S.y, mul_comm S.y S.x, S.x_mul_y, mul_one] at this⟩

theorem gradedPencil_V (hfin) : (S.gradedPencil (K := K) hfin).V = S.V := rfl

theorem gradedPencil_x (hfin) : (S.gradedPencil (K := K) hfin).x = S.x := rfl

theorem finrank_V (n : ℕ) (hn : 1 ≤ n) :
    finrank K (S.V (K := K) n) = finrank K Γ(natTensorPow S.L (1 * n), ⊤) :=
  (S.equivV n hn).finrank_eq.symm

/-! ### Generation of the function field (ampleness) -/

theorem V_mono {m m' : ℕ} (h : m ≤ m') : S.V (K := K) m ≤ S.V m' := fun f hf => ⟨hf.1, by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [show S.y ^ (m + k) * f = S.y ^ k * (S.y ^ m * f) by ring]
  exact mul_mem (pow_mem S.y_mem_O k) hf.2⟩

/-- **`θ` of a section of `L^{⊗(m+1)}` is in `V (m+1)`.** -/
theorem theta_mem_V (n : ℕ) (hn : 1 ≤ n) (T : Γ(natTensorPow S.L (1 * n), ⊤)) :
    (S.data n hn).theta T ∈ S.V (K := K) n := by
  rw [← S.range_thetaLin n hn]
  exact ⟨T, rfl⟩

/-- **Every function on `U₀` has its germ in some `V m`** (Stacks 01PW for an ample `L`). -/
theorem exists_mem_V_of_ample (hL : Stacks.Ample.IsAmple Y S.L) (g : Γ(Y, S.U 0)) :
    ∃ m, germη (S.U 0) (S.hη 0) g ∈ S.V (K := K) m := by
  obtain ⟨z, rfl⟩ := (Stacks.SectionRingChartBijective.chartRingMap_bijective S.L hL le_rfl
    (S.a 0)).2 g
  obtain ⟨n, w, hw, rfl⟩ := HomogeneousLocalization.Away.mk_surjective (grading S.L)
    (Stacks.ExternalGrading.of_mem_summand 1 (S.a 0)) z
  refine ⟨n + 1, ?_⟩
  rw [Stacks.SectionRingChartMap.chartRingMap_mk, Stacks.SectionRingChartMap.chartFamily_apply,
    Stacks.SectionRingChartMap.numMapR_def, Stacks.SectionRingChartMap.ratioR_apply]
  exact S.theta_mem_V (n + 1) (Nat.le_add_left 1 n) (globalSection Y _
    ((DirectSum.of (powSections S.L) 1 (S.a 0) * w) (1 * (n + 1))))

/-- **`U₀ = Y_{t₀}` is affine** for `L` ample and `Y → Spec Γ(Y, 𝒪)` universally closed:
the canonical map `Y → Proj Γ_*(Y, L)` is an isomorphism (Stacks 0C6J) and `U₀` is the preimage
of the affine `D₊(t₀)`. -/
theorem isAffineOpen_U (hL : Stacks.Ample.IsAmple Y S.L) (huc : UniversallyClosed Y.toSpecΓ) :
    IsAffineOpen (S.U 0) := by
  have := Stacks.SectionRingProjMorphism.ToSpecZero.isIso_projHomOfIsAmple S.L hL huc
  have h := (Proj.isAffineOpen_basicOpen (grading S.L) _
    (Stacks.ExternalGrading.of_mem_summand 1 (S.a 0)) one_pos).preimage
      (Stacks.SectionRingProjMorphism.projHomOfIsAmple S.L hL)
  rwa [Stacks.SectionRingProjMorphism.projHomOfIsAmple_preimage_projBasicOpen S.L hL (S.a 0)
    one_pos] at h

/-- **Every `f ∈ K(Y)` is a quotient of two elements of one `V m`.** -/
theorem exists_div (hL : Stacks.Ample.IsAmple Y S.L) (huc : UniversallyClosed Y.toSpecΓ)
    (f : Y.functionField) :
    ∃ m, ∃ p ∈ S.V (K := K) m, ∃ q ∈ S.V (K := K) m, q ≠ 0 ∧ f = p / q := by
  have : Nonempty (S.U 0) := ⟨⟨genericPoint Y, S.hη 0⟩⟩
  have hfr := functionField_isFractionRing_of_isAffineOpen Y (S.U 0) (S.isAffineOpen_U hL huc)
  obtain ⟨p, q, hq, hpq⟩ := IsFractionRing.div_surjective (A := Γ(Y, S.U 0)) f
  have hp' : algebraMap Γ(Y, S.U 0) Y.functionField p = germη (S.U 0) (S.hη 0) p := rfl
  have hq' : algebraMap Γ(Y, S.U 0) Y.functionField q = germη (S.U 0) (S.hη 0) q := rfl
  obtain ⟨m₁, hm₁⟩ := S.exists_mem_V_of_ample (K := K) hL p
  obtain ⟨m₂, hm₂⟩ := S.exists_mem_V_of_ample (K := K) hL q
  refine ⟨max m₁ m₂, _, S.V_mono (le_max_left _ _) hm₁, _, S.V_mono (le_max_right _ _) hm₂,
    ?_, ?_⟩
  · rw [← hq']
    exact IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hq
  · rw [← hp', ← hq', hpq]

end Setup

end RamanujanWeil.Arith.Deuring.Geom.G7.Genus2.Pencil
