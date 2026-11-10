import RamanujanWeil.Arith.DeuringG7Genus2Model
import RamanujanWeil.Arith.DeuringG7Genus2ExistAlg
import RamanujanWeil.Arith.DeuringG7Genus2ExistRR

/-!
# A3-ord, G7-C: `Genus2ModelExistence` from two smaller named Props

`docs/ARITH_DEURING_G7_GENUS2.md`. The model step `Genus2ModelExistence K`
(`DeuringG7Genus2Model`) is reduced to

* **`Genus2CanonicalExistence K`**: a genus-2 curve carries an invertible module of degree 2
  with `h⁰ = 2` (the canonical bundle: `deg ω = 2g − 2`, `h⁰(ω) = g`, `ω` invertible); and
* **`Genus2PencilFunctionField K`**: an invertible `L` of degree 2 with `h⁰(L) = 2` and
  `h⁰(L^{⊗n}) = 2n − 1` (`n ≥ 2`) gives `IntegralPencilData` on the function field:
  `x = s₁/s₀`, the spaces `V n = H⁰(L^{⊗n})/s₀ⁿ ⊆ K(Y)`, `[K(Y) : K(x)] ≤ 2` (Stacks 0CCR) and
  integrality of `V 3` over `K[x]` and (after `/x³`) over `K[x⁻¹]` (finiteness of `φ`).

Proved here:

* `hasHypModel_of_pencilData`: `PencilData` on `K(Y)` ⇒ `HasHypModel s` (pure algebra,
  `DeuringG7Genus2ExistAlg`);
* `genus2ModelExistence_of_pencilExistence`;
* **`genus2ModelExistence_of_canonical_of_pencil`**: the two named Props imply
  `Genus2ModelExistence K`. The Riemann–Roch dimensions `h⁰(L^{⊗n}) = 2n − 1` consumed by
  `Genus2PencilFunctionField` are proved (`DeuringG7Genus2ExistRR.finrank_tensorPower_eq`), not
  assumed.
-/

universe u

open AlgebraicGeometry CategoryTheory Polynomial
open Stacks.SheafOfModules.Invertible (tensorPower)

namespace RamanujanWeil.Arith.Deuring.Geom.G7.Genus2.Exist

variable {K : Type u} [Field K]

theorem eqn_eq_quadEqn (m : HypModel K) : m.eqn = quadEqn m.hPoly m.fPoly := rfl

/-- **`PencilData` on the function field gives a hyperelliptic model.** -/
theorem hasHypModel_of_pencilData {Y : Scheme.{u}} (s : Y ⟶ Spec (.of K)) [IsCurve K s]
    (D : letI := functionFieldAlgebra K s; PencilData K Y.functionField) : HasHypModel s := by
  letI := functionFieldAlgebra K s
  obtain ⟨h, f, hh, hf, ⟨e⟩⟩ := D.exists_model
  obtain ⟨m, rfl, rfl⟩ := HypModel.exists_hypModel_eq h f hh hf
  exact ⟨m, ⟨e⟩⟩

/-- **The function-field form of the model step (named).** Every smooth proper geometrically
irreducible genus-2 curve has `PencilData` on its function field. -/
def Genus2PencilExistence (K : Type u) [Field K] : Prop :=
  ∀ (Y : Scheme.{u}) (s : Y ⟶ Spec (.of K)) [IsCurve K s] [Smooth s] [IsProper s]
    [GeometricallyIrreducible s], genus s = 2 →
      letI := functionFieldAlgebra K s; Nonempty (PencilData K Y.functionField)

theorem genus2ModelExistence_of_pencilExistence (hP : Genus2PencilExistence K) :
    Genus2ModelExistence K := by
  intro Y s _ _ _ _ hg
  obtain ⟨D⟩ := hP Y s hg
  exact hasHypModel_of_pencilData s D

/-- **The canonical bundle (named; Stacks 0BS6 (1)(2) + 0BY8).** A smooth proper geometrically
irreducible genus-2 curve carries an invertible module of degree `2g − 2 = 2` with
`h⁰ = g = 2`. -/
def Genus2CanonicalExistence (K : Type u) [Field K] : Prop :=
  ∀ (Y : Scheme.{u}) (s : Y ⟶ Spec (.of K)) [IsCurve K s] [Smooth s] [IsProper s]
    [GeometricallyIrreducible s], genus s = 2 →
      ∃ (L : Y.Modules) (_ : SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 L),
        invertibleCurveDegree K s (hdim s) L = 2 ∧
          Module.finrank K (cohomologyOverField K s L 0) = 2

/-- **The canonical pencil on the function field (named; Stacks 0CCP/0CCR + finiteness).**
Given an invertible `L` of degree 2 with `h⁰(L) = 2` and `h⁰(L^{⊗n}) = 2n − 1` for `n ≥ 2`, the
function field carries `IntegralPencilData`: `x = s₁/s₀` for a basis `s₀, s₁` of `H⁰(L)`,
`V n = {t/s₀ⁿ : t ∈ H⁰(L^{⊗n})}` (so `dim V 3 = 5`, `dim V 6 = 11` by the hypothesis),
`x` transcendental and `[K(Y) : K(x)] ≤ deg L = 2` (the pencil morphism `φ : Y → ℙ¹`,
Stacks 0CCR), and `V 3` integral over `K[x]` and, after dividing by `x³`, over `K[x⁻¹]`
(`φ` is finite, so `Y_{s₀} = φ⁻¹(𝔸¹)` and `Y_{s₁}` are finite over the two charts). -/
def Genus2PencilFunctionField (K : Type u) [Field K] : Prop :=
  ∀ (Y : Scheme.{u}) (s : Y ⟶ Spec (.of K)) [IsCurve K s] [Smooth s] [IsProper s]
    [GeometricallyIrreducible s], genus s = 2 →
      ∀ (L : Y.Modules) [SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 L],
        invertibleCurveDegree K s (hdim s) L = 2 →
        Module.finrank K (cohomologyOverField K s L 0) = 2 →
        (∀ n : ℕ, 2 ≤ n → (Module.finrank K (cohomologyOverField K s
          (tensorPower Y.toRingedSpace.presheaf (structureSheafRing Y.toRingedSpace).property L n)
            0) : ℤ) = 2 * n - 1) →
        letI := functionFieldAlgebra K s; Nonempty (IntegralPencilData K Y.functionField)

theorem genus2PencilExistence_of_canonical_of_pencil (hω : Genus2CanonicalExistence K)
    (hP : Genus2PencilFunctionField K) : Genus2PencilExistence K := by
  intro Y s _ _ _ _ hg
  obtain ⟨L, hL, hdeg, h0⟩ := hω Y s hg
  letI := functionFieldAlgebra K s
  obtain ⟨D⟩ := hP Y s hg L hdeg h0 (fun n hn => finrank_tensorPower_eq s hg L hdeg n hn)
  exact ⟨D.toPencilData⟩

/-- **`Genus2ModelExistence` from the canonical bundle and the canonical pencil.** -/
theorem genus2ModelExistence_of_canonical_of_pencil (hω : Genus2CanonicalExistence K)
    (hP : Genus2PencilFunctionField K) : Genus2ModelExistence K :=
  genus2ModelExistence_of_pencilExistence (genus2PencilExistence_of_canonical_of_pencil hω hP)

end RamanujanWeil.Arith.Deuring.Geom.G7.Genus2.Exist
