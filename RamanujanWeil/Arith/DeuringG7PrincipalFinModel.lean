import RamanujanWeil.Arith.DeuringG7DGeomFamily
import RamanujanWeil.Arith.DeuringG7CJacBase
import RamanujanWeil.Arith.DeuringG7Genus2Pencil

/-!
# A3-ord, G7 `PrincipalFiniteness`: the Θ + J and C-descent interfaces

`docs/ARITH_DEURING_G7_PRINCIPAL.md`. Setting: `K = 𝔽_q`, `k̄ = 𝔽̄_q`, `F = Spec(x ↦ x^q)` on
`Spec k̄`.

* `frobSpec K`: the `q`-power Frobenius of `Spec k̄`, the base map of every twisted Frobenius
  used by G1 (`JacSite.Ψ_comp`).
* **`IsJacobianOf s Ψ σ B π_B`**: in every big fppf site containing the curve `X` and `Spec k̄`,
  the Jacobian `Pic⁰_{X/k̄}` (`jacobianGrp`) is isomorphic to `B` as a group object, with the
  Jacobian Frobenius induced by `Ψ` matching `π_B`. (The Jacobian does not depend on the site;
  quantifying over sites is what lets C-Jac compare two curves in one site.)
* **`Genus2JacModel K B π_B`**: a smooth projective genus-2 curve `X / k̄` with a twisted
  Frobenius `Ψ` (an automorphism of `X` over `F`) and a point, whose Jacobian is `(B, π_B)`.
* **`ProdJacModel K B π_B`**: two elliptic curves `W₁, W₂` over `K` with
  `(B, π_B) ≅ (J_{W₁} × J_{W₂}, π₁ × π₂)`.
* **`ThetaJacobianModel K`** (Θ + J, named): every principally polarized member `B_n` of a
  family as in `PrincipalFiniteness` has a genus-2 model or a product model.
* **`Genus2Curve K`**, **`Genus2FrobDescent K`** (C-descent, named): a genus-2 curve over `k̄`
  with a twisted Frobenius is the base change of a genus-2 curve over `K`, with `Ψ` becoming
  `id × Spec(frob)`.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory
  CartesianMonoidalCategory Stacks.Frobenius Stacks.PicardFunctor
open scoped CategoryTheory.MonObj

universe u

noncomputable section

namespace RamanujanWeil.Arith.Deuring.Geom.G7.PrincipalFin

open Stacks.Groupoids RamanujanWeil.Arith.Deuring.Geom RamanujanWeil.Arith.Deuring.Geom.G7
  RamanujanWeil.Arith.Deuring.Geom.G7.Fin RamanujanWeil.Ihara

attribute [local instance] RamanujanWeil.Ihara.fact_ringChar_prime

variable (K : Type u) [Field K] [Fintype K]

/-- The `q`-power Frobenius `F` of `Spec k̄`. -/
abbrev frobSpec : Spec (.of (AlgebraicClosure K)) ⟶ Spec (.of (AlgebraicClosure K)) :=
  absoluteFrobeniusPow (Spec (.of (AlgebraicClosure K))) (ringChar K)
    (Jac.JacSite.specIsInChar (k := K)) (cardExp K)

/-- **`(B, π_B)` is the Jacobian of `(X, Ψ)`**, in every big fppf site containing `X` and
`Spec k̄`: `Pic⁰_{X/k̄} ≅ B` as group objects, intertwining the Jacobian Frobenius of `Ψ` with
`π_B`. -/
def IsJacobianOf {X : Scheme.{u}} (s : X ⟶ Spec (.of (AlgebraicClosure K))) (Ψ : X ⟶ X)
    (hΨ : Ψ ≫ s = s ≫ frobSpec K) (σ : Spec (.of (AlgebraicClosure K)) ⟶ X)
    (hσ : σ ≫ s = 𝟙 _) (B : Over (Spec (.of (AlgebraicClosure K)))) [GrpObj B] (πB : B ⟶ B) :
    Prop :=
  ∀ (S : BigFppfSite.{u}) (hX : S.Contains X) (hk : S.Contains (Spec (.of (AlgebraicClosure K))))
    (f : S.obj hX ⟶ S.obj hk) (hf : S.inclusion.map f = s)
    [IsCurve (AlgebraicClosure K) (S.inclusion.map f)]
    [GeometricallyIrreducible (S.inclusion.map f)] [Smooth (S.inclusion.map f)]
    [IsProper (S.inclusion.map f)] [IsProjectiveVariety (AlgebraicClosure K) (S.inclusion.map f)]
    [(picardFunctor S hX hk f).IsRepresentable],
    ∃ e : (jacobianGrp S hX hk f σ (by rw [hf]; exact hσ)).X ≅ B, IsMonHom e.hom ∧
      e.hom ≫ πB = jacobianFrobenius S hX hk f (ringChar K) (Jac.JacSite.specIsInChar (k := K))
        (cardExp K) Ψ (by rw [hf]; exact hΨ) σ (by rw [hf]; exact hσ) ≫ e.hom

/-- **A genus-2 Jacobian model of `(B, π_B)`** (the output of Θ + J): a smooth projective
geometrically irreducible genus-2 curve `X / k̄` with a twisted Frobenius `Ψ` (an automorphism of
`X` lying over `F`) and a `k̄`-point `σ`, with `(B, π_B) ≅ (Pic⁰_X, F_Ψ)`. -/
structure Genus2JacModel (B : Over (Spec (.of (AlgebraicClosure K)))) [GrpObj B] (πB : B ⟶ B) where
  /-- The curve (in truth: the theta divisor, translated to be `Ψ`-stable). -/
  X : Scheme.{u}
  /-- Its structure morphism. -/
  s : X ⟶ Spec (.of (AlgebraicClosure K))
  isCurve : IsCurve (AlgebraicClosure K) s
  geomIrred : GeometricallyIrreducible s
  smooth : Smooth s
  proper : IsProper s
  projVar : IsProjectiveVariety (AlgebraicClosure K) s
  projMor : IsProjectiveMorphism s
  genus_eq : genus s = 2
  /-- The twisted Frobenius. -/
  Ψ : X ⟶ X
  isIso_Ψ : IsIso Ψ
  hΨ : Ψ ≫ s = s ≫ frobSpec K
  /-- A `k̄`-point. -/
  σ : Spec (.of (AlgebraicClosure K)) ⟶ X
  hσ : σ ≫ s = 𝟙 _
  /-- `(B, π_B)` is its Jacobian. -/
  jac : IsJacobianOf K s Ψ hΨ σ hσ B πB

/-- **A product model of `(B, π_B)`**: `(B, π_B) ≅ (J_{W₁} × J_{W₂}, π₁ × π₂)` for elliptic
curves `W₁, W₂` over `K` (for every choice of Jacobian sites). -/
structure ProdJacModel (B : Over (Spec (.of (AlgebraicClosure K)))) [GrpObj B] (πB : B ⟶ B) where
  /-- The first factor. -/
  W₁ : WeierstrassCurve K
  /-- The second factor. -/
  W₂ : WeierstrassCurve K
  ell₁ : W₁.IsElliptic
  ell₂ : W₂.IsElliptic
  /-- The product decomposition, with diagonal Frobenius. -/
  jac : ∀ (S₁ : Jac.JacSite W₁) (S₂ : Jac.JacSite W₂),
    ∃ e : S₁.J ⊗ S₂.J ≅ B, IsMonHom e.hom ∧ e.hom ≫ πB = (S₁.π ⊗ₘ S₂.π) ≫ e.hom

/-- **Θ + J (named).** In a family as in `PrincipalFiniteness`, every principally polarized
`B_n` is, with its Frobenius `π_n`, the Jacobian of a genus-2 curve over `k̄` with a twisted
Frobenius, or a product `J_{W₁} × J_{W₂}` of Jacobians of elliptic curves over `K` with the
diagonal Frobenius.

Mathematically: `Θ_n`, the zero scheme of the section of `L_n`, is an effective divisor with
`Θ_n² = 2`, `p_a(Θ_n) = 2` (adjunction, `K_B = 0`); irreducible ⇒ smooth genus 2, and
`Jac(Θ_n) ≅ B_n` (Albanese); reducible ⇒ `Θ_n = C₁ + C₂`, `B_n ≅ C₁ × C₂`. Frobenius preserves
the polarization class (all of `NS(B_n)` is Frobenius-stable in this ordinary isogeny class),
so a translate of `Θ_n` is `Ψ`-stable; in the product case `π_n` cannot swap the factors
(that forces `t = 0`, `DeuringG7ThetaSwap`) and the factors are elliptic curves over `K`. -/
def ThetaJacobianModel : Prop :=
  ∀ (W W' : WeierstrassCurve K) [W.IsElliptic] [W'.IsElliptic] (S : Jac.JacSite W)
    (S' : Jac.JacSite W'), traceOfFrob W' = traceOfFrob W →
    ¬ (ringChar K : ℤ) ∣ traceOfFrob W → traceOfFrob W ^ 2 < 4 * (Nat.card K : ℤ) →
    ∀ ℓ : ℕ, ℓ.Prime → ℓ ≠ 2 → IsUnit (ℓ : AlgebraicClosure K) →
      ∀ (v : ∀ n : ℕ, Tor S.J (ℓ ^ (n + 1)) ≃+ Tor S'.J (ℓ ^ (n + 1)))
        (hv : ∀ n x, v n (torAct S.π _ x) = torAct S'.π _ (v n x)) (G : ∀ n, Glue (Γ ℓ v n))
        (n : ℕ), DGeom.PrincipallyPolarized (AlgebraicClosure K) (G n).B →
        Nonempty (Genus2JacModel K (G n).B ((G n).πB S.π S'.π hv)) ∨
          Nonempty (ProdJacModel K (G n).B ((G n).πB S.π S'.π hv))

/-- A smooth proper geometrically irreducible curve of genus 2 over `K`. -/
structure Genus2Curve where
  /-- The curve. -/
  Y : Scheme.{u}
  /-- Its structure morphism. -/
  t : Y ⟶ Spec (.of K)
  isCurve : IsCurve K t
  smooth : Smooth t
  proper : IsProper t
  geomIrred : GeometricallyIrreducible t
  genus_eq : genus t = 2

/-- **C-descent (named).** A smooth projective geometrically irreducible genus-2 curve `X / k̄`
with a twisted Frobenius `Ψ` (an automorphism over `F`) is the base change of a genus-2 curve
`Y / K`, with `Ψ` corresponding to `id × Spec(frob)`.

Mathematically: Weil descent along `k̄ / 𝔽_q`. `X` and `Ψ` are defined over some `𝔽_{q^r}`, and
`Aut(X)` is finite (genus 2), so `Ψ` generates a continuous action of `Ẑ`; Galois descent for
the projective curve `X` gives `Y` (or: `k̄(X)^Ψ` is a function field over `𝔽_q` by Lang's
theorem for `GL_N`, and `Y` is its regular projective model). -/
def Genus2FrobDescent : Prop :=
  ∀ (X : Scheme.{u}) (s : X ⟶ Spec (.of (AlgebraicClosure K)))
    [IsCurve (AlgebraicClosure K) s] [GeometricallyIrreducible s] [Smooth s] [IsProper s],
    genus s = 2 → ∀ (Ψ : X ⟶ X) [IsIso Ψ], Ψ ≫ s = s ≫ frobSpec K →
      ∃ C : Genus2Curve K, ∃ β : X ≅ fieldBaseChange (Over.mk C.t) (AlgebraicClosure K),
        β.hom ≫ pullback.snd C.t (specAlgebraMap K (AlgebraicClosure K)) = s ∧
        β.hom ≫ galoisBaseChange (Over.mk C.t) (AlgebraicClosure K) (Jac.JacSite.frob (k := K)) =
          Ψ ≫ β.hom

end RamanujanWeil.Arith.Deuring.Geom.G7.PrincipalFin

end
