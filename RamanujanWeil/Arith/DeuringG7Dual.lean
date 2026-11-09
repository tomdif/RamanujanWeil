import RamanujanWeil.Arith.DeuringMultDef
import RamanujanWeil.Arith.DeuringG4Hom

/-!
# A3-ord, G7-dual: interface and the cheap half

`docs/ARITH_DEURING_MULT.md` §2. Tate (`tate_exists_frobHom`) gives a nontrivial equivariant
homomorphism in **one** direction. The concrete isogeny relation (`DeuringMultDef.IsogStep`)
is symmetrized, so `mult ≤ 1` does **not** need the dual. The dual is needed downstream, inside
the per-class lattice interface (G8: `L(E) = Hom_π(E₀, E)` must have rank 2 for every `E` in
the class).

Proved here, axiom-clean:

* `frobHom_comp_ne_one`: a composite of nonzero homomorphisms of 1-dimensional abelian
  varieties is nonzero (`homDegree_comp`, G4);
* `frobHomNe_trans`: nontrivial equivariant homs compose;
* `tate_frobHomNe_both`: Tate + `FrobHomDual` ⇒ nontrivial equivariant homs **both** ways.

Named (not proved): **`FrobHomDual`**, existence of the dual isogeny for Frobenius Jacobians.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.MonObj

universe u

namespace RamanujanWeil.Arith.Deuring.Mult

open RamanujanWeil.Ihara RamanujanWeil.Arith.Deuring.Geom RamanujanWeil.Arith.Deuring.Geom.G7
  Stacks.Groupoids

section Comp

variable {k : Type u} [Field k] [IsAlgClosed k] {A B C : Over (Spec (.of k))} [GrpObj A] [GrpObj B] [GrpObj C]
  [AlgebraicGeometry.IsAbelianVariety k A] [AlgebraicGeometry.IsAbelianVariety k B]
  [AlgebraicGeometry.IsAbelianVariety k C]

/-- A composite of nonzero homomorphisms of one-dimensional abelian varieties is nonzero. -/
theorem frobHom_comp_ne_one (hA : abelianVarietyDimension A = 1)
    (hB : abelianVarietyDimension B = 1) (hC : abelianVarietyDimension C = 1)
    (α : A ⟶ B) (β : B ⟶ C) [IsMonHom α] [IsMonHom β] (hα : α ≠ 1) (hβ : β ≠ 1) :
    α ≫ β ≠ 1 := by
  intro h
  have hd := homDegree_comp hA hB hC α β
  rw [h, homDegree_one hC] at hd
  rcases Nat.mul_eq_zero.mp hd.symm with h0 | h0
  · exact hα ((homDegree_eq_zero_iff hA hB α).mp h0)
  · exact hβ ((homDegree_eq_zero_iff hB hC β).mp h0)

end Comp

section Frob

variable {K : Type u} [Field K] [Fintype K]

/-- Nontrivial equivariant homomorphisms of Frobenius Jacobians compose. -/
theorem frobHomNe_trans {W W' W'' : WeierstrassCurve K} [W.IsElliptic] [W'.IsElliptic]
    [W''.IsElliptic] {J : FrobeniusJacobian W} {J' : FrobeniusJacobian W'}
    {J'' : FrobeniusJacobian W''} (h₁ : FrobHomNe J J') (h₂ : FrobHomNe J' J'') :
    FrobHomNe J J'' := by
  obtain ⟨α, hα, hαπ, hα1⟩ := h₁
  obtain ⟨β, hβ, hβπ, hβ1⟩ := h₂
  refine ⟨α ≫ β, inferInstance, ?_, frobHom_comp_ne_one J.dim_eq J'.dim_eq J''.dim_eq α β hα1 hβ1⟩
  rw [Category.assoc, hβπ, ← Category.assoc, hαπ, Category.assoc]

/-- **G7-dual (named hypothesis).** A nontrivial `π`-equivariant homomorphism of Frobenius
Jacobians `J ⟶ J'` admits one `J' ⟶ J` (the dual isogeny). -/
def FrobHomDual : Prop :=
  ∀ (K : Type u) [Field K] [Fintype K] (W W' : WeierstrassCurve K) [W.IsElliptic]
    [W'.IsElliptic] (J : FrobeniusJacobian W) (J' : FrobeniusJacobian W'),
    FrobHomNe J J' → FrobHomNe J' J

/-- **Tate in both directions**, given `FrobHomDual`. -/
theorem tate_frobHomNe_both (hdual : FrobHomDual.{u}) {W W' : WeierstrassCurve K}
    [W.IsElliptic] [W'.IsElliptic] (J : FrobeniusJacobian W) (J' : FrobeniusJacobian W')
    (ht : traceOfFrob W' = traceOfFrob W) (hlt : traceOfFrob W ^ 2 < 4 * (Nat.card K : ℤ))
    (hfin : QuotientFiniteness (J.A ⊗ J'.A) (πA J.π J'.π)) :
    FrobHomNe J J' ∧ FrobHomNe J' J := by
  rcases tate_exists_frobHom J J' ht hlt hfin with h | h
  · exact ⟨h, hdual K W W' J J' h⟩
  · exact ⟨hdual K W' W J' J h, h⟩

end Frob

end RamanujanWeil.Arith.Deuring.Mult
