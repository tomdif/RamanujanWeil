import RamanujanWeil.Arith.DeuringG6AbVar
import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteLocallyFree.GenericRank

/-!
# A3-ord, G6: the degree of `A ⟶ A/G` is the order of `G`

If the finite locally free group scheme `G` has rank `r` over `k` (for `G = H_k` constant,
`r = #H`), then the quotient map `q : A ⟶ A/G` is finite locally free of rank `r`, and its
degree `[k(A) : k(A/G)]` (`AlgebraicGeometry.degreeOver`, Stacks 02NY) is `r`:

* `q` is finite locally free of rank `deg q` (Stacks, `isFiniteLocallyFreeOfRank_degreeOver`);
* its base change along `q` is `G ×_k A ⟶ A` (kernel pair), of rank `deg q`;
* that projection is also the base change of `G ⟶ Spec k`, of rank `r`;
* fibre ranks are well defined, so `deg q = r`.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory
  CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

universe u

namespace RamanujanWeil.Arith.Deuring.Geom.G6

/-- The rank of a finite locally free morphism is unique (over a nonempty target). -/
theorem rank_unique {X S : Scheme.{u}} (f : X ⟶ S) (r r' : ℕ)
    (h : Stacks.Morphisms.IsFiniteLocallyFreeOfRank f r)
    (h' : Stacks.Morphisms.IsFiniteLocallyFreeOfRank f r') (s : S) : r = r' :=
  (@Scheme.Modules.fiberRank_eq_of_isFiniteLocallyFreeOfRank _ _ r
      h.toIsFiniteLocallyFreeOfRank s).symm.trans
    (@Scheme.Modules.fiberRank_eq_of_isFiniteLocallyFreeOfRank _ _ r'
      h'.toIsFiniteLocallyFreeOfRank s)

variable {k : Type u} [Field k] [IsAlgClosed k]
  {A G : Over (Spec (.of k))} [GrpObj A] [GrpObj G] [ModObj G A] [IsCommMonObj A]
  {j : G ⟶ A} [IsMonHom j]

namespace TranslationQuotient

variable (Q : TranslationQuotient j)

/-- **`q : A ⟶ A/G` is finite locally free of rank `rank G`.** -/
theorem isFiniteLocallyFreeOfRank_q (r : ℕ) [Stacks.Morphisms.IsFiniteLocallyFreeOfRank G.hom r]
    [IsAbelianVariety k A] : Stacks.Morphisms.IsFiniteLocallyFreeOfRank Q.q.left r := by
  have : IsAbelianVariety k Q.B := Q.isAbelianVariety
  obtain ⟨hfin, -, -⟩ :=
    (Stacks.Morphisms.isFiniteLocallyFree_iff_isFinite_flat_locallyOfFinitePresentation
      Q.q.left).mp Q.finiteLocallyFree
  have := Q.finiteLocallyFree
  have := Q.surjective
  have h1 : Stacks.Morphisms.IsFiniteLocallyFreeOfRank Q.q.left (degreeOver Q.q.left) :=
    Stacks.Morphisms.isFiniteLocallyFreeOfRank_degreeOver _
  have h2 : Stacks.Morphisms.IsFiniteLocallyFreeOfRank (snd G A).left (degreeOver Q.q.left) :=
    Stacks.Morphisms.IsFiniteLocallyFreeOfRank.of_isPullback Q.isPullback
  have h3 : Stacks.Morphisms.IsFiniteLocallyFreeOfRank (snd G A).left r :=
    Stacks.Morphisms.IsFiniteLocallyFreeOfRank.of_isPullback
      (IsPullback.of_hasPullback G.hom A.hom)
  have hA : Nonempty A.left := inferInstance
  rw [rank_unique _ r (degreeOver Q.q.left) h3 h2 hA.some]
  exact h1

/-- **`deg (A ⟶ A/G) = rank G`.** -/
theorem degreeOver_q (r : ℕ) [Stacks.Morphisms.IsFiniteLocallyFreeOfRank G.hom r]
    [IsAbelianVariety k A] :
    haveI : IsAbelianVariety k Q.B := Q.isAbelianVariety
    haveI : IsFinite Q.q.left := ((Stacks.Morphisms.isFiniteLocallyFree_iff_isFinite_flat_locallyOfFinitePresentation
      Q.q.left).mp Q.finiteLocallyFree).1
    haveI := Q.surjective
    degreeOver Q.q.left = r := by
  have : IsAbelianVariety k Q.B := Q.isAbelianVariety
  have : IsFinite Q.q.left := ((Stacks.Morphisms.isFiniteLocallyFree_iff_isFinite_flat_locallyOfFinitePresentation
      Q.q.left).mp Q.finiteLocallyFree).1
  have := Q.surjective
  have := Q.isFiniteLocallyFreeOfRank_q r
  exact (Stacks.Morphisms.eq_degreeOver_of_isFiniteLocallyFreeOfRank _ r).symm

end TranslationQuotient

end RamanujanWeil.Arith.Deuring.Geom.G6
