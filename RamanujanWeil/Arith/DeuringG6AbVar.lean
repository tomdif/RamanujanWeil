import RamanujanWeil.Arith.DeuringG6Quot
import StacksFrontier.AlgebraicGeometry.GroupScheme.OverField.AbelianVarietyProjective
import StacksFrontier.AlgebraicGeometry.GroupScheme.OverField.AbelianVarietyEquivalentDefinitions
import StacksFrontier.AlgebraicGeometry.GroupScheme.Subgroups.Separation
import StacksFrontier.AlgebraicGeometry.Morphisms.FppfSourceLocality
import StacksFrontier.AlgebraicGeometry.Descent.SchemeProperty.Reduced
import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.Reduced

/-!
# A3-ord, G6: the quotient of an abelian variety by a finite subgroup is an abelian variety

Let `k` be an algebraically closed field, `A` an abelian variety over `k` and `j : G ⟶ A` a
monomorphic homomorphism from a finite locally free group scheme `G` (any finite subgroup
scheme, étale or not) acting by translation. Then (`DeuringG6Quot`) the quotient `q : A ⟶ B`
exists, and here we show that **`B` is an abelian variety**:

* `B ⟶ Spec k` is locally of finite type: fppf-local on the source (Stacks 036O), and
  `q ≫ (B ⟶ Spec k) = (A ⟶ Spec k)`;
* `B` is separated: a group scheme over a field (Stacks 047L, via `isSeparated_iff_isClosedImmersion_one`);
* `B` is universally closed and quasi-compact over `k`: `q` is surjective;
* `B` is connected (image of `A`) and reduced (flat descent along `q`), hence geometrically
  reduced (`k` perfect);
* proper + connected + geometrically reduced group scheme ⇒ abelian variety (Stacks).

The main theorem `exists_isogeny_quotient` packages G6: `B`, the homomorphism `q`, `q` finite
locally free and surjective, `ker q = G`, and the universal property.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory
  CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

universe u

namespace RamanujanWeil.Arith.Deuring.Geom.G6

variable {k : Type u} [Field k] [IsAlgClosed k]
  {A G : Over (Spec (.of k))} [GrpObj A] [GrpObj G] [ModObj G A] [IsCommMonObj A]
  {j : G ⟶ A} [IsMonHom j]

namespace TranslationQuotient

variable (Q : TranslationQuotient j)

/-- **The quotient of an abelian variety by a finite subgroup scheme is an abelian variety.** -/
theorem isAbelianVariety [IsAbelianVariety k A] : IsAbelianVariety k Q.B := by
  obtain ⟨hflat, hqc, hsurj⟩ := Q.fqs
  obtain ⟨-, -, hlfp⟩ :=
    (Stacks.Morphisms.isFiniteLocallyFree_iff_isFinite_flat_locallyOfFinitePresentation
      Q.q.left).mp Q.finiteLocallyFree
  have hcomp : Q.q.left ≫ Q.B.hom = A.hom := Over.w Q.q
  -- locally of finite type: fppf local on the source
  have : LocallyOfFiniteType Q.B.hom := by
    have hR : Presieve.singleton Q.q.left ∈ Scheme.fppfPrecoverage Q.B.left :=
      (Scheme.singleton_mem_precoverage_iff (@Flat ⊓ @LocallyOfFinitePresentation)
        Q.q.left).mpr ⟨(surjective_iff _).mp hsurj, hflat, hlfp⟩
    refine MorphismProperty.IsLocalAtSource.of_forall_comp hR ?_
    rintro U g ⟨⟩
    rw [hcomp]
    infer_instance
  -- separated: a group scheme over a field
  have : IsSeparated Q.B.hom := by
    let : GrpObj (Over.mk Q.B.hom) :=
      GrpObj.ofIso (show Q.B ≅ Over.mk Q.B.hom from Over.isoMk (Iso.refl _))
    exact (isSeparated_iff_isClosedImmersion_one Q.B.hom).2 inferInstance
  have : UniversallyClosed Q.B.hom := by
    have : UniversallyClosed (Q.q.left ≫ Q.B.hom) := by rw [hcomp]; infer_instance
    exact UniversallyClosed.of_comp_surjective Q.q.left Q.B.hom
  have : CompactSpace A.left := (quasiCompact_iff_compactSpace A.hom).1 inferInstance
  have : CompactSpace Q.B.left := hsurj.surj.compactSpace Q.q.left.continuous
  have : QuasiCompact Q.B.hom := (quasiCompact_iff_compactSpace Q.B.hom).2 inferInstance
  have : IsProper Q.B.hom := ⟨⟩
  have : ConnectedSpace Q.B.left := hsurj.surj.connectedSpace Q.q.left.continuous
  have : IsReduced Q.B.left := isReduced_of_flat_of_surjective Q.q.left
  have : GeometricallyReduced Q.B.hom := geometricallyReduced_of_isReduced Q.B.hom
  exact isAbelianVariety_of_isProper_of_connectedSpace_of_geometricallyReduced k Q.B

end TranslationQuotient

end RamanujanWeil.Arith.Deuring.Geom.G6
