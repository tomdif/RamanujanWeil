import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.FieldValuedPointCount

/-!
# M6, part 0: weighted closed-point sums are sums over `X(K)`

Let `k` be a finite field, `f : X ⟶ Spec k` locally of finite type and quasi-compact, and `K` a
finite extension of `k` of degree `n`. A `K`-valued point `g ∈ X(K) = Mor_k(Spec K, X)` determines
a closed point `pt g` of `X` (with `deg (pt g) ∣ n`), and over each closed point `x` with
`deg x ∣ n` there are exactly `deg x` such `g` (Stacks: `fieldValuedPointsEquiv`,
`natCard_residueEmbeddings`). Hence for every function `G` on closed points

`∑_{x closed, deg x ∣ n} deg x · G x = ∑_{g ∈ X(K)} G (pt g)`   (`finsum_closedPoints_eq`).

This is the weighted form of Stacks' `natCard_fieldValuedPoints` (which is the case `G = 1`).
-/

open CategoryTheory AlgebraicGeometry Stacks.EtaleCohomology

universe u

namespace RamanujanWeil.Ihara

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) (K : Type u) [Field K]
  [Algebra k K] [Finite K]

section

variable [LocallyOfFiniteType f]

/-- The closed point underlying a `K`-valued point. -/
noncomputable def fvpPoint (g : fieldValuedPoints f K) : closedPoints X :=
  ⟨(fieldValuedPointsEquiv f K g).1,
    (isClosed_and_dvd_of_residueEmbeddings f K _ (fieldValuedPointsEquiv f K g).2).1⟩

theorem residueDegree_fvpPoint_dvd (g : fieldValuedPoints f K) :
    residueDegree f (fvpPoint f K g).1 ∣ Module.finrank k K :=
  (isClosed_and_dvd_of_residueEmbeddings f K _ (fieldValuedPointsEquiv f K g).2).2

end

variable [Finite k] [LocallyOfFiniteType f] [QuasiCompact f]

omit [Finite k] [LocallyOfFiniteType f] [QuasiCompact f] in
/-- The residue degree of a closed point dividing `[K : k]` is nonzero. -/
theorem residueDegree_ne_zero_of_dvd {x : X} (h : residueDegree f x ∣ Module.finrank k K) :
    residueDegree f x ≠ 0 := by
  have hpos : 0 < Module.finrank k K := Module.finrank_pos
  intro h0
  rw [h0, zero_dvd_iff] at h
  omega

/-- The finset of closed points of degree dividing `[K : k]`. -/
noncomputable def dvdPoints : Finset (closedPoints X) :=
  (closedPointsDegreeLE f (Module.finrank k K)).filter
    (fun x => residueDegree f x.1 ∣ Module.finrank k K)

theorem mem_dvdPoints {x : closedPoints X} :
    x ∈ dvdPoints f K ↔ residueDegree f x.1 ∣ Module.finrank k K := by
  have hpos : 0 < Module.finrank k K := Module.finrank_pos
  rw [dvdPoints, Finset.mem_filter]
  simp only [closedPointsDegreeLE, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
  exact ⟨fun h => h.2, fun hd => ⟨Nat.le_of_dvd hpos hd, hd⟩⟩

/-- `X(K) ≃ Σ_{x ∈ dvdPoints} {k-embeddings κ(x) → K}`. -/
noncomputable def fvpEquivSigma :
    fieldValuedPoints f K ≃ Σ y : dvdPoints f K, residueEmbeddings f K y.1.1 :=
  (fieldValuedPointsEquiv f K).trans
    { toFun := fun c => ⟨⟨⟨c.1, (isClosed_and_dvd_of_residueEmbeddings f K c.1 c.2).1⟩,
          (mem_dvdPoints f K).2 (isClosed_and_dvd_of_residueEmbeddings f K c.1 c.2).2⟩, c.2⟩
      invFun := fun c => ⟨c.1.1.1, c.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

theorem fvpEquivSigma_fst (g : fieldValuedPoints f K) :
    ((fvpEquivSigma f K g).1 : closedPoints X) = fvpPoint f K g := rfl

theorem finite_residueEmbeddings (y : dvdPoints f K) : Finite (residueEmbeddings f K y.1.1) := by
  refine Nat.finite_of_card_ne_zero ?_
  have hd := (mem_dvdPoints f K).1 y.2
  rw [natCard_residueEmbeddings, if_pos hd]
  exact residueDegree_ne_zero_of_dvd f K hd

instance finite_fieldValuedPoints : Finite (fieldValuedPoints f K) := by
  have := finite_residueEmbeddings f K
  exact Finite.of_equiv _ (fvpEquivSigma f K).symm

/-- **Weighted point count.** For any `G` on closed points, with `n = [K : k]`,
`∑_{x closed, deg x ∣ n} deg x · G x = ∑_{g ∈ X(K)} G (pt g)`. -/
theorem finsum_closedPoints_eq {M : Type*} [NonAssocSemiring M] (G : closedPoints X → M) :
    ∑ᶠ (x : closedPoints X) (_ : residueDegree f x.1 ∣ Module.finrank k K),
        (residueDegree f x.1 : M) * G x =
      ∑ᶠ g : fieldValuedPoints f K, G (fvpPoint f K g) := by
  classical
  have := finite_residueEmbeddings f K
  letI : ∀ y : dvdPoints f K, Fintype (residueEmbeddings f K y.1.1) :=
    fun y => Fintype.ofFinite _
  letI : Fintype (fieldValuedPoints f K) := Fintype.ofFinite _
  rw [finsum_cond_eq_sum_of_cond_iff _ (t := dvdPoints f K) fun {x} _ => (mem_dvdPoints f K).symm,
    finsum_eq_sum_of_fintype,
    Fintype.sum_equiv (fvpEquivSigma f K) (fun g => G (fvpPoint f K g)) (fun c => G c.1.1)
      (fun g => rfl),
    Fintype.sum_sigma, ← Finset.sum_coe_sort (dvdPoints f K)]
  refine Finset.sum_congr rfl fun y _ => ?_
  show _ = ∑ _σ : residueEmbeddings f K y.1.1, G y.1
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Nat.card_eq_fintype_card,
    natCard_residueEmbeddings, if_pos ((mem_dvdPoints f K).1 y.2)]

end RamanujanWeil.Ihara
