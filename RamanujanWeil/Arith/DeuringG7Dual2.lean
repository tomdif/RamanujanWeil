import RamanujanWeil.Arith.DeuringG7Dual
import StacksFrontier.Topology.Dimension.SpecializingSurjection

/-!
# A3-ord, G7-dual: the separable part, and reduction of `FrobHomDual` to radicial isogenies

`docs/ARITH_DEURING_G8.md` §1. Let `k` be algebraically closed and `A`, `B` one-dimensional
abelian varieties over `k`.

* `cancel_of_ne_one`: a nonzero homomorphism `α : A ⟶ B` is an epimorphism (it is dominant,
  `A` is reduced and every target is separated).
* `comm_of_comp_eq_zpow`, `comp_eq_zpow_symm`: **a dual is automatically equivariant**: if
  `α ≫ β = [n]` and `α` intertwines `π_A`, `π_B`, then so does `β`; and `β ≫ α = [n]`.
* **Separable part** (`exists_dual_of_radicialDual`): with `K = ker α(k)` (finite), the G6
  quotient `q : A → A/K`, `α = q ≫ ᾱ` and `[N] = q ≫ s` (`N = #K`), the induced `ᾱ` is
  injective on `k`-points, and `A/K` is again one-dimensional (`dim_eq_of_surjective`). A dual
  of `ᾱ` up to `[m]` then gives a dual of `α` up to `[Nm]`.
* **`RadicialDual`** (the named remaining input): a homomorphism of one-dimensional abelian
  varieties that is injective on `k`-points (a purely inseparable isogeny) is a left factor of
  some `[n]`, `n ≠ 0`. Mathematically `ᾱ ≅ F^r` (Stacks 0CCZ) and the cofactor is `V^r`.
* **`frobHomDual_of_radicialDual`**: `RadicialDual ⇒ FrobHomDual`, for arbitrary (abstract)
  Frobenius Jacobians.
* `homDualHyp_of_radicialDual`: `RadicialDual ⇒ HomDualHyp A B` for all `A`, `B`.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.MonObj

universe u

namespace RamanujanWeil.Arith.Deuring.Dual2

open RamanujanWeil.Ihara RamanujanWeil.Arith.Deuring.Geom RamanujanWeil.Arith.Deuring.Geom.G7
  RamanujanWeil.Arith.Deuring.Mult Stacks.Groupoids

section AV

variable {k : Type u} [Field k] [IsAlgClosed k]
  {A B C : Over (Spec (.of k))} [GrpObj A] [GrpObj B] [GrpObj C]
  [AlgebraicGeometry.IsAbelianVariety k A] [AlgebraicGeometry.IsAbelianVariety k B]
  [AlgebraicGeometry.IsAbelianVariety k C]

/-- **A nonzero homomorphism of one-dimensional abelian varieties is an epimorphism.** -/
theorem cancel_of_ne_one (hA : abelianVarietyDimension A = 1)
    (hB : abelianVarietyDimension B = 1) (α : A ⟶ B) [IsMonHom α] (hα : α ≠ 1)
    {f g : B ⟶ C} (h : α ≫ f = α ≫ g) : f = g := by
  have := isDominant_of_ne_one hA hB α hα
  have : IsReduced B.left := inferInstance
  apply Over.OverMorphism.ext
  exact ext_of_isDominant_of_isSeparated C.hom (by rw [Over.w f, Over.w g]) α.left
    (by rw [← Over.comp_left, h, Over.comp_left])

omit [IsAlgClosed k] [AlgebraicGeometry.IsAbelianVariety k A]
  [AlgebraicGeometry.IsAbelianVariety k B] in
/-- `[n]` commutes with every homomorphism. -/
theorem zpow_id_comp_comm (n : ℤ) (f : A ⟶ B) [IsMonHom f] :
    ((𝟙 A) ^ n) ≫ f = f ≫ ((𝟙 B) ^ n) := by
  rw [GrpObj.zpow_comp, GrpObj.comp_zpow, Category.id_comp, Category.comp_id]

/-- `[n] ≠ 0` for `n ≠ 0` in dimension one. -/
theorem zpow_id_ne_one (hA : abelianVarietyDimension A = 1) (n : ℤ) (hn : n ≠ 0) :
    (𝟙 A : A ⟶ A) ^ n ≠ 1 := by
  intro h
  have h1 := endDegree_zpow_id_eq_pow A n
  rw [h, endDegree_one hA, hA] at h1
  exact hn (pow_eq_zero_iff (by norm_num) |>.mp h1.symm)

/-- **A dual is equivariant.** -/
theorem comm_of_comp_eq_zpow (hA : abelianVarietyDimension A = 1)
    (hB : abelianVarietyDimension B = 1) (α : A ⟶ B) [IsMonHom α] (hα : α ≠ 1) (β : B ⟶ A)
    (n : ℤ) (hαβ : α ≫ β = (𝟙 A) ^ n) (πA : A ⟶ A) (πB : B ⟶ B) [IsMonHom πA]
    (hπ : α ≫ πB = πA ≫ α) : β ≫ πA = πB ≫ β := by
  apply cancel_of_ne_one hA hB α hα
  rw [← Category.assoc, hαβ, ← Category.assoc, hπ, Category.assoc, hαβ, zpow_id_comp_comm]

/-- **A dual is two-sided.** -/
theorem comp_eq_zpow_symm (hA : abelianVarietyDimension A = 1)
    (hB : abelianVarietyDimension B = 1) (α : A ⟶ B) [IsMonHom α] (hα : α ≠ 1) (β : B ⟶ A)
    (n : ℤ) (hαβ : α ≫ β = (𝟙 A) ^ n) : β ≫ α = (𝟙 B) ^ n := by
  apply cancel_of_ne_one hA hB α hα
  rw [← Category.assoc, hαβ, zpow_id_comp_comm]

/-- A nonzero homomorphism `A ⟶ B` of one-dimensional abelian varieties is surjective. -/
theorem surjective_of_ne_one (hA : abelianVarietyDimension A = 1)
    (hB : abelianVarietyDimension B = 1) (α : A ⟶ B) [IsMonHom α] (hα : α ≠ 1) :
    Surjective α.left := by
  have := isDominant_of_ne_one hA hB α hα
  have := isProper_left_hom α
  exact surjective_of_isDominant_of_isClosed_range _ α.left.isClosedMap.isClosed_range

omit [IsAlgClosed k] in
/-- A surjective morphism of abelian varieties does not increase the dimension. -/
theorem krullDim_le_of_surjective (f : A ⟶ B) (hf : Surjective f.left) :
    topologicalKrullDim B.left ≤ topologicalKrullDim A.left := by
  have := isProper_left_hom f
  exact Topology.topologicalKrullDim_le_of_surjective_of_specializingMap_or_generalizingMap _
    f.left.continuous hf.surj (Or.inl f.left.isClosedMap.specializingMap)

omit [IsAlgClosed k] in
/-- Abelian varieties related by surjections both ways have the same dimension. -/
theorem dim_eq_of_surjective (f : A ⟶ B) (g : B ⟶ A) (hf : Surjective f.left)
    (hg : Surjective g.left) : abelianVarietyDimension A = abelianVarietyDimension B := by
  have h1 := krullDim_le_of_surjective f hf
  have h2 := krullDim_le_of_surjective g hg
  rw [topologicalKrullDim_eq_abelianVarietyDimension,
    topologicalKrullDim_eq_abelianVarietyDimension] at h1 h2
  exact_mod_cast le_antisymm h2 h1

end AV

/-! ### The named radicial input and the reduction -/

/-- **RadicialDual (named hypothesis).** Over an algebraically closed field, a homomorphism
`f : B ⟶ A'` of one-dimensional abelian varieties which is injective on `k`-points (a purely
inseparable isogeny) is a left factor of a nonzero multiplication: `f ≫ h = [n]`, `n ≠ 0`.

Mathematically: `k(B) / f^* k(A')` is purely inseparable, so `f` is the `r`-fold relative
Frobenius up to isomorphism (Stacks 0CCZ, `existsUnique_nat_existsUnique_iso_nFoldFrobeniusTwist`)
and `h` is the Verschiebung, `n = p^r`. -/
def RadicialDual : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k] (B A' : Over (Spec (.of k))) [GrpObj B] [GrpObj A']
    [AlgebraicGeometry.IsAbelianVariety k B] [AlgebraicGeometry.IsAbelianVariety k A'],
    abelianVarietyDimension B = 1 → abelianVarietyDimension A' = 1 →
    ∀ (f : B ⟶ A') [IsMonHom f], (∀ x : 𝟙_ (Over (Spec (.of k))) ⟶ B, x ≫ f = 1 → x = 1) →
    ∃ (n : ℤ) (h : A' ⟶ B), n ≠ 0 ∧ IsMonHom h ∧ f ≫ h = (𝟙 B) ^ n

section Reduction

variable {k : Type u} [Field k] [IsAlgClosed k]
  {A B : Over (Spec (.of k))} [GrpObj A] [GrpObj B]
  [AlgebraicGeometry.IsAbelianVariety k A] [AlgebraicGeometry.IsAbelianVariety k B]

/-- **The separable part of the dual isogeny.** Given `RadicialDual`, every nonzero
homomorphism of one-dimensional abelian varieties `α : A ⟶ B` has a dual `β` with
`α ≫ β = [n]`, `n ≠ 0`. -/
theorem exists_dual_of_radicialDual (hR : RadicialDual.{u})
    (hA : abelianVarietyDimension A = 1) (hB : abelianVarietyDimension B = 1)
    (α : A ⟶ B) [IsMonHom α] (hα : α ≠ 1) :
    ∃ (n : ℤ) (β : B ⟶ A), n ≠ 0 ∧ IsMonHom β ∧ α ≫ β = (𝟙 A) ^ n := by
  classical
  let Γ : Subgroup (Pt A) := (IsMonHom.monoidHom α (𝟙_ (Over (Spec (.of k))))).ker
  have hmem : ∀ x : Pt A, x ∈ Γ ↔ x ≫ α = 1 := fun x => Iff.rfl
  have hfin : (pointKer α).Finite := by
    by_contra h; exact hα (eq_one_of_infinite_pointKer hA α h)
  haveI : Finite Γ := hfin.to_subtype
  obtain ⟨G⟩ := nonempty_glue Γ
  set N : ℤ := (Nat.card Γ : ℤ) with hNdef
  have hN : N ≠ 0 := by
    rw [hNdef, Nat.cast_ne_zero]; exact Nat.card_pos.ne'
  have hΓN : ∀ h ∈ Γ, h ^ N = 1 := fun h hh => by
    have h1 : (⟨h, hh⟩ : Γ) ^ Nat.card Γ = 1 := pow_card_eq_one'
    have h2 := congrArg Subtype.val h1
    rw [Subgroup.coe_pow, Subgroup.coe_one] at h2
    rw [hNdef, zpow_natCast, h2]
  have hαΓ : ∀ h ∈ Γ, h ≫ α = 1 := fun h hh => (hmem h).1 hh
  have hkN : ∀ h ∈ Γ, h ≫ (𝟙 A) ^ N = 1 := fun h hh => by
    rw [comp_zpow_id, hΓN h hh]
  set ab := G.desc α hαΓ
  have := G.desc_isMonHom α hαΓ
  have hq : G.q ≫ ab = α := G.q_desc α hαΓ
  set s := G.desc ((𝟙 A) ^ N) hkN
  have := G.desc_isMonHom ((𝟙 A) ^ N) hkN
  have hqs : G.q ≫ s = (𝟙 A) ^ N := G.q_desc _ hkN
  -- `A/Γ` is one-dimensional
  have hNA : (𝟙 A : A ⟶ A) ^ N ≠ 1 := zpow_id_ne_one hA N hN
  have hsurjN : Surjective ((𝟙 A : A ⟶ A) ^ N).left := surjective_of_ne_one hA hA _ hNA
  have hs : Surjective s.left := by
    have : Surjective (G.q ≫ s).left := by rw [hqs]; exact hsurjN
    rw [Over.comp_left] at this
    exact Surjective.of_comp G.q.left s.left
  have hdimB' : abelianVarietyDimension G.B = 1 :=
    (dim_eq_of_surjective G.q s G.surj hs).symm.trans hA
  -- `ᾱ` is injective on points
  have hinj : ∀ x : Pt G.B, x ≫ ab = 1 → x = 1 := by
    intro x hx
    obtain ⟨z, rfl⟩ := G.exists_comp_q_eq N hN hΓN x
    have hz : z ∈ Γ := by
      rw [hmem, ← hq, ← Category.assoc]; exact hx
    exact (G.ker z).2 hz
  obtain ⟨m, h, hm, hh, hfh⟩ := hR k G.B B hdimB' hB ab hinj
  refine ⟨N * m, h ≫ s, mul_ne_zero hN hm, inferInstance, ?_⟩
  calc α ≫ h ≫ s = G.q ≫ (ab ≫ h) ≫ s := by rw [← hq]; simp only [Category.assoc]
    _ = G.q ≫ ((𝟙 G.B) ^ m) ≫ s := by rw [hfh]
    _ = G.q ≫ s ≫ ((𝟙 A) ^ m) := by rw [zpow_id_comp_comm]
    _ = ((𝟙 A) ^ N) ≫ ((𝟙 A) ^ m) := by rw [← Category.assoc, hqs]
    _ = (𝟙 A) ^ (N * m) := by
      rw [GrpObj.comp_zpow, Category.comp_id, zpow_mul]

/-- **`RadicialDual ⇒ HomDualHyp`**: `Hom(A, B)` is zero or there is a nonzero `B ⟶ A`. -/
theorem homDualHyp_of_radicialDual (hR : RadicialDual.{u})
    (hA : abelianVarietyDimension A = 1) (hB : abelianVarietyDimension B = 1) :
    HomDualHyp A B := by
  by_cases h : ∀ α : A ⟶ B, IsMonHom α → α = 1
  · exact Or.inl h
  push Not at h
  obtain ⟨α, hαm, hα⟩ := h
  obtain ⟨n, β, hn, hβ, hαβ⟩ := exists_dual_of_radicialDual hR hA hB α hα
  refine Or.inr ⟨β, hβ, fun h1 => ?_⟩
  rw [h1, MonObj.comp_one] at hαβ
  exact zpow_id_ne_one hA n hn hαβ.symm

end Reduction

section Frob

variable {K : Type u} [Field K]

/-- **An equivariant dual of an equivariant nonzero homomorphism of Frobenius Jacobians**, given
`RadicialDual`, with `α ≫ β = [n]`. -/
theorem exists_frobDual (hR : RadicialDual.{u}) {W W' : WeierstrassCurve K} [W.IsElliptic]
    [W'.IsElliptic] (J : FrobeniusJacobian W) (J' : FrobeniusJacobian W') (α : J.A ⟶ J'.A)
    [IsMonHom α] (hαπ : α ≫ J'.π = J.π ≫ α) (hα : α ≠ 1) :
    ∃ (n : ℤ) (β : J'.A ⟶ J.A), n ≠ 0 ∧ IsMonHom β ∧ β ≫ J.π = J'.π ≫ β ∧ β ≠ 1 ∧
      α ≫ β = (𝟙 J.A) ^ n ∧ β ≫ α = (𝟙 J'.A) ^ n := by
  obtain ⟨n, β, hn, hβ, hαβ⟩ := exists_dual_of_radicialDual hR J.dim_eq J'.dim_eq α hα
  refine ⟨n, β, hn, hβ, comm_of_comp_eq_zpow J.dim_eq J'.dim_eq α hα β n hαβ J.π J'.π hαπ,
    fun h1 => ?_, hαβ, comp_eq_zpow_symm J.dim_eq J'.dim_eq α hα β n hαβ⟩
  rw [h1, MonObj.comp_one] at hαβ
  exact zpow_id_ne_one J.dim_eq n hn hαβ.symm

/-- **`RadicialDual ⇒ FrobHomDual`** (G7-dual, for arbitrary Frobenius Jacobians). -/
theorem frobHomDual_of_radicialDual (hR : RadicialDual.{u}) : FrobHomDual.{u} := by
  intro K _ _ W W' _ _ J J' ⟨α, hα, hαπ, hα1⟩
  obtain ⟨n, β, -, hβ, hβπ, hβ1, -⟩ := exists_frobDual hR J J' α hαπ hα1
  exact ⟨β, hβ, hβπ, hβ1⟩

end Frob

end RamanujanWeil.Arith.Deuring.Dual2
