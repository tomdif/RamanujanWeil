import RamanujanWeil.Arith.DeuringG7Prod
import RamanujanWeil.Arith.DeuringG3Div

/-!
# A3-ord, G7: Tate's gluing argument, reduced to one finiteness statement

Let `E`, `E'` be abelian varieties over an algebraically closed field `k` with endomorphisms
`π`, `π'` (the Frobenii), `ℓ` a prime invertible in `k`, and suppose that for every `n` there is
a `π`-equivariant isomorphism `u_n : E(k)[ℓⁿ⁺¹] ≅ E'(k)[ℓⁿ⁺¹]` (`DeuringG7Alg` provides these for
elliptic curves with the same trace). Put `A = E × E'`, `Γ_n = graph(u_n) ⊆ A(k)` and
`B_n = A / Γ_n` (G6). Then:

* `exists_frobHom_of_quotientFiniteness`: **if two of the `(B_n, π_n)` are isomorphic** (which
  is what the named hypothesis `QuotientFiniteness A π_A` provides), there is a nontrivial
  `π`-equivariant homomorphism `E ⟶ E'` or `E' ⟶ E`.

Proof (`docs/ARITH_DEURING_G7.md` §3). Inside `B_n` the images `i_n(E)` and `i'_n(E')` meet in
exactly `#E[ℓⁿ⁺¹]` points (`card_inter`). The maps `p_n : B_n → E`, `p'_n : B_n → E'` induced by
`ℓⁿ⁺¹ · pr` have kernels `i'_n(E')`, `i_n(E)` on points (`exists_eq_of_comp_p'`). If there were
no nontrivial equivariant homomorphisms either way, an equivariant isomorphism `B_n ≅ B_m` would
send `i_n(E)` into `i_m(E)` and `i'_n(E')` into `i'_m(E')`, so `#E[ℓⁿ⁺¹] = #E[ℓᵐ⁺¹]`, i.e.
`n = m`. Everything is checked on `k`-points; surjectivity of `q_n` on points comes from the
universal property (`[ℓⁿ⁺¹]_A = q_n ≫ s_n`) and divisibility of `B_n(k)`.

No compactness / `ℓ`-adic limit argument is needed, and the isomorphisms `u_n` need not be
compatible in `n`.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory
  CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

universe u

namespace RamanujanWeil.Arith.Deuring.Geom.G7

open Stacks.Groupoids

variable {k : Type u} [Field k]

/-- `k`-points of `X`. -/
noncomputable abbrev Pt (X : Over (Spec (.of k))) := 𝟙_ (Over (Spec (.of k))) ⟶ X

/-- **The finiteness input of Tate's theorem (named hypothesis).** Among any sequence of quotients
`q_n : A → B_n` of `A` by finite `π_A`-stable subgroups `Γ_n ⊆ A(k)` (étale kernels: `q_n` is
finite locally free of rank `#Γ_n`), with the induced endomorphisms `π_n`, two are
`π`-equivariantly isomorphic.

For `A` an abelian variety over `𝔽̄_q` with the Frobenius `π_A` of an `𝔽_q`-structure this holds:
`Γ_n` is Galois-stable, so `(B_n, π_n)` is an `𝔽_q`-form, and there are only finitely many
`𝔽_q`-isomorphism classes of abelian varieties of a given dimension over `𝔽_q` (Zarhin's trick +
finiteness of `𝔽_q`-points of `𝒜_{g,1,N}`; Tate 1966 §2, Milne–Waterhouse). It is **false** for
general `π_A` (e.g. `π_A = 𝟙`), so it is a hypothesis about the specific Frobenius. -/
def QuotientFiniteness (A : Over (Spec (.of k))) [GrpObj A] (πA : A ⟶ A) : Prop :=
  ∀ (Γ : ℕ → Subgroup (Pt A)) (B : ℕ → Over (Spec (.of k))) [∀ n, GrpObj (B n)]
    (q : ∀ n, A ⟶ B n) (πB : ∀ n, B n ⟶ B n),
    (∀ n, Finite (Γ n)) → (∀ n, ∀ x ∈ Γ n, x ≫ πA ∈ Γ n) →
    (∀ n, AlgebraicGeometry.IsAbelianVariety k (B n)) → (∀ n, IsMonHom (q n)) → (∀ n, IsMonHom (πB n)) →
    (∀ n, q n ≫ πB n = πA ≫ q n) →
    (∀ n, Stacks.Morphisms.IsFiniteLocallyFreeOfRank (q n).left (Nat.card (Γ n))) →
    (∀ n, Surjective (q n).left) →
    (∀ n (x : Pt A), x ≫ q n = 1 ↔ x ∈ Γ n) →
    ∃ n m, n ≠ m ∧ ∃ e : B n ≅ B m, IsMonHom e.hom ∧ e.hom ≫ πB m = πB n ≫ e.hom

/-! ## Points of a product -/

section Product

variable {X Y : Over (Spec (.of k))} [GrpObj X] [GrpObj Y]

theorem lift_mul_lift (a b : Pt X) (c d : Pt Y) : lift a c * lift b d = lift (a * b) (c * d) := by
  apply CartesianMonoidalCategory.hom_ext
  · rw [MonObj.mul_comp, lift_fst, lift_fst, lift_fst]
  · rw [MonObj.mul_comp, lift_snd, lift_snd, lift_snd]

theorem lift_one_one : lift (1 : Pt X) (1 : Pt Y) = 1 := by
  apply CartesianMonoidalCategory.hom_ext
  · rw [lift_fst, MonObj.one_comp]
  · rw [lift_snd, MonObj.one_comp]

theorem lift_inv (a : Pt X) (c : Pt Y) : (lift a c)⁻¹ = lift a⁻¹ c⁻¹ := by
  rw [eq_comm, ← mul_eq_one_iff_eq_inv, lift_mul_lift, inv_mul_cancel, inv_mul_cancel,
    lift_one_one]

theorem lift_zpow (a : Pt X) (c : Pt Y) (n : ℤ) : (lift a c) ^ n = lift (a ^ n) (c ^ n) := by
  apply CartesianMonoidalCategory.hom_ext
  · rw [GrpObj.zpow_comp, lift_fst, lift_fst]
  · rw [GrpObj.zpow_comp, lift_snd, lift_snd]

omit [GrpObj X] [GrpObj Y] in
theorem eq_lift (z : Pt (X ⊗ Y)) : z = lift (z ≫ fst X Y) (z ≫ snd X Y) := by
  apply CartesianMonoidalCategory.hom_ext <;> simp

end Product

/-! ## Quotients with their universal property, packaged -/

section Glue

variable {A : Over (Spec (.of k))} [GrpObj A]

/-- A quotient `q : A → B` by a finite subgroup `Γ ⊆ A(k)`, with the data of G6. -/
structure Glue (Γ : Subgroup (Pt A)) where
  /-- The quotient. -/
  B : Over (Spec (.of k))
  /-- Its group structure. -/
  grp : GrpObj B
  /-- It is an abelian variety. -/
  ab : AlgebraicGeometry.IsAbelianVariety k B
  /-- The quotient map. -/
  q : A ⟶ B
  /-- The quotient map is a homomorphism. -/
  hom : IsMonHom q
  rank : Stacks.Morphisms.IsFiniteLocallyFreeOfRank q.left (Nat.card Γ)
  surj : Surjective q.left
  ker : ∀ x : Pt A, x ≫ q = 1 ↔ x ∈ Γ
  univ : ∀ (C : Over (Spec (.of k))) [GrpObj C] (α : A ⟶ C) [IsMonHom α],
    (∀ h ∈ Γ, h ≫ α = 1) → ∃! β : B ⟶ C, IsMonHom β ∧ q ≫ β = α

attribute [instance] Glue.grp Glue.ab Glue.hom

theorem nonempty_glue [IsAlgClosed k] [AlgebraicGeometry.IsAbelianVariety k A]
    (Γ : Subgroup (Pt A)) [Finite Γ] : Nonempty (Glue Γ) := by
  obtain ⟨B, g, a, q, hq, hr, hs, -, hk, hu⟩ := G6.exists_quotient_by_finite_subgroup' A Γ
  exact ⟨⟨B, g, a, q, hq, hr, hs, hk, hu⟩⟩

namespace Glue

variable {Γ : Subgroup (Pt A)} (G : Glue Γ)

/-- `q` is an epimorphism among homomorphisms. -/
theorem cancel {C : Over (Spec (.of k))} [GrpObj C] (β₁ β₂ : G.B ⟶ C) [IsMonHom β₁] [IsMonHom β₂]
    (h : G.q ≫ β₁ = G.q ≫ β₂) : β₁ = β₂ := by
  obtain ⟨β, -, huniq⟩ := G.univ C (G.q ≫ β₁) (fun x hx => by
    rw [← Category.assoc, (G.ker x).2 hx, MonObj.one_comp])
  rw [huniq β₁ ⟨inferInstance, rfl⟩, huniq β₂ ⟨inferInstance, h.symm⟩]

/-- The homomorphism induced on the quotient. -/
noncomputable def desc {C : Over (Spec (.of k))} [GrpObj C] (α : A ⟶ C) [IsMonHom α]
    (hα : ∀ h ∈ Γ, h ≫ α = 1) : G.B ⟶ C :=
  (G.univ C α hα).exists.choose

theorem desc_isMonHom {C : Over (Spec (.of k))} [GrpObj C] (α : A ⟶ C) [IsMonHom α]
    (hα : ∀ h ∈ Γ, h ≫ α = 1) : IsMonHom (G.desc α hα) :=
  (G.univ C α hα).exists.choose_spec.1

@[reassoc]
theorem q_desc {C : Over (Spec (.of k))} [GrpObj C] (α : A ⟶ C) [IsMonHom α]
    (hα : ∀ h ∈ Γ, h ≫ α = 1) : G.q ≫ G.desc α hα = α :=
  (G.univ C α hα).exists.choose_spec.2

/-- **`q` is surjective on `k`-points** when `Γ` is killed by some `N ≠ 0`. -/
theorem exists_comp_q_eq [IsAlgClosed k] [AlgebraicGeometry.IsAbelianVariety k A]
    (N : ℤ) (hN : N ≠ 0) (hΓ : ∀ h ∈ Γ, h ^ N = 1) (w : Pt G.B) :
    ∃ z : Pt A, z ≫ G.q = w := by
  have hk : ∀ h ∈ Γ, h ≫ (𝟙 A) ^ N = 1 := fun h hh => by
    rw [comp_zpow_id, hΓ h hh]
  let s := G.desc ((𝟙 A) ^ N) hk
  have := G.desc_isMonHom ((𝟙 A) ^ N) hk
  have hs : s ≫ G.q = (𝟙 G.B) ^ N := by
    apply G.cancel
    rw [G.q_desc_assoc, GrpObj.zpow_comp, GrpObj.comp_zpow, Category.id_comp, Category.comp_id]
  obtain ⟨v, rfl⟩ := exists_zpow_eq_point N hN w
  exact ⟨v ≫ s, by rw [Category.assoc, hs, comp_zpow_id]⟩

end Glue

end Glue

/-! ## Torsion points and the graph -/

section Core

variable [IsAlgClosed k] {E E' : Over (Spec (.of k))} [GrpObj E] [GrpObj E']
  [AlgebraicGeometry.IsAbelianVariety k E] [AlgebraicGeometry.IsAbelianVariety k E']

/-- `X(k)[N]`, written additively (as in Stacks). -/
noncomputable abbrev Tor (X : Over (Spec (.of k))) [GrpObj X] [AlgebraicGeometry.IsAbelianVariety k X]
    (N : ℕ) : AddSubgroup (Additive (Pt X)) :=
  AddSubgroup.torsionBy (Additive (Pt X)) (N : ℤ)

/-- The underlying point of a torsion point. -/
abbrev pt {X : Over (Spec (.of k))} [GrpObj X] [AlgebraicGeometry.IsAbelianVariety k X] {N : ℕ}
    (x : Tor X N) : Pt X := Additive.toMul (x : Additive (Pt X))

/-- The action of an endomorphism on `X(k)[N]`. -/
noncomputable def torAct {X : Over (Spec (.of k))} [GrpObj X]
    [AlgebraicGeometry.IsAbelianVariety k X] (π : X ⟶ X) [IsMonHom π] (N : ℕ) :
    Tor X N →+ Tor X N :=
  Stacks.AbelianGroup.torsionMap (IsMonHom.monoidHom π (𝟙_ (Over (Spec (.of k))))).toAdditive (N : ℤ)

theorem pt_torAct {X : Over (Spec (.of k))} [GrpObj X] [AlgebraicGeometry.IsAbelianVariety k X]
    (π : X ⟶ X) [IsMonHom π] {N : ℕ} (x : Tor X N) : pt (torAct π N x) = pt x ≫ π := rfl

theorem mem_tor_iff {X : Over (Spec (.of k))} [GrpObj X] [AlgebraicGeometry.IsAbelianVariety k X]
    (N : ℕ) (x : Pt X) : Additive.ofMul x ∈ Tor X N ↔ x ^ (N : ℤ) = 1 := by
  change ((N : ℤ) • Additive.ofMul x = 0) ↔ _
  rw [← ofMul_zpow, ofMul_eq_zero]

theorem pt_zpow {X : Over (Spec (.of k))} [GrpObj X] [AlgebraicGeometry.IsAbelianVariety k X]
    {N : ℕ} (x : Tor X N) : pt x ^ (N : ℤ) = 1 :=
  (mem_tor_iff N (pt x)).1 x.2

theorem pt_injective {X : Over (Spec (.of k))} [GrpObj X] [AlgebraicGeometry.IsAbelianVariety k X]
    {N : ℕ} : Function.Injective (pt : Tor X N → Pt X) := fun x y h =>
  Subtype.ext (Additive.toMul.injective h)

@[simp] theorem pt_zero {X : Over (Spec (.of k))} [GrpObj X]
    [AlgebraicGeometry.IsAbelianVariety k X] {N : ℕ} : pt (0 : Tor X N) = 1 := rfl

@[simp] theorem pt_add {X : Over (Spec (.of k))} [GrpObj X]
    [AlgebraicGeometry.IsAbelianVariety k X] {N : ℕ} (x y : Tor X N) :
    pt (x + y) = pt x * pt y := rfl

/-- The torsion point of a point killed by `N`. -/
abbrev torMk {X : Over (Spec (.of k))} [GrpObj X] [AlgebraicGeometry.IsAbelianVariety k X]
    {N : ℕ} (x : Pt X) (hx : x ^ (N : ℤ) = 1) : Tor X N :=
  ⟨Additive.ofMul x, (mem_tor_iff N x).2 hx⟩

variable {π : E ⟶ E} {π' : E' ⟶ E'} [IsMonHom π] [IsMonHom π']

variable (π π') in
/-- The Frobenius `π × π'` of `E × E'`. -/
noncomputable def πA : E ⊗ E' ⟶ E ⊗ E' := lift (fst E E' ≫ π) (snd E E' ≫ π')

instance : IsMonHom (πA π π') := by unfold πA; infer_instance

variable (π π') in
theorem lift_πA (a : Pt E) (b : Pt E') : lift a b ≫ πA π π' = lift (a ≫ π) (b ≫ π') := by
  apply CartesianMonoidalCategory.hom_ext <;> simp [πA]

/-- `x ↦ (x, 0)`. -/
noncomputable def ι₁ : E ⟶ E ⊗ E' := lift (𝟙 E) 1
/-- `y ↦ (0, y)`. -/
noncomputable def ι₂ : E' ⟶ E ⊗ E' := lift 1 (𝟙 E')

instance : IsMonHom (ι₁ (E := E) (E' := E')) := by unfold ι₁; infer_instance
instance : IsMonHom (ι₂ (E := E) (E' := E')) := by unfold ι₂; infer_instance

theorem comp_ι₁ (x : Pt E) : x ≫ ι₁ (E' := E') = lift x 1 := by
  rw [ι₁, comp_lift, Category.comp_id, MonObj.comp_one]

theorem comp_ι₂ (y : Pt E') : y ≫ ι₂ (E := E) = lift 1 y := by
  rw [ι₂, comp_lift, Category.comp_id, MonObj.comp_one]

variable (π π') in
theorem ι₁_πA : ι₁ ≫ πA π π' = π ≫ ι₁ := by
  apply CartesianMonoidalCategory.hom_ext <;>
    simp [πA, ι₁, MonObj.one_comp, MonObj.comp_one]

variable (π π') in
theorem ι₂_πA : ι₂ ≫ πA π π' = π' ≫ ι₂ := by
  apply CartesianMonoidalCategory.hom_ext <;>
    simp [πA, ι₂, MonObj.one_comp, MonObj.comp_one]

variable (ℓ : ℕ) (u : ∀ n : ℕ, Tor E (ℓ ^ (n + 1)) ≃+ Tor E' (ℓ ^ (n + 1)))

/-- The graph of `u_n`, as a homomorphism into `(E × E')(k)`. -/
noncomputable def grHom (n : ℕ) : Multiplicative (Tor E (ℓ ^ (n + 1))) →* Pt (E ⊗ E') where
  toFun x := lift (pt x.toAdd) (pt (u n x.toAdd))
  map_one' := by simp [lift_one_one]
  map_mul' x y := by simp [lift_mul_lift]

/-- `Γ_n = graph(u_n) ⊆ (E × E')(k)`. -/
noncomputable def Γ (n : ℕ) : Subgroup (Pt (E ⊗ E')) := (grHom ℓ u n).range

variable {ℓ u} in
theorem mem_Γ {n : ℕ} {z : Pt (E ⊗ E')} :
    z ∈ Γ ℓ u n ↔ ∃ x : Tor E (ℓ ^ (n + 1)), lift (pt x) (pt (u n x)) = z :=
  ⟨fun ⟨x, hx⟩ => ⟨x.toAdd, hx⟩, fun ⟨x, hx⟩ => ⟨Multiplicative.ofAdd x, hx⟩⟩

variable {ℓ u} in
theorem lift_mem_Γ {n : ℕ} (x : Tor E (ℓ ^ (n + 1))) : lift (pt x) (pt (u n x)) ∈ Γ ℓ u n :=
  mem_Γ.2 ⟨x, rfl⟩

theorem finite_tor (hℓ : ℓ.Prime) (hℓk : IsUnit (ℓ : k)) (n : ℕ) :
    Finite (Tor E (ℓ ^ (n + 1))) := by
  have : NeZero (ℓ ^ (n + 1)) := ⟨pow_ne_zero _ hℓ.ne_zero⟩
  obtain ⟨e⟩ := nonempty_torsionBy_pow_addEquiv E ℓ hℓk (n + 1)
  exact Finite.of_equiv _ e.symm.toEquiv

theorem natCard_tor (hℓ : ℓ.Prime) (hℓk : IsUnit (ℓ : k)) (n : ℕ) :
    Nat.card (Tor E (ℓ ^ (n + 1))) = (ℓ ^ (n + 1)) ^ (2 * abelianVarietyDimension E) := by
  have : NeZero (ℓ ^ (n + 1)) := ⟨pow_ne_zero _ hℓ.ne_zero⟩
  obtain ⟨e⟩ := nonempty_torsionBy_pow_addEquiv E ℓ hℓk (n + 1)
  rw [Nat.card_congr e.toEquiv, Nat.card_fun, Nat.card_zmod, Nat.card_eq_fintype_card,
    Fintype.card_fin]

theorem finite_Γ (hℓ : ℓ.Prime) (hℓk : IsUnit (ℓ : k)) (n : ℕ) : Finite (Γ ℓ u n) := by
  have := finite_tor (E := E) ℓ hℓ hℓk n
  exact Finite.of_surjective (fun x => (⟨grHom ℓ u n x, x, rfl⟩ : Γ ℓ u n))
    (fun ⟨_, x, rfl⟩ => ⟨x, rfl⟩)

theorem πA_mem_Γ (hu : ∀ n x, u n (torAct π _ x) = torAct π' _ (u n x)) (n : ℕ) :
    ∀ z ∈ Γ ℓ u n, z ≫ πA π π' ∈ Γ ℓ u n := by
  intro z hz
  obtain ⟨x, rfl⟩ := mem_Γ.1 hz
  rw [lift_πA]
  refine mem_Γ.2 ⟨torAct π _ x, ?_⟩
  rw [hu, pt_torAct, pt_torAct]

theorem zpow_mem_Γ {n : ℕ} : ∀ z ∈ Γ ℓ u n, z ^ ((ℓ ^ (n + 1) : ℕ) : ℤ) = 1 := by
  intro z hz
  obtain ⟨x, rfl⟩ := mem_Γ.1 hz
  rw [lift_zpow, pt_zpow, pt_zpow, lift_one_one]

/-! ## The maps attached to one quotient `B_n = (E × E') / Γ_n` -/

variable {ℓ u} {n : ℕ} (G : Glue (Γ ℓ u n))

/-- `i_n : E → B_n`. -/
noncomputable def Glue.i : E ⟶ G.B := ι₁ ≫ G.q
/-- `i'_n : E' → B_n`. -/
noncomputable def Glue.i' : E' ⟶ G.B := ι₂ ≫ G.q

instance : IsMonHom G.i := by unfold Glue.i; infer_instance
instance : IsMonHom G.i' := by unfold Glue.i'; infer_instance

theorem kill_p : ∀ h ∈ Γ ℓ u n, h ≫ (fst E E' ≫ (𝟙 E) ^ ((ℓ ^ (n + 1) : ℕ) : ℤ)) = 1 := by
  intro h hh
  obtain ⟨x, rfl⟩ := mem_Γ.1 hh
  rw [← Category.assoc, lift_fst, comp_zpow_id, pt_zpow]

theorem kill_p' : ∀ h ∈ Γ ℓ u n, h ≫ (snd E E' ≫ (𝟙 E') ^ ((ℓ ^ (n + 1) : ℕ) : ℤ)) = 1 := by
  intro h hh
  obtain ⟨x, rfl⟩ := mem_Γ.1 hh
  rw [← Category.assoc, lift_snd, comp_zpow_id, pt_zpow]

/-- `p_n : B_n → E`, `q_n ≫ p_n = ℓⁿ⁺¹ · pr₁`. -/
noncomputable def Glue.p : G.B ⟶ E := G.desc _ kill_p
/-- `p'_n : B_n → E'`, `q_n ≫ p'_n = ℓⁿ⁺¹ · pr₂`. -/
noncomputable def Glue.p' : G.B ⟶ E' := G.desc _ kill_p'

instance : IsMonHom G.p := G.desc_isMonHom _ _
instance : IsMonHom G.p' := G.desc_isMonHom _ _

variable (π π') in
/-- The Frobenius `π_n` of `B_n`. -/
noncomputable def Glue.πB (hu : ∀ n x, u n (torAct π _ x) = torAct π' _ (u n x)) : G.B ⟶ G.B :=
  G.desc (πA π π' ≫ G.q) (fun h hh => by
    rw [← Category.assoc, (G.ker _).2 (πA_mem_Γ ℓ u hu n h hh)])

variable (hu : ∀ n x, u n (torAct π _ x) = torAct π' _ (u n x))

instance : IsMonHom (G.πB π π' hu) := G.desc_isMonHom _ _

theorem Glue.q_πB : G.q ≫ G.πB π π' hu = πA π π' ≫ G.q := G.q_desc _ _

theorem Glue.i_πB : G.i ≫ G.πB π π' hu = π ≫ G.i := by
  rw [Glue.i, Category.assoc, G.q_πB, ← Category.assoc, ι₁_πA, Category.assoc]

theorem Glue.i'_πB : G.i' ≫ G.πB π π' hu = π' ≫ G.i' := by
  rw [Glue.i', Category.assoc, G.q_πB, ← Category.assoc, ι₂_πA, Category.assoc]

theorem Glue.p_comm : G.p ≫ π = G.πB π π' hu ≫ G.p := by
  apply G.cancel
  rw [Glue.p, G.q_desc_assoc, ← Category.assoc G.q, G.q_πB, Category.assoc (πA π π') G.q,
    G.q_desc]
  simp only [Category.assoc]
  rw [GrpObj.zpow_comp, Category.id_comp, ← Category.assoc (πA π π'), πA, lift_fst,
    Category.assoc]
  simp only [GrpObj.comp_zpow, Category.comp_id]

theorem Glue.p'_comm : G.p' ≫ π' = G.πB π π' hu ≫ G.p' := by
  apply G.cancel
  rw [Glue.p', G.q_desc_assoc, ← Category.assoc G.q, G.q_πB, Category.assoc (πA π π') G.q,
    G.q_desc]
  simp only [Category.assoc]
  rw [GrpObj.zpow_comp, Category.id_comp, ← Category.assoc (πA π π'), πA, lift_snd,
    Category.assoc]
  simp only [GrpObj.comp_zpow, Category.comp_id]

/-! ## Points of `B_n` -/

theorem Glue.exists_pt (hℓ : ℓ.Prime) (w : Pt G.B) : ∃ z : Pt (E ⊗ E'), z ≫ G.q = w := by
  have := isAbelianVariety_tensor E E'
  exact G.exists_comp_q_eq _ (by exact_mod_cast (pow_ne_zero _ hℓ.ne_zero)) (zpow_mem_Γ ℓ u)
    w

theorem Glue.comp_q_eq_one {z : Pt (E ⊗ E')} : z ≫ G.q = 1 ↔ z ∈ Γ ℓ u n := G.ker z

/-- **Kernel of `p'_n` on points is `i_n(E(k))`.** -/
theorem Glue.exists_eq_of_comp_p' (hℓ : ℓ.Prime) (w : Pt G.B) (hw : w ≫ G.p' = 1) :
    ∃ x : Pt E, w = x ≫ G.i := by
  obtain ⟨z, rfl⟩ := G.exists_pt hℓ w
  have hy : (z ≫ snd E E') ^ ((ℓ ^ (n + 1) : ℕ) : ℤ) = 1 := by
    rw [← hw, Category.assoc, Glue.p', G.q_desc, ← Category.assoc, comp_zpow_id]
  set x₀ := (u n).symm (torMk _ hy)
  have hux : pt (u n x₀) = z ≫ snd E E' := by simp only [x₀, AddEquiv.apply_symm_apply]; rfl
  refine ⟨(z ≫ fst E E') * (pt x₀)⁻¹, ?_⟩
  have hz : z = ((z ≫ fst E E') * (pt x₀)⁻¹) ≫ ι₁ * lift (pt x₀) (pt (u n x₀)) := by
    rw [comp_ι₁, lift_mul_lift, inv_mul_cancel_right, one_mul, hux, ← eq_lift]
  conv_lhs => rw [hz]
  rw [MonObj.mul_comp, (G.comp_q_eq_one).2 (lift_mem_Γ x₀), mul_one, Glue.i, Category.assoc]

/-- **Kernel of `p_n` on points is `i'_n(E'(k))`.** -/
theorem Glue.exists_eq_of_comp_p (hℓ : ℓ.Prime) (w : Pt G.B) (hw : w ≫ G.p = 1) :
    ∃ y : Pt E', w = y ≫ G.i' := by
  obtain ⟨z, rfl⟩ := G.exists_pt hℓ w
  have hx : (z ≫ fst E E') ^ ((ℓ ^ (n + 1) : ℕ) : ℤ) = 1 := by
    rw [← hw, Category.assoc, Glue.p, G.q_desc, ← Category.assoc, comp_zpow_id]
  set x₀ := torMk (N := ℓ ^ (n + 1)) _ hx
  refine ⟨(z ≫ snd E E') * (pt (u n x₀))⁻¹, ?_⟩
  have hz : z = ((z ≫ snd E E') * (pt (u n x₀))⁻¹) ≫ ι₂ * lift (pt x₀) (pt (u n x₀)) := by
    rw [comp_ι₂, lift_mul_lift, inv_mul_cancel_right, one_mul]
    exact eq_lift z
  conv_lhs => rw [hz]
  rw [MonObj.mul_comp, (G.comp_q_eq_one).2 (lift_mem_Γ x₀), mul_one, Glue.i', Category.assoc]

/-- `i_n` is injective on points. -/
theorem Glue.i_injective {x₁ x₂ : Pt E} (h : x₁ ≫ G.i = x₂ ≫ G.i) : x₁ = x₂ := by
  have h1 : lift (x₁ * x₂⁻¹) (1 : Pt E') ≫ G.q = 1 := by
    rw [← comp_ι₁, MonObj.mul_comp, GrpObj.inv_comp, MonObj.mul_comp, GrpObj.inv_comp,
      Category.assoc, Category.assoc]
    change x₁ ≫ G.i * (x₂ ≫ G.i)⁻¹ = 1
    rw [h, mul_inv_cancel]
  obtain ⟨x₀, hx₀⟩ := mem_Γ.1 ((G.comp_q_eq_one).1 h1)
  have h2 : pt (u n x₀) = 1 := by simpa using congrArg (· ≫ snd E E') hx₀
  have h3 : u n x₀ = 0 := pt_injective (by rw [h2]; rfl)
  have h4 : x₀ = 0 := by simpa using h3
  have h5 := congrArg (· ≫ fst E E') hx₀
  simp only [lift_fst, h4, pt_zero] at h5
  exact mul_inv_eq_one.1 h5.symm

/-- **`i_n(E) ∩ i'_n(E') = i_n(E[ℓⁿ⁺¹])` on points.** -/
theorem Glue.mem_inter_iff (w : Pt G.B) :
    ((∃ x : Pt E, w = x ≫ G.i) ∧ (∃ y : Pt E', w = y ≫ G.i')) ↔
      ∃ x : Tor E (ℓ ^ (n + 1)), w = pt x ≫ G.i := by
  constructor
  · rintro ⟨⟨x, rfl⟩, ⟨y, hy⟩⟩
    have h1 : lift x y⁻¹ ≫ G.q = 1 := by
      have : lift x y⁻¹ = x ≫ ι₁ * (y ≫ ι₂)⁻¹ := by
        rw [comp_ι₁, comp_ι₂, lift_inv, lift_mul_lift, inv_one, mul_one, one_mul]
      rw [this, MonObj.mul_comp, GrpObj.inv_comp, Category.assoc, Category.assoc]
      change x ≫ G.i * (y ≫ G.i')⁻¹ = 1
      rw [hy, mul_inv_cancel]
    obtain ⟨x₀, hx₀⟩ := mem_Γ.1 ((G.comp_q_eq_one).1 h1)
    have := congrArg (· ≫ fst E E') hx₀
    simp only [lift_fst] at this
    exact ⟨x₀, by rw [this]⟩
  · rintro ⟨x, rfl⟩
    refine ⟨⟨_, rfl⟩, ⟨(pt (u n x))⁻¹, ?_⟩⟩
    have : pt x ≫ ι₁ = lift (pt x) (pt (u n x)) * (pt (u n x))⁻¹ ≫ ι₂ := by
      rw [comp_ι₁, comp_ι₂, lift_mul_lift, mul_one, mul_inv_cancel]
    rw [Glue.i, Glue.i', ← Category.assoc, this, MonObj.mul_comp,
      (G.comp_q_eq_one).2 (lift_mem_Γ x), one_mul, Category.assoc]

/-! ## The counting argument -/

variable {m : ℕ} (G₂ : Glue (Γ ℓ u m))

/-- If there are no nontrivial equivariant homomorphisms `E → E'`, `E' → E`, an equivariant
homomorphism `f : B_n → B_m` with a left inverse injects `E[ℓⁿ⁺¹]` into `E[ℓᵐ⁺¹]`. -/
theorem card_tor_le (hℓ : ℓ.Prime) (hℓk : IsUnit (ℓ : k))
    (h1 : ∀ α : E ⟶ E', IsMonHom α → α ≫ π' = π ≫ α → α = 1)
    (h2 : ∀ β : E' ⟶ E, IsMonHom β → β ≫ π = π' ≫ β → β = 1)
    (f : G.B ⟶ G₂.B) [IsMonHom f] (g : G₂.B ⟶ G.B) (hfg : f ≫ g = 𝟙 _)
    (hf : f ≫ G₂.πB π π' hu = G.πB π π' hu ≫ f) :
    Nat.card (Tor E (ℓ ^ (n + 1))) ≤ Nat.card (Tor E (ℓ ^ (m + 1))) := by
  have := finite_tor (E := E) ℓ hℓ hℓk m
  have hα : G.i ≫ f ≫ G₂.p' = 1 := h1 _ inferInstance (by
    rw [Category.assoc, Category.assoc, G₂.p'_comm hu, ← Category.assoc f, hf,
      Category.assoc, ← Category.assoc G.i, G.i_πB hu, Category.assoc])
  have hβ : G.i' ≫ f ≫ G₂.p = 1 := h2 _ inferInstance (by
    rw [Category.assoc, Category.assoc, G₂.p_comm hu, ← Category.assoc f, hf,
      Category.assoc, ← Category.assoc G.i', G.i'_πB hu, Category.assoc])
  have key : ∀ x : Tor E (ℓ ^ (n + 1)), ∃ x' : Tor E (ℓ ^ (m + 1)),
      (pt x ≫ G.i) ≫ f = pt x' ≫ G₂.i := by
    intro x
    obtain ⟨⟨-, -⟩, ⟨y, hy⟩⟩ := (G.mem_inter_iff (pt x ≫ G.i)).2 ⟨x, rfl⟩
    refine (G₂.mem_inter_iff _).1 ⟨?_, ?_⟩
    · apply G₂.exists_eq_of_comp_p' hℓ
      simp only [Category.assoc]
      rw [hα, MonObj.comp_one]
    · apply G₂.exists_eq_of_comp_p hℓ
      rw [hy]
      simp only [Category.assoc]
      rw [hβ, MonObj.comp_one]
  choose φ hφ using key
  refine Nat.card_le_card_of_injective φ (fun x₁ x₂ h => pt_injective (G.i_injective ?_))
  have := congrArg (· ≫ g) ((hφ x₁).trans ((congrArg (pt · ≫ G₂.i) h).trans (hφ x₂).symm))
  simpa [Category.assoc, hfg] using this

variable (ℓ u) in
include hu in
/-- **Tate's gluing argument (G7 core).** Let `u_n : E[ℓⁿ⁺¹] ≅ E'[ℓⁿ⁺¹]` be `π`-equivariant for
every `n`. If the quotients `(E × E')/graph(u_n)` satisfy `QuotientFiniteness`, then there is a
nontrivial `π`-equivariant homomorphism `E ⟶ E'` or `E' ⟶ E`. -/
theorem exists_frobHom_of_quotientFiniteness (hℓ : ℓ.Prime) (hℓk : IsUnit (ℓ : k))
    (hdim : 0 < abelianVarietyDimension E)
    (hfin : QuotientFiniteness (E ⊗ E') (πA π π')) :
    (∃ α : E ⟶ E', IsMonHom α ∧ α ≫ π' = π ≫ α ∧ α ≠ 1) ∨
      (∃ β : E' ⟶ E, IsMonHom β ∧ β ≫ π = π' ≫ β ∧ β ≠ 1) := by
  by_contra hcon
  simp only [not_or, not_exists, not_and, not_not] at hcon
  obtain ⟨h1, h2⟩ := hcon
  have := isAbelianVariety_tensor E E'
  have hfinΓ := finite_Γ (E := E) (E' := E') ℓ u hℓ hℓk
  have hG : ∀ n, Nonempty (Glue (Γ ℓ u n)) := fun n => by
    have := hfinΓ n; exact nonempty_glue _
  let G : ∀ n, Glue (Γ ℓ u n) := fun n => (hG n).some
  obtain ⟨n, m, hnm, e, he, heπ⟩ := hfin (Γ ℓ u) (fun n => (G n).B) (fun n => (G n).q)
    (fun n => (G n).πB π π' hu) hfinΓ (fun n => πA_mem_Γ ℓ u hu n)
    (fun n => (G n).ab) (fun n => (G n).hom) (fun n => inferInstance) (fun n => (G n).q_πB hu)
    (fun n => (G n).rank) (fun n => (G n).surj) (fun n => (G n).ker)
  have heπ' : e.inv ≫ (G n).πB π π' hu = (G m).πB π π' hu ≫ e.inv := by
    rw [Iso.inv_comp_eq, ← Category.assoc, heπ, Category.assoc, Iso.hom_inv_id,
      Category.comp_id]
  have hle := card_tor_le (G n) hu (G m) hℓ hℓk h1 h2 e.hom e.inv e.hom_inv_id heπ
  have hge := card_tor_le (G m) hu (G n) hℓ hℓk h1 h2 e.inv e.hom e.inv_hom_id heπ'
  have heq := le_antisymm hle hge
  rw [natCard_tor ℓ hℓ hℓk, natCard_tor ℓ hℓ hℓk, ← pow_mul, ← pow_mul] at heq
  have := Nat.pow_right_injective hℓ.two_le heq
  apply hnm
  have h2g : 0 < 2 * abelianVarietyDimension E := by omega
  have := Nat.eq_of_mul_eq_mul_right h2g this
  omega

end Core

end RamanujanWeil.Arith.Deuring.Geom.G7
