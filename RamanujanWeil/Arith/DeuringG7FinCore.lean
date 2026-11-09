import RamanujanWeil.Arith.DeuringMultDef
import RamanujanWeil.Arith.DeuringG7FinAlg

/-!
# A3-ord, G7-fin: Tate's gluing argument from finiteness of *principally polarizable* graph quotients

`docs/ARITH_DEURING_G7FIN.md`. The G7 core (`exists_frobHom_of_quotientFiniteness`) consumes
`QuotientFiniteness (E × E') π_A`: finiteness up to equivariant isomorphism among quotients of
`E × E'` by **arbitrary** finite `π`-stable étale subgroups. The argument only ever uses the
quotients by **graphs** `Γ_n = graph(u_n)` of `π`-equivariant `u_n : E[ℓⁿ⁺¹] ≅ E'[ℓⁿ⁺¹]`, and the
`u_n` may be chosen freely. This file isolates the weakest finiteness statement that the gluing
argument needs and that the polarization route (G7 doc §4, F1/F2) actually delivers:

* `GraphFiniteness π π' ℓ S`: for every equivariant family `u_n ∈ S n` and every choice of G6
  quotients `B_n = (E × E')/graph(u_n)`, two of the `(B_n, π_n)` are equivariantly isomorphic.
* `PolGraphFiniteness π π' ℓ`: for **every** choice of coordinates `e_n : E[ℓⁿ⁺¹] ≅ (ℤ/ℓⁿ⁺¹)²`,
  `e'_n`, there are **some** unit determinants `c_n` such that `GraphFiniteness` holds for the
  class `S_c = {u_n : det(e'_n ∘ u_n ∘ e_n⁻¹) = c_n}`.

  Why it is true: take `c_n = −s_n / s'_n`, where `e_ℓⁿ⁺¹(e_n(1,0), e_n(0,1)) = ζ^{s_n}` (Weil
  pairing), and likewise `s'_n`. Then every `u_n ∈ S_c` is anti-isometric, `graph(u_n)` is
  maximal isotropic in `(E × E')[ℓⁿ⁺¹]` for `λ_E × λ_{E'}`, the polarization
  `ℓⁿ⁺¹ (λ_E × λ_{E'})` descends to a **principal** polarization of `B_n` (Mumford §23), and there
  are only finitely many principally polarized abelian surfaces over `𝔽_q` (forms of `(B_n, π_n)`).
  So only *principal*-polarization finiteness is needed; no bounded-degree polarization theory,
  no Zarhin trick, no arbitrary π-stable subgroups.

Proved here:

* `graphFiniteness_of_quotientFiniteness`, `polGraphFiniteness_of_quotientFiniteness`: the new
  hypotheses are **weaker** than `QuotientFiniteness`.
* `exists_frobHom_of_graphFiniteness`: the G7 core from `GraphFiniteness`.
* `tate_exists_frobHom_pol`: Tate for Frobenius Jacobians from `PolGraphFiniteness` (the
  equivariant isomorphisms with prescribed determinant come from `DeuringG7FinAlg`).
* `TateFinitenessPol(All)`, `tateFinitenessPolAll_of_tateFinitenessAll`, and
  **`mult_le_one_pol`**: `mult p n t ≤ 1` from `TateFinitenessPolAll`.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory
  CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

universe u

namespace RamanujanWeil.Arith.Deuring.Geom.G7.Fin

open Stacks.Groupoids RamanujanWeil.Arith.Deuring.Geom.G7

section Core

variable {k : Type u} [Field k] [IsAlgClosed k] {E E' : Over (Spec (.of k))} [GrpObj E]
  [GrpObj E'] [AlgebraicGeometry.IsAbelianVariety k E] [AlgebraicGeometry.IsAbelianVariety k E']

variable (π : E ⟶ E) (π' : E' ⟶ E') [IsMonHom π] [IsMonHom π']

/-- **Finiteness of graph quotients for an admissible class `S` of gluings** (named-hypothesis
form). For every `π`-equivariant family `u_n ∈ S n` and every choice of G6 quotients
`B_n = (E × E')/graph(u_n)`, two of the `(B_n, π_n)` are `π`-equivariantly isomorphic. -/
def GraphFiniteness (ℓ : ℕ) (S : ∀ n : ℕ, Set (Tor E (ℓ ^ (n + 1)) ≃+ Tor E' (ℓ ^ (n + 1)))) :
    Prop :=
  ∀ (u : ∀ n : ℕ, Tor E (ℓ ^ (n + 1)) ≃+ Tor E' (ℓ ^ (n + 1)))
    (hu : ∀ n x, u n (torAct π _ x) = torAct π' _ (u n x)), (∀ n, u n ∈ S n) →
    ∀ G : ∀ n, Glue (Γ ℓ u n), ∃ n m, n ≠ m ∧ ∃ e : (G n).B ≅ (G m).B,
      IsMonHom e.hom ∧ e.hom ≫ (G m).πB π π' hu = (G n).πB π π' hu ≫ e.hom

/-- Coordinates on the `ℓ`-power torsion, one for each level. -/
abbrev Coords (X : Over (Spec (.of k))) [GrpObj X] [AlgebraicGeometry.IsAbelianVariety k X]
    (ℓ : ℕ) :=
  ∀ n : ℕ, Tor X (ℓ ^ (n + 1)) ≃+ (Fin 2 → ZMod (ℓ ^ (n + 1)))

/-- The gluings of prescribed determinant `c_n` in the coordinates `e`, `e'`. -/
def detClass {ℓ : ℕ} (e : Coords E ℓ) (e' : Coords E' ℓ) (c : ∀ n : ℕ, ZMod (ℓ ^ (n + 1)))
    (n : ℕ) : Set (Tor E (ℓ ^ (n + 1)) ≃+ Tor E' (ℓ ^ (n + 1))) :=
  {u | (coordMat (e n) (e' n) u).det = c n}

/-- **Principally polarizable graph finiteness (the named hypothesis of G7-fin).** For all
coordinates `e`, `e'` on `E[ℓ^∞]`, `E'[ℓ^∞]` there are unit determinants `c_n` (in truth: the
anti-isometric class `−s_n/s'_n` for the Weil pairings) such that the quotients of `E × E'` by
graphs of equivariant gluings of determinant `c_n` satisfy `GraphFiniteness`. -/
def PolGraphFiniteness (ℓ : ℕ) : Prop :=
  ∀ (e : Coords E ℓ) (e' : Coords E' ℓ), ∃ c : ∀ n : ℕ, ZMod (ℓ ^ (n + 1)),
    (∀ n, IsUnit (c n)) ∧ GraphFiniteness π π' ℓ (detClass e e' c)

variable {π π'}

/-- `QuotientFiniteness` implies `GraphFiniteness` for every class `S`. -/
theorem graphFiniteness_of_quotientFiniteness (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓk : IsUnit (ℓ : k))
    (hfin : QuotientFiniteness (E ⊗ E') (πA π π'))
    (S : ∀ n : ℕ, Set (Tor E (ℓ ^ (n + 1)) ≃+ Tor E' (ℓ ^ (n + 1)))) :
    GraphFiniteness π π' ℓ S := by
  intro u hu _ G
  exact hfin (Γ ℓ u) (fun n => (G n).B) (fun n => (G n).q) (fun n => (G n).πB π π' hu)
    (finite_Γ ℓ u hℓ hℓk) (fun n => πA_mem_Γ ℓ u hu n) (fun n => (G n).ab) (fun n => (G n).hom)
    (fun n => inferInstance) (fun n => (G n).q_πB hu) (fun n => (G n).rank)
    (fun n => (G n).surj) (fun n => (G n).ker)

/-- `QuotientFiniteness` implies `PolGraphFiniteness` (take `c_n = 1`). -/
theorem polGraphFiniteness_of_quotientFiniteness (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓk : IsUnit (ℓ : k))
    (hfin : QuotientFiniteness (E ⊗ E') (πA π π')) : PolGraphFiniteness π π' ℓ :=
  fun _ _ => ⟨fun _ => 1, fun _ => isUnit_one,
    graphFiniteness_of_quotientFiniteness ℓ hℓ hℓk hfin _⟩

/-- **The G7 core from `GraphFiniteness`.** If `u_n ∈ S n` are `π`-equivariant isomorphisms
`E[ℓⁿ⁺¹] ≅ E'[ℓⁿ⁺¹]` and `GraphFiniteness π π' ℓ S` holds, there is a nontrivial `π`-equivariant
homomorphism `E ⟶ E'` or `E' ⟶ E`. -/
theorem exists_frobHom_of_graphFiniteness (ℓ : ℕ)
    (u : ∀ n : ℕ, Tor E (ℓ ^ (n + 1)) ≃+ Tor E' (ℓ ^ (n + 1)))
    (hu : ∀ n x, u n (torAct π _ x) = torAct π' _ (u n x)) (hℓ : ℓ.Prime) (hℓk : IsUnit (ℓ : k))
    (hdim : 0 < abelianVarietyDimension E)
    (S : ∀ n : ℕ, Set (Tor E (ℓ ^ (n + 1)) ≃+ Tor E' (ℓ ^ (n + 1)))) (huS : ∀ n, u n ∈ S n)
    (hfin : GraphFiniteness π π' ℓ S) :
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
  obtain ⟨n, m, hnm, e, he, heπ⟩ := hfin u hu huS G
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

/-! ## Frobenius Jacobians -/

section Bridge

variable {K : Type u} [Field K] [Fintype K]

open RamanujanWeil.Ihara in
/-- **G7 for elliptic curves over `𝔽_q`, modulo principally polarizable graph finiteness.**
As `tate_exists_frobHom`, with `QuotientFiniteness` replaced by the weaker
`PolGraphFiniteness` at every odd prime `ℓ` invertible in `𝔽̄_q`. -/
theorem tate_exists_frobHom_pol {W W' : WeierstrassCurve K} [W.IsElliptic] [W'.IsElliptic]
    (J : FrobeniusJacobian W) (J' : FrobeniusJacobian W')
    (ht : traceOfFrob W' = traceOfFrob W) (hlt : traceOfFrob W ^ 2 < 4 * (Nat.card K : ℤ))
    (hpol : ∀ ℓ : ℕ, ℓ.Prime → ℓ ≠ 2 → IsUnit (ℓ : AlgebraicClosure K) →
      PolGraphFiniteness J.π J'.π ℓ) :
    (∃ α : J.A ⟶ J'.A, IsMonHom α ∧ α ≫ J'.π = J.π ≫ α ∧ α ≠ 1) ∨
      (∃ β : J'.A ⟶ J.A, IsMonHom β ∧ β ≫ J.π = J'.π ≫ β ∧ β ≠ 1) := by
  set t := traceOfFrob W
  set q : ℤ := (Nat.card K : ℤ)
  obtain ⟨ℓ, hℓ, hodd, hroot⟩ := exists_odd_prime_no_root t q hlt
  have hℓk := isUnit_of_no_root (K := K) ℓ hℓ t hroot
  have hrel : ∀ {V : WeierstrassCurve K} [V.IsElliptic] (I : FrobeniusJacobian V),
      traceOfFrob V = t → ∀ (N : ℕ) (x : Tor I.A N),
        torAct I.π N (torAct I.π N x) - t • torAct I.π N x + q • x = 0 := by
    intro V _ I hV N x
    apply pt_injective
    have h := congrArg (pt x ≫ ·) I.frob_quadratic
    simp only [MonObj.comp_one] at h
    rw [hV, comp_endPolyEval_quadratic] at h
    change pt x ≫ I.π ≫ I.π / (pt x ≫ I.π) ^ t * pt x ^ q = 1 at h
    change Additive.toMul (_ - _ + _) = (1 : Pt I.A)
    rw [toMul_add, toMul_sub, AddSubgroupClass.coe_zsmul, AddSubgroupClass.coe_zsmul, toMul_zsmul,
      toMul_zsmul]
    exact h
  -- coordinates
  have hco : ∀ {V : WeierstrassCurve K} [V.IsElliptic] (I : FrobeniusJacobian V) (n : ℕ),
      Nonempty (Tor I.A (ℓ ^ (n + 1)) ≃+ (Fin 2 → ZMod (ℓ ^ (n + 1)))) := by
    intro V _ I n
    obtain ⟨e⟩ := nonempty_torsionBy_pow_addEquiv I.A ℓ hℓk (n + 1)
    rw [I.dim_eq] at e
    exact ⟨e⟩
  let e : Coords J.A ℓ := fun n => (hco J n).some
  let e' : Coords J'.A ℓ := fun n => (hco J' n).some
  obtain ⟨c, hcu, hfin⟩ := hpol ℓ hℓ hodd hℓk e e'
  have hu : ∀ n : ℕ, ∃ u : Tor J.A (ℓ ^ (n + 1)) ≃+ Tor J'.A (ℓ ^ (n + 1)),
      (∀ x, u (torAct J.π _ x) = torAct J'.π _ (u x)) ∧ u ∈ detClass e e' c n := fun n =>
    exists_equivariant_addEquiv_det hℓ hodd (e n) (e' n) (torAct J.π _) (torAct J'.π _) t q
      (hrel J rfl _) (hrel J' ht _) hroot (c n) (hcu n)
  choose u hu huS using hu
  exact exists_frobHom_of_graphFiniteness ℓ u hu hℓ hℓk (by rw [J.dim_eq]; exact one_pos) _ huS
    hfin

end Bridge

/-! ## The concrete isogeny count: `mult ≤ 1` -/

section Mult

open RamanujanWeil.Ihara RamanujanWeil.Arith.Deuring.Mult

variable (K : Type u) [Field K] [Fintype K]

/-- **The named hypothesis of G7-fin at `K = 𝔽_q`**: `PolGraphFiniteness` for the concrete
Jacobians of any two elliptic curves with the same ordinary trace (`p ∤ t`, `t² < 4q`), at every
odd prime `ℓ` invertible in `𝔽̄_q`. Weaker than `TateFiniteness K`
(`tateFinitenessPol_of_tateFiniteness`). -/
def TateFinitenessPol : Prop :=
  ∀ (W W' : WeierstrassCurve K) [W.IsElliptic] [W'.IsElliptic] (S : Jac.JacSite W)
    (S' : Jac.JacSite W'), traceOfFrob W' = traceOfFrob W →
    ¬ (ringChar K : ℤ) ∣ traceOfFrob W → traceOfFrob W ^ 2 < 4 * (Nat.card K : ℤ) →
    ∀ ℓ : ℕ, ℓ.Prime → ℓ ≠ 2 → IsUnit (ℓ : AlgebraicClosure K) →
      PolGraphFiniteness S.π S'.π ℓ

variable {K}

theorem tateFinitenessPol_of_tateFiniteness (hfin : TateFiniteness K) : TateFinitenessPol K :=
  fun W W' _ _ S S' ht hp hlt ℓ hℓ _ hℓk =>
    polGraphFiniteness_of_quotientFiniteness ℓ hℓ hℓk (hfin W W' S S' ht hp hlt)

/-- **Tate (one step) from `TateFinitenessPol`.** -/
theorem isogStep_of_trace_pol (hfin : TateFinitenessPol K) {W W' : WeierstrassCurve K}
    (hW : W.Δ ≠ 0) (hW' : W'.Δ ≠ 0) (ht : traceOfFrob W' = traceOfFrob W)
    (hp : ¬ (ringChar K : ℤ) ∣ traceOfFrob W)
    (hlt : traceOfFrob W ^ 2 < 4 * (Nat.card K : ℤ)) : IsogStep W W' := by
  have : W.IsElliptic := ⟨isUnit_iff_ne_zero.mpr hW⟩
  have : W'.IsElliptic := ⟨isUnit_iff_ne_zero.mpr hW'⟩
  obtain ⟨S⟩ := Jac.nonempty_jacSite W
  obtain ⟨S'⟩ := Jac.nonempty_jacSite W'
  refine Or.inr ⟨inferInstance, inferInstance, S, S', ?_⟩
  exact tate_exists_frobHom_pol S.frobeniusJacobian S'.frobeniusJacobian ht hlt
    (hfin W W' S S' ht hp hlt)

/-- **At most one isogeny class per ordinary trace**, from `TateFinitenessPol`. -/
theorem isogClassCount_le_one_pol (hfin : TateFinitenessPol K) (t : ℤ)
    (hp : ¬ (ringChar K : ℤ) ∣ t) (hlt : t ^ 2 < 4 * (Nat.card K : ℤ)) :
    isogClassCount K t ≤ 1 := by
  rw [isogClassCount, Finite.card_le_one_iff_subsingleton]
  refine ⟨fun a b => ?_⟩
  induction a using Quotient.inductionOn with | h x => ?_
  induction b using Quotient.inductionOn with | h y => ?_
  apply Quotient.sound
  refine Relation.EqvGen.rel _ _ ?_
  have hx := x.2.2
  have hy := y.2.2
  exact isogStep_of_trace_pol hfin x.2.1 y.2.1 (hy.trans hx.symm) (by rw [hx]; exact hp)
    (by rw [hx]; exact hlt)

/-- **`TateFinitenessPol` at every finite field.** -/
def TateFinitenessPolAll : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (n : ℕ), 1 ≤ n →
    letI : Fintype (GaloisField p n) := Fintype.ofFinite _
    TateFinitenessPol (GaloisField p n)

theorem tateFinitenessPolAll_of_tateFinitenessAll (hfin : TateFinitenessAll) :
    TateFinitenessPolAll := fun p _ n hn =>
  letI : Fintype (GaloisField p n) := Fintype.ofFinite _
  tateFinitenessPol_of_tateFiniteness (hfin p n hn)

/-- **`mult ≤ 1`** on the ordinary range, from the weaker `TateFinitenessPolAll`. -/
theorem mult_le_one_pol (hfin : TateFinitenessPolAll) (p : ℕ) [Fact p.Prime] (n : ℕ)
    (hn : 1 ≤ n) (t : ℤ) (hp : ¬ (p : ℤ) ∣ t) (hlt : t ^ 2 < 4 * (p : ℤ) ^ n) :
    mult p n t ≤ 1 := by
  letI : Fintype (GaloisField p n) := Fintype.ofFinite _
  have hcard : (Nat.card (GaloisField p n) : ℤ) = (p : ℤ) ^ n := by
    rw [GaloisField.card p n (by omega)]; push_cast; rfl
  exact isogClassCount_le_one_pol (hfin p n hn) t (by rwa [ringChar_galoisField])
    (by rw [hcard]; exact hlt)

end Mult

end RamanujanWeil.Arith.Deuring.Geom.G7.Fin
