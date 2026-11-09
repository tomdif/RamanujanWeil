import RamanujanWeil.Arith.DeuringG1Jac
import RamanujanWeil.Arith.DeuringG7Bridge
import RamanujanWeil.Arith.TorsorCount

/-!
# A3-ord: the concrete isogeny-class count `mult p n t`, and Tate uniqueness `mult ≤ 1`

`docs/ARITH_DEURING_MULT.md`. The approximate endgame (`FinalDeuringApprox`) needs a function
`mult p n t` with `DeuringMultiplicity` and `mult ≤ 1`. Here it is defined concretely.

* **`IsogStep W W'`** (one step of the isogeny relation on Weierstrass curves over `K = 𝔽_q`):
  either `W'` is a change of variables of `W` (isomorphic over `K`), or both are elliptic and for
  some Jacobian sites `S`, `S'` (G1.0, `JacSite`; `S.J = Pic⁰_{E_W/K̄}` with the Frobenius
  `S.π` induced by the twisted Frobenius of `E_W`) there is a **nontrivial `π`-equivariant
  homomorphism `S.J ⟶ S'.J` or `S'.J ⟶ S.J`**.
* **`isogSetoid K t`**: the equivalence closure (`Relation.EqvGen`) of `IsogStep` on the
  elliptic curves of trace `t`. It is an equivalence by construction, so no dual isogeny
  (G7-dual) is needed for this definition.
* **`isogClassCount K t = #(Ell K t / isogSetoid)`**, and `mult p n t` its value at
  `K = 𝔽_{pⁿ}`.
* **`TateFiniteness K`** (the one named hypothesis): `QuotientFiniteness (S.J × S'.J) (π × π')`
  for all pairs of concrete Jacobians of elliptic curves with the same ordinary trace,
  `t² < 4q`.
* **`isogClassCount_le_one`** / **`mult_le_one`**: `TateFiniteness ⇒ mult ≤ 1`, from
  `tate_exists_frobHom` (G7). One direction of hom suffices, since the relation is
  symmetrized.

Isomorphic curves are put in the same class by the first disjunct, so every class is a union
of `VariableChange`-orbits (`isogClassPred_smul_iff`), which the per-class count
(`DeuringMultCount`) needs.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory WeierstrassCurve
  MulAction
open scoped CategoryTheory.MonObj

universe u

namespace RamanujanWeil.Arith.Deuring.Mult

open RamanujanWeil.Ihara RamanujanWeil.Arith RamanujanWeil.Arith.Deuring.Geom
  RamanujanWeil.Arith.Deuring.Geom.G7 Stacks.Groupoids

section Def

variable {K : Type u} [Field K] [Fintype K]

/-- A nontrivial `π`-equivariant homomorphism of Frobenius Jacobians `J ⟶ J'`. -/
def FrobHomNe {W W' : WeierstrassCurve K} [W.IsElliptic] [W'.IsElliptic]
    (J : FrobeniusJacobian W) (J' : FrobeniusJacobian W') : Prop :=
  ∃ α : J.A ⟶ J'.A, IsMonHom α ∧ α ≫ J'.π = J.π ≫ α ∧ α ≠ 1

/-- **One step of the isogeny relation**: `W'` is isomorphic to `W` (a change of variables), or
the concrete Jacobians (for some Jacobian sites) admit a nontrivial `π`-equivariant homomorphism
in one direction or the other. -/
def IsogStep (W W' : WeierstrassCurve K) : Prop :=
  W' ∈ orbit (VariableChange K) W ∨
    ∃ (_ : W.IsElliptic) (_ : W'.IsElliptic) (S : Jac.JacSite W) (S' : Jac.JacSite W'),
      FrobHomNe S.frobeniusJacobian S'.frobeniusJacobian ∨
        FrobHomNe S'.frobeniusJacobian S.frobeniusJacobian

variable (K) in
/-- Elliptic Weierstrass curves over `K` with trace `t`. -/
abbrev Ell (t : ℤ) := {W : WeierstrassCurve K // W.Δ ≠ 0 ∧ traceOfFrob W = t}

variable (K) in
/-- **The isogeny relation** on curves of trace `t`: the equivalence closure of `IsogStep`. -/
def isogSetoid (t : ℤ) : Setoid (Ell K t) :=
  Relation.EqvGen.setoid fun x y : Ell K t => IsogStep x.1 y.1

variable (K) in
/-- The isogeny classes of elliptic curves over `K` with trace `t`. -/
abbrev IsogClass (t : ℤ) := Quotient (isogSetoid K t)

variable (K) in
/-- **The number of isogeny classes** of elliptic curves over `K` with trace `t`. -/
noncomputable def isogClassCount (t : ℤ) : ℕ := Nat.card (IsogClass K t)

instance finite_weierstrass : Finite (WeierstrassCurve K) := Finite.of_equiv _ wcEquiv

instance finite_isogClass (t : ℤ) : Finite (IsogClass K t) := inferInstance

/-- Membership of a curve in an isogeny class. -/
def IsogClassPred {t : ℤ} (C : IsogClass K t) (W : WeierstrassCurve K) : Prop :=
  ∃ h : W.Δ ≠ 0 ∧ traceOfFrob W = t, (Quotient.mk _ ⟨W, h⟩ : IsogClass K t) = C

lemma isogClassPred_spec {t : ℤ} {C : IsogClass K t} {W : WeierstrassCurve K}
    (h : IsogClassPred C W) : W.Δ ≠ 0 ∧ traceOfFrob W = t := h.1

/-- Isogeny classes are unions of isomorphism classes. -/
theorem isogClassPred_smul_iff {t : ℤ} (C : IsogClass K t) (g : VariableChange K)
    (W : WeierstrassCurve K) : IsogClassPred C (g • W) ↔ IsogClassPred C W := by
  have key : ∀ (g : VariableChange K) (W : WeierstrassCurve K),
      IsogClassPred C W → IsogClassPred C (g • W) := by
    rintro g W ⟨h, rfl⟩
    have h' : (g • W).Δ ≠ 0 ∧ traceOfFrob (g • W) = t := by
      rw [Δ_smul_ne_zero_iff, traceOfFrob_smul]; exact h
    refine ⟨h', ?_⟩
    apply Quotient.sound
    apply Relation.EqvGen.symm
    exact Relation.EqvGen.rel _ _ (Or.inl ⟨g, rfl⟩)
  refine ⟨fun hW => ?_, key g W⟩
  have := key g⁻¹ _ hW
  rwa [inv_smul_smul] at this

/-- Every curve of trace `t` lies in its class. -/
lemma isogClassPred_mk {t : ℤ} (x : Ell K t) :
    IsogClassPred (Quotient.mk _ x : IsogClass K t) x.1 := ⟨x.2, rfl⟩

end Def

/-! ### The named finiteness hypothesis and Tate uniqueness -/

section Tate

variable (K : Type u) [Field K] [Fintype K]

/-- **The named hypothesis of G7 (Tate finiteness)** at `K = 𝔽_q`: for any two elliptic curves
with the same ordinary trace `t` (`p ∤ t`, `t² < 4q`) and any Jacobian sites, the quotients of
`J_W × J_{W'}` by finite `π`-stable étale subgroups fall into finitely many equivariant
isomorphism classes (`QuotientFiniteness`, `docs/ARITH_DEURING_G7.md` §4). -/
def TateFiniteness : Prop :=
  ∀ (W W' : WeierstrassCurve K) [W.IsElliptic] [W'.IsElliptic] (S : Jac.JacSite W)
    (S' : Jac.JacSite W'), traceOfFrob W' = traceOfFrob W →
    ¬ (ringChar K : ℤ) ∣ traceOfFrob W → traceOfFrob W ^ 2 < 4 * (Nat.card K : ℤ) →
    QuotientFiniteness (S.J ⊗ S'.J) (πA S.π S'.π)

variable {K}

/-- **Tate (one step).** Two elliptic curves with the same ordinary trace `t`, `t² < 4q`, are
related by `IsogStep`, given `TateFiniteness`. -/
theorem isogStep_of_trace (hfin : TateFiniteness K) {W W' : WeierstrassCurve K}
    (hW : W.Δ ≠ 0) (hW' : W'.Δ ≠ 0) (ht : traceOfFrob W' = traceOfFrob W)
    (hp : ¬ (ringChar K : ℤ) ∣ traceOfFrob W)
    (hlt : traceOfFrob W ^ 2 < 4 * (Nat.card K : ℤ)) : IsogStep W W' := by
  have : W.IsElliptic := ⟨isUnit_iff_ne_zero.mpr hW⟩
  have : W'.IsElliptic := ⟨isUnit_iff_ne_zero.mpr hW'⟩
  obtain ⟨S⟩ := Jac.nonempty_jacSite W
  obtain ⟨S'⟩ := Jac.nonempty_jacSite W'
  refine Or.inr ⟨inferInstance, inferInstance, S, S', ?_⟩
  exact tate_exists_frobHom S.frobeniusJacobian S'.frobeniusJacobian ht hlt
    (hfin W W' S S' ht hp hlt)

/-- **Tate uniqueness: at most one isogeny class per ordinary trace** (`t² < 4q`, `p ∤ t`),
given `TateFiniteness`. -/
theorem isogClassCount_le_one (hfin : TateFiniteness K) (t : ℤ)
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
  exact isogStep_of_trace hfin x.2.1 y.2.1 (hy.trans hx.symm) (by rw [hx]; exact hp) (by rw [hx]; exact hlt)

end Tate

/-! ### At `K = 𝔽_{pⁿ}` -/

section Galois

variable (p : ℕ) [Fact p.Prime]

/-- **`mult p n t`: the number of isogeny classes of elliptic curves over `𝔽_{pⁿ}` with trace
`t`** (for `p ∤ t` these are the ordinary isogeny classes of trace `t`). -/
noncomputable def mult (n : ℕ) (t : ℤ) : ℕ :=
  letI : Fintype (GaloisField p n) := Fintype.ofFinite _
  isogClassCount (GaloisField p n) t

/-- **`TateFiniteness` at every finite field `𝔽_{pⁿ}`**, `p` prime, `n ≥ 1`: the single named
hypothesis behind `mult ≤ 1`. -/
def TateFinitenessAll : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (n : ℕ), 1 ≤ n →
    letI : Fintype (GaloisField p n) := Fintype.ofFinite _
    TateFiniteness (GaloisField p n)

lemma ringChar_galoisField (n : ℕ) : ringChar (GaloisField p n) = p :=
  ringChar.eq (GaloisField p n) p

/-- **`mult ≤ 1`** on the ordinary range, given `TateFinitenessAll`. -/
theorem mult_le_one (hfin : TateFinitenessAll) (n : ℕ) (hn : 1 ≤ n) (t : ℤ)
    (hp : ¬ (p : ℤ) ∣ t) (hlt : t ^ 2 < 4 * (p : ℤ) ^ n) : mult p n t ≤ 1 := by
  letI : Fintype (GaloisField p n) := Fintype.ofFinite _
  have hcard : (Nat.card (GaloisField p n) : ℤ) = (p : ℤ) ^ n := by
    rw [GaloisField.card p n (by omega)]; push_cast; rfl
  exact isogClassCount_le_one (hfin p n hn) t (by rwa [ringChar_galoisField])
    (by rw [hcard]; exact hlt)

end Galois

end RamanujanWeil.Arith.Deuring.Mult
