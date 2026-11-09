import RamanujanWeil.Arith.DeuringMultDef
import RamanujanWeil.Arith.DeuringAssembly
import RamanujanWeil.Arith.DeuringApproxMult

/-!
# A3-ord: `DeuringMultiplicity` for the concrete `mult` from a per-class lattice interface

`docs/ARITH_DEURING_MULT.md` §4. `DeuringLattice K t` (`DeuringAssembly`) is one lattice functor
for *all* curves of trace `t`; its `surj` field contains Deuring/Honda existence. Here the
interface is restricted to **one isogeny class**:

* **`DeuringClassLattice K t P`**, for an orbit-stable class `P ⊆ {W : Δ ≠ 0, a_W = t}`: a
  matrix `Λ W ∈ TrDet t q` (Frobenius on `L(W) = Hom_π(E₀, E_W)`) with
  `rel_iff`/`card_stab` **within `P`**, and `surj_class`: every `M ∈ TrDet t q` is realized
  by a curve **in `P`**. This is G8(iii) (`L(E₀/G) = M`, `E₀/G` isogenous to `E₀`). It
  needs no existence, since `P` is a given nonempty class.

Results:

* `locusMapP_bijective`, `orbitMassP_eq_matMass`: per-class mass transfer
  `Σ_{E/≅ ∈ P} 1/#Aut E = matMass t q` (the pattern of `ordinaryDeuring_of_lattice`);
* **`card_class_eq`**: `#{W ∈ P} = (q−1)q³·H(4q−t²)/2`, from the torsor count
  `finsum_eq_finsum_orbits` and `matMass_eq_hurwitz`;
* `card_ell_eq_sum`: `#{W : Δ ≠ 0, a_W = t} = Σ_{classes C} #C`;
* **`deuringMultiplicity_of_classLattice`**: `DeuringClassLatticeAll p ⇒
  DeuringMultiplicity hurwitz p (mult p)`.
-/

open WeierstrassCurve MulAction

namespace RamanujanWeil.Arith.Deuring.Mult

open RamanujanWeil.Ihara RamanujanWeil.Arith RamanujanWeil.Arith.Deuring
  RamanujanWeil.Arith.Hurwitz RamanujanWeil.ArithPlan

/-! ### The per-class interface and the per-class mass -/

section Class

variable {K : Type*} [Field K] [Finite K] {t : ℤ}

/-- **The per-class lattice interface (G8 restricted to one isogeny class).** For an
orbit-stable set `P` of curves (one isogeny class of trace `t`): a lattice matrix
`Λ W ∈ TrDet t q` such that, within `P`, isomorphism classes ↔ `GL₂(ℤ)`-conjugacy classes,
`#Aut = #Centralizer`, and every conjugacy class is realized by a curve of `P`. -/
structure DeuringClassLattice (K : Type*) [Field K] [Finite K] (t : ℤ)
    (P : WeierstrassCurve K → Prop) where
  /-- The matrix of Frobenius on a `ℤ`-basis of `L(E) = Hom_π(E₀, E)` (junk off `P`). -/
  Λ : WeierstrassCurve K → TrDet t (Nat.card K)
  /-- Isomorphism classes in `P` ↔ conjugacy classes. -/
  rel_iff : ∀ W W' : WeierstrassCurve K, P W → P W' →
    (W' ∈ orbit (VariableChange K) W ↔ ∃ g : GL2, g • Λ W = Λ W')
  /-- `#Aut(E) = #Centralizer` on `P`. -/
  card_stab : ∀ W : WeierstrassCurve K, P W →
    Nat.card (stabilizer (VariableChange K) W) = Nat.card (stabilizer GL2 (Λ W))
  /-- Every lattice is realized **inside the class** (G8(iii); no existence needed). -/
  surj_class : ∀ M : TrDet t (Nat.card K), ∃ W : WeierstrassCurve K, P W ∧ ∃ g : GL2, g • Λ W = M

/-- Isomorphism classes inside `P`. -/
abbrev LocusP (P : WeierstrassCurve K → Prop) :=
  {O : orbitRel.Quotient (VariableChange K) (WeierstrassCurve K) // P O.out}

variable {P : WeierstrassCurve K → Prop}

/-- The map from isomorphism classes in `P` to conjugacy classes. -/
noncomputable def locusMapP (D : DeuringClassLattice K t P) :
    LocusP P → orbitRel.Quotient GL2 (TrDet t (Nat.card K)) :=
  fun O => Quotient.mk'' (D.Λ O.1.out)

theorem locusMapP_bijective (hP : ∀ (g : VariableChange K) W, P (g • W) ↔ P W)
    (D : DeuringClassLattice K t P) : Function.Bijective (locusMapP D) := by
  constructor
  · rintro ⟨O, hO⟩ ⟨O', hO'⟩ h
    obtain ⟨g, hg⟩ := Quotient.exact' h
    apply Subtype.ext
    have hmem : O.out ∈ orbit (VariableChange K) O'.out :=
      (D.rel_iff O'.out O.out hO' hO).mpr ⟨g, hg⟩
    change O = O'
    calc O = Quotient.mk'' O.out := (Quotient.out_eq' O).symm
      _ = Quotient.mk'' O'.out := Quotient.sound' hmem
      _ = O' := Quotient.out_eq' O'
  · intro Q
    induction Q using Quotient.inductionOn' with | h M => ?_
    obtain ⟨W, hW, g, hg⟩ := D.surj_class M
    obtain ⟨C, hC⟩ := out_mem_orbit (K := K) W
    have hloc : P (Quotient.mk'' W :
        orbitRel.Quotient (VariableChange K) (WeierstrassCurve K)).out := by
      rw [← hC, hP]; exact hW
    refine ⟨⟨_, hloc⟩, ?_⟩
    obtain ⟨g', hg'⟩ := (D.rel_iff W _ hW hloc).mp (out_mem_orbit W)
    apply Quotient.sound'
    refine ⟨g' * g⁻¹, ?_⟩
    change (g' * g⁻¹) • M = D.Λ (Quotient.mk'' W :
      orbitRel.Quotient (VariableChange K) (WeierstrassCurve K)).out
    rw [← hg, mul_smul, inv_smul_smul, hg']

/-- **Per-class mass transfer.** `Σ_{E/≅ ∈ P} 1/#Aut(E) = matMass t q`. -/
theorem orbitMassP_eq_matMass (hP : ∀ (g : VariableChange K) W, P (g • W) ↔ P W)
    (D : DeuringClassLattice K t P) :
    (∑ᶠ O : LocusP P, (1 : ℚ) / Nat.card (stabilizer (VariableChange K) O.1.out)) =
      matMass t (Nat.card K) := by
  classical
  rw [matMass, ← finsum_comp_equiv (Equiv.ofBijective _ (locusMapP_bijective hP D))]
  refine finsum_congr fun O => ?_
  simp only [Equiv.ofBijective_apply, locusMapP]
  congr 2
  rw [D.card_stab _ O.2]
  have h : (Quotient.mk'' (D.Λ O.1.out) :
      orbitRel.Quotient GL2 (TrDet t (Nat.card K))).out ∈ orbit GL2 (D.Λ O.1.out) :=
    Quotient.exact' (Quotient.out_eq'
      (Quotient.mk'' (D.Λ O.1.out) : orbitRel.Quotient GL2 (TrDet t (Nat.card K))))
  obtain ⟨g, hg⟩ := h
  rw [← hg, card_stabilizer_smul_GL]

/-- **Per-class torsor count.** For an orbit-stable `P`:
`#{W ∈ P} = (q−1)q³ · Σ_{E/≅ ∈ P} 1/#Aut(E)`. -/
theorem card_pred_eq_mass (hP : ∀ (g : VariableChange K) W, P (g • W) ↔ P W) :
    (Nat.card {W : WeierstrassCurve K // P W} : ℚ) =
      ((Nat.card K - 1) * Nat.card K ^ 3 : ℕ) *
        ∑ᶠ O : LocusP P, (1 : ℚ) / Nat.card (stabilizer (VariableChange K) O.1.out) := by
  classical
  have : Finite (WeierstrassCurve K) := Finite.of_equiv _ wcEquiv
  have h := finsum_eq_finsum_orbits (K := K) (R := ℚ) (fun W => if P W then 1 else 0)
    (fun g W => by simp only [hP])
  have hl : (∑ᶠ W : WeierstrassCurve K, if P W then (1 : ℚ) else 0) =
      (Nat.card {W : WeierstrassCurve K // P W} : ℚ) := by
    let _ : Fintype (WeierstrassCurve K) := Fintype.ofFinite _
    rw [finsum_eq_sum_of_fintype, Finset.sum_boole, Nat.card_eq_fintype_card,
      Fintype.card_subtype]
  rw [← hl, h]
  congr 1
  rw [finsum_subtype_eq_finsum_cond (f := fun O : orbitRel.Quotient (VariableChange K)
      (WeierstrassCurve K) => (1 : ℚ) / Nat.card (stabilizer (VariableChange K) O.out))
      (fun O => P O.out)]
  refine finsum_congr fun O => ?_
  rw [finsum_eq_if]
  split_ifs <;> simp

/-- **Per-class Deuring count.** An orbit-stable class `P` with a per-class lattice interface
has `#{W ∈ P} = (q−1)q³ · H(4q − t²)/2` (`t² < 4q`). -/
theorem card_class_eq (hP : ∀ (g : VariableChange K) W, P (g • W) ↔ P W)
    (D : DeuringClassLattice K t P) (hlt : t ^ 2 < 4 * (Nat.card K : ℤ)) :
    (Nat.card {W : WeierstrassCurve K // P W} : ℚ) =
      ((Nat.card K - 1) * Nat.card K ^ 3 : ℕ) *
        (hurwitz (4 * (Nat.card K : ℤ) - t ^ 2).toNat / 2) := by
  rw [card_pred_eq_mass hP, orbitMassP_eq_matMass hP D, matMass_eq_hurwitz hlt]

end Class

/-! ### Summing over isogeny classes -/

section Sum

variable {K : Type*} [Field K] [Fintype K] {t : ℤ}

noncomputable instance fintypeIsogClass : Fintype (IsogClass K t) := Fintype.ofFinite _

/-- The fibre of the class map over `C` is the class `C` as a set of curves. -/
def fiberEquiv (C : IsogClass K t) :
    {x : Ell K t // (Quotient.mk _ x : IsogClass K t) = C} ≃
      {W : WeierstrassCurve K // IsogClassPred C W} where
  toFun x := ⟨x.1.1, x.1.2, x.2⟩
  invFun W := ⟨⟨W.1, W.2.1⟩, W.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- `#{W : Δ ≠ 0, a_W = t} = Σ_{isogeny classes C} #C`. -/
theorem card_ell_eq_sum :
    Nat.card (Ell K t) =
      ∑ C : IsogClass K t, Nat.card {W : WeierstrassCurve K // IsogClassPred C W} := by
  classical
  rw [← Nat.card_congr (Equiv.sigmaFiberEquiv (Quotient.mk (isogSetoid K t))), Nat.card_sigma]
  exact Finset.sum_congr rfl fun C _ => Nat.card_congr (fiberEquiv C)

/-- **Class decomposition of the per-trace count.** If every isogeny class of trace `t` has a
per-class lattice interface, then `#{W : Δ ≠ 0, a_W = t} = m(t) · (q−1)q³ · H(4q − t²)/2` with
`m(t) = isogClassCount K t`. -/
theorem card_ell_eq_mult (hlt : t ^ 2 < 4 * (Nat.card K : ℤ))
    (D : ∀ C : IsogClass K t, DeuringClassLattice K t (IsogClassPred C)) :
    (Nat.card (Ell K t) : ℚ) =
      (isogClassCount K t : ℚ) * (((Nat.card K - 1) * Nat.card K ^ 3 : ℕ) *
        (hurwitz (4 * (Nat.card K : ℤ) - t ^ 2).toNat / 2)) := by
  classical
  rw [card_ell_eq_sum, Nat.cast_sum,
    Finset.sum_congr rfl fun C _ => card_class_eq (isogClassPred_smul_iff C) (D C) hlt,
    Finset.sum_const, nsmul_eq_mul, Finset.card_univ, isogClassCount,
    Nat.card_eq_fintype_card (α := IsogClass K t)]

end Sum

/-! ### At `K = 𝔽_{pⁿ}`: `DeuringMultiplicity` -/

section Galois

variable (p : ℕ) [Fact p.Prime]

/-- `traceCount p n t = #{W : Δ ≠ 0, a_W = t}`. -/
lemma traceCount_eq_card_ell (n : ℕ) (t : ℤ) :
    traceCount p n t = Nat.card (Ell (GaloisField p n) t) := by
  letI : Fintype (GaloisField p n) := Fintype.ofFinite _
  classical
  rw [traceCount]
  rw [← Nat.card_congr (Equiv.subtypeEquiv wcEquiv (fun c => Iff.rfl) :
    {c : Fin 5 → GaloisField p n // (wc c).Δ ≠ 0 ∧ traceOfFrob (wc c) = t} ≃ _)]
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]

/-- **The per-class geometric interface at `p`**: every isogeny class of ordinary trace `t`
(`p ∤ t`, `t² < 4pⁿ`) over every `𝔽_{pⁿ}` carries a `DeuringClassLattice`. -/
def DeuringClassLatticeAll : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ t : ℤ, ¬ (p : ℤ) ∣ t → t ^ 2 < 4 * (p : ℤ) ^ n →
    letI : Fintype (GaloisField p n) := Fintype.ofFinite _
    ∀ C : IsogClass (GaloisField p n) t,
      Nonempty (DeuringClassLattice (GaloisField p n) t (IsogClassPred C))

/-- **`DeuringMultiplicity` for the concrete `mult`, from the per-class interface.** -/
theorem deuringMultiplicity_of_classLattice (hL : DeuringClassLatticeAll p) :
    DeuringMultiplicity hurwitz p (mult p) := by
  intro n hn t hpt hlt
  letI : Fintype (GaloisField p n) := Fintype.ofFinite _
  have hcard : Nat.card (GaloisField p n) = p ^ n := GaloisField.card p n (by omega)
  have hcardZ : (Nat.card (GaloisField p n) : ℤ) = (p : ℤ) ^ n := by rw [hcard]; push_cast; rfl
  have hp1 : 1 ≤ p ^ n := Nat.one_le_pow _ _ (Fact.out : p.Prime).pos
  have key := card_ell_eq_mult (K := GaloisField p n) (t := t) (by rw [hcardZ]; exact hlt)
    fun C => (hL n hn t hpt hlt C).some
  rw [traceCount_eq_card_ell, key, hcardZ, hcard]
  simp only [mult]
  push_cast [Nat.cast_sub hp1]
  ring

end Galois

end RamanujanWeil.Arith.Deuring.Mult
