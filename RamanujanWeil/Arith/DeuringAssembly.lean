import RamanujanWeil.Arith.DeuringMatrix
import RamanujanWeil.Arith.TorsorCount
import RamanujanWeil.Arith.AssemblyVocab

/-!
# A3-ord assembly: `OrdinaryDeuring` from the lattice functor (milestone D-ASM)

The geometric input of the Deuring blueprint (`docs/ARITH_DEURING_PLAN.md`) is packaged as
`DeuringLattice K t`: an assignment `W ↦ Λ W ∈ TrDet t q` (the matrix of Frobenius `π` on a
`ℤ`-basis of the `ℤ[π]`-lattice `L(E)` attached to `E`) which

* `rel_iff`: identifies isomorphism classes (`VariableChange`-orbits) of elliptic curves with
  trace `t` with `GL₂(ℤ)`-conjugacy classes,
* `card_stab`: matches `#Aut(E) = #Stab_G(W)` with the centralizer order `#Stab_{GL₂(ℤ)}(Λ W)`,
* `surj`: hits every conjugacy class.

From it, with the torsor count `sum_trace_eq_sum_orbits` (A4) and `matMass_eq_hurwitz` (D-ALG):

* `orbitMass_eq_matMass`: `Σ_{E/≅, a_E = t} 1/#Aut(E) = matMass t q`;
* **`ordinaryDeuring_of_lattice`**: `HasseAll p` and a `DeuringLattice (𝔽_{pⁿ}) t` for every
  `n ≥ 1` and every `t` with `p ∤ t`, `t² < 4pⁿ` give `OrdinaryDeuring hurwitz p`.

So the only remaining content of A3-ord is the construction of `DeuringLattice` (geometry).
-/

open WeierstrassCurve MulAction

namespace RamanujanWeil.Arith.Deuring

open RamanujanWeil.Ihara RamanujanWeil.Arith.Hurwitz RamanujanWeil.ArithPlan

/-- **The geometric interface of A3-ord.** For a finite field `K` with `q` elements and a trace
`t`, a "lattice matrix" for the elliptic curves over `K` with trace `t`, compatible with
isomorphisms and automorphism groups and hitting every `GL₂(ℤ)`-class of `TrDet t q`. -/
structure DeuringLattice (K : Type*) [Field K] [Finite K] (t : ℤ) where
  /-- The matrix of Frobenius on a `ℤ`-basis of the lattice of `E` (junk off the locus). -/
  Λ : WeierstrassCurve K → TrDet t (Nat.card K)
  /-- Isomorphism classes ↔ conjugacy classes. -/
  rel_iff : ∀ W W' : WeierstrassCurve K, W.Δ ≠ 0 → traceOfFrob W = t → W'.Δ ≠ 0 →
    traceOfFrob W' = t → (W' ∈ orbit (VariableChange K) W ↔ ∃ g : GL2, g • Λ W = Λ W')
  /-- `#Aut(E) = #Centralizer`. -/
  card_stab : ∀ W : WeierstrassCurve K, W.Δ ≠ 0 → traceOfFrob W = t →
    Nat.card (stabilizer (VariableChange K) W) = Nat.card (stabilizer GL2 (Λ W))
  /-- Every lattice is realized. -/
  surj : ∀ M : TrDet t (Nat.card K), ∃ W : WeierstrassCurve K, W.Δ ≠ 0 ∧ traceOfFrob W = t ∧
    ∃ g : GL2, g • Λ W = M

variable {K : Type*} [Field K] [Finite K] {t : ℤ}

/-- The isomorphism classes of elliptic curves with trace `t`. -/
def IsLocus (t : ℤ) (O : orbitRel.Quotient (VariableChange K) (WeierstrassCurve K)) : Prop :=
  O.out.Δ ≠ 0 ∧ traceOfFrob O.out = t

lemma isLocus_mk {t : ℤ} (W : WeierstrassCurve K) :
    IsLocus t (Quotient.mk'' W : orbitRel.Quotient (VariableChange K) (WeierstrassCurve K)) ↔
      W.Δ ≠ 0 ∧ traceOfFrob W = t := by
  have h : (Quotient.mk'' W : orbitRel.Quotient (VariableChange K) (WeierstrassCurve K)).out ∈
      orbit (VariableChange K) W :=
    Quotient.exact' (Quotient.out_eq'
      (Quotient.mk'' W : orbitRel.Quotient (VariableChange K) (WeierstrassCurve K)))
  obtain ⟨C, hC⟩ := h
  unfold IsLocus
  rw [← hC, Δ_smul_ne_zero_iff, traceOfFrob_smul]

/-- Isomorphism classes of elliptic curves over `K` with trace `t`. -/
abbrev Locus (K : Type*) [Field K] (t : ℤ) :=
  {O : orbitRel.Quotient (VariableChange K) (WeierstrassCurve K) // IsLocus t O}

/-- The map from isomorphism classes with trace `t` to conjugacy classes. -/
noncomputable def locusMap (D : DeuringLattice K t) :
    Locus K t → orbitRel.Quotient GL2 (TrDet t (Nat.card K)) :=
  fun O => Quotient.mk'' (D.Λ O.1.out)

omit [Finite K] in
lemma out_mem_orbit (W : WeierstrassCurve K) :
    (Quotient.mk'' W : orbitRel.Quotient (VariableChange K) (WeierstrassCurve K)).out ∈
      orbit (VariableChange K) W :=
  Quotient.exact' (Quotient.out_eq'
    (Quotient.mk'' W : orbitRel.Quotient (VariableChange K) (WeierstrassCurve K)))

theorem locusMap_bijective (D : DeuringLattice K t) : Function.Bijective (locusMap D) := by
  constructor
  · rintro ⟨O, hO⟩ ⟨O', hO'⟩ h
    obtain ⟨g, hg⟩ := Quotient.exact' h
    -- `hg : g • Λ O'.out = Λ O.out`
    apply Subtype.ext
    have hmem : O.out ∈ orbit (VariableChange K) O'.out :=
      (D.rel_iff O'.out O.out hO'.1 hO'.2 hO.1 hO.2).mpr ⟨g, hg⟩
    change O = O'
    calc O = Quotient.mk'' O.out := (Quotient.out_eq' O).symm
      _ = Quotient.mk'' O'.out := Quotient.sound' hmem
      _ = O' := Quotient.out_eq' O'
  · intro P
    induction P using Quotient.inductionOn' with | h M => ?_
    obtain ⟨W, hW, htW, g, hg⟩ := D.surj M
    have hloc : IsLocus t
        (Quotient.mk'' W : orbitRel.Quotient (VariableChange K) (WeierstrassCurve K)) :=
      (isLocus_mk W).mpr ⟨hW, htW⟩
    refine ⟨⟨_, hloc⟩, ?_⟩
    obtain ⟨g', hg'⟩ := (D.rel_iff W _ hW htW hloc.1 hloc.2).mp (out_mem_orbit W)
    -- `hg' : g' • Λ W = Λ (mk W).out`, `hg : g • Λ W = M`
    apply Quotient.sound'
    refine ⟨g' * g⁻¹, ?_⟩
    change (g' * g⁻¹) • M = D.Λ (Quotient.mk'' W :
      orbitRel.Quotient (VariableChange K) (WeierstrassCurve K)).out
    rw [← hg, mul_smul, inv_smul_smul, hg']

/-- **Mass transfer.** `Σ_{E/≅, Δ ≠ 0, a_E = t} 1/#Aut(E) = matMass t q`. -/
theorem orbitMass_eq_matMass (D : DeuringLattice K t) :
    (∑ᶠ O : orbitRel.Quotient (VariableChange K) (WeierstrassCurve K),
      open scoped Classical in
      if IsLocus t O then (1 : ℚ) / Nat.card (stabilizer (VariableChange K) O.out) else 0) =
      matMass t (Nat.card K) := by
  classical
  have h1 : (∑ᶠ O : orbitRel.Quotient (VariableChange K) (WeierstrassCurve K),
      if IsLocus t O then (1 : ℚ) / Nat.card (stabilizer (VariableChange K) O.out) else 0) =
      ∑ᶠ O : Locus K t, (1 : ℚ) / Nat.card (stabilizer (VariableChange K) O.1.out) := by
    rw [finsum_subtype_eq_finsum_cond (f := fun O : orbitRel.Quotient (VariableChange K)
      (WeierstrassCurve K) => (1 : ℚ) / Nat.card (stabilizer (VariableChange K) O.out))
      (fun O => IsLocus t O)]
    refine finsum_congr fun O => ?_
    rw [finsum_eq_if]
  rw [h1, matMass, ← finsum_comp_equiv (Equiv.ofBijective _ (locusMap_bijective D))]
  refine finsum_congr fun O => ?_
  simp only [Equiv.ofBijective_apply, locusMap]
  congr 2
  rw [D.card_stab _ O.2.1 O.2.2]
  have h : (Quotient.mk'' (D.Λ O.1.out) :
      orbitRel.Quotient GL2 (TrDet t (Nat.card K))).out ∈ orbit GL2 (D.Λ O.1.out) :=
    Quotient.exact' (Quotient.out_eq'
      (Quotient.mk'' (D.Λ O.1.out) : orbitRel.Quotient GL2 (TrDet t (Nat.card K))))
  obtain ⟨g, hg⟩ := h
  rw [← hg, card_stabilizer_smul_GL]

omit [Finite K] in
/-- The torsor count specialized to one trace: `#{c : Δ ≠ 0, a = t} = (q−1)q³ · mass`. -/
theorem card_trace_eq_mass [Fintype K] [DecidableEq K] (t : ℤ) :
    ((Finset.univ.filter fun c : Fin 5 → K => (wc c).Δ ≠ 0 ∧ traceOfFrob (wc c) = t).card : ℚ) =
      ((Fintype.card K - 1) * Fintype.card K ^ 3 : ℕ) *
        ∑ᶠ O : orbitRel.Quotient (VariableChange K) (WeierstrassCurve K),
          open scoped Classical in
          if IsLocus t O then (1 : ℚ) / Nat.card (stabilizer (VariableChange K) O.out) else 0 := by
  classical
  have := sum_trace_eq_sum_orbits (K := K) (R := ℚ) (fun s => if s = t then 1 else 0)
  rw [Finset.sum_boole, Finset.filter_filter] at this
  rw [this]
  congr 1
  refine finsum_congr fun O => ?_
  unfold IsLocus
  by_cases h1 : O.out.Δ ≠ 0 <;> by_cases h2 : traceOfFrob O.out = t <;> simp [h1, h2]

/-- **D-ASM.** Hasse and the lattice functor at every `(n, t)` with `p ∤ t`, `t² < 4pⁿ` give
ordinary Deuring–Waterhouse for `H = hurwitz`. -/
theorem ordinaryDeuring_of_lattice (p : ℕ) [Fact p.Prime] (hH : HasseAll p)
    (D : ∀ n : ℕ, 1 ≤ n → ∀ t : ℤ, ¬ (p : ℤ) ∣ t → t ^ 2 < 4 * (p : ℤ) ^ n →
      DeuringLattice (GaloisField p n) t) :
    OrdinaryDeuring hurwitz p := by
  intro n hn t hpt
  let _ : Fintype (GaloisField p n) := Fintype.ofFinite _
  classical
  have hcard : Nat.card (GaloisField p n) = p ^ n := GaloisField.card p n (by omega)
  have hfc : Fintype.card (GaloisField p n) = p ^ n := by rw [Fintype.card_eq_nat_card, hcard]
  have hp1 : 1 ≤ p ^ n := Nat.one_le_pow _ _ (Fact.out : p.Prime).pos
  unfold traceCount
  split_ifs with hlt
  · have key := card_trace_eq_mass (K := GaloisField p n) t
    have hm := orbitMass_eq_matMass (D n hn t hpt hlt)
    rw [hcard] at hm
    push_cast at hm
    have hmat := matMass_eq_hurwitz (t := t) (q := (p : ℤ) ^ n) hlt
    convert key using 1
    rw [hm, hmat, hfc]
    push_cast [Nat.cast_sub hp1]
    ring
  · -- no curve: Hasse gives `t² ≤ 4q`, and `t² = 4q` forces `p ∣ t`
    have hzero : ({c : Fin 5 → GaloisField p n | (wc c).Δ ≠ 0 ∧ traceOfFrob (wc c) = t} :
        Finset _).card = 0 := by
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      rintro c - ⟨hc, rfl⟩
      have hle := hH n hn c hc
      have heq : traceOfFrob (wc c) ^ 2 = 4 * (p : ℤ) ^ n := by
        convert le_antisymm (by convert hle using 3) (not_lt.mp hlt) using 1
      apply hpt
      have hp : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp Fact.out
      apply hp.dvd_of_dvd_pow (n := 2)
      rw [heq]
      exact Dvd.dvd.mul_left (dvd_pow_self _ (by omega)) _
    rw [hzero]
    simp
end RamanujanWeil.Arith.Deuring
