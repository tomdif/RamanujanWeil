import RamanujanWeil.Tau
import RamanujanWeil.LinearAlgebra
import Weil.AlgebraicGeometry.EtaleCohomology.Trace.DeligneWeilConjecture
import Weil.FieldTheory.IsAlgClosed.Classification

/-!
# Deligne's bound for `τ(p)` from Axiom's Weil RH + an Eichler–Shimura–Deligne realization

`Weil.satisfiesWeilEstimate` (AxiomMath/Weil) is Deligne's theorem: for `X` smooth and proper over
a finite field `k` with `q` elements and `ℓ ≠ char k`, every eigenvalue of the (geometric)
Frobenius `F_ν = Weil.rationalFrobenius` on `H^ν(X_k̄, ℚ_ℓ) = Weil.rationalCohomology` is, along
every embedding `ι : ℚ_ℓ →+* ℂ`, of absolute value `q ^ (ν / 2)`.

We take as hypothesis the *geometric realization* of `Δ` (`TauRealization p`): a smooth proper
`X / k`, `#k = p`, a prime `ℓ ≠ p`, and a 2-dimensional `F_11`-stable subspace `W` of
`H^11(X_k̄, ℚ_ℓ)` on which `F_11` has trace `τ(p)`. No size condition on `τ` is assumed: the only
analytic input is Axiom's Weil RH. We deduce `τ(p)^2 ≤ 4 p^11`, the statement of
`RamanujanTau.DeligneBound.bound`.

## Main results

* `RamanujanWeil.norm_map_trace_le_of_stable`: for any smooth proper `X/k`, any `ν`, any
  `F_ν`-stable `W` of dimension `d`, and any `ι`, `‖ι (tr F_ν|_W)‖ ≤ d · q^(ν/2)`.
* `RamanujanWeil.int_sq_le_of_stable`: integer form, `tr F_ν|_W = t ∈ ℤ ⇒ t² ≤ d² q^ν`.
* `RamanujanWeil.tau_sq_le_of_realization`: per prime, `TauRealization p → τ(p)² ≤ 4 p¹¹`.
* `RamanujanWeil.deligneBound_of_realization`: the headline, `∀ p prime, τ(p)² ≤ 4 p¹¹`.
* `RamanujanWeil.deligneBound_instance_of_realization`: the same as an instance of the class
  `RamanujanTau.DeligneBound` (restated verbatim from `~/RamanujanTau/RamanujanTau/Deligne.lean`).
-/

open CategoryTheory AlgebraicGeometry Stacks.EtaleCohomology

universe u

namespace RamanujanWeil

section General

variable {B : BigEtaleSite.{u}} (X : B.Scheme) {k : Type u} [Field k] [Fintype k]
  (f : X.1 ⟶ Spec (.of k)) [IsProper f] [Smooth f] (ℓ : ℕ) [Fact ℓ.Prime]
  [Fact (ℓ ≠ ringChar k)]

/-- An embedding `ℚ_ℓ →+* ℂ` exists (`#ℚ_ℓ ≤ 𝔠`). -/
theorem nonempty_padic_ringHom_complex : Nonempty (ℚ_[ℓ] →+* ℂ) :=
  let ⟨ι, _⟩ := RingHom.exists_comp_algebraMap_eq_of_countable (K := ℚ) (L := ℚ_[ℓ])
    (Padic.cardinalMk_le_continuum ℓ) (Rat.castHom ℂ)
  ⟨ι⟩

/-- **Weil RH ⇒ trace bound on a Frobenius-stable subspace.** For `X` smooth and proper over `k`
(`q = #k`), every `F_ν`-stable subspace `W ⊆ H^ν(X_k̄, ℚ_ℓ)` and every `ι : ℚ_ℓ →+* ℂ`,
`‖ι (tr (F_ν|_W))‖ ≤ dim W · q^(ν/2)`. -/
theorem norm_map_trace_le_of_stable (ν : ℕ)
    (W : Submodule ℚ_[ℓ] (Weil.rationalCohomology B X f ℓ ν))
    (hW : ∀ x ∈ W, Weil.rationalFrobenius B X f ℓ ν x ∈ W) (ι : ℚ_[ℓ] →+* ℂ) :
    ‖ι (LinearMap.trace ℚ_[ℓ] W ((Weil.rationalFrobenius B X f ℓ ν).restrict hW))‖ ≤
      Module.finrank ℚ_[ℓ] W * (Fintype.card k : ℝ) ^ ((ν : ℝ) / 2) := by
  refine norm_map_trace_restrict_le _ W hW ι _ fun z hz => ?_
  have hpure := (Weil.satisfiesWeilEstimate_iff_forall_isCharpolyPureOfWeight B X f).1
    (Weil.satisfiesWeilEstimate B X f) ν ι z hz
  simpa using hpure.norm_eq

/-- **Integer form.** If moreover `tr (F_ν|_W) = t` for an integer `t`, then
`t² ≤ (dim W)² · q^ν`. -/
theorem int_sq_le_of_stable (ν : ℕ)
    (W : Submodule ℚ_[ℓ] (Weil.rationalCohomology B X f ℓ ν))
    (hW : ∀ x ∈ W, Weil.rationalFrobenius B X f ℓ ν x ∈ W) (t : ℤ)
    (ht : LinearMap.trace ℚ_[ℓ] W ((Weil.rationalFrobenius B X f ℓ ν).restrict hW) = (t : ℚ_[ℓ])) :
    t ^ 2 ≤ (Module.finrank ℚ_[ℓ] W : ℤ) ^ 2 * (Fintype.card k : ℤ) ^ ν := by
  obtain ⟨ι⟩ := nonempty_padic_ringHom_complex ℓ
  have h := norm_map_trace_le_of_stable X f ℓ ν W hW ι
  rw [ht, map_intCast, Complex.norm_intCast] at h
  exact int_sq_le_of_abs_le t _ _ ν h

end General

/-! ### The realization hypothesis -/

/-- **Eichler–Shimura–Deligne realization of `Δ` at the prime `p`**, in Axiom's API.

A smooth proper scheme `X` over a finite field `k` with exactly `p` elements, a prime `ℓ ≠ char k`,
and a `ℚ_ℓ`-subspace `W ⊆ H^11(X_k̄, ℚ_ℓ)` (`Weil.rationalCohomology`, degree `11`) that is stable
under Axiom's Frobenius `Weil.rationalFrobenius` (the **geometric** Frobenius), has dimension
exactly `2`, and on which the trace of Frobenius is `τ(p)`.

Literature source (cited from memory, NOT checked): Deligne, *Formes modulaires et
représentations ℓ-adiques* (Sém. Bourbaki 355, 1969), and Scholl, *Motives for modular forms*
(Invent. Math. 100, 1990): `X` = the reduction mod `p` of (a desingularization of) the Kuga–Sato
variety `W_10` = 10-fold fibre power of the universal elliptic curve over a modular curve of level
`N ≥ 3`, `p ∤ N`; `W` = one copy of the `Δ`-isotypic part of `H^11`, on which the geometric
Frobenius has characteristic polynomial `X² - τ(p) X + p¹¹` (Eichler–Shimura congruence relation).
With the arithmetic Frobenius the trace would instead be `τ(p)/p¹¹`, so the convention matters
and it is the geometric one, matching Axiom's `rationalFrobenius`. -/
structure TauRealization (p : ℕ) where
  /-- The big étale site in which the scheme lives. -/
  B : BigEtaleSite.{u}
  /-- The finite field with `p` elements. -/
  k : Type u
  [instField : Field k]
  [instFintype : Fintype k]
  card_eq : Fintype.card k = p
  /-- The smooth proper scheme (Kuga–Sato variety mod `p`). -/
  X : B.Scheme
  /-- Its structure morphism. -/
  f : X.1 ⟶ Spec (.of k)
  [instProper : IsProper f]
  [instSmooth : Smooth f]
  /-- The coefficient prime. -/
  ℓ : ℕ
  [instPrime : Fact ℓ.Prime]
  [instNe : Fact (ℓ ≠ ringChar k)]
  /-- The `Δ`-part of `H^11(X_k̄, ℚ_ℓ)`. -/
  W : Submodule ℚ_[ℓ] (Weil.rationalCohomology B X f ℓ 11)
  /-- `W` is stable under the (geometric) Frobenius `F_11`. -/
  stable : ∀ x ∈ W, Weil.rationalFrobenius B X f ℓ 11 x ∈ W
  /-- `W` is two-dimensional. -/
  finrank_eq : Module.finrank ℚ_[ℓ] W = 2
  /-- The trace of Frobenius on `W` is `τ(p)`. -/
  trace_eq : LinearMap.trace ℚ_[ℓ] W ((Weil.rationalFrobenius B X f ℓ 11).restrict stable) =
    ((RamanujanTau.tau p : ℤ) : ℚ_[ℓ])

attribute [instance] TauRealization.instField TauRealization.instFintype
  TauRealization.instProper TauRealization.instSmooth TauRealization.instPrime
  TauRealization.instNe

/-- **Per-prime bound.** A realization of `Δ` at `p` gives `τ(p)² ≤ 4 p¹¹`. -/
theorem tau_sq_le_of_realization {p : ℕ} (R : TauRealization.{u} p) :
    (RamanujanTau.tau p) ^ 2 ≤ 4 * (p : ℤ) ^ 11 := by
  have h := int_sq_le_of_stable R.X R.f R.ℓ 11 R.W R.stable _ R.trace_eq
  rw [R.finrank_eq, R.card_eq] at h
  norm_num at h
  exact h

/-- **Deligne's bound from the Eichler–Shimura–Deligne realization** (headline).
If `Δ` is realized (in the sense of `TauRealization`) at every prime `p`, then
`τ(p)² ≤ 4 p¹¹` for every prime `p`; the analytic input is Axiom's `Weil.satisfiesWeilEstimate`. -/
theorem deligneBound_of_realization
    (hR : ∀ p : ℕ, p.Prime → Nonempty (TauRealization.{u} p)) :
    ∀ p : ℕ, p.Prime → (RamanujanTau.tau p) ^ 2 ≤ 4 * (p : ℤ) ^ 11 :=
  fun p hp => (hR p hp).elim tau_sq_le_of_realization

/-- The same, with the hypothesis in the data-valued form `∀ p, p.Prime → TauRealization p`. -/
theorem deligneBound_of_realization' (hR : ∀ p : ℕ, p.Prime → TauRealization.{u} p) :
    ∀ p : ℕ, p.Prime → (RamanujanTau.tau p) ^ 2 ≤ 4 * (p : ℤ) ^ 11 :=
  fun p hp => tau_sq_le_of_realization (hR p hp)

end RamanujanWeil

namespace RamanujanTau

/-- **Deligne's bound** — restated VERBATIM from `~/RamanujanTau/RamanujanTau/Deligne.lean`
(that repo is on a different toolchain and cannot be imported here). -/
class DeligneBound : Prop where
  bound : ∀ p : ℕ, p.Prime → (τ p) ^ 2 ≤ 4 * (p : ℤ) ^ 11

end RamanujanTau

namespace RamanujanWeil

/-- The hypothesis class `RamanujanTau.DeligneBound` is discharged by the realization. -/
theorem deligneBound_instance_of_realization
    (hR : ∀ p : ℕ, p.Prime → Nonempty (TauRealization.{u} p)) : RamanujanTau.DeligneBound :=
  ⟨deligneBound_of_realization hR⟩

end RamanujanWeil
