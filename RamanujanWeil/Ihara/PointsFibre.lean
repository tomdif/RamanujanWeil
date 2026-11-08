import RamanujanWeil.Ihara.SymSheaf
import RamanujanWeil.Ihara.PointsBase
import RamanujanWeil.Ihara.PointsExtension

/-!
# M6 (B): stalk traces at `y_c` are traces of Frobenius of `E_c / 𝔽_{pⁿ}`

**Frozen M4b interface** `R1StalkCharpolyFibre p B ℓ` (a strengthening of M5's
`R1StalkCharpoly`, with the same coordinates): at every closed point `y` of `W_p`, with
`q_y = p^{deg y}` and `E_y = fibreCurve p y = (curve p).map (residueMapOf y)` over `κ(y)`,

1. (Hasse) `a_y² ≤ 4 q_y` for `a_y = traceOfFrob E_y = #κ(y) + 1 − #E_y(κ(y))`;
2. `charpoly(π_y | R¹_ȳ ⊗ ℚ_ℓ) = X² − a_y X + q_y` — **`a_y` is the trace of the fibre curve**;
3. `ExtensionTraces E_y q_y`: for every finite `L/κ(y)`, `a(E_y,L) = s_{[L:κ(y)]}(a_y, q_y)`.

All three are, at the fibre curve `E_y` over the finite field `κ(y)`, outputs of M4a
(`sq_le_four_mul_card_of_weierstrass`, `charpoly_weierstrassH1`,
`natCard_point_extension_eq_of_weierstrass` + `extensionTraces_of_extension`); M4b's job is to
transport the charpoly from `H¹(E_y)` to the stalk of `R¹` (fibre identification
`isPullback_fromSpecResidueField`, proper base change) and to discharge M4a's hypotheses
(`HasFirstBettiTwo`, `RealizesWeierstrass` — see `PointsCurve.lean` — and geometric
connectedness) at `E_y`.

Results:
* `R1StalkCharpolyFibre.toR1StalkCharpoly`: the M5 hypothesis follows.
* `natCard_residueField`: `#κ(y) = p^{deg y}`.
* `powSum_fibre_eq_traceOfFrob` (**part B**): for `g ∈ W_p(K)` over `y` (`[K : 𝔽_p] = n`),
  `s_{n / deg y}(a_y, q_y) = traceOfFrob (wc (coords g))`, i.e. `pⁿ + 1 − #E_c(K)`.
* `stalkTrace_symR1_fvpOf`: the summand of `pointSum` at `y_c` is
  `symTrace 10 (traceOfFrob (wc c)) (pⁿ)`.
-/

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.SmallEtale Stacks.EtaleCohomology
open AlgebraicGeometry.ModuliEllipticCurves.Weierstrass

noncomputable section

namespace RamanujanWeil.Ihara

attribute [local instance] HasDerivedCategory.standard moduleCat_hasLimitsOfSize

variable (p : ℕ) [Fact p.Prime]

/-! ### Residue fields of `W_p` -/

/-- `#κ(y) = p^{deg y}` at a closed point `y` of `W_p`. -/
theorem Family.natCard_residueField (y : Family.base p) (hy : IsClosed ({y} : Set (Family.base p))) :
    Nat.card ((Family.base p).residueField y) = p ^ residueDegree (Family.toSpecK p) y := by
  letI : Algebra (ZMod p) ((Family.base p).residueField y) :=
    (fieldToResidue (Family.toSpecK p) y).hom.toAlgebra
  have := finite_residueField (Family.toSpecK p) y hy
  have : Module.Finite (ZMod p) ((Family.base p).residueField y) := Module.Finite.of_finite
  rw [Module.natCard_eq_pow_finrank (K := ZMod p), Nat.card_zmod]
  rfl

/-! ### Part B -/

section PartB

variable {K : Type} [Field K] [Algebra (ZMod p) K] [Finite K]

/-- **Part B.** Let `g ∈ W_p(K)` lie over the closed point `y`, `[K : 𝔽_p] = n`. If the fibre curve
`E_y` satisfies `ExtensionTraces E_y (p^{deg y})`, then
`s_{n / deg y}(a(E_y), p^{deg y}) = a(E_{coords g} / K) = pⁿ + 1 − #E_c(K)`. -/
theorem powSum_fibre_eq_traceOfFrob (g : fieldValuedPoints (Family.toSpecK p) K)
    (hE : ExtensionTraces (Family.fibreCurve p (fieldValuedPointsEquiv (Family.toSpecK p) K g).1)
      ((p : ℤ) ^ residueDegree (Family.toSpecK p) (fieldValuedPointsEquiv (Family.toSpecK p) K g).1)) :
    powSum (traceOfFrob (Family.fibreCurve p (fieldValuedPointsEquiv (Family.toSpecK p) K g).1))
        ((p : ℤ) ^ residueDegree (Family.toSpecK p) (fieldValuedPointsEquiv (Family.toSpecK p) K g).1)
        (Module.finrank (ZMod p) K /
          residueDegree (Family.toSpecK p) (fieldValuedPointsEquiv (Family.toSpecK p) K g).1) =
      traceOfFrob (wc (Family.coords p g)) := by
  set y := (fieldValuedPointsEquiv (Family.toSpecK p) K g).1 with hy
  letI : Algebra (ZMod p) ((Family.base p).residueField y) :=
    (fieldToResidue (Family.toSpecK p) y).hom.toAlgebra
  letI : Algebra ((Family.base p).residueField y) K := (Family.residueEmb p g).toAlgebra
  haveI : IsScalarTower (ZMod p) ((Family.base p).residueField y) K :=
    IsScalarTower.of_algebraMap_eq fun r =>
      RingHom.congr_fun (Subsingleton.elim (algebraMap (ZMod p) K)
        ((algebraMap ((Family.base p).residueField y) K).comp
          (algebraMap (ZMod p) ((Family.base p).residueField y)))) r
  have hfinK : Module.Finite (ZMod p) K := Module.Finite.of_finite
  have hfin : Module.Finite ((Family.base p).residueField y) K := Module.Finite.of_finite
  have htower := Module.finrank_mul_finrank (ZMod p) ((Family.base p).residueField y) K
  have hdeg : residueDegree (Family.toSpecK p) y =
      Module.finrank (ZMod p) ((Family.base p).residueField y) := rfl
  have hpos : 0 < residueDegree (Family.toSpecK p) y := by
    rw [hdeg]
    have := finite_residueField (Family.toSpecK p) y
      (isClosed_and_dvd_of_residueEmbeddings (Family.toSpecK p) K y
        (fieldValuedPointsEquiv (Family.toSpecK p) K g).2).1
    have : Module.Finite (ZMod p) ((Family.base p).residueField y) := Module.Finite.of_finite
    exact Module.finrank_pos
  have hm : Module.finrank (ZMod p) K / residueDegree (Family.toSpecK p) y =
      Module.finrank ((Family.base p).residueField y) K := by
    rw [← htower, ← hdeg, Nat.mul_div_cancel_left _ hpos]
  have hW : (Family.fibreCurve p y).baseChange K = wc (Family.coords p g) :=
    Family.fibreCurve_map_residueEmb p g
  rw [hm, ← hE K, hW]

end PartB

/-! ### The frozen M4b interface -/

variable (B : BigEtaleSite.{0}) (ℓ : ℕ) [Fact ℓ.Prime]
  [∀ (n : ℕ) (S T : B.Scheme) (g : T ⟶ S),
    ((AlgebraicGeometry.smallEtaleBaseChange B g).sheafPushforwardContinuous
      (ModuleCat.{1} (ZMod (ℓ ^ (n + 1))))
      (SmallEtale.topology B S.1 S.property)
      (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
  [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
    HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
      (ModuleCat.{1} (ZMod (ℓ ^ (n + 1))))]
  [∀ (n : ℕ) (T : B.Scheme), HasWeakSheafify (SmallEtale.topology B T.1 T.property)
    (ModuleCat.{1} (ZMod (ℓ ^ (n + 1))))]

/-- **Frozen M4b interface (hypothesis).** At every closed point `y` of `W_p`, with
`q_y = p^{deg y}` and the fibre curve `E_y = fibreCurve p y` over `κ(y)`, the trace
`a_y = traceOfFrob E_y = #κ(y) + 1 − #E_y(κ(y))` satisfies Hasse, is the trace of the stalk
Frobenius on `R¹` (charpoly `X² − a_y X + q_y`), and governs the point counts of `E_y` over all
finite extensions of `κ(y)`. Strengthens `R1StalkCharpoly` (same `y`, same `q_y`). -/
def R1StalkCharpolyFibre : Prop :=
  ∀ y : closedPoints (Wp p B).1,
    traceOfFrob (Family.fibreCurve p y.1) ^ 2 ≤ 4 * (p : ℤ) ^ residueDegree (toSpecK p B) y.1 ∧
    (LAdicSheaf.rationalStalkFrobenius B (Wp p B) ℓ (R1 p B ℓ) y.1
        (finite_residueField (toSpecK p B) y.1 y.2)).charpoly =
      Polynomial.X ^ 2 - Polynomial.C ((traceOfFrob (Family.fibreCurve p y.1) : ℤ) : ℚ_[ℓ]) *
        Polynomial.X + Polynomial.C ((p : ℚ_[ℓ]) ^ residueDegree (toSpecK p B) y.1) ∧
    ExtensionTraces (Family.fibreCurve p y.1) ((p : ℤ) ^ residueDegree (toSpecK p B) y.1)

variable {p B ℓ}

theorem R1StalkCharpolyFibre.toR1StalkCharpoly (H : R1StalkCharpolyFibre p B ℓ) :
    R1StalkCharpoly p B ℓ :=
  fun y => ⟨_, (H y).1, (H y).2.1⟩

/-- The coefficient `a` of a monic quadratic `X² − C a X + C q` is determined. -/
theorem eq_of_quadratic_eq {R : Type*} [CommRing R] {a a' q q' : R}
    (h : Polynomial.X ^ 2 - Polynomial.C a * Polynomial.X + Polynomial.C q =
      Polynomial.X ^ 2 - Polynomial.C a' * Polynomial.X + Polynomial.C q') : a = a' := by
  have := congrArg (fun P => Polynomial.coeff P 1) h
  simpa [Polynomial.coeff_X, Polynomial.coeff_C] using this

variable (p B ℓ)

/-- **Stalk traces at `y_c`.** Under `R1StalkCharpolyFibre`, for `c ∈ K⁵` with `Δ(c) ≠ 0`
(`[K : 𝔽_p] = n`), the summand of `pointSum (symR1)` at the closed point `y_c` under `c` is
`tr(π_{y_c}^{n / deg y_c} | F) = symTrace 10 (traceOfFrob (wc c)) (pⁿ)`. -/
theorem stalkTrace_symR1_fvpOf (hℓp : ℓ ≠ p) (H : R1StalkCharpolyFibre p B ℓ)
    {K : Type} [Field K] [Algebra (ZMod p) K] [Finite K] (n : ℕ)
    (hn : Module.finrank (ZMod p) K = n) (c : Fin 5 → K) (hc : (wc c).Δ ≠ 0) :
    LinearMap.trace ℚ_[ℓ] _ (LAdicSheaf.rationalStalkFrobenius B (Wp p B) ℓ (symR1 p B ℓ)
        (fvpPoint (Family.toSpecK p) K (Family.fvpOf p K c hc)).1
        (finite_residueField (toSpecK p B) _ (fvpPoint (Family.toSpecK p) K (Family.fvpOf p K c hc)).2) ^
          (n / residueDegree (toSpecK p B) (fvpPoint (Family.toSpecK p) K (Family.fvpOf p K c hc)).1)) =
      ((symTrace 10 (traceOfFrob (wc c)) ((p : ℤ) ^ n) : ℤ) : ℚ_[ℓ]) := by
  subst hn
  set g := Family.fvpOf p K c hc
  set y : closedPoints (Wp p B).1 := fvpPoint (Family.toSpecK p) K g with hy
  obtain ⟨hhasse, hchar, hE⟩ := H y
  obtain ⟨a, -, ha, htr⟩ := exists_stalkTrace_symR1 p B ℓ hℓp H.toR1StalkCharpoly y
  have haa : a = traceOfFrob (Family.fibreCurve p y.1) := by
    have := eq_of_quadratic_eq (ha.symm.trans hchar)
    exact_mod_cast this
  have hdvd := residueDegree_fvpPoint_dvd (Family.toSpecK p) K g
  rw [(htr _).2, haa]
  have hB := powSum_fibre_eq_traceOfFrob p g hE
  have hcoords : Family.coords p g = c := Family.coords_fvpOf p c hc
  rw [hcoords] at hB
  have hexp : residueDegree (toSpecK p B) y.1 *
      (Module.finrank (ZMod p) K / residueDegree (toSpecK p B) y.1) =
      Module.finrank (ZMod p) K := Nat.mul_div_cancel' hdvd
  rw [hexp]
  exact congrArg (fun t : ℤ => ((symTrace 10 t ((p : ℤ) ^ Module.finrank (ZMod p) K) : ℤ) : ℚ_[ℓ])) hB

end RamanujanWeil.Ihara
