import RamanujanWeil.Ihara.WeilPackageCore
import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LAdicTraceFormulaFinal
import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LFunctionTraceCriterion
import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CohomologicalInterpretation

/-!
# M2, part 1: the Lefschetz trace identity for every power of Frobenius (Tag 03V0)

For a lisse ℓ-adic sheaf `F` (`ℓ ≠ p`) on a noetherian `B`-scheme `X`, separated and of finite
type over a finite field `k` with `p ^ q` elements, pointwise `ι`-mixed of weights `≤ w` and
`ι`-realizable (Stacks' hypotheses of Weil II 3.3.1), and `topologicalKrullDim X ≤ d`, we build a
`LefschetzPackage ℚ_[ℓ] ι (p ^ q) w d (pointSum F)`:

* `V i = Hⁱ_c(X_k̄, F ⊗ ℚ_ℓ)` (`rationalGeometricCompactlySupportedCohomology`, degree `i : ℤ`,
  `0 ≤ i ≤ 2d`), written in `Module.finBasis`; `F i` = the geometric Frobenius
  `rationalGeometricCompactlySupportedFrobenius`;
* weights from `LAdicSheaf.SatisfiesWeightBound` (unconditional, Laumon inputs discharged), which
  gives `‖ι z‖ = (p^q)^(w'/2)` with `w' ≤ w + i`, hence `≤ (p^q)^((w+i)/2)`;
* the trace identity for **every** `n ≥ 1` from Tag 03V0
  (`rationalLFunction_eq_gradedCharSeries_compactSupportFrobenius`) by comparing the `Tⁿ`
  coefficients of the logarithmic derivatives
  (`FrobeniusMatrices.coeff_logDerivative_lFunction`, `coeff_logDerivative_gradedCharSeries`);
* the vanishing of `Hⁱ_c` outside `0 ≤ i ≤ 2 dim X` and finite-dimensionality from Tag 03V2
  (`LAdicSheaf.traceFormula`).

The point side is
`pointSum F n = ∑ᶠ (x : |X|) (_ : deg x ∣ n), deg x · tr((π_x^*)^{n / deg x} | F_x̄ ⊗ ℚ_ℓ)`:
closed points `x` with `deg x = [κ(x) : k]` dividing `n`, weighted by `deg x`, with the trace of
the `(n / deg x)`-th power of the geometric Frobenius of `κ(x)` on the rational stalk. (Each such
`x` accounts for exactly `deg x` points of `X(k_n)`, `[k_n : k] = n`; that bijection is M6.)
-/

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.SmallEtale Stacks.EtaleCohomology
  PowerSeries

universe u

namespace RamanujanWeil.Ihara

attribute [local instance] HasDerivedCategory.standard

variable (B : BigEtaleSite.{u}) (X : B.Scheme) (ℓ : ℕ) [Fact ℓ.Prime]
  [∀ (n : ℕ) (S T : B.Scheme) (g : T ⟶ S),
    ((AlgebraicGeometry.smallEtaleBaseChange B g).sheafPushforwardContinuous
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
      (SmallEtale.topology B S.1 S.property)
      (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
  [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
    HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [∀ (n : ℕ) (T : B.Scheme), HasWeakSheafify (SmallEtale.topology B T.1 T.property)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [IsNoetherian X.1]
  {k : Type u} [Field k] [Fintype k] (f : X.1 ⟶ Spec (.of k))
  [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f]

/-! ### Log-derivative of the alternating product (local copy)

`Stacks.EtaleCohomology.coeff_logDerivative_gradedCharSeries` lives in
`Trace/AdicCompactSupportCharSeries.lean`, which is not in our prebuilt `.lake`; we re-prove it
from the public API of `LFunctionTraceCriterion` / `CohomologicalInterpretation`. -/

theorem coeff_logDerivative_gradedCharSeries' {Λ : Type*} [CommRing Λ] [Nontrivial Λ]
    (V : ℤ → Type*) [∀ i, AddCommGroup (V i)] [∀ i, Module Λ (V i)] [∀ i, Module.Finite Λ (V i)]
    [∀ i, Module.Free Λ (V i)] (φ : ∀ i, V i →ₗ[Λ] V i) (S : Finset ℤ)
    (hS : ∀ i ∉ S, Subsingleton (V i)) {m : ℕ} (hm : m ≠ 0) :
    coeff m (logDerivative (gradedCharSeries V φ)) =
      ∑ᶠ i : ℤ, (if Even i then (1 : Λ) else -1) * LinearMap.trace Λ (V i) (φ i ^ m) := by
  have hG : gradedCharSeries V φ = alternatingCharSeries (fun a : S => (a : ℤ))
      (fun a => Module.finrank Λ (V a))
      (fun a => LinearMap.toMatrix (Module.finBasis Λ (V a)) (Module.finBasis Λ (V a)) (φ a)) := by
    rw [gradedCharSeries_eq_prod V φ S hS, alternatingCharSeries, ← Finset.prod_coe_sort S]
    exact Finset.prod_congr rfl fun a _ => gradedCharFactor_eq_matrix V φ a
  rw [hG, coeff_logDerivative_alternatingCharSeries _ _ _ hm, Finset.sum_coe_sort S
      (fun a => (if Even a then (1 : Λ) else -1) *
        ((LinearMap.toMatrix (Module.finBasis Λ (V a)) (Module.finBasis Λ (V a)) (φ a)) ^
          m).trace)]
  rw [finsum_eq_sum_of_support_subset _ (s := S) fun i hi => ?_]
  · exact Finset.sum_congr rfl fun i _ => by
      rw [LinearMap.trace_eq_matrix_trace Λ (Module.finBasis Λ (V i)), LinearMap.toMatrix_pow]
  · by_contra h
    have := hS i h
    exact hi (by simp only [Subsingleton.elim (φ i ^ m) 0, map_zero, mul_zero])

/-! ### The point side -/

/-- `∑_{x ∈ |X|, deg x ∣ n} deg x · tr((π_x^*)^{n / deg x} | F_x̄ ⊗ ℚ_ℓ)`. -/
noncomputable def pointSum (F : LAdicSheaf.{u, u + 1} B X ℓ) (n : ℕ) : ℚ_[ℓ] :=
  ∑ᶠ (x : closedPoints X.1) (_ : residueDegree f x.1 ∣ n),
    (residueDegree f x.1 : ℚ_[ℓ]) *
      LinearMap.trace ℚ_[ℓ] _
        (LAdicSheaf.rationalStalkFrobenius B X ℓ F x.1 (finite_residueField f x.1 x.2) ^
          (n / residueDegree f x.1))

omit [IsSeparated f] in
/-- The log-derivative coefficient of the Euler product `L(X, F)` is `pointSum`. -/
theorem coeff_logDerivative_rationalLFunction (F : LAdicSheaf.{u, u + 1} B X ℓ) {n : ℕ}
    (hn : n ≠ 0) :
    coeff n (logDerivative (LAdicSheaf.rationalLFunction B X ℓ F f)) = pointSum B X ℓ f F n := by
  have h := (LAdicSheaf.frobeniusMatrices B X ℓ F f).coeff_logDerivative_lFunction hn
  rw [show LAdicSheaf.rationalLFunction B X ℓ F f =
      (LAdicSheaf.frobeniusMatrices B X ℓ F f).lFunction from rfl, h, pointSum]
  rw [finsum_cond_eq_sum_of_cond_iff _ (t := ((LAdicSheaf.frobeniusMatrices B X ℓ F f
      ).eulerSystem.support n).filter fun x => residueDegree f x.1 ∣ n) fun {x} _ => by
    rw [Finset.mem_filter, EulerSystem.mem_support]
    exact ⟨fun hd => ⟨Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hd, hd⟩, fun h => h.2⟩]
  refine Finset.sum_congr rfl fun x _ => ?_
  congr 1
  exact trace_toMatrix_pow _ _ _

/-! ### Degree bounds and the trace identity for all powers -/

section Cohomology

variable (j : CompactificationOf (Over.mk f)) (kbar : Type u) [Field kbar] [Algebra k kbar]
  [IsAlgClosure k kbar] (p q : ℕ) [Fact p.Prime] [CharP k p] (hcard : Fintype.card k = p ^ q)

include hcard in
/-- Tag 03V2, degree part: `Hⁱ_c ≠ 0 ⇒ 0 ≤ i ≤ 2d` once `dim X ≤ d`. -/
theorem nonneg_and_le_of_nontrivial (hℓp : ℓ ≠ p) (d : ℕ) (hdim : topologicalKrullDim X.1 ≤ d)
    (F : LAdicSheaf.{u, u + 1} B X ℓ) (i : ℤ)
    (h : Nontrivial (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f j kbar F i)) :
    0 ≤ i ∧ i ≤ 2 * (d : ℤ) := by
  obtain ⟨h0, d', hd', hi⟩ := (LAdicSheaf.traceFormula B X ℓ f j kbar p q hcard hℓp F).2.1 i h
  refine ⟨h0, hi.trans ?_⟩
  have : ((d' : ℕ) : WithBot ℕ∞) ≤ (d : ℕ) := hd' ▸ hdim
  have : d' ≤ d := by exact_mod_cast this
  omega

/-- **The Lefschetz identity for every power of Frobenius** (Tag 03V0 + log-derivative): for all
`n ≥ 1`, `∑ᵢ (-1)ⁱ tr((π_X^*)ⁿ | Hⁱ_c(X_k̄, F)) = pointSum F n`. -/
theorem alternating_trace_pow_eq_pointSum (hℓp : ℓ ≠ p) (d : ℕ)
    (hdim : topologicalKrullDim X.1 ≤ d) (F : LAdicSheaf.{u, u + 1} B X ℓ) {n : ℕ} (hn : n ≠ 0) :
    haveI := (LAdicSheaf.traceFormula B X ℓ f j kbar p q hcard hℓp F).1
    ∑ᶠ i : ℤ, (if Even i then (1 : ℚ_[ℓ]) else -1) *
        LinearMap.trace ℚ_[ℓ]
          (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f j kbar F i)
          ((LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B X ℓ f j kbar p q hcard F
            i).hom ^ n) =
      pointSum B X ℓ f F n := by
  have := (LAdicSheaf.traceFormula B X ℓ f j kbar p q hcard hℓp F).1
  have hS : ∀ i ∉ (Finset.range (2 * d + 1)).map Nat.castEmbedding, Subsingleton
      (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f j kbar F i) := by
    intro i hi
    by_contra hns
    rw [not_subsingleton_iff_nontrivial] at hns
    obtain ⟨h0, h1⟩ := nonneg_and_le_of_nontrivial B X ℓ f j kbar p q hcard hℓp d hdim F i hns
    exact hi (Finset.mem_map.2 ⟨i.toNat, Finset.mem_range.2 (by omega), by simp; omega⟩)
  rw [← coeff_logDerivative_rationalLFunction B X ℓ f F hn,
    LAdicSheaf.rationalLFunction_eq_gradedCharSeries_compactSupportFrobenius B X ℓ f j kbar p q
      hcard hℓp F, coeff_logDerivative_gradedCharSeries' _ _ _ hS hn]

end Cohomology

/-! ### Reindexing `ℤ` ↦ `Fin (2d+1)` -/

theorem finsum_int_eq_sum_fin {K : Type*} [AddCommMonoid K] (d : ℕ) (g : ℤ → K)
    (hg : ∀ i, g i ≠ 0 → 0 ≤ i ∧ i ≤ 2 * (d : ℤ)) :
    ∑ᶠ i : ℤ, g i = ∑ i : Fin (2 * d + 1), g ((i : ℕ) : ℤ) := by
  rw [finsum_eq_sum_of_support_subset g (s := (Finset.range (2 * d + 1)).map Nat.castEmbedding),
    Finset.sum_map, Fin.sum_univ_eq_sum_range (fun i => g ((i : ℕ) : ℤ))]
  · rfl
  · intro i hi
    obtain ⟨h0, h1⟩ := hg i hi
    exact Finset.mem_coe.2 (Finset.mem_map.2 ⟨i.toNat, Finset.mem_range.2 (by omega), by simp; omega⟩)

theorem ite_even_natCast {K : Type*} [Ring K] (i : ℕ) :
    (if Even (i : ℤ) then (1 : K) else -1) = (-1) ^ i := by
  split_ifs with h
  · exact ((Int.even_coe_nat i).1 h).neg_one_pow.symm
  · exact (Nat.not_even_iff_odd.1 fun h' => h ((Int.even_coe_nat i).2 h')).neg_one_pow.symm

end RamanujanWeil.Ihara
