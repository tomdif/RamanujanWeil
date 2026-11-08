import RamanujanWeil.Ihara.CurveH1Core
import RamanujanWeil.Bridge
import RamanujanWeil.Ihara.WeilPackageTrace
import Weil.AlgebraicGeometry.EtaleCohomology.Trace.DeligneWeilConjecture
import Weil.AlgebraicGeometry.EtaleCohomology.Trace.ConstantDegreeZeroCohomology
import Weil.AlgebraicGeometry.EtaleCohomology.Trace.RepresentationSheafTrivialConstant
import Weil.AlgebraicGeometry.EtaleCohomology.Trace.ConstantSystemLocalFactor
import Weil.AlgebraicGeometry.EtaleCohomology.Duality.RationalPoincareDuality
import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.SmoothSupportSpecialization

/-!
# M4a: `charpoly(Frob | H¹(X_k̄, ℚ_ℓ)) = X² − aX + q` for a genus-one curve over `𝔽_q`

Let `X` be a `B`-scheme, proper and smooth of relative dimension one over a finite field `k` with
`q` elements, with `X_k̄` connected (hence `X` connected) and a `k`-rational point, `ℓ ≠ char k`, and write
`Hᵛ = Weil.rationalCohomology B X f ℓ ν = Hᵛ(X_k̄, ℚ_ℓ)` with the geometric Frobenius
`Fᵥ = Weil.rationalFrobenius B X f ℓ ν`. We prove, from Axiom's Weil package:

* `H⁰`: `dim H⁰ = 1` and `F₀ = id` (`rationalFrobenius_zero_eq_id`);
* `H²`: `charpoly F₂ = X − q` (`charpoly_rationalFrobenius_two`), by Poincaré duality at the
  rational point against `H⁰` (`rationalFrobenius_top_representationSheaf_one_of_rationalPoint`),
  transported from the sheaf `ℱ_𝟏` of the trivial representation to the constant sheaf;
* `Hᵛ = 0` for `ν ≥ 3` (Tag 03V2 and `dim X = 1`);
* the trace formula for every `n ≥ 1`:
  `#X(k_n) = 1 − tr(F₁ⁿ) + qⁿ` with `#X(k_n) = AlgebraicGeometry.pointCountOfDegree f n`
  (`pointCountOfDegree_eq_one_sub_trace_add`), from M2's Tag 03V0 identity;
* purity of `F₁`: every root `z` of `charpoly F₁` along any `ι` has `‖z‖² = q` (Deligne).

Combined with the linear algebra of `CurveH1Core`, this gives (`charpoly_rationalFrobenius_one`):
**if `dim H¹ = 2` and `#X(k₃) ∣ #X(k₆)`, then `charpoly F₁ = X² − aX + q`, `a = q + 1 − #X(k)`**,
together with `tr F₁ⁿ = αⁿ + βⁿ` and `#X(k_n) = qⁿ + 1 − (αⁿ + βⁿ)`.

For a Weierstrass curve `W` with `#X(k_n) = #W(k_n)` (Mathlib's `Point`, which includes the point
at infinity), the divisibility is Lagrange (`natCard_point_extension_dvd`), and
`charpoly_rationalFrobenius_one_of_weierstrass` is the M4a statement. The remaining inputs
`dim H¹ = 2` and `#X(k_n) = #W(k_n)` are discussed in `docs/IHARA_CURVE_H1.md`.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Stacks.EtaleCohomology Stacks.Frobenius
  Polynomial Module

universe u

namespace RamanujanWeil.Ihara

attribute [local instance] HasDerivedCategory.standard

section Curve

variable {B : BigEtaleSite.{u}} (X : B.Scheme) {k : Type u} [Field k] [Fintype k]
  (f : X.1 ⟶ Spec (.of k)) [IsProper f] (ℓ : ℕ) [Fact ℓ.Prime] [hℓk : Fact (ℓ ≠ ringChar k)]

/-! ### Bookkeeping: `#k = p ^ e` with `p = char k` -/

/-- The prime `p = char k`. -/
theorem fact_ringChar_prime : Fact (ringChar k).Prime := ⟨CharP.char_is_prime k _⟩

/-- The exponent `e` with `#k = pᵉ`, as chosen by `Weil.rationalFrobenius`. -/
noncomputable def cardExp (k : Type u) [Field k] [Fintype k] : ℕ :=
  (FiniteField.card k (ringChar k)).choose

attribute [local instance] fact_ringChar_prime

theorem card_eq_ringChar_pow : Fintype.card k = ringChar k ^ cardExp k :=
  (FiniteField.card k (ringChar k)).choose_spec.2

/-! ### `H⁰` -/

section H0

variable [ConnectedSpace ↥(pullback (Over.mk f).hom (specAlgebraMap k (AlgebraicClosure k)))]

/-- `dim H⁰(X_k̄, ℚ_ℓ) = 1` for `X_k̄` connected. -/
theorem finrank_rationalCohomology_zero :
    finrank ℚ_[ℓ] (Weil.rationalCohomology B X f ℓ 0) = 1 := by
  haveI := Weil.isNoetherian_of_isProper f
  exact Weil.LAdicSheaf.finrank_rationalGeometricCompactlySupportedCohomology_constant_zero B X ℓ f
    (AlgebraicClosure k)

/-- The Frobenius on `H⁰(X_k̄, ℚ_ℓ)` is the identity for `X_k̄` connected. -/
theorem rationalFrobenius_zero_eq_id :
    Weil.rationalFrobenius B X f ℓ 0 = LinearMap.id := by
  haveI := Weil.isNoetherian_of_isProper f
  haveI := Weil.quasiSeparatedSpace_of_isProper f
  haveI := fact_ringChar_prime (k := k)
  rw [← Weil.rationalGeometricCompactlySupportedFrobenius_eq_rationalFrobenius B X f ℓ
    (ringChar k) (cardExp k) card_eq_ringChar_pow 0]
  rw [Weil.LAdicSheaf.rationalGeometricCompactlySupportedFrobenius_constant_zero_of_connected B X ℓ
    f (AlgebraicClosure k) (ringChar k) (cardExp k) card_eq_ringChar_pow]
  rfl

theorem charpoly_rationalFrobenius_zero :
    (Weil.rationalFrobenius B X f ℓ 0).charpoly = Polynomial.X - C 1 := by
  rw [rationalFrobenius_zero_eq_id, ← one_smul ℚ_[ℓ] (LinearMap.id : Module.End ℚ_[ℓ] _)]
  exact charpoly_smul_id_of_finrank_eq_one 1 (finrank_rationalCohomology_zero X f ℓ)

end H0

/-! ### `H²` -/

section H2

variable [ConnectedSpace ↥(pullback (Over.mk f).hom (specAlgebraMap k (AlgebraicClosure k)))]

omit [Fintype k] [IsProper f] in
include f in
/-- `X` is connected when `X_k̄` is (the projection `X_k̄ ⟶ X` is surjective). -/
theorem connectedSpace_of_connectedSpace_pullback : ConnectedSpace X.1 := by
  have : Surjective (specAlgebraMap k (AlgebraicClosure k)) := inferInstance
  have h := MorphismProperty.pullback_fst (P := @Surjective) (Over.mk f).hom
    (specAlgebraMap k (AlgebraicClosure k)) this
  exact (pullback.fst (Over.mk f).hom (specAlgebraMap k (AlgebraicClosure k))).surjective.connectedSpace
    (pullback.fst (Over.mk f).hom (specAlgebraMap k (AlgebraicClosure k))).continuous

variable [SmoothOfRelativeDimension 1 f]

/-- **`charpoly(F₂ | H²(X_k̄, ℚ_ℓ)) = X − q`** for `X` connected, proper, smooth of relative
dimension one over `k`, with `X_k̄` connected and a `k`-rational point. -/
theorem charpoly_rationalFrobenius_two (hpt : ∃ s : Spec (.of k) ⟶ X.1, s ≫ f = 𝟙 _) :
    (Weil.rationalFrobenius B X f ℓ 2).charpoly = Polynomial.X - C (Fintype.card k : ℚ_[ℓ]) := by
  haveI := Weil.isNoetherian_of_isProper f
  haveI := Weil.quasiSeparatedSpace_of_isProper f
  haveI := fact_ringChar_prime (k := k)
  have hcard := card_eq_ringChar_pow (k := k)
  have hℓ : ℓ ≠ ringChar k := hℓk.out
  haveI := connectedSpace_of_connectedSpace_pullback X f
  have : Nonempty X.1 := ConnectedSpace.toNonempty
  let x : GeometricPoint X.1 := X.1.algClosedPoint (Classical.arbitrary X.1)
  let F1 := LAdicSheaf.representationSheaf B X x
    (1 : EtaleFundamentalGroup X.1 x →* GL (Fin 1) ℚ_[ℓ]) continuous_const
  have hfd : ∀ i : ℤ, FiniteDimensional ℚ_[ℓ]
      (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f
        (CompactificationOf.ofProper f) (AlgebraicClosure k) F1 i) := fun i =>
    (LAdicSheaf.traceFormula B X ℓ f (CompactificationOf.ofProper f) (AlgebraicClosure k)
      (ringChar k) (cardExp k) hcard hℓ F1).1 i
  have hfd0 : ∀ i : ℤ, FiniteDimensional ℚ_[ℓ]
      (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f
        (CompactificationOf.ofProper f) (AlgebraicClosure k) (LAdicSheaf.constantSystem B X ℓ)
          i) := fun i =>
    (LAdicSheaf.traceFormula B X ℓ f (CompactificationOf.ofProper f) (AlgebraicClosure k)
      (ringChar k) (cardExp k) hcard hℓ (LAdicSheaf.constantSystem B X ℓ)).1 i
  -- transfer of characteristic polynomials `ℱ_𝟏 ↔ ℚ_ℓ`
  have htr : ∀ i : ℤ, (LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B X ℓ f
        (CompactificationOf.ofProper f) (AlgebraicClosure k) (ringChar k) (cardExp k) hcard F1
          i).hom.charpoly =
      (LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B X ℓ f
        (CompactificationOf.ofProper f) (AlgebraicClosure k) (ringChar k) (cardExp k) hcard
          (LAdicSheaf.constantSystem B X ℓ) i).hom.charpoly := fun i => by
    haveI := hfd i; haveI := hfd0 i
    exact Weil.LAdicSheaf.charpoly_rationalGeometricCompactlySupportedFrobenius_representationSheaf_one_eq
      B X x f _ (AlgebraicClosure k) (ringChar k) (cardExp k) hcard i
  -- `H⁰(ℱ_𝟏)`: Frobenius is the identity
  have h0 := htr ((0 : ℕ) : ℤ)
  rw [Weil.rationalGeometricCompactlySupportedFrobenius_eq_rationalFrobenius B X f ℓ (ringChar k)
    (cardExp k) hcard 0, charpoly_rationalFrobenius_zero X f ℓ] at h0
  haveI := hfd ((0 : ℕ) : ℤ)
  have hF0 : (LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B X ℓ f
      (CompactificationOf.ofProper f) (AlgebraicClosure k) (ringChar k) (cardExp k) hcard F1
        0).hom = LinearMap.id := by
    have := eq_smul_id_of_charpoly_eq _ 1 h0
    rw [one_smul] at this
    exact this
  haveI := hfd ((2 * 1 : ℕ) : ℤ)
  obtain ⟨htop, hrank⟩ := LAdicSheaf.rationalFrobenius_top_representationSheaf_one_of_rationalPoint
    B X ℓ f (AlgebraicClosure k) (ringChar k) (cardExp k) hcard hℓ 1 hpt x continuous_const hF0
  have hrank1 : finrank ℚ_[ℓ] (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f
      (CompactificationOf.ofProper f) (AlgebraicClosure k) F1 ((2 * 1 : ℕ) : ℤ)) = 1 := by
    rw [hrank]; exact finrank_eq_one_of_charpoly_eq _ 1 h0
  have h2 := htr ((2 * 1 : ℕ) : ℤ)
  rw [htop, charpoly_smul_id_of_finrank_eq_one _ hrank1,
    Weil.rationalGeometricCompactlySupportedFrobenius_eq_rationalFrobenius B X f ℓ (ringChar k)
      (cardExp k) hcard (2 * 1)] at h2
  rw [← h2, hcard]
  push_cast; ring_nf

end H2

/-! ### The constant sheaf at closed points -/

set_option maxHeartbeats 800000 in
/-- The rational stalk Frobenius of the constant sheaf has all powers of trace `1`. -/
theorem trace_rationalStalkFrobenius_constantSystem_pow (x : closedPoints X.1) (m : ℕ) :
    haveI := Weil.isNoetherian_of_isProper f
    haveI := Weil.quasiSeparatedSpace_of_isProper f
    LinearMap.trace ℚ_[ℓ] _
      (LAdicSheaf.rationalStalkFrobenius B X ℓ (LAdicSheaf.constantSystem B X ℓ) x.1
        (finite_residueField f x.1 x.2) ^ m) = 1 := by
  haveI := Weil.isNoetherian_of_isProper f
  haveI := Weil.quasiSeparatedSpace_of_isProper f
  have hid : LAdicSheaf.rationalStalkFrobenius B X ℓ (LAdicSheaf.constantSystem B X ℓ) x.1
      (finite_residueField f x.1 x.2) = LinearMap.id :=
    Weil.rationalStalkEnd_constantSystem B X ℓ _
  rw [hid]
  rw [← Module.End.one_eq_id, one_pow, LinearMap.trace_one]
  rw [finrank_eq_card_basis (Weil.constantSystemRationalStalkBasis B X ℓ _)]
  simp

/-- The `n`-th point count `#X(k_n)` (`0` for `n = 0`). -/
noncomputable def curvePointCount (n : ℕ) : ℕ :=
  if h : n = 0 then 0 else
    haveI : NeZero n := ⟨h⟩
    pointCountOfDegree f n

theorem curvePointCount_eq (n : ℕ) [NeZero n] : curvePointCount X f n = pointCountOfDegree f n := by
  unfold curvePointCount
  rw [dif_neg (NeZero.ne n)]

/-- **The point side of M2's trace identity for the constant sheaf is `#X(k_n)`.** -/
theorem pointSum_constantSystem (n : ℕ) (hn : n ≠ 0) :
    haveI := Weil.isNoetherian_of_isProper f
    haveI := Weil.quasiSeparatedSpace_of_isProper f
    pointSum B X ℓ f (LAdicSheaf.constantSystem B X ℓ) n = (curvePointCount X f n : ℚ_[ℓ]) := by
  haveI := Weil.isNoetherian_of_isProper f
  haveI := Weil.quasiSeparatedSpace_of_isProper f
  haveI : NeZero n := ⟨hn⟩
  haveI := fact_ringChar_prime (k := k)
  let K := ULift.{u} (FiniteField.Extension k (ringChar k) n)
  have hK : finrank k K = n := by
    rw [(ULift.algEquiv (R := k)
      (A := FiniteField.Extension k (ringChar k) n)).toLinearEquiv.finrank_eq]
    exact FiniteField.finrank_extension k (ringChar k) n
  have : Finite K := Module.finite_of_finite k
  rw [curvePointCount_eq, pointCountOfDegree_eq_pointCount f K hK, pointCount,
    natCard_fieldValuedPoints f K, hK, pointSum]
  simp_rw [trace_rationalStalkFrobenius_constantSystem_pow X f ℓ, mul_one]
  rw [Nat.cast_sum]
  refine finsum_cond_eq_sum_of_cond_iff _ fun {x} _ => ?_
  rw [Finset.mem_filter]
  simp only [closedPointsDegreeLE, Set.Finite.mem_toFinset, Set.mem_setOf_eq]
  exact ⟨fun hd => ⟨Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hd, hd⟩, fun h => h.2⟩

/-! ### Vanishing above degree two and the trace formula -/

section Trace

variable [SmoothOfRelativeDimension 1 f]

include f in
/-- `dim X ≤ 1`. -/
theorem topologicalKrullDim_le_one : topologicalKrullDim X.1 ≤ (1 : ℕ) := by
  rcases isEmpty_or_nonempty X.1 with h | h
  · have : IsEmpty (TopologicalSpace.IrreducibleCloseds X.1) :=
      ⟨fun Z => isEmptyElim Z.isIrreducible.nonempty.some⟩
    rw [topologicalKrullDim, Order.krullDim_eq_bot]; exact bot_le
  · rw [topologicalKrullDim_eq_of_smoothOfRelativeDimension_over_field 1 f]

set_option maxHeartbeats 800000 in
/-- **Tag 03V0 for the constant sheaf on a curve**: for `n ≥ 1`,
`#X(k_n) = tr(F₀ⁿ) − tr(F₁ⁿ) + tr(F₂ⁿ)`. -/
theorem curvePointCount_eq_alternating (n : ℕ) (hn : n ≠ 0) :
    (curvePointCount X f n : ℚ_[ℓ]) =
      LinearMap.trace ℚ_[ℓ] _ (Weil.rationalFrobenius B X f ℓ 0 ^ n) -
        LinearMap.trace ℚ_[ℓ] _ (Weil.rationalFrobenius B X f ℓ 1 ^ n) +
        LinearMap.trace ℚ_[ℓ] _ (Weil.rationalFrobenius B X f ℓ 2 ^ n) := by
  haveI := Weil.isNoetherian_of_isProper f
  haveI := Weil.quasiSeparatedSpace_of_isProper f
  haveI := fact_ringChar_prime (k := k)
  have hcard := card_eq_ringChar_pow (k := k)
  have hℓ : ℓ ≠ ringChar k := hℓk.out
  have h := alternating_trace_pow_eq_pointSum B X ℓ f (CompactificationOf.ofProper f)
    (AlgebraicClosure k) (ringChar k) (cardExp k) hcard hℓ 1 (topologicalKrullDim_le_one X f)
    (LAdicSheaf.constantSystem B X ℓ) hn
  rw [pointSum_constantSystem X f ℓ n hn] at h
  rw [← h, finsum_int_eq_sum_fin 1 _ fun i hi => ?_]
  · have e : ∀ i : Fin (2 * 1 + 1), (if Even ((i : ℕ) : ℤ) then (1 : ℚ_[ℓ]) else -1) *
        LinearMap.trace ℚ_[ℓ]
          (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f
            (CompactificationOf.ofProper f) (AlgebraicClosure k) (LAdicSheaf.constantSystem B X ℓ)
              ((i : ℕ) : ℤ))
          ((LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B X ℓ f
            (CompactificationOf.ofProper f) (AlgebraicClosure k) (ringChar k) (cardExp k) hcard
              (LAdicSheaf.constantSystem B X ℓ) ((i : ℕ) : ℤ)).hom ^ n) =
        (-1) ^ (i : ℕ) * LinearMap.trace ℚ_[ℓ] _ (Weil.rationalFrobenius B X f ℓ i ^ n) :=
      fun i => by
        rw [ite_even_natCast, Weil.rationalGeometricCompactlySupportedFrobenius_eq_rationalFrobenius
          B X f ℓ (ringChar k) (cardExp k) hcard i]
    rw [Finset.sum_congr rfl fun i _ => e i]
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.val_zero, Fin.val_succ, zero_add,
      Nat.reduceAdd, pow_zero, pow_one, one_mul, add_zero]
    ring
  · by_contra hc
    have hns : ¬ Nontrivial (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f
        (CompactificationOf.ofProper f) (AlgebraicClosure k) (LAdicSheaf.constantSystem B X ℓ)
          i) := fun hnt => hc (by
      have := nonneg_and_le_of_nontrivial B X ℓ f (CompactificationOf.ofProper f)
        (AlgebraicClosure k) (ringChar k) (cardExp k) hcard hℓ 1 (topologicalKrullDim_le_one X f)
        (LAdicSheaf.constantSystem B X ℓ) i hnt
      push_cast at this; exact this)
    rw [not_nontrivial_iff_subsingleton] at hns
    exact hi (by simp only [Subsingleton.elim (_ ^ n) (0 : Module.End ℚ_[ℓ] _), map_zero,
      mul_zero])

end Trace

/-! ### Purity of `H¹` -/

/-- **Deligne's purity for `H¹`**: every root `z` of `charpoly F₁` along `ι` has `‖z‖² = q`. -/
theorem norm_sq_eq_card_of_isRoot [Smooth f] (ι : ℚ_[ℓ] →+* ℂ) (z : ℂ)
    (hz : ((Weil.rationalFrobenius B X f ℓ 1).charpoly.map ι).IsRoot z) :
    ‖z‖ ^ 2 = Fintype.card k := by
  have hpure := (Weil.satisfiesWeilEstimate_iff_forall_isCharpolyPureOfWeight B X f).1
    (Weil.satisfiesWeilEstimate B X f) 1 ι z hz
  have h : ‖z‖ = (Fintype.card k : ℝ) ^ ((1 : ℝ) / 2) := by simpa using hpure.norm_eq
  rw [h, ← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _)]
  norm_num

/-! ### The main theorem -/

section Main

variable [Smooth f] [SmoothOfRelativeDimension 1 f]
  [ConnectedSpace ↥(pullback (Over.mk f).hom (specAlgebraMap k (AlgebraicClosure k)))]

/-- **The trace formula on a curve** (`H⁰ = ℚ_ℓ`, `H² = ℚ_ℓ(−1)`):
`#X(k_n) = 1 − tr(F₁ⁿ) + qⁿ` for every `n ≥ 1`. -/
theorem trace_rationalFrobenius_one_pow (hpt : ∃ s : Spec (.of k) ⟶ X.1, s ≫ f = 𝟙 _)
    (n : ℕ) (hn : 1 ≤ n) :
    LinearMap.trace ℚ_[ℓ] _ (Weil.rationalFrobenius B X f ℓ 1 ^ n) =
      (Fintype.card k : ℚ_[ℓ]) ^ n + 1 - curvePointCount X f n := by
  rw [curvePointCount_eq_alternating X f ℓ n (by omega),
    trace_pow_of_charpoly_eq _ _ (charpoly_rationalFrobenius_zero X f ℓ),
    trace_pow_of_charpoly_eq _ _ (charpoly_rationalFrobenius_two X f ℓ hpt), one_pow]
  ring

/-- **M4a (abstract curve form).** For `X` connected, proper, smooth of relative dimension one
over `k` (`#k = q`), with `X_k̄` connected and a `k`-point, `ℓ ≠ char k`: if `dim H¹ = 2` and
`#X(k₃) ∣ #X(k₆)`, then `charpoly(F₁ | H¹(X_k̄, ℚ_ℓ)) = X² − aX + q`, `a = q + 1 − #X(k)`. -/
theorem charpoly_rationalFrobenius_one (hpt : ∃ s : Spec (.of k) ⟶ X.1, s ≫ f = 𝟙 _)
    (hb1 : finrank ℚ_[ℓ] (Weil.rationalCohomology B X f ℓ 1) = 2)
    (hdvd : curvePointCount X f 3 ∣ curvePointCount X f 6) :
    (Weil.rationalFrobenius B X f ℓ 1).charpoly =
      Polynomial.X ^ 2 - C (((Fintype.card k : ℤ) + 1 - curvePointCount X f 1 : ℤ) : ℚ_[ℓ]) * Polynomial.X +
        C (Fintype.card k : ℚ_[ℓ]) := by
  obtain ⟨ι⟩ := nonempty_padic_ringHom_complex ℓ
  exact charpoly_eq_of_pure_of_traces _ hb1 ι (Fintype.card k) Fintype.one_lt_card
    (norm_sq_eq_card_of_isRoot X f ℓ ι) (curvePointCount X f)
    (trace_rationalFrobenius_one_pow X f ℓ hpt) hdvd

/-- **Power-sum form**: `tr(F₁ⁿ) = s_n(a, q) = αⁿ + βⁿ` for all `n`, and
`#X(k_n) = qⁿ + 1 − s_n(a, q)` for `n ≥ 1`. -/
theorem trace_rationalFrobenius_one_pow_eq_frobPowerSum
    (hpt : ∃ s : Spec (.of k) ⟶ X.1, s ≫ f = 𝟙 _)
    (hb1 : finrank ℚ_[ℓ] (Weil.rationalCohomology B X f ℓ 1) = 2)
    (hdvd : curvePointCount X f 3 ∣ curvePointCount X f 6) (n : ℕ) :
    LinearMap.trace ℚ_[ℓ] _ (Weil.rationalFrobenius B X f ℓ 1 ^ n) =
      frobPowerSum ((Fintype.card k : ℤ) + 1 - curvePointCount X f 1) (Fintype.card k) n := by
  obtain ⟨ι⟩ := nonempty_padic_ringHom_complex ℓ
  exact trace_pow_eq_frobPowerSum_of_pure _ hb1 ι (Fintype.card k) Fintype.one_lt_card
    (norm_sq_eq_card_of_isRoot X f ℓ ι) (curvePointCount X f)
    (trace_rationalFrobenius_one_pow X f ℓ hpt) hdvd n

theorem curvePointCount_eq_sub_frobPowerSum (hpt : ∃ s : Spec (.of k) ⟶ X.1, s ≫ f = 𝟙 _)
    (hb1 : finrank ℚ_[ℓ] (Weil.rationalCohomology B X f ℓ 1) = 2)
    (hdvd : curvePointCount X f 3 ∣ curvePointCount X f 6) (n : ℕ) (hn : 1 ≤ n) :
    (curvePointCount X f n : ℤ) = (Fintype.card k : ℤ) ^ n + 1 -
      frobPowerSum ((Fintype.card k : ℤ) + 1 - curvePointCount X f 1) (Fintype.card k) n := by
  obtain ⟨ι⟩ := nonempty_padic_ringHom_complex ℓ
  exact pointCount_eq_sub_frobPowerSum _ hb1 ι (Fintype.card k) Fintype.one_lt_card
    (norm_sq_eq_card_of_isRoot X f ℓ ι) (curvePointCount X f)
    (trace_rationalFrobenius_one_pow X f ℓ hpt) hdvd n hn

/-- **Hasse's bound** `a² ≤ 4q` (from purity; needs only `dim H¹ = 2` and the trace formula). -/
theorem sq_le_four_mul_card (hpt : ∃ s : Spec (.of k) ⟶ X.1, s ≫ f = 𝟙 _)
    (hb1 : finrank ℚ_[ℓ] (Weil.rationalCohomology B X f ℓ 1) = 2) :
    ((Fintype.card k : ℤ) + 1 - curvePointCount X f 1) ^ 2 ≤ 4 * Fintype.card k := by
  obtain ⟨ι⟩ := nonempty_padic_ringHom_complex ℓ
  refine sq_le_four_mul_of_pure _ hb1 ι (Fintype.card k) (norm_sq_eq_card_of_isRoot X f ℓ ι) _ ?_
  have := trace_rationalFrobenius_one_pow X f ℓ hpt 1 le_rfl
  rw [pow_one, pow_one] at this
  rw [this]; push_cast; ring

/-! ### The Weierstrass form -/

/-- **The genus-one input**, as a named hypothesis: `dim H¹(X_k̄, ℚ_ℓ) = 2`. For `X` the plane
cubic of a Weierstrass equation it follows from Stacks'
`LAdicSheaf.finrank_rationalGeometricCompactlySupportedCohomology_constant_one`
(`= 2 · genus X_k̄`, Tag 0C1Z) and `genus_projectionOf` (`= 1`); see `docs/IHARA_CURVE_H1.md`. -/
def HasFirstBettiTwo : Prop := finrank ℚ_[ℓ] (Weil.rationalCohomology B X f ℓ 1) = 2

/-- **The point-count input**, as a named hypothesis: `X` realizes the Weierstrass curve `W`, in
the sense that `#X(k_n) = #W(k_n)` for every `n ≥ 1`, where `#W(k_n)` is Mathlib's
`Nat.card (W.baseChange k_n).toAffine.Point` (affine points plus the point at infinity) and
`k_n = FiniteField.Extension k (char k) n` is the extension used by `pointCountOfDegree`. -/
def RealizesWeierstrass (W : WeierstrassCurve k) : Prop :=
  ∀ n : ℕ, ∀ hn : 1 ≤ n,
    haveI : NeZero n := ⟨by omega⟩
    curvePointCount X f n =
      Nat.card (W.baseChange (FiniteField.Extension k (ringChar k) n)).toAffine.Point

/-- **M4a (Weierstrass form).** Let `W` be a Weierstrass curve over `k` (`#k = q`) and `X` a
connected, proper `B`-scheme, smooth of relative dimension one over `k`, with `X_k̄` connected and
a `k`-point, realizing `W` (`#X(k_n) = #W(k_n)` for `n ≥ 1`) with `dim H¹(X_k̄, ℚ_ℓ) = 2`. Then

`charpoly(Frob | H¹(X_k̄, ℚ_ℓ)) = X² − aX + q`,  `a = q + 1 − #W(k)`,

`#W(k)` being Mathlib's `Nat.card W.toAffine.Point` (the convention of
`WeierstrassCurve.localPolynomial`). -/
theorem charpoly_rationalFrobenius_one_of_weierstrass
    (hpt : ∃ s : Spec (.of k) ⟶ X.1, s ≫ f = 𝟙 _) (W : WeierstrassCurve k)
    (hb1 : HasFirstBettiTwo X f ℓ) (hW : RealizesWeierstrass X f W) :
    (Weil.rationalFrobenius B X f ℓ 1).charpoly =
      Polynomial.X ^ 2 - C (((Fintype.card k : ℤ) + 1 - Nat.card W.toAffine.Point : ℤ) : ℚ_[ℓ]) * Polynomial.X +
        C (Fintype.card k : ℚ_[ℓ]) := by
  haveI := fact_ringChar_prime (k := k)
  have hdvd : curvePointCount X f 3 ∣ curvePointCount X f 6 := by
    have h3 := hW 3 (by norm_num)
    have h6 := hW 6 (by norm_num)
    rw [h3, h6]
    exact natCard_point_extension_dvd (ringChar k) W 3 6 ⟨2, rfl⟩
  have h1 : curvePointCount X f 1 = Nat.card W.toAffine.Point := by
    rw [hW 1 le_rfl, natCard_point_extension_one (ringChar k) W]
  rw [← h1]
  exact charpoly_rationalFrobenius_one X f ℓ hpt hb1 hdvd

/-- **Point counts over every `𝔽_{qⁿ}`** for a realized Weierstrass curve:
`#W(𝔽_{qⁿ}) = qⁿ + 1 − (αⁿ + βⁿ)` (`s_n = αⁿ + βⁿ` via `frobPowerSum`, `α, β` the roots of
`X² − aX + q`), and `tr(Frobⁿ | H¹) = αⁿ + βⁿ`. -/
theorem natCard_point_extension_eq_of_weierstrass
    (hpt : ∃ s : Spec (.of k) ⟶ X.1, s ≫ f = 𝟙 _) (W : WeierstrassCurve k)
    (hb1 : HasFirstBettiTwo X f ℓ) (hW : RealizesWeierstrass X f W) (n : ℕ) (hn : 1 ≤ n) :
    haveI : NeZero n := ⟨by omega⟩
    (Nat.card (W.baseChange (FiniteField.Extension k (ringChar k) n)).toAffine.Point : ℤ) =
      (Fintype.card k : ℤ) ^ n + 1 -
        frobPowerSum ((Fintype.card k : ℤ) + 1 - Nat.card W.toAffine.Point) (Fintype.card k) n ∧
    LinearMap.trace ℚ_[ℓ] _ (Weil.rationalFrobenius B X f ℓ 1 ^ n) =
      frobPowerSum ((Fintype.card k : ℤ) + 1 - Nat.card W.toAffine.Point) (Fintype.card k) n := by
  haveI := fact_ringChar_prime (k := k)
  have hdvd : curvePointCount X f 3 ∣ curvePointCount X f 6 := by
    have h3 := hW 3 (by norm_num)
    have h6 := hW 6 (by norm_num)
    rw [h3, h6]
    exact natCard_point_extension_dvd (ringChar k) W 3 6 ⟨2, rfl⟩
  have h1 : curvePointCount X f 1 = Nat.card W.toAffine.Point := by
    rw [hW 1 le_rfl, natCard_point_extension_one (ringChar k) W]
  refine ⟨?_, ?_⟩
  · have hn' := hW n hn
    rw [← hn', ← h1]
    exact curvePointCount_eq_sub_frobPowerSum X f ℓ hpt hb1 hdvd n hn
  · rw [← h1]
    exact trace_rationalFrobenius_one_pow_eq_frobPowerSum X f ℓ hpt hb1 hdvd n

/-- **Hasse's bound** for a realized Weierstrass curve: `(q + 1 − #W(k))² ≤ 4q`. -/
theorem sq_le_four_mul_card_of_weierstrass (hpt : ∃ s : Spec (.of k) ⟶ X.1, s ≫ f = 𝟙 _)
    (W : WeierstrassCurve k) (hb1 : HasFirstBettiTwo X f ℓ) (hW : RealizesWeierstrass X f W) :
    ((Fintype.card k : ℤ) + 1 - Nat.card W.toAffine.Point) ^ 2 ≤ 4 * Fintype.card k := by
  haveI := fact_ringChar_prime (k := k)
  have h1 : curvePointCount X f 1 = Nat.card W.toAffine.Point := by
    rw [hW 1 le_rfl, natCard_point_extension_one (ringChar k) W]
  rw [← h1]
  exact sq_le_four_mul_card X f ℓ hpt hb1

end Main

end Curve

end RamanujanWeil.Ihara
