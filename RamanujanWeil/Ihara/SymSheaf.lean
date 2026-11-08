import RamanujanWeil.Ihara.SymWeights
import RamanujanWeil.Ihara.FamilyR1
import RamanujanWeil.Ihara.FamilyConnected
import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LAdicSheaves.LisseRepresentation
import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.PointwiseMixedSheaf
import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.IotaRealizableSheaf
import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.WeilIICurveSheafBound
import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.RepresentationSheafTracePow

/-!
# M5: `F = Sym¹⁰ R¹` on `W_p`

Standing context: that of `FamilyR1.lean` (M3): `B : BigEtaleSite.{0}` with the three families of
site instances for `ℤ/ℓⁿ⁺¹`, `ℓ` prime, `W_p = Wp p B` (connected, `FamilyConnected.lean`),
`R1 p B ℓ = R¹π_! ℤ_ℓ`.

Construction.
* `basePt p B`: a geometric point of `W_p` (`W_p` is nonempty, being connected).
* `R1Rep p B ℓ`: the data of Stacks' `exists_representationSheaf_isogeny_of_isLisse` for `R1`:
  a continuous `ρ : π₁(W_p, x̄) → GL_r(ℚ_ℓ)` and an `ℓᴺ`-isogeny `R¹ ⇄ ℱ_ρ`. It is nonempty for
  `ℓ ≠ p` (`nonempty_r1Rep`, from `isLisse_R1`).
* `symRep ρ := Units.map (symHom 10) ∘ ρ : π₁ → GL₁₁(ℚ_ℓ)` for `ρ` of rank `2` (continuous).
* `symSheafOf ρ hρ := ℱ_{Sym¹⁰ ρ}` if `r = 2` (by pattern matching), the rank-1 trivial sheaf
  otherwise. The second branch is never used under the M4 hypothesis, which forces `r = 2`
  (`R1Rep.rank_eq_two`); it only makes `F` a total definition.
* **`symR1 p B ℓ := symSheafOf ρ hρ`** for the chosen `R1Rep` (classical choice; for `ℓ = p`,
  where `R¹` is not known to be lisse, a junk value).

Hypothesis (frozen M4 interface, discharged by M4b):
`R1StalkCharpoly p B ℓ : Prop` — at every closed point `y` of `W_p`, with `q_y = p^{deg y}`,
there is `a ∈ ℤ` with `a² ≤ 4 q_y` (Hasse) and
`charpoly(π_y | R¹_ȳ ⊗ ℚ_ℓ) = X² − aX + q_y`.

Results (`ℓ ≠ p`):
* `isLisse_symR1` (unconditional, even for `ℓ = p`);
* `stalkTrace_symR1`: `tr(π_yᵐ | F_ȳ) = symTrace 10 t (p^{deg y · m})` whenever
  `tr(π_yᵐ | R¹_ȳ) = t ∈ ℤ`, and `exists_stalkTrace_symR1` (with `t = s_m(a_y, q_y)`);
* `mixed_symR1`: pointwise `ι`-mixed of weights `≤ 10` over `𝔽_p` (`q = p^1`), for every `ι`;
* `realizable_symR1`: `ι`-realizable (witness `F' = F`; all stalk traces are integers).
-/

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.SmallEtale Stacks.EtaleCohomology
  Stacks.Frobenius

noncomputable section

namespace RamanujanWeil.Ihara

/-! ### `Sym¹⁰` of a representation -/

section Rep

variable {G : Type*} [Group G] [TopologicalSpace G] {K : Type*} [Field K] [TopologicalSpace K]
  [IsTopologicalRing K]

/-- `Sym¹⁰ ρ : G → GL₁₁(K)` for `ρ : G → GL₂(K)`. -/
def symRep (ρ : G →* GL (Fin 2) K) : G →* GL (Fin (10 + 1)) K :=
  (Units.map (symHom (R := K) 10)).comp ρ

omit [TopologicalSpace G] [TopologicalSpace K] [IsTopologicalRing K] in
theorem symRep_val (ρ : G →* GL (Fin 2) K) (g : G) :
    (symRep ρ g).val = symMat 10 (ρ g).val := rfl

theorem continuous_symRep {ρ : G →* GL (Fin 2) K} (hρ : Continuous ρ) : Continuous (symRep ρ) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · exact (continuous_symMat (R := K) 10).comp (Units.continuous_val.comp hρ)
  · have : (fun g => ((symRep ρ g)⁻¹).val) = fun g => symMat 10 ((ρ g)⁻¹).val := by
      funext g
      rw [symRep, MonoidHom.comp_apply, ← map_inv]
      rfl
    rw [this]
    exact (continuous_symMat (R := K) 10).comp (Units.continuous_coe_inv.comp hρ)

end Rep

attribute [local instance] HasDerivedCategory.standard moduleCat_hasLimitsOfSize

variable (p : ℕ) [Fact p.Prime] (B : BigEtaleSite.{0})

instance : ConnectedSpace (Wp p B).1 := inferInstanceAs (ConnectedSpace (Family.base p))

/-- A geometric point of `W_p`. -/
def basePt : GeometricPoint (Wp p B).1 :=
  geometricPointAt _ (Classical.arbitrary (Wp p B).1)

variable (ℓ : ℕ) [Fact ℓ.Prime]
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

/-- The sheaf `ℱ_{Sym¹⁰ ρ}` when `ρ` has rank `2`; the trivial rank-one sheaf otherwise. -/
def symSheafOf : ∀ {r : ℕ} (ρ : EtaleFundamentalGroup (Wp p B).1 (basePt p B) →* GL (Fin r) ℚ_[ℓ]),
    Continuous ρ → LAdicSheaf.{0, 1} B (Wp p B) ℓ
  | 2, ρ, hρ => LAdicSheaf.representationSheaf B (Wp p B) (basePt p B) (symRep ρ)
      (continuous_symRep hρ)
  | _, _, _ => LAdicSheaf.representationSheaf B (Wp p B) (basePt p B)
      (1 : EtaleFundamentalGroup (Wp p B).1 (basePt p B) →* GL (Fin 1) ℚ_[ℓ]) continuous_const

theorem isLisse_symSheafOf {r : ℕ}
    (ρ : EtaleFundamentalGroup (Wp p B).1 (basePt p B) →* GL (Fin r) ℚ_[ℓ]) (hρ : Continuous ρ) :
    (symSheafOf p B ℓ ρ hρ).IsLisse := by
  unfold symSheafOf
  split <;> exact LAdicSheaf.representationSheaf_isLisse _ _ _ _ _

set_option maxHeartbeats 1000000 in
/-- The data of `exists_representationSheaf_isogeny_of_isLisse` for `R¹`: a continuous
`ρ : π₁(W_p, x̄) → GL_r(ℚ_ℓ)` with an `ℓᴺ`-isogeny `R¹ ⇄ ℱ_ρ`. -/
structure R1Rep where
  r : ℕ
  ρ : EtaleFundamentalGroup (Wp p B).1 (basePt p B) →* GL (Fin r) ℚ_[ℓ]
  hρ : Continuous ρ
  φ : R1 p B ℓ ⟶ LAdicSheaf.representationSheaf B (Wp p B) (basePt p B) ρ hρ
  ψ : LAdicSheaf.representationSheaf B (Wp p B) (basePt p B) ρ hρ ⟶ R1 p B ℓ
  N : ℕ
  h₁ : φ ≫ ψ = (ℓ ^ N) • 𝟙 (R1 p B ℓ)
  h₂ : ψ ≫ φ = (ℓ ^ N) • 𝟙 (LAdicSheaf.representationSheaf B (Wp p B) (basePt p B) ρ hρ)

theorem nonempty_r1Rep (hℓp : ℓ ≠ p) : Nonempty (R1Rep p B ℓ) := by
  obtain ⟨r, ρ, hρ, φ, ψ, N, h₁, h₂⟩ :=
    LAdicSheaf.exists_representationSheaf_isogeny_of_isLisse ℓ B (Wp p B) (basePt p B) (R1 p B ℓ)
      (isLisse_R1 p B ℓ hℓp)
  exact ⟨⟨r, ρ, hρ, φ, ψ, N, h₁, h₂⟩⟩

open scoped Classical in
/-- **`F = Sym¹⁰ R¹`**, an ℓ-adic sheaf on `W_p`: `ℱ_{Sym¹⁰ ρ}` for the representation `ρ` of
`R¹` (`ℓ ≠ p`). -/
def symR1 : LAdicSheaf.{0, 1} B (Wp p B) ℓ :=
  if h : Nonempty (R1Rep p B ℓ) then symSheafOf p B ℓ h.some.ρ h.some.hρ
  else LAdicSheaf.representationSheaf B (Wp p B) (basePt p B)
      (1 : EtaleFundamentalGroup (Wp p B).1 (basePt p B) →* GL (Fin 1) ℚ_[ℓ]) continuous_const

/-- **`F` is lisse.** -/
theorem isLisse_symR1 : (symR1 p B ℓ).IsLisse := by
  unfold symR1
  split
  · exact isLisse_symSheafOf p B ℓ _ _
  · exact LAdicSheaf.representationSheaf_isLisse _ _ _ _ _

theorem symR1_eq (hℓp : ℓ ≠ p) :
    ∃ D : R1Rep p B ℓ, symR1 p B ℓ = symSheafOf p B ℓ D.ρ D.hρ := by
  refine ⟨(nonempty_r1Rep p B ℓ hℓp).some, ?_⟩
  unfold symR1
  rw [dite_cond_eq_true (eq_true (nonempty_r1Rep p B ℓ hℓp))]

/-! ### The M4 interface -/

/-- **Frozen M4 interface (hypothesis).** At every closed point `y` of `W_p`, with
`q_y = p^{deg y}` (`deg y = [κ(y) : 𝔽_p]`), the geometric Frobenius on the rational stalk of `R¹`
has characteristic polynomial `X² − a X + q_y` for an integer `a` with `a² ≤ 4 q_y` (Hasse). -/
def R1StalkCharpoly : Prop :=
  ∀ y : closedPoints (Wp p B).1, ∃ a : ℤ,
    a ^ 2 ≤ 4 * (p : ℤ) ^ residueDegree (toSpecK p B) y.1 ∧
    (LAdicSheaf.rationalStalkFrobenius B (Wp p B) ℓ (R1 p B ℓ) y.1
        (finite_residueField (toSpecK p B) y.1 y.2)).charpoly =
      Polynomial.X ^ 2 - Polynomial.C (a : ℚ_[ℓ]) * Polynomial.X + Polynomial.C ((p : ℚ_[ℓ]) ^ residueDegree (toSpecK p B) y.1)

variable {p B ℓ}

/-- The geometric Frobenius element at `y` and its matrix under `ρ`. -/
abbrev R1Rep.frob (D : R1Rep p B ℓ) (y : closedPoints (Wp p B).1) : Matrix (Fin D.r) (Fin D.r) ℚ_[ℓ] :=
  (D.ρ (geometricFrobeniusFamily (toSpecK p B) (basePt p B) y)).val

/-- Transport across the isogeny: the stalk Frobenius of `R¹` at `y` and `ρ(F_y)` have the same
characteristic polynomial. -/
theorem R1Rep.charpoly_frob (D : R1Rep p B ℓ) (y : closedPoints (Wp p B).1) :
    (LAdicSheaf.rationalStalkFrobenius B (Wp p B) ℓ (R1 p B ℓ) y.1
        (finite_residueField (toSpecK p B) y.1 y.2)).charpoly = (D.frob y).charpoly := by
  have := finite_residueField (toSpecK p B) y.1 y.2
  have h := LAdicSheaf.charpoly_rationalStalkEnd_of_isogeny B (Wp p B) ℓ D.φ D.ψ D.N D.h₁ D.h₂
    (frobeniusPointHom (Wp p B).1 y.1)
  exact h.trans (charpoly_rationalStalkFrobenius_representationSheaf_eq B (Wp p B) (basePt p B)
    (toSpecK p B) D.ρ D.hρ y)

theorem R1Rep.rank_eq_two (D : R1Rep p B ℓ) (H : R1StalkCharpoly p B ℓ)
    (y : closedPoints (Wp p B).1) : D.r = 2 := by
  obtain ⟨a, -, ha⟩ := H y
  have h := congrArg Polynomial.natDegree ((D.charpoly_frob y).symm.trans ha)
  rwa [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin, natDegree_quadratic_monic] at h

/-! ### Stalks of `F` -/

/-- For a rank-two representation, the stalk Frobenius of `ℱ_{Sym¹⁰ ρ}` at `y` has the
characteristic polynomial of `Sym¹⁰ ρ(F_y)`. -/
theorem charpoly_symSheafOf_two
    (ρ : EtaleFundamentalGroup (Wp p B).1 (basePt p B) →* GL (Fin 2) ℚ_[ℓ]) (hρ : Continuous ρ)
    (y : closedPoints (Wp p B).1) :
    (LAdicSheaf.rationalStalkFrobenius B (Wp p B) ℓ (symSheafOf p B ℓ ρ hρ) y.1
        (finite_residueField (toSpecK p B) y.1 y.2)).charpoly =
      (symMat 10 (ρ (geometricFrobeniusFamily (toSpecK p B) (basePt p B) y)).val).charpoly :=
  charpoly_rationalStalkFrobenius_representationSheaf_eq B (Wp p B) (basePt p B)
    (toSpecK p B) (symRep ρ) (continuous_symRep hρ) y

theorem trace_symSheafOf_two
    (ρ : EtaleFundamentalGroup (Wp p B).1 (basePt p B) →* GL (Fin 2) ℚ_[ℓ]) (hρ : Continuous ρ)
    (y : closedPoints (Wp p B).1) (m : ℕ) :
    LinearMap.trace ℚ_[ℓ] _
        (LAdicSheaf.rationalStalkFrobenius B (Wp p B) ℓ (symSheafOf p B ℓ ρ hρ) y.1
          (finite_residueField (toSpecK p B) y.1 y.2) ^ m) =
      symTraceR 10 (((ρ (geometricFrobeniusFamily (toSpecK p B) (basePt p B) y)).val ^ m).trace)
        ((ρ (geometricFrobeniusFamily (toSpecK p B) (basePt p B) y)).val.det ^ m) :=
  (trace_rationalStalkFrobenius_representationSheaf_pow B (Wp p B) (basePt p B)
    (toSpecK p B) (symRep ρ) (continuous_symRep hρ) y m).trans (trace_symMat_ten_pow _ m)

/-- The pointwise statement in terms of the data `(a_y, q_y)` of `R1StalkCharpoly`, for a
rank-two `ρ` whose Frobenius matrices have charpoly `X² − a X + q`. -/
theorem stalk_symSheafOf_two
    (ρ : EtaleFundamentalGroup (Wp p B).1 (basePt p B) →* GL (Fin 2) ℚ_[ℓ]) (hρ : Continuous ρ)
    (y : closedPoints (Wp p B).1) (a q : ℤ)
    (h : (ρ (geometricFrobeniusFamily (toSpecK p B) (basePt p B) y)).val.charpoly =
      Polynomial.X ^ 2 - Polynomial.C (a : ℚ_[ℓ]) * Polynomial.X + Polynomial.C (q : ℚ_[ℓ])) (m : ℕ) :
    ((ρ (geometricFrobeniusFamily (toSpecK p B) (basePt p B) y)).val ^ m).trace =
        (powSum a q m : ℚ_[ℓ]) ∧
    LinearMap.trace ℚ_[ℓ] _
        (LAdicSheaf.rationalStalkFrobenius B (Wp p B) ℓ (symSheafOf p B ℓ ρ hρ) y.1
          (finite_residueField (toSpecK p B) y.1 y.2) ^ m) =
      ((symTrace 10 (powSum a q m) (q ^ m) : ℤ) : ℚ_[ℓ]) := by
  obtain ⟨ha, hq⟩ := trace_det_of_charpoly _ _ _ h
  have ht := trace_pow_eq_powSum _ a q ha hq m
  refine ⟨ht, ?_⟩
  rw [trace_symSheafOf_two, ht, hq, Int.cast_symTrace]
  push_cast
  rfl

/-! ### Main results -/

variable (p B ℓ)

/-- **Stalk traces of `F`**, in closed form: at every closed point `y` there is `a_y ∈ ℤ` with
`charpoly(π_y | R¹) = X² − a_y X + q_y`, and for every `m`,
`tr(π_yᵐ | R¹_ȳ) = s_m(a_y, q_y)` (`powSum`) and
`tr(π_yᵐ | F_ȳ) = symTrace 10 (s_m(a_y, q_y)) (q_yᵐ)`, `q_y = p^{deg y}`. -/
theorem exists_stalkTrace_symR1 (hℓp : ℓ ≠ p) (H : R1StalkCharpoly p B ℓ)
    (y : closedPoints (Wp p B).1) :
    ∃ a : ℤ, a ^ 2 ≤ 4 * (p : ℤ) ^ residueDegree (toSpecK p B) y.1 ∧
      (LAdicSheaf.rationalStalkFrobenius B (Wp p B) ℓ (R1 p B ℓ) y.1
        (finite_residueField (toSpecK p B) y.1 y.2)).charpoly =
        Polynomial.X ^ 2 - Polynomial.C (a : ℚ_[ℓ]) * Polynomial.X + Polynomial.C ((p : ℚ_[ℓ]) ^ residueDegree (toSpecK p B) y.1) ∧
      ∀ m : ℕ,
        LinearMap.trace ℚ_[ℓ] _ (LAdicSheaf.rationalStalkFrobenius B (Wp p B) ℓ (R1 p B ℓ) y.1
          (finite_residueField (toSpecK p B) y.1 y.2) ^ m) =
          (powSum a ((p : ℤ) ^ residueDegree (toSpecK p B) y.1) m : ℚ_[ℓ]) ∧
        LinearMap.trace ℚ_[ℓ] _ (LAdicSheaf.rationalStalkFrobenius B (Wp p B) ℓ (symR1 p B ℓ) y.1
          (finite_residueField (toSpecK p B) y.1 y.2) ^ m) =
          ((symTrace 10 (powSum a ((p : ℤ) ^ residueDegree (toSpecK p B) y.1) m)
            ((p : ℤ) ^ (residueDegree (toSpecK p B) y.1 * m)) : ℤ) : ℚ_[ℓ]) := by
  obtain ⟨D, hD⟩ := symR1_eq p B ℓ hℓp
  obtain ⟨a, hhasse, ha⟩ := H y
  refine ⟨a, hhasse, ha, fun m => ?_⟩
  rw [hD]
  have hc := D.charpoly_frob y
  have htr := trace_pow_eq_of_charpoly_eq _ _ hc m
  rw [htr]
  obtain ⟨r, ρ, hρ, φ, ψ, N, h₁, h₂⟩ := D
  have hr : r = 2 := R1Rep.rank_eq_two ⟨r, ρ, hρ, φ, ψ, N, h₁, h₂⟩ H y
  subst hr
  have hcp : (ρ (geometricFrobeniusFamily (toSpecK p B) (basePt p B) y)).val.charpoly =
      Polynomial.X ^ 2 - Polynomial.C (a : ℚ_[ℓ]) * Polynomial.X +
        Polynomial.C ((((p : ℤ) ^ residueDegree (toSpecK p B) y.1 : ℤ)) : ℚ_[ℓ]) := by
    rw [show ((((p : ℤ) ^ residueDegree (toSpecK p B) y.1 : ℤ)) : ℚ_[ℓ]) =
      (p : ℚ_[ℓ]) ^ residueDegree (toSpecK p B) y.1 by push_cast; rfl, ← ha]
    exact hc.symm
  have := stalk_symSheafOf_two ρ hρ y a _ hcp m
  rw [this.1, this.2, pow_mul]
  exact ⟨rfl, rfl⟩

/-- **`tr(π_yᵐ | F_ȳ) = symTrace 10 (tr(π_yᵐ | R¹_ȳ)) (p^{deg y · m})`**, for any integer value
`t` of the `R¹` trace (which is an integer, `exists_stalkTrace_symR1`). -/
theorem stalkTrace_symR1 (hℓp : ℓ ≠ p) (H : R1StalkCharpoly p B ℓ)
    (y : closedPoints (Wp p B).1) (m : ℕ) (t : ℤ)
    (ht : LinearMap.trace ℚ_[ℓ] _ (LAdicSheaf.rationalStalkFrobenius B (Wp p B) ℓ (R1 p B ℓ) y.1
      (finite_residueField (toSpecK p B) y.1 y.2) ^ m) = (t : ℚ_[ℓ])) :
    LinearMap.trace ℚ_[ℓ] _ (LAdicSheaf.rationalStalkFrobenius B (Wp p B) ℓ (symR1 p B ℓ) y.1
        (finite_residueField (toSpecK p B) y.1 y.2) ^ m) =
      ((symTrace 10 t ((p : ℤ) ^ (residueDegree (toSpecK p B) y.1 * m)) : ℤ) : ℚ_[ℓ]) := by
  obtain ⟨a, -, -, h⟩ := exists_stalkTrace_symR1 p B ℓ hℓp H y
  obtain ⟨h1, h2⟩ := h m
  have : t = powSum a ((p : ℤ) ^ residueDegree (toSpecK p B) y.1) m :=
    Int.cast_injective (α := ℚ_[ℓ]) (ht.symm.trans h1)
  rw [h2, this]

/-- **`F` is pointwise `ι`-mixed of weights `≤ 10`** (over `𝔽_p`, `q = p¹`), for every `ι`:
the stalk Frobenius eigenvalues at `y` are `αᵇ β¹⁰⁻ᵇ` with `|α| = |β| = q_y^{1/2}` (Hasse). -/
theorem mixed_symR1 (hℓp : ℓ ≠ p) (H : R1StalkCharpoly p B ℓ) (ι : ℚ_[ℓ] →+* ℂ) :
    LAdicSheaf.IsPointwiseMixedOfWeightLE B (Wp p B) ℓ (toSpecK p B) (symR1 p B ℓ) (p ^ 1) ι 10 := by
  intro y z hz
  obtain ⟨D, hD⟩ := symR1_eq p B ℓ hℓp
  obtain ⟨a, hhasse, ha⟩ := H y
  have hc := D.charpoly_frob y
  rw [hD] at hz
  obtain ⟨r, ρ, hρ, φ, ψ, N, h₁, h₂⟩ := D
  have hr : r = 2 := R1Rep.rank_eq_two ⟨r, ρ, hρ, φ, ψ, N, h₁, h₂⟩ H y
  subst hr
  set d := residueDegree (toSpecK p B) y.1
  set g := (ρ (geometricFrobeniusFamily (toSpecK p B) (basePt p B) y)).val
  have hcp : g.charpoly = Polynomial.X ^ 2 - Polynomial.C (a : ℚ_[ℓ]) * Polynomial.X + Polynomial.C ((p : ℚ_[ℓ]) ^ d) := by
    rw [← ha]; exact hc.symm
  obtain ⟨htr, hdet⟩ := trace_det_of_charpoly _ _ _ hcp
  rw [charpoly_symSheafOf_two, ← Matrix.charpoly_map, symMat_map] at hz
  set G := g.map ι
  have hGtr : G.trace = ((a : ℝ) : ℂ) := by
    rw [show G.trace = ι g.trace from (AddMonoidHom.map_trace (ι : ℚ_[ℓ] →+ ℂ) g).symm, htr]
    simp
  have hGdet : G.det = (((p : ℝ) ^ d : ℝ) : ℂ) := by
    rw [show G.det = ι g.det from (RingHom.map_det ι g).symm, hdet]
    simp
  obtain ⟨α, β, hs, hp⟩ := exists_add_mul_eq G.trace G.det
  have hd : (a : ℝ) ^ 2 ≤ 4 * (p : ℝ) ^ d := by exact_mod_cast hhasse
  have hα := norm_sq_eq_of_sq_le α β a ((p : ℝ) ^ d) (hs.trans hGtr) (hp.trans hGdet) hd
  have hβ := norm_sq_eq_of_sq_le β α a ((p : ℝ) ^ d) ((add_comm β α).trans (hs.trans hGtr))
    ((mul_comm β α).trans (hp.trans hGdet)) hd
  rw [charpoly_symMat_ten G α β hs hp, Polynomial.IsRoot, Polynomial.eval_prod,
    Finset.prod_eq_zero_iff] at hz
  obtain ⟨b, -, hb⟩ := hz
  rw [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, sub_eq_zero] at hb
  refine ⟨10, le_rfl, ?_⟩
  have hb10 : (b : ℕ) ≤ 10 := Nat.lt_succ_iff.1 b.2
  have hsq : ‖z‖ ^ 2 = (((p : ℝ) ^ (5 * d)) ^ 2) := by
    rw [hb, norm_mul, norm_pow, norm_pow, mul_pow, ← pow_mul, ← pow_mul, mul_comm (b : ℕ) 2,
      mul_comm (10 - (b : ℕ)) 2, pow_mul, pow_mul, hα, hβ, ← pow_add, Nat.add_sub_cancel' hb10,
      ← pow_mul, ← pow_mul]
    ring_nf
  have hn : ‖z‖ = (p : ℝ) ^ (5 * d) :=
    (sq_eq_sq₀ (norm_nonneg _) (by positivity)).1 hsq
  rw [hn, pow_one]
  rw [show ((d : ℤ) * (10 : ℤ) : ℝ) / 2 = ((5 * d : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]

/-- **`F` is `ι`-realizable** for every `ι`: take `F' = F`; all stalk traces of `F` are integers. -/
theorem realizable_symR1 (hℓp : ℓ ≠ p) (H : R1StalkCharpoly p B ℓ) (ι : ℚ_[ℓ] →+* ℂ) :
    LAdicSheaf.IsIotaRealizable B (Wp p B) ℓ (toSpecK p B) (symR1 p B ℓ) ι := by
  refine ⟨symR1 p B ℓ, isLisse_symR1 p B ℓ, fun y n _ => ?_⟩
  obtain ⟨a, -, -, h⟩ := exists_stalkTrace_symR1 p B ℓ hℓp H y
  rw [(h n).2, ← two_mul, map_mul, map_ofNat, map_intCast]
  exact ⟨2 * _, by push_cast; rfl⟩

end RamanujanWeil.Ihara

end
