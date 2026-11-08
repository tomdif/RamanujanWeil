import RamanujanWeil.Ihara.PointsFibre
import RamanujanWeil.Ihara.FamilyPackage
import RamanujanWeil.Bridge

/-!
# M6 (C): assembly — `IharaIdentity p` + M4b ⇒ `τ(p)² ≤ 4 p¹¹`

* `S_eq_pointSum`: for `n ≥ 1`, the point side of the Lefschetz package of `F = Sym¹⁰ R¹` on
  `W_p` is the frozen M1 sum,
  `pointSum B (Wp p B) ℓ (toSpecK p B) (symR1 p B ℓ) n = (weierstrassSum p n : ℚ_[ℓ])`,
  `weierstrassSum p n = Σ_{c ∈ 𝔽_{pⁿ}⁵, Δ(c) ≠ 0} symTrace 10 (traceOfFrob (wc c)) (pⁿ)`.
  Conditional only on the frozen M4b interface `R1StalkCharpolyFibre p B ℓ`.
* `deligneBound_of_ihara_M4b`: `R1StalkCharpolyFibre p B ℓ → IharaIdentity p → τ(p)² ≤ 4 p¹¹`,
  chaining `lefschetzPackage_Wp` (M2+M3), `isLisse/mixed/realizable_symR1` (M5),
  `congrQ`/`congrP` (M2), `elim_deligne` and `deligne_of_package` (M1) with `d = 5`
  (`IharaIdentity` has the factor `p^{3n} = p^{(5−2)n}`).
-/

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.SmallEtale Stacks.EtaleCohomology

noncomputable section

namespace RamanujanWeil.Ihara

attribute [local instance] HasDerivedCategory.standard moduleCat_hasLimitsOfSize

variable (p : ℕ) [Fact p.Prime] (B : BigEtaleSite.{0}) (ℓ : ℕ) [Fact ℓ.Prime]
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

set_option maxHeartbeats 1000000 in
/-- **`S_eq_pointSum` (M6 headline).** For `n ≥ 1`, the point side of the Lefschetz package of
`Sym¹⁰ R¹` on `W_p` is the integer Weierstrass sum of `IharaIdentity`. -/
theorem S_eq_pointSum (hℓp : ℓ ≠ p) (H : R1StalkCharpolyFibre p B ℓ) (n : ℕ) (hn : 1 ≤ n) :
    pointSum B (Wp p B) ℓ (toSpecK p B) (symR1 p B ℓ) n = (weierstrassSum p n : ℚ_[ℓ]) := by
  classical
  letI : Fintype (GaloisField p n) := Fintype.ofFinite _
  have hK : Module.finrank (ZMod p) (GaloisField p n) = n := GaloisField.finrank p (by omega)
  have h1 := Family.finsum_closedPoints_eq_sum p (GaloisField p n) (M := ℚ_[ℓ]) n hK
    (fun y => LinearMap.trace ℚ_[ℓ] _ (LAdicSheaf.rationalStalkFrobenius B (Wp p B) ℓ
      (symR1 p B ℓ) y.1 (finite_residueField (toSpecK p B) y.1 y.2) ^
        (n / residueDegree (toSpecK p B) y.1)))
  rw [pointSum]
  refine Eq.trans h1 ?_
  refine (Finset.sum_congr rfl fun c _ => stalkTrace_symR1_fvpOf p B ℓ hℓp H n hK c.1 c.2).trans ?_
  rw [weierstrassSum, Int.cast_sum]
  refine (Finset.sum_subtype (p := fun c : Fin 5 → GaloisField p n => (wc c).Δ ≠ 0) _
    (fun c => by simp)
    (fun c => ((symTrace 10 (traceOfFrob (wc c)) ((p : ℤ) ^ n) : ℤ) : ℚ_[ℓ]))).symm

/-- **M6 assembly.** Given the frozen M4b interface at `p` (for one big étale site `B` and one
prime `ℓ ≠ p`) and the Ihara–Birch identity at `p`, Deligne's bound `τ(p)² ≤ 4 p¹¹` holds. -/
theorem deligneBound_of_ihara_M4b (hℓp : ℓ ≠ p) (H : R1StalkCharpolyFibre p B ℓ)
    (hI : IharaIdentity p) : RamanujanTau.tau p ^ 2 ≤ 4 * (p : ℤ) ^ 11 := by
  obtain ⟨ι⟩ := RamanujanWeil.nonempty_padic_ringHom_complex ℓ
  obtain ⟨L⟩ := lefschetzPackage_Wp p B ℓ hℓp ι (symR1 p B ℓ) 10 (isLisse_symR1 p B ℓ)
    (mixed_symR1 p B ℓ hℓp H.toR1StalkCharpoly ι) (realizable_symR1 p B ℓ hℓp H.toR1StalkCharpoly ι)
  exact ((L.congrQ (pow_one p)).congrP (P' := fun n => (weierstrassSum p n : ℚ_[ℓ]))
    (S_eq_pointSum p B ℓ hℓp H)).elim_deligne fun V _ _ _ F hw htr =>
      deligne_of_package p 5 (by norm_num) ℚ_[ℓ] ι V F hw (weierstrassSum p) htr
        (weierstrassSum_eq_of_ihara hI)

end RamanujanWeil.Ihara
