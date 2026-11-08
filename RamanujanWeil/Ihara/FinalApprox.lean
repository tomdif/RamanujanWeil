import RamanujanWeil.Ihara.M4b
import RamanujanWeil.Ihara.EndgameApprox
import RamanujanWeil.Bridge

/-!
# M1′b: the approximate Ihara–Birch identity implies Deligne's bound for `τ`

Near-copy of `Assembly.lean` + `M4b.lean` + `Final.lean`, with the M1 call
(`deligne_of_package`) swapped for the M1′ endgame (`deligne_of_package_iharaApprox`, i.e.
`deligne_of_package_approx` at `d = 5`).

* `deligneBound_of_iharaApprox`: for a big étale site `B` and a prime `ℓ ≠ p`,
  `IharaApprox p ⇒ τ(p)² ≤ 4 p¹¹` (M4b discharged by `r1StalkCharpolyFibre`).
* `deligneBound_of_iharaApprox_prime`: the same with `B` and `ℓ` chosen inside the proof.
* `deligneBound_of_iharaApprox_all`: `(∀ p [Fact p.Prime], IharaApprox p) → DeligneBound`.
-/

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.SmallEtale Stacks.EtaleCohomology

noncomputable section

namespace RamanujanWeil.Ihara

attribute [local instance] HasDerivedCategory.standard moduleCat_hasLimitsOfSize

section Site

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

/-- **M6 assembly, approximate form.** Given the M4b interface at `p` and `IharaApprox p`,
Deligne's bound `τ(p)² ≤ 4 p¹¹` holds. -/
theorem deligneBound_of_iharaApprox_M4b (hℓp : ℓ ≠ p) (H : R1StalkCharpolyFibre p B ℓ)
    (hA : IharaApprox p) : RamanujanTau.tau p ^ 2 ≤ 4 * (p : ℤ) ^ 11 := by
  obtain ⟨ι⟩ := RamanujanWeil.nonempty_padic_ringHom_complex ℓ
  obtain ⟨L⟩ := lefschetzPackage_Wp p B ℓ hℓp ι (symR1 p B ℓ) 10 (isLisse_symR1 p B ℓ)
    (mixed_symR1 p B ℓ hℓp H.toR1StalkCharpoly ι)
    (realizable_symR1 p B ℓ hℓp H.toR1StalkCharpoly ι)
  exact ((L.congrQ (pow_one p)).congrP (P' := fun n => (weierstrassSum p n : ℚ_[ℓ]))
    (S_eq_pointSum p B ℓ hℓp H)).elim_deligne fun V _ _ _ F hw htr =>
      deligne_of_package_iharaApprox p ℚ_[ℓ] ι V F hw htr hA

include B in
/-- **Approximate Ihara–Birch ⇒ Deligne at `p`** (any big étale site `B`, any prime `ℓ ≠ p`). -/
theorem deligneBound_of_iharaApprox (hℓp : ℓ ≠ p) (hA : IharaApprox p) :
    RamanujanTau.tau p ^ 2 ≤ 4 * (p : ℤ) ^ 11 :=
  deligneBound_of_iharaApprox_M4b p B ℓ hℓp (r1StalkCharpolyFibre p B ℓ hℓp) hA

end Site

/-- **M1′b (frozen).** For a prime `p`, `IharaApprox p ⇒ τ(p)² ≤ 4 p¹¹`; the big étale site and
the auxiliary prime `ℓ ≠ p` are chosen inside the proof. -/
theorem deligneBound_of_iharaApprox_prime (p : ℕ) [Fact p.Prime] (h : IharaApprox p) :
    RamanujanTau.tau p ^ 2 ≤ 4 * (p : ℤ) ^ 11 := by
  obtain ⟨ℓ, hℓle, hℓ⟩ := Nat.exists_infinite_primes (p + 1)
  have : Fact ℓ.Prime := ⟨hℓ⟩
  exact deligneBound_of_iharaApprox p (BigEtaleSite.containing (Spec (.of (ZMod p)))) ℓ
    (by omega) h

/-- **M1′b (frozen).** `IharaApprox` at every prime implies Deligne's bound. -/
theorem deligneBound_of_iharaApprox_all :
    (∀ (p : ℕ) [Fact p.Prime], IharaApprox p) → RamanujanTau.DeligneBound := fun hA =>
  ⟨fun p hp => by
    have : Fact p.Prime := ⟨hp⟩
    exact deligneBound_of_iharaApprox_prime p (hA p)⟩

end RamanujanWeil.Ihara
