import RamanujanWeil.Ihara.M4b
import RamanujanWeil.Bridge

/-!
# Final: the Ihara–Birch identity implies Deligne's bound for `τ`

`deligneBound_of_ihara_prime`: for a prime `p`, `IharaIdentity p ⇒ τ(p)² ≤ 4 p¹¹`, with the big
étale site and the auxiliary prime `ℓ ≠ p` chosen inside the proof (all site-instance families
are found by instance search for every `B`).

`deligneBound_of_ihara_all`: `(∀ p [Fact p.Prime], IharaIdentity p) → RamanujanTau.DeligneBound`.
-/

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.SmallEtale Stacks.EtaleCohomology

namespace RamanujanWeil.Ihara

attribute [local instance] HasDerivedCategory.standard moduleCat_hasLimitsOfSize

theorem deligneBound_of_ihara_prime (p : ℕ) [Fact p.Prime] (hI : IharaIdentity p) :
    RamanujanTau.tau p ^ 2 ≤ 4 * (p : ℤ) ^ 11 := by
  obtain ⟨ℓ, hℓle, hℓ⟩ := Nat.exists_infinite_primes (p + 1)
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  exact deligneBound_of_ihara p (BigEtaleSite.containing (Spec (.of (ZMod p)))) ℓ
    (by omega) hI

theorem deligneBound_of_ihara_all (hI : ∀ (p : ℕ) [Fact p.Prime], IharaIdentity p) :
    RamanujanTau.DeligneBound :=
  ⟨fun p hp => by
    haveI : Fact p.Prime := ⟨hp⟩
    exact deligneBound_of_ihara_prime p (hI p)⟩

end RamanujanWeil.Ihara
