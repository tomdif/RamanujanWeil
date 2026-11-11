import RamanujanWeil.Arith.DeuringG7AJCore
import RamanujanWeil.Arith.DeuringG7HeisMain
import RamanujanWeil.Arith.DeuringG7DGapsAll

/-!
# A3-ord, G7 Abel–Jacobi + Heisenberg: assembly

`docs/ARITH_DEURING_G7_AJHEIS.md` §3.

* `torsion_of_aj`: Abel–Jacobi compatibility carries Stacks' `J_W[N] ≅ (ℤ/N)²` (`char ∤ N`,
  `nonempty_torsionBy_addEquiv_of_isUnit`, `dim J_W = 1`) to Mathlib's `E(k̄)[N]`.
* **`thetaHeisenbergAll_of_aj`**: `AbelJacobiAll K ⟹ ThetaHeisenbergAll K`, from
  `thetaHeisenberg_of_torsion` (`DeuringG7HeisMain`). So the Heisenberg input is a theorem
  relative to Abel–Jacobi.
* **`dGeomGapsAll_of_aj`**: `AbelJacobiAll K ⟹ DGeomGapsAll K`.
* `abelJacobiAll_of_bridge`, **`dGeomGapsAll_of_bridge`**: everything from
  `PicClassBridgeAll K` (the restriction `Pic⁰(E_W) ↪ Cl(k̄[E])`, `DeuringG7AJCore`).
* **`deligneBound_of_bridge`**: Deligne's bound from `PicClassBridgeAll`, `ThetaLevelDescent`
  and `PrincipalFiniteness` at every finite field.
-/

open AlgebraicGeometry CategoryTheory
open WeierstrassCurve WeierstrassCurve.Affine

universe u

noncomputable section

namespace RamanujanWeil.Arith.Deuring.Geom.G7.DGeom

open scoped Classical

variable {K : Type u} [Field K] [Fintype K]

/-- **`E(k̄)[N] ≅ (ℤ/N)²`** for `char ∤ N`, transported from `J_W[N]` by Abel–Jacobi. -/
theorem torsion_of_aj (W₀ : WeierstrassCurve K) [W₀.IsElliptic] (S : Jac.JacSite W₀)
    (h : AbelJacobiMathlib W₀ S) (N : ℕ) (hN : IsUnit (N : AlgebraicClosure K)) :
    Nonempty (AddSubgroup.torsionBy ((Wbar W₀)⁄(AlgebraicClosure K)).Point (N : ℤ) ≃+
      (Fin 2 → ZMod N)) := by
  obtain ⟨e, -⟩ := h
  obtain ⟨t⟩ := Stacks.Groupoids.nonempty_torsionBy_addEquiv_of_isUnit (AlgebraicClosure K) S.J N hN
  rw [S.dim_J] at t
  exact ⟨(torEquiv W₀ S e N).trans t⟩

/-- **The Heisenberg property from Abel–Jacobi.** -/
theorem thetaHeisenbergAll_of_aj (haj : AbelJacobiAll K) : ThetaHeisenbergAll K := by
  intro W _ ℓ hℓ hodd hk n
  obtain ⟨S⟩ := Jac.nonempty_jacSite W
  have hN : IsUnit ((ℓ ^ (n + 1) : ℕ) : AlgebraicClosure K) := by
    rw [Nat.cast_pow]; exact hk.pow _
  have h3 : 3 ≤ ℓ ^ (n + 1) := by
    have h2 := hℓ.two_le
    have : 3 ≤ ℓ := by omega
    exact this.trans (Nat.le_self_pow (Nat.succ_ne_zero n) ℓ)
  have hoddN : Odd (ℓ ^ (n + 1)) := (hℓ.odd_of_ne_two hodd).pow
  exact thetaHeisenberg_of_torsion (Wbar W) h3 hoddN (torsion_of_aj W S (haj W S) _ hN)

/-- **`DGeomGapsAll K` from Abel–Jacobi alone.** -/
theorem dGeomGapsAll_of_aj (haj : AbelJacobiAll K) : DGeomGapsAll K :=
  dGeomGapsAll_of haj (thetaHeisenbergAll_of_aj haj)

variable (K)

/-- **The class-group bridge for every curve over `K`** (named). -/
def PicClassBridgeAll : Prop :=
  ∀ (W : WeierstrassCurve K) [W.IsElliptic] (S : Jac.JacSite W), PicClassBridge W S

variable {K}

theorem abelJacobiAll_of_bridge (h : PicClassBridgeAll K) : AbelJacobiAll K :=
  fun W _ S => abelJacobiMathlib_of_bridge W S (h W S)

/-- **`DGeomGapsAll K` from the class-group bridge.** -/
theorem dGeomGapsAll_of_bridge (h : PicClassBridgeAll K) : DGeomGapsAll K :=
  dGeomGapsAll_of_aj (abelJacobiAll_of_bridge h)

/-- The remaining seams at every finite field, with Abel–Jacobi and Heisenberg replaced by the
class-group bridge. -/
def DBridgeSplitAll : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (n : ℕ), 1 ≤ n →
    letI : Fintype (GaloisField p n) := Fintype.ofFinite _
    PicClassBridgeAll (GaloisField p n) ∧ ThetaLevelDescent (GaloisField p n) ∧
      PrincipalFiniteness (GaloisField p n)

/-- **Deligne's bound** from the class-group bridge, descent and Θ + J + C. -/
theorem deligneBound_of_bridge (h : DBridgeSplitAll) : RamanujanTau.DeligneBound :=
  deligneBound_of_gaps fun p _ n hn =>
    letI : Fintype (GaloisField p n) := Fintype.ofFinite _
    have h' := h p n hn
    have haj := abelJacobiAll_of_bridge h'.1
    ⟨haj, thetaHeisenbergAll_of_aj haj, h'.2.1, h'.2.2⟩

end RamanujanWeil.Arith.Deuring.Geom.G7.DGeom
