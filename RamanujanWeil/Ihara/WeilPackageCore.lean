import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.LinearAlgebra.Trace
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Complex.Basic

/-!
# M2, frozen interface: the Lefschetz package (Mathlib only)

A `LefschetzPackage K ι Q w d P` is the purely linear-algebraic shadow of
"compactly supported cohomology of a lisse sheaf, pure of weight `≤ w`, on a separated
finite-type scheme of dimension `≤ d` over `𝔽_Q`":

* for each degree `i < 2d+1` a square matrix `frob i` over `K` (the geometric Frobenius on
  `Hⁱ_c(X_k̄, F)` in some basis),
* **weights**: every root `z` of `charpoly (frob i)` mapped along `ι : K →+* ℂ` satisfies
  `‖z‖ ≤ Q ^ ((w + i) / 2)` (Weil II, upper bound only),
* **Lefschetz identity for all powers**: `∑ᵢ (-1)ⁱ tr (frob i ^ n) = P n` for every `n ≥ 1`.

The point-count side `P : ℕ → K` is a *parameter* of the type, so that a producer
(`RamanujanWeil.Ihara.lefschetzPackage_of_lisse_pure`, file `WeilPackage.lean`) fixes it
definitionally, and a consumer rewrites it.

`LefschetzPackage.elim_deligne` repackages a package with `K : Type`, `Q = p`, `w = 10`,
`P n = (S n : K)` into exactly the binder list of the M1 statement
`RamanujanWeil.Plan.deligne_of_package` (`scratch/ProbeInterfaces.lean`):
`V : Fin (2d+1) → Type`, `F i : Module.End K (V i)`, `hw`, `htr`.
-/

open Finset

namespace RamanujanWeil.Ihara

/-- Trace of a power of an endomorphism, read on its matrix in any `Fin r`-basis. -/
theorem trace_toMatrix_pow {K M : Type*} [Field K] [AddCommGroup M] [Module K M] {r : ℕ}
    (b : Module.Basis (Fin r) K M) (φ : Module.End K M) (k : ℕ) :
    ((LinearMap.toMatrix b b φ) ^ k).trace = LinearMap.trace K M (φ ^ k) := by
  rw [LinearMap.toMatrix_pow, ← LinearMap.trace_eq_matrix_trace]

/-- **The frozen M2 interface.** Matrices `frob i` (`i < 2d+1`) over `K` whose characteristic
roots have `ι`-absolute value `≤ Q ^ ((w + i)/2)` and whose alternating traces of powers are
`P n` for all `n ≥ 1`. -/
structure LefschetzPackage (K : Type*) [Field K] (ι : K →+* ℂ) (Q : ℕ) (w : ℤ) (d : ℕ)
    (P : ℕ → K) where
  /-- `dim Hⁱ_c`. -/
  rank : Fin (2 * d + 1) → ℕ
  /-- The matrix of geometric Frobenius on `Hⁱ_c`. -/
  frob : ∀ i, Matrix (Fin (rank i)) (Fin (rank i)) K
  /-- Weil II weight upper bound along `ι`. -/
  weight_le : ∀ (i : Fin (2 * d + 1)) (z : ℂ), ((frob i).charpoly.map ι).IsRoot z →
    ‖z‖ ≤ (Q : ℝ) ^ (((w : ℝ) + (i : ℕ)) / 2)
  /-- Lefschetz trace identity for every power of Frobenius. -/
  trace_eq : ∀ n : ℕ, 1 ≤ n →
    ∑ i : Fin (2 * d + 1), (-1 : K) ^ (i : ℕ) * (frob i ^ n).trace = P n

namespace LefschetzPackage

variable {K : Type*} [Field K] {ι : K →+* ℂ} {Q : ℕ} {w : ℤ} {d : ℕ} {P : ℕ → K}
  (L : LefschetzPackage K ι Q w d P)

/-- The `i`-th space, `Kʳ`. -/
abbrev V (i : Fin (2 * d + 1)) : Type _ := Fin (L.rank i) → K

/-- The `i`-th endomorphism, `x ↦ frob i * x`. -/
noncomputable def F (i : Fin (2 * d + 1)) : Module.End K (L.V i) := Matrix.toLin' (L.frob i)

theorem charpoly_F (i : Fin (2 * d + 1)) : (L.F i).charpoly = (L.frob i).charpoly :=
  Matrix.charpoly_toLin' _

theorem trace_F_pow (i : Fin (2 * d + 1)) (n : ℕ) :
    LinearMap.trace K (L.V i) (L.F i ^ n) = (L.frob i ^ n).trace := by
  rw [F, ← Matrix.toLin'_pow, LinearMap.trace_eq_matrix_trace K (Pi.basisFun K _),
    LinearMap.toMatrix_eq_toMatrix', LinearMap.toMatrix'_toLin']

/-- Weights in endomorphism form. -/
theorem weight_F (i : Fin (2 * d + 1)) (z : ℂ) (hz : ((L.F i).charpoly.map ι).IsRoot z) :
    ‖z‖ ≤ (Q : ℝ) ^ (((w : ℝ) + (i : ℕ)) / 2) :=
  L.weight_le i z (by rwa [charpoly_F] at hz)

/-- Lefschetz identity in endomorphism form. -/
theorem trace_F (n : ℕ) (hn : 1 ≤ n) :
    ∑ i : Fin (2 * d + 1), (-1 : K) ^ (i : ℕ) * LinearMap.trace K (L.V i) (L.F i ^ n) = P n := by
  simp_rw [trace_F_pow]
  exact L.trace_eq n hn

/-- Change the point side along an identity valid for `n ≥ 1` (this is how M6 replaces
`pointSum` by an integer Weierstrass sum). -/
def congrP {P' : ℕ → K} (h : ∀ n : ℕ, 1 ≤ n → P n = P' n) : LefschetzPackage K ι Q w d P' where
  rank := L.rank
  frob := L.frob
  weight_le := L.weight_le
  trace_eq n hn := (L.trace_eq n hn).trans (h n hn)

/-- Change the field size along an equality (e.g. `p ^ 1 = p`). -/
def congrQ {Q' : ℕ} (h : Q = Q') : LefschetzPackage K ι Q' w d P := h ▸ L

end LefschetzPackage

/-- **Hand-off to M1.** A package over `K : Type` with `Q = p`, `w = 10` and integer point sums
`P n = (S n : K)` supplies *verbatim* the hypotheses `V`, `F`, `hw`, `htr` of
`RamanujanWeil.Plan.deligne_of_package`; any conclusion `C` derivable from those binders follows.
Usage: `L.elim_deligne fun V _ _ _ F hw htr => deligne_of_package p d hd K ι V F hw S htr hS`. -/
theorem LefschetzPackage.elim_deligne {K : Type} [Field K] {ι : K →+* ℂ} {p d : ℕ}
    {S : ℕ → ℤ} (L : LefschetzPackage K ι p 10 d (fun n => (S n : K))) {C : Prop}
    (h : ∀ (V : Fin (2 * d + 1) → Type) [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
      [∀ i, FiniteDimensional K (V i)] (F : ∀ i, Module.End K (V i)),
      (∀ i z, ((F i).charpoly.map ι).IsRoot z → ‖z‖ ≤ (p : ℝ) ^ (((10 : ℝ) + (i : ℕ)) / 2)) →
      (∀ n : ℕ, 1 ≤ n →
        ∑ i : Fin (2 * d + 1), (-1 : K) ^ (i : ℕ) * LinearMap.trace K (V i) (F i ^ n) =
          (S n : K)) → C) : C :=
  h L.V L.F (fun i z hz => by
      have := L.weight_F i z hz
      push_cast at this
      exact this)
    (fun n hn => L.trace_F n hn)

end RamanujanWeil.Ihara
