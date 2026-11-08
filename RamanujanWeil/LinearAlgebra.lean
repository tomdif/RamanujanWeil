import Mathlib.LinearAlgebra.Charpoly.BaseChange
import Mathlib.LinearAlgebra.Eigenspace.Charpoly
import Mathlib.LinearAlgebra.Trace
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Linear algebra for the Weil bridge

Pure linear algebra over a field `K` with an embedding `ι : K →+* ℂ`, independent of any
geometry:

* `RamanujanWeil.isRoot_map_charpoly_of_isRoot_map_charpoly_restrict`: if `W` is a `φ`-stable
  subspace, every complex root of `charpoly(φ|_W)` read along `ι` is a root of `charpoly(φ)` read
  along `ι` (eigenvectors of the base change `ℂ ⊗_{K,ι} W` stay eigenvectors in `ℂ ⊗_{K,ι} V`).
* `RamanujanWeil.norm_map_trace_restrict_le`: if every complex root of `charpoly(φ)` along `ι` has
  absolute value `r`, then `‖ι (tr (φ|_W))‖ ≤ dim W · r`.
-/

open Polynomial TensorProduct

namespace RamanujanWeil

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- A complex root (along `ι`) of the characteristic polynomial of the restriction of `φ` to a
`φ`-stable subspace `W` is a root (along `ι`) of the characteristic polynomial of `φ`. -/
theorem isRoot_map_charpoly_of_isRoot_map_charpoly_restrict (φ : Module.End K V)
    (W : Submodule K V) (hW : ∀ x ∈ W, φ x ∈ W) (ι : K →+* ℂ) {z : ℂ}
    (hz : ((φ.restrict hW).charpoly.map ι).IsRoot z) : (φ.charpoly.map ι).IsRoot z := by
  let _ : Algebra K ℂ := ι.toAlgebra
  have hι : algebraMap K ℂ = ι := rfl
  set ψ : Module.End K W := φ.restrict hW
  -- `z` is an eigenvalue of `ψ ⊗ ℂ`
  have hz' : (ψ.baseChange ℂ).charpoly.IsRoot z := by
    rw [LinearMap.charpoly_baseChange, hι]; exact hz
  obtain ⟨v, hv⟩ := (Module.End.hasEigenvalue_iff_isRoot_charpoly (ψ.baseChange ℂ) z).2 hz' |>.exists_hasEigenvector
  -- push the eigenvector into `ℂ ⊗ V`
  let j : ℂ ⊗[K] W →ₗ[ℂ] ℂ ⊗[K] V := W.subtype.baseChange ℂ
  have hj : Function.Injective j :=
    Module.Flat.lTensor_preserves_injective_linearMap (M := ℂ) W.subtype W.injective_subtype
  have hcomm : (φ.baseChange ℂ) ∘ₗ j = j ∘ₗ (ψ.baseChange ℂ) := by
    simp only [j, ← LinearMap.baseChange_comp]
    congr 1
  have hφ : Module.End.HasEigenvalue (φ.baseChange ℂ) z := by
    refine Module.End.hasEigenvalue_of_hasEigenvector (x := j v) ⟨?_, ?_⟩
    · rw [Module.End.mem_eigenspace_iff]
      have := congrArg (fun f => f v) hcomm
      simp only [LinearMap.comp_apply] at this
      rw [this, hv.apply_eq_smul, map_smul]
    · intro h0
      exact hv.2 (hj (by rw [h0, map_zero]))
  have := (Module.End.hasEigenvalue_iff_isRoot_charpoly (φ.baseChange ℂ) z).1 hφ
  rwa [LinearMap.charpoly_baseChange, hι] at this

/-- **Trace bound from the absolute values of the eigenvalues.** If every complex root of
`charpoly(φ)` along `ι` has absolute value `r`, then for every `φ`-stable subspace `W`,
`‖ι (tr (φ|_W))‖ ≤ dim W · r`. -/
theorem norm_map_trace_restrict_le (φ : Module.End K V) (W : Submodule K V)
    (hW : ∀ x ∈ W, φ x ∈ W) (ι : K →+* ℂ) (r : ℝ)
    (hr : ∀ z : ℂ, (φ.charpoly.map ι).IsRoot z → ‖z‖ = r) :
    ‖ι (LinearMap.trace K W (φ.restrict hW))‖ ≤ Module.finrank K W * r := by
  let _ : Algebra K ℂ := ι.toAlgebra
  have hι : algebraMap K ℂ = ι := rfl
  set ψ : Module.End K W := φ.restrict hW
  have hsplit : (ψ.baseChange ℂ).charpoly.Splits := IsAlgClosed.splits _
  have htr : ι (LinearMap.trace K W ψ) = (ψ.baseChange ℂ).charpoly.roots.sum := by
    rw [← Module.End.trace_eq_sum_roots_charpoly_of_splits hsplit, LinearMap.trace_baseChange, hι]
  have hroots : ∀ z ∈ (ψ.baseChange ℂ).charpoly.roots, ‖z‖ = r := by
    intro z hz
    have hz' : (ψ.baseChange ℂ).charpoly.IsRoot z := (mem_roots'.1 hz).2
    rw [LinearMap.charpoly_baseChange, hι] at hz'
    exact hr z (isRoot_map_charpoly_of_isRoot_map_charpoly_restrict φ W hW ι hz')
  have hcard : Multiset.card (ψ.baseChange ℂ).charpoly.roots = Module.finrank K W := by
    rw [IsAlgClosed.card_roots_eq_natDegree, LinearMap.charpoly_baseChange,
      natDegree_map, LinearMap.charpoly_natDegree]
  rw [htr]
  calc ‖(ψ.baseChange ℂ).charpoly.roots.sum‖
      ≤ ((ψ.baseChange ℂ).charpoly.roots.map (‖·‖)).sum := norm_multiset_sum_le _
    _ = ((ψ.baseChange ℂ).charpoly.roots.map (fun _ => r)).sum := by
        rw [Multiset.map_congr rfl hroots]
    _ = Module.finrank K W * r := by
        rw [Multiset.map_const', Multiset.sum_replicate, hcard, nsmul_eq_mul]

/-- Squaring a real bound `|t| ≤ d · q^(ν/2)` gives the integer bound `t² ≤ d² q^ν`. -/
theorem int_sq_le_of_abs_le (t : ℤ) (d q ν : ℕ)
    (h : |(t : ℝ)| ≤ (d : ℝ) * (q : ℝ) ^ ((ν : ℝ) / 2)) :
    t ^ 2 ≤ (d : ℤ) ^ 2 * (q : ℤ) ^ ν := by
  have hq : (0 : ℝ) ≤ (q : ℝ) := Nat.cast_nonneg _
  have hs : (((q : ℝ) ^ ((ν : ℝ) / 2)) ^ 2 : ℝ) = (q : ℝ) ^ ν := by
    rw [← Real.rpow_natCast ((q : ℝ) ^ ((ν : ℝ) / 2)) 2, ← Real.rpow_mul hq,
      ← Real.rpow_natCast]
    congr 1
    push_cast
    ring
  have h0 : 0 ≤ |(t : ℝ)| := abs_nonneg _
  have hreal : (t : ℝ) ^ 2 ≤ (d : ℝ) ^ 2 * (q : ℝ) ^ ν := by
    calc (t : ℝ) ^ 2 = |(t : ℝ)| ^ 2 := (sq_abs _).symm
      _ ≤ ((d : ℝ) * (q : ℝ) ^ ((ν : ℝ) / 2)) ^ 2 := pow_le_pow_left₀ h0 h 2
      _ = (d : ℝ) ^ 2 * (q : ℝ) ^ ν := by rw [mul_pow, hs]
  exact_mod_cast hreal

end RamanujanWeil
