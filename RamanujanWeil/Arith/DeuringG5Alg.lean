import RamanujanWeil.Arith.DeuringMatrix

/-!
# A3-ord, G5 (algebra): every lattice class is a sublattice of index prime to `p`

`docs/ARITH_DEURING_G5.md` §2. Pure linear algebra over `ℤ`, no geometry.

* `cycMat M x y = [v | Mv]` for `v = (x, y)`, and `mul_cycMat`: `M · [v | Mv] = [v | Mv] · C`
  with `C = companion (tr M) (det M)` (Cayley–Hamilton in dimension two).
* `exists_cycMat_not_dvd`: if a prime `p` does not divide the discriminant `tr² − 4 det`, then
  `det [v | Mv]` is prime to `p` for one of `v ∈ {e₀, e₁, e₀ + e₁}` (the form
  `v ↦ det [v | Mv]` has discriminant `tr² − 4 det`).
* **`exists_intertwiner`**: for `M, M₁` with the same trace and determinant and `p ∤ tr² − 4 det`,
  there is an integer matrix `X` with `M₁ X = X M` and `p ∤ det X`. In the ordinary case
  (`p ∤ t`, `p ∣ q`) this is the statement that **every `ℤ[π]`-lattice class is represented by a
  sublattice of a given lattice of index prime to `p`**: the `p`-part of `surj_class` is empty.
* `IsFrobFamily F M γ`: `γ` is a `ℤ`-basis of `V` on which `F` has matrix `M`;
  **`conj_of_isFrobFamily`**: then the matrix of `F` on *any* basis is `GL₂(ℤ)`-conjugate to `M`.
* `colVec b X`, **`isFrobFamily_of_injective`**: if `Φ : V ↪ L` intertwines `F` and `f`, and its
  range is the span of the columns of `X` (in a basis `b` of `L` on which `f` has matrix `M₁`,
  `M₁ X = X M`, `det X ≠ 0`), then `V` has a basis on which `F` has matrix `M`.
* `det_smul_mem_span_colVec`: `det X • L ⊆ span (columns of X)`.
-/

namespace RamanujanWeil.Arith.Deuring.G5

open Matrix

/-! ### Matrices -/

/-- The companion matrix of `X² − tX + q`. -/
def companion (t q : ℤ) : M2 := !![0, -q; 1, t]

/-- The matrix `[v | Mv]` with columns `v = (x, y)` and `Mv`. -/
def cycMat (M : M2) (x y : ℤ) : M2 :=
  !![x, M 0 0 * x + M 0 1 * y; y, M 1 0 * x + M 1 1 * y]

theorem mul_cycMat (M : M2) (x y : ℤ) :
    M * cycMat M x y = cycMat M x y * companion M.trace M.det := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cycMat, companion, Matrix.mul_apply, Fin.sum_univ_two, Matrix.trace_fin_two,
      Matrix.det_fin_two] <;> ring

theorem det_cycMat (M : M2) (x y : ℤ) :
    (cycMat M x y).det = M 1 0 * x ^ 2 + (M 1 1 - M 0 0) * x * y - M 0 1 * y ^ 2 := by
  simp [cycMat, Matrix.det_fin_two]; ring

/-- The discriminant `tr² − 4 det`. -/
def disc (M : M2) : ℤ := M.trace ^ 2 - 4 * M.det

theorem disc_eq (M : M2) : disc M = (M 1 1 - M 0 0) ^ 2 + 4 * M 0 1 * M 1 0 := by
  simp [disc, Matrix.trace_fin_two, Matrix.det_fin_two]; ring

/-- **A cyclic vector with `det [v | Mv]` prime to `p`.** -/
theorem exists_cycMat_not_dvd (M : M2) (p : ℤ) (hp : ¬ p ∣ disc M) :
    ∃ x y : ℤ, ¬ p ∣ (cycMat M x y).det := by
  by_contra h
  push Not at h
  have h1 := h 1 0
  have h2 := h 0 1
  have h3 := h 1 1
  have e1 : (cycMat M 1 0).det = M 1 0 := by rw [det_cycMat]; ring
  have e2 : (cycMat M 0 1).det = -M 0 1 := by rw [det_cycMat]; ring
  have e3 : (cycMat M 1 1).det = M 1 0 + (M 1 1 - M 0 0) - M 0 1 := by rw [det_cycMat]; ring
  rw [e1] at h1
  rw [e2, dvd_neg] at h2
  rw [e3] at h3
  have h4 : p ∣ M 1 1 - M 0 0 := by
    have : M 1 1 - M 0 0 = (M 1 0 + (M 1 1 - M 0 0) - M 0 1) - M 1 0 + M 0 1 := by ring
    rw [this]
    exact (h3.sub h1).add h2
  apply hp
  rw [disc_eq]
  exact (dvd_pow h4 two_ne_zero).add ((h2.mul_left 4).mul_right _)

/-- **Intertwiners of index prime to `p`.** If `M` and `M₁` have the same trace and determinant
and the prime `p` does not divide `tr² − 4 det`, there is `X` with `M₁ X = X M` and `p ∤ det X`. -/
theorem exists_intertwiner (M M₁ : M2) (htr : M₁.trace = M.trace) (hdet : M₁.det = M.det)
    (p : ℕ) (hp : p.Prime) (hd : ¬ (p : ℤ) ∣ disc M) :
    ∃ X : M2, M₁ * X = X * M ∧ ¬ (p : ℤ) ∣ X.det := by
  have hd₁ : ¬ (p : ℤ) ∣ disc M₁ := by rwa [disc, htr, hdet]
  obtain ⟨x, y, hxy⟩ := exists_cycMat_not_dvd M p hd
  obtain ⟨x₁, y₁, hxy₁⟩ := exists_cycMat_not_dvd M₁ p hd₁
  set P := cycMat M x y
  set P₁ := cycMat M₁ x₁ y₁
  set C := companion M.trace M.det
  have hP : M * P = P * C := mul_cycMat M x y
  have hP₁ : M₁ * P₁ = P₁ * C := by
    have := mul_cycMat M₁ x₁ y₁
    rwa [htr, hdet] at this
  have hPne : P.det ≠ 0 := fun h0 => hxy (h0 ▸ dvd_zero _)
  -- `C · adj P = adj P · M`
  have hC : C * adjugate P = adjugate P * M := by
    have e1 : P.det • (adjugate P * M) = P.det • (C * adjugate P) := by
      calc P.det • (adjugate P * M) = adjugate P * M * (P * adjugate P) := by
            rw [mul_adjugate, Matrix.mul_smul, Matrix.mul_one]
        _ = adjugate P * (M * P) * adjugate P := by simp only [Matrix.mul_assoc]
        _ = adjugate P * P * C * adjugate P := by rw [hP]; simp only [Matrix.mul_assoc]
        _ = P.det • (C * adjugate P) := by
            rw [adjugate_mul, Matrix.smul_mul, Matrix.one_mul, Matrix.smul_mul]
    exact (smul_right_injective M2 hPne e1).symm
  refine ⟨P₁ * adjugate P, ?_, ?_⟩
  · rw [← Matrix.mul_assoc, hP₁, Matrix.mul_assoc, hC, Matrix.mul_assoc]
  · have hpr : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
    rw [det_mul, det_adjugate, Fintype.card_fin]
    simp only [Nat.add_one_sub_one, pow_one]
    intro h
    rcases hpr.dvd_or_dvd h with h | h
    · exact hxy₁ h
    · exact hxy h

/-! ### Frobenius bases and conjugacy -/

section Module

variable {V : Type*} [AddCommGroup V] [Module ℤ V]

/-- `γ` is a `ℤ`-basis of `V` on which `F` acts by the matrix `M` (columns = images). -/
def IsFrobFamily (F : V →ₗ[ℤ] V) (M : M2) (γ : Fin 2 → V) : Prop :=
  LinearIndependent ℤ γ ∧ (⊤ ≤ Submodule.span ℤ (Set.range γ)) ∧
    ∀ j, F (γ j) = Fintype.linearCombination ℤ γ (fun l => M l j)

theorem repr_equivFun_symm {W : Type*} [AddCommGroup W] [Module ℤ W]
    (b : Module.Basis (Fin 2) ℤ W) (c : Fin 2 → ℤ) (i : Fin 2) :
    b.repr (b.equivFun.symm c) i = c i := by
  rw [← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply]

theorem toMatrix_isFrobFamily {F : V →ₗ[ℤ] V} {M : M2} {γ : Fin 2 → V}
    (h : IsFrobFamily F M γ) :
    LinearMap.toMatrix (Module.Basis.mk h.1 h.2.1) (Module.Basis.mk h.1 h.2.1) F = M := by
  ext i j
  rw [LinearMap.toMatrix_apply, Module.Basis.mk_apply, h.2.2 j]
  have : Fintype.linearCombination ℤ γ (fun l => M l j) =
      (Module.Basis.mk h.1 h.2.1).equivFun.symm (fun l => M l j) := by
    rw [Module.Basis.equivFun_symm_apply, Fintype.linearCombination_apply]
    simp only [Module.Basis.mk_apply]
  rw [this, repr_equivFun_symm]

/-- **Conjugacy**: if `F` has matrix `M` on some basis, its matrix on any basis `b` is
`GL₂(ℤ)`-conjugate to `M`. -/
theorem conj_of_isFrobFamily {F : V →ₗ[ℤ] V} {M : M2} {γ : Fin 2 → V}
    (h : IsFrobFamily F M γ) (b : Module.Basis (Fin 2) ℤ V) :
    ∃ g : GL2, (g : M2) * LinearMap.toMatrix b b F * (↑g⁻¹ : M2) = M := by
  set c := Module.Basis.mk h.1 h.2.1
  refine ⟨⟨c.toMatrix b, b.toMatrix c, Module.Basis.toMatrix_mul_toMatrix_flip c b,
    Module.Basis.toMatrix_mul_toMatrix_flip b c⟩, ?_⟩
  change c.toMatrix b * LinearMap.toMatrix b b F * b.toMatrix c = M
  rw [basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix]
  exact toMatrix_isFrobFamily h

variable {L : Type*} [AddCommGroup L] [Module ℤ L]

/-- The columns of `X` in the basis `b`. -/
noncomputable def colVec (b : Module.Basis (Fin 2) ℤ L) (X : M2) (j : Fin 2) : L :=
  b.equivFun.symm (fun i => X i j)

theorem repr_colVec (b : Module.Basis (Fin 2) ℤ L) (X : M2) (j i : Fin 2) :
    b.repr (colVec b X j) i = X i j :=
  repr_equivFun_symm b _ i

theorem repr_lc_colVec (b : Module.Basis (Fin 2) ℤ L) (X : M2) (c : Fin 2 → ℤ) (i : Fin 2) :
    b.repr (Fintype.linearCombination ℤ (colVec b X) c) i = (X *ᵥ c) i := by
  rw [Fintype.linearCombination_apply]
  simp only [map_sum, LinearEquiv.map_smul, Finsupp.coe_finsetSum, Finset.sum_apply,
    Finsupp.smul_apply, repr_colVec, smul_eq_mul, Matrix.mulVec, dotProduct]
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

theorem linearIndependent_colVec (b : Module.Basis (Fin 2) ℤ L) (X : M2) (hX : X.det ≠ 0) :
    LinearIndependent ℤ (colVec b X) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc
  rw [← Fintype.linearCombination_apply] at hc
  have hv : X *ᵥ c = 0 := by
    funext i
    have := repr_lc_colVec b X c i
    rw [hc, map_zero, Finsupp.zero_apply] at this
    exact this.symm
  have h2 : X.det • c = 0 := by
    rw [← Matrix.one_mulVec c, ← Matrix.smul_mulVec, ← adjugate_mul, ← Matrix.mulVec_mulVec, hv,
      Matrix.mulVec_zero]
  intro i
  have := congrFun h2 i
  simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply, mul_eq_zero] at this
  exact this.resolve_left hX

/-- `f` maps the columns of `X` by `M`, if `f` has matrix `M₁` in `b` and `M₁ X = X M`. -/
theorem map_colVec (b : Module.Basis (Fin 2) ℤ L) (f : L →ₗ[ℤ] L) (M₁ M X : M2)
    (hM₁ : LinearMap.toMatrix b b f = M₁) (hX : M₁ * X = X * M) (j : Fin 2) :
    f (colVec b X j) = Fintype.linearCombination ℤ (colVec b X) (fun l => M l j) := by
  apply b.repr.injective
  ext k
  have h1 := congrFun (LinearMap.toMatrix_mulVec_repr b b f (colVec b X j)) k
  rw [← h1, hM₁, repr_lc_colVec]
  have hr : ⇑(b.repr (colVec b X j)) = fun i => X i j := funext (repr_colVec b X j)
  rw [hr]
  have h2 := congrFun (congrFun hX k) j
  simp only [Matrix.mul_apply] at h2
  simp only [Matrix.mulVec, dotProduct]
  rw [h2]

/-- `det X • L ⊆ span (columns of X)`. -/
theorem det_smul_mem_span_colVec (b : Module.Basis (Fin 2) ℤ L) (X : M2) (w : L) :
    LinearMap.lsmul ℤ L X.det w ∈ Submodule.span ℤ (Set.range (colVec b X)) := by
  have key : LinearMap.lsmul ℤ L X.det w =
      Fintype.linearCombination ℤ (colVec b X) (adjugate X *ᵥ ⇑(b.repr w)) := by
    apply b.repr.injective
    ext k
    rw [repr_lc_colVec, Matrix.mulVec_mulVec, mul_adjugate, Matrix.smul_mulVec,
      Matrix.one_mulVec, LinearMap.lsmul_apply, LinearEquiv.map_smul]
    rfl
  rw [key, Submodule.mem_span_range_iff_exists_fun]
  exact ⟨_, (Fintype.linearCombination_apply _ _ _).symm⟩

variable {V : Type*} [AddCommGroup V] [Module ℤ V]

/-- **Transport of a Frobenius basis along an injection with prescribed range.** -/
theorem isFrobFamily_of_injective (b : Module.Basis (Fin 2) ℤ L) (f : L →ₗ[ℤ] L)
    (M₁ M X : M2) (hM₁ : LinearMap.toMatrix b b f = M₁) (hX : M₁ * X = X * M)
    (hdet : X.det ≠ 0) (F : V →ₗ[ℤ] V) (Φ : V →ₗ[ℤ] L) (hΦ : Function.Injective Φ)
    (hcomm : ∀ v, Φ (F v) = f (Φ v))
    (hrange : ∀ w, w ∈ Submodule.span ℤ (Set.range (colVec b X)) → ∃ v, Φ v = w)
    (hrange' : ∀ v, Φ v ∈ Submodule.span ℤ (Set.range (colVec b X))) :
    ∃ γ : Fin 2 → V, IsFrobFamily F M γ := by
  choose γ hγ using fun j => hrange (colVec b X j) (Submodule.subset_span ⟨j, rfl⟩)
  have hlc : ∀ c : Fin 2 → ℤ, Φ (Fintype.linearCombination ℤ γ c) =
      Fintype.linearCombination ℤ (colVec b X) c := by
    intro c
    rw [Fintype.linearCombination_apply, Fintype.linearCombination_apply, map_sum]
    simp only [LinearMap.map_smul, hγ]
  refine ⟨γ, ?_, ?_, ?_⟩
  · apply LinearIndependent.of_comp Φ
    have hcomp : Φ ∘ γ = colVec b X := funext hγ
    rw [hcomp]
    exact linearIndependent_colVec b X hdet
  · intro v _
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).1 (hrange' v)
    rw [← Fintype.linearCombination_apply] at hc
    have : v = Fintype.linearCombination ℤ γ c := by
      apply hΦ
      rw [hlc, hc]
    rw [this, Submodule.mem_span_range_iff_exists_fun]
    exact ⟨c, (Fintype.linearCombination_apply _ _ _).symm⟩
  · intro j
    apply hΦ
    rw [hcomm, hγ, map_colVec b f M₁ M X hM₁ hX, hlc]

end Module

end RamanujanWeil.Arith.Deuring.G5
