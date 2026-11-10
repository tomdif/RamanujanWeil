import RamanujanWeil.Arith.DeuringMatrix

/-!
# A3-ord: lattice isomorphisms ↔ `GL₂(ℤ)`-conjugacy (pure algebra)

`docs/ARITH_DEURING_CLASSLATTICE.md` §2. For free `ℤ`-modules `L`, `L'` of rank two with bases
`b`, `b'` and endomorphisms `F`, `F'` with matrices `M = [F]_b`, `M' = [F']_{b'}`:

* `conj_of_linearEquiv`, `linearEquiv_of_conj`: there is a `ℤ[F]`-linear isomorphism
  `L ≃ L'` (`f ∘ F = F' ∘ f`) iff `g M g⁻¹ = M'` for some `g ∈ GL₂(ℤ)`;
* `stabEquiv`: `Aut_{ℤ[F]}(L) = {u ∈ GL(L) : uF = Fu} ≃ Stab_{GL₂(ℤ)}(M)`.
-/

namespace RamanujanWeil.Arith.Deuring.ClassLattice

open Matrix MulAction RamanujanWeil.Arith.Deuring

variable {L L' : Type*} [AddCommGroup L] [Module ℤ L] [AddCommGroup L'] [Module ℤ L']

/-- A `ℤ[F]`-linear isomorphism gives a conjugating matrix. -/
theorem conj_of_linearEquiv (b : Module.Basis (Fin 2) ℤ L) (b' : Module.Basis (Fin 2) ℤ L')
    (F : L →ₗ[ℤ] L) (F' : L' →ₗ[ℤ] L') (f : L ≃ₗ[ℤ] L') (hf : ∀ x, f (F x) = F' (f x)) :
    ∃ g : GL2, (g : M2) * LinearMap.toMatrix b b F * (↑g⁻¹ : M2) =
      LinearMap.toMatrix b' b' F' := by
  have h1 : (f.toLinearMap).comp f.symm.toLinearMap = LinearMap.id :=
    LinearMap.ext fun x => by simp
  have h2 : (f.symm.toLinearMap).comp f.toLinearMap = LinearMap.id :=
    LinearMap.ext fun x => by simp
  let g : GL2 := ⟨LinearMap.toMatrix b b' f, LinearMap.toMatrix b' b f.symm, by
    rw [← LinearMap.toMatrix_comp, h1, LinearMap.toMatrix_id], by
    rw [← LinearMap.toMatrix_comp, h2, LinearMap.toMatrix_id]⟩
  refine ⟨g, ?_⟩
  have hcomm : (f.toLinearMap).comp F = F'.comp f.toLinearMap := LinearMap.ext hf
  have h := congrArg (LinearMap.toMatrix b b') hcomm
  rw [LinearMap.toMatrix_comp b b b', LinearMap.toMatrix_comp b b' b'] at h
  change LinearMap.toMatrix b b' f * LinearMap.toMatrix b b F * LinearMap.toMatrix b' b f.symm =
    LinearMap.toMatrix b' b' F'
  rw [h, Matrix.mul_assoc, ← LinearMap.toMatrix_comp, h1, LinearMap.toMatrix_id, Matrix.mul_one]

/-- A conjugating matrix gives a `ℤ[F]`-linear isomorphism. -/
theorem linearEquiv_of_conj (b : Module.Basis (Fin 2) ℤ L) (b' : Module.Basis (Fin 2) ℤ L')
    (F : L →ₗ[ℤ] L) (F' : L' →ₗ[ℤ] L') (g : GL2)
    (hg : (g : M2) * LinearMap.toMatrix b b F * (↑g⁻¹ : M2) = LinearMap.toMatrix b' b' F') :
    ∃ f : L ≃ₗ[ℤ] L', ∀ x, f (F x) = F' (f x) := by
  let f : L ≃ₗ[ℤ] L' := LinearEquiv.ofLinear (Matrix.toLin b b' (g : M2))
    (Matrix.toLin b' b (↑g⁻¹ : M2))
    (by rw [← Matrix.toLin_mul b' b b', Units.mul_inv, Matrix.toLin_one])
    (by rw [← Matrix.toLin_mul b b' b, Units.inv_mul, Matrix.toLin_one])
  refine ⟨f, fun x => ?_⟩
  have : (Matrix.toLin b b' (g : M2)).comp F = F'.comp (Matrix.toLin b b' (g : M2)) := by
    apply (LinearMap.toMatrix b b').injective
    rw [LinearMap.toMatrix_comp b b b', LinearMap.toMatrix_comp b b' b',
      LinearMap.toMatrix_toLin, ← hg, Matrix.mul_assoc _ (↑g⁻¹ : M2), Units.inv_mul,
      Matrix.mul_one]
  exact LinearMap.congr_fun this x

/-- `g • M = M` iff `g M = M g`. -/
theorem smul_eq_self_iff {t q : ℤ} (g : GL2) (M : TrDet t q) :
    g • M = M ↔ (g : M2) * M.1 = M.1 * g := by
  constructor
  · intro h
    have h1 : (g : M2) * M.1 * (↑g⁻¹ : M2) = M.1 := by
      rw [← smul_val]; exact congrArg Subtype.val h
    calc (g : M2) * M.1 = (g : M2) * M.1 * ((↑g⁻¹ : M2) * (g : M2)) := by
          rw [Units.inv_mul, Matrix.mul_one]
      _ = ((g : M2) * M.1 * (↑g⁻¹ : M2)) * g := by simp only [Matrix.mul_assoc]
      _ = M.1 * g := by rw [h1]
  · intro h
    exact Subtype.ext (by rw [smul_val, h, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one])

/-- `End(L) ≃* M₂(ℤ)` via a basis. -/
noncomputable def toMatrixMulEquiv (b : Module.Basis (Fin 2) ℤ L) : Module.End ℤ L ≃* M2 :=
  { (LinearMap.toMatrix b b).toEquiv with
    map_mul' := fun f g => LinearMap.toMatrix_mul b f g }

theorem toMatrixMulEquiv_apply (b : Module.Basis (Fin 2) ℤ L) (f : Module.End ℤ L) :
    toMatrixMulEquiv b f = LinearMap.toMatrix b b f := rfl

/-- **`Aut_{ℤ[F]}(L) ≃ Stab_{GL₂(ℤ)}([F]_b)`.** -/
noncomputable def stabEquiv {t q : ℤ} (b : Module.Basis (Fin 2) ℤ L) (F : L →ₗ[ℤ] L)
    (M : TrDet t q) (hM : M.1 = LinearMap.toMatrix b b F) :
    {u : (Module.End ℤ L)ˣ // (u : Module.End ℤ L) * F = F * u} ≃ stabilizer GL2 M :=
  (Units.mapEquiv (toMatrixMulEquiv b)).toEquiv.subtypeEquiv fun u => by
    rw [mem_stabilizer_iff, smul_eq_self_iff, hM]
    change _ ↔ toMatrixMulEquiv b (u : Module.End ℤ L) * toMatrixMulEquiv b F =
      toMatrixMulEquiv b F * toMatrixMulEquiv b (u : Module.End ℤ L)
    rw [← map_mul, ← map_mul, (toMatrixMulEquiv b).injective.eq_iff]

end RamanujanWeil.Arith.Deuring.ClassLattice
