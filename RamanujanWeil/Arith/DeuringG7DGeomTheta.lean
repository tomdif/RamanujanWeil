import RamanujanWeil.Arith.DeuringG7DGeomTrans
import RamanujanWeil.Arith.DeuringG7WeilHeis
import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-!
# A3-ord, G7-D-geom (theta group): `𝒢(𝒪(N·O))` on an elliptic curve as a `CentralExt`

`docs/ARITH_DEURING_G7DGEOM.md` §2. Let `E = W⁄F` be an elliptic curve over an algebraically
closed field `F`, `K = F(E)`, `τ_P = t_P^*` the translations of `DeuringG7DGeomTrans`.

**The model.** For a divisor `D` put `L(D) = {f ∈ K : div f ≥ −D}` (a finite-dimensional
`F`-subspace of `K` containing `1` when `D ≥ 0`). An isomorphism `t_P^*𝒪(D) ≅ 𝒪(D)` is
multiplication by a function `f` with `div f = t_P^*D − D`, unique up to `F^×`. For `D = N·O` with
`N ≥ 2` the linear system `|D|` is base-point free, so this condition on `f` is equivalent to
**`f · τ_P(L(D)) = L(D)`** (`τ_P L(D) = L(t_P^*D)`, and `L(D')` determines a divisor `D' ~ D`
of degree `N`). Mumford's theta group `𝒢(𝒪(D)) = {(P, φ : t_P^*L ≅ L)}` is therefore the stabilizer
of `V = L(N·O)` in the semidirect product `K^× ⋊ E(F)` acting on subspaces of `K` by
`(f, P) · V = f · τ_P(V)`, with composition law `(f, P)(g, Q) = (f · τ_P g, P + Q)`.

* `thetaAct`: `K^× ⋊ E(F) → End_F(K)`, `(f, P) ↦ f · τ_P(−)`, multiplicative (`thetaAct_mul`,
  from `trans_trans`).
* **`thetaGroup V`** (the stabilizer) and `thetaKer V = {P : ∃ f, (f, P) ∈ 𝒢(V)}` (`K(L)`).
* **`const_of_map_mulLeft`**: `f · V = V`, `1 ∈ V`, `dim V < ∞`, `F = F̄` ⟹ `f ∈ F`.
  This is `Γ(E, 𝒪_E)^× = F^×`: automorphisms of `L` are scalars.
* **`thetaExt V : CentralExt (thetaGroup V) (thetaKer V) (Additive Fˣ)`**: the central
  extension `1 → F^× → 𝒢(L) → K(L) → 0`.
* `rrSpace W N = L(N·O) = span{xⁱ (2i ≤ N), xʲy (2j + 3 ≤ N)}`: finite-dimensional, contains `1`.
-/

noncomputable section

namespace RamanujanWeil.Arith.Deuring.Geom.G7.DGeom

open WeierstrassCurve WeierstrassCurve.Affine Polynomial
open RamanujanWeil.Arith.Deuring.Geom.G7.Fin.Weil (CentralExt)

universe u

variable {F : Type u} [Field F] (W : Affine F) [W.IsElliptic] [DecidableEq F]

open scoped Classical

/-! ### The semidirect product `K^× ⋊ E(F)` -/

/-- `E(F)` acting on `K^×` by translation. -/
def unitsTrans : Multiplicative (W⁄F).Point →* MulAut (Kf W)ˣ where
  toFun P := Units.mapEquiv (transAut W P).toMulEquiv
  map_one' := by
    ext u
    change trans W 0 (u : Kf W) = u
    rw [trans_zero]; rfl
  map_mul' P Q := by
    ext u
    change trans W (P.toAdd + Q.toAdd) (u : Kf W) = trans W P.toAdd (trans W Q.toAdd u)
    rw [trans_trans]

theorem unitsTrans_apply (P : Multiplicative (W⁄F).Point) (u : (Kf W)ˣ) :
    ((unitsTrans W P u : (Kf W)ˣ) : Kf W) = trans W P.toAdd u := rfl

/-- The ambient group `K^× ⋊ E(F)`. -/
abbrev Amb : Type u := (Kf W)ˣ ⋊[unitsTrans W] Multiplicative (W⁄F).Point

/-- `(f, P) ↦ (v ↦ f · τ_P v)`. -/
def thetaAct (g : Amb W) : Kf W →ₗ[F] Kf W :=
  LinearMap.mulLeft F (g.left : Kf W) ∘ₗ (trans W g.right.toAdd).toLinearMap

theorem thetaAct_apply (g : Amb W) (v : Kf W) :
    thetaAct W g v = (g.left : Kf W) * trans W g.right.toAdd v := rfl

theorem thetaAct_mul (g h : Amb W) : thetaAct W (g * h) = thetaAct W g ∘ₗ thetaAct W h := by
  ext v
  simp only [thetaAct_apply, LinearMap.comp_apply, SemidirectProduct.mul_left,
    SemidirectProduct.mul_right, Units.val_mul, unitsTrans_apply, map_mul, toAdd_mul, trans_trans,
    mul_assoc]

theorem thetaAct_one : thetaAct W 1 = LinearMap.id := by
  ext v
  simp only [thetaAct_apply, SemidirectProduct.one_left, SemidirectProduct.one_right, toAdd_one,
    trans_zero, Units.val_one, one_mul]
  rfl

/-! ### The theta group of a subspace -/

variable (V : Submodule F (Kf W))

/-- **The theta group** `𝒢(V) = {(f, P) : f · τ_P(V) = V}`. -/
def thetaGroup : Subgroup (Amb W) where
  carrier := {g | V.map (thetaAct W g) = V}
  one_mem' := by
    change V.map (thetaAct W 1) = V
    rw [thetaAct_one, Submodule.map_id]
  mul_mem' := by
    intro g h hg hh
    change V.map (thetaAct W (g * h)) = V
    rw [thetaAct_mul, Submodule.map_comp]
    change V.map (thetaAct W h) = V at hh
    change V.map (thetaAct W g) = V at hg
    rw [hh, hg]
  inv_mem' := by
    intro g hg
    change V.map (thetaAct W g) = V at hg
    change V.map (thetaAct W g⁻¹) = V
    conv_lhs => rw [← hg]
    rw [← Submodule.map_comp, ← thetaAct_mul, inv_mul_cancel, thetaAct_one, Submodule.map_id]

theorem mem_thetaGroup {g : Amb W} : g ∈ thetaGroup W V ↔ V.map (thetaAct W g) = V := Iff.rfl

/-- **`K(L)`**: the translations `P` with `t_P^*L ≅ L`. -/
def thetaKer : AddSubgroup (W⁄F).Point where
  carrier := {P | ∃ g ∈ thetaGroup W V, g.right = Multiplicative.ofAdd P}
  zero_mem' := ⟨1, (thetaGroup W V).one_mem, rfl⟩
  add_mem' := by
    rintro P Q ⟨g, hg, hgP⟩ ⟨h, hh, hhQ⟩
    exact ⟨g * h, (thetaGroup W V).mul_mem hg hh, by
      rw [SemidirectProduct.mul_right, hgP, hhQ]; rfl⟩
  neg_mem' := by
    rintro P ⟨g, hg, hgP⟩
    exact ⟨g⁻¹, (thetaGroup W V).inv_mem hg, by
      rw [SemidirectProduct.inv_right, hgP]; rfl⟩

/-! ### `Γ(𝒪)^× = F^×` -/

/-- **Automorphisms of `L` are scalars**: if `f · V = V` for a finite-dimensional `V ∋ 1` and
`F` is algebraically closed, then `f ∈ F`. (`f` is integral over `F`: its powers lie in `V`.) -/
theorem const_of_map_mulLeft [IsAlgClosed F] (h1 : (1 : Kf W) ∈ V) [FiniteDimensional F V]
    (f : Kf W) (hf : V.map (LinearMap.mulLeft F f) = V) : f ∈ (algebraMap F (Kf W)).range := by
  have hpow : ∀ n : ℕ, f ^ n ∈ V := by
    intro n
    induction n with
    | zero => rw [pow_zero]; exact h1
    | succ n ih =>
      rw [← hf, pow_succ']
      exact Submodule.mem_map_of_mem ih
  have hle : Subalgebra.toSubmodule (Algebra.adjoin F {f}) ≤ V := by
    intro z hz
    obtain ⟨p, rfl⟩ := (Algebra.adjoin_singleton_eq_range_aeval F f ▸ hz :
      z ∈ (Polynomial.aeval f).range)
    change Polynomial.aeval f p ∈ V
    rw [Polynomial.aeval_eq_sum_range]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hpow i)
  have : FiniteDimensional F (Subalgebra.toSubmodule (Algebra.adjoin F {f})) :=
    Submodule.finiteDimensional_of_le hle
  have hint : IsIntegral F f :=
    isIntegral_of_submodule_noetherian _ inferInstance f (Algebra.self_mem_adjoin_singleton F f)
  exact minpoly.mem_range_of_degree_eq_one F f
    (IsAlgClosed.degree_eq_one_of_irreducible F (minpoly.irreducible hint))

theorem map_smul_self (c : Fˣ) :
    V.map (LinearMap.mulLeft F (algebraMap F (Kf W) c)) = V := by
  have hc : LinearMap.mulLeft F (algebraMap F (Kf W) c) = (c : F) • LinearMap.id := by
    ext v; simp [Algebra.smul_def]
  rw [hc]
  ext v
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact V.smul_mem _ hw
  · intro hv
    refine ⟨((c⁻¹ : Fˣ) : F) • v, V.smul_mem _ hv, ?_⟩
    simp [smul_smul]

/-! ### The central extension -/

variable [IsAlgClosed F] (h1 : (1 : Kf W) ∈ V) [FiniteDimensional F V]

/-- The scalar `(c, 0) ∈ 𝒢(V)`. -/
def thetaScalar : Fˣ →* thetaGroup W V where
  toFun c := ⟨⟨Units.map (algebraMap F (Kf W)).toMonoidHom c, 1⟩, by
    rw [mem_thetaGroup]
    have : thetaAct W ⟨Units.map (algebraMap F (Kf W)).toMonoidHom c, 1⟩ =
        LinearMap.mulLeft F (algebraMap F (Kf W) c) := by
      ext v
      rw [thetaAct_apply]
      simp only [toAdd_one, trans_zero]
      rfl
    rw [this, map_smul_self]⟩
  map_one' := by
    apply Subtype.ext
    ext
    · change algebraMap F (Kf W) ((1 : Fˣ) : F) = 1
      rw [Units.val_one, map_one]
    · rfl
  map_mul' a b := by
    apply Subtype.ext
    ext
    · change (algebraMap F (Kf W) (a * b)) = algebraMap F (Kf W) a *
        trans W (0 : (W⁄F).Point) (algebraMap F (Kf W) b)
      rw [trans_zero, map_mul]; rfl
    · rfl

theorem thetaScalar_left (c : Fˣ) :
    (((thetaScalar W V c : thetaGroup W V) : Amb W).left : Kf W) = algebraMap F (Kf W) c := rfl

theorem thetaScalar_right (c : Fˣ) :
    ((thetaScalar W V c : thetaGroup W V) : Amb W).right = 1 := rfl

/-- The projection `𝒢(V) → K(V)`. -/
def thetaProj : thetaGroup W V →* Multiplicative (thetaKer W V) where
  toFun g := Multiplicative.ofAdd ⟨(g : Amb W).right.toAdd, g, g.2, rfl⟩
  map_one' := rfl
  map_mul' _ _ := rfl

include h1 in
/-- **The theta group of `V` as a central extension** `1 → F^× → 𝒢(V) → K(V) → 0`. -/
def thetaExt : CentralExt (thetaGroup W V) (thetaKer W V) (Additive Fˣ) where
  p := thetaProj W V
  surj := by
    rintro ⟨P, g, hg, hgP⟩
    exact ⟨⟨g, hg⟩, by
      apply Multiplicative.toAdd.injective
      apply Subtype.ext
      change g.right.toAdd = P
      rw [hgP]; rfl⟩
  ι := (thetaScalar W V).comp (MonoidHom.id _)
  inj := by
    intro a b hab
    have := congrArg (fun g : thetaGroup W V => (((g : Amb W).left : Kf W))) hab
    change algebraMap F (Kf W) (((show Fˣ from a) : Fˣ) : F) =
      algebraMap F (Kf W) (((show Fˣ from b) : Fˣ) : F) at this
    exact Units.ext ((algebraMap F (Kf W)).injective this)
  exact := by
    intro g
    constructor
    · intro hg
      have hr : (g : Amb W).right = 1 := by
        have := congrArg (fun z => ((Multiplicative.toAdd z : thetaKer W V) : (W⁄F).Point)) hg
        exact Multiplicative.toAdd.injective this
      have hmap : V.map (LinearMap.mulLeft F ((g : Amb W).left : Kf W)) = V := by
        have h := g.2
        rw [mem_thetaGroup] at h
        have : thetaAct W g = LinearMap.mulLeft F ((g : Amb W).left : Kf W) := by
          ext v
          rw [thetaAct_apply, hr, toAdd_one, trans_zero]
          rfl
        rwa [this] at h
      obtain ⟨c, hc⟩ := const_of_map_mulLeft W V h1 _ hmap
      have hc0 : c ≠ 0 := by
        rintro rfl
        rw [map_zero] at hc
        exact ((g : Amb W).left.ne_zero) hc.symm
      refine ⟨Units.mk0 c hc0, ?_⟩
      apply Subtype.ext
      ext
      · change algebraMap F (Kf W) c = _
        exact hc
      · exact hr.symm
    · rintro ⟨a, rfl⟩
      rfl
  central := by
    intro a g
    apply Subtype.ext
    ext
    · change (algebraMap F (Kf W) a.toMul) * trans W (0 : (W⁄F).Point) ((g : Amb W).left) =
        ((g : Amb W).left : Kf W) * trans W (g : Amb W).right.toAdd (algebraMap F (Kf W) a.toMul)
      rw [trans_zero, AlgHom.commutes, mul_comm]
      rfl
    · change 1 * (g : Amb W).right = (g : Amb W).right * 1
      rw [one_mul, mul_one]

theorem thetaExt_p_right (g : thetaGroup W V) :
    (((Multiplicative.toAdd ((thetaExt W V h1).p g)) : thetaKer W V) : (W⁄F).Point) =
      (g : Amb W).right.toAdd := rfl

/-! ### The Riemann–Roch space `L(N·O)` -/

/-- The monomials `xⁱ` (`2i ≤ N`) and `xʲy` (`2j + 3 ≤ N`): the functions with a pole of order
`≤ N` at `O` and no other pole. -/
def rrGens (N : ℕ) : Set (Kf W) :=
  (fun i => genX W ^ i) '' {i | 2 * i ≤ N} ∪ (fun j => genX W ^ j * genY W) '' {j | 2 * j + 3 ≤ N}

theorem rrGens_finite (N : ℕ) : (rrGens W N).Finite := by
  refine Set.Finite.union (Set.Finite.image _ ?_) (Set.Finite.image _ ?_)
  · exact (Set.finite_Iic N).subset fun i (hi : 2 * i ≤ N) => (by simp; omega)
  · exact (Set.finite_Iic N).subset fun i (hi : 2 * i + 3 ≤ N) => (by simp; omega)

/-- **`L(N·O)`**, the space of global sections of `𝒪(N·O)`, inside `F(E)`. -/
def rrSpace (N : ℕ) : Submodule F (Kf W) := Submodule.span F (rrGens W N)

instance (N : ℕ) : FiniteDimensional F (rrSpace W N) :=
  FiniteDimensional.span_of_finite F (rrGens_finite W N)

theorem one_mem_rrSpace (N : ℕ) : (1 : Kf W) ∈ rrSpace W N :=
  Submodule.subset_span (Or.inl ⟨0, by simp, by simp⟩)

/-- **The theta group `𝒢(𝒪(N·O))`** of an elliptic curve over `F = F̄`, as a central extension
of `K(𝒪(N·O))` by `F^×`. -/
abbrev thetaExtN (N : ℕ) : CentralExt (thetaGroup W (rrSpace W N)) (thetaKer W (rrSpace W N))
    (Additive Fˣ) :=
  thetaExt W (rrSpace W N) (one_mem_rrSpace W N)

end RamanujanWeil.Arith.Deuring.Geom.G7.DGeom
