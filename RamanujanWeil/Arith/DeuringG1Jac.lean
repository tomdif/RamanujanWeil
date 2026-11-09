import RamanujanWeil.Arith.DeuringG2
import RamanujanWeil.Arith.DeuringG1Coord
import StacksFrontier.AlgebraicGeometry.PicardScheme.CurvePicard.AbelJacobi

/-!
# A3-ord, G1.0: the concrete Jacobian of an elliptic Weierstrass curve

`docs/ARITH_DEURING_G1.md` §2, G1.0. For `W / 𝔽_q` elliptic, `K̄ = AlgebraicClosure 𝔽_q`,
and the geometric cubic `E_W = projOf W ×_{𝔽_q} K̄`, a *Jacobian site* `S : JacSite W` is a
big fppf site containing `E_W` and `Spec K̄`. On it we define, with the zero section `O` of
`E_W` as base point:

* `S.J = Pic⁰_{E_W/K̄}` (Stacks' `jacobianGrp`), an abelian variety;
* `S.π`, the Frobenius of the Jacobian induced by the twisted Frobenius
  `Ψ = id × Spec(x ↦ x^q)` (Stacks' `jacobianFrobenius`);
* `S.aj : E_W ⟶ S.J`, the Abel–Jacobi map `P ↦ 𝒪(P − O)` (Stacks' `abelJacobi`).

## Main results

* `charPoly_of_jacobianData`: the body of `DeuringG2.exists_jacobian_charPoly_twisted`, with the
  Jacobian data as hypotheses instead of an existential, so it applies to a *given* Jacobian.
* **`JacSite.frobeniusJacobian`**: `(S.J, S.π)` is a `FrobeniusJacobian W`: `dim = 1`,
  `χ_π = X² − tX + q`. Hence (`JacSite.frob_quadratic`, `JacSite.endDegree_π`)
  `π² − tπ + q = 0` and `deg π = q` for the concrete Jacobian.
* `JacSite.twist_eq`: the `Ψ` used for `S.π` is the twisted Frobenius `Coord.twistFrob W` of G1.3.
* `JacSite.aj`, `zeroPt`: the Abel–Jacobi map and the zero section, which is the zero of
  `Coord.geomFamily W`.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory Polynomial
open Stacks.Frobenius Stacks.EtaleCohomology
open scoped CategoryTheory.MonObj

universe u

noncomputable section

namespace RamanujanWeil.Arith.Deuring.Geom

open Stacks.Groupoids

section Twisted

variable {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (p : ℕ) [hp : Fact p.Prime] [CharP Ω p]
  (halg : letI := ZMod.algebra Ω p; Algebra.IsAlgebraic (ZMod p) Ω)
  {C : Scheme.{u}} (g : C ⟶ Spec (.of Ω)) [IsProper g] [Smooth g] [IsCurve Ω g]
  (φ : C ⟶ C) (w : φ ≫ g = g) (f : ℕ) (hf : 0 < f) (hC : IsInCharacteristic C p) (Ψ : C ≅ C)
  (hΨ : Ψ.hom ≫ φ = absoluteFrobeniusPow C p hC f)

include halg w hf hΨ in
/-- **`exists_jacobian_charPoly_twisted` for a given Jacobian.** If `A` is an abelian variety
with `E : A(Ω) ≃+ Pic⁰(C)`, and `F : A ⟶ A` is a homomorphism which is `Ψ^*` on points and
kills tangent vectors at the identity (the data of `Stacks.Zeta.exists_jacobianFrobenius_data`),
then `χ_F.nextCoeff = N₁ − 1 − q` and `χ_F` is `q`-symmetric. -/
theorem charPoly_of_jacobianData (hdim : topologicalKrullDim C ≤ 1)
    (A : Over (Spec (.of Ω))) [GrpObj A] [AlgebraicGeometry.IsAbelianVariety Ω A]
    (E : Additive (𝟙_ (Over (Spec (.of Ω))) ⟶ A) ≃+ picardDegreeZero Ω g hdim)
    (F : A ⟶ A) [IsMonHom F]
    (hdimA : abelianVarietyDimension A = genus g)
    (hpts : ∀ x : 𝟙_ (Over (Spec (.of Ω))) ⟶ A,
      (Stacks.GluePicard.picardModelAddEquiv C.toRingedSpace).symm
          (E (Additive.ofMul (x ≫ F))).1 =
        Stacks.Picard.schemePullbackClass Ψ.hom
          ((Stacks.GluePicard.picardModelAddEquiv C.toRingedSpace).symm
            (E (Additive.ofMul x)).1))
    (htan : ∀ (s : Spec (.of Ω)) (v : DottedTangentArrow A.hom ((η[A]).left s)),
      (Over.homMk v.val v.property.2 :
        Over.mk (dualNumberBasePoint A.hom ((η[A]).left s)) ⟶ A) ≫ F = 1) :
    (endCharPoly A F).nextCoeff =
        (((Nat.card {x : C | IsClosed ({x} : Set C) ∧ Ψ.hom.base^[1] x = x} : ℤ) - 1 -
          ((p ^ f : ℕ) : ℤ) : ℤ) : ℚ) ∧
      ∀ j ≤ 2 * genus g, (endCharPoly A F).coeff 0 * (endCharPoly A F).coeff j =
        ((p ^ f : ℕ) : ℚ) ^ (2 * genus g - j) * (endCharPoly A F).coeff (2 * genus g - j) := by
  classical
  obtain ⟨ℓ, hℓp, hℓu⟩ := exists_prime_isUnit Ω
  have hℓ : (ℓ : Ω) ≠ 0 := hℓu.ne_zero
  have : Fact ℓ.Prime := ⟨hℓp⟩
  have : NeZero ℓ := ⟨hℓp.ne_zero⟩
  have hpp : p.Prime := Fact.out
  have hpℓ : p ≠ ℓ := fun h => hℓ (h ▸ CharP.cast_eq_zero Ω p)
  have hΨs := Stacks.Zeta.hom_comp_eq_of_hom_comp_eq_absoluteFrobeniusPow p g φ w hC f Ψ hΨ
  have hφΨ : φ ≫ Ψ.hom = absoluteFrobeniusPow C p hC f := by
    rw [← cancel_epi Ψ.hom, ← Category.assoc, hΨ,
      AlgebraicGeometry.absoluteFrobeniusPow_naturality Ψ.hom p hC hC f]
  -- the zeta function
  obtain ⟨-, hfinH, r, α, hr, hαint, hzeta⟩ :=
    Stacks.Zeta.exists_zeta_roots_of_twistedFrobenius p g f hf halg φ w hC Ψ hΨ
  set q : ℕ := p ^ f
  have hq1 : 1 < q := Nat.one_lt_pow hf.ne' hpp.one_lt
  set gam := genus g
  set deg := Stacks.Picard.picardDegree g hdim
  set Pσ := Stacks.Picard.schemePullbackClassHom Ψ.hom
  -- `Ψ^*` on `Pic⁰`
  have hdegΨ : ∀ L, deg (Pσ L) = deg L :=
    Stacks.Picard.picardDegree_schemePullbackClassHom_of_twist g hdim Ψ.hom
      (iterateFrobeniusEquiv Ω p f) hΨs
  let u : deg.ker →+ deg.ker := (Pσ.comp deg.ker.subtype).codRestrict deg.ker fun c => by
    rw [AddMonoidHom.mem_ker, AddMonoidHom.comp_apply, hdegΨ]
    exact c.2
  -- the Jacobian and its Frobenius, with `χ := endCharPoly A F`
  have : IsCommMonObj A := isCommMonObj_of_isProper_of_geometricallyIntegral A
  set χ := endCharPoly A F with hχdef
  have hmon : χ.Monic := endCharPoly_monic A F
  have hχdeg : χ.natDegree = 2 * gam := by rw [natDegree_endCharPoly, hdimA]
  have hnf : 0 ≤ Stacks.Polynomial.normForm χ Polynomial.X := by
    rw [← endDegree_endPolyEval_eq_normForm]; exact Nat.cast_nonneg _
  let E' : Additive (𝟙_ (Over (Spec (.of Ω))) ⟶ A) ≃+ deg.ker :=
    E.trans (Stacks.Zeta.picardDegreeZeroModelAddEquiv g hdim).symm
  have hE'v : ∀ y, ((E' y : deg.ker) : Stacks.Picard.ofScheme C) =
      (Stacks.GluePicard.picardModelAddEquiv C.toRingedSpace).symm (E y).1 := fun y =>
    Stacks.Zeta.coe_picardDegreeZeroModelAddEquiv_symm g hdim (E y)
  have hE' : ∀ x, E' (Additive.ofMul (x ≫ F)) = u (E' (Additive.ofMul x)) := by
    intro x
    apply Subtype.ext
    rw [hE'v]
    show _ = Pσ ((E' (Additive.ofMul x) : deg.ker) : Stacks.Picard.ofScheme C)
    rw [hE'v]
    exact hpts x
  have hker : ∀ R : ℤ[X], ¬ (p : ℤ) ∣ R.coeff 0 →
      (Nat.card (aeval (Stacks.Picard.asEnd u) R).ker : ℚ) = Stacks.Polynomial.normForm χ R := by
    intro R hR0
    have := Stacks.Groupoids.isMonHom_endPolyEval F R
    have hd : IsUnit ((R.coeff 0 : ℤ) : Ω) :=
      isUnit_iff_ne_zero.mpr fun h => hR0 ((CharP.intCast_eq_zero_iff Ω p _).mp h)
    have hcount := Stacks.Groupoids.natCard_comp_eq_one_eq_endDegree Ω A
      (Stacks.Groupoids.endPolyEval F R) (R.coeff 0) hd
      (fun s v => Stacks.Groupoids.comp_endPolyEval_of_comp_eq_one F _ (htan s v) R)
    have hequiv : {x : 𝟙_ (Over (Spec (.of Ω))) ⟶ A //
        x ≫ Stacks.Groupoids.endPolyEval F R = 1} ≃ (aeval (Stacks.Picard.asEnd u) R).ker :=
      Equiv.subtypeEquiv (Additive.ofMul.trans E'.toEquiv) fun x => by
        show _ ↔ aeval (Stacks.Picard.asEnd u) R (E' (Additive.ofMul x)) = 0
        rw [← Stacks.Zeta.endPolyEval_comp_eq_aeval F E' u hE' R x, AddEquiv.map_eq_zero_iff]
        exact ⟨fun h => by rw [h]; rfl, fun h => Additive.ofMul.injective h⟩
    rw [← Nat.card_congr hequiv, hcount]
    exact endDegree_endPolyEval_eq_normForm A F R
  have htors : ∀ N : ℕ, Nonempty (Submodule.torsionBy ℤ deg.ker ((ℓ : ℤ) ^ N) ≃+
      (Fin (2 * gam) → ZMod (ℓ ^ N))) := by
    intro N
    have hunit : IsUnit ((ℓ ^ N : ℕ) : Ω) := by
      rw [Nat.cast_pow]
      exact (isUnit_iff_ne_zero.mpr hℓ).pow N
    obtain ⟨e⟩ := Stacks.Groupoids.nonempty_torsionBy_addEquiv_of_isUnit Ω A (ℓ ^ N) hunit
    rw [hdimA] at e
    refine ⟨AddEquiv.trans ?_ e⟩
    exact
      { toFun := fun c => ⟨E'.symm c.1, by
          have hc := (Submodule.mem_torsionBy_iff _ _).mp c.2
          show (((ℓ ^ N : ℕ) : ℤ)) • E'.symm c.1 = 0
          rw [← map_zsmul, Nat.cast_pow, hc, map_zero]⟩
        invFun := fun x => ⟨E' x.1, by
          have hx : (((ℓ ^ N : ℕ) : ℤ)) • x.1 = 0 := x.2
          have hx' : ((ℓ : ℤ) ^ N) • x.1 = 0 := by exact_mod_cast hx
          rw [Submodule.mem_torsionBy_iff, ← map_zsmul, hx', map_zero]⟩
        left_inv := fun c => Subtype.ext (E'.apply_symm_apply c.1)
        right_inv := fun x => Subtype.ext (E'.symm_apply_apply x.1)
        map_add' := fun a b => Subtype.ext (map_add E'.symm a.1 b.1) }
  -- from here on: Stacks' proof of `weilTraceInput`, with this `χ`
  let instP : ∀ N : ℕ, Module (ZMod (ℓ ^ N)) (Submodule.torsionBy ℤ deg.ker ((ℓ : ℤ) ^ N)) :=
    fun N => AddCommGroup.zmodModule fun x => by
      have hx : ((ℓ : ℤ) ^ N) • (x : deg.ker) = 0 := (Submodule.mem_torsionBy_iff _ _).mp x.2
      apply Subtype.ext
      rw [Submodule.coe_smul_of_tower, Submodule.coe_zero, ← natCast_zsmul, Nat.cast_pow]
      exact hx
  obtain ⟨Fl, hFχ, hFlev⟩ := Stacks.Picard.exists_charpoly_levelMatrix_eq_of_normForm u p hpp hpℓ
    htors χ hmon hχdeg hker
  let eN : ∀ N : ℕ, Submodule.torsionBy ℤ deg.ker ((ℓ : ℤ) ^ N) ≃ₗ[ZMod (ℓ ^ N)]
      Submodule.torsionBy ℤ (Stacks.Picard.ofScheme C) ((ℓ : ℤ) ^ N) := fun N =>
    Stacks.Picard.zmodLinearEquiv (ℓ ^ N) (torsionByKerAddEquiv deg
      (pow_ne_zero N (by exact_mod_cast hℓp.ne_zero)))
  let tN : (C ⟶ C) → ∀ N : ℕ, Module.End (ZMod (ℓ ^ N))
      (Submodule.torsionBy ℤ (Stacks.Picard.ofScheme C) ((ℓ : ℤ) ^ N)) :=
    fun a N => (Stacks.Picard.torsionByRestrict (A := Stacks.Picard.ofScheme C)
      (Stacks.Picard.schemePullbackClassHom a)
      ((ℓ : ℤ) ^ N)).toZModLinearMap (ℓ ^ N)
  let σN := tN Ψ.hom
  let τN := tN φ
  have hconj : ∀ N, (eN N).conj (Stacks.Picard.levelMap u N) = σN N := fun N =>
    LinearMap.ext fun x => Subtype.ext rfl
  have hcomp : ∀ (N : ℕ) (a b : C ⟶ C), a ≫ b = absoluteFrobeniusPow C p hC f →
      ∀ x, tN a N (tN b N x) = (q : ZMod (ℓ ^ N)) • x := fun N a b hab x => by
    rw [Nat.cast_smul_eq_nsmul]
    exact torsionByRestrict_schemePullbackClassHom_comp_eq_smul p hC f _ hab x
  have hweil : ∀ N : ℕ, ∃ e : Submodule.torsionBy ℤ (Stacks.Picard.ofScheme C) ((ℓ : ℤ) ^ N) →+
      Submodule.torsionBy ℤ (Stacks.Picard.ofScheme C) ((ℓ : ℤ) ^ N) →+ ZMod (ℓ ^ N),
      (∀ a, (∀ b, e a b = 0) → a = 0) ∧
        ∀ a b, e (σN N a) (σN N b) = (q : ZMod (ℓ ^ N)) * e a b := by
    intro N
    obtain ⟨e, he, heσ⟩ := Stacks.Picard.exists_weilPairing_of_twist g (isUnit_iff_ne_zero.mpr hℓ)
      Ψ.hom (iterateFrobenius Ω p f) q hΨs (fun x => rfl) 1
      (fun L => by simpa only [one_mul] using hdegΨ L) N
    refine ⟨e, he, fun a b => ?_⟩
    show e (Stacks.Picard.torsionByRestrict Pσ _ a) (Stacks.Picard.torsionByRestrict Pσ _ b) = _
    rw [heσ, zsmul_eq_mul]
    push_cast
    ring
  have hlevel : ∀ N : ℕ, 0 < N →
      (∀ j ≤ 2 * gam,
        (Fl.map (PadicInt.toZModPow N)).coeff 0 * (Fl.map (PadicInt.toZModPow N)).coeff j =
        (q : ZMod (ℓ ^ N)) ^ (2 * gam - j) * (Fl.map (PadicInt.toZModPow N)).coeff (2 * gam - j)) ∧
      picardTorsionTrace C (Stacks.Picard.schemePullbackClassHom φ) ℓ N =
        -(Fl.map (PadicInt.toZModPow N)).nextCoeff := by
    intro N hN
    have : Fact (1 < ℓ ^ N) := ⟨Nat.one_lt_pow hN.ne' hℓp.one_lt⟩
    obtain ⟨E⟩ := htors N
    let b := (Stacks.Picard.levelBasis N E).map (eN N)
    have hmat : LinearMap.toMatrix b b (σN N) = Stacks.Picard.levelMatrix u N E := by
      ext i j
      rw [Stacks.Picard.levelMatrix, ← hconj, LinearMap.toMatrix_apply, LinearMap.toMatrix_apply]
      simp only [b, Module.Basis.map_apply, Module.Basis.map_repr, LinearEquiv.trans_apply,
        LinearEquiv.conj_apply_apply, LinearEquiv.symm_apply_apply]
    obtain ⟨e, he, heσ⟩ := hweil N
    exact charpoly_symm_and_trace_eq_of_pairing b (σN N) (τN N) (q : ZMod (ℓ ^ N))
      (isUnit_natCast_pow_of_prime_ne hpp hℓp hpℓ f N) e he heσ (hcomp N _ _ hΨ) (hcomp N _ _ hφΨ)
      (by rw [hmat, hFlev N E])
  have hsym : ∀ j ≤ 2 * gam, χ.coeff 0 * χ.coeff j = (q : ℚ) ^ (2 * gam - j) * χ.coeff (2 * gam - j) :=
    coeff_zero_mul_coeff_eq_of_toZModPow hFχ q (2 * gam) fun N hN => (hlevel N hN).1
  -- the zeta function and the roots of `χ`
  set h : ℕ → ℕ := fun m => Nat.card {c : Stacks.Picard.ofScheme C // deg c = 0 ∧ Pσ^[m] c = c}
  have hnorm : ∀ m, 0 < m → (h m : ℚ) = Stacks.Polynomial.normForm χ (1 - Polynomial.X ^ m) := by
    intro m hm
    show ((Nat.card {c : Stacks.Picard.ofScheme C // deg c = 0 ∧ Pσ^[m] c = c} : ℕ) : ℚ) = _
    rw [← natCard_ker_one_sub_pow_eq deg Pσ u (fun c => rfl) m]
    exact hker _ (not_dvd_coeff_zero_one_sub_X_pow hpp hm)
  have hh0 : ∀ m, 0 < m → h m ≠ 0 := by
    intro m hm
    have := hfinH m hm
    have : Nonempty {c : Stacks.Picard.ofScheme C // deg c = 0 ∧ Pσ^[m] c = c} :=
      ⟨⟨0, map_zero _, Function.iterate_fixed (map_zero Pσ) m⟩⟩
    exact Nat.card_pos.ne'
  have hnext := Stacks.Zeta.nextCoeff_eq_neg_sum_of_zeta χ hmon gam hχdeg q hq1 hsym
    (coeff_zero_nonneg_of_normForm_X_nonneg hmon hχdeg hnf) r α hr hαint h
    (fun m hm => (hzeta m hm).2.1) hh0 (fun m hm => (hzeta m hm).2.2) hnorm
  set N₁ := Nat.card {x : C | IsClosed ({x} : Set C) ∧ Ψ.hom.base^[1] x = x}
  have h1 := (hzeta 1 one_pos).1
  simp only [pow_one] at h1
  have hχnext : χ.nextCoeff = (((N₁ : ℤ) - 1 - q : ℤ) : ℚ) := by
    apply (algebraMap ℚ (AlgebraicClosure ℚ)).injective
    rw [hnext]
    push_cast
    linear_combination -h1
  exact ⟨hχnext, hsym⟩

end Twisted

/-! ### The Jacobian site of a Weierstrass curve -/

namespace Jac

open AlgebraicGeometry.ModuliEllipticCurves AlgebraicGeometry.ModuliEllipticCurves.Weierstrass
open RamanujanWeil.Ihara Stacks.PicardFunctor

variable {k : Type u} [Field k] [Fintype k] (W : WeierstrassCurve k)

/-- `projOf W` as a scheme over `Spec k`. -/
abbrev Yw : Over (Spec (.of k)) := Over.mk (projectionOf W)

/-- The geometric cubic `E_W = projOf W ×_k K̄` (Stacks' `fieldBaseChange`). -/
abbrev Ew : Scheme.{u} := fieldBaseChange (Yw W) (AlgebraicClosure k)

/-- The structure morphism `E_W ⟶ Spec K̄`. -/
abbrev gw : Ew W ⟶ Spec (.of (AlgebraicClosure k)) :=
  pullback.snd (Yw W).hom (specAlgebraMap k (AlgebraicClosure k))

/-- **A Jacobian site for `W`**: a big fppf site containing `E_W` and `Spec K̄`. -/
structure JacSite where
  /-- The site. -/
  B : BigFppfSite.{u}
  /-- It contains `E_W`. -/
  hX : B.Contains (Ew W)
  /-- It contains `Spec K̄`. -/
  hk : B.Contains (Spec (.of (AlgebraicClosure k)))

/-- Jacobian sites exist. -/
theorem nonempty_jacSite : Nonempty (JacSite W) := by
  let S₀ : Set Scheme.{u} := {Ew W, Spec (.of (AlgebraicClosure k))}
  have : Small.{u} S₀ := by dsimp [S₀]; infer_instance
  obtain ⟨B, hB⟩ := BigFppfSite.exists_containing S₀
  exact ⟨⟨B, hB _ (by simp [S₀]), hB _ (by simp [S₀])⟩⟩

/-- The zero section `O : Spec K̄ ⟶ E_W`. It is the zero of `Coord.geomFamily W`. -/
def zeroPt : Spec (.of (AlgebraicClosure k)) ⟶ Ew W :=
  pullback.lift (specAlgebraMap k (AlgebraicClosure k) ≫ zeroOf W) (𝟙 _) (by
    rw [Category.assoc, show (Yw W).hom = projectionOf W from rfl, zeroOf_projectionOf,
      Category.comp_id, Category.id_comp])

theorem zeroPt_eq_geomFamily_zero : zeroPt W = (Coord.geomFamily W).zero := rfl

namespace JacSite

variable {W} (S : JacSite W)

/-- The structure morphism of `E_W` as a morphism of the site. -/
def f : S.B.obj S.hX ⟶ S.B.obj S.hk := ObjectProperty.homMk (gw W)

theorem inclusion_map_f : S.B.inclusion.map S.f = gw W := rfl

theorem o_comp : zeroPt W ≫ S.B.inclusion.map S.f = 𝟙 _ := pullback.lift_snd _ _ _


variable [W.IsElliptic]

instance isCurve_f : IsCurve (AlgebraicClosure k) (S.B.inclusion.map S.f) :=
  isCurve_projOf_baseChange W _

instance smooth_f : Smooth (S.B.inclusion.map S.f) :=
  inferInstanceAs (Smooth (pullback.snd (projectionOf W)
    (specAlgebraMap k (AlgebraicClosure k))))

instance isProper_f : IsProper (S.B.inclusion.map S.f) :=
  inferInstanceAs (IsProper (pullback.snd (projectionOf W)
    (specAlgebraMap k (AlgebraicClosure k))))

instance geometricallyIrreducible_f : GeometricallyIrreducible (S.B.inclusion.map S.f) := by
  have : IsCurve (AlgebraicClosure k) (gw W) := isCurve_projOf_baseChange W _
  have : IrreducibleSpace (Ew W) := inferInstance
  exact geometricallyIrreducible_of_irreducibleSpace_of_isSepClosed (AlgebraicClosure k)
    (Ew W) (gw W)

theorem isProjectiveMorphism_f : IsProjectiveMorphism (S.B.inclusion.map S.f) := by
  have : IsCurve (AlgebraicClosure k) (gw W) := isCurve_projOf_baseChange W _
  have : IsProper (gw W) := S.isProper_f
  exact isProjectiveMorphism_of_isProper_of_isCurve (AlgebraicClosure k) (gw W)

instance isProjectiveVariety_f : IsProjectiveVariety (AlgebraicClosure k) (S.B.inclusion.map S.f) := by
  have : IsCurve (AlgebraicClosure k) (gw W) := isCurve_projOf_baseChange W _
  have : IsProper (gw W) := S.isProper_f
  have hproj : IsProjective (S.B.inclusion.map S.f) :=
    (isProjectiveVariety_iff_isProjective (AlgebraicClosure k) (gw W)).1
      ((isProjectiveVariety_iff_isProjectiveMorphism (AlgebraicClosure k) (gw W)).2
        (isProjectiveMorphism_of_isProper_of_isCurve (AlgebraicClosure k) (gw W)))
  exact (isProjectiveVariety_iff_isProjective (AlgebraicClosure k) (gw W)).2 hproj

instance isRepresentable : (picardFunctor S.B S.hX S.hk S.f).IsRepresentable :=
  Stacks.RigidifiedPicard.isRepresentable_picardFunctor_of_isSepClosed (AlgebraicClosure k)
    S.B S.hX S.hk S.f S.isProjectiveMorphism_f

/-- **The Jacobian `J_W = Pic⁰_{E_W/K̄}`.** -/
abbrev J : Over (Spec (.of (AlgebraicClosure k))) := (jacobianGrp S.B S.hX S.hk S.f (zeroPt W) S.o_comp).X

instance isAbelianVariety_J : AlgebraicGeometry.IsAbelianVariety (AlgebraicClosure k) S.J :=
  isAbelianVariety_jacobian S.B S.hX S.hk S.f (zeroPt W) S.o_comp

/-- **The Abel–Jacobi map `aj_W : E_W ⟶ J_W`, `P ↦ 𝒪(P − O)`.** -/
def aj : curveOver S.B S.hX S.hk S.f ⟶ S.J := abelJacobi S.B S.hX S.hk S.f (zeroPt W) S.o_comp

/-! #### The Frobenius -/

attribute [local instance] RamanujanWeil.Ihara.fact_ringChar_prime

instance charP_bar : CharP (AlgebraicClosure k) (ringChar k) :=
  have : CharP k (ringChar k) := ringChar.charP k
  charP_of_injective_algebraMap (algebraMap k (AlgebraicClosure k)).injective _

/-- The `q`-power Frobenius of `K̄` over `k`, as in `DeuringG2` (`arithmeticFrobenius ^ 1`). -/
noncomputable abbrev frob : AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k :=
  arithmeticFrobenius k (AlgebraicClosure k) (ringChar k) (cardExp k) card_eq_ringChar_pow ^ 1

/-- The twisted Frobenius `Ψ_W = id × Spec(frob)` of `E_W`, as in `DeuringG2`. -/
noncomputable abbrev Ψ : Ew W ≅ Ew W := galoisBaseChangeIso (Yw W) (AlgebraicClosure k) frob

/-- `Ψ_W` is the twisted Frobenius `Coord.twistFrob W` of G1.3. -/
theorem twist_eq : (Ψ (W := W)).hom = Coord.twistFrob W := by
  have : (frob : AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k) = Coord.frobAlg k := by
    simp only [frob, pow_one]
    symm
    apply eq_arithmeticFrobenius
    intro x
    rw [FiniteField.coe_frobeniusAlgEquivOfAlgebraic]
  show galoisBaseChange (Yw W) (AlgebraicClosure k) frob = _
  rw [this]

theorem specIsInChar : IsInCharacteristic (Spec (.of (AlgebraicClosure k))) (ringChar k) :=
  isInCharacteristic_spec _ _ (CharP.cast_eq_zero _ _)

theorem Ψ_comp : (Ψ (W := W)).hom ≫ S.B.inclusion.map S.f =
    S.B.inclusion.map S.f ≫
      absoluteFrobeniusPow (Spec (.of (AlgebraicClosure k))) (ringChar k) specIsInChar
        (cardExp k) := by
  rw [inclusion_map_f, ← specMap_eq_absoluteFrobeniusPow
    (frob : AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k).toAlgHom.toRingHom _ _ specIsInChar
    (fun a => by
      simp only [frob, pow_one]
      exact iterateFrobeniusEquiv_def _ _ _ a)]
  exact galoisBaseChange_comp_snd (Yw W) (AlgebraicClosure k) frob

/-- **The Frobenius `π_W` of the Jacobian**, induced by `Ψ_W`. -/
def π : S.J ⟶ S.J :=
  jacobianFrobenius S.B S.hX S.hk S.f (ringChar k) specIsInChar (cardExp k) Ψ.hom S.Ψ_comp
    (zeroPt W) S.o_comp

instance isMonHom_π : IsMonHom S.π := by
  unfold π; infer_instance

theorem cardExp_pos : 0 < cardExp k := by
  have hq1 : 1 < Fintype.card k := Fintype.one_lt_card
  rcases Nat.eq_zero_or_pos (cardExp k) with h | h
  · rw [card_eq_ringChar_pow, h, pow_zero] at hq1; omega
  · exact h

theorem topologicalKrullDim_le : topologicalKrullDim (Ew W) ≤ 1 :=
  have : IsCurve (AlgebraicClosure k) (gw W) := isCurve_projOf_baseChange W _
  Stacks.Zeta.topologicalKrullDim_le_one (gw W)

theorem dim_J_genus : abelianVarietyDimension S.J = genus (S.B.inclusion.map S.f) := by
  have : SmoothOfRelativeDimension (genus (S.B.inclusion.map S.f)) S.J.hom :=
    smoothOfRelativeDimension_picardSchemeDegreeComponent S.B S.hX S.hk S.f (zeroPt W) S.o_comp 0
  have : Nonempty S.J.left := ⟨(η[S.J]).left (IsLocalRing.closedPoint (AlgebraicClosure k))⟩
  have h1 := topologicalKrullDim_eq_of_smoothOfRelativeDimension_over_field
    (genus (S.B.inclusion.map S.f)) S.J.hom
  have h2 := Stacks.Groupoids.topologicalKrullDim_eq_abelianVarietyDimension S.J
  rw [h1] at h2
  exact_mod_cast h2.symm

theorem dim_J : abelianVarietyDimension S.J = 1 :=
  S.dim_J_genus.trans (genus_projOf_baseChange W _)

/-- **G2 for the concrete Jacobian**: `χ_{π_W} = X² − tX + q`, `t = traceOfFrob W`. -/
theorem charPoly_π : endCharPoly S.J S.π =
    Polynomial.X ^ 2 - C ((traceOfFrob W : ℤ) : ℚ) * Polynomial.X + C ((Nat.card k : ℕ) : ℚ) := by
  classical
  set p := ringChar k
  have : CharP k p := ringChar.charP k
  set f := cardExp k
  have hcard : Fintype.card k = p ^ f := card_eq_ringChar_pow (k := k)
  set kbar := AlgebraicClosure k
  set Y := Yw W
  have : IsCurve kbar (pullback.snd Y.hom (specAlgebraMap k kbar)) :=
    isCurve_projOf_baseChange W kbar
  have : Smooth (pullback.snd Y.hom (specAlgebraMap k kbar)) :=
    inferInstanceAs (Smooth (pullback.snd (projectionOf W) (specAlgebraMap k kbar)))
  have : IsProper (pullback.snd Y.hom (specAlgebraMap k kbar)) :=
    inferInstanceAs (IsProper (pullback.snd (projectionOf W) (specAlgebraMap k kbar)))
  have hC := isInCharacteristic_fieldBaseChange Y kbar p
  set φ := geometricFrobeniusBaseChangePow Y kbar p f hcard 1
  have hΨ : (Ψ (W := W)).hom ≫ φ = absoluteFrobeniusPow (fieldBaseChange Y kbar) p hC (f * 1) :=
    galoisBaseChange_comp_geometricFrobeniusBaseChangePow Y kbar p f hcard 1 _
      (arithmeticFrobenius_pow_apply kbar p f hcard 1)
  have w := geometricFrobeniusBaseChangePow_snd Y kbar p f hcard 1
  have hf : 0 < f * 1 := by rw [mul_one]; exact cardExp_pos
  have hdim := topologicalKrullDim_le (W := W)
  have hdimA : abelianVarietyDimension S.J = genus (pullback.snd Y.hom (specAlgebraMap k kbar)) :=
    S.dim_J_genus
  obtain ⟨hnext, hsym⟩ := charPoly_of_jacobianData p (isAlgebraic_zmod_of_finite k kbar p)
    (pullback.snd Y.hom (specAlgebraMap k kbar)) φ w (f * 1) hf hC Ψ hΨ hdim S.J
    (jacobianPointsAddEquiv S.B S.hX S.hk S.f (zeroPt W) S.o_comp hdim) S.π hdimA
    (jacobianPointsAddEquiv_comp_jacobianFrobenius S.B S.hX S.hk S.f p specIsInChar f
      Ψ.hom S.Ψ_comp (zeroPt W) S.o_comp hdim)
    (tangent_comp_jacobianFrobenius S.B S.hX S.hk S.f p specIsInChar f Ψ.hom S.Ψ_comp
      (zeroPt W) S.o_comp cardExp_pos)
  have hgenus : genus (pullback.snd Y.hom (specAlgebraMap k kbar)) = 1 :=
    genus_projOf_baseChange W kbar
  rw [natCard_fixedClosedPoints_weierstrass W p f hcard] at hnext
  rw [hgenus] at hdimA hsym
  have hq : ((p ^ (f * 1) : ℕ) : ℚ) = ((Nat.card k : ℕ) : ℚ) := by
    rw [mul_one, ← hcard, Fintype.card_eq_nat_card]
  set χ := endCharPoly S.J S.π with hχ
  have hdeg : χ.natDegree = 2 := by rw [natDegree_endCharPoly, hdimA]
  have h2 : χ.coeff 2 = 1 := by rw [← hdeg]; exact (endCharPoly_monic S.J S.π).coeff_natDegree
  have hqZ : ((p ^ (f * 1) : ℕ) : ℤ) = ((Nat.card k : ℕ) : ℤ) := by
    rw [mul_one, ← hcard, Fintype.card_eq_nat_card]
  have h1 : χ.coeff 1 = -((traceOfFrob W : ℤ) : ℚ) := by
    have := nextCoeff_of_natDegree_pos (p := χ) (by omega)
    rw [hdeg] at this
    rw [show (1 : ℕ) = 2 - 1 from rfl, ← this, hnext, traceOfFrob, hqZ]
    push_cast
    ring
  have h0 : χ.coeff 0 = ((Nat.card k : ℕ) : ℚ) := by
    have hs := hsym 0 (by omega)
    have h2' : χ.coeff (2 * 1 - 0) = 1 := h2
    rw [h2', mul_one, hq] at hs
    have hs' : χ.coeff 0 ^ 2 = ((Nat.card k : ℕ) : ℚ) ^ 2 := by rw [sq, hs]
    have hnn : 0 ≤ χ.coeff 0 := by rw [coeff_zero_endCharPoly]; exact Nat.cast_nonneg _
    have hqpos : (0 : ℚ) ≤ ((Nat.card k : ℕ) : ℚ) := Nat.cast_nonneg _
    exact (pow_left_inj₀ hnn hqpos two_ne_zero).mp hs'
  exact quadratic_ext _ _ _ hdeg h2 h1 h0

/-- **The concrete Frobenius Jacobian** `(J_W, π_W)` of `W`. -/
noncomputable def frobeniusJacobian : FrobeniusJacobian W where
  A := S.J
  grp := inferInstance
  isAV := inferInstance
  π := S.π
  isMonHom := inferInstance
  dim_eq := S.dim_J
  charPoly_eq := S.charPoly_π

theorem frobeniusJacobian_A : S.frobeniusJacobian.A = S.J := rfl
theorem frobeniusJacobian_π : S.frobeniusJacobian.π = S.π := rfl

/-- **`π_W² − tπ_W + q = 0`** in `End(J_W)`. -/
theorem frob_quadratic :
    endPolyEval S.π (Polynomial.X ^ 2 - C (traceOfFrob W) * Polynomial.X + C (Nat.card k : ℤ)) = 1 :=
  S.frobeniusJacobian.frob_quadratic

/-- **`deg π_W = q`.** -/
theorem endDegree_π : (endDegree S.J S.π : ℚ) = ((Nat.card k : ℕ) : ℚ) :=
  S.frobeniusJacobian.endDegree_π

end JacSite

end Jac

end RamanujanWeil.Arith.Deuring.Geom
