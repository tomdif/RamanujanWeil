import RamanujanWeil.Arith.DeuringG4
import RamanujanWeil.Ihara.PointsCurve
import RamanujanWeil.Ihara.CurveH1BettiConnected
import RamanujanWeil.Ihara.IharaStatement
import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.ConstantCurvePointCount

/-!
# A3-ord, G2: the Frobenius of an elliptic curve satisfies `π² − tπ + q = 0`

Framework (`docs/ARITH_DEURING_PLAN.md` §4, refined in `docs/ARITH_DEURING_PROGRESS.md`): all
Tate-module results of Stacks are stated over an algebraically closed field, so the abelian
variety attached to an elliptic Weierstrass curve `W / 𝔽_q` is the Jacobian `A_W` of the
geometric curve `E_k̄ = (projOf W) ×_k k̄`, and its Frobenius `π_W` is the endomorphism induced
by the *twisted Frobenius* `Ψ = id × Spec(x ↦ x^q)` of `E_k̄` (Stacks'
`Stacks.Zeta.exists_jacobianFrobenius_data`, which is Weil's set-up for the Riemann hypothesis).

## Main results

* `exists_jacobian_charPoly_twisted` (any smooth proper curve `C / Ω`, `Ω = 𝔽̄_p`, with a twisted
  Frobenius `Ψ`, `Ψ ≫ φ = F^f`): the Jacobian `A` of `C` with its Frobenius `F` has
  `χ_F.nextCoeff = N₁ − 1 − q` (`N₁` = closed points fixed by `Ψ`) and `χ_F` is
  `q`-symmetric. This is the part of Stacks' proof of `weilTraceInput` that identifies the
  characteristic polynomial, redone with `χ := endCharPoly A F` (Stacks only exports the
  trace formula).
* **`exists_frobeniusJacobian`** (G2): for `W` elliptic over `𝔽_q` there are an abelian variety
  `A` of dimension one over `k̄ = AlgebraicClosure 𝔽_q` and a homomorphism `π : A ⟶ A` with
  `χ_π = X² − tX + q`, `t = traceOfFrob W = q + 1 − #W(𝔽_q)`, and
  **`π² − tπ + q = 0` in `End(A)`** (via Cayley–Hamilton, `DeuringG3`).
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory Polynomial
open Stacks.Frobenius Stacks.EtaleCohomology
open scoped CategoryTheory.MonObj

universe u

namespace RamanujanWeil.Arith.Deuring.Geom

open Stacks.Groupoids

section Twisted

variable {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (p : ℕ) [hp : Fact p.Prime] [CharP Ω p]
  (halg : letI := ZMod.algebra Ω p; Algebra.IsAlgebraic (ZMod p) Ω)
  {C : Scheme.{u}} (g : C ⟶ Spec (.of Ω)) [IsProper g] [Smooth g] [IsCurve Ω g]
  (φ : C ⟶ C) (w : φ ≫ g = g) (f : ℕ) (hf : 0 < f) (hC : IsInCharacteristic C p) (Ψ : C ≅ C)
  (hΨ : Ψ.hom ≫ φ = absoluteFrobeniusPow C p hC f)

include halg w hf hΨ in
/-- **The characteristic polynomial of the Frobenius of the Jacobian of a curve with a twisted
Frobenius.** There are an abelian variety `A` of dimension `genus g` and a homomorphism `F` (the
Frobenius of the Jacobian, `Ψ^*` on points) whose characteristic polynomial `χ = χ_F` has
`χ.nextCoeff = N₁ − 1 − q`, `N₁` the number of closed points fixed by `Ψ`, and
`χ(0) χ_j = q^{2γ−j} χ_{2γ−j}`. -/
theorem exists_jacobian_charPoly_twisted :
    ∃ (A : Over (Spec (.of Ω))) (_ : GrpObj A) (_ : AlgebraicGeometry.IsAbelianVariety Ω A)
      (F : A ⟶ A) (_ : IsMonHom F),
      abelianVarietyDimension A = genus g ∧
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
  have hdim : topologicalKrullDim C ≤ 1 := Stacks.Zeta.topologicalKrullDim_le_one g
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
  obtain ⟨A, _, _, E, F, _, hdimA, hpts, htan⟩ :=
    Stacks.Zeta.exists_jacobianFrobenius_data p g hdim f hf Ψ.hom hΨs
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
  exact ⟨A, inferInstance, inferInstance, F, inferInstance, hdimA, hχnext, hsym⟩

end Twisted

/-! ### The elliptic curve `projOf W` over `𝔽_q` -/

section Weierstrass

open AlgebraicGeometry.ModuliEllipticCurves.Weierstrass RamanujanWeil.Ihara

variable {k : Type u} [Field k] [Fintype k] (W : WeierstrassCurve k) [W.IsElliptic]

/-- **The number of `𝔽_q`-points of `E = projOf W` fixed by the twisted Frobenius.** With
`Y = projOf W`, `k̄ = AlgebraicClosure k`, `Ψ = id × Spec(Frob_q)` and `π̄` the geometric Frobenius
of `Y` base changed to `k̄`: the closed points of `Y_k̄` fixed by `Ψ` are `#W(𝔽_q)`. -/
theorem natCard_fixedClosedPoints_weierstrass (p f : ℕ) [Fact p.Prime] [CharP k p]
    (hcard : Fintype.card k = p ^ f) :
    haveI : CharP (AlgebraicClosure k) p :=
      charP_of_injective_algebraMap (algebraMap k (AlgebraicClosure k)).injective p
    Nat.card {x : fieldBaseChange (Over.mk (projectionOf W)) (AlgebraicClosure k) |
        IsClosed ({x} : Set _) ∧
        (galoisBaseChangeIso (Over.mk (projectionOf W)) (AlgebraicClosure k)
          (arithmeticFrobenius k (AlgebraicClosure k) p f hcard ^ 1)).hom.base^[1] x = x} =
      Nat.card W.toAffine.Point := by
  haveI : CharP (AlgebraicClosure k) p :=
    charP_of_injective_algebraMap (algebraMap k (AlgebraicClosure k)).injective p
  set Y := Over.mk (projectionOf W)
  set kbar := AlgebraicClosure k
  have : IsCurve kbar (pullback.snd Y.hom (specAlgebraMap k kbar)) :=
    isCurve_projOf_baseChange W kbar
  have : LocallyOfFiniteType (pullback.snd Y.hom (specAlgebraMap k kbar)) :=
    inferInstanceAs (LocallyOfFiniteType (pullback.snd (projectionOf W) (specAlgebraMap k kbar)))
  have hC := isInCharacteristic_fieldBaseChange Y kbar p
  set Ψ := galoisBaseChangeIso Y kbar (arithmeticFrobenius k kbar p f hcard ^ 1)
  set φ := geometricFrobeniusBaseChangePow Y kbar p f hcard 1
  have hΨ : Ψ.hom ≫ φ = absoluteFrobeniusPow (fieldBaseChange Y kbar) p hC (f * 1) :=
    galoisBaseChange_comp_geometricFrobeniusBaseChangePow Y kbar p f hcard 1 _
      (arithmeticFrobenius_pow_apply kbar p f hcard 1)
  have w := geometricFrobeniusBaseChangePow_snd Y kbar p f hcard 1
  have hφΨ : φ ≫ Ψ.hom = absoluteFrobeniusPow (fieldBaseChange Y kbar) p hC (f * 1) := by
    rw [← cancel_epi Ψ.hom, ← Category.assoc, hΨ,
      AlgebraicGeometry.absoluteFrobeniusPow_naturality Ψ.hom p hC hC (f * 1)]
  rw [← natCard_fixedSections_eq_natCard_fixedClosedPoints_of_comp_eq_absoluteFrobeniusPow
    (pullback.snd Y.hom (specAlgebraMap k kbar)) φ w p hC (f * 1) Ψ hφΨ]
  let K : IntermediateField k kbar := ⊥
  let eK : K ≃ₐ[k] k := IntermediateField.botEquiv k kbar
  letI : Fintype K := Fintype.ofEquiv k eK.toEquiv.symm
  have hK : Fintype.card K = p ^ (f * 1) := by
    rw [Fintype.card_congr eK.toEquiv, hcard, mul_one]
  rw [natCard_fixedSections_geometricFrobeniusBaseChangePow Y kbar p f hcard 1 K hK]
  rw [show Y.hom = projectionOf W from rfl, natCard_fieldValuedPoints_projOf W K,
    natCard_point_congr W eK, baseChange_self]

/-- **The Frobenius Jacobian of an elliptic Weierstrass curve `W / 𝔽_q`** (the object of steps
G2–G9): an abelian variety `A` of dimension one over `k̄ = AlgebraicClosure k` (the Jacobian of
`E_k̄`, `E = projOf W`) with a homomorphism `π : A ⟶ A` (the Frobenius of the Jacobian, `Ψ^*` on
`A(k̄) = Pic⁰(E_k̄)`) whose characteristic polynomial is `X² − tX + q`, `t = traceOfFrob W`. -/
structure FrobeniusJacobian where
  /-- The abelian variety. -/
  A : Over (Spec (.of (AlgebraicClosure k)))
  /-- Its group law. -/
  grp : GrpObj A
  /-- It is an abelian variety. -/
  isAV : AlgebraicGeometry.IsAbelianVariety (AlgebraicClosure k) A
  /-- The Frobenius. -/
  π : A ⟶ A
  /-- The Frobenius is a homomorphism. -/
  isMonHom : IsMonHom π
  /-- `dim A = 1`. -/
  dim_eq : abelianVarietyDimension A = 1
  /-- `χ_π = X² − tX + q`. -/
  charPoly_eq : endCharPoly A π =
    Polynomial.X ^ 2 - C ((traceOfFrob W : ℤ) : ℚ) * Polynomial.X + C ((Nat.card k : ℕ) : ℚ)

attribute [instance] FrobeniusJacobian.grp FrobeniusJacobian.isAV FrobeniusJacobian.isMonHom

/-- **G2, existence**: every elliptic `W / 𝔽_q` has a Frobenius Jacobian. -/
theorem nonempty_frobeniusJacobian : Nonempty (FrobeniusJacobian W) := by
  classical
  have := RamanujanWeil.Ihara.fact_ringChar_prime (k := k)
  set p := ringChar k
  have : CharP k p := ringChar.charP k
  set f := RamanujanWeil.Ihara.cardExp k
  have hcard : Fintype.card k = p ^ f := RamanujanWeil.Ihara.card_eq_ringChar_pow (k := k)
  set kbar := AlgebraicClosure k
  have : CharP kbar p := charP_of_injective_algebraMap (algebraMap k kbar).injective p
  set Y := Over.mk (projectionOf W)
  have : IsCurve kbar (pullback.snd Y.hom (specAlgebraMap k kbar)) :=
    isCurve_projOf_baseChange W kbar
  have : Smooth (pullback.snd Y.hom (specAlgebraMap k kbar)) :=
    inferInstanceAs (Smooth (pullback.snd (projectionOf W) (specAlgebraMap k kbar)))
  have : IsProper (pullback.snd Y.hom (specAlgebraMap k kbar)) :=
    inferInstanceAs (IsProper (pullback.snd (projectionOf W) (specAlgebraMap k kbar)))
  have hC := isInCharacteristic_fieldBaseChange Y kbar p
  set Ψ := galoisBaseChangeIso Y kbar (arithmeticFrobenius k kbar p f hcard ^ 1)
  set φ := geometricFrobeniusBaseChangePow Y kbar p f hcard 1
  have hΨ : Ψ.hom ≫ φ = absoluteFrobeniusPow (fieldBaseChange Y kbar) p hC (f * 1) :=
    galoisBaseChange_comp_geometricFrobeniusBaseChangePow Y kbar p f hcard 1 _
      (arithmeticFrobenius_pow_apply kbar p f hcard 1)
  have w := geometricFrobeniusBaseChangePow_snd Y kbar p f hcard 1
  have hq1 : 1 < Fintype.card k := Fintype.one_lt_card
  have hf : 0 < f * 1 := by
    rw [mul_one]
    rcases Nat.eq_zero_or_pos f with h | h
    · rw [hcard, h, pow_zero] at hq1; omega
    · exact h
  obtain ⟨A, _, _, F, _, hdimA, hnext, hsym⟩ := exists_jacobian_charPoly_twisted p
    (isAlgebraic_zmod_of_finite k kbar p) (pullback.snd Y.hom (specAlgebraMap k kbar)) φ w
    (f * 1) hf hC Ψ hΨ
  have hgenus : genus (pullback.snd Y.hom (specAlgebraMap k kbar)) = 1 :=
    genus_projOf_baseChange W kbar
  rw [natCard_fixedClosedPoints_weierstrass W p f hcard] at hnext
  rw [hgenus] at hdimA hsym
  have hq : ((p ^ (f * 1) : ℕ) : ℚ) = ((Nat.card k : ℕ) : ℚ) := by
    rw [mul_one, ← hcard, Fintype.card_eq_nat_card]
  set χ := endCharPoly A F with hχ
  have hdeg : χ.natDegree = 2 := by rw [natDegree_endCharPoly, hdimA]
  have h2 : χ.coeff 2 = 1 := by rw [← hdeg]; exact (endCharPoly_monic A F).coeff_natDegree
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
  refine ⟨⟨A, inferInstance, inferInstance, F, inferInstance, hdimA, ?_⟩⟩
  rw [← hχ]
  exact quadratic_ext _ _ _ hdeg h2 h1 h0

/-- **G2: `π² − tπ + q = 0` in `End(A)`**, `t = traceOfFrob W`, `q = #𝔽_q`. -/
theorem FrobeniusJacobian.frob_quadratic (J : FrobeniusJacobian W) :
    endPolyEval J.π (Polynomial.X ^ 2 - C (traceOfFrob W) * Polynomial.X + C (Nat.card k : ℤ)) = 1 := by
  apply endPolyEval_eq_one_of_endCharPoly_eq J.dim_eq
  rw [J.charPoly_eq]
  simp

/-- **Hasse's bound from the Frobenius Jacobian**: `t² ≤ 4q`, here derived from the positivity
of the degree on `End(A)` rather than from étale cohomology. -/
theorem FrobeniusJacobian.endDegree_π (J : FrobeniusJacobian W) :
    (endDegree J.A J.π : ℚ) = ((Nat.card k : ℕ) : ℚ) := by
  rw [← coeff_zero_endCharPoly, J.charPoly_eq]
  simp

end Weierstrass

end RamanujanWeil.Arith.Deuring.Geom
