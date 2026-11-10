import RamanujanWeil.Arith.DeuringFinalSite
import RamanujanWeil.Arith.DeuringPLink

/-!
# A3-ord, final: the per-class lattice count without Tate

`docs/ARITH_DEURING_FINAL.md` §3. `ClassLattice.deuringMultiplicity_of_props` took
`TateFinitenessPolAll` only to have the `Λ` field (`Hom_π(J_{W₀}, J_W)` of rank 2) and the
prime-to-`p` link for **every** curve `W` of trace `t`. The structure `DeuringClassLattice K t P`
only ever looks at curves in `P` (the class). Restricted to the class, the homomorphisms come from
`Final.frobHomNe_both_class` (no finiteness), so:

* `exists_latticeMatrix_cls`: `Λ` on the class;
* `surjClass_of_descent_cls`: G5's `surjClass_of_descent`, with the `Λ` hypothesis restricted to
  the class (the realized curve `W₀/Γ` is shown to lie in `C` first; the proof is otherwise the
  one of `G5.surjClass_of_descent`);
* `classLattice_cls`: `ClassLattice.classLattice_fam` with all hypotheses restricted to `P`;
* **`nonempty_classLattice_uncond`**, **`deuringClassLatticeAll_uncond`**,
  **`deuringMultiplicity_uncond : DeuringMultiplicity hurwitz p (mult p)`**: no hypothesis.

So the exact per-class count is unconditional, and Deligne's bound needs only `mult ≤ 1` **or**
`mult ≥ 1` (`DeuringFinal`).
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory MulAction
  WeierstrassCurve
open scoped CategoryTheory.MonObj

set_option linter.unusedSectionVars false

universe u

noncomputable section

namespace RamanujanWeil.Arith.Deuring.Final

open RamanujanWeil.Ihara RamanujanWeil.Arith RamanujanWeil.Arith.Deuring
  RamanujanWeil.Arith.Deuring.Geom RamanujanWeil.Arith.Deuring.Geom.G7
  RamanujanWeil.Arith.Deuring.Mult RamanujanWeil.Arith.Deuring.ClassLattice
  RamanujanWeil.Arith.Deuring.G5 RamanujanWeil.Arith.Deuring.Dual2 RamanujanWeil.Arith.Deuring.G8
  RamanujanWeil.Arith.Deuring.G8Int Stacks.Groupoids RamanujanWeil.ArithPlan
  RamanujanWeil.Arith.Hurwitz

variable {K : Type u} [Field K] [Fintype K] {t : ℤ}

/-! ### `Λ` on one class -/

/-- **The `Λ` field on a set `P` of curves**, for a family of Jacobians with homomorphisms both
ways to `J W₀` for the curves in `P` (`ClassLattice.exists_latticeMatrix_fam`, restricted). -/
theorem exists_latticeMatrix_famP (J : JacFam K) {W₀ : WeierstrassCurve K} [W₀.IsElliptic]
    (ht₀ : traceOfFrob W₀ = t) (hlt : t ^ 2 < 4 * (Nat.card K : ℤ))
    (P : WeierstrassCurve K → Prop)
    (hhom : ∀ (W : WeierstrassCurve K) [W.IsElliptic], traceOfFrob W = t → P W →
      FrobHomNe (J W₀) (J W) ∧ FrobHomNe (J W) (J W₀)) :
    ∃ Λ : WeierstrassCurve K → TrDet t (Nat.card K),
      ∀ (W : WeierstrassCurve K) (hW : W.Δ ≠ 0), traceOfFrob W = t → P W →
        haveI : W.IsElliptic := ⟨isUnit_iff_ne_zero.mpr hW⟩
        ∃ b : Module.Basis (Fin 2) ℤ (homPi (J W₀).π (J W).π),
          (Λ W).1 = LinearMap.toMatrix b b (piAct (J W₀).π (J W).π) := by
  classical
  let M₀ : TrDet t (Nat.card K) := ⟨!![0, -(Nat.card K : ℤ); 1, t], by
    simp [Matrix.trace_fin_two], by simp [Matrix.det_fin_two]⟩
  have key : ∀ (W : WeierstrassCurve K) (hW : W.Δ ≠ 0), traceOfFrob W = t → P W →
      haveI : W.IsElliptic := ⟨isUnit_iff_ne_zero.mpr hW⟩
      ∃ M : TrDet t (Nat.card K), ∃ b : Module.Basis (Fin 2) ℤ (homPi (J W₀).π (J W).π),
          M.1 = LinearMap.toMatrix b b (piAct (J W₀).π (J W).π) := by
    intro W hW htW hPW
    have : W.IsElliptic := ⟨isUnit_iff_ne_zero.mpr hW⟩
    have ht : traceOfFrob W = traceOfFrob W₀ := htW.trans ht₀.symm
    have hlt' : traceOfFrob W₀ ^ 2 < 4 * (Nat.card K : ℤ) := by rw [ht₀]; exact hlt
    obtain ⟨h₁, h₂⟩ := hhom W htW hPW
    obtain ⟨-, b, htr, hdet⟩ := frobLattice_trDet (J W₀) (J W) ht hlt' h₁ h₂
    exact ⟨⟨_, htr.trans ht₀, hdet⟩, b, rfl⟩
  refine ⟨fun W => if h : W.Δ ≠ 0 ∧ traceOfFrob W = t ∧ P W then
    (key W h.1 h.2.1 h.2.2).choose else M₀, ?_⟩
  intro W hW htW hPW
  simp only [dif_pos (show W.Δ ≠ 0 ∧ traceOfFrob W = t ∧ P W from ⟨hW, htW, hPW⟩)]
  exact (key W hW htW hPW).choose_spec

set_option maxHeartbeats 1600000 in
/-- **The `Λ` field on one isogeny class** (global site, no Tate). -/
theorem exists_latticeMatrix_cls (G : GlobalSite K) {W₀ : WeierstrassCurve K} [W₀.IsElliptic]
    (ht₀ : traceOfFrob W₀ = t) (hlt : t ^ 2 < 4 * (Nat.card K : ℤ)) {C : IsogClass K t}
    (hC : IsogClassPred C W₀) :
    ∃ Λ : WeierstrassCurve K → TrDet t (Nat.card K),
      ∀ (W : WeierstrassCurve K) (hW : W.Δ ≠ 0), traceOfFrob W = t → IsogClassPred C W →
        haveI : W.IsElliptic := ⟨isUnit_iff_ne_zero.mpr hW⟩
        ∃ b : Module.Basis (Fin 2) ℤ
            (homPi ((G.site W₀).frobeniusJacobian).π ((G.site W).frobeniusJacobian).π),
          (Λ W).1 = LinearMap.toMatrix b b
            (piAct ((G.site W₀).frobeniusJacobian).π ((G.site W).frobeniusJacobian).π) :=
  exists_latticeMatrix_famP (fun W _ => (G.site W).frobeniusJacobian) ht₀ hlt (IsogClassPred C)
    (fun W _ _ hWC => frobHomNe_both_class G hC hWC)

/-! ### `surj_class` with `Λ` only on the class -/

set_option maxHeartbeats 800000 in
/-- **`surj_class` (G5) with the `Λ` specification only on the class `C`.** The proof is that of
`G5.surjClass_of_descent`; the realized curve is placed in `C` before `Λ` is used. -/
theorem surjClass_of_descent_cls (hD : WeierstrassDescent K) {W₀ : WeierstrassCurve K}
    [W₀.IsElliptic] (S₀ : Jac.JacSite W₀) (ht₀ : traceOfFrob W₀ = t)
    (hp : ¬ (ringChar K : ℤ) ∣ t) (hlt : t ^ 2 < 4 * (Nat.card K : ℤ))
    (hmin : MinimalOrder S₀.frobeniusJacobian.π)
    (C : IsogClass K t) (hC : IsogClassPred C W₀)
    (Λ : WeierstrassCurve K → TrDet t (Nat.card K))
    (hΛ : ∀ (W : WeierstrassCurve K) (hW : W.Δ ≠ 0), traceOfFrob W = t → IsogClassPred C W →
        haveI : W.IsElliptic := ⟨isUnit_iff_ne_zero.mpr hW⟩
        ∃ (S : Jac.JacSite W) (b : Module.Basis (Fin 2) ℤ
            (homPi S₀.frobeniusJacobian.π S.frobeniusJacobian.π)),
          (Λ W).1 = LinearMap.toMatrix b b
            (piAct S₀.frobeniusJacobian.π S.frobeniusJacobian.π))
    (M : TrDet t (Nat.card K)) :
    ∃ W : WeierstrassCurve K, IsogClassPred C W ∧ ∃ g : GL2, g • Λ W = M := by
  classical
  set J₀ := S₀.frobeniusJacobian
  have hA₀ := J₀.dim_eq
  have hχ₀ := J₀.charPoly_eq
  have hdisc : traceOfFrob W₀ ^ 2 < 4 * ((Nat.card K : ℕ) : ℤ) := by rw [ht₀]; exact hlt
  have hind := lin_eq_one_iff J₀.dim_eq J₀.π t (Nat.card K) (by rw [← ht₀]; exact hχ₀) hlt
  have hcyc : ∀ n : ℤ, IsUnit (n : AlgebraicClosure K) → CyclicTorsion J₀.π n :=
    fun n hn => cyclicTorsion_of_minimalOrder J₀.dim_eq hmin hind n hn
  obtain ⟨b₁, htr₁, hdet₁⟩ := exists_basis_trDet hA₀ hA₀ J₀.π J₀.π (traceOfFrob W₀)
    (Nat.card K) hχ₀ hχ₀ hdisc (𝟙 J₀.A) (id_ne_one hA₀) (by simp) (𝟙 J₀.A) (id_ne_one hA₀)
    (by simp)
  set M₁ := LinearMap.toMatrix b₁ b₁ (piAct J₀.π J₀.π)
  set p := ringChar K
  haveI : CharP K p := ringChar.charP K
  obtain ⟨m, hpp, hcard⟩ := FiniteField.card K p
  have hpq : (p : ℤ) ∣ (Nat.card K : ℤ) := by
    rw [Nat.card_eq_fintype_card, hcard]; push_cast; exact dvd_pow_self _ m.ne_zero
  have hd : ¬ (p : ℤ) ∣ disc M.1 := by
    rw [disc, M.2.1, M.2.2]
    intro h
    apply hp
    have h2 : (p : ℤ) ∣ t ^ 2 := by
      have := h.add (dvd_mul_of_dvd_right hpq 4)
      simpa using this
    exact (Nat.prime_iff_prime_int.mp hpp).dvd_of_dvd_pow h2
  obtain ⟨X, hX, hXp⟩ := exists_intertwiner M.1 M₁ (by rw [htr₁, M.2.1, ht₀])
    (by rw [hdet₁, M.2.2]) p hpp hd
  haveI : CharP (AlgebraicClosure K) p :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective p
  have hn : IsUnit (X.det : AlgebraicClosure K) := by
    refine Ne.isUnit ?_
    rw [Ne, CharP.intCast_eq_zero_iff (AlgebraicClosure K) p]
    exact hXp
  have hn0 : X.det ≠ 0 := by rintro h; rw [h] at hn; simp at hn
  obtain ⟨Γ, hfin, hπΓ, hkill, hreal⟩ := realize hA₀ b₁ M.1 M₁ X rfl hX hn hmin (hcyc _ hn)
  obtain ⟨G⟩ := nonempty_glue Γ
  obtain ⟨W, hΔ, htrW, hS⟩ := hD W₀ S₀ Γ hfin hπΓ X.det hn hkill G (GlueS.πB G J₀.π hπΓ)
    inferInstance (GlueS.q_πB G J₀.π hπΓ)
  haveI hell : W.IsElliptic := ⟨isUnit_iff_ne_zero.mpr hΔ⟩
  have htW : traceOfFrob W = t := htrW.trans ht₀
  have hWC : IsogClassPred C W := by
    obtain ⟨hW₀, hmk⟩ := hC
    refine ⟨⟨hΔ, htW⟩, ?_⟩
    rw [← hmk]
    apply Quotient.sound
    refine Relation.EqvGen.rel _ _ ?_
    obtain ⟨S⟩ := Jac.nonempty_jacSite W
    obtain ⟨e, he, hcomm⟩ := hS S
    haveI := he
    set s := GlueS.sMap G X.det hkill
    refine Or.inr ⟨hell, inferInstance, S, S₀, Or.inl ⟨e.hom ≫ s, inferInstance, ?_, ?_⟩⟩
    · rw [Category.assoc, GlueS.sMap_π G _ hkill J₀.π hπΓ, ← Category.assoc, hcomm,
        Category.assoc]
    · intro h1
      have hs1 : s = 1 := by
        rw [← Category.id_comp s, ← e.inv_hom_id, Category.assoc, h1, MonObj.comp_one]
      apply zpow_id_ne_one hA₀ X.det hn0
      rw [← GlueS.q_sMap G X.det hkill]
      change G.q ≫ s = 1
      rw [hs1, MonObj.comp_one]
  refine ⟨W, hWC, ?_⟩
  obtain ⟨S, b, hb⟩ := hΛ W hΔ htW hWC
  obtain ⟨e, he, hcomm⟩ := hS S
  have hreal' := hreal G (GlueS.πB G J₀.π hπΓ) (GlueS.q_πB G J₀.π hπΓ)
    S.frobeniusJacobian.A S.frobeniusJacobian.π e he hcomm
  obtain ⟨g, hg⟩ := hreal' b
  exact ⟨g, Subtype.ext (by rw [smul_val, hb]; exact hg)⟩

/-! ### The class lattice with hypotheses on the class only -/

/-- **`DeuringClassLattice` for a family of Jacobians, all hypotheses restricted to `P`.** -/
theorem classLattice_cls (J : JacFam K) {W₀ : WeierstrassCurve K} [W₀.IsElliptic]
    (ht₀ : traceOfFrob W₀ = t)
    (hmin : MinimalOrder (J W₀).π) (hlt : t ^ 2 < 4 * (Nat.card K : ℤ))
    (P : WeierstrassCurve K → Prop) (hP : ∀ W, P W → W.Δ ≠ 0 ∧ traceOfFrob W = t)
    (Λ : WeierstrassCurve K → TrDet t (Nat.card K))
    (hΛ : ∀ (W : WeierstrassCurve K) (hW : W.Δ ≠ 0), traceOfFrob W = t → P W →
        haveI : W.IsElliptic := ⟨isUnit_iff_ne_zero.mpr hW⟩
        ∃ b : Module.Basis (Fin 2) ℤ (homPi (J W₀).π (J W).π),
          (Λ W).1 = LinearMap.toMatrix b b (piAct (J W₀).π (J W).π))
    (hl : ∀ (W : WeierstrassCurve K) [W.IsElliptic], P W → Link (J W₀).π (J W).π)
    (hG1 : ∀ (W W' : WeierstrassCurve K) [W.IsElliptic] [W'.IsElliptic],
      W' ∈ orbit (VariableChange K) W ↔ Nonempty {e : (J W').A ≅ (J W).A //
        IsMonHom e.hom ∧ e.hom ≫ (J W).π = (J W').π ≫ e.hom})
    (hG1' : ∀ (W : WeierstrassCurve K) [W.IsElliptic],
      Nat.card (stabilizer (VariableChange K) W) =
        Nat.card {e : (J W).A ≅ (J W).A // IsMonHom e.hom ∧ e.hom ≫ (J W).π = (J W).π ≫ e.hom})
    (hsurj : ∀ M : TrDet t (Nat.card K), ∃ W, P W ∧ ∃ g : GL2, g • Λ W = M) :
    Nonempty (DeuringClassLattice K t P) := by
  refine ⟨⟨Λ, ?_, ?_, hsurj⟩⟩
  · intro W W' hW hW'
    obtain ⟨hWΔ, htW⟩ := hP W hW
    obtain ⟨hWΔ', htW'⟩ := hP W' hW'
    haveI : W.IsElliptic := ⟨isUnit_iff_ne_zero.mpr hWΔ⟩
    haveI : W'.IsElliptic := ⟨isUnit_iff_ne_zero.mpr hWΔ'⟩
    obtain ⟨b, hb⟩ := hΛ W hWΔ htW hW
    obtain ⟨b', hb'⟩ := hΛ W' hWΔ' htW' hW'
    exact rel_iff_fam J ht₀ hmin hlt Λ W W' b hb b' hb' (hl W hW) (hl W' hW') (hG1 W W')
  · intro W hW
    obtain ⟨hWΔ, htW⟩ := hP W hW
    haveI : W.IsElliptic := ⟨isUnit_iff_ne_zero.mpr hWΔ⟩
    obtain ⟨b, hb⟩ := hΛ W hWΔ htW hW
    exact card_stab_fam J ht₀ hmin hlt Λ W b hb (hl W hW) (hG1' W)

/-! ### Unconditional per-class count -/

set_option maxHeartbeats 1600000 in
/-- **`DeuringClassLattice` for one class, from a minimal base curve in it (no Tate).** -/
theorem nonempty_classLattice_of_base_uncond (hp : ¬ (ringChar K : ℤ) ∣ t)
    (hlt : t ^ 2 < 4 * (Nat.card K : ℤ)) (C : IsogClass K t) (W₀ : WeierstrassCurve K)
    (hC : IsogClassPred C W₀)
    (hmin : ∀ [W₀.IsElliptic] (S : Jac.JacSite W₀), MinimalOrder S.frobeniusJacobian.π) :
    Nonempty (DeuringClassLattice K t (IsogClassPred C)) := by
  obtain ⟨G⟩ := nonempty_globalSite K
  obtain ⟨hW₀, ht₀⟩ := isogClassPred_spec hC
  haveI : W₀.IsElliptic := ⟨isUnit_iff_ne_zero.mpr hW₀⟩
  obtain ⟨Λ, hΛ⟩ := exists_latticeMatrix_cls G ht₀ hlt hC
  have hmin₀ : MinimalOrder ((G.site W₀).frobeniusJacobian).π := hmin (G.site W₀)
  have hp' : ¬ (ringChar K : ℤ) ∣ traceOfFrob W₀ := by rw [ht₀]; exact hp
  have hlt' : traceOfFrob W₀ ^ 2 < 4 * (Nat.card K : ℤ) := by rw [ht₀]; exact hlt
  have hl : ∀ (W : WeierstrassCurve K) [W.IsElliptic], IsogClassPred C W →
      Link ((G.site W₀).frobeniusJacobian).π ((G.site W).frobeniusJacobian).π := by
    intro W _ hWC
    have htW := (isogClassPred_spec hWC).2
    exact PLink.primeToPLink K W₀ W (G.site W₀) (G.site W) (htW.trans ht₀.symm) hp' hlt'
      (frobHomNe_both_class G hC hWC).1
  have hG1 : ∀ (W W' : WeierstrassCurve K) [W.IsElliptic] [W'.IsElliptic],
      W' ∈ orbit (VariableChange K) W ↔ Nonempty {e : ((G.site W').frobeniusJacobian).A ≅
        ((G.site W).frobeniusJacobian).A // IsMonHom e.hom ∧
          e.hom ≫ ((G.site W).frobeniusJacobian).π = ((G.site W').frobeniusJacobian).π ≫ e.hom} :=
    fun W W' _ _ => mem_orbit_iff_global G W W'
  have hG1' : ∀ (W : WeierstrassCurve K) [W.IsElliptic],
      Nat.card (stabilizer (VariableChange K) W) =
        Nat.card {e : ((G.site W).frobeniusJacobian).A ≅ ((G.site W).frobeniusJacobian).A //
          IsMonHom e.hom ∧
            e.hom ≫ ((G.site W).frobeniusJacobian).π = ((G.site W).frobeniusJacobian).π ≫ e.hom} :=
    fun W _ => card_stabilizer_global G W
  have hsurj : ∀ M : TrDet t (Nat.card K), ∃ W, IsogClassPred C W ∧ ∃ g : GL2, g • Λ W = M :=
    surjClass_of_descent_cls (WModel.weierstrassDescent K) (G.site W₀) ht₀ hp hlt hmin₀ C hC Λ
      (fun W hW htW hWC => ⟨G.site W, hΛ W hW htW hWC⟩)
  exact classLattice_cls (fun W _ => (G.site W).frobeniusJacobian) ht₀ hmin₀ hlt
    (IsogClassPred C) (fun W hW => isogClassPred_spec hW) Λ hΛ hl hG1 hG1' hsurj

/-- **`DeuringClassLattice` for every ordinary class over `K`, unconditionally.** -/
theorem nonempty_classLattice_uncond (hp : ¬ (ringChar K : ℤ) ∣ t)
    (hlt : t ^ 2 < 4 * (Nat.card K : ℤ)) (C : IsogClass K t) :
    Nonempty (DeuringClassLattice K t (IsogClassPred C)) := by
  obtain ⟨W₀, hC, hmin⟩ := MinBase.existsMinimalBase K t hp hlt C
  exact nonempty_classLattice_of_base_uncond hp hlt C W₀ hC hmin

/-- **`DeuringClassLatticeAll`, unconditionally.** -/
theorem deuringClassLatticeAll_uncond (p : ℕ) [Fact p.Prime] : DeuringClassLatticeAll p := by
  intro n hn t hpt hlt
  let _ : Fintype (GaloisField p n) := Fintype.ofFinite _
  intro C
  have hcard : (Nat.card (GaloisField p n) : ℤ) = (p : ℤ) ^ n := by
    rw [GaloisField.card p n (by omega)]; push_cast; rfl
  exact nonempty_classLattice_uncond (by rwa [ringChar_galoisField]) (by rw [hcard]; exact hlt) C

/-- **Headline: the exact per-class count, unconditionally.** For every prime `p`, `n ≥ 1`
and ordinary `t` (`p ∤ t`, `t² < 4pⁿ`):
`#{W : Δ ≠ 0, a_W = t} = pⁿ^3 (pⁿ − 1) · mult p n t · H(4pⁿ − t²) / 2`. -/
theorem deuringMultiplicity_uncond (p : ℕ) [Fact p.Prime] :
    DeuringMultiplicity hurwitz p (mult p) :=
  deuringMultiplicity_of_classLattice p (deuringClassLatticeAll_uncond p)

end RamanujanWeil.Arith.Deuring.Final
