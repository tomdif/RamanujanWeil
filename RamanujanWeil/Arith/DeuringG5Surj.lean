import RamanujanWeil.Arith.DeuringG5Alg
import RamanujanWeil.Arith.DeuringG5Kernel
import RamanujanWeil.Arith.DeuringG8Frob

/-!
# A3-ord, G5: `surj_class` from Weierstrass descent

`docs/ARITH_DEURING_G5.md`. For a base curve `E₀` with `End_π(E₀) = ℤ[π]` and cyclic torsion,
every `GL₂(ℤ)`-class of `TrDet t q` is the Frobenius matrix of `L(E) = Hom_π(E₀, E)` for a curve
`E` in the isogeny class of `E₀`, given the named geometric input `WeierstrassDescent`.

General `k` (algebraically closed), `A₀` one-dimensional with endomorphism `π₀`:

* `lin π₀ a b = a + bπ₀` as a homomorphism; `MinimalOrder π₀` (`End_π(A₀) = ℤ[π₀]`),
  `CyclicTorsion π₀ n` (`A₀(k)[n]` is free of rank one over `ℤ[π₀]/n`).
* `gammaOf P L'`: the subgroup `{P ≫ β : β ∈ L'}` for `L' ⊆ End_π(A₀)`.
* **`kernelLattice_iff`**: for the `π`-stable sublattice `L' = span(columns of X)` with
  `det X = n`, `β(A₀[n]) ⊆ Γ ⇔ β ∈ L'`.
* **`realize`**: for `M ∈ M2` and an intertwiner `X` (`M₁ X = X M`, `M₁` the matrix of `π₀` on
  `End_π(A₀)`, `det X` invertible in `k`), there is a finite `π₀`-stable `Γ ⊆ A₀(k)` killed by
  `det X` such that for *every* `(B', π')` equivariantly isomorphic to the quotient
  `(A₀/Γ, π_Γ)`, the matrix of Frobenius on any basis of `Hom_π(A₀, B')` is conjugate to `M`.

Finite fields:

* **`WeierstrassDescent K`** (named): an `𝔽_q`-rational quotient of a concrete Jacobian by a
  finite `π`-stable subgroup of order prime to `p` is the concrete Jacobian of a Weierstrass
  curve over `𝔽_q`, for every Jacobian site.
* **`surjClass_of_descent`**: `WeierstrassDescent` + `MinimalOrder` + `CyclicTorsion` for the base
  curve `W₀ ∈ C` ⇒ the `surj_class` field of `DeuringClassLattice K t (IsogClassPred C)` for any
  `Λ` with the G8 specification (`exists_latticeMatrix`).
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.MonObj

universe u

namespace RamanujanWeil.Arith.Deuring.G5

open RamanujanWeil.Arith.Deuring.Geom RamanujanWeil.Arith.Deuring.Geom.G7
  RamanujanWeil.Arith.Deuring.Dual2 RamanujanWeil.Arith.Deuring.G8 Stacks.Groupoids

section General

variable {k : Type u} [Field k] [IsAlgClosed k]
  {A₀ : Over (Spec (.of k))} [GrpObj A₀] [AlgebraicGeometry.IsAbelianVariety k A₀]
  (π₀ : A₀ ⟶ A₀) [IsMonHom π₀]

/-- `a + bπ₀` as a homomorphism. -/
noncomputable def lin (a b : ℤ) : A₀ ⟶ A₀ := (𝟙 A₀) ^ a * π₀ ^ b

instance isMonHom_lin (a b : ℤ) : IsMonHom (lin π₀ a b) := isMonHom_mul _ _

theorem lin_comp {A : Over (Spec (.of k))} [GrpObj A] [AlgebraicGeometry.IsAbelianVariety k A]
    (π : A ⟶ A) (a b : ℤ) (w : A₀ ⟶ A) [IsMonHom w] (hw : w ≫ π = π₀ ≫ w) :
    lin π₀ a b ≫ w = w ^ a * (w ≫ π) ^ b := by
  rw [lin, MonObj.mul_comp, GrpObj.zpow_comp, GrpObj.zpow_comp, Category.id_comp, ← hw]

theorem lin_comm (a b : ℤ) : lin π₀ a b ≫ π₀ = π₀ ≫ lin π₀ a b := by
  rw [lin_comp π₀ π₀ a b π₀ rfl, lin, MonObj.comp_mul, GrpObj.comp_zpow, GrpObj.comp_zpow,
    Category.comp_id]

theorem lin_mul (n a b : ℤ) : lin π₀ (n * a) (n * b) = (lin π₀ a b) ^ n := by
  rw [lin, lin, mul_zpow, ← zpow_mul, ← zpow_mul, mul_comm a n, mul_comm b n]

/-- **`End_π(A₀) = ℤ[π₀]`** (the base curve has the minimal order). -/
def MinimalOrder : Prop :=
  ∀ e : A₀ ⟶ A₀, IsMonHom e → e ≫ π₀ = π₀ ≫ e → ∃ a b : ℤ, e = lin π₀ a b

/-- **Cyclic torsion**: `A₀(k)[n]` is free of rank one over `ℤ[π₀]/n`, with generator `P`. -/
def CyclicTorsion (n : ℤ) : Prop :=
  ∃ P : Pt A₀, P ^ n = 1 ∧ (∀ x : Pt A₀, x ^ n = 1 → ∃ a b : ℤ, x = P ≫ lin π₀ a b) ∧
    ∀ a b : ℤ, P ≫ lin π₀ a b = 1 → n ∣ a ∧ n ∣ b

/-- The subgroup `{P ≫ β : β ∈ L'}`. -/
def gammaOf (P : Pt A₀) (L' : Submodule ℤ (homPi π₀ π₀)) : Subgroup (Pt A₀) where
  carrier := {x | ∃ β ∈ L', x = P ≫ hm (β : homAV A₀ A₀)}
  one_mem' := ⟨0, L'.zero_mem, by rw [hm_zero, MonObj.comp_one]⟩
  mul_mem' := by
    rintro _ _ ⟨β, hβ, rfl⟩ ⟨β', hβ', rfl⟩
    exact ⟨β + β', L'.add_mem hβ hβ', by rw [hm_add, MonObj.comp_mul]⟩
  inv_mem' := by
    rintro _ ⟨β, hβ, rfl⟩
    refine ⟨(-1 : ℤ) • β, zsmul_mem hβ _, ?_⟩
    rw [hm_zsmul, GrpObj.comp_zpow, zpow_neg_one]

theorem hm_lin_add (a b : ℤ) (β : homPi π₀ π₀) :
    hm ((a • β + b • piAct π₀ π₀ β : homPi π₀ π₀) : homAV A₀ A₀) =
      hm (β : homAV A₀ A₀) ^ a * (hm (β : homAV A₀ A₀) ≫ π₀) ^ b := by
  rw [hm_add, hm_zsmul, hm_zsmul, hm_piAct]

variable {π₀}

theorem zpow_comp_pt {X : Over (Spec (.of k))} [GrpObj X] (P : Pt A₀) (n : ℤ) (f : A₀ ⟶ X)
    [IsMonHom f] (hP : P ^ n = 1) : (P ≫ f) ^ n = 1 := by
  rw [← GrpObj.zpow_comp, hP, MonObj.one_comp]

/-- **The kernel lattice of `gammaOf P L'` is `L'`.** -/
theorem kernelLattice_iff (hmin : MinimalOrder π₀) (n : ℤ) (P : Pt A₀) (hP : P ^ n = 1)
    (hgen : ∀ x : Pt A₀, x ^ n = 1 → ∃ a b : ℤ, x = P ≫ lin π₀ a b)
    (hann : ∀ a b : ℤ, P ≫ lin π₀ a b = 1 → n ∣ a ∧ n ∣ b)
    (L' : Submodule ℤ (homPi π₀ π₀)) (hst : ∀ β ∈ L', piAct π₀ π₀ β ∈ L')
    (hnL : ∀ δ : homPi π₀ π₀, n • δ ∈ L') (β : homPi π₀ π₀) :
    (∀ x : Pt A₀, x ^ n = 1 → x ≫ hm (β : homAV A₀ A₀) ∈ gammaOf π₀ P L') ↔ β ∈ L' := by
  constructor
  · intro h
    obtain ⟨β', hβ', heq⟩ := h P hP
    set δ := β - β' with hδ
    have hδc : hm (δ : homAV A₀ A₀) ≫ π₀ = π₀ ≫ hm (δ : homAV A₀ A₀) := δ.2
    obtain ⟨a, b, hab⟩ := hmin _ inferInstance hδc
    have hP1 : P ≫ lin π₀ a b = 1 := by
      rw [← hab, hδ, sub_eq_add_neg, hm_add, ← neg_one_zsmul, hm_zsmul, MonObj.comp_mul,
        GrpObj.comp_zpow, zpow_neg_one, heq, mul_inv_cancel]
    obtain ⟨⟨a', rfl⟩, ⟨b', rfl⟩⟩ := hann a b hP1
    have hδ' : δ = n • homPi.mk (lin π₀ a' b') (lin_comm π₀ a' b') := by
      apply homPi.ext
      rw [hab, hm_zsmul, lin_mul]
      rfl
    have : β = β' + δ := by rw [hδ]; abel
    rw [this, hδ']
    exact L'.add_mem hβ' (hnL _)
  · intro hβ x hx
    obtain ⟨a, b, rfl⟩ := hgen x hx
    have hc : hm (β : homAV A₀ A₀) ≫ π₀ = π₀ ≫ hm (β : homAV A₀ A₀) := β.2
    refine ⟨a • β + b • piAct π₀ π₀ β, L'.add_mem (zsmul_mem hβ a) (zsmul_mem (hst β hβ) b), ?_⟩
    rw [Category.assoc, lin_comp π₀ π₀ a b _ hc, hm_lin_add]

/-- **Realization.** -/
theorem realize (hA₀ : abelianVarietyDimension A₀ = 1) (b₁ : Module.Basis (Fin 2) ℤ (homPi π₀ π₀))
    (M M₁ X : M2) (hM₁ : LinearMap.toMatrix b₁ b₁ (piAct π₀ π₀) = M₁) (hX : M₁ * X = X * M)
    (hn : IsUnit (X.det : k)) (hmin : MinimalOrder π₀) (hcyc : CyclicTorsion π₀ X.det) :
    ∃ Γ : Subgroup (Pt A₀), Finite Γ ∧ (∀ x ∈ Γ, x ≫ π₀ ∈ Γ) ∧ (∀ h ∈ Γ, h ^ X.det = 1) ∧
      ∀ (G : Glue Γ) (πB : G.B ⟶ G.B) [IsMonHom πB], G.q ≫ πB = π₀ ≫ G.q →
      ∀ (B' : Over (Spec (.of k))) [GrpObj B'] [AlgebraicGeometry.IsAbelianVariety k B']
        (π' : B' ⟶ B') [IsMonHom π'] (e : B' ≅ G.B), IsMonHom e.hom →
        e.hom ≫ πB = π' ≫ e.hom →
        ∀ b : Module.Basis (Fin 2) ℤ (homPi π₀ π'),
          ∃ g : GL2, (g : M2) * LinearMap.toMatrix b b (piAct π₀ π') * (↑g⁻¹ : M2) = M := by
  classical
  set n := X.det with hndef
  have hn0 : n ≠ 0 := by rintro h; rw [h] at hn; simp at hn
  obtain ⟨P, hP, hgen, hann⟩ := hcyc
  set L' := Submodule.span ℤ (Set.range (colVec b₁ X))
  have hst : ∀ β ∈ L', piAct π₀ π₀ β ∈ L' := by
    have hle : L' ≤ L'.comap (piAct π₀ π₀) := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨j, rfl⟩
      show piAct π₀ π₀ (colVec b₁ X j) ∈ L'
      rw [map_colVec b₁ _ M₁ M X hM₁ hX, Fintype.linearCombination_apply]
      exact Submodule.sum_mem _ fun l _ =>
        Submodule.smul_mem _ _ (Submodule.subset_span ⟨l, rfl⟩)
    exact fun β hβ => hle hβ
  have hnL : ∀ δ : homPi π₀ π₀, n • δ ∈ L' := by
    intro δ
    have := det_smul_mem_span_colVec b₁ X δ
    have h2 : LinearMap.lsmul ℤ (homPi π₀ π₀) n δ = n • δ := by
      rw [LinearMap.lsmul_apply]
    rwa [h2] at this
  have key := kernelLattice_iff hmin n P hP hgen hann L' hst hnL
  set Γ := gammaOf π₀ P L'
  -- finiteness: `Γ ⊆ A₀[n]`
  have hkill : ∀ h ∈ Γ, h ^ n = 1 := by
    rintro _ ⟨β, -, rfl⟩
    exact zpow_comp_pt P n _ hP
  have hfinK : (pointKer ((𝟙 A₀ : A₀ ⟶ A₀) ^ n)).Finite := by
    by_contra h
    exact zpow_id_ne_one hA₀ n hn0 (eq_one_of_infinite_pointKer hA₀ _ h)
  have hfin : Finite Γ := by
    refine Set.Finite.to_subtype (hfinK.subset fun h hh => ?_)
    show h ≫ (𝟙 A₀) ^ n = 1
    rw [comp_zpow_id]; exact hkill h hh
  have hπΓ : ∀ x ∈ Γ, x ≫ π₀ ∈ Γ := by
    rintro _ ⟨β, hβ, rfl⟩
    exact ⟨piAct π₀ π₀ β, hst β hβ, by rw [hm_piAct, Category.assoc]⟩
  refine ⟨Γ, hfin, hπΓ, hkill, ?_⟩
  intro G πB _ hqπ B' _ _ π' _ e he hcomm b
  haveI := he
  have hπB : πB = GlueS.πB G π₀ hπΓ := GlueS.eq_πB G π₀ hπΓ πB hqπ
  subst hπB
  set s := GlueS.sMap G n hkill
  -- the comparison map `Φ = (· ≫ e ≫ s)`
  have hφc : (e.hom ≫ s) ≫ π₀ = π' ≫ (e.hom ≫ s) := by
    rw [Category.assoc, GlueS.sMap_π G n hkill π₀ hπΓ, ← Category.assoc, hcomm,
      Category.assoc]
  let φ : homPi π' π₀ := homPi.mk (e.hom ≫ s) hφc
  let Φ := postHom (π₀ := π₀) φ
  have hΦ : ∀ v, hm ((Φ v : homPi π₀ π₀) : homAV A₀ A₀) =
      (hm (v : homAV A₀ B') ≫ e.hom) ≫ s := fun v => by
    simp only [Φ]; rw [hm_postHom, Category.assoc]; rfl
  have hinj : Function.Injective Φ := by
    intro v w hvw
    apply homPi.ext
    have h1 := congrArg (fun z : homPi π₀ π₀ => hm (z : homAV A₀ A₀)) hvw
    simp only [hΦ] at h1
    have h2 := GlueS.comp_sMap_injective G n hkill hA₀ hn0 _ _ h1
    exact (cancel_mono e.hom).1 h2
  have hrange' : ∀ v, Φ v ∈ L' := fun v =>
    (key (Φ v)).1 fun x hx => by
      rw [hΦ]
      exact GlueS.comp_sMap_mem G n hkill (hm (v : homAV A₀ B') ≫ e.hom) x hx
  have hinvc : GlueS.πB G π₀ hπΓ ≫ e.inv = e.inv ≫ π' := by
    rw [Iso.eq_inv_comp, ← Category.assoc, hcomm, Category.assoc, Iso.hom_inv_id,
      Category.comp_id]
  have hrange : ∀ w, w ∈ L' → ∃ v, Φ v = w := by
    intro w hw
    have hwc : hm (w : homAV A₀ A₀) ≫ π₀ = π₀ ≫ hm (w : homAV A₀ A₀) := w.2
    obtain ⟨g, hg, hgs⟩ := GlueS.exists_comp_sMap_eq G n hkill hA₀ hn _ ((key w).2 hw)
    haveI := hg
    have hgc : g ≫ GlueS.πB G π₀ hπΓ = π₀ ≫ g :=
      (GlueS.comm_iff_comp_sMap G n hkill hA₀ hn0 π₀ hπΓ π₀ g).2 (by rw [hgs]; exact hwc)
    refine ⟨homPi.mk (g ≫ e.inv) (by
      rw [Category.assoc, ← hinvc, ← Category.assoc, hgc, Category.assoc]), ?_⟩
    apply homPi.ext
    rw [hΦ]
    change ((g ≫ e.inv) ≫ e.hom) ≫ s = _
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    exact hgs
  obtain ⟨fam, hfam⟩ := isFrobFamily_of_injective b₁ (piAct π₀ π₀) M₁ M X hM₁ hX hn0
    (piAct π₀ π') Φ hinj (fun v => postHom_piAct φ v) hrange hrange'
  exact conj_of_isFrobFamily hfam b

end General

/-! ### Finite fields: the named descent input and `surj_class` -/

section Finite

open RamanujanWeil.Ihara RamanujanWeil.Arith.Deuring.Mult

variable {K : Type u} [Field K] [Fintype K]

variable (K) in
/-- **Weierstrass descent (named hypothesis, G5).** Let `W₀/𝔽_q` be elliptic with concrete
Jacobian `(J₀, π₀)` (any site), `Γ ⊆ J₀(K̄)` a finite `π₀`-stable subgroup killed by an `n`
prime to `p`, and `(B, π_B)` the G6 quotient with the descended Frobenius. Then `(B, π_B)` is
the concrete Jacobian of an elliptic Weierstrass curve `W` over `𝔽_q` (of the same trace), for
**every** Jacobian site of `W`.

Mathematically: `Γ` is `Gal(K̄/𝔽_q)`-stable, so `B` has an `𝔽_q`-form `E₀/Γ` whose Frobenius
is `π_B`; a Weierstrass model of the elliptic curve `E₀/Γ` over `𝔽_q` (Riemann–Roch on `|3O|`,
or Galois descent of a `K̄`-model via Lang's theorem for the coordinate-change group) gives
`W`, and G1 (`PairSite.frobIsoEquiv`, `JacSite.ajIso`) identifies `(J_W, π_W)` with
`(B, π_B)`. See `docs/ARITH_DEURING_G5.md` §4. -/
def WeierstrassDescent : Prop :=
  ∀ (W₀ : WeierstrassCurve K) [W₀.IsElliptic] (S₀ : Jac.JacSite W₀)
    (Γ : Subgroup (Pt S₀.frobeniusJacobian.A)), Finite Γ →
    (∀ x ∈ Γ, x ≫ S₀.frobeniusJacobian.π ∈ Γ) → ∀ n : ℤ, IsUnit (n : AlgebraicClosure K) →
    (∀ h ∈ Γ, h ^ n = 1) → ∀ (G : Glue Γ) (πB : G.B ⟶ G.B), IsMonHom πB →
    G.q ≫ πB = S₀.frobeniusJacobian.π ≫ G.q →
    ∃ (W : WeierstrassCurve K) (hW : W.Δ ≠ 0),
      haveI : W.IsElliptic := ⟨isUnit_iff_ne_zero.mpr hW⟩
      traceOfFrob W = traceOfFrob W₀ ∧
      ∀ S : Jac.JacSite W, ∃ e : S.frobeniusJacobian.A ≅ G.B, IsMonHom e.hom ∧
        e.hom ≫ πB = S.frobeniusJacobian.π ≫ e.hom

-- The final `hreal' b` unifies two `homPi` types over concrete Jacobians; the check unfolds
-- `JacSite.frobeniusJacobian` and needs more than the default budget.
set_option maxHeartbeats 800000 in
/-- **`surj_class` (G5) from Weierstrass descent.** For a base curve `W₀` of the class `C` with
`End_π(J₀) = ℤ[π]` and cyclic torsion, and any `Λ` with the G8 specification (`Λ W` is the
matrix of Frobenius on a basis of `Hom_π(J_{W₀}, J_W)` for some site), every
`M ∈ TrDet t q` is `GL₂(ℤ)`-conjugate to `Λ W` for some `W` in `C`. -/
theorem surjClass_of_descent (hD : WeierstrassDescent K) {W₀ : WeierstrassCurve K}
    [W₀.IsElliptic] (S₀ : Jac.JacSite W₀) {t : ℤ} (ht₀ : traceOfFrob W₀ = t)
    (hp : ¬ (ringChar K : ℤ) ∣ t) (hlt : t ^ 2 < 4 * (Nat.card K : ℤ))
    (hmin : MinimalOrder S₀.frobeniusJacobian.π)
    (hcyc : ∀ n : ℤ, IsUnit (n : AlgebraicClosure K) → CyclicTorsion S₀.frobeniusJacobian.π n)
    (C : IsogClass K t) (hC : IsogClassPred C W₀)
    (Λ : WeierstrassCurve K → TrDet t (Nat.card K))
    (hΛ : ∀ (W : WeierstrassCurve K) (hW : W.Δ ≠ 0), traceOfFrob W = t →
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
  obtain ⟨b₁, htr₁, hdet₁⟩ := exists_basis_trDet hA₀ hA₀ J₀.π J₀.π (traceOfFrob W₀)
    (Nat.card K) hχ₀ hχ₀ hdisc (𝟙 J₀.A) (id_ne_one hA₀) (by simp) (𝟙 J₀.A) (id_ne_one hA₀)
    (by simp)
  set M₁ := LinearMap.toMatrix b₁ b₁ (piAct J₀.π J₀.π)
  -- the characteristic
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
  refine ⟨W, ?_, ?_⟩
  · -- `W` lies in the class `C`
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
  · obtain ⟨S, b, hb⟩ := hΛ W hΔ htW
    obtain ⟨e, he, hcomm⟩ := hS S
    have hreal' := hreal G (GlueS.πB G J₀.π hπΓ) (GlueS.q_πB G J₀.π hπΓ)
      S.frobeniusJacobian.A S.frobeniusJacobian.π e he hcomm
    obtain ⟨g, hg⟩ := hreal' b
    exact ⟨g, Subtype.ext (by rw [smul_val, hb]; exact hg)⟩

end Finite

end RamanujanWeil.Arith.Deuring.G5
