import RamanujanWeil.Arith.DeuringG7Genus2DescentLang
import RamanujanWeil.Arith.DeuringG7PrincipalFinModel
import StacksFrontier.AlgebraicGeometry.Morphisms.DimensionFormula.FunctionField

/-!
# A3-ord, G7 C-descent: `Genus2FrobDescent` from canonical stability and fixed-generator descent

`docs/ARITH_DEURING_G7_G2DESCENT.md`. Setting: `K = 𝔽_q`, `k̄ = K̄`, `X / k̄` a smooth proper
geometrically irreducible genus-2 curve, `Ψ : X ≅ X` over `F = Spec(x ↦ x^q)`.

* **`frobFF s Ψ`**: `Ψ^♯` on `k̄(X)` (`Scheme.Hom.functionFieldMap`).
  **`isFrobSemilinear_frobFF`**: it is `σ`-semilinear, `Ψ^♯ (c) = c^q` (proved from
  `Ψ ≫ s = s ≫ F`, `F = Spec(frob)`).
* **`exists_pres`**: `k̄(X)` has a hyperelliptic presentation `(x, y, h, f)` with
  `k̄(x, y) = k̄(X)` (from the proved `PencilData` of `Genus2.Pencil`, via `exists_relation`;
  generation from `[k̄(X) : k̄(x)] ≤ 2` and `y ∉ k̄(x)`).
* Two named Props:
  * **`Genus2FrobCanonical K`** (canonical stability): for every presentation, `Ψ^♯` acts by a
    model change (`MobForm`). This is "`Ψ` preserves the canonical map `X → ℙ¹` and
    `H⁰(3K_X) = ⟨1, x, x², x³, y⟩`".
  * **`Genus2FixedDescent K`** (descent with fixed generators): if `x, y` are `Ψ^♯`-fixed,
    generate `k̄(X)` and satisfy a relation over `K`, then `X` is the base change of a genus-2
    curve over `K` with `Ψ ↦ id × Spec(frob)`.
* **`genus2FrobDescent_of_canonical_of_fixed`**: the two Props give `Genus2FrobDescent K`. The
  middle step is Lang's theorem for the model group (`exists_descended_model`).
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Polynomial Stacks.Frobenius

universe u

noncomputable section

namespace RamanujanWeil.Arith.Deuring.Geom.G7.Genus2Descent

open RamanujanWeil.Arith.Deuring.Geom RamanujanWeil.Arith.Deuring.Geom.G7
  RamanujanWeil.Arith.Deuring.Geom.G7.PrincipalFin RamanujanWeil.Ihara

attribute [local instance] RamanujanWeil.Ihara.fact_ringChar_prime

variable (K : Type u) [Field K] [Fintype K]

/-! ## The Frobenius on the function field -/

section FunctionField

variable {K}

theorem frob_apply (c : AlgebraicClosure K) :
    (Jac.JacSite.frob (k := K) : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) c =
      c ^ Fintype.card K := by
  rw [card_eq_ringChar_pow]
  simp only [Jac.JacSite.frob, pow_one]
  exact iterateFrobeniusEquiv_def _ _ _ c

theorem frobSpec_eq : frobSpec K = Spec.map (CommRingCat.ofHom
    (Jac.JacSite.frob (k := K) : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K).toAlgHom.toRingHom) :=
  (specMap_eq_absoluteFrobeniusPow _ _ _ _ (fun a => by
    simp only [Jac.JacSite.frob, pow_one]
    exact iterateFrobeniusEquiv_def _ _ _ a)).symm

theorem appLE_top_top {X : Scheme.{u}} (Ψ : X ⟶ X) (h) : Ψ.appLE ⊤ ⊤ h = Ψ.appTop :=
  Ψ.appLE_eq_app (U := ⊤)

/-- On global sections: `Ψ ≫ s = s ≫ Spec φ` gives `Ψ^♯ (s^♯ c) = s^♯ (φ c)`. -/
theorem appLE_appTop_ΓSpecIso {X : Scheme.{u}} {R : CommRingCat.{u}} (s : X ⟶ Spec R)
    (Ψ : X ⟶ X) (φ : R ⟶ R) (hΨ : Ψ ≫ s = s ≫ Spec.map φ) (c : R) :
    Ψ.appLE ⊤ ⊤ le_top (s.appTop ((Scheme.ΓSpecIso R).inv c)) =
      s.appTop ((Scheme.ΓSpecIso R).inv (φ c)) := by
  have h1 := Scheme.ΓSpecIso_inv_naturality φ
  have h3 : (Scheme.ΓSpecIso R).inv (φ c) =
      (Spec.map φ).appTop ((Scheme.ΓSpecIso R).inv c) := by
    have := congrArg (fun g => g c) h1; simpa only [CommRingCat.comp_apply] using this
  have h2 := congrArg Scheme.Hom.appTop hΨ
  rw [Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop] at h2
  have h4 := congrArg (fun g => g ((Scheme.ΓSpecIso R).inv c)) h2
  simp only [CommRingCat.comp_apply] at h4
  rw [h3, ← h4]
  exact congrArg (fun g : Γ(X, ⊤) ⟶ Γ(X, ⊤) =>
    g.hom (s.appTop.hom ((Scheme.ΓSpecIso R).inv.hom c))) (appLE_top_top Ψ le_top)

theorem isIntegral_of_isCurve {X : Scheme.{u}} (s : X ⟶ Spec (.of (AlgebraicClosure K)))
    [IsCurve (AlgebraicClosure K) s] : IsIntegral X :=
  IsCurve.toIsVariety.toIsIntegral (f := s)

/-- **`Ψ^♯` on the function field.** -/
def frobFF {X : Scheme.{u}} (s : X ⟶ Spec (.of (AlgebraicClosure K)))
    [IsCurve (AlgebraicClosure K) s] (Ψ : X ⟶ X) [IsIso Ψ] :
    X.functionField →+* X.functionField :=
  haveI := isIntegral_of_isCurve s
  Ψ.functionFieldMap.hom

/-- **`Ψ^♯` is `σ`-semilinear.** -/
theorem isFrobSemilinear_frobFF {X : Scheme.{u}} (s : X ⟶ Spec (.of (AlgebraicClosure K)))
    [IsCurve (AlgebraicClosure K) s] (Ψ : X ⟶ X) [IsIso Ψ] (hΨ : Ψ ≫ s = s ≫ frobSpec K) :
    letI := functionFieldAlgebra (AlgebraicClosure K) s
    IsFrobSemilinear K (frobFF s Ψ) := by
  letI := functionFieldAlgebra (AlgebraicClosure K) s
  haveI := isIntegral_of_isCurve s
  intro c
  letI : Nonempty (⊤ : X.Opens) := ⟨⟨genericPoint X, trivial⟩⟩
  show Ψ.functionFieldMap.hom ((X.germToFunctionField ⊤).hom
      (s.appTop.hom ((Scheme.ΓSpecIso (.of (AlgebraicClosure K))).inv.hom c))) =
    (X.germToFunctionField ⊤).hom
      (s.appTop.hom ((Scheme.ΓSpecIso (.of (AlgebraicClosure K))).inv.hom (c ^ Fintype.card K)))
  rw [Scheme.Hom.functionFieldMap_germToFunctionField Ψ (U := ⊤) (V := ⊤) le_top]
  congr 1
  rw [frobSpec_eq] at hΨ
  rw [← frob_apply]
  exact appLE_appTop_ΓSpecIso s Ψ _ hΨ c

end FunctionField

/-! ## A presentation of the function field -/

section Presentation

variable {K}
variable {L : Type*} [Field L] [Algebra (AlgebraicClosure K) L]

/-- If `[L : K̄(x)] ≤ 2` and `y ∉ K̄(x)`, then `K̄(x, y) = L`. -/
theorem e₂_eq_top {x y : L} [FiniteDimensional (E K x) L] (hfr : Module.finrank (E K x) L ≤ 2)
    (hy : y ∉ E K x) : E₂ K x y = ⊤ := by
  have hli : LinearIndependent (E K x) ![(1 : L), y] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    simp only [Algebra.smul_def, mul_one, IntermediateField.algebraMap_apply] at hst
    by_cases ht : t = 0
    · subst ht
      simp only [ZeroMemClass.coe_zero, zero_mul, add_zero] at hst
      exact ⟨Subtype.ext hst, rfl⟩
    · exfalso
      apply hy
      have ht' : (t : L) ≠ 0 := fun h => ht (Subtype.ext h)
      have : y = -(s : L) / (t : L) := by
        field_simp; linear_combination hst
      rw [this]
      exact div_mem (neg_mem s.2) t.2
  have hcard : Module.finrank (E K x) L = 2 := by
    refine le_antisymm hfr ?_
    have := hli.fintype_card_le_finrank
    simpa using this
  have hspan := hli.span_eq_top_of_card_eq_finrank (by simp [hcard])
  rw [eq_top_iff]
  intro w _
  have hw : w ∈ Submodule.span (E K x) (Set.range ![(1 : L), y]) := hspan ▸ Submodule.mem_top
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun _).mp hw
  rw [← hc, Fin.sum_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Algebra.smul_def, mul_one,
    IntermediateField.algebraMap_apply]
  have hEx : E K x ≤ E₂ K x y :=
    IntermediateField.adjoin.mono _ _ _ (Set.singleton_subset_iff.mpr (Set.mem_insert _ _))
  have hymem : y ∈ E₂ K x y := IntermediateField.subset_adjoin _ _ (by simp)
  exact add_mem (hEx (c 0).2) (mul_mem (hEx (c 1).2) hymem)

/-- **A hyperelliptic presentation from `PencilData`** (as in `PencilData.exists_model`). -/
theorem exists_pres (D : Genus2.Exist.PencilData (AlgebraicClosure K) L) :
    ∃ (x y : L) (h f : (AlgebraicClosure K)[X]), Pres x y h f ∧ E₂ K x y = ⊤ := by
  have := D.finiteDimensional_three
  have := D.finiteDimensional_six
  have := D.finiteDimensional_adjoin
  obtain ⟨y, hyV, hy⟩ := Genus2.Exist.exists_not_mem_adjoin D.x (D.V 3)
    D.five_le_finrank_three D.pole
  obtain ⟨h, f, hh, hf, hyeq⟩ := Genus2.Exist.exists_relation D.transcendental hy (D.V 6)
    D.finrank_six_le (fun i hi => D.mono_le hi (D.pow_mem i))
    (fun j hj => by
      have := D.mul_mem (D.pow_mem j) hyV
      exact D.mono_le (by omega) this)
    (by rw [pow_two]; exact D.mul_mem hyV hyV)
  exact ⟨D.x, y, h, f, ⟨hyeq, hh, hf, D.transcendental, hy⟩, e₂_eq_top D.finrank_adjoin_le hy⟩

end Presentation

/-! ## The two named Props and the reduction -/

/-- **Canonical stability (named).** For every hyperelliptic presentation `(x, y)` of `k̄(X)`
(`y² + h(x) y = f(x)`, `deg h ≤ 3`, `deg f ≤ 6`, `k̄(x, y) = k̄(X)`), the twisted Frobenius
acts by a model change: `Ψ^♯ x = (a x + b)/(c x + d)`, `Ψ^♯ y = (e y + p(x))/(c x + d)³`.

Mathematically: `[k̄(X) : k̄(x)] = 2`, so the pole divisor `D` of `x` is a `g¹₂`, which on a
genus-2 curve is the canonical class (uniqueness of the `g¹₂`, Riemann–Roch + Serre duality:
`h⁰(D) = 2`, `deg D = 2` ⇒ `D ~ K_X`). `Ψ` is an automorphism of the scheme `X`, so `Ψ^♯ x`
again has degree 2: `k̄(Ψ^♯ x) = k̄(x)`, i.e. `Ψ^♯ x` is a Möbius function of `x`, with pole
divisor `D + div(c x + d)`. `y` is integral over `k̄[x]` and `y/x³` over `k̄[1/x]` (the bounds),
so `y ∈ H⁰(3D) = ⟨1, x, x², x³, y⟩` (`h⁰(3K) = 5`), and `Ψ^♯ H⁰(3D) = H⁰(3 Ψ^*D) =
(c x + d)⁻³ H⁰(3D)`. -/
def Genus2FrobCanonical : Prop :=
  ∀ (X : Scheme.{u}) (s : X ⟶ Spec (.of (AlgebraicClosure K)))
    [IsCurve (AlgebraicClosure K) s] [GeometricallyIrreducible s] [Smooth s] [IsProper s],
    genus s = 2 → ∀ (Ψ : X ⟶ X) [IsIso Ψ], Ψ ≫ s = s ≫ frobSpec K →
      letI := functionFieldAlgebra (AlgebraicClosure K) s
      ∀ (x y : X.functionField) (h f : (AlgebraicClosure K)[X]), Pres x y h f →
        E₂ K x y = ⊤ → MobForm K (frobFF s Ψ) x y

/-- **Descent with fixed generators (named).** If `x, y ∈ k̄(X)` are `Ψ^♯`-fixed, generate
`k̄(X)`, and satisfy `y² + h₀(x) y = f₀(x)` with `h₀, f₀ ∈ K[X]`, then `X` is the base change
of a genus-2 curve `C / K`, with `Ψ` corresponding to `id × Spec(frob)`.

Mathematically: `F₀ = K(x)[y]/(y² + h₀ y − f₀)` is a function field of transcendence degree 1
over `K`; `C` is its regular projective model (Tag 0BY1, essential surjectivity), smooth since
`K` is perfect. `k̄ ⊗_K F₀ = k̄(x, y) = k̄(X)` (`{1, y}` is a basis over `k̄(x)` and over `K(x)`),
so `C_k̄` and `X` are regular projective curves over `k̄` with the same function field and
`β : X ≅ C_k̄` exists (Tag 0BY1, uniqueness), matching `x, y`; then genus and geometric
irreducibility transfer along `β` and flat base change. `β ≫ (id × Spec frob)` and `Ψ ≫ β` lie
over the same map `F` and induce the same map on function fields (both are `σ` on `k̄` and fix
`x, y`), so they agree on the generic point, hence everywhere (`X` reduced, `C_k̄` separated). -/
def Genus2FixedDescent : Prop :=
  ∀ (X : Scheme.{u}) (s : X ⟶ Spec (.of (AlgebraicClosure K)))
    [IsCurve (AlgebraicClosure K) s] [GeometricallyIrreducible s] [Smooth s] [IsProper s],
    genus s = 2 → ∀ (Ψ : X ⟶ X) [IsIso Ψ], Ψ ≫ s = s ≫ frobSpec K →
      letI := functionFieldAlgebra (AlgebraicClosure K) s
      ∀ (x y : X.functionField) (h₀ f₀ : K[X]),
        Pres x y (h₀.map (algebraMap K (AlgebraicClosure K)))
          (f₀.map (algebraMap K (AlgebraicClosure K))) →
        E₂ K x y = ⊤ → frobFF s Ψ x = x → frobFF s Ψ y = y →
        ∃ C : Genus2Curve K, ∃ β : X ≅ fieldBaseChange (Over.mk C.t) (AlgebraicClosure K),
          β.hom ≫ pullback.snd C.t (specAlgebraMap K (AlgebraicClosure K)) = s ∧
          β.hom ≫ galoisBaseChange (Over.mk C.t) (AlgebraicClosure K)
            (Jac.JacSite.frob (k := K)) = Ψ ≫ β.hom

/-- **C-descent from canonical stability and fixed-generator descent.** The proved middle
step: a presentation exists (`Genus2.Pencil`), `Ψ^♯` is `σ`-semilinear, and Lang's theorem
for the model group (`exists_descended_model`) gives `Ψ^♯`-fixed generators with a model over
`K`. -/
theorem genus2FrobDescent_of_canonical_of_fixed (hC : Genus2FrobCanonical K)
    (hF : Genus2FixedDescent K) : Genus2FrobDescent K := by
  intro X s _ _ _ _ hg Ψ _ hΨ
  letI := functionFieldAlgebra (AlgebraicClosure K) s
  obtain ⟨D⟩ := Genus2.Exist.genus2PencilExistence_of_canonical_of_pencil
    Genus2.Exist.genus2CanonicalExistence Genus2.Pencil.genus2PencilFunctionField X s hg
  obtain ⟨x, y, h, f, hP, hE⟩ := exists_pres D
  have hτ := isFrobSemilinear_frobFF s Ψ hΨ
  obtain ⟨x', y', h₀, f₀, hP', hE', hx', hy', -, -⟩ :=
    exists_descended_model hτ hP (hC X s hg Ψ hΨ x y h f hP hE)
  exact hF X s hg Ψ hΨ x' y' h₀ f₀ hP' (hE'.trans hE) hx' hy'

end RamanujanWeil.Arith.Deuring.Geom.G7.Genus2Descent
