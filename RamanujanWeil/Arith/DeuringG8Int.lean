import RamanujanWeil.Arith.DeuringG5Cyclic

/-!
# A3-ord, G8(ii): integral surjectivity `Hom_π(A, A') ≅ Hom_{ℤ[π]}(L A, L A')`

`docs/ARITH_DEURING_CLASSLATTICE.md` §1. Setting: `k` algebraically closed, `A₀`, `A`, `A'`
one-dimensional abelian varieties with endomorphisms `π₀`, `π`, `π'`, and `L A = Hom_π(A₀, A)`
(`G8.homPi`). `G8.postHom φ : L A → L A'` is `γ ↦ γ ≫ φ`.

**`exists_postHom_eq`.** Suppose

* `End_π(A₀) = ℤ[π₀]` (`G5.MinimalOrder`), `ℤ[π₀] ↪ End(A₀)`, and `π₀² − tπ₀ + q = 0`,
  `t² < 4q`;
* there are equivariant `α : A₀ ⟶ A`, `β : A ⟶ A₀` with `α ≫ β = [n]` and **`n` invertible in
  `k`** (a link of degree prime to `p`).

Then every `ℤ[π]`-linear `f : L A → L A'` is `postHom φ` for an equivariant `φ : A ⟶ A'`.

Proof. G8 (`exists_postHom_eq_smul`) gives `φ₁` with `postHom φ₁ = n • f`. It remains to divide
`φ₁` by `n`, i.e. (G3-div, `exists_isMonHom_zpow_comp_eq`) to show that `φ₁` kills `A(k)[n]`.
Let `x ∈ A(k)[n]`, `x = n·z`. Then `w = β(z) ∈ A₀[n²]`, and by cyclic torsion (G5,
`cyclicTorsion_of_minimalOrder`) `w = (a + bπ₀)P` for a generator `P` of `A₀[n²]`. With
`γ = α ∘ (a + bπ₀) ∈ L A`, `x = γ(P)`. Since `n·x = 0`, `γ` kills `nP`, which generates
`A₀[n]`; so `γ = n·γ'` (G3-div again, `γ'` equivariant by cancelling `[n]`). Then
`φ₁(x) = (γ ≫ φ₁)(P) = (n² f(γ'))(P) = f(γ')(n²P) = 0`.

The `p`-part enters only through the hypothesis that `n` is invertible.

Consequences (`postHom_comp`, `postHom_id`): `postHom` is functorial, so equivariant isomorphisms
`A ≅ A'` correspond to `ℤ[π]`-linear isomorphisms `L A ≃ L A'` (`nonempty_iso_iff`), and
`Aut_π(A) ≃ Aut_{ℤ[π]}(L A)` (`autEquiv`).
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.MonObj

set_option linter.unusedSectionVars false

universe u

namespace RamanujanWeil.Arith.Deuring.G8Int

open RamanujanWeil.Arith.Deuring.Geom RamanujanWeil.Arith.Deuring.Geom.G7
  RamanujanWeil.Arith.Deuring.Dual2 RamanujanWeil.Arith.Deuring.G8
  RamanujanWeil.Arith.Deuring.G5 Stacks.Groupoids

section Int

variable {k : Type u} [Field k] [IsAlgClosed k] {A₀ A A' : Over (Spec (.of k))} [GrpObj A₀]
  [GrpObj A] [GrpObj A'] [AlgebraicGeometry.IsAbelianVariety k A₀]
  [AlgebraicGeometry.IsAbelianVariety k A] [AlgebraicGeometry.IsAbelianVariety k A']
  {π₀ : A₀ ⟶ A₀} {π : A ⟶ A} {π' : A' ⟶ A'} [IsMonHom π₀] [IsMonHom π] [IsMonHom π']

/-- `Hom_π(A₀, A)` is torsion free. -/
theorem homPi_eq_of_smul_eq (hA₀ : abelianVarietyDimension A₀ = 1) {n : ℤ} (hn : n ≠ 0)
    {x y : homPi π₀ π} (h : n • x = n • y) : x = y := by
  rw [← sub_eq_zero]
  apply homPi.ext
  have h1 : n • (x - y) = 0 := by rw [smul_sub, h, sub_self]
  have h2 := congrArg (fun w : homPi π₀ π => hm (w : homAV A₀ A)) h1
  change hm ((x - y : homPi π₀ π) : homAV A₀ A) ^ n = 1 at h2
  exact eq_one_of_zpow_eq_one hA₀ _ n hn h2

/-- **Divisibility in `Hom_π`.** An equivariant `γ : A₀ ⟶ A` killing `A₀(k)[n]`, `n` invertible
in `k`, is `n • gb` with `gb` equivariant. -/
theorem exists_homPi_smul_eq (hA₀ : abelianVarietyDimension A₀ = 1) (n : ℤ)
    (hn : IsUnit (n : k)) (ga : homPi π₀ π)
    (h : ∀ x : Pt A₀, x ^ n = 1 → x ≫ hm (ga : homAV A₀ A) = 1) :
    ∃ gb : homPi π₀ π, n • gb = ga := by
  have hn0 : n ≠ 0 := by rintro rfl; simp at hn
  obtain ⟨g, hg, hfac⟩ := exists_isMonHom_zpow_comp_eq n hn _ h
  have hga : hm (ga : homAV A₀ A) ≫ π = π₀ ≫ hm (ga : homAV A₀ A) := ga.2
  have hgπ : g ≫ π = π₀ ≫ g := by
    apply cancel_of_ne_one hA₀ hA₀ ((𝟙 A₀) ^ n) (zpow_id_ne_one hA₀ n hn0)
    rw [← Category.assoc, hfac, hga, ← hfac, ← Category.assoc, ← zpow_id_comp_comm,
      Category.assoc]
  refine ⟨homPi.mk g hgπ, homPi.ext ?_⟩
  rw [hm_zsmul]
  change g ^ n = _
  rw [← hfac, GrpObj.zpow_comp, Category.id_comp]

/-- **G8(ii), integral surjectivity.** With `End_π(A₀) = ℤ[π₀]` and a link `α ≫ β = [n]`,
`n` invertible in `k`, every `ℤ[π]`-linear `f : L A → L A'` is `postHom φ`. -/
theorem exists_postHom_eq (hA₀ : abelianVarietyDimension A₀ = 1)
    (hA : abelianVarietyDimension A = 1) (hmin : MinimalOrder π₀)
    (hind : ∀ a b : ℤ, lin π₀ a b = 1 → a = 0 ∧ b = 0) (t q : ℤ)
    (hπ₀ : endPolyEval π₀ (Polynomial.X ^ 2 - Polynomial.C t * Polynomial.X +
      Polynomial.C q) = 1) (hdisc : t ^ 2 < 4 * q)
    (α : A₀ ⟶ A) [IsMonHom α] (hα : α ≠ 1) (hαπ : α ≫ π = π₀ ≫ α)
    (β : A ⟶ A₀) [IsMonHom β] (n : ℤ) (hn : IsUnit (n : k)) (hαβ : α ≫ β = (𝟙 A₀) ^ n)
    (hβπ : β ≫ π₀ = π ≫ β) (f : homPi π₀ π →ₗ[ℤ] homPi π₀ π')
    (hf : ∀ x, f (piAct π₀ π x) = piAct π₀ π' (f x)) :
    ∃ φ : homPi π π', postHom φ = f := by
  have hn0 : n ≠ 0 := by rintro rfl; simp at hn
  obtain ⟨φ₁, hφ₁⟩ := exists_postHom_eq_smul hA₀ hA t q hπ₀ hdisc α hα hαπ β n hn0 hαβ hβπ f hf
  have hβα : β ≫ α = (𝟙 A) ^ n := comp_eq_zpow_symm hA₀ hA α hα β n hαβ
  have hnn : IsUnit ((n * n : ℤ) : k) := by push_cast; exact hn.mul hn
  obtain ⟨P, hP1, hgen, hann⟩ := cyclicTorsion_of_minimalOrder hA₀ hmin hind (n * n) hnn
  -- `φ₁` kills `A(k)[n]`
  have hkill : ∀ x : Pt A, x ^ n = 1 → x ≫ hm (φ₁ : homAV A A') = 1 := by
    intro x hx
    obtain ⟨z, hz⟩ := exists_zpow_eq_point n hn0 x
    have hw : (z ≫ β) ^ (n * n) = 1 := by
      rw [← GrpObj.zpow_comp, zpow_mul, hz, hx, MonObj.one_comp]
    obtain ⟨a, b, hab⟩ := hgen _ hw
    let ga : homPi π₀ π := homPi.mk (lin π₀ a b ≫ α) (by
      rw [Category.assoc, hαπ, ← Category.assoc, lin_comm, Category.assoc])
    have hga : hm (ga : homAV A₀ A) = lin π₀ a b ≫ α := rfl
    have hgaπ : hm (ga : homAV A₀ A) ≫ π = π₀ ≫ hm (ga : homAV A₀ A) := ga.2
    have hxga : x = P ≫ hm (ga : homAV A₀ A) := by
      rw [hga, ← Category.assoc, ← hab, Category.assoc, hβα, comp_zpow_id, hz]
    have hPn : (P ^ n) ≫ hm (ga : homAV A₀ A) = 1 := by
      rw [GrpObj.zpow_comp, ← hxga, hx]
    -- `ga` kills `A₀(k)[n]`
    have hgakill : ∀ y : Pt A₀, y ^ n = 1 → y ≫ hm (ga : homAV A₀ A) = 1 := by
      intro y hy
      have hy2 : y ^ (n * n) = 1 := by rw [zpow_mul, hy, one_zpow]
      obtain ⟨c, d, hcd⟩ := hgen y hy2
      have h1 : P ≫ lin π₀ (n * c) (n * d) = 1 := by
        rw [lin_mul, GrpObj.comp_zpow, ← hcd, hy]
      obtain ⟨⟨c', hc'⟩, ⟨d', hd'⟩⟩ := hann _ _ h1
      have hc : c = n * c' := mul_left_cancel₀ hn0 (by rw [hc', mul_assoc])
      have hd : d = n * d' := mul_left_cancel₀ hn0 (by rw [hd', mul_assoc])
      rw [hcd, hc, hd, lin_mul, GrpObj.comp_zpow, ← GrpObj.zpow_comp, Category.assoc,
        lin_comp π₀ π c' d' _ hgaπ, MonObj.comp_mul, GrpObj.comp_zpow, GrpObj.comp_zpow,
        ← Category.assoc, hPn, MonObj.one_comp, one_zpow, one_zpow, mul_one]
    obtain ⟨gb, hgb⟩ := exists_homPi_smul_eq hA₀ n hn ga hgakill
    have key : hm (ga : homAV A₀ A) ≫ hm (φ₁ : homAV A A') =
        hm ((f gb : homPi π₀ π') : homAV A₀ A') ^ (n * n) := by
      rw [← hm_postHom, hφ₁, LinearMap.smul_apply, ← hgb, map_zsmul, smul_smul, hm_zsmul]
    rw [hxga, Category.assoc, key, GrpObj.comp_zpow, ← GrpObj.zpow_comp, hP1, MonObj.one_comp]
  obtain ⟨φ', hφ', hfac⟩ := exists_isMonHom_zpow_comp_eq n hn _ hkill
  have hφ₁π : hm (φ₁ : homAV A A') ≫ π' = π ≫ hm (φ₁ : homAV A A') := φ₁.2
  have hφ'π : φ' ≫ π' = π ≫ φ' := by
    apply cancel_of_ne_one hA hA ((𝟙 A) ^ n) (zpow_id_ne_one hA n hn0)
    rw [← Category.assoc, hfac, hφ₁π, ← hfac, ← Category.assoc, ← zpow_id_comp_comm,
      Category.assoc]
  refine ⟨homPi.mk φ' hφ'π, LinearMap.ext fun x => homPi_eq_of_smul_eq hA₀ hn0 ?_⟩
  rw [← LinearMap.smul_apply n f x, ← hφ₁]
  apply homPi.ext
  rw [hm_zsmul, hm_postHom, hm_postHom]
  change (hm (x : homAV A₀ A) ≫ φ') ^ n = hm (x : homAV A₀ A) ≫ hm (φ₁ : homAV A A')
  rw [← hfac, ← Category.assoc, comp_zpow_id, GrpObj.zpow_comp]

end Int

/-! ### Functoriality of `postHom` -/

section Functor

variable {k : Type u} [Field k] [IsAlgClosed k] {A₀ A A' A'' : Over (Spec (.of k))} [GrpObj A₀]
  [GrpObj A] [GrpObj A'] [GrpObj A''] [AlgebraicGeometry.IsAbelianVariety k A₀]
  [AlgebraicGeometry.IsAbelianVariety k A] [AlgebraicGeometry.IsAbelianVariety k A']
  [AlgebraicGeometry.IsAbelianVariety k A'']
  {π₀ : A₀ ⟶ A₀} {π : A ⟶ A} {π' : A' ⟶ A'} {π'' : A'' ⟶ A''} [IsMonHom π₀] [IsMonHom π]
  [IsMonHom π'] [IsMonHom π'']

/-- The composite of two equivariant homomorphisms. -/
noncomputable def compPi (φ : homPi π π') (ψ : homPi π' π'') : homPi π π'' :=
  homPi.mk (hm (φ : homAV A A') ≫ hm (ψ : homAV A' A'')) (by
    have hφ : hm (φ : homAV A A') ≫ π' = π ≫ hm (φ : homAV A A') := φ.2
    have hψ : hm (ψ : homAV A' A'') ≫ π'' = π' ≫ hm (ψ : homAV A' A'') := ψ.2
    rw [Category.assoc, hψ, ← Category.assoc, hφ, Category.assoc])

theorem hm_compPi (φ : homPi π π') (ψ : homPi π' π'') :
    hm ((compPi φ ψ : homPi π π'') : homAV A A'') =
      hm (φ : homAV A A') ≫ hm (ψ : homAV A' A'') := rfl

/-- The identity as an element of `End_π(A)`. -/
noncomputable def idPi : homPi π π := homPi.mk (𝟙 A) (by simp)

theorem hm_idPi : hm ((idPi : homPi π π) : homAV A A) = 𝟙 A := rfl

theorem postHom_compPi (φ : homPi π π') (ψ : homPi π' π'') :
    postHom (π₀ := π₀) (compPi φ ψ) = (postHom ψ).comp (postHom φ) :=
  LinearMap.ext fun x => homPi.ext (by
    rw [LinearMap.comp_apply, hm_postHom, hm_postHom, hm_postHom, hm_compPi, Category.assoc])

theorem postHom_idPi : postHom (π₀ := π₀) (idPi : homPi π π) = LinearMap.id :=
  LinearMap.ext fun x => homPi.ext (by rw [hm_postHom, hm_idPi, Category.comp_id]; rfl)

/-- `postHom` is injective (in `φ`), given a nonzero element of `L A`. -/
theorem postHom_injective (hA₀ : abelianVarietyDimension A₀ = 1)
    (hA : abelianVarietyDimension A = 1) (x : homPi π₀ π) (hx : hm (x : homAV A₀ A) ≠ 1) :
    Function.Injective (postHom (π₀ := π₀) (π := π) (π' := π')) :=
  postHomAdd_injective hA₀ hA x hx

end Functor

end RamanujanWeil.Arith.Deuring.G8Int
