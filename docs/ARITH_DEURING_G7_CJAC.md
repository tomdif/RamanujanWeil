# A3-ord, G7 step C-Jac: `C ≅ C′ ⇒ Jac C ≅ Jac C′`, Frobenius-equivariantly (2026-11-10)

Step **C-Jac** of the Tate route to `MultLeOneAll` (`ARITH_DEURING_FINAL.md` §3,
`ARITH_DEURING_G7FIN.md` §4 step C, `ARITH_DEURING_G7_WC.md` §3). New files only:

| File | Content |
|---|---|
| `Arith/DeuringG7CJac.lean` | two-curve base change `φ_T`, `φ^*` on the Picard presheaf / functor, functoriality, Frobenius square on Picard functors |
| `Arith/DeuringG7CJacPic0.lean` | additivity, `φ^*` on Picard schemes (Yoneda), `φ^*(Pic⁰_{X'}) ⊆ Pic⁰_X`, `IsMonHom` |
| `Arith/DeuringG7CJacIso.lean` | functoriality on `Pic⁰`, Jacobian iso, Frobenius square, **`exists_equivariant_jacobianIso`** |
| `Arith/DeuringG7CJacBase.lean` | common sites, base change of step C's isomorphism, composition with step J |
| `Arith/DeuringG7CJacAxioms.lean` | `#print axioms` audit |

## 1. What step C delivers and what is consumed

* **Step C** (`Genus2.exists_ne_iso_of_genus_eq_two`, modulo `Genus2ModelExistence`): among
  curves `Y n` over the finite field `K`, some `n ≠ m` have `φ : Y n ≅ Y m` with
  `φ.hom ≫ s m = s n`.
* **`GraphFiniteness`** (`DeuringG7FinCore`) consumes `∃ e : (G n).B ≅ (G m).B,
  IsMonHom e.hom ∧ e.hom ≫ π_m = π_n ≫ e.hom`.
* **Step J** (other agent) is to give `Jac(Θ_n) ≅ B_n` in the same equivariant form, with
  `Jac = (jacobianGrp B hX hk f σ hσ).X` and `π = jacobianFrobenius …` as in G1
  (`JacSite.J`, `JacSite.π`).

C-Jac is stated in exactly that form (`DeuringG7CJacIso`):

```lean
theorem exists_equivariant_jacobianIso
    -- X, X' : smooth proper projective geom. irreducible curves over sep. closed k,
    -- in one site B, with rational points σ, σ' and representable Picard functors
    (α : X ≅ X') (hα : α.hom ≫ B.inclusion.map f' = B.inclusion.map f)
    (p) [Fact p.Prime] (hS) (n) (Ψ hΨ Ψ' hΨ')       -- twisted Frobenii over the same F^n
    (hαΨ : α.hom ≫ Ψ' = Ψ ≫ α.hom) :
    ∃ e : (jacobianGrp B hX hk f σ hσ).X ≅ (jacobianGrp B hX' hk f' σ' hσ').X,
      IsMonHom e.hom ∧ e.hom ≫ jacobianFrobenius B hX' hk f' p hS n Ψ' hΨ' σ' hσ' =
        jacobianFrobenius B hX hk f p hS n Ψ hΨ σ hσ ≫ e.hom
```

The base points `σ`, `σ'` are arbitrary and need not correspond under `α`, because `Pic⁰` and
its group law do not depend on the base point.

## 2. Construction (the Yoneda transport)

For `φ : X ⟶ X'` over `k`:

1. `curveBaseChangeMap φ T = φ ×_k 𝟙_T : X_T ⟶ X'_T` is natural in `T`. It also satisfies
   `(φ ≫ ψ)_T = φ_T ≫ ψ_T` and `(𝟙)_T = 𝟙`.
2. Pulling back along `φ_T` gives `curvePicardPresheafMap : Pic(X'_–) ⟶ Pic(X_–)`.
   Sheafifying gives `curvePicardMap : Pic_{X'/k} ⟶ Pic_{X/k}`. It is contravariantly
   functorial (`curvePicardMap_comp`, `curvePicardMap_id`, via `sheafifyMap_comp/id`).
3. `curvePicardMap` is additive (`curvePicardMap_add`), because every point of `Pic_{X'/k}` is a
   class of an invertible module (Stacks 0B9N, `surjective_toPicardFunctorHom`).
4. Yoneda gives `curvePicardSchemeHom : Pic_{X'} ⟶ Pic_X`.
5. It maps `Pic⁰_{X'}` into `Pic⁰_X` (`exists_curveJacobianHom`). This is Stacks' connectedness
   argument for `jacobianPullback`, adapted to two curves: `Pic⁰_{X'}` is irreducible, its image
   contains the zero point (by additivity), and `Pic⁰_X` is clopen.
6. The result is `curveJacobianHom : Pic⁰_{X'} ⟶ Pic⁰_X`. On points it is `φ^*`, and it is a
   homomorphism (`isMonHom_curveJacobianHom`).
7. Morphisms into `Pic⁰_X` are determined by their points (`pic0_hom_ext'`). Hence:
   * `curveJacobianHom_comp`, `curveJacobianHom_id`;
   * the Frobenius square `curveJacobianHom_comp_twistedJacobianHom`. Its presheaf-level input
     is `Θ_T ≫ φ_T = φ_T ≫ Θ'_T` whenever `Ψ ≫ φ = φ ≫ Ψ'`.
8. Over `Spec k`:
   * `curveJacobianPullback = Over.post`-image, which is a homomorphism;
   * **`curveJacobianIso α : J_X ≅ J_{X'}`**, with `hom = (α⁻¹)^*` and `inv = α^*`;
   * **`curveJacobianPullback_comp_jacobianFrobenius`**.

## 3. Interfaces (`DeuringG7CJacBase`)

* `exists_site_containing_family`: all `Θ_n` (or all `Y n ×_K K̄`) and `Spec K̄` lie in one big
  fppf site. So C-Jac applies to any pair, and step J may be stated on that one site.
* `exists_baseChange_iso`: step C's `φ : Y ≅ Y'`, `φ.hom ≫ s' = s` base-changes to
  `α : Y_L ≅ Y'_L`. This `α` lies over `L` (`hα`) and commutes with every Galois twist
  `galoisBaseChange _ L τ`. That includes the twisted Frobenius `Ψ = id × Spec(frob)` used by G1
  for `JacSite.π`, so `hαΨ` holds.
* `IsEquivJacIso.symm/trans` and `exists_equivIso_of_jac` assemble the conclusion of
  `GraphFiniteness` from step J's `Jac_n ≅ B_n`, `Jac_m ≅ B_m` and C-Jac's `Jac_n ≅ Jac_m`.

## 4. What remains (not C-Jac)

* **Hypotheses on the base-changed curves.** To feed `exists_baseChange_iso` into
  `exists_equivariant_jacobianIso` for `Y_K̄`, a consumer must supply four things:
  * the curve instances (`IsCurve`, `Smooth`, `IsProper`, `GeometricallyIrreducible`,
    `IsProjectiveVariety` over `K̄`). G1 does this for cubics via `isCurve_projOf_baseChange`;
    for genus 2 it is the base-change stability of these properties;
  * a `K̄`-point `σ`;
  * representability (`isRepresentable_picardFunctor_of_isSepClosed`, given
    `IsProjectiveMorphism`);
  * `hΨ` (as `JacSite.Ψ_comp`).
  This is routine glue, owned by **C-descent** / **J**. It depends on how J states `Θ_n` (over
  `𝔽_q` and base-changed, or directly over `K̄` with `Ψ`).
* **Steps J, D, Θ, and C's named Props** are unchanged.

No new named Prop is introduced by C-Jac.

## 5. Audit

`nice -n 10 lake build RamanujanWeil.Arith.DeuringG7CJacAxioms` succeeds (2026-11-10).
* All 25 audited declarations depend only on `[propext, Classical.choice, Quot.sound]`. These
  include `exists_equivariant_jacobianIso`, `curveJacobianIso`,
  `curveJacobianPullback_comp_jacobianFrobenius`, `curveJacobianHom_comp` and
  `exists_baseChange_iso`.
* There is no `sorry`, `admit`, `native_decide` or `axiom`. No existing file was edited, and
  `RamanujanWeil.lean` is untouched.
* Sizes: CJac 231, CJacPic0 252, CJacIso 267, CJacBase 174, CJacAxioms 31 lines (955 total),
  inside the 0.6–1.2k estimate.
* Build times are about 3–4 min per file, mostly import loading.

Note: Stacks' `CurvePicard/JacobianPullback.lean` has no built olean in the pinned package, so it
is not imported. Its connectedness and `IsMonHom` arguments are re-done here for two curves.
