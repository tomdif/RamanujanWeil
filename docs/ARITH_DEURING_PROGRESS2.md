# A3-ord progress, session 2: G3 completion, G4 on `Hom(A, B)`, G1 descent (2026-11-08)

This continues `docs/ARITH_DEURING_PLAN.md` and `docs/ARITH_DEURING_PROGRESS.md` (session 1:
G2, G3 injectivity/divisibility/saturation, G4 on `End`). The framework is unchanged: abelian
varieties are Stacks group objects over `k̄ = AlgebraicClosure 𝔽_q`, and the `𝔽_q`-structure is
the Frobenius `π` of `FrobeniusJacobian W`.

All new files are axiom-clean: only `propext`, `Classical.choice`, `Quot.sound`, with no
`sorry`/`admit`/`native_decide`/`axiom`. The audit file is
`RamanujanWeil/Arith/DeuringGAxioms2.lean`. No existing file was edited.

| File | Lines | Imports |
|---|---|---|
| `Arith/DeuringG3Lattice.lean` | 302 | Mathlib only |
| `Arith/DeuringG3Hom.lean` | 356 | `DeuringG4`, `DeuringG3Sat`, `DeuringG3Lattice` |
| `Arith/DeuringG4Hom.lean` | 294 | `DeuringG3Hom`, Stacks `Curves.InseparableFactorizationChain`, `Curves.TwistedFrobeniusDegree` |
| `Arith/DeuringG1Descent.lean` | 178 | Mathlib only |
| `Arith/DeuringGAxioms2.lean` | 44 | audit |

The Stacks module `Curves.InseparableFactorizationChain` was not prebuilt. It was built once this
session in about 50 s.

## 1. G3 completion: `Hom(A, B)` is a lattice of rank `≤ 4`, and `Hom ⊗ ℤ_ℓ ↪ Hom(T_ℓ)`

### 1a. The algebra (`DeuringG3Lattice.lean`, namespace `…Deuring.Geom.Lattice`)

The setting is an abelian group `M` with a biadditive form `B : M →+ M →+ ℤ` that is anisotropic
(`B x x = 0 → x = 0`), and a free `ℤ_ℓ`-module `T` of finite rank. The map `τ : M →+ T` is
`ℓ`-saturated: `τ x = ℓ • z → ∃ y, x = ℓ • y`.

| Name | Statement |
|---|---|
| `finite_free_saturation` | The saturation `{x : ∃ n ≠ 0, n • x ∈ ⟨e⟩}` of a finitely generated subgroup is finitely generated and free. It embeds into `ℤ^s` by `x ↦ (B x eᵢ)ᵢ`. |
| `linearIndependent_of_saturated` | If `N` is free with `ℤ`-basis `b` and `τ` is `ℓ`-saturated, then `(τ bᵢ)` is `ℤ_ℓ`-linearly independent. The proof reduces the coefficients mod `ℓ` (`PadicInt.zmodRepr`), uses saturation, and descends; Krull's intersection theorem in `ℤ_ℓ` then kills the coefficients. |
| `finite_free_of_anisotropic_of_saturated` | `M` is finitely generated and free. A maximal independent family is finite, by the previous row, and everything lies in its saturation. |
| `finrank_le_of_anisotropic_of_saturated` | `rank_ℤ M ≤ rank_{ℤ_ℓ} T`. |
| `liftBaseChange_injective_of_anisotropic_of_saturated` | `ℤ_ℓ ⊗_ℤ M → T` (`LinearMap.liftBaseChange`) is injective. |

The proof is purely algebraic. It does not need the topological "discrete subgroup ⇒ lattice"
step of Silverman III.7.4: the integral pairing already embeds the saturation into `ℤ^s`.

### 1b. The geometry (`DeuringG3Hom.lean`)

Here `k` is algebraically closed, `A` and `B` are abelian varieties of dimension 1, and `ℓ` is a
prime invertible in `k`.

| Name | Statement |
|---|---|
| `homAV A B` | The homomorphisms `A ⟶ B`, as an `AddSubgroup (Additive (A ⟶ B))`. |
| `tateHom ℓ : homAV A B →+ (T_ℓA →ₗ[ℤ_ℓ] T_ℓB)` | `T_ℓ` as an additive map. |
| `homAV_saturated` | `T_ℓ α = ℓ • z ⇒ α = ℓ • β`, from `DeuringG3Sat` with `m = 1`. |
| `degPolar`, `degPolar_mul_left`, `degPolar_self` | `⟨f, g⟩ = deg(f+g) − deg f − deg g` on `End(A)` is biadditive, and `⟨f, f⟩ = 2 deg f`. This is the polar form of `det` on `2×2` matrices, through `endDegree_eq_det_tateModuleMap`. |
| `endForm`, `endForm_anisotropic` | `⟨·,·⟩` as `homAV A A →+ homAV A A →+ ℤ`, which is anisotropic by `endDegree_eq_zero_iff`. |
| `comp_ne_one` | A composite of nontrivial homomorphisms of 1-dimensional abelian varieties is nontrivial. |
| `postcomp ψ`, `postcomp_injective` | `α ↦ α ≫ ψ` is additive, and injective when `ψ ≠ 0`. |
| `HomDualHyp A B` | `Hom(A,B) = 0 ∨ ∃ ψ : B ⟶ A, IsMonHom ψ ∧ ψ ≠ 1`. |
| `homDualHyp_self` | `HomDualHyp A A`. |
| `exists_anisotropic_form` | Under `HomDualHyp`, `homAV A B` carries an anisotropic biadditive `ℤ`-form, namely `endForm` pulled back along `postcomp ψ`. |
| `finrank_tateHom_target` | `rank_{ℤ_ℓ} Hom(T_ℓA, T_ℓB) = 4`. |
| **`homAV_finite_free`** | Under `HomDualHyp A B`, `Hom(A,B)` is `Module.Finite ℤ`, `Module.Free ℤ`, and `finrank ≤ 4`. |
| **`homAV_tensor_injective`** | Under `HomDualHyp A B`, `ℤ_ℓ ⊗_ℤ Hom(A,B) → Hom_{ℤ_ℓ}(T_ℓA, T_ℓB)` is injective. |
| **`endAV_finite_free`, `endAV_tensor_injective`** | Unconditional for `End(A)`. |

**What "unconditional for `A ≠ B`" still needs: sub-lemma G3-dual.** For `α : A ⟶ B` nonzero
(dim 1), there exists a nonzero `B ⟶ A`. With that, `HomDualHyp` holds for all `A`, `B`, and so
do the two headline results. Plan: with `m = #ker α(k̄)`,
* **separable `α`**: `α` is étale and surjective, so `A ×_B A` is reduced. The `DeuringG3Div`
  descent argument, run along `α` instead of `[n]`, then gives `β` with `α ≫ β = [m]`. Two new
  inputs are needed: étaleness of a separable isogeny (translation-homogeneity of the
  differential), and surjectivity on `k̄`-points;
* **inseparable `α`**: factor `α` through Frobenius. Stacks has
  `exists_chain_isInseparableDegreePrime` for curves, and `exists_hom_functionFieldMap_eq`
  (0BY1) to build morphisms from function-field maps. Alternatively, build `α̂` field-theoretically
  as `k(A) ≅ [m]^*k(A) ⊆ α^*k(B)` and apply 0BY1.

Estimate 0.8–2k lines. **This is not on the critical path:** in the Deuring application
`A = A₀`, `B = A_E`, and G7 (Tate) gives nonzero isogenies in both directions, because the traces
are equal and the situation is symmetric. So `HomDualHyp A₀ A_E` comes for free there.

## 2. G4 on `Hom(A, B)` (`DeuringG4Hom.lean`)

`homDegree α := [k(A) : α^*k(B)]` (Stacks `degreeOver`) if `α.left` is dominant, else `0`. This
is exactly Stacks' `endDegree` when `A = B` (`homDegree_eq_endDegree`). Below, `A`, `B`, `C`
have dimension 1 over `k = k̄`.

| Name | Statement |
|---|---|
| `isCurve_of_dim_one` | A 1-dimensional abelian variety is an `IsCurve`. |
| `homDegree_pos_of_isDominant` | Dominant ⇒ `0 < deg`, via Stacks `finiteDimensional_functionField_of_isCurve`. |
| `isDominant_of_ne_one` | A nontrivial homomorphism is dominant: its image is closed, a proper closed subset of a curve is finite, and finite kernel plus finite image would make `A(k̄)` finite. |
| `not_isDominant_one`, `homDegree_one` | `deg 0 = 0`. |
| **`homDegree_eq_zero_iff`** | `deg α = 0 ↔ α = 0`. |
| **`homDegree_comp`** | `deg(α ≫ β) = deg α · deg β`: the tower law `degreeOver_comp_of_pos` (02NZ) plus the zero cases. |
| **`homDegree_zpow`** | `deg(nα) = n² deg α` for `n ≠ 0`. |
| `endDegree_comp_eq` | `endDegree A (α ≫ ψ) = deg α · deg ψ`. |
| `homPolar_mul_left`, `homPolar_self` | Given a nonzero `ψ : B ⟶ A`, `⟨α,β⟩ = deg(α+β) − deg α − deg β` is biadditive and `⟨α,α⟩ = 2 deg α`. |
| **`homDegree_parallelogram`** | Given a nonzero `ψ : B ⟶ A`, `deg(α+β) + deg(α−β) = 2deg α + 2deg β`. So `deg` is a positive definite quadratic form on `Hom(A,B)`. |

Positivity and multiplicativity are unconditional. The quadratic-form property needs a nonzero
`B ⟶ A` (G3-dual), exactly as in Silverman III.6.3, which uses the dual isogeny.

## 3. G1: what Stacks has, what is proved, and the remaining sub-lemmas

### 3a. Inventory (checked this session)

| Need | Stacks | Status |
|---|---|---|
| `A(k̄) ≅ Pic⁰(E_k̄)` with `π ↔ Ψ^*` | `Stacks.Zeta.exists_jacobianFrobenius_data` (`Curves/ZetaFunction/FrobeniusKernelCount.lean`) returns `E : Additive(A(k)) ≃+ picardDegreeZero` and the Frobenius compatibility | **have**. `FrobeniusJacobian` (session 1) dropped `E`; a new structure must keep it |
| Abel map `X → Pic¹`, birational for `d = g` | `Picard/AbelMapFinal.lean`: `existsUnique_abelMap`, `isBirational_curveAbelMap` (0BA0 (4)–(6)), stated on a `BigFppfSite`, with representability, 0B9Y and 0B90 as hypotheses | partial. For `g = 1`, "birational of smooth proper curves ⇒ iso" is still needed (Stacks `isIso_of_degreeOver_eq_one`, 0BY1 in `InseparableFactorizationChain`) |
| `Pic⁰ ≅ E(k̄)` for genus 1 (`P ↦ [P − O]`) | `Picard/CurveChowZeroDivisor.lean`: `[x] − [x']` is the image of `𝒪(x) ⊗ 𝒪(x')⁻¹` (degree 0); `Curves/GenusOne/*`: point divisors, section rings, Weierstrass model, `autScheme` | ingredients only; the bijection is not stated |
| Pointed isos of Weierstrass cubics = coordinate changes | `Stacks/WeierstrassCubicAutomorphisms.lean`: **`exists_unique_variableChange`** (every iso `E_{C'} ≅ E_C` of pointed families over `Spec R` is `changeIso γ C` for a unique `γ` with `γ • C = C'`); `WeierstrassCubicIso.lean`: `changeIso`, `familyOfMapIso` (base change `E_C ×_R S ≅ E_{C.map φ}`) | **have** |
| `W ×_{𝓜₁,₁} W ≅ H × W` | `WeierstrassCoordinateChangeTorsor.lean`: `representsComparisons_coordinateChange` | have (not needed beyond the row above) |
| Rigidity: a pointed morphism of abelian varieties is a homomorphism | none found (`grep rigidity`) | **missing** |
| Galois descent for morphisms of schemes | none in usable form | avoided: descent is done on coordinates (3b) |

### 3b. Proved (`DeuringG1Descent.lean`, namespace `…Deuring.Geom.Descent`, Mathlib only)

`K` is a finite field and `K̄ = AlgebraicClosure K`. `frobQ : K̄ →+* K̄` is `x ↦ x^{#K}`
(`FiniteField.frobeniusAlgHom`).

| Name | Statement |
|---|---|
| `mem_range_of_pow_card_eq` | `x^q = x ⇒ x ∈ K`. The image of `K` gives `q` roots of `X^q − X`, so there is no room for another. |
| `exists_map_eq_of_frobFixed` | `C.map frobQ = C ⇒ ∃ C₀ : VariableChange K, C₀.map (algebraMap K K̄) = C`. |
| `frobFixed` | The subgroup of Frobenius-fixed `VariableChange K̄`. |
| **`mem_orbit_iff_exists_frobFixed`** | `W' ∈ VariableChange K • W ↔ ∃ C ∈ frobFixed, C • W_K̄ = W'_K̄`. |
| **`stabilizerEquivFrobFixed`** | `Stab_{VariableChange K}(W) ≃* Stab_{VariableChange K̄}(W_K̄) ⊓ frobFixed`. |
| `card_stabilizer_eq_frobFixed` | The equality of cardinalities that `card_stab` consumes. |

So the frozen fields `rel_iff`/`card_stab` are reduced to a statement over `K̄` alone: matching
`π`-equivariant isomorphisms of Frobenius Jacobians with Frobenius-fixed coordinate changes.

### 3c. Remaining G1 sub-lemmas (precise statements, in dependency order)

Notation: `E_W := Over.mk (pullback.snd (projectionOf W) (Spec K̄ → Spec K))` is the geometric
cubic, and `0_W` is its zero section. `Ψ_W` is the twisted Frobenius
(`galoisBaseChangeIso … arithmeticFrobenius`), and `P ↦ P^{(q)}` is Mathlib's `Point.map frobQ`
on `W_K̄(K̄)`.

* **G1.0, data** (0.2–0.4k). Define `FrobeniusJacobianPic W extends FrobeniusJacobian W` with the
  extra fields `E : Additive(𝟙 ⟶ A) ≃+ picardDegreeZero …` and the `π ↔ Ψ^*` compatibility from
  `exists_jacobianFrobenius_data`, and prove `Nonempty (FrobeniusJacobianPic W)` by re-running
  `nonempty_frobeniusJacobian` without discarding `E`.
* **G1.1, Abel isomorphism in genus 1** (1.5–3k). There is an isomorphism
  `ab : E_W ≅ J.A` in `Over (Spec K̄)` such that `0_W ≫ ab.hom = η[J.A]`, and for every point
  `P`, `ab(P^{(q)}) = π(ab(P))`. Route: `existsUnique_abelMap`/`isBirational_curveAbelMap` at
  `d = g = 1`. Translate `Pic¹ → Pic⁰` by `−0_W`. Birational + smooth proper curves gives an iso
  (`isIso_of_degreeOver_eq_one`). The hypotheses (representability `0B9Z`, `TwistToNormalized`
  `0B9Y`, `0B90`) are discharged as in `exists_jacobianFrobenius_data`
  (`isRepresentable_picardFunctor_of_isSepClosed`). **Risk:** the Abel map lives on a
  `BigFppfSite`-represented `Pic`, while `J.A` comes from the existential data. Making the two
  meet may force constructing `J` concretely (the representing object) rather than via
  `Nonempty`.
* **G1.2, rigidity** (0.4–1k). A morphism `f : A ⟶ B` of abelian varieties over `k̄` with
  `η ≫ f = η` is a homomorphism. In dimension 1 a cheaper route avoids the rigidity lemma:
  through `ab`, a pointed iso of genus-1 curves induces an iso on `Pic⁰`, which is additive, and
  `A ⊗ A` is reduced, so the `DeuringG3Div` points argument applies.
* **G1.3, coordinates** (0.3–0.6k). For `W₁, W₂` over `K`, pointed isomorphisms
  `E_{W₂} ≅ E_{W₁}` over `Spec K̄` correspond bijectively to
  `{C : VariableChange K̄ // C • W₁_K̄ = W₂_K̄}`. Use `familyOfMapIso` to identify `E_W` with
  `projOf (W.map (algebraMap K K̄))`, then `exists_unique_variableChange`. The iso commutes with
  `P ↦ P^{(q)}` on points iff `C.map frobQ = C`. Points are determined by their coordinates, and
  the substitution `x ↦ u²x + r, …` commutes with `q`-th powers iff `u, r, s, t` are
  `frobQ`-fixed.
* **G1.4, assembly** (0.3–0.5k). For `J`, `J'` Frobenius Jacobians of `W`, `W'`:
  `(∃ e : J.A ≅ J'.A, IsMonHom e.hom ∧ e.hom ≫ J'.π = J.π ≫ e.hom) ↔ W' ∈ orbit W`, and
  `Nat.card (Stab_{VariableChange K} W) = Nat.card {e : Aut_Grp(J.A) // e ≫ π = π ≫ e}`. This
  follows from G1.1–G1.3, `point_ext` (two morphisms that agree on `K̄`-points are equal), and
  `DeuringG1Descent`.

**Revised G1 total: 2.7–5.5k**, the same range as the plan's 3–6k. The coordinate-descent part
(the plan's "Galois descent") is done, and G1.3 is mostly Stacks' `exists_unique_variableChange`.
The risk is concentrated in **G1.1** (Abel iso on the existential Jacobian).

## 4. Revised estimates and risks, G5–G9

| Step | Plan estimate | Revised | Risk | Comment |
|---|---|---|---|---|
| G3-dual (new) | — | 0.8–2k | medium | Needed only for an unconditional G3/G4 on `Hom(A,B)`; the Deuring path gets `HomDualHyp` from G7 |
| G5 (p-part, ordinary) | 2–4k | 2–4k | medium | Needs divisibility by `p`, where `A[p]` is not reduced. "Kills the `k̄`-points" must become "kills the torsion *scheme*" (`torsionScheme`, `ZPowCharFibre`), using `A[p] ≅ μ_p × ℤ/p` for ordinary `A`. `homAV_finite_free` and `homDegree_*` reduce the rest to lattice algebra (`DeuringG3Lattice` works at any prime once saturation is known) |
| G6 (quotients by finite étale subgroups) | 4–8k (session 1) | 4–8k | medium–high | Unchanged. Stacks 06PH gives `A/G` as an algebraic space; still to do: it is a scheme (0B8G-type) and an abelian variety. `homDegree_comp` and `isDominant_of_ne_one` give the degree bookkeeping `deg(A → A/G) = #G` |
| G7 (Tate, ℓ ≠ p) | 10–25k | 10–25k | very high | Unchanged. This session removes the algebraic side completely: the `ℤ_ℓ`-injectivity and the saturation (`homAV_tensor_injective`) are what Tate's argument closes up against. The open inputs remain surface quotients (G6 in dim 2) and finiteness of `π`-equivariant iso classes of the quotients. For the **`End` case** (curves only), finiteness = finitely many Weierstrass equations over `𝔽_q` + G1.4 |
| G8 (lattice functor) | 4–8k | 3.5–7k | medium–high | (i) rank-2 lattice: `homAV_finite_free` + G7 existence + `homDegree` on `Hom(A₀, A)` (rank exactly 2 needs `ℤ[π] ⊗ ℚ` acting freely, from G4). (ii) and (iii) unchanged |
| G9 (package `DeuringLattice`) | 0.5–1k | 0.5–1k | low | `rel_iff`/`card_stab` now go through `DeuringG1Descent` + G1.4 |

**Total remaining:** about 24–55k lines (plan: 28–65k). The critical path is still G6 → G7.

## 5. Next steps (recommended order)

1. G1.0 (keep `E` in the Frobenius Jacobian), then G1.3 (`exists_unique_variableChange` +
   `familyOfMapIso` + the Frobenius check on points). Both are low risk.
2. G1.1 Abel iso. First check whether `isBirational_curveAbelMap`'s hypotheses are discharged
   anywhere for `IsSepClosed k` (search for `TwistToNormalized` instances).
3. G6 via 06PH (first: "proper group algebraic space over a field is a scheme").
4. G3-dual (separable case via the `DeuringG3Div` descent along `α`).

## 6. Build

```
nice -n 10 lake build RamanujanWeil.Arith.DeuringGAxioms2
```

Cost: about 3 min for `DeuringG3Hom` and about 1.5 min for `DeuringG4Hom`, mostly import
loading. The two Mathlib-only files take about 30 s each.
