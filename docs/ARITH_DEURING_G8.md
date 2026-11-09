# A3-ord: G7-dual (separable part) and G8(i)/(ii) (2026-11-09)

This continues `ARITH_DEURING_MULT.md` (§3 G7-dual, §6 per-class content) and
`ARITH_DEURING_G7.md`. New files, audited in `RamanujanWeil/Arith/DeuringG8Axioms.lean`:

| File | Content |
|---|---|
| `Arith/DeuringG7Dual2.lean` | epimorphism + automatic equivariance of duals, separable part of the dual via the G6 quotient, named **`RadicialDual`**, **`frobHomDual_of_radicialDual`** |
| `Arith/DeuringG8Alg.lean` | pure algebra: non-scalar `2×2` root of `X²−tX+q` has trace `t`, det `q`; rank of a torsion extension; the commutant step |
| `Arith/DeuringG8End.lean` | **`exists_zpow_eq_of_comm`**: `End_π(A) ⊗ ℚ = ℚ(π)` (the End case of Tate, no ℓ-adics) |
| `Arith/DeuringG8Lattice.lean` | `homPi π₀ π = Hom_π(A₀, A)`, **`finrank_homPi_eq_two`**, **`exists_basis_trDet`** |
| `Arith/DeuringG8Frob.lean` | G8(i) for Frobenius Jacobians, **`exists_latticeMatrix`** (the `Λ` field), G8(ii) first steps |

No existing file was edited. No `sorry`, `admit`, `native_decide` or `axiom`.
`nice -n 10 lake build RamanujanWeil.Arith.DeuringG8Axioms` succeeds; every audited
declaration depends only on `[propext, Classical.choice, Quot.sound]` (§6).

## 1. G7-dual: the separable part, and the one remaining (radicial) input

Setting: `k` algebraically closed, `A`, `B` one-dimensional abelian varieties over `k`.

* `cancel_of_ne_one`: a nonzero homomorphism `α : A ⟶ B` is an epimorphism in `Over k`
  (dominant by `isDominant_of_ne_one`, `A` reduced, any target separated; Mathlib
  `ext_of_isDominant_of_isSeparated`).
* **Duals are automatically equivariant** (`comm_of_comp_eq_zpow`): if `α ≫ β = [n]` and
  `α ≫ π_B = π_A ≫ α`, then `β ≫ π_A = π_B ≫ β`. Proof: `α ≫ (β ≫ π_A) = [n] ≫ π_A =
  π_A ≫ [n] = α ≫ (π_B ≫ β)`, cancel `α`. Also `β ≫ α = [n]` (`comp_eq_zpow_symm`). So
  **no Frobenius/Verschiebung equivariance has to be proved**: any `β` with `α ≫ β = [n]` is
  the equivariant dual. This also makes the dual available for *abstract* `FrobeniusJacobian`s
  (where `π` need not be the purely inseparable Frobenius).
* **Separable part (proved, `exists_dual_of_radicialDual`).** `Γ = ker α(k)` is finite
  (`eq_one_of_infinite_pointKer`); `G : Glue Γ` is the G6 quotient `q : A → A/Γ`
  (`nonempty_glue`); `α = q ≫ ᾱ`, `[N] = q ≫ s` with `N = #Γ` (Lagrange). Then
  * `ᾱ` is injective on `k`-points (`q` is surjective on points, `Glue.exists_comp_q_eq`);
  * `dim A/Γ = 1` (`dim_eq_of_surjective`: Krull dimension along the surjections `q` and `s`,
    `s` surjective because `[N]` is, `surjective_of_ne_one`);
  * if `ᾱ ≫ h = [m]` then `α ≫ (h ≫ s) = [Nm]`.
* **`RadicialDual` (named, the only remaining input of G7-dual).**

  ```lean
  def RadicialDual : Prop :=
    ∀ (k) [Field k] [IsAlgClosed k] (B A' : Over (Spec (.of k))) [GrpObj B] [GrpObj A']
      [IsAbelianVariety k B] [IsAbelianVariety k A'],
      abelianVarietyDimension B = 1 → abelianVarietyDimension A' = 1 →
      ∀ (f : B ⟶ A') [IsMonHom f], (∀ x : 𝟙_ _ ⟶ B, x ≫ f = 1 → x = 1) →
      ∃ (n : ℤ) (h : A' ⟶ B), n ≠ 0 ∧ IsMonHom h ∧ f ≫ h = (𝟙 B) ^ n
  ```

  A radicial (purely inseparable) isogeny divides a multiplication map. True: `f ≅ F^r`
  (relative Frobenius) and `h = V^r`, `n = p^r`.
* **`frobHomDual_of_radicialDual : RadicialDual → FrobHomDual`**, and
  `homDualHyp_of_radicialDual : RadicialDual → HomDualHyp A B` for all `A`, `B` (so G3's
  `homAV_finite_free` / `homAV_tensor_injective` hold unconditionally given `RadicialDual`).

### Ordinary shortcut: assessment

The prompt asked whether, in the ordinary case, an equivariant homomorphism can be chosen
separable, or composed with `π`-powers, to avoid the inseparable case. Answer: **not cheaply.**

* Composing with `π^m` or with any element of `ℤ[π]` never *decreases* the inseparable degree.
  To get a separable `A ⟶ A'` one needs a separable isogeny `A → A^{(p^r)}`. For ordinary `A`
  this exists (the class of `𝔭` in `Pic(O)` contains ideals prime to `p`), but proving it
  needs CM theory.
* The automatic equivariance above *does* remove the Frobenius/Verschiebung bookkeeping from
  the inseparable step: what remains is the purely geometric `RadicialDual`, with no `π` in
  it.

### Route for `RadicialDual` (estimate 0.8–1.3k lines)

1. (0.4–0.7k, hardest) `f` injective on `k`-points ⇒ `k(B)/f^*k(A')` purely inseparable. Let
   `S` be the separable closure of `f^*k(A')` in `k(B)` and `C` its model
   (`nonempty_functionFieldModel`). Then `B → C` is radicial (bijective on points) and
   `C → A'` is separable of degree `d`. Generic étaleness of a separable extension, plus
   Stacks `card_sections_of_etale_of_isAlgClosed` on a dense open, gives a fibre with `d`
   points, so `d = 1`. Stacks has the endomorphism case of "étale ⇒ #kernel = degree"
   (`EndomorphismKernelCount`), but not the hom case or generic étaleness of curves.
2. (0.2–0.3k) `[p^r]^* k(B) ⊆ k·k(B)^{p^r}`: `[p]` is not étale at `0` (tangent map
   `p = 0`, Stacks `homMk_tangent_comp_endPolyEval_of_modEq`), so `k(B)/[p]^*k(B)` is not
   separable. With `[k(B) : k k(B)^p] = p` (`finrank_compositumFrobenius_functionField`)
   this forces `[p]^*k(B) ⊆ k k(B)^p`. Iterate.
3. (0.2–0.3k) By Stacks 0CCZ (`existsUnique_nat_existsUnique_iso_nFoldFrobeniusTwist`),
   `f^*k(A') = k·k(B)^{p^r}`. So `[p^r]^*k(B) ⊆ f^*k(A')`, and
   `exists_hom_functionFieldMap_eq` gives a morphism `h : A' ⟶ B` with `f ≫ h = [p^r]`
   (`over_hom_ext_of_functionFieldMap`). `h` is a homomorphism: it is additive on `k`-points
   (`f` is bijective on points), and `A' ⊗ A'` is reduced (as in `DeuringG3Div`).

## 2. `End_π(A) ⊗ ℚ = ℚ(π)` (proved, `DeuringG8End`)

```lean
theorem exists_zpow_eq_of_comm (hA : abelianVarietyDimension A = 1) (π e : A ⟶ A)
    [IsMonHom π] [IsMonHom e] (t q : ℤ)
    (hπ : endPolyEval π (X ^ 2 - C t * X + C q) = 1) (hdisc : t ^ 2 < 4 * q)
    (hcomm : e ≫ π = π ≫ e) :
    ∃ N a b : ℤ, N ≠ 0 ∧ e ^ N = π ^ b * (𝟙 A) ^ a
```

Proof, with no ℓ-adic input and no `HomDualHyp`. Work in Stacks' `postcompSubring A`, a ring
model of `End(A)`, inside the commutative subring generated by `π` and `e`
(`Subring.isMulCommutative_closure`). All of its elements are homomorphisms (`homSub`), so
Cayley–Hamilton (`DeuringG3.endPolyEval_eq_one_of_endCharPoly_eq` with integral trace,
`exists_int_trace`), torsion-freeness (`eq_one_of_zpow_eq_one`) and
`deg = 0 ⇔ 0` (`endDegree_eq_zero_iff`) apply to them. With `x = 2π − t` (`x² = t² − 4q < 0`),
`y = 2e − s` (`y² = s² − 4 deg e ≤ 0`, Hasse `trace_sq_le_four_mul_endDegree`) and `z = xy`:
`z² = x²y²` and `z² − τz + deg z = 0`. If `τ ≠ 0`, then `τ(t² − 4q)·y = (x²y² + deg z)·x`.
If `τ = 0`, then `deg z = −x²y² ≤ 0`, so `z = 0` and `y = 0`. (`G8.exists_mul_eq_of_sq`.)

This is the "End case of Tate is free" from `ARITH_DEURING_G7.md` §0.1, done algebraically.

## 3. G8(i): `L(E) = Hom_π(E₀, E)` is free of rank 2 (proved, given homs both ways)

`homPi π₀ π : Submodule ℤ (homAV A₀ A)`, `piAct π₀ π` (postcomposition with `π`).

```lean
theorem finrank_homPi_eq_two (hA₀ hA) (π₀ π) (t : ℤ) (q : ℕ)
    (hχ₀ : endCharPoly A₀ π₀ = X ^ 2 - C (t : ℚ) * X + C (q : ℚ))
    (hχ  : endCharPoly A  π  = X ^ 2 - C (t : ℚ) * X + C (q : ℚ)) (hdisc : t ^ 2 < 4 * q)
    (α : A₀ ⟶ A) [IsMonHom α] (hα : α ≠ 1) (hαπ : α ≫ π = π₀ ≫ α)
    (β : A ⟶ A₀) [IsMonHom β] (hβ : β ≠ 1) (hβπ : β ≫ π₀ = π ≫ β) :
    Module.Finite ℤ (homPi π₀ π) ∧ Module.Free ℤ (homPi π₀ π) ∧ finrank ℤ (homPi π₀ π) = 2
theorem exists_basis_trDet ... : ∃ b : Basis (Fin 2) ℤ (homPi π₀ π),
    (toMatrix b b (piAct π₀ π)).trace = t ∧ (toMatrix b b (piAct π₀ π)).det = q
```

* Finite/free: a submodule of `homAV A₀ A`, which is finite free by G3 with `HomDualHyp`
  supplied by `β`.
* `≥ 2`: `α`, `α ≫ π` are independent: `α ≫ (bπ + a) = 0 ⇒ bπ + a = 0 ⇒
  deg = b²q + abt + a² = 0 ⇒ a = b = 0` (`endDegree_zpow_mul_zpow`, `t² < 4q`).
* `≤ 2`: `γ ↦ γ ≫ β` embeds `L` into `End_π(A₀)` (`comp_ne_one`), and every element of
  `End_π(A₀)` has a nonzero multiple in `ℤ + ℤπ₀` (§2), so `finrank End_π(A₀) ≤ 2`
  (`finrank_le_two_of_torsion_quotient`, rank-nullity over `ℤ`).
* Matrix: `piAct` satisfies `X² − tX + q` (`frob_quadratic` composed on the left) and is not
  scalar (`π = c ⇒ deg(π − c) = q − ct + c² = 0`, impossible). A non-scalar `2×2` integer root
  of `X² − tX + q` has trace `t` and det `q` (`trace_det_of_sq_eq`).

**Only one hom per direction is needed; `α ≫ β = [n]` is not used.** In particular the
zig-zag along the class and the matching of Jacobian sites (the 0.2–0.4k of
`ARITH_DEURING_MULT.md` §6.1) are **not needed**: `TateFiniteness` applies to *any* two curves
of the same ordinary trace and *any* Jacobian sites, and `FrobHomDual` reverses the direction.

For Frobenius Jacobians (`DeuringG8Frob`):

* `frobLattice_trDet` (homs both ways), `frobLattice_trDet_of_tate` (`FrobHomDual` +
  `QuotientFiniteness`);
* **`exists_latticeMatrix`** (`TateFiniteness K`, `FrobHomDual`, fixed `W₀` of trace `t`, site
  `S₀`, `p ∤ t`, `t² < 4q`): a function `Λ : WeierstrassCurve K → TrDet t q` such that for
  every `W` of trace `t`, `Λ W` is the matrix of Frobenius on a `ℤ`-basis of
  `Hom_π(J_{W₀}, J_W)` for a chosen site of `W`. This is the `Λ` field of
  `DeuringClassLattice`, with its intended meaning;
* `exists_latticeMatrix_of_radicialDual`: the same with `RadicialDual` in place of
  `FrobHomDual`.

## 4. G8(ii): first steps (proved)

* `finrank_endPi_eq_two`: `End_π(A₀)` is free of rank 2. With §2, `End_π(A₀) ⊗ ℚ = ℚ(π₀)`.
  So `End_π(A₀)` is an order of `ℚ(π₀)` containing `ℤ[π₀]`, not necessarily equal to it (route
  L's descent to the curve with `End = ℤ[π]` is still needed, as noted in
  `ARITH_DEURING_MULT.md` §6).
* `postHom φ : Hom_π(A₀, A) →ₗ Hom_π(A₀, A')`, `γ ↦ γ ≫ φ`. It commutes with Frobenius
  (`postHom_piAct`), so it is a `ℤ[π]`-module map `L(A) → L(A')`. The map `postHomAdd :
  Hom_π(A, A') →+ Hom_ℤ(L A, L A')` is **injective** whenever `L(A) ≠ 0`
  (`postHomAdd_injective`).

Not done: surjectivity of `Hom_π(E, E') → Hom_{ℤ[π]}(L E, L E')`. Over `ℚ` it follows from
§2–3 (both sides are 1-dimensional over `ℚ(π)`). Integrally, the cokernel is controlled by
`End_π(E₀)` vs `ℤ[π]` and needs the `⊗ ℤ_ℓ` saturation statement (G3 `homAV_saturated`,
`homAV_tensor_injective`) at every `ℓ ≠ p`, plus a separate argument at `p`.
**Estimate 0.5–1k**, plus the `End = ℤ[π]` descent (part of G8(iii)).

## 5. What remains for `DeuringClassLatticeAll`

| Item | Status | Estimate |
|---|---|---|
| `FrobHomDual` | **reduced to `RadicialDual`** (separable part proved) | 0.8–1.3k (§1 route) |
| `Λ` field (G8(i)) | **proved** given `TateFiniteness` + `FrobHomDual` (`exists_latticeMatrix`) | — |
| `End_π ⊗ ℚ = ℚ(π)`, rank 2 | **proved** | — |
| G8(ii) `Hom_π(E,E') ≅ Hom_{ℤ[π]}(L E, L E')` | injectivity + equivariance proved; surjectivity open | 0.5–1k |
| `rel_iff`, `card_stab` | G1 (other agent: `DeuringG1Assembly`) + G8(ii) + descent to `End = ℤ[π]` | 1–2k |
| `surj_class` (G8(iii)) | open | 1.5–3k |
| `TateFinitenessAll` | open (`QuotientFiniteness`) | 12–30k |

Named Props after this session:

| Prop | Where | Meaning |
|---|---|---|
| `RadicialDual` | `DeuringG7Dual2` | a purely inseparable isogeny of elliptic curves divides some `[n]` |
| `FrobHomDual` | `DeuringG7Dual` | now a *theorem* of `RadicialDual` (`frobHomDual_of_radicialDual`) |
| `TateFiniteness(All)` | `DeuringMultDef` | unchanged |
| `DeuringClassLatticeAll` | `DeuringMultCount` | unchanged interface; `Λ` field constructed (§3) |

## 6. Axiom audit

`nice -n 10 lake build RamanujanWeil.Arith.DeuringG8Axioms`: all audited declarations
depend only on `[propext, Classical.choice, Quot.sound]`.
