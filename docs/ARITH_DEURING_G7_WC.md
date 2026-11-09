# A3-ord, G7-W and G7-C: Weil pairing layer and genus-2 finiteness (2026-11-09)

This continues `ARITH_DEURING_G7FIN.md` (route F2′, step table W / D / Θ / J / C). It covers the
two self-contained steps **W** (Weil pairing) and **C** (genus-2 curves over `𝔽_q`). New files,
audited in `RamanujanWeil/Arith/DeuringG7WCAxioms.lean`:

| File | Imports | Content |
|---|---|---|
| `Arith/DeuringG7WeilAlg.lean` | G7FinAlg | alternating pairings on `(ℤ/N)²`: `e = s·det`, `s` a unit, anti-isometry ⟺ `det u = −s/s'`, Lagrangian graphs, automatic Frobenius compatibility `e(φx, φy) = q e(x, y)` |
| `Arith/DeuringG7WeilHeis.lean` | WeilAlg | the **commutator pairing of a central extension** (the theta-group construction of `e_N`), bi-additive, alternating, nondegenerate for Heisenberg groups, `ℤ/N`-valued via a discrete log on `μ_N` |
| `Arith/DeuringG7WeilCore.lean` | G7FinCore, WeilAlg, WeilHeis | `AltPairing`, **`AltPairing.ofCentralExt` / `ofTheta`** (theta group ⇒ `AltPairing`, common `ζ`), `antiIsom`, **`LagGraphFiniteness`** ⟺ `PolGraphFiniteness`; Frobenius compatibility on Frobenius Jacobians; `TateFinitenessLag(All)`, `mult_le_one_lag` |
| `Arith/DeuringG7Genus2Model.lean` | Stacks (0BY1, regular schemes) | hyperelliptic models, finiteness over `𝔽_q`, **genus-2 finiteness modulo the named model step `Genus2ModelExistence`** |
| `Arith/DeuringG7WCAxioms.lean` | all four | audit |

No existing file was edited. No `sorry`, `admit`, `native_decide` or `axiom`.

**Session 2 (2026-11-09, continuation).** The predecessor's four files were uncommitted. WeilAlg
and WeilHeis compiled. WeilCore failed on a docstring placed before `omit … in`. Genus2Model
failed because an imported `_root_.X : Type` shadows `Polynomial.X`, and because `HasHypModel`
lacked `[IsCurve K s]` (needed by `functionFieldAlgebra`). Both are fixed, `sum_coeff_eq` is
reproved via `Fin.sum_univ_eq_sum_range`, the theta-group bridge (`ofCentralExt`, `ofTheta`,
`sCoord_ofCentralExt`, `torsionLog`) is added to WeilCore, and the audit file is written.

## 0. Summary

* **W.** What the gluing argument consumes from a Weil pairing is now fully proved as algebra.
  The hypothesis `PolGraphFiniteness` (coordinates and a determinant class) is **equivalent** to the
  coordinate-free `LagGraphFiniteness ε ε'`: finiteness of the quotients of `E × E'` by π-stable
  graphs that are **Lagrangian** for `ε ⊕ ε'`. This is exactly the input of Mumford's descent
  (step D). The construction of `e_N` as the **commutator pairing of a central extension** is
  done at the group-theory level. Building the theta group `𝒢(𝒪(N[0]))` itself is the first half
  of step D and is not done here.
* **Key finding (scoping W).** The listed properties (alternating, bilinear, nondegenerate,
  `e(πP, πQ) = e(P, Q)^q`) do **not** determine `s_n/s'_n`:
  * every alternating pairing on `E[N] ≅ (ℤ/N)²` is `s·det`;
  * every alternating pairing is automatically π-compatible with factor `det π = q`
    (`IsAlt.map_map_eq_q`, `AltPairing.map_torAct`);
  * every unit class arises as `−s/s'` for some such pair (`exists_alt_of_det`);
  * `PolGraphFiniteness` holds iff `LagGraphFiniteness` holds for *some* alternating
    nondegenerate pair (`exists_lag_of_polGraphFiniteness`, `tateFinitenessLag_of_pol`).

  So the "determinant of the Frobenius-compatible basis" pairing is useless: it carries no
  information. The geometric content of W is *which* pairing it is, namely the one of the
  polarization. That pairing is the theta-group commutator pairing D must build anyway. **W's
  geometric part therefore merges into D.** The Stacks cup-product pairing
  (`Stacks.Picard.exists_weilPairing_of_twist`) is existential, has an unspecified root of unity
  per curve, and is not proved alternating. It cannot serve either.
* **C.** Proved: finiteness of hyperelliptic models over a finite field, and
  "same model ⇒ isomorphic curves" (via Stacks Tag 0BY1, `exists_iso_of_functionFieldEquiv`).
  Hence **finiteness of genus-2 curves over `𝔽_q` modulo one named Prop**,
  `Genus2ModelExistence` (the Riemann–Roch / canonical-map step). `C ≅ C' ⇒ Jac C ≅ Jac C'`
  equivariantly is **not** done (§3.2); it is not cheap with the present Stacks API.

## 1. W: what is proved

### 1.1 Algebra (`DeuringG7WeilAlg`, any `M ≃+ (ℤ/N)²`)

* `IsAlt.eq_sCoord_mul_cdet`: `e(x, y) = s · det(c x, c y)` with `s = e(b₀, b₁)`.
* `IsAlt.isUnit_sCoord`: `s` is a unit when `e` is nondegenerate.
* `IsAlt.apply_apply_eq`: `e'(u x, u y) = s'·det(u)·det(c x, c y)`.
* **`antiIsom_iff_det`**: `(∀ x y, e'(u x, u y) = −e(x, y)) ↔ det(c' ∘ u ∘ c⁻¹) = −s·s'⁻¹`.
* **`graph_isotropic_iff`**, **`eq_of_forall_graph_orth`**: `graph(u)` is isotropic for `e ⊕ e'`
  iff `u` is anti-isometric. It is then its own orthogonal, i.e. maximal isotropic. The proof
  uses nondegeneracy and needs no counting.
* **`IsAlt.map_map_eq_det`**, **`det_mat_eq_q`**, **`IsAlt.map_map_eq_q`**:
  `e(σx, σy) = det(σ)·e(x, y)`. If `φ² − tφ + q = 0` and `X² − tX + q` has no root mod `ℓ`, then
  `det φ = q` (via the companion form of `DeuringG7Alg`).
* `detPairing`, `exists_alt_of_det`: the converse ("no information in the class").

### 1.2 Construction of `e_N` (`DeuringG7WeilHeis`)

`CentralExt G K A` is a central extension `0 → A → G → K → 0`.

* `commVal g h ∈ A` is the commutator. It depends only on the images in `K` (`commVal_congr`).
* `commVal_mul_left` gives `[gg', h] = [g', h] + [g, h]`. Also `commVal_swap` and `commVal_self`.
* **`pairing : K →+ K →+ A`**, with **`pairing_self`** (alternating) and **`pairing_nondeg`**
  (when `Z(G) ⊆ A`, the Heisenberg property).
* **`zmodPairing`**, `zmodPairing_isAlt`, `zmodPairing_isNondeg`: for `N·K = 0` and an injective
  `χ : A[N] → ℤ/N`.
* `exists_injective_torsion_units_zmod`: `χ` on `(L^×)[N]` from a primitive `N`-th root of unity.

**Bridge (`DeuringG7WeilCore`, §Theta).** `AltPairing.ofCentralExt` packages a family of
Heisenberg extensions of `X[ℓⁿ⁺¹]` into an `AltPairing`; `AltPairing.ofTheta` does so with
`A = k^×` and the fixed discrete logs `torsionLog (hζ n)`. Applying `ofTheta` with **the same
`ζ : ℕ → k`** to `E` and to `E'` is the normalization step. `sCoord_ofCentralExt` is the scalar
`s_n`: the discrete log of the commutator of lifts of the two coordinate basis vectors. So the
scalars `s_n, s'_n` of the polarization route are *defined* here, as soon as D supplies the
theta groups.

**Usage in D.**
* `G = 𝒢(𝒪(N[0]))`, `K = E[N]`, `A = Additive k̄^×`.
* **The same `χ` (the same `ζ`) must be used for `E` and `E'`.** That is what makes `s/s'`
  meaningful, and it is automatic because both live over the same `k̄`.
* The resulting `AltPairing`s are the ones for which D proves `LagGraphFiniteness`. Mumford's
  criterion reads: a subgroup lifts to a level subgroup of `𝒢(L)` iff the commutator pairing
  vanishes on it.

### 1.3 Interface (`DeuringG7WeilCore`)

```lean
structure AltPairing (X) (ℓ) where
  e : ∀ n, Tor X (ℓ^(n+1)) →+ Tor X (ℓ^(n+1)) →+ ZMod (ℓ^(n+1))
  alt : ∀ n, IsAlt (e n)
  nondeg : ∀ n, IsNondeg (e n)
def antiIsom ε ε' n := {u | ∀ x y, ε'.e n (u x) (u y) = -ε.e n x y}
def LagGraphFiniteness π π' ℓ ε ε' : Prop := GraphFiniteness π π' ℓ (antiIsom ε ε')

theorem detClass_eq_antiIsom : detClass e e' (lagDet ε ε' e e') = antiIsom ε ε'
theorem polGraphFiniteness_of_lag : LagGraphFiniteness π π' ℓ ε ε' → PolGraphFiniteness π π' ℓ
theorem exists_lag_of_polGraphFiniteness : (coords) → PolGraphFiniteness π π' ℓ →
    ∃ ε ε', LagGraphFiniteness π π' ℓ ε ε'
noncomputable def AltPairing.ofCentralExt (G) (H : ∀ n, CentralExt (G n) (Tor X (ℓ^(n+1))) A)
    (hZ : Heisenberg) (χ : ∀ n, A[ℓ^(n+1)] →+ ZMod (ℓ^(n+1))) (hχ : injective) : AltPairing X ℓ
theorem sCoord_ofCentralExt : sCoord ((ofCentralExt ..).e n) c = χ n ⟨pairing (bas c 0) (bas c 1), _⟩
noncomputable def torsionLog (hζ : IsPrimitiveRoot ζ N) : (L^×)[N] →+ ZMod N   -- injective
noncomputable def AltPairing.ofTheta (ζ : ℕ → k) (hζ) (G) (H : … (Additive kˣ)) (hZ) : AltPairing X ℓ
theorem AltPairing.map_torAct (I : FrobeniusJacobian V) ... :
    ε.e n (torAct I.π _ x) (torAct I.π _ y) = q * ε.e n x y
def TateFinitenessLag K  -- ⟺ TateFinitenessPol K (tateFinitenessPol_of_lag / _lag_of_pol)
theorem mult_le_one_lag (h : TateFinitenessLagAll) ... : mult p n t ≤ 1
```

## 2. C: what is proved (`DeuringG7Genus2Model`)

* `HypModel K` is the coefficient vectors of `(h, f)`, `deg h ≤ 3`, `deg f ≤ 6`.
  * `exists_hypModel_eq`: every such pair of polynomials is a `HypModel`.
  * `finite_hypModel`: there are finitely many over a finite `K`.
* `HypModel.FunField m = AdjoinRoot (y² + h y − f)` over `K(x)`. `HasHypModel s` says the function
  field of `Y` is `K`-isomorphic to one of these.
* **`exists_iso_of_hypModel`**: two regular proper curves with the same model are isomorphic over
  `K` (Stacks 0BY1).
* **`exists_ne_iso_of_hasHypModel`**: in any sequence of regular proper curves over a finite field
  that have models, two are isomorphic over `K` (pigeonhole).
* **`exists_ne_iso_of_genus_eq_two`**: the same for smooth proper geometrically irreducible
  curves of genus 2, from the named
  ```lean
  def Genus2ModelExistence (K) : Prop :=
    ∀ Y (s : Y ⟶ Spec K) [IsCurve K s] [Smooth s] [IsProper s] [GeometricallyIrreducible s],
      genus s = 2 → HasHypModel s
  ```

## 3. Remaining named Props and estimates

| Item | Content | Estimate |
|---|---|---|
| **W-geom** (now part of D) | the theta group `𝒢(𝒪(N[0]))` on `E` as a `CentralExt` with `Z = k̄^×`. Feed it to `zmodPairing`; this gives `AltPairing`s for `J_W`, `J_{W'}` with a common `ζ`. | 1–2k, of which D's Heisenberg part already budgets most; D's 4–7k becomes ≈ 4–6.5k |
| **`Genus2ModelExistence`** | RR on a genus-2 curve: `h⁰(ω) = 2`, `\|ω\|` base point free of degree 2 (Stacks has RR pieces: `RiemannRochSection`, `LinearSeries*`, `DifferentialsDegreeGenus`, `RiemannHurwitz*`); `K(Y)/K(x)` quadratic; integral generator with pole bounds (`deg h ≤ 3`, `deg f ≤ 6`); char 2 included | 2.5–4k |
| **C-Jac** | `α : C' ≅ C` over `k̄`, `Ψ`-equivariant ⇒ `Pic⁰_C ≅ Pic⁰_{C'}` π-equivariantly. Stacks only has the endomorphism version (`jacobianPullback`, `jacobianFrobenius`, about 380 + 490 lines). A two-curve `pullback` along an isomorphism, the natural iso of Picard functors, preservation of `Pic⁰`, and the Frobenius square are needed. | 0.6–1.2k |
| **C-descent** | interface with J: either J descends `Θ_n` to a curve over `𝔽_q` (then C applies, and base change gives the `Ψ`-equivariant iso), or C is restated for pairs `(C/k̄, Ψ)` (models must then be chosen Frobenius-stable). The first route reuses `galoisBaseChange`, as G1 does for cubics. | 0.5–1k |

**Revised totals.**
* W is done here as ≈ 0.8k lines (algebra 303, commutator pairing 228, interface + theta bridge 290). What is left of W is D's theta
  group.
* C is done as ≈ 0.15k lines (153). The remaining C is 3.5–6k, larger than the 1.5–3k of the G7-fin table.
  * Riemann–Roch for the canonical system: the Stacks pieces exist but are not assembled into
    "`h⁰(ω) = g`, `ω` bpf of degree `2g − 2`" for curves over a field.
  * The two-curve Jacobian functoriality is missing from Stacks.
* The F2′ total of 15–25k stands.

## 4. Audit

The audit file is `RamanujanWeil/Arith/DeuringG7WCAxioms.lean`.

## 5. Audit result

`nice -n 10 lake build RamanujanWeil.Arith.DeuringG7WCAxioms` succeeds (2026-11-09), with no
errors. All 41 audited declarations depend only on `[propext, Classical.choice, Quot.sound]`;
two of them (`IsAlt.swap`, `graph_isotropic_iff`) use only
`[propext, Quot.sound]`. There is no `sorry`, `admit`, `native_decide` or `axiom` in the five
files. Sizes: WeilAlg 303, WeilHeis 228, WeilCore 290, Genus2Model 153, WCAxioms 54 lines.
