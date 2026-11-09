# A3-ord: ordinary Deuring–Waterhouse, blueprint and status

> **Status 2026-11-09:** superseded in part. Exact Deuring is no longer needed (docs/ARITH_DEURING_APPROX.md); the current frontier and open named Props (`TateFinitenessPolAll`, `RadicialDual`, `DeuringClassLatticeAll`) are listed in README.md. Progress: ARITH_DEURING_G1*, G5, G6, G7, G7FIN, G8, MULT.


Target (frozen, `RamanujanWeil/Arith/AssemblyVocab.lean`): `OrdinaryDeuring hurwitz p` for every
prime `p`, i.e. for `q = pⁿ`, `n ≥ 1`, `p ∤ t`:

```
traceCount p n t = q³(q − 1) · (if t² < 4q then H(4q − t²) else 0) / 2 .
```

## 0. Summary

* **Route chosen: lattice / Latimer–MacDuffee (Deligne-shaped).** The isomorphism classes of
  ordinary `E/𝔽_q` with trace `t` correspond, with automorphism groups, to the
  `ℤ[π]`-lattices `L(E) = Hom(E₀, E)` (`E₀` a curve with `End E₀ = ℤ[π]`). These lattices are the
  `GL₂(ℤ)`-conjugacy classes of integer matrices with trace `t` and determinant `q`, and those
  correspond to `SL₂(ℤ)`-classes of positive definite forms of discriminant `t² − 4q`, which is
  exactly what `hurwitzOrbit` counts. The ideal classes of orders are never introduced: no
  `Pic(O)`, no `h(O)/w(O)`, no forms ↔ ideals of non-maximal orders.
* **Proved this session, axiom-clean** (`propext, Classical.choice, Quot.sound`; no
  `sorry`/`admit`/`native_decide`/`axiom`; Mathlib plus the repo's A1/A4 files only):
  * **D-ALG** `Arith/DeuringMatrix.lean` (374 lines): `matMass_eq_hurwitz`. For `t² < 4q`,
    `Σ_{GL₂(ℤ)-classes of M, tr M = t, det M = q} 1/#C_{GL₂(ℤ)}(M) = H(4q − t²)/2`.
  * **D-ASM** `Arith/DeuringAssembly.lean` (190 lines): `ordinaryDeuring_of_lattice`.
    `HasseAll p` plus a `DeuringLattice (GaloisField p n) t` for every `n ≥ 1`, `p ∤ t`,
    `t² < 4pⁿ` gives `OrdinaryDeuring hurwitz p`. This uses A4 `sum_trace_eq_sum_orbits` and
    D-ALG. `HasseAll` is already unconditional in the repo (`Ihara/HasseAll.lean`).
  * Audit: `Arith/DeuringAxioms.lean`.
* **What remains is geometry only:** constructing `DeuringLattice K t`, the frozen interface
  below. Honest size is **28–65k lines**.
* **Hardest lemma: Tate's isogeny theorem for elliptic curves over `𝔽_q`** (`ℓ ≠ p`):
  `Hom(E, E') ⊗ ℤ_ℓ ≅ Hom_π(T_ℓE, T_ℓE')`, and in particular "equal trace ⇒ isogenous".
  Neither Stacks nor Weil has it, and neither has the two tools its proof needs: quotients of
  abelian varieties by finite subgroup schemes, and a finiteness statement for the quotients
  (§4). §3 explains why no counting trick avoids it.

## 1. The frozen geometric interface (Lean, `Arith/DeuringAssembly.lean`)

```lean
structure DeuringLattice (K : Type*) [Field K] [Finite K] (t : ℤ) where
  Λ : WeierstrassCurve K → TrDet t (Nat.card K)          -- matrix of π on a ℤ-basis of L(E)
  rel_iff : ∀ W W', W.Δ ≠ 0 → traceOfFrob W = t → W'.Δ ≠ 0 → traceOfFrob W' = t →
    (W' ∈ orbit (VariableChange K) W ↔ ∃ g : GL2, g • Λ W = Λ W')
  card_stab : ∀ W, W.Δ ≠ 0 → traceOfFrob W = t →
    Nat.card (stabilizer (VariableChange K) W) = Nat.card (stabilizer GL2 (Λ W))
  surj : ∀ M : TrDet t (Nat.card K), ∃ W, W.Δ ≠ 0 ∧ traceOfFrob W = t ∧ ∃ g : GL2, g • Λ W = M

theorem ordinaryDeuring_of_lattice (p) [Fact p.Prime] (hH : HasseAll p)
    (D : ∀ n, 1 ≤ n → ∀ t : ℤ, ¬ (p : ℤ) ∣ t → t ^ 2 < 4 * (p : ℤ) ^ n →
      DeuringLattice (GaloisField p n) t) : OrdinaryDeuring hurwitz p
```

`TrDet t q = {M : Matrix (Fin 2) (Fin 2) ℤ // trace = t ∧ det = q}`, and
`GL2 = (Matrix (Fin 2) (Fin 2) ℤ)ˣ` acts by `g • M = g M g⁻¹`. The interface is stated with
`VariableChange`-orbits and stabilizers, as in A4, so the geometric side has to identify
`Stab_G(W)` with `Aut(E)` (G1 below).

## 2. Inventory (what exists, with paths)

### Mathlib (`.lake/packages/mathlib/Mathlib`)

| Topic | Declarations | Use |
|---|---|---|
| Weierstrass curves | `AlgebraicGeometry/EllipticCurve/{Weierstrass,VariableChange,Affine/*,Jacobian/*,Projective/*}`: `WeierstrassCurve`, `VariableChange` + `MulAction`, `Affine.Point` group law, `baseChange`, `j` | objects, isomorphisms |
| Isomorphism by `j` | `IsomOfJ.lean`: `exists_variableChange_of_j_eq` (over sep. closed) | twists (not needed) |
| Division polynomials | `DivisionPolynomial/{Basic,Degree}` (`Ψ`, `Φ`, `ΨSq`) | Vélu / torsion (G6) |
| **Isogenies, End(E), Frobenius endomorphism, Tate modules** | **none** | — |
| Class groups | `RingTheory/ClassGroup/Basic.lean`: `ClassGroup R` for **any domain** = invertible fractional ideals / principal = `Pic(O)` for orders; `NumberField/ClassNumber.lean` `classNumber` (maximal orders only) | not needed by the chosen route |
| Orders, conductor | `Algebra/QuadraticAlgebra/*` (`ℤ[π] = QuadraticAlgebra ℤ (−q) t`), `RingTheory/Conductor.lean` (`conductor R x`), `NumberTheory/Zsqrtd` | G8 bookkeeping |
| Forms ↔ ideals of orders, Latimer–MacDuffee | **none** | done here as D-ALG (matrices ↔ forms) |
| Matrix conjugation | `Matrix.trace_units_conj`, `Matrix.det_units_conj`, `isUnits_det_units` | D-ALG |

### Stacks (`.lake/packages/Stacks/StacksFrontier/AlgebraicGeometry`)

Abelian varieties are group objects `A : Over (Spec k)`, `[GrpObj A]`, `IsAbelianVariety k A`.
Homomorphisms are `α : A ⟶ B` with `[IsMonHom α]`.

| Topic | File : declarations | Status for us |
|---|---|---|
| Degree of endomorphisms | `GroupScheme/AbelianVariety/EndomorphismDegree.lean`: `endDegree`, `endDegree_comp`, `endDegree_zpow` | **End only**; no degree for `A ⟶ B` |
| Char. poly of endomorphisms | `.../CharPoly.lean`: `endCharPoly`, `abelianVarietyTrace`, `charpoly_tateModuleMap` (ℓ ∤ char), `endDegree_eq_det_tateModuleMap`, `trace_tateModuleMap_eq_abelianVarietyTrace` | have |
| Norm form, `ℤ[X]`-evaluation in End | `.../EndomorphismNormForm.lean`: `postcompSubring`, `endPolyEval`, `exists_endDegree_endPolyEval_eq_normForm` | have |
| Kernel counts | `.../EndomorphismKernelCount.lean`: `natCard_comp_eq_one_eq_endDegree_of_etaleAt_unit`, `natCard_comp_endPolyEval_eq_one_eq_endDegree_of_charP`; `.../IsogenyKernelCount.lean`: `natCard_comp_eq_one_eq_endDegree` | have (End only) |
| Tate modules | `.../TateModule.lean`: `tateModule A ℓ`, `tateModuleMap` (functorial in `A ⟶ B`), `module_free_tateModule`, `finrank_tateModule` (= 2g, ℓ unit) | have |
| Torsion | `.../Torsion*.lean`, `.../TorsionPoints.lean`: `nonempty_torsionBy_addEquiv_of_isUnit` ((ℤ/n)^{2g}), `exists_torsionBy_char_pow_addEquiv`, `torsionScheme`, `etale_torsionScheme_hom_iff_isUnit`; `[n]` finite locally free of rank `n^{2g}` (`isFiniteLocallyFreeOfRank_zpow_id_left_of_ne_zero`), surjective | have |
| Jacobian | `PicardScheme/CurvePicard/Jacobian.lean`: `jacobianGrp`, `isAbelianVariety_jacobian`; `JacobianPullback.lean`: `jacobianPullback`; `JacobianTrace.lean`: `trace_tateModuleMap_jacobianPullback`; `JacobianPointGroup.lean`: `jacobianFieldPointsAddEquiv` | have |
| Frobenius on Jacobian | `JacobianFrobenius.lean`: `twistedJacobianHom`, `isMonHom_twistedJacobianHom`; `Curves/ZetaFunction/FrobeniusKernelCount.lean`: `exists_normForm_natCard_ker_twistedFrobenius` | have (gives `#ker R(π) = normForm χ R`) |
| Abel map | `Picard/AbelMap*.lean`, `Picard/Jacobian/AbelianVariety/AbelMap.lean` | partial (genus-1 isomorphism not stated) |
| Weierstrass cubic as a scheme | `Stacks/Weierstrass*.lean`: `projOf W`, `projectionOf`, `zeroOf`; `WeierstrassCubicIsoAction.lean` (`exists_zChartHom_affX/affY`: a pointed isomorphism of cubics acts by `x ↦ u²x + r`, `y ↦ u³y + sx + t`); `WeierstrassCoordinateChangeTorsor.lean` (`representsComparisons_coordinateChange`) | have: pointed isos of cubics = coordinate changes |
| Weil pairing (abstract) | `Picard/WeilPairing.lean` | partial |
| **Quotient `A/G` by a finite subgroup scheme, dual isogeny, Hom(A,B) finite generation / injectivity into Hom(T_ℓ), Tate's theorem, p-divisible groups, Dieudonné, Serre–Tate, canonical lifts, CM theory, Deligne's equivalence** | **none** (grep: 0 hits; "Isogeny" files are about ℓ-adic *coefficient* isogenies; "canonicalLift" is unrelated deformation theory) | to build |

### Weil (`.lake/packages/Weil/Weil`)

Étale cohomology, duality and trace infrastructure (Weil II). There is nothing on isogenies,
abelian-variety quotients or CM.

### Repo

`Arith/TorsorCount.lean` (A4, `sum_trace_eq_sum_orbits`), `Arith/Hurwitz{Basic,Reduction,Orbit}.lean`
(`hurwitz_eq_hurwitzOrbit`, `card_stabilizer_smul`), `Arith/HurwitzPrimeSquare*.lean`,
`Arith/SupersingularTrace.lean`, `Ihara/CurveH1Weierstrass.lean` (`charpoly_weierstrassH1`:
`charpoly(Frob | H¹(E_k̄, ℚ_ℓ)) = X² − aX + q` for `E = projOf W`), and `Ihara/HasseAll.lean`
(`hasseAll`).

## 3. Routes compared

| Route | Algebraic end | Geometric core | Verdict |
|---|---|---|---|
| **L (chosen)**: `L(E) = Hom(E₀, E)`, `End E₀ = ℤ[π]`; lattices ↔ matrices ↔ forms | D-ALG (done, 0.4k) | Tate ℓ ≠ p, Frobenius factorization at p, quotients by étale subgroups, existence of `E₀` | cheapest end. For one isogeny class this is Jordan–Keeton–Poonen–Rains–Shepherd-Barron–Tate (2018), Thm 1.1, in rank 1 |
| W: Waterhouse Thm 4.5, `Pic(O)` torsors, `Σ_O h(O)/w(O)` | forms ↔ invertible ideals of **non-maximal** orders, `w(O) = #Stab`, `Σ_{f²∣D}`. Mathlib has `ClassGroup` but no Gauss correspondence (+3–6k) | same as L, plus kernel ideals `E[𝔞]` and the free/transitive action | dominated by L |
| D: Deligne (canonical lift, `H₁` of lift) | as L | Serre–Tate, canonical lifts, comparison over ℂ | far larger |
| C: Deuring lifting + CM over ℂ | `Pic(O)` | analytic CM theory, class field theory, reduction | far larger |
| X: counting without isogenies | — | — | **fails**. One identity `Σ_t N(t) = #elliptic` cannot rule out a trace with two isogeny classes compensating a missing trace. Every route needs the global integral structure `Hom(E, E')`, i.e. Tate (existence of an isogeny for equal traces) |

**Approximate fallback (only for `IharaApprox`).** Dropping "every lattice is realized" (G8(iii))
still works for the endgame. Use injectivity, the matching of `Aut`, and Tate's existence. Then
`N(t) ≤ M(t)` for every ordinary `t`, and
`Σ_t (M(t) − N(t)) = q³(q−1)(Σ_{p∤t} H(4q−t²)/2 − q) + #SS + #singular − q⁴ = O_p(q⁴)`, which
yields an `O(q⁹)` error in the weighted sum. Numerics N6: `q − Σ_{p∤t} H(4q−t²)/2` is exactly the
number of supersingular `j ∈ 𝔽_q` (1, 1, 1, 1, 2 for p = 2, 3, 5, 7, 11, constant in n). Proving
that bound needs Kronecker–Hurwitz at `pⁿ` with `HurwitzPrimeSquare`, which is not available.
The fallback saves G8(iii) and the existence of `E₀` (part of G6), but not Tate. Not
recommended unless G8(iii) stalls.

## 4. Blueprint for `DeuringLattice` (route L, framework = Stacks group objects)

**Framework decision.** Use the Stacks abelian-variety layer, not hand-made rational maps. It
already supplies Tate modules (ℓ ≠ p, free of rank 2g, functorial for `A ⟶ B`), char. polys and
degrees of endomorphisms, `[n]` finite locally free and surjective, `A[n] ≅ (ℤ/n)²` (p ∤ n), and
the Frobenius endomorphism of a Jacobian with kernel counts. In the Mathlib-points framework all
of that is 8–15k by itself. Objects: for an elliptic `W` over `K = 𝔽_q`, set `C_W = projOf W` and
`A_W = jacobianGrp C_W` (dimension 1). Isogenies: `Hom(W, W') = {α : A_W ⟶ A_W' // IsMonHom α}`.
Practical cost: each Stacks module build needs one Lean process at a time and can exceed 6 GB.

| # | Lemma (statement) | Proof sketch / reuse | Lines | Risk |
|---|---|---|---|---|
| G1 | **Weierstrass ↔ group object.** (a) genus 1: the Abel map `C_W → A_W`, `P ↦ [P − O]`, is an isomorphism of pointed schemes; (b) `W' ∈ G • W ⟺ A_W ≅ A_W'` as group objects; (c) `Stab_G(W) ≃* Aut_Grp(A_W)` | (a) Stacks Abel-map files + RR on genus 1 (`h⁰(O(P−O)) = 0`, P ≠ O); (b,c) pointed isos of cubics = coordinate changes (`WeierstrassCubicIsoAction`, `representsComparisons_coordinateChange`), every iso of group objects is pointed, `jacobianPullback` functoriality | 3–6k | medium |
| G2 | **Frobenius.** `π_W := twistedJacobianHom`, `IsMonHom`, commutes with every `α : A_W ⟶ A_W'`, and `π² − tπ + q = 0` in `End(A_W)` with `t = traceOfFrob W` | charpoly on `T_ℓ` = `X² − tX + q` (`charpoly_tateModuleMap` + `exists_normForm_natCard_ker_twistedFrobenius` + `#A_W(𝔽_q) = #W(𝔽_q)` via G1(a)), then Cayley–Hamilton on `T_ℓ` + G3 injectivity | 1–3k | low–med |
| G3 | **Hom is a lattice.** For `α : A ⟶ B`: `α` kills `A[n]` ⇒ `α = n·β` (every n ≠ 0, incl. p). Hence `Hom(A,B) → Hom_{ℤ_ℓ}(T_ℓA, T_ℓB)` is injective with torsion-free cokernel, and `Hom(A,B)` is free of rank ≤ 4 | `[n]` is finite locally free and surjective (Stacks), hence an fppf epimorphism. Factor `α` by fppf descent of morphisms, then Mumford §19 Thm 3 | 3–6k | medium |
| G4 | **Degree on Hom.** `deg : Hom(A,B) → ℕ` multiplicative, `deg(nα) = n²deg α`; for dim 1 `deg = det(T_ℓ α)` is a positive definite quadratic form; hence `Hom(A,B) ⊗ ℚ` is 0 or 1-dim over `K = ℚ(π)` and `End(A)` is an order containing `ℤ[π]` when p ∤ t | `endDegree` on `A × B`, or `det(T_ℓ α)` composed with a dual; `endDegree_eq_det_tateModuleMap` | 1–3k | low–med |
| G5 | **p-part (ordinary).** For p ∤ t: `ℤ[π] ⊗ ℤ_p ≅ ℤ_p × ℤ_p` (Hensel), and `α ∈ Hom(A,B)` with `α ∘ Hom(A₀,A) ⊆ p·Hom(A₀,B)` is divisible by p | G3 with n = p; `A[p]` is generated by the images of `A₀[p]` under `Hom(A₀,A)` (ordinary: étale and multiplicative parts) | 2–4k | medium |
| G6 | **Quotients by finite étale subgroups.** For `G ⊆ A[m]` (p ∤ m) a `π`-stable subgroup there are `A/G` (an elliptic curve over `𝔽_q`) and `A → A/G` with kernel exactly `G` | either Vélu (explicit general-Weierstrass formulas, all characteristics) plus showing the map is a group hom on `A_W` via G1, or a quotient of `A_k̄` by the finite group of translations followed by Galois descent. Neither is in Stacks | 5–12k | **high** |
| G7 | **Tate's theorem, ℓ ≠ p (HARDEST).** `Hom(A,B) ⊗ ℤ_ℓ ≅ Hom_π(T_ℓA, T_ℓB)`. In particular equal traces give `Hom(A,B) ≠ 0` | Tate's argument on `A × B` for a `π`-stable `W ⊆ V_ℓ(A×B)`. Needs G6 for **abelian surfaces** (quotient of `A×B` by `G_n`) and finiteness of `{(A×B)/G_n}/≅`: principally polarized surfaces over `𝔽_q` are Jacobians of genus 2 or products, hence finitely many (Weil's theorem), or a direct bounded-equation argument | 10–25k | **very high** |
| G8 | **Lattice functor.** Existence of `E₀` with `End = ℤ[π]` (descend along ℓ-isogenies, G6). `L(E) := Hom(A₀, A_E)`, with `ℤ[π]` acting through `π_{A₀}`: (i) a rank-2 lattice (G3, G4, G7 existence); (ii) `Hom(E,E') ≅ Hom_{ℤ[π]}(L E, L E')` (G7 at ℓ ≠ p, G5 at p, then local-global for lattices); (iii) every `ℤ[π]`-lattice occurs: rescale so that `L_p = ℤ[π]_p` (two primes over p, weak approximation), then `L ⊇ ℤ[π]` has index prime to p and `L = L(E₀/G)` with `G = L/ℤ[π] ⊆ E₀[m]` (G6) | 4–8k | medium–high |
| G9 | **Package `DeuringLattice`.** `Λ(W)` = matrix of `π` in a ℤ-basis of `L(E_W)`; `rel_iff` from G1(b) + G8(ii); `card_stab` from G1(c) + G8(ii) (`Aut_Grp(A) = Aut_{ℤ[π]}(L) = Stab_{GL₂}(Λ)`); `surj` from G8(iii) | linear algebra | 0.5–1k | low |
| — | (done) D-ALG + D-ASM | — | 0.56k | — |

**Total remaining: 28–65k.** The critical path is G6 → G7. G1–G5 are mostly assembly of Stacks
facts and can proceed in parallel. G7 is "very high" risk because its proof needs either
quotients of *surfaces* together with a finiteness theorem for (polarized) abelian surfaces over
`𝔽_q`, or a replacement for both. Neither exists. Stacks has `KeelMori` coarse spaces and
`WellNighAffine` moduli, but nothing usable off the shelf. If G7 is too costly, the only known
alternative is CM lifting (route C), which is larger.

**Sub-milestone order (each axiom-clean, frozen statement first):** G2 (`π² − tπ + q = 0` on
`A_W`; Stacks-only) → G3 → G4 → G1 → G5 → G6 → G7 → G8 → G9. G2–G4 do not depend on G6/G7 and
de-risk the framework.

## 5. Algebraic details of D-ALG (proved)

* `formOfMat M = (c, d − a, −b)` for `M = [[a,b],[c,d]]`. Then `f_M(v) = det(v, Mv)` and
  `disc f_M = tr² − 4 det` (`disc_formOfMat`). Its inverse on forms is
  `psi f = [[(t−b)/2, −c], [a, (t−b)/2 + b]]`; `t ≡ b (mod 2)` is `two_dvd_sub`.
* Equivariance `psi_smul`: `psi(γ • f) = θ(γ) · psi(f) · θ(γ)⁻¹` with `θ(γ) = (γᵀ)⁻¹`. This is a
  pure ring identity; no determinant is needed.
* Orientation `det_eq_one_of_conj`: if `g M g⁻¹ = M'` with both lower-left entries positive, then
  `4c · c' · det g = (2cs + (a−d)r)² + (4q − t²)r² > 0`, so `det g = 1`. In particular
  `C_{GL₂(ℤ)}(psi f) = θ(Stab_{SL₂(ℤ)} f)` (`card_stabilizer_psi`).
* `classMap_bijective`: `SL₂(ℤ)\Form N ≃ GL₂(ℤ)\TrDet t q`. For surjectivity, every `M` has
  `c ≠ 0` (`entry10_ne_zero`), and `diag(1,−1)` flips the sign of `c`. Then
  `matMass_eq_hurwitzOrbit` and `matMass_eq_hurwitz` follow via `hurwitz_eq_hurwitzOrbit`.

## 6. Numerical verification (PARI, `nbthreads = 1`)

Scripts and outputs are in the session scratchpad, `deuring/` (full paths in the session report).

| Script | Check | Range | Result |
|---|---|---|---|
| `n1_mass.gp` | N3: `H(N) = Σ_{f²∣D} 2h(D/f²)/w(D/f²)` against the reduced-form count; N1: `#{(a,b) : a_E = t}/(q−1) = H(4q−t²)/2` for p ∤ t (short Weierstrass) | N ≤ 400; q ∈ {5,…,37, 25, 49, 125} | all OK |
| `n4_endorder.gp` | **Waterhouse per order**: `End(E)` conductor via Kohel's criterion (`π` scalar on `E[m]`, computed from division-polynomial roots). For every `(t, O ⊇ ℤ[π])`: `Σ_{End E = O} 1/#Aut = h(O)/w(O)`, and every order occurs | p ≤ 53, all t with `f_π > 1` | 0 mismatches, 0 missing |
| `n5_groupstructure.gp` | **Lattice functor**: `E(𝔽_p) ≅ ℤ²/(M − 1)ℤ²`. The mass-weighted distributions of group structures over curves and over matrix classes `psi(f)` agree (this tests the p-part too) | p ≤ 73, all ordinary t | 0 mismatches |
| `n6_ordsum.gp` | `q − Σ_{p∤t} H(4q−t²)/2` (approximate fallback, §3) | p ≤ 11, n ≤ 9 | = #supersingular j in 𝔽_q, constant in n |

## 7. Files

| File | Content |
|---|---|
| `RamanujanWeil/Arith/DeuringMatrix.lean` | D-ALG: `TrDet`, `GL2` conjugation action, `matMass`, `formOfMat`, `psi`, `theta`, `det_eq_one_of_conj`, `classMap_bijective`, `matMass_eq_hurwitzOrbit`, `matMass_eq_hurwitz` |
| `RamanujanWeil/Arith/DeuringAssembly.lean` | D-ASM: `DeuringLattice`, `Locus`, `locusMap_bijective`, `orbitMass_eq_matMass`, `card_trace_eq_mass`, `ordinaryDeuring_of_lattice` |
| `RamanujanWeil/Arith/DeuringAxioms.lean` | `#print axioms` for the headline results |

Build: `nice -n 10 lake build RamanujanWeil.Arith.DeuringAssembly`. It needs the prebuilt A1/A4
oleans and `AssemblyVocab` (which imports `IharaStatement`), and each file elaborates in about
10 s. The files are not yet imported from `RamanujanWeil.lean`, because existing files were not
edited.
