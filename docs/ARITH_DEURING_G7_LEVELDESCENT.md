# A3-ord, G7: `ThetaLevelDescent` reduced to module descent and ample descent (2026-11-10)

> **Update, 2026-11-10:** [ample descent](ARITH_DEURING_G7_AMPLE.md) discharges
> `GlueAmpleDescent` using Stacks 0B5V, which is present in the pinned dependency.
> This corrects the earlier claim that the theorem was absent.
> `LevelSectionDescent` remains the module/section obligation.

This continues `ARITH_DEURING_G7DGEOM.md` §5 (the seam `ThetaLevelDescent`), `ARITH_DEURING_G7D.md`
§1 (the algebraic half of Mumford's descent) and `ARITH_DEURING_G7_PRINCIPAL.md` (finding 2,
Frobenius compatibility). New files only:

| File | Imports | Content |
|---|---|---|
| `Arith/DeuringG7LevelDescentRep.lean` | DGeomTheta, DAlg, Mathlib | the exact dimension count; `thetaRep` on `L(N·O)`; `dim L(N·O) = N`; `levelRep` on `L(N·O) ⊗ L(N·O)'`; **`finrank_thetaLevelRep_invariants_eq_one`** |
| `Arith/DeuringG7LevelDescent.lean` | DGeomFamily, Rep | `finrank_famInv_eq_one` for the constructed families; the named Props **`LevelSectionDescent`**, **`GlueAmpleDescent`**; `ThetaLevelDescentGood`; the Ψ variants; the reductions down to Deligne |
| `Arith/DeuringG7LevelDescentAxioms.lean` | | audit |

```lean
theorem thetaLevelDescentGood_of_levelSectionDescent (hD : LevelSectionDescent K)
    (hA : GlueAmpleDescent) : ThetaLevelDescentGood K
theorem thetaDescentFiniteness_of_split' (hG : DGeomGapsAll K) (hD : ThetaLevelDescentGood K)
    (hP : PrincipalFiniteness K) : ThetaDescentFiniteness K
theorem deligneBound_of_levelDescent (h : LevelDescentSplitAll) : RamanujanTau.DeligneBound
theorem thetaLevelDescentΨ_of_levelSectionDescentΨ (hD : LevelSectionDescentΨ K)
    (hA : GlueAmpleDescent) : ThetaLevelDescentΨ K
theorem thetaDescentFiniteness_of_splitΨ (hG : DGeomGapsAll K) (hD : ThetaLevelDescentΨ K)
    (hP : PrincipalFiniteness K) : ThetaDescentFiniteness K
```

## 0. Summary and two findings about the seam

Of the five items of the descent (linearization, descent of modules, `h⁰`, ampleness, the bridge
from the function-field theta group to modules), **item 3 is proved exactly**, as a statement about
the *constructed* theta groups: the level subgroup `Γ̃_n` acting on
`L(N·O) ⊗ L(N·O)' = H⁰(E × E', L ⊠ L')` has a **one-dimensional** space of invariants. Items 1, 2
and 5 are one named Prop (`LevelSectionDescent`), whose output is an invertible `L_n` on `B_n` with
`H⁰(B_n, L_n) ≅` those invariants. Item 4 is a second, general named Prop (`GlueAmpleDescent`,
Stacks 0B5V for the G6 quotient). From these two, `h⁰(L_n) = 1` and ampleness are derived, and
the chain runs to `ThetaDescentFiniteness` and Deligne.

**Finding 1: `ThetaLevelDescent` over-quantifies `ℓ`.** The original seam is stated for every
`ℓ` with `DGeomGaps W S ℓ`, with no primality or invertibility hypothesis. For `ℓ = p` and `E`
supersingular, `E(k̄)[pⁿ] = 0`, so `Γ_n = 0`, `B_n = J × J'` and the descended bundle would be
`L ⊠ L'` with `h⁰ = N² ≠ 1`: the Mumford mechanism gives nothing there (`B_n` is still principally
polarized, but by `𝒪(O) ⊠ 𝒪(O')`, not by descent). The downstream
(`thetaDescentFiniteness_of_split`) only uses the seam at odd primes `ℓ` invertible in `k̄`. So the
reduction targets **`ThetaLevelDescentGood`**, the seam at those primes;
`thetaLevelDescentGood_of_thetaLevelDescent` shows it is weaker than the original, and
`thetaDescentFiniteness_of_split'` / `deligneBound_of_levelDescent` re-run the downstream wiring
with it. Nothing downstream needs the original.

**Finding 2: item 5 (the bridge) can only be partly bypassed.** The `h⁰` computation is done on
the function-field side, where the constructed `𝒢(L)` *already acts* on `V = L(N·O)` by
`(f, P) · v = f · τ_P(v)` (`thetaGroup` is by definition the stabilizer of `V`). No module on
`J × J'` is needed for it. What cannot be bypassed is the identification
`H⁰(J × J', L ⊠ L') = V ⊗ V'` *together with the theta-group action*. That identification is part
of `LevelSectionDescent`, since without equivariant structures on `X.Modules` (absent from Stacks
and Mathlib, `ARITH_DEURING_G7D.md` §0) the linearization cannot even be stated on modules.

## 1. The exact dimension count (`DeuringG7LevelDescentRep`, fully proved)

**`finrank_eq_card_mul_finrank_invariants`.** The setup:

* `s : Representation k (Multiplicative K) W`, with `K` finite abelian, `W` finite-dimensional, and
  `#K ≠ 0` in `k`;
* `χ : K → K → k^×`, a bicharacter that is nondegenerate on both sides;
* units `g_y` with `g_y s(x) = χ(y, x) s(x) g_y`.

Then **`dim W = #K · dim W^K`, in `ℕ`**.

* The trace argument (`dim W^K = #K⁻¹ Σ tr s(x)`) gives this only in `k`, i.e. modulo `char k`.
  So the proof uses projectors instead.
* `P_y = #K⁻¹ Σₓ χ(y, x)⁻¹ s(x)`:
  * `s(x') P_y = χ(y, x') P_y` (`s_mul_isoProj`);
  * `P_y P_{y'} = δ P_{y'}`, by vanishing of nontrivial character sums (`sum_hom_units_eq_zero`);
  * `Σ P_y = 1` (`sum_isoProj`);
  * `g_y P_z = P_{z−y} g_y` (`g_mul_isoProj`).
* `range P_0 = W^K` (`range_isoProj_zero`).
* The maps `w ↦ (g_y P_y w)_y` and `(w_y) ↦ Σ g_y⁻¹ w_y` are inverse, so `W ≅ (W^K)^K`
  (`nonempty_linearEquiv_pi`).

**`levelRep`.** Take `ρ : G → End V` and `ρ' : G' → End V'` on which both kernels act by one
character `χ`. A `GraphLevel X X' u` then gives `x ↦ ρ(σ x) ⊗ ρ'(σ' x)`, a genuine representation:
the defects `c` and `−c` cancel (`levelMap_add`, `levelMap_zero`).

* `g_y = ρ(lift y) ⊗ 1` conjugates it by `χ(e(y, x))` (`leftUnit_mul_levelRep`, from
  `comm_eq_ι` / `pairing_eq`).
* **`finrank_levelRep_invariants`**: `dim V · dim V' = #K · dim (V ⊗ V')^{Γ̃}` when `X` is
  Heisenberg (`pairing_nondeg`) and `χ` is injective. Nondegeneracy in the second variable comes
  from `commVal_swap`.

**The theta group on `L(N·O)`.**

* `thetaRep` is the action of `𝒢(V)` on `V`. `thetaRep_scalar` says the kernel `F^×` acts by
  scalars.
* **`finrank_rrSpace`**: `dim L(N·O) = N` for `N ≥ 1`. The family `xⁱ` (`i ≤ N/2`), `xʲy`
  (`j < (N−1)/2`) spans `rrSpace` (`range_rrFam`). It is linearly independent
  (`linearIndependent_rrFam`): `Σ aᵢxⁱ + (Σ bⱼxʲ)y = 0` in `F(E)` pulls back to `p · 1 + q · Y = 0`
  in `F[E]`, and Mathlib's `smul_basis_eq_zero` gives `p = q = 0`.
* **`finrank_thetaLevelRep_invariants_eq_one`**: suppose the extensions have scalar kernels
  (`IsScalarKernel`), `#K = N²`, `N ≠ 0` in `F`, and `X` is Heisenberg. Then
  `N · N = N² · dim(inv)`, so `dim(inv) = 1`.

## 2. The constructed families and the seams (`DeuringG7LevelDescent`)

* `isScalarKernel_thetaFamilyOf` is `rfl`: `thetaFamilyOf`'s `ι` is `thetaScalar`, unchanged by
  `transport`.
* `card_tor_J` gives `#J_W[N] = N²`, from `natCard_tor` and `dim_J`.
* **`finrank_famInv_eq_one`**: for `ℓ` prime and invertible in `k̄`, and any level structure `L_n`
  on the constructed families, `dim (L(N·O) ⊗ L(N·O)')^{Γ̃_n} = 1`. The Heisenberg input is
  `(thetaFamilyOf W S h).hZ n`, i.e. `ThetaHeisenberg` inside `DGeomGaps`.

**`LevelSectionDescent K`** (named: items 1, 2, 5). Fix:

* odd primes `ℓ` invertible in `k̄`;
* `DGeomGaps` for both curves, and any `v`;
* a level structure `L_n`;
* a G6 quotient `G : Glue (Γ ℓ v n)`.

Then there is an invertible `M` on `B_n` with `q_n^*M` invertible and ample on `J × J'`, and
`Γ(B_n, M) ≃ₗ[k̄] famInv h h' v n L_n`.

Mathematically, `M = L_n` is the Mumford descent of `L ⊠ L'`:
* the level subgroup is a `Γ_n`-linearization (Mumford §23 Thm 1);
* fpqc descent of quasi-coherent modules along the finite locally free surjective `q_n` is
  **proved in Stacks** (023T: `QuasicoherentDescentData.isEffective_fpqcPrecoverage`,
  `nonempty_fullyFaithful_canonicalDescentFunctor'`);
* `H⁰(B, L_B) = H⁰(A, L ⊠ L')^{Γ̃}`;
* `H⁰(J × J', L ⊠ L') ≅ L(N·O) ⊗ L(N·O)'`, equivariantly.

**`GlueAmpleDescent`** (named: item 4). For a G6 quotient `q : A → B` of an abelian variety over
`k = k̄`, an invertible `M` on `B` with `q^*M` ample is ample. This is Stacks 0B5V / Hartshorne
III Ex. 5.7(d) for the finite surjective `q`. It is available at this pin as `Stacks.AmpleFiniteSurjective.isAmple_iff_isAmple_modulePullback`
and is applied in `DeuringG7AmpleDescent.lean`.

**Proved reductions:**

* `thetaLevelDescentGood_of_levelSectionDescent`:
  `LevelSectionDescent ∧ GlueAmpleDescent ⇒ ThetaLevelDescentGood`.
* `thetaDescentFiniteness_of_split'`:
  `DGeomGapsAll ∧ ThetaLevelDescentGood ∧ PrincipalFiniteness ⇒ ThetaDescentFiniteness`.
* `deligneBound_of_levelDescent`:
  `LevelDescentSplitAll ⇒ Deligne`, where
  `LevelDescentSplitAll = GlueAmpleDescent ∧ ∀ 𝔽_q, DGeomGapsAll ∧ LevelSectionDescent ∧ PrincipalFiniteness`.

### Ψ-compatibility (finding 2 of `ARITH_DEURING_G7_PRINCIPAL.md`)

**`PrincipallyPolarizedΨ k B π_B q`** is `PrincipallyPolarized` plus the condition
`∃ y ∈ B(k̄), π_B^* L ≅ t_y^*(L^{⊗ q})`, where `transl y = (toUnit ≫ y) * 𝟙`. In words, the class
of `L` is Frobenius-stable up to translation.

* This is what descent gives. `L ⊠ L'` is defined over `𝔽_q` and `Γ_n` is `π`-stable. The
  Frobenius conjugate of `Γ̃_n` is another lift of `Γ_n`, so it differs from `Γ̃_n` by a character
  of `Γ_n`, and the descended bundles differ by an element of `Pic⁰`. Hence
  `π^*L_n ≡ L_n^{⊗ q}`.
* `Pic⁰ = {t_y^*L^q ⊗ L^{−q}}` because `L^q` is ample.
* This holds in **every** isogeny class, not only the ordinary one used in the finding.

Statements:

* `LevelSectionDescentΨ` is `LevelSectionDescent` plus that condition, for `π`-equivariant `v`.
* `ThetaLevelDescentΨ` is the seam with `PrincipallyPolarizedΨ`.
* Adapters: `principallyPolarized_of_Ψ`, `thetaLevelDescentΨ_of_levelSectionDescentΨ` and
  `thetaDescentFiniteness_of_splitΨ`.
* C-descent (`Genus2FrobDescent`) can take the Ψ condition as input once `ThetaJacobianModel` is
  restated over `PrincipallyPolarizedΨ`. That restatement is not done here, since
  `PrincipalFiniteness` is an existing definition.

## 3. What remains

| Named Prop | Content | Estimate |
|---|---|---|
| **`LevelSectionDescent K`** | (a) `𝒪(N·O)` as an `𝒪_{J}`-module through `aj` (G1 Picard), `L ⊠ L'` on `J × J'`, invertible and ample (`N > 0`; product of ample is ample). (b) Equivariant structures: translations `t_γ` on `J × J'` (G6 `translate`), isomorphisms `t_γ^*(L ⊠ L') ≅ L ⊠ L'` with cocycle, built from the level lifts. Needs the function-field/module bridge: a rational function `f` with `f · τ_P(V) = V` gives `t_P^*𝒪(N·O) ≅ 𝒪(N·O)`, which is the module-level content of `RRStabilizerBridge`. (c) Descent datum on `A ×_B A ≅ Γ × A`: G6 has the kernel pair, but `Glue` does not record it, so it must be re-derived from 07S7 or `Glue.univ`. Effectivity by Stacks 023T. (d) `H⁰(B, M) = H⁰(A, q^*M)^Γ` (sheaf property along `q`, Stacks 023T full faithfulness on `Hom(𝒪, −)`). (e) Künneth in degree 0 and `H⁰(E, 𝒪(N·O)) = L(N·O)`. | 2.5–4k: (b) + (e) ≈ 1.5–2.5k, (c) + (d) ≈ 0.7–1k, (a) ≈ 0.3–0.5k |
| **`GlueAmpleDescent`** | Stacks 0B5V for `q` finite locally free surjective between abelian varieties. Route: norm `N_q(s)` of sections of `q^*M^{⊗ n}` (`Divisors/Norm` exists in Stacks, for `QuasiAffine`), or Serre's cohomological criterion with `q_*` exact. | 0.5–1k |
| `LevelSectionDescentΨ` (optional) | as above, plus `π_B^*L_n ≅ t_y^*L_n^{⊗ q}` (Frobenius on `𝒪(N·O)`, the character difference of the lifts) | +0.3–0.6k |

Nothing in §1 or §2 depends on these Props except through the named hypotheses.

## 4. Audit

`nice -n 10 lake build RamanujanWeil.Arith.DeuringG7LevelDescentAxioms` (2026-11-10). All audited
declarations depend only on `[propext, Classical.choice, Quot.sound]`. They include:

* `finrank_eq_card_mul_finrank_invariants`
* `finrank_levelRep_invariants`
* `finrank_rrSpace`
* `finrank_thetaLevelRep_invariants_eq_one`
* `finrank_famInv_eq_one`
* `thetaLevelDescentGood_of_levelSectionDescent`
* `thetaDescentFiniteness_of_split'`
* `deligneBound_of_levelDescent`
* `thetaLevelDescentΨ_of_levelSectionDescentΨ`
* `thetaDescentFiniteness_of_splitΨ`

There is no `sorry`, `admit`, `native_decide` or `axiom`. No existing file was edited, and
`RamanujanWeil.lean` is unchanged.

Build times: Rep ≈ 10 s (Mathlib-level imports); `DeuringG7LevelDescent` ≈ 4–5 min, almost all of
it import loading.
