# A3-ord, G7-D: Mumford's descent for graph quotients, and the step-D seam (2026-11-10)

This continues `ARITH_DEURING_G7FIN.md` (route F2′, steps W / D / Θ / J / C),
`ARITH_DEURING_G7_WC.md` (the theta-group bridge `AltPairing.ofTheta`) and
`ARITH_DEURING_FINAL.md` (the per-class count is unconditional; `MultLeOneAll` alone gives
Deligne). New files only, audited in `RamanujanWeil/Arith/DeuringG7DAxioms.lean`:

| File | Imports | Content |
|---|---|---|
| `Arith/DeuringG7DAlg.lean` | WeilHeis, Mathlib (Baer) | **Mumford's descent criterion for graphs, group-theoretic half**: level structures, existence, trivial descended theta group |
| `Arith/DeuringG7DCore.lean` | DAlg, WeilCore | `k̄^×` divisible, roots of unity, `ThetaFamily`, `ofTheta` pairings, `s_n`, anti-isometry ⟺ level subgroup; the named seam **`ThetaDescentFiniteness`** |
| `Arith/DeuringG7DFinal.lean` | DCore, DeuringFinal | `multLeOneAll_of_thetaDescent`, **`deligneBound_of_thetaDescent`** |
| `Arith/DeuringG7DAxioms.lean` | | audit |

## 0. Summary

Step D splits into two halves:

* an **algebraic half**: Mumford's criterion and the computation of the descended theta group, as
  group theory on central extensions. It is **fully proved** here.
* a **geometric half**:
  * the theta group `𝒢(𝒪(N[0]))` as a scheme-theoretic object;
  * descent of the line bundle `L ⊠ L'` along `E × E' → B_n` given a level subgroup.

  It is **not** built.

The geometric half is folded, together with Θ, J and C, into one named Prop. That Prop is
connected to the headline through the proved algebra:

```lean
theorem deligneBound_of_thetaDescent (h : ThetaDescentFinitenessAll) : RamanujanTau.DeligneBound
```

The chain is:

1. `ThetaDescentFiniteness`;
2. `TateFinitenessLag`, via `ofTheta` pairings with one common `ζ` and `graphLevel_of_antiIsom`;
3. `MultLeOneAll`, via `mult_le_one_lag`;
4. Deligne, via `Final.deligneBound_of_multLeOne`.

**Why the geometric half is not built.** A survey of Stacks (`PicardScheme/CurvePicard/*`) found
the following.

* Present:
  * the polarization class `Λ_L`;
  * the translates `t_y^*L` **as classes in `Pic`** (`PolarizationCriterion`, `PolarizationSeesaw`);
  * the theorem of the cube;
  * the theta divisor of a curve Jacobian (`ThetaPolarization`).
* Absent:
  * the **isomorphisms** `L ≅ t_x^*L` with their composition law, i.e. the theta group;
  * equivariant structures on modules;
  * descent of quasi-coherent modules along a finite étale quotient such as the G6 `Glue`.

Building these is the 4–6k estimate of `ARITH_DEURING_G7_WC.md` §3. It was not attempted in this
pass.

## 1. The algebraic half (`DeuringG7DAlg`, fully proved)

Let `X : 0 → A → G → K → 0` and `X' : 0 → A → G' → K' → 0` be central extensions with a common
`A`. In D these are `𝒢(𝒪(N[0]))` on `E`, `E'` with `A = k̄^×`. The theta group of `L ⊠ L'` is
`G ×_A G' = (G × G')/{(a, a⁻¹)}`, with commutator pairing `e ⊕ e'`.

* **`GraphLevel X X' u`**: a level subgroup over `graph(u)`, `u : K ≃+ K'`. It consists of:
  * lifts `σ x ∈ G` and `σ' x ∈ G'` over `x` and `u x`;
  * defects `c(x, y)` and `−c(x, y)` in `A`, so that `x ↦ [σ x, σ' x]` is a homomorphism into
    `G ×_A G'`.

  This avoids building the quotient group `G ×_A G'` itself.
* **`exists_graphLevel`** (Mumford §23, existence half). Assume `e'(u x, u y) = −e(x, y)` and `A`
  is divisible. Then a level structure exists.
  * `graphGroup` is `Q = {(g, g') : p' g' = u(p g)} ≤ G × G'`, and `antidiag` is
    `{(ι a, ι' a⁻¹)}`, which is central and normal.
  * **`graphQuot_mul_comm`**: `Q/antidiag` is abelian. A commutator is `(ι e, ι' e') = (ι e, ι' (−e))`
    by isotropy.
  * `ιQ : A ↪ Q/antidiag` (`ιQ_injective`).
  * The divisible `A` is Baer (`Module.Baer.of_divisible`), so `ιQ` has a retraction `r`. Correcting
    the canonical lifts by `r` gives `σ`, and the defects cancel because `r` vanishes on the
    corrected lifts.
* **`eq_of_forall_pairing_graph`**: the graph of an anti-isometry is its own orthogonal. The
  pairings are `A`-valued, and `X'` is Heisenberg.
* **`centralizer_graphLevel`**: `Z(Γ̃)/Γ̃ = A`. Suppose `(g, g')` commutes in `G ×_A G'` with every
  `[σ x, σ' x]`, i.e. `[g, σ x] + [g', σ' x] = 0`. Then it is `[σ x, σ' x]` times a central
  element. By Mumford's description `𝒢(L_B) = Z(Γ̃)/Γ̃`, this says `K(L_B) = 0`: **the descended
  polarization is principal**.

## 2. Wiring (`DeuringG7DCore`, fully proved)

* `divisibleBy_units k`: `k^×` is divisible for algebraically closed `k`.
* `exists_primitiveRoots`: primitive `ℓⁿ⁺¹`-th roots `ζ_n` exist for `ℓ` invertible, as roots of
  cyclotomic polynomials. **One** `ζ` serves both curves.
* `ThetaFamily X ℓ` (Heisenberg extensions `G_n` of `X[ℓⁿ⁺¹]` by `k^×`) and
  `ThetaFamily.pairing ζ = AltPairing.ofTheta …`.
* **`ThetaFamily.sCoord_pairing`**: `s_n` (and `s'_n` for `E'`) is the `ζ_n`-log of the
  commutator of lifts of a coordinate basis.
* **`mem_antiIsom_iff_det`**: `u ∈ antiIsom ⟺ det u = −s_n/s'_n`.
* **`antiIsom_iff_pairing`**: `u ∈ antiIsom ⟺` anti-isometry of the `k̄^×`-valued commutator
  pairings. It uses the injectivity of `torsionLog` with the common `ζ`.
* **`graphLevel_of_antiIsom`** and **`centralizer_of_antiIsom`**: the algebraic half of D for the
  gluings `u_n` that `LagGraphFiniteness` quantifies over.

### The named seam

```lean
def ThetaDescentFiniteness (K) : Prop :=
  ∀ W W' S S' (same ordinary trace, t² < 4q) ℓ (odd prime, invertible in 𝔽̄_q),
    ∃ (T : ThetaFamily S.J ℓ) (T' : ThetaFamily S'.J ℓ),
      ∀ v (π-equivariant), (∀ n, Nonempty (GraphLevel (T.H n) (T'.H n) (v n))) →
        ∀ G : ∀ n, Glue (Γ ℓ v n), ∃ n ≠ m, (G n).B ≅ (G m).B equivariantly
```

What it contains mathematically:

1. **D-geom.** `T`, `T'` are the theta groups of `𝒪(ℓⁿ⁺¹[0])` on `J_W` and `J_{W'}`, so
   `Z(𝒢) = k̄^×` and they are Heisenberg. Mumford's descent then applies: a level subgroup over
   `graph(v_n)` descends `L ⊠ L'` to `L_n` on `B_n`, with `𝒢(L_n) = Z(Γ̃)/Γ̃`. That group is
   trivial by `centralizer_of_antiIsom`, so `L_n` is a principal polarization.
2. **Θ.** `h⁰(L_n) = 1` and `Θ_n² = 2`.
   * If `Θ_n` is reducible, `B_n` is a product. That case is killed by `DeuringG7FinProd`.
   * If it is irreducible, `Θ_n` is a smooth genus-2 curve `C_n`.
3. **J.** `Jac(C_n) ≅ B_n` equivariantly.
4. **C** (`Pencil.genus2ModelExistence`, proved; finiteness by `exists_ne_iso_of_genus_eq_two`)
   and **C-Jac** (another agent, `DeuringG7CJac*`). Two of the `C_n` are isomorphic, and so
   are their Jacobians.

## 3. Remaining

| Item | Content | Estimate |
|---|---|---|
| **D-geom** | Translations `t_x` on `J_W`. The theta group `{(x, φ : L ≅ t_x^*L)}` of `L = 𝒪(N[0])` as a `CentralExt` with kernel `Γ(𝒪)^× = k̄^×`, where `K(L) = E[N]` comes from Abel–Jacobi. The Heisenberg property. Descent of modules along the G6 quotient given a level subgroup, and `𝒢(L_B) = Z(Γ̃)/Γ̃`. | 3.5–6k (the algebraic part of the old 4–6.5k is done here, ≈ 0.5k) |
| Θ | intersection theory on the abelian surface `B_n`, adjunction; product case killed | 4–7k |
| J | `Jac(Θ) ≅ B_n` equivariantly (Albanese / `jacobianGrp`) | 2–4k |
| C-descent | `Θ_n` descends to `𝔽_q` (or C is restated for `(C/k̄, Ψ)`) | 0.5–1k |
| C-Jac | other agent | in progress |

**How to split the seam further once the geometric objects exist.** Replace the existential
`T, T'` by a proved theta-group construction (`ThetaFamily` from D-geom). Then state
"level structure ⇒ principally polarized `B_n`" (descent) and
"principally polarized ⇒ genus-2 Jacobian" (Θ + J) separately, so that the proved C and C-Jac are
consumed. The concrete predicate "principally polarized" (an invertible ample `L` on `B_n` with
`h⁰ = 1`) should be fixed together with whoever builds Θ. It was not fixed here, to avoid an
interface that the Θ work would have to change.

## 4. Audit

`nice -n 10 lake build RamanujanWeil.Arith.DeuringG7DAxioms` succeeds (2026-11-10). All 16
audited declarations depend only on `[propext, Classical.choice, Quot.sound]`, including:
* `exists_graphLevel`;
* `centralizer_graphLevel`;
* `tateFinitenessLag_of_thetaDescent`;
* `deligneBound_of_thetaDescent`.

There is no `sorry`, `admit`, `native_decide` or `axiom`. No existing file was edited.

Build times: DAlg ≈ 6 s; DCore and DFinal ≈ 4–5 min each, mostly import loading.
