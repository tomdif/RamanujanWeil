# A3-ord, G7-dual: `RadicialDual` (2026-11-09)

Continues `ARITH_DEURING_G8.md` §1, which reduced `FrobHomDual` to the named Prop
`RadicialDual` (`RamanujanWeil/Arith/DeuringG7Dual2.lean`):

```lean
def RadicialDual : Prop :=
  ∀ (k) [Field k] [IsAlgClosed k] (B A' : Over (Spec (.of k))) [GrpObj B] [GrpObj A']
    [IsAbelianVariety k B] [IsAbelianVariety k A'],
    abelianVarietyDimension B = 1 → abelianVarietyDimension A' = 1 →
    ∀ (f : B ⟶ A') [IsMonHom f], (∀ x : 𝟙_ _ ⟶ B, x ≫ f = 1 → x = 1) →
    ∃ (n : ℤ) (h : A' ⟶ B), n ≠ 0 ∧ IsMonHom h ∧ f ≫ h = (𝟙 B) ^ n
```

**Status: `RadicialDual` is PROVED** (`radicialDual`), hence **`FrobHomDual` is proved**
(`frobHomDual`, via `frobHomDual_of_radicialDual`). No existing file was edited. No `sorry`,
`admit`, `native_decide` or `axiom`. About 640 lines in total, below the 0.8–1.3k estimate.

| File | Content |
|---|---|
| `Arith/DeuringRadicialGen.lean` | generic étaleness, lifting `k`-points, **the fibre count** |
| `Arith/DeuringRadicialFrob.lean` | step (b): `[p]^* k(A) ⊆ k(A)^p`, iterated to `[p^e]` |
| `Arith/DeuringRadicialDual.lean` | step (a) pure inseparability; step (c); `h`; **`radicialDual`**, **`frobHomDual`** |
| `Arith/DeuringRadicialAxioms.lean` | axiom audit |

## Route actually used

Setting: `k` is algebraically closed and `f : B ⟶ A'` is injective on `k`-points. Write
`L = k(B)` and `K = f^* k(A')`.

1. **Generic étaleness** (`etaleAt_genericPoint_of_formallyUnramified`). Let `g` be a dominant
   morphism of integral schemes, locally of finite type, whose map on function fields is formally
   unramified. Then `g` is étale at the generic point. The stalks there are fields, so they are
   regular of dimension 0, and Stacks' `etaleAt_of_unramifiedAt_of_ringKrullDim_eq` applies. The
   map is then also étale at some closed point (`exists_closedPoint_etaleAt`, Jacobson).
2. **Fibre count** (`finrank_le_one_of_injective`). This holds for *any* dominant `v : C ⟶ Y` of
   proper curves with `Y` normal, separable on function fields and injective on `k`-points; it
   needs no group structure, and its conclusion is `[k(C) : k(Y)] ≤ 1`. Proof:
   * `v` is finite locally free of rank `d = deg v` (Stacks
     `isFiniteLocallyFreeOfRank_degreeOver_of_not_constant`).
   * The non-étale locus `Z` is closed. Its image `v(Z)` is closed and misses the generic point
     (`preimage_genericPoint_of_locallyQuasiFinite`).
   * Pick a closed point `y ∉ v(Z)`. The fibre over `y` is finite locally free of rank `d`, and it
     is étale (`etaleAt_iff_of_isPullback`). So it has `d` sections
     (`card_sections_of_etale_of_isAlgClosed`), which are distinct `k`-points of `C` over `y`.
3. **(a) Pure inseparability** (`isPurelyInseparable_of_injective`). Let `S` be the separable
   closure of `K` in `L`, and `C` a proper nonsingular model of `S` (`nonempty_functionFieldModel`).
   * `f = u ≫ v` (`exists_hom_functionFieldMap_eq`, `over_hom_ext_of_functionFieldMap`).
   * `u` is surjective, so it lifts `k`-points (`exists_lift_point`). Hence `v` is injective on
     `k`-points, and it is separable.
   * Step 2 gives `[S : K] = 1`, so `separableClosure = ⊥`.
4. **(b) `[p]` is inseparable** (`exists_pow_eq_functionFieldMap_zpow_char`). Suppose not. Then
   Stacks' `isSeparable_of_notMem_compositumFrobenius`, with `[L : kL^p] = p`, makes `L/[p]^*L`
   separable. So `[p]` is étale at the generic point, hence at a closed point, hence at `0`
   (Stacks `etaleAt_unit_of_etaleAt_closedPoint`), hence unramified there. Then `p` is a unit
   (`isUnit_of_unramifiedAt_zpow_id_left_unit`), a contradiction. Since `kL^p = L^p` for perfect
   `k`, every element of `[p]^*L` is a `p`-th power. Iterating gives the same for `[p^e]` and
   `p^e`-th powers (`exists_pow_eq_functionFieldMap_zpow_pow`).
5. **(c)** Let `e` be the exponent of `L/K` (Mathlib `HasExponent`). Then `[p^e]^* L ⊆ K`; in
   characteristic 0 this is `n = 1`.
   * The `k`-algebra map `y ↦ (f^*)^{-1}([n]^* y)` is induced by a morphism `h : A' ⟶ B`.
   * `f ≫ h = [n]`, because the two maps induce the same map on function fields.
   * `h` is a homomorphism. `h ≫ f = [n]` (`comp_eq_zpow_symm`), so `f` is surjective on points
     and `h` is multiplicative on points. Since `A' ⊗ A'` is reduced, this is checked on points,
     as in `DeuringG3Div`.

Stacks 0CCZ (the Frobenius-twist chain) is **not** needed. Step (a) uses only a model of the
separable closure and the fibre count. Steps (b) and (c) are purely field-theoretic, plus
`exists_hom_functionFieldMap_eq`.

## Build notes

Seven Stacks modules that were not yet built are now compiled in `.lake/packages/Stacks`. Each
was built separately with `lake build <module>`, one Lean process at a time:
`SeparableClosedPoint`, `FlatMorphism`, `FunctionFieldFrobenius`, `SeparableCompositumFrobenius`,
`InseparableFrobeniusChainAssembly`, and their small dependencies.

## Axiom audit

`nice -n 10 lake build RamanujanWeil.Arith.DeuringRadicialAxioms` succeeds. Every audited
declaration depends only on `[propext, Classical.choice, Quot.sound]`:
`etaleAt_genericPoint_of_formallyUnramified`, `exists_lift_point`, `finrank_le_one_of_injective`,
`exists_pow_eq_functionFieldMap_zpow_char`, `exists_pow_eq_functionFieldMap_zpow_pow`,
`isPurelyInseparable_of_injective`, `exists_functionFieldMap_zpow_mem`,
`exists_comp_eq_zpow_of_injective`, `radicialDual`, `frobHomDual`.

## Remaining

Nothing remains for `RadicialDual` or `FrobHomDual`. Downstream, `HomDualHyp` now holds for all
pairs of elliptic curves (`homDualHyp_of_radicialDual radicialDual`), and so does the `Λ` field
(`exists_latticeMatrix_of_radicialDual radicialDual`). The open items in `ARITH_DEURING_G8.md` §5
other than `FrobHomDual` are unchanged: G8(ii) surjectivity, `surj_class`, and `TateFinitenessAll`.
