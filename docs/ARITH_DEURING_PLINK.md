# A3-ord: `PrimeToPLink` proved (2026-11-10)

Discharges the named Prop `ClassLattice.PrimeToPLink K` (`Arith/DeuringClassLattice.lean`,
`docs/ARITH_DEURING_CLASSLATTICE.md` §5) for every finite field `K`. Consequently

```lean
theorem RamanujanWeil.Ihara.deligneBound_of_tatePol (hfin : TateFinitenessPolAll) :
    RamanujanTau.DeligneBound
```

(`Ihara/FinalDeuringTatePol.lean`): **Deligne's bound now depends on the single named Prop
`TateFinitenessPolAll`.**

New files only. No existing file was edited. No `sorry`, `admit`, `native_decide` or `axiom`.

| File | Content |
|---|---|
| `Arith/DeuringPLinkField.lean` | function fields: `exists_comp_eq_of_mem` (right factors of a radicial map), `exists_pow_mem_of_injective`, **`exists_dual_exact`** (`f ≫ h = [deg f]`), **`exists_functionFieldMap_eq_pow`** (`Φ^* L ⊆ L^p`) |
| `Arith/DeuringPLinkRC.lean` | `trSeq`, `ring_identities`, composition powers `cpow`, **`link_of_injective`** (the radicial case) |
| `Arith/DeuringPLinkPhi.lean` | `vOf` (`V = t − π`), `Good`, `good_of_hom`, `card_torsion_le`, **`exists_phi`** (one of `π`, `V` is injective on points) |
| `Arith/DeuringPLink.lean` | `link_trans`, `link_symm`, `link_glue_unit`, **`link_of_ne_one`**, **`primeToPLink`**, **`primeToPLinkAll`** |
| `Arith/DeuringPLinkAxioms.lean` | audit |
| `Ihara/FinalDeuringTatePol.lean` | **`deligneBound_of_tatePol`** |

## 1. The route (cheaper than (i) CM and (ii) `p`-divisible groups)

Neither Deuring lifting nor `p`-divisible groups nor Frobenius twists `E^{(p^r)}` are used. The
only inputs are G6 quotients (`Glue`), the radicial machinery (`isPurelyInseparable_of_injective`,
`exists_hom_functionFieldMap_eq`, `[p]^* L ⊆ L^p`), Stacks' `[L : kL^p] = p` with
`isSeparable_of_notMem_compositumFrobenius`, Stacks' `#A(k)[p^m] = p^{mf}` with `f ≤ dim A`, the
degree (G4) and the endomorphism ring `postcompSubring`.

Notation: `k` algebraically closed of characteristic `p`, `q = p^s`, `p ∤ t`.

**The abstract `π` problem.** `FrobeniusJacobian.π` is characterised only by its characteristic
polynomial `X² − tX + q`, so it is not known to be the (purely inseparable) Frobenius: it could be
the Verschiebung `V = t − π`. `exists_phi` picks `Φ ∈ {π, V}` injective on `k`-points: if
`πx = 0` and `Vy = 0` with `x, y ≠ 0`, then `x, y ∈ X[q]`; multiples `x'`, `y'` have order `p`;
`#X(k)[p] ≤ p` forces `y' ∈ ⟨x'⟩`, so `πy' = 0`; but `Vy' = 0` gives `πy' = ty'`, and `p ∤ t`.
`Φ` commutes with `π`, has `Φ² − tΦ + q = 0` (`endPolyEval_vOf`) and `deg Φ = q`.

## 2. Function fields (`DeuringPLinkField`)

`L = k(X)`. For `f : X ⟶ Y` injective on `k`-points:

* `L / f^* k(Y)` is purely inseparable of degree `p^e = deg f`, and every `p^e`-th power of `L`
  lies in `f^* k(Y)` (`pow_finrank_mem`: the minimal polynomial is `T^{p^n} − c` with
  `p^n ≤ p^e`).
* **`exists_comp_eq_of_mem`**: if `g : X ⟶ C` has `g^* k(C) ⊆ f^* k(Y)`, then `g = f ≫ h`
  for a homomorphism `h` (the construction of `Radicial.exists_comp_eq_zpow_of_injective` with
  `[n]` replaced by `g`; `f` is surjective on points by `radicialDual`).
* **`exists_dual_exact`**: with `g = [p^e]` (`[p^e]^* L ⊆ L^{p^e}`, `RadicialFrob`), `f ≫ h = [p^e]`
  with `p^e = deg f` **exactly** (`RadicialDual` only gave some `n ≠ 0`).
* **`exists_functionFieldMap_eq_pow`**: `Φ` injective on points with `deg Φ ≠ 1` has
  `Φ^* L ⊆ L^p`. Otherwise Stacks makes `L / Φ^* L` separable; it is purely inseparable, so it is
  trivial and `deg Φ = 1`. Iterating (`functionFieldMap_cpow_eq_pow`): `(Φ^m)^* L ⊆ L^{p^m}`.

## 3. The radicial case (`link_of_injective`)

`ι : X ⟶ Y` equivariant and injective on `k`-points.

1. `deg ι = p^e`, `ι ≫ h = [p^e]`.
2. `m = e + 1`: `(Φ^m)^* L ⊆ L^{p^m} ⊆ L^{p^e} ⊆ ι^* k(Y)`, so `Φ^m = ι ≫ ι''`. Then `ι''` is
   injective on points (`Φ^m` is, and `ι` is onto), `deg ι'' = p^{e''}`, `ι'' ≫ h'' = [p^{e''}]`,
   and `p^e · p^{e''} = deg Φ^m = q^m`.
3. `(h'' ≫ h) ≫ Φ^m = h'' ≫ [p^e] ≫ ι'' = [p^e p^{e''}] = [q^m] = V^m Φ^m`. Cancelling `Φ^m` in
   `End(X)` (`comp_ne_one`): **`h'' ≫ h = V^m`**.
4. If `e = 0`, `(ι, h)` is a link of degree `1`; if `e'' = 0`, so is `(h'', ι'')`. Otherwise
   `α = ι + h''`, `β = ι'' + h`:
   `α ≫ β = Φ^m + [p^{e''}] + [p^e] + V^m = [t_m + p^{e''} + p^e]`, where `t_m = Φ^m + V^m ∈ ℤ`
   (`trSeq`, `ring_identities`) and `t_m ≡ t^m (mod p)` (`trSeq_dvd`, as `p ∣ q`). Since
   `p ∤ t`, `p ∤ t_m + p^{e''} + p^e`.
5. Equivariance: `h`, `h''` are duals (`comm_of_comp_eq_zpow`); `ι''` by cancelling `ι`.

The identity behind step 4 is the ideal-theoretic statement that `𝔭^e` and `𝔭̄^{fm−e}` are in
inverse classes with `𝔭^e + 𝔭̄^{fm−e}` coprime to `p`; it is realised by explicit maps, without
ideals, `p`-adic Tate modules or Frobenius twists.

## 4. General homomorphisms (`link_of_ne_one`)

`Good π t q`: `dim X = 1`, `π² − tπ + q = 0`, `deg π = deg V = q`. It passes along nonzero
equivariant homomorphisms (`good_of_hom`). For `φ : X ⟶ Y` nonzero equivariant, `Γ = ker φ(k)`,
`#Γ = p^a m'`, `p ∤ m'`:

1. `q₁ : X → X₁ = X/Γ[m']` with cofactor `[m']`: a link (`link_glue_unit`).
2. `φ = q₁ ≫ φ₁`; `Γ₁ = ker φ₁(k)` is killed by `p^a`, so `#Γ₁ = p^b` (`IsPGroup.iff_card`).
   `#X₁(k)[p^b] ≤ p^b` (`card_torsion_le`) gives `Γ₁ = X₁(k)[p^b]`, so the cofactor
   `s : Z = X₁/Γ₁ → X₁` of `q₂` is injective on points: `Link Z X₁` by §3, reversed.
3. `φ₁ = q₂ ≫ ι`, `ι` injective on points: `Link Z Y` by §3.

`primeToPLink K`: `Good` for the concrete Jacobian from `charPoly_data` and
`endDegree_zpow_mul_zpow` (`deg (t − π) = q − t² + t² = q`), `q = p^s` from `FiniteField.card`.

## 5. Axiom audit

`nice -n 10 lake build RamanujanWeil.Arith.DeuringPLinkAxioms` succeeds (29965 jobs). All 25
audited declarations, including `link_of_injective`, `link_of_ne_one`, `primeToPLink`,
`primeToPLinkAll` and `Ihara.deligneBound_of_tatePol`, depend only on
`[propext, Classical.choice, Quot.sound]` (`trSeq_dvd` only on `[propext, Quot.sound]`).

## 6. What remains

`PrimeToPLink` and `PrimeToPLinkAll` have no remaining hypotheses. The only named Prop left in
the headline is **`TateFinitenessPolAll`** (G7). The class-lattice hypotheses `hlink` in
`ClassLattice.deuringClassLatticeAll_of_props` / `deuringMultiplicity_of_props` can now be
discharged by `PLink.primeToPLinkAll`.

Build notes: `link_of_injective` and `link_of_ne_one` use `maxHeartbeats 1600000`, `exists_phi`
`800000`. The RC module peaked at about 9 GB in a build that failed with errors; the final
successful builds stayed under 4 GB per Lean process.
