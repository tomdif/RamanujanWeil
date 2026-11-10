# A3-ord, G5: `WeierstrassDescent` (2026-11-09)

This is the status of the named Prop `G5.WeierstrassDescent K` (`Arith/DeuringG5Surj.lean`,
`docs/ARITH_DEURING_G5.md` §4–5), the geometric heart of the `surj_class` field.

**Result.** `weierstrassDescent_of_model : WeierstrassModel (AlgebraicClosure K) → G5.WeierstrassDescent K`
is proved. The only remaining input is the named Prop

```lean
def WeierstrassModel (k : Type u) [Field k] : Prop :=
  ∀ (B : Over (Spec (.of k))) [GrpObj B] [AlgebraicGeometry.IsAbelianVariety k B],
    abelianVarietyDimension B = 1 →
    ∃ (C : WeierstrassCurve k) (_ : C.IsElliptic) (ρ : projOf C ≅ B.left),
      ρ.hom ≫ B.hom = projectionOf C ∧ zeroOf C ≫ ρ.hom = η[B].left
```

i.e. piece (a) of the blueprint, over `K̄` only (no Frobenius, no sites, no `𝔽_q`). Pieces (b), (c)
and (d) are proved unconditionally. No existing file was edited; no `sorry`, `admit`,
`native_decide` or `axiom`. Audit: `RamanujanWeil/Arith/DeuringDescentAxioms.lean`.

| File | Content |
|---|---|
| `Arith/DeuringDescentRigid.lean` | **rigidity**: `eq_of_rigid` (a map `c : G × G → H` with `c(e,y) = c(x,e) = e` is constant; `G` proper, `G × G` integral, `H` separated l.f.t.), `isMonHom_of_pointed` (every pointed morphism is a homomorphism) |
| `Arith/DeuringDescentTwist.lean` | semilinear maps and the twist `Φ^* = Over.pullback Φ`: `twHom`, `η_tw_fst`, `isMonHom_twHom`, **`exists_desc`**, **`exists_desc_iso`** (semilinear automorphisms descend to `A/Γ`), `epi_q`, `inv_mem_of_finite`, `isIntegral_tensor`, `isMonHom_of_pointed'` |
| `Arith/DeuringDescentLang.lean` | **Lang for `VariableChange(K̄)`**: `exists_map_frobQ_eq_mul` (`F(δ) = δγ` solvable), `exists_frobFixed_smul`, `exists_map_eq_of_map_frobQ_eq` |
| `Arith/DeuringDescentCoord.lean` | `substOf_mul`, **`changeMap_comp`**, `coordMap_comp` (the cubic isomorphisms compose like the group), `frob_coordMap`, **`exists_descent`** (a plane cubic over `K̄` with a twisted Frobenius descends to `𝔽_q`) |
| `Arith/DeuringDescent.lean` | `WeierstrassModel` (named), `ΨJ` on a concrete Jacobian, `exists_ΨB`, `πB_ΨB`, `exists_curve`, `exists_jacIso`, `trace_eq`, **`weierstrassDescent_of_model`** |
| `Arith/DeuringDescentAxioms.lean` | audit |

## 1. Rigidity (replaces the site comparison (d))

`DeuringDescentRigid` adapts Mathlib's proof of `isCommMonObj_of_isProper_of_isIntegral_tensorObj_of_isAlgClosed`
(Zariski's main theorem + irreducibility of the fibres `{x} × G`): replace the commutator by any
`c : G ⊗ G ⟶ H` with `η ▷ G ≫ c = e`, `G ◁ η ≫ c = e`, and the target `G` by `H`.
`isMonHom_of_pointed` applies it to `c(x, y) = f(xy)(f(x)f(y))⁻¹`.

Consequence: **no site independence is needed**. For any site `S` of `W`, the map
`aj_S⁻¹ ≫ ε : J_{W,S} → B` is pointed, hence a homomorphism. G1.2's Picard-functor rigidity
(same site only) is not used.

## 2. The twisted Frobenius of `B = J₀/Γ` ((b))

Let `F = Fq K` be the `q`-power Frobenius of `Spec K̄` (an isomorphism, `isIso_Fq`), and `F_X` the
absolute `q`-Frobenius of a scheme (`FX`, natural in all scheme maps).

* `ΨJ S = aj⁻¹ ≫ Ψ_W ≫ aj` on `J_W`: semilinear over `F` (`ΨJ_hom`), pointed (`η_ΨJ`), an
  isomorphism, and `π ≫ ΨJ = ΨJ ≫ π = F_J` (`π_ΨJ`, `ΨJ_π`, from G1.1′ and `Ψ ≫ φ = φ ≫ Ψ = F`).
* A semilinear `ψ : A → A` over `Φ` is a `K̄`-morphism `A ⟶ Φ^*A` (`twHom`); `Φ^*` is monoidal,
  so `Φ^*B` is a group scheme, and a pointed `twHom` is a homomorphism by rigidity.
  The universal property of `G : Glue Γ` then descends `twHom ψ ≫ Φ^*q` to `B ⟶ Φ^*B`
  (`exists_desc`), provided `ψ(Γ) ⊆ Φ(Γ)` on points. Doing the same for `ψ⁻¹` over `Φ⁻¹` and
  cancelling the epimorphism `q.left` (flat + surjective) gives an isomorphism `ΨB`
  (`exists_desc_iso`).
* For `ΨJ`: `ΨJ⁻¹` maps `x ∈ Γ` to `F⁻¹(x ≫ π)` (π-stability), and the forward condition
  follows from finiteness of `Γ` (`inv_mem_of_finite`).
* `π_B ≫ ΨB = F_B` (`πB_ΨB`, cancel `q`), `ΨB` pointed (`η_ΨB`).

## 3. Lang descent ((c))

In a model `ρ : E_C ≅ B`, `T = ρ ΨB ρ⁻¹` is a pointed semilinear automorphism of `E_C`. Lifting
through the pullback square `E_{C^σ} → E_C` (Stacks `isPullback_mapMap`) gives a pointed
`K̄`-isomorphism `E_C ≅ E_{C^σ}`, i.e. `γ` with `γ • C^σ = C` (`familyIsoEquiv`). Lang:
`δ^σ = δγ` is solvable componentwise (`u^{q-1} = γ_u`, three equations `x^q = ax + b`), and
then `δ • C` is Frobenius-fixed, so equals `W_K̄` for `W / 𝔽_q`. The key identity
`frobOf ≫ D = D ≫ T` (`frob_coordMap`) needs the composition law `changeMap_comp`, proved from the
substitution identity `substOf a ∘ substOf b = substOf (ab)` (not in Stacks).

## 4. Assembly

`exists_curve`: `ε = geomIso ≫ D ≫ ρ : E_W ≅ B`, pointed, `Ψ_W ε = ε ΨB`, hence
`φ_W ε = ε π_B` (`φ = F ≫ Ψ⁻¹`, naturality of `F`). `exists_jacIso`: for every site,
`e = aj⁻¹ ≫ ε` is a pointed isomorphism (homomorphism by rigidity) with `e π_B = π_S e`
(`π_S = aj⁻¹ φ aj`, G1.1′). `trace_eq`: transporting `π_S² − t_W π_S + q = 0` to `B` and pulling
back along `q`, `(t₀ − t_W)·π₀(x) ∈ Γ` for all points `x`, so `(t₀ − t_W) n π₀ = 0`; comparing
degrees (`deg π₀ = q ≠ 0`) gives `t_W = t₀`. No ordinarity or Hasse bound is used.

## 5. What remains: `WeierstrassModel`

`WeierstrassModel k` is Stacks' `AlgebraicGeometry.GenusOne.exists_weierstrassCurve_iso`
(`Curves/GenusOne/WeierstrassEquation.lean`) applied to `B.hom` with `p = η.left`, once one knows
for a one-dimensional abelian variety `B / k`:

* `IsProper`, `SmoothOfRelativeDimension 1` (Mathlib `smooth_of_grpObj`, G4Hom `isCurve_of_dim_one`,
  Stacks `smoothOfRelativeDimension_one_of_isCurve`): available;
* `h⁰(𝒪_B) = 1`: Stacks `finrank_structureSheafCohomology_zero_eq_card_connectedComponents`
  (module not prebuilt, ~80 unbuilt dependencies);
* **`genus B = 1`**: the real gap. Available routes all need unbuilt Stacks modules
  (`dim H⁰(Ω) = g` / `deg Ω = 2g − 2`, Tag 0C1A, ~600 unbuilt modules; with
  `GroupSchemeDifferentials.exists_free_iso_relativeDifferentials_of_field`, which is built,
  `Ω_B ≅ 𝒪_B` gives `g = 1`), or a longer Picard-scheme argument (`aj_B : B → Pic⁰_B` is a
  homomorphism by rigidity; Jacobi inversion + torsion counts).
* `exists_weierstrassCurve_iso` itself lives in 19 unbuilt Stacks modules
  (`WeierstrassEquation`, `WeierstrassModel`, `SectionRing`, `PointDivisor`, …).

Estimate: 0.1–0.2k lines of glue plus building ~20 Stacks modules if a genus-one statement is
available; the genus statement itself is 0.3–0.8k depending on the route.

## 6. Build and audit

`nice -n 10 lake build RamanujanWeil.Arith.DeuringDescentAxioms` succeeds; all 21 audited
declarations (including `weierstrassDescent_of_model`) depend only on
`[propext, Classical.choice, Quot.sound]`. About 1.0k lines in total (Rigid 176, Twist 204,
Lang 104, Coord 145, main 376). `WeierstrassModel` is a hypothesis of
`weierstrassDescent_of_model`, not an axiom.

Combined with `G5.surjClass_of_descent_minimal`, `surj_class` now depends on
`WeierstrassModel K̄` and `MinimalOrder` for the base curve.
