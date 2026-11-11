# A3-ord, G7 AJ + Heisenberg: Heisenberg is proved, Abel–Jacobi reduced to a class-group bridge (2026-11-10)

This continues `ARITH_DEURING_G7DGAPS.md` §5, which left two inputs of `DGeomGapsAll K`:
`AbelJacobiAll K` and `ThetaHeisenbergAll K`.

* **`ThetaHeisenbergAll K` is a theorem relative to `AbelJacobiAll K`**
  (`thetaHeisenbergAll_of_aj`).
* **`AbelJacobiAll K` is reduced to `PicClassBridgeAll K`**, a single named statement about
  restricting line bundles to the affine chart (`abelJacobiAll_of_bridge`).
* So `DGeomGapsAll K` follows from `PicClassBridgeAll K` alone (`dGeomGapsAll_of_bridge`).
  `deligneBound_of_bridge` gives Deligne's bound from `PicClassBridgeAll`, `ThetaLevelDescent`
  and `PrincipalFiniteness` at every finite field.

New files only, audited in `RamanujanWeil/Arith/DeuringG7AJHeisAxioms.lean`:

| File | Imports | Content |
|---|---|---|
| `Arith/DeuringG7HeisEval.lean` | DGapsBridge | evaluation at affine points; `τ_P r` is regular at `Z` with value `r(Z + P)` |
| `Arith/DeuringG7HeisZeros.lean` | HeisEval | `r · σ r = N(r)`; zeros exist and are roots of `N(r)`; `(c, P) ∈ 𝒢`, `c ∈ F` ⟹ `P = O` |
| `Arith/DeuringG7HeisMain.lean` | HeisZeros | **`thetaHeisenberg_of_torsion`**: `E[N] ≅ (ℤ/N)²` ⟹ `ThetaHeisenberg W N` |
| `Arith/DeuringG7AJCore.lean` | DGeomFamily, G1Point | `ajEquiv : E(k̄) ≃ J_W(k̄)`; `PicClassBridge`; `abelJacobiMathlib_of_bridge` |
| `Arith/DeuringG7HeisAll.lean` | AJCore, HeisMain, DGapsAll | `torsion_of_aj`, `thetaHeisenbergAll_of_aj`, `dGeomGapsAll_of_bridge`, `deligneBound_of_bridge` |
| `Arith/DeuringG7AJHeisAxioms.lean` | | audit |

## 1. Abel–Jacobi (`DeuringG7AJCore`)

* `fvpCurvePt` inverts `curvePtFvp`, by the pullback universal property of
  `E_W = projOf W ×_K k̄`. Composing with `Ihara.fvpEquivPoint` gives `secEquiv`: sections of
  `E_W → Spec k̄` correspond to Mathlib's points `E(k̄)`.
* `aj` is an isomorphism (G1, `JacSite.isIso_aj`), so `z ↦ z ≫ aj` is a bijection on points.
  Together these give **`ajEquiv : E(k̄) ≃ J_W(k̄)`**, with `ajEquiv P_z = z ≫ aj`.
* **`PicClassBridge W S`** (named): there is a homomorphism `ρ : J_W(k̄) → Cl(k̄[E])` with
  `ρ(z ≫ aj) = Point.toClass P_z`.
* **`abelJacobiMathlib_of_bridge`**: `PicClassBridge ⟹ AbelJacobiMathlib`. Mathlib's
  `Point.toClass` is an *injective* homomorphism, which is exactly how Mathlib proves the
  chord–tangent law is a group law. Since `ajEquiv` is onto, `ρ` is injective, so no injectivity
  needs to be assumed. Then `ρ(aj(P + Q)) = ρ(aj P + aj Q)` shows that `ajEquiv` is additive.

**What `PicClassBridge` says.** Let `U = E_W ∖ O = Spec k̄[E]` be the affine chart (`chartOpen`
of `Ihara.PointsCurve`, base-changed). Then `ρ` is restriction `Pic⁰(E_W) → Pic(U)`, followed by
Mathlib's `ClassGroup.equivPic` and a sign. It is additive because restriction commutes with
`⊗`. On `aj(P) = 𝒪(P − O)` it gives `𝒪(P)|_U`, the inverse of the ideal sheaf of `P`, i.e.
`[m_P]^{−1}`. Injectivity on `Pic⁰` is not needed; it comes for free from Mathlib.

**Why this route.** Two alternatives require further geometric arguments:
* Transporting the Jacobian law and checking "three collinear points sum to zero" needs the same
  line-bundle identity `𝒪(P) ⊗ 𝒪(Q) ⊗ 𝒪(R) ≅ 𝒪(3·O)`, but on the projective scheme, i.e. a
  section of `𝒪(1)|_E` and its zero scheme. The bridge pushes everything to the affine chart,
  where Mathlib has already done the group-law work.
* Rigidity does handle negation. The automorphism `[−1]` is a `VariableChange`
  (`u = −1, s = −a₁, t = −a₃`), so `aj ∘ [−1] ∘ aj⁻¹` is a pointed involution of `J`, hence
  `±1`. But rigidity does not reach the addition law, which is not a scheme morphism of the
  plane cubic.

## 2. Heisenberg (`DeuringG7HeisEval`, `DeuringG7HeisZeros`, `DeuringG7HeisMain`)

```lean
theorem thetaHeisenberg_of_torsion [IsAlgClosed F] {N : ℕ} (hN : 3 ≤ N) (hodd : Odd N)
    (htor : Nonempty (AddSubgroup.torsionBy (W⁄F).Point (N : ℤ) ≃+ (Fin 2 → ZMod N))) :
    ThetaHeisenberg W N
```

The proof is a **zero count**: no Galois theory of `[N]^*`, no Riemann–Roch and no
representation theory beyond one common eigenvector. Let `g = (f, S)` be central in
`𝒢 = 𝒢(L(N·O))` with `S ≠ O`.

1. **Choosing `P`** (`exists_big_closure`). Since `E[N] ≅ (ℤ/N)²` and `N` is odd, some
   `P ∈ E[N]` has `#⟨P, S⟩ ≥ 3N`. Write `S = (s₁, s₂)` with `sᵢ ≠ 0`, and let `P = e_j` for
   `j ≠ i`. Then `aS + bP` (`a ∈ {0, 1, 2}`, `b ∈ ℤ/N`) are pairwise distinct, because `2` is a
   unit mod `N`.
2. **A common eigenvector** (`exists_common_eigenvector`). `P ∈ E[N] = K(L)`
   (`thetaKer_eq_torsion` with the proved bridge), so some `g'` lies over `P`. Since `g` is
   central, the operators of `g` and `g'` on `V = L(N·O)` commute, and so they share an
   eigenvector `v`. The points `R` such that some element of `𝒢` over `R` has eigenvector `v`
   form a subgroup (`eigenPts`). It contains `P` and `S`, hence `⟨P, S⟩`.
3. **`v` is not constant.** If it were, `f` would be a constant. But
   `right_eq_zero_of_left_const` says that if `(c, S) ∈ 𝒢` with `c ∈ F`, then `S = O`: a
   function `f` with `f · τ_S L(N·O) = L(N·O)` and `S ≠ O` has a pole of order `≥ N` at `O`, by
   the argument of the bridge. So `v = r ∈ F[E]` has `1 ≤ deg N(r) ≤ N`, where
   `N(r) = r · σ r ∈ F[X]` (`mul_conj_eq_norm`). Hence `r` has a zero `Z₀` (`exists_zero`):
   take a root `x₁` of `N(r)`, a point `(x₁, y₁)`, and use `(σ r)(Z) = r(−Z)` (`evPt_conj`).
4. **Propagating zeros** (`eval_eq_zero_of_eigen`). Suppose `(h, R) ∈ 𝒢` has
   `h · τ_R v = μ v` with `μ ≠ 0`, and `v(Z + R) = 0` with `x(Z) ≠ x(R)`. Then `v(Z) = 0`.
   * This needs the value of `τ_R r` at `Z`, which is `r(Z + R)` (`hasVal_trans`).
     "`u` is regular at `Z` with value `c`" means `(x − x₀)^k u = s ∈ R` with
     `s(Z) = (a − x₀)^k c`. This is closed under ring operations, and
     `(x − x₀)^{−1}` has value `(a − x₀)^{−1}`.
   * The formulas `transX_neg`/`transY_neg` (Mathlib's chord law for `ξ + R`) then evaluate to
     Mathlib's chord law for `Z + R`. An induction over `x, y` (`adjoin_xR_yR`) extends this to
     all of `F[E]`.
5. **Counting.** For `R ∈ ⟨P, S⟩` with `R ≠ Z₀` and `2R ≠ Z₀`, the point `Z₀ − R` is a zero of
   `v`; the hypothesis `x(Z₀ − R) ≠ x(R)` fails only when `Z₀ = 2R`. Since `N` is odd, `[2]` is
   injective on `E[N]` (`two_nsmul_injOn`), so this gives at least `3N − 2` zeros.
   * Each zero has its `x`-coordinate among the at most `N` roots of `N(r)`
     (`isRoot_norm_of_evPt`).
   * Each `x` arises from at most two values of `R` (`eq_or_eq_neg_of_ptX_eq`).
   * So `3N − 2 ≤ 2N`, which contradicts `N ≥ 3`.

**Where `char ∤ N` enters.** Only through `E[N] ≅ (ℤ/N)²`, which is the hypothesis `htor`. The
statement is false without it: on an ordinary curve with `p ∣ N`, the group `E[N]` is too small.

**`E[N] ≅ (ℤ/N)²`** (`torsion_of_aj`). Given `AbelJacobiMathlib`, the map `torEquiv` carries
Stacks' `J_W[N] ≅ (ℤ/N)^{2 dim J}` (`nonempty_torsionBy_addEquiv_of_isUnit`, `dim J_W = 1`) to
Mathlib's `E(k̄)[N]`. This is how `thetaHeisenbergAll_of_aj` uses `IsUnit (ℓ : k̄)`.

## 3. Assembly (`DeuringG7HeisAll`)

```lean
theorem thetaHeisenbergAll_of_aj (haj : AbelJacobiAll K) : ThetaHeisenbergAll K
theorem dGeomGapsAll_of_aj (haj : AbelJacobiAll K) : DGeomGapsAll K
theorem abelJacobiAll_of_bridge (h : PicClassBridgeAll K) : AbelJacobiAll K
theorem dGeomGapsAll_of_bridge (h : PicClassBridgeAll K) : DGeomGapsAll K
theorem deligneBound_of_bridge (h : DBridgeSplitAll) : RamanujanTau.DeligneBound
```

`DBridgeSplitAll` is `PicClassBridgeAll ∧ ThetaLevelDescent ∧ PrincipalFiniteness` at every
`GaloisField p n`.

## 4. What remains

| Item | Content | Estimate |
|---|---|---|
| `PicClassBridge W S` | `ρ : Pic⁰(E_W)(k̄) → Cl(k̄[E])`, additive, `ρ(𝒪(P − O)) = [m_P]`. Steps: (a) the chart `D₊(z) ×_K k̄ ≅ Spec k̄[E]`; (b) restriction of invertible modules to an open is a homomorphism of Stacks' `PicardGroup`; (c) `Pic(Spec R) → CommRing.Pic R` by global sections (quasi-coherence on affines), then `ClassGroup.equivPic`; (d) on the Hilbert family of `P` (Stacks' `pointIdeal`), the restriction is the ideal `m_P`. There is no injectivity or degree argument: injectivity is automatic. | 1.5–2.5k |
| `ThetaLevelDescent`, `PrincipalFiniteness` | unchanged (`ARITH_DEURING_G7DGEOM.md` §6) | — |

`ThetaHeisenberg` itself has no remaining gap.

## 5. Audit

The 20 declarations in `Arith/DeuringG7AJHeisAxioms.lean` cover evaluation,
zero counting, the Abel–Jacobi comparison, the Heisenberg reduction, and assembly.
Reproduce with `lake build RamanujanWeil.Arith.DeuringG7AJHeisAxioms`.
The dated build result and source hashes are in
[publication verification](verification/publication_2026_11_11.json).
