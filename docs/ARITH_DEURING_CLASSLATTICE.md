# A3-ord: G8(ii) integral surjectivity and the `DeuringClassLattice` assembly (2026-11-09)

Continues `ARITH_DEURING_G8.md` (§4 G8(ii), §5 open items), `ARITH_DEURING_G1_3.md` (G1),
`ARITH_DEURING_RADICIAL.md` (`FrobHomDual` proved) and `ARITH_DEURING_G5.md` (`surj_class`).
New files only, audited in `RamanujanWeil/Arith/DeuringClassLatticeAxioms.lean`:

| File | Content |
|---|---|
| `Arith/DeuringG8Int.lean` | **`exists_postHom_eq`** (G8(ii) integral surjectivity), `exists_homPi_smul_eq`, `homPi_eq_of_smul_eq`, `compPi`/`idPi`, `postHom_compPi`, `postHom_idPi` |
| `Arith/DeuringG8IntIso.lean` | `Link`, `PostHomSurj`, `postHomSurj_of_link`, **`nonempty_iso_iff`**, **`card_aut_eq`** |
| `Arith/DeuringClassLatticeAlg.lean` | pure algebra: `conj_of_linearEquiv`, `linearEquiv_of_conj`, `stabEquiv` |
| `Arith/DeuringClassLattice.lean` | `GlobalSite`, `PrimeToPLink`, `ExistsMinimalBase`; family level (`JacFam`): `exists_latticeMatrix_fam`, **`rel_iff_fam`**, **`card_stab_fam`**, **`classLattice_fam`**; global site: `mem_orbit_iff_global` (via `nonempty_equivIso_congr`), `card_stabilizer_global`, `link_global`, `surjClass_global`, **`nonempty_classLattice_of_base`**, **`nonempty_classLattice_of_tate`**; headline **`deuringClassLatticeAll_of_props`**, **`deuringMultiplicity_of_props`** |
| `Arith/DeuringClassLatticeAxioms.lean` | audit |

No existing file was edited. No `sorry`, `admit`, `native_decide` or `axiom`.

## 1. G8(ii): `Hom_π(A, A') ≅ Hom_{ℤ[π]}(L A, L A')` (`DeuringG8Int`)

Setting: `k` algebraically closed, `A₀, A, A'` one-dimensional, `L A = Hom_π(A₀, A)`,
`postHom φ = (γ ↦ γ ≫ φ)`.

```lean
theorem exists_postHom_eq (hA₀ hA) (hmin : MinimalOrder π₀)
    (hind : ∀ a b, lin π₀ a b = 1 → a = 0 ∧ b = 0) (t q : ℤ) (hπ₀ : π₀² − tπ₀ + q = 0)
    (hdisc : t ^ 2 < 4 * q) (α : A₀ ⟶ A) (hα : α ≠ 1) (hαπ) (β : A ⟶ A₀) (n : ℤ)
    (hn : IsUnit (n : k)) (hαβ : α ≫ β = (𝟙 A₀) ^ n) (hβπ)
    (f : homPi π₀ π →ₗ[ℤ] homPi π₀ π') (hf : f ∘ piAct = piAct ∘ f) :
    ∃ φ : homPi π π', postHom φ = f
```

Proof (≈100 lines). G8 gives `postHom φ₁ = n • f`. To divide `φ₁` by `n` it suffices
(G3-div, `exists_isMonHom_zpow_comp_eq`, `n` invertible) that `φ₁` kills `A(k)[n]`:

* `x ∈ A[n]`, `x = n·z`; `w = β(z) ∈ A₀[n²]`; by **cyclic torsion** (G5,
  `cyclicTorsion_of_minimalOrder`, `n²` invertible) `w = (a + bπ₀)·P` with `P` a generator of
  `A₀[n²]` over `ℤ[π₀]/n²`;
* `γ := (a + bπ₀) ≫ α ∈ L A` has `γ(P) = α(w) = (β ≫ α)(z) = n·z = x`;
* `n·x = 0` means `γ` kills `n·P`, and `nP` generates `A₀[n]` (the annihilator clause of
  `CyclicTorsion`), so `γ` kills `A₀[n]` and `γ = n·γ'` in `L A`
  (`exists_homPi_smul_eq`: G3-div + cancelling `[n]`, `cancel_of_ne_one`);
* `φ₁(x) = (γ ≫ φ₁)(P) = (n·f(nγ'))(P) = f(γ')(n²P) = 0`.

No counting and no ℓ-adic input. The `p`-part of G8(ii) is entirely in the hypothesis that the
link `α ≫ β = [n]` has `n` **invertible in `k`**.

Functoriality: `postHom (compPi φ ψ) = postHom ψ ∘ postHom φ`, `postHom idPi = id`; with
`postHomAdd_injective` (G8) `postHom` is injective once `L A ≠ 0`.

## 2. Isomorphisms and automorphisms (`DeuringG8IntIso`, `DeuringClassLatticeAlg`)

* `Link π₀ π`: `∃ α β n, IsUnit (n : k) ∧ … ∧ α ≫ β = [n]`.
* `postHomSurj_of_link`: `MinimalOrder` + `Link π₀ π` ⇒ `PostHomSurj π₀ π π'` for every
  target `(A', π')`.
* **`nonempty_iso_iff`**: with `PostHomSurj` in both directions and `L A, L A' ≠ 0`:
  `Nonempty {e : A' ≅ A // IsMonHom e.hom ∧ e.hom ≫ π = π' ≫ e.hom} ↔
   ∃ f : L A' ≃ₗ[ℤ] L A, f ∘ piAct = piAct ∘ f`.
* **`card_aut_eq`**: `#{e : A ≅ A // …} = #{u : (End_ℤ (L A))ˣ // u·piAct = piAct·u}`.
* Algebra: `conj_of_linearEquiv` / `linearEquiv_of_conj` (a `ℤ[F]`-isomorphism `L ≃ L'` ⇔
  `g [F]_b g⁻¹ = [F']_{b'}`), and `stabEquiv : Aut_{ℤ[F]}(L) ≃ Stab_{GL₂(ℤ)}([F]_b)`.

## 3. Assembly (`DeuringClassLattice`)

**Sites.** `K` finite ⇒ the `E_W` form a small set, so one big fppf site contains all of them
and `Spec K̄` (`nonempty_globalSite`, Stacks `BigFppfSite.exists_containing`). `Λ`, `J₀` and
all `PairSite`s are taken in this `GlobalSite`; then `(G.pair W W').left = G.site W`
definitionally, so G1's `mem_orbit_iff_nonempty_jacIso` / `card_stabilizer_eq_card_jacAut`
plug directly into `nonempty_iso_iff` / `card_aut_eq`. **No site-independence lemma is
needed** (this removes item (d) of `ARITH_DEURING_G5.md` §5 for G8, though not for
`WeierstrassDescent`, which is stated for every site).

**`Λ`** (`exists_latticeMatrix_fam`, `exists_latticeMatrix_global`): needs only **`TateFinitenessPol`** (not
`TateFiniteness`): one homomorphism from `tate_exists_frobHom_pol`, the other from the proved
`Radicial.frobHomDual`, then `frobLattice_trDet`.

**`rel_iff`** (`rel_iff_fam` + `mem_orbit_iff_global`): `W' ∈ orbit W ⇔ Nonempty (G.pair W W').JacIso` (G1) ⇔
`L(W') ≃_{ℤ[π]} L(W)` (`nonempty_iso_iff`) ⇔ `∃ g, g Λ_{W'} g⁻¹ = Λ_W` ⇔
`∃ g, g • Λ W = Λ W'`.

**`card_stab`** (`card_stab_fam` + `card_stabilizer_global`): `#Stab(W) = #Aut_π(J_W)` (G1) `= #Aut_{ℤ[π]}(L W)`
(`card_aut_eq`) `= #Stab_{GL₂(ℤ)}(Λ W)` (`stabEquiv`).

**`surj_class`**: G5 `surjClass_of_descent_minimal` with `S := G.site W`.

## 4. Headline

```lean
theorem nonempty_classLattice_of_tate (hfin : TateFinitenessPol K) (hlink : PrimeToPLink K)
    (hp : ¬ (ringChar K : ℤ) ∣ t) (hlt : t ^ 2 < 4 * (Nat.card K : ℤ)) (C : IsogClass K t) :
    Nonempty (DeuringClassLattice K t (IsogClassPred C))
  -- = nonempty_classLattice hfin hlink (WModel.weierstrassDescent K) (MinBase.existsMinimalBase K)

theorem deuringClassLatticeAll_of_props (hfin : TateFinitenessPolAll)
    (hlink : PrimeToPLinkAll) (p : ℕ) [Fact p.Prime] : DeuringClassLatticeAll p

theorem deuringMultiplicity_of_props (hfin : TateFinitenessPolAll)
    (hlink : PrimeToPLinkAll) (p : ℕ) [Fact p.Prime] : DeuringMultiplicity hurwitz p (mult p)
```

`WeierstrassDescent` and `ExistsMinimalBase` are discharged by the committed theorems
`WModel.weierstrassDescent` (`DeuringWModel`) and `MinBase.existsMinimalBase` (`DeuringMinBase`).
(`TateFinitenessPolAll` follows from `TateFinitenessAll`.) The more general
`nonempty_classLattice` (with `hD`, `hbase` as hypotheses) is kept.

**Engineering note.** The family-level theorems are stated for an abstract
`J : ∀ W [W.IsElliptic], FrobeniusJacobian W`; concrete use takes
`J := fun W _ => (G.site W).frobeniusJacobian` (a lambda, so the Λ spec is syntactically G5's).
G1's pair-site Jacobians `P.JR/JL/πR/πL` are definitionally the family's objects, group
structures and Frobenii, and each piece is cheap by `rfl`, but unifying the whole
`{e // IsMonHom e.hom ∧ …}` subtype at once times out (≥ 4M heartbeats);
`nonempty_equivIso_congr` transports along the pieces (`subst`/`cases` on `HEq`s).

## 5. Named Props (all remaining gaps)

| Prop | Where | Meaning | Status / route |
|---|---|---|---|
| **`PrimeToPLink K`** (new) | `DeuringClassLattice` | two concrete Jacobians of the same ordinary trace with a nonzero equivariant hom `J ⟶ J'` have equivariant `α : J ⟶ J'`, `β : J' ⟶ J`, `α ≫ β = [n]`, `p ∤ n` | the `p`-part of G8(ii); open. True: `p ∤ [O_K : ℤ[π]]` since `disc ℤ[π] ≡ t² ≢ 0 (p)`, and the class of `𝔭 ∣ p` in `Pic(O)` contains ideals prime to `p`, so `E^{(p)} ≅ E/E[𝔞]` with `p ∤ N𝔞` (Deuring lifting / CM). Lean routes: (i) CM theory; (ii) `p`-divisible groups, `ℤ_p[π] ≅ ℤ_p × ℤ_p` (connected–étale splitting), so that every isogeny factors as étale ∘ `F^r` and `F^r` can be replaced by `V^{fm−r}` using `E^{(q)} ≅ E`. Neither is in the library. |
| `TateFinitenessPol K` | `DeuringG7FinCore` | unchanged (weaker than `TateFiniteness`) | G7 |

`WeierstrassDescent K` and `ExistsMinimalBase K` are no longer open (see §4).

Why the `p`-part cannot be avoided by a Bezout trick: the integers `n` with
`n • f ∈ im postHom` form an ideal of `ℤ`, and G8(ii) is proved here once that ideal contains an
integer prime to `p`. But `p`-power divisibility of a homomorphism is not a condition on
`k`-points (G3-div needs `n` invertible), and the `End(A)`-side trace ideal
`Hom(A,A₀)·Hom(A₀,A)` is the conductor of `ℤ[π]` in `End(A)`. That ideal contains integers prime
to `p`, but the library cannot yet show it.

## 6. Axiom audit

`nice -n 10 lake build RamanujanWeil.Arith.DeuringClassLatticeAxioms` succeeds (29491 jobs). All 31
audited declarations, including `deuringClassLatticeAll_of_props` and
`deuringMultiplicity_of_props`, depend only on `[propext, Classical.choice, Quot.sound]`.
