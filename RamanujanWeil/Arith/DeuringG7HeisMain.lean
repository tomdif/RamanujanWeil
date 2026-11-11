import RamanujanWeil.Arith.DeuringG7HeisZeros
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable

/-!
# A3-ord, G7 Heisenberg: the commutator pairing on `E[N]` is nondegenerate

`docs/ARITH_DEURING_G7_AJHEIS.md` §2. Let `F = F̄`, `W / F` elliptic, `N ≥ 3` odd, and suppose
`E[N] ≅ (ℤ/N)²` (for `char F ∤ N` this comes from `J_W[N]` through Abel–Jacobi,
`DeuringG7HeisAll`). Then **`ThetaHeisenberg W N`**: a central element `g = (f, S)` of
`𝒢 = 𝒢(𝒪(N·O))` lies over `S = O`.

**Proof (a zero count, no Galois theory).** Suppose `S ≠ O`.

1. Since `E[N] ≅ (ℤ/N)²` and `N` is odd, some `P ∈ E[N]` has `#⟨P, S⟩ ≥ 3N`
   (`exists_big_closure`).
2. `P ∈ E[N] = K(L)`, so some `g' ∈ 𝒢` lies over `P`. Since `g` is central, the operators of `g`
   and `g'` on `V = L(N·O)` commute, so they have a common eigenvector `v`
   (`exists_common_eigenvector`). Every element of `⟨P, S⟩` is then the image of an element of
   `𝒢` having `v` as an eigenvector (`eigenPts`).
3. `v` is not constant: otherwise `f ∈ F`, which forces `S = O`
   (`right_eq_zero_of_left_const`). So `v` has a zero `Z₀` (`exists_zero`).
4. For `R ∈ ⟨P, S⟩` with `R ≠ Z₀` and `2R ≠ Z₀`, the point `Z₀ − R` is again a zero of `v`
   (`eval_eq_zero_of_eigen`, applied to `(h, R) v = μ v`). Since `N` is odd, at most one `R`
   has `2R = Z₀`. So `v` has at least `3N − 2` zeros `Z₀ − R`.
5. Their `x`-coordinates are roots of `N(v) = v · σ v`, a polynomial of degree `≤ N`, and each
   `x` comes from at most two `R`. So there are at most `2N` zeros, which is a contradiction.

The hypothesis `E[N] ≅ (ℤ/N)²` cannot be dropped: for `char F = p ∣ N` the statement is false
on ordinary curves (`E[p] ≅ ℤ/p`).
-/

noncomputable section

namespace RamanujanWeil.Arith.Deuring.Geom.G7.DGeom

open WeierstrassCurve WeierstrassCurve.Affine Polynomial
open scoped nonZeroDivisors Polynomial.Bivariate

universe u

set_option linter.unusedSectionVars false

open scoped Classical

/-! ### Pure algebra -/

section Algebra

theorem zmod_eq_zero_of_two_mul {N : ℕ} (hodd : Odd N) {s : ZMod N} (h : 2 * s = 0) : s = 0 := by
  obtain ⟨m, hm⟩ := hodd
  have h1 : ((m : ZMod N) + 1) * 2 = 1 := by
    have : ((2 * m + 1 : ℕ) : ZMod N) = 0 := by rw [← hm]; exact ZMod.natCast_self N
    push_cast at this
    linear_combination this
  calc s = ((m : ZMod N) + 1) * 2 * s := by rw [h1, one_mul]
    _ = ((m : ZMod N) + 1) * (2 * s) := by ring
    _ = 0 := by rw [h, mul_zero]

/-- **In `(ℤ/N)²` (`N ≥ 3` odd), every `s ≠ 0` lies in a subgroup `⟨p, s⟩` with `≥ 3N`
elements**, transported to any `T ≅ (ℤ/N)²`. -/
theorem exists_big_closure {A : Type*} [AddCommGroup A] {N : ℕ} (hN : 3 ≤ N) (hodd : Odd N)
    (T : AddSubgroup A) (e : T ≃+ (Fin 2 → ZMod N)) {S : A} (hS : S ∈ T) (hS0 : S ≠ 0) :
    ∃ P ∈ T, 3 * N ≤ Nat.card (AddSubgroup.closure ({P, S} : Set A)) := by
  have : NeZero N := ⟨by omega⟩
  set s := e ⟨S, hS⟩
  have hs : s ≠ 0 := by
    intro h
    apply hS0
    have := congrArg Subtype.val ((AddEquiv.map_eq_zero_iff e).1 h)
    exact this
  obtain ⟨i, hi⟩ : ∃ i, s i ≠ 0 := by
    by_contra h
    push Not at h
    exact hs (funext h)
  set j : Fin 2 := if i = 0 then 1 else 0
  have hij : i ≠ j := by
    fin_cases i <;> simp [j]
  set p : Fin 2 → ZMod N := Pi.single j 1
  set P : A := (e.symm p).1
  have hPT : P ∈ T := (e.symm p).2
  refine ⟨P, hPT, ?_⟩
  set G := AddSubgroup.closure ({P, S} : Set A)
  have hGT : G ≤ T := by
    rw [AddSubgroup.closure_le]
    rintro z (rfl | rfl)
    · exact hPT
    · exact hS
  have hfinT : Finite T := Finite.of_equiv _ e.symm.toEquiv
  have hfinG : Finite G := Finite.of_injective (AddSubgroup.inclusion hGT)
    (AddSubgroup.inclusion_injective hGT)
  have hPG : P ∈ G := AddSubgroup.subset_closure (Set.mem_insert _ _)
  have hSG : S ∈ G := AddSubgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  let ι : Fin 3 × ZMod N → G := fun ab =>
    ⟨(ab.1 : ℕ) • S + ab.2.val • P, G.add_mem (G.nsmul_mem hSG _) (G.nsmul_mem hPG _)⟩
  have hι : Function.Injective ι := by
    rintro ⟨a, b⟩ ⟨a', b'⟩ hab
    have h1 : (a : ℕ) • S + b.val • P = (a' : ℕ) • S + b'.val • P := congrArg Subtype.val hab
    have h2 : e ((a : ℕ) • (⟨S, hS⟩ : T) + b.val • (⟨P, hPT⟩ : T)) =
        e ((a' : ℕ) • (⟨S, hS⟩ : T) + b'.val • (⟨P, hPT⟩ : T)) := by
      congr 1; exact Subtype.ext h1
    have hPe : e ⟨P, hPT⟩ = p := by
      change e (e.symm p) = p
      exact e.apply_symm_apply p
    rw [map_add, map_add, map_nsmul, map_nsmul, map_nsmul, map_nsmul, hPe] at h2
    have hi' := congrFun h2 i
    have hj' := congrFun h2 j
    simp only [Pi.add_apply, Pi.smul_apply] at hi' hj'
    simp only [p, Pi.single_eq_of_ne hij, Pi.single_eq_same, nsmul_eq_mul, mul_zero, add_zero,
      mul_one] at hi' hj'
    change (a : ℕ) * s i = (a' : ℕ) * s i at hi'
    have haa : a = a' := by
      have hd : ((a : ℕ) - (a' : ℕ) : ZMod N) * s i = 0 := by
        rw [sub_mul]; exact sub_eq_zero.2 hi'
      fin_cases a <;> fin_cases a' <;> simp at hd ⊢
      all_goals first
        | exact hi hd
        | exact hi (by linear_combination hd)
        | exact hi (by linear_combination -hd)
        | exact hi (zmod_eq_zero_of_two_mul hodd (by linear_combination hd))
    subst haa
    have hbb : (b.val : ZMod N) = (b'.val : ZMod N) := by linear_combination hj'
    rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val] at hbb
    rw [hbb]
  have := Nat.card_le_card_of_injective ι hι
  rwa [Nat.card_prod, Nat.card_eq_fintype_card, Fintype.card_fin, Nat.card_zmod] at this

/-- **Two commuting operators have a common eigenvector** (finite dimension, `K = K̄`). -/
theorem exists_common_eigenvector {K V : Type*} [Field K] [IsAlgClosed K] [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] [Nontrivial V] (A B : Module.End K V)
    (hAB : A * B = B * A) :
    ∃ v : V, v ≠ 0 ∧ (∃ a : K, A v = a • v) ∧ (∃ b : K, B v = b • v) := by
  obtain ⟨a, ha⟩ := Module.End.exists_eigenvalue A
  have hmaps : ∀ x ∈ A.eigenspace a, B x ∈ A.eigenspace a := fun x hx => by
    rw [Module.End.mem_eigenspace_iff] at hx ⊢
    have : A (B x) = B (A x) := by rw [← Module.End.mul_apply, hAB, Module.End.mul_apply]
    rw [this, hx, map_smul]
  have : Nontrivial (A.eigenspace a) :=
    Submodule.nontrivial_iff_ne_bot.2 (Module.End.hasEigenvalue_iff.1 ha)
  obtain ⟨b, hb⟩ := Module.End.exists_eigenvalue (B.restrict hmaps)
  obtain ⟨w, hw⟩ := hb.exists_hasEigenvector
  refine ⟨w.1, fun h => hw.2 (Subtype.ext h), ⟨a, Module.End.mem_eigenspace_iff.1 w.2⟩, ⟨b, ?_⟩⟩
  have := Module.End.mem_eigenspace_iff.1 hw.1
  exact congrArg Subtype.val this

end Algebra

variable {F : Type u} [Field F] (W : Affine F) [W.IsElliptic] [DecidableEq F]

local notation "cK" => algebraMap F (Kf W)
local notation "ιK" => algebraMap (Rg W) (Kf W)

/-! ### Operators on `V` -/

section Op

variable (V : Submodule F (Kf W))

theorem thetaAct_mem {g : Amb W} (hg : g ∈ thetaGroup W V) {v : Kf W} (hv : v ∈ V) :
    thetaAct W g v ∈ V := by
  rw [mem_thetaGroup] at hg
  rw [← hg]
  exact Submodule.mem_map_of_mem hv

/-- The operator of `g ∈ 𝒢(V)` on `V`. -/
def opV (g : thetaGroup W V) : Module.End F V :=
  (thetaAct W g).restrict fun _ hv => thetaAct_mem W V g.2 hv

theorem opV_apply (g : thetaGroup W V) (v : V) : (opV W V g v : Kf W) = thetaAct W g v := rfl

theorem opV_mul (g h : thetaGroup W V) : opV W V (g * h) = opV W V g * opV W V h := by
  ext v
  rw [opV_apply, Module.End.mul_apply, opV_apply, opV_apply, Subgroup.coe_mul, thetaAct_mul]
  rfl

theorem thetaAct_injective (g : Amb W) : Function.Injective (thetaAct W g) := by
  intro a b hab
  rw [thetaAct_apply, thetaAct_apply] at hab
  exact (trans W _).toRingHom.injective (mul_left_cancel₀ (g.left.ne_zero) hab)

/-- **The translations by elements of `𝒢(V)` having `v` as an eigenvector.** -/
def eigenPts (v : Kf W) : AddSubgroup (W⁄F).Point where
  carrier := {R | ∃ g ∈ thetaGroup W V, g.right = Multiplicative.ofAdd R ∧
    ∃ μ : F, thetaAct W g v = μ • v}
  zero_mem' := ⟨1, (thetaGroup W V).one_mem, rfl, 1, by rw [thetaAct_one, one_smul]; rfl⟩
  add_mem' := by
    rintro R R' ⟨g, hg, hgR, μ, hμ⟩ ⟨g', hg', hgR', μ', hμ'⟩
    refine ⟨g * g', (thetaGroup W V).mul_mem hg hg', ?_, μ * μ', ?_⟩
    · rw [SemidirectProduct.mul_right, hgR, hgR']; rfl
    · rw [thetaAct_mul, LinearMap.comp_apply, hμ', map_smul, hμ, smul_smul, mul_comm]
  neg_mem' := by
    rintro R ⟨g, hg, hgR, μ, hμ⟩
    refine ⟨g⁻¹, (thetaGroup W V).inv_mem hg, ?_, ?_⟩
    · rw [SemidirectProduct.inv_right, hgR]; rfl
    · by_cases hv : v = 0
      · exact ⟨0, by rw [hv, map_zero, smul_zero]⟩
      have hμ0 : μ ≠ 0 := by
        rintro rfl
        rw [zero_smul] at hμ
        exact hv (thetaAct_injective W g (hμ.trans (map_zero _).symm))
      refine ⟨μ⁻¹, ?_⟩
      have h1 : v = thetaAct W g⁻¹ (thetaAct W g v) := by
        rw [← LinearMap.comp_apply, ← thetaAct_mul, inv_mul_cancel, thetaAct_one]; rfl
      rw [hμ, map_smul] at h1
      calc thetaAct W g⁻¹ v = μ⁻¹ • (μ • thetaAct W g⁻¹ v) := by
            rw [smul_smul, inv_mul_cancel₀ hμ0, one_smul]
        _ = μ⁻¹ • v := by rw [← h1]

end Op

/-! ### The zero count -/

section Main

variable [IsAlgClosed F]

theorem two_nsmul_injOn {N : ℕ} (hodd : Odd N) {R R' : (W⁄F).Point}
    (hR : R ∈ AddSubgroup.torsionBy (W⁄F).Point (N : ℤ))
    (hR' : R' ∈ AddSubgroup.torsionBy (W⁄F).Point (N : ℤ)) (h : 2 • R = 2 • R') : R = R' := by
  obtain ⟨m, hm⟩ := hodd
  have h1 : (N : ℤ) • (R - R') = 0 := by
    rw [smul_sub]
    rw [(Submodule.mem_torsionBy_iff _ _).1 hR, (Submodule.mem_torsionBy_iff _ _).1 hR', sub_zero]
  have h2 : (2 : ℤ) • (R - R') = 0 := by
    rw [smul_sub, sub_eq_zero]; exact_mod_cast h
  have : R - R' = (N : ℤ) • (R - R') - (m : ℤ) • ((2 : ℤ) • (R - R')) := by
    rw [smul_smul, ← sub_smul, hm]; push_cast; ring_nf; rw [one_smul]
  rw [h1, h2, smul_zero, sub_zero] at this
  exact sub_eq_zero.1 this

/-- **The Heisenberg property from `E[N] ≅ (ℤ/N)²`** (`N ≥ 3` odd). -/
theorem thetaHeisenberg_of_torsion {N : ℕ} (hN : 3 ≤ N) (hodd : Odd N)
    (htor : Nonempty (AddSubgroup.torsionBy (W⁄F).Point (N : ℤ) ≃+ (Fin 2 → ZMod N))) :
    ThetaHeisenberg W N := by
  intro g hc
  set S := (g : Amb W).right.toAdd with hSdef
  by_cases hS : S = 0
  · apply Multiplicative.toAdd.injective
    apply Subtype.ext
    change (g : Amb W).right.toAdd = (0 : (W⁄F).Point)
    exact hS
  exfalso
  have hker := thetaKer_eq_torsion W (rrStabilizerBridge W (by omega : 2 ≤ N))
  have hSmem : S ∈ thetaKer W (rrSpace W N) := ⟨g, g.2, rfl⟩
  obtain ⟨e⟩ := htor
  obtain ⟨P, hPT, hbig⟩ := exists_big_closure hN hodd _ e (hker ▸ hSmem) hS
  obtain ⟨g', hg', hg'P⟩ : P ∈ thetaKer W (rrSpace W N) := hker ▸ hPT
  have hcomm : opV W (rrSpace W N) g * opV W (rrSpace W N) ⟨g', hg'⟩ = opV W (rrSpace W N) ⟨g', hg'⟩ * opV W (rrSpace W N) g := by
    rw [← opV_mul, ← opV_mul, hc]
  have : Nontrivial (rrSpace W N) := ⟨⟨⟨1, one_mem_rrSpace' W N⟩, 0, fun h =>
    one_ne_zero (congrArg Subtype.val h)⟩⟩
  obtain ⟨v, hv0, ⟨a, ha⟩, ⟨b, hb⟩⟩ := exists_common_eigenvector _ _ hcomm
  set v₀ : Kf W := (v : Kf W)
  have hv₀ : v₀ ≠ 0 := fun h => hv0 (Subtype.ext h)
  have ha' : thetaAct W g v₀ = a • v₀ := congrArg Subtype.val ha
  have hb' : thetaAct W g' v₀ = b • v₀ := congrArg Subtype.val hb
  -- `v₀ = r ∈ F[E]` with a pole of order `≤ N`
  have hvV : v₀ ∈ LN W N := (rrSpace_eq_LN W N) ▸ v.2
  obtain ⟨r, hr, hrN⟩ := hvV
  have hr0 : r ≠ 0 := by rintro rfl; exact hv₀ (by rw [← hr, map_zero])
  have hdegN : normDeg W r ≤ N := by
    rw [vR_of_ne W hr0, WithZero.exp_le_exp] at hrN
    exact_mod_cast hrN
  -- `v₀` is not constant
  have hdeg1 : 1 ≤ normDeg W r := by
    by_contra hlt
    have h0 : normDeg W r = 0 := by omega
    have hle : vR W r ≤ 1 := by rw [vR_of_ne W hr0, h0]; rfl
    obtain ⟨c, hc'⟩ := exists_const_of_vR_le_one W hr0 hle
    have hv₀c : v₀ = cK c := by rw [← hr, ← hc', ιK_algebraMap]
    have hc0 : c ≠ 0 := by rintro rfl; exact hv₀ (by rw [hv₀c, map_zero])
    have hgl : (((g : Amb W).left : (Kf W)ˣ) : Kf W) = cK a := by
      have := ha'
      rw [thetaAct_apply, hv₀c, AlgHom.commutes, Algebra.smul_def] at this
      have hcK : cK c ≠ 0 := by exact (_root_.map_ne_zero _).2 hc0
      exact mul_right_cancel₀ hcK this
    exact hS (right_eq_zero_of_left_const W (by omega) g.2 hgl)
  obtain ⟨Z₀, hZ₀, hzero₀⟩ := exists_zero W hdeg1
  -- the subgroup `G = ⟨P, S⟩` acts on the zeros
  set G := AddSubgroup.closure ({P, S} : Set (W⁄F).Point)
  have hGE : G ≤ eigenPts W (rrSpace W N) v₀ := by
    rw [AddSubgroup.closure_le]
    rintro z (rfl | rfl)
    · exact ⟨g', hg', hg'P, b, hb'⟩
    · exact ⟨g, g.2, rfl, a, ha'⟩
  have hGT : G ≤ AddSubgroup.torsionBy (W⁄F).Point (N : ℤ) := by
    rw [AddSubgroup.closure_le]
    rintro z (rfl | rfl)
    · exact hPT
    · exact hker ▸ hSmem
  have hzeros : ∀ R ∈ G, R ≠ Z₀ → 2 • R ≠ Z₀ →
      ∃ hZ : Z₀ - R ≠ 0, evPt W (Z₀ - R) hZ r = 0 := by
    intro R hRG hRZ h2R
    have hZ : Z₀ - R ≠ 0 := sub_ne_zero.2 (Ne.symm hRZ)
    refine ⟨hZ, ?_⟩
    by_cases hR0 : R = 0
    · subst hR0
      rw [evPt_congr W (sub_zero Z₀) hZ hZ₀]
      exact hzero₀
    obtain ⟨γ, hγ, hγR, μ, hμ⟩ := hGE hRG
    obtain ⟨x₀, y₀, h, rfl⟩ := exists_eq_neg_some W hR0
    have hZP : (Z₀ - -(Point.some x₀ y₀ h)) + -(Point.some x₀ y₀ h) ≠ 0 := by
      rw [sub_add_cancel]; exact hZ₀
    have hx : ptX W (Z₀ - -(Point.some x₀ y₀ h)) ≠ x₀ := by
      intro hx
      have hx' : ptX W (Z₀ - -(Point.some x₀ y₀ h)) = ptX W (-(Point.some x₀ y₀ h)) := by
        rw [hx, ptX_neg]; rfl
      rcases eq_or_eq_neg_of_ptX_eq W hZ hR0 hx' with e1 | e1
      · apply h2R
        rw [two_nsmul]
        calc -(Point.some x₀ y₀ h) + -(Point.some x₀ y₀ h) =
            (Z₀ - -(Point.some x₀ y₀ h)) + -(Point.some x₀ y₀ h) := by rw [e1]
          _ = Z₀ := sub_add_cancel _ _
      · apply hZ₀
        rw [← sub_add_cancel Z₀ (-(Point.some x₀ y₀ h)), e1, neg_add_cancel]
    have hμ0 : μ ≠ 0 := by
      rintro rfl
      rw [zero_smul] at hμ
      exact hv₀ (thetaAct_injective W γ (hμ.trans (map_zero _).symm))
    have hfV := left_mem_rrSpace W hγ
    rw [rrSpace_eq_LN] at hfV
    obtain ⟨f, hf, -⟩ := hfV
    have heig : ιK f * trans W (-(Point.some x₀ y₀ h)) (ιK r) = cK μ * ιK r := by
      rw [hf, hr]
      have := hμ
      rw [thetaAct_apply, hγR, Algebra.smul_def] at this
      exact this
    have hz : evPt W (Z₀ - -(Point.some x₀ y₀ h) + -(Point.some x₀ y₀ h)) hZP r = 0 := by
      rw [evPt_congr W (sub_add_cancel Z₀ _) hZP hZ₀]
      exact hzero₀
    exact eval_eq_zero_of_eigen h hx hZP hμ0 heig hz
  -- counting
  have : NeZero N := ⟨by omega⟩
  have hfinT : Finite (AddSubgroup.torsionBy (W⁄F).Point (N : ℤ)) :=
    Finite.of_equiv _ e.symm.toEquiv
  have hfinG : (G : Set (W⁄F).Point).Finite :=
    (Set.toFinite (AddSubgroup.torsionBy (W⁄F).Point (N : ℤ) : Set (W⁄F).Point)).subset hGT
  set s := hfinG.toFinset
  have hcardG : Nat.card G = s.card := by
    rw [← Set.ncard_eq_toFinset_card _ hfinG]
    exact Nat.card_coe_set_eq (G : Set (W⁄F).Point)
  set t := s.filter fun R => R ≠ Z₀ ∧ 2 • R ≠ Z₀
  have hst : s.card ≤ t.card + 2 := by
    have hsplit : t.card + (s.filter fun R => ¬(R ≠ Z₀ ∧ 2 • R ≠ Z₀)).card = s.card :=
      Finset.card_filter_add_card_filter_not _
    have hrest : (s.filter fun R => ¬(R ≠ Z₀ ∧ 2 • R ≠ Z₀)).card ≤ 2 := by
      have hsub : (s.filter fun R => ¬(R ≠ Z₀ ∧ 2 • R ≠ Z₀)) ⊆
          {Z₀} ∪ s.filter fun R => 2 • R = Z₀ := by
        intro R hR
        rw [Finset.mem_filter] at hR
        rw [Finset.mem_union, Finset.mem_singleton, Finset.mem_filter]
        by_cases h1 : R = Z₀
        · exact Or.inl h1
        · right
          refine ⟨hR.1, ?_⟩
          by_contra h2
          exact hR.2 ⟨h1, h2⟩
      have hone : (s.filter fun R => 2 • R = Z₀).card ≤ 1 := by
        rw [Finset.card_le_one]
        intro R hR R' hR'
        rw [Finset.mem_filter, Set.Finite.mem_toFinset] at hR hR'
        exact two_nsmul_injOn W hodd (hGT hR.1) (hGT hR'.1) (hR.2.trans hR'.2.symm)
      calc _ ≤ ({Z₀} ∪ s.filter fun R => 2 • R = Z₀).card := Finset.card_le_card hsub
        _ ≤ ({Z₀} : Finset _).card + (s.filter fun R => 2 • R = Z₀).card :=
            Finset.card_union_le _ _
        _ ≤ 1 + 1 := by rw [Finset.card_singleton]; omega
        _ = 2 := rfl
    omega
  set φ : (W⁄F).Point → F := fun R => ptX W (Z₀ - R)
  have hfib : ∀ c ∈ t.image φ, (t.filter fun R => φ R = c).card ≤ 2 := by
    intro c hc
    obtain ⟨R₁, hR₁, rfl⟩ := Finset.mem_image.1 hc
    have hsub : (t.filter fun R => φ R = φ R₁) ⊆ {R₁, 2 • Z₀ - R₁} := by
      intro R hR
      rw [Finset.mem_filter] at hR
      rw [Finset.mem_insert, Finset.mem_singleton]
      have hRt := (Finset.mem_filter.1 hR.1).2
      have hR₁t := (Finset.mem_filter.1 hR₁).2
      have hZ : Z₀ - R ≠ 0 := sub_ne_zero.2 (Ne.symm hRt.1)
      have hZ₁ : Z₀ - R₁ ≠ 0 := sub_ne_zero.2 (Ne.symm hR₁t.1)
      rcases eq_or_eq_neg_of_ptX_eq W hZ hZ₁ hR.2 with e1 | e1
      · left
        exact (sub_right_inj.1 e1)
      · right
        rw [two_nsmul]
        rw [neg_sub, sub_eq_sub_iff_add_eq_add] at e1
        rw [eq_sub_iff_add_eq, add_comm]
        exact e1.symm
    exact (Finset.card_le_card hsub).trans (Finset.card_le_two)
  have htn := Finset.card_le_mul_card_image t 2 hfib
  have hnorm0 : Algebra.norm F[X] r ≠ 0 := norm_ne_zero W hr0
  have himg : t.image φ ⊆ (Algebra.norm F[X] r).roots.toFinset := by
    intro c hc
    obtain ⟨R, hR, rfl⟩ := Finset.mem_image.1 hc
    rw [Finset.mem_filter, Set.Finite.mem_toFinset] at hR
    obtain ⟨hZ, hz⟩ := hzeros R hR.1 hR.2.1 hR.2.2
    rw [Multiset.mem_toFinset, mem_roots hnorm0]
    exact isRoot_norm_of_evPt W hZ hz
  have hroots : (Algebra.norm F[X] r).roots.toFinset.card ≤ N :=
    (Multiset.toFinset_card_le _).trans ((card_roots' _).trans hdegN)
  have h1 := (Finset.card_le_card himg).trans hroots
  have h3 : 3 * N ≤ s.card := hcardG ▸ hbig
  omega

end Main

end RamanujanWeil.Arith.Deuring.Geom.G7.DGeom
