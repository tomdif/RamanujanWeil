import Mathlib

/-!
# Masses of group actions

For a group `G` acting on `X` and a weight `w : X → ℚ`, the *mass*
`wmass G X w = Σ_{O ∈ X/G} w(O) / #Stab(O)` (a `finsum` over the orbit space; `w` is meant to be
`G`-invariant). This file proves the four formal properties used for the Hurwitz prime-square
relation:

* `wmass_eq_of_equiv`: a bijection of orbit spaces matching `w / #Stab` preserves the mass;
* `wmass_equivariant`: an equivariant bijection, twisted by a bijection of groups, preserves it;
* `wmass_induced`: for an equivariant map `τ : Z → T` onto a transitive `G`-set, the mass of `Z`
  equals the `Stab(t₀)`-mass of the fibre `τ⁻¹(t₀)` (induction from a stabilizer);
* `wmass_fiber`: for an equivariant `π : Y → X` with finite fibres, finite stabilizers on `X` and
  finitely many orbits on `X`, `mass(Y, w) = mass(X, x ↦ Σ_{π y = x} w y)` (orbit–stabilizer).
-/

namespace RamanujanWeil.Arith.Hurwitz

open MulAction

section Mass

variable (G : Type*) [Group G] (X : Type*) [MulAction G X]

/-- The weighted mass `Σ_{O ∈ X/G} w(O.out) / #Stab_G(O.out)`. -/
noncomputable def wmass (w : X → ℚ) : ℚ :=
  ∑ᶠ O : orbitRel.Quotient G X, w O.out / Nat.card (stabilizer G O.out)

variable {G X}

theorem natCard_stabilizer_smul (g : G) (x : X) :
    Nat.card (stabilizer G (g • x)) = Nat.card (stabilizer G x) := by
  rw [stabilizer_smul_eq_stabilizer_map_conj]
  exact Subgroup.card_map_of_injective (MulAut.conj g).injective

theorem mk_eq_mk_iff_mem_orbit {x y : X} :
    (Quotient.mk'' x : orbitRel.Quotient G X) = Quotient.mk'' y ↔ x ∈ orbit G y :=
  Quotient.eq''

theorem out_mem_orbit (x : X) : (Quotient.mk'' x : orbitRel.Quotient G X).out ∈ orbit G x :=
  mk_eq_mk_iff_mem_orbit.mp (Quotient.out_eq' _)

/-- A bijection of orbit spaces that matches `w / #Stab` preserves the mass. -/
theorem wmass_eq_of_equiv {G₁ X₁ G₂ X₂ : Type*} [Group G₁] [MulAction G₁ X₁] [Group G₂]
    [MulAction G₂ X₂] (e : orbitRel.Quotient G₁ X₁ ≃ orbitRel.Quotient G₂ X₂)
    (w₁ : X₁ → ℚ) (w₂ : X₂ → ℚ)
    (h : ∀ x₁ x₂, e (Quotient.mk'' x₁) = Quotient.mk'' x₂ →
      w₂ x₂ / Nat.card (stabilizer G₂ x₂) = w₁ x₁ / Nat.card (stabilizer G₁ x₁)) :
    wmass G₁ X₁ w₁ = wmass G₂ X₂ w₂ := by
  unfold wmass
  rw [← finsum_comp_equiv e
    (f := fun O₂ : orbitRel.Quotient G₂ X₂ => w₂ O₂.out / Nat.card (stabilizer G₂ O₂.out))]
  refine finsum_congr fun O => (h O.out (e O).out ?_).symm
  rw [Quotient.out_eq', Quotient.out_eq']

/-- **Twisted equivariant bijections preserve the mass.** -/
theorem wmass_equivariant {G₁ X₁ G₂ X₂ : Type*} [Group G₁] [MulAction G₁ X₁] [Group G₂]
    [MulAction G₂ X₂] (σ : G₁ ≃ G₂) (φ : X₁ ≃ X₂) (hφ : ∀ (g : G₁) x, φ (g • x) = σ g • φ x)
    (w : X₂ → ℚ) (hw : ∀ (g : G₂) x, w (g • x) = w x) :
    wmass G₁ X₁ (fun x => w (φ x)) = wmass G₂ X₂ w := by
  have hrel : ∀ a b : X₁, (orbitRel G₁ X₁) a b ↔ (orbitRel G₂ X₂) (φ a) (φ b) := by
    intro a b
    change a ∈ orbit G₁ b ↔ φ a ∈ orbit G₂ (φ b)
    constructor
    · rintro ⟨g, rfl⟩
      exact ⟨σ g, (hφ g b).symm⟩
    · rintro ⟨g, hg⟩
      refine ⟨σ.symm g, φ.injective ?_⟩
      change φ (σ.symm g • b) = φ a
      rw [hφ, Equiv.apply_symm_apply]
      exact hg
  refine wmass_eq_of_equiv (Quotient.congr φ hrel) _ _ fun x₁ x₂ hx => ?_
  have hx' : φ x₁ ∈ orbit G₂ x₂ := by
    rw [← mk_eq_mk_iff_mem_orbit]
    exact (Quotient.congr_mk φ hrel x₁).symm.trans hx
  obtain ⟨g, hg⟩ := hx'
  beta_reduce at hg
  have h1 : w x₂ = w (φ x₁) := by rw [← hg, hw]
  have h2 : Nat.card (stabilizer G₂ x₂) = Nat.card (stabilizer G₂ (φ x₁)) := by
    rw [← hg, natCard_stabilizer_smul]
  rw [h1, h2]
  congr 2
  refine Nat.card_congr
    { toFun := fun s => ⟨σ.symm s.1, φ.injective ?_⟩
      invFun := fun s => ⟨σ s.1, ?_⟩
      left_inv := fun s => by simp
      right_inv := fun s => by simp }
  · change φ (σ.symm s.1 • x₁) = φ x₁
    rw [hφ, Equiv.apply_symm_apply]
    exact s.2
  · change σ s.1 • φ x₁ = φ x₁
    rw [← hφ]
    exact congrArg φ s.2

/-! ### Induction from a stabilizer -/

section Induced

variable {Z T : Type*} [MulAction G Z] [MulAction G T]

/-- The fibre `τ⁻¹(t₀)` of an equivariant map, a `Stab(t₀)`-set. -/
def Fib (τ : Z →[G] T) (t₀ : T) : Type _ := {z : Z // τ z = t₀}

instance (τ : Z →[G] T) (t₀ : T) : MulAction (stabilizer G t₀) (Fib τ t₀) where
  smul h z := ⟨(h : G) • z.1, by rw [map_smul, z.2]; exact h.2⟩
  one_smul z := Subtype.ext (one_smul G z.1)
  mul_smul h k z := Subtype.ext (mul_smul (h : G) (k : G) z.1)

lemma Fib.smul_val (τ : Z →[G] T) (t₀ : T) (h : stabilizer G t₀) (z : Fib τ t₀) :
    (h • z).1 = (h : G) • z.1 := rfl

/-- **Induction.** If `G` acts transitively on `T`, the `G`-mass of `Z` is the `Stab(t₀)`-mass of
the fibre over `t₀`. -/
theorem wmass_induced (τ : Z →[G] T) (t₀ : T) (htr : ∀ t, ∃ g : G, g • t₀ = t) (w : Z → ℚ)
    (hw : ∀ (g : G) z, w (g • z) = w z) :
    wmass G Z w = wmass (stabilizer G t₀) (Fib τ t₀) (fun z => w z.1) := by
  have resp : ∀ a b : Fib τ t₀, (orbitRel (stabilizer G t₀) (Fib τ t₀)) a b →
      (orbitRel G Z) a.1 b.1 := by
    rintro a b ⟨h, rfl⟩
    exact ⟨(h : G), rfl⟩
  let f : orbitRel.Quotient (stabilizer G t₀) (Fib τ t₀) → orbitRel.Quotient G Z :=
    Quotient.map' (fun z : Fib τ t₀ => z.1) resp
  have hf : Function.Bijective f := by
    constructor
    · intro O₁ O₂ h
      induction O₁ using Quotient.inductionOn' with
      | h a =>
      induction O₂ using Quotient.inductionOn' with
      | h b =>
      have h' : a.1 ∈ orbit G b.1 := Quotient.exact' h
      obtain ⟨g, hg⟩ := h'
      have hgt : g ∈ stabilizer G t₀ := by
        rw [mem_stabilizer_iff]
        have := congrArg τ hg
        rw [map_smul, a.2, b.2] at this
        exact this
      exact Quotient.sound' ⟨⟨g, hgt⟩, Subtype.ext hg⟩
    · intro O
      induction O using Quotient.inductionOn' with
      | h z =>
      obtain ⟨g, hg⟩ := htr (τ z)
      refine ⟨Quotient.mk'' ⟨g⁻¹ • z, ?_⟩, ?_⟩
      · rw [map_smul, ← hg, inv_smul_smul]
      · exact Quotient.sound' ⟨g⁻¹, rfl⟩
  symm
  refine wmass_eq_of_equiv (Equiv.ofBijective f hf) _ _ fun x₁ x₂ hx => ?_
  have hx' : x₁.1 ∈ orbit G x₂ := Quotient.exact' hx
  obtain ⟨g, hg⟩ := hx'
  beta_reduce at hg
  have h1 : w x₂ = w x₁.1 := by rw [← hg, hw]
  have h2 : Nat.card (stabilizer G x₂) = Nat.card (stabilizer G x₁.1) := by
    rw [← hg, natCard_stabilizer_smul]
  rw [h1, h2]
  congr 2
  refine Nat.card_congr
    { toFun := fun s => ⟨⟨s.1, ?_⟩, Subtype.ext s.2⟩
      invFun := fun s => ⟨s.1.1, congrArg Subtype.val s.2⟩
      left_inv := fun s => rfl
      right_inv := fun s => rfl }
  rw [mem_stabilizer_iff]
  have := congrArg τ s.2
  rw [map_smul, x₁.2] at this
  exact this

end Induced

/-! ### Linearity -/

theorem wmass_add [Finite (orbitRel.Quotient G X)] (w₁ w₂ : X → ℚ) :
    wmass G X (fun x => w₁ x + w₂ x) = wmass G X w₁ + wmass G X w₂ := by
  unfold wmass
  rw [← finsum_add_distrib (Set.toFinite _) (Set.toFinite _)]
  exact finsum_congr fun O => add_div _ _ _

theorem wmass_const_mul [Finite (orbitRel.Quotient G X)] (c : ℚ) (w : X → ℚ) :
    wmass G X (fun x => c * w x) = c * wmass G X w := by
  unfold wmass
  rw [mul_finsum]
  exact finsum_congr fun O => mul_div_assoc _ _ _

theorem wmass_congr {w₁ w₂ : X → ℚ} (h : ∀ x, w₁ x = w₂ x) : wmass G X w₁ = wmass G X w₂ := by
  rw [show w₁ = w₂ from funext h]

/-! ### Orbit–stabilizer along an equivariant map -/

section Fiber

variable {Y : Type*} [MulAction G Y]

/-- The `Stab(x)`-orbit count inside the fibre: `#{y ∈ π⁻¹(x) : y ∼ y₀} · #Stab(y₀) = #Stab(x)`. -/
theorem card_fiber_orbit_mul (π : Y → X) (hπ : ∀ (g : G) y, π (g • y) = g • π y) (x : X)
    (y₀ : Y) (hy₀ : π y₀ = x) :
    Nat.card {y : {y // π y = x} // (Quotient.mk'' y.1 : orbitRel.Quotient G Y) =
        Quotient.mk'' y₀} * Nat.card (stabilizer G y₀) = Nat.card (stabilizer G x) := by
  let S := stabilizer G x
  have e1 : {y : {y // π y = x} // (Quotient.mk'' y.1 : orbitRel.Quotient G Y) =
      Quotient.mk'' y₀} ≃ orbit S y₀ :=
    { toFun := fun y => ⟨y.1.1, by
        have h : y.1.1 ∈ orbit G y₀ := Quotient.exact' y.2
        obtain ⟨g, hg⟩ := h
        have hgS : g ∈ S := by
          rw [mem_stabilizer_iff]
          have := y.1.2
          rw [← hg, hπ, hy₀] at this
          exact this
        exact ⟨⟨g, hgS⟩, hg⟩⟩
      invFun := fun z => ⟨⟨z.1, by
          obtain ⟨s, hs⟩ := z.2
          rw [← hs]
          change π ((s : G) • y₀) = x
          rw [hπ, hy₀]
          exact s.2⟩, by
          obtain ⟨s, hs⟩ := z.2
          exact Quotient.sound' ⟨(s : G), hs⟩⟩
      left_inv := fun y => rfl
      right_inv := fun z => rfl }
  have e2 : stabilizer S y₀ ≃ stabilizer G y₀ :=
    { toFun := fun s => ⟨s.1.1, s.2⟩
      invFun := fun g => ⟨⟨g.1, by
          rw [mem_stabilizer_iff]
          have := congrArg π g.2
          rw [hπ, hy₀] at this
          exact this⟩, g.2⟩
      left_inv := fun s => rfl
      right_inv := fun g => rfl }
  rw [Nat.card_congr e1, ← Nat.card_congr e2, ← Nat.card_prod,
    Nat.card_congr (orbitProdStabilizerEquivGroup S y₀)]

/-- **Fibre formula (orbit–stabilizer).** -/
theorem wmass_fiber (π : Y → X) (hπ : ∀ (g : G) y, π (g • y) = g • π y)
    [Finite (orbitRel.Quotient G X)] (hS : ∀ x : X, Finite (stabilizer G x))
    (hF : ∀ x : X, Finite {y // π y = x}) (w : Y → ℚ) (hw : ∀ (g : G) y, w (g • y) = w y) :
    wmass G Y w = wmass G X (fun x => ∑ᶠ y : {y // π y = x}, w y.1) := by
  classical
  have hYfin : Finite (orbitRel.Quotient G Y) := by
    refine Finite.of_surjective
      (fun s : (Σ O : orbitRel.Quotient G X, {y // π y = O.out}) =>
        (Quotient.mk'' s.2.1 : orbitRel.Quotient G Y)) ?_
    intro OY
    induction OY using Quotient.inductionOn' with
    | h y =>
    obtain ⟨g, hg⟩ := out_mem_orbit (G := G) (π y)
    beta_reduce at hg
    refine ⟨⟨Quotient.mk'' (π y), ⟨g • y, by rw [hπ, hg]⟩⟩, ?_⟩
    exact Quotient.sound' ⟨g, rfl⟩
  let _ := Fintype.ofFinite (orbitRel.Quotient G X)
  let _ := Fintype.ofFinite (orbitRel.Quotient G Y)
  let _ : ∀ x, Fintype {y // π y = x} := fun x => @Fintype.ofFinite _ (hF x)
  unfold wmass
  rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype]
  simp_rw [finsum_eq_sum_of_fintype]
  have key : ∀ OX : orbitRel.Quotient G X,
      (∑ y : {y // π y = OX.out}, w y.1) / Nat.card (stabilizer G OX.out) =
        ∑ OY : orbitRel.Quotient G Y,
          if (Quotient.mk'' (π OY.out) : orbitRel.Quotient G X) = OX then
            w OY.out / Nat.card (stabilizer G OY.out) else 0 := by
    intro OX
    have hSpos : 0 < Nat.card (stabilizer G OX.out) := by
      have := hS OX.out
      exact Nat.card_pos
    rw [Finset.sum_div, ← Finset.sum_fiberwise Finset.univ
      (fun y : {y // π y = OX.out} => (Quotient.mk'' y.1 : orbitRel.Quotient G Y))]
    refine Finset.sum_congr rfl fun OY _ => ?_
    have hconst : ∀ y ∈ Finset.univ.filter (fun y : {y // π y = OX.out} =>
        (Quotient.mk'' y.1 : orbitRel.Quotient G Y) = OY),
        w y.1 / Nat.card (stabilizer G OX.out) = w OY.out / Nat.card (stabilizer G OX.out) := by
      intro y hy
      rw [Finset.mem_filter] at hy
      have : y.1 ∈ orbit G OY.out := by
        rw [← mk_eq_mk_iff_mem_orbit, Quotient.out_eq']
        exact hy.2
      obtain ⟨g, hg⟩ := this
      beta_reduce at hg
      rw [← hg, hw]
    rw [Finset.sum_congr rfl hconst, Finset.sum_const, nsmul_eq_mul]
    split_ifs with hO
    · -- a representative of `OY` in the fibre over `OX.out`
      have : OX.out ∈ orbit G (π OY.out) := by
        rw [← mk_eq_mk_iff_mem_orbit, Quotient.out_eq', hO]
      obtain ⟨g, hg⟩ := this
      beta_reduce at hg
      have hy₀ : π (g • OY.out) = OX.out := by rw [hπ, hg]
      have hc := card_fiber_orbit_mul π hπ OX.out (g • OY.out) hy₀
      have hOY : (Quotient.mk'' (g • OY.out) : orbitRel.Quotient G Y) = OY := by
        have h3 : (Quotient.mk'' (g • OY.out) : orbitRel.Quotient G Y) = Quotient.mk'' OY.out :=
          Quotient.sound' ⟨g, rfl⟩
        rw [h3, Quotient.out_eq']
      rw [hOY, natCard_stabilizer_smul] at hc
      have hcard : (Finset.univ.filter (fun y : {y // π y = OX.out} =>
          (Quotient.mk'' y.1 : orbitRel.Quotient G Y) = OY)).card =
          Nat.card {y : {y // π y = OX.out} //
            (Quotient.mk'' y.1 : orbitRel.Quotient G Y) = OY} := by
        rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
      rw [hcard]
      have hpos : (Nat.card (stabilizer G OY.out) : ℚ) ≠ 0 := by
        intro h0
        rw [Nat.cast_eq_zero] at h0
        rw [h0, mul_zero] at hc
        omega
      have hc' : (Nat.card {y : {y // π y = OX.out} //
          (Quotient.mk'' y.1 : orbitRel.Quotient G Y) = OY} : ℚ) *
          Nat.card (stabilizer G OY.out) = Nat.card (stabilizer G OX.out) := by
        exact_mod_cast hc
      have hSq : (Nat.card (stabilizer G OX.out) : ℚ) ≠ 0 := by exact_mod_cast hSpos.ne'
      field_simp
      linear_combination (w OY.out) * hc'
    · have hempty : Finset.univ.filter (fun y : {y // π y = OX.out} =>
          (Quotient.mk'' y.1 : orbitRel.Quotient G Y) = OY) = ∅ := by
        rw [Finset.filter_eq_empty_iff]
        intro y _ hy
        apply hO
        have : y.1 ∈ orbit G OY.out := by
          rw [← mk_eq_mk_iff_mem_orbit, Quotient.out_eq']
          exact hy
        obtain ⟨g, hg⟩ := this
        beta_reduce at hg
        have h2 : π y.1 = g • π OY.out := by rw [← hg, hπ]
        have h4 : π OY.out ∈ orbit G OX.out := ⟨g⁻¹, by
          change g⁻¹ • OX.out = π OY.out
          rw [← y.2, h2, inv_smul_smul]⟩
        rw [mk_eq_mk_iff_mem_orbit.mpr h4, Quotient.out_eq']
      rw [hempty, Finset.card_empty]
      simp
  rw [Finset.sum_congr rfl fun OX _ => key OX, Finset.sum_comm]
  refine Finset.sum_congr rfl fun OY _ => ?_
  rw [Finset.sum_ite_eq]
  simp

end Fiber

end Mass

end RamanujanWeil.Arith.Hurwitz
