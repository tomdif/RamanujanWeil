import RamanujanWeil.Arith.DeuringG7WeilHeis
import Mathlib.Algebra.Module.Injective
import Mathlib.Algebra.Category.Grp.Injective

/-!
# A3-ord, G7-D (algebra): Mumford's descent criterion for graph quotients, group-theoretic half

`docs/ARITH_DEURING_G7D.md` §1. Let `X : 0 → A → G → K → 0` and `X' : 0 → A → G' → K' → 0` be
central extensions with the same kernel `A` (in step D: the theta groups `𝒢(𝒪(N[0]))` of `E` and
`E'`, `A = k̄^×`). The theta group of `L ⊠ L'` on `E × E'` is `G ×_A G' = (G × G')/{(a, a⁻¹)}`,
with commutator pairing `e ⊕ e'`. Mumford (*Abelian varieties*, §23, Thm. 2):
`L ⊠ L'` descends along `E × E' → (E × E')/Γ` exactly when `Γ` lifts to a **level subgroup** of
`G ×_A G'`, and the theta group of the descended bundle is `Z(Γ̃)/Γ̃`.

For the graph `Γ = {(x, u x)}` of an isomorphism `u : K ≃+ K'` a level subgroup is the same as a
`GraphLevel`: lifts `σ x ∈ G`, `σ' x ∈ G'` over `x`, `u x` whose multiplication defects are
opposite elements of `A` (so `x ↦ [σ x, σ' x]` is a homomorphism into `G ×_A G'`). Proved:

* **`exists_graphLevel`**: if `u` is anti-isometric for the commutator pairings
  (`e'(u x, u y) = −e(x, y)`) and `A` is divisible, a level structure over the graph exists.
  The subgroup `Q = {(g, g') : p' g' = u (p g)}` of `G × G'` modulo the antidiagonal is
  **abelian** (isotropy), an extension of `K` by `A`, and it splits because a divisible group is
  injective (`Module.Baer.of_divisible`).
* **`eq_of_forall_pairing_graph`**: the graph of an anti-isometry is its own orthogonal
  (`A`-valued, given the Heisenberg property of `X'`).
* **`centralizer_graphLevel`**: an element `(g, g')` of `G ×_A G'` commuting with the level
  subgroup is `(σ x, σ' x)` times a central element, i.e. **`Z(Γ̃)/Γ̃ = A`**: the descended bundle
  has trivial theta group `K(L_B) = 0`, so the descended polarization is **principal**.
-/

namespace RamanujanWeil.Arith.Deuring.Geom.G7.Fin.Weil

namespace CentralExt

variable {G G' K K' A : Type*} [Group G] [Group G'] [AddCommGroup K] [AddCommGroup K']
  [AddCommGroup A] (X : CentralExt G K A) (X' : CentralExt G' K' A)

/-- **A level structure over the graph of `u`** in `G ×_A G'`: lifts with opposite defects. -/
structure GraphLevel (u : K ≃+ K') where
  /-- The lift to `G`. -/
  σ : K → G
  /-- The lift to `G'`. -/
  σ' : K → G'
  hσ : ∀ x, X.p (σ x) = Multiplicative.ofAdd x
  hσ' : ∀ x, X'.p (σ' x) = Multiplicative.ofAdd (u x)
  /-- The defect. -/
  c : K → K → A
  hc : ∀ x y, σ x * σ y = σ (x + y) * X.ι (Multiplicative.ofAdd (c x y))
  hc' : ∀ x y, σ' x * σ' y = σ' (x + y) * X'.ι (Multiplicative.ofAdd (-c x y))

theorem p_ι (a : Multiplicative A) : X.p (X.ι a) = 1 := (X.exact _).2 ⟨a, rfl⟩

/-- The commutator of `g` with an element of `ι A`, or of two elements mapping to commuting
classes, through `commVal`. -/
theorem comm_eq_ι (g h : G) :
    g * h * g⁻¹ * h⁻¹ = X.ι (Multiplicative.ofAdd (X.pairing (Multiplicative.toAdd (X.p g))
      (Multiplicative.toAdd (X.p h)))) := by
  rw [X.pairing_eq, X.ι_commVal]; rfl

/-! ### The abelian graph group -/

section Graph

variable {X X'} (u : K ≃+ K')

/-- `Q = {(g, g') : p' g' = u (p g)}`. -/
def graphGroup : Subgroup (G × G') where
  carrier := {q | X'.p q.2 = Multiplicative.ofAdd (u (Multiplicative.toAdd (X.p q.1)))}
  one_mem' := by simp
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq, Prod.fst_mul, Prod.snd_mul, map_mul, toAdd_mul, map_add,
      ofAdd_add] at *
    rw [ha, hb]
  inv_mem' := by
    intro a ha
    simp only [Set.mem_ofPred_eq, Prod.fst_inv, Prod.snd_inv, map_inv, toAdd_inv, map_neg,
      ofAdd_neg] at *
    rw [ha]

theorem mem_graphGroup {q : G × G'} :
    q ∈ graphGroup (X := X) (X' := X') u ↔
      X'.p q.2 = Multiplicative.ofAdd (u (Multiplicative.toAdd (X.p q.1))) := Iff.rfl

/-- The antidiagonal `{(ι a, ι' a⁻¹)}` inside `Q`. -/
def antidiag : Subgroup (graphGroup (X := X) (X' := X') u) where
  carrier := {q | ∃ a : Multiplicative A, q.1.1 = X.ι a ∧ q.1.2 = X'.ι a⁻¹}
  one_mem' := ⟨1, by simp, by simp⟩
  mul_mem' := by
    rintro ⟨q, _⟩ ⟨r, _⟩ ⟨a, ha1, ha2⟩ ⟨b, hb1, hb2⟩
    refine ⟨a * b, ?_, ?_⟩
    · change q.1 * r.1 = _; rw [ha1, hb1, map_mul]
    · change q.2 * r.2 = _; rw [ha2, hb2, ← map_mul, mul_inv]
  inv_mem' := by
    rintro ⟨q, _⟩ ⟨a, ha1, ha2⟩
    refine ⟨a⁻¹, ?_, ?_⟩
    · change q.1⁻¹ = _; rw [ha1, map_inv]
    · change q.2⁻¹ = _; rw [ha2, ← map_inv]

theorem antidiag_le_center : antidiag (X := X) (X' := X') u ≤
    Subgroup.center (graphGroup (X := X) (X' := X') u) := by
  rintro q ⟨a, ha1, ha2⟩
  rw [Subgroup.mem_center_iff]
  intro r
  apply Subtype.ext
  apply Prod.ext
  · change r.1.1 * q.1.1 = q.1.1 * r.1.1; rw [ha1, X.central]
  · change r.1.2 * q.1.2 = q.1.2 * r.1.2; rw [ha2, X'.central]

instance antidiag_normal : (antidiag (X := X) (X' := X') u).Normal where
  conj_mem q hq g := by
    have hc := (Subgroup.mem_center_iff.1 (antidiag_le_center u hq)) g
    rw [hc, mul_inv_cancel_right]
    exact hq

end Graph

section Level

variable {X X'} (u : K ≃+ K')
  (hu : ∀ x y, X'.pairing (u x) (u y) = -X.pairing x y)

/-- The quotient `Q / antidiag`. -/
abbrev graphQuot := graphGroup (X := X) (X' := X') u ⧸ antidiag (X := X) (X' := X') u

include hu in
/-- Commutators in `Q` lie in the antidiagonal (isotropy of the graph). -/
theorem comm_mem_antidiag (q r : graphGroup (X := X) (X' := X') u) :
    q * r * q⁻¹ * r⁻¹ ∈ antidiag (X := X) (X' := X') u := by
  refine ⟨Multiplicative.ofAdd (X.pairing (Multiplicative.toAdd (X.p q.1.1))
    (Multiplicative.toAdd (X.p r.1.1))), ?_, ?_⟩
  · change q.1.1 * r.1.1 * q.1.1⁻¹ * r.1.1⁻¹ = _
    exact X.comm_eq_ι _ _
  · change q.1.2 * r.1.2 * q.1.2⁻¹ * r.1.2⁻¹ = _
    rw [X'.comm_eq_ι, q.2, r.2]
    simp only [toAdd_ofAdd]
    rw [hu, ofAdd_neg]

include hu in
theorem graphQuot_mul_comm (a b : graphQuot (X := X) (X' := X') u) : a * b = b * a := by
  induction a using QuotientGroup.induction_on with | H q => ?_
  induction b using QuotientGroup.induction_on with | H r => ?_
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
  have : (q * r)⁻¹ * (r * q) = r⁻¹ * q⁻¹ * (r⁻¹)⁻¹ * (q⁻¹)⁻¹ := by group
  rw [this]
  exact comm_mem_antidiag u hu r⁻¹ q⁻¹

/-- The commutative group structure on `Q / antidiag`. -/
@[reducible] def graphQuotCommGroup : CommGroup (graphQuot (X := X) (X' := X') u) :=
  { (inferInstance : Group (graphQuot (X := X) (X' := X') u)) with
    mul_comm := graphQuot_mul_comm u hu }

/-- `(ι a, 1) ∈ Q`. -/
theorem ι_one_mem (a : Multiplicative A) :
    ((X.ι a, (1 : G')) : G × G') ∈ graphGroup (X := X) (X' := X') u := by
  rw [mem_graphGroup, p_ι]; simp

/-- The embedding `A → Q / antidiag`, `a ↦ [(ι a, 1)]`. -/
def ιQ : Multiplicative A →* graphQuot (X := X) (X' := X') u where
  toFun a := QuotientGroup.mk ⟨(X.ι a, 1), ι_one_mem u a⟩
  map_one' := by
    apply congrArg QuotientGroup.mk; apply Subtype.ext; simp
  map_mul' a b := by
    rw [← QuotientGroup.mk_mul]; apply congrArg QuotientGroup.mk; apply Subtype.ext; simp

theorem ιQ_injective : Function.Injective (ιQ (X := X) (X' := X') u) := by
  rw [injective_iff_map_eq_one]
  intro a ha
  rw [ιQ, MonoidHom.coe_mk, OneHom.coe_mk, QuotientGroup.eq_one_iff] at ha
  obtain ⟨b, hb1, hb2⟩ := ha
  have hb : b = 1 := by
    have : X'.ι b⁻¹ = 1 := hb2.symm
    rw [← map_one X'.ι] at this
    exact inv_eq_one.1 (X'.inj this)
  have h1 : X.ι a = X.ι b := hb1
  rw [hb, map_one] at h1
  rw [← map_one X.ι] at h1
  exact X.inj h1

end Level

/-! ### Existence of a level structure -/

section Exists

variable {X X'}

open Classical in
/-- **Mumford's criterion, existence half, for graphs.** If `u` is anti-isometric for the
commutator pairings and `A` is divisible, the graph of `u` lifts to a level subgroup of
`G ×_A G'`. -/
theorem exists_graphLevel [DivisibleBy A ℤ] (u : K ≃+ K')
    (hu : ∀ x y, X'.pairing (u x) (u y) = -X.pairing x y) : Nonempty (GraphLevel X X' u) := by
  let _ : CommGroup (graphQuot (X := X) (X' := X') u) := graphQuotCommGroup u hu
  -- the additive retraction `r : Q/antidiag → A` with `r ∘ ιQ = id`
  let ιA : A →+ Additive (graphQuot (X := X) (X' := X') u) :=
    MonoidHom.toAdditiveRight (ιQ u)
  have hιA : Function.Injective ιA := ιQ_injective u
  obtain ⟨r, hr⟩ := (Module.Baer.of_divisible A).extension_property_addMonoidHom ιA hιA
    (AddMonoidHom.id A)
  have hr' : ∀ a : A, r (ιA a) = a := fun a => congrArg (fun f : A →+ A => f a) hr
  -- `ρ : Q → A`
  let ρ : graphGroup (X := X) (X' := X') u → A := fun q =>
    r (Additive.ofMul (QuotientGroup.mk q : graphQuot (X := X) (X' := X') u))
  have hρmul : ∀ q q', ρ (q * q') = ρ q + ρ q' := fun q q' => by
    simp only [ρ, QuotientGroup.mk_mul, ofMul_mul, map_add]
  have hρι : ∀ a : Multiplicative A,
      ρ ⟨(X.ι a, 1), ι_one_mem u a⟩ = Multiplicative.toAdd a := fun a => hr' _
  have hρZ : ∀ q ∈ antidiag (X := X) (X' := X') u, ρ q = 0 := fun q hq => by
    simp only [ρ, (QuotientGroup.eq_one_iff q).2 hq, ofMul_one, map_zero]
  -- the canonical lifts and their correction
  have hq0 : ∀ x : K, ((X.lift x, X'.lift (u x)) : G × G') ∈ graphGroup (X := X) (X' := X') u :=
    fun x => by rw [mem_graphGroup, X.p_lift, X'.p_lift]; rfl
  let q0 : K → graphGroup (X := X) (X' := X') u := fun x => ⟨_, hq0 x⟩
  let σ : K → G := fun x => X.lift x * X.ι (Multiplicative.ofAdd (-ρ (q0 x)))
  let σ' : K → G' := fun x => X'.lift (u x)
  have hσ : ∀ x, X.p (σ x) = Multiplicative.ofAdd x := fun x => by
    simp only [σ, map_mul, X.p_lift, p_ι, mul_one]
  have hσ' : ∀ x, X'.p (σ' x) = Multiplicative.ofAdd (u x) := fun x => X'.p_lift _
  have hT : ∀ x, ((σ x, σ' x) : G × G') ∈ graphGroup (X := X) (X' := X') u := fun x => by
    rw [mem_graphGroup, hσ, hσ']; rfl
  let T : K → graphGroup (X := X) (X' := X') u := fun x => ⟨_, hT x⟩
  have hTρ : ∀ x, ρ (T x) = 0 := fun x => by
    have : T x = q0 x * ⟨(X.ι (Multiplicative.ofAdd (-ρ (q0 x))), 1), ι_one_mem u _⟩ := by
      apply Subtype.ext; apply Prod.ext <;> simp [T, q0, σ, σ']
    rw [this, hρmul, hρι, toAdd_ofAdd, add_neg_cancel]
  -- the defects
  have hdef : ∀ x y, X.p (σ x * σ y * (σ (x + y))⁻¹) = 1 := fun x y => by
    simp only [map_mul, map_inv, hσ, ofAdd_add]; group
  have hdef' : ∀ x y, X'.p (σ' x * σ' y * (σ' (x + y))⁻¹) = 1 := fun x y => by
    simp only [map_mul, map_inv, hσ', map_add, ofAdd_add]; group
  let a : K → K → Multiplicative A := fun x y => ((X.exact _).1 (hdef x y)).choose
  have ha : ∀ x y, X.ι (a x y) = σ x * σ y * (σ (x + y))⁻¹ := fun x y =>
    ((X.exact _).1 (hdef x y)).choose_spec
  have hb : ∀ x y, ∃ b, X'.ι b = σ' x * σ' y * (σ' (x + y))⁻¹ := fun x y =>
    (X'.exact _).1 (hdef' x y)
  refine ⟨⟨σ, σ', hσ, hσ', fun x y => Multiplicative.toAdd (a x y), ?_, ?_⟩⟩
  · intro x y
    rw [ofAdd_toAdd, ← X.central, ha]; group
  · intro x y
    obtain ⟨b, hb⟩ := hb x y
    -- `ρ(T x T y T(x+y)⁻¹) = 0` and the element is `(ι a, ι' b)`
    have hW : T x * T y * (T (x + y))⁻¹ =
        ⟨(X.ι (a x y * b), 1), ι_one_mem u _⟩ * ⟨(X.ι b⁻¹, X'.ι b), by
          rw [mem_graphGroup, p_ι, p_ι]; simp⟩ := by
      apply Subtype.ext; apply Prod.ext
      · change σ x * σ y * (σ (x + y))⁻¹ = X.ι (a x y * b) * X.ι b⁻¹
        rw [← ha, ← map_mul, mul_inv_cancel_right]
      · change σ' x * σ' y * (σ' (x + y))⁻¹ = 1 * X'.ι b
        rw [hb, one_mul]
    have h0 : ρ (T x * T y * (T (x + y))⁻¹) = 0 := by
      have hinv : ρ (T (x + y))⁻¹ = -ρ (T (x + y)) := by
        have := hρmul (T (x + y))⁻¹ (T (x + y))
        rw [inv_mul_cancel] at this
        have h1 : ρ 1 = 0 := hρZ 1 (Subgroup.one_mem _)
        rw [h1] at this
        exact eq_neg_of_add_eq_zero_left this.symm
      rw [hρmul, hρmul, hinv, hTρ, hTρ, hTρ]; simp
    have hZmem : (⟨(X.ι b⁻¹, X'.ι b), by rw [mem_graphGroup, p_ι, p_ι]; simp⟩ :
        graphGroup (X := X) (X' := X') u) ∈ antidiag (X := X) (X' := X') u :=
      ⟨b⁻¹, rfl, by rw [inv_inv]⟩
    rw [hW, hρmul, hρι, hρZ _ hZmem, add_zero, toAdd_mul] at h0
    have hb' : b = Multiplicative.ofAdd (-Multiplicative.toAdd (a x y)) := by
      apply Multiplicative.toAdd.injective
      rw [toAdd_ofAdd]
      exact eq_neg_of_add_eq_zero_right h0
    have := congrArg (· * σ' (x + y)) hb
    simp only [inv_mul_cancel_right] at this
    rw [← this, ← hb', X'.central]

end Exists

/-! ### The graph is its own orthogonal; the descended theta group is trivial -/

section Orth

variable {X X'}

/-- **The graph of an anti-isometry is its own orthogonal**, for `A`-valued commutator pairings
with `X'` Heisenberg. -/
theorem eq_of_forall_pairing_graph (hZ' : ∀ g : G', (∀ h, g * h = h * g) → X'.p g = 1)
    {u : K ≃+ K'} (hu : ∀ x y, X'.pairing (u x) (u y) = -X.pairing x y) (a : K) (b : K')
    (h : ∀ x, X.pairing a x + X'.pairing b (u x) = 0) : b = u a := by
  rw [← sub_eq_zero]
  refine X'.pairing_nondeg hZ' _ fun z => ?_
  obtain ⟨x, rfl⟩ := u.surjective z
  rw [map_sub, AddMonoidHom.sub_apply, hu, sub_neg_eq_add, add_comm]
  exact h x

/-- **`Z(Γ̃)/Γ̃ = A`: the descended theta group is trivial.** An element `(g, g')` of
`G ×_A G'` commuting with every `[σ x, σ' x]` (i.e. `[g, σ x] + [g', σ' x] = 0` in `A`) is
`[σ x, σ' x]` times a central element. Hence `K(L_B) = 0` and the descended polarization is
principal. -/
theorem centralizer_graphLevel (hZ' : ∀ g : G', (∀ h, g * h = h * g) → X'.p g = 1)
    {u : K ≃+ K'} (hu : ∀ x y, X'.pairing (u x) (u y) = -X.pairing x y)
    (L : GraphLevel X X' u) (g : G) (g' : G')
    (hcomm : ∀ x, X.commVal g (L.σ x) + X'.commVal g' (L.σ' x) = 0) :
    ∃ x α β, g = L.σ x * X.ι α ∧ g' = L.σ' x * X'.ι β := by
  set a := Multiplicative.toAdd (X.p g)
  set b := Multiplicative.toAdd (X'.p g')
  have hab : b = u a := by
    refine eq_of_forall_pairing_graph hZ' hu a b fun x => ?_
    have h1 := X.pairing_eq g (L.σ x)
    have h2 := X'.pairing_eq g' (L.σ' x)
    rw [L.hσ, toAdd_ofAdd] at h1
    rw [L.hσ', toAdd_ofAdd] at h2
    rw [h1, h2]; exact hcomm x
  refine ⟨a, ?_⟩
  have h1 : X.p ((L.σ a)⁻¹ * g) = 1 := by
    rw [map_mul, map_inv, L.hσ]; simp [a]
  have h2 : X'.p ((L.σ' a)⁻¹ * g') = 1 := by
    rw [map_mul, map_inv, L.hσ', ← hab]; simp [b]
  obtain ⟨α, hα⟩ := (X.exact _).1 h1
  obtain ⟨β, hβ⟩ := (X'.exact _).1 h2
  exact ⟨α, β, by rw [hα, mul_inv_cancel_left], by rw [hβ, mul_inv_cancel_left]⟩

end Orth

end CentralExt

end RamanujanWeil.Arith.Deuring.Geom.G7.Fin.Weil
