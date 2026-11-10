import RamanujanWeil.Arith.DeuringPLinkPhi
import RamanujanWeil.Arith.DeuringClassLattice

/-!
# `PrimeToPLink` is a theorem

`docs/ARITH_DEURING_PLINK.md` §5. Setting: `k` algebraically closed of characteristic `p`,
`(X, π_X)` with `Good π_X t p^s` (`p ∤ t`), and a nonzero equivariant `φ : X ⟶ Y`.

**`link_of_ne_one`**: `Link π_X π_Y`. Let `Γ = ker φ(k)`, `#Γ = p^a m'`, `p ∤ m'`.

1. `Γ_{m'} = Γ[m']`, `q₁ : X → X₁ = X/Γ_{m'}`: a link of degree `m'` (`link_glue_unit`).
2. `φ = q₁ ≫ φ₁`, and `Γ₁ = ker φ₁(k)` is a `p`-group, `#Γ₁ = p^b`. `q₂ : X₁ → Z = X₁/Γ₁`.
   Since `#X₁(k)[p^b] ≤ p^b` (`card_torsion_le`), `Γ₁ = X₁(k)[p^b]`, so the cofactor
   `s : Z → X₁` (`q₂ ≫ s = [p^b]`) is injective on points: a link by the radicial case.
3. `φ₁ = q₂ ≫ ι` with `ι` injective on points: a link by the radicial case.

`Good` passes to `X₁` and `Z` (`good_of_hom`). Links compose (`link_trans`) and reverse
(`link_symm`).

**`primeToPLink K`**: `ClassLattice.PrimeToPLink K` for every finite field `K`, and
`primeToPLinkAll : PrimeToPLinkAll`.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory Polynomial
open scoped CategoryTheory.MonObj

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

universe u

namespace RamanujanWeil.Arith.Deuring.PLink

open Stacks.Groupoids RamanujanWeil.Arith.Deuring.Geom RamanujanWeil.Arith.Deuring.Geom.G7
  RamanujanWeil.Arith.Deuring.Dual2 RamanujanWeil.Arith.Deuring.Radicial
  RamanujanWeil.Arith.Deuring.G8 RamanujanWeil.Arith.Deuring.G8Int RamanujanWeil.Arith.Deuring.G5

section Links

variable {k : Type u} [Field k] [IsAlgClosed k] {X Y Z : Over (Spec (.of k))} [GrpObj X]
  [GrpObj Y] [GrpObj Z] [AlgebraicGeometry.IsAbelianVariety k X]
  [AlgebraicGeometry.IsAbelianVariety k Y] [AlgebraicGeometry.IsAbelianVariety k Z]

/-- Links compose. -/
theorem link_trans {πX : X ⟶ X} {πY : Y ⟶ Y} {πZ : Z ⟶ Z} [IsMonHom πX] [IsMonHom πY]
    [IsMonHom πZ] (h1 : Link πX πY) (h2 : Link πY πZ) : Link πX πZ := by
  obtain ⟨α₁, β₁, n₁, hn₁, hα₁, hβ₁, hα₁π, hβ₁π, hαβ₁⟩ := h1
  obtain ⟨α₂, β₂, n₂, hn₂, hα₂, hβ₂, hα₂π, hβ₂π, hαβ₂⟩ := h2
  haveI := hα₁
  haveI := hβ₁
  haveI := hα₂
  haveI := hβ₂
  refine ⟨α₁ ≫ α₂, β₂ ≫ β₁, n₁ * n₂, by push_cast; exact hn₁.mul hn₂, inferInstance,
    inferInstance, ?_, ?_, ?_⟩
  · rw [Category.assoc, hα₂π, ← Category.assoc, hα₁π, Category.assoc]
  · rw [Category.assoc, hβ₁π, ← Category.assoc, hβ₂π, Category.assoc]
  · calc (α₁ ≫ α₂) ≫ β₂ ≫ β₁ = α₁ ≫ (α₂ ≫ β₂) ≫ β₁ := by simp only [Category.assoc]
      _ = α₁ ≫ ((𝟙 Y) ^ n₂) ≫ β₁ := by rw [hαβ₂]
      _ = ((𝟙 X) ^ n₂) ≫ α₁ ≫ β₁ := by
        rw [← Category.assoc, ← zpow_id_comp_comm, Category.assoc]
      _ = (𝟙 X) ^ (n₁ * n₂) := by
        rw [hαβ₁, GrpObj.comp_zpow, Category.comp_id, ← zpow_mul, mul_comm]

/-- Links reverse. -/
theorem link_symm (hX : abelianVarietyDimension X = 1) (hY : abelianVarietyDimension Y = 1)
    {πX : X ⟶ X} {πY : Y ⟶ Y} [IsMonHom πX] [IsMonHom πY] (h : Link πX πY) : Link πY πX := by
  obtain ⟨α, β, n, hn, hα, hβ, hαπ, hβπ, hαβ⟩ := h
  haveI := hα
  have hn0 : n ≠ 0 := by rintro rfl; simp at hn
  have hα1 : α ≠ 1 := by
    rintro rfl
    exact zpow_id_ne_one hX n hn0 (by rw [← hαβ, MonObj.one_comp])
  exact ⟨β, α, n, hn, hβ, hα, hβπ, hαπ, comp_eq_zpow_symm hX hY α hα1 β n hαβ⟩

/-- A quotient by a `π`-stable subgroup killed by `m`, `m` invertible, is a link. -/
theorem link_glue_unit {Γ : Subgroup (Pt X)} (G : Glue Γ) (m : ℤ) (hm : IsUnit (m : k))
    (hΓ : ∀ h ∈ Γ, h ^ m = 1) (π : X ⟶ X) [IsMonHom π] (hπ : ∀ x ∈ Γ, x ≫ π ∈ Γ) :
    Link π (GlueS.πB G π hπ) :=
  ⟨G.q, GlueS.sMap G m hΓ, m, hm, G.hom, inferInstance, GlueS.q_πB G π hπ,
    GlueS.sMap_π G m hΓ π hπ, GlueS.q_sMap G m hΓ⟩

/-- **The radicial case from `Good`.** -/
theorem link_of_injective_good (p : ℕ) [hp : Fact p.Prime] [CharP k p] (t : ℤ) (s : ℕ)
    (hs : s ≠ 0) (hpt : ¬ (p : ℤ) ∣ t) (πX : X ⟶ X) (πY : Y ⟶ Y) [IsMonHom πX] [IsMonHom πY]
    (hG : Good πX t (p ^ s)) (hY : abelianVarietyDimension Y = 1)
    (i₁ : X ⟶ Y) [IsMonHom i₁] (hi₁π : i₁ ≫ πY = πX ≫ i₁)
    (hi₁inj : ∀ x : 𝟙_ (Over (Spec (.of k))) ⟶ X, x ≫ i₁ = 1 → x = 1) : Link πX πY := by
  obtain ⟨Φ, hΦm, hΦ, hdeg, hinj, hcomm⟩ := exists_phi p πX t s hpt hG
  exact link_of_injective p hG.dim hY t s hs hpt πX πY Φ hΦ hdeg hinj hcomm i₁ hi₁π hi₁inj

set_option maxHeartbeats 1600000 in
/-- **A nonzero equivariant homomorphism gives a link of degree prime to `p`.** -/
theorem link_of_ne_one (p : ℕ) [hp : Fact p.Prime] [CharP k p] (t : ℤ) (s : ℕ)
    (hs : s ≠ 0) (hpt : ¬ (p : ℤ) ∣ t) (πX : X ⟶ X) (πY : Y ⟶ Y) [IsMonHom πX] [IsMonHom πY]
    (hG : Good πX t (p ^ s)) (hY : abelianVarietyDimension Y = 1)
    (φ : X ⟶ Y) [IsMonHom φ] (hφπ : φ ≫ πY = πX ≫ φ) (hφ : φ ≠ 1) : Link πX πY := by
  classical
  have hX := hG.dim
  have hcomm : ∀ a b : Pt X, a * b = b * a := fun a b => mul_comm a b
  -- the kernel of `φ`
  let Γ : Subgroup (Pt X) := (IsMonHom.monoidHom φ (𝟙_ (Over (Spec (.of k))))).ker
  have hmemΓ : ∀ x : Pt X, x ∈ Γ ↔ x ≫ φ = 1 := fun x => Iff.rfl
  have hfin : (pointKer φ).Finite := by
    by_contra h; exact hφ (eq_one_of_infinite_pointKer hX φ h)
  haveI : Finite Γ := hfin.to_subtype
  set N := Nat.card Γ with hNdef
  have hN0 : N ≠ 0 := Nat.card_pos.ne'
  have hΓN : ∀ h ∈ Γ, h ^ (N : ℤ) = 1 := fun h hh => by
    have h1 : (⟨h, hh⟩ : Γ) ^ Nat.card Γ = 1 := pow_card_eq_one'
    have h2 := congrArg Subtype.val h1
    rw [Subgroup.coe_pow, Subgroup.coe_one] at h2
    rw [zpow_natCast, h2]
  obtain ⟨a, m', hm'p, hNeq⟩ := Nat.exists_eq_pow_mul_and_not_dvd hN0 p hp.out.ne_one
  have hm'0 : (m' : ℤ) ≠ 0 := by
    intro h0
    have : m' = 0 := by exact_mod_cast h0
    rw [this] at hm'p
    exact hm'p (dvd_zero p)
  have hm'unit : IsUnit ((m' : ℤ) : k) := by
    rw [isUnit_iff_ne_zero, Ne, Int.cast_natCast, CharP.cast_eq_zero_iff k p]
    exact hm'p
  -- step 1: the prime-to-`p` part
  let Γm : Subgroup (Pt X) :=
    { carrier := {z | z ≫ φ = 1 ∧ z ^ (m' : ℤ) = 1}
      mul_mem' := by
        rintro x y ⟨hx1, hx2⟩ ⟨hy1, hy2⟩
        refine ⟨?_, ?_⟩
        · rw [MonObj.mul_comp, hx1, hy1, one_mul]
        · rw [(Commute.mul_zpow (hcomm x y) (m' : ℤ)), hx2, hy2, one_mul]
      one_mem' := ⟨MonObj.one_comp φ, one_zpow _⟩
      inv_mem' := by
        rintro x ⟨hx1, hx2⟩
        refine ⟨?_, ?_⟩
        · rw [← zpow_neg_one, GrpObj.zpow_comp, hx1, one_zpow]
        · rw [inv_zpow, hx2, inv_one] }
  have hΓmΓ : ∀ x ∈ Γm, x ∈ Γ := fun x hx => hx.1
  haveI : Finite Γm := (hfin.subset (fun x hx => hΓmΓ x hx)).to_subtype
  have hΓm : ∀ h ∈ Γm, h ^ (m' : ℤ) = 1 := fun h hh => hh.2
  have hπm : ∀ x ∈ Γm, x ≫ πX ∈ Γm := by
    rintro x ⟨hx1, hx2⟩
    refine ⟨?_, ?_⟩
    · rw [Category.assoc, ← hφπ, ← Category.assoc, hx1, MonObj.one_comp]
    · rw [← GrpObj.zpow_comp, hx2, MonObj.one_comp]
  obtain ⟨G1⟩ := nonempty_glue Γm
  set π₁ := GlueS.πB G1 πX hπm
  haveI : IsMonHom π₁ := GlueS.isMonHom_πB G1 πX hπm
  have hqπ₁ : G1.q ≫ π₁ = πX ≫ G1.q := GlueS.q_πB G1 πX hπm
  have hX₁ : abelianVarietyDimension G1.B = 1 := GlueS.dim_B G1 (m' : ℤ) hΓm hX hm'0
  have L1 : Link πX π₁ := link_glue_unit G1 (m' : ℤ) hm'unit hΓm πX hπm
  have hG₁ : Good π₁ t (p ^ s) :=
    good_of_hom hG hX₁ G1.q (GlueS.q_ne_one G1 (m' : ℤ) hΓm hX hm'0) hqπ₁
  have hkm : ∀ h ∈ Γm, h ≫ φ = 1 := fun h hh => hh.1
  set φ₁ := G1.desc φ hkm
  haveI : IsMonHom φ₁ := G1.desc_isMonHom φ hkm
  have hqφ₁ : G1.q ≫ φ₁ = φ := G1.q_desc φ hkm
  have hφ₁π : φ₁ ≫ πY = π₁ ≫ φ₁ := by
    apply G1.cancel
    rw [← Category.assoc, hqφ₁, hφπ, ← Category.assoc, hqπ₁, Category.assoc, hqφ₁]
  have hφ₁1 : φ₁ ≠ 1 := by
    intro h1
    apply hφ
    rw [← hqφ₁, h1, MonObj.comp_one]
  -- step 2: the kernel of `φ₁` is a `p`-group
  let Γ₁ : Subgroup (Pt G1.B) := (IsMonHom.monoidHom φ₁ (𝟙_ (Over (Spec (.of k))))).ker
  have hmemΓ₁ : ∀ x : Pt G1.B, x ∈ Γ₁ ↔ x ≫ φ₁ = 1 := fun x => Iff.rfl
  have hfin₁ : (pointKer φ₁).Finite := by
    by_contra h; exact hφ₁1 (eq_one_of_infinite_pointKer hX₁ φ₁ h)
  haveI : Finite Γ₁ := hfin₁.to_subtype
  have hpa : ∀ w ∈ Γ₁, w ^ ((p ^ a : ℕ) : ℤ) = 1 := by
    intro w hw
    obtain ⟨z, rfl⟩ := G1.exists_comp_q_eq (m' : ℤ) hm'0 hΓm w
    have hz : z ∈ Γ := by
      rw [hmemΓ, ← hqφ₁, ← Category.assoc]
      exact (hmemΓ₁ _).mp hw
    have hzN := hΓN z hz
    have hzm : z ^ ((p ^ a : ℕ) : ℤ) ∈ Γm := by
      refine ⟨?_, ?_⟩
      · rw [GrpObj.zpow_comp, (hmemΓ z).mp hz, one_zpow]
      · rw [← zpow_mul]
        rw [hNeq] at hzN
        push_cast at hzN ⊢
        exact hzN
    rw [← GrpObj.zpow_comp, (G1.ker _).2 hzm]
  have hpg : IsPGroup p Γ₁ := fun g => ⟨a, Subtype.ext (by
    rw [Subgroup.coe_pow, Subgroup.coe_one, ← zpow_natCast]
    exact_mod_cast hpa g.1 g.2)⟩
  obtain ⟨b, hb⟩ := (IsPGroup.iff_card).mp hpg
  have hΓ₁b : ∀ h ∈ Γ₁, h ^ ((p ^ b : ℕ) : ℤ) = 1 := fun h hh => by
    have h1 : (⟨h, hh⟩ : Γ₁) ^ Nat.card Γ₁ = 1 := pow_card_eq_one'
    have h2 := congrArg Subtype.val h1
    rw [Subgroup.coe_pow, Subgroup.coe_one, hb] at h2
    rw [zpow_natCast, h2]
  have hpb0 : ((p ^ b : ℕ) : ℤ) ≠ 0 := by exact_mod_cast (pow_pos hp.out.pos b).ne'
  have hπ₁ : ∀ x ∈ Γ₁, x ≫ π₁ ∈ Γ₁ := by
    intro x hx
    rw [hmemΓ₁, Category.assoc, ← hφ₁π, ← Category.assoc, (hmemΓ₁ x).mp hx, MonObj.one_comp]
  obtain ⟨G2⟩ := nonempty_glue Γ₁
  set πZ := GlueS.πB G2 π₁ hπ₁
  haveI : IsMonHom πZ := GlueS.isMonHom_πB G2 π₁ hπ₁
  have hqπZ : G2.q ≫ πZ = π₁ ≫ G2.q := GlueS.q_πB G2 π₁ hπ₁
  have hZ : abelianVarietyDimension G2.B = 1 := GlueS.dim_B G2 _ hΓ₁b hX₁ hpb0
  have hGZ : Good πZ t (p ^ s) :=
    good_of_hom hG₁ hZ G2.q (GlueS.q_ne_one G2 _ hΓ₁b hX₁ hpb0) hqπZ
  -- `Γ₁ = X₁(k)[p^b]`
  have hall : ∀ w : Pt G1.B, w ^ ((p ^ b : ℕ) : ℤ) = 1 → w ∈ Γ₁ := by
    obtain ⟨hTfin, hTcard⟩ := card_torsion_le p hX₁ b
    set T : Set (Pt G1.B) := {z | z ^ ((p ^ b : ℕ) : ℤ) = 1}
    have hsub : (Γ₁ : Set (Pt G1.B)) ⊆ T := fun h hh => hΓ₁b h hh
    have hTf : T.Finite := Set.finite_coe_iff.mp hTfin
    have hle : T.ncard ≤ (Γ₁ : Set (Pt G1.B)).ncard := by
      rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq, SetLike.coe_sort_coe, hb]
      exact hTcard
    have heq := Set.eq_of_subset_of_ncard_le hsub hle hTf
    intro w hw
    have : w ∈ T := hw
    rw [← heq] at this
    exact this
  -- step 2': the cofactor of `q₂` is radicial
  set s₂ := GlueS.sMap G2 _ hΓ₁b
  haveI : IsMonHom s₂ := GlueS.isMonHom_sMap G2 _ hΓ₁b
  have hqs₂ : G2.q ≫ s₂ = (𝟙 G1.B) ^ ((p ^ b : ℕ) : ℤ) := GlueS.q_sMap G2 _ hΓ₁b
  have hs₂π : s₂ ≫ π₁ = πZ ≫ s₂ := GlueS.sMap_π G2 _ hΓ₁b π₁ hπ₁
  have hs₂inj : ∀ x : Pt G2.B, x ≫ s₂ = 1 → x = 1 := by
    intro x hx
    obtain ⟨w, rfl⟩ := G2.exists_comp_q_eq _ hpb0 hΓ₁b x
    rw [Category.assoc, hqs₂, comp_zpow_id] at hx
    exact (G2.ker w).2 (hall w hx)
  have L2 : Link π₁ πZ := link_symm hZ hX₁
    (link_of_injective_good p t s hs hpt πZ π₁ hGZ hX₁ s₂ hs₂π hs₂inj)
  -- step 3: the purely inseparable part
  have hk₁ : ∀ h ∈ Γ₁, h ≫ φ₁ = 1 := fun h hh => (hmemΓ₁ h).mp hh
  set i₁ := G2.desc φ₁ hk₁
  haveI : IsMonHom i₁ := G2.desc_isMonHom φ₁ hk₁
  have hqi₁ : G2.q ≫ i₁ = φ₁ := G2.q_desc φ₁ hk₁
  have hi₁π : i₁ ≫ πY = πZ ≫ i₁ := by
    apply G2.cancel
    rw [← Category.assoc, hqi₁, hφ₁π, ← Category.assoc, hqπZ, Category.assoc, hqi₁]
  have hi₁inj : ∀ x : Pt G2.B, x ≫ i₁ = 1 → x = 1 := by
    intro x hx
    obtain ⟨w, rfl⟩ := G2.exists_comp_q_eq _ hpb0 hΓ₁b x
    rw [Category.assoc, hqi₁] at hx
    exact (G2.ker w).2 ((hmemΓ₁ w).mpr hx)
  have L3 : Link πZ πY := link_of_injective_good p t s hs hpt πZ πY hGZ hY i₁ hi₁π hi₁inj
  exact link_trans (link_trans L1 L2) L3

end Links

/-! ### Finite fields -/

section Finite

open RamanujanWeil.Ihara RamanujanWeil.Arith.Deuring.Mult RamanujanWeil.Arith.Deuring.ClassLattice

variable {K : Type u} [Field K] [Fintype K]

/-- The concrete Frobenius Jacobian is `Good`. -/
theorem good_frobeniusJacobian {W : WeierstrassCurve K} [W.IsElliptic] (J : FrobeniusJacobian W) :
    Good J.π (traceOfFrob W) (Nat.card K) := by
  obtain ⟨hpoly, hdeg, htr⟩ := charPoly_data J.dim_eq J.π (traceOfFrob W) (Nat.card K)
    J.charPoly_eq
  refine ⟨J.dim_eq, hpoly, by rw [homDegree_eq_endDegree, hdeg], ?_⟩
  have h := endDegree_zpow_mul_zpow J.dim_eq J.π (-1) (traceOfFrob W)
  rw [hdeg, htr] at h
  unfold vOf
  rw [homDegree_eq_endDegree]
  have h' : (endDegree J.A (J.π ^ (-1 : ℤ) * (𝟙 J.A) ^ traceOfFrob W) : ℚ) = (Nat.card K : ℚ) := by
    rw [h]; push_cast; ring
  exact_mod_cast h'

/-- **`PrimeToPLink K` holds for every finite field `K`.** -/
theorem primeToPLink (K : Type u) [Field K] [Fintype K] : PrimeToPLink K := by
  intro W W' _ _ S S' _ hpt _ hne
  obtain ⟨α, hα, hαπ, hα1⟩ := hne
  haveI := hα
  haveI := fact_ringChar_prime (k := K)
  set p := ringChar K
  haveI : CharP K p := ringChar.charP K
  haveI : CharP (AlgebraicClosure K) p :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective p
  obtain ⟨s, -, hcard⟩ := FiniteField.card K p
  have hq : Nat.card K = p ^ (s : ℕ) := by rw [Nat.card_eq_fintype_card, hcard]
  have hG := good_frobeniusJacobian S.frobeniusJacobian
  rw [hq] at hG
  exact link_of_ne_one p (traceOfFrob W) s s.ne_zero hpt _ _ hG
    S'.frobeniusJacobian.dim_eq α hαπ hα1

/-- **`PrimeToPLinkAll` holds.** -/
theorem primeToPLinkAll : PrimeToPLinkAll := fun p _ n _ =>
  letI : Fintype (GaloisField p n) := Fintype.ofFinite _
  primeToPLink _

end Finite

end RamanujanWeil.Arith.Deuring.PLink
