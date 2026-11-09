import RamanujanWeil.Arith.DeuringG7FinCore
import RamanujanWeil.Arith.DeuringG7WeilAlg
import RamanujanWeil.Arith.DeuringG7WeilHeis

/-!
# A3-ord, G7-W (core): `PolGraphFiniteness` as finiteness of quotients by Lagrangian graphs

`docs/ARITH_DEURING_G7_WC.md`, step **W**. `PolGraphFiniteness` (G7-fin) is phrased with
coordinates: *for all coordinates there are unit determinants `c_n`* such that graph quotients
with `det u_n = c_n` are finite. The intended `c_n` is `−s_n/s'_n`, where `s_n` is the Weil
pairing of a coordinate basis. This file makes that precise and coordinate free:

* `AltPairing X ℓ`: a family of alternating, nondegenerate pairings
  `e_n : X[ℓⁿ⁺¹] × X[ℓⁿ⁺¹] → ℤ/ℓⁿ⁺¹` (the format of the Weil pairing; see
  `DeuringG7WeilHeis` for the commutator-pairing construction).
* `antiIsom ε ε' n`: the gluings `u` with `ε'(u x, u y) = −ε(x, y)`, i.e. those whose graph is
  maximal isotropic (Lagrangian) in `(E × E')[ℓⁿ⁺¹]` for `ε ⊕ ε'`
  (`DeuringG7WeilAlg.graph_isotropic_iff`, `eq_of_forall_graph_orth`).
* `LagGraphFiniteness π π' ℓ ε ε'`: `GraphFiniteness` for the class `antiIsom ε ε'`. This is
  literally *finiteness of the quotients of `E × E'` by `π`-stable Lagrangian graphs*, the
  statement Mumford's descent (step D) turns into finiteness of principally polarized surfaces.
* **`detClass_eq_antiIsom`**: in any coordinates, `detClass e e' (−s/s') = antiIsom ε ε'`.
* **`polGraphFiniteness_of_lag`**: `LagGraphFiniteness ⇒ PolGraphFiniteness`, for *any*
  alternating nondegenerate `ε, ε'`.
* **`exists_lag_of_polGraphFiniteness`**: conversely, given coordinates, `PolGraphFiniteness`
  gives `LagGraphFiniteness` for *some* such pair. So the two are equivalent; the geometric content
  is that `LagGraphFiniteness` holds for the **Weil pairings** (those of the polarization).
* **`AltPairing.map_torAct`**: on a Frobenius Jacobian, `e(πx, πy) = q · e(x, y)` holds for
  *every* alternating pairing (at the primes `ℓ` used by G7-fin), so Frobenius compatibility is
  automatic and never needs to be proved for a particular construction.
* **`AltPairing.ofCentralExt`**, `AltPairing.ofTheta`: the `AltPairing` attached to a family of
  Heisenberg central extensions of `X[ℓⁿ⁺¹]` (the theta groups of step D), with `ℤ/ℓⁿ⁺¹` values
  read through a discrete log `torsionLog` on `(k^×)[ℓⁿ⁺¹]` fixed by a *chosen* compatible system of
  primitive roots `ζ`. Using the same `ζ` for `E` and `E'` is what makes `s_n/s'_n` meaningful;
  `sCoord_ofCentralExt` gives the scalar `s_n` as the discrete log of a commutator.
* `TateFinitenessLag`, `tateFinitenessPol_of_lag`, **`mult_le_one_lag`**.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory
  CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

universe u

noncomputable section

namespace RamanujanWeil.Arith.Deuring.Geom.G7.Fin.Weil

open Stacks.Groupoids RamanujanWeil.Arith.Deuring.Geom.G7 RamanujanWeil.Arith.Deuring.Geom.G7.Fin

section Core

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- **A Weil-type pairing family** on the `ℓ`-power torsion: alternating and nondegenerate
`ℤ/ℓⁿ⁺¹`-valued pairings on `X[ℓⁿ⁺¹]`. -/
structure AltPairing (X : Over (Spec (.of k))) [GrpObj X] [AlgebraicGeometry.IsAbelianVariety k X]
    (ℓ : ℕ) where
  /-- The pairing at level `n`. -/
  e : ∀ n : ℕ, Tor X (ℓ ^ (n + 1)) →+ Tor X (ℓ ^ (n + 1)) →+ ZMod (ℓ ^ (n + 1))
  alt : ∀ n, IsAlt (e n)
  nondeg : ∀ n, IsNondeg (e n)

variable {E E' : Over (Spec (.of k))} [GrpObj E] [GrpObj E']
  [AlgebraicGeometry.IsAbelianVariety k E] [AlgebraicGeometry.IsAbelianVariety k E']

/-- The anti-isometric gluings: those with Lagrangian graph for `ε ⊕ ε'`. -/
def antiIsom {ℓ : ℕ} (ε : AltPairing E ℓ) (ε' : AltPairing E' ℓ) (n : ℕ) :
    Set (Tor E (ℓ ^ (n + 1)) ≃+ Tor E' (ℓ ^ (n + 1))) :=
  {u | ∀ x y, ε'.e n (u x) (u y) = -ε.e n x y}

variable (π : E ⟶ E) (π' : E' ⟶ E') [IsMonHom π] [IsMonHom π']

/-- **Finiteness of quotients by Lagrangian graphs.** -/
def LagGraphFiniteness (ℓ : ℕ) (ε : AltPairing E ℓ) (ε' : AltPairing E' ℓ) : Prop :=
  GraphFiniteness π π' ℓ (antiIsom ε ε')

variable {π π'}

/-- The determinant class `−s_n/s'_n` of a pair of pairings in given coordinates. -/
def lagDet {ℓ : ℕ} (ε : AltPairing E ℓ) (ε' : AltPairing E' ℓ) (e : Coords E ℓ)
    (e' : Coords E' ℓ) (n : ℕ) : ZMod (ℓ ^ (n + 1)) :=
  -sCoord (ε.e n) (e n) * (sCoord (ε'.e n) (e' n))⁻¹

omit [IsAlgClosed k] in
theorem isUnit_lagDet {ℓ : ℕ} (hℓ : ℓ.Prime) (ε : AltPairing E ℓ) (ε' : AltPairing E' ℓ)
    (e : Coords E ℓ) (e' : Coords E' ℓ) (n : ℕ) : IsUnit (lagDet ε ε' e e' n) := by
  have : NeZero (ℓ ^ (n + 1)) := ⟨pow_ne_zero _ hℓ.ne_zero⟩
  have hs := (ε.alt n).isUnit_sCoord (ε.nondeg n) (e n)
  have hs' := (ε'.alt n).isUnit_sCoord (ε'.nondeg n) (e' n)
  have hinv := ZMod.mul_inv_of_unit _ hs'
  have hi : IsUnit (sCoord (ε'.e n) (e' n))⁻¹ :=
    ⟨⟨_, _, by rw [mul_comm, hinv], hinv⟩, rfl⟩
  exact hs.neg.mul hi

omit [IsAlgClosed k] in
/-- **`detClass e e' (−s/s') = antiIsom ε ε'`.** -/
theorem detClass_eq_antiIsom {ℓ : ℕ} (hℓ : ℓ.Prime) (ε : AltPairing E ℓ) (ε' : AltPairing E' ℓ)
    (e : Coords E ℓ) (e' : Coords E' ℓ) : detClass e e' (lagDet ε ε' e e') = antiIsom ε ε' := by
  funext n
  have : NeZero (ℓ ^ (n + 1)) := ⟨pow_ne_zero _ hℓ.ne_zero⟩
  ext u
  exact (antiIsom_iff_det (ε.alt n) (ε'.alt n) (ε'.nondeg n) (e n) (e' n) u).symm

/-- **`LagGraphFiniteness ⇒ PolGraphFiniteness`**, for any alternating nondegenerate pairings. -/
theorem polGraphFiniteness_of_lag {ℓ : ℕ} (hℓ : ℓ.Prime) (ε : AltPairing E ℓ)
    (ε' : AltPairing E' ℓ) (h : LagGraphFiniteness π π' ℓ ε ε') : PolGraphFiniteness π π' ℓ :=
  fun e e' => ⟨lagDet ε ε' e e', isUnit_lagDet hℓ ε ε' e e', by
    rw [detClass_eq_antiIsom hℓ]; exact h⟩

/-- **Conversely**, with coordinates available, `PolGraphFiniteness` is `LagGraphFiniteness` for
*some* alternating nondegenerate pairings: the class `−s/s'` alone carries no information. -/
theorem exists_lag_of_polGraphFiniteness {ℓ : ℕ} (hℓ : ℓ.Prime) (e : Coords E ℓ)
    (e' : Coords E' ℓ) (h : PolGraphFiniteness π π' ℓ) :
    ∃ (ε : AltPairing E ℓ) (ε' : AltPairing E' ℓ), LagGraphFiniteness π π' ℓ ε ε' := by
  obtain ⟨c, hc, hfin⟩ := h e e'
  have hex : ∀ n, ∃ (a : Tor E (ℓ ^ (n + 1)) →+ Tor E (ℓ ^ (n + 1)) →+ ZMod (ℓ ^ (n + 1)))
      (a' : Tor E' (ℓ ^ (n + 1)) →+ Tor E' (ℓ ^ (n + 1)) →+ ZMod (ℓ ^ (n + 1))),
      IsAlt a ∧ IsNondeg a ∧ IsAlt a' ∧ IsNondeg a' ∧
        -sCoord a (e n) * (sCoord a' (e' n))⁻¹ = c n := fun n => by
    have : NeZero (ℓ ^ (n + 1)) := ⟨pow_ne_zero _ hℓ.ne_zero⟩
    exact exists_alt_of_det (e n) (e' n) (hc n)
  choose a a' ha hna ha' hna' hdet using hex
  refine ⟨⟨a, ha, hna⟩, ⟨a', ha', hna'⟩, ?_⟩
  have hc' : c = lagDet ⟨a, ha, hna⟩ ⟨a', ha', hna'⟩ e e' := funext fun n => (hdet n).symm
  unfold LagGraphFiniteness
  rw [← detClass_eq_antiIsom hℓ _ _ e e', ← hc']
  exact hfin

end Core

/-! ## From theta groups (central extensions) to `AltPairing`s -/

section Theta

variable {k : Type u} [Field k] [IsAlgClosed k]

omit [IsAlgClosed k] in
theorem tor_nsmul_eq_zero (X : Over (Spec (.of k))) [GrpObj X]
    [AlgebraicGeometry.IsAbelianVariety k X] (N : ℕ) (x : Tor X N) : N • x = 0 := by
  apply Subtype.ext
  rw [AddSubgroup.coe_nsmul, ← natCast_zsmul]
  exact x.2

/-- **The `AltPairing` of a family of Heisenberg central extensions** `0 → A → G_n → X[ℓⁿ⁺¹] → 0`
(in step D: the theta groups `𝒢(𝒪(ℓⁿ⁺¹[0]))`), read in `ℤ/ℓⁿ⁺¹` through injective
`χ_n : A[ℓⁿ⁺¹] → ℤ/ℓⁿ⁺¹`. -/
noncomputable def AltPairing.ofCentralExt {X : Over (Spec (.of k))} [GrpObj X]
    [AlgebraicGeometry.IsAbelianVariety k X] {ℓ : ℕ} {A : Type*} [AddCommGroup A]
    (G : ℕ → Type*) [∀ n, Group (G n)] (H : ∀ n, CentralExt (G n) (Tor X (ℓ ^ (n + 1))) A)
    (hZ : ∀ n (g : G n), (∀ h, g * h = h * g) → (H n).p g = 1)
    (χ : ∀ n, AddSubgroup.torsionBy A ((ℓ ^ (n + 1) : ℕ) : ℤ) →+ ZMod (ℓ ^ (n + 1)))
    (hχ : ∀ n, Function.Injective (χ n)) : AltPairing X ℓ where
  e n := (H n).zmodPairing (tor_nsmul_eq_zero X _) (χ n)
  alt n := (H n).zmodPairing_isAlt _ _
  nondeg n := (H n).zmodPairing_isNondeg _ _ (hχ n) (hZ n)

omit [IsAlgClosed k] in
/-- **The scalar `s_n`** of the commutator pairing in coordinates `c`: the discrete log of the
commutator of lifts of the two coordinate basis vectors. -/
theorem sCoord_ofCentralExt {X : Over (Spec (.of k))} [GrpObj X]
    [AlgebraicGeometry.IsAbelianVariety k X] {ℓ : ℕ} {A : Type*} [AddCommGroup A]
    (G : ℕ → Type*) [∀ n, Group (G n)] (H : ∀ n, CentralExt (G n) (Tor X (ℓ ^ (n + 1))) A)
    (hZ : ∀ n (g : G n), (∀ h, g * h = h * g) → (H n).p g = 1)
    (χ : ∀ n, AddSubgroup.torsionBy A ((ℓ ^ (n + 1) : ℕ) : ℤ) →+ ZMod (ℓ ^ (n + 1)))
    (hχ : ∀ n, Function.Injective (χ n)) (n : ℕ)
    (c : Tor X (ℓ ^ (n + 1)) ≃+ (Fin 2 → ZMod (ℓ ^ (n + 1)))) :
    sCoord ((AltPairing.ofCentralExt G H hZ χ hχ).e n) c =
      χ n ⟨(H n).pairing (bas c 0) (bas c 1), (H n).pairing_mem_torsion
        (tor_nsmul_eq_zero X _) _ _⟩ := rfl

/-- **The discrete log on `(k^×)[N]`** determined by a primitive `N`-th root of unity. A fixed
choice; feeding the same `ζ` to `E` and to `E'` fixes the normalization of `s_n/s'_n`. -/
noncomputable def torsionLog {L : Type*} [CommRing L] [IsDomain L] {N : ℕ} [NeZero N] {ζ : L}
    (hζ : IsPrimitiveRoot ζ N) : AddSubgroup.torsionBy (Additive Lˣ) (N : ℤ) →+ ZMod N :=
  (exists_injective_torsion_units_zmod hζ).choose

theorem torsionLog_injective {L : Type*} [CommRing L] [IsDomain L] {N : ℕ} [NeZero N] {ζ : L}
    (hζ : IsPrimitiveRoot ζ N) : Function.Injective (torsionLog hζ) :=
  (exists_injective_torsion_units_zmod hζ).choose_spec

/-- **The theta-group `AltPairing`** with values `ζ_n`-logarithms, `A = k^×`: the format in which
step D delivers the Weil pairing of the principal polarization. -/
noncomputable def AltPairing.ofTheta {X : Over (Spec (.of k))} [GrpObj X]
    [AlgebraicGeometry.IsAbelianVariety k X] {ℓ : ℕ} [NeZero ℓ] (ζ : ℕ → k)
    (hζ : ∀ n, IsPrimitiveRoot (ζ n) (ℓ ^ (n + 1)))
    (G : ℕ → Type*) [∀ n, Group (G n)]
    (H : ∀ n, CentralExt (G n) (Tor X (ℓ ^ (n + 1))) (Additive kˣ))
    (hZ : ∀ n (g : G n), (∀ h, g * h = h * g) → (H n).p g = 1) : AltPairing X ℓ :=
  AltPairing.ofCentralExt G H hZ (fun n => torsionLog (hζ n)) (fun n => torsionLog_injective _)

end Theta

/-! ## Frobenius Jacobians: Frobenius compatibility is automatic -/

section Frob

variable {K : Type u} [Field K] [Fintype K]

open RamanujanWeil.Ihara in
/-- `π² − tπ + q = 0` on the torsion of a Frobenius Jacobian. -/
theorem torAct_rel {V : WeierstrassCurve K} [V.IsElliptic] (I : FrobeniusJacobian V) (N : ℕ)
    (x : Tor I.A N) :
    torAct I.π N (torAct I.π N x) - traceOfFrob V • torAct I.π N x +
      (Nat.card K : ℤ) • x = 0 := by
  apply pt_injective
  have h := congrArg (pt x ≫ ·) I.frob_quadratic
  simp only [MonObj.comp_one] at h
  rw [comp_endPolyEval_quadratic] at h
  change pt x ≫ I.π ≫ I.π / (pt x ≫ I.π) ^ (traceOfFrob V) * pt x ^ (Nat.card K : ℤ) = 1 at h
  change Additive.toMul (_ - _ + _) = (1 : Pt I.A)
  rw [toMul_add, toMul_sub, AddSubgroupClass.coe_zsmul, AddSubgroupClass.coe_zsmul, toMul_zsmul,
    toMul_zsmul]
  exact h

open RamanujanWeil.Ihara in
/-- **Frobenius compatibility of every alternating pairing**: on a Frobenius Jacobian, at a prime
`ℓ` for which `X² − tX + q` has no root mod `ℓ`, `e(πx, πy) = q · e(x, y)`. -/
theorem AltPairing.map_torAct {V : WeierstrassCurve K} [V.IsElliptic] (I : FrobeniusJacobian V)
    {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓk : IsUnit (ℓ : AlgebraicClosure K)) (ε : AltPairing I.A ℓ)
    (hroot : ∀ a : ZMod ℓ, a ^ 2 - ((traceOfFrob V : ℤ) : ZMod ℓ) * a +
      ((Nat.card K : ℤ) : ZMod ℓ) ≠ 0) (n : ℕ) (x y : Tor I.A (ℓ ^ (n + 1))) :
    ε.e n (torAct I.π _ x) (torAct I.π _ y) = (Nat.card K : ZMod (ℓ ^ (n + 1))) * ε.e n x y := by
  obtain ⟨c⟩ := nonempty_torsionBy_pow_addEquiv I.A ℓ hℓk (n + 1)
  rw [I.dim_eq] at c
  have := (ε.alt n).map_map_eq_q hℓ c (torAct I.π _) (traceOfFrob V) (Nat.card K)
    (torAct_rel I _) hroot x y
  rw [this]
  push_cast
  rfl

end Frob

/-! ## The concrete isogeny count from Lagrangian graph finiteness -/

section Mult

open RamanujanWeil.Ihara RamanujanWeil.Arith.Deuring.Mult

variable (K : Type u) [Field K] [Fintype K]

/-- **The Lagrangian form of the G7-fin hypothesis at `K = 𝔽_q`**: for the concrete Jacobians of
two elliptic curves with the same ordinary trace and every odd prime `ℓ` invertible in `𝔽̄_q`,
there are alternating nondegenerate pairings (in truth: the Weil pairings) for which the
quotients by Lagrangian graphs are finite. Equivalent to `TateFinitenessPol K`. -/
def TateFinitenessLag : Prop :=
  ∀ (W W' : WeierstrassCurve K) [W.IsElliptic] [W'.IsElliptic] (S : Jac.JacSite W)
    (S' : Jac.JacSite W'), traceOfFrob W' = traceOfFrob W →
    ¬ (ringChar K : ℤ) ∣ traceOfFrob W → traceOfFrob W ^ 2 < 4 * (Nat.card K : ℤ) →
    ∀ ℓ : ℕ, ℓ.Prime → ℓ ≠ 2 → IsUnit (ℓ : AlgebraicClosure K) →
      ∃ (ε : AltPairing S.J ℓ) (ε' : AltPairing S'.J ℓ), LagGraphFiniteness S.π S'.π ℓ ε ε'

variable {K}

theorem tateFinitenessPol_of_lag (h : TateFinitenessLag K) : Fin.TateFinitenessPol K :=
  fun W W' _ _ S S' ht hp hlt ℓ hℓ hodd hℓk => by
    obtain ⟨ε, ε', hlag⟩ := h W W' S S' ht hp hlt ℓ hℓ hodd hℓk
    exact polGraphFiniteness_of_lag hℓ ε ε' hlag

theorem tateFinitenessLag_of_pol (h : Fin.TateFinitenessPol K) : TateFinitenessLag K :=
  fun W W' _ _ S S' ht hp hlt ℓ hℓ hodd hℓk => by
    have hco : ∀ {V : WeierstrassCurve K} [V.IsElliptic] (I : FrobeniusJacobian V) (n : ℕ),
        Nonempty (Tor I.A (ℓ ^ (n + 1)) ≃+ (Fin 2 → ZMod (ℓ ^ (n + 1)))) := fun I n => by
      obtain ⟨c⟩ := nonempty_torsionBy_pow_addEquiv I.A ℓ hℓk (n + 1)
      rw [I.dim_eq] at c
      exact ⟨c⟩
    exact exists_lag_of_polGraphFiniteness hℓ (fun n => (hco S.frobeniusJacobian n).some)
      (fun n => (hco S'.frobeniusJacobian n).some) (h W W' S S' ht hp hlt ℓ hℓ hodd hℓk)

/-- **`TateFinitenessLag` at every finite field.** -/
def TateFinitenessLagAll : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (n : ℕ), 1 ≤ n →
    letI : Fintype (GaloisField p n) := Fintype.ofFinite _
    TateFinitenessLag (GaloisField p n)

theorem tateFinitenessPolAll_of_lagAll (h : TateFinitenessLagAll) : Fin.TateFinitenessPolAll :=
  fun p _ n hn =>
    letI : Fintype (GaloisField p n) := Fintype.ofFinite _
    tateFinitenessPol_of_lag (h p n hn)

/-- **`mult ≤ 1`** on the ordinary range, from finiteness of quotients by Lagrangian graphs. -/
theorem mult_le_one_lag (h : TateFinitenessLagAll) (p : ℕ) [Fact p.Prime] (n : ℕ) (hn : 1 ≤ n)
    (t : ℤ) (hp : ¬ (p : ℤ) ∣ t) (hlt : t ^ 2 < 4 * (p : ℤ) ^ n) : mult p n t ≤ 1 :=
  Fin.mult_le_one_pol (tateFinitenessPolAll_of_lagAll h) p n hn t hp hlt

end Mult

end RamanujanWeil.Arith.Deuring.Geom.G7.Fin.Weil

end
