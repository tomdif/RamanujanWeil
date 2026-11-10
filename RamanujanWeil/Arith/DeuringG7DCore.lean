import RamanujanWeil.Arith.DeuringG7DAlg
import RamanujanWeil.Arith.DeuringG7WeilCore

/-!
# A3-ord, G7-D (core): theta families, `AltPairing.ofTheta`, and the step-D seam

`docs/ARITH_DEURING_G7D.md` §2. A **theta family** on an abelian variety `X / k̄` at `ℓ` is a
family of Heisenberg central extensions `0 → k̄^× → G_n → X[ℓⁿ⁺¹] → 0`. In step D it is the
family of theta groups `𝒢(𝒪(ℓⁿ⁺¹[0]))`.

* `divisibleBy_units`: `k̄^×` is divisible, so `exists_graphLevel` applies with `A = k̄^×`.
* `exists_primitiveRoots`: `ζ_n` primitive of order `ℓⁿ⁺¹` in `k̄` for `ℓ` invertible. This is
  **one** choice for both curves, which normalizes `s_n / s'_n`.
* `ThetaFamily.pairing ζ = AltPairing.ofTheta ζ …`, and `ThetaFamily.sCoord_pairing` for the
  scalars `s_n` (resp. `s'_n` for `E'`): the discrete log of the commutator of lifts of a basis.
* **`antiIsom_iff_pairing`**: `u ∈ antiIsom ε ε'` (i.e. `det u = −s_n/s'_n`,
  `mem_antiIsom_iff_det`) iff `u` is an anti-isometry of the `k̄^×`-valued commutator pairings.
* **`graphLevel_of_antiIsom`**: then the graph of `u_n` lifts to a level subgroup of
  `𝒢 ×_{k̄^×} 𝒢'` (Mumford's criterion, `DeuringG7DAlg`). By `centralizer_graphLevel`, the
  descended theta group is trivial.
* **`ThetaDescentFiniteness K`** (named, the remaining geometry of D + Θ + J + C) and
  **`tateFinitenessLag_of_thetaDescent`**, `tateFinitenessLagAll_of_thetaDescent`.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory
  CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

universe u

noncomputable section

namespace RamanujanWeil.Arith.Deuring.Geom.G7.Fin.Weil

open Stacks.Groupoids RamanujanWeil.Arith.Deuring.Geom.G7 RamanujanWeil.Arith.Deuring.Geom.G7.Fin

/-! ### The field `k̄`: divisibility and roots of unity -/

section Field

variable (k : Type*) [Field k] [IsAlgClosed k]

/-- `k̄^×` is divisible. -/
@[reducible] def divisibleBy_units : DivisibleBy (Additive kˣ) ℤ :=
  divisibleByOfSMulRightSurj _ _ fun {n} hn x => by
    obtain ⟨m, rfl | rfl⟩ := Int.eq_nat_or_neg n
    · have hm : 0 < m := by omega
      obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq ((Additive.toMul x : kˣ) : k) hm
      have hz0 : z ≠ 0 := by
        rintro rfl; rw [zero_pow hm.ne'] at hz; exact (Additive.toMul x).ne_zero hz.symm
      refine ⟨Additive.ofMul (Units.mk0 z hz0), ?_⟩
      change ((m : ℤ)) • Additive.ofMul (Units.mk0 z hz0) = x
      rw [natCast_zsmul, ← ofMul_pow]
      apply Additive.toMul.injective
      apply Units.ext
      simp [hz]
    · have hm : 0 < m := by omega
      obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq ((Additive.toMul (-x) : kˣ) : k) hm
      have hz0 : z ≠ 0 := by
        rintro rfl; rw [zero_pow hm.ne'] at hz; exact (Additive.toMul (-x)).ne_zero hz.symm
      refine ⟨Additive.ofMul (Units.mk0 z hz0), ?_⟩
      change (-(m : ℤ)) • Additive.ofMul (Units.mk0 z hz0) = x
      rw [neg_zsmul, natCast_zsmul, ← ofMul_pow, neg_eq_iff_eq_neg]
      apply Additive.toMul.injective
      apply Units.ext
      simp [hz]

/-- Primitive `ℓⁿ⁺¹`-th roots of unity exist in `k̄` when `ℓ` is invertible. -/
theorem exists_primitiveRoots {ℓ : ℕ} (hℓ : IsUnit (ℓ : k)) :
    ∃ ζ : ℕ → k, ∀ n, IsPrimitiveRoot (ζ n) (ℓ ^ (n + 1)) := by
  have key : ∀ n : ℕ, ∃ z : k, IsPrimitiveRoot z (ℓ ^ (n + 1)) := by
    intro n
    have hN : NeZero (((ℓ ^ (n + 1) : ℕ)) : k) := ⟨by
      rw [Nat.cast_pow]; exact pow_ne_zero _ hℓ.ne_zero⟩
    have hN' : NeZero (ℓ ^ (n + 1)) := ⟨by
      intro h; apply hN.out; rw [h, Nat.cast_zero]⟩
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_root (Polynomial.cyclotomic (ℓ ^ (n + 1)) k)
      (Polynomial.degree_cyclotomic_pos _ k (NeZero.pos _)).ne.symm
    exact ⟨z, (Polynomial.isRoot_cyclotomic_iff).1 hz⟩
  exact ⟨fun n => (key n).choose, fun n => (key n).choose_spec⟩

end Field

/-! ### Theta families -/

section Theta

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- **A theta family** on `X` at `ℓ`: Heisenberg central extensions of `X[ℓⁿ⁺¹]` by `k^×`
(in step D, the theta groups `𝒢(𝒪(ℓⁿ⁺¹[0]))`). -/
structure ThetaFamily (X : Over (Spec (.of k))) [GrpObj X] [AlgebraicGeometry.IsAbelianVariety k X]
    (ℓ : ℕ) where
  /-- The groups. -/
  G : ℕ → Type u
  grp : ∀ n, Group (G n)
  /-- The extensions. -/
  H : ∀ n, CentralExt (G n) (Tor X (ℓ ^ (n + 1))) (Additive kˣ)
  /-- The Heisenberg property `Z(G_n) = k^×`. -/
  hZ : ∀ n (g : G n), (∀ h, g * h = h * g) → (H n).p g = 1

attribute [instance] ThetaFamily.grp

variable {X X' : Over (Spec (.of k))} [GrpObj X] [GrpObj X']
  [AlgebraicGeometry.IsAbelianVariety k X] [AlgebraicGeometry.IsAbelianVariety k X']
  {ℓ : ℕ} [NeZero ℓ]

/-- The `AltPairing` of a theta family (`AltPairing.ofTheta`). -/
def ThetaFamily.pairing (T : ThetaFamily X ℓ) (ζ : ℕ → k)
    (hζ : ∀ n, IsPrimitiveRoot (ζ n) (ℓ ^ (n + 1))) : AltPairing X ℓ :=
  AltPairing.ofTheta ζ hζ T.G T.H T.hZ

theorem ThetaFamily.pairing_apply (T : ThetaFamily X ℓ) (ζ : ℕ → k)
    (hζ : ∀ n, IsPrimitiveRoot (ζ n) (ℓ ^ (n + 1))) (n : ℕ) (x y : Tor X (ℓ ^ (n + 1))) :
    (T.pairing ζ hζ).e n x y =
      torsionLog (hζ n) ⟨(T.H n).pairing x y, (T.H n).pairing_mem_torsion
        (tor_nsmul_eq_zero X _) x y⟩ := rfl

/-- **The scalar `s_n`** of the theta pairing in coordinates `c`: the `ζ_n`-logarithm of the
commutator of lifts of the two basis vectors. -/
theorem ThetaFamily.sCoord_pairing (T : ThetaFamily X ℓ) (ζ : ℕ → k)
    (hζ : ∀ n, IsPrimitiveRoot (ζ n) (ℓ ^ (n + 1))) (n : ℕ)
    (c : Tor X (ℓ ^ (n + 1)) ≃+ (Fin 2 → ZMod (ℓ ^ (n + 1)))) :
    sCoord ((T.pairing ζ hζ).e n) c =
      torsionLog (hζ n) ⟨(T.H n).pairing (bas c 0) (bas c 1), (T.H n).pairing_mem_torsion
        (tor_nsmul_eq_zero X _) _ _⟩ := rfl

/-- **Anti-isometry for the theta pairings ⟺ anti-isometry of the `k^×`-valued commutator
pairings** (the same `ζ` for both). -/
theorem antiIsom_iff_pairing (T : ThetaFamily X ℓ) (T' : ThetaFamily X' ℓ) (ζ : ℕ → k)
    (hζ : ∀ n, IsPrimitiveRoot (ζ n) (ℓ ^ (n + 1))) (n : ℕ)
    (v : Tor X (ℓ ^ (n + 1)) ≃+ Tor X' (ℓ ^ (n + 1))) :
    v ∈ antiIsom (T.pairing ζ hζ) (T'.pairing ζ hζ) n ↔
      ∀ x y, (T'.H n).pairing (v x) (v y) = -(T.H n).pairing x y := by
  refine forall_congr' fun x => forall_congr' fun y => ?_
  rw [ThetaFamily.pairing_apply, ThetaFamily.pairing_apply, ← map_neg]
  constructor
  · intro h
    exact congrArg Subtype.val (torsionLog_injective (hζ n) h)
  · intro h
    congr 1
    exact Subtype.ext h

/-- `det u = −s_n/s'_n` in coordinates (`antiIsom_iff_det`). -/
theorem mem_antiIsom_iff_det (T : ThetaFamily X ℓ) (T' : ThetaFamily X' ℓ) (ζ : ℕ → k)
    (hζ : ∀ n, IsPrimitiveRoot (ζ n) (ℓ ^ (n + 1))) (n : ℕ)
    (c : Tor X (ℓ ^ (n + 1)) ≃+ (Fin 2 → ZMod (ℓ ^ (n + 1))))
    (c' : Tor X' (ℓ ^ (n + 1)) ≃+ (Fin 2 → ZMod (ℓ ^ (n + 1))))
    (v : Tor X (ℓ ^ (n + 1)) ≃+ Tor X' (ℓ ^ (n + 1))) :
    v ∈ antiIsom (T.pairing ζ hζ) (T'.pairing ζ hζ) n ↔
      (coordMat c c' v).det = -sCoord ((T.pairing ζ hζ).e n) c *
        (sCoord ((T'.pairing ζ hζ).e n) c')⁻¹ :=
  antiIsom_iff_det ((T.pairing ζ hζ).alt n) ((T'.pairing ζ hζ).alt n)
    ((T'.pairing ζ hζ).nondeg n) c c' v

/-- **Step D, algebraic half.** An anti-isometric gluing `u_n` lifts to a level structure in
`𝒢_n ×_{k^×} 𝒢'_n` over its graph. -/
theorem graphLevel_of_antiIsom (T : ThetaFamily X ℓ) (T' : ThetaFamily X' ℓ) (ζ : ℕ → k)
    (hζ : ∀ n, IsPrimitiveRoot (ζ n) (ℓ ^ (n + 1))) (n : ℕ)
    (v : Tor X (ℓ ^ (n + 1)) ≃+ Tor X' (ℓ ^ (n + 1)))
    (hv : v ∈ antiIsom (T.pairing ζ hζ) (T'.pairing ζ hζ) n) :
    Nonempty (CentralExt.GraphLevel (T.H n) (T'.H n) v) := by
  letI := divisibleBy_units k
  exact CentralExt.exists_graphLevel v ((antiIsom_iff_pairing T T' ζ hζ n v).1 hv)

/-- **The descended theta group is trivial** (principal polarization on `B_n`). -/
theorem centralizer_of_antiIsom (T : ThetaFamily X ℓ) (T' : ThetaFamily X' ℓ) (ζ : ℕ → k)
    (hζ : ∀ n, IsPrimitiveRoot (ζ n) (ℓ ^ (n + 1))) (n : ℕ)
    (v : Tor X (ℓ ^ (n + 1)) ≃+ Tor X' (ℓ ^ (n + 1)))
    (hv : v ∈ antiIsom (T.pairing ζ hζ) (T'.pairing ζ hζ) n)
    (L : CentralExt.GraphLevel (T.H n) (T'.H n) v) (g : T.G n) (g' : T'.G n)
    (hcomm : ∀ x, (T.H n).commVal g (L.σ x) + (T'.H n).commVal g' (L.σ' x) = 0) :
    ∃ x α β, g = L.σ x * (T.H n).ι α ∧ g' = L.σ' x * (T'.H n).ι β :=
  CentralExt.centralizer_graphLevel (T'.hZ n) ((antiIsom_iff_pairing T T' ζ hζ n v).1 hv) L g g'
    hcomm

end Theta

/-! ### The step-D seam at a finite field -/

section Seam

open RamanujanWeil.Ihara RamanujanWeil.Arith.Deuring.Mult

variable (K : Type u) [Field K] [Fintype K]

/-- **The remaining geometry of route F2′ (named): D-geom + Θ + J + C.** For two elliptic curves
of the same ordinary trace and an odd prime `ℓ ≠ p`, the concrete Jacobians carry theta families
(the theta groups `𝒢(𝒪(ℓⁿ⁺¹[0]))`, D-geom) such that every family of graph quotients
`B_n = (J × J')/graph(u_n)` whose graphs lift to level subgroups of `𝒢_n ×_{k̄^×} 𝒢'_n` is finite
up to equivariant isomorphism.

Mathematically: by Mumford's descent (§23 Thm 2, D-geom) a level subgroup descends
`ℓⁿ⁺¹(λ × λ')` to `B_n`, with theta group `Z(Γ̃)/Γ̃`, which is trivial by
`centralizer_of_antiIsom`. So `B_n` is principally polarized; Θ, J and C (genus-2 curves over
`𝔽_q` are finite, `Pencil.genus2ModelExistence`, plus C-Jac) give finiteness. -/
def ThetaDescentFiniteness : Prop :=
  ∀ (W W' : WeierstrassCurve K) [W.IsElliptic] [W'.IsElliptic] (S : Jac.JacSite W)
    (S' : Jac.JacSite W'), traceOfFrob W' = traceOfFrob W →
    ¬ (ringChar K : ℤ) ∣ traceOfFrob W → traceOfFrob W ^ 2 < 4 * (Nat.card K : ℤ) →
    ∀ ℓ : ℕ, ℓ.Prime → ℓ ≠ 2 → IsUnit (ℓ : AlgebraicClosure K) →
      ∃ (T : ThetaFamily S.J ℓ) (T' : ThetaFamily S'.J ℓ),
        ∀ (v : ∀ n : ℕ, Tor S.J (ℓ ^ (n + 1)) ≃+ Tor S'.J (ℓ ^ (n + 1)))
          (hv : ∀ n x, v n (torAct S.π _ x) = torAct S'.π _ (v n x)),
          (∀ n, Nonempty (CentralExt.GraphLevel (T.H n) (T'.H n) (v n))) →
          ∀ G : ∀ n, Glue (Γ ℓ v n), ∃ n m, n ≠ m ∧ ∃ e : (G n).B ≅ (G m).B,
            IsMonHom e.hom ∧ e.hom ≫ (G m).πB S.π S'.π hv = (G n).πB S.π S'.π hv ≫ e.hom

variable {K}

/-- **`ThetaDescentFiniteness ⇒ TateFinitenessLag`**, with `ε, ε'` the theta pairings
`AltPairing.ofTheta` for one common choice of roots of unity. -/
theorem tateFinitenessLag_of_thetaDescent (h : ThetaDescentFiniteness K) :
    TateFinitenessLag K := by
  intro W W' _ _ S S' ht hp hlt ℓ hℓ hodd hℓk
  haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
  obtain ⟨ζ, hζ⟩ := exists_primitiveRoots (AlgebraicClosure K) hℓk
  obtain ⟨T, T', hT⟩ := h W W' S S' ht hp hlt ℓ hℓ hodd hℓk
  refine ⟨T.pairing ζ hζ, T'.pairing ζ hζ, ?_⟩
  intro v hv hS G
  exact hT v hv (fun n => graphLevel_of_antiIsom T T' ζ hζ n (v n) (hS n)) G

/-- `ThetaDescentFiniteness` at every finite field. -/
def ThetaDescentFinitenessAll : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (n : ℕ), 1 ≤ n →
    letI : Fintype (GaloisField p n) := Fintype.ofFinite _
    ThetaDescentFiniteness (GaloisField p n)

theorem tateFinitenessLagAll_of_thetaDescent (h : ThetaDescentFinitenessAll) :
    TateFinitenessLagAll := fun p _ n hn =>
  letI : Fintype (GaloisField p n) := Fintype.ofFinite _
  tateFinitenessLag_of_thetaDescent (h p n hn)

end Seam

end RamanujanWeil.Arith.Deuring.Geom.G7.Fin.Weil
