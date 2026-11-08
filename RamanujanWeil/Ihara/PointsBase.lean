import RamanujanWeil.Ihara.FamilyGeometry
import RamanujanWeil.Ihara.PointsCount
import RamanujanWeil.Ihara.IharaStatement

/-!
# M6 (A): point bookkeeping on the base `W_p = Spec 𝔽_p[a₁..a₆][1/Δ]`

For a field `K` over `𝔽_p`:

* `fvpEquiv p K : W_p(K) ≃ {c : Fin 5 → K // (wc c).Δ ≠ 0}`: a `K`-valued point of `W_p` over `𝔽_p`
  (`Stacks.EtaleCohomology.fieldValuedPoints`) is a ring map `𝔽_p[a][1/Δ] → K` (`Spec` is fully
  faithful and every ring map out of `𝔽_p` is the structure map), i.e. a vector `c ∈ K⁵` with
  `Δ(c) ≠ 0` (universal property of `MvPolynomial` and of the localization).
* `fibreCurve p y = (curve p).map (residueMapOf y)`: the Weierstrass equation of the fibre of
  `E → W_p` at `y`, over `κ(y)` (Stacks: `isPullback_fromSpecResidueField` identifies the fibre
  with `projOf (fibreCurve p y)`).
* `fibreCurve_map_residueEmb`: if `g ∈ W_p(K)` lies over the closed point `y = pt g`, with residue
  embedding `σ_g : κ(y) → K`, then `(fibreCurve p y).map σ_g = wc (coords g)`.
* `finsum_closedPoints_eq_sum` (**part A**): for every `G` on closed points and `K` of degree `n`
  over `𝔽_p`,
  `∑_{y closed, deg y ∣ n} deg y · G y = ∑_{c ∈ K⁵, Δ(c) ≠ 0} G (y_c)`, with `y_c = pt (fvpOf c)`.
  (The Frobenius orbits of `{c}` are the fibres of `c ↦ y_c`, each of size `deg y`.)
-/

open CategoryTheory AlgebraicGeometry MvPolynomial Stacks.EtaleCohomology
open AlgebraicGeometry.ModuliEllipticCurves.Weierstrass

noncomputable section

namespace RamanujanWeil.Ihara.Family

variable (p : ℕ) [Fact p.Prime]

/-! ### Coefficient vectors -/

section Coeff

variable {K : Type} [Field K] [Algebra (ZMod p) K]

theorem genericCurve_map_aeval (c : Fin 5 → K) :
    (genericCurve p).map (aeval c : coeffRing p →ₐ[ZMod p] K).toRingHom = wc c := by
  simp [genericCurve, wc, WeierstrassCurve.map]

theorem aeval_discriminant (c : Fin 5 → K) :
    aeval c (discriminant p) = (wc c).Δ := by
  rw [← genericCurve_map_aeval p c, WeierstrassCurve.map_Δ]
  rfl

/-- The ring map `𝔽_p[a][1/Δ] → K`, `aᵢ ↦ cᵢ`, for `Δ(c) ≠ 0`. -/
def evalHom (c : Fin 5 → K) (hc : (wc c).Δ ≠ 0) : baseRing p →+* K :=
  IsLocalization.Away.lift (discriminant p) (g := (aeval c : coeffRing p →ₐ[ZMod p] K).toRingHom)
    (by
      show IsUnit (aeval c (discriminant p))
      rw [aeval_discriminant]
      exact hc.isUnit)

theorem evalHom_comp_algebraMap (c : Fin 5 → K) (hc : (wc c).Δ ≠ 0) :
    (evalHom p c hc).comp (algebraMap (coeffRing p) (baseRing p)) =
      (aeval c : coeffRing p →ₐ[ZMod p] K).toRingHom :=
  IsLocalization.Away.lift_comp _ _

theorem curve_map_evalHom (c : Fin 5 → K) (hc : (wc c).Δ ≠ 0) :
    (curve p).map (evalHom p c hc) = wc c := by
  rw [curve, WeierstrassCurve.baseChange, WeierstrassCurve.map_map, evalHom_comp_algebraMap,
    genericCurve_map_aeval]

omit [Algebra (ZMod p) K] in
/-- Two ring maps `𝔽_p[a][1/Δ] → K` agreeing on the `aᵢ` are equal. -/
theorem baseRing_ringHom_ext {φ ψ : baseRing p →+* K}
    (h : ∀ i, φ (algebraMap (coeffRing p) (baseRing p) (X i)) =
      ψ (algebraMap (coeffRing p) (baseRing p) (X i))) : φ = ψ := by
  refine IsLocalization.ringHom_ext (Submonoid.powers (discriminant p)) ?_
  refine MvPolynomial.ringHom_ext (fun r => ?_) h
  have := Subsingleton.elim (((φ.comp (algebraMap (coeffRing p) (baseRing p))).comp C))
    ((ψ.comp (algebraMap (coeffRing p) (baseRing p))).comp C)
  exact RingHom.congr_fun this r

end Coeff

/-! ### `K`-valued points of `W_p` -/

section Points

variable (K : Type) [Field K] [Algebra (ZMod p) K]

/-- The `K`-valued point of `W_p` with coordinates `c`. -/
def fvpOf (c : Fin 5 → K) (hc : (wc c).Δ ≠ 0) : fieldValuedPoints (toSpecK p) K :=
  ⟨Spec.map (CommRingCat.ofHom (evalHom p c hc)), by
    rw [toSpecK, ← Spec.map_comp]
    congr 1
    ext x
    exact RingHom.congr_fun (Subsingleton.elim
      ((evalHom p c hc).comp (algebraMap (ZMod p) (baseRing p))) (algebraMap (ZMod p) K)) x⟩

variable {K}

/-- The ring map `𝔽_p[a][1/Δ] → K` of a `K`-valued point. -/
def ringOf (g : fieldValuedPoints (toSpecK p) K) : baseRing p →+* K :=
  (Spec.preimage g.1).hom

theorem SpecMap_ringOf (g : fieldValuedPoints (toSpecK p) K) :
    Spec.map (CommRingCat.ofHom (ringOf p g)) = g.1 := by
  rw [ringOf, CommRingCat.ofHom_hom, Spec.map_preimage]

/-- The coefficient vector `c ∈ K⁵` of a `K`-valued point. -/
def coords (g : fieldValuedPoints (toSpecK p) K) : Fin 5 → K :=
  fun i => ringOf p g (algebraMap (coeffRing p) (baseRing p) (X i))

theorem ringOf_comp_algebraMap (g : fieldValuedPoints (toSpecK p) K) :
    (ringOf p g).comp (algebraMap (coeffRing p) (baseRing p)) =
      (aeval (coords p g) : coeffRing p →ₐ[ZMod p] K).toRingHom := by
  refine MvPolynomial.ringHom_ext (fun r => ?_) (fun i => by simp [coords])
  have := Subsingleton.elim (((ringOf p g).comp (algebraMap (coeffRing p) (baseRing p))).comp C)
    (((aeval (coords p g) : coeffRing p →ₐ[ZMod p] K).toRingHom).comp C)
  exact RingHom.congr_fun this r

theorem coords_Δ_ne_zero (g : fieldValuedPoints (toSpecK p) K) : (wc (coords p g)).Δ ≠ 0 := by
  rw [← aeval_discriminant p]
  have h := RingHom.congr_fun (ringOf_comp_algebraMap p g) (discriminant p)
  simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at h
  rw [← h]
  exact ((IsLocalization.Away.algebraMap_isUnit (discriminant p)).map (ringOf p g)).ne_zero

theorem evalHom_coords (g : fieldValuedPoints (toSpecK p) K) :
    evalHom p (coords p g) (coords_Δ_ne_zero p g) = ringOf p g :=
  baseRing_ringHom_ext p fun i => by
    rw [evalHom, IsLocalization.Away.lift_eq]; simp [coords]

theorem curve_map_ringOf (g : fieldValuedPoints (toSpecK p) K) :
    (curve p).map (ringOf p g) = wc (coords p g) := by
  rw [← evalHom_coords, curve_map_evalHom]

variable (K) in
/-- **`W_p(K) ≃ {c ∈ K⁵ : Δ(c) ≠ 0}`.** -/
def fvpEquiv : fieldValuedPoints (toSpecK p) K ≃ {c : Fin 5 → K // (wc c).Δ ≠ 0} where
  toFun g := ⟨coords p g, coords_Δ_ne_zero p g⟩
  invFun c := fvpOf p K c.1 c.2
  left_inv g := Subtype.ext <| by
    show Spec.map (CommRingCat.ofHom (evalHom p (coords p g) _)) = g.1
    rw [evalHom_coords, SpecMap_ringOf]
  right_inv c := Subtype.ext <| funext fun i => by
    show (Spec.preimage (Spec.map (CommRingCat.ofHom (evalHom p c.1 c.2)))).hom _ = _
    rw [Spec.preimage_map, CommRingCat.hom_ofHom, evalHom, IsLocalization.Away.lift_eq]
    simp

theorem ringOf_fvpOf (c : Fin 5 → K) (hc : (wc c).Δ ≠ 0) :
    ringOf p (fvpOf p K c hc) = evalHom p c hc := by
  rw [ringOf, fvpOf]
  simp only [Spec.preimage_map, CommRingCat.hom_ofHom]

theorem coords_fvpOf (c : Fin 5 → K) (hc : (wc c).Δ ≠ 0) : coords p (fvpOf p K c hc) = c :=
  funext fun i => by simp [coords, ringOf_fvpOf, evalHom]

end Points

/-! ### The fibre curve and the residue embedding -/

/-- The Weierstrass equation of the fibre of `E → W_p` at `y`, over `κ(y)`. -/
def fibreCurve (y : base p) : WeierstrassCurve ((base p).residueField y) :=
  (curve p).map (residueMapOf y)

section Residue

variable {K : Type} [Field K] [Algebra (ZMod p) K]

/-- The residue embedding `κ(pt g) → K` of a `K`-valued point `g`. -/
def residueEmb (g : fieldValuedPoints (toSpecK p) K) :
    (base p).residueField (fieldValuedPointsEquiv (toSpecK p) K g).1 →+* K :=
  (fieldValuedPointsEquiv (toSpecK p) K g).2.1.hom

theorem residueEmb_comp (g : fieldValuedPoints (toSpecK p) K) :
    (residueEmb p g).comp (residueMapOf (fieldValuedPointsEquiv (toSpecK p) K g).1) =
      ringOf p g := by
  have h1 : g.1 = Spec.map (fieldValuedPointsEquiv (toSpecK p) K g).2.1 ≫
      (base p).fromSpecResidueField (fieldValuedPointsEquiv (toSpecK p) K g).1 :=
    ((Scheme.SpecToEquivOfField K (base p)).symm_apply_apply g.1).symm
  rw [← SpecMap_residueMapOf, ← Spec.map_comp, ← SpecMap_ringOf p g] at h1
  have h2 := Spec.map_injective h1
  have h3 := congrArg CommRingCat.Hom.hom h2
  simpa [residueEmb] using h3.symm

/-- **The fibre curve at `pt g`, pushed along the residue embedding, is `wc (coords g)`.** -/
theorem fibreCurve_map_residueEmb (g : fieldValuedPoints (toSpecK p) K) :
    (fibreCurve p (fieldValuedPointsEquiv (toSpecK p) K g).1).map (residueEmb p g) =
      wc (coords p g) := by
  rw [fibreCurve, WeierstrassCurve.map_map, residueEmb_comp, curve_map_ringOf]

end Residue

/-! ### Part A: closed points with `deg ∣ n` versus `{c ∈ 𝔽_{pⁿ}⁵ : Δ(c) ≠ 0}` -/

section Sum

variable (K : Type) [Field K] [Algebra (ZMod p) K] [Finite K]

open scoped Classical in
/-- **Part A.** For every function `G` on closed points of `W_p` and every finite extension
`K/𝔽_p` of degree `n`,
`∑_{y closed, deg y ∣ n} deg y · G y = ∑_{c ∈ K⁵, Δ(c) ≠ 0} G (y_c)`, where `y_c` is the closed
point under the `K`-valued point `c`. -/
theorem finsum_closedPoints_eq_sum {M : Type*} [NonAssocSemiring M] (n : ℕ)
    (hn : Module.finrank (ZMod p) K = n) (G : closedPoints (base p) → M) [Fintype K] :
    ∑ᶠ (y : closedPoints (base p)) (_ : residueDegree (toSpecK p) y.1 ∣ n),
        (residueDegree (toSpecK p) y.1 : M) * G y =
      ∑ c : {c : Fin 5 → K // (wc c).Δ ≠ 0},
        G (fvpPoint (toSpecK p) K (fvpOf p K c.1 c.2)) := by
  classical
  subst hn
  rw [finsum_closedPoints_eq (toSpecK p) K G]
  letI : Fintype (fieldValuedPoints (toSpecK p) K) := Fintype.ofFinite _
  rw [finsum_eq_sum_of_fintype]
  exact Fintype.sum_equiv (fvpEquiv p K) (fun g => G (fvpPoint (toSpecK p) K g))
    (fun c => G (fvpPoint (toSpecK p) K (fvpOf p K c.1 c.2))) fun g => by
    rw [show fvpOf p K ((fvpEquiv p K) g).1 ((fvpEquiv p K) g).2 = g from
      (fvpEquiv p K).symm_apply_apply g]

end Sum

end RamanujanWeil.Ihara.Family
