import RamanujanWeil.Arith.DeuringG7FinAlg

/-!
# A3-ord, G7-W (algebra): alternating pairings on `(ℤ/N)²`, anti-isometric gluings, Lagrangian graphs

`docs/ARITH_DEURING_G7_WC.md`, step **W**. Everything the gluing argument of
`DeuringG7FinCore` needs to know about a Weil pairing, as pure algebra over a module `M`
with coordinates `c : M ≃+ (ℤ/N)²`:

* `IsAlt`, `IsNondeg`: alternating and (left) nondegenerate `ℤ/N`-valued pairings.
* `IsAlt.swap`: alternating implies skew.
* `bas`, `sCoord`, `cdet`: the coordinate basis `b₀, b₁`, the scalar `s = e(b₀, b₁)` (the `s_n` of
  the G7-fin doc) and the `2 × 2` determinant of two coordinate vectors.
* **`IsAlt.eq_sCoord_mul_cdet`**: an alternating pairing on a rank-two module is
  `e(x, y) = s · det(c x, c y)`.
* **`IsAlt.isUnit_sCoord`**: `s` is a unit iff (here: if) the pairing is nondegenerate.
* `coordMat_mulVec`, `cdet_mulVec`, **`IsAlt.apply_apply_eq`**: `e'(u x, u y) = s' · det(u) · det(c x, c y)`.
* **`antiIsom_iff_det`**: `u` is anti-isometric (`e'(u x, u y) = −e(x, y)`) iff
  `det(c' ∘ u ∘ c⁻¹) = −s/s'`. This is the identity `detClass e e' (−s/s') = antiIsom` behind
  `PolGraphFiniteness`.
* **`IsAlt.map_map_eq_det`**, **`det_mat_eq_q`**, **`IsAlt.map_map_eq_q`**: every alternating
  pairing satisfies `e(σ x, σ y) = det(σ) e(x, y)`; if `φ² − tφ + q = 0` and `X² − tX + q` has no
  root mod `ℓ`, `det φ = q`. So **`e(φ x, φ y) = q e(x, y)` is automatic** for every alternating
  pairing (the Galois/Frobenius compatibility `e(πP, πQ) = e(P, Q)^q`).
* **`graph_isotropic_iff`**, **`eq_of_forall_graph_orth`**: the graph of `u` is isotropic for
  `e ⊕ e'` iff `u` is anti-isometric, and then it is its own orthogonal (maximal isotropic).
* `exists_alt_of_det`: conversely every unit `c` is `−s/s'` for *some* pair of alternating
  nondegenerate pairings. So the class `−s/s'` carries no information beyond the identity of the
  pairing: the geometric content of W is entirely in *which* pairing (the one of the
  polarization, step D).
-/

namespace RamanujanWeil.Arith.Deuring.Geom.G7.Fin.Weil

open Matrix RamanujanWeil.Arith.Deuring.Geom.G7 RamanujanWeil.Arith.Deuring.Geom.G7.Fin

section Pairing

variable {N : ℕ} {M : Type*} [AddCommGroup M]

/-- An alternating pairing. -/
def IsAlt (e : M →+ M →+ ZMod N) : Prop := ∀ x, e x x = 0

/-- A (left) nondegenerate pairing. -/
def IsNondeg (e : M →+ M →+ ZMod N) : Prop := ∀ x, (∀ y, e x y = 0) → x = 0

/-- Alternating pairings are skew. -/
theorem IsAlt.swap {e : M →+ M →+ ZMod N} (he : IsAlt e) (x y : M) : e y x = -e x y := by
  have h := he (x + y)
  simp only [map_add, AddMonoidHom.add_apply, he x, he y] at h
  linear_combination h

/-- An alternating pairing is right nondegenerate when it is left nondegenerate. -/
theorem IsAlt.nondeg_right {e : M →+ M →+ ZMod N} (he : IsAlt e) (hn : IsNondeg e) (y : M)
    (h : ∀ x, e x y = 0) : y = 0 :=
  hn y fun x => by rw [he.swap, h x, neg_zero]

/-- The coordinate basis `bᵢ = c⁻¹(eᵢ)`. -/
def bas (c : M ≃+ (Fin 2 → ZMod N)) (i : Fin 2) : M := c.symm (Pi.single i 1)

/-- The scalar `s = e(b₀, b₁)` of a pairing in the coordinates `c`. -/
def sCoord (e : M →+ M →+ ZMod N) (c : M ≃+ (Fin 2 → ZMod N)) : ZMod N := e (bas c 0) (bas c 1)

/-- The determinant of two vectors of `(ℤ/N)²`. -/
def cdet (v w : Fin 2 → ZMod N) : ZMod N := v 0 * w 1 - v 1 * w 0

theorem cdet_mulVec (A : Matrix (Fin 2) (Fin 2) (ZMod N)) (v w : Fin 2 → ZMod N) :
    cdet (A *ᵥ v) (A *ᵥ w) = A.det * cdet v w := by
  simp only [cdet, mulVec, dotProduct, Fin.sum_univ_two, det_fin_two]
  ring

theorem cdet_single : cdet (Pi.single 0 1 : Fin 2 → ZMod N) (Pi.single 1 1) = 1 := by
  simp [cdet]

variable [NeZero N]

/-- Every element is an integral combination of the coordinate basis. -/
theorem eq_bas_comb (c : M ≃+ (Fin 2 → ZMod N)) (x : M) :
    x = (c x 0).val • bas c 0 + (c x 1).val • bas c 1 := by
  apply c.injective
  rw [map_add, map_nsmul, map_nsmul, bas, bas, AddEquiv.apply_symm_apply,
    AddEquiv.apply_symm_apply]
  ext i
  fin_cases i <;> simp [Pi.single_apply, -ZMod.natCast_val, nsmul_eq_mul, ZMod.natCast_zmod_val]

omit [NeZero N] in
theorem pair_nsmul_left (e : M →+ M →+ ZMod N) (m : ℕ) (a b : M) :
    e (m • a) b = (m : ZMod N) * e a b := by
  rw [map_nsmul, AddMonoidHom.nsmul_apply, nsmul_eq_mul]

omit [NeZero N] in
theorem pair_nsmul_right (e : M →+ M →+ ZMod N) (m : ℕ) (a b : M) :
    e a (m • b) = (m : ZMod N) * e a b := by
  rw [map_nsmul, nsmul_eq_mul]

/-- **An alternating pairing on a rank-two module is `s · det`.** -/
theorem IsAlt.eq_sCoord_mul_cdet {e : M →+ M →+ ZMod N} (he : IsAlt e)
    (c : M ≃+ (Fin 2 → ZMod N)) (x y : M) : e x y = sCoord e c * cdet (c x) (c y) := by
  conv_lhs => rw [eq_bas_comb c x, eq_bas_comb c y]
  simp only [map_add, AddMonoidHom.add_apply, pair_nsmul_left, pair_nsmul_right, he (bas c 0),
    he (bas c 1), he.swap (bas c 0) (bas c 1), ZMod.natCast_zmod_val, sCoord, cdet]
  ring

/-- **A nondegenerate alternating pairing has unit scalar `s`.** -/
theorem IsAlt.isUnit_sCoord {e : M →+ M →+ ZMod N} (he : IsAlt e) (hn : IsNondeg e)
    (c : M ≃+ (Fin 2 → ZMod N)) : IsUnit (sCoord e c) := by
  rw [isUnit_iff_mem_nonZeroDivisors_of_finite]
  refine mem_nonZeroDivisors_of_ne_zero_imp fun m hm => ?_
  -- `m s = 0` forces `c⁻¹(m, 0)` into the kernel
  have hx : c.symm (Pi.single 0 m) = 0 := hn _ fun y => by
    rw [he.eq_sCoord_mul_cdet c, AddEquiv.apply_symm_apply]
    simp only [cdet, Pi.single_eq_same, Pi.single_apply,
      show (1 : Fin 2) ≠ 0 from by decide, ite_false, zero_mul, sub_zero]
    linear_combination (c y 1) * hm
  have := congrArg (fun v => c v 0) hx
  simpa using this
where
  mem_nonZeroDivisors_of_ne_zero_imp {s : ZMod N} (h : ∀ m : ZMod N, m * s = 0 → m = 0) :
      s ∈ nonZeroDivisors (ZMod N) :=
    mem_nonZeroDivisors_iff.2 ⟨fun m hm => h m (by rwa [mul_comm]), fun m hm => h m hm⟩

omit [NeZero N] in
theorem coordMat_mulVec {M' : Type*} [AddCommGroup M'] (c : M ≃+ (Fin 2 → ZMod N))
    (c' : M' ≃+ (Fin 2 → ZMod N)) (u : M ≃+ M') (x : M) :
    coordMat c c' u *ᵥ c x = c' (u x) := by
  rw [coordMat, mat, LinearMap.toMatrix'_mulVec]
  change c' (u (c.symm (c x))) = _
  rw [AddEquiv.symm_apply_apply]

/-- `e'(u x, u y) = s' · det(u) · det(c x, c y)`. -/
theorem IsAlt.apply_apply_eq {M' : Type*} [AddCommGroup M'] {e' : M' →+ M' →+ ZMod N}
    (he' : IsAlt e') (c : M ≃+ (Fin 2 → ZMod N)) (c' : M' ≃+ (Fin 2 → ZMod N)) (u : M ≃+ M')
    (x y : M) :
    e' (u x) (u y) = sCoord e' c' * (coordMat c c' u).det * cdet (c x) (c y) := by
  rw [he'.eq_sCoord_mul_cdet c', ← coordMat_mulVec c c' u, ← coordMat_mulVec c c' u,
    cdet_mulVec, mul_assoc]

omit [NeZero N] in
theorem cdet_bas (c : M ≃+ (Fin 2 → ZMod N)) : cdet (c (bas c 0)) (c (bas c 1)) = 1 := by
  rw [bas, bas, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply, cdet_single]

/-- **Anti-isometries are the gluings of determinant `−s/s'`.** -/
theorem antiIsom_iff_det {M' : Type*} [AddCommGroup M'] {e : M →+ M →+ ZMod N}
    {e' : M' →+ M' →+ ZMod N} (he : IsAlt e) (he' : IsAlt e') (hn' : IsNondeg e')
    (c : M ≃+ (Fin 2 → ZMod N)) (c' : M' ≃+ (Fin 2 → ZMod N)) (u : M ≃+ M') :
    (∀ x y, e' (u x) (u y) = -e x y) ↔
      (coordMat c c' u).det = -sCoord e c * (sCoord e' c')⁻¹ := by
  have hs' := he'.isUnit_sCoord hn' c'
  have hinv := ZMod.mul_inv_of_unit _ hs'
  constructor
  · intro h
    have h1 := h (bas c 0) (bas c 1)
    rw [he'.apply_apply_eq c c' u, cdet_bas, mul_one] at h1
    change _ = -sCoord e c at h1
    rw [← h1]
    linear_combination -(coordMat c c' u).det * hinv
  · intro h x y
    rw [he'.apply_apply_eq c c' u, h, he.eq_sCoord_mul_cdet c]
    linear_combination (-sCoord e c * cdet (c x) (c y)) * hinv

/-- **Galois compatibility is automatic for alternating pairings**: `e(σ x, σ y) = det(σ) e(x, y)`. -/
theorem IsAlt.map_map_eq_det {e : M →+ M →+ ZMod N} (he : IsAlt e) (c : M ≃+ (Fin 2 → ZMod N))
    (σ : M →+ M) (x y : M) :
    e (σ x) (σ y) =
      (mat ((c.toAddMonoidHom.comp σ).comp c.symm.toAddMonoidHom)).det * e x y := by
  have hσ : ∀ z, mat ((c.toAddMonoidHom.comp σ).comp c.symm.toAddMonoidHom) *ᵥ c z = c (σ z) := by
    intro z
    rw [mat, LinearMap.toMatrix'_mulVec]
    change c (σ (c.symm (c z))) = _
    rw [AddEquiv.symm_apply_apply]
  rw [he.eq_sCoord_mul_cdet c, he.eq_sCoord_mul_cdet c, ← hσ, ← hσ, cdet_mulVec]
  ring

end Pairing

section Frobenius

/-- **`det φ = q`** for `φ² − tφ + q = 0` on `(ℤ/ℓⁿ⁺¹)²` when `X² − tX + q` has no root mod `ℓ`. -/
theorem det_mat_eq_q {ℓ : ℕ} (hℓ : ℓ.Prime) {n : ℕ} {M : Type*} [AddCommGroup M]
    (c : M ≃+ (Fin 2 → ZMod (ℓ ^ (n + 1)))) (φ : M →+ M) (t q : ℤ)
    (hφ : ∀ x, φ (φ x) - t • φ x + q • x = 0)
    (hroot : ∀ a : ZMod ℓ, a ^ 2 - (t : ZMod ℓ) * a + (q : ZMod ℓ) ≠ 0) :
    (mat ((c.toAddMonoidHom.comp φ).comp c.symm.toAddMonoidHom)).det = q := by
  obtain ⟨ψ, hψ⟩ := exists_companion_addEquiv hℓ c φ t q hφ hroot
  set C := companion (t : ZMod (ℓ ^ (n + 1))) q
  set σ₁ : (Fin 2 → ZMod (ℓ ^ (n + 1))) ≃+ (Fin 2 → ZMod (ℓ ^ (n + 1))) := ψ.symm.trans c
  set σ₂ : (Fin 2 → ZMod (ℓ ^ (n + 1))) ≃+ (Fin 2 → ZMod (ℓ ^ (n + 1))) := c.symm.trans ψ
  have hsplit : (c.toAddMonoidHom.comp φ).comp c.symm.toAddMonoidHom =
      (σ₁.toAddMonoidHom.comp C.mulVecLin.toAddMonoidHom).comp σ₂.toAddMonoidHom := by
    refine AddMonoidHom.ext fun v => ?_
    change c (φ (c.symm v)) = c (ψ.symm (C *ᵥ ψ (c.symm v)))
    rw [← hψ, AddEquiv.symm_apply_apply]
  have h12 : mat σ₁.toAddMonoidHom * mat σ₂.toAddMonoidHom = 1 := by
    rw [← mat_comp, ← mat_id]
    congr 1
    refine AddMonoidHom.ext fun v => ?_
    change c (ψ.symm (ψ (c.symm v))) = v
    simp
  rw [hsplit, mat_comp, mat_comp, mat_mulVec, det_mul, det_mul]
  have hC : C.det = q := by simp [C, companion, det_fin_two]
  have hd := congrArg det h12
  rw [det_mul, det_one] at hd
  rw [hC]
  linear_combination (q : ZMod (ℓ ^ (n + 1))) * hd

/-- **`e(φ x, φ y) = q e(x, y)`** for every alternating pairing on `(ℤ/ℓⁿ⁺¹)²`-coordinatized `M`,
when `φ² − tφ + q = 0` and `X² − tX + q` has no root mod `ℓ`. -/
theorem IsAlt.map_map_eq_q {ℓ : ℕ} (hℓ : ℓ.Prime) {n : ℕ} {M : Type*} [AddCommGroup M]
    {e : M →+ M →+ ZMod (ℓ ^ (n + 1))} (he : IsAlt e) (c : M ≃+ (Fin 2 → ZMod (ℓ ^ (n + 1))))
    (φ : M →+ M) (t q : ℤ) (hφ : ∀ x, φ (φ x) - t • φ x + q • x = 0)
    (hroot : ∀ a : ZMod ℓ, a ^ 2 - (t : ZMod ℓ) * a + (q : ZMod ℓ) ≠ 0) (x y : M) :
    e (φ x) (φ y) = q * e x y := by
  have : NeZero (ℓ ^ (n + 1)) := ⟨pow_ne_zero _ hℓ.ne_zero⟩
  rw [he.map_map_eq_det c, det_mat_eq_q hℓ c φ t q hφ hroot]

end Frobenius

section Graph

variable {N : ℕ} {M M' : Type*} [AddCommGroup M] [AddCommGroup M']

/-- **The graph of `u` is isotropic for `e ⊕ e'` iff `u` is anti-isometric.** -/
theorem graph_isotropic_iff (e : M →+ M →+ ZMod N) (e' : M' →+ M' →+ ZMod N) (u : M ≃+ M') :
    (∀ x y, e x y + e' (u x) (u y) = 0) ↔ ∀ x y, e' (u x) (u y) = -e x y := by
  refine forall_congr' fun x => forall_congr' fun y => ?_
  constructor <;> intro h <;> linear_combination h

/-- **The graph of an anti-isometry is maximal isotropic**: an element `(a, b)` orthogonal to
the graph for `e ⊕ e'` lies on the graph. -/
theorem eq_of_forall_graph_orth {e : M →+ M →+ ZMod N} {e' : M' →+ M' →+ ZMod N}
    (hn' : IsNondeg e') (he' : IsAlt e') {u : M ≃+ M'} (hu : ∀ x y, e' (u x) (u y) = -e x y)
    (a : M) (b : M') (h : ∀ x, e a x + e' b (u x) = 0) : b = u a := by
  rw [← sub_eq_zero]
  refine he'.nondeg_right hn' _ fun z => ?_
  obtain ⟨x, rfl⟩ := u.surjective z
  have h1 := h x
  have h2 := hu a x
  rw [he'.swap, map_sub, AddMonoidHom.sub_apply]
  linear_combination -h1 + h2

end Graph

section Converse

variable {N : ℕ} [NeZero N] {M M' : Type*} [AddCommGroup M] [AddCommGroup M']

/-- The determinant pairing `(x, y) ↦ a · det(c x, c y)`. -/
def detPairing (c : M ≃+ (Fin 2 → ZMod N)) (a : ZMod N) : M →+ M →+ ZMod N :=
  AddMonoidHom.mk' (fun x => AddMonoidHom.mk' (fun y => a * cdet (c x) (c y))
    fun y y' => by simp only [cdet, map_add, Pi.add_apply]; ring)
    fun x x' => by ext y; simp only [cdet, map_add, Pi.add_apply, AddMonoidHom.mk'_apply,
      AddMonoidHom.add_apply]; ring

omit [NeZero N] in
theorem detPairing_isAlt (c : M ≃+ (Fin 2 → ZMod N)) (a : ZMod N) : IsAlt (detPairing c a) :=
  fun x => by simp [detPairing, cdet, mul_comm]

omit [NeZero N] in
theorem detPairing_isNondeg (c : M ≃+ (Fin 2 → ZMod N)) {a : ZMod N} (ha : IsUnit a) :
    IsNondeg (detPairing c a) := by
  intro x hx
  obtain ⟨b, hb⟩ := ha.exists_left_inv
  have h0 := hx (c.symm (Pi.single 0 1))
  have h1 := hx (c.symm (Pi.single 1 1))
  simp only [detPairing, AddMonoidHom.mk'_apply, cdet, AddEquiv.apply_symm_apply,
    Pi.single_eq_same, Pi.single_apply, show (1 : Fin 2) ≠ 0 from by decide,
    show (0 : Fin 2) ≠ 1 from by decide, ite_false] at h0 h1
  apply c.injective
  rw [map_zero]
  ext i
  fin_cases i
  · change c x 0 = 0
    linear_combination b * h1 - (c x 0) * hb
  · change c x 1 = 0
    linear_combination -b * h0 - (c x 1) * hb

omit [NeZero N] in
theorem sCoord_detPairing (c : M ≃+ (Fin 2 → ZMod N)) (a : ZMod N) :
    sCoord (detPairing c a) c = a := by
  simp [sCoord, detPairing, cdet_bas]

/-- **No information in the class alone**: for any coordinates and any unit `d`, there are
alternating nondegenerate pairings with `−s/s' = d`. -/
theorem exists_alt_of_det (c : M ≃+ (Fin 2 → ZMod N)) (c' : M' ≃+ (Fin 2 → ZMod N))
    {d : ZMod N} (hd : IsUnit d) :
    ∃ (e : M →+ M →+ ZMod N) (e' : M' →+ M' →+ ZMod N), IsAlt e ∧ IsNondeg e ∧ IsAlt e' ∧
      IsNondeg e' ∧ -sCoord e c * (sCoord e' c')⁻¹ = d := by
  have hinv := ZMod.mul_inv_of_unit _ hd
  have hdi : IsUnit d⁻¹ := ⟨⟨d⁻¹, d, by rw [mul_comm, hinv], hinv⟩, rfl⟩
  refine ⟨detPairing c (-1), detPairing c' d⁻¹, detPairing_isAlt _ _,
    detPairing_isNondeg _ isUnit_one.neg, detPairing_isAlt _ _, detPairing_isNondeg _ hdi, ?_⟩
  rw [sCoord_detPairing, sCoord_detPairing]
  have : (d⁻¹)⁻¹ = d := by
    have h2 := ZMod.mul_inv_of_unit _ hdi
    calc (d⁻¹)⁻¹ = (d * d⁻¹) * (d⁻¹)⁻¹ := by rw [hinv, one_mul]
      _ = d * (d⁻¹ * (d⁻¹)⁻¹) := by ring
      _ = d := by rw [h2, mul_one]
  rw [this]
  ring

end Converse

end RamanujanWeil.Arith.Deuring.Geom.G7.Fin.Weil
