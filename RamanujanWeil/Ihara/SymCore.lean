import RamanujanWeil.Ihara.Endgame
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Topology.Algebra.Ring.Basic
import Mathlib.Topology.Instances.Matrix

/-!
# M5, part 1: the symmetric power `Symⁿ` of `2 × 2` matrices (Mathlib only)

For a commutative ring `R` and `g ∈ M₂(R)`, `symMat n g ∈ M_{n+1}(R)` is the matrix of `Symⁿ g`
on binary forms of degree `n`: the substitution `σ_g : X₀ ↦ g₀₀X₀ + g₀₁X₁, X₁ ↦ g₁₀X₀ + g₁₁X₁` sends
`X₀ᵇ X₁ⁿ⁻ᵇ` to `∑_c E(g)_{c,b} X₀ᶜ X₁ⁿ⁻ᶜ` with the explicit binomial entries `symEntry n g c b`,
and `symMat n g := E(g)ᵀ`.

* `symMat_mul : symMat n (g * h) = symMat n g * symMat n h`, `symMat_one`; `symHom n` is the
  monoid hom (`σ_{gh} = σ_h ∘ σ_g`, compared on the monomial basis).
* `continuous_symMat`: the entries are polynomials in the entries of `g`.
* `trace_symMat_ten : (symMat 10 g).trace = symTraceR 10 (tr g) (det g)`, where `symTraceR` is
  `symTrace` (`Endgame.lean`) over an arbitrary commutative ring, `Int.cast_symTrace`.
* `sum_pow_mul_pow_eq_symTraceR_ten : ∑_{b ≤ 10} uᵇ v¹⁰⁻ᵇ = symTraceR 10 (u + v) (uv)`.
-/

open Finset MvPolynomial

namespace RamanujanWeil.Ihara

section Entries

variable {R : Type*} [CommRing R] (n : ℕ)

/-- `E(g)_{c,b}`: the coefficient of `X₀ᶜ X₁ⁿ⁻ᶜ` in `(g₀₀X₀ + g₀₁X₁)ᵇ (g₁₀X₀ + g₁₁X₁)ⁿ⁻ᵇ`. -/
def symEntry (g : Matrix (Fin 2) (Fin 2) R) (c b : ℕ) : R :=
  ∑ j ∈ range (b + 1), ∑ k ∈ range (n - b + 1),
    if j + k = c then
      ((b.choose j * (n - b).choose k : ℕ) : R) * (g 0 0 ^ j * g 0 1 ^ (b - j) *
        (g 1 0 ^ k * g 1 1 ^ (n - b - k)))
    else 0

/-- **`Symⁿ g`**, an `(n+1) × (n+1)` matrix: `(symMat n g) a b = E(g)_{b,a}`. -/
def symMat (g : Matrix (Fin 2) (Fin 2) R) : Matrix (Fin (n + 1)) (Fin (n + 1)) R :=
  Matrix.of fun a b => symEntry n g b a

/-- The substitution `σ_g`. -/
noncomputable def symSubst (g : Matrix (Fin 2) (Fin 2) R) :
    MvPolynomial (Fin 2) R →ₐ[R] MvPolynomial (Fin 2) R :=
  aeval fun i => C (g i 0) * X 0 + C (g i 1) * X 1

/-- The monomial `X₀ᶜ X₁ⁿ⁻ᶜ`. -/
noncomputable def symMono (c : ℕ) : MvPolynomial (Fin 2) R := X 0 ^ c * X 1 ^ (n - c)

/-- The exponent of `X₀ᶜ X₁ⁿ⁻ᶜ`. -/
noncomputable def symExp (c : ℕ) : Fin 2 →₀ ℕ := Finsupp.single 0 c + Finsupp.single 1 (n - c)

theorem symMono_eq (c : ℕ) : (symMono n c : MvPolynomial (Fin 2) R) = monomial (symExp n c) 1 := by
  rw [symMono, symExp, X_pow_eq_monomial, X_pow_eq_monomial, monomial_mul_monomial, one_mul]

theorem symExp_inj {a c : ℕ} (h : symExp n a = symExp n c) : a = c := by
  have := DFunLike.congr_fun h 0
  simpa [symExp] using this

theorem coeff_symMono (a c : ℕ) :
    (symMono n c : MvPolynomial (Fin 2) R).coeff (symExp n a) = if c = a then 1 else 0 := by
  rw [symMono_eq, coeff_monomial]
  by_cases h : c = a
  · subst h; simp
  · rw [if_neg h, if_neg fun h' => h (symExp_inj n h')]

/-- Coefficient extraction on combinations of the monomials `X₀ᶜ X₁ⁿ⁻ᶜ`, `c ≤ n`. -/
theorem coeff_sum_C_mul_symMono (x : ℕ → R) {a : ℕ} (ha : a ∈ range (n + 1)) :
    (∑ c ∈ range (n + 1), C (x c) * symMono n c).coeff (symExp n a) = x a := by
  rw [coeff_sum]
  simp_rw [coeff_C_mul, coeff_symMono, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq' (range (n + 1)) a x, if_pos ha]

/-- The `(j, k)` term of `E(g)_{·,b}`. -/
def symTerm (g : Matrix (Fin 2) (Fin 2) R) (b j k : ℕ) : R :=
  ((b.choose j * (n - b).choose k : ℕ) : R) * (g 0 0 ^ j * g 0 1 ^ (b - j) *
    (g 1 0 ^ k * g 1 1 ^ (n - b - k)))

theorem symEntry_eq (g : Matrix (Fin 2) (Fin 2) R) (c b : ℕ) :
    symEntry n g c b = ∑ j ∈ range (b + 1), ∑ k ∈ range (n - b + 1),
      if j + k = c then symTerm n g b j k else 0 := rfl

/-- **Expansion**: `σ_g(X₀ᵇ X₁ⁿ⁻ᵇ) = ∑_{c ≤ n} E(g)_{c,b} X₀ᶜ X₁ⁿ⁻ᶜ` for `b ≤ n`. -/
theorem symSubst_symMono (g : Matrix (Fin 2) (Fin 2) R) {b : ℕ} (hb : b ≤ n) :
    symSubst g (symMono n b) = ∑ c ∈ range (n + 1), C (symEntry n g c b) * symMono n c := by
  have lhs : symSubst g (symMono n b) =
      ∑ j ∈ range (b + 1), ∑ k ∈ range (n - b + 1), C (symTerm n g b j k) * symMono n (j + k) := by
    rw [symSubst, symMono, map_mul, map_pow, map_pow, aeval_X, aeval_X, add_pow, add_pow,
      Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun j hj => Finset.sum_congr rfl fun k hk => ?_
    rw [mem_range] at hj hk
    have e : n - (j + k) = (b - j) + (n - b - k) := by omega
    rw [symMono, e, symTerm]
    simp only [map_mul, map_pow, map_natCast, Nat.cast_mul]
    ring
  rw [lhs]
  symm
  calc ∑ c ∈ range (n + 1), C (symEntry n g c b) * symMono n c
      = ∑ c ∈ range (n + 1), ∑ j ∈ range (b + 1), ∑ k ∈ range (n - b + 1),
          (if j + k = c then C (symTerm n g b j k) * symMono n c else 0) := by
        refine Finset.sum_congr rfl fun c _ => ?_
        rw [symEntry_eq, map_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [map_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun k _ => ?_
        split_ifs <;> simp
    _ = ∑ j ∈ range (b + 1), ∑ k ∈ range (n - b + 1), ∑ c ∈ range (n + 1),
          (if j + k = c then C (symTerm n g b j k) * symMono n c else 0) := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun j _ => Finset.sum_comm
    _ = _ := by
        refine Finset.sum_congr rfl fun j hj => Finset.sum_congr rfl fun k hk => ?_
        rw [mem_range] at hj hk
        rw [Finset.sum_ite_eq (range (n + 1)) (j + k), if_pos (mem_range.2 (by omega))]

theorem symSubst_C (g : Matrix (Fin 2) (Fin 2) R) (r : R) : symSubst g (C r) = C r :=
  aeval_C _ _

theorem symSubst_mul (g h : Matrix (Fin 2) (Fin 2) R) :
    symSubst (g * h) = (symSubst h).comp (symSubst g) := by
  refine MvPolynomial.algHom_ext fun i => ?_
  simp only [symSubst, AlgHom.comp_apply, aeval_X, map_add, map_mul, aeval_C,
    Matrix.mul_apply, Fin.sum_univ_two, map_add, map_mul, MvPolynomial.algebraMap_eq]
  ring

theorem symSubst_one : symSubst (1 : Matrix (Fin 2) (Fin 2) R) = AlgHom.id R _ := by
  refine MvPolynomial.algHom_ext fun i => ?_
  fin_cases i <;> simp [symSubst]

theorem symEntry_mul (g h : Matrix (Fin 2) (Fin 2) R) {a b : ℕ} (ha : a ≤ n) (hb : b ≤ n) :
    symEntry n (g * h) a b = ∑ c ∈ range (n + 1), symEntry n h a c * symEntry n g c b := by
  have key : symSubst (g * h) (symMono n b) =
      ∑ c ∈ range (n + 1),
        C (∑ c' ∈ range (n + 1), symEntry n h c c' * symEntry n g c' b) * symMono n c := by
    rw [symSubst_mul, AlgHom.comp_apply, symSubst_symMono n g hb, map_sum]
    have : ∀ c' ∈ range (n + 1), symSubst h (C (symEntry n g c' b) * symMono n c') =
        ∑ c ∈ range (n + 1), C (symEntry n h c c' * symEntry n g c' b) * symMono n c := by
      intro c' hc'
      rw [map_mul, symSubst_C, symSubst_symMono n h (Nat.lt_succ_iff.1 (mem_range.1 hc')),
        Finset.mul_sum]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [map_mul]; ring
    rw [Finset.sum_congr rfl this, Finset.sum_comm]
    simp_rw [← Finset.sum_mul, ← map_sum]
  have h1 := congrArg (fun P => P.coeff (symExp n a)) key
  rw [symSubst_symMono n _ hb, coeff_sum_C_mul_symMono n _ (mem_range.2 (by omega)),
    coeff_sum_C_mul_symMono n _ (mem_range.2 (by omega))] at h1
  exact h1

theorem symEntry_one {a b : ℕ} (ha : a ≤ n) (hb : b ≤ n) :
    symEntry n (1 : Matrix (Fin 2) (Fin 2) R) a b = if b = a then 1 else 0 := by
  have h1 := congrArg (fun P => P.coeff (symExp n a)) (symSubst_symMono n (1 : Matrix _ _ R) hb)
  simp only [symSubst_one, AlgHom.id_apply] at h1
  rw [coeff_sum_C_mul_symMono n _ (mem_range.2 (by omega)), coeff_symMono] at h1
  exact h1.symm

theorem symMat_mul (g h : Matrix (Fin 2) (Fin 2) R) :
    symMat n (g * h) = symMat n g * symMat n h := by
  ext a b
  rw [symMat, Matrix.of_apply, symEntry_mul n g h (Nat.lt_succ_iff.1 b.2) (Nat.lt_succ_iff.1 a.2),
    Matrix.mul_apply, ← Fin.sum_univ_eq_sum_range (fun c => symEntry n h b c * symEntry n g c a)]
  refine Finset.sum_congr rfl fun c _ => ?_
  simp only [symMat, Matrix.of_apply]
  ring

theorem symMat_one : symMat n (1 : Matrix (Fin 2) (Fin 2) R) = 1 := by
  ext a b
  rw [symMat, Matrix.of_apply, symEntry_one n (Nat.lt_succ_iff.1 b.2) (Nat.lt_succ_iff.1 a.2),
    Matrix.one_apply]
  by_cases h : a = b
  · subst h; simp
  · rw [if_neg h, if_neg fun h' => h (Fin.ext h')]

/-- `Symⁿ` as a monoid hom `M₂(R) →* M_{n+1}(R)`. -/
def symHom : Matrix (Fin 2) (Fin 2) R →* Matrix (Fin (n + 1)) (Fin (n + 1)) R where
  toFun := symMat n
  map_one' := symMat_one n
  map_mul' := symMat_mul n

@[simp] theorem symHom_apply (g : Matrix (Fin 2) (Fin 2) R) : symHom n g = symMat n g := rfl

theorem symMat_pow (g : Matrix (Fin 2) (Fin 2) R) (m : ℕ) :
    symMat n (g ^ m) = symMat n g ^ m :=
  map_pow (symHom n) g m

theorem continuous_symMat [TopologicalSpace R] [IsTopologicalRing R] :
    Continuous (symMat n : Matrix (Fin 2) (Fin 2) R → _) := by
  refine continuous_pi fun a => continuous_pi fun b => ?_
  simp only [symMat, Matrix.of_apply, symEntry]
  refine continuous_finsetSum _ fun j _ => continuous_finsetSum _ fun k _ => ?_
  split_ifs
  · fun_prop
  · exact continuous_const

end Entries

/-! ### The trace of `Sym¹⁰` -/

section Trace

variable {R : Type*} [CommRing R]

/-- `symTrace` (`Endgame.lean`) over an arbitrary commutative ring. -/
def symTraceR (k : ℕ) (a q : R) : R :=
  ∑ j ∈ range (k / 2 + 1), (-q) ^ j * ((k - j).choose j : R) * a ^ (k - 2 * j)

theorem Int.cast_symTrace (k : ℕ) (a q : ℤ) :
    ((symTrace k a q : ℤ) : R) = symTraceR k (a : R) (q : R) := by
  simp [symTrace, symTraceR]

/-- **`tr Sym¹⁰ g = symTrace 10 (tr g) (det g)`.** -/
theorem trace_symMat_ten (g : Matrix (Fin 2) (Fin 2) R) :
    (symMat 10 g).trace = symTraceR 10 g.trace g.det := by
  rw [Matrix.trace, Matrix.det_fin_two, Matrix.trace_fin_two]
  simp only [Matrix.diag, symMat, Matrix.of_apply, symEntry, symTraceR, Fin.sum_univ_succ,
    Fin.sum_univ_zero]
  norm_num [Finset.sum_range_succ, Nat.choose]
  ring

/-- `∑_{b ≤ 10} uᵇ v¹⁰⁻ᵇ = symTrace 10 (u + v) (uv)`. -/
theorem sum_pow_mul_pow_eq_symTraceR_ten (u v : R) :
    ∑ b : Fin 11, u ^ (b : ℕ) * v ^ (10 - (b : ℕ)) = symTraceR 10 (u + v) (u * v) := by
  simp only [symTraceR, Fin.sum_univ_succ, Fin.sum_univ_zero, Finset.sum_range_succ,
    Finset.sum_range_zero]
  norm_num [Nat.choose]
  ring

end Trace

end RamanujanWeil.Ihara
