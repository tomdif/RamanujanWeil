import RamanujanWeil.Ihara.FamilyGeometry

/-!
# M3: `W_p` is integral, hence connected

`Δ ≠ 0` in `𝔽_p[a₁..a₆]`: at `(a₁,a₂,a₃,a₄,a₆) = (0,0,1,0,0)` it is `-27`, at `(0,0,0,-1,0)` it is
`64`, and no prime divides both. Hence `𝔽_p[a][1/Δ]` is a domain and `W_p` is irreducible and
connected (needed by M5 for `LAdicSheaf.exists_representationSheaf_isogeny_of_isLisse`).
-/

open CategoryTheory AlgebraicGeometry MvPolynomial

namespace RamanujanWeil.Ihara.Family

variable (p : ℕ) [Fact p.Prime]

theorem eval_discriminant (v : Fin 5 → ZMod p) :
    MvPolynomial.eval v (discriminant p) =
      (⟨v 0, v 1, v 2, v 3, v 4⟩ : WeierstrassCurve (ZMod p)).Δ := by
  rw [discriminant, ← WeierstrassCurve.map_Δ]
  congr 1
  simp [genericCurve, WeierstrassCurve.map]

theorem discriminant_ne_zero : discriminant p ≠ 0 := by
  intro h
  have h₁ := eval_discriminant p ![0, 0, 1, 0, 0]
  have h₂ := eval_discriminant p ![0, 0, 0, -1, 0]
  rw [h, map_zero] at h₁ h₂
  simp only [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
    WeierstrassCurve.b₈, Matrix.cons_val] at h₁ h₂
  norm_num at h₁ h₂
  have h27 : ((27 : ℕ) : ZMod p) = 0 := by exact_mod_cast h₁
  have h64 : ((64 : ℕ) : ZMod p) = 0 := by exact_mod_cast h₂.symm
  rw [ZMod.natCast_eq_zero_iff] at h27 h64
  have : p ∣ Nat.gcd 27 64 := Nat.dvd_gcd h27 h64
  norm_num at this
  exact (Fact.out : p.Prime).one_lt.ne' this

instance : IsDomain (baseRing p) :=
  IsLocalization.isDomain_localization
    (powers_le_nonZeroDivisors_of_noZeroDivisors (discriminant_ne_zero p))

instance irreducibleSpace_base : IrreducibleSpace (base p) := inferInstance

instance connectedSpace_base : ConnectedSpace (base p) := inferInstance

end RamanujanWeil.Ihara.Family
