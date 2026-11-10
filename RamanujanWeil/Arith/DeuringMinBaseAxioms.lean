import RamanujanWeil.Arith.DeuringMinBase

/-!
# Axiom audit: `ExistsMinimalBase` (`docs/ARITH_DEURING_MINBASE.md`)

Every declaration below should depend only on `[propext, Classical.choice, Quot.sound]`.
-/

open RamanujanWeil.Arith.Deuring.MinBase

#print axioms coeff_identity
#print axioms postcompHom_injective
#print axioms coeffs
#print axioms comp_lin_comm
#print axioms comp_lin_eq
#print axioms comm_of_comm_lin
#print axioms eq_of_zpow_eq
#print axioms lin_lin
#print axioms lin_of_lin
#print axioms sq_dvd_of_isGen
#print axioms exists_minimalOrder_gen
#print axioms minimalOrder_of_iso
#print axioms exists_minimalOrder_quotient
#print axioms exists_minimalBase_of_descent
#print axioms existsMinimalBase_of_descent
#print axioms existsMinimalBase
