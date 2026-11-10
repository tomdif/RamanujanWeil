import RamanujanWeil.Arith.DeuringG7PrincipalFin
import RamanujanWeil.Arith.DeuringG7ThetaSwap

/-!
# Audit: `PrincipalFiniteness` from Θ + J and C-descent

`docs/ARITH_DEURING_G7_PRINCIPAL.md` §5. Every declaration below depends only on
`[propext, Classical.choice, Quot.sound]`.
-/

open RamanujanWeil.Arith.Deuring.Geom.G7.PrincipalFin RamanujanWeil.Arith.Deuring.Geom.G7.Theta

#print axioms finite_weierstrassCurve
#print axioms exists_equivIso_of_genus2
#print axioms exists_equivIso_of_prod
#print axioms principalFiniteness_of_thetaJacobianModel
#print axioms two_mul_trace_mul_card_smul_eq_zero
