import RamanujanWeil.Arith.DeuringG7DGeomFamily

/-!
# Axiom audit for G7-D-geom (`docs/ARITH_DEURING_G7DGEOM.md`)
-/

open RamanujanWeil.Arith.Deuring.Geom.G7.DGeom

-- Translations on the function field (`DeuringG7DGeomTrans`)
#print axioms coordHom_injective
#print axioms transcendental_transX
#print axioms trans_comp
#print axioms transAut

-- The theta group (`DeuringG7DGeomTheta`)
#print axioms thetaAct_mul
#print axioms const_of_map_mulLeft
#print axioms thetaExt
#print axioms thetaExtN

-- The kernel (`DeuringG7DGeomKer`)
#print axioms isPrincipal_XYIdeal'_pow_iff
#print axioms thetaKer_eq_torsion
#print axioms CentralExtTransport.transport

-- The family and the split seam (`DeuringG7DGeomFamily`)
#print axioms curvePtFvp
#print axioms torEquiv
#print axioms thetaFamilyOf
#print axioms thetaDescentFiniteness_of_split
#print axioms deligneBound_of_split
