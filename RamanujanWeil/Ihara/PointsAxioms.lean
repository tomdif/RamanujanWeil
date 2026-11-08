import RamanujanWeil.Ihara.Assembly
import RamanujanWeil.Ihara.PointsRealizes

/-! Axiom audit for M6 (`docs/IHARA_POINTS.md`). Every line should print
`[propext, Classical.choice, Quot.sound]` (or a subset). -/

open RamanujanWeil.Ihara

#print axioms RamanujanWeil.Ihara.IharaIdentity
#print axioms RamanujanWeil.Ihara.weierstrassSum_eq_of_ihara
#print axioms RamanujanWeil.Ihara.finsum_closedPoints_eq
#print axioms RamanujanWeil.Ihara.Family.fvpEquiv
#print axioms RamanujanWeil.Ihara.Family.fibreCurve_map_residueEmb
#print axioms RamanujanWeil.Ihara.Family.finsum_closedPoints_eq_sum
#print axioms RamanujanWeil.Ihara.extensionTraces_of_extension
#print axioms RamanujanWeil.Ihara.powSum_eq_frobPowerSum
#print axioms RamanujanWeil.Ihara.Family.natCard_residueField
#print axioms RamanujanWeil.Ihara.powSum_fibre_eq_traceOfFrob
#print axioms RamanujanWeil.Ihara.R1StalkCharpolyFibre
#print axioms RamanujanWeil.Ihara.R1StalkCharpolyFibre.toR1StalkCharpoly
#print axioms RamanujanWeil.Ihara.stalkTrace_symR1_fvpOf
#print axioms RamanujanWeil.Ihara.S_eq_pointSum
#print axioms RamanujanWeil.Ihara.deligneBound_of_ihara_M4b
#print axioms RamanujanWeil.Ihara.chartAlgHomEquiv
#print axioms RamanujanWeil.Ihara.fvpChartEquiv
#print axioms RamanujanWeil.Ihara.fvpEquivPoint
#print axioms RamanujanWeil.Ihara.natCard_fieldValuedPoints_projOf
#print axioms RamanujanWeil.Ihara.realizesWeierstrass_projOf
