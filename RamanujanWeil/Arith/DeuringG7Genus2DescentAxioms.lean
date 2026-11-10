import RamanujanWeil.Arith.DeuringG7Genus2Descent

/-!
# Axiom audit: G7 C-descent (`docs/ARITH_DEURING_G7_G2DESCENT.md`)

Every result depends only on `[propext, Classical.choice, Quot.sound]`.
-/

open RamanujanWeil.Arith.Deuring.Geom.G7.Genus2Descent

#print axioms invPoly
#print axioms aeval_invPoly
#print axioms Pres.change
#print axioms pres_inv
#print axioms pres_aff
#print axioms τ_aeval
#print axioms affForm_of_mobForm
#print axioms fixForm_of_affForm
#print axioms fixed_of_fixForm
#print axioms exists_fixed_of_mobForm
#print axioms exists_model_of_fixed
#print axioms exists_descended_model
#print axioms frob_apply
#print axioms frobSpec_eq
#print axioms appLE_appTop_ΓSpecIso
#print axioms isFrobSemilinear_frobFF
#print axioms e₂_eq_top
#print axioms exists_pres
#print axioms Genus2FrobCanonical
#print axioms Genus2FixedDescent
#print axioms genus2FrobDescent_of_canonical_of_fixed
