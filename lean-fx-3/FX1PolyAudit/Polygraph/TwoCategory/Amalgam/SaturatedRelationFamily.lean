import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.Amalgam.SaturatedRelationFamily

/-! # FX1PolyAudit.Polygraph.TwoCategory.Amalgam.SaturatedRelationFamily — zero-axiom gate for the parametric
saturated relation-family library (RELFAM r1, #2213)

Per-declaration zero-axiom gate: the family record (`SaturatedRelationFamily`), the family-generic transport
(`SaturatedRelationFamily.decider`), the three instances (`idempotentRelationFamily` / `involutionRelationFamily`
/ `monadRelationFamily`), the three full-hom definitional-agreement regressions
(`idempotentRelationFamily_decider_eq_shipped` / `involutionRelationFamily_decider_eq_thin` /
`monadRelationFamily_decider_eq_walker`), the non-vacuity smokes (idempotent / involution isTrue + their `_holds`,
`involutionIdentityCell`, monad assoc isTrue + faces isFalse), and the honesty markers (parametric-library `true`,
the two deeper tiers `false`).

Every declaration below must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`,
`omega`. -/

namespace FX1PolyAudit

-- the record + the family-generic transport (P1/P2)
#assert_no_axioms FX1Poly.Polygraph.Amalgam.SaturatedRelationFamily
#assert_no_axioms FX1Poly.Polygraph.Amalgam.SaturatedRelationFamily.decider

-- the three instances (P3/P4 + the separating member)
#assert_no_axioms FX1Poly.Polygraph.Amalgam.idempotentRelationFamily
#assert_no_axioms FX1Poly.Polygraph.Amalgam.involutionRelationFamily
#assert_no_axioms FX1Poly.Polygraph.Amalgam.monadRelationFamily

-- the three full-hom definitional-agreement regressions
#assert_no_axioms FX1Poly.Polygraph.Amalgam.idempotentRelationFamily_decider_eq_shipped
#assert_no_axioms FX1Poly.Polygraph.Amalgam.involutionRelationFamily_decider_eq_thin
#assert_no_axioms FX1Poly.Polygraph.Amalgam.monadRelationFamily_decider_eq_walker

-- non-vacuity smokes (P6)
#assert_no_axioms FX1Poly.Polygraph.Amalgam.idempotentFamilyDecidesTrue_smoke
#assert_no_axioms FX1Poly.Polygraph.Amalgam.idempotentFamilyDecidesTrue_smoke_holds
#assert_no_axioms FX1Poly.Polygraph.Amalgam.involutionIdentityCell
#assert_no_axioms FX1Poly.Polygraph.Amalgam.involutionFamilyDecidesTrue_smoke
#assert_no_axioms FX1Poly.Polygraph.Amalgam.involutionFamilyDecidesTrue_smoke_holds
#assert_no_axioms FX1Poly.Polygraph.Amalgam.monadFamilyAssocVerdict
#assert_no_axioms FX1Poly.Polygraph.Amalgam.monadFamilyFacesVerdict

-- honesty markers (P5)
#assert_no_axioms FX1Poly.Polygraph.Amalgam.fxRelFam_hasParametricFamilyLibrary
#assert_no_axioms FX1Poly.Polygraph.Amalgam.fxRelFam_hasInvariantTierFamilyDecision
#assert_no_axioms FX1Poly.Polygraph.Amalgam.fxRelFam_hasNormalFormTierFamilyDecision

end FX1PolyAudit
