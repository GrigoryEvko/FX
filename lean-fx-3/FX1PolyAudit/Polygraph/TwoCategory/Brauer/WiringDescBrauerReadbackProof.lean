import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescBrauerReadbackProof

/-! # FX1PolyAudit.Polygraph.TwoCategory.Brauer.WiringDescBrauerReadbackProof — zero-axiom gate
(BRAUER-V2 r2 B2: the crossing-only READ-OFF)

Per-declaration zero-axiom gate for the crossing-only READ-OFF that closes the corrected boundary-width-aware readback
`BrauerCrossingOnlyReadbackInRange`: the permutation-forced partner (`permPartnerAt`), the pointwise scan read-off
(`partnerIndexOf_eq_permPartnerAt`), the field-by-field diagram equality
(`extractDiagram_eq_permutationDiagram_ofPermGraph`), and the corrected readback itself
(`brauerCrossingOnlyReadbackInRange_proof`).  Fed by the shipped T2 state invariant `stateIsPermGraph_ofInRange`.

Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`.  Registered in `AuditAll`. -/

namespace FX1PolyAudit

-- The permutation-forced partner + the field-by-field diagram equality
#assert_no_axioms FX1Poly.Polygraph.permPartnerAt
#assert_no_axioms FX1Poly.Polygraph.extractDiagram_eq_permutationDiagram_ofPermGraph

-- ★ The corrected crossing-only readback, PROVEN unconditionally (no readback hypothesis)
#assert_no_axioms FX1Poly.Polygraph.brauerCrossingOnlyReadbackInRange_proof
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_hasCrossingOnlyReadbackProof

end FX1PolyAudit
