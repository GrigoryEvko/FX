import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringNColourAtomPinRerouteClosure

/-! # FX1PolyAudit.…WalkingString.StringNColourAtomPinRerouteClosureAxiomWitness — INDEPENDENT axiom witness
(FC-4 r7)

The trusted independent cross-check for the closure: raw `#print axioms` (the built-in, NOT the custom
`#assert_no_axioms` command) on the two named any-width determinacy instances and the superseding content
marker.  Each must print `does not depend on any axioms`. -/

namespace FX1PolyAudit

#print axioms FX1Poly.Polygraph.stringPureCupDeterminacyAtTwo
#print axioms FX1Poly.Polygraph.quadPureCupDeterminacyAtThree
#print axioms FX1Poly.Polygraph.fxString_hasNColourAtomPinRerouteClosed

end FX1PolyAudit
