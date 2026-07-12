import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringPositiveMidChordShift

/-! # FX1PolyAudit.…WalkingString.StringPositiveMidChordShiftAxiomWitness — INDEPENDENT axiom witness
(FC-3 r45, R1)

The trusted independent cross-check for the positive-mid chord-shift round: raw `#print axioms` on every
proof-carrying declaration.  Not the fuel-based `#assert_no_axioms` macro (that lives in the sibling gate
file) — these are Lean's own kernel axiom-dependency prints.  Each must print `does not depend on any
axioms`. -/

namespace FX1PolyAudit

#print axioms FX1Poly.Polygraph.stringMatchingChordShift_below_mid
#print axioms FX1Poly.Polygraph.stringMatchingChordShift_above_mid
#print axioms FX1Poly.Polygraph.fxString_hasPositiveMidChordShift

end FX1PolyAudit
