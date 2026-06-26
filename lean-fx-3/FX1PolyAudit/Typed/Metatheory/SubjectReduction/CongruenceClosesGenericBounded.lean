import FX1PolyAudit.DependencyAudit
import FX1Poly.Typed.Metatheory.SubjectReduction.CongruenceClosesGenericBounded

/-! # FX1PolyAudit.Typed.Metatheory.SubjectReduction.CongruenceClosesGenericBounded — zero-axiom gate

Per-declaration zero-axiom gate for the fuel-bounded congruence master (SR-WF-TIEOFF step 4): the bounded master
threading `Below bound` + `sizeLe` through the six-arm induction. (The three bounded gate Props are data, no proof
content.) Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Typed.HasTypeUnion.congruenceClosesGenericAuxBounded

end FX1PolyAudit
