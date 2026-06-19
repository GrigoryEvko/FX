import FX1PolyAudit.DependencyAudit
import FX1Poly.Typed.Metatheory.Reducibility.Candidate.DataElimArm

/-! # FX1PolyAudit/AuditDataElimArm
    — zero-axiom gate for the data-elimination FT arm (FTGEN-11, first eliminator)

`canonicalDataCandidate` (the elim-native data candidate = `CanonicalFormsPredicate`),
`canonicalDataCandidate_valid` (its Girard CR validity, given values-are-normal), and `twoBranchMatchElim`
(the two-branch-match elimination arm = the Core `boolElimReducibleScrutineeMember`) — must be free of
`propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Typed.canonicalDataCandidate
#assert_no_axioms FX1Poly.Typed.canonicalDataCandidate_valid
#assert_no_axioms FX1Poly.Typed.twoBranchMatchElim

end FX1PolyAudit
