import FX1PolyAudit.DependencyAudit
import FX1Poly.Typed.Metatheory.Reducibility.Candidate.FlatAndDataIntroArms

/-! # FX1PolyAudit/AuditFlatAndDataIntroArms
    — zero-axiom gate for the flat-former validity (FTGEN-5) + data-intro arm (FTGEN-9)

`flatFormerCandidate` + `flatFormerCandidate_valid` (every flat former's candidate is a Girard CR) +
`equivCodeCandidate_valid` (the equivCode live-shape validity) + `inductiveSaturatedIntro` (a constructor-
headed normal value is in its candidate) — direct applications of the shipped Core lemmas; must be free of
`propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Typed.flatFormerCandidate
#assert_no_axioms FX1Poly.Typed.flatFormerCandidate_valid
#assert_no_axioms FX1Poly.Typed.equivCodeCandidate_valid
#assert_no_axioms FX1Poly.Typed.inductiveSaturatedIntro

end FX1PolyAudit
