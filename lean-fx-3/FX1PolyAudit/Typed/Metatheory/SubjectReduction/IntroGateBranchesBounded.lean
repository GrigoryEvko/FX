import FX1PolyAudit.DependencyAudit
import FX1Poly.Typed.Metatheory.SubjectReduction.IntroGateBranchesBounded

/-! # FX1PolyAudit/.../IntroGateBranchesBounded — zero-axiom gate for the bounded intro-gate branches

Per-declaration zero-axiom gate for the 16 fuel-bounded introducer-congruence branches (the SR-WF-TIEOFF intro
third's per-generator closers).  Each must be free of `propext`, `Quot.sound`, `Classical`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Typed.boolTrueIntroGateBranchClosesBounded
#assert_no_axioms FX1Poly.Typed.boolFalseIntroGateBranchClosesBounded
#assert_no_axioms FX1Poly.Typed.unitIntroGateBranchClosesBounded
#assert_no_axioms FX1Poly.Typed.interval0IntroGateBranchClosesBounded
#assert_no_axioms FX1Poly.Typed.interval1IntroGateBranchClosesBounded
#assert_no_axioms FX1Poly.Typed.natZeroIntroGateBranchClosesBounded
#assert_no_axioms FX1Poly.Typed.optionNoneIntroGateBranchClosesBounded
#assert_no_axioms FX1Poly.Typed.listNilIntroGateBranchClosesBounded
#assert_no_axioms FX1Poly.Typed.natSuccIntroGateBranchClosesBounded
#assert_no_axioms FX1Poly.Typed.optionSomeIntroGateBranchClosesBounded
#assert_no_axioms FX1Poly.Typed.eitherInlIntroGateBranchClosesBounded
#assert_no_axioms FX1Poly.Typed.eitherInrIntroGateBranchClosesBounded
#assert_no_axioms FX1Poly.Typed.pairIntroGateBranchClosesBounded
#assert_no_axioms FX1Poly.Typed.listConsIntroGateBranchClosesBounded
#assert_no_axioms FX1Poly.Typed.reflIntroGateBranchClosesBounded
#assert_no_axioms FX1Poly.Typed.lamIntroGateBranchClosesBounded

end FX1PolyAudit
