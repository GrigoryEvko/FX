import FX1PolyAudit.DependencyAudit
import FX1Poly.Typed.Metatheory.SubjectReduction.IntroGateBranches

/-! # FX1PolyAudit/.../IntroGateBranches — zero-axiom gate

Per-declaration zero-axiom gate for the fourteen `Conv`-refl-output per-generator branches of the SR-DSL-5
introducer congruence gate:

  * the eight nullary data constructors (`boolTrue` / `boolFalse` / `unit` / `interval0` / `interval1` / `natZero` /
    `optionNone` / `listNil`) — vacuous `childStep` over the constant `childNil` member cell;
  * the six recursive / grown data constructors (`natSucc` / `optionSome` / `eitherInl` / `eitherInr` / `pair` /
    `listCons`) — one arg steps, the symbolic-`argsAfter` `ObligationsDrift` threads through `introGateRowReassemble`.

The two output-DRIFTING rows (`refl`, `lam`) and the affine `pathLam` row (blocked by the interval-fibrancy
obstruction) are not yet present.  Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`,
`omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Typed.boolTrueIntroGateBranchCloses
#assert_no_axioms FX1Poly.Typed.boolFalseIntroGateBranchCloses
#assert_no_axioms FX1Poly.Typed.unitIntroGateBranchCloses
#assert_no_axioms FX1Poly.Typed.interval0IntroGateBranchCloses
#assert_no_axioms FX1Poly.Typed.interval1IntroGateBranchCloses
#assert_no_axioms FX1Poly.Typed.natZeroIntroGateBranchCloses
#assert_no_axioms FX1Poly.Typed.optionNoneIntroGateBranchCloses
#assert_no_axioms FX1Poly.Typed.listNilIntroGateBranchCloses
#assert_no_axioms FX1Poly.Typed.natSuccIntroGateBranchCloses
#assert_no_axioms FX1Poly.Typed.optionSomeIntroGateBranchCloses
#assert_no_axioms FX1Poly.Typed.eitherInlIntroGateBranchCloses
#assert_no_axioms FX1Poly.Typed.eitherInrIntroGateBranchCloses
#assert_no_axioms FX1Poly.Typed.pairIntroGateBranchCloses
#assert_no_axioms FX1Poly.Typed.listConsIntroGateBranchCloses

end FX1PolyAudit
