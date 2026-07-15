import FX1PolyAudit.DependencyAudit
import FX1Poly.Typed.Metatheory.SubjectReduction.IntroGateBranches

/-! # FX1PolyAudit/.../IntroGateBranches — zero-axiom gate

Per-declaration zero-axiom gate for the sixteen per-generator branches of the SR-DSL-5 introducer congruence
gate, plus the two head-refutation helpers this module states in full.

Every branch row is DERIVED from its `IntroGateBranchesBounded` twin at `UnionChildSubjectReduction.toBelow`
(the bounded row's child-SR hypothesis is weaker, so the bounded row is the stronger theorem and the unbounded
row is its corollary).  The gate therefore also transitively certifies that the `toBelow` forgetful step and the
bounded twins it fires stay axiom-free:

  * the eight nullary data constructors (`boolTrue` / `boolFalse` / `unit` / `interval0` / `interval1` / `natZero` /
    `optionNone` / `listNil`) — vacuous `childStep` over the constant `childNil` member cell;
  * the six recursive / grown data constructors (`natSucc` / `optionSome` / `eitherInl` / `eitherInr` / `pair` /
    `listCons`) — one arg steps;
  * the two output-DRIFTING rows (`refl`, `lam`);
  * the two `¬ Conv intervalTypeCell _` head refutations (genuine content, not derived).

The affine `pathLam` row (blocked by the interval-fibrancy obstruction) is not present.  Must be free of
`propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Typed.intervalTypeCell_not_conv_natTypeCell
#assert_no_axioms FX1Poly.Typed.intervalTypeCell_not_conv_listTypeCell

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
#assert_no_axioms FX1Poly.Typed.reflIntroGateBranchCloses
#assert_no_axioms FX1Poly.Typed.lamIntroGateBranchCloses

end FX1PolyAudit
