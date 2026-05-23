import LeanFX2.Tools.DependencyAudit
import LeanFX2.Term.PreservesTerm.UniversalChain.LiftFullLeavesEpsilon

/-! # AuditUniversalChainEpsilon — CONVTRANS-C close-out witness-builder log

Strict gate + reviewer-facing `#print axioms` log for the
`DispatchAtom` builders and their derived universal lifts shipped in
`UniversalChain/LiftFullLeavesEpsilon.lean` (toward #2070 — dropping
the `DispatchAtom` restriction).  Extends the Alpha coverage with the
schematic-value/leaf, type-code, modal-scaffold, and recursive-
eliminator constructible arms, plus a canonical interval-literal
totality fragment.

Each entry MUST report "does not depend on any axioms" under strict
policy (no propext, no Quot.sound, no Classical.choice, no user
axioms).

## Coverage

* Schematic-value `DispatchAtom` builders (4): `ofRefl`, `ofOeqRefl`,
  `ofEquivReflId`, `ofEquivReflIdAtId`.
* Schematic-leaf `DispatchAtom` builders (3): `ofFunextRefl`,
  `ofFunextReflAtId`, `ofFunextIntroHet`.
* Type-code `DispatchAtom` builders (11): `ofUniverseCode`,
  `ofArrowCode`, `ofPiTyCode`, `ofSigmaTyCode`, `ofProductCode`,
  `ofSumCode`, `ofListCode`, `ofOptionCode`, `ofEitherCode`,
  `ofIdCode`, `ofEquivCode`.
* Modal-scaffold `DispatchAtom` builders (3): `ofModIntro`,
  `ofModElim`, `ofSubsume`.
* Recursive eliminator `DispatchAtom` builders (5): `ofNatElim`,
  `ofNatRec`, `ofListElim`, `ofOptionMatch`, `ofEitherMatch`.
* Derived universal lifts (9): `lift_universal_refl`,
  `lift_universal_oeqRefl`, `lift_universal_equivReflId`,
  `lift_universal_equivReflIdAtId`, `lift_universal_funextRefl`,
  `lift_universal_funextReflAtId`, `lift_universal_funextIntroHet`,
  `lift_universal_arrowCode`, `lift_universal_idCode`.
* Canonical interval-literal totality (4): `IntervalExpr`,
  `rawIntervalLiteral`, `intervalLiteral`,
  `intervalLiteral_isDispatchable`, `lift_universal_intervalLiteral`.
-/

namespace LeanFX2.SmokeUniversalChainEpsilon

/-! ## Strict gates — `#assert_no_axioms` -/

#assert_no_axioms LeanFX2.DispatchAtom.ofRefl
#assert_no_axioms LeanFX2.DispatchAtom.ofOeqRefl
#assert_no_axioms LeanFX2.DispatchAtom.ofEquivReflId
#assert_no_axioms LeanFX2.DispatchAtom.ofEquivReflIdAtId
#assert_no_axioms LeanFX2.DispatchAtom.ofFunextRefl
#assert_no_axioms LeanFX2.DispatchAtom.ofFunextReflAtId
#assert_no_axioms LeanFX2.DispatchAtom.ofFunextIntroHet
#assert_no_axioms LeanFX2.DispatchAtom.ofUniverseCode
#assert_no_axioms LeanFX2.DispatchAtom.ofArrowCode
#assert_no_axioms LeanFX2.DispatchAtom.ofPiTyCode
#assert_no_axioms LeanFX2.DispatchAtom.ofSigmaTyCode
#assert_no_axioms LeanFX2.DispatchAtom.ofProductCode
#assert_no_axioms LeanFX2.DispatchAtom.ofSumCode
#assert_no_axioms LeanFX2.DispatchAtom.ofListCode
#assert_no_axioms LeanFX2.DispatchAtom.ofOptionCode
#assert_no_axioms LeanFX2.DispatchAtom.ofEitherCode
#assert_no_axioms LeanFX2.DispatchAtom.ofIdCode
#assert_no_axioms LeanFX2.DispatchAtom.ofEquivCode
#assert_no_axioms LeanFX2.DispatchAtom.ofModIntro
#assert_no_axioms LeanFX2.DispatchAtom.ofModElim
#assert_no_axioms LeanFX2.DispatchAtom.ofSubsume
#assert_no_axioms LeanFX2.DispatchAtom.ofNatElim
#assert_no_axioms LeanFX2.DispatchAtom.ofNatRec
#assert_no_axioms LeanFX2.DispatchAtom.ofListElim
#assert_no_axioms LeanFX2.DispatchAtom.ofOptionMatch
#assert_no_axioms LeanFX2.DispatchAtom.ofEitherMatch
#assert_no_axioms LeanFX2.RawStep.par.lift_universal_refl
#assert_no_axioms LeanFX2.RawStep.par.lift_universal_oeqRefl
#assert_no_axioms LeanFX2.RawStep.par.lift_universal_equivReflId
#assert_no_axioms LeanFX2.RawStep.par.lift_universal_equivReflIdAtId
#assert_no_axioms LeanFX2.RawStep.par.lift_universal_funextRefl
#assert_no_axioms LeanFX2.RawStep.par.lift_universal_funextReflAtId
#assert_no_axioms LeanFX2.RawStep.par.lift_universal_funextIntroHet
#assert_no_axioms LeanFX2.RawStep.par.lift_universal_arrowCode
#assert_no_axioms LeanFX2.RawStep.par.lift_universal_idCode
#assert_no_axioms LeanFX2.IntervalExpr
#assert_no_axioms LeanFX2.rawIntervalLiteral
#assert_no_axioms LeanFX2.intervalLiteral
#assert_no_axioms LeanFX2.intervalLiteral_isDispatchable
#assert_no_axioms LeanFX2.RawStep.par.lift_universal_intervalLiteral

/-! ## Reviewer-facing log — `#print axioms` -/

#print axioms LeanFX2.DispatchAtom.ofRefl
#print axioms LeanFX2.DispatchAtom.ofOeqRefl
#print axioms LeanFX2.DispatchAtom.ofEquivReflId
#print axioms LeanFX2.DispatchAtom.ofEquivReflIdAtId
#print axioms LeanFX2.DispatchAtom.ofFunextRefl
#print axioms LeanFX2.DispatchAtom.ofFunextReflAtId
#print axioms LeanFX2.DispatchAtom.ofFunextIntroHet
#print axioms LeanFX2.DispatchAtom.ofUniverseCode
#print axioms LeanFX2.DispatchAtom.ofArrowCode
#print axioms LeanFX2.DispatchAtom.ofPiTyCode
#print axioms LeanFX2.DispatchAtom.ofSigmaTyCode
#print axioms LeanFX2.DispatchAtom.ofProductCode
#print axioms LeanFX2.DispatchAtom.ofSumCode
#print axioms LeanFX2.DispatchAtom.ofListCode
#print axioms LeanFX2.DispatchAtom.ofOptionCode
#print axioms LeanFX2.DispatchAtom.ofEitherCode
#print axioms LeanFX2.DispatchAtom.ofIdCode
#print axioms LeanFX2.DispatchAtom.ofEquivCode
#print axioms LeanFX2.DispatchAtom.ofModIntro
#print axioms LeanFX2.DispatchAtom.ofModElim
#print axioms LeanFX2.DispatchAtom.ofSubsume
#print axioms LeanFX2.DispatchAtom.ofNatElim
#print axioms LeanFX2.DispatchAtom.ofNatRec
#print axioms LeanFX2.DispatchAtom.ofListElim
#print axioms LeanFX2.DispatchAtom.ofOptionMatch
#print axioms LeanFX2.DispatchAtom.ofEitherMatch
#print axioms LeanFX2.RawStep.par.lift_universal_refl
#print axioms LeanFX2.RawStep.par.lift_universal_oeqRefl
#print axioms LeanFX2.RawStep.par.lift_universal_equivReflId
#print axioms LeanFX2.RawStep.par.lift_universal_equivReflIdAtId
#print axioms LeanFX2.RawStep.par.lift_universal_funextRefl
#print axioms LeanFX2.RawStep.par.lift_universal_funextReflAtId
#print axioms LeanFX2.RawStep.par.lift_universal_funextIntroHet
#print axioms LeanFX2.RawStep.par.lift_universal_arrowCode
#print axioms LeanFX2.RawStep.par.lift_universal_idCode
#print axioms LeanFX2.IntervalExpr
#print axioms LeanFX2.rawIntervalLiteral
#print axioms LeanFX2.intervalLiteral
#print axioms LeanFX2.intervalLiteral_isDispatchable
#print axioms LeanFX2.RawStep.par.lift_universal_intervalLiteral

end LeanFX2.SmokeUniversalChainEpsilon
