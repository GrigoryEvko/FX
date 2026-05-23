import LeanFX2.Tools.DependencyAudit
import LeanFX2.Term.PreservesTerm.UniversalChain.LiftFullLeavesAlpha

/-! # AuditUniversalChainAlpha — CONVTRANS-C close-out witness-builder log

Strict gate + reviewer-facing `#print axioms` log for the
`DispatchAtom` atomic builders and their derived universal lifts
shipped in `UniversalChain/LiftFullLeavesAlpha.lean` (toward #2070 —
dropping the `DispatchAtom` restriction).

Each entry MUST report "does not depend on any axioms" under strict
policy (no propext, no Quot.sound, no Classical.choice, no user
axioms).

## Coverage

* Atomic `DispatchAtom` builders (9): `ofUnit`, `ofBoolTrue`,
  `ofBoolFalse`, `ofNatZero`, `ofInterval0`, `ofInterval1`,
  `ofListNil`, `ofOptionNone`, `ofVar` — each names a closed-leaf
  dispatch witness with no side data.
* Derived universal lifts (9): `lift_universal_unit`,
  `lift_universal_boolTrue`, `lift_universal_boolFalse`,
  `lift_universal_natZero`, `lift_universal_interval0`,
  `lift_universal_interval1`, `lift_universal_listNil`,
  `lift_universal_optionNone`, `lift_universal_var` — combine the
  builder with `RawStep.par.lift_full_term` to lift a raw step to
  the typed layer with no `DispatchAtom` hypothesis exposed.
* Recursive closed-value `DispatchAtom` builders (10): `ofNatSucc`,
  `ofIntervalOpp`, `ofIntervalJoin`, `ofIntervalMeet`, `ofListCons`,
  `ofOptionSome`, `ofEitherInl`, `ofEitherInr`, `ofRecordIntro`,
  `ofRecordProj` — thread inner dispatch witnesses (plus an
  `IsClosedTy` witness where the arm requires one).
* Recursive derived universal lifts (4): `lift_universal_natSucc`,
  `lift_universal_intervalOpp`, `lift_universal_listCons`,
  `lift_universal_optionSome`.
* Canonical nat-literal totality (4): `rawNatLiteral`, `natLiteral`,
  `natLiteral_isDispatchable`, `lift_universal_natLiteral` — a whole
  constructor family proven dispatchable by structural recursion on
  the count, with no caller-supplied dispatch data. -/

namespace LeanFX2.SmokeUniversalChainAlpha

/-! ## Strict gates — `#assert_no_axioms` -/

#assert_no_axioms LeanFX2.DispatchAtom.ofUnit
#assert_no_axioms LeanFX2.DispatchAtom.ofBoolTrue
#assert_no_axioms LeanFX2.DispatchAtom.ofBoolFalse
#assert_no_axioms LeanFX2.DispatchAtom.ofNatZero
#assert_no_axioms LeanFX2.DispatchAtom.ofInterval0
#assert_no_axioms LeanFX2.DispatchAtom.ofInterval1
#assert_no_axioms LeanFX2.DispatchAtom.ofListNil
#assert_no_axioms LeanFX2.DispatchAtom.ofOptionNone
#assert_no_axioms LeanFX2.DispatchAtom.ofVar
#assert_no_axioms LeanFX2.RawStep.par.lift_universal_unit
#assert_no_axioms LeanFX2.RawStep.par.lift_universal_boolTrue
#assert_no_axioms LeanFX2.RawStep.par.lift_universal_boolFalse
#assert_no_axioms LeanFX2.RawStep.par.lift_universal_natZero
#assert_no_axioms LeanFX2.RawStep.par.lift_universal_interval0
#assert_no_axioms LeanFX2.RawStep.par.lift_universal_interval1
#assert_no_axioms LeanFX2.RawStep.par.lift_universal_listNil
#assert_no_axioms LeanFX2.RawStep.par.lift_universal_optionNone
#assert_no_axioms LeanFX2.RawStep.par.lift_universal_var
#assert_no_axioms LeanFX2.DispatchAtom.ofNatSucc
#assert_no_axioms LeanFX2.DispatchAtom.ofIntervalOpp
#assert_no_axioms LeanFX2.DispatchAtom.ofIntervalJoin
#assert_no_axioms LeanFX2.DispatchAtom.ofIntervalMeet
#assert_no_axioms LeanFX2.DispatchAtom.ofListCons
#assert_no_axioms LeanFX2.DispatchAtom.ofOptionSome
#assert_no_axioms LeanFX2.DispatchAtom.ofEitherInl
#assert_no_axioms LeanFX2.DispatchAtom.ofEitherInr
#assert_no_axioms LeanFX2.DispatchAtom.ofRecordIntro
#assert_no_axioms LeanFX2.DispatchAtom.ofRecordProj
#assert_no_axioms LeanFX2.RawStep.par.lift_universal_natSucc
#assert_no_axioms LeanFX2.RawStep.par.lift_universal_intervalOpp
#assert_no_axioms LeanFX2.RawStep.par.lift_universal_listCons
#assert_no_axioms LeanFX2.RawStep.par.lift_universal_optionSome
#assert_no_axioms LeanFX2.rawNatLiteral
#assert_no_axioms LeanFX2.natLiteral
#assert_no_axioms LeanFX2.natLiteral_isDispatchable
#assert_no_axioms LeanFX2.RawStep.par.lift_universal_natLiteral

/-! ## Reviewer-facing log — `#print axioms` -/

#print axioms LeanFX2.DispatchAtom.ofUnit
#print axioms LeanFX2.DispatchAtom.ofBoolTrue
#print axioms LeanFX2.DispatchAtom.ofBoolFalse
#print axioms LeanFX2.DispatchAtom.ofNatZero
#print axioms LeanFX2.DispatchAtom.ofInterval0
#print axioms LeanFX2.DispatchAtom.ofInterval1
#print axioms LeanFX2.DispatchAtom.ofListNil
#print axioms LeanFX2.DispatchAtom.ofOptionNone
#print axioms LeanFX2.DispatchAtom.ofVar
#print axioms LeanFX2.RawStep.par.lift_universal_unit
#print axioms LeanFX2.RawStep.par.lift_universal_boolTrue
#print axioms LeanFX2.RawStep.par.lift_universal_boolFalse
#print axioms LeanFX2.RawStep.par.lift_universal_natZero
#print axioms LeanFX2.RawStep.par.lift_universal_interval0
#print axioms LeanFX2.RawStep.par.lift_universal_interval1
#print axioms LeanFX2.RawStep.par.lift_universal_listNil
#print axioms LeanFX2.RawStep.par.lift_universal_optionNone
#print axioms LeanFX2.RawStep.par.lift_universal_var
#print axioms LeanFX2.DispatchAtom.ofNatSucc
#print axioms LeanFX2.DispatchAtom.ofIntervalOpp
#print axioms LeanFX2.DispatchAtom.ofIntervalJoin
#print axioms LeanFX2.DispatchAtom.ofIntervalMeet
#print axioms LeanFX2.DispatchAtom.ofListCons
#print axioms LeanFX2.DispatchAtom.ofOptionSome
#print axioms LeanFX2.DispatchAtom.ofEitherInl
#print axioms LeanFX2.DispatchAtom.ofEitherInr
#print axioms LeanFX2.DispatchAtom.ofRecordIntro
#print axioms LeanFX2.DispatchAtom.ofRecordProj
#print axioms LeanFX2.RawStep.par.lift_universal_natSucc
#print axioms LeanFX2.RawStep.par.lift_universal_intervalOpp
#print axioms LeanFX2.RawStep.par.lift_universal_listCons
#print axioms LeanFX2.RawStep.par.lift_universal_optionSome
#print axioms LeanFX2.rawNatLiteral
#print axioms LeanFX2.natLiteral
#print axioms LeanFX2.natLiteral_isDispatchable
#print axioms LeanFX2.RawStep.par.lift_universal_natLiteral

end LeanFX2.SmokeUniversalChainAlpha
