import LeanFX2.Term.PreservesTerm.UniversalChain.LiftFullTerm

/-! # LiftFullLeavesAlpha — TODO POLYCELL: BODY DISABLED

Body depends on cd_lemma / Conv.canonical_form / parStar.confluence /
RawStep.parStar / lift_full_term orchestration deleted in commit c2efaccf.
Replacement lives in polycell.md §5 as FXcdLemma view defs over PolyTerm.
Imports preserved at top so downstream transitive imports still work.
-/

/- TODO POLYCELL: original body preserved as block comment


/-! # LeanFX2.Term.PreservesTerm.UniversalChain.LiftFullLeavesAlpha

Witness-builder layer for the CONVTRANS-C universal chain close-out
(#2070 — "drop the `DispatchAtom` restriction").

The headline `RawStep.par.lift_full_term` lifts a raw parallel step to
the typed layer for any source whose dispatchability is witnessed by a
`DispatchAtom`.  The close-out toward a fully universal lift needs
`DispatchAtom` witnesses to be *constructible* rather than supplied by
the caller.  This file ships the constructible fragment:

* **Atomic builders** — every closed-leaf source term (`unit`,
  `boolTrue`, `boolFalse`, `natZero`, `interval0`, `interval1`,
  `listNil`, `optionNone`, `var`) admits a `DispatchAtom` with no
  side data, so the builder is a one-liner.

* **Derived universal lifts** — combining a builder with the
  dispatcher yields a `StepParExists` for that source *without* the
  caller threading a `DispatchAtom` hypothesis.  These corollaries
  are the shape the #2070 headline consumes once the totality theorem
  enumerates the remaining (data-carrying) constructors.

Every declaration is verified zero-axiom by the matching
`#print axioms` line in `Smoke/AuditUniversalChainAlpha.lean`.
-/

namespace LeanFX2

/-! ## Atomic `DispatchAtom` builders

Each closed-leaf source term is dispatchable with no auxiliary data.
The builders make those witnesses constructible by name, so callers
need not pattern the constructor manually. -/

/-- `Term.unit` is dispatchable. -/
theorem DispatchAtom.ofUnit
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope} :
    DispatchAtom (Term.unit (context := context)
                  : Term context Ty.unit (RawTerm.unit : RawTerm scope)) :=
  DispatchAtom.unit

/-- `Term.boolTrue` is dispatchable. -/
theorem DispatchAtom.ofBoolTrue
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope} :
    DispatchAtom (Term.boolTrue (context := context)
                  : Term context Ty.bool (RawTerm.boolTrue : RawTerm scope)) :=
  DispatchAtom.boolTrue

/-- `Term.boolFalse` is dispatchable. -/
theorem DispatchAtom.ofBoolFalse
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope} :
    DispatchAtom (Term.boolFalse (context := context)
                  : Term context Ty.bool (RawTerm.boolFalse : RawTerm scope)) :=
  DispatchAtom.boolFalse

/-- `Term.natZero` is dispatchable. -/
theorem DispatchAtom.ofNatZero
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope} :
    DispatchAtom (Term.natZero (context := context)
                  : Term context Ty.nat (RawTerm.natZero : RawTerm scope)) :=
  DispatchAtom.natZero

/-- `Term.interval0` is dispatchable. -/
theorem DispatchAtom.ofInterval0
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope} :
    DispatchAtom (Term.interval0 (context := context)
                  : Term context Ty.interval (RawTerm.interval0 : RawTerm scope)) :=
  DispatchAtom.interval0

/-- `Term.interval1` is dispatchable. -/
theorem DispatchAtom.ofInterval1
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope} :
    DispatchAtom (Term.interval1 (context := context)
                  : Term context Ty.interval (RawTerm.interval1 : RawTerm scope)) :=
  DispatchAtom.interval1

/-- `Term.listNil` is dispatchable at any element type. -/
theorem DispatchAtom.ofListNil
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {elementType : Ty level scope} :
    DispatchAtom (Term.listNil (context := context) (elementType := elementType)
                  : Term context (Ty.listType elementType)
                                 (RawTerm.listNil : RawTerm scope)) :=
  DispatchAtom.listNil

/-- `Term.optionNone` is dispatchable at any element type. -/
theorem DispatchAtom.ofOptionNone
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {elementType : Ty level scope} :
    DispatchAtom (Term.optionNone (context := context) (elementType := elementType)
                  : Term context (Ty.optionType elementType)
                                 (RawTerm.optionNone : RawTerm scope)) :=
  DispatchAtom.optionNone

/-- `Term.var` is dispatchable at every position. -/
theorem DispatchAtom.ofVar
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    (position : Fin scope) :
    DispatchAtom (Term.var (context := context) position
                  : Term context (varType context position)
                                 (RawTerm.var position)) :=
  DispatchAtom.var position

/-! ## Recursive closed-value `DispatchAtom` builders

The closed-value constructors are dispatchable whenever their typed
children are, threading the inner `DispatchAtom` witnesses (and an
`IsClosedTy` witness on the element/inner type where the matching
dispatch arm requires one).  These builders make the recursive
`DispatchAtom` family composable — the shape a totality theorem
folds over. -/

/-- `Term.natSucc` is dispatchable when its predecessor is. -/
theorem DispatchAtom.ofNatSucc
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {predRaw : RawTerm scope}
    {predecessor : Term context Ty.nat predRaw}
    (predDispatch : DispatchAtom predecessor) :
    DispatchAtom (Term.natSucc (context := context) predecessor
                  : Term context Ty.nat (RawTerm.natSucc predRaw)) :=
  DispatchAtom.natSucc predecessor predDispatch

/-- `Term.intervalOpp` is dispatchable when its inner value is. -/
theorem DispatchAtom.ofIntervalOpp
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {innerRaw : RawTerm scope}
    {innerValue : Term context Ty.interval innerRaw}
    (innerDispatch : DispatchAtom innerValue) :
    DispatchAtom (Term.intervalOpp (context := context) innerValue
                  : Term context Ty.interval (RawTerm.intervalOpp innerRaw)) :=
  DispatchAtom.intervalOpp innerValue innerDispatch

/-- `Term.intervalJoin` is dispatchable when both sides are. -/
theorem DispatchAtom.ofIntervalJoin
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {leftRaw rightRaw : RawTerm scope}
    {leftValue : Term context Ty.interval leftRaw}
    {rightValue : Term context Ty.interval rightRaw}
    (leftDispatch : DispatchAtom leftValue)
    (rightDispatch : DispatchAtom rightValue) :
    DispatchAtom (Term.intervalJoin (context := context) leftValue rightValue
                  : Term context Ty.interval (RawTerm.intervalJoin leftRaw rightRaw)) :=
  DispatchAtom.intervalJoin leftValue rightValue leftDispatch rightDispatch

/-- `Term.intervalMeet` is dispatchable when both sides are. -/
theorem DispatchAtom.ofIntervalMeet
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {leftRaw rightRaw : RawTerm scope}
    {leftValue : Term context Ty.interval leftRaw}
    {rightValue : Term context Ty.interval rightRaw}
    (leftDispatch : DispatchAtom leftValue)
    (rightDispatch : DispatchAtom rightValue) :
    DispatchAtom (Term.intervalMeet (context := context) leftValue rightValue
                  : Term context Ty.interval (RawTerm.intervalMeet leftRaw rightRaw)) :=
  DispatchAtom.intervalMeet leftValue rightValue leftDispatch rightDispatch

/-- `Term.listCons` is dispatchable when its head/tail are dispatchable
and the element type is closed. -/
theorem DispatchAtom.ofListCons
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {elementType : Ty level scope}
    (elementClosed : IsClosedTy elementType)
    {headRaw tailRaw : RawTerm scope}
    {headTerm : Term context elementType headRaw}
    {tailTerm : Term context (Ty.listType elementType) tailRaw}
    (headDispatch : DispatchAtom headTerm)
    (tailDispatch : DispatchAtom tailTerm) :
    DispatchAtom (Term.listCons (context := context) headTerm tailTerm
                  : Term context (Ty.listType elementType)
                                 (RawTerm.listCons headRaw tailRaw)) :=
  DispatchAtom.listCons elementClosed headTerm tailTerm headDispatch tailDispatch

/-- `Term.optionSome` is dispatchable when its value is dispatchable and
the element type is closed. -/
theorem DispatchAtom.ofOptionSome
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {elementType : Ty level scope}
    (elementClosed : IsClosedTy elementType)
    {valueRaw : RawTerm scope}
    {valueTerm : Term context elementType valueRaw}
    (valueDispatch : DispatchAtom valueTerm) :
    DispatchAtom (Term.optionSome (context := context) valueTerm
                  : Term context (Ty.optionType elementType)
                                 (RawTerm.optionSome valueRaw)) :=
  DispatchAtom.optionSome elementClosed valueTerm valueDispatch

/-- `Term.eitherInl` is dispatchable when its value is dispatchable and
the left type is closed. -/
theorem DispatchAtom.ofEitherInl
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {leftType rightType : Ty level scope}
    (leftClosed : IsClosedTy leftType)
    {valueRaw : RawTerm scope}
    {valueTerm : Term context leftType valueRaw}
    (valueDispatch : DispatchAtom valueTerm) :
    DispatchAtom (Term.eitherInl (context := context) (rightType := rightType) valueTerm
                  : Term context (Ty.eitherType leftType rightType)
                                 (RawTerm.eitherInl valueRaw)) :=
  DispatchAtom.eitherInl leftClosed valueTerm valueDispatch

/-- `Term.eitherInr` is dispatchable when its value is dispatchable and
the right type is closed. -/
theorem DispatchAtom.ofEitherInr
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {leftType rightType : Ty level scope}
    (rightClosed : IsClosedTy rightType)
    {valueRaw : RawTerm scope}
    {valueTerm : Term context rightType valueRaw}
    (valueDispatch : DispatchAtom valueTerm) :
    DispatchAtom (Term.eitherInr (context := context) (leftType := leftType) valueTerm
                  : Term context (Ty.eitherType leftType rightType)
                                 (RawTerm.eitherInr valueRaw)) :=
  DispatchAtom.eitherInr rightClosed valueTerm valueDispatch

/-- `Term.recordIntro` is dispatchable when its field is dispatchable
and the field type is closed. -/
theorem DispatchAtom.ofRecordIntro
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {singleFieldType : Ty level scope}
    (fieldClosed : IsClosedTy singleFieldType)
    {firstRaw : RawTerm scope}
    {firstField : Term context singleFieldType firstRaw}
    (fieldDispatch : DispatchAtom firstField) :
    DispatchAtom (Term.recordIntro (context := context) firstField
                  : Term context (Ty.record singleFieldType)
                                 (RawTerm.recordIntro firstRaw)) :=
  DispatchAtom.recordIntro fieldClosed firstField fieldDispatch

/-- `Term.recordProj` is dispatchable when its record value is
dispatchable and the field type is closed. -/
theorem DispatchAtom.ofRecordProj
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {singleFieldType : Ty level scope}
    (fieldClosed : IsClosedTy singleFieldType)
    {recordRaw : RawTerm scope}
    {recordValue : Term context (Ty.record singleFieldType) recordRaw}
    (recordDispatch : DispatchAtom recordValue) :
    DispatchAtom (Term.recordProj (context := context) recordValue
                  : Term context singleFieldType (RawTerm.recordProj recordRaw)) :=
  DispatchAtom.recordProj fieldClosed recordValue recordDispatch

/-! ## Derived universal lifts

Combining an atomic builder with the dispatcher gives a
`StepParExists` for the source term directly — the close-out shape
that does not expose the `DispatchAtom` hypothesis. -/

/-- Universal lift for `Term.unit`. -/
theorem RawStep.par.lift_universal_unit
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {targetRaw : RawTerm scope}
    (rawStep : RawStep.par (RawTerm.unit : RawTerm scope) targetRaw) :
    StepParExists (Term.unit (context := context)
                   : Term context Ty.unit (RawTerm.unit : RawTerm scope))
                  targetRaw :=
  RawStep.par.lift_full_term DispatchAtom.ofUnit rawStep

/-- Universal lift for `Term.boolTrue`. -/
theorem RawStep.par.lift_universal_boolTrue
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {targetRaw : RawTerm scope}
    (rawStep : RawStep.par (RawTerm.boolTrue : RawTerm scope) targetRaw) :
    StepParExists (Term.boolTrue (context := context)
                   : Term context Ty.bool (RawTerm.boolTrue : RawTerm scope))
                  targetRaw :=
  RawStep.par.lift_full_term DispatchAtom.ofBoolTrue rawStep

/-- Universal lift for `Term.boolFalse`. -/
theorem RawStep.par.lift_universal_boolFalse
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {targetRaw : RawTerm scope}
    (rawStep : RawStep.par (RawTerm.boolFalse : RawTerm scope) targetRaw) :
    StepParExists (Term.boolFalse (context := context)
                   : Term context Ty.bool (RawTerm.boolFalse : RawTerm scope))
                  targetRaw :=
  RawStep.par.lift_full_term DispatchAtom.ofBoolFalse rawStep

/-- Universal lift for `Term.natZero`. -/
theorem RawStep.par.lift_universal_natZero
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {targetRaw : RawTerm scope}
    (rawStep : RawStep.par (RawTerm.natZero : RawTerm scope) targetRaw) :
    StepParExists (Term.natZero (context := context)
                   : Term context Ty.nat (RawTerm.natZero : RawTerm scope))
                  targetRaw :=
  RawStep.par.lift_full_term DispatchAtom.ofNatZero rawStep

/-- Universal lift for `Term.interval0`. -/
theorem RawStep.par.lift_universal_interval0
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {targetRaw : RawTerm scope}
    (rawStep : RawStep.par (RawTerm.interval0 : RawTerm scope) targetRaw) :
    StepParExists (Term.interval0 (context := context)
                   : Term context Ty.interval (RawTerm.interval0 : RawTerm scope))
                  targetRaw :=
  RawStep.par.lift_full_term DispatchAtom.ofInterval0 rawStep

/-- Universal lift for `Term.interval1`. -/
theorem RawStep.par.lift_universal_interval1
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {targetRaw : RawTerm scope}
    (rawStep : RawStep.par (RawTerm.interval1 : RawTerm scope) targetRaw) :
    StepParExists (Term.interval1 (context := context)
                   : Term context Ty.interval (RawTerm.interval1 : RawTerm scope))
                  targetRaw :=
  RawStep.par.lift_full_term DispatchAtom.ofInterval1 rawStep

/-- Universal lift for `Term.listNil`. -/
theorem RawStep.par.lift_universal_listNil
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {elementType : Ty level scope}
    {targetRaw : RawTerm scope}
    (rawStep : RawStep.par (RawTerm.listNil : RawTerm scope) targetRaw) :
    StepParExists (Term.listNil (context := context) (elementType := elementType)
                   : Term context (Ty.listType elementType)
                                  (RawTerm.listNil : RawTerm scope))
                  targetRaw :=
  RawStep.par.lift_full_term DispatchAtom.ofListNil rawStep

/-- Universal lift for `Term.optionNone`. -/
theorem RawStep.par.lift_universal_optionNone
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {elementType : Ty level scope}
    {targetRaw : RawTerm scope}
    (rawStep : RawStep.par (RawTerm.optionNone : RawTerm scope) targetRaw) :
    StepParExists
      (Term.optionNone (context := context) (elementType := elementType)
       : Term context (Ty.optionType elementType)
                      (RawTerm.optionNone : RawTerm scope))
      targetRaw :=
  RawStep.par.lift_full_term DispatchAtom.ofOptionNone rawStep

/-- Universal lift for `Term.var`. -/
theorem RawStep.par.lift_universal_var
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    (position : Fin scope)
    {targetRaw : RawTerm scope}
    (rawStep : RawStep.par (RawTerm.var position) targetRaw) :
    StepParExists (Term.var (context := context) position
                   : Term context (varType context position)
                                  (RawTerm.var position))
                  targetRaw :=
  RawStep.par.lift_full_term (DispatchAtom.ofVar position) rawStep

/-! ## Derived universal lifts for recursive closed-value ctors

These thread the inner `DispatchAtom` witness through the recursive
builder, then dispatch — giving a `StepParExists` for the recursive
source without a top-level `DispatchAtom` hypothesis. -/

/-- Universal lift for `Term.natSucc`, given a dispatchable predecessor. -/
theorem RawStep.par.lift_universal_natSucc
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {predRaw : RawTerm scope}
    {predecessor : Term context Ty.nat predRaw}
    (predDispatch : DispatchAtom predecessor)
    {targetRaw : RawTerm scope}
    (rawStep : RawStep.par (RawTerm.natSucc predRaw) targetRaw) :
    StepParExists (Term.natSucc (context := context) predecessor
                   : Term context Ty.nat (RawTerm.natSucc predRaw))
                  targetRaw :=
  RawStep.par.lift_full_term (DispatchAtom.ofNatSucc predDispatch) rawStep

/-- Universal lift for `Term.intervalOpp`, given a dispatchable inner. -/
theorem RawStep.par.lift_universal_intervalOpp
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {innerRaw : RawTerm scope}
    {innerValue : Term context Ty.interval innerRaw}
    (innerDispatch : DispatchAtom innerValue)
    {targetRaw : RawTerm scope}
    (rawStep : RawStep.par (RawTerm.intervalOpp innerRaw) targetRaw) :
    StepParExists (Term.intervalOpp (context := context) innerValue
                   : Term context Ty.interval (RawTerm.intervalOpp innerRaw))
                  targetRaw :=
  RawStep.par.lift_full_term (DispatchAtom.ofIntervalOpp innerDispatch) rawStep

/-- Universal lift for `Term.listCons`, given closed element type plus
dispatchable head and tail. -/
theorem RawStep.par.lift_universal_listCons
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {elementType : Ty level scope}
    (elementClosed : IsClosedTy elementType)
    {headRaw tailRaw : RawTerm scope}
    {headTerm : Term context elementType headRaw}
    {tailTerm : Term context (Ty.listType elementType) tailRaw}
    (headDispatch : DispatchAtom headTerm)
    (tailDispatch : DispatchAtom tailTerm)
    {targetRaw : RawTerm scope}
    (rawStep : RawStep.par (RawTerm.listCons headRaw tailRaw) targetRaw) :
    StepParExists (Term.listCons (context := context) headTerm tailTerm
                   : Term context (Ty.listType elementType)
                                  (RawTerm.listCons headRaw tailRaw))
                  targetRaw :=
  RawStep.par.lift_full_term
    (DispatchAtom.ofListCons elementClosed headDispatch tailDispatch) rawStep

/-- Universal lift for `Term.optionSome`, given closed element type plus
a dispatchable value. -/
theorem RawStep.par.lift_universal_optionSome
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {elementType : Ty level scope}
    (elementClosed : IsClosedTy elementType)
    {valueRaw : RawTerm scope}
    {valueTerm : Term context elementType valueRaw}
    (valueDispatch : DispatchAtom valueTerm)
    {targetRaw : RawTerm scope}
    (rawStep : RawStep.par (RawTerm.optionSome valueRaw) targetRaw) :
    StepParExists (Term.optionSome (context := context) valueTerm
                   : Term context (Ty.optionType elementType)
                                  (RawTerm.optionSome valueRaw))
                  targetRaw :=
  RawStep.par.lift_full_term
    (DispatchAtom.ofOptionSome elementClosed valueDispatch) rawStep

/-! ## Canonical nat-literal totality

The canonical natural-number values (`natZero`, and `natSucc` of a
canonical value) are dispatchable by construction.  `natLiteral`
builds the Term for a `Nat` count, and `natLiteral_isDispatchable`
proves it dispatchable by structural recursion on the count.  This is
the first totality fragment toward #2070: a whole constructor family
whose dispatch witness is produced with no caller-supplied data. -/

/-- The raw form of a canonical nat literal — iterated `RawTerm.natSucc`
over `RawTerm.natZero`.  Matches the raw index of `natLiteral`. -/
def rawNatLiteral {scope : Nat} : (count : Nat) → RawTerm scope
  | 0 => RawTerm.natZero
  | count + 1 => RawTerm.natSucc (rawNatLiteral count)

/-- The canonical `Term.nat` value for a literal count, built as an
iterated `Term.natSucc` over `Term.natZero`. -/
def natLiteral {mode : Mode} {level scope : Nat} {context : Ctx mode level scope} :
    (count : Nat) →
    Term context (Ty.nat (level := level)) (rawNatLiteral count)
  | 0 => Term.natZero
  | count + 1 => Term.natSucc (natLiteral count)

/-- Every canonical nat literal is dispatchable.  Structural recursion
on the count: `natZero` is an atom, `natSucc` threads the predecessor's
dispatch witness through `DispatchAtom.ofNatSucc`. -/
theorem natLiteral_isDispatchable
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope} :
    (count : Nat) →
    DispatchAtom (natLiteral (context := context) (level := level) count)
  | 0 => DispatchAtom.ofNatZero
  | count + 1 => DispatchAtom.ofNatSucc (natLiteral_isDispatchable count)

/-- Universal lift for any canonical nat literal — no `DispatchAtom`
hypothesis exposed; the witness is built internally from the count. -/
theorem RawStep.par.lift_universal_natLiteral
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    (count : Nat)
    {targetRaw : RawTerm scope}
    (rawStep : RawStep.par (rawNatLiteral count) targetRaw) :
    StepParExists (natLiteral (context := context) (level := level) count) targetRaw :=
  RawStep.par.lift_full_term (natLiteral_isDispatchable count) rawStep

end LeanFX2

-/
