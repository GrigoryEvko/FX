import LeanFX2.Reduction.ParRed.ParInductive.Inductive
import LeanFX2.Term
import LeanFX2.Foundation.IsClosedTy

/-! # LeanFX2.Term.PreservesTerm.UniversalChain.Core

Domain layer for the CONVTRANS-C universal chain lift:
`StepParExists` packages the typed target existential, and
`DispatchAtom` records the constructors currently admitted by the
universal dispatcher.
-/

namespace LeanFX2

/-- Headline existential: a target type, target Term at that type
and at `targetRaw`, and a typed `Step.par` from source to target. -/
def StepParExists
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType : Ty level scope} {sourceRaw : RawTerm scope}
    (sourceTerm : Term context sourceType sourceRaw)
    (targetRaw : RawTerm scope) : Prop :=
  ∃ (targetType : Ty level scope) (targetTerm : Term context targetType targetRaw),
    Step.par sourceTerm targetTerm

/-- Per-ctor dispatchability predicate.

`DispatchAtom sourceTerm` is inhabited when `sourceTerm` is one of
the Term ctors enumerated below.  Phase A1 ships 25 ctors covering:

* Closed-leaf atoms (10) — raw form admits only `RawStep.par.refl`
  cong; typed target collapses to source.
* Type-code ctors (10) — schematic raw payloads only, no typed
  children; lift descends through `*_inv` raw inversion.
* Schematic-value ctors (5) — raw payload + Ty/UniverseLevel
  parameters, no typed children; lift uses
  free-the-type-via-suffices to destructure source.

Phase A1 follow-up commits extend this predicate with additional
ctors as their dispatch arms land. -/
inductive DispatchAtom :
    {mode : Mode} → {level scope : Nat} → {context : Ctx mode level scope} →
    {sourceType : Ty level scope} → {sourceRaw : RawTerm scope} →
    Term context sourceType sourceRaw → Prop
  | unit {mode : Mode} {level scope : Nat} {context : Ctx mode level scope} :
      DispatchAtom (Term.unit (context := context) : Term context Ty.unit
                    (RawTerm.unit : RawTerm scope))
  | boolTrue {mode : Mode} {level scope : Nat} {context : Ctx mode level scope} :
      DispatchAtom (Term.boolTrue (context := context) : Term context Ty.bool
                    (RawTerm.boolTrue : RawTerm scope))
  | boolFalse {mode : Mode} {level scope : Nat} {context : Ctx mode level scope} :
      DispatchAtom (Term.boolFalse (context := context) : Term context Ty.bool
                    (RawTerm.boolFalse : RawTerm scope))
  | natZero {mode : Mode} {level scope : Nat} {context : Ctx mode level scope} :
      DispatchAtom (Term.natZero (context := context) : Term context Ty.nat
                    (RawTerm.natZero : RawTerm scope))
  | interval0 {mode : Mode} {level scope : Nat}
      {context : Ctx mode level scope} :
      DispatchAtom (Term.interval0 (context := context) : Term context Ty.interval
                    (RawTerm.interval0 : RawTerm scope))
  | interval1 {mode : Mode} {level scope : Nat}
      {context : Ctx mode level scope} :
      DispatchAtom (Term.interval1 (context := context) : Term context Ty.interval
                    (RawTerm.interval1 : RawTerm scope))
  | listNil {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
      {elementType : Ty level scope} :
      DispatchAtom (Term.listNil (context := context)
                                 (elementType := elementType)
                    : Term context (Ty.listType elementType)
                                   (RawTerm.listNil : RawTerm scope))
  | optionNone {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
      {elementType : Ty level scope} :
      DispatchAtom (Term.optionNone (context := context)
                                    (elementType := elementType)
                    : Term context (Ty.optionType elementType)
                                   (RawTerm.optionNone : RawTerm scope))
  | var {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
      (position : Fin scope) :
      DispatchAtom (Term.var (context := context) position
                    : Term context (varType context position)
                                   (RawTerm.var position))
  | universeCode {mode : Mode} {level scope : Nat}
      {context : Ctx mode level scope}
      (innerLevel outerLevel : UniverseLevel)
      (cumulOk : innerLevel.toNat ≤ outerLevel.toNat)
      (levelLe : outerLevel.toNat + 1 ≤ level) :
      DispatchAtom (Term.universeCode (context := context) innerLevel outerLevel
                                       cumulOk levelLe
                    : Term context (Ty.universe outerLevel levelLe)
                                   (RawTerm.universeCode innerLevel.toNat))
  | arrowCode {mode : Mode} {level scope : Nat}
      {context : Ctx mode level scope}
      (outerLevel : UniverseLevel)
      (levelLe : outerLevel.toNat + 1 ≤ level)
      (domainCodeRaw codomainCodeRaw : RawTerm scope) :
      DispatchAtom (Term.arrowCode (context := context) outerLevel levelLe
                                    domainCodeRaw codomainCodeRaw
                    : Term context (Ty.universe outerLevel levelLe)
                                   (RawTerm.arrowCode domainCodeRaw codomainCodeRaw))
  | piTyCode {mode : Mode} {level scope : Nat}
      {context : Ctx mode level scope}
      (outerLevel : UniverseLevel)
      (levelLe : outerLevel.toNat + 1 ≤ level)
      (domainCodeRaw : RawTerm scope)
      (codomainCodeRaw : RawTerm (scope + 1)) :
      DispatchAtom (Term.piTyCode (context := context) outerLevel levelLe
                                   domainCodeRaw codomainCodeRaw
                    : Term context (Ty.universe outerLevel levelLe)
                                   (RawTerm.piTyCode domainCodeRaw codomainCodeRaw))
  | sigmaTyCode {mode : Mode} {level scope : Nat}
      {context : Ctx mode level scope}
      (outerLevel : UniverseLevel)
      (levelLe : outerLevel.toNat + 1 ≤ level)
      (domainCodeRaw : RawTerm scope)
      (codomainCodeRaw : RawTerm (scope + 1)) :
      DispatchAtom (Term.sigmaTyCode (context := context) outerLevel levelLe
                                      domainCodeRaw codomainCodeRaw
                    : Term context (Ty.universe outerLevel levelLe)
                                   (RawTerm.sigmaTyCode domainCodeRaw codomainCodeRaw))
  | productCode {mode : Mode} {level scope : Nat}
      {context : Ctx mode level scope}
      (outerLevel : UniverseLevel)
      (levelLe : outerLevel.toNat + 1 ≤ level)
      (firstCodeRaw secondCodeRaw : RawTerm scope) :
      DispatchAtom (Term.productCode (context := context) outerLevel levelLe
                                      firstCodeRaw secondCodeRaw
                    : Term context (Ty.universe outerLevel levelLe)
                                   (RawTerm.productCode firstCodeRaw secondCodeRaw))
  | sumCode {mode : Mode} {level scope : Nat}
      {context : Ctx mode level scope}
      (outerLevel : UniverseLevel)
      (levelLe : outerLevel.toNat + 1 ≤ level)
      (leftCodeRaw rightCodeRaw : RawTerm scope) :
      DispatchAtom (Term.sumCode (context := context) outerLevel levelLe
                                  leftCodeRaw rightCodeRaw
                    : Term context (Ty.universe outerLevel levelLe)
                                   (RawTerm.sumCode leftCodeRaw rightCodeRaw))
  | listCode {mode : Mode} {level scope : Nat}
      {context : Ctx mode level scope}
      (outerLevel : UniverseLevel)
      (levelLe : outerLevel.toNat + 1 ≤ level)
      (elementCodeRaw : RawTerm scope) :
      DispatchAtom (Term.listCode (context := context) outerLevel levelLe
                                   elementCodeRaw
                    : Term context (Ty.universe outerLevel levelLe)
                                   (RawTerm.listCode elementCodeRaw))
  | optionCode {mode : Mode} {level scope : Nat}
      {context : Ctx mode level scope}
      (outerLevel : UniverseLevel)
      (levelLe : outerLevel.toNat + 1 ≤ level)
      (elementCodeRaw : RawTerm scope) :
      DispatchAtom (Term.optionCode (context := context) outerLevel levelLe
                                     elementCodeRaw
                    : Term context (Ty.universe outerLevel levelLe)
                                   (RawTerm.optionCode elementCodeRaw))
  | eitherCode {mode : Mode} {level scope : Nat}
      {context : Ctx mode level scope}
      (outerLevel : UniverseLevel)
      (levelLe : outerLevel.toNat + 1 ≤ level)
      (leftCodeRaw rightCodeRaw : RawTerm scope) :
      DispatchAtom (Term.eitherCode (context := context) outerLevel levelLe
                                     leftCodeRaw rightCodeRaw
                    : Term context (Ty.universe outerLevel levelLe)
                                   (RawTerm.eitherCode leftCodeRaw rightCodeRaw))
  | idCode {mode : Mode} {level scope : Nat}
      {context : Ctx mode level scope}
      (outerLevel : UniverseLevel)
      (levelLe : outerLevel.toNat + 1 ≤ level)
      (typeCodeRaw leftRaw rightRaw : RawTerm scope) :
      DispatchAtom (Term.idCode (context := context) outerLevel levelLe
                                 typeCodeRaw leftRaw rightRaw
                    : Term context (Ty.universe outerLevel levelLe)
                                   (RawTerm.idCode typeCodeRaw leftRaw rightRaw))
  | equivCode {mode : Mode} {level scope : Nat}
      {context : Ctx mode level scope}
      (outerLevel : UniverseLevel)
      (levelLe : outerLevel.toNat + 1 ≤ level)
      (leftTypeCodeRaw rightTypeCodeRaw : RawTerm scope) :
      DispatchAtom (Term.equivCode (context := context) outerLevel levelLe
                                    leftTypeCodeRaw rightTypeCodeRaw
                    : Term context (Ty.universe outerLevel levelLe)
                                   (RawTerm.equivCode leftTypeCodeRaw rightTypeCodeRaw))
  | oeqRefl {mode : Mode} {level scope : Nat}
      {context : Ctx mode level scope}
      (carrier : Ty level scope) (rawWitness : RawTerm scope) :
      DispatchAtom (Term.oeqRefl (context := context) carrier rawWitness
                    : Term context (Ty.oeq carrier rawWitness rawWitness)
                                   (RawTerm.oeqRefl rawWitness))
  | refl {mode : Mode} {level scope : Nat}
      {context : Ctx mode level scope}
      (carrier : Ty level scope) (rawWitness : RawTerm scope) :
      DispatchAtom (Term.refl (context := context) carrier rawWitness
                    : Term context (Ty.id carrier rawWitness rawWitness)
                                   (RawTerm.refl rawWitness))
  | idStrictRefl {mode : Mode} {level scope : Nat}
      {context : Ctx mode level scope}
      (modeIsStrict : mode = Mode.strict)
      (carrier : Ty level scope) (rawWitness : RawTerm scope) :
      DispatchAtom (Term.idStrictRefl (context := context)
                                       modeIsStrict carrier rawWitness
                    : Term context (Ty.idStrict carrier rawWitness rawWitness)
                                   (RawTerm.idStrictRefl rawWitness))
  | equivReflId {mode : Mode} {level scope : Nat}
      {context : Ctx mode level scope}
      (carrier : Ty level scope) :
      DispatchAtom (Term.equivReflId (context := context) carrier
                    : Term context (Ty.equiv carrier carrier)
                                   (RawTerm.equivIntro
                                     (RawTerm.lam (RawTerm.var ⟨0, Nat.zero_lt_succ scope⟩))
                                     (RawTerm.lam (RawTerm.var ⟨0, Nat.zero_lt_succ scope⟩))))
  | equivReflIdAtId {mode : Mode} {level scope : Nat}
      {context : Ctx mode level scope}
      (innerLevel : UniverseLevel)
      (innerLevelLt : innerLevel.toNat + 1 ≤ level)
      (carrier : Ty level scope) (carrierRaw : RawTerm scope) :
      DispatchAtom (Term.equivReflIdAtId (context := context)
                                          innerLevel innerLevelLt
                                          carrier carrierRaw
                    : Term context
                        (Ty.id (Ty.universe innerLevel innerLevelLt)
                               carrierRaw carrierRaw)
                        (RawTerm.equivIntro
                          (RawTerm.lam (RawTerm.var ⟨0, Nat.zero_lt_succ scope⟩))
                          (RawTerm.lam (RawTerm.var ⟨0, Nat.zero_lt_succ scope⟩))))
  /-- Phase A1 follow-up: closed-type single-child compound ctor.

  `intervalOpp` takes one typed child at the closed type `Ty.interval`.
  The dispatch arm calls `lift_full_intervalOpp` with a callback
  recursively built from the inner `DispatchAtom` witness's IH —
  bridged from two-Ty `StepParExists` to fixed-Ty `Term ctx Ty.interval`
  via `Step.par.preserves_isClosedTy IsClosedTy.interval`. -/
  | intervalOpp {mode : Mode} {level scope : Nat}
      {context : Ctx mode level scope}
      {innerRaw : RawTerm scope}
      (innerValue : Term context Ty.interval innerRaw)
      (innerDispatch : DispatchAtom innerValue) :
      DispatchAtom (Term.intervalOpp (context := context) innerValue
                    : Term context Ty.interval
                                   (RawTerm.intervalOpp innerRaw))
  | intervalJoin {mode : Mode} {level scope : Nat}
      {context : Ctx mode level scope}
      {leftRaw rightRaw : RawTerm scope}
      (leftValue : Term context Ty.interval leftRaw)
      (rightValue : Term context Ty.interval rightRaw)
      (leftDispatch : DispatchAtom leftValue)
      (rightDispatch : DispatchAtom rightValue) :
      DispatchAtom (Term.intervalJoin (context := context) leftValue rightValue
                    : Term context Ty.interval
                                   (RawTerm.intervalJoin leftRaw rightRaw))
  | intervalMeet {mode : Mode} {level scope : Nat}
      {context : Ctx mode level scope}
      {leftRaw rightRaw : RawTerm scope}
      (leftValue : Term context Ty.interval leftRaw)
      (rightValue : Term context Ty.interval rightRaw)
      (leftDispatch : DispatchAtom leftValue)
      (rightDispatch : DispatchAtom rightValue) :
      DispatchAtom (Term.intervalMeet (context := context) leftValue rightValue
                    : Term context Ty.interval
                                   (RawTerm.intervalMeet leftRaw rightRaw))
  | natSucc {mode : Mode} {level scope : Nat}
      {context : Ctx mode level scope}
      {predRaw : RawTerm scope}
      (predecessor : Term context Ty.nat predRaw)
      (predDispatch : DispatchAtom predecessor) :
      DispatchAtom (Term.natSucc (context := context) predecessor
                    : Term context Ty.nat
                                   (RawTerm.natSucc predRaw))
  /-- Parametric closed-type ctor.  Requires `IsClosedTy elementType` so
  the SR bridge for both head (at `elementType`) and tail (at
  `Ty.listType elementType` via `IsClosedTy.listType`) discharges. -/
  | listCons {mode : Mode} {level scope : Nat}
      {context : Ctx mode level scope}
      {elementType : Ty level scope}
      (elementClosed : IsClosedTy elementType)
      {headRaw tailRaw : RawTerm scope}
      (headTerm : Term context elementType headRaw)
      (tailTerm : Term context (Ty.listType elementType) tailRaw)
      (headDispatch : DispatchAtom headTerm)
      (tailDispatch : DispatchAtom tailTerm) :
      DispatchAtom (Term.listCons (context := context) headTerm tailTerm
                    : Term context (Ty.listType elementType)
                                   (RawTerm.listCons headRaw tailRaw))
  /-- Parametric closed-type option ctor. -/
  | optionSome {mode : Mode} {level scope : Nat}
      {context : Ctx mode level scope}
      {elementType : Ty level scope}
      (elementClosed : IsClosedTy elementType)
      {valueRaw : RawTerm scope}
      (valueTerm : Term context elementType valueRaw)
      (valueDispatch : DispatchAtom valueTerm) :
      DispatchAtom (Term.optionSome (context := context) valueTerm
                    : Term context (Ty.optionType elementType)
                                   (RawTerm.optionSome valueRaw))
  /-- Parametric closed-type either-left ctor. -/
  | eitherInl {mode : Mode} {level scope : Nat}
      {context : Ctx mode level scope}
      {leftType rightType : Ty level scope}
      (leftClosed : IsClosedTy leftType)
      {valueRaw : RawTerm scope}
      (valueTerm : Term context leftType valueRaw)
      (valueDispatch : DispatchAtom valueTerm) :
      DispatchAtom (Term.eitherInl (context := context)
                                    (rightType := rightType) valueTerm
                    : Term context (Ty.eitherType leftType rightType)
                                   (RawTerm.eitherInl valueRaw))
  /-- Parametric closed-type either-right ctor. -/
  | eitherInr {mode : Mode} {level scope : Nat}
      {context : Ctx mode level scope}
      {leftType rightType : Ty level scope}
      (rightClosed : IsClosedTy rightType)
      {valueRaw : RawTerm scope}
      (valueTerm : Term context rightType valueRaw)
      (valueDispatch : DispatchAtom valueTerm) :
      DispatchAtom (Term.eitherInr (context := context)
                                    (leftType := leftType) valueTerm
                    : Term context (Ty.eitherType leftType rightType)
                                   (RawTerm.eitherInr valueRaw))
  /-- Non-dependent-motive natural eliminator (current kernel pre-K07.1).
  Branches at `motiveType` and `Ty.arrow Ty.nat motiveType`; both close
  via `IsClosedTy.arrow IsClosedTy.nat motiveClosed`. -/
  | natElim {mode : Mode} {level scope : Nat}
      {context : Ctx mode level scope}
      {motiveType : Ty level scope}
      (motiveClosed : IsClosedTy motiveType)
      {scrutineeRaw zeroRaw succRaw : RawTerm scope}
      (scrutinee : Term context Ty.nat scrutineeRaw)
      (zeroBranch : Term context motiveType zeroRaw)
      (succBranch : Term context (Ty.arrow Ty.nat motiveType) succRaw)
      (scrutDispatch : DispatchAtom scrutinee)
      (zeroDispatch : DispatchAtom zeroBranch)
      (succDispatch : DispatchAtom succBranch) :
      DispatchAtom (Term.natElim (context := context) scrutinee
                                  zeroBranch succBranch
                    : Term context motiveType
                                   (RawTerm.natElim scrutineeRaw zeroRaw
                                                    succRaw))
  /-- Non-dependent-motive natural recursor.  Branches at `motiveType` and
  `Ty.arrow Ty.nat (Ty.arrow motiveType motiveType)`. -/
  | natRec {mode : Mode} {level scope : Nat}
      {context : Ctx mode level scope}
      {motiveType : Ty level scope}
      (motiveClosed : IsClosedTy motiveType)
      {scrutineeRaw zeroRaw succRaw : RawTerm scope}
      (scrutinee : Term context Ty.nat scrutineeRaw)
      (zeroBranch : Term context motiveType zeroRaw)
      (succBranch :
        Term context (Ty.arrow Ty.nat (Ty.arrow motiveType motiveType)) succRaw)
      (scrutDispatch : DispatchAtom scrutinee)
      (zeroDispatch : DispatchAtom zeroBranch)
      (succDispatch : DispatchAtom succBranch) :
      DispatchAtom (Term.natRec (context := context) scrutinee
                                 zeroBranch succBranch
                    : Term context motiveType
                                   (RawTerm.natRec scrutineeRaw zeroRaw
                                                   succRaw))
  /-- Non-dependent-motive list eliminator.  Scrutinee at
  `Ty.listType elementType`; cons branch at
  `Ty.arrow elementType (Ty.arrow (Ty.listType elementType) motiveType)`. -/
  | listElim {mode : Mode} {level scope : Nat}
      {context : Ctx mode level scope}
      {elementType motiveType : Ty level scope}
      (elementClosed : IsClosedTy elementType)
      (motiveClosed : IsClosedTy motiveType)
      {scrutineeRaw nilRaw consRaw : RawTerm scope}
      (scrutinee : Term context (Ty.listType elementType) scrutineeRaw)
      (nilBranch : Term context motiveType nilRaw)
      (consBranch :
        Term context
          (Ty.arrow elementType (Ty.arrow (Ty.listType elementType) motiveType))
          consRaw)
      (scrutDispatch : DispatchAtom scrutinee)
      (nilDispatch : DispatchAtom nilBranch)
      (consDispatch : DispatchAtom consBranch) :
      DispatchAtom (Term.listElim (context := context) scrutinee
                                   nilBranch consBranch
                    : Term context motiveType
                                   (RawTerm.listElim scrutineeRaw nilRaw
                                                     consRaw))
  /-- Non-dependent-motive option matcher.  Scrutinee at
  `Ty.optionType elementType`; some branch at
  `Ty.arrow elementType motiveType`. -/
  | optionMatch {mode : Mode} {level scope : Nat}
      {context : Ctx mode level scope}
      {elementType motiveType : Ty level scope}
      (elementClosed : IsClosedTy elementType)
      (motiveClosed : IsClosedTy motiveType)
      {scrutineeRaw noneRaw someRaw : RawTerm scope}
      (scrutinee : Term context (Ty.optionType elementType) scrutineeRaw)
      (noneBranch : Term context motiveType noneRaw)
      (someBranch : Term context (Ty.arrow elementType motiveType) someRaw)
      (scrutDispatch : DispatchAtom scrutinee)
      (noneDispatch : DispatchAtom noneBranch)
      (someDispatch : DispatchAtom someBranch) :
      DispatchAtom (Term.optionMatch (context := context) scrutinee
                                      noneBranch someBranch
                    : Term context motiveType
                                   (RawTerm.optionMatch scrutineeRaw noneRaw
                                                        someRaw))
  /-- Non-dependent-motive either matcher.  Scrutinee at
  `Ty.eitherType leftType rightType`; left branch at
  `Ty.arrow leftType motiveType`; right branch at
  `Ty.arrow rightType motiveType`. -/
  | eitherMatch {mode : Mode} {level scope : Nat}
      {context : Ctx mode level scope}
      {leftType rightType motiveType : Ty level scope}
      (leftClosed : IsClosedTy leftType)
      (rightClosed : IsClosedTy rightType)
      (motiveClosed : IsClosedTy motiveType)
      {scrutineeRaw leftBranchRaw rightBranchRaw : RawTerm scope}
      (scrutinee :
        Term context (Ty.eitherType leftType rightType) scrutineeRaw)
      (leftBranch :
        Term context (Ty.arrow leftType motiveType) leftBranchRaw)
      (rightBranch :
        Term context (Ty.arrow rightType motiveType) rightBranchRaw)
      (scrutDispatch : DispatchAtom scrutinee)
      (leftDispatch : DispatchAtom leftBranch)
      (rightDispatch : DispatchAtom rightBranch) :
      DispatchAtom (Term.eitherMatch (context := context) scrutinee
                                      leftBranch rightBranch
                    : Term context motiveType
                                   (RawTerm.eitherMatch scrutineeRaw
                                                         leftBranchRaw
                                                         rightBranchRaw))
  /-- Modal-intro scaffold (Layer 1 — `innerType` preserved).  Closed
  inner-type witness propagates to the modal-intro target. -/
  | modIntro {mode : Mode} {level scope : Nat}
      {context : Ctx mode level scope}
      {innerType : Ty level scope}
      (innerClosed : IsClosedTy innerType)
      {innerRaw : RawTerm scope}
      (innerTerm : Term context innerType innerRaw)
      (innerDispatch : DispatchAtom innerTerm) :
      DispatchAtom (Term.modIntro (context := context) innerTerm
                    : Term context innerType
                                   (RawTerm.modIntro innerRaw))
  /-- Modal-elim scaffold (Layer 1 — `innerType` preserved). -/
  | modElim {mode : Mode} {level scope : Nat}
      {context : Ctx mode level scope}
      {innerType : Ty level scope}
      (innerClosed : IsClosedTy innerType)
      {innerRaw : RawTerm scope}
      (innerTerm : Term context innerType innerRaw)
      (innerDispatch : DispatchAtom innerTerm) :
      DispatchAtom (Term.modElim (context := context) innerTerm
                    : Term context innerType
                                   (RawTerm.modElim innerRaw))
  /-- Subsumption (cumulativity Conv-rule scaffold). -/
  | subsume {mode : Mode} {level scope : Nat}
      {context : Ctx mode level scope}
      {innerType : Ty level scope}
      (innerClosed : IsClosedTy innerType)
      {innerRaw : RawTerm scope}
      (innerTerm : Term context innerType innerRaw)
      (innerDispatch : DispatchAtom innerTerm) :
      DispatchAtom (Term.subsume (context := context) innerTerm
                    : Term context innerType
                                   (RawTerm.subsume innerRaw))
  /-- Single-field record introduction.  Closed field-type witness
  propagates to `Ty.record singleFieldType` via `IsClosedTy.record`. -/
  | recordIntro {mode : Mode} {level scope : Nat}
      {context : Ctx mode level scope}
      {singleFieldType : Ty level scope}
      (fieldClosed : IsClosedTy singleFieldType)
      {firstRaw : RawTerm scope}
      (firstField : Term context singleFieldType firstRaw)
      (fieldDispatch : DispatchAtom firstField) :
      DispatchAtom (Term.recordIntro (context := context) firstField
                    : Term context (Ty.record singleFieldType)
                                   (RawTerm.recordIntro firstRaw))
  /-- Record projection at the single-field encoding.  Source carries
  `Ty.record singleFieldType`; target at `singleFieldType`. -/
  | recordProj {mode : Mode} {level scope : Nat}
      {context : Ctx mode level scope}
      {singleFieldType : Ty level scope}
      (fieldClosed : IsClosedTy singleFieldType)
      {recordRaw : RawTerm scope}
      (recordValue : Term context (Ty.record singleFieldType) recordRaw)
      (recordDispatch : DispatchAtom recordValue) :
      DispatchAtom (Term.recordProj (context := context) recordValue
                    : Term context singleFieldType
                                   (RawTerm.recordProj recordRaw))
  /-- Codata destructor.  Source carries `Ty.codata stateType outputType`;
  target at `outputType`.  Both state and output types must be closed. -/
  | codataDest {mode : Mode} {level scope : Nat}
      {context : Ctx mode level scope}
      {stateType outputType : Ty level scope}
      (stateClosed : IsClosedTy stateType)
      (outputClosed : IsClosedTy outputType)
      {codataRaw : RawTerm scope}
      (codataValue : Term context (Ty.codata stateType outputType) codataRaw)
      (codataDispatch : DispatchAtom codataValue) :
      DispatchAtom (Term.codataDest (context := context) codataValue
                    : Term context outputType
                                   (RawTerm.codataDest codataRaw))
  /-- Universe-level cumulativity raise.  Source at
  `Ty.universe lowerLevel levelLeLow`; target at
  `Ty.universe higherLevel levelLeHigh`.  Both ends are unconditionally
  closed (`IsClosedTy.universe`) — no IsClosedTy hypothesis needed. -/
  | cumulUp {mode : Mode} {level scope : Nat}
      {context : Ctx mode level scope}
      (lowerLevel higherLevel : UniverseLevel)
      (cumulMonotone : lowerLevel.toNat ≤ higherLevel.toNat)
      (levelLeLow : lowerLevel.toNat + 1 ≤ level)
      (levelLeHigh : higherLevel.toNat + 1 ≤ level)
      {codeRaw : RawTerm scope}
      (typeCode : Term context (Ty.universe lowerLevel levelLeLow) codeRaw)
      (codeDispatch : DispatchAtom typeCode) :
      DispatchAtom (Term.cumulUp (context := context)
                                  lowerLevel higherLevel cumulMonotone
                                  levelLeLow levelLeHigh typeCode
                    : Term context (Ty.universe higherLevel levelLeHigh)
                                   (RawTerm.cumulUpMarker codeRaw))
  /-- Glue introduction (univalent mode).  Two children share
  `baseType`; closed-base witness propagates to both SR bridges. -/
  | glueIntro {mode : Mode} {level scope : Nat}
      {context : Ctx mode level scope}
      (modeIsUnivalent : mode = Mode.univalent)
      {baseType : Ty level scope}
      (baseClosed : IsClosedTy baseType)
      (boundaryWitness : RawTerm scope)
      {baseRaw partialRaw : RawTerm scope}
      (baseValue : Term context baseType baseRaw)
      (partialValue : Term context baseType partialRaw)
      (baseDispatch : DispatchAtom baseValue)
      (partialDispatch : DispatchAtom partialValue) :
      DispatchAtom (Term.glueIntro (context := context) modeIsUnivalent
                                    baseType boundaryWitness baseValue
                                    partialValue
                    : Term context (Ty.glue baseType boundaryWitness)
                                   (RawTerm.glueIntro baseRaw partialRaw))
  /-- Codata unfold.  State child at `stateType`; transition child at
  `Ty.arrow stateType outputType`.  Both state and output closed. -/
  | codataUnfold {mode : Mode} {level scope : Nat}
      {context : Ctx mode level scope}
      {stateType outputType : Ty level scope}
      (stateClosed : IsClosedTy stateType)
      (outputClosed : IsClosedTy outputType)
      {stateRaw transitionRaw : RawTerm scope}
      (initialState : Term context stateType stateRaw)
      (transition : Term context (Ty.arrow stateType outputType) transitionRaw)
      (stateDispatch : DispatchAtom initialState)
      (transitionDispatch : DispatchAtom transition) :
      DispatchAtom (Term.codataUnfold (context := context)
                                       initialState transition
                    : Term context (Ty.codata stateType outputType)
                                   (RawTerm.codataUnfold stateRaw transitionRaw))
  /-- Equiv application.  Equiv child at `Ty.equiv carrierA carrierB`;
  argument child at `carrierA`.  Both carriers closed. -/
  | equivApp {mode : Mode} {level scope : Nat}
      {context : Ctx mode level scope}
      {carrierA carrierB : Ty level scope}
      (carrierAClosed : IsClosedTy carrierA)
      (carrierBClosed : IsClosedTy carrierB)
      {equivRaw argumentRaw : RawTerm scope}
      (equivTerm : Term context (Ty.equiv carrierA carrierB) equivRaw)
      (argumentTerm : Term context carrierA argumentRaw)
      (equivDispatch : DispatchAtom equivTerm)
      (argumentDispatch : DispatchAtom argumentTerm) :
      DispatchAtom (Term.equivApp (context := context) equivTerm
                                   argumentTerm
                    : Term context carrierB
                                   (RawTerm.equivApp equivRaw argumentRaw))
  /-- Refinement introduction.  Value child at `baseType`; proof child at
  `Ty.unit`.  Only base type needs to be closed. -/
  | refineIntro {mode : Mode} {level scope : Nat}
      {context : Ctx mode level scope}
      {baseType : Ty level scope}
      (baseClosed : IsClosedTy baseType)
      (predicate : RawTerm (scope + 1))
      {valueRaw proofRaw : RawTerm scope}
      (baseValue : Term context baseType valueRaw)
      (predicateProof : Term context Ty.unit proofRaw)
      (valueDispatch : DispatchAtom baseValue)
      (proofDispatch : DispatchAtom predicateProof) :
      DispatchAtom (Term.refineIntro (context := context) predicate
                                      baseValue predicateProof
                    : Term context (Ty.refine baseType predicate)
                                   (RawTerm.refineIntro valueRaw proofRaw))
  /-- Non-dependent lambda (`Term.lam`).  Body sits at
  `codomainType.weaken` under one extended binder; SR bridge consumes
  `IsClosedTy.weaken codomainClosed` to fix the body's target type. -/
  | lam {mode : Mode} {level scope : Nat}
      {context : Ctx mode level scope}
      {domainType codomainType : Ty level scope}
      (codomainClosed : IsClosedTy codomainType)
      {bodyRaw : RawTerm (scope + 1)}
      (body : Term (Ctx.cons context domainType) codomainType.weaken bodyRaw)
      (bodyDispatch : DispatchAtom body) :
      DispatchAtom (Term.lam (context := context)
                              (domainType := domainType) body
                    : Term context (Ty.arrow domainType codomainType)
                                   (RawTerm.lam bodyRaw))
  /-- Dependent Π-lambda (`Term.lamPi`).  Body sits at
  `codomainType : Ty level (scope + 1)` directly; user must supply
  `IsClosedTy codomainType` at the extended scope. -/
  | lamPi {mode : Mode} {level scope : Nat}
      {context : Ctx mode level scope}
      {domainType : Ty level scope}
      {codomainType : Ty level (scope + 1)}
      (codomainClosed : IsClosedTy codomainType)
      {bodyRaw : RawTerm (scope + 1)}
      (body : Term (Ctx.cons context domainType) codomainType bodyRaw)
      (bodyDispatch : DispatchAtom body) :
      DispatchAtom (Term.lamPi (context := context)
                                (domainType := domainType) body
                    : Term context (Ty.piTy domainType codomainType)
                                   (RawTerm.lam bodyRaw))
  /-- Path lambda (univalent-mode binder).  Body at `carrierType.weaken`
  under one interval binder; SR bridge uses `IsClosedTy.weaken`. -/
  | pathLam {mode : Mode} {level scope : Nat}
      {context : Ctx mode level scope}
      (modeIsUnivalent : mode = Mode.univalent)
      (carrierType : Ty level scope)
      (carrierClosed : IsClosedTy carrierType)
      (leftEndpoint rightEndpoint : RawTerm scope)
      {bodyRaw : RawTerm (scope + 1)}
      (body : Term (Ctx.cons context Ty.interval) carrierType.weaken bodyRaw)
      (bodyDispatch : DispatchAtom body) :
      DispatchAtom (Term.pathLam (context := context) modeIsUnivalent
                                  carrierType leftEndpoint rightEndpoint body
                    : Term context (Ty.path carrierType leftEndpoint
                                            rightEndpoint)
                                   (RawTerm.pathLam bodyRaw))
  /-- Non-dependent function application.  Function child at
  `Ty.arrow domainType codomainType`; argument child at `domainType`.
  Both ends require `IsClosedTy` so the SR bridge fixes both child
  target types.  `lift_full_app` absorbs both the cong arm and the
  β-deep arm internally (target type for β is
  `codomainType.weaken.subst0 ... ≡ codomainType` propositionally;
  the two-Ty existential headline absorbs the cast). -/
  | app {mode : Mode} {level scope : Nat}
      {context : Ctx mode level scope}
      {domainType codomainType : Ty level scope}
      (domainClosed : IsClosedTy domainType)
      (codomainClosed : IsClosedTy codomainType)
      {functionRaw argumentRaw : RawTerm scope}
      (functionTerm : Term context (Ty.arrow domainType codomainType)
                                    functionRaw)
      (argumentTerm : Term context domainType argumentRaw)
      (functionDispatch : DispatchAtom functionTerm)
      (argumentDispatch : DispatchAtom argumentTerm) :
      DispatchAtom (Term.app (context := context) functionTerm argumentTerm
                    : Term context codomainType
                                   (RawTerm.app functionRaw argumentRaw))
  /-- Heterogeneous-carrier univalence introduction.  Single typed
  child `equivWitness : Term ctx (Ty.equiv carrierA carrierB)
  (RawTerm.equivIntro forwardRaw backwardRaw)` whose raw matches the
  parent's raw (`RawTerm.equivIntro forwardRaw backwardRaw`).  Requires
  `IsClosedTy` on both carriers so the SR bridge fixes the child
  target type at `Ty.equiv carrierA carrierB`. -/
  | uaIntroHet {mode : Mode} {level scope : Nat}
      {context : Ctx mode level scope}
      (innerLevel : UniverseLevel)
      (innerLevelLt : innerLevel.toNat + 1 ≤ level)
      {carrierA carrierB : Ty level scope}
      (carrierAClosed : IsClosedTy carrierA)
      (carrierBClosed : IsClosedTy carrierB)
      (carrierARaw carrierBRaw : RawTerm scope)
      {forwardRaw backwardRaw : RawTerm scope}
      (equivWitness : Term context (Ty.equiv carrierA carrierB)
                                   (RawTerm.equivIntro forwardRaw backwardRaw))
      (equivWitnessDispatch : DispatchAtom equivWitness) :
      DispatchAtom (Term.uaIntroHet (context := context) innerLevel
                                     innerLevelLt carrierARaw carrierBRaw
                                     equivWitness
                    : Term context (Ty.id (Ty.universe innerLevel innerLevelLt)
                                          carrierARaw carrierBRaw)
                                   (RawTerm.equivIntro forwardRaw backwardRaw))
  /-- Boolean dependent eliminator.  Motive is at scope+1 so the two
  branches live at distinct closed types after substituting the
  Boolean value.  The two `IsClosedTy` witnesses (one per branch type
  after `subst0`) let the driver fix each branch's target type under
  parallel reduction — no new under-subst0 SR lemma required. -/
  | boolElim {mode : Mode} {level scope : Nat}
      {context : Ctx mode level scope}
      {motiveType : Ty level (scope + 1)}
      (thenTypeClosed :
        IsClosedTy (motiveType.subst0 Ty.bool RawTerm.boolTrue))
      (elseTypeClosed :
        IsClosedTy (motiveType.subst0 Ty.bool RawTerm.boolFalse))
      {scrutineeRaw thenRaw elseRaw : RawTerm scope}
      (scrutinee : Term context Ty.bool scrutineeRaw)
      (thenBranch :
        Term context (motiveType.subst0 Ty.bool RawTerm.boolTrue) thenRaw)
      (elseBranch :
        Term context (motiveType.subst0 Ty.bool RawTerm.boolFalse) elseRaw)
      (scrutDispatch : DispatchAtom scrutinee)
      (thenDispatch : DispatchAtom thenBranch)
      (elseDispatch : DispatchAtom elseBranch) :
      DispatchAtom (Term.boolElim (motiveType := motiveType) scrutinee
                                   thenBranch elseBranch
                    : Term context (motiveType.subst0 Ty.bool scrutineeRaw)
                                   (RawTerm.boolElim scrutineeRaw thenRaw
                                                     elseRaw))
  /-- Heterogeneous-carrier equivalence introduction.  Both `forward`
  and `backward` sit at `Ty.arrow` (closed via `IsClosedTy.arrow`), so
  their step targets fix typewise.  The two inverse witnesses (leftInv,
  rightInv) live at types parametric in `forwardRaw`/`backwardRaw`; the
  cong rule preserves the same raw witness while retargeting the type
  index, so the caller supplies retargeting functions for each. -/
  | equivIntroHet {mode : Mode} {level scope : Nat}
      {context : Ctx mode level scope}
      {carrierA carrierB : Ty level scope}
      (carrierAClosed : IsClosedTy carrierA)
      (carrierBClosed : IsClosedTy carrierB)
      {forwardRaw backwardRaw leftInvRaw rightInvRaw : RawTerm scope}
      (forward : Term context (Ty.arrow carrierA carrierB) forwardRaw)
      (backward : Term context (Ty.arrow carrierB carrierA) backwardRaw)
      (leftInv :
        Term context
          (equivIntroHetLeftInverseType carrierA forwardRaw backwardRaw)
          leftInvRaw)
      (rightInv :
        Term context
          (equivIntroHetRightInverseType carrierB forwardRaw backwardRaw)
          rightInvRaw)
      (leftInvRetarget :
        ∀ (forwardTarget backwardTarget : RawTerm scope),
          Term context
            (equivIntroHetLeftInverseType carrierA forwardTarget backwardTarget)
            leftInvRaw)
      (rightInvRetarget :
        ∀ (forwardTarget backwardTarget : RawTerm scope),
          Term context
            (equivIntroHetRightInverseType carrierB forwardTarget backwardTarget)
            rightInvRaw)
      (forwardDispatch : DispatchAtom forward)
      (backwardDispatch : DispatchAtom backward) :
      DispatchAtom (Term.equivIntroHet (context := context) forward backward
                                        leftInv rightInv
                    : Term context (Ty.equiv carrierA carrierB)
                                   (RawTerm.equivIntro forwardRaw backwardRaw))

end LeanFX2
