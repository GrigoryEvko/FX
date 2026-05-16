import LeanFX2.Reduction.ParRed
import LeanFX2.Reduction.RawParInversion
import LeanFX2.Term.Inversion

/-! # LeanFX2.Term.PreservesTerm.EliminatorConstantMotive

Tier 3 eliminator lifts where the motive lives at the eliminators
output scope (NOT scope+1), giving a fixed result type.  Three-arm
raw inversion: cong + iotaCanonical1 + iotaCanonical2.

Covers 5 eliminators: natElim, natRec, listElim, optionMatch,
eitherMatch; plus the binary Tier 2 effectPerform.

## Root status

Zero-axiom; carved from `Term/PreservesTerm.lean`. -/

namespace LeanFX2

variable {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}


/-! ## Tier 3 — eliminators with constant motive

Eliminators where `motiveType : Ty level scope` (NOT scope+1) — the
result type is `motiveType` regardless of the scrutinee's raw form.
Hence the lift can stay at fixed type even when the scrutinee
parallel-reduces.

The raw inversion has THREE arms: cong + iota-canonical (one per
canonical scrutinee form).  We dispatch each arm to the matching typed
Step.par cong / iota rule.  The iota arms use the deep variants
(iota*Deep) which take a `Step.par scrutinee canonicalTerm` premise —
this is exactly what the scrutinee IH produces (after the
`Term.<canonical>_unique` HEq → eq conversion).

For natElim's iotaSucc arm, the raw scrutinee parallel-reduces to
`RawTerm.natSucc predRaw`.  The typed scrutinee IH applied to this
step yields a typed term at `Term ctx Ty.nat (natSucc predRaw)`.
Pattern-matching on this typed term forces it to be of the form
`Term.natSucc predTarget` for some typed predTarget. -/

/-- **Tier 3 — Term.natElim lift.**  Three-arm raw inversion handles
cong + iotaZero + iotaSucc.  motiveType at scope (constant), so
target type is fixed at `motiveType`. -/
theorem RawStep.par.lift_natElim
    {motiveType : Ty level scope}
    {scrutineeRaw zeroRaw succRaw : RawTerm scope}
    (scrutinee : Term context Ty.nat scrutineeRaw)
    (zeroBranch : Term context motiveType zeroRaw)
    (succBranch : Term context (Ty.arrow Ty.nat motiveType) succRaw)
    (scrutLift : ∀ {targetRawIH : RawTerm scope},
      RawStep.par scrutineeRaw targetRawIH →
      ∃ scrutTarget : Term context Ty.nat targetRawIH,
        Step.par scrutinee scrutTarget)
    (zeroLift : ∀ {targetRawIH : RawTerm scope},
      RawStep.par zeroRaw targetRawIH →
      ∃ zeroTarget : Term context motiveType targetRawIH,
        Step.par zeroBranch zeroTarget)
    (succLift : ∀ {targetRawIH : RawTerm scope},
      RawStep.par succRaw targetRawIH →
      ∃ succTarget : Term context (Ty.arrow Ty.nat motiveType) targetRawIH,
        Step.par succBranch succTarget)
    {targetRaw : RawTerm scope}
    (rawStep :
      RawStep.par (RawTerm.natElim scrutineeRaw zeroRaw succRaw) targetRaw) :
    ∃ targetTerm : Term context motiveType targetRaw,
      Step.par (Term.natElim scrutinee zeroBranch succBranch) targetTerm := by
  rcases RawStep.par.natElim_inv rawStep with
    ⟨scrutTargetRaw, zeroTargetRaw, succTargetRaw, eq, scrutStep, zeroStep, succStep⟩
    | ⟨zeroTargetRaw, eq, scrutToZero, zeroStep⟩
    | ⟨predTargetRaw, succTargetRaw, eq, scrutToSucc, succStep⟩
  · -- cong arm
    obtain ⟨scrutTarget, scrutStepTyped⟩ := scrutLift scrutStep
    obtain ⟨zeroTarget, zeroStepTyped⟩ := zeroLift zeroStep
    obtain ⟨succTarget, succStepTyped⟩ := succLift succStep
    cases eq
    exact ⟨Term.natElim scrutTarget zeroTarget succTarget,
           Step.par.natElim scrutStepTyped zeroStepTyped succStepTyped⟩
  · -- iotaZero arm: scrutinee →* natZero, target = zero result
    obtain ⟨scrutTarget, scrutStepTyped⟩ := scrutLift scrutToZero
    obtain ⟨zeroTarget, zeroStepTyped⟩ := zeroLift zeroStep
    -- Use uniqueness to force scrutTarget = Term.natZero (HEq → eq at fixed type)
    have heq :
        HEq scrutTarget (Term.natZero (context := context)) :=
      Term.natZero_unique scrutTarget Term.natZero
    have scrutEq : scrutTarget = (Term.natZero (context := context)) := eq_of_heq heq
    rw [scrutEq] at scrutStepTyped
    cases eq
    exact ⟨zeroTarget,
           Step.par.iotaNatElimZeroDeep succBranch scrutStepTyped zeroStepTyped⟩
  · -- iotaSucc arm: scrutinee →* natSucc predRaw, target = app succ predRaw
    obtain ⟨scrutTarget, scrutStepTyped⟩ := scrutLift scrutToSucc
    obtain ⟨succTarget, succStepTyped⟩ := succLift succStep
    -- scrutTarget : Term ctx Ty.nat (natSucc predTargetRaw) — must be Term.natSucc _
    -- Use the destructor (suffices/free-index pattern) to extract the
    -- predecessor at fixed Ty.nat type.
    obtain ⟨predecessor, predecessorHeq⟩ := Term.natSuccDestruct scrutTarget
    have predecessorEq : scrutTarget = Term.natSucc predecessor :=
      eq_of_heq predecessorHeq
    rw [predecessorEq] at scrutStepTyped
    cases eq
    exact ⟨Term.app succTarget predecessor,
           Step.par.iotaNatElimSuccDeep zeroBranch scrutStepTyped succStepTyped⟩

/-- **Tier 3 — Term.natRec lift.**  Same shape as natElim but with
the recursive succ branch type `Ty.arrow Ty.nat (Ty.arrow motiveType
motiveType)` and the iotaSucc target shape `app (app succ pred)
(natRec pred zero succ)`. -/
theorem RawStep.par.lift_natRec
    {motiveType : Ty level scope}
    {scrutineeRaw zeroRaw succRaw : RawTerm scope}
    (scrutinee : Term context Ty.nat scrutineeRaw)
    (zeroBranch : Term context motiveType zeroRaw)
    (succBranch :
      Term context (Ty.arrow Ty.nat (Ty.arrow motiveType motiveType)) succRaw)
    (scrutLift : ∀ {targetRawIH : RawTerm scope},
      RawStep.par scrutineeRaw targetRawIH →
      ∃ scrutTarget : Term context Ty.nat targetRawIH,
        Step.par scrutinee scrutTarget)
    (zeroLift : ∀ {targetRawIH : RawTerm scope},
      RawStep.par zeroRaw targetRawIH →
      ∃ zeroTarget : Term context motiveType targetRawIH,
        Step.par zeroBranch zeroTarget)
    (succLift : ∀ {targetRawIH : RawTerm scope},
      RawStep.par succRaw targetRawIH →
      ∃ succTarget :
          Term context (Ty.arrow Ty.nat (Ty.arrow motiveType motiveType))
                       targetRawIH,
        Step.par succBranch succTarget)
    {targetRaw : RawTerm scope}
    (rawStep :
      RawStep.par (RawTerm.natRec scrutineeRaw zeroRaw succRaw) targetRaw) :
    ∃ targetTerm : Term context motiveType targetRaw,
      Step.par (Term.natRec scrutinee zeroBranch succBranch) targetTerm := by
  rcases RawStep.par.natRec_inv rawStep with
    ⟨scrutTargetRaw, zeroTargetRaw, succTargetRaw, eq, scrutStep, zeroStep, succStep⟩
    | ⟨zeroTargetRaw, eq, scrutToZero, zeroStep⟩
    | ⟨predRaw, zeroTargetRaw, succTargetRaw, eq, scrutToSucc, zeroStep, succStep⟩
  · obtain ⟨scrutTarget, scrutStepTyped⟩ := scrutLift scrutStep
    obtain ⟨zeroTarget, zeroStepTyped⟩ := zeroLift zeroStep
    obtain ⟨succTarget, succStepTyped⟩ := succLift succStep
    cases eq
    exact ⟨Term.natRec scrutTarget zeroTarget succTarget,
           Step.par.natRec scrutStepTyped zeroStepTyped succStepTyped⟩
  · obtain ⟨scrutTarget, scrutStepTyped⟩ := scrutLift scrutToZero
    obtain ⟨zeroTarget, zeroStepTyped⟩ := zeroLift zeroStep
    have heq :
        HEq scrutTarget (Term.natZero (context := context)) :=
      Term.natZero_unique scrutTarget Term.natZero
    have scrutEq : scrutTarget = (Term.natZero (context := context)) := eq_of_heq heq
    rw [scrutEq] at scrutStepTyped
    cases eq
    exact ⟨zeroTarget,
           Step.par.iotaNatRecZeroDeep succBranch scrutStepTyped zeroStepTyped⟩
  · obtain ⟨scrutTarget, scrutStepTyped⟩ := scrutLift scrutToSucc
    obtain ⟨zeroTarget, zeroStepTyped⟩ := zeroLift zeroStep
    obtain ⟨succTarget, succStepTyped⟩ := succLift succStep
    obtain ⟨predecessor, predecessorHeq⟩ := Term.natSuccDestruct scrutTarget
    have predecessorEq : scrutTarget = Term.natSucc predecessor :=
      eq_of_heq predecessorHeq
    rw [predecessorEq] at scrutStepTyped
    cases eq
    exact ⟨Term.app (Term.app succTarget predecessor)
                    (Term.natRec predecessor zeroTarget succTarget),
           Step.par.iotaNatRecSuccDeep scrutStepTyped zeroStepTyped succStepTyped⟩

/-- **Tier 3 — Term.listElim lift.**  Three-arm raw inversion: cong
+ iotaNil + iotaCons.  motiveType at scope, listType elementType
scrutinee. -/
theorem RawStep.par.lift_listElim
    {elementType motiveType : Ty level scope}
    {scrutineeRaw nilRaw consRaw : RawTerm scope}
    (scrutinee : Term context (Ty.listType elementType) scrutineeRaw)
    (nilBranch : Term context motiveType nilRaw)
    (consBranch :
      Term context
        (Ty.arrow elementType (Ty.arrow (Ty.listType elementType) motiveType))
        consRaw)
    (scrutLift : ∀ {targetRawIH : RawTerm scope},
      RawStep.par scrutineeRaw targetRawIH →
      ∃ scrutTarget : Term context (Ty.listType elementType) targetRawIH,
        Step.par scrutinee scrutTarget)
    (nilLift : ∀ {targetRawIH : RawTerm scope},
      RawStep.par nilRaw targetRawIH →
      ∃ nilTarget : Term context motiveType targetRawIH,
        Step.par nilBranch nilTarget)
    (consLift : ∀ {targetRawIH : RawTerm scope},
      RawStep.par consRaw targetRawIH →
      ∃ consTarget :
          Term context
            (Ty.arrow elementType (Ty.arrow (Ty.listType elementType) motiveType))
            targetRawIH,
        Step.par consBranch consTarget)
    {targetRaw : RawTerm scope}
    (rawStep :
      RawStep.par (RawTerm.listElim scrutineeRaw nilRaw consRaw) targetRaw) :
    ∃ targetTerm : Term context motiveType targetRaw,
      Step.par (Term.listElim scrutinee nilBranch consBranch) targetTerm := by
  rcases RawStep.par.listElim_inv rawStep with
    ⟨scrutTargetRaw, nilTargetRaw, consTargetRaw, eq, scrutStep, nilStep, consStep⟩
    | ⟨nilTargetRaw, eq, scrutToNil, nilStep⟩
    | ⟨headRaw, tailRaw, consTargetRaw, eq, scrutToCons, consStep⟩
  · obtain ⟨scrutTarget, scrutStepTyped⟩ := scrutLift scrutStep
    obtain ⟨nilTarget, nilStepTyped⟩ := nilLift nilStep
    obtain ⟨consTarget, consStepTyped⟩ := consLift consStep
    cases eq
    exact ⟨Term.listElim scrutTarget nilTarget consTarget,
           Step.par.listElim scrutStepTyped nilStepTyped consStepTyped⟩
  · obtain ⟨scrutTarget, scrutStepTyped⟩ := scrutLift scrutToNil
    obtain ⟨nilTarget, nilStepTyped⟩ := nilLift nilStep
    -- scrutTarget : Term ctx (listType elementType) listNil — must be Term.listNil.
    -- Use suffices/free-index destructor to bypass dep-elim on var arm.
    have scrutEq :
        scrutTarget = (Term.listNil (context := context) (elementType := elementType)) := by
      suffices key :
          ∀ {someType : Ty level scope}
            (genericTerm : Term context someType (RawTerm.listNil (scope := scope))),
            someType = Ty.listType elementType →
            HEq genericTerm
                (Term.listNil (context := context) (elementType := elementType)) by
        exact eq_of_heq (key scrutTarget rfl)
      intro someType genericTerm someTypeIsListType
      cases genericTerm
      rename_i innerElement
      have elementEq : innerElement = elementType :=
        Ty.listType.inj someTypeIsListType
      cases elementEq
      exact HEq.rfl
    rw [scrutEq] at scrutStepTyped
    cases eq
    exact ⟨nilTarget,
           Step.par.iotaListElimNilDeep consBranch scrutStepTyped nilStepTyped⟩
  · obtain ⟨scrutTarget, scrutStepTyped⟩ := scrutLift scrutToCons
    obtain ⟨consTarget, consStepTyped⟩ := consLift consStep
    obtain ⟨headTerm, tailTerm, headHeq⟩ := Term.listConsDestruct scrutTarget
    have headEq : scrutTarget = Term.listCons headTerm tailTerm :=
      eq_of_heq headHeq
    rw [headEq] at scrutStepTyped
    cases eq
    exact ⟨Term.app (Term.app consTarget headTerm) tailTerm,
           Step.par.iotaListElimConsDeep nilBranch scrutStepTyped consStepTyped⟩

/-- **Tier 3 — Term.optionMatch lift.** -/
theorem RawStep.par.lift_optionMatch
    {elementType motiveType : Ty level scope}
    {scrutineeRaw noneRaw someRaw : RawTerm scope}
    (scrutinee : Term context (Ty.optionType elementType) scrutineeRaw)
    (noneBranch : Term context motiveType noneRaw)
    (someBranch : Term context (Ty.arrow elementType motiveType) someRaw)
    (scrutLift : ∀ {targetRawIH : RawTerm scope},
      RawStep.par scrutineeRaw targetRawIH →
      ∃ scrutTarget : Term context (Ty.optionType elementType) targetRawIH,
        Step.par scrutinee scrutTarget)
    (noneLift : ∀ {targetRawIH : RawTerm scope},
      RawStep.par noneRaw targetRawIH →
      ∃ noneTarget : Term context motiveType targetRawIH,
        Step.par noneBranch noneTarget)
    (someLift : ∀ {targetRawIH : RawTerm scope},
      RawStep.par someRaw targetRawIH →
      ∃ someTarget :
          Term context (Ty.arrow elementType motiveType) targetRawIH,
        Step.par someBranch someTarget)
    {targetRaw : RawTerm scope}
    (rawStep :
      RawStep.par
        (RawTerm.optionMatch scrutineeRaw noneRaw someRaw) targetRaw) :
    ∃ targetTerm : Term context motiveType targetRaw,
      Step.par (Term.optionMatch scrutinee noneBranch someBranch) targetTerm := by
  rcases RawStep.par.optionMatch_inv rawStep with
    ⟨scrutTargetRaw, noneTargetRaw, someTargetRaw, eq, scrutStep, noneStep, someStep⟩
    | ⟨noneTargetRaw, eq, scrutToNone, noneStep⟩
    | ⟨valueRaw, someTargetRaw, eq, scrutToSome, someStep⟩
  · obtain ⟨scrutTarget, scrutStepTyped⟩ := scrutLift scrutStep
    obtain ⟨noneTarget, noneStepTyped⟩ := noneLift noneStep
    obtain ⟨someTarget, someStepTyped⟩ := someLift someStep
    cases eq
    exact ⟨Term.optionMatch scrutTarget noneTarget someTarget,
           Step.par.optionMatch scrutStepTyped noneStepTyped someStepTyped⟩
  · obtain ⟨scrutTarget, scrutStepTyped⟩ := scrutLift scrutToNone
    obtain ⟨noneTarget, noneStepTyped⟩ := noneLift noneStep
    -- scrutTarget : Term ctx (optionType elementType) optionNone
    have scrutEq :
        scrutTarget = (Term.optionNone (context := context)
                                       (elementType := elementType)) := by
      suffices key :
          ∀ {someType : Ty level scope}
            (genericTerm : Term context someType (RawTerm.optionNone (scope := scope))),
            someType = Ty.optionType elementType →
            HEq genericTerm
                (Term.optionNone (context := context) (elementType := elementType)) by
        exact eq_of_heq (key scrutTarget rfl)
      intro someType genericTerm someTypeIsOptionType
      cases genericTerm
      rename_i innerElement
      have elementEq : innerElement = elementType :=
        Ty.optionType.inj someTypeIsOptionType
      cases elementEq
      exact HEq.rfl
    rw [scrutEq] at scrutStepTyped
    cases eq
    exact ⟨noneTarget,
           Step.par.iotaOptionMatchNoneDeep someBranch scrutStepTyped noneStepTyped⟩
  · obtain ⟨scrutTarget, scrutStepTyped⟩ := scrutLift scrutToSome
    obtain ⟨someTarget, someStepTyped⟩ := someLift someStep
    obtain ⟨valueTerm, valueHeq⟩ := Term.optionSomeDestruct scrutTarget
    have valueEq : scrutTarget = Term.optionSome valueTerm := eq_of_heq valueHeq
    rw [valueEq] at scrutStepTyped
    cases eq
    exact ⟨Term.app someTarget valueTerm,
           Step.par.iotaOptionMatchSomeDeep noneBranch scrutStepTyped someStepTyped⟩

/-- **Tier 3 — Term.eitherMatch lift.** -/
theorem RawStep.par.lift_eitherMatch
    {leftType rightType motiveType : Ty level scope}
    {scrutineeRaw leftRaw rightRaw : RawTerm scope}
    (scrutinee : Term context (Ty.eitherType leftType rightType) scrutineeRaw)
    (leftBranch : Term context (Ty.arrow leftType motiveType) leftRaw)
    (rightBranch : Term context (Ty.arrow rightType motiveType) rightRaw)
    (scrutLift : ∀ {targetRawIH : RawTerm scope},
      RawStep.par scrutineeRaw targetRawIH →
      ∃ scrutTarget :
          Term context (Ty.eitherType leftType rightType) targetRawIH,
        Step.par scrutinee scrutTarget)
    (leftLift : ∀ {targetRawIH : RawTerm scope},
      RawStep.par leftRaw targetRawIH →
      ∃ leftTarget :
          Term context (Ty.arrow leftType motiveType) targetRawIH,
        Step.par leftBranch leftTarget)
    (rightLift : ∀ {targetRawIH : RawTerm scope},
      RawStep.par rightRaw targetRawIH →
      ∃ rightTarget :
          Term context (Ty.arrow rightType motiveType) targetRawIH,
        Step.par rightBranch rightTarget)
    {targetRaw : RawTerm scope}
    (rawStep :
      RawStep.par
        (RawTerm.eitherMatch scrutineeRaw leftRaw rightRaw) targetRaw) :
    ∃ targetTerm : Term context motiveType targetRaw,
      Step.par (Term.eitherMatch scrutinee leftBranch rightBranch) targetTerm := by
  rcases RawStep.par.eitherMatch_inv rawStep with
    ⟨scrutTargetRaw, leftTargetRaw, rightTargetRaw, eq, scrutStep, leftStep, rightStep⟩
    | ⟨valueRaw, leftTargetRaw, eq, scrutToInl, leftStep⟩
    | ⟨valueRaw, rightTargetRaw, eq, scrutToInr, rightStep⟩
  · obtain ⟨scrutTarget, scrutStepTyped⟩ := scrutLift scrutStep
    obtain ⟨leftTarget, leftStepTyped⟩ := leftLift leftStep
    obtain ⟨rightTarget, rightStepTyped⟩ := rightLift rightStep
    cases eq
    exact ⟨Term.eitherMatch scrutTarget leftTarget rightTarget,
           Step.par.eitherMatch scrutStepTyped leftStepTyped rightStepTyped⟩
  · obtain ⟨scrutTarget, scrutStepTyped⟩ := scrutLift scrutToInl
    obtain ⟨leftTarget, leftStepTyped⟩ := leftLift leftStep
    obtain ⟨valueTerm, valueHeq⟩ := Term.eitherInlDestruct scrutTarget
    have valueEq :
        scrutTarget = (Term.eitherInl (rightType := rightType) valueTerm) :=
      eq_of_heq valueHeq
    rw [valueEq] at scrutStepTyped
    cases eq
    exact ⟨Term.app leftTarget valueTerm,
           Step.par.iotaEitherMatchInlDeep rightBranch scrutStepTyped leftStepTyped⟩
  · obtain ⟨scrutTarget, scrutStepTyped⟩ := scrutLift scrutToInr
    obtain ⟨rightTarget, rightStepTyped⟩ := rightLift rightStep
    obtain ⟨valueTerm, valueHeq⟩ := Term.eitherInrDestruct scrutTarget
    have valueEq :
        scrutTarget = (Term.eitherInr (leftType := leftType) valueTerm) :=
      eq_of_heq valueHeq
    rw [valueEq] at scrutStepTyped
    cases eq
    exact ⟨Term.app rightTarget valueTerm,
           Step.par.iotaEitherMatchInrDeep leftBranch scrutStepTyped rightStepTyped⟩

/-- **Tier 2 — Term.effectPerform lift.**  Two children: operationTag
(Ty.effect argumentCarrier effectTag) and arguments (argumentCarrier).  -/
theorem RawStep.par.lift_effectPerform
    (effectTag : RawTerm scope)
    (effectRow : Effects.EffectRow)
    (operationSignature : Effects.OperationSignature (Ty level scope))
    (canPerformOperation :
      Effects.CanPerform effectRow operationSignature)
    {operationRaw argumentsRaw : RawTerm scope}
    (operationTag :
      Term context (Ty.effect operationSignature.argumentCarrier effectTag)
                   operationRaw)
    (arguments :
      Term context operationSignature.argumentCarrier argumentsRaw)
    (operationLift : ∀ {targetRawIH : RawTerm scope},
      RawStep.par operationRaw targetRawIH →
      ∃ operationTarget :
          Term context (Ty.effect operationSignature.argumentCarrier effectTag)
                       targetRawIH,
        Step.par operationTag operationTarget)
    (argumentsLift : ∀ {targetRawIH : RawTerm scope},
      RawStep.par argumentsRaw targetRawIH →
      ∃ argumentsTarget :
          Term context operationSignature.argumentCarrier targetRawIH,
        Step.par arguments argumentsTarget)
    {targetRaw : RawTerm scope}
    (rawStep :
      RawStep.par (RawTerm.effectPerform operationRaw argumentsRaw) targetRaw) :
    ∃ targetTerm :
        Term context (Ty.effect operationSignature.resultCarrier effectTag)
                     targetRaw,
      Step.par
        (Term.effectPerform effectTag effectRow operationSignature
          canPerformOperation operationTag arguments)
        targetTerm := by
  obtain ⟨operationTargetRaw, argumentsTargetRaw, eq, operationStep, argumentsStep⟩ :=
    RawStep.par.effectPerform_inv rawStep
  obtain ⟨operationTarget, operationStepTyped⟩ := operationLift operationStep
  obtain ⟨argumentsTarget, argumentsStepTyped⟩ := argumentsLift argumentsStep
  cases eq
  exact ⟨Term.effectPerform effectTag effectRow operationSignature
                            canPerformOperation operationTarget argumentsTarget,
         Step.par.effectPerformCong operationStepTyped argumentsStepTyped⟩

/-! ## CONVTRANS-B.2b — closed-type cong-only eliminator lifts

Cong-only lift variants for the six closed-type eliminators (boolElim,
natElim, natRec, listElim, optionMatch, eitherMatch).  Each takes raw
parallel-reduction steps on the scrutinee + branches plus per-subterm
typed-lift callbacks, and assembles the typed `Step.par.<elim>` cong
witness directly — bypassing the three-arm raw inversion that the
full lifts above need to dispatch the ι-canonical arms.

Five of the six (natElim, natRec, listElim, optionMatch, eitherMatch)
have a constant motive at `Ty level scope` — output type is
`motiveType` independent of the scrutinee raw.  The boolElim cong
lift's output type is `motiveType.subst0 Ty.bool scrutineeTargetRaw`
because boolElim's motive lives at `scope + 1`; the dependent
substitution rides along on the scrutinee target raw produced by the
cong arm.

These are the structural building block for CONVTRANS-B.2b (#1723)
and feed CONVTRANS-C/D headlines that chain raw-typed lifts through
`RawStep.parStar` and ultimately `Conv.trans`. -/

/-- **CONVTRANS-B.2b — Term.boolElim lift, cong arm only.**  Motive
lives at `scope + 1`; output type rides on `scrutineeTargetRaw` via
`motiveType.subst0 Ty.bool _`.  The β-arms (iotaBoolElimTrueDeep /
iotaBoolElimFalseDeep) live in the full `lift_boolElim` variant. -/
theorem RawStep.par.lift_boolElim_cong
    {motiveType : Ty level (scope + 1)}
    {scrutineeRaw thenRaw elseRaw : RawTerm scope}
    (scrutinee : Term context Ty.bool scrutineeRaw)
    (thenBranch :
      Term context (motiveType.subst0 Ty.bool RawTerm.boolTrue) thenRaw)
    (elseBranch :
      Term context (motiveType.subst0 Ty.bool RawTerm.boolFalse) elseRaw)
    (scrutLift : ∀ {targetRawIH : RawTerm scope},
      RawStep.par scrutineeRaw targetRawIH →
      ∃ scrutTarget : Term context Ty.bool targetRawIH,
        Step.par scrutinee scrutTarget)
    (thenLift : ∀ {targetRawIH : RawTerm scope},
      RawStep.par thenRaw targetRawIH →
      ∃ thenTarget :
          Term context (motiveType.subst0 Ty.bool RawTerm.boolTrue) targetRawIH,
        Step.par thenBranch thenTarget)
    (elseLift : ∀ {targetRawIH : RawTerm scope},
      RawStep.par elseRaw targetRawIH →
      ∃ elseTarget :
          Term context (motiveType.subst0 Ty.bool RawTerm.boolFalse) targetRawIH,
        Step.par elseBranch elseTarget)
    {scrutTargetRaw thenTargetRaw elseTargetRaw : RawTerm scope}
    (scrutStep : RawStep.par scrutineeRaw scrutTargetRaw)
    (thenStep : RawStep.par thenRaw thenTargetRaw)
    (elseStep : RawStep.par elseRaw elseTargetRaw) :
    ∃ targetTerm :
        Term context (motiveType.subst0 Ty.bool scrutTargetRaw)
                     (RawTerm.boolElim scrutTargetRaw thenTargetRaw elseTargetRaw),
      Step.par (Term.boolElim (motiveType := motiveType) scrutinee thenBranch elseBranch)
               targetTerm := by
  obtain ⟨scrutTarget, scrutStepTyped⟩ := scrutLift scrutStep
  obtain ⟨thenTarget, thenStepTyped⟩ := thenLift thenStep
  obtain ⟨elseTarget, elseStepTyped⟩ := elseLift elseStep
  exact ⟨Term.boolElim (motiveType := motiveType) scrutTarget thenTarget elseTarget,
         Step.par.boolElim scrutStepTyped thenStepTyped elseStepTyped⟩

/-- **CONVTRANS-B.2b — Term.natElim lift, cong arm only.**  Constant
motive at `Ty level scope`; output type fixed at `motiveType`.  The
ι-arms (iotaNatElimZeroDeep / iotaNatElimSuccDeep) live in the full
`lift_natElim` variant above. -/
theorem RawStep.par.lift_natElim_cong
    {motiveType : Ty level scope}
    {scrutineeRaw zeroRaw succRaw : RawTerm scope}
    (scrutinee : Term context Ty.nat scrutineeRaw)
    (zeroBranch : Term context motiveType zeroRaw)
    (succBranch : Term context (Ty.arrow Ty.nat motiveType) succRaw)
    (scrutLift : ∀ {targetRawIH : RawTerm scope},
      RawStep.par scrutineeRaw targetRawIH →
      ∃ scrutTarget : Term context Ty.nat targetRawIH,
        Step.par scrutinee scrutTarget)
    (zeroLift : ∀ {targetRawIH : RawTerm scope},
      RawStep.par zeroRaw targetRawIH →
      ∃ zeroTarget : Term context motiveType targetRawIH,
        Step.par zeroBranch zeroTarget)
    (succLift : ∀ {targetRawIH : RawTerm scope},
      RawStep.par succRaw targetRawIH →
      ∃ succTarget : Term context (Ty.arrow Ty.nat motiveType) targetRawIH,
        Step.par succBranch succTarget)
    {scrutTargetRaw zeroTargetRaw succTargetRaw : RawTerm scope}
    (scrutStep : RawStep.par scrutineeRaw scrutTargetRaw)
    (zeroStep : RawStep.par zeroRaw zeroTargetRaw)
    (succStep : RawStep.par succRaw succTargetRaw) :
    ∃ targetTerm :
        Term context motiveType
                     (RawTerm.natElim scrutTargetRaw zeroTargetRaw succTargetRaw),
      Step.par (Term.natElim scrutinee zeroBranch succBranch) targetTerm := by
  obtain ⟨scrutTarget, scrutStepTyped⟩ := scrutLift scrutStep
  obtain ⟨zeroTarget, zeroStepTyped⟩ := zeroLift zeroStep
  obtain ⟨succTarget, succStepTyped⟩ := succLift succStep
  exact ⟨Term.natElim scrutTarget zeroTarget succTarget,
         Step.par.natElim scrutStepTyped zeroStepTyped succStepTyped⟩

/-- **CONVTRANS-B.2b — Term.natRec lift, cong arm only.**  Same
constant-motive shape as natElim_cong; succ branch type uses the
recursive arrow `Ty.arrow Ty.nat (Ty.arrow motiveType motiveType)`. -/
theorem RawStep.par.lift_natRec_cong
    {motiveType : Ty level scope}
    {scrutineeRaw zeroRaw succRaw : RawTerm scope}
    (scrutinee : Term context Ty.nat scrutineeRaw)
    (zeroBranch : Term context motiveType zeroRaw)
    (succBranch :
      Term context (Ty.arrow Ty.nat (Ty.arrow motiveType motiveType)) succRaw)
    (scrutLift : ∀ {targetRawIH : RawTerm scope},
      RawStep.par scrutineeRaw targetRawIH →
      ∃ scrutTarget : Term context Ty.nat targetRawIH,
        Step.par scrutinee scrutTarget)
    (zeroLift : ∀ {targetRawIH : RawTerm scope},
      RawStep.par zeroRaw targetRawIH →
      ∃ zeroTarget : Term context motiveType targetRawIH,
        Step.par zeroBranch zeroTarget)
    (succLift : ∀ {targetRawIH : RawTerm scope},
      RawStep.par succRaw targetRawIH →
      ∃ succTarget :
          Term context (Ty.arrow Ty.nat (Ty.arrow motiveType motiveType))
                       targetRawIH,
        Step.par succBranch succTarget)
    {scrutTargetRaw zeroTargetRaw succTargetRaw : RawTerm scope}
    (scrutStep : RawStep.par scrutineeRaw scrutTargetRaw)
    (zeroStep : RawStep.par zeroRaw zeroTargetRaw)
    (succStep : RawStep.par succRaw succTargetRaw) :
    ∃ targetTerm :
        Term context motiveType
                     (RawTerm.natRec scrutTargetRaw zeroTargetRaw succTargetRaw),
      Step.par (Term.natRec scrutinee zeroBranch succBranch) targetTerm := by
  obtain ⟨scrutTarget, scrutStepTyped⟩ := scrutLift scrutStep
  obtain ⟨zeroTarget, zeroStepTyped⟩ := zeroLift zeroStep
  obtain ⟨succTarget, succStepTyped⟩ := succLift succStep
  exact ⟨Term.natRec scrutTarget zeroTarget succTarget,
         Step.par.natRec scrutStepTyped zeroStepTyped succStepTyped⟩

/-- **CONVTRANS-B.2b — Term.listElim lift, cong arm only.**  Constant
motive; scrutinee at `Ty.listType elementType`; cons branch type uses
the binary arrow `Ty.arrow elementType (Ty.arrow (Ty.listType elementType)
motiveType)`. -/
theorem RawStep.par.lift_listElim_cong
    {elementType motiveType : Ty level scope}
    {scrutineeRaw nilRaw consRaw : RawTerm scope}
    (scrutinee : Term context (Ty.listType elementType) scrutineeRaw)
    (nilBranch : Term context motiveType nilRaw)
    (consBranch :
      Term context
        (Ty.arrow elementType (Ty.arrow (Ty.listType elementType) motiveType))
        consRaw)
    (scrutLift : ∀ {targetRawIH : RawTerm scope},
      RawStep.par scrutineeRaw targetRawIH →
      ∃ scrutTarget : Term context (Ty.listType elementType) targetRawIH,
        Step.par scrutinee scrutTarget)
    (nilLift : ∀ {targetRawIH : RawTerm scope},
      RawStep.par nilRaw targetRawIH →
      ∃ nilTarget : Term context motiveType targetRawIH,
        Step.par nilBranch nilTarget)
    (consLift : ∀ {targetRawIH : RawTerm scope},
      RawStep.par consRaw targetRawIH →
      ∃ consTarget :
          Term context
            (Ty.arrow elementType (Ty.arrow (Ty.listType elementType) motiveType))
            targetRawIH,
        Step.par consBranch consTarget)
    {scrutTargetRaw nilTargetRaw consTargetRaw : RawTerm scope}
    (scrutStep : RawStep.par scrutineeRaw scrutTargetRaw)
    (nilStep : RawStep.par nilRaw nilTargetRaw)
    (consStep : RawStep.par consRaw consTargetRaw) :
    ∃ targetTerm :
        Term context motiveType
                     (RawTerm.listElim scrutTargetRaw nilTargetRaw consTargetRaw),
      Step.par (Term.listElim scrutinee nilBranch consBranch) targetTerm := by
  obtain ⟨scrutTarget, scrutStepTyped⟩ := scrutLift scrutStep
  obtain ⟨nilTarget, nilStepTyped⟩ := nilLift nilStep
  obtain ⟨consTarget, consStepTyped⟩ := consLift consStep
  exact ⟨Term.listElim scrutTarget nilTarget consTarget,
         Step.par.listElim scrutStepTyped nilStepTyped consStepTyped⟩

/-- **CONVTRANS-B.2b — Term.optionMatch lift, cong arm only.**
Constant motive; scrutinee at `Ty.optionType elementType`; some branch
type `Ty.arrow elementType motiveType`. -/
theorem RawStep.par.lift_optionMatch_cong
    {elementType motiveType : Ty level scope}
    {scrutineeRaw noneRaw someRaw : RawTerm scope}
    (scrutinee : Term context (Ty.optionType elementType) scrutineeRaw)
    (noneBranch : Term context motiveType noneRaw)
    (someBranch : Term context (Ty.arrow elementType motiveType) someRaw)
    (scrutLift : ∀ {targetRawIH : RawTerm scope},
      RawStep.par scrutineeRaw targetRawIH →
      ∃ scrutTarget : Term context (Ty.optionType elementType) targetRawIH,
        Step.par scrutinee scrutTarget)
    (noneLift : ∀ {targetRawIH : RawTerm scope},
      RawStep.par noneRaw targetRawIH →
      ∃ noneTarget : Term context motiveType targetRawIH,
        Step.par noneBranch noneTarget)
    (someLift : ∀ {targetRawIH : RawTerm scope},
      RawStep.par someRaw targetRawIH →
      ∃ someTarget :
          Term context (Ty.arrow elementType motiveType) targetRawIH,
        Step.par someBranch someTarget)
    {scrutTargetRaw noneTargetRaw someTargetRaw : RawTerm scope}
    (scrutStep : RawStep.par scrutineeRaw scrutTargetRaw)
    (noneStep : RawStep.par noneRaw noneTargetRaw)
    (someStep : RawStep.par someRaw someTargetRaw) :
    ∃ targetTerm :
        Term context motiveType
                     (RawTerm.optionMatch scrutTargetRaw noneTargetRaw
                                          someTargetRaw),
      Step.par (Term.optionMatch scrutinee noneBranch someBranch) targetTerm := by
  obtain ⟨scrutTarget, scrutStepTyped⟩ := scrutLift scrutStep
  obtain ⟨noneTarget, noneStepTyped⟩ := noneLift noneStep
  obtain ⟨someTarget, someStepTyped⟩ := someLift someStep
  exact ⟨Term.optionMatch scrutTarget noneTarget someTarget,
         Step.par.optionMatch scrutStepTyped noneStepTyped someStepTyped⟩

/-- **CONVTRANS-B.2b — Term.eitherMatch lift, cong arm only.**
Constant motive; scrutinee at `Ty.eitherType leftType rightType`;
both branches at `Ty.arrow <side>Type motiveType`. -/
theorem RawStep.par.lift_eitherMatch_cong
    {leftType rightType motiveType : Ty level scope}
    {scrutineeRaw leftRaw rightRaw : RawTerm scope}
    (scrutinee : Term context (Ty.eitherType leftType rightType) scrutineeRaw)
    (leftBranch : Term context (Ty.arrow leftType motiveType) leftRaw)
    (rightBranch : Term context (Ty.arrow rightType motiveType) rightRaw)
    (scrutLift : ∀ {targetRawIH : RawTerm scope},
      RawStep.par scrutineeRaw targetRawIH →
      ∃ scrutTarget :
          Term context (Ty.eitherType leftType rightType) targetRawIH,
        Step.par scrutinee scrutTarget)
    (leftLift : ∀ {targetRawIH : RawTerm scope},
      RawStep.par leftRaw targetRawIH →
      ∃ leftTarget :
          Term context (Ty.arrow leftType motiveType) targetRawIH,
        Step.par leftBranch leftTarget)
    (rightLift : ∀ {targetRawIH : RawTerm scope},
      RawStep.par rightRaw targetRawIH →
      ∃ rightTarget :
          Term context (Ty.arrow rightType motiveType) targetRawIH,
        Step.par rightBranch rightTarget)
    {scrutTargetRaw leftTargetRaw rightTargetRaw : RawTerm scope}
    (scrutStep : RawStep.par scrutineeRaw scrutTargetRaw)
    (leftStep : RawStep.par leftRaw leftTargetRaw)
    (rightStep : RawStep.par rightRaw rightTargetRaw) :
    ∃ targetTerm :
        Term context motiveType
                     (RawTerm.eitherMatch scrutTargetRaw leftTargetRaw
                                          rightTargetRaw),
      Step.par (Term.eitherMatch scrutinee leftBranch rightBranch) targetTerm := by
  obtain ⟨scrutTarget, scrutStepTyped⟩ := scrutLift scrutStep
  obtain ⟨leftTarget, leftStepTyped⟩ := leftLift leftStep
  obtain ⟨rightTarget, rightStepTyped⟩ := rightLift rightStep
  exact ⟨Term.eitherMatch scrutTarget leftTarget rightTarget,
         Step.par.eitherMatch scrutStepTyped leftStepTyped rightStepTyped⟩

end LeanFX2
