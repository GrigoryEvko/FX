import LeanFX2.Term.StrengtheningImage.Core
import LeanFX2.Term.StrengtheningImage.EliminatorsAndModal
import LeanFX2.Term.StrengtheningImage.CollectionsSigmaInterval


/-! # Term/StrengtheningImage/DispatcherBasicCollections

Dispatcher-arm soundness for basic unary, modal, interval, list, and either constructors.
-/

namespace LeanFX2

namespace Term

/-! ## Dispatcher-level soundness — leaf prologue.

The `partialStrengthenTyped?` top-level dispatcher (78 arms) takes any
typed term to an optional `StrengtheningResult`.  Wrapper-level
soundness already certifies each successful arm: every leaf and every
recursive wrapper has a `_sound` theorem promoting its
`StrengtheningResult` into a `StrengtheningSoundness` certificate.

This prologue lifts the wrapper certificates to the dispatcher for the
closed-leaf cases (var, unit, boolean/nat zero literals, interval
endpoints).  Each such theorem inverts the dispatcher's arm by
unfolding the auxiliary `match` plus, for `var`, the option-cases on
`strengthening.back`, then immediately applies the matching wrapper
soundness.

Cumulatively, these lemmas plus the wrapper soundness theorems form
the foundation for the headline image theorem trio (right-inverse,
totality, iff): once every dispatcher arm is lifted, the trio becomes
a uniform consequence of structural recursion on `Term`.  This commit
ships the cheap, no-subterm-recursion fragment so the recursive arms
can build on a known-good prologue. -/

/-- Dispatcher soundness at the `Term.var` arm.  After refactoring the
dispatcher's var body to term-mode `match h :`, the standard `split`
machinery penetrates the resulting `Option` match and exposes a clean
witness `survives : strengthening.back sourcePosition = some targetPosition`
that feeds the wrapper soundness directly. -/
theorem partialStrengthenTyped?_atVar_imp_sound {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    (sourcePosition : Fin sourceScope)
    (strengthening : ContextStrengthening sourceCtx targetCtx)
    (result : StrengtheningResult strengthening
      (Term.var (context := sourceCtx) sourcePosition))
    (success : partialStrengthenTyped?
        (Term.var (context := sourceCtx) sourcePosition) strengthening =
          some result) :
    StrengtheningSoundness result := by
  unfold partialStrengthenTyped? at success
  split at success
  · cases success
  · rename_i targetPosition survives
    cases success
    exact partialStrengthenTypedVarOfSurvives_sound strengthening sourcePosition
      targetPosition survives

/-- Dispatcher soundness at the `Term.natSucc` arm.  First arm with a
recursive `partialStrengthenTyped?` sub-call: the inductive hypothesis
on the predecessor flows through as an explicit `predecessorIH`
parameter, which `split at success` plus `cases success` reduces to
exactly the wrapper soundness premise.  Same term-mode `match h :`
refactor as `atVar`: standard equation lemmas, no Option.casesOn
motive trap. -/
theorem partialStrengthenTyped?_atNatSucc_imp_sound {mode : Mode}
    {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {predecessorRaw : RawTerm sourceScope}
    {predecessor : Term sourceCtx Ty.nat predecessorRaw}
    (strengthening : ContextStrengthening sourceCtx targetCtx)
    (predecessorIH : ∀ predecessorResult,
        partialStrengthenTyped? predecessor strengthening =
            some predecessorResult →
          StrengtheningSoundness predecessorResult)
    (result : StrengtheningResult strengthening
      (Term.natSucc (predecessor := predecessor)))
    (success : partialStrengthenTyped?
        (Term.natSucc (predecessor := predecessor)) strengthening =
          some result) :
    StrengtheningSoundness result := by
  unfold partialStrengthenTyped? at success
  split at success
  · cases success
  · rename_i predecessorResult predecessorRecurse
    cases success
    exact partialStrengthenTypedNatSucc_sound
      (predecessorSound := predecessorIH predecessorResult predecessorRecurse)

/-- Dispatcher soundness at the `Term.optionSome` arm.  Single-recurse
arm with no type-shape strengthening: identical proof shape to
`atNatSucc`. -/
theorem partialStrengthenTyped?_atOptionSome_imp_sound {mode : Mode}
    {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {elementType : Ty level sourceScope}
    {valueRaw : RawTerm sourceScope}
    {valueTerm : Term sourceCtx elementType valueRaw}
    (strengthening : ContextStrengthening sourceCtx targetCtx)
    (valueIH : ∀ valueResult,
        partialStrengthenTyped? valueTerm strengthening =
            some valueResult →
          StrengtheningSoundness valueResult)
    (result : StrengtheningResult strengthening
      (Term.optionSome (valueTerm := valueTerm)))
    (success : partialStrengthenTyped?
        (Term.optionSome (valueTerm := valueTerm)) strengthening =
          some result) :
    StrengtheningSoundness result := by
  unfold partialStrengthenTyped? at success
  split at success
  · cases success
  · rename_i valueResult valueRecurse
    cases success
    exact partialStrengthenTypedOptionSome_sound
      (valueSound := valueIH valueResult valueRecurse)

/-- Dispatcher soundness at the `Term.modIntro` arm. -/
theorem partialStrengthenTyped?_atModIntro_imp_sound {mode : Mode}
    {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {innerType : Ty level sourceScope}
    {innerRaw : RawTerm sourceScope}
    {innerTerm : Term sourceCtx innerType innerRaw}
    (strengthening : ContextStrengthening sourceCtx targetCtx)
    (innerIH : ∀ innerResult,
        partialStrengthenTyped? innerTerm strengthening =
            some innerResult →
          StrengtheningSoundness innerResult)
    (result : StrengtheningResult strengthening
      (Term.modIntro (innerTerm := innerTerm)))
    (success : partialStrengthenTyped?
        (Term.modIntro (innerTerm := innerTerm)) strengthening =
          some result) :
    StrengtheningSoundness result := by
  unfold partialStrengthenTyped? at success
  split at success
  · cases success
  · rename_i innerResult innerRecurse
    cases success
    exact partialStrengthenTypedModIntro_sound
      (innerSound := innerIH innerResult innerRecurse)

/-- Dispatcher soundness at the `Term.modElim` arm. -/
theorem partialStrengthenTyped?_atModElim_imp_sound {mode : Mode}
    {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {innerType : Ty level sourceScope}
    {innerRaw : RawTerm sourceScope}
    {innerTerm : Term sourceCtx innerType innerRaw}
    (strengthening : ContextStrengthening sourceCtx targetCtx)
    (innerIH : ∀ innerResult,
        partialStrengthenTyped? innerTerm strengthening =
            some innerResult →
          StrengtheningSoundness innerResult)
    (result : StrengtheningResult strengthening
      (Term.modElim (innerTerm := innerTerm)))
    (success : partialStrengthenTyped?
        (Term.modElim (innerTerm := innerTerm)) strengthening =
          some result) :
    StrengtheningSoundness result := by
  unfold partialStrengthenTyped? at success
  split at success
  · cases success
  · rename_i innerResult innerRecurse
    cases success
    exact partialStrengthenTypedModElim_sound
      (innerSound := innerIH innerResult innerRecurse)

/-- Dispatcher soundness at the `Term.subsume` arm. -/
theorem partialStrengthenTyped?_atSubsume_imp_sound {mode : Mode}
    {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {innerType : Ty level sourceScope}
    {innerRaw : RawTerm sourceScope}
    {innerTerm : Term sourceCtx innerType innerRaw}
    (strengthening : ContextStrengthening sourceCtx targetCtx)
    (innerIH : ∀ innerResult,
        partialStrengthenTyped? innerTerm strengthening =
            some innerResult →
          StrengtheningSoundness innerResult)
    (result : StrengtheningResult strengthening
      (Term.subsume (innerTerm := innerTerm)))
    (success : partialStrengthenTyped?
        (Term.subsume (innerTerm := innerTerm)) strengthening =
          some result) :
    StrengtheningSoundness result := by
  unfold partialStrengthenTyped? at success
  split at success
  · cases success
  · rename_i innerResult innerRecurse
    cases success
    exact partialStrengthenTypedSubsume_sound
      (innerSound := innerIH innerResult innerRecurse)

/-- Dispatcher soundness at the `Term.intervalOpp` arm. -/
theorem partialStrengthenTyped?_atIntervalOpp_imp_sound {mode : Mode}
    {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {innerRaw : RawTerm sourceScope}
    {innerValue : Term sourceCtx Ty.interval innerRaw}
    (strengthening : ContextStrengthening sourceCtx targetCtx)
    (innerIH : ∀ innerResult,
        partialStrengthenTyped? innerValue strengthening =
            some innerResult →
          StrengtheningSoundness innerResult)
    (result : StrengtheningResult strengthening
      (Term.intervalOpp (innerValue := innerValue)))
    (success : partialStrengthenTyped?
        (Term.intervalOpp (innerValue := innerValue)) strengthening =
          some result) :
    StrengtheningSoundness result := by
  unfold partialStrengthenTyped? at success
  split at success
  · cases success
  · rename_i innerResult innerRecurse
    cases success
    exact partialStrengthenTypedIntervalOpp_sound
      (innerSound := innerIH innerResult innerRecurse)

/-- Dispatcher soundness at the `Term.intervalMeet` arm.  Binary
recurse on two interval subterms, no type-shape strengthening: two
inductive hypotheses (one per subterm) thread to the wrapper. -/
theorem partialStrengthenTyped?_atIntervalMeet_imp_sound {mode : Mode}
    {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {leftRaw rightRaw : RawTerm sourceScope}
    {leftValue : Term sourceCtx Ty.interval leftRaw}
    {rightValue : Term sourceCtx Ty.interval rightRaw}
    (strengthening : ContextStrengthening sourceCtx targetCtx)
    (leftIH : ∀ leftResult,
        partialStrengthenTyped? leftValue strengthening =
            some leftResult →
          StrengtheningSoundness leftResult)
    (rightIH : ∀ rightResult,
        partialStrengthenTyped? rightValue strengthening =
            some rightResult →
          StrengtheningSoundness rightResult)
    (result : StrengtheningResult strengthening
      (Term.intervalMeet (leftValue := leftValue) (rightValue := rightValue)))
    (success : partialStrengthenTyped?
        (Term.intervalMeet (leftValue := leftValue) (rightValue := rightValue))
          strengthening =
          some result) :
    StrengtheningSoundness result := by
  unfold partialStrengthenTyped? at success
  split at success
  · cases success
  · rename_i leftResult leftRecurse
    split at success
    · cases success
    · rename_i rightResult rightRecurse
      cases success
      exact partialStrengthenTypedIntervalMeet_sound
        (leftSound := leftIH leftResult leftRecurse)
        (rightSound := rightIH rightResult rightRecurse)

/-- Dispatcher soundness at the `Term.intervalJoin` arm.  Mirrors
`atIntervalMeet`. -/
theorem partialStrengthenTyped?_atIntervalJoin_imp_sound {mode : Mode}
    {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {leftRaw rightRaw : RawTerm sourceScope}
    {leftValue : Term sourceCtx Ty.interval leftRaw}
    {rightValue : Term sourceCtx Ty.interval rightRaw}
    (strengthening : ContextStrengthening sourceCtx targetCtx)
    (leftIH : ∀ leftResult,
        partialStrengthenTyped? leftValue strengthening =
            some leftResult →
          StrengtheningSoundness leftResult)
    (rightIH : ∀ rightResult,
        partialStrengthenTyped? rightValue strengthening =
            some rightResult →
          StrengtheningSoundness rightResult)
    (result : StrengtheningResult strengthening
      (Term.intervalJoin (leftValue := leftValue) (rightValue := rightValue)))
    (success : partialStrengthenTyped?
        (Term.intervalJoin (leftValue := leftValue) (rightValue := rightValue))
          strengthening =
          some result) :
    StrengtheningSoundness result := by
  unfold partialStrengthenTyped? at success
  split at success
  · cases success
  · rename_i leftResult leftRecurse
    split at success
    · cases success
    · rename_i rightResult rightRecurse
      cases success
      exact partialStrengthenTypedIntervalJoin_sound
        (leftSound := leftIH leftResult leftRecurse)
        (rightSound := rightIH rightResult rightRecurse)

/-- Dispatcher soundness at the `Term.listCons` arm.  Binary recurse
on head and tail subterms; the elementType strengthening is implicit
in the wrapper's type-equality discharge. -/
theorem partialStrengthenTyped?_atListCons_imp_sound {mode : Mode}
    {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {elementType : Ty level sourceScope}
    {headRaw tailRaw : RawTerm sourceScope}
    {headTerm : Term sourceCtx elementType headRaw}
    {tailTerm : Term sourceCtx (Ty.listType elementType) tailRaw}
    (strengthening : ContextStrengthening sourceCtx targetCtx)
    (headIH : ∀ headResult,
        partialStrengthenTyped? headTerm strengthening =
            some headResult →
          StrengtheningSoundness headResult)
    (tailIH : ∀ tailResult,
        partialStrengthenTyped? tailTerm strengthening =
            some tailResult →
          StrengtheningSoundness tailResult)
    (result : StrengtheningResult strengthening
      (Term.listCons (headTerm := headTerm) (tailTerm := tailTerm)))
    (success : partialStrengthenTyped?
        (Term.listCons (headTerm := headTerm) (tailTerm := tailTerm))
          strengthening =
          some result) :
    StrengtheningSoundness result := by
  unfold partialStrengthenTyped? at success
  split at success
  · cases success
  · rename_i headResult headRecurse
    split at success
    · cases success
    · rename_i tailResult tailRecurse
      cases success
      exact partialStrengthenTypedListCons_sound
        (headSound := headIH headResult headRecurse)
        (tailSound := tailIH tailResult tailRecurse)

/-- Dispatcher soundness at the `Term.listNil` arm.  Type-only
strengthening (no value recurse): the dispatcher branches solely on
`elementType.partialStrengthen?`, and the wrapper soundness consumes
the witness directly. -/
theorem partialStrengthenTyped?_atListNil_imp_sound {mode : Mode}
    {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    (elementType : Ty level sourceScope)
    (strengthening : ContextStrengthening sourceCtx targetCtx)
    (result : StrengtheningResult strengthening
      (Term.listNil (context := sourceCtx) (elementType := elementType)))
    (success : partialStrengthenTyped?
        (Term.listNil (context := sourceCtx) (elementType := elementType))
          strengthening =
          some result) :
    StrengtheningSoundness result := by
  unfold partialStrengthenTyped? at success
  split at success
  · cases success
  · rename_i targetElementType elementSuccess
    cases success
    exact partialStrengthenTypedListNilOfType_sound strengthening
      elementType targetElementType elementSuccess

/-- Dispatcher soundness at the `Term.optionNone` arm.  Mirrors
`atListNil`: type-only strengthening, wrapper applied directly. -/
theorem partialStrengthenTyped?_atOptionNone_imp_sound {mode : Mode}
    {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    (elementType : Ty level sourceScope)
    (strengthening : ContextStrengthening sourceCtx targetCtx)
    (result : StrengtheningResult strengthening
      (Term.optionNone (context := sourceCtx) (elementType := elementType)))
    (success : partialStrengthenTyped?
        (Term.optionNone (context := sourceCtx) (elementType := elementType))
          strengthening =
          some result) :
    StrengtheningSoundness result := by
  unfold partialStrengthenTyped? at success
  split at success
  · cases success
  · rename_i targetElementType elementSuccess
    cases success
    exact partialStrengthenTypedOptionNoneOfType_sound strengthening
      elementType targetElementType elementSuccess

/-- Dispatcher soundness at the `Term.eitherInl` arm.  Mixed shape:
right-type strengthening witness + single value-subterm IH. -/
theorem partialStrengthenTyped?_atEitherInl_imp_sound {mode : Mode}
    {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {leftType rightType : Ty level sourceScope}
    {valueRaw : RawTerm sourceScope}
    {valueTerm : Term sourceCtx leftType valueRaw}
    (strengthening : ContextStrengthening sourceCtx targetCtx)
    (valueIH : ∀ valueResult,
        partialStrengthenTyped? valueTerm strengthening =
            some valueResult →
          StrengtheningSoundness valueResult)
    (result : StrengtheningResult strengthening
      (Term.eitherInl (rightType := rightType) (valueTerm := valueTerm)))
    (success : partialStrengthenTyped?
        (Term.eitherInl (rightType := rightType) (valueTerm := valueTerm))
          strengthening =
          some result) :
    StrengtheningSoundness result := by
  unfold partialStrengthenTyped? at success
  split at success
  · cases success
  · rename_i targetRightType rightSuccess
    split at success
    · cases success
    · rename_i valueResult valueRecurse
      cases success
      exact partialStrengthenTypedEitherInlOfRightType_sound
        rightSuccess (valueSound := valueIH valueResult valueRecurse)

/-- Dispatcher soundness at the `Term.eitherInr` arm.  Mirrors
`atEitherInl` with left-type strengthening on the unused side. -/
theorem partialStrengthenTyped?_atEitherInr_imp_sound {mode : Mode}
    {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {leftType rightType : Ty level sourceScope}
    {valueRaw : RawTerm sourceScope}
    {valueTerm : Term sourceCtx rightType valueRaw}
    (strengthening : ContextStrengthening sourceCtx targetCtx)
    (valueIH : ∀ valueResult,
        partialStrengthenTyped? valueTerm strengthening =
            some valueResult →
          StrengtheningSoundness valueResult)
    (result : StrengtheningResult strengthening
      (Term.eitherInr (leftType := leftType) (valueTerm := valueTerm)))
    (success : partialStrengthenTyped?
        (Term.eitherInr (leftType := leftType) (valueTerm := valueTerm))
          strengthening =
          some result) :
    StrengtheningSoundness result := by
  unfold partialStrengthenTyped? at success
  split at success
  · cases success
  · rename_i targetLeftType leftSuccess
    split at success
    · cases success
    · rename_i valueResult valueRecurse
      cases success
      exact partialStrengthenTypedEitherInrOfLeftType_sound
        leftSuccess (valueSound := valueIH valueResult valueRecurse)

end Term

end LeanFX2
