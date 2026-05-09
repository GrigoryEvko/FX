import LeanFX2.Foundation.RenameIdentity

/-! # Foundation/RawPartialRename

Partial raw renamings are the safe primitive for recognizing whether a
raw term is the weakening of a term in the previous outer scope.  A naive
`dropNewest?` recursion is wrong under binders: inside `lam` or `pathLam`,
index 0 is the binder and must be preserved while the outer dropped
variable shifts to index 1.  `PartialRawRenaming.lift` encodes exactly
that de Bruijn behavior.
-/

namespace LeanFX2

/-- Partial renaming from one raw scope to another.  Returning `none`
means the source variable cannot be represented in the target scope. -/
def PartialRawRenaming (sourceScope targetScope : Nat) : Type :=
  Fin sourceScope → Option (Fin targetScope)

namespace PartialRawRenaming

/-- Lift a partial renaming under a raw binder.  The binder variable is
preserved; outer variables are delegated to the underlying partial
renaming and shifted when they survive. -/
@[reducible] def lift {sourceScope targetScope : Nat}
    (partialRenaming : PartialRawRenaming sourceScope targetScope) :
    PartialRawRenaming (sourceScope + 1) (targetScope + 1)
  | ⟨0, _⟩ => some ⟨0, Nat.zero_lt_succ _⟩
  | ⟨index + 1, indexLt⟩ =>
      match partialRenaming ⟨index, Nat.lt_of_succ_lt_succ indexLt⟩ with
      | some targetPosition => some (Fin.succ targetPosition)
      | none => none

/-- Drop the newest variable from a scope, if the variable being renamed
is not that newest variable. -/
@[reducible] def dropNewest {scope : Nat} :
    PartialRawRenaming (scope + 1) scope
  | ⟨0, _⟩ => none
  | ⟨index + 1, indexLt⟩ =>
      some ⟨index, Nat.lt_of_succ_lt_succ indexLt⟩

/-- Dropping after weakening recovers the original variable. -/
theorem dropNewest_weaken {scope : Nat} (position : Fin scope) :
    dropNewest (RawRenaming.weaken position) = some position := rfl

/-- Lifted dropping after lifted weakening recovers the original variable,
including the preserved binder case. -/
theorem lift_dropNewest_weaken_lift {scope : Nat} :
    ∀ position : Fin (scope + 1),
      (lift dropNewest) (RawRenaming.lift RawRenaming.weaken position) =
        some position
  | ⟨0, _⟩ => rfl
  | ⟨index + 1, indexLt⟩ => by
      cases index with
      | zero => rfl
      | succ priorIndex => rfl

end PartialRawRenaming

/-- Combine two optional results. -/
def Option.mapTwo
    {firstType secondType resultType : Type}
    (firstOption : Option firstType)
    (secondOption : Option secondType)
    (combine : firstType → secondType → resultType) :
    Option resultType :=
  match firstOption with
  | some firstValue =>
      match secondOption with
      | some secondValue => some (combine firstValue secondValue)
      | none => none
  | none => none

/-- Combine three optional results. -/
def Option.mapThree
    {firstType secondType thirdType resultType : Type}
    (firstOption : Option firstType)
    (secondOption : Option secondType)
    (thirdOption : Option thirdType)
    (combine : firstType → secondType → thirdType → resultType) :
    Option resultType :=
  match firstOption with
  | some firstValue =>
      match secondOption with
      | some secondValue =>
          match thirdOption with
          | some thirdValue => some (combine firstValue secondValue thirdValue)
          | none => none
      | none => none
  | none => none

/-- Apply a partial renaming to a raw term.  The result is `none` exactly
when some variable occurrence cannot be represented in the target scope. -/
def RawTerm.partialRename? : ∀ {sourceScope targetScope : Nat},
    RawTerm sourceScope →
    PartialRawRenaming sourceScope targetScope →
    Option (RawTerm targetScope)
  | _, _, .var position, partialRenaming =>
      match partialRenaming position with
      | some targetPosition => some (RawTerm.var targetPosition)
      | none => none
  | _, _, .unit, _ => some RawTerm.unit
  | _, _, .lam body, partialRenaming =>
      match RawTerm.partialRename? body partialRenaming.lift with
      | some renamedBody => some (RawTerm.lam renamedBody)
      | none => none
  | _, _, .app functionTerm argumentTerm, partialRenaming =>
      Option.mapTwo
        (RawTerm.partialRename? functionTerm partialRenaming)
        (RawTerm.partialRename? argumentTerm partialRenaming)
        RawTerm.app
  | _, _, .pair firstValue secondValue, partialRenaming =>
      Option.mapTwo
        (RawTerm.partialRename? firstValue partialRenaming)
        (RawTerm.partialRename? secondValue partialRenaming)
        RawTerm.pair
  | _, _, .fst pairTerm, partialRenaming =>
      match RawTerm.partialRename? pairTerm partialRenaming with
      | some renamedPair => some (RawTerm.fst renamedPair)
      | none => none
  | _, _, .snd pairTerm, partialRenaming =>
      match RawTerm.partialRename? pairTerm partialRenaming with
      | some renamedPair => some (RawTerm.snd renamedPair)
      | none => none
  | _, _, .boolTrue, _ => some RawTerm.boolTrue
  | _, _, .boolFalse, _ => some RawTerm.boolFalse
  | _, _, .boolElim scrutinee thenBranch elseBranch, partialRenaming =>
      Option.mapThree
        (RawTerm.partialRename? scrutinee partialRenaming)
        (RawTerm.partialRename? thenBranch partialRenaming)
        (RawTerm.partialRename? elseBranch partialRenaming)
        RawTerm.boolElim
  | _, _, .natZero, _ => some RawTerm.natZero
  | _, _, .natSucc predecessor, partialRenaming =>
      match RawTerm.partialRename? predecessor partialRenaming with
      | some renamedPredecessor => some (RawTerm.natSucc renamedPredecessor)
      | none => none
  | _, _, .natElim scrutinee zeroBranch succBranch, partialRenaming =>
      Option.mapThree
        (RawTerm.partialRename? scrutinee partialRenaming)
        (RawTerm.partialRename? zeroBranch partialRenaming)
        (RawTerm.partialRename? succBranch partialRenaming)
        RawTerm.natElim
  | _, _, .natRec scrutinee zeroBranch succBranch, partialRenaming =>
      Option.mapThree
        (RawTerm.partialRename? scrutinee partialRenaming)
        (RawTerm.partialRename? zeroBranch partialRenaming)
        (RawTerm.partialRename? succBranch partialRenaming)
        RawTerm.natRec
  | _, _, .listNil, _ => some RawTerm.listNil
  | _, _, .listCons headTerm tailTerm, partialRenaming =>
      Option.mapTwo
        (RawTerm.partialRename? headTerm partialRenaming)
        (RawTerm.partialRename? tailTerm partialRenaming)
        RawTerm.listCons
  | _, _, .listElim scrutinee nilBranch consBranch, partialRenaming =>
      Option.mapThree
        (RawTerm.partialRename? scrutinee partialRenaming)
        (RawTerm.partialRename? nilBranch partialRenaming)
        (RawTerm.partialRename? consBranch partialRenaming)
        RawTerm.listElim
  | _, _, .optionNone, _ => some RawTerm.optionNone
  | _, _, .optionSome valueTerm, partialRenaming =>
      match RawTerm.partialRename? valueTerm partialRenaming with
      | some renamedValue => some (RawTerm.optionSome renamedValue)
      | none => none
  | _, _, .optionMatch scrutinee noneBranch someBranch, partialRenaming =>
      Option.mapThree
        (RawTerm.partialRename? scrutinee partialRenaming)
        (RawTerm.partialRename? noneBranch partialRenaming)
        (RawTerm.partialRename? someBranch partialRenaming)
        RawTerm.optionMatch
  | _, _, .eitherInl valueTerm, partialRenaming =>
      match RawTerm.partialRename? valueTerm partialRenaming with
      | some renamedValue => some (RawTerm.eitherInl renamedValue)
      | none => none
  | _, _, .eitherInr valueTerm, partialRenaming =>
      match RawTerm.partialRename? valueTerm partialRenaming with
      | some renamedValue => some (RawTerm.eitherInr renamedValue)
      | none => none
  | _, _, .eitherMatch scrutinee leftBranch rightBranch, partialRenaming =>
      Option.mapThree
        (RawTerm.partialRename? scrutinee partialRenaming)
        (RawTerm.partialRename? leftBranch partialRenaming)
        (RawTerm.partialRename? rightBranch partialRenaming)
        RawTerm.eitherMatch
  | _, _, .refl rawWitness, partialRenaming =>
      match RawTerm.partialRename? rawWitness partialRenaming with
      | some renamedWitness => some (RawTerm.refl renamedWitness)
      | none => none
  | _, _, .idJ baseCase witness, partialRenaming =>
      Option.mapTwo
        (RawTerm.partialRename? baseCase partialRenaming)
        (RawTerm.partialRename? witness partialRenaming)
        RawTerm.idJ
  | _, _, .modIntro raw, partialRenaming =>
      match RawTerm.partialRename? raw partialRenaming with
      | some renamedRaw => some (RawTerm.modIntro renamedRaw)
      | none => none
  | _, _, .modElim raw, partialRenaming =>
      match RawTerm.partialRename? raw partialRenaming with
      | some renamedRaw => some (RawTerm.modElim renamedRaw)
      | none => none
  | _, _, .subsume raw, partialRenaming =>
      match RawTerm.partialRename? raw partialRenaming with
      | some renamedRaw => some (RawTerm.subsume renamedRaw)
      | none => none
  | _, _, .interval0, _ => some RawTerm.interval0
  | _, _, .interval1, _ => some RawTerm.interval1
  | _, _, .intervalOpp intervalTerm, partialRenaming =>
      match RawTerm.partialRename? intervalTerm partialRenaming with
      | some renamedInterval => some (RawTerm.intervalOpp renamedInterval)
      | none => none
  | _, _, .intervalMeet leftInterval rightInterval, partialRenaming =>
      Option.mapTwo
        (RawTerm.partialRename? leftInterval partialRenaming)
        (RawTerm.partialRename? rightInterval partialRenaming)
        RawTerm.intervalMeet
  | _, _, .intervalJoin leftInterval rightInterval, partialRenaming =>
      Option.mapTwo
        (RawTerm.partialRename? leftInterval partialRenaming)
        (RawTerm.partialRename? rightInterval partialRenaming)
        RawTerm.intervalJoin
  | _, _, .pathLam body, partialRenaming =>
      match RawTerm.partialRename? body partialRenaming.lift with
      | some renamedBody => some (RawTerm.pathLam renamedBody)
      | none => none
  | _, _, .pathApp pathTerm intervalArg, partialRenaming =>
      Option.mapTwo
        (RawTerm.partialRename? pathTerm partialRenaming)
        (RawTerm.partialRename? intervalArg partialRenaming)
        RawTerm.pathApp
  | _, _, .glueIntro baseValue partialValue, partialRenaming =>
      Option.mapTwo
        (RawTerm.partialRename? baseValue partialRenaming)
        (RawTerm.partialRename? partialValue partialRenaming)
        RawTerm.glueIntro
  | _, _, .glueElim gluedValue, partialRenaming =>
      match RawTerm.partialRename? gluedValue partialRenaming with
      | some renamedGlued => some (RawTerm.glueElim renamedGlued)
      | none => none
  | _, _, .transp path source, partialRenaming =>
      Option.mapTwo
        (RawTerm.partialRename? path partialRenaming)
        (RawTerm.partialRename? source partialRenaming)
        RawTerm.transp
  | _, _, .hcomp sides cap, partialRenaming =>
      Option.mapTwo
        (RawTerm.partialRename? sides partialRenaming)
        (RawTerm.partialRename? cap partialRenaming)
        RawTerm.hcomp
  | _, _, .oeqRefl witnessTerm, partialRenaming =>
      match RawTerm.partialRename? witnessTerm partialRenaming with
      | some renamedWitness => some (RawTerm.oeqRefl renamedWitness)
      | none => none
  | _, _, .oeqJ baseCase witness, partialRenaming =>
      Option.mapTwo
        (RawTerm.partialRename? baseCase partialRenaming)
        (RawTerm.partialRename? witness partialRenaming)
        RawTerm.oeqJ
  | _, _, .oeqFunext pointwiseEquality, partialRenaming =>
      match RawTerm.partialRename? pointwiseEquality partialRenaming with
      | some renamedPointwise => some (RawTerm.oeqFunext renamedPointwise)
      | none => none
  | _, _, .idStrictRefl witnessTerm, partialRenaming =>
      match RawTerm.partialRename? witnessTerm partialRenaming with
      | some renamedWitness => some (RawTerm.idStrictRefl renamedWitness)
      | none => none
  | _, _, .idStrictRec baseCase witness, partialRenaming =>
      Option.mapTwo
        (RawTerm.partialRename? baseCase partialRenaming)
        (RawTerm.partialRename? witness partialRenaming)
        RawTerm.idStrictRec
  | _, _, .equivIntro forwardFn backwardFn, partialRenaming =>
      Option.mapTwo
        (RawTerm.partialRename? forwardFn partialRenaming)
        (RawTerm.partialRename? backwardFn partialRenaming)
        RawTerm.equivIntro
  | _, _, .equivApp equivTerm argument, partialRenaming =>
      Option.mapTwo
        (RawTerm.partialRename? equivTerm partialRenaming)
        (RawTerm.partialRename? argument partialRenaming)
        RawTerm.equivApp
  | _, _, .refineIntro rawValue predicateProof, partialRenaming =>
      Option.mapTwo
        (RawTerm.partialRename? rawValue partialRenaming)
        (RawTerm.partialRename? predicateProof partialRenaming)
        RawTerm.refineIntro
  | _, _, .refineElim refinedValue, partialRenaming =>
      match RawTerm.partialRename? refinedValue partialRenaming with
      | some renamedRefined => some (RawTerm.refineElim renamedRefined)
      | none => none
  | _, _, .recordIntro firstField, partialRenaming =>
      match RawTerm.partialRename? firstField partialRenaming with
      | some renamedField => some (RawTerm.recordIntro renamedField)
      | none => none
  | _, _, .recordProj recordValue, partialRenaming =>
      match RawTerm.partialRename? recordValue partialRenaming with
      | some renamedRecord => some (RawTerm.recordProj renamedRecord)
      | none => none
  | _, _, .codataUnfold initialState transition, partialRenaming =>
      Option.mapTwo
        (RawTerm.partialRename? initialState partialRenaming)
        (RawTerm.partialRename? transition partialRenaming)
        RawTerm.codataUnfold
  | _, _, .codataDest codataValue, partialRenaming =>
      match RawTerm.partialRename? codataValue partialRenaming with
      | some renamedCodata => some (RawTerm.codataDest renamedCodata)
      | none => none
  | _, _, .sessionSend channel payload, partialRenaming =>
      Option.mapTwo
        (RawTerm.partialRename? channel partialRenaming)
        (RawTerm.partialRename? payload partialRenaming)
        RawTerm.sessionSend
  | _, _, .sessionRecv channel, partialRenaming =>
      match RawTerm.partialRename? channel partialRenaming with
      | some renamedChannel => some (RawTerm.sessionRecv renamedChannel)
      | none => none
  | _, _, .effectPerform operationTag arguments, partialRenaming =>
      Option.mapTwo
        (RawTerm.partialRename? operationTag partialRenaming)
        (RawTerm.partialRename? arguments partialRenaming)
        RawTerm.effectPerform
  | _, _, .universeCode innerLevel, _ => some (RawTerm.universeCode innerLevel)
  | _, _, .arrowCode domainCode codomainCode, partialRenaming =>
      Option.mapTwo
        (RawTerm.partialRename? domainCode partialRenaming)
        (RawTerm.partialRename? codomainCode partialRenaming)
        RawTerm.arrowCode
  | _, _, .piTyCode domainCode codomainCode, partialRenaming =>
      Option.mapTwo
        (RawTerm.partialRename? domainCode partialRenaming)
        (RawTerm.partialRename? codomainCode partialRenaming.lift)
        RawTerm.piTyCode
  | _, _, .sigmaTyCode domainCode codomainCode, partialRenaming =>
      Option.mapTwo
        (RawTerm.partialRename? domainCode partialRenaming)
        (RawTerm.partialRename? codomainCode partialRenaming.lift)
        RawTerm.sigmaTyCode
  | _, _, .productCode firstCode secondCode, partialRenaming =>
      Option.mapTwo
        (RawTerm.partialRename? firstCode partialRenaming)
        (RawTerm.partialRename? secondCode partialRenaming)
        RawTerm.productCode
  | _, _, .sumCode leftCode rightCode, partialRenaming =>
      Option.mapTwo
        (RawTerm.partialRename? leftCode partialRenaming)
        (RawTerm.partialRename? rightCode partialRenaming)
        RawTerm.sumCode
  | _, _, .listCode elementCode, partialRenaming =>
      match RawTerm.partialRename? elementCode partialRenaming with
      | some renamedElement => some (RawTerm.listCode renamedElement)
      | none => none
  | _, _, .optionCode elementCode, partialRenaming =>
      match RawTerm.partialRename? elementCode partialRenaming with
      | some renamedElement => some (RawTerm.optionCode renamedElement)
      | none => none
  | _, _, .eitherCode leftCode rightCode, partialRenaming =>
      Option.mapTwo
        (RawTerm.partialRename? leftCode partialRenaming)
        (RawTerm.partialRename? rightCode partialRenaming)
        RawTerm.eitherCode
  | _, _, .idCode typeCode leftRaw rightRaw, partialRenaming =>
      Option.mapThree
        (RawTerm.partialRename? typeCode partialRenaming)
        (RawTerm.partialRename? leftRaw partialRenaming)
        (RawTerm.partialRename? rightRaw partialRenaming)
        RawTerm.idCode
  | _, _, .equivCode leftTypeCode rightTypeCode, partialRenaming =>
      Option.mapTwo
        (RawTerm.partialRename? leftTypeCode partialRenaming)
        (RawTerm.partialRename? rightTypeCode partialRenaming)
        RawTerm.equivCode
  | _, _, .cumulUpMarker innerCodeRaw, partialRenaming =>
      match RawTerm.partialRename? innerCodeRaw partialRenaming with
      | some renamedInnerCode => some (RawTerm.cumulUpMarker renamedInnerCode)
      | none => none
  | _, _, .uaToEquiv proofRaw, partialRenaming =>
      match RawTerm.partialRename? proofRaw partialRenaming with
      | some renamedProof => some (RawTerm.uaToEquiv renamedProof)
      | none => none
  | _, _, .equivApply equivRaw argRaw, partialRenaming =>
      Option.mapTwo
        (RawTerm.partialRename? equivRaw partialRenaming)
        (RawTerm.partialRename? argRaw partialRenaming)
        RawTerm.equivApply
  | _, _, .pathCompose leftPathRaw rightPathRaw, partialRenaming =>
      Option.mapTwo
        (RawTerm.partialRename? leftPathRaw partialRenaming)
        (RawTerm.partialRename? rightPathRaw partialRenaming)
        RawTerm.pathCompose

/-- Try to lower a raw term across one outer weakening.  This is the
recognizer needed before any safe constant-transport computation rule:
it succeeds only when every variable occurrence survives `dropNewest`,
with binders handled by `PartialRawRenaming.lift`. -/
def RawTerm.unweaken? {scope : Nat}
    (term : RawTerm (scope + 1)) : Option (RawTerm scope) :=
  RawTerm.partialRename? term PartialRawRenaming.dropNewest

/-- Recognize the raw shape of a constant path: a `pathLam` whose body
is just a weakening of an outer-scope term.  This is deliberately only a
recognizer, not a reduction rule; transport computation must use a
separate confluence-aware cascade. -/
def RawTerm.constantPathBody? {scope : Nat}
    (pathTerm : RawTerm scope) : Option (RawTerm scope) :=
  match pathTerm with
  | RawTerm.pathLam body => RawTerm.unweaken? body
  | RawTerm.var _ => none
  | RawTerm.unit => none
  | RawTerm.lam _ => none
  | RawTerm.app _ _ => none
  | RawTerm.pair _ _ => none
  | RawTerm.fst _ => none
  | RawTerm.snd _ => none
  | RawTerm.boolTrue => none
  | RawTerm.boolFalse => none
  | RawTerm.boolElim _ _ _ => none
  | RawTerm.natZero => none
  | RawTerm.natSucc _ => none
  | RawTerm.natElim _ _ _ => none
  | RawTerm.natRec _ _ _ => none
  | RawTerm.listNil => none
  | RawTerm.listCons _ _ => none
  | RawTerm.listElim _ _ _ => none
  | RawTerm.optionNone => none
  | RawTerm.optionSome _ => none
  | RawTerm.optionMatch _ _ _ => none
  | RawTerm.eitherInl _ => none
  | RawTerm.eitherInr _ => none
  | RawTerm.eitherMatch _ _ _ => none
  | RawTerm.refl _ => none
  | RawTerm.idJ _ _ => none
  | RawTerm.modIntro _ => none
  | RawTerm.modElim _ => none
  | RawTerm.subsume _ => none
  | RawTerm.interval0 => none
  | RawTerm.interval1 => none
  | RawTerm.intervalOpp _ => none
  | RawTerm.intervalMeet _ _ => none
  | RawTerm.intervalJoin _ _ => none
  | RawTerm.pathApp _ _ => none
  | RawTerm.glueIntro _ _ => none
  | RawTerm.glueElim _ => none
  | RawTerm.transp _ _ => none
  | RawTerm.hcomp _ _ => none
  | RawTerm.oeqRefl _ => none
  | RawTerm.oeqJ _ _ => none
  | RawTerm.oeqFunext _ => none
  | RawTerm.idStrictRefl _ => none
  | RawTerm.idStrictRec _ _ => none
  | RawTerm.equivIntro _ _ => none
  | RawTerm.equivApp _ _ => none
  | RawTerm.refineIntro _ _ => none
  | RawTerm.refineElim _ => none
  | RawTerm.recordIntro _ => none
  | RawTerm.recordProj _ => none
  | RawTerm.codataUnfold _ _ => none
  | RawTerm.codataDest _ => none
  | RawTerm.sessionSend _ _ => none
  | RawTerm.sessionRecv _ => none
  | RawTerm.effectPerform _ _ => none
  | RawTerm.universeCode _ => none
  | RawTerm.arrowCode _ _ => none
  | RawTerm.piTyCode _ _ => none
  | RawTerm.sigmaTyCode _ _ => none
  | RawTerm.productCode _ _ => none
  | RawTerm.sumCode _ _ => none
  | RawTerm.listCode _ => none
  | RawTerm.optionCode _ => none
  | RawTerm.eitherCode _ _ => none
  | RawTerm.idCode _ _ _ => none
  | RawTerm.equivCode _ _ => none
  | RawTerm.cumulUpMarker _ => none
  | RawTerm.uaToEquiv _ => none
  | RawTerm.equivApply _ _ => none
  | RawTerm.pathCompose _ _ => none

/-- The newest variable cannot be lowered across the dropped binder. -/
theorem RawTerm.unweaken?_newest_var_none {scope : Nat} :
    RawTerm.unweaken? (RawTerm.var ⟨0, Nat.zero_lt_succ scope⟩) = none := rfl

/-- A weakened variable lowers to its original position. -/
theorem RawTerm.unweaken?_weaken_var {scope : Nat}
    (position : Fin scope) :
    RawTerm.unweaken? (RawTerm.var (RawRenaming.weaken position)) =
      some (RawTerm.var position) := rfl

/-- Binder variables are preserved while lowering across an outer
weakening.  This guards the bug that a naive `dropNewest?` would make
under `lam` and `pathLam`. -/
theorem RawTerm.partialRename?_lift_preserves_binder_var
    {sourceScope targetScope : Nat}
    (partialRenaming : PartialRawRenaming sourceScope targetScope) :
    RawTerm.partialRename?
      (RawTerm.var ⟨0, Nat.zero_lt_succ sourceScope⟩)
      partialRenaming.lift =
      some (RawTerm.var ⟨0, Nat.zero_lt_succ targetScope⟩) := rfl

/-- Lifting preserves the pointwise "this source variable survives"
condition used by `partialRename?_rename_some`. -/
theorem PartialRawRenaming.lift_rename_some
    {sourceScope middleScope targetScope : Nat}
    {sourceRenaming : RawRenaming sourceScope middleScope}
    {targetRenaming : RawRenaming sourceScope targetScope}
    {partialRenaming : PartialRawRenaming middleScope targetScope}
    (renamingSurvives :
      ∀ position, partialRenaming (sourceRenaming position) =
        some (targetRenaming position)) :
    ∀ position,
      partialRenaming.lift (sourceRenaming.lift position) =
        some (targetRenaming.lift position)
  | ⟨0, _⟩ => rfl
  | ⟨index + 1, indexLt⟩ => by
      cases sourceRenaming ⟨index, Nat.lt_of_succ_lt_succ indexLt⟩ with
      | mk middleIndex middleLt =>
          simp only [PartialRawRenaming.lift, RawRenaming.lift, Fin.succ]
          rw [renamingSurvives ⟨index, Nat.lt_of_succ_lt_succ indexLt⟩]

/-- If a partial renaming accepts every variable produced by a total
renaming, it accepts the whole renamed raw term and produces the
corresponding target-renamed term. -/
theorem RawTerm.partialRename?_rename_some
    {sourceScope middleScope targetScope : Nat}
    (term : RawTerm sourceScope)
    (sourceRenaming : RawRenaming sourceScope middleScope)
    (targetRenaming : RawRenaming sourceScope targetScope)
    (partialRenaming : PartialRawRenaming middleScope targetScope)
    (renamingSurvives :
      ∀ position, partialRenaming (sourceRenaming position) =
        some (targetRenaming position)) :
    RawTerm.partialRename? (term.rename sourceRenaming) partialRenaming =
      some (term.rename targetRenaming) := by
  induction term generalizing middleScope targetScope with
  | var position =>
      simp only [RawTerm.rename, RawTerm.partialRename?]
      rw [renamingSurvives position]
  | unit => rfl
  | lam body bodyIH =>
      simp only [RawTerm.rename, RawTerm.partialRename?]
      rw [bodyIH sourceRenaming.lift targetRenaming.lift
        partialRenaming.lift
        (PartialRawRenaming.lift_rename_some renamingSurvives)]
  | app functionTerm argumentTerm functionIH argumentIH =>
      simp only [RawTerm.rename, RawTerm.partialRename?, Option.mapTwo]
      rw [functionIH sourceRenaming targetRenaming partialRenaming renamingSurvives,
        argumentIH sourceRenaming targetRenaming partialRenaming renamingSurvives]
  | pair firstValue secondValue firstIH secondIH =>
      simp only [RawTerm.rename, RawTerm.partialRename?, Option.mapTwo]
      rw [firstIH sourceRenaming targetRenaming partialRenaming renamingSurvives,
        secondIH sourceRenaming targetRenaming partialRenaming renamingSurvives]
  | fst pairTerm pairIH =>
      simp only [RawTerm.rename, RawTerm.partialRename?]
      rw [pairIH sourceRenaming targetRenaming partialRenaming renamingSurvives]
  | snd pairTerm pairIH =>
      simp only [RawTerm.rename, RawTerm.partialRename?]
      rw [pairIH sourceRenaming targetRenaming partialRenaming renamingSurvives]
  | boolTrue => rfl
  | boolFalse => rfl
  | boolElim scrutinee thenBranch elseBranch scrutineeIH thenIH elseIH =>
      simp only [RawTerm.rename, RawTerm.partialRename?, Option.mapThree]
      rw [scrutineeIH sourceRenaming targetRenaming partialRenaming renamingSurvives,
        thenIH sourceRenaming targetRenaming partialRenaming renamingSurvives,
        elseIH sourceRenaming targetRenaming partialRenaming renamingSurvives]
  | natZero => rfl
  | natSucc predecessor predecessorIH =>
      simp only [RawTerm.rename, RawTerm.partialRename?]
      rw [predecessorIH sourceRenaming targetRenaming partialRenaming renamingSurvives]
  | natElim scrutinee zeroBranch succBranch scrutineeIH zeroIH succIH =>
      simp only [RawTerm.rename, RawTerm.partialRename?, Option.mapThree]
      rw [scrutineeIH sourceRenaming targetRenaming partialRenaming renamingSurvives,
        zeroIH sourceRenaming targetRenaming partialRenaming renamingSurvives,
        succIH sourceRenaming targetRenaming partialRenaming renamingSurvives]
  | natRec scrutinee zeroBranch succBranch scrutineeIH zeroIH succIH =>
      simp only [RawTerm.rename, RawTerm.partialRename?, Option.mapThree]
      rw [scrutineeIH sourceRenaming targetRenaming partialRenaming renamingSurvives,
        zeroIH sourceRenaming targetRenaming partialRenaming renamingSurvives,
        succIH sourceRenaming targetRenaming partialRenaming renamingSurvives]
  | listNil => rfl
  | listCons headTerm tailTerm headIH tailIH =>
      simp only [RawTerm.rename, RawTerm.partialRename?, Option.mapTwo]
      rw [headIH sourceRenaming targetRenaming partialRenaming renamingSurvives,
        tailIH sourceRenaming targetRenaming partialRenaming renamingSurvives]
  | listElim scrutinee nilBranch consBranch scrutineeIH nilIH consIH =>
      simp only [RawTerm.rename, RawTerm.partialRename?, Option.mapThree]
      rw [scrutineeIH sourceRenaming targetRenaming partialRenaming renamingSurvives,
        nilIH sourceRenaming targetRenaming partialRenaming renamingSurvives,
        consIH sourceRenaming targetRenaming partialRenaming renamingSurvives]
  | optionNone => rfl
  | optionSome valueTerm valueIH =>
      simp only [RawTerm.rename, RawTerm.partialRename?]
      rw [valueIH sourceRenaming targetRenaming partialRenaming renamingSurvives]
  | optionMatch scrutinee noneBranch someBranch scrutineeIH noneIH someIH =>
      simp only [RawTerm.rename, RawTerm.partialRename?, Option.mapThree]
      rw [scrutineeIH sourceRenaming targetRenaming partialRenaming renamingSurvives,
        noneIH sourceRenaming targetRenaming partialRenaming renamingSurvives,
        someIH sourceRenaming targetRenaming partialRenaming renamingSurvives]
  | eitherInl valueTerm valueIH =>
      simp only [RawTerm.rename, RawTerm.partialRename?]
      rw [valueIH sourceRenaming targetRenaming partialRenaming renamingSurvives]
  | eitherInr valueTerm valueIH =>
      simp only [RawTerm.rename, RawTerm.partialRename?]
      rw [valueIH sourceRenaming targetRenaming partialRenaming renamingSurvives]
  | eitherMatch scrutinee leftBranch rightBranch scrutineeIH leftIH rightIH =>
      simp only [RawTerm.rename, RawTerm.partialRename?, Option.mapThree]
      rw [scrutineeIH sourceRenaming targetRenaming partialRenaming renamingSurvives,
        leftIH sourceRenaming targetRenaming partialRenaming renamingSurvives,
        rightIH sourceRenaming targetRenaming partialRenaming renamingSurvives]
  | refl witness witnessIH =>
      simp only [RawTerm.rename, RawTerm.partialRename?]
      rw [witnessIH sourceRenaming targetRenaming partialRenaming renamingSurvives]
  | idJ baseCase witness baseIH witnessIH =>
      simp only [RawTerm.rename, RawTerm.partialRename?, Option.mapTwo]
      rw [baseIH sourceRenaming targetRenaming partialRenaming renamingSurvives,
        witnessIH sourceRenaming targetRenaming partialRenaming renamingSurvives]
  | modIntro innerTerm innerIH =>
      simp only [RawTerm.rename, RawTerm.partialRename?]
      rw [innerIH sourceRenaming targetRenaming partialRenaming renamingSurvives]
  | modElim innerTerm innerIH =>
      simp only [RawTerm.rename, RawTerm.partialRename?]
      rw [innerIH sourceRenaming targetRenaming partialRenaming renamingSurvives]
  | subsume innerTerm innerIH =>
      simp only [RawTerm.rename, RawTerm.partialRename?]
      rw [innerIH sourceRenaming targetRenaming partialRenaming renamingSurvives]
  | interval0 => rfl
  | interval1 => rfl
  | intervalOpp intervalTerm intervalIH =>
      simp only [RawTerm.rename, RawTerm.partialRename?]
      rw [intervalIH sourceRenaming targetRenaming partialRenaming renamingSurvives]
  | intervalMeet leftInterval rightInterval leftIH rightIH =>
      simp only [RawTerm.rename, RawTerm.partialRename?, Option.mapTwo]
      rw [leftIH sourceRenaming targetRenaming partialRenaming renamingSurvives,
        rightIH sourceRenaming targetRenaming partialRenaming renamingSurvives]
  | intervalJoin leftInterval rightInterval leftIH rightIH =>
      simp only [RawTerm.rename, RawTerm.partialRename?, Option.mapTwo]
      rw [leftIH sourceRenaming targetRenaming partialRenaming renamingSurvives,
        rightIH sourceRenaming targetRenaming partialRenaming renamingSurvives]
  | pathLam body bodyIH =>
      simp only [RawTerm.rename, RawTerm.partialRename?]
      rw [bodyIH sourceRenaming.lift targetRenaming.lift
        partialRenaming.lift
        (PartialRawRenaming.lift_rename_some renamingSurvives)]
  | pathApp pathTerm intervalArg pathIH intervalIH =>
      simp only [RawTerm.rename, RawTerm.partialRename?, Option.mapTwo]
      rw [pathIH sourceRenaming targetRenaming partialRenaming renamingSurvives,
        intervalIH sourceRenaming targetRenaming partialRenaming renamingSurvives]
  | glueIntro baseValue partialValue baseIH partialIH =>
      simp only [RawTerm.rename, RawTerm.partialRename?, Option.mapTwo]
      rw [baseIH sourceRenaming targetRenaming partialRenaming renamingSurvives,
        partialIH sourceRenaming targetRenaming partialRenaming renamingSurvives]
  | glueElim gluedValue gluedIH =>
      simp only [RawTerm.rename, RawTerm.partialRename?]
      rw [gluedIH sourceRenaming targetRenaming partialRenaming renamingSurvives]
  | transp pathTerm sourceTerm pathIH sourceIH =>
      simp only [RawTerm.rename, RawTerm.partialRename?, Option.mapTwo]
      rw [pathIH sourceRenaming targetRenaming partialRenaming renamingSurvives,
        sourceIH sourceRenaming targetRenaming partialRenaming renamingSurvives]
  | hcomp sidesTerm capTerm sidesIH capIH =>
      simp only [RawTerm.rename, RawTerm.partialRename?, Option.mapTwo]
      rw [sidesIH sourceRenaming targetRenaming partialRenaming renamingSurvives,
        capIH sourceRenaming targetRenaming partialRenaming renamingSurvives]
  | oeqRefl witness witnessIH =>
      simp only [RawTerm.rename, RawTerm.partialRename?]
      rw [witnessIH sourceRenaming targetRenaming partialRenaming renamingSurvives]
  | oeqJ baseCase witness baseIH witnessIH =>
      simp only [RawTerm.rename, RawTerm.partialRename?, Option.mapTwo]
      rw [baseIH sourceRenaming targetRenaming partialRenaming renamingSurvives,
        witnessIH sourceRenaming targetRenaming partialRenaming renamingSurvives]
  | oeqFunext pointwiseEquality pointwiseIH =>
      simp only [RawTerm.rename, RawTerm.partialRename?]
      rw [pointwiseIH sourceRenaming targetRenaming partialRenaming renamingSurvives]
  | idStrictRefl witness witnessIH =>
      simp only [RawTerm.rename, RawTerm.partialRename?]
      rw [witnessIH sourceRenaming targetRenaming partialRenaming renamingSurvives]
  | idStrictRec baseCase witness baseIH witnessIH =>
      simp only [RawTerm.rename, RawTerm.partialRename?, Option.mapTwo]
      rw [baseIH sourceRenaming targetRenaming partialRenaming renamingSurvives,
        witnessIH sourceRenaming targetRenaming partialRenaming renamingSurvives]
  | equivIntro forwardFn backwardFn forwardIH backwardIH =>
      simp only [RawTerm.rename, RawTerm.partialRename?, Option.mapTwo]
      rw [forwardIH sourceRenaming targetRenaming partialRenaming renamingSurvives,
        backwardIH sourceRenaming targetRenaming partialRenaming renamingSurvives]
  | equivApp equivTerm argument equivIH argumentIH =>
      simp only [RawTerm.rename, RawTerm.partialRename?, Option.mapTwo]
      rw [equivIH sourceRenaming targetRenaming partialRenaming renamingSurvives,
        argumentIH sourceRenaming targetRenaming partialRenaming renamingSurvives]
  | refineIntro rawValue predicateProof valueIH proofIH =>
      simp only [RawTerm.rename, RawTerm.partialRename?, Option.mapTwo]
      rw [valueIH sourceRenaming targetRenaming partialRenaming renamingSurvives,
        proofIH sourceRenaming targetRenaming partialRenaming renamingSurvives]
  | refineElim refinedValue refinedIH =>
      simp only [RawTerm.rename, RawTerm.partialRename?]
      rw [refinedIH sourceRenaming targetRenaming partialRenaming renamingSurvives]
  | recordIntro firstField firstIH =>
      simp only [RawTerm.rename, RawTerm.partialRename?]
      rw [firstIH sourceRenaming targetRenaming partialRenaming renamingSurvives]
  | recordProj recordValue recordIH =>
      simp only [RawTerm.rename, RawTerm.partialRename?]
      rw [recordIH sourceRenaming targetRenaming partialRenaming renamingSurvives]
  | codataUnfold initialState transition stateIH transitionIH =>
      simp only [RawTerm.rename, RawTerm.partialRename?, Option.mapTwo]
      rw [stateIH sourceRenaming targetRenaming partialRenaming renamingSurvives,
        transitionIH sourceRenaming targetRenaming partialRenaming renamingSurvives]
  | codataDest codataValue codataIH =>
      simp only [RawTerm.rename, RawTerm.partialRename?]
      rw [codataIH sourceRenaming targetRenaming partialRenaming renamingSurvives]
  | sessionSend channel payload channelIH payloadIH =>
      simp only [RawTerm.rename, RawTerm.partialRename?, Option.mapTwo]
      rw [channelIH sourceRenaming targetRenaming partialRenaming renamingSurvives,
        payloadIH sourceRenaming targetRenaming partialRenaming renamingSurvives]
  | sessionRecv channel channelIH =>
      simp only [RawTerm.rename, RawTerm.partialRename?]
      rw [channelIH sourceRenaming targetRenaming partialRenaming renamingSurvives]
  | effectPerform operationTag arguments tagIH argumentsIH =>
      simp only [RawTerm.rename, RawTerm.partialRename?, Option.mapTwo]
      rw [tagIH sourceRenaming targetRenaming partialRenaming renamingSurvives,
        argumentsIH sourceRenaming targetRenaming partialRenaming renamingSurvives]
  | universeCode innerLevel => rfl
  | arrowCode domainCode codomainCode domainIH codomainIH =>
      simp only [RawTerm.rename, RawTerm.partialRename?, Option.mapTwo]
      rw [domainIH sourceRenaming targetRenaming partialRenaming renamingSurvives,
        codomainIH sourceRenaming targetRenaming partialRenaming renamingSurvives]
  | piTyCode domainCode codomainCode domainIH codomainIH =>
      simp only [RawTerm.rename, RawTerm.partialRename?, Option.mapTwo]
      rw [domainIH sourceRenaming targetRenaming partialRenaming renamingSurvives,
        codomainIH sourceRenaming.lift targetRenaming.lift partialRenaming.lift
          (PartialRawRenaming.lift_rename_some renamingSurvives)]
  | sigmaTyCode domainCode codomainCode domainIH codomainIH =>
      simp only [RawTerm.rename, RawTerm.partialRename?, Option.mapTwo]
      rw [domainIH sourceRenaming targetRenaming partialRenaming renamingSurvives,
        codomainIH sourceRenaming.lift targetRenaming.lift partialRenaming.lift
          (PartialRawRenaming.lift_rename_some renamingSurvives)]
  | productCode firstCode secondCode firstIH secondIH =>
      simp only [RawTerm.rename, RawTerm.partialRename?, Option.mapTwo]
      rw [firstIH sourceRenaming targetRenaming partialRenaming renamingSurvives,
        secondIH sourceRenaming targetRenaming partialRenaming renamingSurvives]
  | sumCode leftCode rightCode leftIH rightIH =>
      simp only [RawTerm.rename, RawTerm.partialRename?, Option.mapTwo]
      rw [leftIH sourceRenaming targetRenaming partialRenaming renamingSurvives,
        rightIH sourceRenaming targetRenaming partialRenaming renamingSurvives]
  | listCode elementCode elementIH =>
      simp only [RawTerm.rename, RawTerm.partialRename?]
      rw [elementIH sourceRenaming targetRenaming partialRenaming renamingSurvives]
  | optionCode elementCode elementIH =>
      simp only [RawTerm.rename, RawTerm.partialRename?]
      rw [elementIH sourceRenaming targetRenaming partialRenaming renamingSurvives]
  | eitherCode leftCode rightCode leftIH rightIH =>
      simp only [RawTerm.rename, RawTerm.partialRename?, Option.mapTwo]
      rw [leftIH sourceRenaming targetRenaming partialRenaming renamingSurvives,
        rightIH sourceRenaming targetRenaming partialRenaming renamingSurvives]
  | idCode typeCode leftRaw rightRaw typeIH leftIH rightIH =>
      simp only [RawTerm.rename, RawTerm.partialRename?, Option.mapThree]
      rw [typeIH sourceRenaming targetRenaming partialRenaming renamingSurvives,
        leftIH sourceRenaming targetRenaming partialRenaming renamingSurvives,
        rightIH sourceRenaming targetRenaming partialRenaming renamingSurvives]
  | equivCode leftTypeCode rightTypeCode leftIH rightIH =>
      simp only [RawTerm.rename, RawTerm.partialRename?, Option.mapTwo]
      rw [leftIH sourceRenaming targetRenaming partialRenaming renamingSurvives,
        rightIH sourceRenaming targetRenaming partialRenaming renamingSurvives]
  | cumulUpMarker innerCode innerIH =>
      simp only [RawTerm.rename, RawTerm.partialRename?]
      rw [innerIH sourceRenaming targetRenaming partialRenaming renamingSurvives]
  | uaToEquiv proofRaw proofIH =>
      simp only [RawTerm.rename, RawTerm.partialRename?]
      rw [proofIH sourceRenaming targetRenaming partialRenaming renamingSurvives]
  | equivApply equivRaw argRaw equivIH argIH =>
      simp only [RawTerm.rename, RawTerm.partialRename?, Option.mapTwo]
      rw [equivIH sourceRenaming targetRenaming partialRenaming renamingSurvives,
        argIH sourceRenaming targetRenaming partialRenaming renamingSurvives]
  | pathCompose leftPathRaw rightPathRaw leftIH rightIH =>
      simp only [RawTerm.rename, RawTerm.partialRename?, Option.mapTwo]
      rw [leftIH sourceRenaming targetRenaming partialRenaming renamingSurvives,
        rightIH sourceRenaming targetRenaming partialRenaming renamingSurvives]

/-- Weakening followed by `unweaken?` recovers any raw term.  This is the
generic form of the constant-path recognizer's positive case and is the
fact future transport computation rules must use instead of per-ctor
ad hoc reductions. -/
theorem RawTerm.unweaken?_weaken {scope : Nat}
    (term : RawTerm scope) :
    RawTerm.unweaken? term.weaken = some term := by
  unfold RawTerm.unweaken?
  unfold RawTerm.weaken
  rw [RawTerm.partialRename?_rename_some term RawRenaming.weaken
    RawRenaming.identity PartialRawRenaming.dropNewest
    PartialRawRenaming.dropNewest_weaken]
  rw [RawTerm.rename_identity]

/-- Compile-time guardrail: the constant-path recognizer accepts every
path whose body is literally an outer-scope term weakened under the
interval binder.  This is the positive all-constructors counterpart to
the interval-escape rejection tests below. -/
theorem RawTerm.constantPathBody?_pathLam_weaken {scope : Nat}
    (term : RawTerm scope) :
    RawTerm.constantPathBody? (RawTerm.pathLam term.weaken) =
      some term := by
  unfold RawTerm.constantPathBody?
  change RawTerm.unweaken? term.weaken = some term
  rw [RawTerm.unweaken?_weaken]

/-- Compile-time guardrail: under `pathLam`, the path binder itself must
survive `unweaken?`.  If binder lifting is wired incorrectly, this stops
being definitional. -/
theorem RawTerm.unweaken?_pathLam_binder_var {scope : Nat} :
    RawTerm.unweaken?
      (RawTerm.pathLam
        (RawTerm.var ⟨0, Nat.zero_lt_succ (scope + 1)⟩)) =
      some
        (RawTerm.pathLam
          (RawTerm.var ⟨0, Nat.zero_lt_succ scope⟩)) := rfl

/-- Compile-time guardrail: under `pathLam`, the dropped outer variable is
index 1 and must be rejected.  This is the shape that blocks an unsound
"constant path" transport rule from accepting a captured variable. -/
theorem RawTerm.unweaken?_pathLam_dropped_outer_var_none {scope : Nat} :
    RawTerm.unweaken?
      (RawTerm.pathLam
        (RawTerm.var
          ⟨1, Nat.succ_lt_succ (Nat.zero_lt_succ scope)⟩)) =
      none := rfl

/-- The constant-path recognizer rejects a path body that mentions the
interval binder.  Such a path is not constant, so future transport must
not compute by the constant-path rule. -/
theorem RawTerm.constantPathBody?_pathLam_interval_var_none {scope : Nat} :
    RawTerm.constantPathBody?
      (RawTerm.pathLam
        (RawTerm.var ⟨0, Nat.zero_lt_succ scope⟩)) =
      none := rfl

/-- The constant-path recognizer accepts a body that is exactly a
weakened outer variable. -/
theorem RawTerm.constantPathBody?_pathLam_weaken_var {scope : Nat}
    (position : Fin scope) :
    RawTerm.constantPathBody?
      (RawTerm.pathLam
        (RawTerm.var (RawRenaming.weaken position))) =
      some (RawTerm.var position) := rfl

/-- The recognizer treats an inner path binder as local to that inner
path, not as a use of the outer interval binder. -/
theorem RawTerm.constantPathBody?_pathLam_nested_binder_var {scope : Nat} :
    RawTerm.constantPathBody?
      (RawTerm.pathLam
        (RawTerm.pathLam
          (RawTerm.var ⟨0, Nat.zero_lt_succ (scope + 1)⟩))) =
      some
        (RawTerm.pathLam
          (RawTerm.var ⟨0, Nat.zero_lt_succ scope⟩)) := rfl

/-- The recognizer rejects a nested body that mentions the outer
interval binder.  This is the compile-time tripwire for the classic
unsound constant-transport shortcut. -/
theorem RawTerm.constantPathBody?_pathLam_nested_interval_escape_none
    {scope : Nat} :
    RawTerm.constantPathBody?
      (RawTerm.pathLam
        (RawTerm.pathLam
          (RawTerm.var
            ⟨1, Nat.succ_lt_succ (Nat.zero_lt_succ scope)⟩))) =
      none := rfl

/-- A non-path term is not a constant path. -/
theorem RawTerm.constantPathBody?_unit_none {scope : Nat} :
    RawTerm.constantPathBody? (RawTerm.unit (scope := scope)) = none := rfl

/-! ### Inversion: `Option.mapTwo`/`Option.mapThree` decompose `some`
results into per-input `some` witnesses.

Used pervasively by `RawTerm.partialRename?_imp_rename` to invert each
multi-child constructor's `Option.mapN` aggregate into per-child
`some` equations.  Plain `cases firstOption` (without `:`-witness)
substitutes the scrutinee in `success`'s type via Lean's definitional
reduction of `Option.mapN`; the `none` branches then `no-confuse` and
the `some` branches `injection` cleanly.  Zero axioms. -/
theorem Option.mapTwo_eq_some
    {firstType secondType resultType : Type _}
    {firstOption : Option firstType}
    {secondOption : Option secondType}
    {combine : firstType → secondType → resultType}
    {result : resultType}
    (success :
      Option.mapTwo firstOption secondOption combine = some result) :
    ∃ firstValue secondValue,
      firstOption = some firstValue ∧
      secondOption = some secondValue ∧
      result = combine firstValue secondValue := by
  cases firstOption with
  | none => cases success
  | some firstValue =>
      cases secondOption with
      | none => cases success
      | some secondValue =>
          injection success with eqResult
          exact ⟨firstValue, secondValue, rfl, rfl, eqResult.symm⟩

theorem Option.mapThree_eq_some
    {firstType secondType thirdType resultType : Type _}
    {firstOption : Option firstType}
    {secondOption : Option secondType}
    {thirdOption : Option thirdType}
    {combine : firstType → secondType → thirdType → resultType}
    {result : resultType}
    (success :
      Option.mapThree firstOption secondOption thirdOption combine =
        some result) :
    ∃ firstValue secondValue thirdValue,
      firstOption = some firstValue ∧
      secondOption = some secondValue ∧
      thirdOption = some thirdValue ∧
      result = combine firstValue secondValue thirdValue := by
  cases firstOption with
  | none => cases success
  | some firstValue =>
      cases secondOption with
      | none => cases success
      | some secondValue =>
          cases thirdOption with
          | none => cases success
          | some thirdValue =>
              injection success with eqResult
              exact ⟨firstValue, secondValue, thirdValue,
                rfl, rfl, rfl, eqResult.symm⟩

/-! ### Inversion: lift preserves the "partial renaming injects back"
property.

The forward direction `lift_rename_some` says: if `partialRenaming` is
the left-inverse of a total renaming pointwise, then so is the lift.
This inversion variant flips the implication: if `partialRenaming` is
*injective into the image of a forward renaming* (every `some k`
result identifies the source position uniquely as `forwardRenaming k`),
then so is the lift.

This is the load-bearing lemma for the Step.transpReflBeta cd cascade
(D2.5.4): under a binder, the cd-firing condition needs to convert an
`unweaken? body = some inner` Option-match witness into the syntactic
equation `body = inner.weaken`.  The inversion proof operates by
forward-style case-split on the inner `partialRenaming ⟨index, _⟩`
result *before* touching the lift hypothesis — never `split at` and
never `simp only [...] at` a hypothesis (both leak `propext` through
Lean 4 v4.29.1's match-compiler equation-lemma generator on indexed
`Fin` cases).  Equality inversions go through `injection` (no-confusion
based) rather than `Option.some.injEq` (an `=`-shaped iff between
propositions, which is `propext`-using). -/
theorem PartialRawRenaming.lift_renamingInjectsBack
    {sourceScope intermediateScope : Nat}
    {forwardRenaming : RawRenaming sourceScope intermediateScope}
    {partialRenaming : PartialRawRenaming intermediateScope sourceScope}
    (renamingInjectsBack :
      ∀ (intermediatePos : Fin intermediateScope)
        (sourcePos : Fin sourceScope),
        partialRenaming intermediatePos = some sourcePos →
        intermediatePos = forwardRenaming sourcePos) :
    ∀ (intermediatePos : Fin (intermediateScope + 1))
      (sourcePos : Fin (sourceScope + 1)),
      partialRenaming.lift intermediatePos = some sourcePos →
      intermediatePos = forwardRenaming.lift sourcePos
  | ⟨0, _⟩, ⟨0, _⟩, _ => rfl
  | ⟨0, _⟩, ⟨targetIndex + 1, _⟩, liftEq => by
      injection liftEq with finEq
      injection finEq with valEq
      cases valEq
  | ⟨intermediateIndex + 1, intermediateIndexLt⟩, sourcePos, liftEq => by
      have priorLt : intermediateIndex < intermediateScope :=
        Nat.lt_of_succ_lt_succ intermediateIndexLt
      cases hInner : partialRenaming ⟨intermediateIndex, priorLt⟩ with
      | none =>
          have liftBranchEq :
              partialRenaming.lift
                ⟨intermediateIndex + 1, intermediateIndexLt⟩ =
              (none : Option (Fin (sourceScope + 1))) := by
            show (match partialRenaming ⟨intermediateIndex, priorLt⟩ with
                  | some targetPosition => some (Fin.succ targetPosition)
                  | none => none) = none
            rw [hInner]
          rw [liftBranchEq] at liftEq
          cases liftEq
      | some resolvedTargetPos =>
          have liftBranchEq :
              partialRenaming.lift
                ⟨intermediateIndex + 1, intermediateIndexLt⟩ =
              some (Fin.succ resolvedTargetPos) := by
            show (match partialRenaming ⟨intermediateIndex, priorLt⟩ with
                  | some targetPosition => some (Fin.succ targetPosition)
                  | none => none) = some (Fin.succ resolvedTargetPos)
            rw [hInner]
          rw [liftBranchEq] at liftEq
          injection liftEq with someEq
          have priorEq :=
            renamingInjectsBack ⟨intermediateIndex, priorLt⟩
              resolvedTargetPos hInner
          rw [← someEq]
          show (⟨intermediateIndex + 1, intermediateIndexLt⟩
                : Fin (intermediateScope + 1)) =
              Fin.succ (forwardRenaming resolvedTargetPos)
          apply Fin.ext
          show intermediateIndex + 1 =
              (Fin.succ (forwardRenaming resolvedTargetPos)).val
          show intermediateIndex + 1 =
              (forwardRenaming resolvedTargetPos).val + 1
          exact congrArg (· + 1) (congrArg Fin.val priorEq)

/-! ### Inversion: a successful `partialRename?` recovers the body as
the forward-rename of the extracted result.

Generalised inversion of `RawTerm.partialRename?`: if the partial
rename succeeds on `body` AND the partial renaming is injective into
the image of `forwardRenaming` (every `some k` result identifies the
source position uniquely as `forwardRenaming k`), then `body` is the
syntactic forward-renaming of the extracted result.

The proof is a structural induction over `body` covering all 67
`RawTerm` constructors.  Each constructor's case follows one of five
mechanical patterns, all propext-clean:

* **Nullary** (`unit`, `boolTrue`, `boolFalse`, `natZero`, `listNil`,
  `optionNone`, `interval0`, `interval1`, `universeCode`): `injection
  success` then `rfl`.
* **Variable** (`var`): forward case-split on `partialRenaming
  position`, construct lift outcome, apply `renamingInjectsBack`.
* **One-child match-form** (~25 ctors like `lam`, `fst`, `natSucc`,
  ...): forward case-split on the child's `partialRename?` result,
  construct branch outcome via `show ...; rw [hChild]`, then `rw` at
  `success`, `injection`, recurse via the IH.
* **Multi-child via `Option.mapTwo` / `Option.mapThree`**: invoke
  `Option.mapTwo_eq_some` / `Option.mapThree_eq_some` to decompose into
  per-child `some` witnesses, recurse on each, reassemble.
* **Binder** (`lam`, `pathLam`, `piTyCode`, `sigmaTyCode`): same as
  match-form / mapTwo, but the inner IH is fed
  `forwardRenaming.lift`, `partialRenaming.lift`, and
  `lift_renamingInjectsBack renamingInjectsBack`.

Used by `RawTerm.unweaken?_imp_weaken` (the load-bearing inversion the
Step.transpReflBeta cd cascade needs to convert
`unweaken? body = some inner` into `body = inner.weaken`). -/
set_option linter.unusedVariables false in
theorem RawTerm.partialRename?_imp_rename :
    ∀ {sourceScope intermediateScope : Nat}
      (body : RawTerm intermediateScope)
      (forwardRenaming : RawRenaming sourceScope intermediateScope)
      (partialRenaming : PartialRawRenaming intermediateScope sourceScope)
      (renamingInjectsBack :
        ∀ (intermediatePos : Fin intermediateScope)
          (sourcePos : Fin sourceScope),
          partialRenaming intermediatePos = some sourcePos →
          intermediatePos = forwardRenaming sourcePos)
      (extracted : RawTerm sourceScope),
      RawTerm.partialRename? body partialRenaming = some extracted →
      body = extracted.rename forwardRenaming := by
  intro sourceScope intermediateScope body
  induction body generalizing sourceScope with
  | var position =>
      intro forwardRenaming partialRenaming renamingInjectsBack extracted success
      cases hRen : partialRenaming position with
      | none =>
          have eq :
              RawTerm.partialRename? (RawTerm.var position) partialRenaming =
              (none : Option (RawTerm sourceScope)) := by
            show (match partialRenaming position with
                  | some targetPosition => some (RawTerm.var targetPosition)
                  | none => none) = none
            rw [hRen]
          rw [eq] at success
          cases success
      | some targetPosition =>
          have eq :
              RawTerm.partialRename? (RawTerm.var position) partialRenaming =
              some (RawTerm.var targetPosition) := by
            show (match partialRenaming position with
                  | some targetPosition => some (RawTerm.var targetPosition)
                  | none => none) = some (RawTerm.var targetPosition)
            rw [hRen]
          rw [eq] at success
          injection success with eqExtracted
          rw [← eqExtracted]
          show RawTerm.var position =
              RawTerm.var (forwardRenaming targetPosition)
          have priorEq := renamingInjectsBack position targetPosition hRen
          rw [priorEq]
  | unit =>
      intro _ _ _ extracted success
      injection success with eqExtracted
      rw [← eqExtracted]; rfl
  | lam innerBody innerIH =>
      intro forwardRenaming partialRenaming renamingInjectsBack extracted success
      cases hInner : RawTerm.partialRename? innerBody partialRenaming.lift with
      | none =>
          have eq :
              RawTerm.partialRename? (RawTerm.lam innerBody) partialRenaming =
              (none : Option (RawTerm sourceScope)) := by
            show (match RawTerm.partialRename? innerBody partialRenaming.lift with
                  | some renamedBody => some (RawTerm.lam renamedBody)
                  | none => none) = none
            rw [hInner]
          rw [eq] at success
          cases success
      | some renamedInner =>
          have eq :
              RawTerm.partialRename? (RawTerm.lam innerBody) partialRenaming =
              some (RawTerm.lam renamedInner) := by
            show (match RawTerm.partialRename? innerBody partialRenaming.lift with
                  | some renamedBody => some (RawTerm.lam renamedBody)
                  | none => none) = some (RawTerm.lam renamedInner)
            rw [hInner]
          rw [eq] at success
          injection success with eqExtracted
          rw [← eqExtracted]
          show RawTerm.lam innerBody =
              RawTerm.lam (renamedInner.rename forwardRenaming.lift)
          rw [innerIH forwardRenaming.lift partialRenaming.lift
                (PartialRawRenaming.lift_renamingInjectsBack renamingInjectsBack)
                renamedInner hInner]
  | app functionTerm argumentTerm functionIH argumentIH =>
      intro forwardRenaming partialRenaming renamingInjectsBack extracted success
      obtain ⟨renamedFn, renamedArg, hFn, hArg, eqResult⟩ :=
        Option.mapTwo_eq_some success
      have eqFn :=
        functionIH forwardRenaming partialRenaming renamingInjectsBack
          renamedFn hFn
      have eqArg :=
        argumentIH forwardRenaming partialRenaming renamingInjectsBack
          renamedArg hArg
      rw [eqResult]
      show RawTerm.app functionTerm argumentTerm =
        RawTerm.app (renamedFn.rename forwardRenaming)
          (renamedArg.rename forwardRenaming)
      rw [eqFn, eqArg]
  | pair firstValue secondValue firstIH secondIH =>
      intro forwardRenaming partialRenaming renamingInjectsBack extracted success
      obtain ⟨r1, r2, h1, h2, eqResult⟩ := Option.mapTwo_eq_some success
      have e1 := firstIH forwardRenaming partialRenaming renamingInjectsBack r1 h1
      have e2 := secondIH forwardRenaming partialRenaming renamingInjectsBack r2 h2
      rw [eqResult]
      show RawTerm.pair firstValue secondValue =
        RawTerm.pair (r1.rename forwardRenaming) (r2.rename forwardRenaming)
      rw [e1, e2]
  | fst pairTerm pairIH =>
      intro forwardRenaming partialRenaming renamingInjectsBack extracted success
      cases hChild : RawTerm.partialRename? pairTerm partialRenaming with
      | none =>
          have eq :
              RawTerm.partialRename? (RawTerm.fst pairTerm) partialRenaming =
              (none : Option (RawTerm sourceScope)) := by
            show (match RawTerm.partialRename? pairTerm partialRenaming with
                  | some renamedPair => some (RawTerm.fst renamedPair)
                  | none => none) = none
            rw [hChild]
          rw [eq] at success
          cases success
      | some renamedPair =>
          have eq :
              RawTerm.partialRename? (RawTerm.fst pairTerm) partialRenaming =
              some (RawTerm.fst renamedPair) := by
            show (match RawTerm.partialRename? pairTerm partialRenaming with
                  | some renamedPair => some (RawTerm.fst renamedPair)
                  | none => none) = some (RawTerm.fst renamedPair)
            rw [hChild]
          rw [eq] at success
          injection success with eqExtracted
          rw [← eqExtracted]
          show RawTerm.fst pairTerm =
            RawTerm.fst (renamedPair.rename forwardRenaming)
          rw [pairIH forwardRenaming partialRenaming renamingInjectsBack
                renamedPair hChild]
  | snd pairTerm pairIH =>
      intro forwardRenaming partialRenaming renamingInjectsBack extracted success
      cases hChild : RawTerm.partialRename? pairTerm partialRenaming with
      | none =>
          have eq :
              RawTerm.partialRename? (RawTerm.snd pairTerm) partialRenaming =
              (none : Option (RawTerm sourceScope)) := by
            show (match RawTerm.partialRename? pairTerm partialRenaming with
                  | some renamedPair => some (RawTerm.snd renamedPair)
                  | none => none) = none
            rw [hChild]
          rw [eq] at success
          cases success
      | some renamedPair =>
          have eq :
              RawTerm.partialRename? (RawTerm.snd pairTerm) partialRenaming =
              some (RawTerm.snd renamedPair) := by
            show (match RawTerm.partialRename? pairTerm partialRenaming with
                  | some renamedPair => some (RawTerm.snd renamedPair)
                  | none => none) = some (RawTerm.snd renamedPair)
            rw [hChild]
          rw [eq] at success
          injection success with eqExtracted
          rw [← eqExtracted]
          show RawTerm.snd pairTerm =
            RawTerm.snd (renamedPair.rename forwardRenaming)
          rw [pairIH forwardRenaming partialRenaming renamingInjectsBack
                renamedPair hChild]
  | boolTrue =>
      intro _ _ _ extracted success
      injection success with eqExtracted
      rw [← eqExtracted]; rfl
  | boolFalse =>
      intro _ _ _ extracted success
      injection success with eqExtracted
      rw [← eqExtracted]; rfl
  | boolElim scrutinee thenBranch elseBranch scrutineeIH thenIH elseIH =>
      intro forwardRenaming partialRenaming renamingInjectsBack extracted success
      obtain ⟨rs, rt, re, hs, ht, he, eqResult⟩ :=
        Option.mapThree_eq_some success
      have eqs :=
        scrutineeIH forwardRenaming partialRenaming renamingInjectsBack rs hs
      have eqt :=
        thenIH forwardRenaming partialRenaming renamingInjectsBack rt ht
      have eqe :=
        elseIH forwardRenaming partialRenaming renamingInjectsBack re he
      rw [eqResult]
      show RawTerm.boolElim scrutinee thenBranch elseBranch =
        RawTerm.boolElim (rs.rename forwardRenaming)
          (rt.rename forwardRenaming) (re.rename forwardRenaming)
      rw [eqs, eqt, eqe]
  | natZero =>
      intro _ _ _ extracted success
      injection success with eqExtracted
      rw [← eqExtracted]; rfl
  | natSucc predecessor predecessorIH =>
      intro forwardRenaming partialRenaming renamingInjectsBack extracted success
      cases hChild : RawTerm.partialRename? predecessor partialRenaming with
      | none =>
          have eq :
              RawTerm.partialRename? (RawTerm.natSucc predecessor) partialRenaming =
              (none : Option (RawTerm sourceScope)) := by
            show (match RawTerm.partialRename? predecessor partialRenaming with
                  | some renamedPredecessor => some (RawTerm.natSucc renamedPredecessor)
                  | none => none) = none
            rw [hChild]
          rw [eq] at success
          cases success
      | some renamedPredecessor =>
          have eq :
              RawTerm.partialRename? (RawTerm.natSucc predecessor) partialRenaming =
              some (RawTerm.natSucc renamedPredecessor) := by
            show (match RawTerm.partialRename? predecessor partialRenaming with
                  | some renamedPredecessor => some (RawTerm.natSucc renamedPredecessor)
                  | none => none) = some (RawTerm.natSucc renamedPredecessor)
            rw [hChild]
          rw [eq] at success
          injection success with eqExtracted
          rw [← eqExtracted]
          show RawTerm.natSucc predecessor =
            RawTerm.natSucc (renamedPredecessor.rename forwardRenaming)
          rw [predecessorIH forwardRenaming partialRenaming
                renamingInjectsBack renamedPredecessor hChild]
  | natElim scrutinee zeroBranch succBranch scrutineeIH zeroIH succIH =>
      intro forwardRenaming partialRenaming renamingInjectsBack extracted success
      obtain ⟨rs, rz, rsucc, hs, hz, hsucc, eqResult⟩ :=
        Option.mapThree_eq_some success
      have eqs :=
        scrutineeIH forwardRenaming partialRenaming renamingInjectsBack rs hs
      have eqz :=
        zeroIH forwardRenaming partialRenaming renamingInjectsBack rz hz
      have eqsucc :=
        succIH forwardRenaming partialRenaming renamingInjectsBack rsucc hsucc
      rw [eqResult]
      show RawTerm.natElim scrutinee zeroBranch succBranch =
        RawTerm.natElim (rs.rename forwardRenaming)
          (rz.rename forwardRenaming) (rsucc.rename forwardRenaming)
      rw [eqs, eqz, eqsucc]
  | natRec scrutinee zeroBranch succBranch scrutineeIH zeroIH succIH =>
      intro forwardRenaming partialRenaming renamingInjectsBack extracted success
      obtain ⟨rs, rz, rsucc, hs, hz, hsucc, eqResult⟩ :=
        Option.mapThree_eq_some success
      have eqs :=
        scrutineeIH forwardRenaming partialRenaming renamingInjectsBack rs hs
      have eqz :=
        zeroIH forwardRenaming partialRenaming renamingInjectsBack rz hz
      have eqsucc :=
        succIH forwardRenaming partialRenaming renamingInjectsBack rsucc hsucc
      rw [eqResult]
      show RawTerm.natRec scrutinee zeroBranch succBranch =
        RawTerm.natRec (rs.rename forwardRenaming)
          (rz.rename forwardRenaming) (rsucc.rename forwardRenaming)
      rw [eqs, eqz, eqsucc]
  | listNil =>
      intro _ _ _ extracted success
      injection success with eqExtracted
      rw [← eqExtracted]; rfl
  | listCons headTerm tailTerm headIH tailIH =>
      intro forwardRenaming partialRenaming renamingInjectsBack extracted success
      obtain ⟨rh, rt, hh, ht, eqResult⟩ := Option.mapTwo_eq_some success
      have eh := headIH forwardRenaming partialRenaming renamingInjectsBack rh hh
      have et := tailIH forwardRenaming partialRenaming renamingInjectsBack rt ht
      rw [eqResult]
      show RawTerm.listCons headTerm tailTerm =
        RawTerm.listCons (rh.rename forwardRenaming) (rt.rename forwardRenaming)
      rw [eh, et]
  | listElim scrutinee nilBranch consBranch scrutineeIH nilIH consIH =>
      intro forwardRenaming partialRenaming renamingInjectsBack extracted success
      obtain ⟨rs, rn, rc, hs, hn, hc, eqResult⟩ :=
        Option.mapThree_eq_some success
      have eqs :=
        scrutineeIH forwardRenaming partialRenaming renamingInjectsBack rs hs
      have eqn :=
        nilIH forwardRenaming partialRenaming renamingInjectsBack rn hn
      have eqc :=
        consIH forwardRenaming partialRenaming renamingInjectsBack rc hc
      rw [eqResult]
      show RawTerm.listElim scrutinee nilBranch consBranch =
        RawTerm.listElim (rs.rename forwardRenaming)
          (rn.rename forwardRenaming) (rc.rename forwardRenaming)
      rw [eqs, eqn, eqc]
  | optionNone =>
      intro _ _ _ extracted success
      injection success with eqExtracted
      rw [← eqExtracted]; rfl
  | optionSome valueTerm valueIH =>
      intro forwardRenaming partialRenaming renamingInjectsBack extracted success
      cases hChild : RawTerm.partialRename? valueTerm partialRenaming with
      | none =>
          have eq :
              RawTerm.partialRename? (RawTerm.optionSome valueTerm)
                partialRenaming = (none : Option (RawTerm sourceScope)) := by
            show (match RawTerm.partialRename? valueTerm partialRenaming with
                  | some renamedValue => some (RawTerm.optionSome renamedValue)
                  | none => none) = none
            rw [hChild]
          rw [eq] at success
          cases success
      | some renamedValue =>
          have eq :
              RawTerm.partialRename? (RawTerm.optionSome valueTerm)
                partialRenaming = some (RawTerm.optionSome renamedValue) := by
            show (match RawTerm.partialRename? valueTerm partialRenaming with
                  | some renamedValue => some (RawTerm.optionSome renamedValue)
                  | none => none) = some (RawTerm.optionSome renamedValue)
            rw [hChild]
          rw [eq] at success
          injection success with eqExtracted
          rw [← eqExtracted]
          show RawTerm.optionSome valueTerm =
            RawTerm.optionSome (renamedValue.rename forwardRenaming)
          rw [valueIH forwardRenaming partialRenaming renamingInjectsBack
                renamedValue hChild]
  | optionMatch scrutinee noneBranch someBranch scrutineeIH noneIH someIH =>
      intro forwardRenaming partialRenaming renamingInjectsBack extracted success
      obtain ⟨rs, rn, rsome, hs, hn, hsome, eqResult⟩ :=
        Option.mapThree_eq_some success
      have eqs :=
        scrutineeIH forwardRenaming partialRenaming renamingInjectsBack rs hs
      have eqn :=
        noneIH forwardRenaming partialRenaming renamingInjectsBack rn hn
      have eqsome :=
        someIH forwardRenaming partialRenaming renamingInjectsBack rsome hsome
      rw [eqResult]
      show RawTerm.optionMatch scrutinee noneBranch someBranch =
        RawTerm.optionMatch (rs.rename forwardRenaming)
          (rn.rename forwardRenaming) (rsome.rename forwardRenaming)
      rw [eqs, eqn, eqsome]
  | eitherInl valueTerm valueIH =>
      intro forwardRenaming partialRenaming renamingInjectsBack extracted success
      cases hChild : RawTerm.partialRename? valueTerm partialRenaming with
      | none =>
          have eq :
              RawTerm.partialRename? (RawTerm.eitherInl valueTerm)
                partialRenaming = (none : Option (RawTerm sourceScope)) := by
            show (match RawTerm.partialRename? valueTerm partialRenaming with
                  | some renamedValue => some (RawTerm.eitherInl renamedValue)
                  | none => none) = none
            rw [hChild]
          rw [eq] at success
          cases success
      | some renamedValue =>
          have eq :
              RawTerm.partialRename? (RawTerm.eitherInl valueTerm)
                partialRenaming = some (RawTerm.eitherInl renamedValue) := by
            show (match RawTerm.partialRename? valueTerm partialRenaming with
                  | some renamedValue => some (RawTerm.eitherInl renamedValue)
                  | none => none) = some (RawTerm.eitherInl renamedValue)
            rw [hChild]
          rw [eq] at success
          injection success with eqExtracted
          rw [← eqExtracted]
          show RawTerm.eitherInl valueTerm =
            RawTerm.eitherInl (renamedValue.rename forwardRenaming)
          rw [valueIH forwardRenaming partialRenaming renamingInjectsBack
                renamedValue hChild]
  | eitherInr valueTerm valueIH =>
      intro forwardRenaming partialRenaming renamingInjectsBack extracted success
      cases hChild : RawTerm.partialRename? valueTerm partialRenaming with
      | none =>
          have eq :
              RawTerm.partialRename? (RawTerm.eitherInr valueTerm)
                partialRenaming = (none : Option (RawTerm sourceScope)) := by
            show (match RawTerm.partialRename? valueTerm partialRenaming with
                  | some renamedValue => some (RawTerm.eitherInr renamedValue)
                  | none => none) = none
            rw [hChild]
          rw [eq] at success
          cases success
      | some renamedValue =>
          have eq :
              RawTerm.partialRename? (RawTerm.eitherInr valueTerm)
                partialRenaming = some (RawTerm.eitherInr renamedValue) := by
            show (match RawTerm.partialRename? valueTerm partialRenaming with
                  | some renamedValue => some (RawTerm.eitherInr renamedValue)
                  | none => none) = some (RawTerm.eitherInr renamedValue)
            rw [hChild]
          rw [eq] at success
          injection success with eqExtracted
          rw [← eqExtracted]
          show RawTerm.eitherInr valueTerm =
            RawTerm.eitherInr (renamedValue.rename forwardRenaming)
          rw [valueIH forwardRenaming partialRenaming renamingInjectsBack
                renamedValue hChild]
  | eitherMatch scrutinee leftBranch rightBranch scrutineeIH leftIH rightIH =>
      intro forwardRenaming partialRenaming renamingInjectsBack extracted success
      obtain ⟨rs, rl, rr, hs, hl, hr, eqResult⟩ :=
        Option.mapThree_eq_some success
      have eqs :=
        scrutineeIH forwardRenaming partialRenaming renamingInjectsBack rs hs
      have eql :=
        leftIH forwardRenaming partialRenaming renamingInjectsBack rl hl
      have eqr :=
        rightIH forwardRenaming partialRenaming renamingInjectsBack rr hr
      rw [eqResult]
      show RawTerm.eitherMatch scrutinee leftBranch rightBranch =
        RawTerm.eitherMatch (rs.rename forwardRenaming)
          (rl.rename forwardRenaming) (rr.rename forwardRenaming)
      rw [eqs, eql, eqr]
  | refl rawWitness witnessIH =>
      intro forwardRenaming partialRenaming renamingInjectsBack extracted success
      cases hChild : RawTerm.partialRename? rawWitness partialRenaming with
      | none =>
          have eq :
              RawTerm.partialRename? (RawTerm.refl rawWitness)
                partialRenaming = (none : Option (RawTerm sourceScope)) := by
            show (match RawTerm.partialRename? rawWitness partialRenaming with
                  | some renamedWitness => some (RawTerm.refl renamedWitness)
                  | none => none) = none
            rw [hChild]
          rw [eq] at success
          cases success
      | some renamedWitness =>
          have eq :
              RawTerm.partialRename? (RawTerm.refl rawWitness)
                partialRenaming = some (RawTerm.refl renamedWitness) := by
            show (match RawTerm.partialRename? rawWitness partialRenaming with
                  | some renamedWitness => some (RawTerm.refl renamedWitness)
                  | none => none) = some (RawTerm.refl renamedWitness)
            rw [hChild]
          rw [eq] at success
          injection success with eqExtracted
          rw [← eqExtracted]
          show RawTerm.refl rawWitness =
            RawTerm.refl (renamedWitness.rename forwardRenaming)
          rw [witnessIH forwardRenaming partialRenaming renamingInjectsBack
                renamedWitness hChild]
  | idJ baseCase witness baseIH witnessIH =>
      intro forwardRenaming partialRenaming renamingInjectsBack extracted success
      obtain ⟨rb, rw, hb, hw, eqResult⟩ := Option.mapTwo_eq_some success
      have eqb := baseIH forwardRenaming partialRenaming renamingInjectsBack rb hb
      have eqw := witnessIH forwardRenaming partialRenaming renamingInjectsBack rw hw
      rw [eqResult]
      show RawTerm.idJ baseCase witness =
        RawTerm.idJ (rb.rename forwardRenaming) (rw.rename forwardRenaming)
      rw [eqb, eqw]
  | modIntro inner innerIH =>
      intro forwardRenaming partialRenaming renamingInjectsBack extracted success
      cases hChild : RawTerm.partialRename? inner partialRenaming with
      | none =>
          have eq :
              RawTerm.partialRename? (RawTerm.modIntro inner)
                partialRenaming = (none : Option (RawTerm sourceScope)) := by
            show (match RawTerm.partialRename? inner partialRenaming with
                  | some renamedRaw => some (RawTerm.modIntro renamedRaw)
                  | none => none) = none
            rw [hChild]
          rw [eq] at success
          cases success
      | some renamedRaw =>
          have eq :
              RawTerm.partialRename? (RawTerm.modIntro inner)
                partialRenaming = some (RawTerm.modIntro renamedRaw) := by
            show (match RawTerm.partialRename? inner partialRenaming with
                  | some renamedRaw => some (RawTerm.modIntro renamedRaw)
                  | none => none) = some (RawTerm.modIntro renamedRaw)
            rw [hChild]
          rw [eq] at success
          injection success with eqExtracted
          rw [← eqExtracted]
          show RawTerm.modIntro inner =
            RawTerm.modIntro (renamedRaw.rename forwardRenaming)
          rw [innerIH forwardRenaming partialRenaming renamingInjectsBack
                renamedRaw hChild]
  | modElim inner innerIH =>
      intro forwardRenaming partialRenaming renamingInjectsBack extracted success
      cases hChild : RawTerm.partialRename? inner partialRenaming with
      | none =>
          have eq :
              RawTerm.partialRename? (RawTerm.modElim inner)
                partialRenaming = (none : Option (RawTerm sourceScope)) := by
            show (match RawTerm.partialRename? inner partialRenaming with
                  | some renamedRaw => some (RawTerm.modElim renamedRaw)
                  | none => none) = none
            rw [hChild]
          rw [eq] at success
          cases success
      | some renamedRaw =>
          have eq :
              RawTerm.partialRename? (RawTerm.modElim inner)
                partialRenaming = some (RawTerm.modElim renamedRaw) := by
            show (match RawTerm.partialRename? inner partialRenaming with
                  | some renamedRaw => some (RawTerm.modElim renamedRaw)
                  | none => none) = some (RawTerm.modElim renamedRaw)
            rw [hChild]
          rw [eq] at success
          injection success with eqExtracted
          rw [← eqExtracted]
          show RawTerm.modElim inner =
            RawTerm.modElim (renamedRaw.rename forwardRenaming)
          rw [innerIH forwardRenaming partialRenaming renamingInjectsBack
                renamedRaw hChild]
  | subsume inner innerIH =>
      intro forwardRenaming partialRenaming renamingInjectsBack extracted success
      cases hChild : RawTerm.partialRename? inner partialRenaming with
      | none =>
          have eq :
              RawTerm.partialRename? (RawTerm.subsume inner)
                partialRenaming = (none : Option (RawTerm sourceScope)) := by
            show (match RawTerm.partialRename? inner partialRenaming with
                  | some renamedRaw => some (RawTerm.subsume renamedRaw)
                  | none => none) = none
            rw [hChild]
          rw [eq] at success
          cases success
      | some renamedRaw =>
          have eq :
              RawTerm.partialRename? (RawTerm.subsume inner)
                partialRenaming = some (RawTerm.subsume renamedRaw) := by
            show (match RawTerm.partialRename? inner partialRenaming with
                  | some renamedRaw => some (RawTerm.subsume renamedRaw)
                  | none => none) = some (RawTerm.subsume renamedRaw)
            rw [hChild]
          rw [eq] at success
          injection success with eqExtracted
          rw [← eqExtracted]
          show RawTerm.subsume inner =
            RawTerm.subsume (renamedRaw.rename forwardRenaming)
          rw [innerIH forwardRenaming partialRenaming renamingInjectsBack
                renamedRaw hChild]
  | interval0 =>
      intro _ _ _ extracted success
      injection success with eqExtracted
      rw [← eqExtracted]; rfl
  | interval1 =>
      intro _ _ _ extracted success
      injection success with eqExtracted
      rw [← eqExtracted]; rfl
  | intervalOpp intervalTerm intervalIH =>
      intro forwardRenaming partialRenaming renamingInjectsBack extracted success
      cases hChild : RawTerm.partialRename? intervalTerm partialRenaming with
      | none =>
          have eq :
              RawTerm.partialRename? (RawTerm.intervalOpp intervalTerm)
                partialRenaming = (none : Option (RawTerm sourceScope)) := by
            show (match RawTerm.partialRename? intervalTerm partialRenaming with
                  | some renamedInterval => some (RawTerm.intervalOpp renamedInterval)
                  | none => none) = none
            rw [hChild]
          rw [eq] at success
          cases success
      | some renamedInterval =>
          have eq :
              RawTerm.partialRename? (RawTerm.intervalOpp intervalTerm)
                partialRenaming = some (RawTerm.intervalOpp renamedInterval) := by
            show (match RawTerm.partialRename? intervalTerm partialRenaming with
                  | some renamedInterval => some (RawTerm.intervalOpp renamedInterval)
                  | none => none) = some (RawTerm.intervalOpp renamedInterval)
            rw [hChild]
          rw [eq] at success
          injection success with eqExtracted
          rw [← eqExtracted]
          show RawTerm.intervalOpp intervalTerm =
            RawTerm.intervalOpp (renamedInterval.rename forwardRenaming)
          rw [intervalIH forwardRenaming partialRenaming renamingInjectsBack
                renamedInterval hChild]
  | intervalMeet leftInterval rightInterval leftIH rightIH =>
      intro forwardRenaming partialRenaming renamingInjectsBack extracted success
      obtain ⟨rl, rr, hl, hr, eqResult⟩ := Option.mapTwo_eq_some success
      have eql := leftIH forwardRenaming partialRenaming renamingInjectsBack rl hl
      have eqr := rightIH forwardRenaming partialRenaming renamingInjectsBack rr hr
      rw [eqResult]
      show RawTerm.intervalMeet leftInterval rightInterval =
        RawTerm.intervalMeet (rl.rename forwardRenaming) (rr.rename forwardRenaming)
      rw [eql, eqr]
  | intervalJoin leftInterval rightInterval leftIH rightIH =>
      intro forwardRenaming partialRenaming renamingInjectsBack extracted success
      obtain ⟨rl, rr, hl, hr, eqResult⟩ := Option.mapTwo_eq_some success
      have eql := leftIH forwardRenaming partialRenaming renamingInjectsBack rl hl
      have eqr := rightIH forwardRenaming partialRenaming renamingInjectsBack rr hr
      rw [eqResult]
      show RawTerm.intervalJoin leftInterval rightInterval =
        RawTerm.intervalJoin (rl.rename forwardRenaming) (rr.rename forwardRenaming)
      rw [eql, eqr]
  | pathLam innerBody innerIH =>
      intro forwardRenaming partialRenaming renamingInjectsBack extracted success
      cases hInner : RawTerm.partialRename? innerBody partialRenaming.lift with
      | none =>
          have eq :
              RawTerm.partialRename? (RawTerm.pathLam innerBody)
                partialRenaming = (none : Option (RawTerm sourceScope)) := by
            show (match RawTerm.partialRename? innerBody partialRenaming.lift with
                  | some renamedBody => some (RawTerm.pathLam renamedBody)
                  | none => none) = none
            rw [hInner]
          rw [eq] at success
          cases success
      | some renamedInner =>
          have eq :
              RawTerm.partialRename? (RawTerm.pathLam innerBody)
                partialRenaming = some (RawTerm.pathLam renamedInner) := by
            show (match RawTerm.partialRename? innerBody partialRenaming.lift with
                  | some renamedBody => some (RawTerm.pathLam renamedBody)
                  | none => none) = some (RawTerm.pathLam renamedInner)
            rw [hInner]
          rw [eq] at success
          injection success with eqExtracted
          rw [← eqExtracted]
          show RawTerm.pathLam innerBody =
            RawTerm.pathLam (renamedInner.rename forwardRenaming.lift)
          rw [innerIH forwardRenaming.lift partialRenaming.lift
                (PartialRawRenaming.lift_renamingInjectsBack renamingInjectsBack)
                renamedInner hInner]
  | pathApp pathTerm intervalArg pathIH intervalIH =>
      intro forwardRenaming partialRenaming renamingInjectsBack extracted success
      obtain ⟨rp, ri, hp, hi, eqResult⟩ := Option.mapTwo_eq_some success
      have eqp := pathIH forwardRenaming partialRenaming renamingInjectsBack rp hp
      have eqi := intervalIH forwardRenaming partialRenaming renamingInjectsBack ri hi
      rw [eqResult]
      show RawTerm.pathApp pathTerm intervalArg =
        RawTerm.pathApp (rp.rename forwardRenaming) (ri.rename forwardRenaming)
      rw [eqp, eqi]
  | glueIntro baseValue partialValue baseIH partialIH =>
      intro forwardRenaming partialRenaming renamingInjectsBack extracted success
      obtain ⟨rb, rp, hb, hp, eqResult⟩ := Option.mapTwo_eq_some success
      have eqb := baseIH forwardRenaming partialRenaming renamingInjectsBack rb hb
      have eqp := partialIH forwardRenaming partialRenaming renamingInjectsBack rp hp
      rw [eqResult]
      show RawTerm.glueIntro baseValue partialValue =
        RawTerm.glueIntro (rb.rename forwardRenaming) (rp.rename forwardRenaming)
      rw [eqb, eqp]
  | glueElim gluedValue gluedIH =>
      intro forwardRenaming partialRenaming renamingInjectsBack extracted success
      cases hChild : RawTerm.partialRename? gluedValue partialRenaming with
      | none =>
          have eq :
              RawTerm.partialRename? (RawTerm.glueElim gluedValue)
                partialRenaming = (none : Option (RawTerm sourceScope)) := by
            show (match RawTerm.partialRename? gluedValue partialRenaming with
                  | some renamedGlued => some (RawTerm.glueElim renamedGlued)
                  | none => none) = none
            rw [hChild]
          rw [eq] at success
          cases success
      | some renamedGlued =>
          have eq :
              RawTerm.partialRename? (RawTerm.glueElim gluedValue)
                partialRenaming = some (RawTerm.glueElim renamedGlued) := by
            show (match RawTerm.partialRename? gluedValue partialRenaming with
                  | some renamedGlued => some (RawTerm.glueElim renamedGlued)
                  | none => none) = some (RawTerm.glueElim renamedGlued)
            rw [hChild]
          rw [eq] at success
          injection success with eqExtracted
          rw [← eqExtracted]
          show RawTerm.glueElim gluedValue =
            RawTerm.glueElim (renamedGlued.rename forwardRenaming)
          rw [gluedIH forwardRenaming partialRenaming renamingInjectsBack
                renamedGlued hChild]
  | transp path source pathIH sourceIH =>
      intro forwardRenaming partialRenaming renamingInjectsBack extracted success
      obtain ⟨rp, rs, hp, hs, eqResult⟩ := Option.mapTwo_eq_some success
      have eqp := pathIH forwardRenaming partialRenaming renamingInjectsBack rp hp
      have eqs := sourceIH forwardRenaming partialRenaming renamingInjectsBack rs hs
      rw [eqResult]
      show RawTerm.transp path source =
        RawTerm.transp (rp.rename forwardRenaming) (rs.rename forwardRenaming)
      rw [eqp, eqs]
  | hcomp sides cap sidesIH capIH =>
      intro forwardRenaming partialRenaming renamingInjectsBack extracted success
      obtain ⟨rsides, rcap, hsides, hcap, eqResult⟩ := Option.mapTwo_eq_some success
      have eqsides := sidesIH forwardRenaming partialRenaming renamingInjectsBack rsides hsides
      have eqcap := capIH forwardRenaming partialRenaming renamingInjectsBack rcap hcap
      rw [eqResult]
      show RawTerm.hcomp sides cap =
        RawTerm.hcomp (rsides.rename forwardRenaming) (rcap.rename forwardRenaming)
      rw [eqsides, eqcap]
  | oeqRefl witness witnessIH =>
      intro forwardRenaming partialRenaming renamingInjectsBack extracted success
      cases hChild : RawTerm.partialRename? witness partialRenaming with
      | none =>
          have eq :
              RawTerm.partialRename? (RawTerm.oeqRefl witness)
                partialRenaming = (none : Option (RawTerm sourceScope)) := by
            show (match RawTerm.partialRename? witness partialRenaming with
                  | some renamedWitness => some (RawTerm.oeqRefl renamedWitness)
                  | none => none) = none
            rw [hChild]
          rw [eq] at success
          cases success
      | some renamedWitness =>
          have eq :
              RawTerm.partialRename? (RawTerm.oeqRefl witness)
                partialRenaming = some (RawTerm.oeqRefl renamedWitness) := by
            show (match RawTerm.partialRename? witness partialRenaming with
                  | some renamedWitness => some (RawTerm.oeqRefl renamedWitness)
                  | none => none) = some (RawTerm.oeqRefl renamedWitness)
            rw [hChild]
          rw [eq] at success
          injection success with eqExtracted
          rw [← eqExtracted]
          show RawTerm.oeqRefl witness =
            RawTerm.oeqRefl (renamedWitness.rename forwardRenaming)
          rw [witnessIH forwardRenaming partialRenaming renamingInjectsBack
                renamedWitness hChild]
  | oeqJ baseCase witness baseIH witnessIH =>
      intro forwardRenaming partialRenaming renamingInjectsBack extracted success
      obtain ⟨rb, rw, hb, hw, eqResult⟩ := Option.mapTwo_eq_some success
      have eqb := baseIH forwardRenaming partialRenaming renamingInjectsBack rb hb
      have eqw := witnessIH forwardRenaming partialRenaming renamingInjectsBack rw hw
      rw [eqResult]
      show RawTerm.oeqJ baseCase witness =
        RawTerm.oeqJ (rb.rename forwardRenaming) (rw.rename forwardRenaming)
      rw [eqb, eqw]
  | oeqFunext pointwiseEquality pointwiseIH =>
      intro forwardRenaming partialRenaming renamingInjectsBack extracted success
      cases hChild : RawTerm.partialRename? pointwiseEquality partialRenaming with
      | none =>
          have eq :
              RawTerm.partialRename? (RawTerm.oeqFunext pointwiseEquality)
                partialRenaming = (none : Option (RawTerm sourceScope)) := by
            show (match RawTerm.partialRename? pointwiseEquality partialRenaming with
                  | some renamedPointwise => some (RawTerm.oeqFunext renamedPointwise)
                  | none => none) = none
            rw [hChild]
          rw [eq] at success
          cases success
      | some renamedPointwise =>
          have eq :
              RawTerm.partialRename? (RawTerm.oeqFunext pointwiseEquality)
                partialRenaming = some (RawTerm.oeqFunext renamedPointwise) := by
            show (match RawTerm.partialRename? pointwiseEquality partialRenaming with
                  | some renamedPointwise => some (RawTerm.oeqFunext renamedPointwise)
                  | none => none) = some (RawTerm.oeqFunext renamedPointwise)
            rw [hChild]
          rw [eq] at success
          injection success with eqExtracted
          rw [← eqExtracted]
          show RawTerm.oeqFunext pointwiseEquality =
            RawTerm.oeqFunext (renamedPointwise.rename forwardRenaming)
          rw [pointwiseIH forwardRenaming partialRenaming renamingInjectsBack
                renamedPointwise hChild]
  | idStrictRefl witness witnessIH =>
      intro forwardRenaming partialRenaming renamingInjectsBack extracted success
      cases hChild : RawTerm.partialRename? witness partialRenaming with
      | none =>
          have eq :
              RawTerm.partialRename? (RawTerm.idStrictRefl witness)
                partialRenaming = (none : Option (RawTerm sourceScope)) := by
            show (match RawTerm.partialRename? witness partialRenaming with
                  | some renamedWitness => some (RawTerm.idStrictRefl renamedWitness)
                  | none => none) = none
            rw [hChild]
          rw [eq] at success
          cases success
      | some renamedWitness =>
          have eq :
              RawTerm.partialRename? (RawTerm.idStrictRefl witness)
                partialRenaming = some (RawTerm.idStrictRefl renamedWitness) := by
            show (match RawTerm.partialRename? witness partialRenaming with
                  | some renamedWitness => some (RawTerm.idStrictRefl renamedWitness)
                  | none => none) = some (RawTerm.idStrictRefl renamedWitness)
            rw [hChild]
          rw [eq] at success
          injection success with eqExtracted
          rw [← eqExtracted]
          show RawTerm.idStrictRefl witness =
            RawTerm.idStrictRefl (renamedWitness.rename forwardRenaming)
          rw [witnessIH forwardRenaming partialRenaming renamingInjectsBack
                renamedWitness hChild]
  | idStrictRec baseCase witness baseIH witnessIH =>
      intro forwardRenaming partialRenaming renamingInjectsBack extracted success
      obtain ⟨rb, rw, hb, hw, eqResult⟩ := Option.mapTwo_eq_some success
      have eqb := baseIH forwardRenaming partialRenaming renamingInjectsBack rb hb
      have eqw := witnessIH forwardRenaming partialRenaming renamingInjectsBack rw hw
      rw [eqResult]
      show RawTerm.idStrictRec baseCase witness =
        RawTerm.idStrictRec (rb.rename forwardRenaming) (rw.rename forwardRenaming)
      rw [eqb, eqw]
  | equivIntro fwd bwd fwdIH bwdIH =>
      intro forwardRenaming partialRenaming renamingInjectsBack extracted success
      obtain ⟨rfwd, rbwd, hfwd, hbwd, eqResult⟩ := Option.mapTwo_eq_some success
      have eqfwd := fwdIH forwardRenaming partialRenaming renamingInjectsBack rfwd hfwd
      have eqbwd := bwdIH forwardRenaming partialRenaming renamingInjectsBack rbwd hbwd
      rw [eqResult]
      show RawTerm.equivIntro fwd bwd =
        RawTerm.equivIntro (rfwd.rename forwardRenaming) (rbwd.rename forwardRenaming)
      rw [eqfwd, eqbwd]
  | equivApp equivTerm argument equivIH argumentIH =>
      intro forwardRenaming partialRenaming renamingInjectsBack extracted success
      obtain ⟨reqv, rarg, heqv, harg, eqResult⟩ := Option.mapTwo_eq_some success
      have eqeqv := equivIH forwardRenaming partialRenaming renamingInjectsBack reqv heqv
      have eqarg := argumentIH forwardRenaming partialRenaming renamingInjectsBack rarg harg
      rw [eqResult]
      show RawTerm.equivApp equivTerm argument =
        RawTerm.equivApp (reqv.rename forwardRenaming) (rarg.rename forwardRenaming)
      rw [eqeqv, eqarg]
  | refineIntro rawValue predicateProof valueIH proofIH =>
      intro forwardRenaming partialRenaming renamingInjectsBack extracted success
      obtain ⟨rv, rp, hv, hp, eqResult⟩ := Option.mapTwo_eq_some success
      have eqv := valueIH forwardRenaming partialRenaming renamingInjectsBack rv hv
      have eqp := proofIH forwardRenaming partialRenaming renamingInjectsBack rp hp
      rw [eqResult]
      show RawTerm.refineIntro rawValue predicateProof =
        RawTerm.refineIntro (rv.rename forwardRenaming) (rp.rename forwardRenaming)
      rw [eqv, eqp]
  | refineElim refinedValue refinedIH =>
      intro forwardRenaming partialRenaming renamingInjectsBack extracted success
      cases hChild : RawTerm.partialRename? refinedValue partialRenaming with
      | none =>
          have eq :
              RawTerm.partialRename? (RawTerm.refineElim refinedValue)
                partialRenaming = (none : Option (RawTerm sourceScope)) := by
            show (match RawTerm.partialRename? refinedValue partialRenaming with
                  | some renamedRefined => some (RawTerm.refineElim renamedRefined)
                  | none => none) = none
            rw [hChild]
          rw [eq] at success
          cases success
      | some renamedRefined =>
          have eq :
              RawTerm.partialRename? (RawTerm.refineElim refinedValue)
                partialRenaming = some (RawTerm.refineElim renamedRefined) := by
            show (match RawTerm.partialRename? refinedValue partialRenaming with
                  | some renamedRefined => some (RawTerm.refineElim renamedRefined)
                  | none => none) = some (RawTerm.refineElim renamedRefined)
            rw [hChild]
          rw [eq] at success
          injection success with eqExtracted
          rw [← eqExtracted]
          show RawTerm.refineElim refinedValue =
            RawTerm.refineElim (renamedRefined.rename forwardRenaming)
          rw [refinedIH forwardRenaming partialRenaming renamingInjectsBack
                renamedRefined hChild]
  | recordIntro firstField fieldIH =>
      intro forwardRenaming partialRenaming renamingInjectsBack extracted success
      cases hChild : RawTerm.partialRename? firstField partialRenaming with
      | none =>
          have eq :
              RawTerm.partialRename? (RawTerm.recordIntro firstField)
                partialRenaming = (none : Option (RawTerm sourceScope)) := by
            show (match RawTerm.partialRename? firstField partialRenaming with
                  | some renamedField => some (RawTerm.recordIntro renamedField)
                  | none => none) = none
            rw [hChild]
          rw [eq] at success
          cases success
      | some renamedField =>
          have eq :
              RawTerm.partialRename? (RawTerm.recordIntro firstField)
                partialRenaming = some (RawTerm.recordIntro renamedField) := by
            show (match RawTerm.partialRename? firstField partialRenaming with
                  | some renamedField => some (RawTerm.recordIntro renamedField)
                  | none => none) = some (RawTerm.recordIntro renamedField)
            rw [hChild]
          rw [eq] at success
          injection success with eqExtracted
          rw [← eqExtracted]
          show RawTerm.recordIntro firstField =
            RawTerm.recordIntro (renamedField.rename forwardRenaming)
          rw [fieldIH forwardRenaming partialRenaming renamingInjectsBack
                renamedField hChild]
  | recordProj recordValue recordIH =>
      intro forwardRenaming partialRenaming renamingInjectsBack extracted success
      cases hChild : RawTerm.partialRename? recordValue partialRenaming with
      | none =>
          have eq :
              RawTerm.partialRename? (RawTerm.recordProj recordValue)
                partialRenaming = (none : Option (RawTerm sourceScope)) := by
            show (match RawTerm.partialRename? recordValue partialRenaming with
                  | some renamedRecord => some (RawTerm.recordProj renamedRecord)
                  | none => none) = none
            rw [hChild]
          rw [eq] at success
          cases success
      | some renamedRecord =>
          have eq :
              RawTerm.partialRename? (RawTerm.recordProj recordValue)
                partialRenaming = some (RawTerm.recordProj renamedRecord) := by
            show (match RawTerm.partialRename? recordValue partialRenaming with
                  | some renamedRecord => some (RawTerm.recordProj renamedRecord)
                  | none => none) = some (RawTerm.recordProj renamedRecord)
            rw [hChild]
          rw [eq] at success
          injection success with eqExtracted
          rw [← eqExtracted]
          show RawTerm.recordProj recordValue =
            RawTerm.recordProj (renamedRecord.rename forwardRenaming)
          rw [recordIH forwardRenaming partialRenaming renamingInjectsBack
                renamedRecord hChild]
  | codataUnfold initialState transition initialIH transitionIH =>
      intro forwardRenaming partialRenaming renamingInjectsBack extracted success
      obtain ⟨ri, rt, hi, ht, eqResult⟩ := Option.mapTwo_eq_some success
      have eqi := initialIH forwardRenaming partialRenaming renamingInjectsBack ri hi
      have eqt := transitionIH forwardRenaming partialRenaming renamingInjectsBack rt ht
      rw [eqResult]
      show RawTerm.codataUnfold initialState transition =
        RawTerm.codataUnfold (ri.rename forwardRenaming) (rt.rename forwardRenaming)
      rw [eqi, eqt]
  | codataDest codataValue codataIH =>
      intro forwardRenaming partialRenaming renamingInjectsBack extracted success
      cases hChild : RawTerm.partialRename? codataValue partialRenaming with
      | none =>
          have eq :
              RawTerm.partialRename? (RawTerm.codataDest codataValue)
                partialRenaming = (none : Option (RawTerm sourceScope)) := by
            show (match RawTerm.partialRename? codataValue partialRenaming with
                  | some renamedCodata => some (RawTerm.codataDest renamedCodata)
                  | none => none) = none
            rw [hChild]
          rw [eq] at success
          cases success
      | some renamedCodata =>
          have eq :
              RawTerm.partialRename? (RawTerm.codataDest codataValue)
                partialRenaming = some (RawTerm.codataDest renamedCodata) := by
            show (match RawTerm.partialRename? codataValue partialRenaming with
                  | some renamedCodata => some (RawTerm.codataDest renamedCodata)
                  | none => none) = some (RawTerm.codataDest renamedCodata)
            rw [hChild]
          rw [eq] at success
          injection success with eqExtracted
          rw [← eqExtracted]
          show RawTerm.codataDest codataValue =
            RawTerm.codataDest (renamedCodata.rename forwardRenaming)
          rw [codataIH forwardRenaming partialRenaming renamingInjectsBack
                renamedCodata hChild]
  | sessionSend channel payload channelIH payloadIH =>
      intro forwardRenaming partialRenaming renamingInjectsBack extracted success
      obtain ⟨rch, rpl, hch, hpl, eqResult⟩ := Option.mapTwo_eq_some success
      have eqch := channelIH forwardRenaming partialRenaming renamingInjectsBack rch hch
      have eqpl := payloadIH forwardRenaming partialRenaming renamingInjectsBack rpl hpl
      rw [eqResult]
      show RawTerm.sessionSend channel payload =
        RawTerm.sessionSend (rch.rename forwardRenaming) (rpl.rename forwardRenaming)
      rw [eqch, eqpl]
  | sessionRecv channel channelIH =>
      intro forwardRenaming partialRenaming renamingInjectsBack extracted success
      cases hChild : RawTerm.partialRename? channel partialRenaming with
      | none =>
          have eq :
              RawTerm.partialRename? (RawTerm.sessionRecv channel)
                partialRenaming = (none : Option (RawTerm sourceScope)) := by
            show (match RawTerm.partialRename? channel partialRenaming with
                  | some renamedChannel => some (RawTerm.sessionRecv renamedChannel)
                  | none => none) = none
            rw [hChild]
          rw [eq] at success
          cases success
      | some renamedChannel =>
          have eq :
              RawTerm.partialRename? (RawTerm.sessionRecv channel)
                partialRenaming = some (RawTerm.sessionRecv renamedChannel) := by
            show (match RawTerm.partialRename? channel partialRenaming with
                  | some renamedChannel => some (RawTerm.sessionRecv renamedChannel)
                  | none => none) = some (RawTerm.sessionRecv renamedChannel)
            rw [hChild]
          rw [eq] at success
          injection success with eqExtracted
          rw [← eqExtracted]
          show RawTerm.sessionRecv channel =
            RawTerm.sessionRecv (renamedChannel.rename forwardRenaming)
          rw [channelIH forwardRenaming partialRenaming renamingInjectsBack
                renamedChannel hChild]
  | effectPerform operationTag arguments operationIH argumentsIH =>
      intro forwardRenaming partialRenaming renamingInjectsBack extracted success
      obtain ⟨rop, rarg, hop, harg, eqResult⟩ := Option.mapTwo_eq_some success
      have eqop := operationIH forwardRenaming partialRenaming renamingInjectsBack rop hop
      have eqarg := argumentsIH forwardRenaming partialRenaming renamingInjectsBack rarg harg
      rw [eqResult]
      show RawTerm.effectPerform operationTag arguments =
        RawTerm.effectPerform (rop.rename forwardRenaming) (rarg.rename forwardRenaming)
      rw [eqop, eqarg]
  | universeCode innerLevel =>
      intro _ _ _ extracted success
      injection success with eqExtracted
      rw [← eqExtracted]; rfl
  | arrowCode domainCode codomainCode domainIH codomainIH =>
      intro forwardRenaming partialRenaming renamingInjectsBack extracted success
      obtain ⟨rd, rc, hd, hc, eqResult⟩ := Option.mapTwo_eq_some success
      have eqd := domainIH forwardRenaming partialRenaming renamingInjectsBack rd hd
      have eqc := codomainIH forwardRenaming partialRenaming renamingInjectsBack rc hc
      rw [eqResult]
      show RawTerm.arrowCode domainCode codomainCode =
        RawTerm.arrowCode (rd.rename forwardRenaming) (rc.rename forwardRenaming)
      rw [eqd, eqc]
  | piTyCode domainCode codomainCode domainIH codomainIH =>
      intro forwardRenaming partialRenaming renamingInjectsBack extracted success
      obtain ⟨rd, rc, hd, hc, eqResult⟩ := Option.mapTwo_eq_some success
      have eqd := domainIH forwardRenaming partialRenaming renamingInjectsBack rd hd
      have eqc := codomainIH forwardRenaming.lift partialRenaming.lift
                    (PartialRawRenaming.lift_renamingInjectsBack renamingInjectsBack)
                    rc hc
      rw [eqResult]
      show RawTerm.piTyCode domainCode codomainCode =
        RawTerm.piTyCode (rd.rename forwardRenaming) (rc.rename forwardRenaming.lift)
      rw [eqd, eqc]
  | sigmaTyCode domainCode codomainCode domainIH codomainIH =>
      intro forwardRenaming partialRenaming renamingInjectsBack extracted success
      obtain ⟨rd, rc, hd, hc, eqResult⟩ := Option.mapTwo_eq_some success
      have eqd := domainIH forwardRenaming partialRenaming renamingInjectsBack rd hd
      have eqc := codomainIH forwardRenaming.lift partialRenaming.lift
                    (PartialRawRenaming.lift_renamingInjectsBack renamingInjectsBack)
                    rc hc
      rw [eqResult]
      show RawTerm.sigmaTyCode domainCode codomainCode =
        RawTerm.sigmaTyCode (rd.rename forwardRenaming) (rc.rename forwardRenaming.lift)
      rw [eqd, eqc]
  | productCode firstCode secondCode firstIH secondIH =>
      intro forwardRenaming partialRenaming renamingInjectsBack extracted success
      obtain ⟨rf, rs, hf, hs, eqResult⟩ := Option.mapTwo_eq_some success
      have eqf := firstIH forwardRenaming partialRenaming renamingInjectsBack rf hf
      have eqs := secondIH forwardRenaming partialRenaming renamingInjectsBack rs hs
      rw [eqResult]
      show RawTerm.productCode firstCode secondCode =
        RawTerm.productCode (rf.rename forwardRenaming) (rs.rename forwardRenaming)
      rw [eqf, eqs]
  | sumCode leftCode rightCode leftIH rightIH =>
      intro forwardRenaming partialRenaming renamingInjectsBack extracted success
      obtain ⟨rl, rr, hl, hr, eqResult⟩ := Option.mapTwo_eq_some success
      have eql := leftIH forwardRenaming partialRenaming renamingInjectsBack rl hl
      have eqr := rightIH forwardRenaming partialRenaming renamingInjectsBack rr hr
      rw [eqResult]
      show RawTerm.sumCode leftCode rightCode =
        RawTerm.sumCode (rl.rename forwardRenaming) (rr.rename forwardRenaming)
      rw [eql, eqr]
  | listCode elementCode elementIH =>
      intro forwardRenaming partialRenaming renamingInjectsBack extracted success
      cases hChild : RawTerm.partialRename? elementCode partialRenaming with
      | none =>
          have eq :
              RawTerm.partialRename? (RawTerm.listCode elementCode)
                partialRenaming = (none : Option (RawTerm sourceScope)) := by
            show (match RawTerm.partialRename? elementCode partialRenaming with
                  | some renamedElement => some (RawTerm.listCode renamedElement)
                  | none => none) = none
            rw [hChild]
          rw [eq] at success
          cases success
      | some renamedElement =>
          have eq :
              RawTerm.partialRename? (RawTerm.listCode elementCode)
                partialRenaming = some (RawTerm.listCode renamedElement) := by
            show (match RawTerm.partialRename? elementCode partialRenaming with
                  | some renamedElement => some (RawTerm.listCode renamedElement)
                  | none => none) = some (RawTerm.listCode renamedElement)
            rw [hChild]
          rw [eq] at success
          injection success with eqExtracted
          rw [← eqExtracted]
          show RawTerm.listCode elementCode =
            RawTerm.listCode (renamedElement.rename forwardRenaming)
          rw [elementIH forwardRenaming partialRenaming renamingInjectsBack
                renamedElement hChild]
  | optionCode elementCode elementIH =>
      intro forwardRenaming partialRenaming renamingInjectsBack extracted success
      cases hChild : RawTerm.partialRename? elementCode partialRenaming with
      | none =>
          have eq :
              RawTerm.partialRename? (RawTerm.optionCode elementCode)
                partialRenaming = (none : Option (RawTerm sourceScope)) := by
            show (match RawTerm.partialRename? elementCode partialRenaming with
                  | some renamedElement => some (RawTerm.optionCode renamedElement)
                  | none => none) = none
            rw [hChild]
          rw [eq] at success
          cases success
      | some renamedElement =>
          have eq :
              RawTerm.partialRename? (RawTerm.optionCode elementCode)
                partialRenaming = some (RawTerm.optionCode renamedElement) := by
            show (match RawTerm.partialRename? elementCode partialRenaming with
                  | some renamedElement => some (RawTerm.optionCode renamedElement)
                  | none => none) = some (RawTerm.optionCode renamedElement)
            rw [hChild]
          rw [eq] at success
          injection success with eqExtracted
          rw [← eqExtracted]
          show RawTerm.optionCode elementCode =
            RawTerm.optionCode (renamedElement.rename forwardRenaming)
          rw [elementIH forwardRenaming partialRenaming renamingInjectsBack
                renamedElement hChild]
  | eitherCode leftCode rightCode leftIH rightIH =>
      intro forwardRenaming partialRenaming renamingInjectsBack extracted success
      obtain ⟨rl, rr, hl, hr, eqResult⟩ := Option.mapTwo_eq_some success
      have eql := leftIH forwardRenaming partialRenaming renamingInjectsBack rl hl
      have eqr := rightIH forwardRenaming partialRenaming renamingInjectsBack rr hr
      rw [eqResult]
      show RawTerm.eitherCode leftCode rightCode =
        RawTerm.eitherCode (rl.rename forwardRenaming) (rr.rename forwardRenaming)
      rw [eql, eqr]
  | idCode typeCode leftRaw rightRaw typeIH leftIH rightIH =>
      intro forwardRenaming partialRenaming renamingInjectsBack extracted success
      obtain ⟨rt, rl, rr, ht, hl, hr, eqResult⟩ := Option.mapThree_eq_some success
      have eqt := typeIH forwardRenaming partialRenaming renamingInjectsBack rt ht
      have eql := leftIH forwardRenaming partialRenaming renamingInjectsBack rl hl
      have eqr := rightIH forwardRenaming partialRenaming renamingInjectsBack rr hr
      rw [eqResult]
      show RawTerm.idCode typeCode leftRaw rightRaw =
        RawTerm.idCode (rt.rename forwardRenaming) (rl.rename forwardRenaming) (rr.rename forwardRenaming)
      rw [eqt, eql, eqr]
  | equivCode leftTypeCode rightTypeCode leftIH rightIH =>
      intro forwardRenaming partialRenaming renamingInjectsBack extracted success
      obtain ⟨rl, rr, hl, hr, eqResult⟩ := Option.mapTwo_eq_some success
      have eql := leftIH forwardRenaming partialRenaming renamingInjectsBack rl hl
      have eqr := rightIH forwardRenaming partialRenaming renamingInjectsBack rr hr
      rw [eqResult]
      show RawTerm.equivCode leftTypeCode rightTypeCode =
        RawTerm.equivCode (rl.rename forwardRenaming) (rr.rename forwardRenaming)
      rw [eql, eqr]
  | cumulUpMarker innerCodeRaw innerIH =>
      intro forwardRenaming partialRenaming renamingInjectsBack extracted success
      cases hChild : RawTerm.partialRename? innerCodeRaw partialRenaming with
      | none =>
          have eq :
              RawTerm.partialRename? (RawTerm.cumulUpMarker innerCodeRaw)
                partialRenaming = (none : Option (RawTerm sourceScope)) := by
            show (match RawTerm.partialRename? innerCodeRaw partialRenaming with
                  | some renamedInnerCode => some (RawTerm.cumulUpMarker renamedInnerCode)
                  | none => none) = none
            rw [hChild]
          rw [eq] at success
          cases success
      | some renamedInnerCode =>
          have eq :
              RawTerm.partialRename? (RawTerm.cumulUpMarker innerCodeRaw)
                partialRenaming = some (RawTerm.cumulUpMarker renamedInnerCode) := by
            show (match RawTerm.partialRename? innerCodeRaw partialRenaming with
                  | some renamedInnerCode => some (RawTerm.cumulUpMarker renamedInnerCode)
                  | none => none) = some (RawTerm.cumulUpMarker renamedInnerCode)
            rw [hChild]
          rw [eq] at success
          injection success with eqExtracted
          rw [← eqExtracted]
          show RawTerm.cumulUpMarker innerCodeRaw =
            RawTerm.cumulUpMarker (renamedInnerCode.rename forwardRenaming)
          rw [innerIH forwardRenaming partialRenaming renamingInjectsBack
                renamedInnerCode hChild]
  | uaToEquiv proofRaw proofIH =>
      intro forwardRenaming partialRenaming renamingInjectsBack extracted success
      cases hChild : RawTerm.partialRename? proofRaw partialRenaming with
      | none =>
          have eq :
              RawTerm.partialRename? (RawTerm.uaToEquiv proofRaw)
                partialRenaming = (none : Option (RawTerm sourceScope)) := by
            show (match RawTerm.partialRename? proofRaw partialRenaming with
                  | some renamedProof => some (RawTerm.uaToEquiv renamedProof)
                  | none => none) = none
            rw [hChild]
          rw [eq] at success
          cases success
      | some renamedProof =>
          have eq :
              RawTerm.partialRename? (RawTerm.uaToEquiv proofRaw)
                partialRenaming = some (RawTerm.uaToEquiv renamedProof) := by
            show (match RawTerm.partialRename? proofRaw partialRenaming with
                  | some renamedProof => some (RawTerm.uaToEquiv renamedProof)
                  | none => none) = some (RawTerm.uaToEquiv renamedProof)
            rw [hChild]
          rw [eq] at success
          injection success with eqExtracted
          rw [← eqExtracted]
          show RawTerm.uaToEquiv proofRaw =
            RawTerm.uaToEquiv (renamedProof.rename forwardRenaming)
          rw [proofIH forwardRenaming partialRenaming renamingInjectsBack
                renamedProof hChild]
  | equivApply equivRaw argRaw equivIH argIH =>
      intro forwardRenaming partialRenaming renamingInjectsBack extracted success
      obtain ⟨renamedEquiv, renamedArg, hEquiv, hArg, eqResult⟩ :=
        Option.mapTwo_eq_some success
      have eqEquiv :=
        equivIH forwardRenaming partialRenaming renamingInjectsBack
          renamedEquiv hEquiv
      have eqArg :=
        argIH forwardRenaming partialRenaming renamingInjectsBack
          renamedArg hArg
      rw [eqResult]
      show RawTerm.equivApply equivRaw argRaw =
        RawTerm.equivApply (renamedEquiv.rename forwardRenaming)
                           (renamedArg.rename forwardRenaming)
      rw [eqEquiv, eqArg]
  | pathCompose leftPathRaw rightPathRaw leftIH rightIH =>
      intro forwardRenaming partialRenaming renamingInjectsBack extracted success
      obtain ⟨renamedLeft, renamedRight, hLeft, hRight, eqResult⟩ :=
        Option.mapTwo_eq_some success
      have eqLeft :=
        leftIH forwardRenaming partialRenaming renamingInjectsBack
          renamedLeft hLeft
      have eqRight :=
        rightIH forwardRenaming partialRenaming renamingInjectsBack
          renamedRight hRight
      rw [eqResult]
      show RawTerm.pathCompose leftPathRaw rightPathRaw =
        RawTerm.pathCompose (renamedLeft.rename forwardRenaming)
                            (renamedRight.rename forwardRenaming)
      rw [eqLeft, eqRight]

/-! ### Specialization: `dropNewest` injects back into the image of
`RawRenaming.weaken`.

The hypothesis required by `partialRename?_imp_rename` for the
`dropNewest` partial renaming.  By definition: `dropNewest ⟨0, _⟩ =
none` (impossible-to-witness branch) and `dropNewest ⟨k+1, _⟩ =
some ⟨k, _⟩`, while `RawRenaming.weaken ⟨k, _⟩ = ⟨k+1, _⟩` via
`Fin.succ`.  Pattern-match on the `Fin (scope+1)` index, discharge
the impossible branch via `cases`, and chain `injection` + `rfl`. -/
theorem PartialRawRenaming.dropNewest_renamingInjectsBack {scope : Nat} :
    ∀ (intermediatePos : Fin (scope + 1)) (sourcePos : Fin scope),
      PartialRawRenaming.dropNewest intermediatePos = some sourcePos →
      intermediatePos = RawRenaming.weaken sourcePos
  | ⟨0, _⟩, _, h => by cases h
  | ⟨_ + 1, _⟩, _, h => by
      injection h with sourceEq
      rw [← sourceEq]
      rfl

/-- Inversion for `unweaken?`: a successful `unweaken?` recovers the
syntactic equation `body = extracted.weaken`.  The headline lemma the
Step.transpReflBeta cd cascade needs to convert an Option-match
witness into a definitional substitution equation.  Strict
specialization of `partialRename?_imp_rename` to the canonical
`(RawRenaming.weaken, PartialRawRenaming.dropNewest)` pair. -/
theorem RawTerm.unweaken?_imp_weaken {scope : Nat}
    (term : RawTerm (scope + 1)) (extracted : RawTerm scope)
    (success : term.unweaken? = some extracted) :
    term = extracted.weaken :=
  RawTerm.partialRename?_imp_rename term RawRenaming.weaken
    PartialRawRenaming.dropNewest
    PartialRawRenaming.dropNewest_renamingInjectsBack
    extracted success

end LeanFX2
