import LeanFX2.Foundation.RenameIdentity
import LeanFX2.Foundation.RawSubst

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

end LeanFX2
