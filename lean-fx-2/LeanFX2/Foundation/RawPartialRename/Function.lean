import LeanFX2.Foundation.RawPartialRename.Helpers

/-! # LeanFX2.Foundation.RawPartialRename.Function

The big per-constructor `RawTerm.partialRename?` definition and its
two immediate specializations, `RawTerm.unweaken?` (lower across one
outer weakening) and `RawTerm.constantPathBody?` (recognize the raw
shape of a constant path).  These three definitions live together
because `unweaken?` / `constantPathBody?` are one-line wrappers built
on `partialRename?` and the whole block is consumed atomically by
the downstream inversion proofs.

## Root status

Kernel definitions; structural Option-valued recursion over the
67 `RawTerm` constructors.  No axioms. -/

namespace LeanFX2

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
  | _, _, .idToEquiv proofRaw, partialRenaming =>
      match RawTerm.partialRename? proofRaw partialRenaming with
      | some renamedProof => some (RawTerm.idToEquiv renamedProof)
      | none => none
  | _, _, .oeqTrans firstProof secondProof, partialRenaming =>
      Option.mapTwo
        (RawTerm.partialRename? firstProof partialRenaming)
        (RawTerm.partialRename? secondProof partialRenaming)
        RawTerm.oeqTrans
  | _, _, .equivCompose firstEquiv secondEquiv, partialRenaming =>
      Option.mapTwo
        (RawTerm.partialRename? firstEquiv partialRenaming)
        (RawTerm.partialRename? secondEquiv partialRenaming)
        RawTerm.equivCompose

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
  | RawTerm.idToEquiv _ => none
  | RawTerm.oeqTrans _ _ => none
  | RawTerm.equivCompose _ _ => none

end LeanFX2
