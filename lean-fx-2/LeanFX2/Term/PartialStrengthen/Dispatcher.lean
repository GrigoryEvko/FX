import LeanFX2.Term.PartialStrengthen.Constructors.HeterogeneousEquivalence

/-! # Term/PartialStrengthen/Dispatcher

Universal typed partial-strengthening dispatcher over all `Term` constructors.
-/

namespace LeanFX2

namespace Term

/-- Universal typed partial strengthening dispatcher.

This is the public computational layer above the constructor-specific
certificates in this file.  It traverses a typed term once, recursively
strengthens the typed subterms, computes any schematic type/raw side
successes needed by value-shaped constructors, and delegates every
reconstruction step to the corresponding certificate.
-/
def partialStrengthenTyped? {mode : Mode} {level sourceScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {sourceType : Ty level sourceScope}
    {sourceRaw : RawTerm sourceScope}
    (sourceTerm : Term sourceCtx sourceType sourceRaw)
    {targetScope : Nat}
    {targetCtx : Ctx mode level targetScope}
    (strengthening : ContextStrengthening sourceCtx targetCtx) :
    Option (StrengtheningResult strengthening sourceTerm) :=
  match sourceTerm with
  | @Term.var _ _ _ _ position =>
      match survives : strengthening.back position with
      | none => none
      | some targetPosition =>
          some
            (partialStrengthenTypedVarOfSurvives strengthening position
              targetPosition survives)
  | @Term.unit _ _ _ _ => by
      exact some (partialStrengthenTypedUnit strengthening)
  | @Term.lam _ _ _ _ domainType codomainType _ body =>
      match domainSuccess :
          domainType.partialStrengthen? strengthening.back with
      | none => none
      | some targetDomainType =>
          match codomainSuccess :
              codomainType.partialStrengthen? strengthening.back with
          | none => none
          | some _ =>
              match
                  partialStrengthenTyped? body
                    (strengthening :=
                      strengthening.lift domainType targetDomainType
                        domainSuccess) with
              | none => none
              | some bodyResult =>
                  some
                    (partialStrengthenTypedLam domainSuccess
                      codomainSuccess bodyResult)
  | @Term.app _ _ _ _ domainType codomainType _ _ functionTerm
      argumentTerm =>
      match domainSuccess :
          domainType.partialStrengthen? strengthening.back with
      | none => none
      | some targetDomainType =>
          match codomainSuccess :
              codomainType.partialStrengthen? strengthening.back with
          | none => none
          | some targetCodomainType =>
              match functionRecurse :
                  partialStrengthenTyped? functionTerm
                    (strengthening := strengthening) with
              | none => none
              | some functionResult =>
                  match argumentRecurse :
                      partialStrengthenTyped? argumentTerm
                        (strengthening := strengthening) with
                  | none => none
                  | some argumentResult =>
                      some
                        (partialStrengthenTypedApp domainSuccess
                          codomainSuccess functionResult argumentResult)
  | @Term.lamPi _ _ _ _ domainType _ _ body =>
      match domainSuccess :
          domainType.partialStrengthen? strengthening.back with
      | none => none
      | some targetDomainType =>
          match
              partialStrengthenTyped? body
                (strengthening :=
                  strengthening.lift domainType targetDomainType
                    domainSuccess) with
          | none => none
          | some bodyResult =>
              some
                (partialStrengthenTypedLamPi domainSuccess bodyResult)
  | @Term.appPi _ _ _ _ domainType codomainType _ _ functionTerm
      argumentTerm =>
      match domainSuccess :
          domainType.partialStrengthen? strengthening.back with
      | none => none
      | some targetDomainType =>
          match codomainSuccess :
              codomainType.partialStrengthen? strengthening.back.lift with
          | none => none
          | some targetCodomainType =>
              match functionRecurse :
                  partialStrengthenTyped? functionTerm
                    (strengthening := strengthening) with
              | none => none
              | some functionResult =>
                  match argumentRecurse :
                      partialStrengthenTyped? argumentTerm
                        (strengthening := strengthening) with
                  | none => none
                  | some argumentResult =>
                      some
                        (partialStrengthenTypedAppPi domainSuccess
                          codomainSuccess functionResult argumentResult)
  | @Term.pair _ _ _ _ _ secondType _ _ firstValue secondValue =>
      match secondTypeSuccess :
          secondType.partialStrengthen? strengthening.back.lift with
      | none => none
      | some targetSecondType =>
          match firstRecurse :
              partialStrengthenTyped? firstValue
                (strengthening := strengthening) with
          | none => none
          | some firstResult =>
              match secondRecurse :
                  partialStrengthenTyped? secondValue
                    (strengthening := strengthening) with
              | none => none
              | some secondResult =>
                  some
                    (partialStrengthenTypedPair secondTypeSuccess
                      firstResult secondResult)
  | @Term.fst _ _ _ _ firstType secondType _ pairTerm =>
      match firstSuccess :
          firstType.partialStrengthen? strengthening.back with
      | none => none
      | some targetFirstType =>
          match secondSuccess :
              secondType.partialStrengthen? strengthening.back.lift with
          | none => none
          | some targetSecondType =>
              match pairRecurse :
                  partialStrengthenTyped? pairTerm
                    (strengthening := strengthening) with
              | none => none
              | some pairResult =>
                  some
                    (partialStrengthenTypedFst firstSuccess secondSuccess
                      pairResult)
  | @Term.snd _ _ _ _ firstType secondType _ pairTerm =>
      match firstSuccess :
          firstType.partialStrengthen? strengthening.back with
      | none => none
      | some targetFirstType =>
          match secondSuccess :
              secondType.partialStrengthen? strengthening.back.lift with
          | none => none
          | some targetSecondType =>
              match pairRecurse :
                  partialStrengthenTyped? pairTerm
                    (strengthening := strengthening) with
              | none => none
              | some pairResult =>
                  some
                    (partialStrengthenTypedSnd firstSuccess secondSuccess
                      pairResult)
  | @Term.boolTrue _ _ _ _ => by
      exact some (partialStrengthenTypedBoolTrue strengthening)
  | @Term.boolFalse _ _ _ _ => by
      exact some (partialStrengthenTypedBoolFalse strengthening)
  | @Term.boolElim _ _ _ _ motiveType _ _ _ scrutinee thenBranch
      elseBranch =>
      match motiveSuccess :
          motiveType.partialStrengthen? strengthening.back.lift with
      | none => none
      | some targetMotiveType =>
          match scrutineeRecurse :
              partialStrengthenTyped? scrutinee
                (strengthening := strengthening) with
          | none => none
          | some scrutineeResult =>
              match thenRecurse :
                  partialStrengthenTyped? thenBranch
                    (strengthening := strengthening) with
              | none => none
              | some thenResult =>
                  match elseRecurse :
                      partialStrengthenTyped? elseBranch
                        (strengthening := strengthening) with
                  | none => none
                  | some elseResult =>
                      some
                        (partialStrengthenTypedBoolElim motiveSuccess
                          scrutineeResult thenResult elseResult)
  | @Term.natZero _ _ _ _ => by
      exact some (partialStrengthenTypedNatZero strengthening)
  | @Term.natSucc _ _ _ _ _ predecessor =>
      match predecessorRecurse :
          partialStrengthenTyped? predecessor
            (strengthening := strengthening) with
      | none => none
      | some predecessorResult =>
          some (partialStrengthenTypedNatSucc predecessorResult)
  | @Term.natElim _ _ _ _ _ _ _ _ scrutinee zeroBranch succBranch =>
      match scrutineeRecurse :
          partialStrengthenTyped? scrutinee
            (strengthening := strengthening) with
      | none => none
      | some scrutineeResult =>
          match zeroRecurse :
              partialStrengthenTyped? zeroBranch
                (strengthening := strengthening) with
          | none => none
          | some zeroResult =>
              match succRecurse :
                  partialStrengthenTyped? succBranch
                    (strengthening := strengthening) with
              | none => none
              | some succResult =>
                  some
                    (partialStrengthenTypedNatElim scrutineeResult
                      zeroResult succResult)
  | @Term.natRec _ _ _ _ _ _ _ _ scrutinee zeroBranch succBranch =>
      match scrutineeRecurse :
          partialStrengthenTyped? scrutinee
            (strengthening := strengthening) with
      | none => none
      | some scrutineeResult =>
          match zeroRecurse :
              partialStrengthenTyped? zeroBranch
                (strengthening := strengthening) with
          | none => none
          | some zeroResult =>
              match succRecurse :
                  partialStrengthenTyped? succBranch
                    (strengthening := strengthening) with
              | none => none
              | some succResult =>
                  some
                    (partialStrengthenTypedNatRec scrutineeResult
                      zeroResult succResult)
  | @Term.listNil _ _ _ _ elementType =>
      match elementSuccess :
          elementType.partialStrengthen? strengthening.back with
      | none => none
      | some targetElementType =>
          some
            (partialStrengthenTypedListNilOfType strengthening
              elementType targetElementType elementSuccess)
  | @Term.listCons _ _ _ _ _ _ _ headTerm tailTerm =>
      match headRecurse :
          partialStrengthenTyped? headTerm
            (strengthening := strengthening) with
      | none => none
      | some headResult =>
          match tailRecurse :
              partialStrengthenTyped? tailTerm
                (strengthening := strengthening) with
          | none => none
          | some tailResult =>
              some (partialStrengthenTypedListCons headResult tailResult)
  | @Term.listElim _ _ _ _ elementType _ _ _ _ scrutinee nilBranch
      consBranch =>
      match elementSuccess :
          elementType.partialStrengthen? strengthening.back with
      | none => none
      | some targetElementType =>
          match scrutineeRecurse :
              partialStrengthenTyped? scrutinee
                (strengthening := strengthening) with
          | none => none
          | some scrutineeResult =>
              match nilRecurse :
                  partialStrengthenTyped? nilBranch
                    (strengthening := strengthening) with
              | none => none
              | some nilResult =>
                  match consRecurse :
                      partialStrengthenTyped? consBranch
                        (strengthening := strengthening) with
                  | none => none
                  | some consResult =>
                      some
                        (partialStrengthenTypedListElim elementSuccess
                          scrutineeResult nilResult consResult)
  | @Term.optionNone _ _ _ _ elementType =>
      match elementSuccess :
          elementType.partialStrengthen? strengthening.back with
      | none => none
      | some targetElementType =>
          some
            (partialStrengthenTypedOptionNoneOfType strengthening
              elementType targetElementType elementSuccess)
  | @Term.optionSome _ _ _ _ _ _ valueTerm =>
      match valueRecurse :
          partialStrengthenTyped? valueTerm
            (strengthening := strengthening) with
      | none => none
      | some valueResult =>
          some (partialStrengthenTypedOptionSome valueResult)
  | @Term.optionMatch _ _ _ _ elementType _ _ _ _ scrutinee noneBranch
      someBranch =>
      match elementSuccess :
          elementType.partialStrengthen? strengthening.back with
      | none => none
      | some targetElementType =>
          match scrutineeRecurse :
              partialStrengthenTyped? scrutinee
                (strengthening := strengthening) with
          | none => none
          | some scrutineeResult =>
              match noneRecurse :
                  partialStrengthenTyped? noneBranch
                    (strengthening := strengthening) with
              | none => none
              | some noneResult =>
                  match someRecurse :
                      partialStrengthenTyped? someBranch
                        (strengthening := strengthening) with
                  | none => none
                  | some someResult =>
                      some
                        (partialStrengthenTypedOptionMatch elementSuccess
                          scrutineeResult noneResult someResult)
  | @Term.eitherInl _ _ _ _ _ rightType _ valueTerm =>
      match rightSuccess :
          rightType.partialStrengthen? strengthening.back with
      | none => none
      | some targetRightType =>
          match valueRecurse :
              partialStrengthenTyped? valueTerm
                (strengthening := strengthening) with
          | none => none
          | some valueResult =>
              some
                (partialStrengthenTypedEitherInlOfRightType
                  rightSuccess valueResult)
  | @Term.eitherInr _ _ _ _ leftType _ _ valueTerm =>
      match leftSuccess :
          leftType.partialStrengthen? strengthening.back with
      | none => none
      | some targetLeftType =>
          match valueRecurse :
              partialStrengthenTyped? valueTerm
                (strengthening := strengthening) with
          | none => none
          | some valueResult =>
              some
                (partialStrengthenTypedEitherInrOfLeftType
                  leftSuccess valueResult)
  | @Term.eitherMatch _ _ _ _ leftType rightType motiveType _ _ _ scrutinee
      leftBranch rightBranch =>
      match leftSuccess :
          leftType.partialStrengthen? strengthening.back with
      | none => none
      | some targetLeftType =>
          match rightSuccess :
              rightType.partialStrengthen? strengthening.back with
          | none => none
          | some targetRightType =>
              match motiveSuccess :
                  motiveType.partialStrengthen? strengthening.back with
              | none => none
              | some targetMotiveType =>
                  match scrutineeRecurse :
                      partialStrengthenTyped? scrutinee
                        (strengthening := strengthening) with
                  | none => none
                  | some scrutineeResult =>
                      match leftRecurse :
                          partialStrengthenTyped? leftBranch
                            (strengthening := strengthening) with
                      | none => none
                      | some leftResult =>
                          match rightRecurse :
                              partialStrengthenTyped? rightBranch
                                (strengthening := strengthening) with
                          | none => none
                          | some rightResult =>
                              some
                                (partialStrengthenTypedEitherMatch leftSuccess
                                  rightSuccess motiveSuccess scrutineeResult
                                  leftResult rightResult)
  | @Term.refl _ _ _ _ carrier rawWitness =>
      match carrierSuccess :
          carrier.partialStrengthen? strengthening.back with
      | none => none
      | some targetCarrier =>
          match witnessSuccess :
              rawWitness.partialStrengthen? strengthening.back with
          | none => none
          | some targetWitness =>
              some (partialStrengthenTypedRefl carrierSuccess witnessSuccess)
  | @Term.idJ _ _ _ _ carrier leftEndpoint rightEndpoint _ _ _ baseCase
      witness =>
      match carrierSuccess :
          carrier.partialStrengthen? strengthening.back with
      | none => none
      | some targetCarrier =>
          match leftSuccess :
              leftEndpoint.partialStrengthen? strengthening.back with
          | none => none
          | some targetLeftEndpoint =>
              match rightSuccess :
                  rightEndpoint.partialStrengthen? strengthening.back with
              | none => none
              | some targetRightEndpoint =>
                  match baseRecurse :
                      partialStrengthenTyped? baseCase
                        (strengthening := strengthening) with
                  | none => none
                  | some baseResult =>
                      match witnessRecurse :
                          partialStrengthenTyped? witness
                            (strengthening := strengthening) with
                      | none => none
                      | some witnessResult =>
                          some
                            (partialStrengthenTypedIdJ carrierSuccess
                              leftSuccess rightSuccess baseResult
                              witnessResult)
  | @Term.oeqRefl _ _ _ _ carrier rawWitness =>
      match carrierSuccess :
          carrier.partialStrengthen? strengthening.back with
      | none => none
      | some targetCarrier =>
          match witnessSuccess :
              rawWitness.partialStrengthen? strengthening.back with
          | none => none
          | some targetWitness =>
              some
                (partialStrengthenTypedOeqRefl carrierSuccess witnessSuccess)
  | @Term.oeqJ _ _ _ _ carrier leftEndpoint rightEndpoint _ _ _ baseCase
      witness =>
      match carrierSuccess :
          carrier.partialStrengthen? strengthening.back with
      | none => none
      | some targetCarrier =>
          match leftSuccess :
              leftEndpoint.partialStrengthen? strengthening.back with
          | none => none
          | some targetLeftEndpoint =>
              match rightSuccess :
                  rightEndpoint.partialStrengthen? strengthening.back with
              | none => none
              | some targetRightEndpoint =>
                  match baseRecurse :
                      partialStrengthenTyped? baseCase
                        (strengthening := strengthening) with
                  | none => none
                  | some baseResult =>
                      match witnessRecurse :
                          partialStrengthenTyped? witness
                            (strengthening := strengthening) with
                      | none => none
                      | some witnessResult =>
                          some
                            (partialStrengthenTypedOeqJ carrierSuccess
                              leftSuccess rightSuccess baseResult
                              witnessResult)
  | @Term.oeqFunext _ _ _ _ domainType codomainType leftFunctionRaw
      rightFunctionRaw _ pointwiseProof =>
      match domainSuccess :
          domainType.partialStrengthen? strengthening.back with
      | none => none
      | some targetDomainType =>
          match codomainSuccess :
              codomainType.partialStrengthen? strengthening.back with
          | none => none
          | some targetCodomainType =>
              match leftSuccess :
                  leftFunctionRaw.partialStrengthen? strengthening.back with
              | none => none
              | some targetLeftFunctionRaw =>
                  match rightSuccess :
                      rightFunctionRaw.partialStrengthen?
                        strengthening.back with
                  | none => none
                  | some targetRightFunctionRaw =>
                      match pointwiseRecurse :
                          partialStrengthenTyped? pointwiseProof
                            (strengthening := strengthening) with
                      | none => none
                      | some pointwiseResult =>
                          some
                            (partialStrengthenTypedOeqFunext domainType
                              codomainType targetDomainType
                              targetCodomainType leftFunctionRaw
                              rightFunctionRaw targetLeftFunctionRaw
                              targetRightFunctionRaw domainSuccess
                              codomainSuccess leftSuccess rightSuccess
                              pointwiseResult)
  | @Term.idStrictRefl _ _ _ _ modeIsStrict carrier rawWitness =>
      match carrierSuccess :
          carrier.partialStrengthen? strengthening.back with
      | none => none
      | some targetCarrier =>
          match witnessSuccess :
              rawWitness.partialStrengthen? strengthening.back with
          | none => none
          | some targetWitness =>
              some
                (partialStrengthenTypedIdStrictRefl modeIsStrict
                  carrierSuccess witnessSuccess)
  | @Term.idStrictRec _ _ _ _ modeIsStrict carrier leftEndpoint
      rightEndpoint _ _ _ baseCase witness =>
      match carrierSuccess :
          carrier.partialStrengthen? strengthening.back with
      | none => none
      | some targetCarrier =>
          match leftSuccess :
              leftEndpoint.partialStrengthen? strengthening.back with
          | none => none
          | some targetLeftEndpoint =>
              match rightSuccess :
                  rightEndpoint.partialStrengthen? strengthening.back with
              | none => none
              | some targetRightEndpoint =>
                  match baseRecurse :
                      partialStrengthenTyped? baseCase
                        (strengthening := strengthening) with
                  | none => none
                  | some baseResult =>
                      match witnessRecurse :
                          partialStrengthenTyped? witness
                            (strengthening := strengthening) with
                      | none => none
                      | some witnessResult =>
                          some
                            (partialStrengthenTypedIdStrictRec modeIsStrict
                              carrierSuccess leftSuccess rightSuccess
                              baseResult witnessResult)
  | @Term.modIntro _ _ _ _ _ _ innerTerm =>
      match innerRecurse :
          partialStrengthenTyped? innerTerm
            (strengthening := strengthening) with
      | none => none
      | some innerResult =>
          some (partialStrengthenTypedModIntro innerResult)
  | @Term.modElim _ _ _ _ _ _ innerTerm =>
      match innerRecurse :
          partialStrengthenTyped? innerTerm
            (strengthening := strengthening) with
      | none => none
      | some innerResult =>
          some (partialStrengthenTypedModElim innerResult)
  | @Term.subsume _ _ _ _ _ _ innerTerm =>
      match innerRecurse :
          partialStrengthenTyped? innerTerm
            (strengthening := strengthening) with
      | none => none
      | some innerResult =>
          some (partialStrengthenTypedSubsume innerResult)
  | @Term.interval0 _ _ _ _ => by
      exact some (partialStrengthenTypedInterval0 strengthening)
  | @Term.interval1 _ _ _ _ => by
      exact some (partialStrengthenTypedInterval1 strengthening)
  | @Term.intervalOpp _ _ _ _ _ innerValue =>
      match innerRecurse :
          partialStrengthenTyped? innerValue
            (strengthening := strengthening) with
      | none => none
      | some innerResult =>
          some (partialStrengthenTypedIntervalOpp innerResult)
  | @Term.intervalMeet _ _ _ _ _ _ leftValue rightValue =>
      match leftRecurse :
          partialStrengthenTyped? leftValue
            (strengthening := strengthening) with
      | none => none
      | some leftResult =>
          match rightRecurse :
              partialStrengthenTyped? rightValue
                (strengthening := strengthening) with
          | none => none
          | some rightResult =>
              some (partialStrengthenTypedIntervalMeet leftResult rightResult)
  | @Term.intervalJoin _ _ _ _ _ _ leftValue rightValue =>
      match leftRecurse :
          partialStrengthenTyped? leftValue
            (strengthening := strengthening) with
      | none => none
      | some leftResult =>
          match rightRecurse :
              partialStrengthenTyped? rightValue
                (strengthening := strengthening) with
          | none => none
          | some rightResult =>
              some (partialStrengthenTypedIntervalJoin leftResult rightResult)
  | @Term.pathLam _ _ _ _ modeIsUnivalent carrierType leftEndpoint
      rightEndpoint _ body =>
      match carrierSuccess :
          carrierType.partialStrengthen? strengthening.back with
      | none => none
      | some targetCarrierType =>
          match leftSuccess :
              leftEndpoint.partialStrengthen? strengthening.back with
          | none => none
          | some targetLeftEndpoint =>
              match rightSuccess :
                  rightEndpoint.partialStrengthen? strengthening.back with
              | none => none
              | some targetRightEndpoint =>
                  match partialStrengthenTyped? body
                      (strengthening :=
                        strengthening.lift Ty.interval Ty.interval rfl) with
                  | none => none
                  | some bodyResult =>
                      some
                        (partialStrengthenTypedPathLam modeIsUnivalent
                          carrierSuccess leftSuccess rightSuccess bodyResult)
  | @Term.pathApp _ _ _ _ modeIsUnivalent carrierType leftEndpoint
      rightEndpoint _ _ pathTerm intervalTerm =>
      match carrierSuccess :
          carrierType.partialStrengthen? strengthening.back with
      | none => none
      | some targetCarrierType =>
          match leftSuccess :
              leftEndpoint.partialStrengthen? strengthening.back with
          | none => none
          | some targetLeftEndpoint =>
              match rightSuccess :
                  rightEndpoint.partialStrengthen? strengthening.back with
              | none => none
              | some targetRightEndpoint =>
                  match pathRecurse :
                      partialStrengthenTyped? pathTerm
                        (strengthening := strengthening) with
                  | none => none
                  | some pathResult =>
                      match intervalRecurse :
                          partialStrengthenTyped? intervalTerm
                            (strengthening := strengthening) with
                      | none => none
                      | some intervalResult =>
                          some
                            (partialStrengthenTypedPathApp modeIsUnivalent
                              carrierSuccess leftSuccess rightSuccess
                              pathResult intervalResult)
  | @Term.glueIntro _ _ _ _ modeIsUnivalent baseType boundaryWitness _ _
      baseValue partialValue =>
      match baseTypeSuccess :
          baseType.partialStrengthen? strengthening.back with
      | none => none
      | some targetBaseType =>
          match boundarySuccess :
              boundaryWitness.partialStrengthen? strengthening.back with
          | none => none
          | some targetBoundaryWitness =>
              match partialStrengthenTyped? baseValue
                  (strengthening := strengthening) with
              | none => none
              | some baseResult =>
                  match partialStrengthenTyped? partialValue
                      (strengthening := strengthening) with
                  | none => none
                  | some partialResult =>
                      some
                        (partialStrengthenTypedGlueIntro modeIsUnivalent
                          baseType targetBaseType boundaryWitness
                          targetBoundaryWitness baseTypeSuccess
                          boundarySuccess baseResult partialResult)
  | @Term.glueElim _ _ _ _ modeIsUnivalent baseType boundaryWitness _
      gluedValue =>
      match baseSuccess :
          baseType.partialStrengthen? strengthening.back with
      | none => none
      | some targetBaseType =>
          match boundarySuccess :
              boundaryWitness.partialStrengthen? strengthening.back with
          | none => none
          | some targetBoundaryWitness =>
              match gluedRecurse :
                  partialStrengthenTyped? gluedValue
                    (strengthening := strengthening) with
              | none => none
              | some gluedResult =>
                  some
                    (partialStrengthenTypedGlueElim modeIsUnivalent
                      baseSuccess boundarySuccess gluedResult)
  | @Term.transp _ _ _ _ modeIsUnivalent universeLevel universeLevelLt
      sourceType targetType sourceTypeRaw targetTypeRaw _ _ typePath
      sourceValue =>
      match sourceTypeSuccess :
          sourceType.partialStrengthen? strengthening.back with
      | none => none
      | some targetSourceType =>
          match targetTypeSuccess :
              targetType.partialStrengthen? strengthening.back with
          | none => none
          | some targetTargetType =>
              match sourceTypeRawSuccess :
                  sourceTypeRaw.partialStrengthen? strengthening.back with
              | none => none
              | some targetSourceTypeRaw =>
                  match targetTypeRawSuccess :
                      targetTypeRaw.partialStrengthen? strengthening.back with
                  | none => none
                  | some targetTargetTypeRaw =>
                      match pathRecurse :
                          partialStrengthenTyped? typePath
                            (strengthening := strengthening) with
                      | none => none
                      | some pathResult =>
                          match sourceRecurse :
                              partialStrengthenTyped? sourceValue
                                (strengthening := strengthening) with
                          | none => none
                          | some sourceResult =>
                              some
                                (partialStrengthenTypedTransp
                                  modeIsUnivalent universeLevel
                                  universeLevelLt sourceType targetType
                                  targetSourceType targetTargetType
                                  sourceTypeRaw targetTypeRaw
                                  targetSourceTypeRaw targetTargetTypeRaw
                                  sourceTypeSuccess targetTypeSuccess
                                  sourceTypeRawSuccess targetTypeRawSuccess
                                  pathResult sourceResult)
  | @Term.hcomp _ _ _ _ modeIsUnivalent _ _ _ sidesValue capValue =>
      match sidesRecurse :
          partialStrengthenTyped? sidesValue
            (strengthening := strengthening) with
      | none => none
      | some sidesResult =>
          match capRecurse :
              partialStrengthenTyped? capValue
                (strengthening := strengthening) with
          | none => none
          | some capResult =>
              some
                (partialStrengthenTypedHcomp modeIsUnivalent sidesResult
                  capResult)
  | @Term.hcompPath _ _ _ _ modeIsUnivalent carrierType leftEndpoint
      rightEndpoint _ _ sidesPath capValue =>
      match carrierSuccess :
          carrierType.partialStrengthen? strengthening.back with
      | none => none
      | some _ =>
          match leftSuccess :
              leftEndpoint.partialStrengthen? strengthening.back with
          | none => none
          | some _ =>
              match rightSuccess :
                  rightEndpoint.partialStrengthen? strengthening.back with
              | none => none
              | some _ =>
                  match sidesRecurse :
                      partialStrengthenTyped? sidesPath
                        (strengthening := strengthening) with
                  | none => none
                  | some sidesResult =>
                      match capRecurse :
                          partialStrengthenTyped? capValue
                            (strengthening := strengthening) with
                      | none => none
                      | some capResult =>
                          some
                            (partialStrengthenTypedHcompPath modeIsUnivalent
                              leftEndpoint rightEndpoint carrierSuccess
                              leftSuccess rightSuccess sidesResult capResult)
  | @Term.recordIntro _ _ _ _ _ _ firstField =>
      match fieldRecurse :
          partialStrengthenTyped? firstField
            (strengthening := strengthening) with
      | none => none
      | some fieldResult =>
          some (partialStrengthenTypedRecordIntro fieldResult)
  | @Term.recordProj _ _ _ _ singleFieldType _ recordValue =>
      match fieldSuccess :
          singleFieldType.partialStrengthen? strengthening.back with
      | none => none
      | some _ =>
          match recordRecurse :
              partialStrengthenTyped? recordValue
                (strengthening := strengthening) with
          | none => none
          | some recordResult =>
              some
                (partialStrengthenTypedRecordProj fieldSuccess recordResult)
  | @Term.refineIntro _ _ _ _ _ predicate _ _ baseValue predicateProof =>
      match predicateSuccess :
          predicate.partialStrengthen? strengthening.back.lift with
      | none => none
      | some _ =>
          match baseRecurse :
              partialStrengthenTyped? baseValue
                (strengthening := strengthening) with
          | none => none
          | some baseResult =>
              match proofRecurse :
                  partialStrengthenTyped? predicateProof
                    (strengthening := strengthening) with
              | none => none
              | some proofResult =>
                  some
                    (partialStrengthenTypedRefineIntro predicateSuccess
                      baseResult proofResult)
  | @Term.refineElim _ _ _ _ baseType predicate _ refinedValue =>
      match baseSuccess :
          baseType.partialStrengthen? strengthening.back with
      | none => none
      | some _ =>
          match predicateSuccess :
              predicate.partialStrengthen? strengthening.back.lift with
          | none => none
          | some _ =>
              match refinedRecurse :
                  partialStrengthenTyped? refinedValue
                    (strengthening := strengthening) with
              | none => none
              | some refinedResult =>
                  some
                    (partialStrengthenTypedRefineElim baseSuccess
                      predicateSuccess refinedResult)
  | @Term.codataUnfold _ _ _ _ _ outputType _ _ initialState transition =>
      match outputSuccess :
          outputType.partialStrengthen? strengthening.back with
      | none => none
      | some _ =>
          match stateRecurse :
              partialStrengthenTyped? initialState
                (strengthening := strengthening) with
          | none => none
          | some stateResult =>
              match transitionRecurse :
                  partialStrengthenTyped? transition
                    (strengthening := strengthening) with
              | none => none
              | some transitionResult =>
                  some
                    (partialStrengthenTypedCodataUnfold outputSuccess
                      stateResult transitionResult)
  | @Term.codataDest _ _ _ _ stateType outputType _ codataValue =>
      match stateSuccess :
          stateType.partialStrengthen? strengthening.back with
      | none => none
      | some _ =>
          match outputSuccess :
              outputType.partialStrengthen? strengthening.back with
          | none => none
          | some _ =>
              match codataRecurse :
                  partialStrengthenTyped? codataValue
                    (strengthening := strengthening) with
              | none => none
              | some codataResult =>
                  some
                    (partialStrengthenTypedCodataDest stateSuccess
                      outputSuccess codataResult)
  | @Term.sessionSend _ _ _ _ protocolStep _ _ _ channel payload =>
      match protocolSuccess :
          protocolStep.partialStrengthen? strengthening.back with
      | none => none
      | some _ =>
          match channelRecurse :
              partialStrengthenTyped? channel
                (strengthening := strengthening) with
          | none => none
          | some channelResult =>
              match payloadRecurse :
                  partialStrengthenTyped? payload
                    (strengthening := strengthening) with
              | none => none
              | some payloadResult =>
                  some
                    (partialStrengthenTypedSessionSend protocolSuccess
                      channelResult payloadResult)
  | @Term.sessionRecv _ _ _ _ protocolStep _ channel =>
      match protocolSuccess :
          protocolStep.partialStrengthen? strengthening.back with
      | none => none
      | some _ =>
          match channelRecurse :
              partialStrengthenTyped? channel
                (strengthening := strengthening) with
          | none => none
          | some channelResult =>
              some
                (partialStrengthenTypedSessionRecv protocolSuccess
                  channelResult)
  | @Term.effectPerform _ _ _ _ effectTag effectRow operationSignature
      canPerformOperation _ _ operationTag arguments =>
      match effectTagSuccess :
          effectTag.partialStrengthen? strengthening.back with
      | none => none
      | some targetEffectTag =>
          match argumentCarrierSuccess :
              operationSignature.argumentCarrier.partialStrengthen?
                strengthening.back with
          | none => none
          | some targetArgumentCarrier =>
              match resultCarrierSuccess :
                  operationSignature.resultCarrier.partialStrengthen?
                    strengthening.back with
              | none => none
              | some targetResultCarrier =>
                  match partialStrengthenTyped? operationTag
                      (strengthening := strengthening) with
                  | none => none
                  | some operationResult =>
                      match partialStrengthenTyped? arguments
                          (strengthening := strengthening) with
                      | none => none
                      | some argumentsResult =>
                          some
                            (partialStrengthenTypedEffectPerform effectTag
                              targetEffectTag effectRow operationSignature
                              targetArgumentCarrier targetResultCarrier
                              canPerformOperation effectTagSuccess
                              argumentCarrierSuccess resultCarrierSuccess
                              operationResult argumentsResult)
  | @Term.universeCode _ _ _ _ innerLevel outerLevel cumulOk levelLe =>
      some
        (partialStrengthenTypedUniverseCode strengthening innerLevel
          outerLevel cumulOk levelLe)
  | @Term.cumulUp _ _ _ _ lowerLevel higherLevel cumulMonotone levelLeLow
      levelLeHigh _ typeCode =>
      match codeRecurse :
          partialStrengthenTyped? typeCode
            (strengthening := strengthening) with
      | none => none
      | some codeResult =>
          some
            (partialStrengthenTypedCumulUp lowerLevel higherLevel
              cumulMonotone levelLeLow levelLeHigh codeResult)
  | @Term.equivReflId _ _ _ _ carrier =>
      match carrierSuccess :
          carrier.partialStrengthen? strengthening.back with
      | none => none
      | some targetCarrier =>
          some
            (partialStrengthenTypedEquivReflId carrier targetCarrier
              carrierSuccess)
  | @Term.funextRefl _ _ _ _ domainType codomainType applyRaw =>
      match domainSuccess :
          domainType.partialStrengthen? strengthening.back with
      | none => none
      | some targetDomainType =>
          match codomainSuccess :
              codomainType.partialStrengthen? strengthening.back with
          | none => none
          | some targetCodomainType =>
              match applySuccess :
                  applyRaw.partialStrengthen? strengthening.back.lift with
              | none => none
              | some targetApplyRaw =>
                  some
                    (partialStrengthenTypedFunextRefl domainType
                      codomainType targetDomainType targetCodomainType
                      applyRaw targetApplyRaw domainSuccess
                      codomainSuccess applySuccess)
  | @Term.equivReflIdAtId _ _ _ _ innerLevel innerLevelLt carrier
      carrierRaw =>
      match carrierSuccess :
          carrier.partialStrengthen? strengthening.back with
      | none => none
      | some targetCarrier =>
          match carrierRawSuccess :
              carrierRaw.partialStrengthen? strengthening.back with
          | none => none
          | some targetCarrierRaw =>
              some
                (partialStrengthenTypedEquivReflIdAtId innerLevel
                  innerLevelLt carrier targetCarrier carrierRaw
                  targetCarrierRaw carrierSuccess carrierRawSuccess)
  | @Term.funextReflAtId _ _ _ _ domainType codomainType applyRaw =>
      match domainSuccess :
          domainType.partialStrengthen? strengthening.back with
      | none => none
      | some targetDomainType =>
          match codomainSuccess :
              codomainType.partialStrengthen? strengthening.back with
          | none => none
          | some targetCodomainType =>
              match applySuccess :
                  applyRaw.partialStrengthen? strengthening.back.lift with
              | none => none
              | some targetApplyRaw =>
                  some
                    (partialStrengthenTypedFunextReflAtId domainType
                      codomainType targetDomainType targetCodomainType
                      applyRaw targetApplyRaw domainSuccess
                      codomainSuccess applySuccess)
  | @Term.equivIntroHet _ _ _ _ carrierA carrierB _ _ _ _ forward backward
      leftInv rightInv =>
      match carrierASuccess :
          carrierA.partialStrengthen? strengthening.back with
      | none => none
      | some _ =>
          match carrierBSuccess :
              carrierB.partialStrengthen? strengthening.back with
          | none => none
          | some _ =>
              match forwardRecurse :
                  partialStrengthenTyped? forward
                    (strengthening := strengthening) with
              | none => none
              | some forwardResult =>
                  match backwardRecurse :
                      partialStrengthenTyped? backward
                        (strengthening := strengthening) with
                  | none => none
                  | some backwardResult =>
                      match leftInvRecurse :
                          partialStrengthenTyped? leftInv
                            (strengthening := strengthening) with
                      | none => none
                      | some leftInvResult =>
                          match rightInvRecurse :
                              partialStrengthenTyped? rightInv
                                (strengthening := strengthening) with
                          | none => none
                          | some rightInvResult =>
                              some
                                (partialStrengthenTypedEquivIntroHet
                                  carrierASuccess carrierBSuccess
                                  forwardResult backwardResult leftInvResult
                                  rightInvResult)
  | @Term.equivApp _ _ _ _ carrierA carrierB _ _ equivTerm argumentTerm =>
      match carrierASuccess :
          carrierA.partialStrengthen? strengthening.back with
      | none => none
      | some _ =>
          match carrierBSuccess :
              carrierB.partialStrengthen? strengthening.back with
          | none => none
          | some _ =>
              match equivRecurse :
                  partialStrengthenTyped? equivTerm
                    (strengthening := strengthening) with
              | none => none
              | some equivResult =>
                  match argumentRecurse :
                      partialStrengthenTyped? argumentTerm
                        (strengthening := strengthening) with
                  | none => none
                  | some argumentResult =>
                      some
                        (partialStrengthenTypedEquivApp carrierASuccess
                          carrierBSuccess equivResult argumentResult)
  | @Term.uaIntroHet _ _ _ _ innerLevel innerLevelLt carrierA carrierB
      carrierARaw carrierBRaw forwardRaw backwardRaw equivWitness =>
      match carrierASuccess :
          carrierA.partialStrengthen? strengthening.back with
      | none => none
      | some targetCarrierA =>
          match carrierBSuccess :
              carrierB.partialStrengthen? strengthening.back with
          | none => none
          | some targetCarrierB =>
              match carrierARawSuccess :
                  carrierARaw.partialStrengthen? strengthening.back with
              | none => none
              | some targetCarrierARaw =>
                  match carrierBRawSuccess :
                      carrierBRaw.partialStrengthen? strengthening.back with
                  | none => none
                  | some targetCarrierBRaw =>
                      match forwardRawSuccess :
                          forwardRaw.partialStrengthen?
                            strengthening.back with
                      | none => none
                      | some targetForwardRaw =>
                          match backwardRawSuccess :
                              backwardRaw.partialStrengthen?
                                strengthening.back with
                          | none => none
                          | some targetBackwardRaw =>
                              match equivRecurse :
                                  partialStrengthenTyped? equivWitness
                                    (strengthening := strengthening) with
                              | none => none
                              | some equivResult =>
                                  some
                                    (partialStrengthenTypedUaIntroHet
                                      innerLevel innerLevelLt targetCarrierA
                                      targetCarrierB carrierARaw carrierBRaw
                                      targetCarrierARaw targetCarrierBRaw
                                      targetForwardRaw targetBackwardRaw
                                      carrierASuccess carrierBSuccess
                                      carrierARawSuccess carrierBRawSuccess
                                      forwardRawSuccess backwardRawSuccess
                                      equivResult)
  | @Term.funextIntroHet _ _ _ _ domainType codomainType applyARaw
      applyBRaw =>
      match domainSuccess :
          domainType.partialStrengthen? strengthening.back with
      | none => none
      | some targetDomainType =>
          match codomainSuccess :
              codomainType.partialStrengthen? strengthening.back with
          | none => none
          | some targetCodomainType =>
              match applyASuccess :
                  applyARaw.partialStrengthen? strengthening.back.lift with
              | none => none
              | some targetApplyARaw =>
                  match applyBSuccess :
                      applyBRaw.partialStrengthen? strengthening.back.lift with
                  | none => none
                  | some targetApplyBRaw =>
                      some
                        (partialStrengthenTypedFunextIntroHet domainType
                          codomainType targetDomainType targetCodomainType
                          applyARaw applyBRaw targetApplyARaw
                          targetApplyBRaw domainSuccess codomainSuccess
                          applyASuccess applyBSuccess)
  | @Term.arrowCode _ _ _ _ outerLevel levelLe domainCodeRaw
      codomainCodeRaw =>
      match domainSuccess :
          domainCodeRaw.partialStrengthen? strengthening.back with
      | none => none
      | some targetDomainCodeRaw =>
          match codomainSuccess :
              codomainCodeRaw.partialStrengthen? strengthening.back with
          | none => none
          | some targetCodomainCodeRaw =>
              some
                (partialStrengthenTypedArrowCode outerLevel levelLe
                  domainCodeRaw codomainCodeRaw targetDomainCodeRaw
                  targetCodomainCodeRaw domainSuccess codomainSuccess)
  | @Term.piTyCode _ _ _ _ outerLevel levelLe domainCodeRaw
      codomainCodeRaw =>
      match domainSuccess :
          domainCodeRaw.partialStrengthen? strengthening.back with
      | none => none
      | some targetDomainCodeRaw =>
          match codomainSuccess :
              codomainCodeRaw.partialStrengthen? strengthening.back.lift with
          | none => none
          | some targetCodomainCodeRaw =>
              some
                (partialStrengthenTypedPiTyCode outerLevel levelLe
                  domainCodeRaw codomainCodeRaw targetDomainCodeRaw
                  targetCodomainCodeRaw domainSuccess codomainSuccess)
  | @Term.sigmaTyCode _ _ _ _ outerLevel levelLe domainCodeRaw
      codomainCodeRaw =>
      match domainSuccess :
          domainCodeRaw.partialStrengthen? strengthening.back with
      | none => none
      | some targetDomainCodeRaw =>
          match codomainSuccess :
              codomainCodeRaw.partialStrengthen? strengthening.back.lift with
          | none => none
          | some targetCodomainCodeRaw =>
              some
                (partialStrengthenTypedSigmaTyCode outerLevel levelLe
                  domainCodeRaw codomainCodeRaw targetDomainCodeRaw
                  targetCodomainCodeRaw domainSuccess codomainSuccess)
  | @Term.productCode _ _ _ _ outerLevel levelLe firstCodeRaw
      secondCodeRaw =>
      match firstSuccess :
          firstCodeRaw.partialStrengthen? strengthening.back with
      | none => none
      | some targetFirstCodeRaw =>
          match secondSuccess :
              secondCodeRaw.partialStrengthen? strengthening.back with
          | none => none
          | some targetSecondCodeRaw =>
              some
                (partialStrengthenTypedProductCode outerLevel levelLe
                  firstCodeRaw secondCodeRaw targetFirstCodeRaw
                  targetSecondCodeRaw firstSuccess secondSuccess)
  | @Term.sumCode _ _ _ _ outerLevel levelLe leftCodeRaw rightCodeRaw =>
      match leftSuccess :
          leftCodeRaw.partialStrengthen? strengthening.back with
      | none => none
      | some targetLeftCodeRaw =>
          match rightSuccess :
              rightCodeRaw.partialStrengthen? strengthening.back with
          | none => none
          | some targetRightCodeRaw =>
              some
                (partialStrengthenTypedSumCode outerLevel levelLe
                  leftCodeRaw rightCodeRaw targetLeftCodeRaw
                  targetRightCodeRaw leftSuccess rightSuccess)
  | @Term.listCode _ _ _ _ outerLevel levelLe elementCodeRaw =>
      match elementSuccess :
          elementCodeRaw.partialStrengthen? strengthening.back with
      | none => none
      | some targetElementCodeRaw =>
          some
            (partialStrengthenTypedListCode outerLevel levelLe
              elementCodeRaw targetElementCodeRaw elementSuccess)
  | @Term.optionCode _ _ _ _ outerLevel levelLe elementCodeRaw =>
      match elementSuccess :
          elementCodeRaw.partialStrengthen? strengthening.back with
      | none => none
      | some targetElementCodeRaw =>
          some
            (partialStrengthenTypedOptionCode outerLevel levelLe
              elementCodeRaw targetElementCodeRaw elementSuccess)
  | @Term.eitherCode _ _ _ _ outerLevel levelLe leftCodeRaw rightCodeRaw =>
      match leftSuccess :
          leftCodeRaw.partialStrengthen? strengthening.back with
      | none => none
      | some targetLeftCodeRaw =>
          match rightSuccess :
              rightCodeRaw.partialStrengthen? strengthening.back with
          | none => none
          | some targetRightCodeRaw =>
              some
                (partialStrengthenTypedEitherCode outerLevel levelLe
                  leftCodeRaw rightCodeRaw targetLeftCodeRaw
                  targetRightCodeRaw leftSuccess rightSuccess)
  | @Term.idCode _ _ _ _ outerLevel levelLe typeCodeRaw leftRaw rightRaw =>
      match typeSuccess :
          typeCodeRaw.partialStrengthen? strengthening.back with
      | none => none
      | some targetTypeCodeRaw =>
          match leftSuccess :
              leftRaw.partialStrengthen? strengthening.back with
          | none => none
          | some targetLeftRaw =>
              match rightSuccess :
                  rightRaw.partialStrengthen? strengthening.back with
              | none => none
              | some targetRightRaw =>
                  some
                    (partialStrengthenTypedIdCode outerLevel levelLe
                      typeCodeRaw leftRaw rightRaw targetTypeCodeRaw
                      targetLeftRaw targetRightRaw typeSuccess leftSuccess
                      rightSuccess)
  | @Term.equivCode _ _ _ _ outerLevel levelLe leftTypeCodeRaw
      rightTypeCodeRaw =>
      match leftSuccess :
          leftTypeCodeRaw.partialStrengthen? strengthening.back with
      | none => none
      | some targetLeftTypeCodeRaw =>
          match rightSuccess :
              rightTypeCodeRaw.partialStrengthen? strengthening.back with
          | none => none
          | some targetRightTypeCodeRaw =>
              some
                (partialStrengthenTypedEquivCode outerLevel levelLe
                  leftTypeCodeRaw rightTypeCodeRaw targetLeftTypeCodeRaw
                  targetRightTypeCodeRaw leftSuccess rightSuccess)
  | @Term.uaToEquiv _ _ _ _ innerLevel innerLevelLt leftTy rightTy
      leftTyRaw rightTyRaw _ proof =>
      match leftTySuccess :
          leftTy.partialStrengthen? strengthening.back with
      | none => none
      | some targetLeftTy =>
          match rightTySuccess :
              rightTy.partialStrengthen? strengthening.back with
          | none => none
          | some targetRightTy =>
              match leftRawSuccess :
                  leftTyRaw.partialStrengthen? strengthening.back with
              | none => none
              | some targetLeftTyRaw =>
                  match rightRawSuccess :
                      rightTyRaw.partialStrengthen? strengthening.back with
                  | none => none
                  | some targetRightTyRaw =>
                      match proofRecurse :
                          partialStrengthenTyped? proof
                            (strengthening := strengthening) with
                      | none => none
                      | some proofResult =>
                          some
                            (partialStrengthenTypedUaToEquiv innerLevel
                              innerLevelLt leftTy rightTy targetLeftTy
                              targetRightTy leftTyRaw rightTyRaw
                              targetLeftTyRaw targetRightTyRaw
                              leftTySuccess rightTySuccess leftRawSuccess
                              rightRawSuccess proofResult)
  | @Term.equivApply _ _ _ _ carrierA carrierB _ _ equivTerm argumentTerm =>
      match carrierASuccess :
          carrierA.partialStrengthen? strengthening.back with
      | none => none
      | some _ =>
          match carrierBSuccess :
              carrierB.partialStrengthen? strengthening.back with
          | none => none
          | some _ =>
              match equivRecurse :
                  partialStrengthenTyped? equivTerm
                    (strengthening := strengthening) with
              | none => none
              | some equivResult =>
                  match argumentRecurse :
                      partialStrengthenTyped? argumentTerm
                        (strengthening := strengthening) with
                  | none => none
                  | some argumentResult =>
                      some
                        (partialStrengthenTypedEquivApply carrierASuccess
                          carrierBSuccess equivResult argumentResult)

end Term

end LeanFX2
