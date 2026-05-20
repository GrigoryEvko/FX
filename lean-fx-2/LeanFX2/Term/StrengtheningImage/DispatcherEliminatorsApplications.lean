import LeanFX2.Term.StrengtheningImage.Core
import LeanFX2.Term.StrengtheningImage.Applications
import LeanFX2.Term.StrengtheningImage.EliminatorsAndModal
import LeanFX2.Term.StrengtheningImage.CollectionsSigmaInterval
import LeanFX2.Term.StrengtheningImage.Reflexivity
import LeanFX2.Term.StrengtheningImage.MatcherWrappers
import LeanFX2.Term.StrengtheningImage.HoTTAppWrappers


/-! # Term/StrengtheningImage/DispatcherEliminatorsApplications

Dispatcher-arm soundness for eliminators, function application, Sigma pair and projection constructors.
-/

namespace LeanFX2

namespace Term

/-- Dispatcher soundness at the `Term.refl` arm.  HoTT identity
introduction: one type witness (carrier) plus one raw witness
(rawWitness) — no value IH at all. -/
theorem partialStrengthenTyped?_atRefl_imp_sound {mode : Mode}
    {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {carrier : Ty level sourceScope}
    {rawWitness : RawTerm sourceScope}
    (strengthening : ContextStrengthening sourceCtx targetCtx)
    (result : StrengtheningResult strengthening
      (Term.refl (context := sourceCtx) (carrier := carrier) rawWitness))
    (success : partialStrengthenTyped?
        (Term.refl (context := sourceCtx) (carrier := carrier) rawWitness)
          strengthening =
          some result) :
    StrengtheningSoundness result := by
  unfold partialStrengthenTyped? at success
  split at success
  · cases success
  · rename_i targetCarrier carrierSuccess
    split at success
    · cases success
    · rename_i targetWitness witnessSuccess
      cases success
      exact partialStrengthenTypedRefl_sound carrierSuccess witnessSuccess

/-- Dispatcher soundness at the `Term.oeqRefl` arm.  Mirrors `atRefl`
for observational equality: one type witness + one raw witness, no
value IH. -/
theorem partialStrengthenTyped?_atOeqRefl_imp_sound {mode : Mode}
    {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {carrier : Ty level sourceScope}
    {rawWitness : RawTerm sourceScope}
    (strengthening : ContextStrengthening sourceCtx targetCtx)
    (result : StrengtheningResult strengthening
      (Term.oeqRefl (context := sourceCtx) (carrier := carrier)
        rawWitness))
    (success : partialStrengthenTyped?
        (Term.oeqRefl (context := sourceCtx) (carrier := carrier)
          rawWitness) strengthening =
          some result) :
    StrengtheningSoundness result := by
  unfold partialStrengthenTyped? at success
  split at success
  · cases success
  · rename_i targetCarrier carrierSuccess
    split at success
    · cases success
    · rename_i targetWitness witnessSuccess
      cases success
      exact partialStrengthenTypedOeqRefl_sound carrierSuccess
        witnessSuccess

/-- Dispatcher soundness at the `Term.idJ` arm.  HoTT J-eliminator:
one type witness (carrier) + two raw witnesses (leftEndpoint +
rightEndpoint) + two flat-context value IHs (baseCase + witness). -/
theorem partialStrengthenTyped?_atIdJ_imp_sound {mode : Mode}
    {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {carrier : Ty level sourceScope}
    {leftEndpoint rightEndpoint : RawTerm sourceScope}
    {motiveType : Ty level sourceScope}
    {baseRaw witnessRaw : RawTerm sourceScope}
    {baseCase : Term sourceCtx motiveType baseRaw}
    {witness :
      Term sourceCtx (Ty.id carrier leftEndpoint rightEndpoint) witnessRaw}
    (strengthening : ContextStrengthening sourceCtx targetCtx)
    (baseIH : ∀ baseResult,
        partialStrengthenTyped? baseCase strengthening =
            some baseResult →
          StrengtheningSoundness baseResult)
    (witnessIH : ∀ witnessResult,
        partialStrengthenTyped? witness strengthening =
            some witnessResult →
          StrengtheningSoundness witnessResult)
    (result : StrengtheningResult strengthening
      (Term.idJ (motiveType := motiveType) baseCase witness))
    (success : partialStrengthenTyped?
        (Term.idJ (motiveType := motiveType) baseCase witness)
          strengthening =
          some result) :
    StrengtheningSoundness result := by
  unfold partialStrengthenTyped? at success
  split at success
  · cases success
  · rename_i targetCarrier carrierSuccess
    split at success
    · cases success
    · rename_i targetLeftEndpoint leftSuccess
      split at success
      · cases success
      · rename_i targetRightEndpoint rightSuccess
        split at success
        · cases success
        · rename_i baseResult baseRecurse
          split at success
          · cases success
          · rename_i witnessResult witnessRecurse
            cases success
            exact partialStrengthenTypedIdJ_sound
              carrierSuccess leftSuccess rightSuccess
              (baseIH baseResult baseRecurse)
              (witnessIH witnessResult witnessRecurse)

/-- Dispatcher soundness at the `Term.oeqJ` arm.  Mirrors `atIdJ` for
observational equality: one type witness + two raw witnesses + two
flat-context value IHs. -/
theorem partialStrengthenTyped?_atOeqJ_imp_sound {mode : Mode}
    {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {carrier : Ty level sourceScope}
    {leftEndpoint rightEndpoint : RawTerm sourceScope}
    {motiveType : Ty level sourceScope}
    {baseRaw witnessRaw : RawTerm sourceScope}
    {baseCase : Term sourceCtx motiveType baseRaw}
    {witness :
      Term sourceCtx (Ty.oeq carrier leftEndpoint rightEndpoint) witnessRaw}
    (strengthening : ContextStrengthening sourceCtx targetCtx)
    (baseIH : ∀ baseResult,
        partialStrengthenTyped? baseCase strengthening =
            some baseResult →
          StrengtheningSoundness baseResult)
    (witnessIH : ∀ witnessResult,
        partialStrengthenTyped? witness strengthening =
            some witnessResult →
          StrengtheningSoundness witnessResult)
    (result : StrengtheningResult strengthening
      (Term.oeqJ (motiveType := motiveType) baseCase witness))
    (success : partialStrengthenTyped?
        (Term.oeqJ (motiveType := motiveType) baseCase witness)
          strengthening =
          some result) :
    StrengtheningSoundness result := by
  unfold partialStrengthenTyped? at success
  split at success
  · cases success
  · rename_i targetCarrier carrierSuccess
    split at success
    · cases success
    · rename_i targetLeftEndpoint leftSuccess
      split at success
      · cases success
      · rename_i targetRightEndpoint rightSuccess
        split at success
        · cases success
        · rename_i baseResult baseRecurse
          split at success
          · cases success
          · rename_i witnessResult witnessRecurse
            cases success
            exact partialStrengthenTypedOeqJ_sound
              carrierSuccess leftSuccess rightSuccess
              (baseIH baseResult baseRecurse)
              (witnessIH witnessResult witnessRecurse)

/-- Dispatcher soundness at the `Term.boolElim` arm.  ι-eliminator
shape: one binder-type strengthening witness on the motive slot
(`strengthening.back.lift`) plus three flat-context value IHs
(scrutinee + then + else). -/
theorem partialStrengthenTyped?_atBoolElim_imp_sound {mode : Mode}
    {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {motiveType : Ty level (sourceScope + 1)}
    {scrutineeRaw thenRaw elseRaw : RawTerm sourceScope}
    {scrutinee : Term sourceCtx Ty.bool scrutineeRaw}
    {thenBranch :
      Term sourceCtx (motiveType.subst0 Ty.bool RawTerm.boolTrue) thenRaw}
    {elseBranch :
      Term sourceCtx (motiveType.subst0 Ty.bool RawTerm.boolFalse) elseRaw}
    (strengthening : ContextStrengthening sourceCtx targetCtx)
    (scrutineeIH : ∀ scrutineeResult,
        partialStrengthenTyped? scrutinee strengthening =
            some scrutineeResult →
          StrengtheningSoundness scrutineeResult)
    (thenIH : ∀ thenResult,
        partialStrengthenTyped? thenBranch strengthening =
            some thenResult →
          StrengtheningSoundness thenResult)
    (elseIH : ∀ elseResult,
        partialStrengthenTyped? elseBranch strengthening =
            some elseResult →
          StrengtheningSoundness elseResult)
    (result : StrengtheningResult strengthening
      (Term.boolElim (motiveType := motiveType) scrutinee thenBranch
        elseBranch))
    (success : partialStrengthenTyped?
        (Term.boolElim (motiveType := motiveType) scrutinee thenBranch
          elseBranch) strengthening =
          some result) :
    StrengtheningSoundness result := by
  unfold partialStrengthenTyped? at success
  split at success
  · cases success
  · rename_i targetMotiveType motiveSuccess
    split at success
    · cases success
    · rename_i scrutineeResult scrutineeRecurse
      split at success
      · cases success
      · rename_i thenResult thenRecurse
        split at success
        · cases success
        · rename_i elseResult elseRecurse
          cases success
          exact partialStrengthenTypedBoolElim_sound motiveSuccess
            (scrutineeIH scrutineeResult scrutineeRecurse)
            (thenIH thenResult thenRecurse)
            (elseIH elseResult elseRecurse)

/-- Dispatcher soundness at the `Term.natElim` arm.  ι-eliminator with
non-dependent motive at the kernel level: no type witness needed,
three flat-context value IHs (scrutinee + zero + succ). -/
theorem partialStrengthenTyped?_atNatElim_imp_sound {mode : Mode}
    {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {motiveType : Ty level sourceScope}
    {scrutineeRaw zeroRaw succRaw : RawTerm sourceScope}
    {scrutinee : Term sourceCtx Ty.nat scrutineeRaw}
    {zeroBranch : Term sourceCtx motiveType zeroRaw}
    {succBranch : Term sourceCtx (Ty.arrow Ty.nat motiveType) succRaw}
    (strengthening : ContextStrengthening sourceCtx targetCtx)
    (scrutineeIH : ∀ scrutineeResult,
        partialStrengthenTyped? scrutinee strengthening =
            some scrutineeResult →
          StrengtheningSoundness scrutineeResult)
    (zeroIH : ∀ zeroResult,
        partialStrengthenTyped? zeroBranch strengthening =
            some zeroResult →
          StrengtheningSoundness zeroResult)
    (succIH : ∀ succResult,
        partialStrengthenTyped? succBranch strengthening =
            some succResult →
          StrengtheningSoundness succResult)
    (result : StrengtheningResult strengthening
      (Term.natElim (motiveType := motiveType) scrutinee zeroBranch
        succBranch))
    (success : partialStrengthenTyped?
        (Term.natElim (motiveType := motiveType) scrutinee zeroBranch
          succBranch) strengthening =
          some result) :
    StrengtheningSoundness result := by
  unfold partialStrengthenTyped? at success
  split at success
  · cases success
  · rename_i scrutineeResult scrutineeRecurse
    split at success
    · cases success
    · rename_i zeroResult zeroRecurse
      split at success
      · cases success
      · rename_i succResult succRecurse
        cases success
        exact partialStrengthenTypedNatElim_sound
          (scrutineeIH scrutineeResult scrutineeRecurse)
          (zeroIH zeroResult zeroRecurse)
          (succIH succResult succRecurse)

/-- Dispatcher soundness at the `Term.natRec` arm.  Mirrors `atNatElim`
shape: no type witness, three flat-context value IHs (scrutinee +
zero + succ); succ branch has the recursor's higher-kinded arrow. -/
theorem partialStrengthenTyped?_atNatRec_imp_sound {mode : Mode}
    {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {motiveType : Ty level sourceScope}
    {scrutineeRaw zeroRaw succRaw : RawTerm sourceScope}
    {scrutinee : Term sourceCtx Ty.nat scrutineeRaw}
    {zeroBranch : Term sourceCtx motiveType zeroRaw}
    {succBranch :
      Term sourceCtx (Ty.arrow Ty.nat (Ty.arrow motiveType motiveType))
        succRaw}
    (strengthening : ContextStrengthening sourceCtx targetCtx)
    (scrutineeIH : ∀ scrutineeResult,
        partialStrengthenTyped? scrutinee strengthening =
            some scrutineeResult →
          StrengtheningSoundness scrutineeResult)
    (zeroIH : ∀ zeroResult,
        partialStrengthenTyped? zeroBranch strengthening =
            some zeroResult →
          StrengtheningSoundness zeroResult)
    (succIH : ∀ succResult,
        partialStrengthenTyped? succBranch strengthening =
            some succResult →
          StrengtheningSoundness succResult)
    (result : StrengtheningResult strengthening
      (Term.natRec (motiveType := motiveType) scrutinee zeroBranch
        succBranch))
    (success : partialStrengthenTyped?
        (Term.natRec (motiveType := motiveType) scrutinee zeroBranch
          succBranch) strengthening =
          some result) :
    StrengtheningSoundness result := by
  unfold partialStrengthenTyped? at success
  split at success
  · cases success
  · rename_i scrutineeResult scrutineeRecurse
    split at success
    · cases success
    · rename_i zeroResult zeroRecurse
      split at success
      · cases success
      · rename_i succResult succRecurse
        cases success
        exact partialStrengthenTypedNatRec_sound
          (scrutineeIH scrutineeResult scrutineeRecurse)
          (zeroIH zeroResult zeroRecurse)
          (succIH succResult succRecurse)

/-- Dispatcher soundness at the `Term.listElim` arm.  Parametric ι-
eliminator: one type witness (element type at `strengthening.back`)
plus three flat-context value IHs (scrutinee + nil + cons). -/
theorem partialStrengthenTyped?_atListElim_imp_sound {mode : Mode}
    {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {elementType motiveType : Ty level sourceScope}
    {scrutineeRaw nilRaw consRaw : RawTerm sourceScope}
    {scrutinee : Term sourceCtx (Ty.listType elementType) scrutineeRaw}
    {nilBranch : Term sourceCtx motiveType nilRaw}
    {consBranch :
      Term sourceCtx
        (Ty.arrow elementType
          (Ty.arrow (Ty.listType elementType) motiveType))
        consRaw}
    (strengthening : ContextStrengthening sourceCtx targetCtx)
    (scrutineeIH : ∀ scrutineeResult,
        partialStrengthenTyped? scrutinee strengthening =
            some scrutineeResult →
          StrengtheningSoundness scrutineeResult)
    (nilIH : ∀ nilResult,
        partialStrengthenTyped? nilBranch strengthening =
            some nilResult →
          StrengtheningSoundness nilResult)
    (consIH : ∀ consResult,
        partialStrengthenTyped? consBranch strengthening =
            some consResult →
          StrengtheningSoundness consResult)
    (result : StrengtheningResult strengthening
      (Term.listElim (motiveType := motiveType) scrutinee nilBranch
        consBranch))
    (success : partialStrengthenTyped?
        (Term.listElim (motiveType := motiveType) scrutinee nilBranch
          consBranch) strengthening =
          some result) :
    StrengtheningSoundness result := by
  unfold partialStrengthenTyped? at success
  split at success
  · cases success
  · rename_i targetElementType elementSuccess
    split at success
    · cases success
    · rename_i scrutineeResult scrutineeRecurse
      split at success
      · cases success
      · rename_i nilResult nilRecurse
        split at success
        · cases success
        · rename_i consResult consRecurse
          cases success
          exact partialStrengthenTypedListElim_sound elementSuccess
            (scrutineeIH scrutineeResult scrutineeRecurse)
            (nilIH nilResult nilRecurse)
            (consIH consResult consRecurse)

/-- Dispatcher soundness at the `Term.optionMatch` arm.  Mirrors
`atListElim`: one element-type witness + three flat-context value IHs
(scrutinee + none + some). -/
theorem partialStrengthenTyped?_atOptionMatch_imp_sound {mode : Mode}
    {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {elementType motiveType : Ty level sourceScope}
    {scrutineeRaw noneRaw someRaw : RawTerm sourceScope}
    {scrutinee :
      Term sourceCtx (Ty.optionType elementType) scrutineeRaw}
    {noneBranch : Term sourceCtx motiveType noneRaw}
    {someBranch :
      Term sourceCtx (Ty.arrow elementType motiveType) someRaw}
    (strengthening : ContextStrengthening sourceCtx targetCtx)
    (scrutineeIH : ∀ scrutineeResult,
        partialStrengthenTyped? scrutinee strengthening =
            some scrutineeResult →
          StrengtheningSoundness scrutineeResult)
    (noneIH : ∀ noneResult,
        partialStrengthenTyped? noneBranch strengthening =
            some noneResult →
          StrengtheningSoundness noneResult)
    (someIH : ∀ someResult,
        partialStrengthenTyped? someBranch strengthening =
            some someResult →
          StrengtheningSoundness someResult)
    (result : StrengtheningResult strengthening
      (Term.optionMatch (motiveType := motiveType) scrutinee noneBranch
        someBranch))
    (success : partialStrengthenTyped?
        (Term.optionMatch (motiveType := motiveType) scrutinee noneBranch
          someBranch) strengthening =
          some result) :
    StrengtheningSoundness result := by
  unfold partialStrengthenTyped? at success
  split at success
  · cases success
  · rename_i targetElementType elementSuccess
    split at success
    · cases success
    · rename_i scrutineeResult scrutineeRecurse
      split at success
      · cases success
      · rename_i noneResult noneRecurse
        split at success
        · cases success
        · rename_i someResult someRecurse
          cases success
          exact partialStrengthenTypedOptionMatch_sound elementSuccess
            (scrutineeIH scrutineeResult scrutineeRecurse)
            (noneIH noneResult noneRecurse)
            (someIH someResult someRecurse)

/-- Dispatcher soundness at the `Term.app` arm.  Non-dependent
application: two type strengthening witnesses (domain + codomain,
both at `strengthening.back` since the codomain in `Ty.arrow` does
not see the bound variable) plus two value IHs (function + argument). -/
theorem partialStrengthenTyped?_atApp_imp_sound {mode : Mode}
    {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {domainType codomainType : Ty level sourceScope}
    {functionRaw argumentRaw : RawTerm sourceScope}
    {functionTerm :
      Term sourceCtx (Ty.arrow domainType codomainType) functionRaw}
    {argumentTerm : Term sourceCtx domainType argumentRaw}
    (strengthening : ContextStrengthening sourceCtx targetCtx)
    (functionIH : ∀ functionResult,
        partialStrengthenTyped? functionTerm strengthening =
            some functionResult →
          StrengtheningSoundness functionResult)
    (argumentIH : ∀ argumentResult,
        partialStrengthenTyped? argumentTerm strengthening =
            some argumentResult →
          StrengtheningSoundness argumentResult)
    (result : StrengtheningResult strengthening
      (Term.app (codomainType := codomainType)
        functionTerm argumentTerm))
    (success : partialStrengthenTyped?
        (Term.app (codomainType := codomainType)
          functionTerm argumentTerm) strengthening =
          some result) :
    StrengtheningSoundness result := by
  unfold partialStrengthenTyped? at success
  split at success
  · cases success
  · rename_i targetDomainType domainSuccess
    split at success
    · cases success
    · rename_i targetCodomainType codomainSuccess
      split at success
      · cases success
      · rename_i functionResult functionRecurse
        split at success
        · cases success
        · rename_i argumentResult argumentRecurse
          cases success
          exact partialStrengthenTypedApp_sound
            domainSuccess codomainSuccess
            (functionIH functionResult functionRecurse)
            (argumentIH argumentResult argumentRecurse)

/-- Dispatcher soundness at the `Term.appPi` arm.  Dependent application:
domain strengthens at `strengthening.back`, codomain strengthens under
the binder via `strengthening.back.lift`; two value IHs. -/
theorem partialStrengthenTyped?_atAppPi_imp_sound {mode : Mode}
    {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {domainType : Ty level sourceScope}
    {codomainType : Ty level (sourceScope + 1)}
    {functionRaw argumentRaw : RawTerm sourceScope}
    {functionTerm :
      Term sourceCtx (Ty.piTy domainType codomainType) functionRaw}
    {argumentTerm : Term sourceCtx domainType argumentRaw}
    (strengthening : ContextStrengthening sourceCtx targetCtx)
    (functionIH : ∀ functionResult,
        partialStrengthenTyped? functionTerm strengthening =
            some functionResult →
          StrengtheningSoundness functionResult)
    (argumentIH : ∀ argumentResult,
        partialStrengthenTyped? argumentTerm strengthening =
            some argumentResult →
          StrengtheningSoundness argumentResult)
    (result : StrengtheningResult strengthening
      (Term.appPi (codomainType := codomainType)
        functionTerm argumentTerm))
    (success : partialStrengthenTyped?
        (Term.appPi (codomainType := codomainType)
          functionTerm argumentTerm) strengthening =
          some result) :
    StrengtheningSoundness result := by
  unfold partialStrengthenTyped? at success
  split at success
  · cases success
  · rename_i targetDomainType domainSuccess
    split at success
    · cases success
    · rename_i targetCodomainType codomainSuccess
      split at success
      · cases success
      · rename_i functionResult functionRecurse
        split at success
        · cases success
        · rename_i argumentResult argumentRecurse
          cases success
          exact partialStrengthenTypedAppPi_sound
            domainSuccess codomainSuccess
            (functionIH functionResult functionRecurse)
            (argumentIH argumentResult argumentRecurse)

/-- Dispatcher soundness at the `Term.pair` arm.  Sigma-pair shape:
one binder-type strengthening witness on the second-type slot, plus
two value-subterm IHs (first value at `firstType`, second value at
the substituted type). -/
theorem partialStrengthenTyped?_atPair_imp_sound {mode : Mode}
    {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {firstType : Ty level sourceScope}
    {secondType : Ty level (sourceScope + 1)}
    {firstRaw secondRaw : RawTerm sourceScope}
    {firstValue : Term sourceCtx firstType firstRaw}
    {secondValue :
      Term sourceCtx (secondType.subst0 firstType firstRaw) secondRaw}
    (strengthening : ContextStrengthening sourceCtx targetCtx)
    (firstIH : ∀ firstResult,
        partialStrengthenTyped? firstValue strengthening =
            some firstResult →
          StrengtheningSoundness firstResult)
    (secondIH : ∀ secondResult,
        partialStrengthenTyped? secondValue strengthening =
            some secondResult →
          StrengtheningSoundness secondResult)
    (result : StrengtheningResult strengthening
      (Term.pair (secondType := secondType) firstValue secondValue))
    (success : partialStrengthenTyped?
        (Term.pair (secondType := secondType) firstValue secondValue)
          strengthening =
          some result) :
    StrengtheningSoundness result := by
  unfold partialStrengthenTyped? at success
  split at success
  · cases success
  · rename_i targetSecondType secondTypeSuccess
    split at success
    · cases success
    · rename_i firstResult firstRecurse
      split at success
      · cases success
      · rename_i secondResult secondRecurse
        cases success
        exact partialStrengthenTypedPair_sound secondTypeSuccess
          (firstIH firstResult firstRecurse)
          (secondIH secondResult secondRecurse)

/-- Dispatcher soundness at the `Term.fst` arm.  Sigma first-projection:
two type strengthening witnesses (firstType + secondType) plus a
single sigma-value IH. -/
theorem partialStrengthenTyped?_atFst_imp_sound {mode : Mode}
    {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {firstType : Ty level sourceScope}
    {secondType : Ty level (sourceScope + 1)}
    {pairRaw : RawTerm sourceScope}
    {pairTerm : Term sourceCtx (Ty.sigmaTy firstType secondType) pairRaw}
    (strengthening : ContextStrengthening sourceCtx targetCtx)
    (pairIH : ∀ pairResult,
        partialStrengthenTyped? pairTerm strengthening =
            some pairResult →
          StrengtheningSoundness pairResult)
    (result : StrengtheningResult strengthening (Term.fst pairTerm))
    (success :
      partialStrengthenTyped? (Term.fst pairTerm) strengthening =
        some result) :
    StrengtheningSoundness result := by
  unfold partialStrengthenTyped? at success
  split at success
  · cases success
  · rename_i targetFirstType firstSuccess
    split at success
    · cases success
    · rename_i targetSecondType secondSuccess
      split at success
      · cases success
      · rename_i pairResult pairRecurse
        cases success
        exact partialStrengthenTypedFst_sound firstSuccess secondSuccess
          (pairIH pairResult pairRecurse)

/-- Dispatcher soundness at the `Term.snd` arm.  Mirrors `atFst` —
two type strengthening witnesses plus a single sigma-value IH. -/
theorem partialStrengthenTyped?_atSnd_imp_sound {mode : Mode}
    {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {firstType : Ty level sourceScope}
    {secondType : Ty level (sourceScope + 1)}
    {pairRaw : RawTerm sourceScope}
    {pairTerm : Term sourceCtx (Ty.sigmaTy firstType secondType) pairRaw}
    (strengthening : ContextStrengthening sourceCtx targetCtx)
    (pairIH : ∀ pairResult,
        partialStrengthenTyped? pairTerm strengthening =
            some pairResult →
          StrengtheningSoundness pairResult)
    (result : StrengtheningResult strengthening (Term.snd pairTerm))
    (success :
      partialStrengthenTyped? (Term.snd pairTerm) strengthening =
        some result) :
    StrengtheningSoundness result := by
  unfold partialStrengthenTyped? at success
  split at success
  · cases success
  · rename_i targetFirstType firstSuccess
    split at success
    · cases success
    · rename_i targetSecondType secondSuccess
      split at success
      · cases success
      · rename_i pairResult pairRecurse
        cases success
        exact partialStrengthenTypedSnd_sound firstSuccess secondSuccess
          (pairIH pairResult pairRecurse)

end Term

end LeanFX2
