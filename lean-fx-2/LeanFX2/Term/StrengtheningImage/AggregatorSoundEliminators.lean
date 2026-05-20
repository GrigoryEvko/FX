import LeanFX2.Term.StrengtheningImage.AggregatorSoundCore

/-! # Term/StrengtheningImage/AggregatorSoundEliminators

Aggregator-soundness instances for eliminator, equivalence, heterogeneous, and effect wrappers.
-/

namespace LeanFX2

namespace Term

/-- Aggregator wrapper at the `Term.boolElim` arm.  Three flat-context
value IHs (scrutinee + then + else); motive is a `Ty (sourceScope + 1)`
handled by the dispatcher leaf's internal type-witness split, so no
motive aggregator. -/
theorem isAggregatorSound_boolElim {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope}
    {motiveType : Ty level (sourceScope + 1)}
    {scrutineeRaw thenRaw elseRaw : RawTerm sourceScope}
    {scrutinee : Term sourceCtx Ty.bool scrutineeRaw}
    {thenBranch :
      Term sourceCtx (motiveType.subst0 Ty.bool RawTerm.boolTrue) thenRaw}
    {elseBranch :
      Term sourceCtx (motiveType.subst0 Ty.bool RawTerm.boolFalse) elseRaw}
    (scrutineeAggregator : IsAggregatorSound scrutinee)
    (thenAggregator : IsAggregatorSound thenBranch)
    (elseAggregator : IsAggregatorSound elseBranch) :
    IsAggregatorSound
      (Term.boolElim (motiveType := motiveType) scrutinee thenBranch
        elseBranch) := by
  intros _ _ strengthening result success
  exact partialStrengthenTyped?_atBoolElim_imp_sound strengthening
    (scrutineeAggregator strengthening)
    (thenAggregator strengthening)
    (elseAggregator strengthening)
    result success

/-- Aggregator wrapper at the `Term.natElim` arm.  Three flat-context
value IHs (scrutinee + zero + succ); succ branch has the eliminator's
arrow `Ty.nat → motiveType`. -/
theorem isAggregatorSound_natElim {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope}
    {motiveType : Ty level sourceScope}
    {scrutineeRaw zeroRaw succRaw : RawTerm sourceScope}
    {scrutinee : Term sourceCtx Ty.nat scrutineeRaw}
    {zeroBranch : Term sourceCtx motiveType zeroRaw}
    {succBranch : Term sourceCtx (Ty.arrow Ty.nat motiveType) succRaw}
    (scrutineeAggregator : IsAggregatorSound scrutinee)
    (zeroAggregator : IsAggregatorSound zeroBranch)
    (succAggregator : IsAggregatorSound succBranch) :
    IsAggregatorSound
      (Term.natElim (motiveType := motiveType) scrutinee zeroBranch
        succBranch) := by
  intros _ _ strengthening result success
  exact partialStrengthenTyped?_atNatElim_imp_sound strengthening
    (scrutineeAggregator strengthening)
    (zeroAggregator strengthening)
    (succAggregator strengthening)
    result success

/-- Aggregator wrapper at the `Term.natRec` arm.  Mirrors `atNatElim`
shape with the recursor's higher-kinded succ branch
`Ty.nat → motiveType → motiveType`. -/
theorem isAggregatorSound_natRec {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope}
    {motiveType : Ty level sourceScope}
    {scrutineeRaw zeroRaw succRaw : RawTerm sourceScope}
    {scrutinee : Term sourceCtx Ty.nat scrutineeRaw}
    {zeroBranch : Term sourceCtx motiveType zeroRaw}
    {succBranch :
      Term sourceCtx (Ty.arrow Ty.nat (Ty.arrow motiveType motiveType))
        succRaw}
    (scrutineeAggregator : IsAggregatorSound scrutinee)
    (zeroAggregator : IsAggregatorSound zeroBranch)
    (succAggregator : IsAggregatorSound succBranch) :
    IsAggregatorSound
      (Term.natRec (motiveType := motiveType) scrutinee zeroBranch
        succBranch) := by
  intros _ _ strengthening result success
  exact partialStrengthenTyped?_atNatRec_imp_sound strengthening
    (scrutineeAggregator strengthening)
    (zeroAggregator strengthening)
    (succAggregator strengthening)
    result success

/-- Aggregator wrapper at the `Term.listElim` arm.  Parametric ι-
eliminator: one element-type witness handled internally by the leaf
plus three flat-context value IHs (scrutinee + nil + cons). -/
theorem isAggregatorSound_listElim {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope}
    {elementType motiveType : Ty level sourceScope}
    {scrutineeRaw nilRaw consRaw : RawTerm sourceScope}
    {scrutinee : Term sourceCtx (Ty.listType elementType) scrutineeRaw}
    {nilBranch : Term sourceCtx motiveType nilRaw}
    {consBranch :
      Term sourceCtx
        (Ty.arrow elementType
          (Ty.arrow (Ty.listType elementType) motiveType))
        consRaw}
    (scrutineeAggregator : IsAggregatorSound scrutinee)
    (nilAggregator : IsAggregatorSound nilBranch)
    (consAggregator : IsAggregatorSound consBranch) :
    IsAggregatorSound
      (Term.listElim (motiveType := motiveType) scrutinee nilBranch
        consBranch) := by
  intros _ _ strengthening result success
  exact partialStrengthenTyped?_atListElim_imp_sound strengthening
    (scrutineeAggregator strengthening)
    (nilAggregator strengthening)
    (consAggregator strengthening)
    result success

/-- Aggregator wrapper at the `Term.optionMatch` arm.  Mirrors
`atListElim` shape: one element-type witness internal + three flat-
context value IHs (scrutinee + none + some). -/
theorem isAggregatorSound_optionMatch {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope}
    {elementType motiveType : Ty level sourceScope}
    {scrutineeRaw noneRaw someRaw : RawTerm sourceScope}
    {scrutinee :
      Term sourceCtx (Ty.optionType elementType) scrutineeRaw}
    {noneBranch : Term sourceCtx motiveType noneRaw}
    {someBranch :
      Term sourceCtx (Ty.arrow elementType motiveType) someRaw}
    (scrutineeAggregator : IsAggregatorSound scrutinee)
    (noneAggregator : IsAggregatorSound noneBranch)
    (someAggregator : IsAggregatorSound someBranch) :
    IsAggregatorSound
      (Term.optionMatch (motiveType := motiveType) scrutinee noneBranch
        someBranch) := by
  intros _ _ strengthening result success
  exact partialStrengthenTyped?_atOptionMatch_imp_sound strengthening
    (scrutineeAggregator strengthening)
    (noneAggregator strengthening)
    (someAggregator strengthening)
    result success

/-- Aggregator wrapper at the `Term.eitherMatch` arm.  Two-source
parametric ι-eliminator: two type witnesses (leftType + rightType)
handled internally plus three flat-context value IHs (scrutinee +
left + right). -/
theorem isAggregatorSound_eitherMatch {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope}
    {leftType rightType motiveType : Ty level sourceScope}
    {scrutineeRaw leftRaw rightRaw : RawTerm sourceScope}
    {scrutinee :
      Term sourceCtx (Ty.eitherType leftType rightType) scrutineeRaw}
    {leftBranch :
      Term sourceCtx (Ty.arrow leftType motiveType) leftRaw}
    {rightBranch :
      Term sourceCtx (Ty.arrow rightType motiveType) rightRaw}
    (scrutineeAggregator : IsAggregatorSound scrutinee)
    (leftAggregator : IsAggregatorSound leftBranch)
    (rightAggregator : IsAggregatorSound rightBranch) :
    IsAggregatorSound
      (Term.eitherMatch (motiveType := motiveType) scrutinee leftBranch
        rightBranch) := by
  intros _ _ strengthening result success
  exact partialStrengthenTyped?_atEitherMatch_imp_sound strengthening
    (scrutineeAggregator strengthening)
    (leftAggregator strengthening)
    (rightAggregator strengthening)
    result success

/-- Aggregator wrapper at the `Term.idJ` arm.  HoTT J-eliminator: two
flat-context value IHs (baseCase + witness); type witnesses (carrier +
both endpoints) are handled internally by the leaf via the
`strengthening`-driven splits, so no companion aggregators. -/
theorem isAggregatorSound_idJ {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope}
    {carrier : Ty level sourceScope}
    {leftEndpoint rightEndpoint : RawTerm sourceScope}
    {motiveType : Ty level sourceScope}
    {baseRaw witnessRaw : RawTerm sourceScope}
    {baseCase : Term sourceCtx motiveType baseRaw}
    {witness :
      Term sourceCtx (Ty.id carrier leftEndpoint rightEndpoint) witnessRaw}
    (baseAggregator : IsAggregatorSound baseCase)
    (witnessAggregator : IsAggregatorSound witness) :
    IsAggregatorSound
      (Term.idJ (motiveType := motiveType) baseCase witness) := by
  intros _ _ strengthening result success
  exact partialStrengthenTyped?_atIdJ_imp_sound strengthening
    (baseAggregator strengthening)
    (witnessAggregator strengthening)
    result success

/-- Aggregator wrapper at the `Term.oeqJ` arm.  Mirrors `atIdJ` for
observational equality: two flat-context value IHs (baseCase +
witness). -/
theorem isAggregatorSound_oeqJ {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope}
    {carrier : Ty level sourceScope}
    {leftEndpoint rightEndpoint : RawTerm sourceScope}
    {motiveType : Ty level sourceScope}
    {baseRaw witnessRaw : RawTerm sourceScope}
    {baseCase : Term sourceCtx motiveType baseRaw}
    {witness :
      Term sourceCtx (Ty.oeq carrier leftEndpoint rightEndpoint) witnessRaw}
    (baseAggregator : IsAggregatorSound baseCase)
    (witnessAggregator : IsAggregatorSound witness) :
    IsAggregatorSound
      (Term.oeqJ (motiveType := motiveType) baseCase witness) := by
  intros _ _ strengthening result success
  exact partialStrengthenTyped?_atOeqJ_imp_sound strengthening
    (baseAggregator strengthening)
    (witnessAggregator strengthening)
    result success

/-- Aggregator wrapper at the `Term.idStrictRec` arm.  Strict-mode
J-eliminator: two flat-context value IHs plus the `modeIsStrict`
discipline witness threaded through. -/
theorem isAggregatorSound_idStrictRec {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope}
    {modeIsStrict : mode = Mode.strict}
    {carrier : Ty level sourceScope}
    {leftEndpoint rightEndpoint : RawTerm sourceScope}
    {motiveType : Ty level sourceScope}
    {baseRaw witnessRaw : RawTerm sourceScope}
    {baseCase : Term sourceCtx motiveType baseRaw}
    {witness :
      Term sourceCtx (Ty.idStrict carrier leftEndpoint rightEndpoint)
        witnessRaw}
    (baseAggregator : IsAggregatorSound baseCase)
    (witnessAggregator : IsAggregatorSound witness) :
    IsAggregatorSound
      (Term.idStrictRec (motiveType := motiveType) modeIsStrict
        baseCase witness) := by
  intros _ _ strengthening result success
  exact partialStrengthenTyped?_atIdStrictRec_imp_sound strengthening
    (baseAggregator strengthening)
    (witnessAggregator strengthening)
    result success

/-- Aggregator wrapper at the `Term.equivApp` arm.  Heterogeneous
equivalence application: two flat-context value IHs (equiv + argument);
both carrier-type witnesses (`carrierA`/`carrierB`) handled inside the
leaf. -/
theorem isAggregatorSound_equivApp {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope}
    {carrierA carrierB : Ty level sourceScope}
    {equivRaw argumentRaw : RawTerm sourceScope}
    {equivTerm :
      Term sourceCtx (Ty.equiv carrierA carrierB) equivRaw}
    {argumentTerm : Term sourceCtx carrierA argumentRaw}
    (equivAggregator : IsAggregatorSound equivTerm)
    (argumentAggregator : IsAggregatorSound argumentTerm) :
    IsAggregatorSound (Term.equivApp equivTerm argumentTerm) := by
  intros _ _ strengthening result success
  exact partialStrengthenTyped?_atEquivApp_imp_sound strengthening
    (equivAggregator strengthening)
    (argumentAggregator strengthening)
    result success

/-- Aggregator wrapper at the `Term.equivApply` arm.  Univalence-
flavoured equivalence application: same shape as `equivApp` — two
flat-context value IHs.  Differs from `equivApp` only in the raw
constructor used by the dispatcher. -/
theorem isAggregatorSound_equivApply {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope}
    {carrierA carrierB : Ty level sourceScope}
    {equivRaw argumentRaw : RawTerm sourceScope}
    {equivTerm :
      Term sourceCtx (Ty.equiv carrierA carrierB) equivRaw}
    {argumentTerm : Term sourceCtx carrierA argumentRaw}
    (equivAggregator : IsAggregatorSound equivTerm)
    (argumentAggregator : IsAggregatorSound argumentTerm) :
    IsAggregatorSound (Term.equivApply equivTerm argumentTerm) := by
  intros _ _ strengthening result success
  exact partialStrengthenTyped?_atEquivApply_imp_sound strengthening
    (equivAggregator strengthening)
    (argumentAggregator strengthening)
    result success

/-- Aggregator wrapper at the `Term.equivIntroHet` arm.  Heterogeneous
equivalence introduction: four function-shaped value IHs (forward +
backward + leftInverse + rightInverse).  Both carrier types handled
internally. -/
theorem isAggregatorSound_equivIntroHet {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope}
    {carrierA carrierB : Ty level sourceScope}
    {forwardRaw backwardRaw leftInvRaw rightInvRaw : RawTerm sourceScope}
    {forward :
      Term sourceCtx (Ty.arrow carrierA carrierB) forwardRaw}
    {backward :
      Term sourceCtx (Ty.arrow carrierB carrierA) backwardRaw}
    {leftInv :
      Term sourceCtx
        (equivIntroHetLeftInverseType carrierA forwardRaw backwardRaw)
        leftInvRaw}
    {rightInv :
      Term sourceCtx
        (equivIntroHetRightInverseType carrierB forwardRaw backwardRaw)
        rightInvRaw}
    (forwardAggregator : IsAggregatorSound forward)
    (backwardAggregator : IsAggregatorSound backward)
    (leftInvAggregator : IsAggregatorSound leftInv)
    (rightInvAggregator : IsAggregatorSound rightInv) :
    IsAggregatorSound
      (Term.equivIntroHet forward backward leftInv rightInv) := by
  intros _ _ strengthening result success
  exact partialStrengthenTyped?_atEquivIntroHet_imp_sound strengthening
    (forwardAggregator strengthening)
    (backwardAggregator strengthening)
    (leftInvAggregator strengthening)
    (rightInvAggregator strengthening)
    result success

/-- Aggregator wrapper at the `Term.oeqFunext` arm.  Observational-
equality funext: one value IH on the pointwise-equality proof.  All
type and raw witnesses handled internally by the leaf's sequential
splits. -/
theorem isAggregatorSound_oeqFunext {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope}
    {domainType codomainType : Ty level sourceScope}
    {leftFunctionRaw rightFunctionRaw : RawTerm sourceScope}
    {pointwiseRaw : RawTerm sourceScope}
    {pointwiseProof :
      Term sourceCtx
        (oeqFunextPointwiseType domainType codomainType
          leftFunctionRaw rightFunctionRaw)
        pointwiseRaw}
    (pointwiseAggregator : IsAggregatorSound pointwiseProof) :
    IsAggregatorSound
      (Term.oeqFunext (domainType := domainType)
        (codomainType := codomainType)
        (leftFunctionRaw := leftFunctionRaw)
        (rightFunctionRaw := rightFunctionRaw)
        pointwiseProof) := by
  intros _ _ strengthening result success
  exact partialStrengthenTyped?_atOeqFunext_imp_sound strengthening
    (pointwiseAggregator strengthening)
    result success

/-- Aggregator wrapper at the `Term.uaIntroHet` arm.  Heterogeneous
univalence introduction: one value IH on the equivalence-witness term;
positional `innerLevel`/`innerLevelLt` (universe level + bound) and
the two raw carrier witnesses thread through directly. -/
theorem isAggregatorSound_uaIntroHet {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope}
    (innerLevel : UniverseLevel)
    (innerLevelLt : innerLevel.toNat + 1 ≤ level)
    {carrierA carrierB : Ty level sourceScope}
    (carrierARaw carrierBRaw : RawTerm sourceScope)
    {forwardRaw backwardRaw : RawTerm sourceScope}
    {equivWitness :
      Term sourceCtx (Ty.equiv carrierA carrierB)
        (RawTerm.equivIntro forwardRaw backwardRaw)}
    (equivAggregator : IsAggregatorSound equivWitness) :
    IsAggregatorSound
      (Term.uaIntroHet (context := sourceCtx) innerLevel innerLevelLt
        carrierARaw carrierBRaw equivWitness) := by
  intros _ _ strengthening result success
  exact partialStrengthenTyped?_atUaIntroHet_imp_sound innerLevel
    innerLevelLt carrierARaw carrierBRaw strengthening
    (equivAggregator strengthening)
    result success

/-- Aggregator wrapper at the `Term.effectPerform` arm.  Effect
operation invocation: two flat-context value IHs (operation tag +
arguments); positional `canPerformOperation` predicate threads through
unstrengthened (mode/effect-row metadata). -/
theorem isAggregatorSound_effectPerform {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope}
    {effectTag : RawTerm sourceScope}
    {effectRow : Effects.EffectRow}
    {operationSignature :
      Effects.OperationSignature (Ty level sourceScope)}
    (canPerformOperation :
      Effects.CanPerform effectRow operationSignature)
    {operationRaw argumentsRaw : RawTerm sourceScope}
    {operationTag :
      Term sourceCtx
        (Ty.effect operationSignature.argumentCarrier effectTag)
        operationRaw}
    {arguments :
      Term sourceCtx operationSignature.argumentCarrier argumentsRaw}
    (operationAggregator : IsAggregatorSound operationTag)
    (argumentsAggregator : IsAggregatorSound arguments) :
    IsAggregatorSound
      (Term.effectPerform (context := sourceCtx) effectTag effectRow
        operationSignature canPerformOperation operationTag arguments) := by
  intros _ _ strengthening result success
  exact partialStrengthenTyped?_atEffectPerform_imp_sound
    canPerformOperation strengthening
    (operationAggregator strengthening)
    (argumentsAggregator strengthening)
    result success

end Term

end LeanFX2
