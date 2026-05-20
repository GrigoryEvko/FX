import LeanFX2.Term.StrengtheningImage.TotalOnWeakenCubicalHoTT

/-! # Term/StrengtheningImage/TotalOnWeakenEliminators

Total-on-weaken wrappers for natural, list, option, either eliminators and effect performance.
-/

namespace LeanFX2

namespace Term

/-- 3-IH non-binder totality: `Term.natElim`.  Pure 3-IH (no Ty
payload in dispatcher arm). -/
theorem isTotalOnWeaken_natElim {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {motiveType : Ty level scope}
    {scrutineeRaw zeroRaw succRaw : RawTerm scope}
    {scrutinee : Term context Ty.nat scrutineeRaw}
    {zeroBranch : Term context motiveType zeroRaw}
    {succBranch : Term context (Ty.arrow Ty.nat motiveType) succRaw}
    (scrutineeIH : IsTotalOnWeaken scrutinee)
    (zeroIH : IsTotalOnWeaken zeroBranch)
    (succIH : IsTotalOnWeaken succBranch) :
    IsTotalOnWeaken (Term.natElim scrutinee zeroBranch succBranch) := by
  intro newType
  show (strengthenTyped? (Term.natElim
      (Term.weaken newType scrutinee)
      (Term.weaken newType zeroBranch)
      (Term.weaken newType succBranch))).isSome
  unfold strengthenTyped?
  unfold partialStrengthenTyped?
  split
  · next scrutineeRecurse =>
      exfalso
      have totHyp := scrutineeIH newType
      unfold strengthenTyped? at totHyp
      have : Option.isSome (none (α := StrengtheningResult
          (ContextStrengthening.dropNewest context newType)
          (Term.weaken newType scrutinee))) = true :=
        scrutineeRecurse ▸ totHyp
      cases this
  · split
    · next zeroRecurse =>
        exfalso
        have totHyp := zeroIH newType
        unfold strengthenTyped? at totHyp
        have : Option.isSome (none (α := StrengtheningResult
            (ContextStrengthening.dropNewest context newType)
            (Term.weaken newType zeroBranch))) = true :=
          zeroRecurse ▸ totHyp
        cases this
    · split
      · next succRecurse =>
          exfalso
          have totHyp := succIH newType
          unfold strengthenTyped? at totHyp
          have : Option.isSome (none (α := StrengtheningResult
              (ContextStrengthening.dropNewest context newType)
              (Term.weaken newType succBranch))) = true :=
            succRecurse ▸ totHyp
          cases this
      · rfl

/-- 3-IH non-binder totality: `Term.natRec`.  Pure 3-IH (no Ty
payload in dispatcher arm). -/
theorem isTotalOnWeaken_natRec {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {motiveType : Ty level scope}
    {scrutineeRaw zeroRaw succRaw : RawTerm scope}
    {scrutinee : Term context Ty.nat scrutineeRaw}
    {zeroBranch : Term context motiveType zeroRaw}
    {succBranch : Term context
      (Ty.arrow Ty.nat (Ty.arrow motiveType motiveType)) succRaw}
    (scrutineeIH : IsTotalOnWeaken scrutinee)
    (zeroIH : IsTotalOnWeaken zeroBranch)
    (succIH : IsTotalOnWeaken succBranch) :
    IsTotalOnWeaken (Term.natRec scrutinee zeroBranch succBranch) := by
  intro newType
  show (strengthenTyped? (Term.natRec
      (Term.weaken newType scrutinee)
      (Term.weaken newType zeroBranch)
      (Term.weaken newType succBranch))).isSome
  unfold strengthenTyped?
  unfold partialStrengthenTyped?
  split
  · next scrutineeRecurse =>
      exfalso
      have totHyp := scrutineeIH newType
      unfold strengthenTyped? at totHyp
      have : Option.isSome (none (α := StrengtheningResult
          (ContextStrengthening.dropNewest context newType)
          (Term.weaken newType scrutinee))) = true :=
        scrutineeRecurse ▸ totHyp
      cases this
  · split
    · next zeroRecurse =>
        exfalso
        have totHyp := zeroIH newType
        unfold strengthenTyped? at totHyp
        have : Option.isSome (none (α := StrengtheningResult
            (ContextStrengthening.dropNewest context newType)
            (Term.weaken newType zeroBranch))) = true :=
          zeroRecurse ▸ totHyp
        cases this
    · split
      · next succRecurse =>
          exfalso
          have totHyp := succIH newType
          unfold strengthenTyped? at totHyp
          have : Option.isSome (none (α := StrengtheningResult
              (ContextStrengthening.dropNewest context newType)
              (Term.weaken newType succBranch))) = true :=
            succRecurse ▸ totHyp
          cases this
      · rfl

/-- 3-IH non-binder totality: `Term.listElim`.  One Ty (elementType)
+ 3 Term IH (scrutinee, nilBranch, consBranch). -/
theorem isTotalOnWeaken_listElim {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {elementType motiveType : Ty level scope}
    {scrutineeRaw nilRaw consRaw : RawTerm scope}
    {scrutinee : Term context (Ty.listType elementType) scrutineeRaw}
    {nilBranch : Term context motiveType nilRaw}
    {consBranch : Term context
      (Ty.arrow elementType
        (Ty.arrow (Ty.listType elementType) motiveType)) consRaw}
    (scrutineeIH : IsTotalOnWeaken scrutinee)
    (nilIH : IsTotalOnWeaken nilBranch)
    (consIH : IsTotalOnWeaken consBranch) :
    IsTotalOnWeaken (Term.listElim scrutinee nilBranch consBranch) := by
  intro newType
  show (strengthenTyped? (Term.listElim
      (Term.weaken newType scrutinee)
      (Term.weaken newType nilBranch)
      (Term.weaken newType consBranch))).isSome
  unfold strengthenTyped?
  unfold partialStrengthenTyped?
  split
  · next elementFails =>
      exfalso
      have elementSuccess :
          elementType.weaken.partialStrengthen?
              (ContextStrengthening.dropNewest context newType).back =
            some elementType :=
        Ty.strengthen?_weaken elementType
      rw [elementSuccess] at elementFails
      cases elementFails
  · split
    · next scrutineeRecurse =>
        exfalso
        have totHyp := scrutineeIH newType
        unfold strengthenTyped? at totHyp
        have : Option.isSome (none (α := StrengtheningResult
            (ContextStrengthening.dropNewest context newType)
            (Term.weaken newType scrutinee))) = true :=
          scrutineeRecurse ▸ totHyp
        cases this
    · split
      · next nilRecurse =>
          exfalso
          have totHyp := nilIH newType
          unfold strengthenTyped? at totHyp
          have : Option.isSome (none (α := StrengtheningResult
              (ContextStrengthening.dropNewest context newType)
              (Term.weaken newType nilBranch))) = true :=
            nilRecurse ▸ totHyp
          cases this
      · split
        · next consRecurse =>
            exfalso
            have totHyp := consIH newType
            unfold strengthenTyped? at totHyp
            have : Option.isSome (none (α := StrengtheningResult
                (ContextStrengthening.dropNewest context newType)
                (Term.weaken newType consBranch))) = true :=
              consRecurse ▸ totHyp
            cases this
        · rfl

/-- 3-IH non-binder totality: `Term.optionMatch`.  One Ty (elementType)
+ 3 Term IH (scrutinee, noneBranch, someBranch). -/
theorem isTotalOnWeaken_optionMatch {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {elementType motiveType : Ty level scope}
    {scrutineeRaw noneRaw someRaw : RawTerm scope}
    {scrutinee : Term context (Ty.optionType elementType) scrutineeRaw}
    {noneBranch : Term context motiveType noneRaw}
    {someBranch : Term context (Ty.arrow elementType motiveType) someRaw}
    (scrutineeIH : IsTotalOnWeaken scrutinee)
    (noneIH : IsTotalOnWeaken noneBranch)
    (someIH : IsTotalOnWeaken someBranch) :
    IsTotalOnWeaken (Term.optionMatch scrutinee noneBranch someBranch) := by
  intro newType
  show (strengthenTyped? (Term.optionMatch
      (Term.weaken newType scrutinee)
      (Term.weaken newType noneBranch)
      (Term.weaken newType someBranch))).isSome
  unfold strengthenTyped?
  unfold partialStrengthenTyped?
  split
  · next elementFails =>
      exfalso
      have elementSuccess :
          elementType.weaken.partialStrengthen?
              (ContextStrengthening.dropNewest context newType).back =
            some elementType :=
        Ty.strengthen?_weaken elementType
      rw [elementSuccess] at elementFails
      cases elementFails
  · split
    · next scrutineeRecurse =>
        exfalso
        have totHyp := scrutineeIH newType
        unfold strengthenTyped? at totHyp
        have : Option.isSome (none (α := StrengtheningResult
            (ContextStrengthening.dropNewest context newType)
            (Term.weaken newType scrutinee))) = true :=
          scrutineeRecurse ▸ totHyp
        cases this
    · split
      · next noneRecurse =>
          exfalso
          have totHyp := noneIH newType
          unfold strengthenTyped? at totHyp
          have : Option.isSome (none (α := StrengtheningResult
              (ContextStrengthening.dropNewest context newType)
              (Term.weaken newType noneBranch))) = true :=
            noneRecurse ▸ totHyp
          cases this
      · split
        · next someRecurse =>
            exfalso
            have totHyp := someIH newType
            unfold strengthenTyped? at totHyp
            have : Option.isSome (none (α := StrengtheningResult
                (ContextStrengthening.dropNewest context newType)
                (Term.weaken newType someBranch))) = true :=
              someRecurse ▸ totHyp
            cases this
        · rfl

/-- 3-IH non-binder totality: `Term.eitherMatch`.  Three Ty (leftType,
rightType, motiveType) + 3 Term IH. -/
theorem isTotalOnWeaken_eitherMatch {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {leftType rightType motiveType : Ty level scope}
    {scrutineeRaw leftRaw rightRaw : RawTerm scope}
    {scrutinee : Term context (Ty.eitherType leftType rightType)
      scrutineeRaw}
    {leftBranch : Term context (Ty.arrow leftType motiveType) leftRaw}
    {rightBranch : Term context (Ty.arrow rightType motiveType) rightRaw}
    (scrutineeIH : IsTotalOnWeaken scrutinee)
    (leftIH : IsTotalOnWeaken leftBranch)
    (rightIH : IsTotalOnWeaken rightBranch) :
    IsTotalOnWeaken (Term.eitherMatch scrutinee leftBranch rightBranch) := by
  intro newType
  show (strengthenTyped? (Term.eitherMatch
      (Term.weaken newType scrutinee)
      (Term.weaken newType leftBranch)
      (Term.weaken newType rightBranch))).isSome
  unfold strengthenTyped?
  unfold partialStrengthenTyped?
  split
  · next leftFails =>
      exfalso
      have leftSuccess :
          leftType.weaken.partialStrengthen?
              (ContextStrengthening.dropNewest context newType).back =
            some leftType :=
        Ty.strengthen?_weaken leftType
      rw [leftSuccess] at leftFails
      cases leftFails
  · split
    · next rightFails =>
        exfalso
        have rightSuccess :
            rightType.weaken.partialStrengthen?
                (ContextStrengthening.dropNewest context newType).back =
              some rightType :=
          Ty.strengthen?_weaken rightType
        rw [rightSuccess] at rightFails
        cases rightFails
    · split
      · next motiveFails =>
          exfalso
          have motiveSuccess :
              motiveType.weaken.partialStrengthen?
                  (ContextStrengthening.dropNewest context newType).back =
                some motiveType :=
            Ty.strengthen?_weaken motiveType
          rw [motiveSuccess] at motiveFails
          cases motiveFails
      · split
        · next scrutineeRecurse =>
            exfalso
            have totHyp := scrutineeIH newType
            unfold strengthenTyped? at totHyp
            have : Option.isSome (none (α := StrengtheningResult
                (ContextStrengthening.dropNewest context newType)
                (Term.weaken newType scrutinee))) = true :=
              scrutineeRecurse ▸ totHyp
            cases this
        · split
          · next leftRecurse =>
              exfalso
              have totHyp := leftIH newType
              unfold strengthenTyped? at totHyp
              have : Option.isSome (none (α := StrengtheningResult
                  (ContextStrengthening.dropNewest context newType)
                  (Term.weaken newType leftBranch))) = true :=
                leftRecurse ▸ totHyp
              cases this
          · split
            · next rightRecurse =>
                exfalso
                have totHyp := rightIH newType
                unfold strengthenTyped? at totHyp
                have : Option.isSome (none (α := StrengtheningResult
                    (ContextStrengthening.dropNewest context newType)
                    (Term.weaken newType rightBranch))) = true :=
                  rightRecurse ▸ totHyp
                cases this
            · rfl

/-- 2-IH non-binder totality: `Term.effectPerform`.  One RawTerm
(effectTag) + signature with two Ty carriers + two Term IH. -/
theorem isTotalOnWeaken_effectPerform {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (effectTag : RawTerm scope)
    (effectRow : Effects.EffectRow)
    (operationSignature : Effects.OperationSignature (Ty level scope))
    (canPerformOperation :
      Effects.CanPerform effectRow operationSignature)
    {operationRaw argumentsRaw : RawTerm scope}
    {operationTag : Term context
      (Ty.effect operationSignature.argumentCarrier effectTag)
      operationRaw}
    {arguments : Term context operationSignature.argumentCarrier
      argumentsRaw}
    (operationIH : IsTotalOnWeaken operationTag)
    (argumentsIH : IsTotalOnWeaken arguments) :
    IsTotalOnWeaken (Term.effectPerform effectTag effectRow
      operationSignature canPerformOperation operationTag arguments) := by
  intro newType
  show (strengthenTyped? (Term.effectPerform effectTag.weaken
      effectRow
      (operationSignature.map
        (fun carrierType : Ty level scope =>
          (carrierType : Ty level scope).rename RawRenaming.weaken))
      (Effects.CanPerform.map
        (fun carrierType : Ty level scope =>
          (carrierType : Ty level scope).rename RawRenaming.weaken)
        canPerformOperation)
      (Term.weaken newType operationTag)
      (Term.weaken newType arguments))).isSome
  unfold strengthenTyped?
  unfold partialStrengthenTyped?
  split
  · next effectTagFails =>
      exfalso
      have effectTagSuccess :
          effectTag.weaken.partialStrengthen?
              (ContextStrengthening.dropNewest context newType).back =
            some effectTag :=
        RawTerm.strengthen?_weaken effectTag
      rw [effectTagSuccess] at effectTagFails
      cases effectTagFails
  · split
    · next argumentCarrierFails =>
        exfalso
        have argumentCarrierSuccess :
            (Effects.OperationSignature.map
              (fun carrierType : Ty level scope =>
                (carrierType : Ty level scope).rename RawRenaming.weaken)
              operationSignature).argumentCarrier.partialStrengthen?
                (ContextStrengthening.dropNewest context newType).back =
              some operationSignature.argumentCarrier := by
          change operationSignature.argumentCarrier.weaken.partialStrengthen?
              _ = _
          exact Ty.strengthen?_weaken operationSignature.argumentCarrier
        rw [argumentCarrierSuccess] at argumentCarrierFails
        cases argumentCarrierFails
    · split
      · next resultCarrierFails =>
          exfalso
          have resultCarrierSuccess :
              (Effects.OperationSignature.map
                (fun carrierType : Ty level scope =>
                  (carrierType : Ty level scope).rename RawRenaming.weaken)
                operationSignature).resultCarrier.partialStrengthen?
                  (ContextStrengthening.dropNewest context newType).back =
                some operationSignature.resultCarrier := by
            change operationSignature.resultCarrier.weaken.partialStrengthen?
                _ = _
            exact Ty.strengthen?_weaken operationSignature.resultCarrier
          rw [resultCarrierSuccess] at resultCarrierFails
          cases resultCarrierFails
      · split
        · next operationRecurse =>
            exfalso
            have totHyp := operationIH newType
            unfold strengthenTyped? at totHyp
            have : Option.isSome (none (α := StrengtheningResult
                (ContextStrengthening.dropNewest context newType)
                (Term.weaken newType operationTag))) = true :=
              operationRecurse ▸ totHyp
            cases this
        · split
          · next argumentsRecurse =>
              exfalso
              have totHyp := argumentsIH newType
              unfold strengthenTyped? at totHyp
              have : Option.isSome (none (α := StrengtheningResult
                  (ContextStrengthening.dropNewest context newType)
                  (Term.weaken newType arguments))) = true :=
                argumentsRecurse ▸ totHyp
              cases this
          · rfl

end Term

end LeanFX2
