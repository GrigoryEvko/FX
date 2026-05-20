import LeanFX2.Term.StrengtheningImage.AggregatorTotalBridgeAdvanced

/-! # Term/StrengtheningImage/AggregatorTotalBridgeEliminators

Bridge totality wrappers for natural, list, option, and either eliminators.
-/

namespace LeanFX2

namespace Term

/-- 3-IH totality: `Term.natElim`.  Source type is `motiveType`
directly (✓).  Dispatcher takes only 3 IH recurses (no type witness
checks).  scrutinee : Ty.nat (closed-atomic), zeroBranch : motiveType,
succBranch : Ty.arrow Ty.nat motiveType.  Construct succ's arrow type
strengthens from typeStrengthens + Ty.nat trivial. -/
theorem isAggregatorTotal_natElim {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope}
    {motiveType : Ty level sourceScope}
    {scrutineeRaw zeroRaw succRaw : RawTerm sourceScope}
    {scrutinee : Term sourceCtx Ty.nat scrutineeRaw}
    {zeroBranch : Term sourceCtx motiveType zeroRaw}
    {succBranch :
      Term sourceCtx (Ty.arrow Ty.nat motiveType) succRaw}
    (scrutineeTotal : IsAggregatorTotal scrutinee)
    (zeroTotal : IsAggregatorTotal zeroBranch)
    (succTotal : IsAggregatorTotal succBranch) :
    IsAggregatorTotal (Term.natElim scrutinee zeroBranch succBranch) := by
  intros _ _ strengthening targetMotiveType _ typeStrengthens rawStrengthens
  change Option.mapThree
      (scrutineeRaw.partialStrengthen? strengthening.back)
      (zeroRaw.partialStrengthen? strengthening.back)
      (succRaw.partialStrengthen? strengthening.back)
      RawTerm.natElim = some _ at rawStrengthens
  obtain ⟨_, _, _, scrutineeRawSuccess, zeroRawSuccess, succRawSuccess, _⟩ :=
    Option.mapThree_eq_some rawStrengthens
  have natStrengthens :
      (Ty.nat : Ty level sourceScope).partialStrengthen?
          strengthening.back =
        some Ty.nat := rfl
  have arrowStrengthens :
      (Ty.arrow Ty.nat motiveType).partialStrengthen?
          strengthening.back =
        some (Ty.arrow Ty.nat targetMotiveType) := by
    show Option.mapTwo
        ((Ty.nat : Ty level sourceScope).partialStrengthen?
          strengthening.back)
        (motiveType.partialStrengthen? strengthening.back)
        Ty.arrow = _
    rw [natStrengthens, typeStrengthens]
    rfl
  have scrutineeTotalCall :=
    scrutineeTotal strengthening natStrengthens scrutineeRawSuccess
  have zeroTotalCall :=
    zeroTotal strengthening typeStrengthens zeroRawSuccess
  have succTotalCall :=
    succTotal strengthening arrowStrengthens succRawSuccess
  dsimp only [partialStrengthenTyped?]
  split
  · next scrutineeFails =>
      rw [scrutineeFails] at scrutineeTotalCall
      cases scrutineeTotalCall
  · next _ _ =>
      split
      · next zeroFails =>
          rw [zeroFails] at zeroTotalCall
          cases zeroTotalCall
      · next _ _ =>
          split
          · next succFails =>
              rw [succFails] at succTotalCall
              cases succTotalCall
          · rfl

/-- 3-IH totality: `Term.natRec`.  Source type motiveType (✓).
Like natElim but succBranch's type is
`Ty.arrow Ty.nat (Ty.arrow motiveType motiveType)`. -/
theorem isAggregatorTotal_natRec {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope}
    {motiveType : Ty level sourceScope}
    {scrutineeRaw zeroRaw succRaw : RawTerm sourceScope}
    {scrutinee : Term sourceCtx Ty.nat scrutineeRaw}
    {zeroBranch : Term sourceCtx motiveType zeroRaw}
    {succBranch :
      Term sourceCtx
        (Ty.arrow Ty.nat (Ty.arrow motiveType motiveType)) succRaw}
    (scrutineeTotal : IsAggregatorTotal scrutinee)
    (zeroTotal : IsAggregatorTotal zeroBranch)
    (succTotal : IsAggregatorTotal succBranch) :
    IsAggregatorTotal (Term.natRec scrutinee zeroBranch succBranch) := by
  intros _ _ strengthening targetMotiveType _ typeStrengthens rawStrengthens
  change Option.mapThree
      (scrutineeRaw.partialStrengthen? strengthening.back)
      (zeroRaw.partialStrengthen? strengthening.back)
      (succRaw.partialStrengthen? strengthening.back)
      RawTerm.natRec = some _ at rawStrengthens
  obtain ⟨_, _, _, scrutineeRawSuccess, zeroRawSuccess, succRawSuccess, _⟩ :=
    Option.mapThree_eq_some rawStrengthens
  have natStrengthens :
      (Ty.nat : Ty level sourceScope).partialStrengthen?
          strengthening.back =
        some Ty.nat := rfl
  have innerArrowStrengthens :
      (Ty.arrow motiveType motiveType).partialStrengthen?
          strengthening.back =
        some (Ty.arrow targetMotiveType targetMotiveType) := by
    show Option.mapTwo
        (motiveType.partialStrengthen? strengthening.back)
        (motiveType.partialStrengthen? strengthening.back)
        Ty.arrow = _
    rw [typeStrengthens]
    rfl
  have outerArrowStrengthens :
      (Ty.arrow Ty.nat (Ty.arrow motiveType motiveType)).partialStrengthen?
          strengthening.back =
        some (Ty.arrow Ty.nat (Ty.arrow targetMotiveType
          targetMotiveType)) := by
    show Option.mapTwo
        ((Ty.nat : Ty level sourceScope).partialStrengthen?
          strengthening.back)
        ((Ty.arrow motiveType motiveType).partialStrengthen?
          strengthening.back)
        Ty.arrow = _
    rw [natStrengthens, innerArrowStrengthens]
    rfl
  have scrutineeTotalCall :=
    scrutineeTotal strengthening natStrengthens scrutineeRawSuccess
  have zeroTotalCall :=
    zeroTotal strengthening typeStrengthens zeroRawSuccess
  have succTotalCall :=
    succTotal strengthening outerArrowStrengthens succRawSuccess
  dsimp only [partialStrengthenTyped?]
  split
  · next scrutineeFails =>
      rw [scrutineeFails] at scrutineeTotalCall
      cases scrutineeTotalCall
  · next _ _ =>
      split
      · next zeroFails =>
          rw [zeroFails] at zeroTotalCall
          cases zeroTotalCall
      · next _ _ =>
          split
          · next succFails =>
              rw [succFails] at succTotalCall
              cases succTotalCall
          · rfl

/-- Bridge totality wrapper for `Term.listElim`.  Source type
motiveType (✓); dispatcher needs elementType.back + 3 IH children.
Take elementType.back as extra hypothesis. -/
theorem isAggregatorTotal_listElim_with_element {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope}
    {elementType motiveType : Ty level sourceScope}
    {scrutineeRaw nilRaw consRaw : RawTerm sourceScope}
    {scrutinee :
      Term sourceCtx (Ty.listType elementType) scrutineeRaw}
    {nilBranch : Term sourceCtx motiveType nilRaw}
    {consBranch :
      Term sourceCtx (Ty.arrow elementType
        (Ty.arrow (Ty.listType elementType) motiveType)) consRaw}
    (scrutineeTotal : IsAggregatorTotal scrutinee)
    (nilTotal : IsAggregatorTotal nilBranch)
    (consTotal : IsAggregatorTotal consBranch)
    (elementTypeTotal :
      ∀ {targetScope : Nat} {targetCtx : Ctx mode level targetScope}
        (strengthening : ContextStrengthening sourceCtx targetCtx)
        {targetMotiveType : Ty level targetScope},
        motiveType.partialStrengthen? strengthening.back =
            some targetMotiveType →
        ∃ targetElementType,
          elementType.partialStrengthen? strengthening.back =
            some targetElementType) :
    IsAggregatorTotal
      (Term.listElim scrutinee nilBranch consBranch) := by
  intros _ _ strengthening targetMotiveType _ typeStrengthens rawStrengthens
  change Option.mapThree
      (scrutineeRaw.partialStrengthen? strengthening.back)
      (nilRaw.partialStrengthen? strengthening.back)
      (consRaw.partialStrengthen? strengthening.back)
      RawTerm.listElim = some _ at rawStrengthens
  obtain ⟨_, _, _, scrutineeRawSuccess, nilRawSuccess, consRawSuccess, _⟩ :=
    Option.mapThree_eq_some rawStrengthens
  obtain ⟨targetElementType, elementSuccess⟩ :=
    elementTypeTotal strengthening typeStrengthens
  -- scrutinee type: Ty.listType elementType
  have listTypeStrengthens :
      (Ty.listType elementType).partialStrengthen?
          strengthening.back =
        some (Ty.listType targetElementType) := by
    show (match elementType.partialStrengthen? strengthening.back with
          | some r => some (Ty.listType r)
          | none => none) = _
    rw [elementSuccess]
  -- consBranch type: Ty.arrow elementType (Ty.arrow (Ty.listType elementType) motiveType)
  have innerArrowStrengthens :
      (Ty.arrow (Ty.listType elementType) motiveType).partialStrengthen?
          strengthening.back =
        some (Ty.arrow (Ty.listType targetElementType) targetMotiveType) := by
    show Option.mapTwo
        ((Ty.listType elementType).partialStrengthen? strengthening.back)
        (motiveType.partialStrengthen? strengthening.back)
        Ty.arrow = _
    rw [listTypeStrengthens, typeStrengthens]
    rfl
  have outerArrowStrengthens :
      (Ty.arrow elementType
        (Ty.arrow (Ty.listType elementType) motiveType)).partialStrengthen?
          strengthening.back =
        some (Ty.arrow targetElementType
          (Ty.arrow (Ty.listType targetElementType)
            targetMotiveType)) := by
    show Option.mapTwo
        (elementType.partialStrengthen? strengthening.back)
        ((Ty.arrow (Ty.listType elementType) motiveType).partialStrengthen?
          strengthening.back)
        Ty.arrow = _
    rw [elementSuccess, innerArrowStrengthens]
    rfl
  have scrutineeTotalCall :=
    scrutineeTotal strengthening listTypeStrengthens scrutineeRawSuccess
  have nilTotalCall :=
    nilTotal strengthening typeStrengthens nilRawSuccess
  have consTotalCall :=
    consTotal strengthening outerArrowStrengthens consRawSuccess
  dsimp only [partialStrengthenTyped?]
  split
  · next elementFails =>
      rw [elementSuccess] at elementFails
      cases elementFails
  · next _ _ =>
      split
      · next scrutineeFails =>
          rw [scrutineeFails] at scrutineeTotalCall
          cases scrutineeTotalCall
      · next _ _ =>
          split
          · next nilFails =>
              rw [nilFails] at nilTotalCall
              cases nilTotalCall
          · next _ _ =>
              split
              · next consFails =>
                  rw [consFails] at consTotalCall
                  cases consTotalCall
              · rfl

/-- Bridge totality wrapper for `Term.optionMatch`.  Source type
motiveType (✓); dispatcher needs elementType.back + 3 IH children. -/
theorem isAggregatorTotal_optionMatch_with_element {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope}
    {elementType motiveType : Ty level sourceScope}
    {scrutineeRaw noneRaw someRaw : RawTerm sourceScope}
    {scrutinee :
      Term sourceCtx (Ty.optionType elementType) scrutineeRaw}
    {noneBranch : Term sourceCtx motiveType noneRaw}
    {someBranch :
      Term sourceCtx (Ty.arrow elementType motiveType) someRaw}
    (scrutineeTotal : IsAggregatorTotal scrutinee)
    (noneTotal : IsAggregatorTotal noneBranch)
    (someTotal : IsAggregatorTotal someBranch)
    (elementTypeTotal :
      ∀ {targetScope : Nat} {targetCtx : Ctx mode level targetScope}
        (strengthening : ContextStrengthening sourceCtx targetCtx)
        {targetMotiveType : Ty level targetScope},
        motiveType.partialStrengthen? strengthening.back =
            some targetMotiveType →
        ∃ targetElementType,
          elementType.partialStrengthen? strengthening.back =
            some targetElementType) :
    IsAggregatorTotal
      (Term.optionMatch scrutinee noneBranch someBranch) := by
  intros _ _ strengthening targetMotiveType _ typeStrengthens rawStrengthens
  change Option.mapThree
      (scrutineeRaw.partialStrengthen? strengthening.back)
      (noneRaw.partialStrengthen? strengthening.back)
      (someRaw.partialStrengthen? strengthening.back)
      RawTerm.optionMatch = some _ at rawStrengthens
  obtain ⟨_, _, _, scrutineeRawSuccess, noneRawSuccess, someRawSuccess, _⟩ :=
    Option.mapThree_eq_some rawStrengthens
  obtain ⟨targetElementType, elementSuccess⟩ :=
    elementTypeTotal strengthening typeStrengthens
  have optionTypeStrengthens :
      (Ty.optionType elementType).partialStrengthen?
          strengthening.back =
        some (Ty.optionType targetElementType) := by
    show (match elementType.partialStrengthen? strengthening.back with
          | some r => some (Ty.optionType r)
          | none => none) = _
    rw [elementSuccess]
  have arrowStrengthens :
      (Ty.arrow elementType motiveType).partialStrengthen?
          strengthening.back =
        some (Ty.arrow targetElementType targetMotiveType) := by
    show Option.mapTwo
        (elementType.partialStrengthen? strengthening.back)
        (motiveType.partialStrengthen? strengthening.back)
        Ty.arrow = _
    rw [elementSuccess, typeStrengthens]
    rfl
  have scrutineeTotalCall :=
    scrutineeTotal strengthening optionTypeStrengthens scrutineeRawSuccess
  have noneTotalCall :=
    noneTotal strengthening typeStrengthens noneRawSuccess
  have someTotalCall :=
    someTotal strengthening arrowStrengthens someRawSuccess
  dsimp only [partialStrengthenTyped?]
  split
  · next elementFails =>
      rw [elementSuccess] at elementFails
      cases elementFails
  · next _ _ =>
      split
      · next scrutineeFails =>
          rw [scrutineeFails] at scrutineeTotalCall
          cases scrutineeTotalCall
      · next _ _ =>
          split
          · next noneFails =>
              rw [noneFails] at noneTotalCall
              cases noneTotalCall
          · next _ _ =>
              split
              · next someFails =>
                  rw [someFails] at someTotalCall
                  cases someTotalCall
              · rfl

/-- Bridge totality wrapper for `Term.eitherMatch`.  Source type
motiveType (✓); dispatcher needs leftType.back + rightType.back +
3 IH children. -/
theorem isAggregatorTotal_eitherMatch_with_lr_types {mode : Mode}
    {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope}
    {leftType rightType motiveType : Ty level sourceScope}
    {scrutineeRaw leftRaw rightRaw : RawTerm sourceScope}
    {scrutinee :
      Term sourceCtx (Ty.eitherType leftType rightType) scrutineeRaw}
    {leftBranch : Term sourceCtx (Ty.arrow leftType motiveType) leftRaw}
    {rightBranch : Term sourceCtx (Ty.arrow rightType motiveType) rightRaw}
    (scrutineeTotal : IsAggregatorTotal scrutinee)
    (leftTotal : IsAggregatorTotal leftBranch)
    (rightTotal : IsAggregatorTotal rightBranch)
    (lrTypesTotal :
      ∀ {targetScope : Nat} {targetCtx : Ctx mode level targetScope}
        (strengthening : ContextStrengthening sourceCtx targetCtx)
        {targetMotiveType : Ty level targetScope},
        motiveType.partialStrengthen? strengthening.back =
            some targetMotiveType →
        ∃ targetLeftType targetRightType,
          leftType.partialStrengthen? strengthening.back =
              some targetLeftType ∧
          rightType.partialStrengthen? strengthening.back =
              some targetRightType) :
    IsAggregatorTotal
      (Term.eitherMatch scrutinee leftBranch rightBranch) := by
  intros _ _ strengthening targetMotiveType _ typeStrengthens rawStrengthens
  change Option.mapThree
      (scrutineeRaw.partialStrengthen? strengthening.back)
      (leftRaw.partialStrengthen? strengthening.back)
      (rightRaw.partialStrengthen? strengthening.back)
      RawTerm.eitherMatch = some _ at rawStrengthens
  obtain ⟨_, _, _, scrutineeRawSuccess, leftRawSuccess, rightRawSuccess, _⟩ :=
    Option.mapThree_eq_some rawStrengthens
  obtain ⟨targetLeftType, targetRightType, leftTypeSuccess,
    rightTypeSuccess⟩ :=
    lrTypesTotal strengthening typeStrengthens
  have eitherTypeStrengthens :
      (Ty.eitherType leftType rightType).partialStrengthen?
          strengthening.back =
        some (Ty.eitherType targetLeftType targetRightType) := by
    show Option.mapTwo
        (leftType.partialStrengthen? strengthening.back)
        (rightType.partialStrengthen? strengthening.back)
        Ty.eitherType = _
    rw [leftTypeSuccess, rightTypeSuccess]
    rfl
  have leftArrowStrengthens :
      (Ty.arrow leftType motiveType).partialStrengthen?
          strengthening.back =
        some (Ty.arrow targetLeftType targetMotiveType) := by
    show Option.mapTwo
        (leftType.partialStrengthen? strengthening.back)
        (motiveType.partialStrengthen? strengthening.back)
        Ty.arrow = _
    rw [leftTypeSuccess, typeStrengthens]
    rfl
  have rightArrowStrengthens :
      (Ty.arrow rightType motiveType).partialStrengthen?
          strengthening.back =
        some (Ty.arrow targetRightType targetMotiveType) := by
    show Option.mapTwo
        (rightType.partialStrengthen? strengthening.back)
        (motiveType.partialStrengthen? strengthening.back)
        Ty.arrow = _
    rw [rightTypeSuccess, typeStrengthens]
    rfl
  have scrutineeTotalCall :=
    scrutineeTotal strengthening eitherTypeStrengthens scrutineeRawSuccess
  have leftTotalCall :=
    leftTotal strengthening leftArrowStrengthens leftRawSuccess
  have rightTotalCall :=
    rightTotal strengthening rightArrowStrengthens rightRawSuccess
  dsimp only [partialStrengthenTyped?]
  split
  · next leftFails =>
      rw [leftTypeSuccess] at leftFails
      cases leftFails
  · next _ _ =>
      split
      · next rightFails =>
          rw [rightTypeSuccess] at rightFails
          cases rightFails
      · next _ _ =>
          split
          · next motiveFails =>
              rw [typeStrengthens] at motiveFails
              cases motiveFails
          · next _ _ =>
              split
              · next scrutineeFails =>
                  rw [scrutineeFails] at scrutineeTotalCall
                  cases scrutineeTotalCall
              · next _ _ =>
                  split
                  · next leftBFails =>
                      rw [leftBFails] at leftTotalCall
                      cases leftTotalCall
                  · next _ _ =>
                      split
                      · next rightBFails =>
                          rw [rightBFails] at rightTotalCall
                          cases rightTotalCall
                      · rfl

end Term

end LeanFX2
