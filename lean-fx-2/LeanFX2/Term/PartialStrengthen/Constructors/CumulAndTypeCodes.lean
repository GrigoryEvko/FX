import LeanFX2.Term.PartialStrengthen.Constructors.SigmaRecordCodataSession

/-! # Term/PartialStrengthen/Constructors/CumulAndTypeCodes

Typed partial-strengthening producers for cumulativity promotion and
universe/type-code terms.
-/

namespace LeanFX2

namespace Term

/-- Cumulativity promotion strengthens by strengthening its inner
type-code payload and rebuilding the promotion at the target context. -/
def partialStrengthenTypedCumulUp {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    (lowerLevel higherLevel : UniverseLevel)
    (cumulMonotone : lowerLevel.toNat ≤ higherLevel.toNat)
    (levelLeLow : lowerLevel.toNat + 1 ≤ level)
    (levelLeHigh : higherLevel.toNat + 1 ≤ level)
    {codeRaw : RawTerm sourceScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    {typeCode :
      Term sourceCtx (Ty.universe lowerLevel levelLeLow) codeRaw}
    (codeResult : StrengtheningResult strengthening typeCode) :
    StrengtheningResult strengthening
      (Term.cumulUp lowerLevel higherLevel cumulMonotone levelLeLow
        levelLeHigh typeCode) := by
  cases codeResult with
  | mk targetCodeType targetCodeRaw targetCodeTerm codeTypeStrengthens
      codeRawStrengthens codeTypeRenames codeRawRenames =>
      cases codeTypeStrengthens
      exact {
        targetType := Ty.universe higherLevel levelLeHigh
        targetRaw := RawTerm.cumulUpMarker targetCodeRaw
        targetTerm := Term.cumulUp lowerLevel higherLevel cumulMonotone
          levelLeLow levelLeHigh targetCodeTerm
        typeStrengthens := rfl
        rawStrengthens := by
          change
            (match codeRaw.partialStrengthen? strengthening.back with
            | some strengthenedCode =>
                some (RawTerm.cumulUpMarker strengthenedCode)
            | none => none) =
              some (RawTerm.cumulUpMarker targetCodeRaw)
          rw [codeRawStrengthens]
        typeRenames := rfl
        rawRenames := congrArg RawTerm.cumulUpMarker codeRawRenames
      }

/-- Universe-code terms strengthen through every context strengthening.

The raw universe code carries only the encoded inner universe level, so
no scope-indexed payload needs strengthening. -/
def partialStrengthenTypedUniverseCode {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    (strengthening : ContextStrengthening sourceCtx targetCtx)
    (innerLevel outerLevel : UniverseLevel)
    (cumulOk : innerLevel.toNat ≤ outerLevel.toNat)
    (levelLe : outerLevel.toNat + 1 ≤ level) :
    StrengtheningResult strengthening
      (Term.universeCode (context := sourceCtx) innerLevel outerLevel
        cumulOk levelLe) where
  targetType := Ty.universe outerLevel levelLe
  targetRaw := RawTerm.universeCode innerLevel.toNat
  targetTerm := Term.universeCode (context := targetCtx) innerLevel
    outerLevel cumulOk levelLe
  typeStrengthens := rfl
  rawStrengthens := rfl
  typeRenames := rfl
  rawRenames := rfl

/-- Arrow type-code terms strengthen by strengthening both schematic
raw payloads. -/
def partialStrengthenTypedArrowCode {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    (domainCodeRaw codomainCodeRaw : RawTerm sourceScope)
    (targetDomainCodeRaw targetCodomainCodeRaw : RawTerm targetScope)
    (domainStrengthens :
      domainCodeRaw.partialStrengthen? strengthening.back =
        some targetDomainCodeRaw)
    (codomainStrengthens :
      codomainCodeRaw.partialStrengthen? strengthening.back =
        some targetCodomainCodeRaw) :
    StrengtheningResult strengthening
      (Term.arrowCode (context := sourceCtx) outerLevel levelLe
        domainCodeRaw codomainCodeRaw) where
  targetType := Ty.universe outerLevel levelLe
  targetRaw := RawTerm.arrowCode targetDomainCodeRaw targetCodomainCodeRaw
  targetTerm := Term.arrowCode (context := targetCtx) outerLevel levelLe
    targetDomainCodeRaw targetCodomainCodeRaw
  typeStrengthens := rfl
  rawStrengthens := by
    change
      Option.mapTwo
        (domainCodeRaw.partialStrengthen? strengthening.back)
        (codomainCodeRaw.partialStrengthen? strengthening.back)
        RawTerm.arrowCode =
          some (RawTerm.arrowCode targetDomainCodeRaw targetCodomainCodeRaw)
    rw [domainStrengthens, codomainStrengthens]
    rfl
  typeRenames := rfl
  rawRenames :=
    RawTerm.partialStrengthen?_imp_rename
      (RawTerm.arrowCode domainCodeRaw codomainCodeRaw)
      strengthening.forward strengthening.back strengthening.injectsBack
      (RawTerm.arrowCode targetDomainCodeRaw targetCodomainCodeRaw)
      (by
        change
          Option.mapTwo
            (domainCodeRaw.partialStrengthen? strengthening.back)
            (codomainCodeRaw.partialStrengthen? strengthening.back)
            RawTerm.arrowCode =
              some (RawTerm.arrowCode targetDomainCodeRaw targetCodomainCodeRaw)
        rw [domainStrengthens, codomainStrengthens]
        rfl)

/-- Dependent-Pi type-code terms strengthen by strengthening the domain
payload at the current context and the codomain payload under the lifted
context strengthening. -/
def partialStrengthenTypedPiTyCode {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    (domainCodeRaw : RawTerm sourceScope)
    (codomainCodeRaw : RawTerm (sourceScope + 1))
    (targetDomainCodeRaw : RawTerm targetScope)
    (targetCodomainCodeRaw : RawTerm (targetScope + 1))
    (domainStrengthens :
      domainCodeRaw.partialStrengthen? strengthening.back =
        some targetDomainCodeRaw)
    (codomainStrengthens :
      codomainCodeRaw.partialStrengthen? strengthening.back.lift =
        some targetCodomainCodeRaw) :
    StrengtheningResult strengthening
      (Term.piTyCode (context := sourceCtx) outerLevel levelLe
        domainCodeRaw codomainCodeRaw) where
  targetType := Ty.universe outerLevel levelLe
  targetRaw := RawTerm.piTyCode targetDomainCodeRaw targetCodomainCodeRaw
  targetTerm := Term.piTyCode (context := targetCtx) outerLevel levelLe
    targetDomainCodeRaw targetCodomainCodeRaw
  typeStrengthens := rfl
  rawStrengthens := by
    change
      Option.mapTwo
        (domainCodeRaw.partialStrengthen? strengthening.back)
        (codomainCodeRaw.partialStrengthen? strengthening.back.lift)
        RawTerm.piTyCode =
          some (RawTerm.piTyCode targetDomainCodeRaw targetCodomainCodeRaw)
    rw [domainStrengthens, codomainStrengthens]
    rfl
  typeRenames := rfl
  rawRenames :=
    RawTerm.partialStrengthen?_imp_rename
      (RawTerm.piTyCode domainCodeRaw codomainCodeRaw)
      strengthening.forward strengthening.back strengthening.injectsBack
      (RawTerm.piTyCode targetDomainCodeRaw targetCodomainCodeRaw)
      (by
        change
          Option.mapTwo
            (domainCodeRaw.partialStrengthen? strengthening.back)
            (codomainCodeRaw.partialStrengthen? strengthening.back.lift)
            RawTerm.piTyCode =
              some (RawTerm.piTyCode targetDomainCodeRaw targetCodomainCodeRaw)
        rw [domainStrengthens, codomainStrengthens]
        rfl)

/-- Dependent-Sigma type-code terms strengthen by strengthening the
domain payload at the current context and the codomain payload under the
lifted context strengthening. -/
def partialStrengthenTypedSigmaTyCode {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    (domainCodeRaw : RawTerm sourceScope)
    (codomainCodeRaw : RawTerm (sourceScope + 1))
    (targetDomainCodeRaw : RawTerm targetScope)
    (targetCodomainCodeRaw : RawTerm (targetScope + 1))
    (domainStrengthens :
      domainCodeRaw.partialStrengthen? strengthening.back =
        some targetDomainCodeRaw)
    (codomainStrengthens :
      codomainCodeRaw.partialStrengthen? strengthening.back.lift =
        some targetCodomainCodeRaw) :
    StrengtheningResult strengthening
      (Term.sigmaTyCode (context := sourceCtx) outerLevel levelLe
        domainCodeRaw codomainCodeRaw) where
  targetType := Ty.universe outerLevel levelLe
  targetRaw := RawTerm.sigmaTyCode targetDomainCodeRaw targetCodomainCodeRaw
  targetTerm := Term.sigmaTyCode (context := targetCtx) outerLevel levelLe
    targetDomainCodeRaw targetCodomainCodeRaw
  typeStrengthens := rfl
  rawStrengthens := by
    change
      Option.mapTwo
        (domainCodeRaw.partialStrengthen? strengthening.back)
        (codomainCodeRaw.partialStrengthen? strengthening.back.lift)
        RawTerm.sigmaTyCode =
          some (RawTerm.sigmaTyCode targetDomainCodeRaw targetCodomainCodeRaw)
    rw [domainStrengthens, codomainStrengthens]
    rfl
  typeRenames := rfl
  rawRenames :=
    RawTerm.partialStrengthen?_imp_rename
      (RawTerm.sigmaTyCode domainCodeRaw codomainCodeRaw)
      strengthening.forward strengthening.back strengthening.injectsBack
      (RawTerm.sigmaTyCode targetDomainCodeRaw targetCodomainCodeRaw)
      (by
        change
          Option.mapTwo
            (domainCodeRaw.partialStrengthen? strengthening.back)
            (codomainCodeRaw.partialStrengthen? strengthening.back.lift)
            RawTerm.sigmaTyCode =
              some (RawTerm.sigmaTyCode targetDomainCodeRaw
                targetCodomainCodeRaw)
        rw [domainStrengthens, codomainStrengthens]
        rfl)

/-- Product type-code terms strengthen by strengthening both schematic
raw payloads. -/
def partialStrengthenTypedProductCode {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    (firstCodeRaw secondCodeRaw : RawTerm sourceScope)
    (targetFirstCodeRaw targetSecondCodeRaw : RawTerm targetScope)
    (firstStrengthens :
      firstCodeRaw.partialStrengthen? strengthening.back =
        some targetFirstCodeRaw)
    (secondStrengthens :
      secondCodeRaw.partialStrengthen? strengthening.back =
        some targetSecondCodeRaw) :
    StrengtheningResult strengthening
      (Term.productCode (context := sourceCtx) outerLevel levelLe
        firstCodeRaw secondCodeRaw) where
  targetType := Ty.universe outerLevel levelLe
  targetRaw := RawTerm.productCode targetFirstCodeRaw targetSecondCodeRaw
  targetTerm := Term.productCode (context := targetCtx) outerLevel levelLe
    targetFirstCodeRaw targetSecondCodeRaw
  typeStrengthens := rfl
  rawStrengthens := by
    change
      Option.mapTwo
        (firstCodeRaw.partialStrengthen? strengthening.back)
        (secondCodeRaw.partialStrengthen? strengthening.back)
        RawTerm.productCode =
          some (RawTerm.productCode targetFirstCodeRaw targetSecondCodeRaw)
    rw [firstStrengthens, secondStrengthens]
    rfl
  typeRenames := rfl
  rawRenames :=
    RawTerm.partialStrengthen?_imp_rename
      (RawTerm.productCode firstCodeRaw secondCodeRaw)
      strengthening.forward strengthening.back strengthening.injectsBack
      (RawTerm.productCode targetFirstCodeRaw targetSecondCodeRaw)
      (by
        change
          Option.mapTwo
            (firstCodeRaw.partialStrengthen? strengthening.back)
            (secondCodeRaw.partialStrengthen? strengthening.back)
            RawTerm.productCode =
              some (RawTerm.productCode targetFirstCodeRaw targetSecondCodeRaw)
        rw [firstStrengthens, secondStrengthens]
        rfl)

/-- Sum type-code terms strengthen by strengthening both schematic raw
payloads. -/
def partialStrengthenTypedSumCode {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    (leftCodeRaw rightCodeRaw : RawTerm sourceScope)
    (targetLeftCodeRaw targetRightCodeRaw : RawTerm targetScope)
    (leftStrengthens :
      leftCodeRaw.partialStrengthen? strengthening.back =
        some targetLeftCodeRaw)
    (rightStrengthens :
      rightCodeRaw.partialStrengthen? strengthening.back =
        some targetRightCodeRaw) :
    StrengtheningResult strengthening
      (Term.sumCode (context := sourceCtx) outerLevel levelLe
        leftCodeRaw rightCodeRaw) where
  targetType := Ty.universe outerLevel levelLe
  targetRaw := RawTerm.sumCode targetLeftCodeRaw targetRightCodeRaw
  targetTerm := Term.sumCode (context := targetCtx) outerLevel levelLe
    targetLeftCodeRaw targetRightCodeRaw
  typeStrengthens := rfl
  rawStrengthens := by
    change
      Option.mapTwo
        (leftCodeRaw.partialStrengthen? strengthening.back)
        (rightCodeRaw.partialStrengthen? strengthening.back)
        RawTerm.sumCode =
          some (RawTerm.sumCode targetLeftCodeRaw targetRightCodeRaw)
    rw [leftStrengthens, rightStrengthens]
    rfl
  typeRenames := rfl
  rawRenames :=
    RawTerm.partialStrengthen?_imp_rename
      (RawTerm.sumCode leftCodeRaw rightCodeRaw)
      strengthening.forward strengthening.back strengthening.injectsBack
      (RawTerm.sumCode targetLeftCodeRaw targetRightCodeRaw)
      (by
        change
          Option.mapTwo
            (leftCodeRaw.partialStrengthen? strengthening.back)
            (rightCodeRaw.partialStrengthen? strengthening.back)
            RawTerm.sumCode =
              some (RawTerm.sumCode targetLeftCodeRaw targetRightCodeRaw)
        rw [leftStrengthens, rightStrengthens]
        rfl)

/-- List type-code terms strengthen by strengthening their schematic
element-code payload. -/
def partialStrengthenTypedListCode {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    (elementCodeRaw : RawTerm sourceScope)
    (targetElementCodeRaw : RawTerm targetScope)
    (elementStrengthens :
      elementCodeRaw.partialStrengthen? strengthening.back =
        some targetElementCodeRaw) :
    StrengtheningResult strengthening
      (Term.listCode (context := sourceCtx) outerLevel levelLe
        elementCodeRaw) where
  targetType := Ty.universe outerLevel levelLe
  targetRaw := RawTerm.listCode targetElementCodeRaw
  targetTerm := Term.listCode (context := targetCtx) outerLevel levelLe
    targetElementCodeRaw
  typeStrengthens := rfl
  rawStrengthens := by
    change
      (match elementCodeRaw.partialStrengthen? strengthening.back with
      | some strengthenedElement => some (RawTerm.listCode strengthenedElement)
      | none => none) = some (RawTerm.listCode targetElementCodeRaw)
    rw [elementStrengthens]
  typeRenames := rfl
  rawRenames :=
    RawTerm.partialStrengthen?_imp_rename
      (RawTerm.listCode elementCodeRaw)
      strengthening.forward strengthening.back strengthening.injectsBack
      (RawTerm.listCode targetElementCodeRaw)
      (by
        change
          (match elementCodeRaw.partialStrengthen? strengthening.back with
          | some strengthenedElement =>
              some (RawTerm.listCode strengthenedElement)
          | none => none) = some (RawTerm.listCode targetElementCodeRaw)
        rw [elementStrengthens])

/-- Option type-code terms strengthen by strengthening their schematic
element-code payload. -/
def partialStrengthenTypedOptionCode {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    (elementCodeRaw : RawTerm sourceScope)
    (targetElementCodeRaw : RawTerm targetScope)
    (elementStrengthens :
      elementCodeRaw.partialStrengthen? strengthening.back =
        some targetElementCodeRaw) :
    StrengtheningResult strengthening
      (Term.optionCode (context := sourceCtx) outerLevel levelLe
        elementCodeRaw) where
  targetType := Ty.universe outerLevel levelLe
  targetRaw := RawTerm.optionCode targetElementCodeRaw
  targetTerm := Term.optionCode (context := targetCtx) outerLevel levelLe
    targetElementCodeRaw
  typeStrengthens := rfl
  rawStrengthens := by
    change
      (match elementCodeRaw.partialStrengthen? strengthening.back with
      | some strengthenedElement =>
          some (RawTerm.optionCode strengthenedElement)
      | none => none) = some (RawTerm.optionCode targetElementCodeRaw)
    rw [elementStrengthens]
  typeRenames := rfl
  rawRenames :=
    RawTerm.partialStrengthen?_imp_rename
      (RawTerm.optionCode elementCodeRaw)
      strengthening.forward strengthening.back strengthening.injectsBack
      (RawTerm.optionCode targetElementCodeRaw)
      (by
        change
          (match elementCodeRaw.partialStrengthen? strengthening.back with
          | some strengthenedElement =>
              some (RawTerm.optionCode strengthenedElement)
          | none => none) = some (RawTerm.optionCode targetElementCodeRaw)
        rw [elementStrengthens])

/-- Either type-code terms strengthen by strengthening both schematic
raw payloads. -/
def partialStrengthenTypedEitherCode {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    (leftCodeRaw rightCodeRaw : RawTerm sourceScope)
    (targetLeftCodeRaw targetRightCodeRaw : RawTerm targetScope)
    (leftStrengthens :
      leftCodeRaw.partialStrengthen? strengthening.back =
        some targetLeftCodeRaw)
    (rightStrengthens :
      rightCodeRaw.partialStrengthen? strengthening.back =
        some targetRightCodeRaw) :
    StrengtheningResult strengthening
      (Term.eitherCode (context := sourceCtx) outerLevel levelLe
        leftCodeRaw rightCodeRaw) where
  targetType := Ty.universe outerLevel levelLe
  targetRaw := RawTerm.eitherCode targetLeftCodeRaw targetRightCodeRaw
  targetTerm := Term.eitherCode (context := targetCtx) outerLevel levelLe
    targetLeftCodeRaw targetRightCodeRaw
  typeStrengthens := rfl
  rawStrengthens := by
    change
      Option.mapTwo
        (leftCodeRaw.partialStrengthen? strengthening.back)
        (rightCodeRaw.partialStrengthen? strengthening.back)
        RawTerm.eitherCode =
          some (RawTerm.eitherCode targetLeftCodeRaw targetRightCodeRaw)
    rw [leftStrengthens, rightStrengthens]
    rfl
  typeRenames := rfl
  rawRenames :=
    RawTerm.partialStrengthen?_imp_rename
      (RawTerm.eitherCode leftCodeRaw rightCodeRaw)
      strengthening.forward strengthening.back strengthening.injectsBack
      (RawTerm.eitherCode targetLeftCodeRaw targetRightCodeRaw)
      (by
        change
          Option.mapTwo
            (leftCodeRaw.partialStrengthen? strengthening.back)
            (rightCodeRaw.partialStrengthen? strengthening.back)
            RawTerm.eitherCode =
              some (RawTerm.eitherCode targetLeftCodeRaw targetRightCodeRaw)
        rw [leftStrengthens, rightStrengthens]
        rfl)

/-- Identity type-code terms strengthen by strengthening the carrier
code and both schematic endpoint payloads. -/
def partialStrengthenTypedIdCode {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    (typeCodeRaw leftRaw rightRaw : RawTerm sourceScope)
    (targetTypeCodeRaw targetLeftRaw targetRightRaw : RawTerm targetScope)
    (typeCodeStrengthens :
      typeCodeRaw.partialStrengthen? strengthening.back =
        some targetTypeCodeRaw)
    (leftStrengthens :
      leftRaw.partialStrengthen? strengthening.back =
        some targetLeftRaw)
    (rightStrengthens :
      rightRaw.partialStrengthen? strengthening.back =
        some targetRightRaw) :
    StrengtheningResult strengthening
      (Term.idCode (context := sourceCtx) outerLevel levelLe
        typeCodeRaw leftRaw rightRaw) where
  targetType := Ty.universe outerLevel levelLe
  targetRaw := RawTerm.idCode targetTypeCodeRaw targetLeftRaw targetRightRaw
  targetTerm := Term.idCode (context := targetCtx) outerLevel levelLe
    targetTypeCodeRaw targetLeftRaw targetRightRaw
  typeStrengthens := rfl
  rawStrengthens := by
    change
      Option.mapThree
        (typeCodeRaw.partialStrengthen? strengthening.back)
        (leftRaw.partialStrengthen? strengthening.back)
        (rightRaw.partialStrengthen? strengthening.back)
        RawTerm.idCode =
          some (RawTerm.idCode targetTypeCodeRaw targetLeftRaw targetRightRaw)
    rw [typeCodeStrengthens, leftStrengthens, rightStrengthens]
    rfl
  typeRenames := rfl
  rawRenames :=
    RawTerm.partialStrengthen?_imp_rename
      (RawTerm.idCode typeCodeRaw leftRaw rightRaw)
      strengthening.forward strengthening.back strengthening.injectsBack
      (RawTerm.idCode targetTypeCodeRaw targetLeftRaw targetRightRaw)
      (by
        change
          Option.mapThree
            (typeCodeRaw.partialStrengthen? strengthening.back)
            (leftRaw.partialStrengthen? strengthening.back)
            (rightRaw.partialStrengthen? strengthening.back)
            RawTerm.idCode =
              some (RawTerm.idCode targetTypeCodeRaw targetLeftRaw
                targetRightRaw)
        rw [typeCodeStrengthens, leftStrengthens, rightStrengthens]
        rfl)

/-- Equivalence type-code terms strengthen by strengthening both
schematic type-code payloads. -/
def partialStrengthenTypedEquivCode {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    (leftTypeCodeRaw rightTypeCodeRaw : RawTerm sourceScope)
    (targetLeftTypeCodeRaw targetRightTypeCodeRaw : RawTerm targetScope)
    (leftStrengthens :
      leftTypeCodeRaw.partialStrengthen? strengthening.back =
        some targetLeftTypeCodeRaw)
    (rightStrengthens :
      rightTypeCodeRaw.partialStrengthen? strengthening.back =
        some targetRightTypeCodeRaw) :
    StrengtheningResult strengthening
      (Term.equivCode (context := sourceCtx) outerLevel levelLe
        leftTypeCodeRaw rightTypeCodeRaw) where
  targetType := Ty.universe outerLevel levelLe
  targetRaw := RawTerm.equivCode targetLeftTypeCodeRaw targetRightTypeCodeRaw
  targetTerm := Term.equivCode (context := targetCtx) outerLevel levelLe
    targetLeftTypeCodeRaw targetRightTypeCodeRaw
  typeStrengthens := rfl
  rawStrengthens := by
    change
      Option.mapTwo
        (leftTypeCodeRaw.partialStrengthen? strengthening.back)
        (rightTypeCodeRaw.partialStrengthen? strengthening.back)
        RawTerm.equivCode =
          some (RawTerm.equivCode targetLeftTypeCodeRaw
            targetRightTypeCodeRaw)
    rw [leftStrengthens, rightStrengthens]
    rfl
  typeRenames := rfl
  rawRenames :=
    RawTerm.partialStrengthen?_imp_rename
      (RawTerm.equivCode leftTypeCodeRaw rightTypeCodeRaw)
      strengthening.forward strengthening.back strengthening.injectsBack
      (RawTerm.equivCode targetLeftTypeCodeRaw targetRightTypeCodeRaw)
      (by
        change
          Option.mapTwo
            (leftTypeCodeRaw.partialStrengthen? strengthening.back)
            (rightTypeCodeRaw.partialStrengthen? strengthening.back)
            RawTerm.equivCode =
              some (RawTerm.equivCode targetLeftTypeCodeRaw
                targetRightTypeCodeRaw)
        rw [leftStrengthens, rightStrengthens]
        rfl)

end Term

end LeanFX2
