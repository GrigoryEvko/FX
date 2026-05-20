import LeanFX2.Term.StrengtheningImage.TotalOnWeakenEliminators

/-! # Term/StrengtheningImage/TotalOnWeakenTypeCodesMisc

Total-on-weaken wrappers for type codes, projections, refinement, and funext atoms.
-/

namespace LeanFX2

namespace Term

/-- 0-IH parametric atomic totality: `Term.piTyCode` (universe-code
for `Ty.piTy`).  Domain at outer scope; codomain at scope+1 (under
binder).  Codomain strengthen uses `back.lift` and the lift-after-
lift composition lemma. -/
theorem isTotalOnWeaken_piTyCode {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    (domainCodeRaw : RawTerm scope)
    (codomainCodeRaw : RawTerm (scope + 1)) :
    IsTotalOnWeaken (Term.piTyCode (context := context) outerLevel
      levelLe domainCodeRaw codomainCodeRaw) := by
  intro newType
  show (strengthenTyped? (Term.piTyCode
      (context := context.cons newType) outerLevel levelLe
      domainCodeRaw.weaken
      (codomainCodeRaw.rename RawRenaming.weaken.lift))).isSome
  dsimp only [strengthenTyped?]
  dsimp only [partialStrengthenTyped?]
  split
  · next domainFails =>
      exfalso
      have domainSuccess :
          domainCodeRaw.weaken.partialStrengthen?
              (ContextStrengthening.dropNewest context newType).back =
            some domainCodeRaw :=
        RawTerm.strengthen?_weaken domainCodeRaw
      rw [domainSuccess] at domainFails
      cases domainFails
  · split
    · next codomainFails =>
        exfalso
        have codomainSuccess :
            (codomainCodeRaw.rename RawRenaming.weaken.lift).partialStrengthen?
                (ContextStrengthening.dropNewest context newType).back.lift =
              some codomainCodeRaw := by
          have := RawTerm.partialStrengthen?_rename_some codomainCodeRaw
            RawRenaming.weaken.lift RawRenaming.identity
            (ContextStrengthening.dropNewest context newType).back.lift
            (fun position =>
              PartialRawRenaming.lift_dropNewest_weaken_lift position)
          rw [RawTerm.rename_identity] at this
          exact this
        rw [codomainSuccess] at codomainFails
        cases codomainFails
    · rfl

/-- 0-IH parametric atomic totality: `Term.sigmaTyCode` (universe-code
for `Ty.sigmaTy`).  Same shape as `piTyCode`. -/
theorem isTotalOnWeaken_sigmaTyCode {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    (domainCodeRaw : RawTerm scope)
    (codomainCodeRaw : RawTerm (scope + 1)) :
    IsTotalOnWeaken (Term.sigmaTyCode (context := context) outerLevel
      levelLe domainCodeRaw codomainCodeRaw) := by
  intro newType
  show (strengthenTyped? (Term.sigmaTyCode
      (context := context.cons newType) outerLevel levelLe
      domainCodeRaw.weaken
      (codomainCodeRaw.rename RawRenaming.weaken.lift))).isSome
  dsimp only [strengthenTyped?]
  dsimp only [partialStrengthenTyped?]
  split
  · next domainFails =>
      exfalso
      have domainSuccess :
          domainCodeRaw.weaken.partialStrengthen?
              (ContextStrengthening.dropNewest context newType).back =
            some domainCodeRaw :=
        RawTerm.strengthen?_weaken domainCodeRaw
      rw [domainSuccess] at domainFails
      cases domainFails
  · split
    · next codomainFails =>
        exfalso
        have codomainSuccess :
            (codomainCodeRaw.rename RawRenaming.weaken.lift).partialStrengthen?
                (ContextStrengthening.dropNewest context newType).back.lift =
              some codomainCodeRaw := by
          have := RawTerm.partialStrengthen?_rename_some codomainCodeRaw
            RawRenaming.weaken.lift RawRenaming.identity
            (ContextStrengthening.dropNewest context newType).back.lift
            (fun position =>
              PartialRawRenaming.lift_dropNewest_weaken_lift position)
          rw [RawTerm.rename_identity] at this
          exact this
        rw [codomainSuccess] at codomainFails
        cases codomainFails
    · rfl

/-- 1-IH non-binder totality: `Term.fst`.  One Ty (firstType) at outer
scope + one Ty (secondType) at scope+1 (lift) + one Term IH.  The
secondType strengthen uses `back.lift`. -/
theorem isTotalOnWeaken_fst {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {firstType : Ty level scope} {secondType : Ty level (scope + 1)}
    {pairRaw : RawTerm scope}
    {pairTerm : Term context (Ty.sigmaTy firstType secondType) pairRaw}
    (pairIH : IsTotalOnWeaken pairTerm) :
    IsTotalOnWeaken (Term.fst pairTerm) := by
  intro newType
  show (strengthenTyped? (Term.fst (Term.weaken newType pairTerm))).isSome
  dsimp only [strengthenTyped?]
  dsimp only [partialStrengthenTyped?]
  split
  · next firstFails =>
      exfalso
      have firstSuccess :
          firstType.weaken.partialStrengthen?
              (ContextStrengthening.dropNewest context newType).back =
            some firstType :=
        Ty.strengthen?_weaken firstType
      rw [firstSuccess] at firstFails
      cases firstFails
  · split
    · next secondFails =>
        exfalso
        have secondSuccess :
            (secondType.rename RawRenaming.weaken.lift).partialStrengthen?
                (ContextStrengthening.dropNewest context newType).back.lift =
              some secondType := by
          have := Ty.partialStrengthen?_rename_some secondType
            RawRenaming.weaken.lift RawRenaming.identity
            (ContextStrengthening.dropNewest context newType).back.lift
            (fun position =>
              PartialRawRenaming.lift_dropNewest_weaken_lift position)
          rw [Ty.rename_identity] at this
          exact this
        rw [secondSuccess] at secondFails
        cases secondFails
    · split
      · next pairRecurse =>
          exfalso
          have totHyp := pairIH newType
          dsimp only [strengthenTyped?] at totHyp
          have : Option.isSome (none (α := StrengtheningResult
              (ContextStrengthening.dropNewest context newType)
              (Term.weaken newType pairTerm))) = true :=
            pairRecurse ▸ totHyp
          cases this
      · rfl

/-- 2-IH non-binder totality: `Term.refineIntro`.  Predicate (RawTerm)
at scope+1 uses `back.lift`; baseValue and predicateProof are Term
IHs at outer scope. -/
theorem isTotalOnWeaken_refineIntro {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {baseType : Ty level scope}
    (predicate : RawTerm (scope + 1))
    {valueRaw proofRaw : RawTerm scope}
    {baseValue : Term context baseType valueRaw}
    {predicateProof : Term context Ty.unit proofRaw}
    (baseIH : IsTotalOnWeaken baseValue)
    (proofIH : IsTotalOnWeaken predicateProof) :
    IsTotalOnWeaken (Term.refineIntro predicate baseValue
      predicateProof) := by
  intro newType
  show (strengthenTyped? (Term.refineIntro
      (predicate.rename RawRenaming.weaken.lift)
      (Term.weaken newType baseValue)
      (Term.weaken newType predicateProof))).isSome
  dsimp only [strengthenTyped?]
  dsimp only [partialStrengthenTyped?]
  split
  · next predicateFails =>
      exfalso
      have predicateSuccess :
          (predicate.rename RawRenaming.weaken.lift).partialStrengthen?
              (ContextStrengthening.dropNewest context newType).back.lift =
            some predicate := by
        have := RawTerm.partialStrengthen?_rename_some predicate
          RawRenaming.weaken.lift RawRenaming.identity
          (ContextStrengthening.dropNewest context newType).back.lift
          (fun position =>
            PartialRawRenaming.lift_dropNewest_weaken_lift position)
        rw [RawTerm.rename_identity] at this
        exact this
      rw [predicateSuccess] at predicateFails
      cases predicateFails
  · split
    · next baseRecurse =>
        exfalso
        have totHyp := baseIH newType
        dsimp only [strengthenTyped?] at totHyp
        have : Option.isSome (none (α := StrengtheningResult
            (ContextStrengthening.dropNewest context newType)
            (Term.weaken newType baseValue))) = true :=
          baseRecurse ▸ totHyp
        cases this
    · split
      · next proofRecurse =>
          exfalso
          have totHyp := proofIH newType
          dsimp only [strengthenTyped?] at totHyp
          have : Option.isSome (none (α := StrengtheningResult
              (ContextStrengthening.dropNewest context newType)
              (Term.weaken newType predicateProof))) = true :=
            proofRecurse ▸ totHyp
          cases this
      · rfl

/-- 1-IH non-binder totality: `Term.refineElim`.  One Ty (baseType) at
outer scope + one RawTerm (predicate) at scope+1 + one Term IH. -/
theorem isTotalOnWeaken_refineElim {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {baseType : Ty level scope}
    {predicate : RawTerm (scope + 1)}
    {refinedRaw : RawTerm scope}
    {refinedValue : Term context (Ty.refine baseType predicate) refinedRaw}
    (refinedIH : IsTotalOnWeaken refinedValue) :
    IsTotalOnWeaken (Term.refineElim refinedValue) := by
  intro newType
  show (strengthenTyped? (Term.refineElim (Term.weaken newType
      refinedValue))).isSome
  dsimp only [strengthenTyped?]
  dsimp only [partialStrengthenTyped?]
  split
  · next baseFails =>
      exfalso
      have baseSuccess :
          baseType.weaken.partialStrengthen?
              (ContextStrengthening.dropNewest context newType).back =
            some baseType :=
        Ty.strengthen?_weaken baseType
      rw [baseSuccess] at baseFails
      cases baseFails
  · split
    · next predicateFails =>
        exfalso
        have predicateSuccess :
            (predicate.rename RawRenaming.weaken.lift).partialStrengthen?
                (ContextStrengthening.dropNewest context newType).back.lift =
              some predicate := by
          have := RawTerm.partialStrengthen?_rename_some predicate
            RawRenaming.weaken.lift RawRenaming.identity
            (ContextStrengthening.dropNewest context newType).back.lift
            (fun position =>
              PartialRawRenaming.lift_dropNewest_weaken_lift position)
          rw [RawTerm.rename_identity] at this
          exact this
        rw [predicateSuccess] at predicateFails
        cases predicateFails
    · split
      · next refinedRecurse =>
          exfalso
          have totHyp := refinedIH newType
          dsimp only [strengthenTyped?] at totHyp
          have : Option.isSome (none (α := StrengtheningResult
              (ContextStrengthening.dropNewest context newType)
              (Term.weaken newType refinedValue))) = true :=
            refinedRecurse ▸ totHyp
          cases this
      · rfl

/-- 0-IH parametric atomic totality: `Term.funextReflAtId`.  Two Ty
(domainType, codomainType) at outer scope + one RawTerm (applyRaw)
at scope+1.  No Term IH. -/
theorem isTotalOnWeaken_funextReflAtId {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (domainType codomainType : Ty level scope)
    (applyRaw : RawTerm (scope + 1)) :
    IsTotalOnWeaken (Term.funextReflAtId (context := context)
      domainType codomainType applyRaw) := by
  intro newType
  show (strengthenTyped? (Term.funextReflAtId
      (context := context.cons newType)
      domainType.weaken codomainType.weaken
      (applyRaw.rename RawRenaming.weaken.lift))).isSome
  dsimp only [strengthenTyped?]
  dsimp only [partialStrengthenTyped?]
  split
  · next domainFails =>
      exfalso
      have domainSuccess :
          domainType.weaken.partialStrengthen?
              (ContextStrengthening.dropNewest context newType).back =
            some domainType :=
        Ty.strengthen?_weaken domainType
      rw [domainSuccess] at domainFails
      cases domainFails
  · split
    · next codomainFails =>
        exfalso
        have codomainSuccess :
            codomainType.weaken.partialStrengthen?
                (ContextStrengthening.dropNewest context newType).back =
              some codomainType :=
          Ty.strengthen?_weaken codomainType
        rw [codomainSuccess] at codomainFails
        cases codomainFails
    · split
      · next applyFails =>
          exfalso
          have applySuccess :
              (applyRaw.rename RawRenaming.weaken.lift).partialStrengthen?
                  (ContextStrengthening.dropNewest context newType).back.lift =
                some applyRaw := by
            have := RawTerm.partialStrengthen?_rename_some applyRaw
              RawRenaming.weaken.lift RawRenaming.identity
              (ContextStrengthening.dropNewest context newType).back.lift
              (fun position =>
                PartialRawRenaming.lift_dropNewest_weaken_lift position)
            rw [RawTerm.rename_identity] at this
            exact this
          rw [applySuccess] at applyFails
          cases applyFails
      · rfl

/-- 0-IH parametric atomic totality: `Term.funextIntroHet`.  Two Ty +
two RawTerm at scope+1.  No Term IH. -/
theorem isTotalOnWeaken_funextIntroHet {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (domainType codomainType : Ty level scope)
    (applyARaw applyBRaw : RawTerm (scope + 1)) :
    IsTotalOnWeaken (Term.funextIntroHet (context := context)
      domainType codomainType applyARaw applyBRaw) := by
  intro newType
  show (strengthenTyped? (Term.funextIntroHet
      (context := context.cons newType)
      domainType.weaken codomainType.weaken
      (applyARaw.rename RawRenaming.weaken.lift)
      (applyBRaw.rename RawRenaming.weaken.lift))).isSome
  dsimp only [strengthenTyped?]
  dsimp only [partialStrengthenTyped?]
  split
  · next domainFails =>
      exfalso
      have domainSuccess :
          domainType.weaken.partialStrengthen?
              (ContextStrengthening.dropNewest context newType).back =
            some domainType :=
        Ty.strengthen?_weaken domainType
      rw [domainSuccess] at domainFails
      cases domainFails
  · split
    · next codomainFails =>
        exfalso
        have codomainSuccess :
            codomainType.weaken.partialStrengthen?
                (ContextStrengthening.dropNewest context newType).back =
              some codomainType :=
          Ty.strengthen?_weaken codomainType
        rw [codomainSuccess] at codomainFails
        cases codomainFails
    · split
      · next applyAFails =>
          exfalso
          have applyASuccess :
              (applyARaw.rename RawRenaming.weaken.lift).partialStrengthen?
                  (ContextStrengthening.dropNewest context newType).back.lift =
                some applyARaw := by
            have := RawTerm.partialStrengthen?_rename_some applyARaw
              RawRenaming.weaken.lift RawRenaming.identity
              (ContextStrengthening.dropNewest context newType).back.lift
              (fun position =>
                PartialRawRenaming.lift_dropNewest_weaken_lift position)
            rw [RawTerm.rename_identity] at this
            exact this
          rw [applyASuccess] at applyAFails
          cases applyAFails
      · split
        · next applyBFails =>
            exfalso
            have applyBSuccess :
                (applyBRaw.rename RawRenaming.weaken.lift).partialStrengthen?
                    (ContextStrengthening.dropNewest context newType).back.lift =
                  some applyBRaw := by
              have := RawTerm.partialStrengthen?_rename_some applyBRaw
                RawRenaming.weaken.lift RawRenaming.identity
                (ContextStrengthening.dropNewest context newType).back.lift
                (fun position =>
                  PartialRawRenaming.lift_dropNewest_weaken_lift position)
              rw [RawTerm.rename_identity] at this
              exact this
            rw [applyBSuccess] at applyBFails
            cases applyBFails
        · rfl

/-- 0-IH parametric atomic totality: `Term.arrowCode` (universe-code
for `Ty.arrow`).  Two RawTerm sub-payloads at the outer scope. -/
theorem isTotalOnWeaken_arrowCode {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    (domainCodeRaw codomainCodeRaw : RawTerm scope) :
    IsTotalOnWeaken (Term.arrowCode (context := context) outerLevel
      levelLe domainCodeRaw codomainCodeRaw) := by
  intro newType
  show (strengthenTyped? (Term.arrowCode
      (context := context.cons newType) outerLevel levelLe
      domainCodeRaw.weaken codomainCodeRaw.weaken)).isSome
  dsimp only [strengthenTyped?]
  dsimp only [partialStrengthenTyped?]
  split
  · next domainFails =>
      exfalso
      have domainSuccess :
          domainCodeRaw.weaken.partialStrengthen?
              (ContextStrengthening.dropNewest context newType).back =
            some domainCodeRaw :=
        RawTerm.strengthen?_weaken domainCodeRaw
      rw [domainSuccess] at domainFails
      cases domainFails
  · split
    · next codomainFails =>
        exfalso
        have codomainSuccess :
            codomainCodeRaw.weaken.partialStrengthen?
                (ContextStrengthening.dropNewest context newType).back =
              some codomainCodeRaw :=
          RawTerm.strengthen?_weaken codomainCodeRaw
        rw [codomainSuccess] at codomainFails
        cases codomainFails
    · rfl

/-- 0-IH parametric atomic totality: `Term.productCode` (universe-code
for `Ty.product`).  Two RawTerm sub-payloads at the outer scope. -/
theorem isTotalOnWeaken_productCode {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    (firstCodeRaw secondCodeRaw : RawTerm scope) :
    IsTotalOnWeaken (Term.productCode (context := context) outerLevel
      levelLe firstCodeRaw secondCodeRaw) := by
  intro newType
  show (strengthenTyped? (Term.productCode
      (context := context.cons newType) outerLevel levelLe
      firstCodeRaw.weaken secondCodeRaw.weaken)).isSome
  dsimp only [strengthenTyped?]
  dsimp only [partialStrengthenTyped?]
  split
  · next firstFails =>
      exfalso
      have firstSuccess :
          firstCodeRaw.weaken.partialStrengthen?
              (ContextStrengthening.dropNewest context newType).back =
            some firstCodeRaw :=
        RawTerm.strengthen?_weaken firstCodeRaw
      rw [firstSuccess] at firstFails
      cases firstFails
  · split
    · next secondFails =>
        exfalso
        have secondSuccess :
            secondCodeRaw.weaken.partialStrengthen?
                (ContextStrengthening.dropNewest context newType).back =
              some secondCodeRaw :=
          RawTerm.strengthen?_weaken secondCodeRaw
        rw [secondSuccess] at secondFails
        cases secondFails
    · rfl

/-- 0-IH parametric atomic totality: `Term.sumCode` (universe-code
for `Ty.sum`). -/
theorem isTotalOnWeaken_sumCode {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    (leftCodeRaw rightCodeRaw : RawTerm scope) :
    IsTotalOnWeaken (Term.sumCode (context := context) outerLevel
      levelLe leftCodeRaw rightCodeRaw) := by
  intro newType
  show (strengthenTyped? (Term.sumCode
      (context := context.cons newType) outerLevel levelLe
      leftCodeRaw.weaken rightCodeRaw.weaken)).isSome
  dsimp only [strengthenTyped?]
  dsimp only [partialStrengthenTyped?]
  split
  · next leftFails =>
      exfalso
      have leftSuccess :
          leftCodeRaw.weaken.partialStrengthen?
              (ContextStrengthening.dropNewest context newType).back =
            some leftCodeRaw :=
        RawTerm.strengthen?_weaken leftCodeRaw
      rw [leftSuccess] at leftFails
      cases leftFails
  · split
    · next rightFails =>
        exfalso
        have rightSuccess :
            rightCodeRaw.weaken.partialStrengthen?
                (ContextStrengthening.dropNewest context newType).back =
              some rightCodeRaw :=
          RawTerm.strengthen?_weaken rightCodeRaw
        rw [rightSuccess] at rightFails
        cases rightFails
    · rfl

/-- 0-IH parametric atomic totality: `Term.listCode` (universe-code
for `Ty.listType`).  One RawTerm sub-payload. -/
theorem isTotalOnWeaken_listCode {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    (elementCodeRaw : RawTerm scope) :
    IsTotalOnWeaken (Term.listCode (context := context) outerLevel
      levelLe elementCodeRaw) := by
  intro newType
  show (strengthenTyped? (Term.listCode
      (context := context.cons newType) outerLevel levelLe
      elementCodeRaw.weaken)).isSome
  dsimp only [strengthenTyped?]
  dsimp only [partialStrengthenTyped?]
  split
  · next elementFails =>
      exfalso
      have elementSuccess :
          elementCodeRaw.weaken.partialStrengthen?
              (ContextStrengthening.dropNewest context newType).back =
            some elementCodeRaw :=
        RawTerm.strengthen?_weaken elementCodeRaw
      rw [elementSuccess] at elementFails
      cases elementFails
  · rfl

/-- 0-IH parametric atomic totality: `Term.optionCode` (universe-code
for `Ty.optionType`).  One RawTerm sub-payload. -/
theorem isTotalOnWeaken_optionCode {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    (elementCodeRaw : RawTerm scope) :
    IsTotalOnWeaken (Term.optionCode (context := context) outerLevel
      levelLe elementCodeRaw) := by
  intro newType
  show (strengthenTyped? (Term.optionCode
      (context := context.cons newType) outerLevel levelLe
      elementCodeRaw.weaken)).isSome
  dsimp only [strengthenTyped?]
  dsimp only [partialStrengthenTyped?]
  split
  · next elementFails =>
      exfalso
      have elementSuccess :
          elementCodeRaw.weaken.partialStrengthen?
              (ContextStrengthening.dropNewest context newType).back =
            some elementCodeRaw :=
        RawTerm.strengthen?_weaken elementCodeRaw
      rw [elementSuccess] at elementFails
      cases elementFails
  · rfl

/-- 0-IH parametric atomic totality: `Term.eitherCode` (universe-code
for `Ty.eitherType`).  Two RawTerm sub-payloads. -/
theorem isTotalOnWeaken_eitherCode {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    (leftCodeRaw rightCodeRaw : RawTerm scope) :
    IsTotalOnWeaken (Term.eitherCode (context := context) outerLevel
      levelLe leftCodeRaw rightCodeRaw) := by
  intro newType
  show (strengthenTyped? (Term.eitherCode
      (context := context.cons newType) outerLevel levelLe
      leftCodeRaw.weaken rightCodeRaw.weaken)).isSome
  dsimp only [strengthenTyped?]
  dsimp only [partialStrengthenTyped?]
  split
  · next leftFails =>
      exfalso
      have leftSuccess :
          leftCodeRaw.weaken.partialStrengthen?
              (ContextStrengthening.dropNewest context newType).back =
            some leftCodeRaw :=
        RawTerm.strengthen?_weaken leftCodeRaw
      rw [leftSuccess] at leftFails
      cases leftFails
  · split
    · next rightFails =>
        exfalso
        have rightSuccess :
            rightCodeRaw.weaken.partialStrengthen?
                (ContextStrengthening.dropNewest context newType).back =
              some rightCodeRaw :=
          RawTerm.strengthen?_weaken rightCodeRaw
        rw [rightSuccess] at rightFails
        cases rightFails
    · rfl

/-- 0-IH parametric atomic totality: `Term.idCode` (universe-code
for `Ty.id`).  Three RawTerm sub-payloads at the outer scope. -/
theorem isTotalOnWeaken_idCode {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    (typeCodeRaw leftRaw rightRaw : RawTerm scope) :
    IsTotalOnWeaken (Term.idCode (context := context) outerLevel
      levelLe typeCodeRaw leftRaw rightRaw) := by
  intro newType
  show (strengthenTyped? (Term.idCode
      (context := context.cons newType) outerLevel levelLe
      typeCodeRaw.weaken leftRaw.weaken rightRaw.weaken)).isSome
  dsimp only [strengthenTyped?]
  dsimp only [partialStrengthenTyped?]
  split
  · next typeFails =>
      exfalso
      have typeSuccess :
          typeCodeRaw.weaken.partialStrengthen?
              (ContextStrengthening.dropNewest context newType).back =
            some typeCodeRaw :=
        RawTerm.strengthen?_weaken typeCodeRaw
      rw [typeSuccess] at typeFails
      cases typeFails
  · split
    · next leftFails =>
        exfalso
        have leftSuccess :
            leftRaw.weaken.partialStrengthen?
                (ContextStrengthening.dropNewest context newType).back =
              some leftRaw :=
          RawTerm.strengthen?_weaken leftRaw
        rw [leftSuccess] at leftFails
        cases leftFails
    · split
      · next rightFails =>
          exfalso
          have rightSuccess :
              rightRaw.weaken.partialStrengthen?
                  (ContextStrengthening.dropNewest context newType).back =
                some rightRaw :=
            RawTerm.strengthen?_weaken rightRaw
          rw [rightSuccess] at rightFails
          cases rightFails
      · rfl

/-- 0-IH parametric atomic totality: `Term.equivCode` (universe-code
for `Ty.equiv`).  Two RawTerm sub-payloads. -/
theorem isTotalOnWeaken_equivCode {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    (leftTypeCodeRaw rightTypeCodeRaw : RawTerm scope) :
    IsTotalOnWeaken (Term.equivCode (context := context) outerLevel
      levelLe leftTypeCodeRaw rightTypeCodeRaw) := by
  intro newType
  show (strengthenTyped? (Term.equivCode
      (context := context.cons newType) outerLevel levelLe
      leftTypeCodeRaw.weaken rightTypeCodeRaw.weaken)).isSome
  dsimp only [strengthenTyped?]
  dsimp only [partialStrengthenTyped?]
  split
  · next leftFails =>
      exfalso
      have leftSuccess :
          leftTypeCodeRaw.weaken.partialStrengthen?
              (ContextStrengthening.dropNewest context newType).back =
            some leftTypeCodeRaw :=
        RawTerm.strengthen?_weaken leftTypeCodeRaw
      rw [leftSuccess] at leftFails
      cases leftFails
  · split
    · next rightFails =>
        exfalso
        have rightSuccess :
            rightTypeCodeRaw.weaken.partialStrengthen?
                (ContextStrengthening.dropNewest context newType).back =
              some rightTypeCodeRaw :=
          RawTerm.strengthen?_weaken rightTypeCodeRaw
        rw [rightSuccess] at rightFails
        cases rightFails
    · rfl

end Term

end LeanFX2
