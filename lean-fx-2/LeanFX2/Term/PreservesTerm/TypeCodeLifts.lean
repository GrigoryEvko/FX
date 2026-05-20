import LeanFX2.Reduction.ParRed.ParInductive.Inductive
import LeanFX2.Reduction.RawParInversion.TypeCodes
import LeanFX2.Term.Inversion

/-! # LeanFX2.Term.PreservesTerm.TypeCodeLifts

Full lifts for the schematic-payload type-code ctors that carry
their raw payloads as schematic fields (no recursive typed Term
children).  Free the type index via `suffices`, then realign with
`Ty.universe.inj` after exhaustion.

Covers 10 ctors: arrowCode, piTyCode, sigmaTyCode, productCode,
sumCode, listCode, optionCode, eitherCode, idCode, equivCode.

## Root status

Zero-axiom; carved from `Term/PreservesTerm.lean`. -/

namespace LeanFX2

variable {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}


/-! ## Schematic-payload type-code ctors (full lifts)

`Term.arrowCode`, `piTyCode`, ..., `equivCode` are CUMUL-2.4 VALUE-shaped
ctors carrying their raw payloads as schematic fields (no recursive
typed children).  Each has a typed cong rule
`Step.par.<X>CodeCong` mirroring the raw `RawStep.par.<X>CodeCong`.

Pattern per ctor:
1. `RawStep.par.<X>Code_inv` extracts subterm raw steps + target eq.
2. `cases eq` aligns target raw shape.
3. `suffices` over `someType` aligns the universe-Ty type index using
   `Ty.universe.inj`-style reasoning (universe ctor is parametric in
   level + level proof).
4. Apply typed `Step.par.<X>CodeCong`.

All ten codes target `Ty.universe outerLevel levelLe` so the source's
fixed type aligns trivially via `cases` on the proof / by reading off
the result type. -/

/-- **Term.arrowCode full lift.** -/
theorem RawStep.par.lift_full_arrowCode
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    (domainCodeRaw codomainCodeRaw : RawTerm scope)
    (sourceTerm :
      Term context (Ty.universe outerLevel levelLe)
        (RawTerm.arrowCode domainCodeRaw codomainCodeRaw))
    {targetRaw : RawTerm scope}
    (rawStep :
      RawStep.par (RawTerm.arrowCode domainCodeRaw codomainCodeRaw) targetRaw) :
    ∃ (targetType : Ty level scope) (targetTerm : Term context targetType targetRaw),
      Step.par sourceTerm targetTerm := by
  obtain ⟨domainTarget, codomainTarget, eq, domainStep, codomainStep⟩ :=
    RawStep.par.arrowCode_inv rawStep
  cases eq
  refine ⟨Ty.universe outerLevel levelLe,
          Term.arrowCode (context := context) outerLevel levelLe
            domainTarget codomainTarget, ?_⟩
  -- Free-the-type-via-suffices: feedback_lean_free_type_via_suffices.md.
  -- Freeing someType lets Lean's match-compiler dispatch the var arm
  -- via raw-RawTerm.arrowCode-vs-RawTerm.var nomatch, and handle the
  -- arrowCode arm with proper level alignment via someTypeIsUniverse.
  suffices key :
      ∀ {someType : Ty level scope}
        (genericTerm :
          Term context someType
            (RawTerm.arrowCode domainCodeRaw codomainCodeRaw)),
        someType = Ty.universe outerLevel levelLe →
        Step.par genericTerm
                 (Term.arrowCode (context := context) outerLevel levelLe
                   domainTarget codomainTarget) by
    exact key sourceTerm rfl
  intro someType genericTerm someTypeIsUniverse
  cases genericTerm
  rename_i innerLevel innerLevelLe
  -- innerLevel innerLevelLe come from inner Term.arrowCode ctor
  -- someTypeIsUniverse : Ty.universe innerLevel innerLevelLe = Ty.universe outerLevel levelLe
  -- We need Step.par.arrowCodeCong at outerLevel/levelLe but ctor instance is at inner.
  -- Substitute the equality:
  have universeEq : innerLevel = outerLevel := by
    cases someTypeIsUniverse
    rfl
  cases universeEq
  -- innerLevelLe and levelLe have the same type now (innerLevel.toNat + 1 ≤ level);
  -- they may differ proof-irrelevantly, but here we need to close definitionally.
  -- The remaining Step.par target Term.arrowCode is at innerLevelLe vs outerLevelLe.
  -- Since the `≤` proof is propositional (Nat.le is a Prop), proof-irrelevance kicks in.
  exact Step.par.arrowCodeCong outerLevel innerLevelLe domainStep codomainStep

/-- **Term.piTyCode full lift.** Codomain raw lives at scope+1. -/
theorem RawStep.par.lift_full_piTyCode
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    (domainCodeRaw : RawTerm scope) (codomainCodeRaw : RawTerm (scope + 1))
    (sourceTerm :
      Term context (Ty.universe outerLevel levelLe)
        (RawTerm.piTyCode domainCodeRaw codomainCodeRaw))
    {targetRaw : RawTerm scope}
    (rawStep :
      RawStep.par (RawTerm.piTyCode domainCodeRaw codomainCodeRaw) targetRaw) :
    ∃ (targetType : Ty level scope) (targetTerm : Term context targetType targetRaw),
      Step.par sourceTerm targetTerm := by
  obtain ⟨domainTarget, codomainTarget, eq, domainStep, codomainStep⟩ :=
    RawStep.par.piTyCode_inv rawStep
  cases eq
  refine ⟨Ty.universe outerLevel levelLe,
          Term.piTyCode (context := context) outerLevel levelLe
            domainTarget codomainTarget, ?_⟩
  suffices key :
      ∀ {someType : Ty level scope}
        (genericTerm :
          Term context someType
            (RawTerm.piTyCode domainCodeRaw codomainCodeRaw)),
        someType = Ty.universe outerLevel levelLe →
        Step.par genericTerm
                 (Term.piTyCode (context := context) outerLevel levelLe
                   domainTarget codomainTarget) by
    exact key sourceTerm rfl
  intro someType genericTerm someTypeIsUniverse
  cases genericTerm
  rename_i innerLevel innerLevelLe
  have universeEq : innerLevel = outerLevel := by
    cases someTypeIsUniverse
    rfl
  cases universeEq
  exact Step.par.piTyCodeCong outerLevel innerLevelLe domainStep codomainStep

/-- **Term.sigmaTyCode full lift.** Second raw lives at scope+1. -/
theorem RawStep.par.lift_full_sigmaTyCode
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    (firstCodeRaw : RawTerm scope) (secondCodeRaw : RawTerm (scope + 1))
    (sourceTerm :
      Term context (Ty.universe outerLevel levelLe)
        (RawTerm.sigmaTyCode firstCodeRaw secondCodeRaw))
    {targetRaw : RawTerm scope}
    (rawStep :
      RawStep.par (RawTerm.sigmaTyCode firstCodeRaw secondCodeRaw) targetRaw) :
    ∃ (targetType : Ty level scope) (targetTerm : Term context targetType targetRaw),
      Step.par sourceTerm targetTerm := by
  obtain ⟨firstTarget, secondTarget, eq, firstStep, secondStep⟩ :=
    RawStep.par.sigmaTyCode_inv rawStep
  cases eq
  refine ⟨Ty.universe outerLevel levelLe,
          Term.sigmaTyCode (context := context) outerLevel levelLe
            firstTarget secondTarget, ?_⟩
  suffices key :
      ∀ {someType : Ty level scope}
        (genericTerm :
          Term context someType
            (RawTerm.sigmaTyCode firstCodeRaw secondCodeRaw)),
        someType = Ty.universe outerLevel levelLe →
        Step.par genericTerm
                 (Term.sigmaTyCode (context := context) outerLevel levelLe
                   firstTarget secondTarget) by
    exact key sourceTerm rfl
  intro someType genericTerm someTypeIsUniverse
  cases genericTerm
  rename_i innerLevel innerLevelLe
  have universeEq : innerLevel = outerLevel := by
    cases someTypeIsUniverse
    rfl
  cases universeEq
  exact Step.par.sigmaTyCodeCong outerLevel innerLevelLe firstStep secondStep

/-- **Term.productCode full lift.** -/
theorem RawStep.par.lift_full_productCode
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    (firstCodeRaw secondCodeRaw : RawTerm scope)
    (sourceTerm :
      Term context (Ty.universe outerLevel levelLe)
        (RawTerm.productCode firstCodeRaw secondCodeRaw))
    {targetRaw : RawTerm scope}
    (rawStep :
      RawStep.par (RawTerm.productCode firstCodeRaw secondCodeRaw) targetRaw) :
    ∃ (targetType : Ty level scope) (targetTerm : Term context targetType targetRaw),
      Step.par sourceTerm targetTerm := by
  obtain ⟨firstTarget, secondTarget, eq, firstStep, secondStep⟩ :=
    RawStep.par.productCode_inv rawStep
  cases eq
  refine ⟨Ty.universe outerLevel levelLe,
          Term.productCode (context := context) outerLevel levelLe
            firstTarget secondTarget, ?_⟩
  suffices key :
      ∀ {someType : Ty level scope}
        (genericTerm :
          Term context someType
            (RawTerm.productCode firstCodeRaw secondCodeRaw)),
        someType = Ty.universe outerLevel levelLe →
        Step.par genericTerm
                 (Term.productCode (context := context) outerLevel levelLe
                   firstTarget secondTarget) by
    exact key sourceTerm rfl
  intro someType genericTerm someTypeIsUniverse
  cases genericTerm
  rename_i innerLevel innerLevelLe
  have universeEq : innerLevel = outerLevel := by
    cases someTypeIsUniverse
    rfl
  cases universeEq
  exact Step.par.productCodeCong outerLevel innerLevelLe firstStep secondStep

/-- **Term.sumCode full lift.** -/
theorem RawStep.par.lift_full_sumCode
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    (leftCodeRaw rightCodeRaw : RawTerm scope)
    (sourceTerm :
      Term context (Ty.universe outerLevel levelLe)
        (RawTerm.sumCode leftCodeRaw rightCodeRaw))
    {targetRaw : RawTerm scope}
    (rawStep :
      RawStep.par (RawTerm.sumCode leftCodeRaw rightCodeRaw) targetRaw) :
    ∃ (targetType : Ty level scope) (targetTerm : Term context targetType targetRaw),
      Step.par sourceTerm targetTerm := by
  obtain ⟨leftTarget, rightTarget, eq, leftStep, rightStep⟩ :=
    RawStep.par.sumCode_inv rawStep
  cases eq
  refine ⟨Ty.universe outerLevel levelLe,
          Term.sumCode (context := context) outerLevel levelLe
            leftTarget rightTarget, ?_⟩
  suffices key :
      ∀ {someType : Ty level scope}
        (genericTerm :
          Term context someType
            (RawTerm.sumCode leftCodeRaw rightCodeRaw)),
        someType = Ty.universe outerLevel levelLe →
        Step.par genericTerm
                 (Term.sumCode (context := context) outerLevel levelLe
                   leftTarget rightTarget) by
    exact key sourceTerm rfl
  intro someType genericTerm someTypeIsUniverse
  cases genericTerm
  rename_i innerLevel innerLevelLe
  have universeEq : innerLevel = outerLevel := by
    cases someTypeIsUniverse
    rfl
  cases universeEq
  exact Step.par.sumCodeCong outerLevel innerLevelLe leftStep rightStep

/-- **Term.listCode full lift.** -/
theorem RawStep.par.lift_full_listCode
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    (elementCodeRaw : RawTerm scope)
    (sourceTerm :
      Term context (Ty.universe outerLevel levelLe)
        (RawTerm.listCode elementCodeRaw))
    {targetRaw : RawTerm scope}
    (rawStep : RawStep.par (RawTerm.listCode elementCodeRaw) targetRaw) :
    ∃ (targetType : Ty level scope) (targetTerm : Term context targetType targetRaw),
      Step.par sourceTerm targetTerm := by
  obtain ⟨elementTarget, eq, elementStep⟩ := RawStep.par.listCode_inv rawStep
  cases eq
  refine ⟨Ty.universe outerLevel levelLe,
          Term.listCode (context := context) outerLevel levelLe
            elementTarget, ?_⟩
  suffices key :
      ∀ {someType : Ty level scope}
        (genericTerm :
          Term context someType (RawTerm.listCode elementCodeRaw)),
        someType = Ty.universe outerLevel levelLe →
        Step.par genericTerm
                 (Term.listCode (context := context) outerLevel levelLe
                   elementTarget) by
    exact key sourceTerm rfl
  intro someType genericTerm someTypeIsUniverse
  cases genericTerm
  rename_i innerLevel innerLevelLe
  have universeEq : innerLevel = outerLevel := by
    cases someTypeIsUniverse
    rfl
  cases universeEq
  exact Step.par.listCodeCong outerLevel innerLevelLe elementStep

/-- **Term.optionCode full lift.** -/
theorem RawStep.par.lift_full_optionCode
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    (elementCodeRaw : RawTerm scope)
    (sourceTerm :
      Term context (Ty.universe outerLevel levelLe)
        (RawTerm.optionCode elementCodeRaw))
    {targetRaw : RawTerm scope}
    (rawStep : RawStep.par (RawTerm.optionCode elementCodeRaw) targetRaw) :
    ∃ (targetType : Ty level scope) (targetTerm : Term context targetType targetRaw),
      Step.par sourceTerm targetTerm := by
  obtain ⟨elementTarget, eq, elementStep⟩ := RawStep.par.optionCode_inv rawStep
  cases eq
  refine ⟨Ty.universe outerLevel levelLe,
          Term.optionCode (context := context) outerLevel levelLe
            elementTarget, ?_⟩
  suffices key :
      ∀ {someType : Ty level scope}
        (genericTerm :
          Term context someType (RawTerm.optionCode elementCodeRaw)),
        someType = Ty.universe outerLevel levelLe →
        Step.par genericTerm
                 (Term.optionCode (context := context) outerLevel levelLe
                   elementTarget) by
    exact key sourceTerm rfl
  intro someType genericTerm someTypeIsUniverse
  cases genericTerm
  rename_i innerLevel innerLevelLe
  have universeEq : innerLevel = outerLevel := by
    cases someTypeIsUniverse
    rfl
  cases universeEq
  exact Step.par.optionCodeCong outerLevel innerLevelLe elementStep

/-- **Term.eitherCode full lift.** -/
theorem RawStep.par.lift_full_eitherCode
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    (leftCodeRaw rightCodeRaw : RawTerm scope)
    (sourceTerm :
      Term context (Ty.universe outerLevel levelLe)
        (RawTerm.eitherCode leftCodeRaw rightCodeRaw))
    {targetRaw : RawTerm scope}
    (rawStep :
      RawStep.par (RawTerm.eitherCode leftCodeRaw rightCodeRaw) targetRaw) :
    ∃ (targetType : Ty level scope) (targetTerm : Term context targetType targetRaw),
      Step.par sourceTerm targetTerm := by
  obtain ⟨leftTarget, rightTarget, eq, leftStep, rightStep⟩ :=
    RawStep.par.eitherCode_inv rawStep
  cases eq
  refine ⟨Ty.universe outerLevel levelLe,
          Term.eitherCode (context := context) outerLevel levelLe
            leftTarget rightTarget, ?_⟩
  suffices key :
      ∀ {someType : Ty level scope}
        (genericTerm :
          Term context someType
            (RawTerm.eitherCode leftCodeRaw rightCodeRaw)),
        someType = Ty.universe outerLevel levelLe →
        Step.par genericTerm
                 (Term.eitherCode (context := context) outerLevel levelLe
                   leftTarget rightTarget) by
    exact key sourceTerm rfl
  intro someType genericTerm someTypeIsUniverse
  cases genericTerm
  rename_i innerLevel innerLevelLe
  have universeEq : innerLevel = outerLevel := by
    cases someTypeIsUniverse
    rfl
  cases universeEq
  exact Step.par.eitherCodeCong outerLevel innerLevelLe leftStep rightStep

/-- **Term.idCode full lift.** -/
theorem RawStep.par.lift_full_idCode
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    (typeCodeRaw leftRaw rightRaw : RawTerm scope)
    (sourceTerm :
      Term context (Ty.universe outerLevel levelLe)
        (RawTerm.idCode typeCodeRaw leftRaw rightRaw))
    {targetRaw : RawTerm scope}
    (rawStep :
      RawStep.par (RawTerm.idCode typeCodeRaw leftRaw rightRaw) targetRaw) :
    ∃ (targetType : Ty level scope) (targetTerm : Term context targetType targetRaw),
      Step.par sourceTerm targetTerm := by
  obtain ⟨typeTarget, leftTarget, rightTarget, eq, typeStep, leftStep, rightStep⟩ :=
    RawStep.par.idCode_inv rawStep
  cases eq
  refine ⟨Ty.universe outerLevel levelLe,
          Term.idCode (context := context) outerLevel levelLe
            typeTarget leftTarget rightTarget, ?_⟩
  suffices key :
      ∀ {someType : Ty level scope}
        (genericTerm :
          Term context someType
            (RawTerm.idCode typeCodeRaw leftRaw rightRaw)),
        someType = Ty.universe outerLevel levelLe →
        Step.par genericTerm
                 (Term.idCode (context := context) outerLevel levelLe
                   typeTarget leftTarget rightTarget) by
    exact key sourceTerm rfl
  intro someType genericTerm someTypeIsUniverse
  cases genericTerm
  rename_i innerLevel innerLevelLe
  have universeEq : innerLevel = outerLevel := by
    cases someTypeIsUniverse
    rfl
  cases universeEq
  exact Step.par.idCodeCong outerLevel innerLevelLe typeStep leftStep rightStep

/-- **Term.equivCode full lift.** -/
theorem RawStep.par.lift_full_equivCode
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    (leftCodeRaw rightCodeRaw : RawTerm scope)
    (sourceTerm :
      Term context (Ty.universe outerLevel levelLe)
        (RawTerm.equivCode leftCodeRaw rightCodeRaw))
    {targetRaw : RawTerm scope}
    (rawStep :
      RawStep.par (RawTerm.equivCode leftCodeRaw rightCodeRaw) targetRaw) :
    ∃ (targetType : Ty level scope) (targetTerm : Term context targetType targetRaw),
      Step.par sourceTerm targetTerm := by
  obtain ⟨leftTarget, rightTarget, eq, leftStep, rightStep⟩ :=
    RawStep.par.equivCode_inv rawStep
  cases eq
  refine ⟨Ty.universe outerLevel levelLe,
          Term.equivCode (context := context) outerLevel levelLe
            leftTarget rightTarget, ?_⟩
  suffices key :
      ∀ {someType : Ty level scope}
        (genericTerm :
          Term context someType
            (RawTerm.equivCode leftCodeRaw rightCodeRaw)),
        someType = Ty.universe outerLevel levelLe →
        Step.par genericTerm
                 (Term.equivCode (context := context) outerLevel levelLe
                   leftTarget rightTarget) by
    exact key sourceTerm rfl
  intro someType genericTerm someTypeIsUniverse
  cases genericTerm
  rename_i innerLevel innerLevelLe
  have universeEq : innerLevel = outerLevel := by
    cases someTypeIsUniverse
    rfl
  cases universeEq
  exact Step.par.equivCodeCong outerLevel innerLevelLe leftStep rightStep

end LeanFX2
