import LeanFX2.Term.PartialStrengthen.Constructors.EquivalenceCanonical

/-! # Term/PartialStrengthen/Constructors/EquivalenceApplications

Typed partial-strengthening producers for equivalence application,
univalence-to-equivalence, and observational funext terms.
-/

namespace LeanFX2

namespace Term

/-- Success branch for equivalence-application strengthening.  Mirrors
`partialStrengthenTypedEquivApplyOfSuccess` (Phase 22) but for the
univalence-α companion `Term.equivApp` / `RawTerm.equivApp` constructor
pair.  Same dual Option.casesOn discriminator wall over `Ty.equiv`'s
carrier-pair pivots. -/
def partialStrengthenTypedEquivAppOfSuccess {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {carrierA carrierB : Ty level sourceScope}
    {targetCarrierA targetCarrierB : Ty level targetScope}
    {equivRaw argumentRaw : RawTerm sourceScope}
    {targetEquivRaw targetArgumentRaw : RawTerm targetScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    {equivTerm : Term sourceCtx (Ty.equiv carrierA carrierB) equivRaw}
    {argumentTerm : Term sourceCtx carrierA argumentRaw}
    (targetEquivTerm :
      Term targetCtx (Ty.equiv targetCarrierA targetCarrierB) targetEquivRaw)
    (targetArgumentTerm :
      Term targetCtx targetCarrierA targetArgumentRaw)
    (_carrierASuccess :
      carrierA.partialStrengthen? strengthening.back = some targetCarrierA)
    (carrierBSuccess :
      carrierB.partialStrengthen? strengthening.back = some targetCarrierB)
    (equivRawStrengthens :
      equivRaw.partialStrengthen? strengthening.back = some targetEquivRaw)
    (argumentRawStrengthens :
      argumentRaw.partialStrengthen? strengthening.back =
        some targetArgumentRaw)
    (equivRawRenames :
      equivRaw = targetEquivRaw.rename strengthening.forward)
    (argumentRawRenames :
      argumentRaw = targetArgumentRaw.rename strengthening.forward) :
    StrengtheningResult strengthening
      (Term.equivApp equivTerm argumentTerm) where
  targetType := targetCarrierB
  targetRaw := RawTerm.equivApp targetEquivRaw targetArgumentRaw
  targetTerm := Term.equivApp targetEquivTerm targetArgumentTerm
  typeStrengthens := carrierBSuccess
  rawStrengthens := by
    change
      Option.mapTwo
        (equivRaw.partialStrengthen? strengthening.back)
        (argumentRaw.partialStrengthen? strengthening.back)
        RawTerm.equivApp =
          some (RawTerm.equivApp targetEquivRaw targetArgumentRaw)
    rw [equivRawStrengthens, argumentRawStrengthens]
    rfl
  typeRenames :=
    Ty.partialStrengthen?_imp_rename carrierB
      strengthening.forward strengthening.back strengthening.injectsBack
      targetCarrierB carrierBSuccess
  rawRenames := by
    cases equivRawRenames
    cases argumentRawRenames
    rfl

/-- Equiv-application strengthens by decomposing the strengthened
`Ty.equiv` carrier-pair pivots and threading them into the
`equivApp` constructor at the target context.  Wrapper delegates the
success path to `partialStrengthenTypedEquivAppOfSuccess`. -/
def partialStrengthenTypedEquivApp {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {carrierA carrierB : Ty level sourceScope}
    {targetCarrierA targetCarrierB : Ty level targetScope}
    {equivRaw argumentRaw : RawTerm sourceScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    {equivTerm : Term sourceCtx (Ty.equiv carrierA carrierB) equivRaw}
    {argumentTerm : Term sourceCtx carrierA argumentRaw}
    (carrierASuccess :
      carrierA.partialStrengthen? strengthening.back = some targetCarrierA)
    (carrierBSuccess :
      carrierB.partialStrengthen? strengthening.back = some targetCarrierB)
    (equivResult : StrengtheningResult strengthening equivTerm)
    (argumentResult : StrengtheningResult strengthening argumentTerm) :
    StrengtheningResult strengthening
      (Term.equivApp equivTerm argumentTerm) := by
  cases equivResult with
  | mk targetEquivType targetEquivRaw targetEquivTerm
      equivTypeStrengthens equivRawStrengthens equivTypeRenames
      equivRawRenames =>
      have expectedEquivTypeStrengthens :
          (Ty.equiv carrierA carrierB).partialStrengthen?
              strengthening.back =
            some (Ty.equiv targetCarrierA targetCarrierB) := by
        change
          Option.mapTwo
            (carrierA.partialStrengthen? strengthening.back)
            (carrierB.partialStrengthen? strengthening.back)
            Ty.equiv = some (Ty.equiv targetCarrierA targetCarrierB)
        rw [carrierASuccess, carrierBSuccess]
        rfl
      rw [expectedEquivTypeStrengthens] at equivTypeStrengthens
      cases equivTypeStrengthens
      cases argumentResult with
      | mk targetArgumentType targetArgumentRaw targetArgumentTerm
          argumentTypeStrengthens argumentRawStrengthens
          argumentTypeRenames argumentRawRenames =>
          rw [carrierASuccess] at argumentTypeStrengthens
          cases argumentTypeStrengthens
          exact partialStrengthenTypedEquivAppOfSuccess
            targetEquivTerm targetArgumentTerm carrierASuccess
            carrierBSuccess equivRawStrengthens argumentRawStrengthens
            equivRawRenames argumentRawRenames

/-- Success branch for equiv-application strengthening.  Takes
pre-decomposed witnesses for the equiv carrier-pair pivots plus the
strengthened equiv-term + argument-term values.  Splits out the
term-mode body so the strengthening-image soundness layer can prove
the soundness theorem without traversing `Option.casesOn` on the
`carrierA.partialStrengthen?` / `carrierB.partialStrengthen?` pivots
inside the wrapper's tactic-mode `cases` chain. -/
def partialStrengthenTypedEquivApplyOfSuccess {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {carrierA carrierB : Ty level sourceScope}
    {targetCarrierA targetCarrierB : Ty level targetScope}
    {equivRaw argumentRaw : RawTerm sourceScope}
    {targetEquivRaw targetArgumentRaw : RawTerm targetScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    {equivTerm : Term sourceCtx (Ty.equiv carrierA carrierB) equivRaw}
    {argumentTerm : Term sourceCtx carrierA argumentRaw}
    (targetEquivTerm :
      Term targetCtx (Ty.equiv targetCarrierA targetCarrierB) targetEquivRaw)
    (targetArgumentTerm :
      Term targetCtx targetCarrierA targetArgumentRaw)
    (_carrierASuccess :
      carrierA.partialStrengthen? strengthening.back = some targetCarrierA)
    (carrierBSuccess :
      carrierB.partialStrengthen? strengthening.back = some targetCarrierB)
    (equivRawStrengthens :
      equivRaw.partialStrengthen? strengthening.back = some targetEquivRaw)
    (argumentRawStrengthens :
      argumentRaw.partialStrengthen? strengthening.back =
        some targetArgumentRaw)
    (equivRawRenames :
      equivRaw = targetEquivRaw.rename strengthening.forward)
    (argumentRawRenames :
      argumentRaw = targetArgumentRaw.rename strengthening.forward) :
    StrengtheningResult strengthening
      (Term.equivApply equivTerm argumentTerm) where
  targetType := targetCarrierB
  targetRaw := RawTerm.equivApply targetEquivRaw targetArgumentRaw
  targetTerm := Term.equivApply targetEquivTerm targetArgumentTerm
  typeStrengthens := carrierBSuccess
  rawStrengthens := by
    change
      Option.mapTwo
        (equivRaw.partialStrengthen? strengthening.back)
        (argumentRaw.partialStrengthen? strengthening.back)
        RawTerm.equivApply =
          some (RawTerm.equivApply targetEquivRaw targetArgumentRaw)
    rw [equivRawStrengthens, argumentRawStrengthens]
    rfl
  typeRenames :=
    Ty.partialStrengthen?_imp_rename carrierB
      strengthening.forward strengthening.back strengthening.injectsBack
      targetCarrierB carrierBSuccess
  rawRenames := by
    cases equivRawRenames
    cases argumentRawRenames
    rfl

/-- Univalence-beta equivalence application strengthens with the same
binary proof shape as `partialStrengthenTypedEquivApp`; only the raw
constructor differs.  Wrapper delegates the success path to
`partialStrengthenTypedEquivApplyOfSuccess` so the strengthening-image
soundness layer can skip the wrapper's dual `Option.casesOn`
discriminator wall over `Ty.equiv`'s carrier-pair pivots. -/
def partialStrengthenTypedEquivApply {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {carrierA carrierB : Ty level sourceScope}
    {targetCarrierA targetCarrierB : Ty level targetScope}
    {equivRaw argumentRaw : RawTerm sourceScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    {equivTerm : Term sourceCtx (Ty.equiv carrierA carrierB) equivRaw}
    {argumentTerm : Term sourceCtx carrierA argumentRaw}
    (carrierASuccess :
      carrierA.partialStrengthen? strengthening.back = some targetCarrierA)
    (carrierBSuccess :
      carrierB.partialStrengthen? strengthening.back = some targetCarrierB)
    (equivResult : StrengtheningResult strengthening equivTerm)
    (argumentResult : StrengtheningResult strengthening argumentTerm) :
    StrengtheningResult strengthening
      (Term.equivApply equivTerm argumentTerm) := by
  cases equivResult with
  | mk targetEquivType targetEquivRaw targetEquivTerm
      equivTypeStrengthens equivRawStrengthens equivTypeRenames
      equivRawRenames =>
      have expectedEquivTypeStrengthens :
          (Ty.equiv carrierA carrierB).partialStrengthen?
              strengthening.back =
            some (Ty.equiv targetCarrierA targetCarrierB) := by
        change
          Option.mapTwo
            (carrierA.partialStrengthen? strengthening.back)
            (carrierB.partialStrengthen? strengthening.back)
            Ty.equiv = some (Ty.equiv targetCarrierA targetCarrierB)
        rw [carrierASuccess, carrierBSuccess]
        rfl
      rw [expectedEquivTypeStrengthens] at equivTypeStrengthens
      cases equivTypeStrengthens
      cases argumentResult with
      | mk targetArgumentType targetArgumentRaw targetArgumentTerm
          argumentTypeStrengthens argumentRawStrengthens
          argumentTypeRenames argumentRawRenames =>
          rw [carrierASuccess] at argumentTypeStrengthens
          cases argumentTypeStrengthens
          exact partialStrengthenTypedEquivApplyOfSuccess
            targetEquivTerm targetArgumentTerm carrierASuccess
            carrierBSuccess equivRawStrengthens argumentRawStrengthens
            equivRawRenames argumentRawRenames

/-- `uaToEquiv` strengthens by strengthening its universe-path proof and
the schematic left/right carrier types and raw endpoints. -/
def partialStrengthenTypedUaToEquiv {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    (innerLevel : UniverseLevel)
    (innerLevelLt : innerLevel.toNat + 1 ≤ level)
    (leftTy rightTy : Ty level sourceScope)
    (targetLeftTy targetRightTy : Ty level targetScope)
    (leftTyRaw rightTyRaw : RawTerm sourceScope)
    (targetLeftTyRaw targetRightTyRaw : RawTerm targetScope)
    {proofRaw : RawTerm sourceScope}
    {proof :
      Term sourceCtx
        (Ty.id (Ty.universe innerLevel innerLevelLt) leftTyRaw rightTyRaw)
        proofRaw}
    (leftTyStrengthens :
      leftTy.partialStrengthen? strengthening.back = some targetLeftTy)
    (rightTyStrengthens :
      rightTy.partialStrengthen? strengthening.back = some targetRightTy)
    (leftRawStrengthens :
      leftTyRaw.partialStrengthen? strengthening.back = some targetLeftTyRaw)
    (rightRawStrengthens :
      rightTyRaw.partialStrengthen? strengthening.back = some targetRightTyRaw)
    (proofResult : StrengtheningResult strengthening proof) :
    StrengtheningResult strengthening
      (Term.uaToEquiv (context := sourceCtx) innerLevel innerLevelLt
        leftTy rightTy leftTyRaw rightTyRaw proof) := by
  cases proofResult with
  | mk targetProofType targetProofRaw targetProofTerm
      proofTypeStrengthens proofRawStrengthens proofTypeRenames
      proofRawRenames =>
      have expectedProofTypeStrengthens :
          (Ty.id (Ty.universe innerLevel innerLevelLt)
              leftTyRaw rightTyRaw).partialStrengthen? strengthening.back =
            some (Ty.id (Ty.universe innerLevel innerLevelLt)
              targetLeftTyRaw targetRightTyRaw) := by
        change
          Option.mapThree
            ((Ty.universe innerLevel innerLevelLt).partialStrengthen?
              strengthening.back)
            (leftTyRaw.partialStrengthen? strengthening.back)
            (rightTyRaw.partialStrengthen? strengthening.back)
            Ty.id =
              some (Ty.id (Ty.universe innerLevel innerLevelLt)
                targetLeftTyRaw targetRightTyRaw)
        rw [leftRawStrengthens, rightRawStrengthens]
        rfl
      rw [expectedProofTypeStrengthens] at proofTypeStrengthens
      cases proofTypeStrengthens
      exact {
        targetType := Ty.equiv targetLeftTy targetRightTy
        targetRaw := RawTerm.uaToEquiv targetProofRaw
        targetTerm :=
          Term.uaToEquiv (context := targetCtx) innerLevel innerLevelLt
            targetLeftTy targetRightTy targetLeftTyRaw targetRightTyRaw
            targetProofTerm
        typeStrengthens := by
          change
            Option.mapTwo
              (leftTy.partialStrengthen? strengthening.back)
              (rightTy.partialStrengthen? strengthening.back)
              Ty.equiv =
                some (Ty.equiv targetLeftTy targetRightTy)
          rw [leftTyStrengthens, rightTyStrengthens]
          rfl
        rawStrengthens := by
          change
            (match proofRaw.partialStrengthen? strengthening.back with
            | some strengthenedProof => some (RawTerm.uaToEquiv strengthenedProof)
            | none => none) =
                some (RawTerm.uaToEquiv targetProofRaw)
          rw [proofRawStrengthens]
        typeRenames := by
          simp only [Ty.rename]
          rw [Ty.partialStrengthen?_imp_rename leftTy
              strengthening.forward strengthening.back
              strengthening.injectsBack targetLeftTy leftTyStrengthens,
            Ty.partialStrengthen?_imp_rename rightTy
              strengthening.forward strengthening.back
              strengthening.injectsBack targetRightTy rightTyStrengthens]
        rawRenames := by
          cases proofRawRenames
          rfl
      }

/-- Observational funext strengthens by strengthening the pointwise
proof plus the schematic domain, codomain, and endpoint raws. -/
def partialStrengthenTypedOeqFunext {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    (domainType codomainType : Ty level sourceScope)
    (targetDomainType targetCodomainType : Ty level targetScope)
    (leftFunctionRaw rightFunctionRaw : RawTerm sourceScope)
    (targetLeftFunctionRaw targetRightFunctionRaw : RawTerm targetScope)
    {pointwiseRaw : RawTerm sourceScope}
    {pointwiseProof :
      Term sourceCtx
        (oeqFunextPointwiseType domainType codomainType
          leftFunctionRaw rightFunctionRaw)
        pointwiseRaw}
    (domainStrengthens :
      domainType.partialStrengthen? strengthening.back =
        some targetDomainType)
    (codomainStrengthens :
      codomainType.partialStrengthen? strengthening.back =
        some targetCodomainType)
    (leftFunctionStrengthens :
      leftFunctionRaw.partialStrengthen? strengthening.back =
        some targetLeftFunctionRaw)
    (rightFunctionStrengthens :
      rightFunctionRaw.partialStrengthen? strengthening.back =
        some targetRightFunctionRaw)
    (pointwiseResult : StrengtheningResult strengthening pointwiseProof) :
    StrengtheningResult strengthening
      (Term.oeqFunext (context := sourceCtx) domainType codomainType
        leftFunctionRaw rightFunctionRaw pointwiseProof) := by
  cases pointwiseResult with
  | mk targetPointwiseType targetPointwiseRaw targetPointwiseProof
      pointwiseTypeStrengthens pointwiseRawStrengthens
      pointwiseTypeRenames pointwiseRawRenames =>
      have codomainWeakenStrengthens :
          codomainType.weaken.partialStrengthen? strengthening.back.lift =
            some targetCodomainType.weaken := by
        rw [Ty.partialStrengthen?_weaken_lift codomainType
          strengthening.back, codomainStrengthens]
        rfl
      have leftWeakenStrengthens :
          leftFunctionRaw.weaken.partialStrengthen?
              strengthening.back.lift =
            some targetLeftFunctionRaw.weaken := by
        rw [RawTerm.partialStrengthen?_weaken_lift leftFunctionRaw
          strengthening.back, leftFunctionStrengthens]
        rfl
      have rightWeakenStrengthens :
          rightFunctionRaw.weaken.partialStrengthen?
              strengthening.back.lift =
            some targetRightFunctionRaw.weaken := by
        rw [RawTerm.partialStrengthen?_weaken_lift rightFunctionRaw
          strengthening.back, rightFunctionStrengthens]
        rfl
      have pointwiseExpectedStrengthens :
          (oeqFunextPointwiseType domainType codomainType
              leftFunctionRaw rightFunctionRaw).partialStrengthen?
              strengthening.back =
            some (oeqFunextPointwiseType targetDomainType targetCodomainType
              targetLeftFunctionRaw targetRightFunctionRaw) := by
        have codomainBodyStrengthens :
            (oeqFunextPointwiseCodomain codomainType
                leftFunctionRaw rightFunctionRaw).partialStrengthen?
                strengthening.back.lift =
              some (oeqFunextPointwiseCodomain targetCodomainType
                targetLeftFunctionRaw targetRightFunctionRaw) := by
          have leftAppStrengthens :
              (RawTerm.app leftFunctionRaw.weaken
                (RawTerm.var ⟨0, Nat.zero_lt_succ sourceScope⟩)
                ).partialStrengthen? strengthening.back.lift =
                some (RawTerm.app targetLeftFunctionRaw.weaken
                  (RawTerm.var ⟨0, Nat.zero_lt_succ targetScope⟩)) := by
            change
              Option.mapTwo
                (leftFunctionRaw.weaken.partialStrengthen?
                  strengthening.back.lift)
                (some (RawTerm.var ⟨0, Nat.zero_lt_succ targetScope⟩))
                RawTerm.app =
                  some (RawTerm.app targetLeftFunctionRaw.weaken
                    (RawTerm.var ⟨0, Nat.zero_lt_succ targetScope⟩))
            rw [leftWeakenStrengthens]
            rfl
          have rightAppStrengthens :
              (RawTerm.app rightFunctionRaw.weaken
                (RawTerm.var ⟨0, Nat.zero_lt_succ sourceScope⟩)
                ).partialStrengthen? strengthening.back.lift =
                some (RawTerm.app targetRightFunctionRaw.weaken
                  (RawTerm.var ⟨0, Nat.zero_lt_succ targetScope⟩)) := by
            change
              Option.mapTwo
                (rightFunctionRaw.weaken.partialStrengthen?
                  strengthening.back.lift)
                (some (RawTerm.var ⟨0, Nat.zero_lt_succ targetScope⟩))
                RawTerm.app =
                  some (RawTerm.app targetRightFunctionRaw.weaken
                    (RawTerm.var ⟨0, Nat.zero_lt_succ targetScope⟩))
            rw [rightWeakenStrengthens]
            rfl
          change
            Option.mapThree
              (codomainType.weaken.partialStrengthen?
                strengthening.back.lift)
              ((RawTerm.app leftFunctionRaw.weaken
                (RawTerm.var ⟨0, Nat.zero_lt_succ sourceScope⟩)
                ).partialStrengthen? strengthening.back.lift)
              ((RawTerm.app rightFunctionRaw.weaken
                (RawTerm.var ⟨0, Nat.zero_lt_succ sourceScope⟩)
                ).partialStrengthen? strengthening.back.lift)
              Ty.oeq =
                some (oeqFunextPointwiseCodomain targetCodomainType
                  targetLeftFunctionRaw targetRightFunctionRaw)
          rw [codomainWeakenStrengthens, leftAppStrengthens,
            rightAppStrengthens]
          rfl
        change
          Option.mapTwo
            (domainType.partialStrengthen? strengthening.back)
            ((oeqFunextPointwiseCodomain codomainType
                leftFunctionRaw rightFunctionRaw).partialStrengthen?
                strengthening.back.lift)
            Ty.piTy =
              some (oeqFunextPointwiseType targetDomainType
                targetCodomainType targetLeftFunctionRaw
                targetRightFunctionRaw)
        rw [domainStrengthens, codomainBodyStrengthens]
        rfl
      rw [pointwiseExpectedStrengthens] at pointwiseTypeStrengthens
      cases pointwiseTypeStrengthens
      exact {
        targetType :=
          Ty.oeq (Ty.arrow targetDomainType targetCodomainType)
            targetLeftFunctionRaw targetRightFunctionRaw
        targetRaw := RawTerm.oeqFunext targetPointwiseRaw
        targetTerm :=
          Term.oeqFunext (context := targetCtx)
            targetDomainType targetCodomainType targetLeftFunctionRaw
            targetRightFunctionRaw targetPointwiseProof
        typeStrengthens := by
          have arrowStrengthens :
              (Ty.arrow domainType codomainType).partialStrengthen?
                  strengthening.back =
                some (Ty.arrow targetDomainType targetCodomainType) := by
            change
              Option.mapTwo
                (domainType.partialStrengthen? strengthening.back)
                (codomainType.partialStrengthen? strengthening.back)
                Ty.arrow =
                  some (Ty.arrow targetDomainType targetCodomainType)
            rw [domainStrengthens, codomainStrengthens]
            rfl
          change
            Option.mapThree
              ((Ty.arrow domainType codomainType).partialStrengthen?
                strengthening.back)
              (leftFunctionRaw.partialStrengthen? strengthening.back)
              (rightFunctionRaw.partialStrengthen? strengthening.back)
              Ty.oeq =
                some
                  (Ty.oeq (Ty.arrow targetDomainType targetCodomainType)
                    targetLeftFunctionRaw targetRightFunctionRaw)
          rw [arrowStrengthens, leftFunctionStrengthens,
            rightFunctionStrengthens]
          rfl
        rawStrengthens := by
          change
            (match pointwiseRaw.partialStrengthen? strengthening.back with
            | some strengthenedPointwise =>
                some (RawTerm.oeqFunext strengthenedPointwise)
            | none => none) =
              some (RawTerm.oeqFunext targetPointwiseRaw)
          rw [pointwiseRawStrengthens]
        typeRenames := by
          exact
            Ty.partialStrengthen?_imp_rename
              (Ty.oeq (Ty.arrow domainType codomainType)
                leftFunctionRaw rightFunctionRaw)
              strengthening.forward strengthening.back
              strengthening.injectsBack
              (Ty.oeq (Ty.arrow targetDomainType targetCodomainType)
                targetLeftFunctionRaw targetRightFunctionRaw)
              (by
                have arrowStrengthens :
                    (Ty.arrow domainType codomainType).partialStrengthen?
                        strengthening.back =
                      some (Ty.arrow targetDomainType targetCodomainType) := by
                  change
                    Option.mapTwo
                      (domainType.partialStrengthen? strengthening.back)
                      (codomainType.partialStrengthen? strengthening.back)
                      Ty.arrow =
                        some (Ty.arrow targetDomainType targetCodomainType)
                  rw [domainStrengthens, codomainStrengthens]
                  rfl
                change
                  Option.mapThree
                    ((Ty.arrow domainType codomainType).partialStrengthen?
                      strengthening.back)
                    (leftFunctionRaw.partialStrengthen? strengthening.back)
                    (rightFunctionRaw.partialStrengthen? strengthening.back)
                    Ty.oeq =
                      some
                        (Ty.oeq
                          (Ty.arrow targetDomainType targetCodomainType)
                          targetLeftFunctionRaw targetRightFunctionRaw)
                rw [arrowStrengthens, leftFunctionStrengthens,
                  rightFunctionStrengthens]
                rfl)
        rawRenames := by
          cases pointwiseRawRenames
          rfl
      }

end Term

end LeanFX2
