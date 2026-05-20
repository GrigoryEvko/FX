import LeanFX2.Term.PartialStrengthen.Constructors.Reflexivity

/-! # Term/PartialStrengthen/Constructors/Identity

Typed partial-strengthening producers for identity, observational equality,
and strict identity recursors.
-/

namespace LeanFX2

namespace Term

/-- Strict identity reflexivity strengthens by strengthening the carrier
type and raw witness endpoint, preserving the strict-mode evidence. -/
def partialStrengthenTypedIdStrictRefl {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    (modeIsStrict : mode = Mode.strict)
    {carrier : Ty level sourceScope}
    {targetCarrier : Ty level targetScope}
    {rawWitness : RawTerm sourceScope}
    {targetWitness : RawTerm targetScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    (carrierStrengthens :
      carrier.partialStrengthen? strengthening.back = some targetCarrier)
    (witnessStrengthens :
      rawWitness.partialStrengthen? strengthening.back =
        some targetWitness) :
    StrengtheningResult strengthening
      (Term.idStrictRefl (context := sourceCtx) modeIsStrict
        carrier rawWitness) where
  targetType := Ty.idStrict targetCarrier targetWitness targetWitness
  targetRaw := RawTerm.idStrictRefl targetWitness
  targetTerm := Term.idStrictRefl (context := targetCtx) modeIsStrict
    targetCarrier targetWitness
  typeStrengthens := by
    change
      Option.mapThree
        (carrier.partialStrengthen? strengthening.back)
        (rawWitness.partialStrengthen? strengthening.back)
        (rawWitness.partialStrengthen? strengthening.back)
        Ty.idStrict =
        some (Ty.idStrict targetCarrier targetWitness targetWitness)
    rw [carrierStrengthens, witnessStrengthens]
    rfl
  rawStrengthens := by
    change
      (match rawWitness.partialStrengthen? strengthening.back with
      | some strengthenedWitness =>
          some (RawTerm.idStrictRefl strengthenedWitness)
      | none => none) =
        some (RawTerm.idStrictRefl targetWitness)
    rw [witnessStrengthens]
  typeRenames :=
    Ty.partialStrengthen?_imp_rename
      (Ty.idStrict carrier rawWitness rawWitness)
      strengthening.forward strengthening.back strengthening.injectsBack
      (Ty.idStrict targetCarrier targetWitness targetWitness)
      (by
        change
          Option.mapThree
            (carrier.partialStrengthen? strengthening.back)
            (rawWitness.partialStrengthen? strengthening.back)
            (rawWitness.partialStrengthen? strengthening.back)
            Ty.idStrict =
            some (Ty.idStrict targetCarrier targetWitness targetWitness)
        rw [carrierStrengthens, witnessStrengthens]
        rfl)
  rawRenames :=
    RawTerm.partialStrengthen?_imp_rename
      (RawTerm.idStrictRefl rawWitness) strengthening.forward
      strengthening.back strengthening.injectsBack
      (RawTerm.idStrictRefl targetWitness)
      (by
        change
          (match rawWitness.partialStrengthen? strengthening.back with
          | some strengthenedWitness =>
              some (RawTerm.idStrictRefl strengthenedWitness)
          | none => none) =
            some (RawTerm.idStrictRefl targetWitness)
        rw [witnessStrengthens])

/-- Success branch for identity-elimination strengthening.

Takes pre-decomposed witnesses for the carrier, left endpoint, right
endpoint of the witness's identity type, plus the strengthened
base-case and witness-term values.  Splits out the term-mode body so
the strengthening-image soundness layer can prove the soundness
theorem without traversing `Option.casesOn` on the three
`partialStrengthen?` pivots (carrier / leftEndpoint / rightEndpoint)
inside the wrapper's tactic-mode `cases` chain. -/
def partialStrengthenTypedIdJOfSuccess {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {carrier : Ty level sourceScope}
    {leftEndpoint rightEndpoint : RawTerm sourceScope}
    {motiveType : Ty level sourceScope}
    {targetMotiveType : Ty level targetScope}
    {baseRaw witnessRaw : RawTerm sourceScope}
    {targetBaseRaw targetWitnessRaw : RawTerm targetScope}
    {targetCarrier : Ty level targetScope}
    {targetLeftEndpoint targetRightEndpoint : RawTerm targetScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    {baseCase : Term sourceCtx motiveType baseRaw}
    {witness :
      Term sourceCtx (Ty.id carrier leftEndpoint rightEndpoint) witnessRaw}
    (targetBaseTerm : Term targetCtx targetMotiveType targetBaseRaw)
    (targetWitnessTerm :
      Term targetCtx
        (Ty.id targetCarrier targetLeftEndpoint targetRightEndpoint)
        targetWitnessRaw)
    (baseTypeStrengthens :
      motiveType.partialStrengthen? strengthening.back =
        some targetMotiveType)
    (_carrierSuccess :
      carrier.partialStrengthen? strengthening.back = some targetCarrier)
    (_leftSuccess :
      leftEndpoint.partialStrengthen? strengthening.back =
        some targetLeftEndpoint)
    (_rightSuccess :
      rightEndpoint.partialStrengthen? strengthening.back =
        some targetRightEndpoint)
    (baseRawStrengthens :
      baseRaw.partialStrengthen? strengthening.back = some targetBaseRaw)
    (witnessRawStrengthens :
      witnessRaw.partialStrengthen? strengthening.back =
        some targetWitnessRaw)
    (baseTypeRenames :
      motiveType = targetMotiveType.rename strengthening.forward)
    (baseRawRenames : baseRaw = targetBaseRaw.rename strengthening.forward)
    (witnessRawRenames :
      witnessRaw = targetWitnessRaw.rename strengthening.forward) :
    StrengtheningResult strengthening (Term.idJ baseCase witness) where
  targetType := targetMotiveType
  targetRaw := RawTerm.idJ targetBaseRaw targetWitnessRaw
  targetTerm := Term.idJ targetBaseTerm targetWitnessTerm
  typeStrengthens := baseTypeStrengthens
  rawStrengthens := by
    change
      Option.mapTwo
        (baseRaw.partialStrengthen? strengthening.back)
        (witnessRaw.partialStrengthen? strengthening.back)
        RawTerm.idJ =
          some (RawTerm.idJ targetBaseRaw targetWitnessRaw)
    rw [baseRawStrengthens, witnessRawStrengthens]
    rfl
  typeRenames := baseTypeRenames
  rawRenames := by
    cases baseRawRenames
    cases witnessRawRenames
    rfl

/-- Identity eliminator strengthens by strengthening its base case and
witness, then decomposing the strengthened identity type carried by the
witness. -/
def partialStrengthenTypedIdJ {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {carrier : Ty level sourceScope}
    {targetCarrier : Ty level targetScope}
    {leftEndpoint rightEndpoint : RawTerm sourceScope}
    {targetLeftEndpoint targetRightEndpoint : RawTerm targetScope}
    {motiveType : Ty level sourceScope}
    {baseRaw witnessRaw : RawTerm sourceScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    {baseCase : Term sourceCtx motiveType baseRaw}
    {witness :
      Term sourceCtx (Ty.id carrier leftEndpoint rightEndpoint) witnessRaw}
    (carrierSuccess :
      carrier.partialStrengthen? strengthening.back = some targetCarrier)
    (leftSuccess :
      leftEndpoint.partialStrengthen? strengthening.back =
        some targetLeftEndpoint)
    (rightSuccess :
      rightEndpoint.partialStrengthen? strengthening.back =
        some targetRightEndpoint)
    (baseResult : StrengtheningResult strengthening baseCase)
    (witnessResult : StrengtheningResult strengthening witness) :
    StrengtheningResult strengthening (Term.idJ baseCase witness) := by
  cases baseResult with
  | mk targetMotiveType targetBaseRaw targetBaseTerm baseTypeStrengthens
      baseRawStrengthens baseTypeRenames baseRawRenames =>
      cases witnessResult with
      | mk targetWitnessType targetWitnessRaw targetWitnessTerm
          witnessTypeStrengthens witnessRawStrengthens witnessTypeRenames
          witnessRawRenames =>
          have expectedWitnessTypeStrengthens :
              (Ty.id carrier leftEndpoint rightEndpoint).partialStrengthen?
                  strengthening.back =
                some (Ty.id targetCarrier targetLeftEndpoint
                  targetRightEndpoint) := by
            change
              Option.mapThree
                (carrier.partialStrengthen? strengthening.back)
                (leftEndpoint.partialStrengthen? strengthening.back)
                (rightEndpoint.partialStrengthen? strengthening.back)
                Ty.id =
                  some (Ty.id targetCarrier targetLeftEndpoint
                    targetRightEndpoint)
            rw [carrierSuccess, leftSuccess, rightSuccess]
            rfl
          rw [expectedWitnessTypeStrengthens] at witnessTypeStrengthens
          cases witnessTypeStrengthens
          exact partialStrengthenTypedIdJOfSuccess
            targetBaseTerm targetWitnessTerm baseTypeStrengthens
            carrierSuccess leftSuccess rightSuccess
            baseRawStrengthens witnessRawStrengthens
            baseTypeRenames baseRawRenames witnessRawRenames

/-- Success branch for observational-equality elimination strengthening.
Mirrors `partialStrengthenTypedIdJOfSuccess`: pre-decomposed witnesses
for the observational equality's carrier/leftEndpoint/rightEndpoint
pivots, plus strengthened base-case and witness-term values.  Allows
soundness to apply `Term.oeqJ_HEq_congr` without traversing the
wrapper's triple `Option.casesOn` discriminator wall. -/
def partialStrengthenTypedOeqJOfSuccess {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {carrier : Ty level sourceScope}
    {leftEndpoint rightEndpoint : RawTerm sourceScope}
    {motiveType : Ty level sourceScope}
    {targetMotiveType : Ty level targetScope}
    {baseRaw witnessRaw : RawTerm sourceScope}
    {targetBaseRaw targetWitnessRaw : RawTerm targetScope}
    {targetCarrier : Ty level targetScope}
    {targetLeftEndpoint targetRightEndpoint : RawTerm targetScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    {baseCase : Term sourceCtx motiveType baseRaw}
    {witness :
      Term sourceCtx (Ty.oeq carrier leftEndpoint rightEndpoint) witnessRaw}
    (targetBaseTerm : Term targetCtx targetMotiveType targetBaseRaw)
    (targetWitnessTerm :
      Term targetCtx
        (Ty.oeq targetCarrier targetLeftEndpoint targetRightEndpoint)
        targetWitnessRaw)
    (baseTypeStrengthens :
      motiveType.partialStrengthen? strengthening.back =
        some targetMotiveType)
    (_carrierSuccess :
      carrier.partialStrengthen? strengthening.back = some targetCarrier)
    (_leftSuccess :
      leftEndpoint.partialStrengthen? strengthening.back =
        some targetLeftEndpoint)
    (_rightSuccess :
      rightEndpoint.partialStrengthen? strengthening.back =
        some targetRightEndpoint)
    (baseRawStrengthens :
      baseRaw.partialStrengthen? strengthening.back = some targetBaseRaw)
    (witnessRawStrengthens :
      witnessRaw.partialStrengthen? strengthening.back =
        some targetWitnessRaw)
    (baseTypeRenames :
      motiveType = targetMotiveType.rename strengthening.forward)
    (baseRawRenames : baseRaw = targetBaseRaw.rename strengthening.forward)
    (witnessRawRenames :
      witnessRaw = targetWitnessRaw.rename strengthening.forward) :
    StrengtheningResult strengthening (Term.oeqJ baseCase witness) where
  targetType := targetMotiveType
  targetRaw := RawTerm.oeqJ targetBaseRaw targetWitnessRaw
  targetTerm := Term.oeqJ targetBaseTerm targetWitnessTerm
  typeStrengthens := baseTypeStrengthens
  rawStrengthens := by
    change
      Option.mapTwo
        (baseRaw.partialStrengthen? strengthening.back)
        (witnessRaw.partialStrengthen? strengthening.back)
        RawTerm.oeqJ =
          some (RawTerm.oeqJ targetBaseRaw targetWitnessRaw)
    rw [baseRawStrengthens, witnessRawStrengthens]
    rfl
  typeRenames := baseTypeRenames
  rawRenames := by
    cases baseRawRenames
    cases witnessRawRenames
    rfl

/-- Observational-equality eliminator strengthens by strengthening its
base case and witness, then decomposing the strengthened observational
equality type carried by the witness. -/
def partialStrengthenTypedOeqJ {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {carrier : Ty level sourceScope}
    {targetCarrier : Ty level targetScope}
    {leftEndpoint rightEndpoint : RawTerm sourceScope}
    {targetLeftEndpoint targetRightEndpoint : RawTerm targetScope}
    {motiveType : Ty level sourceScope}
    {baseRaw witnessRaw : RawTerm sourceScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    {baseCase : Term sourceCtx motiveType baseRaw}
    {witness :
      Term sourceCtx (Ty.oeq carrier leftEndpoint rightEndpoint) witnessRaw}
    (carrierSuccess :
      carrier.partialStrengthen? strengthening.back = some targetCarrier)
    (leftSuccess :
      leftEndpoint.partialStrengthen? strengthening.back =
        some targetLeftEndpoint)
    (rightSuccess :
      rightEndpoint.partialStrengthen? strengthening.back =
        some targetRightEndpoint)
    (baseResult : StrengtheningResult strengthening baseCase)
    (witnessResult : StrengtheningResult strengthening witness) :
    StrengtheningResult strengthening (Term.oeqJ baseCase witness) := by
  cases baseResult with
  | mk targetMotiveType targetBaseRaw targetBaseTerm baseTypeStrengthens
      baseRawStrengthens baseTypeRenames baseRawRenames =>
      cases witnessResult with
      | mk targetWitnessType targetWitnessRaw targetWitnessTerm
          witnessTypeStrengthens witnessRawStrengthens witnessTypeRenames
          witnessRawRenames =>
          have expectedWitnessTypeStrengthens :
              (Ty.oeq carrier leftEndpoint rightEndpoint).partialStrengthen?
                  strengthening.back =
                some (Ty.oeq targetCarrier targetLeftEndpoint
                  targetRightEndpoint) := by
            change
              Option.mapThree
                (carrier.partialStrengthen? strengthening.back)
                (leftEndpoint.partialStrengthen? strengthening.back)
                (rightEndpoint.partialStrengthen? strengthening.back)
                Ty.oeq =
                  some (Ty.oeq targetCarrier targetLeftEndpoint
                    targetRightEndpoint)
            rw [carrierSuccess, leftSuccess, rightSuccess]
            rfl
          rw [expectedWitnessTypeStrengthens] at witnessTypeStrengthens
          cases witnessTypeStrengthens
          exact partialStrengthenTypedOeqJOfSuccess
            targetBaseTerm targetWitnessTerm baseTypeStrengthens
            carrierSuccess leftSuccess rightSuccess
            baseRawStrengthens witnessRawStrengthens
            baseTypeRenames baseRawRenames witnessRawRenames

/-- Success branch for strict-identity recursor strengthening.  Mirrors
`partialStrengthenTypedIdJOfSuccess` with the strict-identity carrier
shape and the `modeIsStrict` evidence. -/
def partialStrengthenTypedIdStrictRecOfSuccess {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    (modeIsStrict : mode = Mode.strict)
    {carrier : Ty level sourceScope}
    {leftEndpoint rightEndpoint : RawTerm sourceScope}
    {motiveType : Ty level sourceScope}
    {targetMotiveType : Ty level targetScope}
    {baseRaw witnessRaw : RawTerm sourceScope}
    {targetBaseRaw targetWitnessRaw : RawTerm targetScope}
    {targetCarrier : Ty level targetScope}
    {targetLeftEndpoint targetRightEndpoint : RawTerm targetScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    {baseCase : Term sourceCtx motiveType baseRaw}
    {witness :
      Term sourceCtx
        (Ty.idStrict carrier leftEndpoint rightEndpoint) witnessRaw}
    (targetBaseTerm : Term targetCtx targetMotiveType targetBaseRaw)
    (targetWitnessTerm :
      Term targetCtx
        (Ty.idStrict targetCarrier targetLeftEndpoint targetRightEndpoint)
        targetWitnessRaw)
    (baseTypeStrengthens :
      motiveType.partialStrengthen? strengthening.back =
        some targetMotiveType)
    (_carrierSuccess :
      carrier.partialStrengthen? strengthening.back = some targetCarrier)
    (_leftSuccess :
      leftEndpoint.partialStrengthen? strengthening.back =
        some targetLeftEndpoint)
    (_rightSuccess :
      rightEndpoint.partialStrengthen? strengthening.back =
        some targetRightEndpoint)
    (baseRawStrengthens :
      baseRaw.partialStrengthen? strengthening.back = some targetBaseRaw)
    (witnessRawStrengthens :
      witnessRaw.partialStrengthen? strengthening.back =
        some targetWitnessRaw)
    (baseTypeRenames :
      motiveType = targetMotiveType.rename strengthening.forward)
    (baseRawRenames : baseRaw = targetBaseRaw.rename strengthening.forward)
    (witnessRawRenames :
      witnessRaw = targetWitnessRaw.rename strengthening.forward) :
    StrengtheningResult strengthening
      (Term.idStrictRec modeIsStrict baseCase witness) where
  targetType := targetMotiveType
  targetRaw := RawTerm.idStrictRec targetBaseRaw targetWitnessRaw
  targetTerm := Term.idStrictRec modeIsStrict targetBaseTerm
    targetWitnessTerm
  typeStrengthens := baseTypeStrengthens
  rawStrengthens := by
    change
      Option.mapTwo
        (baseRaw.partialStrengthen? strengthening.back)
        (witnessRaw.partialStrengthen? strengthening.back)
        RawTerm.idStrictRec =
          some (RawTerm.idStrictRec targetBaseRaw targetWitnessRaw)
    rw [baseRawStrengthens, witnessRawStrengthens]
    rfl
  typeRenames := baseTypeRenames
  rawRenames := by
    cases baseRawRenames
    cases witnessRawRenames
    rfl

/-- Strict-identity recursor strengthens by strengthening its base case
and witness, then decomposing the strengthened strict identity type
carried by the witness. -/
def partialStrengthenTypedIdStrictRec {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    (modeIsStrict : mode = Mode.strict)
    {carrier : Ty level sourceScope}
    {targetCarrier : Ty level targetScope}
    {leftEndpoint rightEndpoint : RawTerm sourceScope}
    {targetLeftEndpoint targetRightEndpoint : RawTerm targetScope}
    {motiveType : Ty level sourceScope}
    {baseRaw witnessRaw : RawTerm sourceScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    {baseCase : Term sourceCtx motiveType baseRaw}
    {witness :
      Term sourceCtx
        (Ty.idStrict carrier leftEndpoint rightEndpoint) witnessRaw}
    (carrierSuccess :
      carrier.partialStrengthen? strengthening.back = some targetCarrier)
    (leftSuccess :
      leftEndpoint.partialStrengthen? strengthening.back =
        some targetLeftEndpoint)
    (rightSuccess :
      rightEndpoint.partialStrengthen? strengthening.back =
        some targetRightEndpoint)
    (baseResult : StrengtheningResult strengthening baseCase)
    (witnessResult : StrengtheningResult strengthening witness) :
    StrengtheningResult strengthening
      (Term.idStrictRec modeIsStrict baseCase witness) := by
  cases baseResult with
  | mk targetMotiveType targetBaseRaw targetBaseTerm baseTypeStrengthens
      baseRawStrengthens baseTypeRenames baseRawRenames =>
      cases witnessResult with
      | mk targetWitnessType targetWitnessRaw targetWitnessTerm
          witnessTypeStrengthens witnessRawStrengthens witnessTypeRenames
          witnessRawRenames =>
          have expectedWitnessTypeStrengthens :
              (Ty.idStrict carrier leftEndpoint
                  rightEndpoint).partialStrengthen?
                  strengthening.back =
                some (Ty.idStrict targetCarrier targetLeftEndpoint
                  targetRightEndpoint) := by
            change
              Option.mapThree
                (carrier.partialStrengthen? strengthening.back)
                (leftEndpoint.partialStrengthen? strengthening.back)
                (rightEndpoint.partialStrengthen? strengthening.back)
                Ty.idStrict =
                  some (Ty.idStrict targetCarrier targetLeftEndpoint
                    targetRightEndpoint)
            rw [carrierSuccess, leftSuccess, rightSuccess]
            rfl
          rw [expectedWitnessTypeStrengthens] at witnessTypeStrengthens
          cases witnessTypeStrengthens
          exact partialStrengthenTypedIdStrictRecOfSuccess
            modeIsStrict targetBaseTerm targetWitnessTerm
            baseTypeStrengthens carrierSuccess leftSuccess
            rightSuccess baseRawStrengthens witnessRawStrengthens
            baseTypeRenames baseRawRenames witnessRawRenames

end Term

end LeanFX2
