import LeanFX2.Term.PartialStrengthen.Constructors.Refine

/-! # Term/PartialStrengthen/Constructors/Reflexivity

Typed partial-strengthening producers for homogeneous and observational
equality reflexivity terms.
-/

namespace LeanFX2

namespace Term

/-- HoTT reflexivity strengthens by strengthening the carrier type and
the raw witness endpoint. -/
def partialStrengthenTypedRefl {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
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
      (Term.refl (context := sourceCtx) carrier rawWitness) where
  targetType := Ty.id targetCarrier targetWitness targetWitness
  targetRaw := RawTerm.refl targetWitness
  targetTerm := Term.refl (context := targetCtx) targetCarrier targetWitness
  typeStrengthens := by
    change
      Option.mapThree
        (carrier.partialStrengthen? strengthening.back)
        (rawWitness.partialStrengthen? strengthening.back)
        (rawWitness.partialStrengthen? strengthening.back)
        Ty.id =
        some (Ty.id targetCarrier targetWitness targetWitness)
    rw [carrierStrengthens, witnessStrengthens]
    rfl
  rawStrengthens := by
    change
      (match rawWitness.partialStrengthen? strengthening.back with
      | some strengthenedWitness => some (RawTerm.refl strengthenedWitness)
      | none => none) =
        some (RawTerm.refl targetWitness)
    rw [witnessStrengthens]
  typeRenames :=
    Ty.partialStrengthen?_imp_rename
      (Ty.id carrier rawWitness rawWitness)
      strengthening.forward strengthening.back strengthening.injectsBack
      (Ty.id targetCarrier targetWitness targetWitness)
      (by
        change
          Option.mapThree
            (carrier.partialStrengthen? strengthening.back)
            (rawWitness.partialStrengthen? strengthening.back)
            (rawWitness.partialStrengthen? strengthening.back)
            Ty.id =
            some (Ty.id targetCarrier targetWitness targetWitness)
        rw [carrierStrengthens, witnessStrengthens]
        rfl)
  rawRenames :=
    RawTerm.partialStrengthen?_imp_rename
      (RawTerm.refl rawWitness) strengthening.forward strengthening.back
      strengthening.injectsBack (RawTerm.refl targetWitness)
      (by
        change
          (match rawWitness.partialStrengthen? strengthening.back with
          | some strengthenedWitness => some (RawTerm.refl strengthenedWitness)
          | none => none) =
            some (RawTerm.refl targetWitness)
        rw [witnessStrengthens])

/-- Observational-equality reflexivity strengthens by strengthening the
carrier type and raw witness endpoint. -/
def partialStrengthenTypedOeqRefl {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
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
      (Term.oeqRefl (context := sourceCtx) carrier rawWitness) where
  targetType := Ty.oeq targetCarrier targetWitness targetWitness
  targetRaw := RawTerm.oeqRefl targetWitness
  targetTerm := Term.oeqRefl (context := targetCtx) targetCarrier targetWitness
  typeStrengthens := by
    change
      Option.mapThree
        (carrier.partialStrengthen? strengthening.back)
        (rawWitness.partialStrengthen? strengthening.back)
        (rawWitness.partialStrengthen? strengthening.back)
        Ty.oeq =
        some (Ty.oeq targetCarrier targetWitness targetWitness)
    rw [carrierStrengthens, witnessStrengthens]
    rfl
  rawStrengthens := by
    change
      (match rawWitness.partialStrengthen? strengthening.back with
      | some strengthenedWitness => some (RawTerm.oeqRefl strengthenedWitness)
      | none => none) =
        some (RawTerm.oeqRefl targetWitness)
    rw [witnessStrengthens]
  typeRenames :=
    Ty.partialStrengthen?_imp_rename
      (Ty.oeq carrier rawWitness rawWitness)
      strengthening.forward strengthening.back strengthening.injectsBack
      (Ty.oeq targetCarrier targetWitness targetWitness)
      (by
        change
          Option.mapThree
            (carrier.partialStrengthen? strengthening.back)
            (rawWitness.partialStrengthen? strengthening.back)
            (rawWitness.partialStrengthen? strengthening.back)
            Ty.oeq =
            some (Ty.oeq targetCarrier targetWitness targetWitness)
        rw [carrierStrengthens, witnessStrengthens]
        rfl)
  rawRenames :=
    RawTerm.partialStrengthen?_imp_rename
      (RawTerm.oeqRefl rawWitness) strengthening.forward strengthening.back
      strengthening.injectsBack (RawTerm.oeqRefl targetWitness)
      (by
        change
          (match rawWitness.partialStrengthen? strengthening.back with
          | some strengthenedWitness =>
              some (RawTerm.oeqRefl strengthenedWitness)
          | none => none) =
            some (RawTerm.oeqRefl targetWitness)
        rw [witnessStrengthens])

end Term

end LeanFX2
