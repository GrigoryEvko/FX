import LeanFX2.Term.PartialStrengthen.Constructors.CollectionsAndSums

/-! # Term/PartialStrengthen/Constructors/Refine

Typed partial-strengthening producers for refinement introduction and
refinement elimination.
-/

namespace LeanFX2

namespace Term

/-- Refinement introduction strengthens by strengthening its base value,
unit proof, and binder-indexed predicate raw. -/
def partialStrengthenTypedRefineIntro {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {baseType : Ty level sourceScope}
    {predicate : RawTerm (sourceScope + 1)}
    {targetPredicate : RawTerm (targetScope + 1)}
    {valueRaw proofRaw : RawTerm sourceScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    {baseValue : Term sourceCtx baseType valueRaw}
    {predicateProof : Term sourceCtx Ty.unit proofRaw}
    (predicateStrengthens :
      predicate.partialStrengthen? strengthening.back.lift =
        some targetPredicate)
    (baseResult : StrengtheningResult strengthening baseValue)
    (proofResult : StrengtheningResult strengthening predicateProof) :
    StrengtheningResult strengthening
      (Term.refineIntro predicate baseValue predicateProof) := by
  cases proofResult with
  | mk targetProofType targetProofRaw targetProofTerm proofTypeStrengthens
      proofRawStrengthens proofTypeRenames proofRawRenames =>
      cases proofTypeStrengthens
      exact {
        targetType := Ty.refine baseResult.targetType targetPredicate
        targetRaw := RawTerm.refineIntro baseResult.targetRaw targetProofRaw
        targetTerm := Term.refineIntro targetPredicate baseResult.targetTerm
          targetProofTerm
        typeStrengthens := by
          change
            Option.mapTwo
              (baseType.partialStrengthen? strengthening.back)
              (predicate.partialStrengthen? strengthening.back.lift)
              Ty.refine =
              some (Ty.refine baseResult.targetType targetPredicate)
          rw [baseResult.typeStrengthens, predicateStrengthens]
          rfl
        rawStrengthens := by
          change
            Option.mapTwo
              (valueRaw.partialStrengthen? strengthening.back)
              (proofRaw.partialStrengthen? strengthening.back)
              RawTerm.refineIntro =
              some (RawTerm.refineIntro baseResult.targetRaw targetProofRaw)
          rw [baseResult.rawStrengthens, proofRawStrengthens]
          rfl
        typeRenames :=
          Ty.partialStrengthen?_imp_rename
            (Ty.refine baseType predicate)
            strengthening.forward strengthening.back strengthening.injectsBack
            (Ty.refine baseResult.targetType targetPredicate)
            (by
              change
                Option.mapTwo
                  (baseType.partialStrengthen? strengthening.back)
                  (predicate.partialStrengthen? strengthening.back.lift)
                  Ty.refine =
                  some (Ty.refine baseResult.targetType targetPredicate)
              rw [baseResult.typeStrengthens, predicateStrengthens]
              rfl)
        rawRenames := by
          exact RawTerm.partialStrengthen?_imp_rename
            (RawTerm.refineIntro valueRaw proofRaw)
            strengthening.forward strengthening.back strengthening.injectsBack
            (RawTerm.refineIntro baseResult.targetRaw targetProofRaw)
            (by
              change
                Option.mapTwo
                  (valueRaw.partialStrengthen? strengthening.back)
                  (proofRaw.partialStrengthen? strengthening.back)
                  RawTerm.refineIntro =
                  some (RawTerm.refineIntro baseResult.targetRaw
                    targetProofRaw)
              rw [baseResult.rawStrengthens, proofRawStrengthens]
              rfl)
      }

/-- Success branch for refinement-elimination strengthening.

Takes pre-decomposed witnesses for the base type, predicate, and the
strengthened refined-value term.  Splits out the term-mode body so the
strengthening-image soundness layer can prove the soundness theorem
without traversing `Option.casesOn` on the `partialStrengthen?` pivots
inside the wrapper's tactic-mode `cases` chain. -/
def partialStrengthenTypedRefineElimOfSuccess {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {baseType : Ty level sourceScope}
    {predicate : RawTerm (sourceScope + 1)}
    {refinedRaw : RawTerm sourceScope}
    {targetBaseType : Ty level targetScope}
    {targetPredicate : RawTerm (targetScope + 1)}
    {targetRefinedRaw : RawTerm targetScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    {refinedValue :
      Term sourceCtx (Ty.refine baseType predicate) refinedRaw}
    (targetRefinedTerm :
      Term targetCtx (Ty.refine targetBaseType targetPredicate)
        targetRefinedRaw)
    (baseSuccess :
      baseType.partialStrengthen? strengthening.back = some targetBaseType)
    (_predicateSuccess :
      predicate.partialStrengthen? strengthening.back.lift =
        some targetPredicate)
    (refinedRawStrengthens :
      refinedRaw.partialStrengthen? strengthening.back =
        some targetRefinedRaw)
    (refinedRawRenames :
      refinedRaw = targetRefinedRaw.rename strengthening.forward) :
    StrengtheningResult strengthening (Term.refineElim refinedValue) := {
  targetType := targetBaseType
  targetRaw := RawTerm.refineElim targetRefinedRaw
  targetTerm := Term.refineElim targetRefinedTerm
  typeStrengthens := baseSuccess
  rawStrengthens := by
    change
      (match refinedRaw.partialStrengthen? strengthening.back with
        | some strengthenedRefined =>
            some (RawTerm.refineElim strengthenedRefined)
        | none => none) =
        some (RawTerm.refineElim targetRefinedRaw)
    rw [refinedRawStrengthens]
  typeRenames :=
    Ty.partialStrengthen?_imp_rename baseType
      strengthening.forward strengthening.back strengthening.injectsBack
      targetBaseType baseSuccess
  rawRenames := by
    cases refinedRawRenames
    rfl
}

/-- Refinement elimination strengthens by strengthening its refined
payload and projecting the strengthened base type out of the refined
type index.

App-pattern: takes the base-type and predicate strengthening witnesses
`baseSuccess` / `predicateSuccess` as explicit parameters, lifted from
the dispatcher's nested option-splits.  The body destructures the
refined value's `StrengtheningResult`, aligns the `Ty.refine` shape via
`rw` + `cases` on the derived equation, then delegates to
`partialStrengthenTypedRefineElimOfSuccess`.  This shape admits a
clean App-pattern soundness proof
(`partialStrengthenTypedRefineElim_sound`) by mirror-destructure +
final-arm `OfSuccess_sound` delegation. -/
def partialStrengthenTypedRefineElim {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {baseType : Ty level sourceScope}
    {predicate : RawTerm (sourceScope + 1)}
    {targetBaseType : Ty level targetScope}
    {targetPredicate : RawTerm (targetScope + 1)}
    {refinedRaw : RawTerm sourceScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    {refinedValue :
      Term sourceCtx (Ty.refine baseType predicate) refinedRaw}
    (baseSuccess :
      baseType.partialStrengthen? strengthening.back = some targetBaseType)
    (predicateSuccess :
      predicate.partialStrengthen? strengthening.back.lift =
        some targetPredicate)
    (refinedResult : StrengtheningResult strengthening refinedValue) :
    StrengtheningResult strengthening (Term.refineElim refinedValue) := by
  cases refinedResult with
  | mk targetType targetRaw targetTerm typeStrengthens rawStrengthens
      typeRenames rawRenames =>
      have expectedRefineTypeStrengthens :
          (Ty.refine baseType predicate).partialStrengthen? strengthening.back =
            some (Ty.refine targetBaseType targetPredicate) := by
        change
          Option.mapTwo
            (baseType.partialStrengthen? strengthening.back)
            (predicate.partialStrengthen? strengthening.back.lift)
            Ty.refine =
              some (Ty.refine targetBaseType targetPredicate)
        rw [baseSuccess, predicateSuccess]
        rfl
      rw [expectedRefineTypeStrengthens] at typeStrengthens
      cases typeStrengthens
      exact partialStrengthenTypedRefineElimOfSuccess
        targetTerm baseSuccess predicateSuccess rawStrengthens rawRenames
end Term

end LeanFX2
