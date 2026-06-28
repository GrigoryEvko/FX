import FX1Poly.Typed.Metatheory.SubjectReduction.ElimGateBranches
import FX1Poly.Typed.Metatheory.SubjectReduction.HasTypeUnionCongruenceClosesGeneric
import FX1Poly.Typed.Metatheory.Validity.WfContextUnionNoConsInterval

/-! # FX1Poly/Typed/Metatheory/SubjectReduction/ElimCongruenceGate
    — SR-DSL-5: the ELIM gate inhabited by dispatch over the eleven per-generator branches

`HasTypeUnionCongruenceClosesGeneric.lean` reduced the native congruence mountain to three named gates plus the
single-step-SR self-reference (`unionCongruenceCloserOfGates`).  `ElimGateBranches.lean` shipped the eleven
per-generator branch lemmas, each proving the `UnionElimCongruenceCloses` conclusion SPECIALIZED to one eliminator
rule.  This file closes the loop: it inhabits the GENERIC `UnionElimCongruenceCloses` by case-splitting the
`elimRuleOf generator = some rule` table hit (`elimRuleOf_cases`, the eleven-way disjunction) and dispatching each
disjunct to its matching branch.

Because every branch lemma shares the IDENTICAL parameter order — `args params level0 level1 flag premisesHold
childSubjectReduction wellFormed memberEq childStep`, differing only in which concrete `ElimRule` it pins — the
dispatch is one `exact <branch> …` per row, after `rcases … ⟨rfl, rfl⟩` substitutes both `generator` and `rule`.
A `ProfileExtension` adding an eliminator row extends `elimRuleOf_cases` by one disjunct and this dispatch by one
`exact` — never a new typing arm, never new metatheory.

## Zero-axiom

`elimRuleOf_cases` (decidable `by_cases` over `DecidableEq Generator`, no `propext`) + the eleven audit-gated
branch lemmas.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.
Per-declaration audit-gated in `FX1PolyAudit/`. -/

namespace FX1Poly.Typed

open FX1Poly.Core

/-- **★ The ELIM congruence gate, inhabited.**  For ANY profile, `UnionElimCongruenceCloses` holds: an eliminator
cell whose children step re-types its reformed cell at a `Conv`-equal classifier.  Proved by dispatch — the
`elimRuleOf` table hit pins one of the eleven rows (`elimRuleOf_cases`), and each row is discharged by its
audit-gated per-generator branch (`ElimGateBranches.lean`).  This is the second of the three gates feeding
`unionCongruenceCloserOfGates`; with the formation and intro gates it yields the unconditional single-step
`UnionCongruenceCloser`. -/
theorem elimCongruenceClosesFromBranches {profile : PolyProfile} :
    UnionElimCongruenceCloses profile := by
  intro scope context generator rule args params level0 level1 flag isElim premisesHold
    usabilityHolds childSubjectReduction wellFormed reformedGenerator reformedPayload childrenBefore
    childrenAfter memberEq childStep
  rcases elimRuleOf_cases isElim with
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact appElimGateBranchCloses args params level0 level1 flag premisesHold childSubjectReduction
      wellFormed usabilityHolds memberEq childStep
  · exact pathAppElimGateBranchCloses args params level0 level1 flag premisesHold childSubjectReduction
      wellFormed (HasTypeUnion.stepPreservesDimensionalSubjectUsability_ofWfContext wellFormed)
      memberEq childStep
  · exact natElimGateBranchCloses args params level0 level1 flag premisesHold childSubjectReduction
      wellFormed usabilityHolds memberEq childStep
  · exact natRecGateBranchCloses args params level0 level1 flag premisesHold childSubjectReduction
      wellFormed usabilityHolds memberEq childStep
  · exact boolElimGateBranchCloses args params level0 level1 flag premisesHold childSubjectReduction
      wellFormed usabilityHolds memberEq childStep
  · exact optionMatchGateBranchCloses args params level0 level1 flag premisesHold childSubjectReduction
      wellFormed usabilityHolds memberEq childStep
  · exact eitherMatchGateBranchCloses args params level0 level1 flag premisesHold childSubjectReduction
      wellFormed memberEq childStep
  · exact idJGateBranchCloses args params level0 level1 flag premisesHold childSubjectReduction
      wellFormed usabilityHolds memberEq childStep
  · exact fstElimGateBranchCloses args params level0 level1 flag premisesHold childSubjectReduction
      wellFormed memberEq childStep
  · exact sndElimGateBranchCloses args params level0 level1 flag premisesHold childSubjectReduction
      wellFormed memberEq childStep
  · exact listElimGateBranchCloses args params level0 level1 flag premisesHold childSubjectReduction
      wellFormed usabilityHolds memberEq childStep

end FX1Poly.Typed
