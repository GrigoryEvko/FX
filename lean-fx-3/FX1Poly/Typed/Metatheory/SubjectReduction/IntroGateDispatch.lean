import FX1Poly.Typed.Metatheory.SubjectReduction.IntroGateBranches

/-! # FX1Poly/Typed/Metatheory/SubjectReduction/IntroGateDispatch
    — SR-DSL-5: inhabiting the introducer-congruence gate by dispatch over the intro table

`IntroGateBranches.lean` ships the per-generator branch lemmas for SIXTEEN of the seventeen introducer rows
(the eight nullary data constructors, the six recursive/grown data constructors, `refl`, and `lam`); the
seventeenth, `pathLam`, is blocked by the interval-fibrancy obstruction (the staged interval-non-fibrant arc).
This file CLOSES the gate `UnionIntroCongruenceCloses` MODULO exactly that one honest blocker: it takes the
`pathLam` branch as a single explicit premise (`PathLamIntroGateBranchCloses`) and dispatches all seventeen rows
of `introRuleOf_cases` to their branch lemmas — the sixteen shipped ones directly, the `pathLam` row to the
premise.

So the entire INTRODUCER leg of the native congruence mountain (`UnionIntroCongruenceCloses`, one of the three
gates `HasTypeUnion.unionCongruenceCloserOfGates` reduces the congruence closer to) now rests on the ONE
`pathLam` branch the A1 / interval-non-fibrant lineage discharges; nothing else in the intro arm remains open.
The dispatch follows the row ORDER of `introRuleOf_cases` (not the source order of the branch file).

## Zero-axiom

`introRuleOf_cases` (the `by_cases` table enumerator) + the sixteen shipped branch lemmas + the supplied
`pathLam` branch.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.
Per-declaration audit-gated in `FX1PolyAudit/`. -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- **The `pathLam` introducer-congruence branch, isolated as a premise.**  The seventeenth introducer row's
closure obligation on its own: when a `pathLam` cell `pathLamIntroRule.memberCell scope args` (typed at its
`outputType`) is a `.mkGen` whose children step, the reformed cell re-types at a `Conv`-equal classifier.
Mirrors the shipped `lamIntroGateBranchCloses` shape at `pathLamIntroRule`; the A1 / interval-non-fibrant
lineage discharges it, at which point the intro gate becomes unconditional. -/
def PathLamIntroGateBranchCloses (profile : PolyProfile) : Prop :=
  ∀ {scope : Nat} {context : TypingContext profile scope}
    (args : RawTermChildren pathLamIntroRule.argShifts scope)
    (params : RawTermChildren pathLamIntroRule.paramShifts scope)
    (level0 level1 : LevelExpr) (flag : UniverseFlag),
    (∀ obligation ∈ pathLamIntroRule.obligations scope context args params level0 level1 flag,
      HasTypeUnion profile obligation.context obligation.subject obligation.classifier) →
    UnionChildSubjectReduction profile →
    WfContextUnion context →
    ∀ {reformedGenerator : Generator} {reformedPayload : reformedGenerator.payload scope}
      {childrenBefore childrenAfter : RawTermChildren reformedGenerator.binderShifts scope},
      pathLamIntroRule.memberCell scope args = RawTerm.mkGen reformedGenerator reformedPayload childrenBefore →
      StepChildren childrenBefore childrenAfter →
      ∃ pinned : RawTerm scope,
        HasTypeUnion profile context (RawTerm.mkGen reformedGenerator reformedPayload childrenAfter) pinned ∧
        Conv pinned (pathLamIntroRule.outputType scope args params)

/-- **★ The introducer-congruence gate, modulo the `pathLam` branch.**  Given the one `pathLam` branch, the
gate `UnionIntroCongruenceCloses` holds: dispatch `introRuleOf_cases` over all seventeen rows — the sixteen
shipped branch lemmas for the data constructors + `lam`, and the supplied premise for `pathLam`.  The whole
intro leg of the native congruence mountain is now this single honest obligation. -/
theorem HasTypeUnion.unionIntroCongruenceClosesOfPathLam {profile : PolyProfile}
    (pathLamBranch : PathLamIntroGateBranchCloses profile) :
    UnionIntroCongruenceCloses profile := by
  intro scope context generator rule args params level0 level1 flag isIntro premisesHold
    childSubjectReduction wellFormed reformedGenerator reformedPayload childrenBefore childrenAfter
    memberEq childStep
  rcases introRuleOf_cases isIntro with
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact boolTrueIntroGateBranchCloses args params level0 level1 flag premisesHold
      childSubjectReduction wellFormed memberEq childStep
  · exact boolFalseIntroGateBranchCloses args params level0 level1 flag premisesHold
      childSubjectReduction wellFormed memberEq childStep
  · exact unitIntroGateBranchCloses args params level0 level1 flag premisesHold
      childSubjectReduction wellFormed memberEq childStep
  · exact interval0IntroGateBranchCloses args params level0 level1 flag premisesHold
      childSubjectReduction wellFormed memberEq childStep
  · exact interval1IntroGateBranchCloses args params level0 level1 flag premisesHold
      childSubjectReduction wellFormed memberEq childStep
  · exact natZeroIntroGateBranchCloses args params level0 level1 flag premisesHold
      childSubjectReduction wellFormed memberEq childStep
  · exact lamIntroGateBranchCloses args params level0 level1 flag premisesHold
      childSubjectReduction wellFormed memberEq childStep
  · exact pathLamBranch args params level0 level1 flag premisesHold
      childSubjectReduction wellFormed memberEq childStep
  · exact natSuccIntroGateBranchCloses args params level0 level1 flag premisesHold
      childSubjectReduction wellFormed memberEq childStep
  · exact listConsIntroGateBranchCloses args params level0 level1 flag premisesHold
      childSubjectReduction wellFormed memberEq childStep
  · exact optionSomeIntroGateBranchCloses args params level0 level1 flag premisesHold
      childSubjectReduction wellFormed memberEq childStep
  · exact optionNoneIntroGateBranchCloses args params level0 level1 flag premisesHold
      childSubjectReduction wellFormed memberEq childStep
  · exact listNilIntroGateBranchCloses args params level0 level1 flag premisesHold
      childSubjectReduction wellFormed memberEq childStep
  · exact eitherInlIntroGateBranchCloses args params level0 level1 flag premisesHold
      childSubjectReduction wellFormed memberEq childStep
  · exact eitherInrIntroGateBranchCloses args params level0 level1 flag premisesHold
      childSubjectReduction wellFormed memberEq childStep
  · exact pairIntroGateBranchCloses args params level0 level1 flag premisesHold
      childSubjectReduction wellFormed memberEq childStep
  · exact reflIntroGateBranchCloses args params level0 level1 flag premisesHold
      childSubjectReduction wellFormed memberEq childStep

end FX1Poly.Typed
