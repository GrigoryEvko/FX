import FX1Poly.Typed.Metatheory.SubjectReduction.IntroGateBranchesBounded
import FX1Poly.Typed.Metatheory.SubjectReduction.CongruenceClosesGenericBounded

/-! # FX1Poly/Typed/Metatheory/SubjectReduction/IntroGateDispatchBounded
    — SR-WF-TIEOFF (intro third): inhabiting the FUEL-BOUNDED introducer-congruence gate

The fuel-bounded twin of `IntroGateDispatch.lean`.  It CLOSES the bounded gate `UnionIntroCongruenceClosesBounded`
(`CongruenceClosesGenericBounded.lean`, the intro third of the bounded congruence master
`HasTypeUnion.congruenceClosesGenericAuxBounded`) MODULO the one honest `pathLam` blocker: it takes the bounded
`pathLam` branch as a single explicit premise (`PathLamIntroGateBranchClosesBounded`) and dispatches all seventeen
rows of `introRuleOf_cases` to their bounded branch lemmas — the sixteen shipped ones directly, the `pathLam` row to
the premise.

The dispatch is verbatim the unbounded `HasTypeUnion.unionIntroCongruenceClosesOfPathLam`, with the universal
`childSubjectReduction` replaced by the fuel-bounded `childSubjectReductionBelow`
(`UnionChildSubjectReductionBelow profile (rule.memberCell scope args).size`, which after each row's
`introRuleOf_cases` substitution is exactly the bound the matching bounded branch demands).

So the entire INTRODUCER leg of the bounded congruence master now rests on the ONE bounded `pathLam` branch the
A1 / interval-non-fibrant lineage discharges — completing the intro third of SR-WF-TIEOFF.  Formation third is
shipped (`HasTypeUnionFormationCongruenceBoundedGate.lean`); the elim third (the open motive-multi-step
obstruction) is the remaining gate of the bounded master.

## Zero-axiom

`introRuleOf_cases` (the table enumerator) + the sixteen shipped bounded branch lemmas + the supplied bounded
`pathLam` branch.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.
Per-declaration audit-gated in `FX1PolyAudit/`. -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- **The `pathLam` introducer-congruence branch, fuel-bounded, isolated as a premise.**  The bounded twin of
`PathLamIntroGateBranchCloses`: the seventeenth introducer row's closure obligation, consuming the fuel-bounded
`UnionChildSubjectReductionBelow profile (pathLamIntroRule.memberCell scope args).size` rather than the universal
child-SR.  The A1 / interval-non-fibrant lineage discharges it, at which point the bounded intro gate becomes
unconditional. -/
def PathLamIntroGateBranchClosesBounded (profile : PolyProfile) : Prop :=
  ∀ {scope : Nat} {context : TypingContext profile scope}
    (args : RawTermChildren pathLamIntroRule.argShifts scope)
    (params : RawTermChildren pathLamIntroRule.paramShifts scope)
    (level0 level1 : LevelExpr) (flag : UniverseFlag),
    (∀ obligation ∈ pathLamIntroRule.obligations scope context args params level0 level1 flag,
      HasTypeUnion profile obligation.context obligation.subject obligation.classifier) →
    UnionChildSubjectReductionBelow profile (pathLamIntroRule.memberCell scope args).size →
    WfContextUnion context →
    ∀ {reformedGenerator : Generator} {reformedPayload : reformedGenerator.payload scope}
      {childrenBefore childrenAfter : RawTermChildren reformedGenerator.binderShifts scope},
      pathLamIntroRule.memberCell scope args = RawTerm.mkGen reformedGenerator reformedPayload childrenBefore →
      StepChildren childrenBefore childrenAfter →
      ∃ pinned : RawTerm scope,
        HasTypeUnion profile context (RawTerm.mkGen reformedGenerator reformedPayload childrenAfter) pinned ∧
        Conv pinned (pathLamIntroRule.outputType scope args params)

/-- **★ The FUEL-BOUNDED introducer-congruence gate, modulo the `pathLam` branch.**  Given the one bounded `pathLam`
branch, the bounded gate `UnionIntroCongruenceClosesBounded` holds: dispatch `introRuleOf_cases` over all seventeen
rows — the sixteen shipped bounded branch lemmas for the data constructors + `lam`, and the supplied premise for
`pathLam`.  The intro third of the bounded congruence master `HasTypeUnion.congruenceClosesGenericAuxBounded`. -/
theorem HasTypeUnion.unionIntroCongruenceClosesBoundedGate {profile : PolyProfile}
    (pathLamBranch : PathLamIntroGateBranchClosesBounded profile) :
    UnionIntroCongruenceClosesBounded profile := by
  intro scope context generator rule args params level0 level1 flag isIntro premisesHold
    childSubjectReductionBelow wellFormed reformedGenerator reformedPayload childrenBefore childrenAfter
    memberEq childStep
  rcases introRuleOf_cases isIntro with
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact boolTrueIntroGateBranchClosesBounded args params level0 level1 flag premisesHold
      childSubjectReductionBelow wellFormed memberEq childStep
  · exact boolFalseIntroGateBranchClosesBounded args params level0 level1 flag premisesHold
      childSubjectReductionBelow wellFormed memberEq childStep
  · exact unitIntroGateBranchClosesBounded args params level0 level1 flag premisesHold
      childSubjectReductionBelow wellFormed memberEq childStep
  · exact interval0IntroGateBranchClosesBounded args params level0 level1 flag premisesHold
      childSubjectReductionBelow wellFormed memberEq childStep
  · exact interval1IntroGateBranchClosesBounded args params level0 level1 flag premisesHold
      childSubjectReductionBelow wellFormed memberEq childStep
  · exact natZeroIntroGateBranchClosesBounded args params level0 level1 flag premisesHold
      childSubjectReductionBelow wellFormed memberEq childStep
  · exact lamIntroGateBranchClosesBounded args params level0 level1 flag premisesHold
      childSubjectReductionBelow wellFormed memberEq childStep
  · exact pathLamBranch args params level0 level1 flag premisesHold
      childSubjectReductionBelow wellFormed memberEq childStep
  · exact natSuccIntroGateBranchClosesBounded args params level0 level1 flag premisesHold
      childSubjectReductionBelow wellFormed memberEq childStep
  · exact listConsIntroGateBranchClosesBounded args params level0 level1 flag premisesHold
      childSubjectReductionBelow wellFormed memberEq childStep
  · exact optionSomeIntroGateBranchClosesBounded args params level0 level1 flag premisesHold
      childSubjectReductionBelow wellFormed memberEq childStep
  · exact optionNoneIntroGateBranchClosesBounded args params level0 level1 flag premisesHold
      childSubjectReductionBelow wellFormed memberEq childStep
  · exact listNilIntroGateBranchClosesBounded args params level0 level1 flag premisesHold
      childSubjectReductionBelow wellFormed memberEq childStep
  · exact eitherInlIntroGateBranchClosesBounded args params level0 level1 flag premisesHold
      childSubjectReductionBelow wellFormed memberEq childStep
  · exact eitherInrIntroGateBranchClosesBounded args params level0 level1 flag premisesHold
      childSubjectReductionBelow wellFormed memberEq childStep
  · exact pairIntroGateBranchClosesBounded args params level0 level1 flag premisesHold
      childSubjectReductionBelow wellFormed memberEq childStep
  · exact reflIntroGateBranchClosesBounded args params level0 level1 flag premisesHold
      childSubjectReductionBelow wellFormed memberEq childStep

end FX1Poly.Typed
