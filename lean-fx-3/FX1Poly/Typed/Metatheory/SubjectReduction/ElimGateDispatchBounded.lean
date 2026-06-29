import FX1Poly.Typed.Metatheory.SubjectReduction.ElimGateBranchesBounded
import FX1Poly.Typed.Metatheory.SubjectReduction.CongruenceClosesGenericBounded

/-! # FX1Poly/Typed/Metatheory/SubjectReduction/ElimGateDispatchBounded
    — SR-WF-TIEOFF (elim third): inhabiting the FUEL-BOUNDED eliminator-congruence gate

The fuel-bounded twin of `ElimCongruenceGate.lean`.  It CLOSES the bounded gate `UnionElimCongruenceClosesBounded`
(`CongruenceClosesGenericBounded.lean`, the elim third of the bounded congruence master
`HasTypeUnion.congruenceClosesGenericAuxBounded`) MODULO three honest residuals.  Dispatch `elimRuleOf_cases` over
all eleven rows; the bounded branches (`ElimGateBranchesBounded.lean`) discharge seven of them, the remaining four
rest on explicit premises.

## The three residuals (why the bounded elim gate cannot be unconditional yet)

Unlike the bounded INTRO gate, `UnionElimCongruenceClosesBounded` carries NO before-step usability premise:
`congruenceClosesGenericAuxBounded` does not forward the native `elim` arm's `usabilityHolds` to the gate.  So the
after-args usability the bounded reassembly demands splits the rows:

  * **`fst` / `snd`** — every obligation classifier is rigid (`≢ interval`), so usability discharges from the
    re-typed obligations alone.  These rows are UNCONDITIONAL.
  * **`app` / `boolElim` / `natElim` / `natRec`** — a branch obligation reads the motive / an arbitrary param, so
    usability is not derivable from typing; the bounded branch threads the before-step usability forward.  That
    before-usability is the honest residual `ElimObligationsBeforeUsable` (exactly the `usabilityHolds` the master
    drops).
  * **`pathApp`** — the interval argument is consumed at the `.dimensional` modality, whose usability is the
    use-site statement of interval non-fibrancy; supplied by the honest residual
    `argumentDimensionalUsable`.

The four dependent-match rows whose fuel-bounded `ObligationsDriftBelow` builder is not yet shipped (`optionMatch` /
`eitherMatch` / `idJ` / `listElim`) rest on per-row branch premises (`ElimRowCongruenceClosesBounded`), exactly as
`IntroGateDispatchBounded` leaves its one `pathLam` row.

So the entire ELIMINATOR leg of the bounded congruence master now rests on these named residuals; the seven
shipped-drift rows are proven.  Formation third is shipped (`HasTypeUnionFormationCongruenceBoundedGate`); the intro
third is shipped modulo its `pathLam` row (`IntroGateDispatchBounded`).

## Zero-axiom

`elimRuleOf_cases` (the table enumerator) + the seven shipped bounded branch lemmas + the supplied residuals.  No
`axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Per-declaration audit-gated in
`FX1PolyAudit/`. -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- **The before-step usability the bounded elim gate's signature drops.**  The native `elim` arm's `usabilityHolds`
that `congruenceClosesGenericAuxBounded` does not forward to the gate, threaded back as an explicit premise: for any
eliminator rule whose obligations are union-typed in a well-formed context, those obligation subjects are usable at
their modality.  The honest residual the step-preservation rows (`app` / `boolElim` / `natElim` / `natRec`) consume —
exactly as the unbounded `elimCongruenceClosesFromBranches` consumes the gate's `usabilityHolds`. -/
def ElimObligationsBeforeUsable (profile : PolyProfile) : Prop :=
  ∀ {scope : Nat} {context : TypingContext profile scope} (rule : ElimRule)
    {args : RawTermChildren rule.argShifts scope} {params : RawTermChildren rule.paramShifts scope}
    {level0 level1 : LevelExpr} {flag : UniverseFlag},
    (∀ obligation ∈ rule.obligations scope context args params level0 level1 flag,
      HasTypeUnion profile obligation.context obligation.subject obligation.classifier) →
    WfContextUnion context →
    ∀ obligation ∈ rule.obligations scope context args params level0 level1 flag,
      obligation.context.isSubjectUsableAtModality obligation.subject obligation.modality = true

/-- **A single eliminator row's fuel-bounded congruence closure, isolated as a premise.**  The bounded gate
conclusion SPECIALIZED to one `ElimRule` — the per-row residual for the dependent-match eliminators whose
fuel-bounded `ObligationsDriftBelow` builder is not yet shipped (`optionMatch` / `eitherMatch` / `idJ` /
`listElim`).  The elim analogue of `IntroGateDispatchBounded`'s one `pathLam` row premise. -/
def ElimRowCongruenceClosesBounded (profile : PolyProfile) (rule : ElimRule) : Prop :=
  ∀ {scope : Nat} {context : TypingContext profile scope}
    (args : RawTermChildren rule.argShifts scope) (params : RawTermChildren rule.paramShifts scope)
    (level0 level1 : LevelExpr) (flag : UniverseFlag),
    (∀ obligation ∈ rule.obligations scope context args params level0 level1 flag,
      HasTypeUnion profile obligation.context obligation.subject obligation.classifier) →
    UnionChildSubjectReductionBelow profile (rule.memberCell scope args).size →
    WfContextUnion context →
    ∀ {reformedGenerator : Generator} {reformedPayload : reformedGenerator.payload scope}
      {childrenBefore childrenAfter : RawTermChildren reformedGenerator.binderShifts scope},
      rule.memberCell scope args = RawTerm.mkGen reformedGenerator reformedPayload childrenBefore →
      StepChildren childrenBefore childrenAfter →
      ∃ pinned : RawTerm scope,
        HasTypeUnion profile context (RawTerm.mkGen reformedGenerator reformedPayload childrenAfter) pinned ∧
        Conv pinned (rule.outputType scope args params)

/-- **★ The FUEL-BOUNDED eliminator-congruence gate, modulo three honest residuals.**  Given the before-step
usability the master drops (`ElimObligationsBeforeUsable`), the `.dimensional` interval-argument residual
(`argumentDimensionalUsable`), and the four not-yet-drift-shipped dependent-match rows as per-row premises, the
bounded gate `UnionElimCongruenceClosesBounded` holds: dispatch `elimRuleOf_cases` over all eleven rows — `fst` /
`snd` unconditionally, `app` / `boolElim` / `natElim` / `natRec` via the before-usability residual, `pathApp` via
the dimensional residual, and `optionMatch` / `eitherMatch` / `idJ` / `listElim` via their per-row premises.  The
elim third of the bounded congruence master `HasTypeUnion.congruenceClosesGenericAuxBounded`. -/
theorem HasTypeUnion.unionElimCongruenceClosesBoundedGate {profile : PolyProfile}
    (elimObligationsBeforeUsable : ElimObligationsBeforeUsable profile)
    (argumentDimensionalUsable : ∀ {scope : Nat} {context : TypingContext profile scope} {subject : RawTerm scope},
      HasTypeUnion profile context subject intervalTypeCell →
        context.isSubjectUsableAtModality subject ObligationModality.dimensional = true)
    (optionMatchRow : ElimRowCongruenceClosesBounded profile optionMatchElimRule)
    (eitherMatchRow : ElimRowCongruenceClosesBounded profile eitherMatchElimRule)
    (idJRow : ElimRowCongruenceClosesBounded profile idJElimRule)
    (listElimRow : ElimRowCongruenceClosesBounded profile listElimRule) :
    UnionElimCongruenceClosesBounded profile := by
  intro scope context generator rule args params level0 level1 flag isElim premisesHold
    childSubjectReductionBelow wellFormed reformedGenerator reformedPayload childrenBefore
    childrenAfter memberEq childStep
  rcases elimRuleOf_cases isElim with
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact appElimGateBranchClosesBounded args params level0 level1 flag premisesHold
      childSubjectReductionBelow wellFormed (elimObligationsBeforeUsable appElimRule premisesHold wellFormed)
      memberEq childStep
  · exact pathAppElimGateBranchClosesBounded args params level0 level1 flag premisesHold
      childSubjectReductionBelow wellFormed (fun typed => argumentDimensionalUsable typed) memberEq childStep
  · exact natElimGateBranchClosesBounded args params level0 level1 flag premisesHold
      childSubjectReductionBelow wellFormed (elimObligationsBeforeUsable natElimRule premisesHold wellFormed)
      memberEq childStep
  · exact natRecGateBranchClosesBounded args params level0 level1 flag premisesHold
      childSubjectReductionBelow wellFormed (elimObligationsBeforeUsable natRecElimRule premisesHold wellFormed)
      memberEq childStep
  · exact boolElimGateBranchClosesBounded args params level0 level1 flag premisesHold
      childSubjectReductionBelow wellFormed (elimObligationsBeforeUsable boolElimRule premisesHold wellFormed)
      memberEq childStep
  · exact optionMatchRow args params level0 level1 flag premisesHold childSubjectReductionBelow wellFormed
      memberEq childStep
  · exact eitherMatchRow args params level0 level1 flag premisesHold childSubjectReductionBelow wellFormed
      memberEq childStep
  · exact idJRow args params level0 level1 flag premisesHold childSubjectReductionBelow wellFormed
      memberEq childStep
  · exact fstElimGateBranchClosesBounded args params level0 level1 flag premisesHold
      childSubjectReductionBelow wellFormed memberEq childStep
  · exact sndElimGateBranchClosesBounded args params level0 level1 flag premisesHold
      childSubjectReductionBelow wellFormed memberEq childStep
  · exact listElimRow args params level0 level1 flag premisesHold childSubjectReductionBelow wellFormed
      memberEq childStep

end FX1Poly.Typed
