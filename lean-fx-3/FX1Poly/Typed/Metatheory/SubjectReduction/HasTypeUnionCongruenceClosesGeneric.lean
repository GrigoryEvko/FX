import FX1Poly.Typed.Metatheory.SubjectReduction.HasTypeUnionEmptyTypeCongruenceCloser
import FX1Poly.Typed.Metatheory.Validity.HasTypeUnionValidity

/-! # FX1Poly/Typed/Metatheory/SubjectReduction/HasTypeUnionCongruenceClosesGeneric
    — the OFF-EMPTYTYPE generic congruence master: `UnionCongruenceCloser` ⟸ three named gates (SR-DSL-5 skeleton)

`HasTypeUnionEmptyTypeCongruenceCloser.lean` ships `congruenceClosesToEmptyTypeAux` — the congruence closer
SPECIALIZED to the classifier `emptyTypeCell`, where FOUR of the six native arms collapse VACUOUSLY (var /
universeFormation / formationRule / intro all refute, because nothing reaches `emptyTypeCell`), leaving only the
`elim` arm and the recursing `conv` arm.

This file **generalizes that off `emptyTypeCell` to an ARBITRARY classifier** — the SR-DSL-5 structural keystone.
Off the empty type the four refuting arms split two ways:

  * **var / universeFormation** stay vacuous — but now by *leaf-childNil* (a `variableCell` / `universeCodeCell`
    is `.mkGen … .childNil`, so `StepChildren childNil _` is impossible), via the SHIPPED
    `variableCellHasNoCongruenceStep` / `universeCodeCellHasNoCongruenceStep`.  No closedness, no `emptyTypeCell`
    rigidity — these arms are unconditionally vacuous.
  * **formationRule / intro / elim** can no longer refute (the classifier is arbitrary, not `emptyTypeCell`): they
    must RE-TYPE the reformed cell.  Each becomes a named congruence GATE — `UnionFormationCongruenceCloses` /
    `UnionIntroCongruenceCloses` / `UnionElimCongruenceCloses` — exactly mirroring how the empty-type closer
    isolated the single `UnionElimCongruenceClosesToEmptyType` gate.

The `conv` arm recurses, post-composing the drift through `converts.trans`.  So the GENERIC `UnionCongruenceCloser`
(the residual of `singleStepSubjectReductionUpToCongruence`) reduces to THREE crisp gates plus the
single-step-SR self-reference `UnionChildSubjectReduction` (the `childSubjectReduction` premise the per-eliminator
motive arms — e.g. `natElimMotiveCongruenceSubjectReduction` — already take): the full native mountain is now
three named obligations, not one monolith.

## Why `childSubjectReduction` is a premise, not the induction IH

The outer induction on the typing derivation supplies, for each obligation sub-derivation, the CONGRUENCE-closure
property (a top-level child of the obligation steps) — NOT full single-step subject reduction (the obligation
subject itself fires a root redex).  Re-typing a stepped child needs the latter.  So the gates (and this master)
take `UnionChildSubjectReduction` — the "single-step SR holds for every sub-derivation" property — as a premise,
discharged later by the well-founded recursion that ties single-step SR to its own congruence case.

## Zero-axiom verification

`HasTypeUnion.toNativeOnly` (reflect to the ofGrown-free judgment) + a six-arm `induction` + the two shipped
leaf-vacuity lemmas + `Conv.trans` + `HasTypeUnionNativeOnly.toUnion` (re-embed the obligations for the gates).
No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Per-declaration audit-gated
in `FX1PolyAudit/`. -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- **The single-step subject-reduction self-reference.**  "Single-step SR holds for every sub-derivation": any
union-typed term, stepped once, re-types at a `Conv`-equal classifier.  This is the `childSubjectReduction`
premise the per-eliminator congruence motive arms already take (`natElimMotiveCongruenceSubjectReduction`); the
congruence gates consume it to re-type a stepped child, and the eventual well-founded recursion discharges it from
the strictly-smaller IH. -/
def UnionChildSubjectReduction (profile : PolyProfile) : Prop :=
  ∀ {scope : Nat} {context : TypingContext profile scope} {subterm reduct subtermType : RawTerm scope},
    HasTypeUnion profile context subterm subtermType → Step subterm reduct →
      ∃ reductType : RawTerm scope,
        HasTypeUnion profile context reduct reductType ∧ Conv subtermType reductType

/-- **Gate — the FORMATION-arm congruence closer (generic classifier).**  When a formation cell `.mkGen generator
payload children` (typed at `rule.outputType scope levels level flag`) is a `.mkGen` whose children step, the
reformed cell re-types at a `Conv`-equal classifier — given the union-typed obligations and the single-step-SR
self-reference.  The off-`emptyTypeCell` successor of the empty closer's (there vacuous) `formationRule` arm. -/
def UnionFormationCongruenceCloses (profile : PolyProfile) : Prop :=
  ∀ {scope : Nat} {context : TypingContext profile scope}
    (generator : Generator) (payload : generator.payload scope)
    (children : RawTermChildren generator.binderShifts scope)
    (rule : FormationRule) (levels : List LevelExpr) (carrier : RawTerm scope)
    (level : LevelExpr) (flag : UniverseFlag),
    formationRuleOf generator = some rule →
    (∀ obligation ∈ rule.obligations profile context children levels carrier level flag,
      HasTypeUnion profile obligation.context obligation.subject obligation.classifier) →
    UnionChildSubjectReduction profile →
    WfContextUnion context →
    ∀ {reformedGenerator : Generator} {reformedPayload : reformedGenerator.payload scope}
      {childrenBefore childrenAfter : RawTermChildren reformedGenerator.binderShifts scope},
      (RawTerm.mkGen generator payload children : RawTerm scope) =
        RawTerm.mkGen reformedGenerator reformedPayload childrenBefore →
      StepChildren childrenBefore childrenAfter →
      ∃ pinned : RawTerm scope,
        HasTypeUnion profile context (RawTerm.mkGen reformedGenerator reformedPayload childrenAfter) pinned ∧
        Conv pinned (rule.outputType scope levels level flag)

/-- **Gate — the INTRO-arm congruence closer (generic classifier).**  When an introducer cell `rule.memberCell
scope args` (typed at `rule.outputType scope args params`) is a `.mkGen` whose children step, the reformed cell
re-types at a `Conv`-equal classifier — given the union-typed obligations and the single-step-SR self-reference.
The off-`emptyTypeCell` successor of the empty closer's (there refuted) `intro` arm. -/
def UnionIntroCongruenceCloses (profile : PolyProfile) : Prop :=
  ∀ {scope : Nat} {context : TypingContext profile scope}
    (generator : Generator) (rule : IntroRule)
    (args : RawTermChildren rule.argShifts scope) (params : RawTermChildren rule.paramShifts scope)
    (level0 level1 : LevelExpr) (flag : UniverseFlag),
    introRuleOf generator = some rule →
    (∀ obligation ∈ rule.obligations scope context args params level0 level1 flag,
      HasTypeUnion profile obligation.context obligation.subject obligation.classifier) →
    UnionChildSubjectReduction profile →
    WfContextUnion context →
    ∀ {reformedGenerator : Generator} {reformedPayload : reformedGenerator.payload scope}
      {childrenBefore childrenAfter : RawTermChildren reformedGenerator.binderShifts scope},
      rule.memberCell scope args = RawTerm.mkGen reformedGenerator reformedPayload childrenBefore →
      StepChildren childrenBefore childrenAfter →
      ∃ pinned : RawTerm scope,
        HasTypeUnion profile context (RawTerm.mkGen reformedGenerator reformedPayload childrenAfter) pinned ∧
        Conv pinned (rule.outputType scope args params)

/-- **Gate — the ELIM-arm congruence closer (generic classifier).**  When an eliminator cell `rule.memberCell
scope args` (typed at `rule.outputType scope args params`) is a `.mkGen` whose children step, the reformed cell
re-types at a `Conv`-equal classifier — given the union-typed obligations and the single-step-SR self-reference.
The off-`emptyTypeCell`, output-drifting successor of `UnionElimCongruenceClosesToEmptyType` (the empty closer's
ONE surviving gate).  The per-row motive arms (`natElimMotiveCongruenceSubjectReduction`, …) inhabit this. -/
def UnionElimCongruenceCloses (profile : PolyProfile) : Prop :=
  ∀ {scope : Nat} {context : TypingContext profile scope}
    (generator : Generator) (rule : ElimRule)
    (args : RawTermChildren rule.argShifts scope) (params : RawTermChildren rule.paramShifts scope)
    (level0 level1 : LevelExpr) (flag : UniverseFlag),
    elimRuleOf generator = some rule →
    (∀ obligation ∈ rule.obligations scope context args params level0 level1 flag,
      HasTypeUnion profile obligation.context obligation.subject obligation.classifier) →
    UnionChildSubjectReduction profile →
    WfContextUnion context →
    ∀ {reformedGenerator : Generator} {reformedPayload : reformedGenerator.payload scope}
      {childrenBefore childrenAfter : RawTermChildren reformedGenerator.binderShifts scope},
      rule.memberCell scope args = RawTerm.mkGen reformedGenerator reformedPayload childrenBefore →
      StepChildren childrenBefore childrenAfter →
      ∃ pinned : RawTerm scope,
        HasTypeUnion profile context (RawTerm.mkGen reformedGenerator reformedPayload childrenAfter) pinned ∧
        Conv pinned (rule.outputType scope args params)

/-- **★ The off-`emptyTypeCell` generic congruence master (the context-threaded core).**  A union typing of a
`.mkGen` cell whose children step re-types at a `Conv`-equal classifier — given the single-step-SR self-reference
and the three congruence gates.  Reflected to the native judgment (`toNativeOnly`) and inducted over all six
native arms: `var` / `universeFormation` are vacuous by leaf-childNil; `formationRule` / `intro` / `elim` delegate
to their gates (obligations re-embedded via `toUnion`); `conv` recurses, post-composing the drift through
`converts.trans`.  Stated over a free `subject` / `classifier` with a `subject = .mkGen …` pin, so the
`UnionCongruenceCloser` shape is the `rfl`-pin specialization (`unionCongruenceCloserOfGates`). -/
theorem HasTypeUnion.congruenceClosesGenericAux {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    (typed : HasTypeUnion profile context subject classifier)
    (childSubjectReduction : UnionChildSubjectReduction profile)
    (formationGate : UnionFormationCongruenceCloses profile)
    (introGate : UnionIntroCongruenceCloses profile)
    (elimGate : UnionElimCongruenceCloses profile) :
    WfContextUnion context →
    ∀ {gen : Generator} {payload : gen.payload scope}
      {before after : RawTermChildren gen.binderShifts scope},
      subject = RawTerm.mkGen gen payload before →
      StepChildren before after →
      ∃ pinned : RawTerm scope,
        HasTypeUnion profile context (RawTerm.mkGen gen payload after) pinned ∧
        Conv pinned classifier := by
  have nativeTyped := typed.toNativeOnly
  clear typed
  induction nativeTyped with
  | var _context index =>
      intro _wellFormed _gen _payload _before _after subjectShape childStep
      exact (variableCellHasNoCongruenceStep subjectShape childStep).elim
  | universeFormation _context _levelExpr _flag =>
      intro _wellFormed _gen _payload _before _after subjectShape childStep
      exact (universeCodeCellHasNoCongruenceStep subjectShape childStep).elim
  | formationRule _fContext fGenerator fPayload fChildren rule levels carrier level flag
      isFormationRule premisesHold _ihPremises =>
      intro wellFormed _gen _payload _before _after subjectShape childStep
      replace premisesHold := fun obligation member => (premisesHold obligation member).toUnion
      exact formationGate fGenerator fPayload fChildren rule levels carrier level flag isFormationRule
        premisesHold childSubjectReduction wellFormed subjectShape childStep
  | intro _iContext iGenerator rule args params level0 level1 flag isIntro _sideHolds
      premisesHold _ihPremises =>
      intro wellFormed _gen _payload _before _after subjectShape childStep
      replace premisesHold := fun obligation member => (premisesHold obligation member).toUnion
      exact introGate iGenerator rule args params level0 level1 flag isIntro
        premisesHold childSubjectReduction wellFormed subjectShape childStep
  | elim _eContext eGenerator rule args params level0 level1 flag isElim premisesHold
      _ihPremises =>
      intro wellFormed _gen _payload _before _after subjectShape childStep
      replace premisesHold := fun obligation member => (premisesHold obligation member).toUnion
      exact elimGate eGenerator rule args params level0 level1 flag isElim
        premisesHold childSubjectReduction wellFormed subjectShape childStep
  | conv _levelExpr _flag _innerTyped converts _reclassifierTyped ihTyped _ihReclassifier =>
      intro wellFormed _gen _payload _before _after subjectShape childStep
      obtain ⟨pinned, pinnedTyped, pinnedConv⟩ := ihTyped wellFormed subjectShape childStep
      exact ⟨pinned, pinnedTyped, pinnedConv.trans converts⟩

/-- **★ The generic `UnionCongruenceCloser` from the three gates.**  For ANY context and classifier, the
congruence closer (the residual of `singleStepSubjectReductionUpToCongruence`) is inhabited given the single-step
SR self-reference and the formation / intro / elim congruence gates.  The `UnionCongruenceCloser` shape is
`congruenceClosesGenericAux` at the `rfl` subject-pin.  So the native congruence mountain is now exactly three
named obligations plus the well-founded self-reference — the off-`emptyTypeCell` generalization of
`congruenceClosesToEmptyTypeModuloElim`. -/
theorem HasTypeUnion.unionCongruenceCloserOfGates {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {classifier : RawTerm scope}
    (wellFormed : WfContextUnion context)
    (childSubjectReduction : UnionChildSubjectReduction profile)
    (formationGate : UnionFormationCongruenceCloses profile)
    (introGate : UnionIntroCongruenceCloses profile)
    (elimGate : UnionElimCongruenceCloses profile) :
    UnionCongruenceCloser profile context classifier := by
  intro _generator _payload _childrenBefore _childrenAfter typed childStep
  exact HasTypeUnion.congruenceClosesGenericAux typed childSubjectReduction formationGate introGate
    elimGate wellFormed rfl childStep

end FX1Poly.Typed
