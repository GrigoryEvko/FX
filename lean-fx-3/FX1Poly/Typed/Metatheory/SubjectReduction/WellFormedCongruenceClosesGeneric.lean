import FX1Poly.Typed.Metatheory.SubjectReduction.WellFormedSubjectReductionClosure

/-! # FX1Poly/Typed/Metatheory/SubjectReduction/WellFormedCongruenceClosesGeneric
    — the well-formed-context fuel-bounded congruence master: three named gates close the residual (SR-WF-TIEOFF)

`WellFormedSubjectReductionClosure.lean` reduced the whole single-step-SR tie-off to ONE residual gate,
`UnionCongruenceClosesBoundedWf` — re-type a `.mkGen` cell when one child steps, given the carried
`WfContextUnion` and the fuel-bounded WELL-FORMED child-SR `UnionChildSubjectReductionBelowWf`.  This file does the
six-arm induction that the shipped no-`Wf` master `HasTypeUnion.congruenceClosesGenericAuxBounded` does, but
threading the carried `WfContextUnion` and consuming `UnionChildSubjectReductionBelowWf`, so the residual collapses
to the SAME three crisp gates the shipped congruence mountain decomposes into — now in their well-formed-context
form.

The arms split exactly as in the shipped master:

  * **var / universeFormation** — vacuous by leaf-childNil (`variableCellHasNoCongruenceStep` /
    `universeCodeCellHasNoCongruenceStep`): a `variableCell` / `universeCodeCell` is `.mkGen … .childNil`, so
    `StepChildren childNil _` is impossible.  No well-formedness, no child-SR.
  * **formationRule / intro / elim** — delegate to the three well-formed-context gates
    (`UnionFormationCongruenceClosesBoundedWf` / `…Intro…` / `…Elim…`), the obligations re-embedded via
    `toUnion`, the carried `WfContextUnion` forwarded, the fuel-bounded child-SR weakened to the arm cell's size
    (`UnionChildSubjectReductionBelowWf.weakenWf`).
  * **conv** — recurse, post-composing the classifier drift through `converts.trans`.

So the SR-WF-TIEOFF residual is now exactly three well-formed-context congruence gates plus the (shipped) fuel
self-reference — the off-`emptyTypeCell` generalization of the empty-type closer, in the well-formed regime.  Each
gate's inhabitant re-threads the corresponding bounded drift machinery with the carried `WfContextUnion`, deriving
each binder child's context well-formedness from the parent's (`WfContextUnion.cons` for concrete-typed binders,
`.lockCons` for the affine interval); the function/pair-domain binder row is the open non-fibrancy residual
(`¬ Conv domainCode intervalTypeCell` for arbitrary universe-typed `domainCode`).

## Zero-axiom

`HasTypeUnion.toNativeOnly` + the six-arm `induction` (mirroring `congruenceClosesGenericAuxBounded`) + the two
shipped leaf-vacuity lemmas + `UnionChildSubjectReductionBelowWf.weakenWf` + `Conv.trans` + `toUnion`.  No `axiom`,
`sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Per-declaration audit-gated in
`FX1PolyAudit/`. -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- **Well-formed bounded gate — FORMATION.**  The formation congruence gate consuming the fuel-bounded WELL-FORMED
child-SR (`UnionChildSubjectReductionBelowWf`) — the well-formed-context twin of
`UnionFormationCongruenceClosesBounded`.  The stepping cell's children are strictly smaller than the cell, so the
bound always suffices; the carried `WfContextUnion` is what the obligation re-typing's app-chain ι closers need. -/
def UnionFormationCongruenceClosesBoundedWf (profile : PolyProfile) : Prop :=
  ∀ {scope : Nat} {context : TypingContext profile scope}
    (generator : Generator) (payload : generator.payload scope)
    (children : RawTermChildren generator.binderShifts scope)
    (rule : FormationRule) (levels : List LevelExpr) (carrier : RawTerm scope)
    (level : LevelExpr) (flag : UniverseFlag),
    formationRuleOf generator = some rule →
    (∀ obligation ∈ rule.obligations profile context children levels carrier level flag,
      HasTypeUnion profile obligation.context obligation.subject obligation.classifier) →
    (∀ obligation ∈ rule.obligations profile context children levels carrier level flag,
      obligation.context.isSubjectUsableAtModality obligation.subject obligation.modality = true) →
    UnionChildSubjectReductionBelowWf profile (RawTerm.mkGen generator payload children).size →
    WfContextUnion context →
    ∀ {reformedGenerator : Generator} {reformedPayload : reformedGenerator.payload scope}
      {childrenBefore childrenAfter : RawTermChildren reformedGenerator.binderShifts scope},
      (RawTerm.mkGen generator payload children : RawTerm scope) =
        RawTerm.mkGen reformedGenerator reformedPayload childrenBefore →
      StepChildren childrenBefore childrenAfter →
      ∃ pinned : RawTerm scope,
        HasTypeUnion profile context (RawTerm.mkGen reformedGenerator reformedPayload childrenAfter) pinned ∧
        Conv pinned (rule.outputType scope levels level flag)

/-- **Well-formed bounded gate — INTRO.**  The introducer congruence gate consuming the fuel-bounded WELL-FORMED
child-SR — the well-formed twin of `UnionIntroCongruenceClosesBounded`. -/
def UnionIntroCongruenceClosesBoundedWf (profile : PolyProfile) : Prop :=
  ∀ {scope : Nat} {context : TypingContext profile scope}
    (generator : Generator) (rule : IntroRule)
    (args : RawTermChildren rule.argShifts scope) (params : RawTermChildren rule.paramShifts scope)
    (level0 level1 : LevelExpr) (flag : UniverseFlag),
    introRuleOf generator = some rule →
    (∀ obligation ∈ rule.obligations scope context args params level0 level1 flag,
      HasTypeUnion profile obligation.context obligation.subject obligation.classifier) →
    (∀ obligation ∈ rule.obligations scope context args params level0 level1 flag,
      obligation.context.isSubjectUsableAtModality obligation.subject obligation.modality = true) →
    UnionChildSubjectReductionBelowWf profile (rule.memberCell scope args).size →
    WfContextUnion context →
    ∀ {reformedGenerator : Generator} {reformedPayload : reformedGenerator.payload scope}
      {childrenBefore childrenAfter : RawTermChildren reformedGenerator.binderShifts scope},
      rule.memberCell scope args = RawTerm.mkGen reformedGenerator reformedPayload childrenBefore →
      StepChildren childrenBefore childrenAfter →
      ∃ pinned : RawTerm scope,
        HasTypeUnion profile context (RawTerm.mkGen reformedGenerator reformedPayload childrenAfter) pinned ∧
        Conv pinned (rule.outputType scope args params)

/-- **Well-formed bounded gate — ELIM.**  The eliminator congruence gate consuming the fuel-bounded WELL-FORMED
child-SR — the well-formed twin of `UnionElimCongruenceClosesBounded`. -/
def UnionElimCongruenceClosesBoundedWf (profile : PolyProfile) : Prop :=
  ∀ {scope : Nat} {context : TypingContext profile scope}
    (generator : Generator) (rule : ElimRule)
    (args : RawTermChildren rule.argShifts scope) (params : RawTermChildren rule.paramShifts scope)
    (level0 level1 : LevelExpr) (flag : UniverseFlag),
    elimRuleOf generator = some rule →
    (∀ obligation ∈ rule.obligations scope context args params level0 level1 flag,
      HasTypeUnion profile obligation.context obligation.subject obligation.classifier) →
    UnionChildSubjectReductionBelowWf profile (rule.memberCell scope args).size →
    WfContextUnion context →
    ∀ {reformedGenerator : Generator} {reformedPayload : reformedGenerator.payload scope}
      {childrenBefore childrenAfter : RawTermChildren reformedGenerator.binderShifts scope},
      rule.memberCell scope args = RawTerm.mkGen reformedGenerator reformedPayload childrenBefore →
      StepChildren childrenBefore childrenAfter →
      ∃ pinned : RawTerm scope,
        HasTypeUnion profile context (RawTerm.mkGen reformedGenerator reformedPayload childrenAfter) pinned ∧
        Conv pinned (rule.outputType scope args params)

/-- **★ The well-formed-context fuel-bounded congruence master, from the three gates.**  Mirrors
`HasTypeUnion.congruenceClosesGenericAuxBounded`: reflect to the native judgment (`toNativeOnly`), six-arm
induction; var / universeFormation vacuous by leaf-childNil; formationRule / intro / elim delegate to their
well-formed gates after `weakenWf`; conv recurses post-composing through `converts.trans`.  The free `bound` and
the `BelowWf bound` survive the induction; the `sizeLe` auto-reverts and per-arm `weakenWf`s `BelowWf bound` down
to `BelowWf armCell.size`. -/
theorem HasTypeUnion.congruenceClosesGenericAuxBoundedWf {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    (typed : HasTypeUnion profile context subject classifier)
    (bound : Nat) (sizeLe : subject.size ≤ bound)
    (childSubjectReductionBelow : UnionChildSubjectReductionBelowWf profile bound)
    (formationGate : UnionFormationCongruenceClosesBoundedWf profile)
    (introGate : UnionIntroCongruenceClosesBoundedWf profile)
    (elimGate : UnionElimCongruenceClosesBoundedWf profile) :
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
      isFormationRule premisesHold usabilityHolds =>
      intro wellFormed _gen _payload _before _after subjectShape childStep
      replace premisesHold := fun obligation member => (premisesHold obligation member).toUnion
      exact formationGate fGenerator fPayload fChildren rule levels carrier level flag isFormationRule
        premisesHold usabilityHolds (childSubjectReductionBelow.weakenWf sizeLe) wellFormed subjectShape childStep
  | intro _iContext iGenerator rule args params level0 level1 flag isIntro _sideHolds
      premisesHold usabilityHolds =>
      intro wellFormed _gen _payload _before _after subjectShape childStep
      replace premisesHold := fun obligation member => (premisesHold obligation member).toUnion
      exact introGate iGenerator rule args params level0 level1 flag isIntro
        premisesHold usabilityHolds (childSubjectReductionBelow.weakenWf sizeLe) wellFormed subjectShape childStep
  | elim _eContext eGenerator rule args params level0 level1 flag isElim premisesHold
      _ihPremises =>
      intro wellFormed _gen _payload _before _after subjectShape childStep
      replace premisesHold := fun obligation member => (premisesHold obligation member).toUnion
      exact elimGate eGenerator rule args params level0 level1 flag isElim
        premisesHold (childSubjectReductionBelow.weakenWf sizeLe) wellFormed subjectShape childStep
  | conv _levelExpr _flag _innerTyped converts _reclassifierTyped ihTyped _ihReclassifier =>
      intro wellFormed _gen _payload _before _after subjectShape childStep
      obtain ⟨pinned, pinnedTyped, pinnedConv⟩ := ihTyped sizeLe wellFormed subjectShape childStep
      exact ⟨pinned, pinnedTyped, pinnedConv.trans converts⟩

/-- **★ The residual congruence gate, from the three well-formed gates.**  Inhabits the SR-WF-TIEOFF residual
`UnionCongruenceClosesBoundedWf` (the lone obligation `WellFormedSubjectReductionClosure` left) from the three
well-formed-context congruence gates: it is `congruenceClosesGenericAuxBoundedWf` at the caller-supplied free
bound and `BelowWf`.  So the SR-WF-TIEOFF now rests on exactly the three named well-formed gates plus the shipped
fuel self-reference. -/
theorem unionCongruenceClosesBoundedWfOfGates {profile : PolyProfile}
    (formationGate : UnionFormationCongruenceClosesBoundedWf profile)
    (introGate : UnionIntroCongruenceClosesBoundedWf profile)
    (elimGate : UnionElimCongruenceClosesBoundedWf profile) :
    UnionCongruenceClosesBoundedWf profile := by
  intro _scope _context _subject _classifier typed wellFormed bound sizeLe childSubjectReductionBelow
    _gen _payload _before _after subjectShape childStep
  exact HasTypeUnion.congruenceClosesGenericAuxBoundedWf typed bound sizeLe childSubjectReductionBelow
    formationGate introGate elimGate wellFormed subjectShape childStep

end FX1Poly.Typed
