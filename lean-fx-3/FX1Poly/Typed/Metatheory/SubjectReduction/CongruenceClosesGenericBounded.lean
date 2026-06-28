import FX1Poly.Typed.Metatheory.SubjectReduction.HasTypeUnionCongruenceClosesGeneric
import FX1Poly.Typed.Metatheory.SubjectReduction.UnionChildSubjectReductionBounded

/-! # FX1Poly/Typed/Metatheory/SubjectReduction/CongruenceClosesGenericBounded
    — the FUEL-BOUNDED congruence master: three bounded gates ⟹ congruence closure (SR-WF-TIEOFF step 4)

`HasTypeUnionCongruenceClosesGeneric.lean` reduces the native congruence mountain to three gates that each consume
the UNIVERSAL `UnionChildSubjectReduction`.  But the SR full arc discharges that self-reference by STRUCTURAL-FUEL
recursion on subject size (`WellFounded.fix` leaks propext here) — and a fuel IH only supplies single-step SR for
terms STRICTLY SMALLER than the stepping cell, never the full universal.  This file re-expresses the master to
consume the fuel-BOUNDED child-SR (`UnionChildSubjectReductionBelow`), so the eventual fuel induction can feed its
IH directly.

## The bound-threading design (the induction-generalization crux)

`congruenceClosesGenericAux` inducts on the typing derivation, and the ONLY cell it reforms is the (top) subject —
so the gates only ever need child-SR below `subject.size`.  But a hypothesis `Below subject.size` would mention
`subject` (an index of the inducted derivation) and get mangled by `induction`.  The fix: carry a FREE bound
`bound : Nat` with `subject.size ≤ bound` and `UnionChildSubjectReductionBelow profile bound`.  The free `bound`
and the `Below bound` survive `induction` untouched; the `sizeLe : subject.size ≤ bound` auto-reverts (it depends
on the index `subject`) and reappears per-arm as `armCell.size ≤ bound`; each bounded gate then receives
`Below armCell.size` via `UnionChildSubjectReductionBelow.weaken sizeLeArm childSubjectReductionBelow`.

The three bounded gates (`UnionFormationCongruenceClosesBounded` / `…Intro…` / `…Elim…`) are the existing gates
with `UnionChildSubjectReduction profile` swapped for `UnionChildSubjectReductionBelow profile (cell).size` — the
child-SR fuel-bounded by the stepping cell's own size.  Inhabiting them is the next step (formation via
`formationGateInlineChildSubjectReductionOfBelow`; elim/intro via the per-branch stepped-child size at each
`cases childStep` leaf — every child-SR application is on a STEPPED CELL-CHILD, structurally smaller, never on a
type param).

## Zero-axiom

`HasTypeUnion.toNativeOnly` + a six-arm `induction` (mirroring `congruenceClosesGenericAux`: var/universeFormation
vacuous by leaf-childNil; formation/intro/elim delegate to the bounded gates after `weaken`; conv recurses) +
`UnionChildSubjectReductionBelow.weaken` + `Conv.trans` + `toUnion`.  No `axiom`, `sorry`, `propext`, `Quot.sound`,
`Classical`, `native_decide`, `omega`.  Per-declaration audit-gated in `FX1PolyAudit/`. -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- **Bounded gate — FORMATION.**  The formation congruence gate, consuming the FUEL-BOUNDED child-SR
(`Below (mkGen generator payload children).size`) instead of the universal `UnionChildSubjectReduction`.  The
stepping cell's children are strictly smaller than the cell, so the bound always suffices. -/
def UnionFormationCongruenceClosesBounded (profile : PolyProfile) : Prop :=
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
    UnionChildSubjectReductionBelow profile (RawTerm.mkGen generator payload children).size →
    WfContextUnion context →
    ∀ {reformedGenerator : Generator} {reformedPayload : reformedGenerator.payload scope}
      {childrenBefore childrenAfter : RawTermChildren reformedGenerator.binderShifts scope},
      (RawTerm.mkGen generator payload children : RawTerm scope) =
        RawTerm.mkGen reformedGenerator reformedPayload childrenBefore →
      StepChildren childrenBefore childrenAfter →
      ∃ pinned : RawTerm scope,
        HasTypeUnion profile context (RawTerm.mkGen reformedGenerator reformedPayload childrenAfter) pinned ∧
        Conv pinned (rule.outputType scope levels level flag)

/-- **Bounded gate — INTRO.**  The intro congruence gate, consuming `Below (rule.memberCell scope args).size`. -/
def UnionIntroCongruenceClosesBounded (profile : PolyProfile) : Prop :=
  ∀ {scope : Nat} {context : TypingContext profile scope}
    (generator : Generator) (rule : IntroRule)
    (args : RawTermChildren rule.argShifts scope) (params : RawTermChildren rule.paramShifts scope)
    (level0 level1 : LevelExpr) (flag : UniverseFlag),
    introRuleOf generator = some rule →
    (∀ obligation ∈ rule.obligations scope context args params level0 level1 flag,
      HasTypeUnion profile obligation.context obligation.subject obligation.classifier) →
    (∀ obligation ∈ rule.obligations scope context args params level0 level1 flag,
      obligation.context.isSubjectUsableAtModality obligation.subject obligation.modality = true) →
    UnionChildSubjectReductionBelow profile (rule.memberCell scope args).size →
    WfContextUnion context →
    ∀ {reformedGenerator : Generator} {reformedPayload : reformedGenerator.payload scope}
      {childrenBefore childrenAfter : RawTermChildren reformedGenerator.binderShifts scope},
      rule.memberCell scope args = RawTerm.mkGen reformedGenerator reformedPayload childrenBefore →
      StepChildren childrenBefore childrenAfter →
      ∃ pinned : RawTerm scope,
        HasTypeUnion profile context (RawTerm.mkGen reformedGenerator reformedPayload childrenAfter) pinned ∧
        Conv pinned (rule.outputType scope args params)

/-- **Bounded gate — ELIM.**  The elim congruence gate, consuming `Below (rule.memberCell scope args).size`. -/
def UnionElimCongruenceClosesBounded (profile : PolyProfile) : Prop :=
  ∀ {scope : Nat} {context : TypingContext profile scope}
    (generator : Generator) (rule : ElimRule)
    (args : RawTermChildren rule.argShifts scope) (params : RawTermChildren rule.paramShifts scope)
    (level0 level1 : LevelExpr) (flag : UniverseFlag),
    elimRuleOf generator = some rule →
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

/-- **★ The fuel-bounded congruence master.**  A union typing of a `.mkGen` cell whose children step re-types at a
`Conv`-equal classifier — given a free fuel `bound` dominating the subject's size, the fuel-bounded child-SR at
that bound, and the three BOUNDED congruence gates.  Mirrors `congruenceClosesGenericAux`: the free `bound` and
`Below bound` survive the six-arm `induction`; the `sizeLe` auto-reverts and per-arm `weaken`s `Below bound` down
to `Below armCell.size` for the gate. -/
theorem HasTypeUnion.congruenceClosesGenericAuxBounded {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    (typed : HasTypeUnion profile context subject classifier)
    (bound : Nat) (sizeLe : subject.size ≤ bound)
    (childSubjectReductionBelow : UnionChildSubjectReductionBelow profile bound)
    (formationGate : UnionFormationCongruenceClosesBounded profile)
    (introGate : UnionIntroCongruenceClosesBounded profile)
    (elimGate : UnionElimCongruenceClosesBounded profile) :
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
        premisesHold usabilityHolds (childSubjectReductionBelow.weaken sizeLe) wellFormed subjectShape childStep
  | intro _iContext iGenerator rule args params level0 level1 flag isIntro _sideHolds
      premisesHold usabilityHolds =>
      intro wellFormed _gen _payload _before _after subjectShape childStep
      replace premisesHold := fun obligation member => (premisesHold obligation member).toUnion
      exact introGate iGenerator rule args params level0 level1 flag isIntro
        premisesHold usabilityHolds (childSubjectReductionBelow.weaken sizeLe) wellFormed subjectShape childStep
  | elim _eContext eGenerator rule args params level0 level1 flag isElim premisesHold
      _ihPremises =>
      intro wellFormed _gen _payload _before _after subjectShape childStep
      replace premisesHold := fun obligation member => (premisesHold obligation member).toUnion
      exact elimGate eGenerator rule args params level0 level1 flag isElim
        premisesHold (childSubjectReductionBelow.weaken sizeLe) wellFormed subjectShape childStep
  | conv _levelExpr _flag _innerTyped converts _reclassifierTyped ihTyped _ihReclassifier =>
      intro wellFormed _gen _payload _before _after subjectShape childStep
      obtain ⟨pinned, pinnedTyped, pinnedConv⟩ := ihTyped sizeLe wellFormed subjectShape childStep
      exact ⟨pinned, pinnedTyped, pinnedConv.trans converts⟩

end FX1Poly.Typed
