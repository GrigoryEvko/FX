import FX1Poly.Typed.Metatheory.SubjectReduction.HasTypeUnionCongruenceClosesGeneric
import FX1Poly.Typed.Metatheory.SubjectReduction.HasTypeUnionFlatFormationCongruence
import FX1Poly.Typed.Metatheory.SubjectReduction.HasTypeUnionTermIndexedFormationCongruence
import FX1Poly.Typed.Metatheory.SubjectReduction.HasTypeUnionCumulativeFormationCongruence
import FX1Poly.Typed.Metatheory.SubjectReduction.HasTypeUnionSingleStepSubjectReduction
import FX1Poly.Typed.Metatheory.SubjectReduction.UsabilityHoldsUnderObligationsDrift
import FX1Poly.Typed.Engine.Union.HasTypeUnionFormationObligations

/-! # FX1Poly/Typed/Metatheory/SubjectReduction/HasTypeUnionFormationCongruenceGate
    — the FORMATION congruence gate inhabitant (SR-DSL-5, 1 of 3 gates)

`HasTypeUnionCongruenceClosesGeneric.lean` reduces the native congruence mountain `UnionCongruenceCloser` to
THREE named gates plus the well-founded single-step-SR self-reference.  This file INHABITS the first — the
formation gate `UnionFormationCongruenceCloses` — generically over the formation table's FOUR families, with
ZERO per-generator case analysis: it `cases` the `FormationRule` into `baseType` / `flat` / `termIndexed` /
`cumulative` and routes each to its already-shipped obligation-transform.  Adding a future formation former
(W-types, quotients) that fits an existing family needs NO new gate proof — the transform is generic over the
children spine.

## Why the output `Conv` is `refl`

Every formation former's OUTPUT type is CHILDREN-INVARIANT — `rule.outputType scope levels level flag` reads
only the levels / flag, never the children (a `productTypeCell A B : Type@e` keeps its universe when `A` / `B`
step).  So the reformed cell re-types at the SAME `rule.outputType` and the gate's `Conv pinned (rule.outputType
…)` obligation is `Conv.refl`.  All the work is re-establishing the PREMISES at the stepped children — exactly
what the four family transforms do.

## The four family routes

  * **`baseType`** — childless: `rule.obligations = []` unconditionally, so the after-premises hold vacuously
    (`cases obligationMem`).  (A base type's `children` is `childNil`, so the child step is even impossible — but
    the empty obligation list discharges the premise without needing that.)
  * **`flat`** — `flatFormationPremisesHoldAfter`: each flat child at its universe code, the stepped child
    re-typed + reclassified, siblings unchanged.
  * **`termIndexed`** — `termIndexedFormationPremisesHoldAfterWf`: the carrier-at-universe head + endpoints at the
    fixed carrier, the carrier-is-type witness derived LOCALLY from the stepping endpoint's own obligation via the
    `WfContextUnion` the gate carries (no separate carrier hypothesis — future-proof for 0-endpoint formers).
  * **`cumulative`** — `cumulativeFormationPremisesHoldAfter`: the Π/Σ binder-crossing codomain via native context
    conversion when the domain steps + the List/Option element step.

## Zero-axiom verification

The four shipped family transforms (each zero-axiom) + `HasTypeUnion.formationRuleOfObligations` (the rebuild
primitive) + `injection` on the `mkGen` subject equation + `Conv.refl`.  No `axiom`, `sorry`, `propext`,
`Quot.sound`, `Classical`, `native_decide`, `omega`.  Per-declaration audit-gated in `FX1PolyAudit/`. -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-! ## (0) The A1-CONJUNCT-WIRE usability discharge kit for the formation families (local to this file)

The rebuilt formation cell now demands, alongside the typing obligations, the matching fibrant-usability
obligations (`obligation.context.isSubjectUsableAtModality obligation.subject obligation.modality = true`,
modality `.fibrant` for every formation row).  EVERY formation obligation's CLASSIFIER is a universe code
(`flat` / `cumulative` children at their universe codes, the `termIndexed` carrier at its universe code), so the
after-typed obligation's subject is fibrantly usable by the shared bridge
`typedAtUniverseImpliesFibrantlyUsable_ofLocksInterval` over the interval-lock discipline `WfContextUnion`
supplies (`allLocksAreInterval`).  Two spine helpers (`flat` / `cumulative`) discharge the variable-length
obligation lists by mirroring the lock-free usability dischargers (`flatFormationObligations_usableOfLockFree`
/ `cumulativeFormationObligations_usableOfLockFree`), with the lock-free leaf replaced by the universe bridge
on the supplied after-premise typing — so the gate is interval-lock-discipline-conditioned, NOT lock-free. -/

/-- **Flat-family obligation usability from the after-typings.**  Every flat obligation is an ambient-context
child at a universe code; the after-premise types it there, so the universe bridge over `AllLocksAreInterval`
makes it fibrantly usable.  Spine recursion on `binderShifts`, mirroring
`flatFormationObligations_usableOfLockFree`. -/
theorem flatFormationObligationsUsable_ofAfterTyped {profile : PolyProfile} {scope : Nat}
    (context : TypingContext profile scope) (locksInterval : context.AllLocksAreInterval)
    (flag : UniverseFlag) :
    ∀ {binderShifts : List Nat} (children : RawTermChildren binderShifts scope) (levels : List LevelExpr),
      (∀ obligation ∈ flatFormationObligations profile context flag children levels,
        HasTypeUnion profile obligation.context obligation.subject obligation.classifier) →
      ∀ targetObligation ∈ flatFormationObligations profile context flag children levels,
        targetObligation.context.isSubjectUsableAtModality targetObligation.subject
          targetObligation.modality = true := by
  intro binderShifts
  induction binderShifts with
  | nil =>
      intro children levels _premisesAfter targetObligation targetMember
      cases children
      cases targetMember
  | cons headShift restShifts ih =>
      intro children levels premisesAfter targetObligation targetMember
      cases children with
      | childCons childHead childTail =>
          cases headShift with
          | zero =>
              cases levels with
              | nil =>
                  cases targetMember with
                  | head =>
                      exact typedAtUniverseImpliesFibrantlyUsable_ofLocksInterval locksInterval
                        (premisesAfter _ (List.Mem.head _))
                  | tail _ tailMember =>
                      exact ih childTail [] (fun o om => premisesAfter o (List.Mem.tail _ om))
                        targetObligation tailMember
              | cons headLevel restLevels =>
                  cases targetMember with
                  | head =>
                      exact typedAtUniverseImpliesFibrantlyUsable_ofLocksInterval locksInterval
                        (premisesAfter _ (List.Mem.head _))
                  | tail _ tailMember =>
                      exact ih childTail restLevels (fun o om => premisesAfter o (List.Mem.tail _ om))
                        targetObligation tailMember
          | succ _ => cases targetMember

/-- **Cumulative-family obligation usability from the after-typings.**  The element / domain obligation is an
ambient-context child at a universe code; the Π / Σ binder-crossing codomain is at `context.cons domain` at a
universe code.  Both reclassify to fibrantly usable via the universe bridge — the codomain over the
`cons`-extended interval-lock discipline.  Same spine dispatch as
`cumulativeFormationObligations_usableOfLockFree`. -/
theorem cumulativeFormationObligationsUsable_ofAfterTyped {profile : PolyProfile} {scope : Nat}
    (context : TypingContext profile scope) (locksInterval : context.AllLocksAreInterval)
    (flag : UniverseFlag) :
    ∀ {binderShifts : List Nat} (children : RawTermChildren binderShifts scope) (levels : List LevelExpr),
      (∀ obligation ∈ cumulativeFormationObligations profile context flag children levels,
        HasTypeUnion profile obligation.context obligation.subject obligation.classifier) →
      ∀ targetObligation ∈ cumulativeFormationObligations profile context flag children levels,
        targetObligation.context.isSubjectUsableAtModality targetObligation.subject
          targetObligation.modality = true := by
  intro binderShifts children levels premisesAfter targetObligation targetMember
  match binderShifts, children, levels with
  | _, .childNil, _ => cases targetMember
  | _, .childCons (shift := 0) headChild .childNil, [] =>
      cases targetMember with
      | head =>
          exact typedAtUniverseImpliesFibrantlyUsable_ofLocksInterval locksInterval
            (premisesAfter _ (List.Mem.head _))
      | tail _ tailMember => cases tailMember
  | _, .childCons (shift := 0) headChild .childNil, _elementLevel :: _ =>
      cases targetMember with
      | head =>
          exact typedAtUniverseImpliesFibrantlyUsable_ofLocksInterval locksInterval
            (premisesAfter _ (List.Mem.head _))
      | tail _ tailMember => cases tailMember
  | _, .childCons (shift := 0) domain (.childCons (shift := 1) codomain .childNil),
      _domainLevel :: _codomainLevel :: _ =>
      cases targetMember with
      | head =>
          exact typedAtUniverseImpliesFibrantlyUsable_ofLocksInterval locksInterval
            (premisesAfter _ (List.Mem.head _))
      | tail _ tailMember =>
          cases tailMember with
          | head =>
              exact typedAtUniverseImpliesFibrantlyUsable_ofLocksInterval
                (TypingContext.AllLocksAreInterval.cons locksInterval)
                (premisesAfter _ (List.Mem.tail _ (List.Mem.head _)))
          | tail _ deeperMember => cases deeperMember
  | _, .childCons (shift := 0) domain (.childCons (shift := 1) codomain .childNil), [] =>
      cases targetMember with
      | head =>
          exact typedAtUniverseImpliesFibrantlyUsable_ofLocksInterval locksInterval
            (premisesAfter _ (List.Mem.head _))
      | tail _ tailMember =>
          cases tailMember with
          | head =>
              exact typedAtUniverseImpliesFibrantlyUsable_ofLocksInterval
                (TypingContext.AllLocksAreInterval.cons locksInterval)
                (premisesAfter _ (List.Mem.tail _ (List.Mem.head _)))
          | tail _ deeperMember => cases deeperMember
  | _, .childCons (shift := 0) domain (.childCons (shift := 1) codomain .childNil), [_] =>
      cases targetMember with
      | head =>
          exact typedAtUniverseImpliesFibrantlyUsable_ofLocksInterval locksInterval
            (premisesAfter _ (List.Mem.head _))
      | tail _ tailMember =>
          cases tailMember with
          | head =>
              exact typedAtUniverseImpliesFibrantlyUsable_ofLocksInterval
                (TypingContext.AllLocksAreInterval.cons locksInterval)
                (premisesAfter _ (List.Mem.tail _ (List.Mem.head _)))
          | tail _ deeperMember => cases deeperMember
  | _, .childCons (shift := 0) _ (.childCons (shift := 1) _ (.childCons _ _)), _ => cases targetMember
  | _, .childCons (shift := 0) _ (.childCons (shift := 0) _ _), _ => cases targetMember
  | _, .childCons (shift := 0) _ (.childCons (shift := _ + 2) _ _), _ => cases targetMember
  | _, .childCons (shift := _ + 1) _ _, _ => cases targetMember

/-! ## (0b) The term-indexed ENDPOINT usability discharge (the genuine #1829 HARD CASE, threaded)

`baseType` / `flat` / `cumulative` obligations — and the term-indexed CARRIER obligation — are all children at
universe codes, so the after-typing makes each fibrantly usable via the universe bridge (above).  The term-indexed
ENDPOINTS (`Id A a b` / `Bridge A a b`'s `a` / `b`) are typed at the ARBITRARY carrier `A`, NOT a universe code.
When `A` is (convertible to) the affine `intervalTypeCell`, an endpoint can be a `lockCons`-bound DIMENSION
VARIABLE — `.dimensional`-accessible (hence typeable at `A`, so it satisfies the gate's `premisesHold` TYPING
premise) yet NOT `.fibrant`-usable (`isFibrantlyAccessibleAt` is `false` at a `lockCons`-0 position).  So the
endpoints' fibrant usability is NOT derivable from their typing alone — it is threaded from the formation cell's own
`usabilityHolds` (the native `HasTypeUnionNativeOnly.formationRule` arm's field, now carried through the
`UnionFormationCongruenceCloses` gate) and transported across the child step by the SHIPPED unconditional
single-step `HasTypeUnion.stepPreservesFibrantSubjectUsability` — the stepped endpoint preserved, every sibling
unchanged.  This is the formation analogue of `elimGateRowReassemble`'s `usabilityAfter`, DISCHARGED (not a
residual). -/

/-- **Term-indexed ENDPOINT obligation usability after a child congruence, from the BEFORE usability.**  The
usability twin of `termIndexedEndpointObligationsHoldAfterWf`: every endpoint obligation (subject at the FIXED
`carrier`, modality `.fibrant`) is usable after the step — the stepped endpoint by the unconditional single-step
`HasTypeUnion.stepPreservesFibrantSubjectUsability` (fed its before-typing + before-usability), every sibling
unchanged.  Spine-length recursion on `shifts`, mirroring the typing transform. -/
theorem termIndexedEndpointObligationsUsableAfterWf {profile : PolyProfile} {scope : Nat}
    (context : TypingContext profile scope) (carrier : RawTerm scope) :
    ∀ {shifts : List Nat} (childrenBefore childrenAfter : RawTermChildren shifts scope),
      StepChildren childrenBefore childrenAfter →
        (∀ obligation ∈ termIndexedEndpointObligations profile context carrier childrenBefore,
          HasTypeUnion profile obligation.context obligation.subject obligation.classifier) →
        (∀ obligation ∈ termIndexedEndpointObligations profile context carrier childrenBefore,
          obligation.context.isSubjectUsableAtModality obligation.subject obligation.modality = true) →
        ∀ obligation ∈ termIndexedEndpointObligations profile context carrier childrenAfter,
          obligation.context.isSubjectUsableAtModality obligation.subject obligation.modality = true := by
  intro shifts
  induction shifts with
  | nil =>
      intro childrenBefore childrenAfter childStep _premisesHold _usabilityHolds obligation obligationMem
      cases childrenBefore
      exact (StepStar.noStepChildren_childNil childStep).elim
  | cons childShift restShifts restIH =>
      cases childShift with
      | succ _childShiftPredecessor =>
          intro childrenBefore childrenAfter childStep _premisesHold _usabilityHolds obligation obligationMem
          cases childrenBefore with
          | childCons head rest =>
              cases childStep with
              | @here _ _ _ _ _headAfter _restSame _childStepHead => cases obligationMem
              | @there _ _ _ _ _ _restAfter _restStep => cases obligationMem
      | zero =>
          intro childrenBefore childrenAfter childStep premisesHold usabilityHolds obligation obligationMem
          cases childrenBefore with
          | childCons head rest =>
              cases childStep with
              | @here _ _ _ _ headAfter restSame childStepHead =>
                  cases obligationMem with
                  | head =>
                      exact HasTypeUnion.stepPreservesFibrantSubjectUsability
                        (premisesHold
                          { scope := scope, context := context, subject := head, classifier := carrier }
                          (List.Mem.head _)) childStepHead
                        (usabilityHolds
                          { scope := scope, context := context, subject := head, classifier := carrier }
                          (List.Mem.head _))
                  | tail _ tailMem => exact usabilityHolds _ (List.Mem.tail _ tailMem)
              | @there _ _ _ _ _ restAfter restStep =>
                  cases obligationMem with
                  | head => exact usabilityHolds _ (List.Mem.head _)
                  | tail _ tailMem =>
                      exact restIH rest restAfter restStep
                        (fun o om => premisesHold o (List.Mem.tail _ om))
                        (fun o om => usabilityHolds o (List.Mem.tail _ om)) _ tailMem

/-- **★ The `WfContextUnion`-driven term-indexed FULL formation-obligation usability transform.**  The usability
twin of `termIndexedFormationPremisesHoldAfterWf`: the carrier-at-universe HEAD obligation is fibrantly usable from
the after-typing via the universe bridge over `AllLocksAreInterval`; the endpoint TAIL is transported from the
BEFORE usability (threaded from the cell's `usabilityHolds`) through `termIndexedEndpointObligationsUsableAfterWf`.
A child step touches either the carrier (head re-typed, endpoints unchanged) or an endpoint (head unchanged,
endpoints transported). -/
theorem termIndexedFormationObligationsUsableAfterWf {profile : PolyProfile} {scope : Nat}
    (context : TypingContext profile scope) (termRule : TermIndexedFormerDesc)
    (carrier : RawTerm scope) (level : LevelExpr) (flag : UniverseFlag)
    (locksInterval : context.AllLocksAreInterval)
    {binderShifts : List Nat} (childrenBefore childrenAfter : RawTermChildren binderShifts scope)
    (childStep : StepChildren childrenBefore childrenAfter) (levels : List LevelExpr)
    (premisesHold : ∀ obligation ∈ (FormationRule.termIndexed termRule).obligations profile context
        childrenBefore levels carrier level flag,
      HasTypeUnion profile obligation.context obligation.subject obligation.classifier)
    (usabilityHolds : ∀ obligation ∈ (FormationRule.termIndexed termRule).obligations profile context
        childrenBefore levels carrier level flag,
      obligation.context.isSubjectUsableAtModality obligation.subject obligation.modality = true)
    (premisesAfter : ∀ obligation ∈ (FormationRule.termIndexed termRule).obligations profile context
        childrenAfter levels carrier level flag,
      HasTypeUnion profile obligation.context obligation.subject obligation.classifier) :
    ∀ obligation ∈ (FormationRule.termIndexed termRule).obligations profile context childrenAfter
        levels carrier level flag,
      obligation.context.isSubjectUsableAtModality obligation.subject obligation.modality = true := by
  intro obligation obligationMem
  cases childrenBefore with
  | childNil => exact (StepStar.noStepChildren_childNil childStep).elim
  | childCons head rest =>
      rename_i carrierShift _restShifts
      cases carrierShift with
      | succ _carrierShiftPredecessor =>
          cases childStep with
          | @here _ _ _ _ _headAfter _restSame _childStepHead => cases obligationMem
          | @there _ _ _ _ _ _restAfter _restStep => cases obligationMem
      | zero =>
          cases childStep with
          | @here _ _ _ _ headAfter restSame childStepHead =>
              cases obligationMem with
              | head =>
                  exact typedAtUniverseImpliesFibrantlyUsable_ofLocksInterval locksInterval
                    (premisesAfter _ (List.Mem.head _))
              | tail _ tailMem => exact usabilityHolds _ (List.Mem.tail _ tailMem)
          | @there _ _ _ _ _ restAfter restStep =>
              cases obligationMem with
              | head =>
                  exact typedAtUniverseImpliesFibrantlyUsable_ofLocksInterval locksInterval
                    (premisesAfter _ (List.Mem.head _))
              | tail _ tailMem =>
                  exact termIndexedEndpointObligationsUsableAfterWf context carrier
                    rest restAfter restStep
                    (fun o om => premisesHold o (List.Mem.tail _ om))
                    (fun o om => usabilityHolds o (List.Mem.tail _ om)) _ tailMem

/-- **★ The FORMATION congruence gate, inhabited generically over the four formation families.**  When a
formation cell's children step, the reformed cell re-types at the SAME children-invariant `rule.outputType` (so
the gate's output `Conv` is `Conv.refl`), with the premises re-established by the family's obligation transform.
The first of the three gates `HasTypeUnion.unionCongruenceCloserOfGates` reduces `UnionCongruenceCloser` to.

★ A1-CONJUNCT-WIRE (#1829): the rebuilt cell now also demands its obligation subjects' fibrant USABILITY.  Three
families (`baseType` / `flat` / `cumulative`) and the term-indexed CARRIER discharge it unconditionally from the
after-typings (every such obligation is a child at a universe code — `flatFormationObligationsUsable_ofAfterTyped`
/ `cumulativeFormationObligationsUsable_ofAfterTyped` over the interval-lock discipline).  The term-indexed
ENDPOINTS (at the arbitrary carrier, possibly the affine interval) are the genuine HARD CASE — their usability is
THREADED from the formation cell's own `usabilityHolds` (the native `HasTypeUnionNativeOnly.formationRule` field,
now carried through the `UnionFormationCongruenceCloses` gate) and transported across the child step by
`termIndexedFormationObligationsUsableAfterWf` (single-step preservation), the formation analogue of
`elimGateRowReassemble`'s `usabilityAfter`, DISCHARGED rather than left a residual. -/
theorem HasTypeUnion.unionFormationCongruenceClosesGate {profile : PolyProfile} :
    UnionFormationCongruenceCloses profile := by
  intro scope context generator payload children rule levels carrier level flag
    isFormationRule premisesHold usabilityHolds childSubjectReduction wellFormed
    reformedGenerator reformedPayload childrenBefore childrenAfter subjectShape childStep
  -- The reformed cell IS the original cell: recover `reformedGenerator = generator`,
  -- `reformedPayload = payload`, `childrenBefore = children` from the `mkGen` injection.
  injection subjectShape with scopeEq genEq payloadEq childrenEq
  subst genEq
  cases eq_of_heq payloadEq
  cases eq_of_heq childrenEq
  -- The single-step-SR self-reference, in the INLINE per-obligation form the flat / term-indexed transforms take.
  have inlineChildSubjectReduction :
      ∀ obligation ∈ rule.obligations profile context children levels carrier level flag,
        ∀ reduct : RawTerm obligation.scope, Step obligation.subject reduct →
          ∃ pinned : RawTerm obligation.scope,
            HasTypeUnion profile obligation.context reduct pinned ∧ Conv pinned obligation.classifier :=
    fun obligation obligationMem reduct stepReduct =>
      have ⟨reductType, reductTyped, classifierConv⟩ :=
        childSubjectReduction (premisesHold obligation obligationMem) stepReduct
      ⟨reductType, reductTyped, classifierConv.sym⟩
  have locksInterval : context.AllLocksAreInterval :=
    WfContextUnion.allLocksAreInterval context wellFormed
  cases rule with
  | baseType baseRule =>
      refine ⟨_, ?_, Conv.refl _⟩
      refine HasTypeUnion.formationRuleOfObligations context generator payload childrenAfter
        (FormationRule.baseType baseRule) levels carrier level flag isFormationRule ?_ ?_
      · intro obligation obligationMem
        cases obligationMem
      · intro obligation obligationMem
        cases obligationMem
  | flat flatRule =>
      refine ⟨_, ?_, Conv.refl _⟩
      have premisesAfter := flatFormationPremisesHoldAfter context flag children childrenAfter childStep
        levels premisesHold inlineChildSubjectReduction
      exact HasTypeUnion.formationRuleOfObligations context generator payload childrenAfter
        (FormationRule.flat flatRule) levels carrier level flag isFormationRule premisesAfter
        (flatFormationObligationsUsable_ofAfterTyped context locksInterval flag childrenAfter levels
          premisesAfter)
  | termIndexed termRule =>
      refine ⟨_, ?_, Conv.refl _⟩
      have premisesAfter := termIndexedFormationPremisesHoldAfterWf context termRule carrier level flag
        wellFormed children childrenAfter childStep levels premisesHold inlineChildSubjectReduction
      exact HasTypeUnion.formationRuleOfObligations context generator payload childrenAfter
        (FormationRule.termIndexed termRule) levels carrier level flag isFormationRule premisesAfter
        (termIndexedFormationObligationsUsableAfterWf context termRule carrier level flag locksInterval
          children childrenAfter childStep levels premisesHold usabilityHolds premisesAfter)
  | cumulative cumulativeRule =>
      refine ⟨_, ?_, Conv.refl _⟩
      have premisesAfter := cumulativeFormationPremisesHoldAfter context flag children childrenAfter
        childStep levels premisesHold inlineChildSubjectReduction
      exact HasTypeUnion.formationRuleOfObligations context generator payload childrenAfter
        (FormationRule.cumulative cumulativeRule) levels carrier level flag isFormationRule premisesAfter
        (cumulativeFormationObligationsUsable_ofAfterTyped context locksInterval flag childrenAfter levels
          premisesAfter)

/-- **★ Single-step union subject reduction, modulo the INTRO + ELIM gates + the single-step-SR self-reference.**
The formation gate (`unionFormationCongruenceClosesGate`) is now DISCHARGED into the single-step SR master: this
states the residual reached after closing the formation third of the native congruence mountain.  What remains is
exactly the two non-formation gates (`UnionIntroCongruenceCloses` / `UnionElimCongruenceCloses`) plus the
well-founded `UnionChildSubjectReduction` self-reference — the precise frontier of the SR full arc with the
formation third landed table-generically. -/
theorem HasTypeUnion.singleStepSubjectReductionModuloIntroElimGates {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject reduct classifier : RawTerm scope}
    (typed : HasTypeUnion profile context subject classifier)
    (wellFormed : WfContextUnion context)
    (childSubjectReduction : UnionChildSubjectReduction profile)
    (introGate : UnionIntroCongruenceCloses profile)
    (elimGate : UnionElimCongruenceCloses profile)
    (step : Step subject reduct) :
    ∃ pinned : RawTerm scope,
      HasTypeUnion profile context reduct pinned ∧ Conv pinned classifier :=
  HasTypeUnion.singleStepSubjectReductionUpToCongruence typed wellFormed
    (HasTypeUnion.unionCongruenceCloserOfGates wellFormed childSubjectReduction
      HasTypeUnion.unionFormationCongruenceClosesGate introGate elimGate) step

end FX1Poly.Typed
