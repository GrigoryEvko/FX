import FX1Poly.Typed.Metatheory.SubjectReduction.HasTypeUnionCongruenceClosesGeneric
import FX1Poly.Typed.Metatheory.SubjectReduction.HasTypeUnionFlatFormationCongruence
import FX1Poly.Typed.Metatheory.SubjectReduction.HasTypeUnionTermIndexedFormationCongruence
import FX1Poly.Typed.Metatheory.SubjectReduction.HasTypeUnionCumulativeFormationCongruence
import FX1Poly.Typed.Metatheory.SubjectReduction.HasTypeUnionSingleStepSubjectReduction
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

/-- **★ The FORMATION congruence gate, inhabited generically over the four formation families.**  When a
formation cell's children step, the reformed cell re-types at the SAME children-invariant `rule.outputType` (so
the gate's output `Conv` is `Conv.refl`), with the premises re-established by the family's obligation transform.
The first of the three gates `HasTypeUnion.unionCongruenceCloserOfGates` reduces `UnionCongruenceCloser` to. -/
theorem HasTypeUnion.unionFormationCongruenceClosesGate {profile : PolyProfile} :
    UnionFormationCongruenceCloses profile := by
  intro scope context generator payload children rule levels carrier level flag
    isFormationRule premisesHold childSubjectReduction wellFormed
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
  cases rule with
  | baseType baseRule =>
      refine ⟨_, ?_, Conv.refl _⟩
      refine HasTypeUnion.formationRuleOfObligations context generator payload childrenAfter
        (FormationRule.baseType baseRule) levels carrier level flag isFormationRule ?_
      intro obligation obligationMem
      cases obligationMem
  | flat flatRule =>
      refine ⟨_, ?_, Conv.refl _⟩
      refine HasTypeUnion.formationRuleOfObligations context generator payload childrenAfter
        (FormationRule.flat flatRule) levels carrier level flag isFormationRule ?_
      exact flatFormationPremisesHoldAfter context flag children childrenAfter childStep levels
        premisesHold inlineChildSubjectReduction
  | termIndexed termRule =>
      refine ⟨_, ?_, Conv.refl _⟩
      refine HasTypeUnion.formationRuleOfObligations context generator payload childrenAfter
        (FormationRule.termIndexed termRule) levels carrier level flag isFormationRule ?_
      exact termIndexedFormationPremisesHoldAfterWf context termRule carrier level flag wellFormed
        children childrenAfter childStep levels premisesHold inlineChildSubjectReduction
  | cumulative cumulativeRule =>
      refine ⟨_, ?_, Conv.refl _⟩
      refine HasTypeUnion.formationRuleOfObligations context generator payload childrenAfter
        (FormationRule.cumulative cumulativeRule) levels carrier level flag isFormationRule ?_
      exact cumulativeFormationPremisesHoldAfter context flag children childrenAfter childStep levels
        premisesHold inlineChildSubjectReduction

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
