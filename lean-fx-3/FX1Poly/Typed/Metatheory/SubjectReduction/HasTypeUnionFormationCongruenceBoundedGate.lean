import FX1Poly.Typed.Metatheory.SubjectReduction.HasTypeUnionFormationCongruenceGate
import FX1Poly.Typed.Metatheory.SubjectReduction.FormationBoundedChildSubjectReduction
import FX1Poly.Typed.Metatheory.SubjectReduction.CongruenceClosesGenericBounded

/-! # FX1Poly/Typed/Metatheory/SubjectReduction/HasTypeUnionFormationCongruenceBoundedGate
    — the FORMATION congruence gate, FUEL-BOUNDED variant (SR-WF-TIEOFF, formation third)

`HasTypeUnionFormationCongruenceGate.lean` inhabits the formation congruence gate `UnionFormationCongruenceCloses`
from the UNIVERSAL `UnionChildSubjectReduction` self-reference.  The SR-WF-TIEOFF well-founded recursion only
supplies single-step SR for terms STRICTLY SMALLER than the stepping cell, so the master
`HasTypeUnion.congruenceClosesGenericAuxBounded` consumes the FUEL-BOUNDED gate `UnionFormationCongruenceClosesBounded`
(`CongruenceClosesGenericBounded.lean`) instead — keyed on `UnionChildSubjectReductionBelow profile cell.size`.

This file ships that bounded gate, and it is a near-verbatim mirror of the unbounded
`HasTypeUnion.unionFormationCongruenceClosesGate`: the SAME four-family dispatch (`baseType` / `flat` /
`termIndexed` / `cumulative`), each routing through the SAME already-shipped family obligation-transform.  The ONLY
difference is the source of the inline per-obligation child-SR the transforms consume: instead of building it
inline from the universal `UnionChildSubjectReduction`, it is sourced from the fuel-bounded predicate through the
shipped bridge `formationGateInlineChildSubjectReductionOfBelow` (every formation obligation's subject is a
structural child, so `subject.size < children.size < cell.size` — exactly the bound the fuel-bounded predicate
demands).  Because the unification of the cumulative arm onto the inline per-obligation form
(`HasTypeUnionCumulativeFormationCongruence.lean`) made ALL FOUR families consume that one inline form, the bridge
is a single drop-in here and the gate closes uniformly.

## Why the output `Conv` is `refl`

Identical to the unbounded gate: every formation former's OUTPUT type `rule.outputType scope levels level flag` is
CHILDREN-INVARIANT, so the reformed cell re-types at the SAME classifier and the gate's `Conv` obligation is
`Conv.refl`.  All the work is re-establishing the PREMISES at the stepped children — the four family transforms.

## Zero-axiom verification

The shipped unbounded family transforms + `HasTypeUnion.formationRuleOfObligations` (the rebuild primitive) +
`formationGateInlineChildSubjectReductionOfBelow` (the fuel-bounded bridge) + `injection` on the `mkGen` subject
equation + `Conv.refl`.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.
Per-declaration audit-gated in `FX1PolyAudit/`. -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- **★ The FORMATION congruence gate, FUEL-BOUNDED.**  The fuel-bounded twin of
`HasTypeUnion.unionFormationCongruenceClosesGate`: when a formation cell's children step, the reformed cell
re-types at the SAME children-invariant `rule.outputType` (so the output `Conv` is `Conv.refl`), with the premises
re-established by the family's obligation transform — the inline per-obligation child-SR now sourced from the
fuel-bounded `UnionChildSubjectReductionBelow profile cell.size` through the bridge
`formationGateInlineChildSubjectReductionOfBelow`.  The formation third of the bounded-gate master
`HasTypeUnion.congruenceClosesGenericAuxBounded`. -/
theorem HasTypeUnion.unionFormationCongruenceClosesBoundedGate {profile : PolyProfile} :
    UnionFormationCongruenceClosesBounded profile := by
  intro scope context generator payload children rule levels carrier level flag
    isFormationRule premisesHold childSubjectReductionBelow wellFormed
    reformedGenerator reformedPayload childrenBefore childrenAfter subjectShape childStep
  -- The reformed cell IS the original cell: recover `reformedGenerator = generator`,
  -- `reformedPayload = payload`, `childrenBefore = children` from the `mkGen` injection.
  injection subjectShape with scopeEq genEq payloadEq childrenEq
  subst genEq
  cases eq_of_heq payloadEq
  cases eq_of_heq childrenEq
  -- The inline per-obligation child-SR, sourced from the FUEL-BOUNDED predicate via the shipped bridge
  -- (every formation obligation's subject is a structural child, strictly smaller than the cell).
  have inlineChildSubjectReduction :=
    formationGateInlineChildSubjectReductionOfBelow generator payload children rule levels carrier level flag
      premisesHold childSubjectReductionBelow
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

end FX1Poly.Typed
