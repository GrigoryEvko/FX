import FX1Poly.Typed.Engine.Union.HasTypeUnion
import FX1Poly.Typed.Engine.RuleTables.FormationRuleTable
import FX1Poly.Typed.Metatheory.SubjectReduction.HasTypeUnionEmptyTypeCongruenceCloser

/-! # FX1Poly/Typed/Metatheory/SubjectReduction/HasTypeUnionTermIndexedFormationCongruence
    — the TERM-INDEXED endpoint obligation transform under a child congruence (gate-2, formationRule arm, Id/Bridge)

The term-indexed formers `Id A a b` / `Bridge A a b` have obligation list `[carrier : Type@level] ++
termIndexedEndpointObligations carrier [a, b]` — a carrier-at-universe head obligation, then every ENDPOINT typed
at the FIXED `carrier`.  This file ships the endpoint-obligation transform, the term-indexed analogue of
`flatFormationPremisesHoldAfter`: when an endpoint steps, re-type it at `carrier` through its subject reduction +
a `carrier`-is-type reclassification.

Unlike the cumulative Π/Σ codomain obligation (which lives in the binder-extended context `context.cons domain`,
so a domain step shifts a SIBLING obligation's context and needs native context conversion — not yet shipped), the
term-indexed endpoints all sit at the SAME ambient context classified by the SAME fixed `carrier`, so the transform
is binder-free: a child congruence touches exactly one endpoint's subject and every sibling obligation is unchanged.
(The carrier-head obligation is handled separately by the flat-style universe reclassification when assembling the
full term-indexed arm; this file is the endpoint tail.)

## The recursion: on `shifts`, not on the mutual inductives

As with `flatFormationPremisesHoldAfter`, both `StepChildren` (mutual with `Step`) and `RawTermChildren` (mutual with
`RawTerm`) reject `induction`; the recursion driver is the spine length `shifts : List Nat` + one-level `cases` on
the children / `childStep`.

## Zero-axiom verification

`shifts` `induction` + one-level `cases` + `reclassifyToType` over the `carrier`-is-type premise, threading the
membership premises by `List.Mem.head` / `List.Mem.tail`.  No `axiom`, `sorry`, `propext`, `Quot.sound`,
`Classical`, `native_decide`, `omega`.  Per-declaration audit-gated in `FX1PolyAudit/`. -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- **The term-indexed endpoint obligation transform under a child congruence.**  Given the endpoint obligations at
`childrenBefore` all hold (each endpoint at the fixed `carrier`), each enjoys subject reduction (the master's IH),
and `carrier` is a type, a child step re-establishes every endpoint obligation at `childrenAfter` — the stepped
endpoint re-typed at `carrier` through its SR + reclassification, every sibling unchanged.  Spine-length recursion
(`shifts`). -/
theorem termIndexedEndpointObligationsHoldAfter {profile : PolyProfile} {scope : Nat}
    (context : TypingContext profile scope) (carrier : RawTerm scope)
    (carrierIsType : UnionClassifierIsType profile context carrier) :
    ∀ {shifts : List Nat} (childrenBefore childrenAfter : RawTermChildren shifts scope),
      StepChildren childrenBefore childrenAfter →
        (∀ obligation ∈ termIndexedEndpointObligations profile context carrier childrenBefore,
          HasTypeUnion profile obligation.context obligation.subject obligation.classifier) →
        (∀ obligation ∈ termIndexedEndpointObligations profile context carrier childrenBefore,
          ∀ reduct : RawTerm obligation.scope, Step obligation.subject reduct →
            ∃ pinned : RawTerm obligation.scope,
              HasTypeUnion profile obligation.context reduct pinned ∧ Conv pinned obligation.classifier) →
        ∀ obligation ∈ termIndexedEndpointObligations profile context carrier childrenAfter,
          HasTypeUnion profile obligation.context obligation.subject obligation.classifier := by
  intro shifts
  induction shifts with
  | nil =>
      intro childrenBefore childrenAfter childStep _premisesHold _childSubjectReduction
        obligation obligationMem
      cases childrenBefore
      exact (StepStar.noStepChildren_childNil childStep).elim
  | cons childShift restShifts restIH =>
      cases childShift with
      | succ _childShiftPredecessor =>
          intro childrenBefore childrenAfter childStep _premisesHold _childSubjectReduction
            obligation obligationMem
          cases childrenBefore with
          | childCons head rest =>
              cases childStep with
              | @here _ _ _ _ headAfter restSame _childStepHead => cases obligationMem
              | @there _ _ _ _ _ restAfter _restStep => cases obligationMem
      | zero =>
          intro childrenBefore childrenAfter childStep premisesHold childSubjectReduction
            obligation obligationMem
          cases childrenBefore with
          | childCons head rest =>
              cases childStep with
              | @here _ _ _ _ headAfter restSame childStepHead =>
                  cases obligationMem with
                  | head =>
                      obtain ⟨pinned, reductTyped, convPinned⟩ :=
                        childSubjectReduction _ (List.Mem.head _) headAfter childStepHead
                      exact HasTypeUnion.reclassifyToType reductTyped convPinned carrierIsType
                  | tail _ tailMem => exact premisesHold _ (List.Mem.tail _ tailMem)
              | @there _ _ _ _ _ restAfter restStep =>
                  cases obligationMem with
                  | head => exact premisesHold _ (List.Mem.head _)
                  | tail _ tailMem =>
                      exact restIH rest restAfter restStep
                        (fun o om => premisesHold o (List.Mem.tail _ om))
                        (fun o om => childSubjectReduction o (List.Mem.tail _ om)) _ tailMem

end FX1Poly.Typed
