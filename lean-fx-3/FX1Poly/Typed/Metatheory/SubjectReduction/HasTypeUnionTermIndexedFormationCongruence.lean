import FX1Poly.Typed.Engine.Union.HasTypeUnion
import FX1Poly.Typed.Engine.RuleTables.FormationRuleTable
import FX1Poly.Typed.Metatheory.SubjectReduction.HasTypeUnionEmptyTypeCongruenceCloser
import FX1Poly.Typed.Metatheory.Validity.HasTypeUnionValidity

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

/-- **The term-indexed endpoint obligations transport under a carrier conversion.**  When the CARRIER child of a
term-indexed former steps (`carrierOld ↝ carrierNew`, hence `Conv carrierOld carrierNew`), every endpoint — typed at
the OLD carrier — must be re-typed at the NEW carrier.  Each endpoint reclassifies from `carrierOld` to `carrierNew`
through the carrier `Conv` and a `carrierNew`-is-type witness (which the master supplies from the carrier
obligation's own subject reduction, `carrierNew : Type@level`).  The carrier-step complement of
`termIndexedEndpointObligationsHoldAfter`: the children are UNCHANGED here (only the classifier carrier moves), so
there is no `childStep` — a pure spine-length transport. -/
theorem termIndexedEndpointObligationsHoldUnderCarrierConv {profile : PolyProfile} {scope : Nat}
    (context : TypingContext profile scope) (carrierOld carrierNew : RawTerm scope)
    (carrierConv : Conv carrierOld carrierNew)
    (carrierNewIsType : UnionClassifierIsType profile context carrierNew) :
    ∀ {shifts : List Nat} (children : RawTermChildren shifts scope),
      (∀ obligation ∈ termIndexedEndpointObligations profile context carrierOld children,
        HasTypeUnion profile obligation.context obligation.subject obligation.classifier) →
      ∀ obligation ∈ termIndexedEndpointObligations profile context carrierNew children,
        HasTypeUnion profile obligation.context obligation.subject obligation.classifier := by
  intro shifts
  induction shifts with
  | nil =>
      intro children _premisesHold obligation obligationMem
      cases children
      cases obligationMem
  | cons childShift restShifts restIH =>
      cases childShift with
      | succ _childShiftPredecessor =>
          intro children _premisesHold obligation obligationMem
          cases children with
          | childCons head rest => cases obligationMem
      | zero =>
          intro children premisesHold obligation obligationMem
          cases children with
          | childCons head rest =>
              cases obligationMem with
              | head =>
                  have headTypedAtOldCarrier : HasTypeUnion profile context head carrierOld :=
                    premisesHold _ (List.Mem.head _)
                  exact HasTypeUnion.reclassifyToType headTypedAtOldCarrier carrierConv carrierNewIsType
              | tail _ tailMem =>
                  exact restIH rest (fun o om => premisesHold o (List.Mem.tail _ om)) _ tailMem

/-- **★ The term-indexed FULL formation-obligation transform under a child congruence.**  The complete
`FormationRule.termIndexed` obligation list — the carrier-at-universe HEAD obligation (the first child at
`universeCodeCell level flag`) plus the endpoint TAIL (`termIndexedEndpointObligations carrier rest`) —
re-establishes after a single child congruence.  Two step loci, split by `cases childStep`:

  * the FIRST CHILD (the carrier-at-universe subject) stepping re-types the head obligation through its SR +
    universe reclassification, while the endpoint tail — which references the FREE `carrier` param and the
    UNCHANGED `rest` — stays literally put;
  * an ENDPOINT (in `rest`) stepping leaves the head obligation untouched and routes the endpoint tail through
    `termIndexedEndpointObligationsHoldAfter`.

The carrier obligation's SUBJECT is the first child while the endpoints' CLASSIFIER is the FREE `carrier`
param — DECOUPLED in `FormationRule.obligations`, so a carrier-child step needs NO endpoint carrier-conv
transport (the endpoints' classifier did not move).  `levels` is inert for the term-indexed family.  No spine
`induction` (the endpoint fold self-recurses inside `termIndexedEndpointObligationsHoldAfter`); a single
`cases childrenBefore` + `cases childStep`.  The formationRule-arm congruence transform for Id/Bridge, the
term-indexed sibling of `flatFormationPremisesHoldAfter`. -/
theorem termIndexedFormationPremisesHoldAfter {profile : PolyProfile} {scope : Nat}
    (context : TypingContext profile scope) (termRule : TermIndexedFormerDesc)
    (carrier : RawTerm scope) (level : LevelExpr) (flag : UniverseFlag)
    (carrierIsType : UnionClassifierIsType profile context carrier)
    {binderShifts : List Nat} (childrenBefore childrenAfter : RawTermChildren binderShifts scope)
    (childStep : StepChildren childrenBefore childrenAfter) (levels : List LevelExpr)
    (premisesHold : ∀ obligation ∈ (FormationRule.termIndexed termRule).obligations profile context
        childrenBefore levels carrier level flag,
      HasTypeUnion profile obligation.context obligation.subject obligation.classifier)
    (childSubjectReduction : ∀ obligation ∈ (FormationRule.termIndexed termRule).obligations profile context
        childrenBefore levels carrier level flag,
      ∀ reduct : RawTerm obligation.scope, Step obligation.subject reduct →
        ∃ pinned : RawTerm obligation.scope,
          HasTypeUnion profile obligation.context reduct pinned ∧ Conv pinned obligation.classifier) :
    ∀ obligation ∈ (FormationRule.termIndexed termRule).obligations profile context childrenAfter
        levels carrier level flag,
      HasTypeUnion profile obligation.context obligation.subject obligation.classifier := by
  intro obligation obligationMem
  cases childrenBefore with
  | childNil => exact (StepStar.noStepChildren_childNil childStep).elim
  | childCons head rest =>
      rename_i carrierShift _restShifts
      cases carrierShift with
      | succ _carrierShiftPredecessor =>
          -- carrier shift `_+1`: the term-indexed obligation list is `[]` on both sides.
          cases childStep with
          | @here _ _ _ _ _headAfter _restSame _childStepHead => cases obligationMem
          | @there _ _ _ _ _ _restAfter _restStep => cases obligationMem
      | zero =>
          cases childStep with
          | @here _ _ _ _ headAfter restSame childStepHead =>
              -- the carrier child stepped: re-type the head obligation, endpoints untouched.
              cases obligationMem with
              | head =>
                  obtain ⟨pinned, reductTyped, convPinned⟩ :=
                    childSubjectReduction _ (List.Mem.head _) headAfter childStepHead
                  exact HasTypeUnion.reclassifyToType reductTyped convPinned
                    ⟨_, _, HasTypeUnion.universeFormation context level flag⟩
              | tail _ tailMem => exact premisesHold _ (List.Mem.tail _ tailMem)
          | @there _ _ _ _ _ restAfter restStep =>
              -- an endpoint stepped: head obligation untouched, endpoints transform at the fixed carrier.
              cases obligationMem with
              | head => exact premisesHold _ (List.Mem.head _)
              | tail _ tailMem =>
                  exact termIndexedEndpointObligationsHoldAfter context carrier carrierIsType
                    rest restAfter restStep
                    (fun o om => premisesHold o (List.Mem.tail _ om))
                    (fun o om => childSubjectReduction o (List.Mem.tail _ om)) _ tailMem

/-- **The `WfContextUnion`-driven term-indexed endpoint transform** — the future-proof twin of
`termIndexedEndpointObligationsHoldAfter` that takes `WfContextUnion context` instead of a pre-built
`carrier`-is-type witness.  When an endpoint steps, the carrier-is-type fact needed to reclassify the reduct
back to `carrier` is derived RIGHT WHERE NEEDED, from the stepping endpoint's own obligation (`head : carrier`)
via the unconditional validity `HasTypeUnion.classifierIsType` over `wellFormed`.  Because the witness is
derived locally — in the one branch where an endpoint actually reclassifies — a term-indexed former with ZERO
endpoints (where `carrier` is otherwise unconstrained by the obligations) is handled without ever demanding a
carrier-is-type witness: the reclassify branch is simply unreachable.  This is what makes the formation
congruence GATE inhabitable from the `WfContextUnion` it already carries, with no separate carrier hypothesis. -/
theorem termIndexedEndpointObligationsHoldAfterWf {profile : PolyProfile} {scope : Nat}
    (context : TypingContext profile scope) (carrier : RawTerm scope)
    (wellFormed : WfContextUnion context) :
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
                      have headBeforeTyped : HasTypeUnion profile context head carrier :=
                        premisesHold _ (List.Mem.head _)
                      obtain ⟨pinned, reductTyped, convPinned⟩ :=
                        childSubjectReduction _ (List.Mem.head _) headAfter childStepHead
                      exact HasTypeUnion.reclassifyToType reductTyped convPinned
                        (HasTypeUnion.classifierIsType headBeforeTyped wellFormed)
                  | tail _ tailMem => exact premisesHold _ (List.Mem.tail _ tailMem)
              | @there _ _ _ _ _ restAfter restStep =>
                  cases obligationMem with
                  | head => exact premisesHold _ (List.Mem.head _)
                  | tail _ tailMem =>
                      exact restIH rest restAfter restStep
                        (fun o om => premisesHold o (List.Mem.tail _ om))
                        (fun o om => childSubjectReduction o (List.Mem.tail _ om)) _ tailMem

/-- **★ The `WfContextUnion`-driven term-indexed FULL formation-obligation transform.**  The future-proof twin
of `termIndexedFormationPremisesHoldAfter` consumed by the formation congruence gate: it takes
`WfContextUnion context` (which the gate already holds) rather than a separate `carrier`-is-type witness, routing
the endpoint tail through `termIndexedEndpointObligationsHoldAfterWf`.  The carrier-at-universe HEAD obligation
re-types through the universe formation witness (no carrier witness needed); an endpoint step routes through the
Wf endpoint transform, which derives the carrier-is-type fact locally from the stepping endpoint's obligation. -/
theorem termIndexedFormationPremisesHoldAfterWf {profile : PolyProfile} {scope : Nat}
    (context : TypingContext profile scope) (termRule : TermIndexedFormerDesc)
    (carrier : RawTerm scope) (level : LevelExpr) (flag : UniverseFlag)
    (wellFormed : WfContextUnion context)
    {binderShifts : List Nat} (childrenBefore childrenAfter : RawTermChildren binderShifts scope)
    (childStep : StepChildren childrenBefore childrenAfter) (levels : List LevelExpr)
    (premisesHold : ∀ obligation ∈ (FormationRule.termIndexed termRule).obligations profile context
        childrenBefore levels carrier level flag,
      HasTypeUnion profile obligation.context obligation.subject obligation.classifier)
    (childSubjectReduction : ∀ obligation ∈ (FormationRule.termIndexed termRule).obligations profile context
        childrenBefore levels carrier level flag,
      ∀ reduct : RawTerm obligation.scope, Step obligation.subject reduct →
        ∃ pinned : RawTerm obligation.scope,
          HasTypeUnion profile obligation.context reduct pinned ∧ Conv pinned obligation.classifier) :
    ∀ obligation ∈ (FormationRule.termIndexed termRule).obligations profile context childrenAfter
        levels carrier level flag,
      HasTypeUnion profile obligation.context obligation.subject obligation.classifier := by
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
                  obtain ⟨pinned, reductTyped, convPinned⟩ :=
                    childSubjectReduction _ (List.Mem.head _) headAfter childStepHead
                  exact HasTypeUnion.reclassifyToType reductTyped convPinned
                    ⟨_, _, HasTypeUnion.universeFormation context level flag⟩
              | tail _ tailMem => exact premisesHold _ (List.Mem.tail _ tailMem)
          | @there _ _ _ _ _ restAfter restStep =>
              cases obligationMem with
              | head => exact premisesHold _ (List.Mem.head _)
              | tail _ tailMem =>
                  exact termIndexedEndpointObligationsHoldAfterWf context carrier wellFormed
                    rest restAfter restStep
                    (fun o om => premisesHold o (List.Mem.tail _ om))
                    (fun o om => childSubjectReduction o (List.Mem.tail _ om)) _ tailMem

end FX1Poly.Typed
