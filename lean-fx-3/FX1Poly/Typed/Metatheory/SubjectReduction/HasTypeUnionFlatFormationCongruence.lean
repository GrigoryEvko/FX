import FX1Poly.Typed.Engine.Union.HasTypeUnion
import FX1Poly.Typed.Engine.RuleTables.FormationRuleTable
import FX1Poly.Typed.Metatheory.SubjectReduction.HasTypeUnionEmptyTypeCongruenceCloser

/-! # FX1Poly/Typed/Metatheory/SubjectReduction/HasTypeUnionFlatFormationCongruence
    — the FLAT-former obligation transformation under a child congruence (gate-2, formationRule arm, flat family)

The `UnionCongruenceCloser` (TYTAB-2-FT gate 2) is the congruence case of single-step subject reduction: when one
child of a `.mkGen` cell steps, re-type the parent.  Proven by induction on the typing derivation it splits per
typing arm; the `formationRule` arm needs the per-family obligation transformation: the flat formation obligations
at `childrenBefore` all hold, plus each obligation's subject enjoys subject reduction (the master's IH) ⟹ every
flat obligation at `childrenAfter` holds.

The flat family (`product` / `either` / `equiv`) is the CLEANEST: `flatFormationObligations` classifies each child
at its own universe code `universeCodeCell level_i flag` — a classifier independent of the OTHER children's values —
so a single child congruence touches exactly ONE obligation's subject and leaves every sibling obligation literally
unchanged.  Re-typing the one stepped child is: take its subject reduction (`childSubjectReduction`), then
reclassify the reduct back to its universe code (universe rigidity: `reclassifyToType` lands the `Conv`-image of
`Type@level` exactly at `Type@level`, the target typed by `universeFormation`).

## The recursion: on `binderShifts`, not on the mutual inductives

`StepChildren` (mutual with `Step`) and `RawTermChildren` (mutual with `RawTerm`) both REJECT `induction`.  The
plain-inductive recursion driver is the spine length `binderShifts : List Nat`: `induction binderShifts` gives the
tail IH, and `cases` (allowed on mutual inductives) splits the children / `childStep` one level per node into the
`here` (head steps) / `there` (tail steps) cases — the native analogue of how the grown mutual SR recurses on its
`DescTelescopePi` telescope companion.

## Zero-axiom verification

`binderShifts` `induction` + one-level `cases` on children / `childStep` + `reclassifyToType` over the
`universeFormation` validity, threading the membership premises by `List.Mem.head` / `List.Mem.tail`.  No `axiom`,
`sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Per-declaration audit-gated in
`FX1PolyAudit/`. -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- **The flat-family obligation transformation under a child congruence.**  Given the flat formation obligations
at `childrenBefore` all hold and each enjoys subject reduction (the master's IH), a child step
`StepChildren childrenBefore childrenAfter` re-establishes every flat obligation at `childrenAfter`.  Recursion on
the spine length `binderShifts`; `here` re-types the stepped head via its obligation's SR + universe
reclassification, `there` recurses into the tail. -/
theorem flatFormationPremisesHoldAfter {profile : PolyProfile} {scope : Nat}
    (context : TypingContext profile scope) (flag : UniverseFlag) :
    ∀ {binderShifts : List Nat} (childrenBefore childrenAfter : RawTermChildren binderShifts scope),
      StepChildren childrenBefore childrenAfter →
      ∀ (levels : List LevelExpr),
        (∀ obligation ∈ flatFormationObligations profile context flag childrenBefore levels,
          HasTypeUnion profile obligation.context obligation.subject obligation.classifier) →
        (∀ obligation ∈ flatFormationObligations profile context flag childrenBefore levels,
          ∀ reduct : RawTerm obligation.scope, Step obligation.subject reduct →
            ∃ pinned : RawTerm obligation.scope,
              HasTypeUnion profile obligation.context reduct pinned ∧ Conv pinned obligation.classifier) →
        ∀ obligation ∈ flatFormationObligations profile context flag childrenAfter levels,
          HasTypeUnion profile obligation.context obligation.subject obligation.classifier := by
  intro binderShifts
  induction binderShifts with
  | nil =>
      intro childrenBefore childrenAfter childStep levels _premisesHold _childSubjectReduction
        obligation obligationMem
      cases childrenBefore
      exact (StepStar.noStepChildren_childNil childStep).elim
  | cons childShift restShifts restIH =>
      cases childShift with
      | succ _childShiftPredecessor =>
          intro childrenBefore childrenAfter childStep levels _premisesHold _childSubjectReduction
            obligation obligationMem
          cases childrenBefore with
          | childCons head rest =>
              -- `childShift = _ + 1`: `flatFormationObligations (childCons …) = []` on both sides.
              cases childStep with
              | @here _ _ _ _ headAfter restSame _childStepHead => cases obligationMem
              | @there _ _ _ _ _ restAfter _restStep => cases obligationMem
      | zero =>
          intro childrenBefore childrenAfter childStep levels premisesHold childSubjectReduction
            obligation obligationMem
          cases childrenBefore with
          | childCons head rest =>
              cases childStep with
              | @here _ _ _ _ headAfter restSame childStepHead =>
                  cases levels with
                  | nil =>
                      cases obligationMem with
                      | head =>
                          obtain ⟨pinned, reductTyped, convPinned⟩ :=
                            childSubjectReduction _ (List.Mem.head _) headAfter childStepHead
                          exact HasTypeUnion.reclassifyToType reductTyped convPinned
                            ⟨_, _, HasTypeUnion.universeFormation context LevelExpr.lzero flag⟩
                      | tail _ tailMem => exact premisesHold _ (List.Mem.tail _ tailMem)
                  | cons headLevel restLevels =>
                      cases obligationMem with
                      | head =>
                          obtain ⟨pinned, reductTyped, convPinned⟩ :=
                            childSubjectReduction _ (List.Mem.head _) headAfter childStepHead
                          exact HasTypeUnion.reclassifyToType reductTyped convPinned
                            ⟨_, _, HasTypeUnion.universeFormation context headLevel flag⟩
                      | tail _ tailMem => exact premisesHold _ (List.Mem.tail _ tailMem)
              | @there _ _ _ _ _ restAfter restStep =>
                  cases levels with
                  | nil =>
                      cases obligationMem with
                      | head => exact premisesHold _ (List.Mem.head _)
                      | tail _ tailMem =>
                          exact restIH rest restAfter restStep []
                            (fun o om => premisesHold o (List.Mem.tail _ om))
                            (fun o om => childSubjectReduction o (List.Mem.tail _ om)) _ tailMem
                  | cons headLevel restLevels =>
                      cases obligationMem with
                      | head => exact premisesHold _ (List.Mem.head _)
                      | tail _ tailMem =>
                          exact restIH rest restAfter restStep restLevels
                            (fun o om => premisesHold o (List.Mem.tail _ om))
                            (fun o om => childSubjectReduction o (List.Mem.tail _ om)) _ tailMem

end FX1Poly.Typed
