import FX1Poly.Core.Rewriting.RuleTables.Eta.StepEtaOverTable

/-! # StepEtaTableBackward — the generic eta-observation core extractor
inversion

The shared substrate brick the table-native source-shape reader
(`StepEtaRootTableSourceShape`) and the per-row child-join dispatchers
build on: from a successful `EtaObservationSpec.extractCoreFrom?` it
names the observed pieces — the intro child at the declared slot IS an
observer-headed cell, the fresh-variable test passed, and the core slot
strengthened to the extracted core.

(The bespoke `Step.eta`-producing backward bridges that once lived here
— the per-row `*ToBespokeEta` inversions and the total
`stepEtaTableRootToBespokeEta` — were retired in the TABLE-CANON-ETA
wave-4 retirement of the `Step.eta` sibling inductive; the table-native
source-shape reader `stepEtaRootTableSourceShape` replaced them.)

Proof discipline (the increment-A recipes, systematized):

  * peel the walk by proof-irrelevant ASCRIPTION (`have shaped : … :=
    success`), never by `dsimp` — every stuck conditional is re-spelled
    with our own bound proofs, which the kernel accepts by definitional
    proof irrelevance and `rw [if_neg …]`/`if_pos` then consumes;
  * `Option.some.inj` through whnf by the same ascription trick.

Zero-axiom: no `sorry`, no `propext`, no `Quot.sound`, no `Classical`,
`native_decide`, `omega`.  Per-declaration audit-gated in
`FX1PolyAudit/AuditStepEtaTableBackward.lean`. -/

namespace FX1Poly.Core

/-! ## The generic observation inversion -/

/-- A successful core extraction names its pieces: the intro child at
the declared slot IS an observer-headed cell, the fresh-variable test
passed, and the core slot strengthened to the extracted core. -/
theorem EtaObservationSpec.extractCoreFrom?_someInversion
    (spec : EtaObservationSpec) {scope : Nat} {introShifts : List Nat}
    {introChildren : RawTermChildren introShifts scope}
    {core : RawTerm scope}
    (success : spec.extractCoreFrom? introChildren = some core) :
    ∃ (observedPayload :
        spec.observerHead.payload (scope + spec.binderDepth))
      (observedChildren :
        RawTermChildren spec.observerHead.binderShifts
          (scope + spec.binderDepth)),
      introChildren.childAtShift? spec.introChildSlot spec.binderDepth
          = some (.mkGen spec.observerHead observedPayload observedChildren)
        ∧ observerFreshVarsHold observedChildren spec.freshVarSlots 0 = true
        ∧ (observedChildren.childAtShift? spec.coreSlot 0).bind
            (fun rawCore => RawTerm.strengthenBy? spec.binderDepth rawCore)
          = some core := by
  dsimp only [EtaObservationSpec.extractCoreFrom?] at success
  match lookupEq :
      introChildren.childAtShift? spec.introChildSlot spec.binderDepth with
  | none =>
      rw [lookupEq] at success
      exact nomatch success
  | some observedCell =>
      rw [lookupEq] at success
      match observedCell, success with
      | .mkGen observedHead observedPayload observedChildren, success =>
        have successReduced :
            (if observedHead = spec.observerHead then
              (if observerFreshVarsHold observedChildren
                  spec.freshVarSlots 0 = true then
                (observedChildren.childAtShift? spec.coreSlot 0).bind
                  (fun rawCore =>
                    RawTerm.strengthenBy? spec.binderDepth rawCore)
              else none)
            else none)
            = some core := success
        by_cases isObserver : observedHead = spec.observerHead
        case neg =>
            rw [if_neg isObserver] at successReduced
            exact nomatch successReduced
        case pos =>
            rw [if_pos isObserver] at successReduced
            subst isObserver
            by_cases freshHolds :
                observerFreshVarsHold observedChildren spec.freshVarSlots 0
                  = true
            case neg =>
                rw [if_neg freshHolds] at successReduced
                exact nomatch successReduced
            case pos =>
                rw [if_pos freshHolds] at successReduced
                exact ⟨observedPayload, observedChildren, rfl,
                  freshHolds, successReduced⟩

end FX1Poly.Core
