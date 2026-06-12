import FX1Poly.Core.EtaIotaCommutationSubstrate
import FX1Poly.Core.EtaContractionNaturality
import FX1Poly.Core.StepTableEquivariance

/-! # EtaIotaCoreReplacement — ETA-T5 increment 2: one observation's
core copy steps inside the intro cell

The root-eta case of the eta/iota quasi-commutation replaces, one
observation at a time, the weakened core copy inside the intro cell by
the weakened iota target.  This file ships that single-observation
replacement:

  * `strengthenBy?_freshVar_isNone` — a fresh variable never
    strengthens through its own binder block; with the fresh-pattern
    extraction `observerFreshVarsHold_atSlot` this REFUTES any
    collision between an observation's core slot and its fresh slots
    (a colliding row could never have extracted in the first place);
  * `observerFreshVarsHold_ofLookupAgree` — the fresh test transfers
    along lookup-preserving spines;
  * `StepOverTable.weakenByLift` — iota steps lift through iterated
    weakening (renaming closure, once per binder);
  * ★ `extractCoreFrom?_replaceCore` — ONE iota step on the core
    becomes ONE spine step on the intro children, after which the
    observation extracts the TARGET; every other intro slot's lookup
    is untouched (consumers re-run sibling observations through
    `extractCoreFrom?_congrLookup`).

Zero-axiom: no `sorry`, no `propext`, no `Quot.sound`, no `Classical`,
`native_decide`, `omega`.  Per-declaration audit-gated in
`FX1PolyAudit/AuditEtaIotaCoreReplacement.lean`. -/

namespace FX1Poly.Core

open FX1Poly.Foundation (RawRenaming)

/-! ## Fresh variables never strengthen through their block -/

/-- A variable inside the fresh block is killed by `strengthenBy?`:
peeling reaches it at index zero and the un-weakening refuses. -/
theorem RawTerm.strengthenBy?_freshVar_isNone {scope : Nat} :
    (depth : Nat) → (varIndex : Nat) → varIndex < depth →
    (bound : varIndex < scope + depth) →
    RawTerm.strengthenBy? depth
        (.mkGen .gen_var ⟨varIndex, bound⟩ .childNil)
      = (none : Option (RawTerm scope))
  | 0, _varIndex, isFresh, _bound => absurd isFresh (Nat.not_lt_zero _)
  | _depth + 1, 0, _isFresh, _bound => rfl
  | depth + 1, varIndex + 1, isFresh, bound =>
      RawTerm.strengthenBy?_freshVar_isNone depth varIndex
        (Nat.lt_of_succ_lt_succ isFresh) (Nat.lt_of_succ_lt_succ bound)

/-! ## Fresh-pattern extraction and transfer -/

/-- A passing fresh test pins each listed slot to its fresh variable,
with the variable index inside the block window. -/
theorem observerFreshVarsHold_atSlot {observerScope : Nat}
    {observerShifts : List Nat}
    (observedChildren : RawTermChildren observerShifts observerScope) :
    (varSlots : List Nat) → (startIndex : Nat) →
    observerFreshVarsHold observedChildren varSlots startIndex = true →
    {slot : Nat} → slot ∈ varSlots →
    ∃ (varIndex : Nat) (varBound : varIndex < observerScope),
      startIndex ≤ varIndex
      ∧ varIndex < startIndex + varSlots.length
      ∧ observedChildren.childAtShift? slot 0
          = some (.mkGen .gen_var ⟨varIndex, varBound⟩ .childNil)
  | [], _, _, _, isMember => by cases isMember
  | slot :: restSlots, startIndex, holds, querySlot, isMember => by
      dsimp only [observerFreshVarsHold] at holds
      match lookupEq : observedChildren.childAtShift? slot 0 with
      | none =>
          rw [lookupEq] at holds
          exact nomatch holds
      | some child =>
          rw [lookupEq] at holds
          have holdsReduced :
              ((if isInBounds : startIndex < observerScope then
                  if child
                      = RawTerm.mkGen .gen_var ⟨startIndex, isInBounds⟩
                          .childNil then true
                  else false
                else false)
                && observerFreshVarsHold observedChildren restSlots
                    (startIndex + 1))
              = true := holds
          by_cases startInBounds : startIndex < observerScope
          case neg =>
              rw [dif_neg startInBounds] at holdsReduced
              exact nomatch holdsReduced
          case pos =>
              rw [dif_pos startInBounds] at holdsReduced
              by_cases childIsVar :
                  child = RawTerm.mkGen .gen_var ⟨startIndex, startInBounds⟩
                    .childNil
              case neg =>
                  rw [if_neg childIsVar] at holdsReduced
                  exact nomatch holdsReduced
              case pos =>
                  obtain ⟨_headHolds, restHolds⟩ :=
                    andEqTrueSplit holdsReduced
                  cases isMember with
                  | head =>
                      exact ⟨startIndex, startInBounds, Nat.le_refl _,
                        Nat.lt_add_of_pos_right (Nat.succ_pos _),
                        lookupEq.trans (congrArg some childIsVar)⟩
                  | tail _ isInRest =>
                      obtain ⟨varIndex, varBound, lower, upper,
                          varLookup⟩ :=
                        observerFreshVarsHold_atSlot observedChildren
                          restSlots (startIndex + 1) restHolds isInRest
                      refine ⟨varIndex, varBound,
                        Nat.le_of_succ_le lower, ?_, varLookup⟩
                      rw [Nat.succ_add] at upper
                      exact upper
  termination_by varSlots => varSlots

/-- The fresh test transfers to any spine whose lookups agree at the
listed slots. -/
theorem observerFreshVarsHold_ofLookupAgree {observerScope : Nat}
    {observerShifts : List Nat}
    {observedChildren replacedChildren :
      RawTermChildren observerShifts observerScope} :
    (varSlots : List Nat) → (startIndex : Nat) →
    (lookupsAgree : ∀ slot, slot ∈ varSlots →
      replacedChildren.childAtShift? slot 0
        = observedChildren.childAtShift? slot 0) →
    observerFreshVarsHold observedChildren varSlots startIndex = true →
    observerFreshVarsHold replacedChildren varSlots startIndex = true
  | [], _, _, _ => rfl
  | slot :: restSlots, startIndex, lookupsAgree, holds => by
      dsimp only [observerFreshVarsHold] at holds ⊢
      rw [lookupsAgree slot (.head _)]
      match lookupEq : observedChildren.childAtShift? slot 0 with
      | none =>
          rw [lookupEq] at holds
          exact nomatch holds
      | some child =>
          rw [lookupEq] at holds
          have holdsReduced :
              ((if isInBounds : startIndex < observerScope then
                  if child
                      = RawTerm.mkGen .gen_var ⟨startIndex, isInBounds⟩
                          .childNil then true
                  else false
                else false)
                && observerFreshVarsHold observedChildren restSlots
                    (startIndex + 1))
              = true := holds
          obtain ⟨headHolds, restHolds⟩ := andEqTrueSplit holdsReduced
          show ((if isInBounds : startIndex < observerScope then
              if child
                  = RawTerm.mkGen .gen_var ⟨startIndex, isInBounds⟩
                      .childNil then true
              else false
            else false)
            && observerFreshVarsHold replacedChildren restSlots
                (startIndex + 1))
            = true
          rw [headHolds,
            observerFreshVarsHold_ofLookupAgree restSlots
              (startIndex + 1)
              (fun innerSlot isInRest =>
                lookupsAgree innerSlot (.tail _ isInRest))
              restHolds]
          rfl

/-! ## Extraction depends only on the observed slot -/

/-- The extraction consults the intro spine through ONE lookup; spines
agreeing there extract identically. -/
theorem EtaObservationSpec.extractCoreFrom?_congrLookup
    (spec : EtaObservationSpec) {scope : Nat} {introShifts : List Nat}
    {introChildren replacedChildren :
      RawTermChildren introShifts scope}
    (lookupAgrees :
      replacedChildren.childAtShift? spec.introChildSlot spec.binderDepth
        = introChildren.childAtShift? spec.introChildSlot
            spec.binderDepth) :
    spec.extractCoreFrom? replacedChildren
      = spec.extractCoreFrom? introChildren := by
  dsimp only [EtaObservationSpec.extractCoreFrom?]
  rw [lookupAgrees]

/-! ## Iota steps lift through iterated weakening -/

/-- A table step lifts through `weakenBy` — one renaming closure per
binder. -/
theorem StepOverTable.weakenByLift {table : List IotaRuleDesc}
    (tableIsUniform : ∀ rule, rule ∈ table → rule.IsScopeUniform)
    {scope : Nat} :
    (depth : Nat) → {source target : RawTerm scope} →
    StepOverTable table source target →
    StepOverTable table (RawTerm.weakenBy depth source)
      (RawTerm.weakenBy depth target)
  | 0, _, _, tableStep => tableStep
  | depth + 1, source, target, tableStep => by
      dsimp only [RawTerm.weakenBy]
      exact StepOverTable.rename tableIsUniform RawRenaming.weaken
        (StepOverTable.weakenByLift tableIsUniform depth tableStep)

/-! ## ★ The single-observation core replacement -/

/-- **One iota step on the core is one spine step on the intro
children**: the observation re-extracts the TARGET from the stepped
spine, and every other intro slot's lookup is untouched.  The fresh
slots cannot collide with the core slot — a colliding observation
could never have extracted (`strengthenBy?_freshVar_isNone`). -/
theorem EtaObservationSpec.extractCoreFrom?_replaceCore
    {iotaTable : List IotaRuleDesc}
    (tableIsUniform : ∀ rule, rule ∈ iotaTable → rule.IsScopeUniform)
    (spec : EtaObservationSpec) (isScopeSafe : spec.IsScopeSafe)
    {scope : Nat} {introShifts : List Nat}
    {introChildren : RawTermChildren introShifts scope}
    {core target : RawTerm scope}
    (extracts : spec.extractCoreFrom? introChildren = some core)
    (iotaStep : StepOverTable iotaTable core target) :
    ∃ replacedIntroChildren : RawTermChildren introShifts scope,
      StepOverTableChildren iotaTable introChildren
        replacedIntroChildren
      ∧ spec.extractCoreFrom? replacedIntroChildren = some target
      ∧ ∀ otherSlot otherShift : Nat,
          otherSlot ≠ spec.introChildSlot →
          replacedIntroChildren.childAtShift? otherSlot otherShift
            = introChildren.childAtShift? otherSlot otherShift := by
  obtain ⟨observedPayload, observedChildren, lookupEq, freshHolds,
    coreExtract⟩ :=
    EtaObservationSpec.extractCoreFrom?_someInversion spec extracts
  match coreLookupEq :
      observedChildren.childAtShift? spec.coreSlot 0 with
  | none =>
      rw [coreLookupEq] at coreExtract
      exact nomatch coreExtract
  | some rawCore =>
      rw [coreLookupEq] at coreExtract
      have strengthenedRaw :
          RawTerm.strengthenBy? spec.binderDepth rawCore = some core :=
        coreExtract
      have rawIsWeakenedCore :
          RawTerm.weakenBy spec.binderDepth core = rawCore :=
        RawTerm.weakenBy_strengthenBy? spec.binderDepth rawCore core
          strengthenedRaw
      -- lift the iota step to the weakened copy
      have liftedStep :
          StepOverTable iotaTable rawCore
            (RawTerm.weakenBy spec.binderDepth target) := by
        rw [← rawIsWeakenedCore]
        exact StepOverTable.weakenByLift tableIsUniform
          spec.binderDepth iotaStep
      -- replace inside the observer cell
      obtain ⟨replacedObserved, innerStep, newInnerLookup,
          innerPreserved⟩ :=
        StepOverTableChildren.ofChildAtShiftStep observedChildren
          spec.coreSlot 0 coreLookupEq liftedStep
      -- the fresh slots avoid the core slot (else extraction
      -- would have refused)
      have freshAvoidsCore :
          ∀ slot, slot ∈ spec.freshVarSlots → slot ≠ spec.coreSlot := by
        intro slot isMember slotIsCore
        obtain ⟨varIndex, varBound, _lower, upper, varLookup⟩ :=
          observerFreshVarsHold_atSlot observedChildren
            spec.freshVarSlots 0 freshHolds isMember
        have varIsFresh : varIndex < spec.binderDepth := by
          rw [Nat.zero_add] at upper
          exact Nat.lt_of_lt_of_le upper isScopeSafe.freshVarsWithinDepth
        rw [slotIsCore] at varLookup
        have rawIsVar :
            rawCore
              = RawTerm.mkGen .gen_var ⟨varIndex, varBound⟩ .childNil :=
          Option.some.inj (coreLookupEq.symm.trans varLookup)
        rw [rawIsVar,
          RawTerm.strengthenBy?_freshVar_isNone spec.binderDepth
            varIndex varIsFresh varBound] at strengthenedRaw
        exact nomatch strengthenedRaw
      have freshHoldsReplaced :
          observerFreshVarsHold replacedObserved spec.freshVarSlots 0
            = true :=
        observerFreshVarsHold_ofLookupAgree spec.freshVarSlots 0
          (fun slot isMember =>
            innerPreserved slot 0 (freshAvoidsCore slot isMember))
          freshHolds
      -- step the observer cell, then the intro spine
      have cellStep :
          StepOverTable iotaTable
            (RawTerm.mkGen spec.observerHead observedPayload
              observedChildren)
            (RawTerm.mkGen spec.observerHead observedPayload
              replacedObserved) :=
        StepOverTable.cong spec.observerHead observedPayload innerStep
      obtain ⟨replacedIntroChildren, outerStep, newOuterLookup,
          outerPreserved⟩ :=
        StepOverTableChildren.ofChildAtShiftStep introChildren
          spec.introChildSlot spec.binderDepth lookupEq cellStep
      refine ⟨replacedIntroChildren, outerStep, ?_, outerPreserved⟩
      -- assemble the replaced extraction
      dsimp only [EtaObservationSpec.extractCoreFrom?]
      rw [newOuterLookup]
      show (if spec.observerHead = spec.observerHead then
          (if observerFreshVarsHold replacedObserved
              spec.freshVarSlots 0 = true then
            (replacedObserved.childAtShift? spec.coreSlot 0).bind
              (fun rawCoreTerm =>
                RawTerm.strengthenBy? spec.binderDepth rawCoreTerm)
          else none)
        else none)
        = some target
      rw [if_pos rfl, if_pos freshHoldsReplaced, newInnerLookup]
      show RawTerm.strengthenBy? spec.binderDepth
          (RawTerm.weakenBy spec.binderDepth target)
        = some target
      exact RawTerm.strengthenBy?_weakenBy spec.binderDepth target

end FX1Poly.Core
