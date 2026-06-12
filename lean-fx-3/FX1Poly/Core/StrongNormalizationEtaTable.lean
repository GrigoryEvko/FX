import FX1Poly.Core.StepEtaTableBackward
import FX1Poly.Core.StrongNormalizationEta

/-! # StrongNormalizationEtaTable — ETA-T3: size decrease is a THEOREM

The schema makes eta size decrease a theorem, not a per-row
certificate: a contracting intro cell's core is a STRENGTHENED
child-subterm of an observation cell inside the intro cell, and
strengthening preserves `RawTerm.size` (un-weakening renames variables;
renaming never duplicates or drops node structure — `size_rename`).
The strict inequalities stack:

    core  =  rawCore  <  observer spine  <  observer cell
          <  intro spine  <  intro cell.

Corollary, generic over ANY `EtaRuleDesc` table: `StepEtaOverTable` is
strongly normalizing via the `RawTerm.size` measure — the table
replacement of the bespoke hand-threaded 5-arm `etaStar` SN
(`StrongNormalizationEta`).  Every future eta row inherits SN with ZERO
new proof.  No claim here about the union with the iota table — that is
ETA-T5/T6 territory.

Zero-axiom: no `sorry`, no `propext`, no `Quot.sound`, no `Classical`,
`native_decide`, `omega`.  Per-declaration audit-gated in
`FX1PolyAudit/AuditStrongNormalizationEtaTable.lean`. -/

namespace FX1Poly.Core

/-! ## Strengthening preserves size -/

/-- Single-depth: a successful strengthening preserves size — the body
IS the weakened core (`strengthen_sound`), and weakening is a renaming
(`size_weaken`). -/
theorem RawTerm.size_strengthen {scope : Nat}
    {body : RawTerm (scope + 1)} {extracted : RawTerm scope}
    (success : RawTerm.strengthen body = some extracted) :
    extracted.size = body.size := by
  rw [← RawTerm.strengthen_sound body extracted success]
  exact (RawTerm.size_weaken extracted).symm

/-- Multi-depth: `strengthenBy?` preserves size, stacking the
single-depth square along the newest-first recursion. -/
theorem RawTerm.size_strengthenBy? {scope : Nat} :
    (depth : Nat) → {body : RawTerm (scope + depth)} →
    {core : RawTerm scope} →
    RawTerm.strengthenBy? depth body = some core →
    core.size = body.size
  | 0, body, core, success => by
      have bodyIsCore : core = body := (Option.some.inj success).symm
      subst bodyIsCore
      rfl
  | depth + 1, body, core, success => by
      have peeled :
          (RawTerm.strengthen body).bind
            (fun stripped => RawTerm.strengthenBy? depth stripped)
          = some core := success
      match strippedEq : RawTerm.strengthen body with
      | none =>
          rw [strippedEq] at peeled
          exact nomatch peeled
      | some stripped =>
          rw [strippedEq] at peeled
          have strippedSuccess :
              RawTerm.strengthenBy? depth stripped = some core := peeled
          rw [RawTerm.size_strengthenBy? depth strippedSuccess]
          exact RawTerm.size_strengthen strippedEq

/-! ## Lookup finds a strict subterm -/

/-- A successful shift-checked lookup finds a STRICT subterm of the
spine. -/
theorem RawTermChildren.size_childAtShift? {scope : Nat} :
    {binderShifts : List Nat} →
    (children : RawTermChildren binderShifts scope) →
    (slot expectedShift : Nat) →
    {found : RawTerm (scope + expectedShift)} →
    RawTermChildren.childAtShift? children slot expectedShift
      = some found →
    found.size < children.size
  | _, .childNil, _, _, _, lookupEq => nomatch lookupEq
  | headShift :: _restShifts, .childCons head rest, 0, expectedShift,
      found, lookupEq => by
      by_cases shiftMatches : headShift = expectedShift
      case pos =>
          have computed :
              RawTermChildren.childAtShift?
                (RawTermChildren.childCons head rest) 0 expectedShift
              = (if shiftEq : headShift = expectedShift then
                  some (shiftEq ▸ head)
                else none) := rfl
          rw [computed, dif_pos shiftMatches] at lookupEq
          have headIsFound : shiftMatches ▸ head = found :=
            Option.some.inj lookupEq
          subst headIsFound
          cases shiftMatches
          exact RawTermChildren.size_lt_childCons_head head rest
      case neg =>
          have computed :
              RawTermChildren.childAtShift?
                (RawTermChildren.childCons head rest) 0 expectedShift
              = (if shiftEq : headShift = expectedShift then
                  some (shiftEq ▸ head)
                else none) := rfl
          rw [computed, dif_neg shiftMatches] at lookupEq
          exact nomatch lookupEq
  | _headShift :: _restShifts, .childCons _head rest, nextSlot + 1,
      expectedShift, found, lookupEq =>
      Nat.lt_trans
        (RawTermChildren.size_childAtShift? rest nextSlot expectedShift
          lookupEq)
        (RawTermChildren.size_lt_childCons_tail _head rest)

/-! ## The contraction inversion -/

/-- A successful contraction inverts to its PRIMARY observation: the
head of the observation list extracts the shared core. -/
theorem EtaRuleDesc.contractsOn?_someInversion (rule : EtaRuleDesc)
    {scope : Nat}
    {introChildren :
      RawTermChildren rule.introGenerator.binderShifts scope}
    {core : RawTerm scope}
    (contracts : rule.contractsOn? introChildren = some core) :
    ∃ primarySpec, primarySpec ∈ rule.observations
      ∧ primarySpec.extractCoreFrom? introChildren = some core := by
  dsimp only [EtaRuleDesc.contractsOn?] at contracts
  match specsEq : rule.observations with
  | [] =>
      rw [specsEq] at contracts
      exact nomatch contracts
  | primarySpec :: restSpecs =>
      rw [specsEq] at contracts
      have contractsReduced :
          (primarySpec.extractCoreFrom? introChildren).bind
              (fun sharedCore =>
                if etaObservationsAgree introChildren sharedCore
                    restSpecs then some sharedCore
                else none)
            = some core := contracts
      match extractEq : primarySpec.extractCoreFrom? introChildren with
      | none =>
          rw [extractEq] at contractsReduced
          exact nomatch contractsReduced
      | some extractedCore =>
          rw [extractEq] at contractsReduced
          have gateReduced :
              (if etaObservationsAgree introChildren extractedCore
                  restSpecs then some extractedCore
              else none)
                = some core := contractsReduced
          by_cases agreeHolds :
              etaObservationsAgree introChildren extractedCore restSpecs
                = true
          case neg =>
              rw [if_neg agreeHolds] at gateReduced
              exact nomatch gateReduced
          case pos =>
              rw [if_pos agreeHolds] at gateReduced
              have coreIsExtracted : extractedCore = core :=
                Option.some.inj gateReduced
              exact ⟨primarySpec, List.Mem.head _,
                by rw [extractEq, coreIsExtracted]⟩

/-! ## ★ The size-decrease theorem -/

/-- **Eta size decrease is a THEOREM of the schema**: any contraction
of any rule strictly shrinks the term — the core is a strengthened
strict subterm of the observation cell, itself a strict subterm of the
intro cell.  No per-row certificate. -/
theorem EtaRuleDesc.contractsOn?_sizeDecreases (rule : EtaRuleDesc)
    {scope : Nat}
    (introPayload : rule.introGenerator.payload scope)
    {introChildren :
      RawTermChildren rule.introGenerator.binderShifts scope}
    {core : RawTerm scope}
    (contracts : rule.contractsOn? introChildren = some core) :
    core.size
      < (RawTerm.mkGen rule.introGenerator introPayload
          introChildren).size := by
  obtain ⟨primarySpec, _isMember, extractSuccess⟩ :=
    rule.contractsOn?_someInversion contracts
  obtain ⟨observedPayload, observedChildren, lookupEq, _freshHolds,
    coreExtract⟩ :=
    EtaObservationSpec.extractCoreFrom?_someInversion primarySpec
      extractSuccess
  match coreLookupEq :
      observedChildren.childAtShift? primarySpec.coreSlot 0 with
  | none =>
      rw [coreLookupEq] at coreExtract
      exact nomatch coreExtract
  | some rawCore =>
      rw [coreLookupEq] at coreExtract
      have strengthenedRaw :
          RawTerm.strengthenBy? primarySpec.binderDepth rawCore
            = some core := coreExtract
      have coreSizeIsRaw : core.size = rawCore.size :=
        RawTerm.size_strengthenBy? primarySpec.binderDepth
          strengthenedRaw
      have rawLtObservedSpine : rawCore.size < observedChildren.size :=
        RawTermChildren.size_childAtShift? observedChildren
          primarySpec.coreSlot 0 coreLookupEq
      have observedSpineLtObserverCell :
          observedChildren.size
            < (RawTerm.mkGen primarySpec.observerHead observedPayload
                observedChildren).size := by
        dsimp only [RawTerm.size]
        exact Nat.lt_succ_self _
      have observerCellLtIntroSpine :
          (RawTerm.mkGen primarySpec.observerHead observedPayload
              observedChildren).size
            < introChildren.size :=
        RawTermChildren.size_childAtShift? introChildren
          primarySpec.introChildSlot primarySpec.binderDepth lookupEq
      have introSpineLtIntroCell :
          introChildren.size
            < (RawTerm.mkGen rule.introGenerator introPayload
                introChildren).size := by
        dsimp only [RawTerm.size]
        exact Nat.lt_succ_self _
      rw [coreSizeIsRaw]
      exact Nat.lt_trans rawLtObservedSpine
        (Nat.lt_trans observedSpineLtObserverCell
          (Nat.lt_trans observerCellLtIntroSpine introSpineLtIntroCell))

/-! ## The full relation decreases size -/

mutual

/-- Every table eta step — root contraction OR congruence — strictly
decreases `RawTerm.size`, for ANY table. -/
theorem StepEtaOverTable.sizeDecreases {table : List EtaRuleDesc} :
    {scope : Nat} → {source target : RawTerm scope} →
    StepEtaOverTable table source target →
    target.size < source.size
  | _, _, _, .etaRedex _isRow _isRawTier introPayload contracts =>
      EtaRuleDesc.contractsOn?_sizeDecreases _ introPayload contracts
  | _, _, _, .cong _gen _payload childStep => by
      dsimp only [RawTerm.size]
      exact Nat.succ_lt_succ
        (StepEtaOverTableChildren.sizeDecreases childStep)

/-- Spine companion: a step at any position strictly decreases the
spine size. -/
theorem StepEtaOverTableChildren.sizeDecreases
    {table : List EtaRuleDesc} :
    {parentScope : Nat} → {binderShifts : List Nat} →
    {children children' : RawTermChildren binderShifts parentScope} →
    StepEtaOverTableChildren table children children' →
    children'.size < children.size
  | _, _, _, _, .here rest headStep => by
      dsimp only [RawTermChildren.size]
      exact Nat.succ_lt_succ
        (Nat.add_lt_add_right
          (StepEtaOverTable.sizeDecreases headStep) rest.size)
  | _, _, _, _, .there head restStep => by
      dsimp only [RawTermChildren.size]
      exact Nat.succ_lt_succ
        (Nat.add_lt_add_left
          (StepEtaOverTableChildren.sizeDecreases restStep) head.size)

end

/-! ## ★ Generic table eta SN -/

/-- Successor orientation for accessibility: `laterTerm` is below
`earlierTerm` when `earlierTerm` eta-contracts to it over the table. -/
def StepEtaOverTable.successorOver (table : List EtaRuleDesc)
    {scope : Nat} (laterTerm earlierTerm : RawTerm scope) : Prop :=
  StepEtaOverTable table earlierTerm laterTerm

/-- **Generic table eta SN**: `StepEtaOverTable` is strongly
normalizing for ANY table, via the `RawTerm.size` measure.  Every
future eta row inherits this with zero new proof. -/
theorem stepEtaOverTable_wellFounded (table : List EtaRuleDesc)
    {scope : Nat} :
    WellFounded (StepEtaOverTable.successorOver table (scope := scope)) :=
  Subrelation.wf
    (q := StepEtaOverTable.successorOver table (scope := scope))
    (r := InvImage (fun leftSize rightSize : Nat =>
      leftSize < rightSize) RawTerm.size)
    (fun etaStep => StepEtaOverTable.sizeDecreases etaStep)
    (InvImage.wf RawTerm.size
      (Nat.lt_wfRel.wf :
        WellFounded (fun leftSize rightSize : Nat =>
          leftSize < rightSize)))

/-- Every raw term is strongly normalizing for table eta over ANY
table. -/
theorem StepEtaOverTable.isStronglyNormalizing
    (table : List EtaRuleDesc) {scope : Nat}
    (sourceTerm : RawTerm scope) :
    Acc (StepEtaOverTable.successorOver table) sourceTerm :=
  (stepEtaOverTable_wellFounded table).apply sourceTerm

/-- The canonical 5-row table eta relation is well-founded. -/
theorem stepEtaTable_wellFounded {scope : Nat} :
    WellFounded
      (StepEtaOverTable.successorOver etaRuleTable (scope := scope)) :=
  stepEtaOverTable_wellFounded etaRuleTable

end FX1Poly.Core
