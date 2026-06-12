import FX1Poly.Core.StepEtaOverTable

/-! # StepEtaTableBackward — ETA-T1 increment B: the backward firing
inversions

The backward half of the eta adequacy: a TABLE contraction is the
bespoke `Step.eta` — per raw row, a successful `contractsOn?` forces the
intro children into EXACTLY the bespoke source shape (the observer head
pins, the fresh-variable test pins the argument to `var 0`, and the
`strengthenBy?` success reconstructs the weakened core through the
reverse roundtrip), so the bespoke constructor applies.  The typed-tier
rows discharge vacuously at the raw relation (their tier verdict
contradicts the `etaRedex` gate), giving the TOTAL root backward
`stepEtaTableRootToBespokeEta`.

Proof discipline (the increment-A recipes, systematized):

  * peel the walk by proof-irrelevant ASCRIPTION (`have shaped : … :=
    contracts`), never by `dsimp` — every stuck conditional is re-spelled
    with our own bound proofs, which the kernel accepts by definitional
    proof irrelevance and `rw [if_neg …]`/`if_pos` then consumes;
  * `Option.some.inj` through whnf by the same ascription trick;
  * the reverse roundtrip `weakenBy_strengthenBy?` turns the core
    extraction into the syntactic `weaken core` the bespoke source
    shape demands.

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

/-! ## The per-row backward inversions -/

/-- **Function eta, backward**: a successful `etaLamRow` contraction
forces the bespoke `etaLamSource` shape, so the bespoke arm applies. -/
theorem etaLamRowContractionToBespokeEta {scope : Nat}
    (introPayload : etaLamRow.introGenerator.payload scope)
    {introChildren :
      RawTermChildren etaLamRow.introGenerator.binderShifts scope}
    {core : RawTerm scope}
    (contracts : etaLamRow.contractsOn? introChildren = some core) :
    Step.eta (.mkGen etaLamRow.introGenerator introPayload introChildren)
      core := by
  match introChildren, contracts with
  | .childCons domainAnn (.childCons bodyChild .childNil), contracts =>
    have peeled :
        (({ introChildSlot := 1, observerHead := .gen_app, coreSlot := 0
          , binderDepth := 1, freshVarSlots := [1] } :
            EtaObservationSpec).extractCoreFrom?
          (RawTermChildren.childCons domainAnn
            (RawTermChildren.childCons bodyChild
              RawTermChildren.childNil))).bind some
        = some core := contracts
    match extractEq :
        ({ introChildSlot := 1, observerHead := .gen_app, coreSlot := 0
         , binderDepth := 1, freshVarSlots := [1] } :
           EtaObservationSpec).extractCoreFrom?
          (RawTermChildren.childCons domainAnn
            (RawTermChildren.childCons bodyChild
              RawTermChildren.childNil)) with
    | none =>
        rw [extractEq] at peeled
        exact nomatch peeled
    | some extracted =>
        rw [extractEq] at peeled
        have extractedIsCore : core = extracted :=
          (Option.some.inj (peeled : some extracted = some core)).symm
        subst extractedIsCore
        obtain ⟨observedPayload, observedChildren, lookupEq, freshHolds,
          coreExtract⟩ :=
          EtaObservationSpec.extractCoreFrom?_someInversion _ extractEq
        have bodyShape :
            bodyChild
              = RawTerm.mkGen .gen_app observedPayload observedChildren :=
          Option.some.inj
            (lookupEq :
              some bodyChild
                = some (RawTerm.mkGen .gen_app observedPayload
                    observedChildren))
        subst bodyShape
        match observedChildren, freshHolds, coreExtract with
        | .childCons functionChild (.childCons argumentChild .childNil),
            freshHolds, coreExtract =>
          have argTest :
              ((if argumentChild
                    = RawTerm.mkGen .gen_var ⟨0, Nat.zero_lt_succ scope⟩
                        .childNil then true
                else false)
                && true)
              = true := freshHolds
          by_cases argEq :
              argumentChild
                = RawTerm.mkGen .gen_var ⟨0, Nat.zero_lt_succ scope⟩
                    .childNil
          case neg =>
              rw [if_neg argEq] at argTest
              exact nomatch argTest
          case pos =>
              subst argEq
              have strengthened :
                  RawTerm.strengthenBy? 1 functionChild = some core :=
                coreExtract
              have functionShape :
                  RawTerm.weakenBy 1 core = functionChild :=
                RawTerm.weakenBy_strengthenBy? 1 functionChild core
                  strengthened
              rw [← functionShape]
              exact Step.eta.etaLam domainAnn core

/-- **Path eta, backward.** -/
theorem etaPathLamRowContractionToBespokeEta {scope : Nat}
    (introPayload : etaPathLamRow.introGenerator.payload scope)
    {introChildren :
      RawTermChildren etaPathLamRow.introGenerator.binderShifts scope}
    {core : RawTerm scope}
    (contracts : etaPathLamRow.contractsOn? introChildren = some core) :
    Step.eta
      (.mkGen etaPathLamRow.introGenerator introPayload introChildren)
      core := by
  match introChildren, contracts with
  | .childCons bodyChild .childNil, contracts =>
    have peeled :
        (({ introChildSlot := 0, observerHead := .gen_pathApp, coreSlot := 0
          , binderDepth := 1, freshVarSlots := [1] } :
            EtaObservationSpec).extractCoreFrom?
          (RawTermChildren.childCons bodyChild
            RawTermChildren.childNil)).bind some
        = some core := contracts
    match extractEq :
        ({ introChildSlot := 0, observerHead := .gen_pathApp, coreSlot := 0
         , binderDepth := 1, freshVarSlots := [1] } :
           EtaObservationSpec).extractCoreFrom?
          (RawTermChildren.childCons bodyChild RawTermChildren.childNil) with
    | none =>
        rw [extractEq] at peeled
        exact nomatch peeled
    | some extracted =>
        rw [extractEq] at peeled
        have extractedIsCore : core = extracted :=
          (Option.some.inj (peeled : some extracted = some core)).symm
        subst extractedIsCore
        obtain ⟨observedPayload, observedChildren, lookupEq, freshHolds,
          coreExtract⟩ :=
          EtaObservationSpec.extractCoreFrom?_someInversion _ extractEq
        have bodyShape :
            bodyChild
              = RawTerm.mkGen .gen_pathApp observedPayload
                  observedChildren :=
          Option.some.inj
            (lookupEq :
              some bodyChild
                = some (RawTerm.mkGen .gen_pathApp observedPayload
                    observedChildren))
        subst bodyShape
        match observedChildren, freshHolds, coreExtract with
        | .childCons pathChild (.childCons argumentChild .childNil),
            freshHolds, coreExtract =>
          have argTest :
              ((if argumentChild
                    = RawTerm.mkGen .gen_var ⟨0, Nat.zero_lt_succ scope⟩
                        .childNil then true
                else false)
                && true)
              = true := freshHolds
          by_cases argEq :
              argumentChild
                = RawTerm.mkGen .gen_var ⟨0, Nat.zero_lt_succ scope⟩
                    .childNil
          case neg =>
              rw [if_neg argEq] at argTest
              exact nomatch argTest
          case pos =>
              subst argEq
              have strengthened :
                  RawTerm.strengthenBy? 1 pathChild = some core :=
                coreExtract
              have pathShape : RawTerm.weakenBy 1 core = pathChild :=
                RawTerm.weakenBy_strengthenBy? 1 pathChild core strengthened
              rw [← pathShape]
              exact Step.eta.etaPathLam core

/-- **Pair eta, backward**: BOTH observations invert — the second
through the agreement gate — pinning both projections of the SAME
core. -/
theorem etaPairRowContractionToBespokeEta {scope : Nat}
    (introPayload : etaPairRow.introGenerator.payload scope)
    {introChildren :
      RawTermChildren etaPairRow.introGenerator.binderShifts scope}
    {core : RawTerm scope}
    (contracts : etaPairRow.contractsOn? introChildren = some core) :
    Step.eta (.mkGen etaPairRow.introGenerator introPayload introChildren)
      core := by
  match introChildren, contracts with
  | .childCons fstCell (.childCons sndCell .childNil), contracts =>
    have peeled :
        (({ introChildSlot := 0, observerHead := .gen_fst, coreSlot := 0
          , binderDepth := 0, freshVarSlots := [] } :
            EtaObservationSpec).extractCoreFrom?
          (RawTermChildren.childCons fstCell
            (RawTermChildren.childCons sndCell
              RawTermChildren.childNil))).bind
          (fun candidate =>
            if etaObservationsAgree
                (RawTermChildren.childCons fstCell
                  (RawTermChildren.childCons sndCell
                    RawTermChildren.childNil))
                candidate
                [{ introChildSlot := 1, observerHead := .gen_snd
                 , coreSlot := 0, binderDepth := 0, freshVarSlots := [] }]
              then some candidate
            else none)
        = some core := contracts
    match extractEq :
        ({ introChildSlot := 0, observerHead := .gen_fst, coreSlot := 0
         , binderDepth := 0, freshVarSlots := [] } :
           EtaObservationSpec).extractCoreFrom?
          (RawTermChildren.childCons fstCell
            (RawTermChildren.childCons sndCell RawTermChildren.childNil)) with
    | none =>
        rw [extractEq] at peeled
        exact nomatch peeled
    | some extracted =>
        rw [extractEq] at peeled
        by_cases agreeHolds :
            etaObservationsAgree
              (RawTermChildren.childCons fstCell
                (RawTermChildren.childCons sndCell
                  RawTermChildren.childNil))
              extracted
              [{ introChildSlot := 1, observerHead := .gen_snd
               , coreSlot := 0, binderDepth := 0, freshVarSlots := [] }]
            = true
        case neg =>
            have peeledIf :
                (if etaObservationsAgree
                    (RawTermChildren.childCons fstCell
                      (RawTermChildren.childCons sndCell
                        RawTermChildren.childNil))
                    extracted
                    [{ introChildSlot := 1, observerHead := .gen_snd
                     , coreSlot := 0, binderDepth := 0
                     , freshVarSlots := [] }]
                  = true then some extracted
                else none)
                = some core := peeled
            rw [if_neg agreeHolds] at peeledIf
            exact nomatch peeledIf
        case pos =>
            have peeledIf :
                (if etaObservationsAgree
                    (RawTermChildren.childCons fstCell
                      (RawTermChildren.childCons sndCell
                        RawTermChildren.childNil))
                    extracted
                    [{ introChildSlot := 1, observerHead := .gen_snd
                     , coreSlot := 0, binderDepth := 0
                     , freshVarSlots := [] }]
                  = true then some extracted
                else none)
                = some core := peeled
            rw [if_pos agreeHolds] at peeledIf
            have extractedIsCore : core = extracted :=
              (Option.some.inj peeledIf).symm
            subst extractedIsCore
            -- first observation: the fst cell
            obtain ⟨fstPayload, fstChildren, fstLookup, _fstFresh,
              fstCoreExtract⟩ :=
              EtaObservationSpec.extractCoreFrom?_someInversion _ extractEq
            have fstShape :
                fstCell = RawTerm.mkGen .gen_fst fstPayload fstChildren :=
              Option.some.inj
                (fstLookup :
                  some fstCell
                    = some (RawTerm.mkGen .gen_fst fstPayload fstChildren))
            subst fstShape
            -- second observation: through the agreement gate
            have agreeShaped :
                ((match
                    ({ introChildSlot := 1, observerHead := .gen_snd
                     , coreSlot := 0, binderDepth := 0
                     , freshVarSlots := [] } :
                       EtaObservationSpec).extractCoreFrom?
                      (RawTermChildren.childCons
                        (RawTerm.mkGen .gen_fst fstPayload fstChildren)
                        (RawTermChildren.childCons sndCell
                          RawTermChildren.childNil)) with
                  | some otherCore =>
                      if otherCore = core then true else false
                  | none => false)
                  && true)
                = true := agreeHolds
            match sndExtractEq :
                ({ introChildSlot := 1, observerHead := .gen_snd
                 , coreSlot := 0, binderDepth := 0, freshVarSlots := [] } :
                   EtaObservationSpec).extractCoreFrom?
                  (RawTermChildren.childCons
                    (RawTerm.mkGen .gen_fst fstPayload fstChildren)
                    (RawTermChildren.childCons sndCell
                      RawTermChildren.childNil)) with
            | none =>
                rw [sndExtractEq] at agreeShaped
                exact nomatch agreeShaped
            | some otherCore =>
                rw [sndExtractEq] at agreeShaped
                by_cases otherEq : otherCore = core
                case neg =>
                    have agreeIf :
                        ((if otherCore = core then true else false) && true)
                        = true := agreeShaped
                    rw [if_neg otherEq] at agreeIf
                    exact nomatch agreeIf
                case pos =>
                    have coreIsOther : core = otherCore := otherEq.symm
                    subst coreIsOther
                    obtain ⟨sndPayload, sndChildren, sndLookup, _sndFresh,
                      sndCoreExtract⟩ :=
                      EtaObservationSpec.extractCoreFrom?_someInversion _
                        sndExtractEq
                    have sndShape :
                        sndCell
                          = RawTerm.mkGen .gen_snd sndPayload sndChildren :=
                      Option.some.inj
                        (sndLookup :
                          some sndCell
                            = some (RawTerm.mkGen .gen_snd sndPayload
                                sndChildren))
                    subst sndShape
                    -- both projection arguments ARE the core
                    match fstChildren, fstCoreExtract with
                    | .childCons fstArgument .childNil, fstCoreExtract =>
                      have fstArgIsCore : core = fstArgument :=
                        (Option.some.inj
                          (fstCoreExtract :
                            some fstArgument = some core)).symm
                      subst fstArgIsCore
                      match sndChildren, sndCoreExtract with
                      | .childCons sndArgument .childNil,
                          sndCoreExtract =>
                        have sndArgIsCore : core = sndArgument :=
                          (Option.some.inj
                            (sndCoreExtract :
                              some sndArgument = some core)).symm
                        subst sndArgIsCore
                        exact Step.eta.etaPair core

/-! ## The total root backward -/

/-- **★ Every raw-tier table contraction is the bespoke eta** — 6-way
membership dispatch into the per-row inversions; the typed-tier rows
contradict the raw-tier gate. -/
theorem stepEtaTableRootToBespokeEta {scope : Nat} {rule : EtaRuleDesc}
    (isRow : rule ∈ etaRuleTable)
    (isRawTier : rule.requiresTypedFiring = false)
    (introPayload : rule.introGenerator.payload scope)
    {introChildren :
      RawTermChildren rule.introGenerator.binderShifts scope}
    {core : RawTerm scope}
    (contracts : rule.contractsOn? introChildren = some core) :
    Step.eta (.mkGen rule.introGenerator introPayload introChildren)
      core := by
  cases isRow with
  | head => exact etaLamRowContractionToBespokeEta introPayload contracts
  | tail _ isRow => cases isRow with
    | head => exact etaPairRowContractionToBespokeEta introPayload contracts
    | tail _ isRow => cases isRow with
      | head =>
          exact etaPathLamRowContractionToBespokeEta introPayload contracts
      | tail _ isRow => cases isRow with
        | head => exact Bool.noConfusion isRawTier
        | tail _ isRow => cases isRow with
          | head => exact Bool.noConfusion isRawTier
          | tail _ isRow => cases isRow with
            | head => exact Bool.noConfusion isRawTier
            | tail _ isRow => cases isRow

end FX1Poly.Core
