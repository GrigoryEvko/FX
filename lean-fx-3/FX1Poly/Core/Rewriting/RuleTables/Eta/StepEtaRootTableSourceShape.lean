import FX1Poly.Core.Rewriting.RuleTables.Eta.StepEtaTableBackward

/-! # StepEtaRootTableSourceShape — the bespoke-FREE source-shape reader
for the raw-tier root eta rows (TABLE-CANON-ETA re-base, increment 1)

The ETA-T7 canonicality flip declared the table relation
(`StepEtaRootTable` / `StepTableBetaEtaRoot`) canonical, but the typed
subject-reduction leg (`HasTypeDescPi.preservedByTableEtaRoot`) still
*delegated back into* the bespoke `Step.eta` inductive: it converted a
table contraction to a bespoke step via `stepEtaTableRootToBespokeEta`
and then applied the bespoke dispatcher `preservedByEta`.  That keeps
`StepEta.lean` load-bearing and blocks the TABLE-CANON-ETA deletion.

This module supplies the missing bespoke-construction-free brick: a
per-row reader that, from a successful raw-tier `contractsOn?`, recovers
the EXACT raw source SHAPE (`RawTerm.etaLamSource` / `etaPairSource` /
`etaPathLamSource`) as a plain `RawTerm` equation — NEVER constructing a
`Step.eta` value.  The substantive per-shape subject-reduction lemmas
(`HasTypeDescPi.preservedByEtaLam` and the vacuous structural arms) are
already stated over these raw source shapes, so a table-native SR
dispatches straight into them through these equations.

The extraction logic mirrors the shipped backward bridge
(`etaLamRowContractionToBespokeEta` et al.) line-for-line; only the
conclusion changes (a source-shape equation in place of the bespoke
constructor), so it closes by the SAME definitional equalities (Unit
payload structure-eta, `weaken = weakenBy 1`) that make the bridge
typecheck.

Zero-axiom: no `sorry`, no `propext`, no `Quot.sound`, no `Classical`,
`native_decide`, `omega`.  Per-declaration audit-gated in
`FX1PolyAudit/AuditStepEtaRootTableSourceShape.lean`. -/

namespace FX1Poly.Core

/-- **Function-eta source shape, table-native**: a successful `etaLamRow`
raw contraction forces the intro cell into EXACTLY the bespoke
`RawTerm.etaLamSource` shape over the extracted core — recovered as a raw
equation, with NO `Step.eta` constructed. -/
theorem etaLamRowContraction_sourceShape {scope : Nat}
    (introPayload : etaLamRow.introGenerator.payload scope)
    {introChildren :
      RawTermChildren etaLamRow.introGenerator.binderShifts scope}
    {core : RawTerm scope}
    (contracts : etaLamRow.contractsOn? introChildren = some core) :
    ∃ domainAnn : RawTerm scope,
      (RawTerm.mkGen etaLamRow.introGenerator introPayload introChildren)
        = RawTerm.etaLamSource domainAnn core := by
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
              subst functionChild
              exact ⟨domainAnn, rfl⟩

/-- **Path-eta source shape, table-native**: a successful `etaPathLamRow`
raw contraction forces the intro cell into EXACTLY the bespoke
`RawTerm.etaPathLamSource` shape over the extracted core — recovered as a
raw equation, with NO `Step.eta` constructed.  The one-binder twin of
`etaLamRowContraction_sourceShape`. -/
theorem etaPathLamRowContraction_sourceShape {scope : Nat}
    (introPayload : etaPathLamRow.introGenerator.payload scope)
    {introChildren :
      RawTermChildren etaPathLamRow.introGenerator.binderShifts scope}
    {core : RawTerm scope}
    (contracts : etaPathLamRow.contractsOn? introChildren = some core) :
    (RawTerm.mkGen etaPathLamRow.introGenerator introPayload introChildren)
      = RawTerm.etaPathLamSource core := by
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
              subst pathChild
              rfl

/-- **Pair-eta source shape, table-native**: a successful `etaPairRow`
raw contraction forces the intro cell into EXACTLY the bespoke
`RawTerm.etaPairSource` shape over the extracted core — both projections
pin the SAME core — recovered as a raw equation, with NO `Step.eta`
constructed. -/
theorem etaPairRowContraction_sourceShape {scope : Nat}
    (introPayload : etaPairRow.introGenerator.payload scope)
    {introChildren :
      RawTermChildren etaPairRow.introGenerator.binderShifts scope}
    {core : RawTerm scope}
    (contracts : etaPairRow.contractsOn? introChildren = some core) :
    (RawTerm.mkGen etaPairRow.introGenerator introPayload introChildren)
      = RawTerm.etaPairSource core := by
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
                        rfl

/-! ## The total root source-shape dispatcher

Mirrors `stepEtaTableRootToBespokeEta`'s 8-way membership dispatch, but
concludes a RAW SOURCE-SHAPE disjunction — one disjunct per raw-tier row
— instead of a bespoke `Step.eta` value.  The five typed-tier rows
discharge vacuously against the raw-tier gate (`Bool.noConfusion`).  This
is the bespoke-construction-free replacement the native SN/RPO twins read
off. -/

/-- **★ Every raw-tier root-table contraction has a bespoke source
shape** — the table-native counterpart of `stepEtaTableRootToBespokeEta`,
concluding the raw `etaLamSource` / `etaPairSource` / `etaPathLamSource`
equation directly. -/
theorem stepEtaRootTableSourceShape {scope : Nat} {rule : EtaRuleDesc}
    (isRow : rule ∈ etaRuleTable)
    (isRawTier : rule.requiresTypedFiring = false)
    (introPayload : rule.introGenerator.payload scope)
    {introChildren :
      RawTermChildren rule.introGenerator.binderShifts scope}
    {core : RawTerm scope}
    (contracts : rule.contractsOn? introChildren = some core) :
    (∃ domainAnn : RawTerm scope,
        (RawTerm.mkGen rule.introGenerator introPayload introChildren)
          = RawTerm.etaLamSource domainAnn core)
      ∨ (RawTerm.mkGen rule.introGenerator introPayload introChildren)
          = RawTerm.etaPairSource core
      ∨ (RawTerm.mkGen rule.introGenerator introPayload introChildren)
          = RawTerm.etaPathLamSource core := by
  cases isRow with
  | head =>
      exact Or.inl (etaLamRowContraction_sourceShape introPayload contracts)
  | tail _ isRow => cases isRow with
    | head =>
        exact Or.inr (Or.inl
          (etaPairRowContraction_sourceShape introPayload contracts))
    | tail _ isRow => cases isRow with
      | head =>
          exact Or.inr (Or.inr
            (etaPathLamRowContraction_sourceShape introPayload contracts))
      | tail _ isRow => cases isRow with
        | head => exact Bool.noConfusion isRawTier
        | tail _ isRow => cases isRow with
          | head => exact Bool.noConfusion isRawTier
          | tail _ isRow => cases isRow with
            | head => exact Bool.noConfusion isRawTier
            | tail _ isRow => cases isRow with
              | head => exact Bool.noConfusion isRawTier
              | tail _ isRow => cases isRow with
                | head => exact Bool.noConfusion isRawTier
                | tail _ isRow => cases isRow with
                  | head => exact Bool.noConfusion isRawTier
                  | tail _ isRow => cases isRow

end FX1Poly.Core
