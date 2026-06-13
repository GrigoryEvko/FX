import FX1Poly.Core.StepEtaTableBackward

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

end FX1Poly.Core
