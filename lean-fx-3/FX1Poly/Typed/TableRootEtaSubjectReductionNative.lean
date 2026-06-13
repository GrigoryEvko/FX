import FX1Poly.Core.StepEtaRootTableSourceShape
import FX1Poly.Core.StepEtaRootTable
import FX1Poly.Typed.GrownEtaSubjectReduction
import FX1Poly.Typed.TableBetaEtaRootSubjectReduction

/-! # TableRootEtaSubjectReductionNative — table-native root-eta subject
reduction, with NO bespoke `Step.eta` construction (TABLE-CANON-ETA
re-base, increment 1)

The shipped `HasTypeDescPi.preservedByTableEtaRoot`
(`TableBetaEtaRootSubjectReduction`) proves table-root-eta SR by
*delegating into* the bespoke `Step.eta` inductive: it converts the
table contraction to a `Step.eta` via `stepEtaTableRootToBespokeEta`
and applies the bespoke dispatcher `preservedByEta`.  That delegation
keeps `StepEta.lean` load-bearing for the canonical relation and blocks
the bespoke-eta deletion.

This module re-bases that SR leg.  `preservedByTableEtaRootNative`
dispatches on the fired row directly:

  * `etaLamRow` (the only substantive raw-tier row) — recover the
    `RawTerm.etaLamSource` source SHAPE through the bespoke-free
    `etaLamRowContraction_sourceShape` and feed the raw-shape-stated
    `HasTypeDescPi.preservedByEtaLam`;
  * `etaPairRow` / `etaPathLamRow` — the source is `gen_pair` /
    `gen_pathLam` headed, both `isUntypableHead = true`, so a grown
    typing of the source is impossible (`isUntypableHead_sound`);
  * the five typed-tier rows contradict the raw-tier gate
    (`Bool.noConfusion`).

No arm constructs a `Step.eta` value — the canonical table relation's
SR no longer references the bespoke inductive's CONSTRUCTORS.  (The
substantive `preservedByEtaLam` still lives in `GrownEtaSubjectReduction`
alongside the bespoke dispatcher; relocating it to a bespoke-import-free
home is re-base increment 2.)

Zero-axiom: no `sorry`, no `propext`, no `Quot.sound`, no `Classical`,
`native_decide`, `omega`.  Per-declaration audit-gated in
`FX1PolyAudit/AuditTableRootEtaSubjectReductionNative.lean`. -/

namespace FX1Poly.Typed

open FX1Poly.Core

/-- **Table-root-eta subject reduction, bespoke-construction-free**: a
grown typing of a raw-tier root-eta source descends to the contractum at
the SAME classifier, dispatching on the fired `etaRuleTable` row WITHOUT
building any `Step.eta`. -/
theorem HasTypeDescPi.preservedByTableEtaRootNative {profile : PolyProfile}
    {scope : Nat} {context : TypingContext profile scope}
    {source target classifier : RawTerm scope}
    (wellFormed : WfContextDescPi context)
    (typed : HasTypeDescPi profile context source classifier)
    (rootStep : StepEtaRootTable source target) :
    HasTypeDescPi profile context target classifier := by
  cases rootStep with
  | etaRedex isRow isRawTier introPayload contracts =>
      cases isRow with
      | head =>
          obtain ⟨domainAnn, sourceShape⟩ :=
            etaLamRowContraction_sourceShape introPayload contracts
          rw [sourceShape] at typed
          exact HasTypeDescPi.preservedByEtaLam wellFormed typed
      | tail _ isRow => cases isRow with
        | head => exact (isUntypableHead_sound rfl typed).elim
        | tail _ isRow => cases isRow with
          | head => exact (isUntypableHead_sound rfl typed).elim
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

/-- **Table beta-eta-root union SR, bespoke-construction-free**: the
table iota side uses the T9 flip's `subjectReductionTable`; the
root-eta side uses the native dispatch above.  The drop-in replacement
for `HasTypeDescPi.subjectReductionTableBetaEtaRoot` that does not route
through `Step.eta`. -/
theorem HasTypeDescPi.subjectReductionTableBetaEtaRootNative
    {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {subject reduct classifier : RawTerm scope}
    (wellFormed : WfContextDescPi context)
    (typed : HasTypeDescPi profile context subject classifier)
    (unionStep : StepTableBetaEtaRoot subject reduct) :
    HasTypeDescPi profile context reduct classifier := by
  cases unionStep with
  | inl tableStep =>
      exact HasTypeDescPi.subjectReductionTable typed wellFormed tableStep
  | inr rootEtaStep =>
      exact HasTypeDescPi.preservedByTableEtaRootNative wellFormed typed
        rootEtaStep

end FX1Poly.Typed
