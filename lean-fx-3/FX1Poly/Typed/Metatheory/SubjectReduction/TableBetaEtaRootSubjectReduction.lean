import FX1Poly.Core.Rewriting.RuleTables.Eta.StepEtaRootTable
import FX1Poly.Core.Rewriting.RuleTables.Eta.StepEtaRootTableSourceShape
import FX1Poly.Core.Metatheory.Normalization.StrongNorm.StrongNormalizationUnion
import FX1Poly.Typed.Corpus.Smoke.TypedFragmentTableAdequacy
import FX1Poly.Typed.Equality.Eta.GrownEtaShapePreservation

/-! # FX1Poly/Typed/TableBetaEtaRootSubjectReduction — ETA-T6
increment 5b: typed SR for the table beta-eta-root union

The table twin of the bespoke `Step.betaEta` (= `Step ∨ Step.eta`,
root-only eta) is `StepTable ∨ StepEtaRootTable`.  Its typed subject
reduction composes shipped bricks: the iota side is the T9 flip's
typed leg (`subjectReductionTable`); the root-eta side dispatches
NATIVELY on the fired `etaRuleTable` row.  `etaLamRow` (the only
substantive raw-tier row) recovers its `RawTerm.etaLamSource` source
SHAPE through the bespoke-construction-free `etaLamRowContraction_sourceShape`
and feeds the raw-shape-stated `preservedByEtaLam` (housed in the
bespoke-import-free `GrownEtaShapePreservation`); `etaPairRow` /
`etaPathLamRow` are `gen_pair` / `gen_pathLam` headed — both
`isUntypableHead = true`, so a grown typing of the source is impossible
(`isUntypableHead_sound`); the five typed-tier rows contradict the
raw-tier gate (`Bool.noConfusion`).  No bespoke `Step.eta` value is
ever constructed, so this SR leg no longer depends on the
bespoke-relation home `GrownEtaSubjectReduction` (TABLE-CANON-ETA
re-base).  Both sides preserve the EXACT classifier, so the union and
its star do too.

This is the SR leg of the (d) plan: with eta SN (ETA-T3, the root
tier is a sub-relation), the quadrant-1 quasi-commutation (root-eta
over iota, GLOBAL — no typing needed at the root tier), and this SR,
the typed union SN and the Newman-route CR follow downstream.

Zero-axiom: no `sorry`, no `propext`, no `Quot.sound`, no `Classical`,
`native_decide`, `omega`.  Per-declaration audit-gated in
`FX1PolyAudit/AuditTableBetaEtaRootSubjectReduction.lean`. -/

namespace FX1Poly.Typed

open FX1Poly.Core

/-- The canonical table beta-eta-root union: a full-congruence table
iota step, or a root table eta contraction. -/
def StepTableBetaEtaRoot {scope : Nat}
    (source target : RawTerm scope) : Prop :=
  StepTable source target ∨ StepEtaRootTable source target

/-- **Root table eta preserves grown typing at the same classifier**
— native dispatch on the fired `etaRuleTable` row: `etaLamRow` recovers
its source SHAPE through the bespoke-construction-free
`etaLamRowContraction_sourceShape` and feeds `preservedByEtaLam`;
`etaPairRow` / `etaPathLamRow` sources are grown-untypable-headed
(`isUntypableHead_sound`); the five typed-tier rows contradict the
raw-tier gate (`Bool.noConfusion`).  No `Step.eta` is ever built. -/
theorem HasTypeDescPi.preservedByTableEtaRoot {profile : PolyProfile}
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

/-- ★ **Typed SR for the table beta-eta-root union**: grown typing in
a well-formed context is preserved by every union step, at the SAME
classifier. -/
theorem HasTypeDescPi.subjectReductionTableBetaEtaRoot
    {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {subject reduct classifier : RawTerm scope}
    (wellFormed : WfContextDescPi context)
    (typed : HasTypeDescPi profile context subject classifier)
    (unionStep : StepTableBetaEtaRoot subject reduct) :
    HasTypeDescPi profile context reduct classifier := by
  cases unionStep with
  | inl tableStep =>
      exact HasTypeDescPi.subjectReductionTable typed wellFormed
        tableStep
  | inr rootEtaStep =>
      exact HasTypeDescPi.preservedByTableEtaRoot wellFormed typed
        rootEtaStep

/-- The star version, over the T5 union-star vocabulary: grown typing
is preserved along any `UnionStar StepTable StepEtaRootTable` chain. -/
theorem HasTypeDescPi.subjectReductionTableBetaEtaRootStar
    {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {subject reduct classifier : RawTerm scope}
    (wellFormed : WfContextDescPi context)
    (typed : HasTypeDescPi profile context subject classifier)
    (chain : UnionStar (StepTable (scope := scope)) StepEtaRootTable
      subject reduct) :
    HasTypeDescPi profile context reduct classifier := by
  induction chain with
  | refl => exact typed
  | tailLeft _priorStar tableStep priorIH =>
      exact HasTypeDescPi.subjectReductionTable priorIH wellFormed
        tableStep
  | tailRight _priorStar rootEtaStep priorIH =>
      exact HasTypeDescPi.preservedByTableEtaRoot wellFormed priorIH
        rootEtaStep

end FX1Poly.Typed
