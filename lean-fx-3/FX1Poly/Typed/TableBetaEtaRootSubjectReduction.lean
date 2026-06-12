import FX1Poly.Core.StepEtaRootTable
import FX1Poly.Core.StepEtaTableBackward
import FX1Poly.Core.StrongNormalizationUnion
import FX1Poly.Typed.TypedFragmentTableAdequacy
import FX1Poly.Typed.GrownEtaSubjectReduction

/-! # FX1Poly/Typed/TableBetaEtaRootSubjectReduction — ETA-T6
increment 5b: typed SR for the table beta-eta-root union

The table twin of the bespoke `Step.betaEta` (= `Step ∨ Step.eta`,
root-only eta) is `StepTable ∨ StepEtaRootTable`.  Its typed subject
reduction composes shipped bricks: the iota side is the T9 flip's
typed leg (`subjectReductionTable`); the root-eta side transfers
through the ETA-T1 backward adequacy (`stepEtaTableRootToBespokeEta`
— every raw-tier table contraction IS a bespoke `Step.eta`) into the
bespoke eta-SR dispatcher (`preservedByEta`).  Both sides preserve
the EXACT classifier, so the union and its star do too.

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
— the ETA-T1 backward adequacy composed with the bespoke eta-SR
dispatcher. -/
theorem HasTypeDescPi.preservedByTableEtaRoot {profile : PolyProfile}
    {scope : Nat} {context : TypingContext profile scope}
    {source target classifier : RawTerm scope}
    (wellFormed : WfContextDescPi context)
    (typed : HasTypeDescPi profile context source classifier)
    (rootStep : StepEtaRootTable source target) :
    HasTypeDescPi profile context target classifier := by
  cases rootStep with
  | etaRedex isRow isRawTier introPayload contracts =>
      exact HasTypeDescPi.preservedByEta wellFormed typed
        (stepEtaTableRootToBespokeEta isRow isRawTier introPayload
          contracts)

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
