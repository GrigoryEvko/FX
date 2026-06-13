import FX1Poly.Typed.GrownEtaShapePreservation
import FX1Poly.Core.StepEtaCriticalPairs

/-! # FX1Poly/Typed/GrownEtaSubjectReduction — the bespoke-`Step.eta`
relation dispatchers for grown η subject reduction (PAR-2)

The substantive shape-stated arms (`preservedByEtaLam` + the four vacuous
structural arms + the round-trip regression) now live in the
bespoke-import-free `GrownEtaShapePreservation`; they are stated over the
η-source SHAPES and never mention the bespoke `Step.eta` inductive, so the
keep-set (the table-native subject reduction) depends on them directly.

This file holds the arms that genuinely CASE on the bespoke `Step.eta` /
`Step.betaEta` relation — `preservedByEtaLamStep`, the `preservedByEta`
dispatcher, and the `subjectReductionBetaEta(Star)` masters — together with
the import of the bespoke critical-pair substrate.  These belong to the
bespoke-relation home slated for the TABLE-CANON-ETA retirement: once the
last keep-set consumer routes through the table relation, this file goes
with the bespoke `Step.eta` cluster.

## Zero-axiom verification

Every ingredient is a shipped zero-axiom brick; the composition adds none.  No `axiom`, `sorry`,
`propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Audit-gated in
`FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe FX1Poly.Foundation

/-- The arm restated against the `Step.eta` constructor: any `etaLam` contraction instance
preserves grown typing in a well-formed context. -/
theorem HasTypeDescPi.preservedByEtaLamStep {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {domainAnn innerFunction : RawTerm scope} {classifier : RawTerm scope}
    (wellFormed : WfContextDescPi context)
    (typed : HasTypeDescPi profile context
      (RawTerm.etaLamSource domainAnn innerFunction) classifier)
    (_contracts : Step.eta (RawTerm.etaLamSource domainAnn innerFunction) innerFunction) :
    HasTypeDescPi profile context innerFunction classifier :=
  HasTypeDescPi.preservedByEtaLam wellFormed typed

/-- **η subject reduction, assembled**: grown typing in a well-formed context is preserved by
EVERY `Step.eta` contraction — the substantive λ-arm plus the four (currently vacuous)
structural arms. -/
theorem HasTypeDescPi.preservedByEta {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {source contractum classifier : RawTerm scope}
    (wellFormed : WfContextDescPi context)
    (typed : HasTypeDescPi profile context source classifier)
    (contracts : Step.eta source contractum) :
    HasTypeDescPi profile context contractum classifier := by
  cases contracts with
  | etaLam domainAnn innerFunction =>
      exact HasTypeDescPi.preservedByEtaLam wellFormed typed
  | etaPair pairTerm =>
      exact HasTypeDescPi.preservedByEtaPair typed
  | etaPathLam innerPath =>
      exact HasTypeDescPi.preservedByEtaPathLam typed
  | etaModIntro modalTerm =>
      exact HasTypeDescPi.preservedByEtaModIntro typed
  | etaGlueIntro gluedTerm =>
      exact HasTypeDescPi.preservedByEtaGlueIntro typed

/-- ★ **The grown βη master subject reduction (PAR-2)**: grown typing in a well-formed context
is preserved by every `Step.betaEta` step — the shipped β/ι master (`subjectReduction`, SR-U4)
on the `Step` side, the η dispatcher on the `Step.eta` side. -/
theorem HasTypeDescPi.subjectReductionBetaEta {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {subject reduct classifier : RawTerm scope}
    (wellFormed : WfContextDescPi context)
    (typed : HasTypeDescPi profile context subject classifier)
    (steps : Step.betaEta subject reduct) :
    HasTypeDescPi profile context reduct classifier := by
  cases steps with
  | inl betaStep => exact HasTypeDescPi.subjectReduction typed wellFormed reduct betaStep
  | inr etaStep => exact HasTypeDescPi.preservedByEta wellFormed typed etaStep

/-- **The βη star version**: grown typing is preserved along any `Step.betaEtaStar` chain. -/
theorem HasTypeDescPi.subjectReductionBetaEtaStar {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {subject reduct classifier : RawTerm scope}
    (wellFormed : WfContextDescPi context)
    (typed : HasTypeDescPi profile context subject classifier)
    (chain : Step.betaEtaStar subject reduct) :
    HasTypeDescPi profile context reduct classifier := by
  induction chain with
  | refl _ => exact typed
  | trans firstStep _restChain chainIH =>
      exact chainIH (HasTypeDescPi.subjectReductionBetaEta wellFormed typed firstStep)

end FX1Poly.Typed
