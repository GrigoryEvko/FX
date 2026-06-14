import FX1Poly.Core.Rewriting.RuleTables.Eta.StepEtaRootTable
import FX1Poly.Typed.Metatheory.SubjectReduction.TableBetaEtaRootSubjectReduction

/-! # TableRootEtaSubjectReductionNative — table-native root-eta subject
reduction, with NO bespoke `Step.eta` construction (TABLE-CANON-ETA
re-base, increment 1)

`HasTypeDescPi.preservedByTableEtaRoot`
(`TableBetaEtaRootSubjectReduction`) is now itself bespoke-construction-free:
it dispatches on the fired `etaRuleTable` row directly — `etaLamRow`
recovers its `RawTerm.etaLamSource` source SHAPE through the bespoke-free
`etaLamRowContraction_sourceShape` and feeds `preservedByEtaLam`;
`etaPairRow` / `etaPathLamRow` are `gen_pair` / `gen_pathLam` headed and
thus grown-untypable (`isUntypableHead_sound`); the five typed-tier rows
contradict the raw-tier gate (`Bool.noConfusion`).  No arm constructs a
`Step.eta` value.

This module therefore no longer carries its own native dispatch: the
`…Native` theorems are now thin delegations to the (now-native) base
versions, kept as a stable name for the existing consumers and the
audit gate.  This severs the module from the bespoke-relation home
`GrownEtaSubjectReduction` (re-base increment).

Zero-axiom: no `sorry`, no `propext`, no `Quot.sound`, no `Classical`,
`native_decide`, `omega`.  Per-declaration audit-gated in
`FX1PolyAudit/AuditTableRootEtaSubjectReductionNative.lean`. -/

namespace FX1Poly.Typed

open FX1Poly.Core

/-- **Table-root-eta subject reduction, bespoke-construction-free**: a
grown typing of a raw-tier root-eta source descends to the contractum at
the SAME classifier.  A thin alias for the now-native
`HasTypeDescPi.preservedByTableEtaRoot`. -/
theorem HasTypeDescPi.preservedByTableEtaRootNative {profile : PolyProfile}
    {scope : Nat} {context : TypingContext profile scope}
    {source target classifier : RawTerm scope}
    (wellFormed : WfContextDescPi context)
    (typed : HasTypeDescPi profile context source classifier)
    (rootStep : StepEtaRootTable source target) :
    HasTypeDescPi profile context target classifier :=
  HasTypeDescPi.preservedByTableEtaRoot wellFormed typed rootStep

/-- **Table beta-eta-root union SR, bespoke-construction-free**: a thin
alias for the now-native `HasTypeDescPi.subjectReductionTableBetaEtaRoot`. -/
theorem HasTypeDescPi.subjectReductionTableBetaEtaRootNative
    {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {subject reduct classifier : RawTerm scope}
    (wellFormed : WfContextDescPi context)
    (typed : HasTypeDescPi profile context subject classifier)
    (unionStep : StepTableBetaEtaRoot subject reduct) :
    HasTypeDescPi profile context reduct classifier :=
  HasTypeDescPi.subjectReductionTableBetaEtaRoot wellFormed typed unionStep

end FX1Poly.Typed
