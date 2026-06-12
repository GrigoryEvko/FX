import FX1Poly.Core.EtaIotaRootTierUnion
import FX1Poly.Core.StepEtaTableSubstitution
import FX1Poly.Typed.TableBetaEtaRootSubjectReduction
import FX1Poly.Typed.GrownWfOpenStronglyNormalizing

/-! # FX1Poly/Typed/TableBetaEtaRootStrongNormalization — ETA-T6
increment 6b: typed SN for the table beta-eta-root union

The SN leg of the table-generic Geuvers chain.  Two compositions:

  * `tableAccOfTyped` — typed iota-table accessibility: the bespoke
    open SN (`stronglyNormalizingOfWfContextDescPi`) transfers to
    `StepTable` by accessibility induction with the typing carried —
    every table step out of a typed subject IS a bespoke step
    (`tableStepToStep`), and the reduct stays typed
    (`subjectReductionTable`), so the bespoke descent simulates the
    table descent hereditarily.
  * `tableBetaEtaRootStronglyNormalizing` — the union SN: the global
    root-tier Geser instance (`accUnionTablesRootEta`, no typing
    needed for the reordering at this tier) applied at the typed
    iota accessibility, with all three canonical certificates
    discharged by their shipped pins.

Zero-axiom: no `sorry`, no `propext`, no `Quot.sound`, no `Classical`,
`native_decide`, `omega`.  Per-declaration audit-gated in
`FX1PolyAudit/AuditTableBetaEtaRootStrongNormalization.lean`. -/

namespace FX1Poly.Typed

open FX1Poly.Core

/-- **Typed iota-table accessibility**: a grown-typed subject in a
well-formed context is `StepTable`-accessible — the bespoke open SN
simulated onto the table relation through the typed adequacy and
subject reduction. -/
theorem HasTypeDescPi.tableAccOfTyped {profile : PolyProfile}
    {scope : Nat} {context : TypingContext profile scope}
    {subject classifier : RawTerm scope}
    (wellFormed : WfContextDescPi context)
    (typed : HasTypeDescPi profile context subject classifier) :
    Acc (fun laterTerm earlierTerm =>
      StepOverTable iotaRuleTable earlierTerm laterTerm) subject := by
  have bespokeAccessible :=
    HasTypeDescPi.stronglyNormalizingOfWfContextDescPi wellFormed typed
  revert typed
  induction bespokeAccessible with
  | intro currentSubject _bespokeInv descendIH =>
    intro typed
    refine Acc.intro currentSubject (fun reduct tableStep => ?_)
    have bespokeStep :=
      HasTypeDescPi.tableStepToStep typed tableStep
    exact descendIH reduct bespokeStep
      (HasTypeDescPi.subjectReductionTable typed wellFormed tableStep)

/-- ★★ **Typed SN for the table beta-eta-root union**: every
grown-typed subject in a well-formed context is accessible for
`StepTable ∪ StepEtaRootTable` — typed iota accessibility through the
global root-tier Geser engine, certificates discharged by the
canonical pins. -/
theorem HasTypeDescPi.tableBetaEtaRootStronglyNormalizing
    {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {subject classifier : RawTerm scope}
    (wellFormed : WfContextDescPi context)
    (typed : HasTypeDescPi profile context subject classifier) :
    Acc (UnionSuccessor (StepTable (scope := scope)) StepEtaRootTable)
      subject :=
  accUnionTablesRootEta iotaRuleTable_isScopeUniform etaRuleTable_isWf
    etaRuleTable_isScopeSafe
    (HasTypeDescPi.tableAccOfTyped wellFormed typed)

end FX1Poly.Typed
