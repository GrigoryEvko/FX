import FX1Poly.Typed.TableBetaEtaRootStrongNormalization
import FX1Poly.Core.UnionStarReflTransBridge

/-! # FX1Poly/Typed/TableBetaEtaRootGuardedConfluence
    — the table beta-eta-root Church-Rosser assembled DIRECTLY via guarded Newman,
      with no bespoke `Step.eta`/`Step.betaEta` round-trip.

`TableBetaEtaRootConfluence` proves the same headline by round-tripping the table union
through the bespoke `Step.betaEta` relation (`unionStarToBetaEtaStar` → the bespoke CR engine
`subjectBetaEtaConfluenceTypedUnconditional` → `betaEtaStarToUnionStar`).  That route keeps the
deletable bespoke `Step.eta` cluster alive.  This module assembles the SAME conclusion natively:
the relation-generic guarded Newman (`newmanGuarded`, `FX1Poly/Core/Newman.lean`) instantiated at

  * `rel  := StepTableBetaEtaRoot` (the canonical table union, defeq the pointwise
    `StepTable ∪ StepEtaRootTable`),
  * `guard := "typed in some classifier in this well-formed context"`.

The three guarded-Newman suppliers are all shipped, native, table-stated:

  * **accessibility** — `tableBetaEtaRootStronglyNormalizing` gives the per-source `Acc`
    (`UnionSuccessor StepTable StepEtaRootTable` is defeq the flipped pointwise union);
  * **hereditary guard** — `subjectReductionTableBetaEtaRoot`: a single table-union step out
    of a typed subject lands typed at the SAME classifier, so the guard discharges hereditarily;
  * **guarded local join** — the table guarded local-join, taken here as an EXPLICIT
    hypothesis (`guardedLocalJoin`) to isolate it; the unconditional discharge (Q1 iota/iota via
    `StepOverTable.canonicalConfluent`, Q2 eta/eta via `StepEtaRootOverTable.deterministic`,
    Q3/Q4 the cross-quadrant eta-lambda/pair/path-lam ports) is the remaining brick.

The `UnionStar`↔`ReflTransClosure` vocabulary bridge (`UnionStarReflTransBridge`) carries the
incoming `UnionStar` chains into the head-form closure `newmanGuarded` consumes and the resulting
`Joinable` back into the `UnionStar` join the kernel's relations speak — so the conclusion shape
matches `tableBetaEtaRootConfluenceTyped` exactly, ready to re-point once the join is discharged.

## Zero-axiom verification

A composition of the shipped zero-axiom guarded-Newman core, the table-union SN/SR pins, and the
two closure transports; no `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`,
`native_decide`, `omega`.  Audit-gated in
`FX1PolyAudit/AuditTableBetaEtaRootConfluence.lean`. -/

namespace FX1Poly.Typed

open FX1Poly.Core

/-- ★ **Guarded-Newman table beta-eta Church-Rosser (local-join-conditional)**: given the table
guarded local join as a hypothesis, any two `UnionStar StepTable StepEtaRootTable` reducts of a
grown-typed subject in a well-formed context join — assembled directly by `newmanGuarded` at the
"typed in context" guard, with NO bespoke `Step.eta`/`Step.betaEta` round-trip.  The single-step
table-union subject reduction discharges the hereditary guard; the table-union SN supplies
accessibility; the `UnionStar`↔`ReflTransClosure` bridge matches the closure vocabularies. -/
theorem HasTypeDescPi.tableBetaEtaRootConfluenceTypedFromLocalJoin
    {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {subject classifier : RawTerm scope}
    (wellFormed : WfContextDescPi context)
    (typed : HasTypeDescPi profile context subject classifier)
    (guardedLocalJoin :
      ∀ {origin leftStep rightStep : RawTerm scope},
        (∃ stepClassifier : RawTerm scope,
          HasTypeDescPi profile context origin stepClassifier) →
        StepTableBetaEtaRoot origin leftStep →
        StepTableBetaEtaRoot origin rightStep →
        Joinable StepTableBetaEtaRoot leftStep rightStep)
    {leftReduct rightReduct : RawTerm scope}
    (toLeft : UnionStar (StepTable (scope := scope)) StepEtaRootTable subject leftReduct)
    (toRight : UnionStar (StepTable (scope := scope)) StepEtaRootTable subject rightReduct) :
    ∃ commonReduct : RawTerm scope,
      UnionStar (StepTable (scope := scope)) StepEtaRootTable leftReduct commonReduct
      ∧ UnionStar (StepTable (scope := scope)) StepEtaRootTable rightReduct commonReduct := by
  have guardHereditary :
      ∀ {origin reduct : RawTerm scope},
        (∃ stepClassifier : RawTerm scope,
          HasTypeDescPi profile context origin stepClassifier) →
        StepTableBetaEtaRoot origin reduct →
        (∃ stepClassifier : RawTerm scope,
          HasTypeDescPi profile context reduct stepClassifier) := by
    intro _origin _reduct guardOrigin unionStep
    obtain ⟨stepClassifier, typedOrigin⟩ := guardOrigin
    exact ⟨stepClassifier,
      HasTypeDescPi.subjectReductionTableBetaEtaRoot wellFormed typedOrigin unionStep⟩
  obtain ⟨commonReduct, leftToCommon, rightToCommon⟩ :=
    newmanGuarded (rel := StepTableBetaEtaRoot)
      (guard := fun term =>
        ∃ stepClassifier : RawTerm scope,
          HasTypeDescPi profile context term stepClassifier)
      guardHereditary guardedLocalJoin
      (HasTypeDescPi.tableBetaEtaRootStronglyNormalizing wellFormed typed)
      ⟨classifier, typed⟩
      toLeft.toReflTransClosure toRight.toReflTransClosure
  exact ⟨commonReduct,
    ReflTransClosure.toUnionStar (reduceLeft := StepTable) (reduceRight := StepEtaRootTable)
      leftToCommon,
    ReflTransClosure.toUnionStar (reduceLeft := StepTable) (reduceRight := StepEtaRootTable)
      rightToCommon⟩

end FX1Poly.Typed
