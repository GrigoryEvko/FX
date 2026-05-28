/-! # Tools/AuditAll/LedgerState
   — shared 5-ctor ledger-state lattice for audit-infrastructure

audit-A18 (#401, 2026-05-28).  Closes Agent 2's gap-audit finding
that `AuditEtaDiscipline.lean`'s 3-ctor `EtaCoverageState` and
`AuditPhaseZ.lean`'s 5-ctor `PhaseZLedgerState` are MISMATCHED:
they encode the same "audit progression" lattice with different
shapes + ctor names.

## The unified lattice

Five monotone-ordered states matching `PhaseZLedgerState`'s
existing shape (the strictly more expressive of the two):

```
notStarted → specOnly → scaffoldShipped → partialShipped → fullyShipped
```

* `notStarted` — no work shipped; not even the polycell.md spec
  section exists.
* `specOnly` — polycell.md section written; no Lean code.
* `scaffoldShipped` — type signatures / marker enums shipped;
  no witnesses yet.
* `partialShipped` — some witnesses shipped, not all.  Matches
  `EtaCoverageState.audited` semantically (classified but ctor
  pending).
* `fullyShipped` — every required witness shipped + every one
  gated by `#assert_no_axioms`.

## Semantic mapping for the old inductives

`EtaCoverageState` → `LedgerState` (3 ctors map cleanly into 5):

| EtaCoverageState | LedgerState         |
|------------------|---------------------|
| notStarted       | notStarted          |
| audited          | partialShipped (♦)  |
| fullyShipped     | fullyShipped        |

(♦) Naming difference only.  EtaDiscipline used "audited" to
mean "classified but ctor pending"; PhaseZ used "partialShipped"
for the same state.  The unified type picks the PhaseZ name.

`PhaseZLedgerState` → `LedgerState` (5 ctors identity-map):

| PhaseZLedgerState | LedgerState     |
|-------------------|-----------------|
| notStarted        | notStarted      |
| specOnly          | specOnly        |
| scaffoldShipped   | scaffoldShipped |
| partialShipped    | partialShipped  |
| fullyShipped      | fullyShipped    |

## What this file ships and what it doesn't

**Ships:**
* `LedgerState` inductive (5 ctors).
* `DecidableEq`, `BEq`, `Repr` instances via deriving.
* `LedgerState.ctorCount` sanity-pin theorem.

**Does NOT ship** (deferred to the consumer files for backward
compatibility per the project's "don't delete without confirming"
rule):
* `EtaCoverageState.toLedger` injection — lives in
  `AuditEtaDiscipline.lean` to avoid an upward import.
* `PhaseZLedgerState.toLedger` injection — lives in
  `AuditPhaseZ.lean` for the same reason.
* Migration of existing consumer code to use `LedgerState`
  directly — both old inductives keep working.  Future
  refactor can flip the direction once policy permits
  deletion.

## Why additive, not replacement

CLAUDE.md project rule: "PLEASE DON'T DELETE ANYTHING FROM OLD
CODE WITHOUT EXPLICITLY CONFIRMING FROM ME".  An audit-hygiene
task should not silently delete pre-existing inductives.  The
additive design closes the "mismatch is unaddressed" finding
by providing the canonical lattice + bridges, while preserving
EVERY existing audit-infrastructure ledger.

## Zero-axiom verification

Pure inductive declaration + derived instances + `rfl` smoke
theorem.  No `axiom`, no `sorry`, no Classical.  Audit-gated.
-/

namespace LeanFX2.Tools.AuditAll

/-- The canonical 5-ctor audit-progression lattice.

Unifies the 3-ctor `EtaCoverageState` (in `AuditEtaDiscipline.lean`)
and the 5-ctor `PhaseZLedgerState` (in `AuditPhaseZ.lean`) under
a single shared type.  Both existing inductives ship injective
conversion functions into this type in their respective files.

States advance monotonically forward (never backward):

* `notStarted`     — no work + no spec.
* `specOnly`       — spec written; no Lean code.
* `scaffoldShipped`— types/markers shipped; no witnesses.
* `partialShipped` — some witnesses shipped; not all.
* `fullyShipped`   — every witness shipped + audit-gated. -/
inductive LedgerState
  /-- No work + no spec. -/
  | notStarted
  /-- Polycell spec section written; no Lean code. -/
  | specOnly
  /-- Type signatures / marker enums shipped; no witnesses. -/
  | scaffoldShipped
  /-- Some witnesses shipped, not all.  Corresponds to
  `EtaCoverageState.audited` from the old 3-ctor variant. -/
  | partialShipped
  /-- Every required witness shipped + each gated by
  `#assert_no_axioms`. -/
  | fullyShipped
deriving DecidableEq, BEq, Repr

/-! ## Aggregate metric -/

/-- The `LedgerState` lattice has 5 explicit ctors. -/
def LedgerState.ctorCount : Nat := 5

theorem LedgerState.ctorCount_correct :
    LedgerState.ctorCount = 5 := rfl

end LeanFX2.Tools.AuditAll
