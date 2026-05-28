/-! # Tools/AuditAll/AuditStrictAxes
   — honest STRICT-CS/TC/SO/DF cross-cutting ledger

M-strict-axes-CS-TC-SO-DF (#381, 2026-05-28).  Sibling to
M-phaseZ-strict-gates `#380`'s honest ledger pattern, applied to
the 4 cross-cutting STRICT axes per polycell.md §11.7.5
(lines 7134-7146).

Per Agent 4 of the 5-agent gap audit: "§11.7.5 STRICT-CS /
STRICT-TC / STRICT-SO / STRICT-DF gates — 4 named gates, 0
tasks."  This file closes that gap without shipping passing-
placeholder gates.

## The 4 cross-cutting STRICT axes

Per polycell.md §11.7.5:

* **STRICT-CS** (ConsistencyStrength) — ConsistencyStrength
  monotone through ProfileExtension chain.  Required: every
  profile admission preserves or increases the ConsistencyStrength
  rank (no admission can SECRETLY lower the strength).
  Substrate: `LeanFX2/Foundation/PolyCell/Core/ConsistencyStrength.lean`
  (6-ctor inductive + LE relation + Decidable LE — SCAFFOLDED).

* **STRICT-TC** (TotalityClass) — TotalityClass constraints on
  Generator children, checked at certification time.  Required:
  `certifyRawCellExact?` per-child verification that each child's
  TotalityClass is admissible under the parent's totality
  requirements.
  Substrate: `LeanFX2/Foundation/PolyCell/Core/GeneratorTotalityClass.lean`
  (SCAFFOLDED).

* **STRICT-SO** (SiteOpenness) — SiteOpenness compatibility on
  ProfileExtension admission.  Required: every extension's
  openness profile matches the existing site's; no admission
  can re-open a closed site.
  Substrate: `LeanFX2/Foundation/PolyCell/Core/SiteOpenness.lean`
  (SCAFFOLDED).

* **STRICT-DF** (DecidabilityStatus) — Conservative decidability
  marking.  Required: no Decidable claim ships without a concrete
  decider witness; `isDecidableInProfile?` is the canonical
  query.
  Substrate: NOT YET SHIPPED — task slot exists but no
  `LeanFX2/Foundation/PolyCell/Core/DecidabilityStatus.lean`
  file.

## State machine (same as M-phaseZ-strict-gates #380)

```
notStarted → specOnly → scaffoldShipped → partialShipped → fullyShipped
```

* `notStarted` — no Lean code, no spec section.  Default.
* `specOnly` — polycell.md section exists, no Lean code yet.
* `scaffoldShipped` — type signatures + design markers shipped.
  e.g., `ConsistencyStrength` inductive + LE relation.
* `partialShipped` — some witnesses shipped, not all.  e.g.,
  ConsistencyStrength.monotone_under_extension proved for one
  extension type but not all.
* `fullyShipped` — every required witness + each
  `#assert_no_axioms` clean + cross-cutting smoke corpus passes.

## Honest current states

Today's snapshot reflects ACTUAL file existence + theorem coverage:

| Axis | State | Substrate file |
|------|-------|---------------|
| CS   | scaffoldShipped | ConsistencyStrength.lean (6-ctor + LE) |
| TC   | scaffoldShipped | GeneratorTotalityClass.lean |
| SO   | scaffoldShipped | SiteOpenness.lean |
| DF   | notStarted      | (no file yet) |

All 3 scaffolded axes need monotonicity / compatibility / per-
child theorems to advance to `.partialShipped`.  The DF axis
needs its `DecidabilityStatus` inductive shipped to advance to
`.scaffoldShipped`.

## Forward-compat: advancing an axis

When work ships that advances STRICT-CS (e.g., M97 #346 cross-
dimension interaction matrix lands `ConsistencyStrength.monotone_
through_ProfileExtension`):
1. Update `STRICT_CS_state := .partialShipped`.
2. Update `strictAxes_current_summary` to match.
3. Add `#assert_no_axioms` for the new theorem.
4. Re-run audit.

Failing to update both (1)+(2) breaks the summary's `rfl`-
conjunction.  Build-break enforces lockstep.

## Aggregate metrics

Convenience counts at the bottom for at-a-glance audit reporting.
Today: 3 scaffolded, 1 not-started, 0 fully-shipped.

## Zero-axiom verification

Same shape as `AuditPhaseZ.lean`:
* `StrictAxisLedgerState` inductive (5 states) deriving
  `DecidableEq + BEq + Repr`.
* 4 state defs at honest current values.
* Summary theorem via `refine` + `all_goals rfl`.
* Aggregate count defs + honest count theorem.

No `axiom`, no `sorry`, no Classical.  Audit-gated. -/

namespace LeanFX2.Tools.AuditAll
namespace Audit

/-- Per-axis ledger state for the cross-cutting STRICT axes.

Identical shape to `PhaseZLedgerState` (from `AuditPhaseZ.lean`)
but kept as a SEPARATE inductive to keep audit files independent
and avoid cross-import noise.

Same monotone forward-advance discipline:
* `notStarted → specOnly` when polycell.md section is written.
* `specOnly → scaffoldShipped` when type signatures ship.
* `scaffoldShipped → partialShipped` when some witnesses ship.
* `partialShipped → fullyShipped` when every required witness
  ships + each is `#assert_no_axioms` clean. -/
inductive StrictAxisLedgerState
  | notStarted
  | specOnly
  | scaffoldShipped
  | partialShipped
  | fullyShipped
deriving DecidableEq, BEq, Repr

/-! ## Per-axis current states (honest current snapshot) -/

/-- STRICT-CS: ConsistencyStrength monotone through ProfileExtension.

Substrate file `ConsistencyStrength.lean` ships the 6-ctor
inductive + LE relation + Decidable LE instance.  Monotonicity-
under-extension theorem not yet proved.  Current state:
`.scaffoldShipped` — type machinery exists, headline theorem
pending. -/
def STRICT_CS_state : StrictAxisLedgerState := .scaffoldShipped

/-- STRICT-TC: TotalityClass constraints on Generator children.

Substrate file `GeneratorTotalityClass.lean` ships the inductive
+ predicate machinery.  Per-child verification integrated into
`certifyRawCellExact?` partially.  Full coverage across all
194 generators pending.  Current state: `.scaffoldShipped`. -/
def STRICT_TC_state : StrictAxisLedgerState := .scaffoldShipped

/-- STRICT-SO: SiteOpenness compatibility on ProfileExtension.

Substrate file `SiteOpenness.lean` ships the openness profile
machinery.  Extension-admission compatibility theorem pending.
Current state: `.scaffoldShipped`. -/
def STRICT_SO_state : StrictAxisLedgerState := .scaffoldShipped

/-- STRICT-DF: Conservative decidability marking.

NO substrate file yet.  Task slot pending — DecidabilityStatus
inductive + `isDecidableInProfile?` query.  Cross-references the
STRICT-COMPLEXITY discipline (M58 #307) but tracks a distinct
property (conservative DF marking ≠ explicit complexity bound).
Current state: `.notStarted`. -/
def STRICT_DF_state : StrictAxisLedgerState := .notStarted

/-! ## Honest current summary

Pins all 4 per-axis states via `rfl`-conjunction.  Build-break
enforces lockstep with per-axis state advances. -/

/-- Honest snapshot of the current STRICT-axes cross-cutting
ledger.  Updates lockstep with per-axis state values.

Today: 3 axes at `.scaffoldShipped` (CS/TC/SO — their substrate
inductives exist), 1 axis at `.notStarted` (DF — no
DecidabilityStatus inductive yet).

Advancing ANY axis requires updating both its individual state
value AND this summary's conjunction to match.  Failing to
update both fails the audit build. -/
theorem strictAxes_current_summary :
    STRICT_CS_state = .scaffoldShipped ∧
    STRICT_TC_state = .scaffoldShipped ∧
    STRICT_SO_state = .scaffoldShipped ∧
    STRICT_DF_state = .notStarted := by
  refine ⟨?_, ?_, ?_, ?_⟩
  all_goals rfl

/-! ## Aggregate metrics

Updates lockstep with per-axis state advances. -/

/-- Count of cross-axis gates currently at `.scaffoldShipped`.
Today: 3 (CS/TC/SO). -/
def strictAxes_scaffoldShipped_count : Nat := 3

/-- Count of cross-axis gates currently at `.notStarted`.
Today: 1 (DF). -/
def strictAxes_notStarted_count : Nat := 1

/-- Count of cross-axis gates currently at `.fullyShipped`.
Today: 0.  Advances toward 4 as monotonicity / compatibility /
per-child / DecidabilityStatus theorems all ship. -/
def strictAxes_fullyShipped_count : Nat := 0

/-- Honest assertion: today's counts are 3/1/0
(scaffoldShipped/notStarted/fullyShipped).  Total across all
states = 4 (matches axis count). -/
theorem strictAxes_counts_honest :
    strictAxes_scaffoldShipped_count = 3 ∧
    strictAxes_notStarted_count = 1 ∧
    strictAxes_fullyShipped_count = 0 :=
  ⟨rfl, rfl, rfl⟩

/-- Total axes tracked = sum of all per-state counts = 4. -/
theorem strictAxes_total_count :
    strictAxes_scaffoldShipped_count +
    strictAxes_notStarted_count +
    strictAxes_fullyShipped_count = 4 := rfl

end Audit
end LeanFX2.Tools.AuditAll
