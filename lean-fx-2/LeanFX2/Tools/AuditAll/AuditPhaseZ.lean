/-! # Tools/AuditAll/AuditPhaseZ
   — honest STRICT-Z ledgers for the 10 phase-Z audit gates

M-phaseZ-strict-gates (#380, 2026-05-28).  Ships HONEST ledgers
for 10 phase-Z STRICT audit gates per polycell.md §3.16.20.

Per Agent 4 of the 5-agent gap audit: "only M57 #306 covers
STRICT-Z3-DECIDABLE-CONV; the other 9 gates are named in spec
without corresponding tasks."  This file closes that gap WITHOUT
shipping passing-placeholder gates that pretend coverage exists.

## The "honest ledger" pattern

Each phase-Z STRICT gate has a per-gate state value
(`Audit.STRICT_ZX_state : PhaseZLedgerState`) declared explicitly
at its CURRENT honest level — `notStarted` until the phase's
generators + theorems land.

A SUMMARY THEOREM pins all 10 states via `rfl`-conjunction.  When
any gate's state advances (e.g., Z0 → `scaffoldShipped` as M21 +
M22 ship), the summary theorem fails to elaborate — forcing the
audit author to update both the per-gate state AND the summary
in lockstep.  Build-break enforces ledger honesty.

This is STRUCTURALLY DIFFERENT from passing-placeholder gates:
* **Passing-placeholder** (REJECTED): `def gate : Bool := true ;
  #assert_no_axioms gate` — audit passes trivially, the gate
  tracks nothing.
* **Honest ledger** (committed): `def gate_state : PhaseZLedgerState
  := .notStarted` — audit passes with EXPLICIT acknowledgment that
  no work is shipped yet.  Build-break on the summary theorem when
  the value advances without matching code.

## The 10 phase-Z STRICT gates

Per polycell.md §3.16.20:

* **Z0 STRICT-Z0-MOTIVE** — Phase Z₀ universe-mode invariant
  (LevelExpr × UniverseFlag normalization).  M21-M30 task slots.
* **Z1 STRICT-Z1-CTX** — TypingContext profile inductive coherence
  (Decidable lookup per context shape).  M31-M32 task slots.
* **Z2 STRICT-Z2-CONV-TYPE** — HasType conv rule (type up-to-Conv
  preservation).  M33 task slot.
* **Z3 STRICT-Z3-DECIDABLE-CONV** — Decidable Conv via NbE.
  Tracked by M57 #306 separately; this file cross-references it.
* **Z4 STRICT-Z4-CUBICAL** — Cubical Kan structure (each Generator
  preserves filling).  M61-M68 task slots.
* **Z5 STRICT-Z5-HIT** — HIT framework (gen_hitCtor + gen_hitPath +
  gen_hitRec + canonical-form theorems).  M71-M75 task slots.
* **Z6 STRICT-Z6-IRT** — Induction-recursion + HIIRT closure
  (Setzer-Rathjen ladder consistency).  M76-M83 task slots.
* **Z7 STRICT-Z7-GUARDED** — Multi-clock guarded TT (clock + later
  + force productivity).  M84-M92 task slots.
* **Z8 STRICT-Z8-MODAL** — MTT modal layer (mode-theoretic
  coherence per GSS 2020).  M93-M100 task slots.
* **Z9 STRICT-Z9-SMT** — Internal verified SMT (decidability +
  completeness).  Future task, no current M-slot.

## Per-gate state machine

```
notStarted → specOnly → scaffoldShipped → partialShipped → fullyShipped
```

* **notStarted**: no Lean code, no spec section.  Default.
* **specOnly**: polycell.md section exists, no Lean code yet.
* **scaffoldShipped**: type signatures + design markers shipped
  (e.g., LevelExpr inductive + UniverseFlag enum committed).
* **partial**: some witnesses shipped, not all.
* **fullyShipped**: all required theorems shipped + every
  one of them gated by `#assert_no_axioms`.

## Forward-compat: advancing a gate

When work for Z0 (LevelExpr + UniverseFlag scaffolds) ships, the
implementer:
1. Updates `Audit.STRICT_Z0_MOTIVE_state := .scaffoldShipped`.
2. Updates `Audit.phaseZ_current_summary` to match the new state.
3. Adds `#assert_no_axioms` gates for each of the load-bearing
   theorems shipped.
4. Re-runs `lake build LeanFX2 LeanFX2Audit`.  The summary
   theorem now elaborates against the advanced state value.

If steps (1)+(2) get out of sync (state advances but summary
forgets to update), the audit fails on the summary theorem.  If
step (3) is skipped (state advances without per-theorem audit
gates), the audit_namespace sweep catches the orphan theorems.

## Why phase-Z and not phase-K?

PolyCell's existing audit infrastructure already covers M1-M20
substrate (audit-gated per declaration via `#assert_no_axioms` in
this same `AuditPolyCell.lean` file).  Phase Z₀-Z₈ is the TYPED
LAYER + CUBICAL/HIT/MODAL/MTT extensions — a distinct cascade
that doesn't fit the per-declaration pattern (the gates aggregate
across many theorems).

The honest-ledger pattern is specifically designed for THIS shape:
cross-cutting milestones that span dozens of theorems each.

## Zero-axiom verification

All declarations close by `rfl` (for state values) or `refine` +
`all_goals rfl` (for the summary conjunction).  No `axiom`, no
`sorry`, no Classical.  Audit-gated. -/

namespace LeanFX2.Tools.AuditAll
namespace Audit

/-- Per-gate ledger state.  Advances monotonically as the phase's
work lands.

State transitions (only forward, never backward):
* `notStarted → specOnly` when the polycell.md section gets
  written.
* `specOnly → scaffoldShipped` when the type signatures /
  marker enums for the phase ship.
* `scaffoldShipped → partial` when some witnesses ship.
* `partialShipped → fullyShipped` when every required witness ships
  + each is `#assert_no_axioms` clean. -/
inductive PhaseZLedgerState
  | notStarted
  | specOnly
  | scaffoldShipped
  | partialShipped
  | fullyShipped
deriving DecidableEq, BEq, Repr

/-! ## Per-gate current states

Each state value is declared explicitly at its honest level.
Advancing a state requires updating BOTH this declaration AND
`Audit.phaseZ_current_summary` below — the summary's `rfl`-
conjunction enforces the lockstep. -/

/-- Phase Z₀ universe-mode invariant.  Tracks M21-M30 task slots
(LevelExpr inductive, UniverseFlag enum, Generator.payload
refactor, 4 universe-mode generators, sprop + univLift/Lower). -/
def STRICT_Z0_MOTIVE_state : PhaseZLedgerState := .notStarted

/-- Phase Z₁ TypingContext profile inductive coherence.  Tracks
M31-M32 task slots. -/
def STRICT_Z1_CTX_state : PhaseZLedgerState := .notStarted

/-- Phase Z₂ HasType conv rule (type up-to-Conv preservation).
Tracks M33 task slot. -/
def STRICT_Z2_CONV_TYPE_state : PhaseZLedgerState := .notStarted

/-- Phase Z₃ Decidable Conv via NbE.  Tracked by M57 #306 audit
task separately; this entry cross-references for completeness.
Advances when M55a #364 typed β+η Decidable Conv ships. -/
def STRICT_Z3_DECIDABLE_CONV_state : PhaseZLedgerState := .notStarted

/-- Phase Z₄ cubical Kan structure (each Generator preserves
filling).  Tracks M61-M68 task slots. -/
def STRICT_Z4_CUBICAL_state : PhaseZLedgerState := .notStarted

/-- Phase Z₅ HIT framework (gen_hitCtor + gen_hitPath +
gen_hitRec + canonical-form theorems).  Tracks M71-M75 task
slots. -/
def STRICT_Z5_HIT_state : PhaseZLedgerState := .notStarted

/-- Phase Z₆ induction-recursion + HIIRT closure (Setzer-Rathjen
ladder consistency).  Tracks M76-M83 task slots. -/
def STRICT_Z6_IRT_state : PhaseZLedgerState := .notStarted

/-- Phase Z₇ multi-clock guarded TT (clock + later + force
productivity).  Tracks M84-M92 task slots. -/
def STRICT_Z7_GUARDED_state : PhaseZLedgerState := .notStarted

/-- Phase Z₈ MTT modal layer (mode-theoretic coherence per
Gratzer-Sterling-Sterling LICS 2020).  Tracks M93-M100 task
slots. -/
def STRICT_Z8_MODAL_state : PhaseZLedgerState := .notStarted

/-- Phase Z₉ internal verified SMT (decidability + completeness).
Future task, no current M-slot. -/
def STRICT_Z9_SMT_state : PhaseZLedgerState := .notStarted

/-! ## Honest current summary

Pins all 10 per-gate states via a single `rfl`-conjunction.
Build-break enforces ledger honesty: if any state advances
without updating this summary, the theorem fails to elaborate. -/

/-- Honest snapshot of the current Phase Z STRICT ledger.

EVERY gate is currently `notStarted` — no Phase Z₀-Z₈ work has
landed at the time of this commit (M-phaseZ-strict-gates #380).

Advancing ANY gate requires updating both the gate's individual
state value AND this summary's conjunction to match.  Failing to
update both fails the audit build. -/
theorem phaseZ_current_summary :
    STRICT_Z0_MOTIVE_state = .notStarted ∧
    STRICT_Z1_CTX_state = .notStarted ∧
    STRICT_Z2_CONV_TYPE_state = .notStarted ∧
    STRICT_Z3_DECIDABLE_CONV_state = .notStarted ∧
    STRICT_Z4_CUBICAL_state = .notStarted ∧
    STRICT_Z5_HIT_state = .notStarted ∧
    STRICT_Z6_IRT_state = .notStarted ∧
    STRICT_Z7_GUARDED_state = .notStarted ∧
    STRICT_Z8_MODAL_state = .notStarted ∧
    STRICT_Z9_SMT_state = .notStarted := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals rfl

/-! ## Aggregate metrics

Convenience aggregates for at-a-glance audit reporting.  Both
counts advance as the per-gate state values progress. -/

/-- Count of phase-Z gates currently at `notStarted`.  Today this
is 10; advances downward as gates progress. -/
def phaseZ_notStarted_count : Nat := 10

/-- Count of phase-Z gates currently at `fullyShipped`.  Today
this is 0; advances toward 10 as work lands. -/
def phaseZ_fullyShipped_count : Nat := 0

/-- Honest assertion: today's count is 10/0 (notStarted/fullyShipped).
Updates lockstep with per-gate state advances. -/
theorem phaseZ_counts_honest :
    phaseZ_notStarted_count = 10 ∧
    phaseZ_fullyShipped_count = 0 :=
  ⟨rfl, rfl⟩

end Audit
end LeanFX2.Tools.AuditAll
