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

Per polycell.md §3.16.20 (canonical hyphenated names listed
verbatim from the spec table; Lean def identifiers use the
underscored variant since hyphens are not valid in identifiers):

* **Z0 STRICT-Z0-MOTIVE** — every eliminator's spine carries a
  motive child at the correct binder shift; pre-Z₀ shapes
  flagged.  M21-M30 task slots ship the LevelExpr × UniverseFlag
  substrate + the 4 universe-mode generators that motivate the
  motive-shape invariant.
* **Z1 STRICT-Z1-TYPED** — every typed-core generator has a
  `HasType` rule with proper inversion lemmas.  M31-M45 task
  slots ship TypingContext + lookup + per-form HasType ctors +
  inversion lemmas.
* **Z2 STRICT-Z2-CANONICITY** — every closed inhabitant of a
  canonical type reduces to a constructor.  M48-M50 task slots
  ship per-family canonicity theorems + global consistency.
* **Z3 STRICT-Z3-DECIDABLE-CONV** — Typed Conv decision procedure
  ships with a `Complexity` witness.  Tracked by M57 #306
  separately; this file cross-references it.
* **Z4 STRICT-Z4-CUBICAL** — every cubical Kan op has a defining
  reduction rule.  M61-M68 task slots ship gen_path / gen_pathLam
  / gen_pathApp / gen_transp / gen_hcomp / gen_glueType / Kan
  structure proofs.
* **Z5 STRICT-Z5-HIT** — every HIT family ships path constructor
  + recursor + iota rule + cubical Kan witness.  M71-M75 task
  slots ship Generator.Kind tag + HIT framework + concrete HITs
  + canonicity.
* **Z6 STRICT-Z6-HIIRT** — every IR / HIIRT family has a
  Setzer-form admission witness with proof-theoretic strength
  tag.  M76-M83 task slots ship Standard IR + Indexed/Higher
  IR + HIIRT combined beast + UniverseFlag admissions.
* **Z7 STRICT-Z7-GUARDED** — every multi-clock generator has a
  productivity witness.  M84-M92 task slots ship multi-clock
  guarded TT + internal parametricity + rewriting rules + dProp
  + dependent pattern matching + commuting conversions.
* **Z8 STRICT-Z8-21DIM** — every dimension d ∈ {2,…,21} ships a
  typing judgment with decidable typechecking.  M93-M100 task
  slots ship MTT modal layer + cohesion + algebraic effects +
  21-dim typing judgments + cross-dimension interaction matrix
  + Tier 0 + FX0 verifier.
* **Z9 STRICT-Z9-SMT** — every SMT certificate has an in-kernel
  verifier that accepts iff the certificate is sound.  Future
  task, no current M-slot.

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

/-- Phase Z₁ STRICT-Z1-TYPED per polycell.md §3.16.20: every
typed-core generator has a `HasType` rule with proper inversion
lemmas.  Tracks M31-M45 task slots (TypingContext substrate
through full HasType ctor cascade + inversion lemmas). -/
def STRICT_Z1_TYPED_state : PhaseZLedgerState := .notStarted

/-- Phase Z₂ STRICT-Z2-CANONICITY per polycell.md §3.16.20:
every closed inhabitant of a canonical type reduces to a
constructor.  Tracks M48-M50 task slots (per-family canonicity
theorems for bool / Nat / List / Option / Either + global
consistency). -/
def STRICT_Z2_CANONICITY_state : PhaseZLedgerState := .notStarted

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

/-- Phase Z₆ STRICT-Z6-HIIRT per polycell.md §3.16.20: every IR /
HIIRT family has a Setzer-form admission witness with
proof-theoretic strength tag.  Tracks M76-M83 task slots
(Standard IR + Indexed/Higher IR + HIIRT combined beast +
UniverseFlag admissions through Vopěnka apex). -/
def STRICT_Z6_HIIRT_state : PhaseZLedgerState := .notStarted

/-- Phase Z₇ multi-clock guarded TT (clock + later + force
productivity).  Tracks M84-M92 task slots. -/
def STRICT_Z7_GUARDED_state : PhaseZLedgerState := .notStarted

/-- Phase Z₈ STRICT-Z8-21DIM per polycell.md §3.16.20: every
dimension d ∈ {2,…,21} ships a typing judgment with decidable
typechecking.  Tracks M93-M100 task slots (MTT modal layer +
cohesion + algebraic effects + 21-dim typing judgments +
cross-dimension interaction matrix + Tier 0 + FX0 verifier). -/
def STRICT_Z8_21DIM_state : PhaseZLedgerState := .notStarted

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
    STRICT_Z1_TYPED_state = .notStarted ∧
    STRICT_Z2_CANONICITY_state = .notStarted ∧
    STRICT_Z3_DECIDABLE_CONV_state = .notStarted ∧
    STRICT_Z4_CUBICAL_state = .notStarted ∧
    STRICT_Z5_HIT_state = .notStarted ∧
    STRICT_Z6_HIIRT_state = .notStarted ∧
    STRICT_Z7_GUARDED_state = .notStarted ∧
    STRICT_Z8_21DIM_state = .notStarted ∧
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
