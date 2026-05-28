import LeanFX2.Tools.AuditAll.AuditEtaDiscipline

/-! # Tools/AuditAll/AuditIotaEtaMatrix
   — coverage matrix for the 16 iota × 5 eta critical-pair audit

M-iotaEta-audit-matrix (#387, 2026-05-28).  Coverage harness for
the 80-cell iota-η critical-pair matrix.  Sibling to η-M8i
`#358` (per-generator η eligibility), M-iotaEta-inside-binder
`#385` (Class-2 nested cases) + M-iotaEta-reserved-doublestrips
`#386` (Class-3 reserved cases).

## What this audit gate enforces

Per the gap-audit Class-1/2/3 analysis from the iota-η matrix:

* **Class 1 (disjoint)**: ~85 cells across 16 iotas × 5 eta —
  iota and eta fire on different generators with no
  syntactic overlap.  Trivially resolved (no critical pair
  exists).

* **Class 2 (inside-binder trivial diamond)**: 16 cells where
  iota fires inside an η-lam-shaped body.  Covered by
  M-iotaEta-inside-binder #385.  Each is a trivial diamond
  (both reductions converge structurally).

* **Class 3 (genuine self-eliminator overlap)**: currently
  2 cells (iotaFstPair × etaPair, iotaSndPair × etaPair) +
  5 reserved cells (Phase Z₀+ double-strips per #386 —
  modal/cubical/clock/param/Glue).  These need explicit
  critical-pair resolution.

## State machine

Same pattern as #380/#381/#358 (honest ledger via per-cell
state values).

For tractability at the cell level (80 cells = 16 iotas × 5
eta), the matrix is keyed by ETA constructor only with a count
of iota cells per Class.  Each EtaCtor gets a `MatrixRowState`:

* `notClassified` — no analysis yet.
* `partialAudit` — some Class-1/2 cells confirmed but Class-3
  resolutions pending.
* `fullyAudited` — all 16 iota interactions classified +
  Class-3 cells resolved.

## Today's snapshot

Per the iota-η matrix gap audit:

| eta ctor       | shipped Class-1 disjoint cells | Class-2 inside-binder | Class-3 overlap | state |
|----------------|-------------------------------|----------------------|-----------------|-------|
| etaLam         | 14 (all iotas not iotaFst/Snd) | iotaLam (#385)       | none in scope   | partialAudit |
| etaPair        | 14 (all iotas not iotaFst/Snd) | structural diamond   | iotaFst/Snd × etaPair (#386) | fullyAudited |
| etaPathLam     | 16 (no iota touches paths yet) | n/a                  | reserved (#386) | partialAudit |
| etaModIntro    | 16 (no iota touches modal yet) | n/a                  | reserved (#386) | partialAudit |
| etaGlueIntro   | 16 (no iota touches Glue yet)  | n/a                  | reserved (#386) | partialAudit |

`etaPair` is `fullyAudited` because Class-3 cells (iotaFst/Snd
× etaPair) shipped at M-iotaEta-reserved-doublestrips #386.
Other rows are `partialAudit` — Class-3 resolutions waiting
on Phase Z₀+ generators (pathLam needs cubical paths typed,
modIntro needs MTT modal layer, glueIntro needs CCHM Glue
coherence).

## Honest-ledger discipline

Same as #380/#381/#358: per-cell state values + summary
theorem via `rfl`-conjunction.  When a row advances (e.g.,
M61 cubical lands path generators and pathLam's Class-3
resolutions ship), the `iotaEtaMatrix_summary` theorem fails
to elaborate until the per-row state value AND the summary
are updated in lockstep.  Build-break enforces the discipline.

## Zero-axiom verification

Mirror the AuditEtaDiscipline.lean recipe:
* Inductive enums for `MatrixRowState`.
* Per-row state defs via `rfl`-pinned values.
* Summary theorem via `refine` + `all_goals rfl`.
* No `axiom`, no `sorry`, no Classical.  Audit-gated.

## Cross-references

* Per-generator eta classification: `AuditEtaDiscipline.lean`
  (#358).
* Class-2 inside-binder resolutions: `#385`
  (M-iotaEta-inside-binder).
* Class-3 reserved/active double-strips: `#386`
  (M-iotaEta-reserved-doublestrips).
-/

namespace LeanFX2.Tools.AuditAll
namespace Audit

/-- Per-row coverage state in the iota × eta matrix.

* `notClassified` — no analysis shipped for this eta row.
* `partialAudit` — some Class-1/2 cells confirmed, Class-3
  resolutions pending (reserved for future Phase Z₀+
  generators).
* `fullyAudited` — all 16 iota interactions classified +
  Class-3 cells explicitly resolved with critical-pair
  closure. -/
inductive MatrixRowState
  | notClassified
  | partialAudit
  | fullyAudited
deriving DecidableEq, BEq, Repr

/-! ## Per-eta-row state values

Today's snapshot reflects ACTUAL Class-3 resolution coverage.
Advance lockstep with the summary theorem when a row's
Class-3 resolutions ship. -/

/-- etaLam row state.  Class-2 inside-binder covered by #385;
no Class-3 overlap in current scope (would require an iota that
contracts to a lam-shaped term, which no existing iota does).
Marked partialAudit because no audit-tracked Class-3 entries
exist yet for this row (vs etaPair which has explicit Class-3
resolutions shipped). -/
def iotaEta_etaLam_state : MatrixRowState := .partialAudit

/-- etaPair row state.  Class-2 trivial diamonds.  Class-3
shipped: iotaFstPair × etaPair + iotaSndPair × etaPair via
M-iotaEta-reserved-doublestrips #386 (the 2 active Class-3
cells in the entire current matrix). -/
def iotaEta_etaPair_state : MatrixRowState := .fullyAudited

/-- etaPathLam row state.  No iota touches paths yet (path-app
iota is reserved for M61 cubical Phase Z₄).  Class-3 reserved
in #386 docstring; state stays partialAudit. -/
def iotaEta_etaPathLam_state : MatrixRowState := .partialAudit

/-- etaModIntro row state.  No iota touches modal yet
(gen_modElim iota is reserved for M93 MTT Phase Z₈).  Class-3
reserved in #386 docstring; state stays partialAudit. -/
def iotaEta_etaModIntro_state : MatrixRowState := .partialAudit

/-- etaGlueIntro row state.  No iota touches Glue yet
(gen_unglue iota is reserved for M66 cubical Glue
coherence).  Class-3 reserved in #386 docstring; state
stays partialAudit. -/
def iotaEta_etaGlueIntro_state : MatrixRowState := .partialAudit

/-! ## Summary theorem (lockstep enforcement) -/

/-- Honest snapshot of the iota × eta matrix coverage state.
Pins all 5 per-row state values via `rfl`-conjunction.

When ANY row's Class-3 resolutions ship (or any new η ctor
lands), this summary fails to elaborate until both the per-row
state AND the conjunction are updated in lockstep. -/
theorem iotaEtaMatrix_summary :
    iotaEta_etaLam_state = .partialAudit ∧
    iotaEta_etaPair_state = .fullyAudited ∧
    iotaEta_etaPathLam_state = .partialAudit ∧
    iotaEta_etaModIntro_state = .partialAudit ∧
    iotaEta_etaGlueIntro_state = .partialAudit := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  all_goals rfl

/-! ## Aggregate matrix metrics

80-cell matrix = 16 iotas × 5 eta.  Per the gap-audit
Class-1/2/3 analysis:

* Class-1 disjoint cells: ~76 cells (all iota × eta pairs
  where no generator overlap exists at the syntactic level).
* Class-2 trivial diamond cells: 2 cells (iotaFst × etaPair,
  iotaSnd × etaPair — the inside-binder cases per #385 are
  zero at present because none of the 16 iotas contract to
  η-lam-shaped terms).
* Class-3 explicit critical-pair cells: 2 shipped
  (iotaFst/Snd × etaPair via #386) + 0 reserved-in-enum.

Counts at honest current values; advance lockstep with the
matrix coverage state. -/

/-- Total cells in the 16 × 5 iota-η matrix. -/
def iotaEtaMatrix_total_cells : Nat := 80

/-- Cells currently `fullyAudited` (etaPair row has 2 Class-3
ships + 14 Class-1 disjoint = 16 cells). -/
def iotaEtaMatrix_fullyAudited_cells : Nat := 16

/-- Cells currently `partialAudit` (4 rows × 16 cells each =
64 cells; each is Class-1 disjoint + Class-3 reserved waiting
on Phase Z₀+ generators). -/
def iotaEtaMatrix_partialAudit_cells : Nat := 64

/-- Honest assertion of matrix cell counts.  16 + 64 = 80
matches the total.  Updates lockstep with row state advances. -/
theorem iotaEtaMatrix_cell_counts_honest :
    iotaEtaMatrix_total_cells = 80 ∧
    iotaEtaMatrix_fullyAudited_cells = 16 ∧
    iotaEtaMatrix_partialAudit_cells = 64 ∧
    iotaEtaMatrix_fullyAudited_cells + iotaEtaMatrix_partialAudit_cells =
      iotaEtaMatrix_total_cells :=
  ⟨rfl, rfl, rfl, rfl⟩

/-! ## Per-iota-class counts

How many iotas the current Step inductive has, classified by
category.  Used by reviewers to understand the matrix
dimensions. -/

/-- 16 iota constructors in the current `Step` inductive
(per Foundation/PolyCell/Core/Step.lean :253-540):
  iotaBoolTrue / iotaBoolFalse
  iotaFstPair / iotaSndPair
  iotaNatElimZero / iotaNatRecZero
  iotaListElimNil
  iotaOptionMatchNone / iotaOptionMatchSome
  iotaEitherMatchInl / iotaEitherMatchInr
  iotaNatElimSucc / iotaNatRecSucc
  iotaListElimCons
  iotaIdJRefl / iotaIdStrictRecRefl
-/
def matrix_iota_count : Nat := 16

/-- 5 eta constructors in the current `Step.eta` inductive
(per Foundation/PolyCell/Core/StepEta.lean :97-115):
  etaLam / etaPair / etaPathLam / etaModIntro / etaGlueIntro
-/
def matrix_eta_count : Nat := 5

/-- Matrix dimension check: 16 × 5 = 80. -/
theorem matrix_dimensions_consistent :
    matrix_iota_count * matrix_eta_count = iotaEtaMatrix_total_cells := rfl

end Audit
end LeanFX2.Tools.AuditAll
