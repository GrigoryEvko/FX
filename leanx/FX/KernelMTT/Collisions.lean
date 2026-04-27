import FX.KernelMTT.Modality

/-!
# §6.8 collision catalog as missing 2-cells (R0.6)

Encodes the nine primary cross-dimension soundness rules of
`fx_design.md` §6.8 as "collision records" — specifications
of modality compositions that MUST NOT admit a coherent 2-cell
in the mode theory.  Plus three reductions that fall out of
existing infrastructure (linearity + secure-zeroing + effect
lattice).

## R0.6 vs R0.5

  * **R0.5** (`TwoCells.lean`) enumerates the SUBSUMPTION 2-cells
    that EXIST — the edges of the mode theory's 2-category.
  * **R0.6** (this file) enumerates the ABSENT 2-cells — the
    compositions that `fx_reframing.md` §3.6.2 commits to being
    non-coherent.  Under the reframe, these catalog entries
    become "no coherent 2-cell exists for this specific
    composition" rather than hand-stated rejection rules.

The nine records carry the diagnostic error codes `I002`,
`L002`, `E044`, `I003`, `M012`, `P002`, `I004`, `N002`, `L003`
that `fx_design.md` §6.8 declares.  R1.12 will wire these
codes into the MTT diagnostic layer so a composition failure
surfaces as the right error code at the source site.

## Three reductions

Three gap-listed collisions don't get their own error codes
because they REDUCE to existing infrastructure:

  * **gap #103 (session × Fail)** → M011 + `cancel(ch)`
    stdlib primitive.
  * **gap #111 (classified × linear × Fail)** → M011 + §12.7
    secure zeroing.
  * **gap #110 (multiple Fail effects)** → §9.3 effect lattice
    normalizes `Fail(E1) ∨ Fail(E2)` to `Fail(E1 | E2)`.

Encoded here as `Reduction` records so the full collision
landscape is auditable in one file, separate from the
`CollisionRule` records that carry dedicated error codes.

## Scope — descriptive, not operational

R0.6 enumerates.  The ACTUAL detection of these collisions at
elaboration time is:

  * R1.5 (modality application/elimination operations) —
    encodes the basic 2-cell lookup.
  * R1.7 (2-cell subsumption lookup) — wires the collision
    list into the composition check.
  * R1.12 (diagnostic → FX error-code mapping) — emits the
    §6.8 error codes when a collision triggers.

Under the reframe, a composition that would trigger an
R0.6-enumerated rule fails the 2-cell coherence check at
elaboration and produces the declared error code.  The "hand-
stated" §6.8 rules become "composition lacks a coherent 2-cell
matching this pattern."

## Cross-references

  * `fx_design.md` §6.8 — the canonical collision catalog
  * `fx_reframing.md` §3.6.2 — collisions as missing 2-cells
  * `gaps.json` — ids #101–#114 cover the R0.6 entries plus
    the related M011 linear-cleanup obligation (§7.11)
  * `FX/KernelMTT/TwoCells.lean` (R0.5) — the PRESENT 2-cells
-/

namespace FX.KernelMTT

/-- A primary §6.8 collision rule — composition of modality
    grades that the mode theory rejects at elaboration, with
    a dedicated error code surfaced to users.

    `sources` is a list of human-readable descriptions of the
    modality-grade pairs (or term-position shapes) whose
    composition triggers the rule.  Encoded as strings rather
    than typed `(Modality, Grade)` pairs because some
    collisions reference shapes that aren't modality grades
    (P002's "runtime conditional position", N002's "decimal
    type").  The string form keeps the enumeration uniform; R1
    kernel dispatch resolves each string to its operational
    check.

    `refinement` (when `some`) describes what declaration a
    programmer can add to admit the composition — the error
    message's remedy text.  For `none`, the composition is
    always rejected (no refinement admits it). -/
structure CollisionRule where
  /-- Error code from `fx_design.md` §6.8 — e.g., "I002". -/
  errorCode  : String
  /-- Human-readable collision name — e.g., "classified × Fail". -/
  name       : String
  /-- List of modality-grade / term-shape descriptions whose
      composition triggers the rule.  Two or three entries. -/
  sources    : List String
  /-- If `some text`, the refinement that admits the
      composition.  `none` for unconditionally rejected
      compositions. -/
  refinement : Option String
  /-- `gaps.json` reference — e.g., "#102". -/
  gapRef     : String
  /-- `fx_design.md` subsection number — always "§6.8" for
      R0.6 records. -/
  docSection : String
  deriving Repr, Inhabited, DecidableEq

/-- A collision that reduces to existing infrastructure
    rather than getting its own error code.  Three entries
    per `fx_design.md` §6.8 "Composition with ..."
    paragraph. -/
structure Reduction where
  /-- `gaps.json` reference. -/
  gapRef     : String
  /-- Human-readable collision name. -/
  name       : String
  /-- Description of what handles this collision (reduction
      target). -/
  reducesTo  : String
  /-- `fx_design.md` subsection number. -/
  docSection : String
  deriving Repr, Inhabited, DecidableEq

namespace CollisionRule

/-! ## The nine primary collision rules per §6.8 -/

/-- **I002 — classified × Fail** (gap #102).  A Fail site
    producing error values containing classified data must
    declare `Fail(secret E)`; a plain `Fail(E)` with
    classified payload is rejected.  Matches Jif and FlowCaml's
    treatment of exception payloads as information-flow
    sources; FX makes the label explicit in the row. -/
def i002 : CollisionRule :=
  { errorCode  := "I002"
  , name       := "classified × Fail"
  , sources    := [ "◇_sec: classified (on error payload)"
                  , "◇_eff: Fail(E)" ]
  , refinement := some "declare 'Fail(secret E)'"
  , gapRef     := "#102"
  , docSection := "§6.8"
  }

/-- **L002 — borrow × Async** (gap #104).  A `ref` or `ref mut`
    borrow live at an `await(...)` site is rejected — the
    borrow does not live long enough across suspension. -/
def l002 : CollisionRule :=
  { errorCode  := "L002"
  , name       := "borrow × Async"
  , sources    := [ "◇_usage: ref or ref mut"
                  , "◇_eff: Async (at await site)" ]
  , refinement := some "scope the borrow before await, clone via @[copy], or use own"
  , gapRef     := "#104"
  , docSection := "§6.8"
  }

/-- **E044 — CT × Async** (gap #105).  Declaring `with CT,
    Async` on the same function is rejected unconditionally
    — async scheduling introduces observable timing variation
    incompatible with CT's execution-trace-independence
    guarantee. -/
def e044 : CollisionRule :=
  { errorCode  := "E044"
  , name       := "CT × Async"
  , sources    := [ "◇_eff: CT"
                  , "◇_eff: Async" ]
  , refinement := none
  , gapRef     := "#105"
  , docSection := "§6.8"
  }

/-- **I003 — CT × Fail on secret** (gap #106).  Inside a
    `with CT` function, `fail(e)` whose condition (surrounding
    `if` or `match` scrutinee) is classified is rejected —
    dispatching the exception exposes the branch taken, leaking
    the secret. -/
def i003 : CollisionRule :=
  { errorCode  := "I003"
  , name       := "CT × Fail on secret"
  , sources    := [ "◇_eff: CT"
                  , "◇_eff: Fail on secret-dependent condition"
                  , "◇_sec: classified (on fail condition)" ]
  , refinement := some "use ct_select and raise fail outside the secret region"
  , gapRef     := "#106"
  , docSection := "§6.8"
  }

/-- **M012 — monotonic × concurrent** (gap #108).  A
    binding with mutation dimension `monotonic` or
    `append_only` in a non-`single_thread` machine/module
    whose store is not `atomic(T)` is rejected.  LVar and CvRDT
    safety conditions formalize: concurrent monotonic updates
    are race-free only under atomic (scalars) or
    commutative/associative/idempotent merge (lattice state). -/
def m012 : CollisionRule :=
  { errorCode  := "M012"
  , name       := "monotonic × concurrent"
  , sources    := [ "◇_mutation: monotonic or append_only"
                  , "concurrency: not single_thread"
                  , "store: not atomic(T)" ]
  , refinement := some "use atomic(T) or declare 'concurrency lock_free'"
  , gapRef     := "#108"
  , docSection := "§6.8"
  }

/-- **P002 — ghost × runtime conditional** (gap #109).  A
    ghost-graded value (usage grade 0, erased at codegen) as
    the scrutinee of a runtime `if`, `while`, `match`, pattern
    guard, or array index is rejected — ghost terms have no
    runtime representation to branch on.  F* `GTot`, Idris 2
    multiplicity 0, Agda `@0` all draw the same boundary. -/
def p002 : CollisionRule :=
  { errorCode  := "P002"
  , name       := "ghost × runtime conditional"
  , sources    := [ "◇_usage: 0 (ghost)"
                  , "runtime conditional position (if/while/match/index)" ]
  , refinement := none
  , gapRef     := "#109"
  , docSection := "§6.8"
  }

/-- **I004 — classified × async × session** (gap #112).
    Sending a classified value over a session channel from a
    `with Async` context without `with CT` and without a
    `declassify` at the send point is rejected — well-typed
    session code can leak protocol state via send latency when
    the data is secret. -/
def i004 : CollisionRule :=
  { errorCode  := "I004"
  , name       := "classified × async × session"
  , sources    := [ "◇_sec: classified (on send payload)"
                  , "◇_eff: Async (surrounding context)"
                  , "◇_protocol: Send (session channel state)" ]
  , refinement := some "synchronous CT region at the send, OR declassify at boundary"
  , gapRef     := "#112"
  , docSection := "§6.8"
  }

/-- **N002 — decimal × overflow(wrap)** (gap #113).  Exact
    decimal types (`decimal`, `dec32`, ..., `dec1024`)
    declaring `with overflow(wrap)` are rejected.  IEEE 754-
    2008 decimal defines trap/round/saturate, not wrap; wrap
    is meaningless for exact decimals. -/
def n002 : CollisionRule :=
  { errorCode  := "N002"
  , name       := "decimal × overflow(wrap)"
  , sources    := [ "type: exact decimal (decimal, dec32..dec1024)"
                  , "◇_overflow: wrap" ]
  , refinement := some "use overflow(trap) or overflow(saturate), or widen to a non-decimal type"
  , gapRef     := "#113"
  , docSection := "§6.8"
  }

/-- **L003 — borrow × unscoped spawn** (gap #114).  An
    unscoped `spawn(closure)` capturing any borrow is rejected.
    `spawn_in(group, closure)` inside `task_group` preserves
    borrow lifetimes via structured concurrency and is
    permitted; bare `spawn` is not. -/
def l003 : CollisionRule :=
  { errorCode  := "L003"
  , name       := "borrow × unscoped spawn"
  , sources    := [ "◇_usage: ref or ref mut (captured)"
                  , "◇_eff: Async (via unscoped spawn)" ]
  , refinement := some "use task_group for scoped spawn, or move ownership into the closure"
  , gapRef     := "#114"
  , docSection := "§6.8"
  }

/-- All nine primary §6.8 collision rules in the order the
    spec introduces them (I002, L002, E044, I003, M012, P002,
    I004, N002, L003). -/
def all : List CollisionRule :=
  [ i002, l002, e044, i003, m012, p002, i004, n002, l003 ]

/-- Lookup a collision rule by its error code.  Returns
    `none` for unknown codes.  Used by R1.12's diagnostic
    mapping layer to resolve an elaboration failure to its
    collision record. -/
def byErrorCode? (code : String) : Option CollisionRule :=
  all.find? fun rule => rule.errorCode == code

/-- Lookup a collision rule by its gap reference.  Returns
    `none` for unknown refs. -/
def byGapRef? (ref : String) : Option CollisionRule :=
  all.find? fun rule => rule.gapRef == ref

end CollisionRule

namespace Reduction

/-! ## The three reductions per §6.8 trailing paragraphs -/

/-- **gap #103: session × Fail**.  Reduces to the §7.11
    G-Linear-Cleanup-On-Fail rule (error M011) plus a new
    stdlib primitive `cancel(ch)`.  Session channels are
    linear; an errdefer registering `cancel(ch)` at the
    channel acquisition site satisfies M011 and propagates a
    `Cancelled` message to the peer per the session type.
    EGV (Fowler-Lindley-Morris-Decova, POPL 2019) semantics. -/
def sessionFail : Reduction :=
  { gapRef     := "#103"
  , name       := "session × Fail"
  , reducesTo  := "G-Linear-Cleanup-On-Fail (M011) + stdlib cancel(ch) primitive (§7.11)"
  , docSection := "§6.8"
  }

/-- **gap #111: classified × linear × Fail**.  Reduces to
    M011 (defer/errdefer for linear) plus §12.7 secure-zeroing
    on drop.  The compiler emits `secure_zero(v); drop(v)`
    automatically when a classified-plus-linear binding leaves
    scope, including via Fail unwinding. -/
def classifiedLinearFail : Reduction :=
  { gapRef     := "#111"
  , name       := "classified × linear × Fail"
  , reducesTo  := "M011 (defer/errdefer linear) + §12.7 secure_zero on drop"
  , docSection := "§6.8"
  }

/-- **gap #110: multiple Fail effects**.  Follows from the
    §9.3 effect lattice: `Fail(E1) \/ Fail(E2) = Fail(E1 | E2)`.
    A single source-level signature must name one `Fail(T)`
    with a single (possibly union) error type; composition
    across call sites normalizes via the lattice.  E045 rejects
    multiple `Fail` terms in the same explicit annotation. -/
def multipleFail : Reduction :=
  { gapRef     := "#110"
  , name       := "multiple Fail effects"
  , reducesTo  := "§9.3 effect lattice Fail(E1) \\/ Fail(E2) = Fail(E1 | E2)"
  , docSection := "§6.8"
  }

/-- All three §6.8 reductions in the order the spec groups
    them (session × Fail, classified × linear × Fail, multiple
    Fail). -/
def all : List Reduction :=
  [ sessionFail, classifiedLinearFail, multipleFail ]

/-- Lookup a reduction record by its gap reference.  Returns
    `none` for unknown refs. -/
def byGapRef? (ref : String) : Option Reduction :=
  all.find? fun red => red.gapRef == ref

end Reduction

/-! ## Aggregate catalog pinning theorems

The combined collision landscape: 9 primary rules + 3
reductions = 12 §6.8 entries. -/

namespace CollisionCatalog

/-- Total §6.8 entries — 9 primary + 3 reductions. -/
def totalEntryCount : Nat :=
  CollisionRule.all.length + Reduction.all.length

/-- Exactly 9 primary §6.8 rules per `fx_design.md`. -/
theorem primary_count : CollisionRule.all.length = 9 := by decide

/-- Exactly 3 reductions per §6.8. -/
theorem reduction_count : Reduction.all.length = 3 := by decide

/-- Exactly 12 total §6.8 entries. -/
theorem total_entry_count : totalEntryCount = 12 := by decide

/-- Every primary rule has a unique error code — no
    duplicates in the enumeration.  Pinned via List.Nodup. -/
theorem error_codes_distinct :
    (CollisionRule.all.map (·.errorCode)) =
      [ "I002", "L002", "E044", "I003", "M012"
      , "P002", "I004", "N002", "L003" ] := by
  decide

/-- Every primary rule's gap reference is in the #102-#114
    range.  Pin the exact gap refs so future renumbering
    surfaces. -/
theorem gap_refs_match_spec :
    (CollisionRule.all.map (·.gapRef)) =
      [ "#102", "#104", "#105", "#106", "#108"
      , "#109", "#112", "#113", "#114" ] := by
  decide

/-- Every reduction's gap reference. -/
theorem reduction_gap_refs :
    (Reduction.all.map (·.gapRef)) =
      [ "#103", "#111", "#110" ] := by
  decide

/-! ### Classification counts

Among the 9 primary rules:

  * **Unconditional rejections** (no refinement admits):
    E044, P002.
  * **Conditional** (some refinement admits): the remaining 7
    (I002, L002, I003, M012, I004, N002, L003).
-/

/-- Exactly 2 unconditional-rejection rules (E044, P002). -/
theorem unconditional_count :
    (CollisionRule.all.filter
      (fun rule => rule.refinement.isNone)).length = 2 := by
  decide

/-- Exactly 7 conditional rules — every other rule admits
    a refinement remedy. -/
theorem conditional_count :
    (CollisionRule.all.filter
      (fun rule => rule.refinement.isSome)).length = 7 := by
  decide

/-! ### Source-count distribution

Most §6.8 collisions are 2-way (two sources); three are 3-way
(I003 CT×Fail-on-secret, I004 classified×async×session, M012
monotonic×concurrent-without-atomic).  Pin the counts.
-/

/-- Exactly 6 two-source rules (I002, L002, E044, P002, N002, L003). -/
theorem two_source_count :
    (CollisionRule.all.filter
      (fun rule => rule.sources.length = 2)).length = 6 := by
  decide

/-- Exactly 3 three-source rules (I003, M012, I004). -/
theorem three_source_count :
    (CollisionRule.all.filter
      (fun rule => rule.sources.length = 3)).length = 3 := by
  decide

/-! ### Lookup agreement

Every declared error code resolves via `byErrorCode?`; every
gap reference resolves via `byGapRef?` (both across rules and
reductions).  Lookup consistency pins the indexing
functions. -/

/-- All 9 error codes resolve. -/
theorem all_codes_resolve :
    CollisionRule.all.all
      (fun rule => (CollisionRule.byErrorCode? rule.errorCode).isSome) = true := by
  decide

/-- All 9 primary gap refs resolve via `byGapRef?`. -/
theorem all_primary_gaps_resolve :
    CollisionRule.all.all
      (fun rule => (CollisionRule.byGapRef? rule.gapRef).isSome) = true := by
  decide

/-- All 3 reduction gap refs resolve via `byGapRef?`. -/
theorem all_reduction_gaps_resolve :
    Reduction.all.all
      (fun red => (Reduction.byGapRef? red.gapRef).isSome) = true := by
  decide

/-- Primary and reduction gap-ref namespaces are disjoint —
    a primary rule's gap isn't found as a reduction and vice
    versa.  Catches accidental classification drift. -/
theorem primary_gaps_not_reductions :
    CollisionRule.all.all
      (fun rule => (Reduction.byGapRef? rule.gapRef).isNone) = true := by
  decide

theorem reduction_gaps_not_primary :
    Reduction.all.all
      (fun red => (CollisionRule.byErrorCode? red.gapRef).isNone
                    && (CollisionRule.byGapRef? red.gapRef).isNone) = true := by
  decide

end CollisionCatalog

end FX.KernelMTT
