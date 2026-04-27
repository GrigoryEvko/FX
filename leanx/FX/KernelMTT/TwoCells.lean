import FX.KernelMTT.Modality

/-!
# Subsumption 2-cells (R0.5)

Enumerates the subsumption 2-cells of the FX mode theory per
`fx_reframing.md` §3.6.1.  A 2-cell `α ⇒ β` on a modality `◇_M`
says "a value at grade α of modality M can be used where grade
β is expected" — the categorical encoding of the grade-level
subsumption rule of `fx_design.md` §6.2 (Subsumption).

## Scope

R0.5 enumerates the DIRECT subsumption edges declared in the
spec.  Transitive closure, coherence proofs (2-category law
verification), and the kernel-level dispatch of these cells
are R0.7 / R1.7.

The enumeration is intentionally narrow: only modalities with
an enumerable / finite grade lattice get cells here.  Modalities
with continuous or unbounded grade domains
(`complexity`, `precision`, `space`, `size`, `lifetime`,
`provenance`, `protocol`, `format`, `version`) have their own
subsumption logic handled at the kernel layer and don't
participate in this enumeration.

## Direction convention

`fromGrade ⇒ toGrade` means "`fromGrade` subsumes `toGrade`",
i.e., a value at `fromGrade` satisfies a context expecting
`toGrade`.  This matches `fx_design.md` §6.2's Subsumption
rule: `r ≤ s` allows grade `r` where grade `s` is expected.

Example: `Tot ⇒ IO` means a `Tot` function can be passed where
`IO` is expected (Tot is stronger / more restrictive, so any
code that requires IO already accepts Tot).

## Enumerated modalities (9 of 20)

  * **Usage** — `0 ⇒ 1 ⇒ w`  (three cells covering the
    absent ⇒ linear ⇒ unrestricted chain).
  * **Effect** — `Tot ⇒ {IO, Alloc, Read, Write, Async, Div,
    Exn}` plus `Read ⇒ Write` per `fx_design.md` §9.3.
  * **Security** — `unclassified ⇒ classified`.
  * **Observability** — `opaque ⇒ transparent`.
  * **Trust** — `Verified ⇒ Tested ⇒ Sorry ⇒ Assumed ⇒
    External` (higher trust subsumes lower-trust requirement).
  * **Mutation** — `immutable ⇒ append_only ⇒ monotonic ⇒
    read_write`.
  * **Overflow** — `exact ⇒ {wrap, trap, saturate}`.
  * **FP order** — `strict ⇒ reassociate`.
  * **Reentrancy** — `non_reentrant ⇒ reentrant`.
  * **Clock** — `combinational ⇒ sync(_)` (combinational
    signals feed any clock domain).
  * **Representation** — `Native ⇒ C` (Native layout fits any
    C-compatible slot).

## Trust layer

Scaffold (per `FX/KernelMTT/CLAUDE.md`).  No axioms.  The
enumeration is descriptive — the 2-category coherence (R0.7)
verifies that these cells compose correctly.

## Cross-references

  * `fx_reframing.md` §3.6.1 — 2-cells as subsumption
  * `fx_design.md` §6.2 — Subsumption typing rule
  * `fx_design.md` §6.3 — per-dimension preorder structure
  * `fx_design.md` §9.3 — effect lattice
  * `fx_design.md` §10.6 — trust propagation / lattice
  * `fx_design.md` §12.1 — security lattice
  * `FX/KernelMTT/Modality.lean` (R0.3) — the modality
    enumeration these cells live over
  * R0.6 — missing 2-cells encoding `fx_design.md` §6.8
    collision catalog
-/

namespace FX.KernelMTT

/-- A subsumption 2-cell `◇_{modality, fromGrade} ⇒
    ◇_{modality, toGrade}`.  Declares that the source grade
    subsumes the target grade for the given modality.

    The fields are intentionally string-typed for `fromGrade`
    and `toGrade` rather than per-modality grade enums — grade
    domains vary enormously (finite for Tot/IO/..., continuous
    for rationals), so a string encoding lets the enumeration
    be uniform without committing to a grade datatype per
    modality at this layer.  The kernel layer (R1.7) resolves
    strings against each modality's grade type. -/
structure SubsumptionCell where
  /-- The modality the 2-cell lives on. -/
  modality  : Modality
  /-- Source grade (the MORE restrictive / stronger grade).
      Subsumes the target grade. -/
  fromGrade : String
  /-- Target grade (the LESS restrictive / weaker grade). -/
  toGrade   : String
  /-- Cross-reference to the `fx_design.md` section declaring
      the subsumption.  E.g., "§6.2", "§9.3". -/
  docSource : String
  deriving Repr, Inhabited, DecidableEq

namespace SubsumptionCell

/-! ## Per-modality cell enumerations

Each section enumerates the direct subsumption edges for one
modality.  The `all` aggregator concatenates them. -/

/-- Usage semiring subsumption per `fx_design.md` §6.1 / §6.2:
    `0 ⇒ 1 ⇒ ω`.  Ghost (`0`) subsumes linear (`1`) subsumes
    unrestricted (`w`) — a ghost value vacuously inhabits a
    linear requirement (it won't actually appear at runtime);
    a linear value inhabits an unrestricted requirement (you
    may use it zero or more times, including once).

    Includes the transitive `0 ⇒ w` as an explicit cell so
    lookup `hasCell` doesn't need transitivity. -/
def usageCells : List SubsumptionCell :=
  [ { modality := Modality.usage, fromGrade := "0",  toGrade := "1", docSource := "§6.1" }
  , { modality := Modality.usage, fromGrade := "1",  toGrade := "w", docSource := "§6.1" }
  , { modality := Modality.usage, fromGrade := "0",  toGrade := "w", docSource := "§6.1" }
  ]

/-- Effect lattice subsumption per `fx_design.md` §9.3.  `Tot`
    is the bottom element (empty effect row) and subsumes every
    non-Tot effect.  `Read ⇒ Write` is the only declared
    non-Tot inclusion per §9.3 ("Write implies Read"). -/
def effCells : List SubsumptionCell :=
  [ { modality := Modality.eff, fromGrade := "Tot",  toGrade := "IO",    docSource := "§9.3" }
  , { modality := Modality.eff, fromGrade := "Tot",  toGrade := "Alloc", docSource := "§9.3" }
  , { modality := Modality.eff, fromGrade := "Tot",  toGrade := "Read",  docSource := "§9.3" }
  , { modality := Modality.eff, fromGrade := "Tot",  toGrade := "Write", docSource := "§9.3" }
  , { modality := Modality.eff, fromGrade := "Tot",  toGrade := "Async", docSource := "§9.3" }
  , { modality := Modality.eff, fromGrade := "Tot",  toGrade := "Div",   docSource := "§9.3" }
  , { modality := Modality.eff, fromGrade := "Tot",  toGrade := "Exn",   docSource := "§9.3" }
  , { modality := Modality.eff, fromGrade := "Read", toGrade := "Write", docSource := "§9.3" }
  ]

/-- Security lattice per `fx_design.md` §12.1: two-element
    `unclassified < classified`.  Combining public and secret
    yields secret; there's no implicit downgrade.  The single
    2-cell encodes the only subsumption edge. -/
def secCells : List SubsumptionCell :=
  [ { modality := Modality.sec, fromGrade := "unclassified", toGrade := "classified", docSource := "§12.1" }
  ]

/-- Observability lattice per `fx_design.md` §6.3 dim 11:
    `opaque < transparent`.  In `with CT` context, all values
    must be opaque — opaque is the more-restrictive end.  A
    single 2-cell. -/
def obsCells : List SubsumptionCell :=
  [ { modality := Modality.obs, fromGrade := "opaque", toGrade := "transparent", docSource := "§6.3.11" }
  ]

/-- Trust lattice per `fx_design.md` §6.3 dim 9 / §10.6:
    `Verified > Tested > Sorry > Assumed > External`.  Trust
    propagates as MIN through the call graph — a caller's
    effective trust is the minimum of its own declared trust
    and its transitive callees'.  Subsumption direction:
    a higher-trust value can be used where a lower-trust one
    is expected (satisfies the trust requirement with room to
    spare).  Four direct cells covering the chain. -/
def trustCells : List SubsumptionCell :=
  [ { modality := Modality.trust, fromGrade := "Verified", toGrade := "Tested",   docSource := "§10.6" }
  , { modality := Modality.trust, fromGrade := "Tested",   toGrade := "Sorry",    docSource := "§10.6" }
  , { modality := Modality.trust, fromGrade := "Sorry",    toGrade := "Assumed",  docSource := "§10.6" }
  , { modality := Modality.trust, fromGrade := "Assumed",  toGrade := "External", docSource := "§10.6" }
  ]

/-- Mutation lattice per `fx_design.md` §6.3 dim 18:
    `immutable < append_only < monotonic < read_write`.  An
    immutable binding can be used where any higher permission
    is expected (the caller gets fewer rights than it asked
    for, which is safe).  Three direct cells. -/
def mutationCells : List SubsumptionCell :=
  [ { modality := Modality.mutation, fromGrade := "immutable",    toGrade := "append_only", docSource := "§6.3.18" }
  , { modality := Modality.mutation, fromGrade := "append_only",  toGrade := "monotonic",   docSource := "§6.3.18" }
  , { modality := Modality.mutation, fromGrade := "monotonic",    toGrade := "read_write",  docSource := "§6.3.18" }
  ]

/-- Overflow per `fx_design.md` §6.3 dim 16: `{exact, wrap,
    trap, saturate}` where `exact` is bottom; wrap/trap/saturate
    are PAIRWISE INCOMPARABLE.  Three cells covering the only
    declared edges. -/
def overflowCells : List SubsumptionCell :=
  [ { modality := Modality.overflow, fromGrade := "exact", toGrade := "wrap",     docSource := "§6.3.16" }
  , { modality := Modality.overflow, fromGrade := "exact", toGrade := "trap",     docSource := "§6.3.16" }
  , { modality := Modality.overflow, fromGrade := "exact", toGrade := "saturate", docSource := "§6.3.16" }
  ]

/-- FP order per `fx_design.md` §6.3 dim 17: `strict <
    reassociate`.  Strict is the more-deterministic end;
    reassociate admits compiler reordering for SIMD.  Single
    cell. -/
def fporderCells : List SubsumptionCell :=
  [ { modality := Modality.fporder, fromGrade := "strict", toGrade := "reassociate", docSource := "§6.3.17" }
  ]

/-- Reentrancy per `fx_design.md` §6.3 dim 19: `non_reentrant
    < reentrant`.  The default non-reentrant end is more
    restrictive; granting `reentrant` is explicit.  Single
    cell. -/
def reentrancyCells : List SubsumptionCell :=
  [ { modality := Modality.reentrancy, fromGrade := "non_reentrant", toGrade := "reentrant", docSource := "§6.3.19" }
  ]

/-- Clock domain per `fx_design.md` §6.3 dim 12 / §18.7:
    `combinational` is the identity — a combinational signal
    can feed ANY clock domain.  The `sync(clk_id)` grades are
    indexed by clock name and pairwise incomparable when the
    names differ; we encode the generic `combinational ⇒
    sync(_)` as the placeholder edge using the literal
    string "sync(_)".  Specific sync(A) ⇒ sync(B) cells land
    in the kernel layer with per-clock resolution. -/
def clockCells : List SubsumptionCell :=
  [ { modality := Modality.clock, fromGrade := "combinational", toGrade := "sync(_)", docSource := "§18.7" }
  ]

/-- Representation per `fx_design.md` §6.3 dim 10: layout
    preorder `repr(Native) ≤ repr(C)` (a C-compatible layout
    is usable anywhere native-picked layout is expected; not
    vice versa).  The remaining layout attributes
    (`packed`, `aligned(n)`, `big_endian`, `transparent`) form
    a lattice with conditional joins per `fx_reframing.md`
    §3.6.3; enumerate just the single declared direct edge
    here. -/
def reprCells : List SubsumptionCell :=
  [ { modality := Modality.repr, fromGrade := "Native", toGrade := "C", docSource := "§6.3.10" }
  ]

/-- Every enumerated subsumption cell, concatenated in
    per-modality order. -/
def all : List SubsumptionCell :=
  usageCells ++ effCells ++ secCells ++ obsCells ++ trustCells
    ++ mutationCells ++ overflowCells ++ fporderCells
    ++ reentrancyCells ++ clockCells ++ reprCells

/-! ## Lookup helpers -/

/-- All cells for the given modality.  Linear scan of `all`.
    Used by R1.7's 2-cell dispatch and by diagnostic emission
    to list available subsumptions at an error site. -/
def cellsForModality (m : Modality) : List SubsumptionCell :=
  all.filter fun cell => cell.modality = m

/-- `true` iff a DIRECT 2-cell exists from `fromGrade` to
    `toGrade` on the given modality.  Does NOT do transitive
    closure — call sites that need transitivity must compose
    multiple direct lookups. -/
def hasCell (m : Modality) (fromGrade toGrade : String) : Bool :=
  all.any fun cell =>
    cell.modality = m
      && cell.fromGrade == fromGrade
      && cell.toGrade == toGrade

/-- All grades reachable from `fromGrade` via direct or
    transitive subsumption cells on the given modality.  Fuel-
    bounded at the enumeration length to guarantee termination
    (there are only finitely many cells). -/
def reachableFrom (m : Modality) (fromGrade : String) : List String :=
  let rec loop (fuel : Nat) (frontier : List String) (visited : List String)
      : List String :=
    match fuel with
    | 0          => visited
    | Nat.succ k =>
      let nextHops : List String :=
        frontier.flatMap fun g =>
          (cellsForModality m).filterMap fun cell =>
            if cell.fromGrade == g && !(visited.contains cell.toGrade)
            then some cell.toGrade
            else none
      match nextHops with
      | [] => visited
      | _  => loop k nextHops (visited ++ nextHops)
  loop all.length [fromGrade] [fromGrade]

/-- `true` iff a transitive subsumption chain exists from
    `fromGrade` to `toGrade` on the given modality.  Equivalent
    to `(reachableFrom m fromGrade).contains toGrade`. -/
def subsumes (m : Modality) (fromGrade toGrade : String) : Bool :=
  (reachableFrom m fromGrade).contains toGrade

/-! ## Shape sanity theorems

Pin per-modality cell counts and the total enumeration
length.  Any future edit to the cell lists that changes a
count must update the theorem — forcing explicit decision. -/

/-- 3 usage cells (0⇒1, 1⇒w, 0⇒w). -/
theorem usage_cell_count : usageCells.length = 3 := by decide

/-- 8 effect cells (Tot⇒7 effects + Read⇒Write). -/
theorem eff_cell_count : effCells.length = 8 := by decide

/-- 1 security cell. -/
theorem sec_cell_count : secCells.length = 1 := by decide

/-- 1 observability cell. -/
theorem obs_cell_count : obsCells.length = 1 := by decide

/-- 4 trust cells (Verified→Tested→Sorry→Assumed→External). -/
theorem trust_cell_count : trustCells.length = 4 := by decide

/-- 3 mutation cells. -/
theorem mutation_cell_count : mutationCells.length = 3 := by decide

/-- 3 overflow cells (exact→each of wrap/trap/saturate). -/
theorem overflow_cell_count : overflowCells.length = 3 := by decide

/-- 1 FP-order cell. -/
theorem fporder_cell_count : fporderCells.length = 1 := by decide

/-- 1 reentrancy cell. -/
theorem reentrancy_cell_count : reentrancyCells.length = 1 := by decide

/-- 1 clock cell (combinational ⇒ sync(_)). -/
theorem clock_cell_count : clockCells.length = 1 := by decide

/-- 1 representation cell (Native ⇒ C). -/
theorem repr_cell_count : reprCells.length = 1 := by decide

/-- 27 cells total across all modalities. -/
theorem total_cell_count : all.length = 27 := by decide

/-! ### Cells live on admissible modalities only

Every cell's modality is admissible at at least one mode
(trivially true since every `Modality` is admissible at some
mode, but the theorem pins the invariant).  More pointedly:
every cell's modality participates in the `Mode.all` per-mode
modality lists from R0.2. -/

/-- Every cell's modality has a non-empty admissibility set
    — i.e., it's a valid 1-cell in at least one mode.  A
    defensive sanity check over the R0.3 admissibility
    function. -/
theorem cells_modalities_admissible :
    all.all (fun cell => !cell.modality.admissibleModes.isEmpty) = true := by
  decide

/-- Every cell's modality is one of the 20 modalities (no
    dangling constructor references). -/
theorem cells_modalities_enumerable :
    all.all (fun cell => Modality.all.contains cell.modality) = true := by
  decide

/-! ### `hasCell` direct-lookup spot checks

Verify the lookup helper correctly finds enumerated cells and
rejects non-cells. -/

/-- A declared cell is found by `hasCell`. -/
theorem has_usage_zero_to_one :
    hasCell Modality.usage "0" "1" = true := by decide

theorem has_eff_tot_to_io :
    hasCell Modality.eff "Tot" "IO" = true := by decide

theorem has_trust_verified_to_tested :
    hasCell Modality.trust "Verified" "Tested" = true := by decide

/-- `hasCell` is not transitive — `Tot ⇒ Write` is a direct
    cell, but `Tot ⇒ Read ⇒ Write` doesn't give a separate
    `Tot ⇒ Write` cell beyond what's enumerated.  (Here the
    `Tot ⇒ Write` edge IS enumerated, so the test confirms
    it's direct.  The opposite direction `Write ⇒ Tot` is
    not a cell.) -/
theorem has_cell_respects_direction :
    hasCell Modality.eff "Write" "Tot" = false := by decide

/-- Unknown grades are rejected. -/
theorem has_cell_unknown_grade :
    hasCell Modality.eff "Unicorn" "IO" = false := by decide

/-- Cells for wrong modality are rejected. -/
theorem has_cell_wrong_modality :
    hasCell Modality.sec "Tot" "IO" = false := by decide

/-! ### Transitive reachability spot checks

`subsumes` closes over direct cells.  Verify the fuel loop
terminates and reports expected reachability. -/

/-- `0` reaches `1`, `w`, and itself via usage chain. -/
theorem usage_zero_reaches_w :
    subsumes Modality.usage "0" "w" = true := by decide

/-- Verified reaches every lower trust level. -/
theorem verified_reaches_external :
    subsumes Modality.trust "Verified" "External" = true := by decide

/-- Tot reaches every effect in the enumeration. -/
theorem tot_reaches_write :
    subsumes Modality.eff "Tot" "Write" = true := by decide

/-- Reverse subsumption fails. -/
theorem write_does_not_reach_tot :
    subsumes Modality.eff "Write" "Tot" = false := by decide

/-- Non-enumerated grade rejects. -/
theorem bogus_reaches_nothing :
    subsumes Modality.eff "Unicorn" "IO" = false := by decide

/-- Reachability is reflexive (every grade "reaches" itself
    via the seed of the loop). -/
theorem reflexive_reachability :
    subsumes Modality.eff "IO" "IO" = true := by decide

end SubsumptionCell

end FX.KernelMTT
