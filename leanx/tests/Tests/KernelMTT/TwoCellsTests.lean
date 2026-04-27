import FX.KernelMTT.TwoCells

/-!
# Subsumption-2-cell tests (R0.5)

Compile-time tests pinning the 27 direct subsumption cells
across 11 modalities, lookup helpers, and transitive
reachability.  Complements the per-modality count theorems in
`TwoCells.lean` with per-cell membership assertions and
negative tests against non-enumerated edges.
-/

namespace Tests.KernelMTT.TwoCellsTests

open FX.KernelMTT
open FX.KernelMTT.SubsumptionCell

/-! ## Per-cell direct membership

One `hasCell` assertion per enumerated edge — catches any
typo or drift in `TwoCells.lean`'s per-modality lists. -/

-- Usage (3 cells)
example : hasCell Modality.usage "0" "1" = true := by decide
example : hasCell Modality.usage "1" "w" = true := by decide
example : hasCell Modality.usage "0" "w" = true := by decide

-- Effect (8 cells)
example : hasCell Modality.eff "Tot"  "IO"    = true := by decide
example : hasCell Modality.eff "Tot"  "Alloc" = true := by decide
example : hasCell Modality.eff "Tot"  "Read"  = true := by decide
example : hasCell Modality.eff "Tot"  "Write" = true := by decide
example : hasCell Modality.eff "Tot"  "Async" = true := by decide
example : hasCell Modality.eff "Tot"  "Div"   = true := by decide
example : hasCell Modality.eff "Tot"  "Exn"   = true := by decide
example : hasCell Modality.eff "Read" "Write" = true := by decide

-- Security (1 cell)
example : hasCell Modality.sec "unclassified" "classified" = true := by decide

-- Observability (1 cell)
example : hasCell Modality.obs "opaque" "transparent" = true := by decide

-- Trust (4 cells)
example : hasCell Modality.trust "Verified" "Tested"   = true := by decide
example : hasCell Modality.trust "Tested"   "Sorry"    = true := by decide
example : hasCell Modality.trust "Sorry"    "Assumed"  = true := by decide
example : hasCell Modality.trust "Assumed"  "External" = true := by decide

-- Mutation (3 cells)
example : hasCell Modality.mutation "immutable"   "append_only" = true := by decide
example : hasCell Modality.mutation "append_only" "monotonic"   = true := by decide
example : hasCell Modality.mutation "monotonic"   "read_write"  = true := by decide

-- Overflow (3 cells)
example : hasCell Modality.overflow "exact" "wrap"     = true := by decide
example : hasCell Modality.overflow "exact" "trap"     = true := by decide
example : hasCell Modality.overflow "exact" "saturate" = true := by decide

-- FP order (1 cell)
example : hasCell Modality.fporder "strict" "reassociate" = true := by decide

-- Reentrancy (1 cell)
example : hasCell Modality.reentrancy "non_reentrant" "reentrant" = true := by decide

-- Clock (1 cell)
example : hasCell Modality.clock "combinational" "sync(_)" = true := by decide

-- Representation (1 cell)
example : hasCell Modality.repr "Native" "C" = true := by decide

/-! ## Reverse direction rejections

Every enumerated cell goes ONE direction.  Reverse lookups
must fail — subsumption is not symmetric. -/

example : hasCell Modality.usage "1" "0"          = false := by decide
example : hasCell Modality.usage "w" "1"          = false := by decide
example : hasCell Modality.eff   "IO" "Tot"       = false := by decide
example : hasCell Modality.eff   "Write" "Read"   = false := by decide
example : hasCell Modality.sec   "classified" "unclassified" = false := by decide
example : hasCell Modality.obs   "transparent" "opaque"      = false := by decide
example : hasCell Modality.trust "External" "Assumed"        = false := by decide
example : hasCell Modality.mutation "read_write" "monotonic" = false := by decide
example : hasCell Modality.overflow "wrap" "exact"           = false := by decide
example : hasCell Modality.fporder "reassociate" "strict"    = false := by decide
example : hasCell Modality.reentrancy "reentrant" "non_reentrant" = false := by decide

/-! ## Cross-modality rejections

A cell for modality X is NOT a cell for modality Y.  Confirms
`hasCell` respects the modality tag. -/

-- Effect cells are not usage cells.
example : hasCell Modality.usage "Tot" "IO"    = false := by decide
example : hasCell Modality.sec   "Tot" "IO"    = false := by decide
-- Security cells are not observability cells.
example : hasCell Modality.obs "unclassified" "classified" = false := by decide
-- Trust cells are not mutation cells.
example : hasCell Modality.mutation "Verified" "Tested" = false := by decide

/-! ## Unknown grade rejections

Grades not in the enumeration — `bogus`, `Unicorn`, empty
string — return false. -/

example : hasCell Modality.eff   "Unicorn" "IO"      = false := by decide
example : hasCell Modality.eff   "Tot"     "Unicorn" = false := by decide
example : hasCell Modality.trust ""        "Tested"  = false := by decide
example : hasCell Modality.sec   "SECRET"  "classified" = false := by decide  -- case-sensitive

/-! ## `cellsForModality` shape

Per-modality extraction filters `all` correctly; lengths
match the per-modality `_cell_count` theorems. -/

example : (cellsForModality Modality.usage).length      = 3 := by decide
example : (cellsForModality Modality.eff).length        = 8 := by decide
example : (cellsForModality Modality.sec).length        = 1 := by decide
example : (cellsForModality Modality.obs).length        = 1 := by decide
example : (cellsForModality Modality.trust).length      = 4 := by decide
example : (cellsForModality Modality.mutation).length   = 3 := by decide
example : (cellsForModality Modality.overflow).length   = 3 := by decide
example : (cellsForModality Modality.fporder).length    = 1 := by decide
example : (cellsForModality Modality.reentrancy).length = 1 := by decide
example : (cellsForModality Modality.clock).length      = 1 := by decide
example : (cellsForModality Modality.repr).length       = 1 := by decide

-- Modalities without enumerated cells return empty lists.
example : (cellsForModality Modality.lifetime).length   = 0 := by decide
example : (cellsForModality Modality.provenance).length = 0 := by decide
example : (cellsForModality Modality.complexity).length = 0 := by decide
example : (cellsForModality Modality.precision).length  = 0 := by decide
example : (cellsForModality Modality.space).length      = 0 := by decide
example : (cellsForModality Modality.size).length       = 0 := by decide
example : (cellsForModality Modality.protocol).length   = 0 := by decide
example : (cellsForModality Modality.format).length     = 0 := by decide
example : (cellsForModality Modality.version).length    = 0 := by decide

/-! ## `subsumes` transitive closure

Directly-enumerated edges are subsumed; longer chains are
reachable via the fuel loop.  Check every edge's direct
reach, plus several multi-step chains. -/

-- Usage: 0 reaches 1 (direct), w (direct), itself (reflexive).
example : subsumes Modality.usage "0" "1" = true := by decide
example : subsumes Modality.usage "0" "w" = true := by decide
example : subsumes Modality.usage "0" "0" = true := by decide

-- Effect: Tot reaches all 7 enumerated effects directly; Read
-- reaches Write directly; Tot reaches Write via Tot ⇒ Read ⇒
-- Write AND via the direct Tot ⇒ Write cell (both paths).
example : subsumes Modality.eff "Tot"  "IO"    = true := by decide
example : subsumes Modality.eff "Tot"  "Write" = true := by decide
example : subsumes Modality.eff "Read" "Write" = true := by decide

-- Trust chain: Verified transitively reaches every lower tier.
example : subsumes Modality.trust "Verified" "Tested"   = true := by decide
example : subsumes Modality.trust "Verified" "Sorry"    = true := by decide
example : subsumes Modality.trust "Verified" "Assumed"  = true := by decide
example : subsumes Modality.trust "Verified" "External" = true := by decide
example : subsumes Modality.trust "Tested"   "External" = true := by decide
example : subsumes Modality.trust "Sorry"    "External" = true := by decide
-- Reflexive.
example : subsumes Modality.trust "Verified" "Verified" = true := by decide

-- Mutation chain: immutable transitively reaches all.
example : subsumes Modality.mutation "immutable"   "append_only" = true := by decide
example : subsumes Modality.mutation "immutable"   "monotonic"   = true := by decide
example : subsumes Modality.mutation "immutable"   "read_write"  = true := by decide
example : subsumes Modality.mutation "append_only" "read_write"  = true := by decide

-- Overflow: exact reaches wrap/trap/saturate; wrap does NOT
-- reach trap (they're incomparable per §6.3 dim 16).
example : subsumes Modality.overflow "exact" "wrap"     = true  := by decide
example : subsumes Modality.overflow "exact" "trap"     = true  := by decide
example : subsumes Modality.overflow "exact" "saturate" = true  := by decide
example : subsumes Modality.overflow "wrap"  "trap"     = false := by decide
example : subsumes Modality.overflow "wrap"  "saturate" = false := by decide
example : subsumes Modality.overflow "trap"  "saturate" = false := by decide

/-! ## Reverse and non-edge reachability failures

`subsumes` returns false for unreachable pairs — reverse
direction, wrong modality, non-enumerated grades. -/

example : subsumes Modality.eff "Write" "Tot"  = false := by decide
example : subsumes Modality.eff "IO"    "Read" = false := by decide
example : subsumes Modality.trust "External" "Verified" = false := by decide
example : subsumes Modality.mutation "read_write" "immutable" = false := by decide
example : subsumes Modality.sec   "Tot" "IO"    = false := by decide  -- wrong modality
example : subsumes Modality.eff   "Unicorn" "IO" = false := by decide  -- bogus source
example : subsumes Modality.eff   "Tot" "Unicorn" = false := by decide  -- bogus target

/-! ## Reflexivity at every enumerated grade

`subsumes m x x = true` for any grade that appears as either
endpoint of a cell (the reachability seed returns itself).
Spot-check across modalities. -/

example : subsumes Modality.usage "0"              "0"              = true := by decide
example : subsumes Modality.usage "1"              "1"              = true := by decide
example : subsumes Modality.usage "w"              "w"              = true := by decide
example : subsumes Modality.sec   "classified"     "classified"     = true := by decide
example : subsumes Modality.sec   "unclassified"   "unclassified"   = true := by decide
example : subsumes Modality.repr  "Native"         "Native"         = true := by decide
example : subsumes Modality.repr  "C"              "C"              = true := by decide

/-! ## `all` aggregator consistency

The `all` list's length matches the sum of per-modality
cells.  Already pinned by `total_cell_count = 27` in
`TwoCells.lean` — here we cross-check via concatenation. -/

example :
    SubsumptionCell.all.length
      = usageCells.length + effCells.length + secCells.length
        + obsCells.length + trustCells.length + mutationCells.length
        + overflowCells.length + fporderCells.length
        + reentrancyCells.length + clockCells.length + reprCells.length
    := by decide

end Tests.KernelMTT.TwoCellsTests
