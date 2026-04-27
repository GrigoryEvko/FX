import FX.KernelMTT.Adjunction

/-!
# Adjunction tests (R0.4)

Compile-time tests pinning the four cross-mode adjunction
records per `fx_reframing.md` §3.5.  Cross-validates with
`Mode.lean` R0.2's morphism lists — any drift between the
adjunction records and the per-mode morphism lists fails one
of the agreement theorems in `Adjunction.lean`.

Coverage here (beyond Adjunction.lean's own theorems):

  * Per-record field-by-field assertion (name, modes,
    morphism names, proper/partial flags, doc section).
  * `findByForward?` / `findByMorphism?` lookup behavior for
    all six morphism names (4 forwards + 2 backward halves of
    proper adjunctions).
  * `forwardEdge` / `backwardEdge?` projections match the
    declared edges.
  * The edge-count-matches-Mode theorem's decomposition:
    ghost⊣erase contributes 2 edges, synth contributes 1,
    serialize⊣parse contributes 2, observe contributes 1.
-/

namespace Tests.KernelMTT.AdjunctionTests

open FX.KernelMTT
open FX.KernelMTT.Adjunction

/-! ## Per-record field pinning

Each of the four records gets its own set of field-level
`rfl` tests.  A drift in ANY field on ANY record flips a
specific test — localizing the failure to that (adjunction,
field) pair. -/

/-! ### Ghost ⊣ Software (§3.5.1) -/

example : ghostSoftware.name          = "Ghost ⊣ Software" := rfl
example : ghostSoftware.leftMode      = Mode.ghost         := rfl
example : ghostSoftware.rightMode     = Mode.software      := rfl
example : ghostSoftware.forwardName   = "ghost"            := rfl
example : ghostSoftware.backwardName  = some "erase"       := rfl
example : ghostSoftware.isProperAdj   = true               := rfl
example : ghostSoftware.isForwardPartial = false           := rfl
example : ghostSoftware.docSection    = "3.5.1"            := rfl

/-! ### Software → Hardware (synth) (§3.5.2) -/

example : softwareHardware.name          = "Software → Hardware (synth)" := rfl
example : softwareHardware.leftMode      = Mode.software    := rfl
example : softwareHardware.rightMode     = Mode.hardware    := rfl
example : softwareHardware.forwardName   = "synth"          := rfl
example : softwareHardware.backwardName  = none             := rfl
example : softwareHardware.isProperAdj   = false            := rfl
example : softwareHardware.isForwardPartial = true          := rfl
example : softwareHardware.docSection    = "3.5.2"          := rfl

/-! ### Software ⇄ Wire (serialize ⊣ parse) (§3.5.3) -/

example : softwareWire.name          = "Software ⇄ Wire (serialize ⊣ parse)" := rfl
example : softwareWire.leftMode      = Mode.software   := rfl
example : softwareWire.rightMode     = Mode.wire       := rfl
example : softwareWire.forwardName   = "serialize"     := rfl
example : softwareWire.backwardName  = some "parse"    := rfl
example : softwareWire.isProperAdj   = true            := rfl
example : softwareWire.isForwardPartial = false        := rfl
example : softwareWire.docSection    = "3.5.3"         := rfl

/-! ### Hardware → Software (observe) (§3.5.4) -/

example : hardwareSoftware.name          = "Hardware → Software (observe)" := rfl
example : hardwareSoftware.leftMode      = Mode.hardware    := rfl
example : hardwareSoftware.rightMode     = Mode.software    := rfl
example : hardwareSoftware.forwardName   = "observe"        := rfl
example : hardwareSoftware.backwardName  = none             := rfl
example : hardwareSoftware.isProperAdj   = false            := rfl
example : hardwareSoftware.isForwardPartial = false         := rfl
example : hardwareSoftware.docSection    = "3.5.4"          := rfl

/-! ## `all` enumeration shape

Four records in §3.5.1–§3.5.4 order.  Pin the list's head,
tail, and length so any reorder or addition surfaces
immediately. -/

example : Adjunction.all.length = 4 := by decide

example : Adjunction.all.head? = some ghostSoftware := by decide

example : Adjunction.all.getLast? = some hardwareSoftware := by decide

-- Full list pinning — catches any reorder.
example :
    Adjunction.all = [ ghostSoftware, softwareHardware, softwareWire, hardwareSoftware ]
    := by decide

/-! ## `findByForward?` — forward-name lookup

Each forward morphism resolves to its adjunction.  Unknown
names return `none`. -/

example : findByForward? "ghost"     = some ghostSoftware     := by decide
example : findByForward? "synth"     = some softwareHardware  := by decide
example : findByForward? "serialize" = some softwareWire      := by decide
example : findByForward? "observe"   = some hardwareSoftware  := by decide

-- Backward names do NOT resolve via findByForward?.
example : findByForward? "erase"     = none := by decide
example : findByForward? "parse"     = none := by decide

-- Unknown names return none.
example : findByForward? "bogus"     = none := by decide
example : findByForward? ""          = none := by decide
example : findByForward? "SYNTH"     = none := by decide  -- case-sensitive

/-! ## `findByMorphism?` — any-side lookup

Forward names resolve as in `findByForward?`; backward names
ALSO resolve to their parent adjunction record, because
`findByMorphism?` walks both sides. -/

-- Forward morphisms — same results as findByForward?.
example : findByMorphism? "ghost"     = some ghostSoftware     := by decide
example : findByMorphism? "synth"     = some softwareHardware  := by decide
example : findByMorphism? "serialize" = some softwareWire      := by decide
example : findByMorphism? "observe"   = some hardwareSoftware  := by decide

-- Backward names — resolve to their parent proper adjunction.
example : findByMorphism? "erase" = some ghostSoftware  := by decide
example : findByMorphism? "parse" = some softwareWire   := by decide

-- Unknown names — none.
example : findByMorphism? "bogus" = none := by decide

/-! ## Edge projection

`forwardEdge` extracts (leftMode, rightMode, forwardName).
`backwardEdge?` is `some` iff the record is a proper adj. -/

-- Forward edges.
example : ghostSoftware.forwardEdge    = (Mode.ghost,    Mode.software, "ghost")     := rfl
example : softwareHardware.forwardEdge = (Mode.software, Mode.hardware, "synth")     := rfl
example : softwareWire.forwardEdge     = (Mode.software, Mode.wire,     "serialize") := rfl
example : hardwareSoftware.forwardEdge = (Mode.hardware, Mode.software, "observe")   := rfl

-- Backward edges — `some` for proper adjunctions.
example : ghostSoftware.backwardEdge?
        = some (Mode.software, Mode.ghost, "erase") := rfl

example : softwareWire.backwardEdge?
        = some (Mode.wire, Mode.software, "parse") := rfl

-- Backward edges — `none` for one-way / partial records.
example : softwareHardware.backwardEdge? = none := rfl
example : hardwareSoftware.backwardEdge? = none := rfl

/-! ## `allEdges` — the six-edge flattening

2 proper adjunctions × 2 directions + 2 one-way × 1 direction
= 6 total edges.  Pin the exact list so any ordering drift
surfaces.
-/

example : Adjunction.allEdges.length = 6 := by decide

-- Every declared morphism-edge is reachable via allEdges.
example : Adjunction.allEdges.contains (Mode.ghost, Mode.software, "ghost")     := by decide
example : Adjunction.allEdges.contains (Mode.software, Mode.ghost, "erase")     := by decide
example : Adjunction.allEdges.contains (Mode.software, Mode.hardware, "synth")  := by decide
example : Adjunction.allEdges.contains (Mode.software, Mode.wire, "serialize")  := by decide
example : Adjunction.allEdges.contains (Mode.wire, Mode.software, "parse")      := by decide
example : Adjunction.allEdges.contains (Mode.hardware, Mode.software, "observe") := by decide

-- Non-edges: Mode pairs without a morphism return false.
example : Adjunction.allEdges.contains
  (Mode.ghost, Mode.hardware, "nonexistent") = false := by decide

example : Adjunction.allEdges.contains
  (Mode.ghost, Mode.wire, "nonexistent") = false := by decide

example : Adjunction.allEdges.contains
  (Mode.hardware, Mode.wire, "nonexistent") = false := by decide

-- "synth" going backward (Hardware → Software) — no such edge.
example : Adjunction.allEdges.contains
  (Mode.hardware, Mode.software, "synth") = false := by decide

-- "erase" going forward (Ghost → Software) — no such edge
-- (erase is Software → Ghost).
example : Adjunction.allEdges.contains
  (Mode.ghost, Mode.software, "erase") = false := by decide

/-! ## Classification counts

Spot-check the §3.5 classification: 2 proper + 2 non-proper;
1 partial forward; etc.  These are covered by theorems in
`Adjunction.lean` already, but repeating them here as `decide`
checks pins the exact records rather than just counts.
-/

example :
    (Adjunction.all.filter (fun adj => adj.isProperAdj)).map (·.name)
      = [ "Ghost ⊣ Software"
        , "Software ⇄ Wire (serialize ⊣ parse)"
        ]
    := by decide

example :
    (Adjunction.all.filter (fun adj => ¬ adj.isProperAdj)).map (·.name)
      = [ "Software → Hardware (synth)"
        , "Hardware → Software (observe)"
        ]
    := by decide

example :
    (Adjunction.all.filter (fun adj => adj.isForwardPartial)).map (·.name)
      = [ "Software → Hardware (synth)" ]
    := by decide

/-! ## Doc-section uniqueness

Each record has a distinct `docSection`.  If a future edit
accidentally reuses a section identifier, this flips. -/

example :
    (Adjunction.all.map (·.docSection))
      = [ "3.5.1", "3.5.2", "3.5.3", "3.5.4" ]
    := by decide

/-! ## R0.8 — unit/counit 2-cell structure

Spot checks at the TestsTests layer for the unit/counit names,
triangle-endpoint shapes, and ten-name pinning added in R0.8.
A regression here fails `lake build Tests` (not just the library
build). -/

/-! ### Per-record unit/counit name pinning -/

example : Adjunction.ghostSoftware.unitName = some "eta_ghost" := by decide
example : Adjunction.ghostSoftware.counitName = some "epsilon_ghost" := by decide
example : Adjunction.softwareWire.unitName = some "eta_serialize" := by decide
example : Adjunction.softwareWire.counitName = some "epsilon_serialize" := by decide

-- Non-proper records carry neither.
example : Adjunction.softwareHardware.unitName = none := by decide
example : Adjunction.softwareHardware.counitName = none := by decide
example : Adjunction.hardwareSoftware.unitName = none := by decide
example : Adjunction.hardwareSoftware.counitName = none := by decide

/-! ### Triangle-endpoint shape per record -/

example :
    Adjunction.ghostSoftware.unitTriangleEndpoints?
      = some (Mode.ghost, Mode.software, Mode.ghost) := by decide

example :
    Adjunction.ghostSoftware.counitTriangleEndpoints?
      = some (Mode.software, Mode.ghost, Mode.software) := by decide

example :
    Adjunction.softwareWire.unitTriangleEndpoints?
      = some (Mode.software, Mode.wire, Mode.software) := by decide

example :
    Adjunction.softwareWire.counitTriangleEndpoints?
      = some (Mode.wire, Mode.software, Mode.wire) := by decide

-- Non-proper records have no triangle shape.
example : Adjunction.softwareHardware.unitTriangleEndpoints? = none := by decide
example : Adjunction.softwareHardware.counitTriangleEndpoints? = none := by decide
example : Adjunction.hardwareSoftware.unitTriangleEndpoints? = none := by decide
example : Adjunction.hardwareSoftware.counitTriangleEndpoints? = none := by decide

/-! ### `twoCellNames` pinning -/

example :
    Adjunction.twoCellNames
      = [ "eta_ghost", "epsilon_ghost"
        , "eta_serialize", "epsilon_serialize" ] := by decide

example : Adjunction.twoCellNames.length = 4 := by decide

/-! ### Name uniqueness across 1-cells and 2-cells

Ten names total, pinned as a literal list in record order. -/

example :
    (Adjunction.all.map (·.forwardName))
      ++ (Adjunction.all.filterMap (·.backwardName))
      ++ Adjunction.twoCellNames
      = [ "ghost", "synth", "serialize", "observe"
        , "erase", "parse"
        , "eta_ghost", "epsilon_ghost"
        , "eta_serialize", "epsilon_serialize" ] := by
  decide

/-! ### Invariants on proper vs non-proper records -/

-- Proper adjunctions satisfy the name-existence biconditional.
example :
    Adjunction.all.all (fun adj =>
      adj.isProperAdj = adj.unitName.isSome) = true := by decide

example :
    Adjunction.all.all (fun adj =>
      adj.isProperAdj = adj.counitName.isSome) = true := by decide

-- Triangle endpoints exist exactly for proper adjunctions.
example :
    Adjunction.all.all (fun adj =>
      adj.isProperAdj → adj.unitTriangleEndpoints?.isSome) = true := by decide

example :
    Adjunction.all.all (fun adj =>
      ¬ adj.isProperAdj → adj.unitTriangleEndpoints? = none) = true := by decide

example :
    Adjunction.all.all (fun adj =>
      adj.isProperAdj → adj.counitTriangleEndpoints?.isSome) = true := by decide

example :
    Adjunction.all.all (fun adj =>
      ¬ adj.isProperAdj → adj.counitTriangleEndpoints? = none) = true := by decide

end Tests.KernelMTT.AdjunctionTests
