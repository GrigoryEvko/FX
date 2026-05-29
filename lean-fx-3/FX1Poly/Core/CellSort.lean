/-!
# CellSort — Sort Vocabulary for Certified PolyCells

This file introduces only the closed sort vocabulary used by the
raw-to-certified PolyCell boundary.  It deliberately carries no typing
semantics: later files attach generator metadata, child specifications, and
certified cells to these tags.
-/

namespace FX1Poly.Core

/-- Visible strata of the one certified FX cell substrate.

These tags separate the shape of certified cells before any typing rule is
allowed to claim that a raw `PolyTerm` is meaningful. -/
inductive CellSort where
  /-- Context cells: environments and context morphisms. -/
  | context
  /-- Type cells: type formers and universe-level data. -/
  | type
  /-- Term cells: value-level syntax and reductions over values. -/
  | term
  /-- Mode cells: modal/usage mode data. -/
  | mode
  /-- Effect cells: effect capability data. -/
  | effect
  /-- Grade cells: quantitative resource/security/cost grades. -/
  | grade
  /-- Protocol cells: session/protocol-state data. -/
  | protocol
  deriving DecidableEq

namespace CellSort

/-- Stable finite enumeration of the current sort vocabulary. -/
def all : List CellSort :=
  [.context, .type, .term, .mode, .effect, .grade, .protocol]

/-- Stable numeric code for compact generator metadata tables. -/
def toCode : CellSort → Nat
  | .context => 0
  | .type => 1
  | .term => 2
  | .mode => 3
  | .effect => 4
  | .grade => 5
  | .protocol => 6

/-- Decode a stable numeric sort code. -/
def ofCode? : Nat → Option CellSort
  | 0 => some .context
  | 1 => some .type
  | 2 => some .term
  | 3 => some .mode
  | 4 => some .effect
  | 5 => some .grade
  | 6 => some .protocol
  | _ => none

/-- Encoding then decoding a sort recovers the original sort. -/
theorem ofCode?_toCode (sort : CellSort) :
    ofCode? sort.toCode = some sort := by
  cases sort <;> rfl

/-- The sort enumeration has exactly seven entries. -/
theorem all_length : all.length = 7 := rfl

end CellSort

end FX1Poly.Core
