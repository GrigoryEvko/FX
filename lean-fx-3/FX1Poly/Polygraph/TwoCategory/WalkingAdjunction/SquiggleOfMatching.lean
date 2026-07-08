import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.NonCrossingMatching
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.Squiggle

/-! # squiggleOfMatching — the GLOBAL populator of the oriented squiggle NF (SQ-2 via the global route)

`Squiggle.lean` (SQ-1) shipped the RV Def 3.1.2 oriented squiggle *carrier* (`SquiggleString`, a
strictly-undulating level word whose every level carries an `L`/`R` port object) together with the
honesty marker `fxMode_hasOrientedSquiggleFoldSoundness := false`: a left-to-right per-atom **fold**
into that carrier is machine-refuted (`arcMatching_cupAtoms_locallyIndistinguishable` — two cups with
literally equal local spine data `(2, 0, 2)` must receive OPPOSITE variance, decided by a cap in the
fold's *future*).

This file supplies the faithful populator by the route the no-go leaves open: a **global read-off** of
the FINISHED planar matching `matchingOf` (`DiagramType`), never a spine fold. Riehl–Verity §3.1: the
squiggle level string is the *height function of the turning points* of the diagram — level = the
global nesting depth (number of arcs currently straddling the port), a count over the WHOLE matching
that a prefix builder cannot see but the completed `DiagramType.partner` records exactly. Since the
input is the finished matching (both endpoints of every arc already known), each level and side is a
total function of the global datum — outside the refuted fold class by construction.

## The construction (all `Nat`/`Bool`/structural, propext-clean)

1. Traverse the rectangle boundary in cyclic order (`rectangleBoundaryOrder`): bottom ports
   left-to-right (`0 … bottomCount-1`), then top ports right-to-left (`total-1 … bottomCount`) — the
   canonical Dyck reading order along which, under non-crossing nesting, arcs open and close
   well-nested. This mirrors `boundaryPosition`'s cyclic linearization from `NonCrossingMatching`.
2. Level = running nesting depth. At each index `arcOpensAtIndex` compares the index's boundary
   position with its partner's: the nearer endpoint OPENS the arc (rise, `depth+1`); the farther
   endpoint CLOSES it (fall, `depth-1`). The level emitted is the depth AFTER the step. Because every
   port is exactly one endpoint of exactly one arc, every step is a unit `±1` and open/close alternate
   under non-crossing nesting — a strictly-undulating profile by construction.
3. Side = the port's boundary object (`portSideOfIndex`): bottom ports (`index < bottomCount`, the
   source word) sit on `leftPort`, top ports on `rightPort` — a function of the GLOBAL split the fold
   could not read.

Composed with `matchingOf`, `squiggleOfCell := squiggleOfMatching ∘ matchingOf` inherits ALL of
`matchingOf`'s invariance (SQ-3 soundness below): equal-matching cells get an equal squiggle NF, so
the squiggle decision never contradicts the matching decision.

## HONEST scope

This is a matchingOf-DERIVED **second presentation** — a cross-check and the SQ-9 ledger, NOT an
independent completeness route. It gives no fresh purchase on the keystone `convOfMapEq` (which stays
the matchingOf RV width-induction). SQ-3 (soundness) is one direction — the squiggle decision is
coarser-or-equal to the matching decision. The CONVERSE full faithfulness (squiggle NF determines the
matching, the height-function ↔ non-crossing-matching Dyck bijection) is the standing SQ-7 residual;
`squiggleOfMatching` drops the loop count outright, so it is NOT injective on all `DiagramType`. What
IS shipped for SQ-7 is the decidable witness-level agreement: on cells `matchingOf` keeps distinct the
derived squiggle is ALSO distinct.

Raw Lean 4 + `Init`; every declaration `propext`/`Quot.sound`/`Classical`/`sorry`/`native_decide`/
`omega`-free (full-enum `Bool` matches, structural recursion on the index list, `Nat.blt`/`Nat.succ`/
`Nat.pred`). Per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## SQ-2a — the per-index side and open/close reading (global functions of the matching) -/

/-- The boundary object a port sits on: bottom ports (`index < bottomCount`, the source word) are on
`leftPort`, top ports (the target word) on `rightPort`. A `Nat.blt` full-enum `Bool` match, so it is
propext-clean; it reads the GLOBAL bottom/top split, the datum the variance-blind fold could not see. -/
def portSideOfIndex (bottomCount index : Nat) : PortSide :=
  match Nat.blt index bottomCount with
  | true  => PortSide.leftPort
  | false => PortSide.rightPort

/-- Whether the arc through `index` OPENS at `index`: `index` is the nearer rectangle endpoint of its
arc, i.e. its boundary position precedes its partner's. Both positions come from `boundaryPosition`
(shared with `NonCrossingMatching`); the comparison is a single `Nat.blt`. Opening ⟹ a rise, closing
⟹ a fall — the height-function step. -/
def arcOpensAtIndex (bottomCount total : Nat) (partner : List Nat) (index : Nat) : Bool :=
  Nat.blt (boundaryPosition bottomCount total index)
          (boundaryPosition bottomCount total (natListGetAt partner index))

/-! ## SQ-2b — the rectangle boundary traversal order -/

/-- The boundary indices in rectangle-traversal order: bottom ports left-to-right (`0 … bottomCount-1`)
then top ports right-to-left (`total-1 … bottomCount`, the last top port first) — the canonical Dyck
reading order matching `boundaryPosition`'s cyclic linearization. -/
def rectangleBoundaryOrder (bottomCount topCount : Nat) : List Nat :=
  List.range bottomCount
    ++ (List.range topCount).map (fun offset => (bottomCount + topCount) - 1 - offset)

/-! ## SQ-2c — the global populator -/

/-- Worker: fold the rectangle-ordered indices carrying the running nesting `depth`. Each opening arc
raises the depth (a rise), each closing arc lowers it (a fall); the level emitted is the depth AFTER
the step, tagged with the port's side. Structural recursion on the index list — no fuel, no
well-founded recursion. -/
def squiggleLettersFrom (bottomCount total : Nat) (partner : List Nat) :
    Nat → List Nat → SquiggleString
  | _depth, [] => []
  | depth, index :: remainingIndices =>
    match arcOpensAtIndex bottomCount total partner index with
    | true =>
        let raisedDepth := depth + 1
        ⟨raisedDepth, portSideOfIndex bottomCount index⟩
          :: squiggleLettersFrom bottomCount total partner raisedDepth remainingIndices
    | false =>
        let loweredDepth := depth - 1
        ⟨loweredDepth, portSideOfIndex bottomCount index⟩
          :: squiggleLettersFrom bottomCount total partner loweredDepth remainingIndices

/-- ★ **SQ-2 (global route).** The oriented squiggle normal form read off the FINISHED planar matching
`DiagramType`: sweep the rectangle boundary in Dyck order, emitting the running nesting depth as the
level and the bottom/top split as the side. A GLOBAL construction over the completed `partner` — NOT a
left-to-right spine fold — so the fold no-go (`fxMode_hasOrientedSquiggleFoldSoundness := false`) does
not apply. -/
def squiggleOfMatching (diagram : DiagramType) : SquiggleString :=
  squiggleLettersFrom diagram.bottomCount (diagram.bottomCount + diagram.topCount) diagram.partner 0
    (rectangleBoundaryOrder diagram.bottomCount diagram.topCount)

/-- The populator composed with `matchingOf`: the oriented squiggle NF of a free 2-cell, read globally
off its boundary matching. -/
def squiggleOfCell {signature : ModeSignature} {sourceMode targetMode : signature.graph.Mode}
    {sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode}
    (cell : RawTwoCellExpr signature sourcePath targetPath) : SquiggleString :=
  squiggleOfMatching (matchingOf cell)

/-! ## SQ-2 smoke facts — the populator computes the height function on the shipped witnesses

Each value is the rectangle-order height word of the corresponding `matchingOf` witness
(`MatchingDecision.lean`); every fact is `rfl`, zero-axiom. -/

/-- Bare unit (a cup): the two top ports `0↔1` read as one rise then one fall, both on `R`. -/
theorem squiggleOfMatching_unit :
    squiggleOfMatching { bottomCount := 0, topCount := 2, partner := [1, 0], loops := 0 }
      = [⟨1, .rightPort⟩, ⟨0, .rightPort⟩] := rfl

/-- Bare counit (a cap): the two bottom ports `0↔1` read as one rise then one fall, both on `L`. -/
theorem squiggleOfMatching_counit :
    squiggleOfMatching { bottomCount := 2, topCount := 0, partner := [1, 0], loops := 0 }
      = [⟨1, .leftPort⟩, ⟨0, .leftPort⟩] := rfl

/-- The single through-strand (the snake's / identity's diagram type): one bottom port on `L` rising,
one top port on `R` falling. -/
theorem squiggleOfMatching_throughStrand :
    squiggleOfMatching { bottomCount := 1, topCount := 1, partner := [1, 0], loops := 0 }
      = [⟨1, .leftPort⟩, ⟨0, .rightPort⟩] := rfl

/-- Parallel units (two cups): the 4 top ports `0↔1`, `2↔3` read as the zigzag `1 ↓ 0 ↑ 1 ↓ 0`, all
on `R`. -/
theorem squiggleOfMatching_parallelUnits :
    squiggleOfMatching { bottomCount := 0, topCount := 4, partner := [1, 0, 3, 2], loops := 0 }
      = [⟨1, .rightPort⟩, ⟨0, .rightPort⟩, ⟨1, .rightPort⟩, ⟨0, .rightPort⟩] := rfl

/-! ## SQ-2 well-formedness — the populated string strictly undulates (RV Def 3.1.2) on the witnesses

The height word of a well-nested (non-crossing, loop-free) matching is a Dyck profile: unit steps that
alternate. Each witness lands strictly-undulating, by `rfl`. -/

theorem isStrictlyUndulating_squiggleOfMatching_unit :
    isStrictlyUndulating
      (squiggleOfMatching { bottomCount := 0, topCount := 2, partner := [1, 0], loops := 0 })
      = true := rfl

theorem isStrictlyUndulating_squiggleOfMatching_counit :
    isStrictlyUndulating
      (squiggleOfMatching { bottomCount := 2, topCount := 0, partner := [1, 0], loops := 0 })
      = true := rfl

theorem isStrictlyUndulating_squiggleOfMatching_throughStrand :
    isStrictlyUndulating
      (squiggleOfMatching { bottomCount := 1, topCount := 1, partner := [1, 0], loops := 0 })
      = true := rfl

theorem isStrictlyUndulating_squiggleOfMatching_parallelUnits :
    isStrictlyUndulating
      (squiggleOfMatching { bottomCount := 0, topCount := 4, partner := [1, 0, 3, 2], loops := 0 })
      = true := rfl

/-! ## SQ-3 — soundness: the populator is invariant under exactly what `matchingOf` is

`squiggleOfCell = squiggleOfMatching ∘ matchingOf`, so every `matchingOf`-invariance transfers by
`congrArg`. These are the honest SOUND direction: equal-matching cells receive an equal squiggle NF, so
the squiggle decision never contradicts the matching decision (it is coarser-or-equal). -/

/-- ★ **SQ-3 (soundness).** Cells with equal boundary matching receive an equal oriented squiggle NF —
the populator inherits matchingOf-invariance verbatim. -/
theorem squiggleOfCell_congr_of_matchingOf_eq {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode}
    {sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode}
    {firstCell secondCell : RawTwoCellExpr signature sourcePath targetPath}
    (matchingEqual : matchingOf firstCell = matchingOf secondCell) :
    squiggleOfCell firstCell = squiggleOfCell secondCell :=
  congrArg squiggleOfMatching matchingEqual

/-- Cells with equal spine receive an equal squiggle NF (composing the SQ-3 congruence with
`matchingOf_congr_of_spine_eq`). -/
theorem squiggleOfCell_congr_of_spine_eq {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode}
    {sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode}
    {firstCell secondCell : RawTwoCellExpr signature sourcePath targetPath}
    (spineEqual : firstCell.spine = secondCell.spine) :
    squiggleOfCell firstCell = squiggleOfCell secondCell :=
  congrArg squiggleOfMatching (matchingOf_congr_of_spine_eq spineEqual)

/-- ★ **SQ-3 for the interchange-free structural fragment.** Every one of the eleven structural
strict-2-category laws preserves the oriented squiggle NF, because each preserves the spine on the nose
(`matchingOf_eq_of_interchangeFreeStep`). The squiggle presentation agrees with the matching
presentation on the whole structural fragment. -/
theorem squiggleOfCell_eq_of_interchangeFreeStep {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode}
    {sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode}
    {firstCell secondCell : RawTwoCellExpr signature sourcePath targetPath}
    (step : TwoCellStepInterchangeFree signature firstCell secondCell) :
    squiggleOfCell firstCell = squiggleOfCell secondCell :=
  congrArg squiggleOfMatching (matchingOf_eq_of_interchangeFreeStep step)

/-! ## SQ-7 (partial) — decidable agreement: the derived decision retains discriminating power

Full faithfulness (squiggle NF ⟹ matching, the height-function Dyck bijection) is the standing residual
— `squiggleOfMatching` forgets the loop count, so it is not injective on all `DiagramType`. What is
shipped here is the honest cross-check on the shipped witnesses: on cells `matchingOf` keeps distinct,
the derived squiggle NF is ALSO distinct (`decide`, via the shipped `squiggleStringDecEq`). This is the
genuine "the two decisions agree" content — the squiggle decision is at least as fine as the matching
decision on these witnesses, not a degenerate constant map. -/

/-- Unit and counit have DISTINCT matchings (`bottomCount` `0` vs `2`); the derived squiggle NFs are
ALSO distinct (the sides flip `R` vs `L`). The squiggle decision agrees with the matching decision in
keeping them apart. -/
theorem squiggleOfMatching_unit_ne_counit :
    squiggleOfMatching { bottomCount := 0, topCount := 2, partner := [1, 0], loops := 0 }
      ≠ squiggleOfMatching { bottomCount := 2, topCount := 0, partner := [1, 0], loops := 0 } := by
  decide

/-- Unit and the through-strand have DISTINCT matchings; the derived squiggle NFs are ALSO distinct. -/
theorem squiggleOfMatching_unit_ne_throughStrand :
    squiggleOfMatching { bottomCount := 0, topCount := 2, partner := [1, 0], loops := 0 }
      ≠ squiggleOfMatching { bottomCount := 1, topCount := 1, partner := [1, 0], loops := 0 } := by
  decide

/-- Unit and parallel-units have DISTINCT matchings (`topCount` `2` vs `4`); the derived squiggle NFs
are ALSO distinct (length `2` vs `4`). -/
theorem squiggleOfMatching_unit_ne_parallelUnits :
    squiggleOfMatching { bottomCount := 0, topCount := 2, partner := [1, 0], loops := 0 }
      ≠ squiggleOfMatching { bottomCount := 0, topCount := 4, partner := [1, 0, 3, 2], loops := 0 } := by
  decide

/-- The through-strand and the counit have DISTINCT matchings; the derived squiggle NFs are ALSO
distinct. -/
theorem squiggleOfMatching_throughStrand_ne_counit :
    squiggleOfMatching { bottomCount := 1, topCount := 1, partner := [1, 0], loops := 0 }
      ≠ squiggleOfMatching { bottomCount := 2, topCount := 0, partner := [1, 0], loops := 0 } := by
  decide

/-! ## SQ-9 ledger — honesty markers -/

/-- **ESTABLISHED.** The GLOBAL populator `squiggleOfMatching : DiagramType → SquiggleString` (SQ-2 via
the global route) is shipped: it reads the running nesting depth off the FINISHED planar matching in
rectangle-boundary order, tagging each level with the bottom/top port object — a total function of the
completed `partner`, outside the refuted left-to-right fold class by construction. Composed with
`matchingOf` it lands strictly-undulating on every shipped witness. `= true`. -/
def fxMode_hasGlobalSquigglePopulator : Bool := true

/-- **ESTABLISHED.** SQ-3 soundness: `squiggleOfCell = squiggleOfMatching ∘ matchingOf` is invariant
under exactly what `matchingOf` is — equal matching ⟹ equal squiggle NF
(`squiggleOfCell_congr_of_matchingOf_eq`), and hence over the whole interchange-free structural fragment
(`squiggleOfCell_eq_of_interchangeFreeStep`). The squiggle decision never contradicts the matching
decision. `= true`. -/
def fxMode_hasSquiggleMatchingSoundness : Bool := true

/-- **RESIDUAL — the honest SQ-7 wall.** FULL faithfulness (the derived squiggle NF DETERMINES the
matching — the height-function ↔ non-crossing-matching Dyck bijection) is NOT shipped. `squiggleOfMatching`
forgets the loop count, so it is provably not injective on all `DiagramType`; on the reachable
non-crossing loop-free class the injectivity is the standing residual. What IS shipped is the decidable
witness-level agreement (`squiggleOfMatching_unit_ne_counit` and companions): on cells `matchingOf`
keeps distinct, the derived squiggle is also distinct. This is a matchingOf-DERIVED second presentation
— a cross-check and the SQ-9 ledger — NOT an independent completeness route; it gives no fresh purchase
on the keystone `convOfMapEq`. `= false`. -/
def fxMode_hasSquiggleMatchingFaithfulness : Bool := false

end FX1Poly.Polygraph
