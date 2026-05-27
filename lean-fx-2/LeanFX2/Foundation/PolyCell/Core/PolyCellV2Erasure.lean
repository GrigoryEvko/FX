import LeanFX2.Foundation.PolyCell.Core.PolyCellV2

/-! # Foundation/PolyCell/Core/PolyCellV2Erasure — raw-erasure rfl lemmas

This file ships the value-level raw-erasure extractor and four
per-constructor `raw_eq` rfl lemmas for `PolyCellV2`.  Together they
witness the architectural property quoted in `polycell.md` §4:

> "erasure back to raw is definitional"

The rawCell is a TYPE INDEX of `PolyCellV2`, not a separately-
computed field.  Each constructor's output type pins the exact
rawCell value, so the value-level erasure extraction is trivial
(just project the implicit type index) and the per-constructor
equation lemmas close by `rfl`.

## Why this file exists

Strictly speaking, the four `raw_eq` lemmas are tautological — they
restate what's already in each constructor's type signature.  They
exist for three reasons:

1. **Downstream rewrites.**  Code that pattern-matches on a
   `PolyCellV2` value and wants to relate its raw erasure to the
   constructor's args can cite a named lemma instead of re-deriving
   the equation.

2. **Documentation.**  The lemmas spell out, in one place, what the
   raw erasure of each ctor is — useful for readers learning the
   spec without spelunking the inductive declaration.

3. **Future fragility check.**  If a future refactor changes any
   ctor's rawCell index, these lemmas STOP compiling — catching the
   spec drift at the earliest possible point.

## The extractor

`PolyCellV2.raw : PolyCellV2 ... rawCell → RawCellV2 scope` takes
a certified cell and returns its rawCell index.  The body is a
one-liner: just return the implicit `rawCell` argument that Lean's
type unifier already determined from the cell's type signature.
The `_cell` parameter is used by the typechecker (to fix the
implicit) but not in the body — hence the underscore prefix.

This mirrors v1's `PolyCell.raw` (`Core/Certified.lean:212`) with
the v2 vocabulary (`RawCellV2 scope` instead of
`PolyTerm profile cellDimension`).

## The four raw_eq lemmas

One per `PolyCellV2` constructor:

* `gen_raw_eq` — `.termBase (.mkGen generator payload children)`
* `generatingCell_raw_eq` —
  `.generatingCell rule.ruleId source target`
* `verticalComposite_raw_eq` —
  `.verticalComposite firstRaw secondRaw`
* `identityCell_raw_eq` — `.identityCell baseRaw`

Each closes by `rfl` because the ctor's output `rawCell` index IS
the stated expression by definition.

## Zero-axiom verification

All five declarations are propext-free: the extractor is a pure
projection of an implicit argument, and the equations close by
`rfl` (no equation-compiler reasoning on the Nat dim index, no
HEq, no transports).  Audit-gated in `Tools/AuditAll/AuditPolyCell.lean`.
-/

namespace LeanFX2.Foundation.PolyCell.Core
namespace PolyCellV2

/-- Extract the raw erasure index from a certified cell.

The body is the implicit `rawCell` type index, returned as a
value-level term.  Mirrors v1's `PolyCell.raw` with `RawCellV2 scope`
in place of `PolyTerm profile cellDimension`.

The `_cell` parameter is consumed by Lean's type unifier to fix the
implicit `rawCell` argument; the body itself doesn't reference it
(hence the underscore prefix). -/
def raw {profile : PolyProfile} {sort : CellSort} {dim scope : Nat}
    {boundary : CellBoundaryV2 profile sort dim scope}
    {rawCell : RawCellV2 scope}
    (_cell : PolyCellV2 profile sort dim scope boundary rawCell) :
    RawCellV2 scope :=
  rawCell

/-- The `gen` constructor's raw erasure is the `RawCellV2.termBase`
wrapper around `RawTermV2.mkGen` with the generator, payload, and
children spine.

Closes by `rfl` because `gen`'s output type pins
`rawCell := .termBase (.mkGen generator payload children)` and
`raw` just returns that index. -/
theorem gen_raw_eq {profile : PolyProfile} {scope : Nat}
    {generator : Generator}
    {payload : generator.payload scope}
    {children : RawTermChildrenV2 generator.binderShifts scope}
    (admission : SupportedGeneratorV2 generator)
    (payloadEvidence : GenPayloadEvidence generator scope payload)
    (childSpine : CertifiedTermSpineV2 profile generator.childSpecs
                    scope generator.binderShifts children) :
    (PolyCellV2.gen admission payloadEvidence childSpine).raw =
      .termBase (.mkGen generator payload children) :=
  rfl

/-- The `generatingCell` constructor's raw erasure is the
`RawCellV2.generatingCell` triple of `(rule.ruleId, source, target)`.

Closes by `rfl` since the ctor's output type pins
`rawCell := .generatingCell rule.ruleId source target`.

This is the SPIKE-1 dim-transport ctor — the `HasEqualDim` parameter
reconciles source and target dims via `Nat.decEq`, which is propext-
free, so this lemma also stays propext-free. -/
theorem generatingCell_raw_eq {profile : PolyProfile} {scope : Nat}
    (rule : RuleSpecV2)
    (admission : SupportedRuleSpecV2 rule)
    {source target : RawCellV2 scope}
    {sourceBoundary targetBoundary :
      CellBoundaryV2 profile rule.cellSort source.dim scope}
    (dimEq : HasEqualDim source target)
    (sourceCell : PolyCellV2 profile rule.cellSort source.dim scope
                    sourceBoundary source)
    (targetCell : PolyCellV2 profile rule.cellSort source.dim scope
                    targetBoundary target) :
    (PolyCellV2.generatingCell rule admission dimEq sourceCell
      targetCell).raw =
      .generatingCell rule.ruleId source target :=
  rfl

/-- The `verticalComposite` constructor's raw erasure is
`RawCellV2.verticalComposite` of the two component raw cells.

Closes by `rfl` since the ctor's output type pins
`rawCell := .verticalComposite firstRaw secondRaw`. -/
theorem verticalComposite_raw_eq {profile : PolyProfile}
    {sort : CellSort} {dim scope : Nat}
    {source middle target : RawCellV2 scope}
    {firstRaw secondRaw : RawCellV2 scope}
    (firstCell : PolyCellV2 profile sort (dim + 1) scope
                   (CellBoundaryV2.endpoints source middle) firstRaw)
    (secondCell : PolyCellV2 profile sort (dim + 1) scope
                    (CellBoundaryV2.endpoints middle target)
                    secondRaw) :
    (PolyCellV2.verticalComposite firstCell secondCell).raw =
      .verticalComposite firstRaw secondRaw :=
  rfl

/-- The `identityCell` constructor's raw erasure is
`RawCellV2.identityCell` of the base raw cell.

Closes by `rfl` since the ctor's output type pins
`rawCell := .identityCell baseRaw`. -/
theorem identityCell_raw_eq {profile : PolyProfile} {sort : CellSort}
    {dim scope : Nat}
    {boundary : CellBoundaryV2 profile sort dim scope}
    {baseRaw : RawCellV2 scope}
    (baseCell : PolyCellV2 profile sort dim scope boundary baseRaw) :
    (PolyCellV2.identityCell baseCell).raw =
      .identityCell baseRaw :=
  rfl

end PolyCellV2
end LeanFX2.Foundation.PolyCell.Core
