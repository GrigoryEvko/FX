import LeanFX2.Foundation.PolyCell.Core.PolyProfile
import LeanFX2.Foundation.PolyCell.Core.CellSort
import LeanFX2.Foundation.PolyCell.Core.RawCell

/-! # Foundation/PolyCell/Core/CellBoundary — boundary data for v2 cells

This file ships the v2 boundary-data computation: `CellBoundary`
returns the TYPE of boundary data a certified cell carries at each
dimension.  It is the v2 counterpart to v1's `CellBoundary`
(`Foundation/PolyCell/Core/Certified.lean`).

## The dimension stratification of boundary data

A certified cell at dimension `n` carries an `n-1`-dimensional
boundary describing where it lives in the polygraph:

* **Dim 0 cells** (terms, types, contexts, modes, etc.) have no
  lower-dim boundary — the boundary type is `Unit` (one inhabitant,
  trivially constructible).

* **Dim (n+1) cells** (rewrite steps, equality cells, composites)
  have a PAIR boundary: a SOURCE endpoint at dim n and a TARGET
  endpoint at dim n.  In v2 these endpoints are RAW cells
  (`RawCell scope`), because the certified layer pins their dim
  through the certified sub-cell parameter type — not through the
  boundary value's type.

This recursive structure parallels Brunerie's omega-cellular sets and
the polygraph paradigm: an n-cell has (n-1)-dimensional boundary
data, which is itself n-1 cellular data, etc.  At dim 0, the recursion
hits the trivial base case.

## Why the source/target are raw, not certified

In v1, the boundary was a pair of typed `PolyTerm profile dimension`
values — the boundary type CARRIED the dim constraint at the type
level.  This was the very source of the propext walls that motivated
the v2 architecture: pattern-matching on a `(dim, term)` pair
triggered equation-compiler reasoning over the Nat dim index.

In v2, the boundary carries RAW cells (`RawCell scope`, dim
computed not indexed).  The dim constraint is enforced ELSEWHERE:

* The certified sub-cell parameters (`PolyCell profile cellSort
  source.dim scope sourceBoundary source` etc.) demand source and
  target be CERTIFIED at the correct dim through their TYPE
  signature.

* The `HasEqualDim source target` parameter explicitly reconciles
  the two endpoints' computed dims as a propext-free `Nat` equation.

This decoupling is the SPIKE-1 architectural payoff: boundary data
becomes raw-only (zero type-level dim reasoning), and dim
correctness gets enforced via separate certified parameters.

## The profile parameter

`CellBoundary` takes a `PolyProfile` parameter for spec alignment
with `polycell.md` §4 and forward-compat: future profiles may
restrict WHICH raw cells are admissible as boundaries (e.g. a
constructive-only profile rejecting HoTT cells in boundary
positions).  Under `fxProfile`, the boundary is unconstrained beyond
the dim stratification — the parameter is phantom for now.

The underscore prefix `_profile` documents the intentional-but-
currently-unused parameter without triggering Lean's
unused-variable warning.

## Why `def` rather than `inductive`

A `def` returning `Unit` for dim 0 and a pair type for dim n+1
gives a SIMPLE, MATCH-FREE consumer interface:

* `cellBoundary : CellBoundary fxProfile .term 0 scope = ()` —
  the unique inhabitant of Unit.
* `cellBoundary : CellBoundary fxProfile .term (n+1) scope =
  (source, target)` — a pair, destructure with `let (s, t) :=
  cellBoundary`.

An inductive declaration would force pattern-matching dispatch on
dim, re-introducing the indexed-inductive complexity the v2
architecture removed.

## Zero-axiom verification

Pattern matches Nat's two constructors directly (`0` and `_ + 1`)
to avoid the wildcard-pattern propext-leak class catalogued in
`feedback_lean_match_propext_recipe.md`.  Audit-gated in
`Tools/AuditAll/AuditPolyCell.lean`.
-/

namespace LeanFX2.Foundation.PolyCell.Core

/-- Boundary-data TYPE for a v2 certified cell at the given
dimension.

Reads as a sentence: "for any profile, sort, dimension, and scope,
the boundary type is either Unit (dim 0) or a pair of raw cells
(dim n+1)".  The dim parameter is what discriminates: the function
is a type-level dispatch on dim.

Currently profile-agnostic (the `_profile` parameter is forward-
compat).  Future per-profile restrictions refine the body without
breaking the existing surface. -/
def CellBoundary (_profile : PolyProfile) :
    CellSort → Nat → Nat → Type
  | _, 0, _ => Unit
  | _, _ + 1, scope => RawCell scope × RawCell scope

/-- The dim-0 boundary type is `Unit`.

Useful for downstream code that wants to rewrite a `CellBoundary`
expression at dim 0 into the canonical `Unit` form for further
reasoning.  Closes by `rfl` since `CellBoundary` is by-arms
defined and the dim-0 arm is a literal Unit. -/
theorem CellBoundary_zero {profile : PolyProfile} (cellSort : CellSort)
    (scope : Nat) :
    CellBoundary profile cellSort 0 scope = Unit :=
  rfl

/-- The dim-(n+1) boundary type is a pair of raw cells at scope.

Useful for downstream code that destructures the boundary.  Closes
by `rfl` since the dim-(n+1) arm of `CellBoundary` is literally
the product type. -/
theorem CellBoundary_succ {profile : PolyProfile} (cellSort : CellSort)
    (dimension scope : Nat) :
    CellBoundary profile cellSort (dimension + 1) scope =
      (RawCell scope × RawCell scope) :=
  rfl

/-- The canonical dim-0 boundary value.

A `CellBoundary profile sort 0 scope` is `Unit` (by
`CellBoundary_zero`), so its unique inhabitant is `()`.  Provided
here as a named value so downstream code can write
`CellBoundary.trivial` instead of an opaque `()` cast through the
type-equation. -/
@[reducible] def CellBoundary.trivial {profile : PolyProfile}
    {cellSort : CellSort} {scope : Nat} :
    CellBoundary profile cellSort 0 scope :=
  ()

/-- Construct a dim-(n+1) boundary from a source and target raw cell.

A `CellBoundary profile sort (n+1) scope` is `RawCell scope ×
RawCell scope` (by `CellBoundary_succ`), so we build it from
source and target raw cells directly.

Provided here as a named smart constructor so call sites read as
`CellBoundary.endpoints source target` rather than a bare pair
construction through the type-equation. -/
@[reducible] def CellBoundary.endpoints {profile : PolyProfile}
    {cellSort : CellSort} {dimension scope : Nat}
    (source target : RawCell scope) :
    CellBoundary profile cellSort (dimension + 1) scope :=
  (source, target)

end LeanFX2.Foundation.PolyCell.Core
