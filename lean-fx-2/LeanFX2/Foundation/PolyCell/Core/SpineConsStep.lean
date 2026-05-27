import LeanFX2.Foundation.PolyCell.Core.CertifiedTermSpineProjections
import LeanFX2.Foundation.PolyCell.Core.GeneratorChildSpecsDim0

/-! # Foundation/PolyCell/Core/SpineConsStep
   — non-recursive cons-step helper for the spine renamer/substituter

V2-L3.1 phase D step 34 (2026-05-27).  Ships the **spine-side
inductive step** of the eventual structural-induction mutual block —
packaged as a NON-RECURSIVE definition.

## What this ships

`CertifiedTermSpine.consStep_dim0Trivial` — given:

  * `hHeadDim0 : headSpec.cellDimension = 0`,
  * a pre-built head cell at dim 0 / trivial boundary / target scope
    over a renamed/substituted `newHeadRaw`,
  * a pre-built rest spine over renamed/substituted `newRestRaws`,

construct a `CertifiedTermSpine ... (headSpec :: restSpecs) tgtScope
(headSpec.scopeShift :: restShifts) (.childCons newHeadRaw newRestRaws)`.

This is the cons construction step factored out from the spine
recursion's mutual block.  Caller supplies the pre-renamed head cell
(at dim 0 / trivial via `Subsingleton.elim` if needed) and the
recursively-renamed tail.

## Why this matters

The mutual block's spine arm has two architectural challenges:
  1. **Recursion**: well-founded over the spine's children (the
     blocker on `cell` recursion is resolved here since spine
     children are `RawTermChildren`, a non-dependent inductive).
  2. **Dependent cast on cons**: the implicit `headBoundary` on
     `CertifiedTermSpine.cons` requires careful boundary handling.

This file ships (2): the cons step in a non-recursive helper, using
the `generalize` + `subst` pattern from `CertifiedTermSpineProjections.
headAtDim0` to collapse the boundary.  Combined with the cell-step
helpers (`CellNonVarStepRenamer` / `CellNonVarStepSubstituter`), the
mutual block becomes a thin recursive driver.

## Direction-agnostic

The helper does NOT mention `RawTerm.rename` or `RawTerm.subst` —
it takes pre-renamed/substituted raw terms as inputs.  So one helper
serves both directions.  The mutual block's body chooses the
direction by passing the appropriate raw terms.

## Zero-axiom verification

Uses the `generalize` + `subst` + `Subsingleton.elim` pattern proven
clean in `CertifiedTermSpineProjections.headAtDim0` (phase D step 2).
Audit-gated.
-/

namespace LeanFX2.Foundation.PolyCell.Core

open LeanFX2

/-- **Cons-step constructor for the spine, dim-0 / trivial boundary.**

Given a dim-0 hypothesis on `headSpec`, a pre-built head cell at dim
0 / trivial boundary / target scope, and a pre-built rest spine,
construct the cons with the proper `headBoundary` implicit derived
from the dim-0 fact.

Boundary handling: under `hHeadDim0 : headSpec.cellDimension = 0`,
the `CellBoundary profile sort headSpec.cellDimension scope` type
reduces to `Unit` (definitional unfolding), and `Subsingleton.elim`
identifies any inhabitant with `CellBoundary.trivial`.  The `▸`
infix cast aligns the head cell's type at `headSpec.cellDimension`
from the dim-0 form callers provide. -/
def CertifiedTermSpine.consStep_dim0Trivial
    {profile : PolyProfile} {parentScope : Nat}
    {headSpec : ChildSpec} {restSpecs : List ChildSpec}
    {restShifts : List Nat}
    (hHeadDim0 : headSpec.cellDimension = 0)
    {newHeadRaw : RawTerm (parentScope + headSpec.scopeShift)}
    {newRestRaws : RawTermChildren restShifts parentScope}
    (newHeadCell :
      PolyCell profile headSpec.cellSort 0
        (parentScope + headSpec.scopeShift) CellBoundary.trivial
        (.termBase newHeadRaw))
    (newRestSpine :
      CertifiedTermSpine profile restSpecs parentScope restShifts
        newRestRaws) :
    CertifiedTermSpine profile (headSpec :: restSpecs) parentScope
      (headSpec.scopeShift :: restShifts)
      (.childCons newHeadRaw newRestRaws) := by
  -- Use generalize + subst trick (mirror of headAtDim0) to lift
  -- newHeadCell from dim 0 / trivial up to headSpec.cellDimension /
  -- (Subsingleton-derived) boundary.
  -- 1. Construct the new boundary at headSpec.cellDimension level.
  have newHeadBoundary :
      CellBoundary profile headSpec.cellSort headSpec.cellDimension
        (parentScope + headSpec.scopeShift) := by
    rw [hHeadDim0]
    exact CellBoundary.trivial
  -- 2. Cast newHeadCell from (dim 0, .trivial) to (headSpec.cellDimension, newHeadBoundary).
  have newHeadCellLifted :
      PolyCell profile headSpec.cellSort headSpec.cellDimension
        (parentScope + headSpec.scopeShift) newHeadBoundary
        (.termBase newHeadRaw) := by
    -- generalize + subst pattern: introduce a fresh `cellDim` variable
    -- that equals headSpec.cellDimension, then substitute it to 0 via
    -- hHeadDim0.  This rewrites the cell's type into the
    -- headSpec.cellDimension form.
    generalize hCellDim : headSpec.cellDimension = cellDim at newHeadBoundary hHeadDim0
    subst hHeadDim0
    -- After subst, newHeadBoundary at type CellBoundary ... 0 ... = Unit;
    -- Subsingleton.elim identifies it with .trivial.
    haveI : Subsingleton (CellBoundary profile headSpec.cellSort 0
                            (parentScope + headSpec.scopeShift)) :=
      inferInstanceAs (Subsingleton Unit)
    have boundaryEq : newHeadBoundary = CellBoundary.trivial :=
      Subsingleton.elim _ _
    exact boundaryEq ▸ newHeadCell
  -- 3. Build the cons using the lifted boundary + cell.
  exact CertifiedTermSpine.cons
    (headBoundary := newHeadBoundary)
    newHeadCellLifted
    newRestSpine

/-- **Nil-step constructor for the spine.**

Trivially `.nil`.  Shipped as the symmetric counterpart to
`consStep_dim0Trivial` so the mutual block's spine arm's `nil` case
reads as a one-liner alongside the cons case. -/
def CertifiedTermSpine.nilStep
    {profile : PolyProfile} {parentScope : Nat} :
    CertifiedTermSpine profile [] parentScope []
      (.childNil : RawTermChildren [] parentScope) :=
  .nil

end LeanFX2.Foundation.PolyCell.Core
