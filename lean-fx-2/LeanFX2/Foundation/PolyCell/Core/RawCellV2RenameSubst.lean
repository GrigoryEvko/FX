import LeanFX2.Foundation.PolyCell.Core.RawCellV2
import LeanFX2.Foundation.PolyCell.Core.RawTermV2Rename
import LeanFX2.Foundation.PolyCell.Core.RawTermV2Subst

/-! # Foundation/PolyCell/Core/RawCellV2RenameSubst — cell-layer rename / subst

V2-L2.8.  This file shipss the **cell-layer fold** for `RawCellV2`:

  RawCellV2.rename : RawRenaming src tgt → RawCellV2 src → RawCellV2 tgt
  RawCellV2.subst  : RawTermSubstV2 src tgt → RawCellV2 src → RawCellV2 tgt

The cell layer is structurally simpler than the term layer:

* 5 ctors (vs RawTermV2's `.mkGen` with 194 generators).
* No binder shifts at the cell layer — categorical composition
  doesn't introduce new variable binders.  The term layer's foldV2
  (#177) handles all binder plumbing internally.
* `termBase t` delegates to term-layer `rename` / `subst` (#178 / #180).
* All other ctors are pure structural recursion.

## Position in the V2 ladder

V2-L2 (the Allais-style fold layer) consists of three sub-layers:
  * V2-L2.1-L2.7 — the TERM layer (foldV2 + Action laws).  COMPLETE.
  * V2-L2.8       — the CELL layer (rename/subst lift).  THIS COMMIT.
  * V2-L2.9-L2.11 — cascade-deletion demo + subst0/β + audit gates.

After this commit, the cell layer has its own rename/subst —
exactly mirroring v1's `PolyCell.rename` / `PolyCell.subst` but
over the un-indexed scope-only-indexed v2 representation.

## Why structural recursion (not foldV2-like generic engine)

RawCellV2 has only 5 ctors — no need for a 194-generator dispatch
abstraction.  Direct structural recursion is simpler, more
readable, and equally cascade-tax-resistant (adding a new cell
ctor costs ONE arm, which is intrinsic to cell-layer extension).

If/when we add a 6th cell ctor (e.g. `pushoutCell` for HoTT-style
HITs at the cell layer), each rename/subst gets one new arm —
trivial to extend.

## Future cascade savings

This file enables the cell-layer metatheory (V2-L2.12 boundary
preservation, V2-L2.13 rename-equivariance) and the cell-layer
confluence (V2-L3.x).  Without `RawCellV2.rename` / `subst`, those
later steps can't even state their goals.

## Zero-axiom verification

Straightforward structural recursion with `dsimp only [foldV2]`-
style proofs at the term-base case.  No `unfold` on mutual recursion
(per `feedback_lean_unfold_mutual_quot_sound`).

Audit-gated in `Tools/AuditAll/AuditPolyCell.lean`.
-/

namespace LeanFX2.Foundation.PolyCell.Core

open LeanFX2

/-! ## Section 1 — Rename: cell-layer renaming

5-arm structural recursion.  Delegates to `RawTermV2.rename` at
the `termBase` leaf; recurses on RawCellV2 sub-cells elsewhere. -/

/-- Apply a renaming to a `RawCellV2`.

Structural recursion on the cell:
* `termBase t`: rename the wrapped term via `RawTermV2.rename`.
* `generatingCell ruleId source target`: recurse on source/target.
* `verticalComposite first second`: recurse on both.
* `horizontalComposite left right`: recurse on both.
* `identityCell base`: recurse on base.

No binder shifts at the cell layer — the term layer's foldV2
handles variable scopes when needed (within terms wrapped in
`termBase`). -/
def RawCellV2.rename {sourceScope targetScope : Nat}
    (rawRenaming : LeanFX2.RawRenaming sourceScope targetScope)
    (sourceCell : RawCellV2 sourceScope) : RawCellV2 targetScope :=
  match sourceCell with
  | .termBase wrappedTerm =>
      .termBase (RawTermV2.rename rawRenaming wrappedTerm)
  | .generatingCell ruleId sourceSubCell targetSubCell =>
      .generatingCell ruleId
        (RawCellV2.rename rawRenaming sourceSubCell)
        (RawCellV2.rename rawRenaming targetSubCell)
  | .verticalComposite firstSubCell secondSubCell =>
      .verticalComposite
        (RawCellV2.rename rawRenaming firstSubCell)
        (RawCellV2.rename rawRenaming secondSubCell)
  | .horizontalComposite leftSubCell rightSubCell =>
      .horizontalComposite
        (RawCellV2.rename rawRenaming leftSubCell)
        (RawCellV2.rename rawRenaming rightSubCell)
  | .identityCell baseSubCell =>
      .identityCell (RawCellV2.rename rawRenaming baseSubCell)

/-! ## Section 2 — Subst: cell-layer substitution

Same shape as `rename` — 5-arm structural recursion delegating to
`RawTermV2.subst` at the `termBase` leaf. -/

/-- Apply a substitution to a `RawCellV2`.

Structural recursion on the cell:
* `termBase t`: substitute into the wrapped term via `RawTermV2.subst`.
* All other ctors: recurse on sub-cells. -/
def RawCellV2.subst {sourceScope targetScope : Nat}
    (someSubstitution : RawTermSubstV2 sourceScope targetScope)
    (sourceCell : RawCellV2 sourceScope) : RawCellV2 targetScope :=
  match sourceCell with
  | .termBase wrappedTerm =>
      .termBase (RawTermV2.subst someSubstitution wrappedTerm)
  | .generatingCell ruleId sourceSubCell targetSubCell =>
      .generatingCell ruleId
        (RawCellV2.subst someSubstitution sourceSubCell)
        (RawCellV2.subst someSubstitution targetSubCell)
  | .verticalComposite firstSubCell secondSubCell =>
      .verticalComposite
        (RawCellV2.subst someSubstitution firstSubCell)
        (RawCellV2.subst someSubstitution secondSubCell)
  | .horizontalComposite leftSubCell rightSubCell =>
      .horizontalComposite
        (RawCellV2.subst someSubstitution leftSubCell)
        (RawCellV2.subst someSubstitution rightSubCell)
  | .identityCell baseSubCell =>
      .identityCell (RawCellV2.subst someSubstitution baseSubCell)

/-! ## Section 3 — Dimension preservation

Both `rename` and `subst` preserve cell dimension.  Important for
downstream metatheory: dim-1 cells (steps / rewrites) stay at dim-1
after renaming or substitution.

Structural recursion mirroring the rename/subst defs. -/

/-- Renaming preserves cell dimension. -/
theorem RawCellV2.rename_preserves_dim
    {sourceScope targetScope : Nat}
    (rawRenaming : LeanFX2.RawRenaming sourceScope targetScope)
    (sourceCell : RawCellV2 sourceScope) :
    (RawCellV2.rename rawRenaming sourceCell).dim = sourceCell.dim := by
  match sourceCell with
  | .termBase _ => rfl
  | .generatingCell _ sourceSubCell _ =>
      show (RawCellV2.rename rawRenaming sourceSubCell).dim + 1 =
            sourceSubCell.dim + 1
      rw [RawCellV2.rename_preserves_dim rawRenaming sourceSubCell]
  | .verticalComposite firstSubCell _ =>
      show (RawCellV2.rename rawRenaming firstSubCell).dim =
            firstSubCell.dim
      exact RawCellV2.rename_preserves_dim rawRenaming firstSubCell
  | .horizontalComposite leftSubCell _ =>
      show (RawCellV2.rename rawRenaming leftSubCell).dim =
            leftSubCell.dim
      exact RawCellV2.rename_preserves_dim rawRenaming leftSubCell
  | .identityCell baseSubCell =>
      show (RawCellV2.rename rawRenaming baseSubCell).dim + 1 =
            baseSubCell.dim + 1
      rw [RawCellV2.rename_preserves_dim rawRenaming baseSubCell]

/-- Substitution preserves cell dimension. -/
theorem RawCellV2.subst_preserves_dim
    {sourceScope targetScope : Nat}
    (someSubstitution : RawTermSubstV2 sourceScope targetScope)
    (sourceCell : RawCellV2 sourceScope) :
    (RawCellV2.subst someSubstitution sourceCell).dim = sourceCell.dim := by
  match sourceCell with
  | .termBase _ => rfl
  | .generatingCell _ sourceSubCell _ =>
      show (RawCellV2.subst someSubstitution sourceSubCell).dim + 1 =
            sourceSubCell.dim + 1
      rw [RawCellV2.subst_preserves_dim someSubstitution sourceSubCell]
  | .verticalComposite firstSubCell _ =>
      show (RawCellV2.subst someSubstitution firstSubCell).dim =
            firstSubCell.dim
      exact RawCellV2.subst_preserves_dim someSubstitution firstSubCell
  | .horizontalComposite leftSubCell _ =>
      show (RawCellV2.subst someSubstitution leftSubCell).dim =
            leftSubCell.dim
      exact RawCellV2.subst_preserves_dim someSubstitution leftSubCell
  | .identityCell baseSubCell =>
      show (RawCellV2.subst someSubstitution baseSubCell).dim + 1 =
            baseSubCell.dim + 1
      rw [RawCellV2.subst_preserves_dim someSubstitution baseSubCell]

/-! ## Section 4 — Smoke tests

These verify the structural reduction rules of the cell-layer rename
and subst.  Each smoke tests ONE arm's reduction step (cell-layer
pattern match unfolds to its body); the inner term-layer rename /
subst delegate is left symbolic.  All close by `rfl` from the
cell-layer's defining equations. -/

/-- Smoke: rename on `termBase t` reduces to `termBase (rename rho t)`. -/
theorem RawCellV2.rename_termBase_unfolds
    {sourceScope targetScope : Nat}
    (rawRenaming : LeanFX2.RawRenaming sourceScope targetScope)
    (wrappedTerm : RawTermV2 sourceScope) :
    RawCellV2.rename rawRenaming (.termBase wrappedTerm) =
      .termBase (RawTermV2.rename rawRenaming wrappedTerm) := rfl

/-- Smoke: subst on `termBase t` reduces to `termBase (subst sigma t)`. -/
theorem RawCellV2.subst_termBase_unfolds
    {sourceScope targetScope : Nat}
    (someSubstitution : RawTermSubstV2 sourceScope targetScope)
    (wrappedTerm : RawTermV2 sourceScope) :
    RawCellV2.subst someSubstitution (.termBase wrappedTerm) =
      .termBase (RawTermV2.subst someSubstitution wrappedTerm) := rfl

/-- Smoke: rename on `generatingCell` reduces to the recursive form. -/
theorem RawCellV2.rename_generatingCell_unfolds
    {sourceScope targetScope : Nat}
    (rawRenaming : LeanFX2.RawRenaming sourceScope targetScope)
    (ruleId : Nat)
    (sourceCell targetCell : RawCellV2 sourceScope) :
    RawCellV2.rename rawRenaming
        (.generatingCell ruleId sourceCell targetCell) =
      .generatingCell ruleId
        (RawCellV2.rename rawRenaming sourceCell)
        (RawCellV2.rename rawRenaming targetCell) := rfl

/-- Smoke: rename on `verticalComposite` reduces to the recursive form. -/
theorem RawCellV2.rename_verticalComposite_unfolds
    {sourceScope targetScope : Nat}
    (rawRenaming : LeanFX2.RawRenaming sourceScope targetScope)
    (firstCell secondCell : RawCellV2 sourceScope) :
    RawCellV2.rename rawRenaming
        (.verticalComposite firstCell secondCell) =
      .verticalComposite
        (RawCellV2.rename rawRenaming firstCell)
        (RawCellV2.rename rawRenaming secondCell) := rfl

/-- Smoke: rename on `horizontalComposite` reduces to the recursive form. -/
theorem RawCellV2.rename_horizontalComposite_unfolds
    {sourceScope targetScope : Nat}
    (rawRenaming : LeanFX2.RawRenaming sourceScope targetScope)
    (leftCell rightCell : RawCellV2 sourceScope) :
    RawCellV2.rename rawRenaming
        (.horizontalComposite leftCell rightCell) =
      .horizontalComposite
        (RawCellV2.rename rawRenaming leftCell)
        (RawCellV2.rename rawRenaming rightCell) := rfl

/-- Smoke: rename on `identityCell` reduces to the recursive form. -/
theorem RawCellV2.rename_identityCell_unfolds
    {sourceScope targetScope : Nat}
    (rawRenaming : LeanFX2.RawRenaming sourceScope targetScope)
    (baseCell : RawCellV2 sourceScope) :
    RawCellV2.rename rawRenaming (.identityCell baseCell) =
      .identityCell (RawCellV2.rename rawRenaming baseCell) := rfl

/-- Smoke: rename preserves dim on a sample `generatingCell` (dim=1). -/
theorem RawCellV2.rename_preserves_dim_generatingCell_smoke
    {sourceScope targetScope : Nat}
    (rawRenaming : LeanFX2.RawRenaming sourceScope targetScope)
    (ruleId : Nat)
    (sourceCell targetCell : RawCellV2 sourceScope) :
    (RawCellV2.rename rawRenaming
        (.generatingCell ruleId sourceCell targetCell)).dim =
      (RawCellV2.generatingCell ruleId sourceCell targetCell).dim :=
  RawCellV2.rename_preserves_dim rawRenaming _

end LeanFX2.Foundation.PolyCell.Core
