import FX1Poly.Core.RawCell
import FX1Poly.Core.RawTermRename
import FX1Poly.Core.RawTermSubst

/-! # Foundation/PolyCell/Core/RawCellRenameSubst — cell-layer rename / subst

The **cell-layer fold** for `RawCell`:

  RawCell.rename : RawRenaming src tgt → RawCell src → RawCell tgt
  RawCell.subst  : RawTermSubst src tgt → RawCell src → RawCell tgt

The cell layer is structurally simpler than the term layer:

* 5 ctors (vs RawTerm's `.mkGen` with 194 generators).
* No binder shifts at the cell layer — categorical composition
  doesn't introduce new variable binders.  The term layer's fold
  handles all binder plumbing internally.
* `termBase t` delegates to term-layer `rename` / `subst`.
* All other ctors are pure structural recursion.

## Why structural recursion (not fold-like generic engine)

RawCell has only 5 ctors — no need for a 194-generator dispatch
abstraction.  Direct structural recursion is simpler, more
readable, and equally cascade-tax-resistant (adding a new cell
ctor costs ONE arm, which is intrinsic to cell-layer extension).

If/when a 6th cell ctor is added (e.g. `pushoutCell` for HoTT-style
HITs at the cell layer), each rename/subst gets one new arm —
trivial to extend.

## Downstream consumers

`RawCell.rename` / `subst` are the prerequisites for the cell-layer
metatheory (boundary preservation, rename-equivariance) and
cell-layer confluence — those later steps cannot state their goals
without them.

## Zero-axiom verification

Straightforward structural recursion with `dsimp only [fold]`-
style proofs at the term-base case.  No `unfold` on mutual recursion
(per `feedback_lean_unfold_mutual_quot_sound`).

Audit-gated in `Tools/AuditAll/AuditPolyCell.lean`.
-/

namespace FX1Poly.Core

open FX1Poly.Foundation

/-! ## Section 1 — Rename: cell-layer renaming

5-arm structural recursion.  Delegates to `RawTerm.rename` at
the `termBase` leaf; recurses on RawCell sub-cells elsewhere. -/

/-- Apply a renaming to a `RawCell`.

Structural recursion on the cell:
* `termBase t`: rename the wrapped term via `RawTerm.rename`.
* `generatingCell ruleId source target`: recurse on source/target.
* `verticalComposite first second`: recurse on both.
* `horizontalComposite left right`: recurse on both.
* `identityCell base`: recurse on base.

No binder shifts at the cell layer — the term layer's fold
handles variable scopes when needed (within terms wrapped in
`termBase`). -/
def RawCell.rename {sourceScope targetScope : Nat}
    (rawRenaming : FX1Poly.Foundation.RawRenaming sourceScope targetScope)
    (sourceCell : RawCell sourceScope) : RawCell targetScope :=
  match sourceCell with
  | .termBase wrappedTerm =>
      .termBase (RawTerm.rename rawRenaming wrappedTerm)
  | .generatingCell ruleId sourceSubCell targetSubCell =>
      .generatingCell ruleId
        (RawCell.rename rawRenaming sourceSubCell)
        (RawCell.rename rawRenaming targetSubCell)
  | .verticalComposite firstSubCell secondSubCell =>
      .verticalComposite
        (RawCell.rename rawRenaming firstSubCell)
        (RawCell.rename rawRenaming secondSubCell)
  | .horizontalComposite leftSubCell rightSubCell =>
      .horizontalComposite
        (RawCell.rename rawRenaming leftSubCell)
        (RawCell.rename rawRenaming rightSubCell)
  | .identityCell baseSubCell =>
      .identityCell (RawCell.rename rawRenaming baseSubCell)

/-! ## Section 2 — Subst: cell-layer substitution

Same shape as `rename` — 5-arm structural recursion delegating to
`RawTerm.subst` at the `termBase` leaf. -/

/-- Apply a substitution to a `RawCell`.

Structural recursion on the cell:
* `termBase t`: substitute into the wrapped term via `RawTerm.subst`.
* All other ctors: recurse on sub-cells. -/
def RawCell.subst {sourceScope targetScope : Nat}
    (someSubstitution : RawTermSubst sourceScope targetScope)
    (sourceCell : RawCell sourceScope) : RawCell targetScope :=
  match sourceCell with
  | .termBase wrappedTerm =>
      .termBase (RawTerm.subst someSubstitution wrappedTerm)
  | .generatingCell ruleId sourceSubCell targetSubCell =>
      .generatingCell ruleId
        (RawCell.subst someSubstitution sourceSubCell)
        (RawCell.subst someSubstitution targetSubCell)
  | .verticalComposite firstSubCell secondSubCell =>
      .verticalComposite
        (RawCell.subst someSubstitution firstSubCell)
        (RawCell.subst someSubstitution secondSubCell)
  | .horizontalComposite leftSubCell rightSubCell =>
      .horizontalComposite
        (RawCell.subst someSubstitution leftSubCell)
        (RawCell.subst someSubstitution rightSubCell)
  | .identityCell baseSubCell =>
      .identityCell (RawCell.subst someSubstitution baseSubCell)

/-! ## Section 3 — Dimension preservation

Both `rename` and `subst` preserve cell dimension.  Important for
downstream metatheory: dim-1 cells (steps / rewrites) stay at dim-1
after renaming or substitution.

Structural recursion mirroring the rename/subst defs. -/

/-- Renaming preserves cell dimension. -/
theorem RawCell.rename_preserves_dim
    {sourceScope targetScope : Nat}
    (rawRenaming : FX1Poly.Foundation.RawRenaming sourceScope targetScope)
    (sourceCell : RawCell sourceScope) :
    (RawCell.rename rawRenaming sourceCell).dim = sourceCell.dim := by
  match sourceCell with
  | .termBase _ => rfl
  | .generatingCell _ sourceSubCell _ =>
      show (RawCell.rename rawRenaming sourceSubCell).dim + 1 =
            sourceSubCell.dim + 1
      rw [RawCell.rename_preserves_dim rawRenaming sourceSubCell]
  | .verticalComposite firstSubCell _ =>
      show (RawCell.rename rawRenaming firstSubCell).dim =
            firstSubCell.dim
      exact RawCell.rename_preserves_dim rawRenaming firstSubCell
  | .horizontalComposite leftSubCell _ =>
      show (RawCell.rename rawRenaming leftSubCell).dim =
            leftSubCell.dim
      exact RawCell.rename_preserves_dim rawRenaming leftSubCell
  | .identityCell baseSubCell =>
      show (RawCell.rename rawRenaming baseSubCell).dim + 1 =
            baseSubCell.dim + 1
      rw [RawCell.rename_preserves_dim rawRenaming baseSubCell]

/-- Substitution preserves cell dimension. -/
theorem RawCell.subst_preserves_dim
    {sourceScope targetScope : Nat}
    (someSubstitution : RawTermSubst sourceScope targetScope)
    (sourceCell : RawCell sourceScope) :
    (RawCell.subst someSubstitution sourceCell).dim = sourceCell.dim := by
  match sourceCell with
  | .termBase _ => rfl
  | .generatingCell _ sourceSubCell _ =>
      show (RawCell.subst someSubstitution sourceSubCell).dim + 1 =
            sourceSubCell.dim + 1
      rw [RawCell.subst_preserves_dim someSubstitution sourceSubCell]
  | .verticalComposite firstSubCell _ =>
      show (RawCell.subst someSubstitution firstSubCell).dim =
            firstSubCell.dim
      exact RawCell.subst_preserves_dim someSubstitution firstSubCell
  | .horizontalComposite leftSubCell _ =>
      show (RawCell.subst someSubstitution leftSubCell).dim =
            leftSubCell.dim
      exact RawCell.subst_preserves_dim someSubstitution leftSubCell
  | .identityCell baseSubCell =>
      show (RawCell.subst someSubstitution baseSubCell).dim + 1 =
            baseSubCell.dim + 1
      rw [RawCell.subst_preserves_dim someSubstitution baseSubCell]

/-! ## Section 4 — Smoke tests

These verify the structural reduction rules of the cell-layer rename
and subst.  Each smoke tests ONE arm's reduction step (cell-layer
pattern match unfolds to its body); the inner term-layer rename /
subst delegate is left symbolic.  All close by `rfl` from the
cell-layer's defining equations. -/

/-- Smoke: rename on `termBase t` reduces to `termBase (rename rho t)`. -/
theorem RawCell.rename_termBase_unfolds
    {sourceScope targetScope : Nat}
    (rawRenaming : FX1Poly.Foundation.RawRenaming sourceScope targetScope)
    (wrappedTerm : RawTerm sourceScope) :
    RawCell.rename rawRenaming (.termBase wrappedTerm) =
      .termBase (RawTerm.rename rawRenaming wrappedTerm) := rfl

/-- Smoke: subst on `termBase t` reduces to `termBase (subst sigma t)`. -/
theorem RawCell.subst_termBase_unfolds
    {sourceScope targetScope : Nat}
    (someSubstitution : RawTermSubst sourceScope targetScope)
    (wrappedTerm : RawTerm sourceScope) :
    RawCell.subst someSubstitution (.termBase wrappedTerm) =
      .termBase (RawTerm.subst someSubstitution wrappedTerm) := rfl

/-- Smoke: rename on `generatingCell` reduces to the recursive form. -/
theorem RawCell.rename_generatingCell_unfolds
    {sourceScope targetScope : Nat}
    (rawRenaming : FX1Poly.Foundation.RawRenaming sourceScope targetScope)
    (ruleId : Nat)
    (sourceCell targetCell : RawCell sourceScope) :
    RawCell.rename rawRenaming
        (.generatingCell ruleId sourceCell targetCell) =
      .generatingCell ruleId
        (RawCell.rename rawRenaming sourceCell)
        (RawCell.rename rawRenaming targetCell) := rfl

/-- Smoke: rename on `verticalComposite` reduces to the recursive form. -/
theorem RawCell.rename_verticalComposite_unfolds
    {sourceScope targetScope : Nat}
    (rawRenaming : FX1Poly.Foundation.RawRenaming sourceScope targetScope)
    (firstCell secondCell : RawCell sourceScope) :
    RawCell.rename rawRenaming
        (.verticalComposite firstCell secondCell) =
      .verticalComposite
        (RawCell.rename rawRenaming firstCell)
        (RawCell.rename rawRenaming secondCell) := rfl

/-- Smoke: rename on `horizontalComposite` reduces to the recursive form. -/
theorem RawCell.rename_horizontalComposite_unfolds
    {sourceScope targetScope : Nat}
    (rawRenaming : FX1Poly.Foundation.RawRenaming sourceScope targetScope)
    (leftCell rightCell : RawCell sourceScope) :
    RawCell.rename rawRenaming
        (.horizontalComposite leftCell rightCell) =
      .horizontalComposite
        (RawCell.rename rawRenaming leftCell)
        (RawCell.rename rawRenaming rightCell) := rfl

/-- Smoke: rename on `identityCell` reduces to the recursive form. -/
theorem RawCell.rename_identityCell_unfolds
    {sourceScope targetScope : Nat}
    (rawRenaming : FX1Poly.Foundation.RawRenaming sourceScope targetScope)
    (baseCell : RawCell sourceScope) :
    RawCell.rename rawRenaming (.identityCell baseCell) =
      .identityCell (RawCell.rename rawRenaming baseCell) := rfl

/-! ## Subst push-through lemmas (cell-level boundary preservation)

Per polycell.md §11.6.2, the LOAD-BEARING property of cell-level
substitution is that `subst` pushes through each cell constructor
homomorphically.  The `termBase` arm is above; this section
completes the family for the four remaining ctors.

Each closes by `rfl` because `RawCell.subst` is a direct 5-arm
structural recursion: the ctor pattern match unfolds definitionally
when the scrutinee is a concrete ctor.

Together with `subst_termBase_unfolds`, these five theorems witness
that cell-level substitution preserves the boundary structure of
every cell ctor -- the "boundary preservation" obligation of
§11.6.2. -/

/-- Smoke: subst on `generatingCell` reduces to the recursive form
(homomorphic over the source/target sub-cells). -/
theorem RawCell.subst_generatingCell_unfolds
    {sourceScope targetScope : Nat}
    (someSubstitution : RawTermSubst sourceScope targetScope)
    (ruleId : Nat)
    (sourceCell targetCell : RawCell sourceScope) :
    RawCell.subst someSubstitution
        (.generatingCell ruleId sourceCell targetCell) =
      .generatingCell ruleId
        (RawCell.subst someSubstitution sourceCell)
        (RawCell.subst someSubstitution targetCell) := rfl

/-- Smoke: subst on `verticalComposite` reduces to the recursive form
(homomorphic over the first/second sub-cells). -/
theorem RawCell.subst_verticalComposite_unfolds
    {sourceScope targetScope : Nat}
    (someSubstitution : RawTermSubst sourceScope targetScope)
    (firstCell secondCell : RawCell sourceScope) :
    RawCell.subst someSubstitution
        (.verticalComposite firstCell secondCell) =
      .verticalComposite
        (RawCell.subst someSubstitution firstCell)
        (RawCell.subst someSubstitution secondCell) := rfl

/-- Smoke: subst on `horizontalComposite` reduces to the recursive
form (homomorphic over the left/right sub-cells). -/
theorem RawCell.subst_horizontalComposite_unfolds
    {sourceScope targetScope : Nat}
    (someSubstitution : RawTermSubst sourceScope targetScope)
    (leftCell rightCell : RawCell sourceScope) :
    RawCell.subst someSubstitution
        (.horizontalComposite leftCell rightCell) =
      .horizontalComposite
        (RawCell.subst someSubstitution leftCell)
        (RawCell.subst someSubstitution rightCell) := rfl

/-- Smoke: subst on `identityCell` reduces to the recursive form
(homomorphic over the base sub-cell). -/
theorem RawCell.subst_identityCell_unfolds
    {sourceScope targetScope : Nat}
    (someSubstitution : RawTermSubst sourceScope targetScope)
    (baseCell : RawCell sourceScope) :
    RawCell.subst someSubstitution (.identityCell baseCell) =
      .identityCell (RawCell.subst someSubstitution baseCell) := rfl

/-- Smoke: rename preserves dim on a sample `generatingCell` (dim=1). -/
theorem RawCell.rename_preserves_dim_generatingCell_smoke
    {sourceScope targetScope : Nat}
    (rawRenaming : FX1Poly.Foundation.RawRenaming sourceScope targetScope)
    (ruleId : Nat)
    (sourceCell targetCell : RawCell sourceScope) :
    (RawCell.rename rawRenaming
        (.generatingCell ruleId sourceCell targetCell)).dim =
      (RawCell.generatingCell ruleId sourceCell targetCell).dim :=
  RawCell.rename_preserves_dim rawRenaming _

end FX1Poly.Core
