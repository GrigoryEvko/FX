import FX1Poly.Core.RawCellRenameSubst
import FX1Poly.Core.RawTermRenameComposeFusion
import FX1Poly.Core.RawTermSubstCompose
import FX1Poly.Core.RawTermSubstIdentity
import FX1Poly.Core.RawTermRenameSubstCommute
import FX1Poly.Core.RawTermSubstRenameCommute

/-! # Foundation/PolyCell/Core/RawCellCascadeLaws — cell-layer cascade laws

The cell-layer instances of the five canonical substitution-algebra
laws, each a five-arm structural recursion citing the corresponding
term-layer Allais theorem at the `termBase` leaf.  This is the
cell-layer surfacing of the term-layer Action laws, lifted through
the structural fold.

## The five cascade lemmas

One per term-layer Action law:

| Cell-layer theorem             | Cites term-layer                |
|--------------------------------|---------------------------------|
| `RawCell.rename_compose`       | `RawTerm.rename_compose`        |
| `RawCell.subst_compose`        | `RawTerm.subst_compose`         |
| `RawCell.subst_identity_apply` | `RawTerm.subst_identity_apply`  |
| `RawCell.rename_subst_commute` | `RawTerm.rename_subst_commute`  |
| `RawCell.subst_rename_commute` | `RawTerm.subst_rename_commute`  |

Each cell-layer theorem is one 5-arm `match`: the `termBase` arm
cites the term-layer lemma in a single line; the four composite/
identity arms call the same theorem recursively on sub-cells.

These exist so downstream consumers (boundary preservation, subject
reduction, confluence) can cite cell-layer compose/identity/commute
laws without re-running the cell-layer recursion themselves.

## Zero-axiom verification

All five cell-layer lemmas pass `#assert_no_axioms`.  Each smoke
theorem (per-arm reduction equality at a specific cell shape) also
passes.  Gated in `Tools/AuditAll/AuditPolyCell.lean`.

The cell layer has the full substitution-algebra API: rename, subst,
rename_compose, subst_compose, subst_identity, rename_subst_commute,
subst_rename_commute — every law downstream metatheory needs.

## On the design choice "structural recursion vs fold abstraction"

The cell layer has 5 ctors and no binder shifts.  A fold-like
generic engine at the cell layer would buy nothing because:

* No cascade savings: 5 arms ≈ 5 arms whether you go generic or not.
* No abstraction savings: there's no binder plumbing to centralize.
* Net loss: a generic cell-fold would add ~200 lines of dispatch
  machinery to save zero downstream lines.

Direct match-form structural recursion is the right tool at this
layer.  Future extensions (adding `pushoutCell` for HoTT-style HITs)
would cost ONE arm per cascade lemma (~5 lines), so total marginal
cost per new cell ctor is ~25 lines across the five cascade lemmas.
That's the "cascade tax-resistant" property at the cell layer.
-/

namespace FX1Poly.Core

open FX1Poly.Foundation

/-! ## Section 1 — Renaming-composition law at the cell layer

`rename second (rename first cell) = rename (compose first second) cell`.

This is the cell-layer surfacing of `RawTerm.rename_compose`.
Five-arm structural recursion; `termBase` cites the term-layer
compose; the four composite/identity arms recurse on sub-cells with
the same composition. -/

/-- Cell-layer renaming-composition law.  Applying two renamings
sequentially to a cell equals applying their pointwise composition. -/
theorem RawCell.rename_compose
    {sourceScope middleScope targetScope : Nat}
    (firstRenaming : FX1Poly.Foundation.RawRenaming sourceScope middleScope)
    (secondRenaming : FX1Poly.Foundation.RawRenaming middleScope targetScope)
    (sourceCell : RawCell sourceScope) :
    RawCell.rename secondRenaming
        (RawCell.rename firstRenaming sourceCell) =
      RawCell.rename
        (FX1Poly.Foundation.RawRenaming.compose firstRenaming secondRenaming)
        sourceCell := by
  match sourceCell with
  | .termBase wrappedTerm =>
      show RawCell.termBase
            (RawTerm.rename secondRenaming
              (RawTerm.rename firstRenaming wrappedTerm)) =
          RawCell.termBase
            (RawTerm.rename
              (FX1Poly.Foundation.RawRenaming.compose firstRenaming secondRenaming)
              wrappedTerm)
      rw [RawTerm.rename_compose firstRenaming secondRenaming
            wrappedTerm]
  | .generatingCell ruleId sourceSubCell targetSubCell =>
      show RawCell.generatingCell ruleId
            (RawCell.rename secondRenaming
              (RawCell.rename firstRenaming sourceSubCell))
            (RawCell.rename secondRenaming
              (RawCell.rename firstRenaming targetSubCell)) =
          RawCell.generatingCell ruleId
            (RawCell.rename
              (FX1Poly.Foundation.RawRenaming.compose firstRenaming secondRenaming)
              sourceSubCell)
            (RawCell.rename
              (FX1Poly.Foundation.RawRenaming.compose firstRenaming secondRenaming)
              targetSubCell)
      rw [RawCell.rename_compose firstRenaming secondRenaming
            sourceSubCell,
          RawCell.rename_compose firstRenaming secondRenaming
            targetSubCell]
  | .verticalComposite firstSubCell secondSubCell =>
      show RawCell.verticalComposite
            (RawCell.rename secondRenaming
              (RawCell.rename firstRenaming firstSubCell))
            (RawCell.rename secondRenaming
              (RawCell.rename firstRenaming secondSubCell)) =
          RawCell.verticalComposite
            (RawCell.rename
              (FX1Poly.Foundation.RawRenaming.compose firstRenaming secondRenaming)
              firstSubCell)
            (RawCell.rename
              (FX1Poly.Foundation.RawRenaming.compose firstRenaming secondRenaming)
              secondSubCell)
      rw [RawCell.rename_compose firstRenaming secondRenaming
            firstSubCell,
          RawCell.rename_compose firstRenaming secondRenaming
            secondSubCell]
  | .horizontalComposite leftSubCell rightSubCell =>
      show RawCell.horizontalComposite
            (RawCell.rename secondRenaming
              (RawCell.rename firstRenaming leftSubCell))
            (RawCell.rename secondRenaming
              (RawCell.rename firstRenaming rightSubCell)) =
          RawCell.horizontalComposite
            (RawCell.rename
              (FX1Poly.Foundation.RawRenaming.compose firstRenaming secondRenaming)
              leftSubCell)
            (RawCell.rename
              (FX1Poly.Foundation.RawRenaming.compose firstRenaming secondRenaming)
              rightSubCell)
      rw [RawCell.rename_compose firstRenaming secondRenaming
            leftSubCell,
          RawCell.rename_compose firstRenaming secondRenaming
            rightSubCell]
  | .identityCell baseSubCell =>
      show RawCell.identityCell
            (RawCell.rename secondRenaming
              (RawCell.rename firstRenaming baseSubCell)) =
          RawCell.identityCell
            (RawCell.rename
              (FX1Poly.Foundation.RawRenaming.compose firstRenaming secondRenaming)
              baseSubCell)
      rw [RawCell.rename_compose firstRenaming secondRenaming
            baseSubCell]

/-! ## Section 2 — Substitution-composition law at the cell layer

`subst second (subst first cell) = subst (compose first second) cell`.

The polynomial-monad multiplication law lifted to cells.  Cites
`RawTerm.subst_compose` at the `termBase` arm. -/

/-- Cell-layer substitution-composition law.  Applying two
substitutions sequentially to a cell equals applying their pointwise
composition. -/
theorem RawCell.subst_compose
    {sourceScope middleScope targetScope : Nat}
    (firstSubstitution : RawTermSubst sourceScope middleScope)
    (secondSubstitution : RawTermSubst middleScope targetScope)
    (sourceCell : RawCell sourceScope) :
    RawCell.subst secondSubstitution
        (RawCell.subst firstSubstitution sourceCell) =
      RawCell.subst
        (RawTermSubst.compose firstSubstitution secondSubstitution)
        sourceCell := by
  match sourceCell with
  | .termBase wrappedTerm =>
      show RawCell.termBase
            (RawTerm.subst secondSubstitution
              (RawTerm.subst firstSubstitution wrappedTerm)) =
          RawCell.termBase
            (RawTerm.subst
              (RawTermSubst.compose firstSubstitution
                secondSubstitution)
              wrappedTerm)
      rw [RawTerm.subst_compose firstSubstitution secondSubstitution
            wrappedTerm]
  | .generatingCell ruleId sourceSubCell targetSubCell =>
      show RawCell.generatingCell ruleId
            (RawCell.subst secondSubstitution
              (RawCell.subst firstSubstitution sourceSubCell))
            (RawCell.subst secondSubstitution
              (RawCell.subst firstSubstitution targetSubCell)) =
          RawCell.generatingCell ruleId
            (RawCell.subst
              (RawTermSubst.compose firstSubstitution
                secondSubstitution)
              sourceSubCell)
            (RawCell.subst
              (RawTermSubst.compose firstSubstitution
                secondSubstitution)
              targetSubCell)
      rw [RawCell.subst_compose firstSubstitution secondSubstitution
            sourceSubCell,
          RawCell.subst_compose firstSubstitution secondSubstitution
            targetSubCell]
  | .verticalComposite firstSubCell secondSubCell =>
      show RawCell.verticalComposite
            (RawCell.subst secondSubstitution
              (RawCell.subst firstSubstitution firstSubCell))
            (RawCell.subst secondSubstitution
              (RawCell.subst firstSubstitution secondSubCell)) =
          RawCell.verticalComposite
            (RawCell.subst
              (RawTermSubst.compose firstSubstitution
                secondSubstitution)
              firstSubCell)
            (RawCell.subst
              (RawTermSubst.compose firstSubstitution
                secondSubstitution)
              secondSubCell)
      rw [RawCell.subst_compose firstSubstitution secondSubstitution
            firstSubCell,
          RawCell.subst_compose firstSubstitution secondSubstitution
            secondSubCell]
  | .horizontalComposite leftSubCell rightSubCell =>
      show RawCell.horizontalComposite
            (RawCell.subst secondSubstitution
              (RawCell.subst firstSubstitution leftSubCell))
            (RawCell.subst secondSubstitution
              (RawCell.subst firstSubstitution rightSubCell)) =
          RawCell.horizontalComposite
            (RawCell.subst
              (RawTermSubst.compose firstSubstitution
                secondSubstitution)
              leftSubCell)
            (RawCell.subst
              (RawTermSubst.compose firstSubstitution
                secondSubstitution)
              rightSubCell)
      rw [RawCell.subst_compose firstSubstitution secondSubstitution
            leftSubCell,
          RawCell.subst_compose firstSubstitution secondSubstitution
            rightSubCell]
  | .identityCell baseSubCell =>
      show RawCell.identityCell
            (RawCell.subst secondSubstitution
              (RawCell.subst firstSubstitution baseSubCell)) =
          RawCell.identityCell
            (RawCell.subst
              (RawTermSubst.compose firstSubstitution
                secondSubstitution)
              baseSubCell)
      rw [RawCell.subst_compose firstSubstitution secondSubstitution
            baseSubCell]

/-! ## Section 3 — Identity substitution at the cell layer

`subst identity cell = cell` — the polynomial-monad unit law.

Cites `RawTerm.subst_identity_apply` at the `termBase` arm. -/

/-- Cell-layer identity substitution.  Substituting by the identity
substitution returns the cell unchanged. -/
theorem RawCell.subst_identity_apply {scope : Nat}
    (sourceCell : RawCell scope) :
    RawCell.subst RawTermSubst.identity sourceCell = sourceCell := by
  match sourceCell with
  | .termBase wrappedTerm =>
      show RawCell.termBase
            (RawTerm.subst RawTermSubst.identity wrappedTerm) =
          RawCell.termBase wrappedTerm
      rw [RawTerm.subst_identity_apply wrappedTerm]
  | .generatingCell ruleId sourceSubCell targetSubCell =>
      show RawCell.generatingCell ruleId
            (RawCell.subst RawTermSubst.identity sourceSubCell)
            (RawCell.subst RawTermSubst.identity targetSubCell) =
          RawCell.generatingCell ruleId sourceSubCell targetSubCell
      rw [RawCell.subst_identity_apply sourceSubCell,
          RawCell.subst_identity_apply targetSubCell]
  | .verticalComposite firstSubCell secondSubCell =>
      show RawCell.verticalComposite
            (RawCell.subst RawTermSubst.identity firstSubCell)
            (RawCell.subst RawTermSubst.identity secondSubCell) =
          RawCell.verticalComposite firstSubCell secondSubCell
      rw [RawCell.subst_identity_apply firstSubCell,
          RawCell.subst_identity_apply secondSubCell]
  | .horizontalComposite leftSubCell rightSubCell =>
      show RawCell.horizontalComposite
            (RawCell.subst RawTermSubst.identity leftSubCell)
            (RawCell.subst RawTermSubst.identity rightSubCell) =
          RawCell.horizontalComposite leftSubCell rightSubCell
      rw [RawCell.subst_identity_apply leftSubCell,
          RawCell.subst_identity_apply rightSubCell]
  | .identityCell baseSubCell =>
      show RawCell.identityCell
            (RawCell.subst RawTermSubst.identity baseSubCell) =
          RawCell.identityCell baseSubCell
      rw [RawCell.subst_identity_apply baseSubCell]

/-! ## Section 4 — Rename-then-subst commute at the cell layer

`subst sigma (rename rho cell) = subst (rho.thenSubst sigma) cell`.

The first cross-direction commute lemma at the cell layer.  Cites
`RawTerm.rename_subst_commute` at the `termBase` arm. -/

/-- Cell-layer rename-then-subst commute.  Renaming a cell and then
substituting is equivalent to substituting by the pre-composed
substitution `rho.thenSubst sigma`. -/
theorem RawCell.rename_subst_commute
    {sourceScope middleScope targetScope : Nat}
    (rawRenaming : FX1Poly.Foundation.RawRenaming sourceScope middleScope)
    (someSubstitution : RawTermSubst middleScope targetScope)
    (sourceCell : RawCell sourceScope) :
    RawCell.subst someSubstitution
        (RawCell.rename rawRenaming sourceCell) =
      RawCell.subst
        (RawRenaming.thenSubst rawRenaming someSubstitution)
        sourceCell := by
  match sourceCell with
  | .termBase wrappedTerm =>
      show RawCell.termBase
            (RawTerm.subst someSubstitution
              (RawTerm.rename rawRenaming wrappedTerm)) =
          RawCell.termBase
            (RawTerm.subst
              (RawRenaming.thenSubst rawRenaming someSubstitution)
              wrappedTerm)
      rw [RawTerm.rename_subst_commute rawRenaming someSubstitution
            wrappedTerm]
  | .generatingCell ruleId sourceSubCell targetSubCell =>
      show RawCell.generatingCell ruleId
            (RawCell.subst someSubstitution
              (RawCell.rename rawRenaming sourceSubCell))
            (RawCell.subst someSubstitution
              (RawCell.rename rawRenaming targetSubCell)) =
          RawCell.generatingCell ruleId
            (RawCell.subst
              (RawRenaming.thenSubst rawRenaming someSubstitution)
              sourceSubCell)
            (RawCell.subst
              (RawRenaming.thenSubst rawRenaming someSubstitution)
              targetSubCell)
      rw [RawCell.rename_subst_commute rawRenaming someSubstitution
            sourceSubCell,
          RawCell.rename_subst_commute rawRenaming someSubstitution
            targetSubCell]
  | .verticalComposite firstSubCell secondSubCell =>
      show RawCell.verticalComposite
            (RawCell.subst someSubstitution
              (RawCell.rename rawRenaming firstSubCell))
            (RawCell.subst someSubstitution
              (RawCell.rename rawRenaming secondSubCell)) =
          RawCell.verticalComposite
            (RawCell.subst
              (RawRenaming.thenSubst rawRenaming someSubstitution)
              firstSubCell)
            (RawCell.subst
              (RawRenaming.thenSubst rawRenaming someSubstitution)
              secondSubCell)
      rw [RawCell.rename_subst_commute rawRenaming someSubstitution
            firstSubCell,
          RawCell.rename_subst_commute rawRenaming someSubstitution
            secondSubCell]
  | .horizontalComposite leftSubCell rightSubCell =>
      show RawCell.horizontalComposite
            (RawCell.subst someSubstitution
              (RawCell.rename rawRenaming leftSubCell))
            (RawCell.subst someSubstitution
              (RawCell.rename rawRenaming rightSubCell)) =
          RawCell.horizontalComposite
            (RawCell.subst
              (RawRenaming.thenSubst rawRenaming someSubstitution)
              leftSubCell)
            (RawCell.subst
              (RawRenaming.thenSubst rawRenaming someSubstitution)
              rightSubCell)
      rw [RawCell.rename_subst_commute rawRenaming someSubstitution
            leftSubCell,
          RawCell.rename_subst_commute rawRenaming someSubstitution
            rightSubCell]
  | .identityCell baseSubCell =>
      show RawCell.identityCell
            (RawCell.subst someSubstitution
              (RawCell.rename rawRenaming baseSubCell)) =
          RawCell.identityCell
            (RawCell.subst
              (RawRenaming.thenSubst rawRenaming someSubstitution)
              baseSubCell)
      rw [RawCell.rename_subst_commute rawRenaming someSubstitution
            baseSubCell]

/-! ## Section 5 — Subst-then-rename commute at the cell layer

`rename rho (subst sigma cell) = subst (sigma.postRename rho) cell`.

The second cross-direction commute lemma at the cell layer.  Cites
`RawTerm.subst_rename_commute` at the `termBase` arm. -/

/-- Cell-layer subst-then-rename commute.  Substituting into a cell
and then renaming is equivalent to substituting by the post-composed
substitution `sigma.postRename rho`. -/
theorem RawCell.subst_rename_commute
    {sourceScope middleScope targetScope : Nat}
    (someSubstitution : RawTermSubst sourceScope middleScope)
    (rawRenaming : FX1Poly.Foundation.RawRenaming middleScope targetScope)
    (sourceCell : RawCell sourceScope) :
    RawCell.rename rawRenaming
        (RawCell.subst someSubstitution sourceCell) =
      RawCell.subst
        (RawTermSubst.postRename someSubstitution rawRenaming)
        sourceCell := by
  match sourceCell with
  | .termBase wrappedTerm =>
      show RawCell.termBase
            (RawTerm.rename rawRenaming
              (RawTerm.subst someSubstitution wrappedTerm)) =
          RawCell.termBase
            (RawTerm.subst
              (RawTermSubst.postRename someSubstitution rawRenaming)
              wrappedTerm)
      rw [RawTerm.subst_rename_commute someSubstitution rawRenaming
            wrappedTerm]
  | .generatingCell ruleId sourceSubCell targetSubCell =>
      show RawCell.generatingCell ruleId
            (RawCell.rename rawRenaming
              (RawCell.subst someSubstitution sourceSubCell))
            (RawCell.rename rawRenaming
              (RawCell.subst someSubstitution targetSubCell)) =
          RawCell.generatingCell ruleId
            (RawCell.subst
              (RawTermSubst.postRename someSubstitution rawRenaming)
              sourceSubCell)
            (RawCell.subst
              (RawTermSubst.postRename someSubstitution rawRenaming)
              targetSubCell)
      rw [RawCell.subst_rename_commute someSubstitution rawRenaming
            sourceSubCell,
          RawCell.subst_rename_commute someSubstitution rawRenaming
            targetSubCell]
  | .verticalComposite firstSubCell secondSubCell =>
      show RawCell.verticalComposite
            (RawCell.rename rawRenaming
              (RawCell.subst someSubstitution firstSubCell))
            (RawCell.rename rawRenaming
              (RawCell.subst someSubstitution secondSubCell)) =
          RawCell.verticalComposite
            (RawCell.subst
              (RawTermSubst.postRename someSubstitution rawRenaming)
              firstSubCell)
            (RawCell.subst
              (RawTermSubst.postRename someSubstitution rawRenaming)
              secondSubCell)
      rw [RawCell.subst_rename_commute someSubstitution rawRenaming
            firstSubCell,
          RawCell.subst_rename_commute someSubstitution rawRenaming
            secondSubCell]
  | .horizontalComposite leftSubCell rightSubCell =>
      show RawCell.horizontalComposite
            (RawCell.rename rawRenaming
              (RawCell.subst someSubstitution leftSubCell))
            (RawCell.rename rawRenaming
              (RawCell.subst someSubstitution rightSubCell)) =
          RawCell.horizontalComposite
            (RawCell.subst
              (RawTermSubst.postRename someSubstitution rawRenaming)
              leftSubCell)
            (RawCell.subst
              (RawTermSubst.postRename someSubstitution rawRenaming)
              rightSubCell)
      rw [RawCell.subst_rename_commute someSubstitution rawRenaming
            leftSubCell,
          RawCell.subst_rename_commute someSubstitution rawRenaming
            rightSubCell]
  | .identityCell baseSubCell =>
      show RawCell.identityCell
            (RawCell.rename rawRenaming
              (RawCell.subst someSubstitution baseSubCell)) =
          RawCell.identityCell
            (RawCell.subst
              (RawTermSubst.postRename someSubstitution rawRenaming)
              baseSubCell)
      rw [RawCell.subst_rename_commute someSubstitution rawRenaming
            baseSubCell]

/-! ## Section 6 — Per-cascade specialization smokes

For each cascade lemma, a smoke verifying the `termBase` arm reduces
to its cited term-layer counterpart.  These witness that the
cell-layer cascade lemma genuinely delegates to the term-layer
Allais machinery (no hidden cell-layer computation). -/

/-- Smoke: cell-layer `rename_compose` at `termBase` reduces to the
term-layer `RawTerm.rename_compose` applied to the wrapped term. -/
theorem RawCell.rename_compose_termBase_smoke
    {sourceScope middleScope targetScope : Nat}
    (firstRenaming : FX1Poly.Foundation.RawRenaming sourceScope middleScope)
    (secondRenaming : FX1Poly.Foundation.RawRenaming middleScope targetScope)
    (wrappedTerm : RawTerm sourceScope) :
    RawCell.rename_compose firstRenaming secondRenaming
        (.termBase wrappedTerm)
    = congrArg RawCell.termBase
        (RawTerm.rename_compose firstRenaming secondRenaming
          wrappedTerm) := rfl

/-- Smoke: cell-layer `subst_compose` at `termBase` reduces to the
term-layer `RawTerm.subst_compose` applied to the wrapped term. -/
theorem RawCell.subst_compose_termBase_smoke
    {sourceScope middleScope targetScope : Nat}
    (firstSubstitution : RawTermSubst sourceScope middleScope)
    (secondSubstitution : RawTermSubst middleScope targetScope)
    (wrappedTerm : RawTerm sourceScope) :
    RawCell.subst_compose firstSubstitution secondSubstitution
        (.termBase wrappedTerm)
    = congrArg RawCell.termBase
        (RawTerm.subst_compose firstSubstitution secondSubstitution
          wrappedTerm) := rfl

/-- Smoke: cell-layer `subst_identity_apply` at `termBase` reduces to
the term-layer `RawTerm.subst_identity_apply` applied to the
wrapped term. -/
theorem RawCell.subst_identity_apply_termBase_smoke {scope : Nat}
    (wrappedTerm : RawTerm scope) :
    RawCell.subst_identity_apply (.termBase wrappedTerm)
    = congrArg RawCell.termBase
        (RawTerm.subst_identity_apply wrappedTerm) := rfl

end FX1Poly.Core
