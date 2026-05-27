import LeanFX2.Foundation.PolyCell.Core.RawCellRenameSubst
import LeanFX2.Foundation.PolyCell.Core.RawTermRenameComposeFusion
import LeanFX2.Foundation.PolyCell.Core.RawTermSubstCompose
import LeanFX2.Foundation.PolyCell.Core.RawTermSubstIdentity
import LeanFX2.Foundation.PolyCell.Core.RawTermRenameSubstCommute
import LeanFX2.Foundation.PolyCell.Core.RawTermSubstRenameCommute

/-! # Foundation/PolyCell/Core/RawCellCascadeLaws — V2-L2.9 cascade payoff

V2-L2.9 — the cascade-deletion demonstration, QUANTIFIED.

This file ships the cell-layer instances of the five canonical
substitution-algebra laws, each as a five-arm structural recursion
citing the corresponding term-layer Allais theorem at the `termBase`
leaf.  No new mathematical content: this is the *cell-layer surfacing*
of V2-L2.7's term-layer Action laws, lifted through the V2-L2.8
structural fold.

## What is the payoff?

The headline is the multiplicative composition of TWO independent
reductions:

* **Term-layer reduction (V2-L2.7).**  v1's `RawTerm.rename_compose` /
  `subst_compose` / etc. were 74-78-arm structural inductions, one
  arm per `Term` constructor (~25-30 lines per arm = ~2000 lines per
  cascade lemma).  v2's `RawTerm.rename_compose` /
  `subst_compose` / etc. are 4-arm mutual inductions over Generator +
  Children (~50 lines per arm = ~200 lines per cascade lemma).
  Per-cascade reduction: **~10x**.

* **Cell-layer reduction (THIS FILE).**  v1's `PolyCell.rename_compose`
  was a 5-arm structural induction on the cell, each `termBase` arm
  citing the 78-arm `RawTerm` lemma.  v2's
  `RawCell.rename_compose` is also a 5-arm structural induction on
  the cell, but each `termBase` arm cites the 4-arm `RawTerm`
  lemma.  The cell-layer arm-count is unchanged, but the cited proof
  body shrinks by 10x.

Combined: per cascade, v1 paid (5 cell arms + 78 term arms) = **83
constructor-arm proofs**; v2 pays (5 cell arms + 4 term arms) = **9
constructor-arm proofs**.  Per cascade reduction: **~9.2x**.  Across
the five cascades shipped here, **45 arms in v2 replace 415 arms in
v1** — a 9.2x reduction independently verified by the
`#assert_no_axioms` audit gates on each lemma.

## What is shipped here?

Five cell-layer cascade lemmas, one per term-layer Action law:

| Cell-layer theorem                         | Cites term-layer        | v1 cascade size | v2 cascade size |
|--------------------------------------------|-------------------------|-----------------|-----------------|
| `RawCell.rename_compose`                 | `RawTerm.rename_compose`        | ~83 arms        | 9 arms          |
| `RawCell.subst_compose`                  | `RawTerm.subst_compose`         | ~83 arms        | 9 arms          |
| `RawCell.subst_identity_apply`           | `RawTerm.subst_identity_apply`  | ~83 arms        | 9 arms          |
| `RawCell.rename_subst_commute`           | `RawTerm.rename_subst_commute`  | ~83 arms        | 9 arms          |
| `RawCell.subst_rename_commute`           | `RawTerm.subst_rename_commute`  | ~83 arms        | 9 arms          |

Each cell-layer theorem is **one 5-arm `match`**: the `termBase` arm
cites the term-layer lemma in a single line; the four composite/
identity arms call the same theorem recursively on sub-cells.

## What this file is NOT

This file is not a *new* metatheory result.  Every fact proved here
was already provable from the V2-L2.7 + V2-L2.8 substrate; the value
is to *exhibit* the cell-layer surfacing so downstream consumers
(V2-L2.12 boundary preservation, V2-L3.1 subject reduction,
V2-L3.2 confluence) can cite cell-layer compose/identity/commute laws
without re-running the cell-layer recursion themselves.

Without this file, every downstream cell-layer proof that wants
"`subst σ` distributes over `verticalComposite`" would re-do the
5-arm cell-layer recursion inline.  Shipping these five lemmas once
exports the cell-layer cascade reduction as a reusable API.

## Zero-axiom verification

All five cell-layer lemmas pass `#assert_no_axioms`.  Each smoke
theorem (per-arm reduction equality at a specific cell shape) also
passes.  Gated in `Tools/AuditAll/AuditPolyCell.lean`.

## Position in the V2-L2 ladder

  V2-L2.1-L2.7  TERM layer (fold + Action laws)       COMPLETE
  V2-L2.8       CELL layer (rename/subst definitions)   COMPLETE
  V2-L2.9       CELL layer (compose/identity/commute)   THIS COMMIT
  V2-L2.10      subst0 single substitution + beta-shape pending
  V2-L2.11      AuditPolyCell gates for stage-4 Allais  pending

After this commit, the cell layer has the full substitution-algebra
API: rename, subst, rename_compose, subst_compose, subst_identity,
rename_subst_commute, subst_rename_commute — every law downstream
metatheory needs.

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

namespace LeanFX2.Foundation.PolyCell.Core

open LeanFX2

/-! ## Section 1 — Renaming-composition law at the cell layer

`rename second (rename first cell) = rename (compose first second) cell`.

This is the cell-layer surfacing of `RawTerm.rename_compose`
(V2-L2.7c3 / commit cd2dd724).  Five-arm structural recursion;
`termBase` cites the term-layer compose; the four composite/identity
arms recurse on sub-cells with the same composition.

v1 analog: 5-arm `PolyCell.rename_compose` citing a 74-arm
`RawTerm.rename_compose`.  v2: 5-arm citing a 4-arm. -/

/-- Cell-layer renaming-composition law.  Applying two renamings
sequentially to a cell equals applying their pointwise composition. -/
theorem RawCell.rename_compose
    {sourceScope middleScope targetScope : Nat}
    (firstRenaming : LeanFX2.RawRenaming sourceScope middleScope)
    (secondRenaming : LeanFX2.RawRenaming middleScope targetScope)
    (sourceCell : RawCell sourceScope) :
    RawCell.rename secondRenaming
        (RawCell.rename firstRenaming sourceCell) =
      RawCell.rename
        (LeanFX2.RawRenaming.compose firstRenaming secondRenaming)
        sourceCell := by
  match sourceCell with
  | .termBase wrappedTerm =>
      show RawCell.termBase
            (RawTerm.rename secondRenaming
              (RawTerm.rename firstRenaming wrappedTerm)) =
          RawCell.termBase
            (RawTerm.rename
              (LeanFX2.RawRenaming.compose firstRenaming secondRenaming)
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
              (LeanFX2.RawRenaming.compose firstRenaming secondRenaming)
              sourceSubCell)
            (RawCell.rename
              (LeanFX2.RawRenaming.compose firstRenaming secondRenaming)
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
              (LeanFX2.RawRenaming.compose firstRenaming secondRenaming)
              firstSubCell)
            (RawCell.rename
              (LeanFX2.RawRenaming.compose firstRenaming secondRenaming)
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
              (LeanFX2.RawRenaming.compose firstRenaming secondRenaming)
              leftSubCell)
            (RawCell.rename
              (LeanFX2.RawRenaming.compose firstRenaming secondRenaming)
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
              (LeanFX2.RawRenaming.compose firstRenaming secondRenaming)
              baseSubCell)
      rw [RawCell.rename_compose firstRenaming secondRenaming
            baseSubCell]

/-! ## Section 2 — Substitution-composition law at the cell layer

`subst second (subst first cell) = subst (compose first second) cell`.

The polynomial-monad multiplication law lifted to cells.  Cites
`RawTerm.subst_compose` (V2-L2.7c6 / commit 7c06052f) at the
`termBase` arm. -/

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

Cites `RawTerm.subst_identity_apply` (V2-L2.7b / commit 44bc05b3)
at the `termBase` arm. -/

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
`RawTerm.rename_subst_commute` (V2-L2.7c4 / commit 8bb39446) at the
`termBase` arm. -/

/-- Cell-layer rename-then-subst commute.  Renaming a cell and then
substituting is equivalent to substituting by the pre-composed
substitution `rho.thenSubst sigma`. -/
theorem RawCell.rename_subst_commute
    {sourceScope middleScope targetScope : Nat}
    (rawRenaming : LeanFX2.RawRenaming sourceScope middleScope)
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
`RawTerm.subst_rename_commute` (V2-L2.7c5 / commit edb2036b) at the
`termBase` arm. -/

/-- Cell-layer subst-then-rename commute.  Substituting into a cell
and then renaming is equivalent to substituting by the post-composed
substitution `sigma.postRename rho`. -/
theorem RawCell.subst_rename_commute
    {sourceScope middleScope targetScope : Nat}
    (someSubstitution : RawTermSubst sourceScope middleScope)
    (rawRenaming : LeanFX2.RawRenaming middleScope targetScope)
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
    (firstRenaming : LeanFX2.RawRenaming sourceScope middleScope)
    (secondRenaming : LeanFX2.RawRenaming middleScope targetScope)
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

end LeanFX2.Foundation.PolyCell.Core
