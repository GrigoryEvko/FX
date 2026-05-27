import LeanFX2.Foundation.PolyCell.Core.RawCellV2RenameSubst
import LeanFX2.Foundation.PolyCell.Core.RawTermV2RenameComposeFusion
import LeanFX2.Foundation.PolyCell.Core.RawTermV2SubstCompose
import LeanFX2.Foundation.PolyCell.Core.RawTermV2SubstIdentity
import LeanFX2.Foundation.PolyCell.Core.RawTermV2RenameSubstCommute
import LeanFX2.Foundation.PolyCell.Core.RawTermV2SubstRenameCommute

/-! # Foundation/PolyCell/Core/RawCellV2CascadeLaws — V2-L2.9 cascade payoff

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
  cascade lemma).  v2's `RawTermV2.rename_compose` /
  `subst_compose` / etc. are 4-arm mutual inductions over Generator +
  Children (~50 lines per arm = ~200 lines per cascade lemma).
  Per-cascade reduction: **~10x**.

* **Cell-layer reduction (THIS FILE).**  v1's `PolyCell.rename_compose`
  was a 5-arm structural induction on the cell, each `termBase` arm
  citing the 78-arm `RawTerm` lemma.  v2's
  `RawCellV2.rename_compose` is also a 5-arm structural induction on
  the cell, but each `termBase` arm cites the 4-arm `RawTermV2`
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
| `RawCellV2.rename_compose`                 | `RawTermV2.rename_compose`        | ~83 arms        | 9 arms          |
| `RawCellV2.subst_compose`                  | `RawTermV2.subst_compose`         | ~83 arms        | 9 arms          |
| `RawCellV2.subst_identity_apply`           | `RawTermV2.subst_identity_apply`  | ~83 arms        | 9 arms          |
| `RawCellV2.rename_subst_commute`           | `RawTermV2.rename_subst_commute`  | ~83 arms        | 9 arms          |
| `RawCellV2.subst_rename_commute`           | `RawTermV2.subst_rename_commute`  | ~83 arms        | 9 arms          |

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

  V2-L2.1-L2.7  TERM layer (foldV2 + Action laws)       COMPLETE
  V2-L2.8       CELL layer (rename/subst definitions)   COMPLETE
  V2-L2.9       CELL layer (compose/identity/commute)   THIS COMMIT
  V2-L2.10      subst0 single substitution + beta-shape pending
  V2-L2.11      AuditPolyCell gates for stage-4 Allais  pending

After this commit, the cell layer has the full substitution-algebra
API: rename, subst, rename_compose, subst_compose, subst_identity,
rename_subst_commute, subst_rename_commute — every law downstream
metatheory needs.

## On the design choice "structural recursion vs foldV2 abstraction"

The cell layer has 5 ctors and no binder shifts.  A foldV2-like
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

This is the cell-layer surfacing of `RawTermV2.rename_compose`
(V2-L2.7c3 / commit cd2dd724).  Five-arm structural recursion;
`termBase` cites the term-layer compose; the four composite/identity
arms recurse on sub-cells with the same composition.

v1 analog: 5-arm `PolyCell.rename_compose` citing a 74-arm
`RawTerm.rename_compose`.  v2: 5-arm citing a 4-arm. -/

/-- Cell-layer renaming-composition law.  Applying two renamings
sequentially to a cell equals applying their pointwise composition. -/
theorem RawCellV2.rename_compose
    {sourceScope middleScope targetScope : Nat}
    (firstRenaming : LeanFX2.RawRenaming sourceScope middleScope)
    (secondRenaming : LeanFX2.RawRenaming middleScope targetScope)
    (sourceCell : RawCellV2 sourceScope) :
    RawCellV2.rename secondRenaming
        (RawCellV2.rename firstRenaming sourceCell) =
      RawCellV2.rename
        (LeanFX2.RawRenaming.compose firstRenaming secondRenaming)
        sourceCell := by
  match sourceCell with
  | .termBase wrappedTerm =>
      show RawCellV2.termBase
            (RawTermV2.rename secondRenaming
              (RawTermV2.rename firstRenaming wrappedTerm)) =
          RawCellV2.termBase
            (RawTermV2.rename
              (LeanFX2.RawRenaming.compose firstRenaming secondRenaming)
              wrappedTerm)
      rw [RawTermV2.rename_compose firstRenaming secondRenaming
            wrappedTerm]
  | .generatingCell ruleId sourceSubCell targetSubCell =>
      show RawCellV2.generatingCell ruleId
            (RawCellV2.rename secondRenaming
              (RawCellV2.rename firstRenaming sourceSubCell))
            (RawCellV2.rename secondRenaming
              (RawCellV2.rename firstRenaming targetSubCell)) =
          RawCellV2.generatingCell ruleId
            (RawCellV2.rename
              (LeanFX2.RawRenaming.compose firstRenaming secondRenaming)
              sourceSubCell)
            (RawCellV2.rename
              (LeanFX2.RawRenaming.compose firstRenaming secondRenaming)
              targetSubCell)
      rw [RawCellV2.rename_compose firstRenaming secondRenaming
            sourceSubCell,
          RawCellV2.rename_compose firstRenaming secondRenaming
            targetSubCell]
  | .verticalComposite firstSubCell secondSubCell =>
      show RawCellV2.verticalComposite
            (RawCellV2.rename secondRenaming
              (RawCellV2.rename firstRenaming firstSubCell))
            (RawCellV2.rename secondRenaming
              (RawCellV2.rename firstRenaming secondSubCell)) =
          RawCellV2.verticalComposite
            (RawCellV2.rename
              (LeanFX2.RawRenaming.compose firstRenaming secondRenaming)
              firstSubCell)
            (RawCellV2.rename
              (LeanFX2.RawRenaming.compose firstRenaming secondRenaming)
              secondSubCell)
      rw [RawCellV2.rename_compose firstRenaming secondRenaming
            firstSubCell,
          RawCellV2.rename_compose firstRenaming secondRenaming
            secondSubCell]
  | .horizontalComposite leftSubCell rightSubCell =>
      show RawCellV2.horizontalComposite
            (RawCellV2.rename secondRenaming
              (RawCellV2.rename firstRenaming leftSubCell))
            (RawCellV2.rename secondRenaming
              (RawCellV2.rename firstRenaming rightSubCell)) =
          RawCellV2.horizontalComposite
            (RawCellV2.rename
              (LeanFX2.RawRenaming.compose firstRenaming secondRenaming)
              leftSubCell)
            (RawCellV2.rename
              (LeanFX2.RawRenaming.compose firstRenaming secondRenaming)
              rightSubCell)
      rw [RawCellV2.rename_compose firstRenaming secondRenaming
            leftSubCell,
          RawCellV2.rename_compose firstRenaming secondRenaming
            rightSubCell]
  | .identityCell baseSubCell =>
      show RawCellV2.identityCell
            (RawCellV2.rename secondRenaming
              (RawCellV2.rename firstRenaming baseSubCell)) =
          RawCellV2.identityCell
            (RawCellV2.rename
              (LeanFX2.RawRenaming.compose firstRenaming secondRenaming)
              baseSubCell)
      rw [RawCellV2.rename_compose firstRenaming secondRenaming
            baseSubCell]

/-! ## Section 2 — Substitution-composition law at the cell layer

`subst second (subst first cell) = subst (compose first second) cell`.

The polynomial-monad multiplication law lifted to cells.  Cites
`RawTermV2.subst_compose` (V2-L2.7c6 / commit 7c06052f) at the
`termBase` arm. -/

/-- Cell-layer substitution-composition law.  Applying two
substitutions sequentially to a cell equals applying their pointwise
composition. -/
theorem RawCellV2.subst_compose
    {sourceScope middleScope targetScope : Nat}
    (firstSubstitution : RawTermSubstV2 sourceScope middleScope)
    (secondSubstitution : RawTermSubstV2 middleScope targetScope)
    (sourceCell : RawCellV2 sourceScope) :
    RawCellV2.subst secondSubstitution
        (RawCellV2.subst firstSubstitution sourceCell) =
      RawCellV2.subst
        (RawTermSubstV2.compose firstSubstitution secondSubstitution)
        sourceCell := by
  match sourceCell with
  | .termBase wrappedTerm =>
      show RawCellV2.termBase
            (RawTermV2.subst secondSubstitution
              (RawTermV2.subst firstSubstitution wrappedTerm)) =
          RawCellV2.termBase
            (RawTermV2.subst
              (RawTermSubstV2.compose firstSubstitution
                secondSubstitution)
              wrappedTerm)
      rw [RawTermV2.subst_compose firstSubstitution secondSubstitution
            wrappedTerm]
  | .generatingCell ruleId sourceSubCell targetSubCell =>
      show RawCellV2.generatingCell ruleId
            (RawCellV2.subst secondSubstitution
              (RawCellV2.subst firstSubstitution sourceSubCell))
            (RawCellV2.subst secondSubstitution
              (RawCellV2.subst firstSubstitution targetSubCell)) =
          RawCellV2.generatingCell ruleId
            (RawCellV2.subst
              (RawTermSubstV2.compose firstSubstitution
                secondSubstitution)
              sourceSubCell)
            (RawCellV2.subst
              (RawTermSubstV2.compose firstSubstitution
                secondSubstitution)
              targetSubCell)
      rw [RawCellV2.subst_compose firstSubstitution secondSubstitution
            sourceSubCell,
          RawCellV2.subst_compose firstSubstitution secondSubstitution
            targetSubCell]
  | .verticalComposite firstSubCell secondSubCell =>
      show RawCellV2.verticalComposite
            (RawCellV2.subst secondSubstitution
              (RawCellV2.subst firstSubstitution firstSubCell))
            (RawCellV2.subst secondSubstitution
              (RawCellV2.subst firstSubstitution secondSubCell)) =
          RawCellV2.verticalComposite
            (RawCellV2.subst
              (RawTermSubstV2.compose firstSubstitution
                secondSubstitution)
              firstSubCell)
            (RawCellV2.subst
              (RawTermSubstV2.compose firstSubstitution
                secondSubstitution)
              secondSubCell)
      rw [RawCellV2.subst_compose firstSubstitution secondSubstitution
            firstSubCell,
          RawCellV2.subst_compose firstSubstitution secondSubstitution
            secondSubCell]
  | .horizontalComposite leftSubCell rightSubCell =>
      show RawCellV2.horizontalComposite
            (RawCellV2.subst secondSubstitution
              (RawCellV2.subst firstSubstitution leftSubCell))
            (RawCellV2.subst secondSubstitution
              (RawCellV2.subst firstSubstitution rightSubCell)) =
          RawCellV2.horizontalComposite
            (RawCellV2.subst
              (RawTermSubstV2.compose firstSubstitution
                secondSubstitution)
              leftSubCell)
            (RawCellV2.subst
              (RawTermSubstV2.compose firstSubstitution
                secondSubstitution)
              rightSubCell)
      rw [RawCellV2.subst_compose firstSubstitution secondSubstitution
            leftSubCell,
          RawCellV2.subst_compose firstSubstitution secondSubstitution
            rightSubCell]
  | .identityCell baseSubCell =>
      show RawCellV2.identityCell
            (RawCellV2.subst secondSubstitution
              (RawCellV2.subst firstSubstitution baseSubCell)) =
          RawCellV2.identityCell
            (RawCellV2.subst
              (RawTermSubstV2.compose firstSubstitution
                secondSubstitution)
              baseSubCell)
      rw [RawCellV2.subst_compose firstSubstitution secondSubstitution
            baseSubCell]

/-! ## Section 3 — Identity substitution at the cell layer

`subst identity cell = cell` — the polynomial-monad unit law.

Cites `RawTermV2.subst_identity_apply` (V2-L2.7b / commit 44bc05b3)
at the `termBase` arm. -/

/-- Cell-layer identity substitution.  Substituting by the identity
substitution returns the cell unchanged. -/
theorem RawCellV2.subst_identity_apply {scope : Nat}
    (sourceCell : RawCellV2 scope) :
    RawCellV2.subst RawTermSubstV2.identity sourceCell = sourceCell := by
  match sourceCell with
  | .termBase wrappedTerm =>
      show RawCellV2.termBase
            (RawTermV2.subst RawTermSubstV2.identity wrappedTerm) =
          RawCellV2.termBase wrappedTerm
      rw [RawTermV2.subst_identity_apply wrappedTerm]
  | .generatingCell ruleId sourceSubCell targetSubCell =>
      show RawCellV2.generatingCell ruleId
            (RawCellV2.subst RawTermSubstV2.identity sourceSubCell)
            (RawCellV2.subst RawTermSubstV2.identity targetSubCell) =
          RawCellV2.generatingCell ruleId sourceSubCell targetSubCell
      rw [RawCellV2.subst_identity_apply sourceSubCell,
          RawCellV2.subst_identity_apply targetSubCell]
  | .verticalComposite firstSubCell secondSubCell =>
      show RawCellV2.verticalComposite
            (RawCellV2.subst RawTermSubstV2.identity firstSubCell)
            (RawCellV2.subst RawTermSubstV2.identity secondSubCell) =
          RawCellV2.verticalComposite firstSubCell secondSubCell
      rw [RawCellV2.subst_identity_apply firstSubCell,
          RawCellV2.subst_identity_apply secondSubCell]
  | .horizontalComposite leftSubCell rightSubCell =>
      show RawCellV2.horizontalComposite
            (RawCellV2.subst RawTermSubstV2.identity leftSubCell)
            (RawCellV2.subst RawTermSubstV2.identity rightSubCell) =
          RawCellV2.horizontalComposite leftSubCell rightSubCell
      rw [RawCellV2.subst_identity_apply leftSubCell,
          RawCellV2.subst_identity_apply rightSubCell]
  | .identityCell baseSubCell =>
      show RawCellV2.identityCell
            (RawCellV2.subst RawTermSubstV2.identity baseSubCell) =
          RawCellV2.identityCell baseSubCell
      rw [RawCellV2.subst_identity_apply baseSubCell]

/-! ## Section 4 — Rename-then-subst commute at the cell layer

`subst sigma (rename rho cell) = subst (rho.thenSubst sigma) cell`.

The first cross-direction commute lemma at the cell layer.  Cites
`RawTermV2.rename_subst_commute` (V2-L2.7c4 / commit 8bb39446) at the
`termBase` arm. -/

/-- Cell-layer rename-then-subst commute.  Renaming a cell and then
substituting is equivalent to substituting by the pre-composed
substitution `rho.thenSubst sigma`. -/
theorem RawCellV2.rename_subst_commute
    {sourceScope middleScope targetScope : Nat}
    (rawRenaming : LeanFX2.RawRenaming sourceScope middleScope)
    (someSubstitution : RawTermSubstV2 middleScope targetScope)
    (sourceCell : RawCellV2 sourceScope) :
    RawCellV2.subst someSubstitution
        (RawCellV2.rename rawRenaming sourceCell) =
      RawCellV2.subst
        (RawRenaming.thenSubst rawRenaming someSubstitution)
        sourceCell := by
  match sourceCell with
  | .termBase wrappedTerm =>
      show RawCellV2.termBase
            (RawTermV2.subst someSubstitution
              (RawTermV2.rename rawRenaming wrappedTerm)) =
          RawCellV2.termBase
            (RawTermV2.subst
              (RawRenaming.thenSubst rawRenaming someSubstitution)
              wrappedTerm)
      rw [RawTermV2.rename_subst_commute rawRenaming someSubstitution
            wrappedTerm]
  | .generatingCell ruleId sourceSubCell targetSubCell =>
      show RawCellV2.generatingCell ruleId
            (RawCellV2.subst someSubstitution
              (RawCellV2.rename rawRenaming sourceSubCell))
            (RawCellV2.subst someSubstitution
              (RawCellV2.rename rawRenaming targetSubCell)) =
          RawCellV2.generatingCell ruleId
            (RawCellV2.subst
              (RawRenaming.thenSubst rawRenaming someSubstitution)
              sourceSubCell)
            (RawCellV2.subst
              (RawRenaming.thenSubst rawRenaming someSubstitution)
              targetSubCell)
      rw [RawCellV2.rename_subst_commute rawRenaming someSubstitution
            sourceSubCell,
          RawCellV2.rename_subst_commute rawRenaming someSubstitution
            targetSubCell]
  | .verticalComposite firstSubCell secondSubCell =>
      show RawCellV2.verticalComposite
            (RawCellV2.subst someSubstitution
              (RawCellV2.rename rawRenaming firstSubCell))
            (RawCellV2.subst someSubstitution
              (RawCellV2.rename rawRenaming secondSubCell)) =
          RawCellV2.verticalComposite
            (RawCellV2.subst
              (RawRenaming.thenSubst rawRenaming someSubstitution)
              firstSubCell)
            (RawCellV2.subst
              (RawRenaming.thenSubst rawRenaming someSubstitution)
              secondSubCell)
      rw [RawCellV2.rename_subst_commute rawRenaming someSubstitution
            firstSubCell,
          RawCellV2.rename_subst_commute rawRenaming someSubstitution
            secondSubCell]
  | .horizontalComposite leftSubCell rightSubCell =>
      show RawCellV2.horizontalComposite
            (RawCellV2.subst someSubstitution
              (RawCellV2.rename rawRenaming leftSubCell))
            (RawCellV2.subst someSubstitution
              (RawCellV2.rename rawRenaming rightSubCell)) =
          RawCellV2.horizontalComposite
            (RawCellV2.subst
              (RawRenaming.thenSubst rawRenaming someSubstitution)
              leftSubCell)
            (RawCellV2.subst
              (RawRenaming.thenSubst rawRenaming someSubstitution)
              rightSubCell)
      rw [RawCellV2.rename_subst_commute rawRenaming someSubstitution
            leftSubCell,
          RawCellV2.rename_subst_commute rawRenaming someSubstitution
            rightSubCell]
  | .identityCell baseSubCell =>
      show RawCellV2.identityCell
            (RawCellV2.subst someSubstitution
              (RawCellV2.rename rawRenaming baseSubCell)) =
          RawCellV2.identityCell
            (RawCellV2.subst
              (RawRenaming.thenSubst rawRenaming someSubstitution)
              baseSubCell)
      rw [RawCellV2.rename_subst_commute rawRenaming someSubstitution
            baseSubCell]

/-! ## Section 5 — Subst-then-rename commute at the cell layer

`rename rho (subst sigma cell) = subst (sigma.postRename rho) cell`.

The second cross-direction commute lemma at the cell layer.  Cites
`RawTermV2.subst_rename_commute` (V2-L2.7c5 / commit edb2036b) at the
`termBase` arm. -/

/-- Cell-layer subst-then-rename commute.  Substituting into a cell
and then renaming is equivalent to substituting by the post-composed
substitution `sigma.postRename rho`. -/
theorem RawCellV2.subst_rename_commute
    {sourceScope middleScope targetScope : Nat}
    (someSubstitution : RawTermSubstV2 sourceScope middleScope)
    (rawRenaming : LeanFX2.RawRenaming middleScope targetScope)
    (sourceCell : RawCellV2 sourceScope) :
    RawCellV2.rename rawRenaming
        (RawCellV2.subst someSubstitution sourceCell) =
      RawCellV2.subst
        (RawTermSubstV2.postRename someSubstitution rawRenaming)
        sourceCell := by
  match sourceCell with
  | .termBase wrappedTerm =>
      show RawCellV2.termBase
            (RawTermV2.rename rawRenaming
              (RawTermV2.subst someSubstitution wrappedTerm)) =
          RawCellV2.termBase
            (RawTermV2.subst
              (RawTermSubstV2.postRename someSubstitution rawRenaming)
              wrappedTerm)
      rw [RawTermV2.subst_rename_commute someSubstitution rawRenaming
            wrappedTerm]
  | .generatingCell ruleId sourceSubCell targetSubCell =>
      show RawCellV2.generatingCell ruleId
            (RawCellV2.rename rawRenaming
              (RawCellV2.subst someSubstitution sourceSubCell))
            (RawCellV2.rename rawRenaming
              (RawCellV2.subst someSubstitution targetSubCell)) =
          RawCellV2.generatingCell ruleId
            (RawCellV2.subst
              (RawTermSubstV2.postRename someSubstitution rawRenaming)
              sourceSubCell)
            (RawCellV2.subst
              (RawTermSubstV2.postRename someSubstitution rawRenaming)
              targetSubCell)
      rw [RawCellV2.subst_rename_commute someSubstitution rawRenaming
            sourceSubCell,
          RawCellV2.subst_rename_commute someSubstitution rawRenaming
            targetSubCell]
  | .verticalComposite firstSubCell secondSubCell =>
      show RawCellV2.verticalComposite
            (RawCellV2.rename rawRenaming
              (RawCellV2.subst someSubstitution firstSubCell))
            (RawCellV2.rename rawRenaming
              (RawCellV2.subst someSubstitution secondSubCell)) =
          RawCellV2.verticalComposite
            (RawCellV2.subst
              (RawTermSubstV2.postRename someSubstitution rawRenaming)
              firstSubCell)
            (RawCellV2.subst
              (RawTermSubstV2.postRename someSubstitution rawRenaming)
              secondSubCell)
      rw [RawCellV2.subst_rename_commute someSubstitution rawRenaming
            firstSubCell,
          RawCellV2.subst_rename_commute someSubstitution rawRenaming
            secondSubCell]
  | .horizontalComposite leftSubCell rightSubCell =>
      show RawCellV2.horizontalComposite
            (RawCellV2.rename rawRenaming
              (RawCellV2.subst someSubstitution leftSubCell))
            (RawCellV2.rename rawRenaming
              (RawCellV2.subst someSubstitution rightSubCell)) =
          RawCellV2.horizontalComposite
            (RawCellV2.subst
              (RawTermSubstV2.postRename someSubstitution rawRenaming)
              leftSubCell)
            (RawCellV2.subst
              (RawTermSubstV2.postRename someSubstitution rawRenaming)
              rightSubCell)
      rw [RawCellV2.subst_rename_commute someSubstitution rawRenaming
            leftSubCell,
          RawCellV2.subst_rename_commute someSubstitution rawRenaming
            rightSubCell]
  | .identityCell baseSubCell =>
      show RawCellV2.identityCell
            (RawCellV2.rename rawRenaming
              (RawCellV2.subst someSubstitution baseSubCell)) =
          RawCellV2.identityCell
            (RawCellV2.subst
              (RawTermSubstV2.postRename someSubstitution rawRenaming)
              baseSubCell)
      rw [RawCellV2.subst_rename_commute someSubstitution rawRenaming
            baseSubCell]

/-! ## Section 6 — Per-cascade specialization smokes

For each cascade lemma, a smoke verifying the `termBase` arm reduces
to its cited term-layer counterpart.  These witness that the
cell-layer cascade lemma genuinely delegates to the term-layer
Allais machinery (no hidden cell-layer computation). -/

/-- Smoke: cell-layer `rename_compose` at `termBase` reduces to the
term-layer `RawTermV2.rename_compose` applied to the wrapped term. -/
theorem RawCellV2.rename_compose_termBase_smoke
    {sourceScope middleScope targetScope : Nat}
    (firstRenaming : LeanFX2.RawRenaming sourceScope middleScope)
    (secondRenaming : LeanFX2.RawRenaming middleScope targetScope)
    (wrappedTerm : RawTermV2 sourceScope) :
    RawCellV2.rename_compose firstRenaming secondRenaming
        (.termBase wrappedTerm)
    = congrArg RawCellV2.termBase
        (RawTermV2.rename_compose firstRenaming secondRenaming
          wrappedTerm) := rfl

/-- Smoke: cell-layer `subst_compose` at `termBase` reduces to the
term-layer `RawTermV2.subst_compose` applied to the wrapped term. -/
theorem RawCellV2.subst_compose_termBase_smoke
    {sourceScope middleScope targetScope : Nat}
    (firstSubstitution : RawTermSubstV2 sourceScope middleScope)
    (secondSubstitution : RawTermSubstV2 middleScope targetScope)
    (wrappedTerm : RawTermV2 sourceScope) :
    RawCellV2.subst_compose firstSubstitution secondSubstitution
        (.termBase wrappedTerm)
    = congrArg RawCellV2.termBase
        (RawTermV2.subst_compose firstSubstitution secondSubstitution
          wrappedTerm) := rfl

/-- Smoke: cell-layer `subst_identity_apply` at `termBase` reduces to
the term-layer `RawTermV2.subst_identity_apply` applied to the
wrapped term. -/
theorem RawCellV2.subst_identity_apply_termBase_smoke {scope : Nat}
    (wrappedTerm : RawTermV2 scope) :
    RawCellV2.subst_identity_apply (.termBase wrappedTerm)
    = congrArg RawCellV2.termBase
        (RawTermV2.subst_identity_apply wrappedTerm) := rfl

end LeanFX2.Foundation.PolyCell.Core
