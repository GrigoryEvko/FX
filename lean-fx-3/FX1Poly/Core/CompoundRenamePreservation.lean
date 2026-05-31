import FX1Poly.Core.HasCertifiedComposition
import FX1Poly.Core.SubstPreservationProbes

/-! # Foundation/PolyCell/Core/CompoundRenamePreservation — compound rename preservation

Ships **compositional preservation lemmas** for compound
generators under rename.

## What this ships

For each compound term-shape generator, two theorems:

1. **`rename_X_reduces`** — `RawTerm.rename ρ (mkGen X () children)`
   distributes over children by `rfl`.  Empirically verified: the
   fold engine's distributivity is definitional, including the
   binder case for `gen_lam` (where the body's renaming uses
   `RawRenaming.lift ρ`).

2. **`HasCertifiedCellDim0.X_preservedByRename`** — given the
   RENAMED CHILDREN'S CELLS as inputs, produces the renamed
   parent term's certification.  Closes by
   `rw [rename_X_reduces]; exact .X-intro renamedChildren`.

## Compositional, not full induction

These are the **inductive step** of the structural induction.
The CALLER (`HasCertifiedCellDim0.preservedByRename`, a structural
induction over the cell) provides the renamed-children cells
recursively.  This file gives the BUILDING BLOCKS that thread the
inductive hypothesis.

## Coverage

Same compound generators as `HasCertifiedComposition.lean`:

  * Binary, no binders: `app`, `pair`, `listCons`
  * Unary, no binders: `natSucc`, `optionSome`, `eitherInl`,
    `eitherInr`, `refl`
  * Unary, 1 binder: `lam` (body uses lifted renaming)

## Zero-axiom verification

Each reduction probe closes by `rfl` — definitional unfolding
of the fold engine on the concrete generator.  Each
preservation theorem closes by `rw + exact .intro`.  No
tactics that touch propext / Quot.sound / Classical.choice.

Audit-gated.
-/

namespace FX1Poly.Core

open FX1Poly.Foundation

/-! ## Section 1 — Rename distributivity probes (compound, by rfl) -/

/-- **Probe: rename distributes over `gen_app`.** -/
theorem RawTerm.rename_app_reduces
    {sourceScope targetScope : Nat}
    (rawRenaming : RawRenaming sourceScope targetScope)
    (functionTerm argumentTerm : RawTerm sourceScope) :
    RawTerm.rename rawRenaming
        (.mkGen .gen_app ()
          (.childCons functionTerm
            (.childCons argumentTerm .childNil))) =
      (.mkGen .gen_app ()
        (.childCons (RawTerm.rename rawRenaming functionTerm)
          (.childCons (RawTerm.rename rawRenaming argumentTerm)
            .childNil))
        : RawTerm targetScope) := rfl

/-- **Probe: rename distributes over `gen_pair`.** -/
theorem RawTerm.rename_pair_reduces
    {sourceScope targetScope : Nat}
    (rawRenaming : RawRenaming sourceScope targetScope)
    (firstTerm secondTerm : RawTerm sourceScope) :
    RawTerm.rename rawRenaming
        (.mkGen .gen_pair ()
          (.childCons firstTerm
            (.childCons secondTerm .childNil))) =
      (.mkGen .gen_pair ()
        (.childCons (RawTerm.rename rawRenaming firstTerm)
          (.childCons (RawTerm.rename rawRenaming secondTerm)
            .childNil))
        : RawTerm targetScope) := rfl

/-- **Probe: rename distributes over `gen_listCons`.** -/
theorem RawTerm.rename_listCons_reduces
    {sourceScope targetScope : Nat}
    (rawRenaming : RawRenaming sourceScope targetScope)
    (headTerm tailTerm : RawTerm sourceScope) :
    RawTerm.rename rawRenaming
        (.mkGen .gen_listCons ()
          (.childCons headTerm
            (.childCons tailTerm .childNil))) =
      (.mkGen .gen_listCons ()
        (.childCons (RawTerm.rename rawRenaming headTerm)
          (.childCons (RawTerm.rename rawRenaming tailTerm)
            .childNil))
        : RawTerm targetScope) := rfl

/-- **Probe: rename distributes over `gen_natSucc`.** -/
theorem RawTerm.rename_natSucc_reduces
    {sourceScope targetScope : Nat}
    (rawRenaming : RawRenaming sourceScope targetScope)
    (predecessorTerm : RawTerm sourceScope) :
    RawTerm.rename rawRenaming
        (.mkGen .gen_natSucc ()
          (.childCons predecessorTerm .childNil)) =
      (.mkGen .gen_natSucc ()
        (.childCons (RawTerm.rename rawRenaming predecessorTerm)
          .childNil)
        : RawTerm targetScope) := rfl

/-- **Probe: rename distributes over `gen_optionSome`.** -/
theorem RawTerm.rename_optionSome_reduces
    {sourceScope targetScope : Nat}
    (rawRenaming : RawRenaming sourceScope targetScope)
    (wrappedTerm : RawTerm sourceScope) :
    RawTerm.rename rawRenaming
        (.mkGen .gen_optionSome ()
          (.childCons wrappedTerm .childNil)) =
      (.mkGen .gen_optionSome ()
        (.childCons (RawTerm.rename rawRenaming wrappedTerm)
          .childNil)
        : RawTerm targetScope) := rfl

/-- **Probe: rename distributes over `gen_eitherInl`.** -/
theorem RawTerm.rename_eitherInl_reduces
    {sourceScope targetScope : Nat}
    (rawRenaming : RawRenaming sourceScope targetScope)
    (wrappedTerm : RawTerm sourceScope) :
    RawTerm.rename rawRenaming
        (.mkGen .gen_eitherInl ()
          (.childCons wrappedTerm .childNil)) =
      (.mkGen .gen_eitherInl ()
        (.childCons (RawTerm.rename rawRenaming wrappedTerm)
          .childNil)
        : RawTerm targetScope) := rfl

/-- **Probe: rename distributes over `gen_eitherInr`.** -/
theorem RawTerm.rename_eitherInr_reduces
    {sourceScope targetScope : Nat}
    (rawRenaming : RawRenaming sourceScope targetScope)
    (wrappedTerm : RawTerm sourceScope) :
    RawTerm.rename rawRenaming
        (.mkGen .gen_eitherInr ()
          (.childCons wrappedTerm .childNil)) =
      (.mkGen .gen_eitherInr ()
        (.childCons (RawTerm.rename rawRenaming wrappedTerm)
          .childNil)
        : RawTerm targetScope) := rfl

/-- **Probe: rename distributes over `gen_refl`.** -/
theorem RawTerm.rename_refl_reduces
    {sourceScope targetScope : Nat}
    (rawRenaming : RawRenaming sourceScope targetScope)
    (witnessTerm : RawTerm sourceScope) :
    RawTerm.rename rawRenaming
        (.mkGen .gen_refl ()
          (.childCons witnessTerm .childNil)) =
      (.mkGen .gen_refl ()
        (.childCons (RawTerm.rename rawRenaming witnessTerm)
          .childNil)
        : RawTerm targetScope) := rfl

/-- **Probe: rename distributes over `gen_lam` (BINDER CASE).**

The body's renaming uses `RawRenaming.lift rawRenaming` — the
renaming shifted under one binder.  This is the key fold-engine
property that makes compound preservation under binders
tractable: the binder lift is also definitional. -/
theorem RawTerm.rename_lam_reduces
    {sourceScope targetScope : Nat}
    (rawRenaming : RawRenaming sourceScope targetScope)
    (bodyTerm : RawTerm (sourceScope + 1)) :
    RawTerm.rename rawRenaming
        ((.mkGen .gen_lam ()
          (.childCons bodyTerm .childNil)) : RawTerm sourceScope) =
      ((.mkGen .gen_lam ()
        (.childCons (RawTerm.rename (RawRenaming.lift rawRenaming) bodyTerm)
          .childNil)) : RawTerm targetScope) := rfl

/-! ## Section 2 — Compound cell-level preservation (compositional)

Each theorem takes the RENAMED CHILDREN'S CELLS as inputs and
produces the certification of the renamed PARENT term.  This is
the **inductive step** of the structural induction over PolyCell
that the full `preservedByRename` theorem will use. -/

/-- **`app` preserved by rename (compositional form).**

Given the renamed function and argument cells, build the renamed
app cell.  This will compose with the structural induction's IH
on each child. -/
theorem HasCertifiedCellDim0.app_preservedByRename
    {profile : PolyProfile} {sourceScope targetScope : Nat}
    (rawRenaming : RawRenaming sourceScope targetScope)
    (functionTerm argumentTerm : RawTerm sourceScope)
    (renamedFunctionCell :
      PolyCell profile .term 0 targetScope CellBoundary.trivial
        (.termBase (RawTerm.rename rawRenaming functionTerm)))
    (renamedArgumentCell :
      PolyCell profile .term 0 targetScope CellBoundary.trivial
        (.termBase (RawTerm.rename rawRenaming argumentTerm))) :
    HasCertifiedCellDim0 (profile := profile)
      (RawTerm.rename rawRenaming
        (.mkGen .gen_app ()
          (.childCons functionTerm
            (.childCons argumentTerm .childNil)))) := by
  rw [RawTerm.rename_app_reduces]
  exact HasCertifiedCellDim0.app renamedFunctionCell renamedArgumentCell

/-- **`pair` preserved by rename (compositional form).** -/
theorem HasCertifiedCellDim0.pair_preservedByRename
    {profile : PolyProfile} {sourceScope targetScope : Nat}
    (rawRenaming : RawRenaming sourceScope targetScope)
    (firstTerm secondTerm : RawTerm sourceScope)
    (renamedFirstCell :
      PolyCell profile .term 0 targetScope CellBoundary.trivial
        (.termBase (RawTerm.rename rawRenaming firstTerm)))
    (renamedSecondCell :
      PolyCell profile .term 0 targetScope CellBoundary.trivial
        (.termBase (RawTerm.rename rawRenaming secondTerm))) :
    HasCertifiedCellDim0 (profile := profile)
      (RawTerm.rename rawRenaming
        (.mkGen .gen_pair ()
          (.childCons firstTerm
            (.childCons secondTerm .childNil)))) := by
  rw [RawTerm.rename_pair_reduces]
  exact HasCertifiedCellDim0.pair renamedFirstCell renamedSecondCell

/-- **`listCons` preserved by rename (compositional form).** -/
theorem HasCertifiedCellDim0.listCons_preservedByRename
    {profile : PolyProfile} {sourceScope targetScope : Nat}
    (rawRenaming : RawRenaming sourceScope targetScope)
    (headTerm tailTerm : RawTerm sourceScope)
    (renamedHeadCell :
      PolyCell profile .term 0 targetScope CellBoundary.trivial
        (.termBase (RawTerm.rename rawRenaming headTerm)))
    (renamedTailCell :
      PolyCell profile .term 0 targetScope CellBoundary.trivial
        (.termBase (RawTerm.rename rawRenaming tailTerm))) :
    HasCertifiedCellDim0 (profile := profile)
      (RawTerm.rename rawRenaming
        (.mkGen .gen_listCons ()
          (.childCons headTerm
            (.childCons tailTerm .childNil)))) := by
  rw [RawTerm.rename_listCons_reduces]
  exact HasCertifiedCellDim0.listCons renamedHeadCell renamedTailCell

/-- **`natSucc` preserved by rename (compositional form).** -/
theorem HasCertifiedCellDim0.natSucc_preservedByRename
    {profile : PolyProfile} {sourceScope targetScope : Nat}
    (rawRenaming : RawRenaming sourceScope targetScope)
    (predecessorTerm : RawTerm sourceScope)
    (renamedPredecessorCell :
      PolyCell profile .term 0 targetScope CellBoundary.trivial
        (.termBase (RawTerm.rename rawRenaming predecessorTerm))) :
    HasCertifiedCellDim0 (profile := profile)
      (RawTerm.rename rawRenaming
        (.mkGen .gen_natSucc ()
          (.childCons predecessorTerm .childNil))) := by
  rw [RawTerm.rename_natSucc_reduces]
  exact HasCertifiedCellDim0.natSucc renamedPredecessorCell

/-- **`optionSome` preserved by rename (compositional form).** -/
theorem HasCertifiedCellDim0.optionSome_preservedByRename
    {profile : PolyProfile} {sourceScope targetScope : Nat}
    (rawRenaming : RawRenaming sourceScope targetScope)
    (wrappedTerm : RawTerm sourceScope)
    (renamedWrappedCell :
      PolyCell profile .term 0 targetScope CellBoundary.trivial
        (.termBase (RawTerm.rename rawRenaming wrappedTerm))) :
    HasCertifiedCellDim0 (profile := profile)
      (RawTerm.rename rawRenaming
        (.mkGen .gen_optionSome ()
          (.childCons wrappedTerm .childNil))) := by
  rw [RawTerm.rename_optionSome_reduces]
  exact HasCertifiedCellDim0.optionSome renamedWrappedCell

/-- **`eitherInl` preserved by rename (compositional form).** -/
theorem HasCertifiedCellDim0.eitherInl_preservedByRename
    {profile : PolyProfile} {sourceScope targetScope : Nat}
    (rawRenaming : RawRenaming sourceScope targetScope)
    (wrappedTerm : RawTerm sourceScope)
    (renamedWrappedCell :
      PolyCell profile .term 0 targetScope CellBoundary.trivial
        (.termBase (RawTerm.rename rawRenaming wrappedTerm))) :
    HasCertifiedCellDim0 (profile := profile)
      (RawTerm.rename rawRenaming
        (.mkGen .gen_eitherInl ()
          (.childCons wrappedTerm .childNil))) := by
  rw [RawTerm.rename_eitherInl_reduces]
  exact HasCertifiedCellDim0.eitherInl renamedWrappedCell

/-- **`eitherInr` preserved by rename (compositional form).** -/
theorem HasCertifiedCellDim0.eitherInr_preservedByRename
    {profile : PolyProfile} {sourceScope targetScope : Nat}
    (rawRenaming : RawRenaming sourceScope targetScope)
    (wrappedTerm : RawTerm sourceScope)
    (renamedWrappedCell :
      PolyCell profile .term 0 targetScope CellBoundary.trivial
        (.termBase (RawTerm.rename rawRenaming wrappedTerm))) :
    HasCertifiedCellDim0 (profile := profile)
      (RawTerm.rename rawRenaming
        (.mkGen .gen_eitherInr ()
          (.childCons wrappedTerm .childNil))) := by
  rw [RawTerm.rename_eitherInr_reduces]
  exact HasCertifiedCellDim0.eitherInr renamedWrappedCell

/-- **`refl` preserved by rename (compositional form).** -/
theorem HasCertifiedCellDim0.refl_preservedByRename
    {profile : PolyProfile} {sourceScope targetScope : Nat}
    (rawRenaming : RawRenaming sourceScope targetScope)
    (witnessTerm : RawTerm sourceScope)
    (renamedWitnessCell :
      PolyCell profile .term 0 targetScope CellBoundary.trivial
        (.termBase (RawTerm.rename rawRenaming witnessTerm))) :
    HasCertifiedCellDim0 (profile := profile)
      (RawTerm.rename rawRenaming
        (.mkGen .gen_refl ()
          (.childCons witnessTerm .childNil))) := by
  rw [RawTerm.rename_refl_reduces]
  exact HasCertifiedCellDim0.refl renamedWitnessCell

/-- **`lam` preserved by rename (compositional form, BINDER CASE).**

The body's renamed cell uses the LIFTED renaming, since lam's
body lives under one binder.  This compositional form propagates
the binder discipline cleanly through the structural induction. -/
theorem HasCertifiedCellDim0.lam_preservedByRename
    {profile : PolyProfile} {sourceScope targetScope : Nat}
    (rawRenaming : RawRenaming sourceScope targetScope)
    (bodyTerm : RawTerm (sourceScope + 1))
    (renamedBodyCell :
      PolyCell profile .term 0 (targetScope + 1) CellBoundary.trivial
        (.termBase (RawTerm.rename
          (RawRenaming.lift rawRenaming) bodyTerm))) :
    HasCertifiedCellDim0 (profile := profile)
      (RawTerm.rename rawRenaming
        ((.mkGen .gen_lam ()
          (.childCons bodyTerm .childNil)) : RawTerm sourceScope)) := by
  rw [RawTerm.rename_lam_reduces]
  exact HasCertifiedCellDim0.lam renamedBodyCell

end FX1Poly.Core
