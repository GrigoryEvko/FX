import FX1Poly.Core.HasCertifiedComposition
import FX1Poly.Core.SubstPreservationProbes

/-! # Foundation/PolyCell/Core/CompoundSubstPreservation — compound subst preservation

Symmetric to `CompoundRenamePreservation.lean` — ships
**compositional preservation lemmas** for compound generators
under SUBST.

## Why this matters

The structural-induction approach to
`HasCertifiedCellDim0.preservedBySubst` needs the SAME
compositional building blocks as rename: for each compound
generator X, a lemma saying "given the substituted children's
cells, the substituted parent is certified."

Like the rename side, the subst engine's distributivity is
DEFINITIONAL.  `RawTerm.subst σ (mkGen X ...)` reduces by `rfl`
to `mkGen X (substituted children)`, including the binder case
for `gen_lam` (where the body uses `RawTermSubst.lift σ`).

## Why subst's variable case differs from rename's

Rename: `RawTerm.rename ρ (gen_var i)` reduces to a wrapped
`gen_var (ρ i)` — still a `gen_var` shape, always certified via
`HasCertifiedCellDim0.var`.

Subst: `RawTerm.subst σ (gen_var i) = σ i` — the substituent is
WHATEVER `σ i` is.  For preservation, we need to know `σ i` is
itself certified.  This requires an external hypothesis at the
full-theorem level (the "pointwise σ-certification" hypothesis).

Compound subst-preservation doesn't hit this issue because
the children are pre-substituted by the caller.

## Coverage

Same compound generators as the rename side:
  * Binary, no binders: `app`, `pair`, `listCons`
  * Unary, no binders: `natSucc`, `optionSome`, `eitherInl`,
    `eitherInr`, `refl`
  * Unary, 1 binder: `lam` (body uses lifted subst)

## Zero-axiom verification

Each closes by `rw [subst_X_reduces]; exact .X-intro
substChildren`.  Audit-gated.
-/

namespace FX1Poly.Core

open FX1Poly.Foundation

/-! ## Section 1 — Subst distributivity probes (by rfl) -/

/-- **Probe: subst distributes over `gen_app`.** -/
theorem RawTerm.subst_app_reduces
    {sourceScope targetScope : Nat}
    (substitution : RawTermSubst sourceScope targetScope)
    (functionTerm argumentTerm : RawTerm sourceScope) :
    RawTerm.subst substitution
        (.mkGen .gen_app ()
          (.childCons functionTerm
            (.childCons argumentTerm .childNil))) =
      (.mkGen .gen_app ()
        (.childCons (RawTerm.subst substitution functionTerm)
          (.childCons (RawTerm.subst substitution argumentTerm)
            .childNil))
        : RawTerm targetScope) := rfl

/-- **Probe: subst distributes over `gen_pair`.** -/
theorem RawTerm.subst_pair_reduces
    {sourceScope targetScope : Nat}
    (substitution : RawTermSubst sourceScope targetScope)
    (firstTerm secondTerm : RawTerm sourceScope) :
    RawTerm.subst substitution
        (.mkGen .gen_pair ()
          (.childCons firstTerm
            (.childCons secondTerm .childNil))) =
      (.mkGen .gen_pair ()
        (.childCons (RawTerm.subst substitution firstTerm)
          (.childCons (RawTerm.subst substitution secondTerm)
            .childNil))
        : RawTerm targetScope) := rfl

/-- **Probe: subst distributes over `gen_listCons`.** -/
theorem RawTerm.subst_listCons_reduces
    {sourceScope targetScope : Nat}
    (substitution : RawTermSubst sourceScope targetScope)
    (headTerm tailTerm : RawTerm sourceScope) :
    RawTerm.subst substitution
        (.mkGen .gen_listCons ()
          (.childCons headTerm
            (.childCons tailTerm .childNil))) =
      (.mkGen .gen_listCons ()
        (.childCons (RawTerm.subst substitution headTerm)
          (.childCons (RawTerm.subst substitution tailTerm)
            .childNil))
        : RawTerm targetScope) := rfl

/-- **Probe: subst distributes over `gen_natSucc`.** -/
theorem RawTerm.subst_natSucc_reduces
    {sourceScope targetScope : Nat}
    (substitution : RawTermSubst sourceScope targetScope)
    (predecessorTerm : RawTerm sourceScope) :
    RawTerm.subst substitution
        (.mkGen .gen_natSucc ()
          (.childCons predecessorTerm .childNil)) =
      (.mkGen .gen_natSucc ()
        (.childCons (RawTerm.subst substitution predecessorTerm)
          .childNil)
        : RawTerm targetScope) := rfl

/-- **Probe: subst distributes over `gen_optionSome`.** -/
theorem RawTerm.subst_optionSome_reduces
    {sourceScope targetScope : Nat}
    (substitution : RawTermSubst sourceScope targetScope)
    (wrappedTerm : RawTerm sourceScope) :
    RawTerm.subst substitution
        (.mkGen .gen_optionSome ()
          (.childCons wrappedTerm .childNil)) =
      (.mkGen .gen_optionSome ()
        (.childCons (RawTerm.subst substitution wrappedTerm)
          .childNil)
        : RawTerm targetScope) := rfl

/-- **Probe: subst distributes over `gen_eitherInl`.** -/
theorem RawTerm.subst_eitherInl_reduces
    {sourceScope targetScope : Nat}
    (substitution : RawTermSubst sourceScope targetScope)
    (wrappedTerm : RawTerm sourceScope) :
    RawTerm.subst substitution
        (.mkGen .gen_eitherInl ()
          (.childCons wrappedTerm .childNil)) =
      (.mkGen .gen_eitherInl ()
        (.childCons (RawTerm.subst substitution wrappedTerm)
          .childNil)
        : RawTerm targetScope) := rfl

/-- **Probe: subst distributes over `gen_eitherInr`.** -/
theorem RawTerm.subst_eitherInr_reduces
    {sourceScope targetScope : Nat}
    (substitution : RawTermSubst sourceScope targetScope)
    (wrappedTerm : RawTerm sourceScope) :
    RawTerm.subst substitution
        (.mkGen .gen_eitherInr ()
          (.childCons wrappedTerm .childNil)) =
      (.mkGen .gen_eitherInr ()
        (.childCons (RawTerm.subst substitution wrappedTerm)
          .childNil)
        : RawTerm targetScope) := rfl

/-- **Probe: subst distributes over `gen_refl`.** -/
theorem RawTerm.subst_refl_reduces
    {sourceScope targetScope : Nat}
    (substitution : RawTermSubst sourceScope targetScope)
    (witnessTerm : RawTerm sourceScope) :
    RawTerm.subst substitution
        (.mkGen .gen_refl ()
          (.childCons witnessTerm .childNil)) =
      (.mkGen .gen_refl ()
        (.childCons (RawTerm.subst substitution witnessTerm)
          .childNil)
        : RawTerm targetScope) := rfl

/-- **Probe: subst distributes over `gen_lam` (BINDER CASE).**

Body uses the LIFTED substitution `RawTermSubst.lift σ`,
analogous to rename's `RawRenaming.lift ρ`.  Closes by `rfl`. -/
theorem RawTerm.subst_lam_reduces
    {sourceScope targetScope : Nat}
    (substitution : RawTermSubst sourceScope targetScope)
    (bodyTerm : RawTerm (sourceScope + 1)) :
    RawTerm.subst substitution
        ((.mkGen .gen_lam ()
          (.childCons bodyTerm .childNil)) : RawTerm sourceScope) =
      ((.mkGen .gen_lam ()
        (.childCons (RawTerm.subst (RawTermSubst.lift substitution) bodyTerm)
          .childNil)) : RawTerm targetScope) := rfl

/-! ## Section 2 — Compound cell-level subst preservation -/

/-- **`app` preserved by subst (compositional).** -/
theorem HasCertifiedCellDim0.app_preservedBySubst
    {profile : PolyProfile} {sourceScope targetScope : Nat}
    (substitution : RawTermSubst sourceScope targetScope)
    (functionTerm argumentTerm : RawTerm sourceScope)
    (substFunctionCell :
      PolyCell profile .term 0 targetScope CellBoundary.trivial
        (.termBase (RawTerm.subst substitution functionTerm)))
    (substArgumentCell :
      PolyCell profile .term 0 targetScope CellBoundary.trivial
        (.termBase (RawTerm.subst substitution argumentTerm))) :
    HasCertifiedCellDim0 (profile := profile)
      (RawTerm.subst substitution
        (.mkGen .gen_app ()
          (.childCons functionTerm
            (.childCons argumentTerm .childNil)))) := by
  rw [RawTerm.subst_app_reduces]
  exact HasCertifiedCellDim0.app substFunctionCell substArgumentCell

/-- **`pair` preserved by subst (compositional).** -/
theorem HasCertifiedCellDim0.pair_preservedBySubst
    {profile : PolyProfile} {sourceScope targetScope : Nat}
    (substitution : RawTermSubst sourceScope targetScope)
    (firstTerm secondTerm : RawTerm sourceScope)
    (substFirstCell :
      PolyCell profile .term 0 targetScope CellBoundary.trivial
        (.termBase (RawTerm.subst substitution firstTerm)))
    (substSecondCell :
      PolyCell profile .term 0 targetScope CellBoundary.trivial
        (.termBase (RawTerm.subst substitution secondTerm))) :
    HasCertifiedCellDim0 (profile := profile)
      (RawTerm.subst substitution
        (.mkGen .gen_pair ()
          (.childCons firstTerm
            (.childCons secondTerm .childNil)))) := by
  rw [RawTerm.subst_pair_reduces]
  exact HasCertifiedCellDim0.pair substFirstCell substSecondCell

/-- **`listCons` preserved by subst (compositional).** -/
theorem HasCertifiedCellDim0.listCons_preservedBySubst
    {profile : PolyProfile} {sourceScope targetScope : Nat}
    (substitution : RawTermSubst sourceScope targetScope)
    (headTerm tailTerm : RawTerm sourceScope)
    (substHeadCell :
      PolyCell profile .term 0 targetScope CellBoundary.trivial
        (.termBase (RawTerm.subst substitution headTerm)))
    (substTailCell :
      PolyCell profile .term 0 targetScope CellBoundary.trivial
        (.termBase (RawTerm.subst substitution tailTerm))) :
    HasCertifiedCellDim0 (profile := profile)
      (RawTerm.subst substitution
        (.mkGen .gen_listCons ()
          (.childCons headTerm
            (.childCons tailTerm .childNil)))) := by
  rw [RawTerm.subst_listCons_reduces]
  exact HasCertifiedCellDim0.listCons substHeadCell substTailCell

/-- **`natSucc` preserved by subst (compositional).** -/
theorem HasCertifiedCellDim0.natSucc_preservedBySubst
    {profile : PolyProfile} {sourceScope targetScope : Nat}
    (substitution : RawTermSubst sourceScope targetScope)
    (predecessorTerm : RawTerm sourceScope)
    (substPredecessorCell :
      PolyCell profile .term 0 targetScope CellBoundary.trivial
        (.termBase (RawTerm.subst substitution predecessorTerm))) :
    HasCertifiedCellDim0 (profile := profile)
      (RawTerm.subst substitution
        (.mkGen .gen_natSucc ()
          (.childCons predecessorTerm .childNil))) := by
  rw [RawTerm.subst_natSucc_reduces]
  exact HasCertifiedCellDim0.natSucc substPredecessorCell

/-- **`optionSome` preserved by subst (compositional).** -/
theorem HasCertifiedCellDim0.optionSome_preservedBySubst
    {profile : PolyProfile} {sourceScope targetScope : Nat}
    (substitution : RawTermSubst sourceScope targetScope)
    (wrappedTerm : RawTerm sourceScope)
    (substWrappedCell :
      PolyCell profile .term 0 targetScope CellBoundary.trivial
        (.termBase (RawTerm.subst substitution wrappedTerm))) :
    HasCertifiedCellDim0 (profile := profile)
      (RawTerm.subst substitution
        (.mkGen .gen_optionSome ()
          (.childCons wrappedTerm .childNil))) := by
  rw [RawTerm.subst_optionSome_reduces]
  exact HasCertifiedCellDim0.optionSome substWrappedCell

/-- **`eitherInl` preserved by subst (compositional).** -/
theorem HasCertifiedCellDim0.eitherInl_preservedBySubst
    {profile : PolyProfile} {sourceScope targetScope : Nat}
    (substitution : RawTermSubst sourceScope targetScope)
    (wrappedTerm : RawTerm sourceScope)
    (substWrappedCell :
      PolyCell profile .term 0 targetScope CellBoundary.trivial
        (.termBase (RawTerm.subst substitution wrappedTerm))) :
    HasCertifiedCellDim0 (profile := profile)
      (RawTerm.subst substitution
        (.mkGen .gen_eitherInl ()
          (.childCons wrappedTerm .childNil))) := by
  rw [RawTerm.subst_eitherInl_reduces]
  exact HasCertifiedCellDim0.eitherInl substWrappedCell

/-- **`eitherInr` preserved by subst (compositional).** -/
theorem HasCertifiedCellDim0.eitherInr_preservedBySubst
    {profile : PolyProfile} {sourceScope targetScope : Nat}
    (substitution : RawTermSubst sourceScope targetScope)
    (wrappedTerm : RawTerm sourceScope)
    (substWrappedCell :
      PolyCell profile .term 0 targetScope CellBoundary.trivial
        (.termBase (RawTerm.subst substitution wrappedTerm))) :
    HasCertifiedCellDim0 (profile := profile)
      (RawTerm.subst substitution
        (.mkGen .gen_eitherInr ()
          (.childCons wrappedTerm .childNil))) := by
  rw [RawTerm.subst_eitherInr_reduces]
  exact HasCertifiedCellDim0.eitherInr substWrappedCell

/-- **`refl` preserved by subst (compositional).** -/
theorem HasCertifiedCellDim0.refl_preservedBySubst
    {profile : PolyProfile} {sourceScope targetScope : Nat}
    (substitution : RawTermSubst sourceScope targetScope)
    (witnessTerm : RawTerm sourceScope)
    (substWitnessCell :
      PolyCell profile .term 0 targetScope CellBoundary.trivial
        (.termBase (RawTerm.subst substitution witnessTerm))) :
    HasCertifiedCellDim0 (profile := profile)
      (RawTerm.subst substitution
        (.mkGen .gen_refl ()
          (.childCons witnessTerm .childNil))) := by
  rw [RawTerm.subst_refl_reduces]
  exact HasCertifiedCellDim0.refl substWitnessCell

/-- **`lam` preserved by subst (compositional, BINDER CASE).**

Body uses lifted substitution `RawTermSubst.lift substitution`.
Analogous to rename's `lam_preservedByRename`. -/
theorem HasCertifiedCellDim0.lam_preservedBySubst
    {profile : PolyProfile} {sourceScope targetScope : Nat}
    (substitution : RawTermSubst sourceScope targetScope)
    (bodyTerm : RawTerm (sourceScope + 1))
    (substBodyCell :
      PolyCell profile .term 0 (targetScope + 1) CellBoundary.trivial
        (.termBase (RawTerm.subst
          (RawTermSubst.lift substitution) bodyTerm))) :
    HasCertifiedCellDim0 (profile := profile)
      (RawTerm.subst substitution
        ((.mkGen .gen_lam ()
          (.childCons bodyTerm .childNil)) : RawTerm sourceScope)) := by
  rw [RawTerm.subst_lam_reduces]
  exact HasCertifiedCellDim0.lam substBodyCell

end FX1Poly.Core
