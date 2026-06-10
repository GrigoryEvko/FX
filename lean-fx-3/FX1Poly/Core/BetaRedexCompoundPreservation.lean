import FX1Poly.Core.HasCertifiedComposition
import FX1Poly.Core.BetaRedexLeafPreservation

/-! # Foundation/PolyCell/Core/BetaRedexCompoundPreservation
   — beta-redex compound preservations (subst0 distributing over compounds)

Sibling to `BetaRedexLeafPreservation.lean`; ships the
**compositional inductive step** of the structural SR-beta theorem
for the compound body shapes.

## What this ships

For each of the 9 compound generators
(app/pair/listCons/natSucc/optionSome/eitherInl/eitherInr/refl/lam),
two theorems:

1. **`subst0_X_reduces`** — subst0 distributes over the spine by
   `rfl`.  Same fold-engine distributivity that powers the
   rename/subst probes, specialized to subst0
   (`subst0 = subst ∘ singleton`).

2. **`HasCertifiedCellDim0.subst0_X_preservation`** — given the
   substituted children's certs as inputs, produces the parent's
   cert.  Same compositional template as
   `app_preservedBySubst` etc: `rw [subst0_X_reduces]; exact .X-intro`.

## Binder case (`lam`) discipline

The lam body lives at scope+2 (one binder deeper than the outer
body at scope+1).  Subst0 acts on the outer body via the
singleton substitution; under the lam's binder it must lift to
`RawTermSubst.lift (RawTermSubst.singleton rawArg)`.  The
compositional preservation takes the inner cell at scope+1
already substituted with the lifted singleton.

## How this combines with SR-beta

Beta redex: `app (lam outerBody) outerArg → subst0 outerBody outerArg`.

When `outerBody` has compound shape `(.mkGen .gen_X () [children])`,
the structural induction's inductive step is:
  1. Recurse on each child to get its subst0 preservation.
  2. Apply the compound subst0 preservation to combine them.

This file ships step 2 (the COMBINING half) for all 9 compound
shapes.  Step 1 (the RECURSIVE CALL) is supplied by the full
structural induction's mutual block.

## Coverage

| Generator    | Children    | Binder shifts | Inner subst         |
|--------------|-------------|---------------|---------------------|
| app          | f, a        | [0; 0]        | singleton           |
| pair         | first, sec  | [0; 0]        | singleton           |
| listCons     | head, tail  | [0; 0]        | singleton           |
| natSucc      | pred        | [0]           | singleton           |
| optionSome   | wrapped     | [0]           | singleton           |
| eitherInl    | wrapped     | [0]           | singleton           |
| eitherInr    | wrapped     | [0]           | singleton           |
| refl         | witness     | [0]           | singleton           |
| lam          | innerBody   | [1]           | lift singleton      |

Binder shift `[1]` for lam means innerBody lives at scope+1+1
relative to the substitution's target scope.

## Zero-axiom verification

Each reduction probe closes by `rfl` — `RawTerm.subst0 = subst ∘
singleton`, and subst distributes over compounds by `rfl` (the
existing `subst_X_reduces` probes).  Each preservation closes
by `rw + exact .X-intro`.  No propext / Quot.sound / Classical.choice.

Audit-gated.
-/

namespace FX1Poly.Core

open FX1Poly.Foundation

/-! ## Section 1 — subst0 distributivity probes for compound bodies -/

/-- **Probe: subst0 distributes over `gen_app`.** -/
theorem RawTerm.subst0_app_reduces
    {scope : Nat} (rawArg : RawTerm scope)
    (functionTerm argumentTerm : RawTerm (scope + 1)) :
    RawTerm.subst0
        ((.mkGen .gen_app ()
          (.childCons functionTerm
            (.childCons argumentTerm .childNil))) : RawTerm (scope + 1))
        rawArg =
      (.mkGen .gen_app ()
        (.childCons (RawTerm.subst0 functionTerm rawArg)
          (.childCons (RawTerm.subst0 argumentTerm rawArg) .childNil))
        : RawTerm scope) := rfl

/-- **Probe: subst0 distributes over `gen_pair`.** -/
theorem RawTerm.subst0_pair_reduces
    {scope : Nat} (rawArg : RawTerm scope)
    (firstTerm secondTerm : RawTerm (scope + 1)) :
    RawTerm.subst0
        ((.mkGen .gen_pair ()
          (.childCons firstTerm
            (.childCons secondTerm .childNil))) : RawTerm (scope + 1))
        rawArg =
      (.mkGen .gen_pair ()
        (.childCons (RawTerm.subst0 firstTerm rawArg)
          (.childCons (RawTerm.subst0 secondTerm rawArg) .childNil))
        : RawTerm scope) := rfl

/-- **Probe: subst0 distributes over `gen_listCons`.** -/
theorem RawTerm.subst0_listCons_reduces
    {scope : Nat} (rawArg : RawTerm scope)
    (headTerm tailTerm : RawTerm (scope + 1)) :
    RawTerm.subst0
        ((.mkGen .gen_listCons ()
          (.childCons headTerm
            (.childCons tailTerm .childNil))) : RawTerm (scope + 1))
        rawArg =
      (.mkGen .gen_listCons ()
        (.childCons (RawTerm.subst0 headTerm rawArg)
          (.childCons (RawTerm.subst0 tailTerm rawArg) .childNil))
        : RawTerm scope) := rfl

/-- **Probe: subst0 distributes over `gen_natSucc`.** -/
theorem RawTerm.subst0_natSucc_reduces
    {scope : Nat} (rawArg : RawTerm scope)
    (predecessorTerm : RawTerm (scope + 1)) :
    RawTerm.subst0
        ((.mkGen .gen_natSucc ()
          (.childCons predecessorTerm .childNil)) : RawTerm (scope + 1))
        rawArg =
      (.mkGen .gen_natSucc ()
        (.childCons (RawTerm.subst0 predecessorTerm rawArg) .childNil)
        : RawTerm scope) := rfl

/-- **Probe: subst0 distributes over `gen_optionSome`.** -/
theorem RawTerm.subst0_optionSome_reduces
    {scope : Nat} (rawArg : RawTerm scope)
    (wrappedTerm : RawTerm (scope + 1)) :
    RawTerm.subst0
        ((.mkGen .gen_optionSome ()
          (.childCons wrappedTerm .childNil)) : RawTerm (scope + 1))
        rawArg =
      (.mkGen .gen_optionSome ()
        (.childCons (RawTerm.subst0 wrappedTerm rawArg) .childNil)
        : RawTerm scope) := rfl

/-- **Probe: subst0 distributes over `gen_eitherInl`.** -/
theorem RawTerm.subst0_eitherInl_reduces
    {scope : Nat} (rawArg : RawTerm scope)
    (wrappedTerm : RawTerm (scope + 1)) :
    RawTerm.subst0
        ((.mkGen .gen_eitherInl ()
          (.childCons wrappedTerm .childNil)) : RawTerm (scope + 1))
        rawArg =
      (.mkGen .gen_eitherInl ()
        (.childCons (RawTerm.subst0 wrappedTerm rawArg) .childNil)
        : RawTerm scope) := rfl

/-- **Probe: subst0 distributes over `gen_eitherInr`.** -/
theorem RawTerm.subst0_eitherInr_reduces
    {scope : Nat} (rawArg : RawTerm scope)
    (wrappedTerm : RawTerm (scope + 1)) :
    RawTerm.subst0
        ((.mkGen .gen_eitherInr ()
          (.childCons wrappedTerm .childNil)) : RawTerm (scope + 1))
        rawArg =
      (.mkGen .gen_eitherInr ()
        (.childCons (RawTerm.subst0 wrappedTerm rawArg) .childNil)
        : RawTerm scope) := rfl

/-- **Probe: subst0 distributes over `gen_refl`.** -/
theorem RawTerm.subst0_refl_reduces
    {scope : Nat} (rawArg : RawTerm scope)
    (witnessTerm : RawTerm (scope + 1)) :
    RawTerm.subst0
        ((.mkGen .gen_refl ()
          (.childCons witnessTerm .childNil)) : RawTerm (scope + 1))
        rawArg =
      (.mkGen .gen_refl ()
        (.childCons (RawTerm.subst0 witnessTerm rawArg) .childNil)
        : RawTerm scope) := rfl

/-- **Probe: subst0 distributes over `gen_lam` (BINDER CASE).**

The inner body lives at scope+2 (the outer body at scope+1, plus
one for lam's binder).  Under subst0, the lam's body is
substituted with the LIFTED singleton substitution
`RawTermSubst.lift (RawTermSubst.singleton rawArg)`.

Closes by `rfl` — the fold engine's binder discipline is
definitional. -/
theorem RawTerm.subst0_lam_reduces
    {scope : Nat} (rawArg : RawTerm scope)
    (innerDomain : RawTerm (scope + 1))
    (innerBody : RawTerm (scope + 2)) :
    RawTerm.subst0
        ((.mkGen .gen_lam ()
          (.childCons innerDomain (.childCons innerBody .childNil))) :
          RawTerm (scope + 1))
        rawArg =
      (.mkGen .gen_lam ()
        (.childCons
          (RawTerm.subst0 innerDomain rawArg)
          (.childCons
            (RawTerm.subst
              (RawTermSubst.lift (RawTermSubst.singleton rawArg))
              innerBody)
            .childNil))
        : RawTerm scope) := rfl

/-! ## Section 2 — compound beta-redex preservations

Each preservation takes the substituted children's cells and
produces the parent's certification under subst0.  These are the
COMPOSITIONAL inductive steps the structural induction dispatches
to. -/

/-- **Beta-redex: `(lam (.gen_app () [f, a])) outerArg →
    .gen_app () [subst0 f outerArg, subst0 a outerArg]`.** -/
theorem HasCertifiedCellDim0.subst0_app_preservation
    {profile : PolyProfile} {scope : Nat}
    (rawArg : RawTerm scope)
    (functionTerm argumentTerm : RawTerm (scope + 1))
    (substFunctionCell :
      PolyCell profile .term 0 scope CellBoundary.trivial
        (.termBase (RawTerm.subst0 functionTerm rawArg)))
    (substArgumentCell :
      PolyCell profile .term 0 scope CellBoundary.trivial
        (.termBase (RawTerm.subst0 argumentTerm rawArg))) :
    HasCertifiedCellDim0 (profile := profile)
      (RawTerm.subst0
        ((.mkGen .gen_app ()
          (.childCons functionTerm
            (.childCons argumentTerm .childNil))) : RawTerm (scope + 1))
        rawArg) := by
  rw [RawTerm.subst0_app_reduces]
  exact HasCertifiedCellDim0.app substFunctionCell substArgumentCell

/-- **Beta-redex: `(lam (.gen_pair () [f, s])) outerArg →
    .gen_pair () [subst0 f outerArg, subst0 s outerArg]`.** -/
theorem HasCertifiedCellDim0.subst0_pair_preservation
    {profile : PolyProfile} {scope : Nat}
    (rawArg : RawTerm scope)
    (firstTerm secondTerm : RawTerm (scope + 1))
    (substFirstCell :
      PolyCell profile .term 0 scope CellBoundary.trivial
        (.termBase (RawTerm.subst0 firstTerm rawArg)))
    (substSecondCell :
      PolyCell profile .term 0 scope CellBoundary.trivial
        (.termBase (RawTerm.subst0 secondTerm rawArg))) :
    HasCertifiedCellDim0 (profile := profile)
      (RawTerm.subst0
        ((.mkGen .gen_pair ()
          (.childCons firstTerm
            (.childCons secondTerm .childNil))) : RawTerm (scope + 1))
        rawArg) := by
  rw [RawTerm.subst0_pair_reduces]
  exact HasCertifiedCellDim0.pair substFirstCell substSecondCell

/-- **Beta-redex: `(lam (.gen_listCons () [h, t])) outerArg →
    .gen_listCons () [subst0 h outerArg, subst0 t outerArg]`.** -/
theorem HasCertifiedCellDim0.subst0_listCons_preservation
    {profile : PolyProfile} {scope : Nat}
    (rawArg : RawTerm scope)
    (headTerm tailTerm : RawTerm (scope + 1))
    (substHeadCell :
      PolyCell profile .term 0 scope CellBoundary.trivial
        (.termBase (RawTerm.subst0 headTerm rawArg)))
    (substTailCell :
      PolyCell profile .term 0 scope CellBoundary.trivial
        (.termBase (RawTerm.subst0 tailTerm rawArg))) :
    HasCertifiedCellDim0 (profile := profile)
      (RawTerm.subst0
        ((.mkGen .gen_listCons ()
          (.childCons headTerm
            (.childCons tailTerm .childNil))) : RawTerm (scope + 1))
        rawArg) := by
  rw [RawTerm.subst0_listCons_reduces]
  exact HasCertifiedCellDim0.listCons substHeadCell substTailCell

/-- **Beta-redex: `(lam (.gen_natSucc () [p])) outerArg →
    .gen_natSucc () [subst0 p outerArg]`.** -/
theorem HasCertifiedCellDim0.subst0_natSucc_preservation
    {profile : PolyProfile} {scope : Nat}
    (rawArg : RawTerm scope)
    (predecessorTerm : RawTerm (scope + 1))
    (substPredecessorCell :
      PolyCell profile .term 0 scope CellBoundary.trivial
        (.termBase (RawTerm.subst0 predecessorTerm rawArg))) :
    HasCertifiedCellDim0 (profile := profile)
      (RawTerm.subst0
        ((.mkGen .gen_natSucc ()
          (.childCons predecessorTerm .childNil)) : RawTerm (scope + 1))
        rawArg) := by
  rw [RawTerm.subst0_natSucc_reduces]
  exact HasCertifiedCellDim0.natSucc substPredecessorCell

/-- **Beta-redex: `(lam (.gen_optionSome () [w])) outerArg →
    .gen_optionSome () [subst0 w outerArg]`.** -/
theorem HasCertifiedCellDim0.subst0_optionSome_preservation
    {profile : PolyProfile} {scope : Nat}
    (rawArg : RawTerm scope)
    (wrappedTerm : RawTerm (scope + 1))
    (substWrappedCell :
      PolyCell profile .term 0 scope CellBoundary.trivial
        (.termBase (RawTerm.subst0 wrappedTerm rawArg))) :
    HasCertifiedCellDim0 (profile := profile)
      (RawTerm.subst0
        ((.mkGen .gen_optionSome ()
          (.childCons wrappedTerm .childNil)) : RawTerm (scope + 1))
        rawArg) := by
  rw [RawTerm.subst0_optionSome_reduces]
  exact HasCertifiedCellDim0.optionSome substWrappedCell

/-- **Beta-redex: `(lam (.gen_eitherInl () [w])) outerArg →
    .gen_eitherInl () [subst0 w outerArg]`.** -/
theorem HasCertifiedCellDim0.subst0_eitherInl_preservation
    {profile : PolyProfile} {scope : Nat}
    (rawArg : RawTerm scope)
    (wrappedTerm : RawTerm (scope + 1))
    (substWrappedCell :
      PolyCell profile .term 0 scope CellBoundary.trivial
        (.termBase (RawTerm.subst0 wrappedTerm rawArg))) :
    HasCertifiedCellDim0 (profile := profile)
      (RawTerm.subst0
        ((.mkGen .gen_eitherInl ()
          (.childCons wrappedTerm .childNil)) : RawTerm (scope + 1))
        rawArg) := by
  rw [RawTerm.subst0_eitherInl_reduces]
  exact HasCertifiedCellDim0.eitherInl substWrappedCell

/-- **Beta-redex: `(lam (.gen_eitherInr () [w])) outerArg →
    .gen_eitherInr () [subst0 w outerArg]`.** -/
theorem HasCertifiedCellDim0.subst0_eitherInr_preservation
    {profile : PolyProfile} {scope : Nat}
    (rawArg : RawTerm scope)
    (wrappedTerm : RawTerm (scope + 1))
    (substWrappedCell :
      PolyCell profile .term 0 scope CellBoundary.trivial
        (.termBase (RawTerm.subst0 wrappedTerm rawArg))) :
    HasCertifiedCellDim0 (profile := profile)
      (RawTerm.subst0
        ((.mkGen .gen_eitherInr ()
          (.childCons wrappedTerm .childNil)) : RawTerm (scope + 1))
        rawArg) := by
  rw [RawTerm.subst0_eitherInr_reduces]
  exact HasCertifiedCellDim0.eitherInr substWrappedCell

/-- **Beta-redex: `(lam (.gen_refl () [w])) outerArg →
    .gen_refl () [subst0 w outerArg]`.** -/
theorem HasCertifiedCellDim0.subst0_refl_preservation
    {profile : PolyProfile} {scope : Nat}
    (rawArg : RawTerm scope)
    (witnessTerm : RawTerm (scope + 1))
    (substWitnessCell :
      PolyCell profile .term 0 scope CellBoundary.trivial
        (.termBase (RawTerm.subst0 witnessTerm rawArg))) :
    HasCertifiedCellDim0 (profile := profile)
      (RawTerm.subst0
        ((.mkGen .gen_refl ()
          (.childCons witnessTerm .childNil)) : RawTerm (scope + 1))
        rawArg) := by
  rw [RawTerm.subst0_refl_reduces]
  exact HasCertifiedCellDim0.refl substWitnessCell

/-- **Beta-redex: `(lam (.gen_lam () [innerBody])) outerArg →
    .gen_lam () [subst (lift (singleton outerArg)) innerBody]`.**

BINDER CASE.  The inner body lives at scope+2 (one binder deeper
than the outer body at scope+1).  Substitution lifts through the
lam's binder, so the inner subst uses the lifted singleton. -/
theorem HasCertifiedCellDim0.subst0_lam_preservation
    {profile : PolyProfile} {scope : Nat}
    (rawArg : RawTerm scope)
    (innerDomain : RawTerm (scope + 1))
    (innerBody : RawTerm (scope + 2))
    (substInnerDomainCell :
      PolyCell profile .term 0 scope CellBoundary.trivial
        (.termBase (RawTerm.subst0 innerDomain rawArg)))
    (substInnerBodyCell :
      PolyCell profile .term 0 (scope + 1) CellBoundary.trivial
        (.termBase
          (RawTerm.subst
            (RawTermSubst.lift (RawTermSubst.singleton rawArg))
            innerBody))) :
    HasCertifiedCellDim0 (profile := profile)
      (RawTerm.subst0
        ((.mkGen .gen_lam ()
          (.childCons innerDomain (.childCons innerBody .childNil))) :
          RawTerm (scope + 1))
        rawArg) := by
  rw [RawTerm.subst0_lam_reduces]
  exact HasCertifiedCellDim0.lam substInnerDomainCell substInnerBodyCell

end FX1Poly.Core
