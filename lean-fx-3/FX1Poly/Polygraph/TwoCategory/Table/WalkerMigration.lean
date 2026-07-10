import FX1Poly.Polygraph.TwoCategory.Table.FrobeniusSeed

/-! # Polygraph/TwoCategory/Table/WalkerMigration — the smallest-walker migration playbook (POLY-TAB r0, T4)

The POLY-TAB thesis: a walker's symbolic 2-cell congruence should be BORN on the generic `SaturatedConvOver`
carrier (a `CellRel` of law rows), not re-declared as a bespoke inductive that re-states the seven congruence
constructors.  The `Table/FrobeniusSeed.lean` Frobenius spider is exactly that — a NEW walker with NO bespoke
inductive, so its "migration" to the generic is the identity (nothing to bridge).

This file demonstrates the OTHER direction — the RETIREMENT bridge for a walker that DID ship a bespoke inductive.
It is the monad exemplar's playbook (`monadSaturated_iff_generic`, `Amalgam/SaturatedOver.lean`) applied to the
SMALLEST possible law set: a ONE-law bespoke walker (`FrobeniusSpecialWalkerConv`, the walking special-Frobenius
relation `mult . comult ~ id_t`) proved logically identical to the generic `SaturatedConvOver` at its one-row law
relation.  Each direction is one structural fold, ctor-for-ctor — the reusable migration recipe:

  1. **forward** (`frobeniusSpecialWalker_to_generic`): induction on the bespoke conv, each congruence ctor to the
     same-named generic ctor, the law to `ofRelation`;
  2. **backward** (`generic_to_frobeniusSpecialWalker`): the bespoke conv absorbs the generic congruence (an
     `IsSaturatedCongruence` record), fed to the universal property `SaturatedConvOver.recInto`;
  3. **bridge** (`frobeniusSpecialWalker_iff_generic`): the two-way iso, the migration certificate.

REGRESSION VERDICT: the bespoke walker and the generic decide the same relation (the iff), so any decision or
soundness fact proved for one transports to the other with zero re-proof — the retirement is behaviour-preserving.
This is the value + bridge-iff + regression triple the migration playbook requires, at minimal law count.

Raw Lean 4 + Init; the bespoke relation is an inductive `Prop`, the bridge is two structural folds, so every
declaration is `propext`/`Quot.sound`/`Classical`/`sorry`/`native_decide`/`omega`-free.  Additive — nothing
outside `Table/` is touched.  Per-declaration `#assert_no_axioms` in the audit twin. -/

namespace FX1Poly.Polygraph

open FX1Poly.Polygraph.Amalgam

/-! ## The one-law law relation -/

/-- The **walking special-Frobenius relation as a `CellRel`** — a single row, the special law `mult . comult ~
id_t`.  The smallest non-trivial base relation, for demonstrating the migration bridge. -/
inductive FrobeniusSpecialLawRel :
    {sourceMode targetMode : FrobeniusMode} →
    {sourcePath targetPath : ModalityPath frobeniusGraph sourceMode targetMode} →
    RawTwoCellExpr frobeniusModeSignature sourcePath targetPath →
    RawTwoCellExpr frobeniusModeSignature sourcePath targetPath → Prop where
  /-- The special law `comult . mult ~ id_t`. -/
  | special : FrobeniusSpecialLawRel frobeniusSpecialCell frobeniusIdTCell

/-! ## The bespoke walker (the shape a hand-written walker would take) -/

/-- The **bespoke walking-special-Frobenius 2-cell convertibility** — the completed free convertibility plus the
one special law, made a congruence by the four one-hole congruences and `refl`/`symm`/`trans`.  This is the shape
a hand-authored walker takes; the migration below retires it into the generic. -/
inductive FrobeniusSpecialWalkerConv :
    {sourceMode targetMode : FrobeniusMode} →
    {sourcePath targetPath : ModalityPath frobeniusGraph sourceMode targetMode} →
    RawTwoCellExpr frobeniusModeSignature sourcePath targetPath →
    RawTwoCellExpr frobeniusModeSignature sourcePath targetPath → Prop where
  /-- Embed the completed free convertibility. -/
  | ofFull {sourceMode targetMode : FrobeniusMode}
      {sourcePath targetPath : ModalityPath frobeniusGraph sourceMode targetMode}
      {cellAlpha cellBeta : RawTwoCellExpr frobeniusModeSignature sourcePath targetPath} :
      TwoCellConvFull frobeniusModeSignature cellAlpha cellBeta →
      FrobeniusSpecialWalkerConv cellAlpha cellBeta
  /-- The special law `comult . mult ~ id_t`. -/
  | special : FrobeniusSpecialWalkerConv frobeniusSpecialCell frobeniusIdTCell
  /-- Congruence in the LEFT factor of a vertical composite. -/
  | vcompCongrLeft {sourceMode targetMode : FrobeniusMode}
      {oneCellF oneCellG oneCellH : ModalityPath frobeniusGraph sourceMode targetMode}
      {cellAlpha cellAlpha' : RawTwoCellExpr frobeniusModeSignature oneCellF oneCellG}
      (cellBeta : RawTwoCellExpr frobeniusModeSignature oneCellG oneCellH) :
      FrobeniusSpecialWalkerConv cellAlpha cellAlpha' →
      FrobeniusSpecialWalkerConv (RawTwoCellExpr.vcomp cellAlpha cellBeta)
        (RawTwoCellExpr.vcomp cellAlpha' cellBeta)
  /-- Congruence in the RIGHT factor of a vertical composite. -/
  | vcompCongrRight {sourceMode targetMode : FrobeniusMode}
      {oneCellF oneCellG oneCellH : ModalityPath frobeniusGraph sourceMode targetMode}
      (cellAlpha : RawTwoCellExpr frobeniusModeSignature oneCellF oneCellG)
      {cellBeta cellBeta' : RawTwoCellExpr frobeniusModeSignature oneCellG oneCellH} :
      FrobeniusSpecialWalkerConv cellBeta cellBeta' →
      FrobeniusSpecialWalkerConv (RawTwoCellExpr.vcomp cellAlpha cellBeta)
        (RawTwoCellExpr.vcomp cellAlpha cellBeta')
  /-- Congruence under a left whiskering. -/
  | whiskerLeftCongr {sourceMode middleMode targetMode : FrobeniusMode}
      (oneCell : ModalityPath frobeniusGraph sourceMode middleMode)
      {oneCellG oneCellH : ModalityPath frobeniusGraph middleMode targetMode}
      {cellBeta cellBeta' : RawTwoCellExpr frobeniusModeSignature oneCellG oneCellH} :
      FrobeniusSpecialWalkerConv cellBeta cellBeta' →
      FrobeniusSpecialWalkerConv (RawTwoCellExpr.whiskerLeft oneCell cellBeta)
        (RawTwoCellExpr.whiskerLeft oneCell cellBeta')
  /-- Congruence under a right whiskering. -/
  | whiskerRightCongr {sourceMode middleMode targetMode : FrobeniusMode}
      {oneCellF oneCellG : ModalityPath frobeniusGraph sourceMode middleMode}
      (oneCell : ModalityPath frobeniusGraph middleMode targetMode)
      {cellAlpha cellAlpha' : RawTwoCellExpr frobeniusModeSignature oneCellF oneCellG} :
      FrobeniusSpecialWalkerConv cellAlpha cellAlpha' →
      FrobeniusSpecialWalkerConv (RawTwoCellExpr.whiskerRight oneCell cellAlpha)
        (RawTwoCellExpr.whiskerRight oneCell cellAlpha')
  /-- Reflexivity. -/
  | refl {sourceMode targetMode : FrobeniusMode}
      {sourcePath targetPath : ModalityPath frobeniusGraph sourceMode targetMode}
      (cell : RawTwoCellExpr frobeniusModeSignature sourcePath targetPath) :
      FrobeniusSpecialWalkerConv cell cell
  /-- Symmetry. -/
  | symm {sourceMode targetMode : FrobeniusMode}
      {sourcePath targetPath : ModalityPath frobeniusGraph sourceMode targetMode}
      {cellAlpha cellBeta : RawTwoCellExpr frobeniusModeSignature sourcePath targetPath} :
      FrobeniusSpecialWalkerConv cellAlpha cellBeta → FrobeniusSpecialWalkerConv cellBeta cellAlpha
  /-- Transitivity. -/
  | trans {sourceMode targetMode : FrobeniusMode}
      {sourcePath targetPath : ModalityPath frobeniusGraph sourceMode targetMode}
      {cellAlpha cellBeta cellGamma : RawTwoCellExpr frobeniusModeSignature sourcePath targetPath} :
      FrobeniusSpecialWalkerConv cellAlpha cellBeta → FrobeniusSpecialWalkerConv cellBeta cellGamma →
      FrobeniusSpecialWalkerConv cellAlpha cellGamma

/-! ## The migration bridge (the reusable playbook) -/

/-- **Forward** — the bespoke walker maps into the generic at `FrobeniusSpecialLawRel`.  Structural induction,
each congruence ctor to the same-named generic ctor; the special law lands as `ofRelation`. -/
theorem frobeniusSpecialWalker_to_generic {sourceMode targetMode : FrobeniusMode}
    {sourcePath targetPath : ModalityPath frobeniusGraph sourceMode targetMode}
    {cellAlpha cellBeta : RawTwoCellExpr frobeniusModeSignature sourcePath targetPath}
    (conv : FrobeniusSpecialWalkerConv cellAlpha cellBeta) :
    SaturatedConvOver frobeniusModeSignature FrobeniusSpecialLawRel cellAlpha cellBeta := by
  induction conv with
  | ofFull full => exact SaturatedConvOver.ofFull full
  | special => exact SaturatedConvOver.ofRelation FrobeniusSpecialLawRel.special
  | vcompCongrLeft cellBeta _ ih => exact SaturatedConvOver.vcompCongrLeft cellBeta ih
  | vcompCongrRight cellAlpha _ ih => exact SaturatedConvOver.vcompCongrRight cellAlpha ih
  | whiskerLeftCongr oneCell _ ih => exact SaturatedConvOver.whiskerLeftCongr oneCell ih
  | whiskerRightCongr oneCell _ ih => exact SaturatedConvOver.whiskerRightCongr oneCell ih
  | refl cell => exact SaturatedConvOver.refl cell
  | symm _ ih => exact SaturatedConvOver.symm ih
  | trans _ _ ihLeft ihRight => exact SaturatedConvOver.trans ihLeft ihRight

/-- The bespoke walker absorbs the generic congruence at `FrobeniusSpecialLawRel` — the backward-direction
witness, packaged for the universal property `recInto`. -/
def frobeniusSpecialWalkerIsCongruence :
    IsSaturatedCongruence frobeniusModeSignature FrobeniusSpecialLawRel
      (fun cellAlpha cellBeta => FrobeniusSpecialWalkerConv cellAlpha cellBeta) where
  ofFull full := FrobeniusSpecialWalkerConv.ofFull full
  ofRelation row :=
    match row with
    | FrobeniusSpecialLawRel.special => FrobeniusSpecialWalkerConv.special
  vcompCongrLeft {_ _ _ _ _ _ _ cellBeta} ih := FrobeniusSpecialWalkerConv.vcompCongrLeft cellBeta ih
  vcompCongrRight {_ _ _ _ _ cellAlpha _ _} ih := FrobeniusSpecialWalkerConv.vcompCongrRight cellAlpha ih
  whiskerLeftCongr {_ _ _ oneCell _ _ _ _} ih := FrobeniusSpecialWalkerConv.whiskerLeftCongr oneCell ih
  whiskerRightCongr {_ _ _ _ _ oneCell _ _} ih := FrobeniusSpecialWalkerConv.whiskerRightCongr oneCell ih
  refl cell := FrobeniusSpecialWalkerConv.refl cell
  symm ih := FrobeniusSpecialWalkerConv.symm ih
  trans ihLeft ihRight := FrobeniusSpecialWalkerConv.trans ihLeft ihRight

/-- **Backward** — the generic at `FrobeniusSpecialLawRel` maps back into the bespoke walker, via the universal
property `recInto` with the walker congruence. -/
theorem generic_to_frobeniusSpecialWalker {sourceMode targetMode : FrobeniusMode}
    {sourcePath targetPath : ModalityPath frobeniusGraph sourceMode targetMode}
    {cellAlpha cellBeta : RawTwoCellExpr frobeniusModeSignature sourcePath targetPath}
    (conv : SaturatedConvOver frobeniusModeSignature FrobeniusSpecialLawRel cellAlpha cellBeta) :
    FrobeniusSpecialWalkerConv cellAlpha cellBeta :=
  SaturatedConvOver.recInto frobeniusSpecialWalkerIsCongruence conv

/-- ★ **The migration bridge (the certificate)** — the bespoke walking-special-Frobenius conv IS the generic
saturated conv at its one-row law relation.  The retirement is behaviour-preserving: every decision or soundness
fact transports across this iso with zero re-proof (the regression verdict). -/
theorem frobeniusSpecialWalker_iff_generic {sourceMode targetMode : FrobeniusMode}
    {sourcePath targetPath : ModalityPath frobeniusGraph sourceMode targetMode}
    (cellAlpha cellBeta : RawTwoCellExpr frobeniusModeSignature sourcePath targetPath) :
    FrobeniusSpecialWalkerConv cellAlpha cellBeta
      ↔ SaturatedConvOver frobeniusModeSignature FrobeniusSpecialLawRel cellAlpha cellBeta :=
  ⟨frobeniusSpecialWalker_to_generic, generic_to_frobeniusSpecialWalker⟩

/-- Regression smoke: the special law itself transports across the bridge — the bespoke witness maps to the
generic `ofRelation` and back. -/
theorem frobeniusSpecialWalker_special_transports :
    SaturatedConvOver frobeniusModeSignature FrobeniusSpecialLawRel frobeniusSpecialCell frobeniusIdTCell :=
  (frobeniusSpecialWalker_iff_generic frobeniusSpecialCell frobeniusIdTCell).mp
    FrobeniusSpecialWalkerConv.special

/-! ## Honesty markers -/

/-- ★ **Honesty marker — the smallest-walker migration playbook SHIPS (POLY-TAB r0, T4).**  The one-law bespoke
walker (`FrobeniusSpecialWalkerConv`) is proved logically identical to the generic `SaturatedConvOver` at its
one-row law relation (`frobeniusSpecialWalker_iff_generic`), via the reusable forward-fold + backward-`recInto`
recipe (the monad exemplar `monadSaturated_iff_generic` at minimal law count).  The regression verdict: the iso
transports every decision / soundness fact with zero re-proof (`frobeniusSpecialWalker_special_transports`).
`= true`. -/
def fxTab_hasSmallestWalkerMigration : Bool := true

/-- ★ **Honesty marker — the born-generic migration verdict.**  The `Table/FrobeniusSeed.lean` Frobenius spider is
a NEW walker BORN on the generic `SaturatedConvOver` carrier (a `CellRel` of law rows) with ZERO bespoke
inductive, so its migration to the generic is the identity — there is nothing to bridge.  Combined with the
retirement bridge above (for a walker that DID ship a bespoke inductive), this is the two-sided migration story:
new walkers are born generic; existing bespoke walkers retire via the one-row iff.  `= true`. -/
def fxTab_hasBornGenericWalker : Bool := true

end FX1Poly.Polygraph
