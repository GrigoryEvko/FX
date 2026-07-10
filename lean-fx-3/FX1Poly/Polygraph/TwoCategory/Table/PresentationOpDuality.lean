import FX1Poly.Polygraph.TwoCategory.Amalgam.SaturatedOver

/-! # Polygraph/TwoCategory/Table/PresentationOpDuality — the co- direction: the `op` involution on the
presentation carrier (#2024, WALKER-DUALITY)

Every shipped decided walker rides the generic saturated carrier `SaturatedConvOver signature baseRel`
(`Amalgam/SaturatedOver.lean`) over a `ModeSignature` and a law relation `CellRel`.  This file builds the
2-cell DUALITY (`op`) on that carrier: the operation that reverses 2-cells (a `t ⇒ id` counit is the `op` of a
`id ⇒ t` unit), leaving the 0- and 1-cells (the mode graph) untouched.  It is the substrate a co-monad / co-KZ
/ idempotent-comonad presentation is the `op` of its shipped dual.

## What ships here (B1 — the op involution + its involutivity)

  * **`opSignature`** — `op` on a `ModeSignature`: SAME graph (op reverses 2-cells, not 1-cells), the 2-cell
    family transposed (`opSignature sig |>.twoCell a b = sig.twoCell b a`).  `op` is a DEFINITIONAL involution
    on signatures (`opSignature_involutive : opSignature (opSignature sig) = sig` is `rfl` — structure + function
    eta fire through the indexed 2-cell family).
  * **`opCell`** — `op` on a free 2-cell `RawTwoCellExpr sig f g → RawTwoCellExpr (opSignature sig) g f`: the
    boundary swaps (a `f ⇒ g` becomes a `g ⇒ f`), the vertical composite ORDER-FLIPS (`op (α ⊟ β) = op β ⊟ op α`),
    the two whiskerings COMMUTE with `op`, generators and identities are payload-preserved.  This is the cell
    involution `RawTwoCellExpr` lacked (the `op`/`reverse`/`converse` hits elsewhere are unrelated chain /
    Brauer / marker operations); it is BUILT here.
  * **`opCell_involutive`** — `op (op cell) = cell` (structural induction; the two order-flips of `op` on `vcomp`
    cancel).  Well-typed BECAUSE `opSignature_involutive` is definitional.
  * **`opCellRel`** — `op` on a law relation `CellRel sig → CellRel (opSignature sig)`, pulling each row back
    through `opCell`.  `opCellRel_ofCells` : a row of `baseRel a b` reflects into `opCellRel baseRel (opCell a)
    (opCell b)` (and back), the bridge the row-transport of the duality theorem rides.

The DECISION transport (Conv-iff under `op` ⇒ `Decidable` transport) and the three instances (walking comonad /
idempotent comonad / co-KZ, each decided by the `op` of the shipped dual through the iff) are the follow-on
bricks; this file ships the carrier-level `op` and its involutivity, walker-agnostic.

Raw Lean 4 + Init; STRUCTURAL only; ASCII-only.  Per-declaration `#assert_no_axioms` gated in the audit twin. -/

namespace FX1Poly.Polygraph.Table

open FX1Poly.Polygraph
open FX1Poly.Polygraph.Amalgam

/-! ## The `op` involution on signatures -/

/-- ★ **`op` on a mode signature** — reverse the 2-cells, keep the 0- and 1-cells.  The graph is UNTOUCHED (op does
not reverse 1-cells, that is the separate `co` axis); the generating-2-cell family is transposed, so a generator
`sig.twoCell sourcePath targetPath` becomes a generator `(opSignature sig).twoCell targetPath sourcePath`.  The
walking comonad's counit / comult are exactly the walking monad's unit / mult READ BACKWARDS through this. -/
def opSignature (sig : ModeSignature) : ModeSignature where
  graph := sig.graph
  twoCell := fun a b => sig.twoCell b a

/-- ★ **`op` is a DEFINITIONAL involution on signatures** — `opSignature (opSignature sig) = sig` by `rfl`.
Structure eta plus function eta fire through the transposed 2-cell family (the double transpose is the identity
family on the nose). -/
theorem opSignature_involutive (sig : ModeSignature) :
    opSignature (opSignature sig) = sig := rfl

/-! ## The `op` involution on free 2-cells -/

/-- ★ **`op` on a free 2-cell** — the cell involution `RawTwoCellExpr` lacked.  Boundaries swap (`f ⇒ g` maps to
`g ⇒ f`); the vertical composite ORDER-FLIPS (`op (α ⊟ β) = op β ⊟ op α`, the contravariance of reversal); the
two whiskerings COMMUTE with `op` (whiskering is a bimodule action, op-stable); generators and identities keep
their payload (a generator becomes a generator of the transposed family, definitionally). -/
def opCell {sig : ModeSignature} :
    {sourceMode targetMode : sig.graph.Mode} →
    {sourcePath targetPath : ModalityPath sig.graph sourceMode targetMode} →
    RawTwoCellExpr sig sourcePath targetPath →
    RawTwoCellExpr (opSignature sig) targetPath sourcePath
  | _, _, _, _, .gen twoCellGen => RawTwoCellExpr.gen (signature := opSignature sig) twoCellGen
  | _, _, _, _, .id path => RawTwoCellExpr.id (signature := opSignature sig) path
  | _, _, _, _, .vcomp cellAlpha cellBeta =>
      RawTwoCellExpr.vcomp (opCell cellBeta) (opCell cellAlpha)
  | _, _, _, _, .whiskerLeft oneCell cellBeta =>
      RawTwoCellExpr.whiskerLeft (signature := opSignature sig) oneCell (opCell cellBeta)
  | _, _, _, _, .whiskerRight oneCell cellAlpha =>
      RawTwoCellExpr.whiskerRight (signature := opSignature sig) oneCell (opCell cellAlpha)

/-- ★ **`op` is an involution on free 2-cells** — `op (op cell) = cell`, by structural induction (the two
`vcomp` order-flips cancel; the whiskerings pass through; generators / identities are fixed).  Well-typed
because `opSignature_involutive` holds definitionally, so `op (op cell)` already lands at `sig`. -/
theorem opCell_involutive {sig : ModeSignature}
    {sourceMode targetMode : sig.graph.Mode}
    {sourcePath targetPath : ModalityPath sig.graph sourceMode targetMode}
    (cell : RawTwoCellExpr sig sourcePath targetPath) :
    opCell (opCell cell) = cell := by
  induction cell with
  | gen twoCellGen => rfl
  | id path => rfl
  | vcomp cellAlpha cellBeta ihAlpha ihBeta => dsimp only [opCell]; congr 1
  | whiskerLeft oneCell cellBeta ih => dsimp only [opCell]; congr 1
  | whiskerRight oneCell cellAlpha ih => dsimp only [opCell]; congr 1

/-! ## The `op` involution on law relations -/

/-- ★ **`op` on a law relation** — transport a `CellRel sig` to a `CellRel (opSignature sig)` by pulling each
argument back through `opCell`.  A dual presentation's law relation is `opCellRel` of its shipped dual's: the
comonad's three co-laws are `opCellRel MonadLawRel`, the monad's three laws read as 2-cell reversals. -/
def opCellRel {sig : ModeSignature} (baseRel : CellRel sig) : CellRel (opSignature sig) :=
  fun cellX cellY => baseRel (opCell cellX) (opCell cellY)

/-- The row bridge: a base row `baseRel a b` reflects EXACTLY into `opCellRel baseRel (opCell a) (opCell b)`
(the `opCell` boundary-swapped images), and back — the two are logically equal, by the `op` involutivity on the
two cells.  This is the `ofRelation` transport leg of the duality theorem. -/
theorem opCellRel_ofCells {sig : ModeSignature} (baseRel : CellRel sig)
    {sourceMode targetMode : sig.graph.Mode}
    {sourcePath targetPath : ModalityPath sig.graph sourceMode targetMode}
    (cellA cellB : RawTwoCellExpr sig sourcePath targetPath) :
    opCellRel baseRel (opCell cellA) (opCell cellB) ↔ baseRel cellA cellB := by
  unfold opCellRel
  rw [opCell_involutive, opCell_involutive]

/-! ## The 2-cell coherence transported through `op` — the Godement commute

The single genuine coherence `op` must respect is the middle-four INTERCHANGE (Godement) law: `op` sends the
upper-right Godement (`hcomp`) to the upper-LEFT ordering, and the two are convertible.  Everything else in the
completed convertibility (`TwoCellConvFull`) transports either by the same constructor or a left/right swap. -/

/-- ★ The **Godement commute**: the two orderings of independent whiskers of `cellU` (over `modeA -> modeB`) and
`cellV` (over `modeB -> modeC`) are convertible — `(oneCellP <| cellV) . (cellU |> oneCellS)` (upper-left) equals
`(cellU |> oneCellR) . (oneCellQ <| cellV)` (upper-right).  Derived from the shipped middle-four
`TwoCellStep.interchange` instantiated with identities, plus cast-FREE `vcompId` / `whiskerId` cleanups. -/
theorem godementCommute {sig : ModeSignature}
    {modeA modeB modeC : sig.graph.Mode}
    {oneCellP oneCellQ : ModalityPath sig.graph modeA modeB}
    {oneCellR oneCellS : ModalityPath sig.graph modeB modeC}
    (cellU : RawTwoCellExpr sig oneCellP oneCellQ)
    (cellV : RawTwoCellExpr sig oneCellR oneCellS) :
    TwoCellConvFull sig
      (RawTwoCellExpr.vcomp (RawTwoCellExpr.whiskerLeft oneCellP cellV)
        (RawTwoCellExpr.whiskerRight oneCellS cellU))
      (RawTwoCellExpr.vcomp (RawTwoCellExpr.whiskerRight oneCellR cellU)
        (RawTwoCellExpr.whiskerLeft oneCellQ cellV)) := by
  have stepInterchange :
      TwoCellConvFull sig
        (RawTwoCellExpr.hcomp
          (RawTwoCellExpr.vcomp (RawTwoCellExpr.id oneCellP) cellU)
          (RawTwoCellExpr.vcomp cellV (RawTwoCellExpr.id oneCellS)))
        (RawTwoCellExpr.vcomp
          (RawTwoCellExpr.hcomp (RawTwoCellExpr.id oneCellP) cellV)
          (RawTwoCellExpr.hcomp cellU (RawTwoCellExpr.id oneCellS))) :=
    TwoCellConvFull.ofConv (TwoCellConv.ofStep
      (TwoCellStep.interchange (RawTwoCellExpr.id oneCellP) cellU cellV (RawTwoCellExpr.id oneCellS)))
  have cleanupLeft :
      TwoCellConvFull sig
        (RawTwoCellExpr.hcomp
          (RawTwoCellExpr.vcomp (RawTwoCellExpr.id oneCellP) cellU)
          (RawTwoCellExpr.vcomp cellV (RawTwoCellExpr.id oneCellS)))
        (RawTwoCellExpr.vcomp (RawTwoCellExpr.whiskerRight oneCellR cellU)
          (RawTwoCellExpr.whiskerLeft oneCellQ cellV)) := by
    apply TwoCellConvFull.trans
      (TwoCellConvFull.vcompCongrLeft _
        (TwoCellConvFull.whiskerRightCongr oneCellR
          (TwoCellConvFull.ofConv (TwoCellConv.ofStep (TwoCellStep.vcompIdLeft cellU)))))
    exact TwoCellConvFull.vcompCongrRight _
      (TwoCellConvFull.whiskerLeftCongr oneCellQ
        (TwoCellConvFull.ofConv (TwoCellConv.ofStep (TwoCellStep.vcompIdRight cellV))))
  have cleanupRight :
      TwoCellConvFull sig
        (RawTwoCellExpr.vcomp
          (RawTwoCellExpr.hcomp (RawTwoCellExpr.id oneCellP) cellV)
          (RawTwoCellExpr.hcomp cellU (RawTwoCellExpr.id oneCellS)))
        (RawTwoCellExpr.vcomp (RawTwoCellExpr.whiskerLeft oneCellP cellV)
          (RawTwoCellExpr.whiskerRight oneCellS cellU)) := by
    apply TwoCellConvFull.trans
      (TwoCellConvFull.vcompCongrLeft _
        (TwoCellConvFull.trans
          (TwoCellConvFull.vcompCongrLeft _
            (TwoCellConvFull.ofConv (TwoCellConv.ofStep (TwoCellStep.whiskerRightId oneCellP oneCellR))))
          (TwoCellConvFull.ofConv (TwoCellConv.ofStep
            (TwoCellStep.vcompIdLeft (RawTwoCellExpr.whiskerLeft oneCellP cellV))))))
    exact TwoCellConvFull.vcompCongrRight _
      (TwoCellConvFull.trans
        (TwoCellConvFull.vcompCongrRight _
          (TwoCellConvFull.ofConv (TwoCellConv.ofStep (TwoCellStep.whiskerLeftId oneCellQ oneCellS))))
        (TwoCellConvFull.ofConv (TwoCellConv.ofStep
          (TwoCellStep.vcompIdRight (RawTwoCellExpr.whiskerRight oneCellS cellU)))))
  exact TwoCellConvFull.trans (TwoCellConvFull.symm cleanupRight)
    (TwoCellConvFull.trans (TwoCellConvFull.symm stepInterchange) cleanupLeft)

/-- `op` commutes (up to conv) with horizontal composition: `op` sends the upper-right Godement `hcomp` to the
upper-left ordering, which the Godement commute reconciles. -/
theorem opCell_hcomp_conv {sig : ModeSignature}
    {modeA modeB modeC : sig.graph.Mode}
    {oneCellFDom oneCellFCod : ModalityPath sig.graph modeA modeB}
    {oneCellGDom oneCellGCod : ModalityPath sig.graph modeB modeC}
    (cellX : RawTwoCellExpr sig oneCellFDom oneCellFCod)
    (cellY : RawTwoCellExpr sig oneCellGDom oneCellGCod) :
    TwoCellConvFull (opSignature sig)
      (opCell (RawTwoCellExpr.hcomp cellX cellY))
      (RawTwoCellExpr.hcomp (opCell cellX) (opCell cellY)) :=
  godementCommute (opCell cellX) (opCell cellY)

/-- `op` commutes with the boundary cast (the boundaries swap) — the `Eq.rec` transport commutation the
whisker-functoriality cases of the completed-convertibility transport ride on. -/
theorem opCell_castBoundary {sig : ModeSignature} {sourceMode targetMode : sig.graph.Mode}
    {sourcePath sourcePath' targetPath targetPath' : ModalityPath sig.graph sourceMode targetMode}
    (hsource : sourcePath = sourcePath') (htarget : targetPath = targetPath')
    (cell : RawTwoCellExpr sig sourcePath targetPath) :
    opCell (RawTwoCellExpr.castBoundary hsource htarget cell)
      = RawTwoCellExpr.castBoundary (signature := opSignature sig) htarget hsource (opCell cell) := by
  cases hsource; cases htarget; rfl

/-! ## The completed-convertibility transport under `op` -/

/-- Transport a single 3-cell rewrite through `op` into the completed convertibility of the `op` signature.
Eleven cases are same-ctor or a left/right swap; the `interchange` case is the Godement commute (`opCell_hcomp_conv`)
plus the `op` signature's own interchange step. -/
theorem opStep_toFull {sig : ModeSignature}
    {sourceMode targetMode : sig.graph.Mode}
    {sourcePath targetPath : ModalityPath sig.graph sourceMode targetMode}
    {cellA cellB : RawTwoCellExpr sig sourcePath targetPath}
    (step : TwoCellStep sig cellA cellB) :
    TwoCellConvFull (opSignature sig) (opCell cellA) (opCell cellB) := by
  induction step with
  | vcompIdLeft cellAlpha =>
      exact TwoCellConvFull.ofConv (TwoCellConv.ofStep (TwoCellStep.vcompIdRight (opCell cellAlpha)))
  | vcompIdRight cellAlpha =>
      exact TwoCellConvFull.ofConv (TwoCellConv.ofStep (TwoCellStep.vcompIdLeft (opCell cellAlpha)))
  | vcompAssoc cellAlpha cellBeta cellGamma =>
      exact TwoCellConvFull.ofConv (TwoCellConv.symm (TwoCellConv.ofStep
        (TwoCellStep.vcompAssoc (opCell cellGamma) (opCell cellBeta) (opCell cellAlpha))))
  | whiskerLeftId oneCell path =>
      exact TwoCellConvFull.ofConv (TwoCellConv.ofStep
        (TwoCellStep.whiskerLeftId (signature := opSignature sig) oneCell path))
  | whiskerRightId path oneCell =>
      exact TwoCellConvFull.ofConv (TwoCellConv.ofStep
        (TwoCellStep.whiskerRightId (signature := opSignature sig) path oneCell))
  | whiskerLeftVcomp oneCell cellBeta cellGamma =>
      exact TwoCellConvFull.ofConv (TwoCellConv.ofStep
        (TwoCellStep.whiskerLeftVcomp (signature := opSignature sig) oneCell (opCell cellGamma) (opCell cellBeta)))
  | whiskerRightVcomp oneCell cellAlpha cellBeta =>
      exact TwoCellConvFull.ofConv (TwoCellConv.ofStep
        (TwoCellStep.whiskerRightVcomp (signature := opSignature sig) oneCell (opCell cellBeta) (opCell cellAlpha)))
  | vcompCongrLeft cellBeta _ ih =>
      exact TwoCellConvFull.vcompCongrRight (opCell cellBeta) ih
  | vcompCongrRight cellAlpha _ ih =>
      exact TwoCellConvFull.vcompCongrLeft (opCell cellAlpha) ih
  | whiskerLeftCongr oneCell _ ih =>
      exact TwoCellConvFull.whiskerLeftCongr (signature := opSignature sig) oneCell ih
  | whiskerRightCongr oneCell _ ih =>
      exact TwoCellConvFull.whiskerRightCongr (signature := opSignature sig) oneCell ih
  | interchange cellAlpha cellAlphaUpper cellBeta cellBetaUpper =>
      refine TwoCellConvFull.trans (opCell_hcomp_conv _ _) ?_
      refine TwoCellConvFull.trans
        (TwoCellConvFull.ofConv (TwoCellConv.ofStep
          (TwoCellStep.interchange (opCell cellAlphaUpper) (opCell cellAlpha)
            (opCell cellBetaUpper) (opCell cellBeta)))) ?_
      exact TwoCellConvFull.trans
        (TwoCellConvFull.vcompCongrLeft _
          (TwoCellConvFull.symm (opCell_hcomp_conv cellAlphaUpper cellBetaUpper)))
        (TwoCellConvFull.vcompCongrRight _
          (TwoCellConvFull.symm (opCell_hcomp_conv cellAlpha cellBeta)))

/-- Transport a convertibility through `op` (structural closure: `ofStep` through `opStep_toFull`). -/
theorem opConv_toFull {sig : ModeSignature}
    {sourceMode targetMode : sig.graph.Mode}
    {sourcePath targetPath : ModalityPath sig.graph sourceMode targetMode}
    {cellA cellB : RawTwoCellExpr sig sourcePath targetPath}
    (conv : TwoCellConv sig cellA cellB) :
    TwoCellConvFull (opSignature sig) (opCell cellA) (opCell cellB) := by
  induction conv with
  | ofStep step => exact opStep_toFull step
  | refl cell => exact TwoCellConvFull.refl (opCell cell)
  | symm _ ih => exact TwoCellConvFull.symm ih
  | trans _ _ ihLeft ihRight => exact TwoCellConvFull.trans ihLeft ihRight

/-- ★ Transport the COMPLETED free-strict-2-category convertibility through `op`.  The four whisker-functoriality
cases map to the same ctor via `opCell_castBoundary`; the two vcomp congruences SWAP left/right; the whiskerings
and `refl`/`symm`/`trans` map to the same ctor; `ofConv` recurses through `opConv_toFull`. -/
theorem opConvFull {sig : ModeSignature}
    {sourceMode targetMode : sig.graph.Mode}
    {sourcePath targetPath : ModalityPath sig.graph sourceMode targetMode}
    {cellA cellB : RawTwoCellExpr sig sourcePath targetPath}
    (convFull : TwoCellConvFull sig cellA cellB) :
    TwoCellConvFull (opSignature sig) (opCell cellA) (opCell cellB) := by
  induction convFull with
  | ofConv conv => exact opConv_toFull conv
  | whiskerLeftUnit body => exact TwoCellConvFull.whiskerLeftUnit (opCell body)
  | whiskerRightUnit body =>
      rw [opCell_castBoundary]; exact TwoCellConvFull.whiskerRightUnit (opCell body)
  | whiskerLeftComp oneCellOuter oneCellInner body =>
      rw [opCell_castBoundary]
      exact TwoCellConvFull.whiskerLeftComp (signature := opSignature sig) oneCellOuter oneCellInner (opCell body)
  | whiskerRightComp oneCellInner oneCellOuter body =>
      rw [opCell_castBoundary]
      exact TwoCellConvFull.whiskerRightComp (signature := opSignature sig) oneCellInner oneCellOuter (opCell body)
  | whiskerExchange leftWhisker rightWhisker body =>
      rw [opCell_castBoundary]
      exact TwoCellConvFull.whiskerExchange (signature := opSignature sig) leftWhisker rightWhisker (opCell body)
  | vcompCongrLeft cellBeta _ ih => exact TwoCellConvFull.vcompCongrRight (opCell cellBeta) ih
  | vcompCongrRight cellAlpha _ ih => exact TwoCellConvFull.vcompCongrLeft (opCell cellAlpha) ih
  | whiskerLeftCongr oneCell _ ih => exact TwoCellConvFull.whiskerLeftCongr (signature := opSignature sig) oneCell ih
  | whiskerRightCongr oneCell _ ih => exact TwoCellConvFull.whiskerRightCongr (signature := opSignature sig) oneCell ih
  | refl cell => exact TwoCellConvFull.refl (opCell cell)
  | symm _ ih => exact TwoCellConvFull.symm ih
  | trans _ _ ihLeft ihRight => exact TwoCellConvFull.trans ihLeft ihRight

/-! ## The saturated-convertibility transport + the Decidable transport -/

/-- The forward congruence: the base saturated congruence maps into the `op`'d saturated conv (via the universal
property `recInto`).  The two vcomp congruences SWAP; `ofRelation` rides the row bridge; `ofFull` rides
`opConvFull`. -/
def opDualityForwardCongruence {sig : ModeSignature} (baseRel : CellRel sig) :
    IsSaturatedCongruence sig baseRel
      (fun cellA cellB => SaturatedConvOver (opSignature sig) (opCellRel baseRel)
        (opCell cellA) (opCell cellB)) where
  ofFull full := SaturatedConvOver.ofFull (opConvFull full)
  ofRelation row := SaturatedConvOver.ofRelation ((opCellRel_ofCells baseRel _ _).mpr row)
  vcompCongrLeft {_ _ _ _ _ _ _ cellBeta} ih := SaturatedConvOver.vcompCongrRight (opCell cellBeta) ih
  vcompCongrRight {_ _ _ _ _ cellAlpha _ _} ih := SaturatedConvOver.vcompCongrLeft (opCell cellAlpha) ih
  whiskerLeftCongr {_ _ _ oneCell _ _ _ _} ih := SaturatedConvOver.whiskerLeftCongr (signature := opSignature sig) oneCell ih
  whiskerRightCongr {_ _ _ _ _ oneCell _ _} ih := SaturatedConvOver.whiskerRightCongr (signature := opSignature sig) oneCell ih
  refl cell := SaturatedConvOver.refl (opCell cell)
  symm ih := SaturatedConvOver.symm ih
  trans ihLeft ihRight := SaturatedConvOver.trans ihLeft ihRight

/-- ★ **Forward duality transport** — the base saturated conv maps into the `op`'d saturated conv over
`opCellRel baseRel`. -/
theorem forwardOpDuality {sig : ModeSignature} {baseRel : CellRel sig}
    {sourceMode targetMode : sig.graph.Mode}
    {sourcePath targetPath : ModalityPath sig.graph sourceMode targetMode}
    {cellA cellB : RawTwoCellExpr sig sourcePath targetPath}
    (conv : SaturatedConvOver sig baseRel cellA cellB) :
    SaturatedConvOver (opSignature sig) (opCellRel baseRel) (opCell cellA) (opCell cellB) :=
  SaturatedConvOver.recInto (opDualityForwardCongruence baseRel) conv

/-- The backward congruence: the `op`'d saturated conv maps back into the base saturated congruence (via
`recInto`).  `ofRelation` is DEFINITIONAL here (`opCellRel baseRel x y` unfolds to `baseRel (opCell x)(opCell y)`);
`ofFull` rides `opConvFull` at the `op` signature (landing at `sig` since `op` is a definitional involution). -/
def opDualityBackwardCongruence {sig : ModeSignature} (baseRel : CellRel sig) :
    IsSaturatedCongruence (opSignature sig) (opCellRel baseRel)
      (fun cellX cellY => SaturatedConvOver sig baseRel (opCell cellX) (opCell cellY)) where
  ofFull full := SaturatedConvOver.ofFull (opConvFull full)
  ofRelation row := SaturatedConvOver.ofRelation row
  vcompCongrLeft {_ _ _ _ _ _ _ cellBeta} ih := SaturatedConvOver.vcompCongrRight (opCell cellBeta) ih
  vcompCongrRight {_ _ _ _ _ cellAlpha _ _} ih := SaturatedConvOver.vcompCongrLeft (opCell cellAlpha) ih
  whiskerLeftCongr {_ _ _ oneCell _ _ _ _} ih := SaturatedConvOver.whiskerLeftCongr (signature := sig) oneCell ih
  whiskerRightCongr {_ _ _ _ _ oneCell _ _} ih := SaturatedConvOver.whiskerRightCongr (signature := sig) oneCell ih
  refl cell := SaturatedConvOver.refl (opCell cell)
  symm ih := SaturatedConvOver.symm ih
  trans ihLeft ihRight := SaturatedConvOver.trans ihLeft ihRight

/-- ★ **Backward duality transport** — the `op`'d saturated conv maps back to the base saturated conv on the
`op`'d cells. -/
theorem backwardOpDuality {sig : ModeSignature} {baseRel : CellRel sig}
    {sourceMode targetMode : sig.graph.Mode}
    {sourcePath targetPath : ModalityPath sig.graph sourceMode targetMode}
    {cellX cellY : RawTwoCellExpr (opSignature sig) sourcePath targetPath}
    (conv : SaturatedConvOver (opSignature sig) (opCellRel baseRel) cellX cellY) :
    SaturatedConvOver sig baseRel (opCell cellX) (opCell cellY) :=
  SaturatedConvOver.recInto (opDualityBackwardCongruence baseRel) conv

/-- ★ **The duality iff (decision-oriented)** — the base saturated conv on the `op`'d cells is logically the
`op`'d saturated conv.  Backward is `backwardOpDuality` directly; forward is `forwardOpDuality` closed by the
`opCell` involutivity. -/
theorem opDuality_iff {sig : ModeSignature} (baseRel : CellRel sig)
    {sourceMode targetMode : sig.graph.Mode}
    {sourcePath targetPath : ModalityPath sig.graph sourceMode targetMode}
    (cellX cellY : RawTwoCellExpr (opSignature sig) sourcePath targetPath) :
    SaturatedConvOver sig baseRel (opCell cellX) (opCell cellY)
      ↔ SaturatedConvOver (opSignature sig) (opCellRel baseRel) cellX cellY := by
  constructor
  · intro convBase
    have transported := forwardOpDuality convBase
    have involuteX : opCell (opCell cellX) = cellX := opCell_involutive cellX
    have involuteY : opCell (opCell cellY) = cellY := opCell_involutive cellY
    exact involuteX ▸ involuteY ▸ transported
  · intro convOp
    exact backwardOpDuality convOp

/-- ★ **The generic, walker-agnostic Decidable transport** — a decider for the base saturated conv yields a
decider for the `op`'d saturated conv (`opCellRel baseRel`) by deciding the base conv on the `op`'d cells and
routing both verdicts through `opDuality_iff`.  This is the machine every decided-dual walker (comonad,
idempotent comonad, co-KZ) instantiates: the SHIPPED dual's decider decides the dual through the iff. -/
def decideSaturatedConvUnderOp {sig : ModeSignature} {baseRel : CellRel sig}
    (decideBase : DecidableSaturatedConvForRel sig baseRel) :
    DecidableSaturatedConvForRel (opSignature sig) (opCellRel baseRel) :=
  fun cellX cellY =>
    match decideBase (opCell cellX) (opCell cellY) with
    | isTrue convBase => isTrue ((opDuality_iff baseRel cellX cellY).mp convBase)
    | isFalse notConvBase => isFalse (fun convOp => notConvBase ((opDuality_iff baseRel cellX cellY).mpr convOp))

/-! ## Honesty marker -/

/-- ★ **Honesty marker — the `op` INVOLUTION on the presentation carrier SHIPS (WALKER-DUALITY B1).**  The
signature involution (`opSignature`, DEFINITIONAL involutivity), the free-2-cell involution (`opCell`, the cell
reversal `RawTwoCellExpr` lacked, with structural `opCell_involutive`), and the law-relation involution
(`opCellRel` with the row bridge `opCellRel_ofCells`) are all zero-axiom and STRUCTURAL.  This is the carrier a
co-monad / idempotent-comonad / co-KZ presentation is the `op` of its shipped dual; the Conv-iff decision
transport and the three decided-dual instances are the follow-on bricks.  `= true`. -/
def fxTab_hasOpInvolution : Bool := true

/-- ★ **Honesty marker — the Conv-iff DECISION TRANSPORT under `op` SHIPS (WALKER-DUALITY B2).**  The completed
free-strict-2-category convertibility transports through `op` constructor-by-constructor (`opConvFull`), the one
genuine coherence being the middle-four INTERCHANGE, discharged by the Godement commute (`godementCommute`, from
the shipped `TwoCellStep.interchange` + cast-free identity cleanups).  Lifted to `SaturatedConvOver` via the
universal property (`forwardOpDuality` / `backwardOpDuality` through `recInto`), giving the walker-agnostic iff
(`opDuality_iff`) and hence the generic `Decidable` transport (`decideSaturatedConvUnderOp`): any shipped decider
decides the `op`-dual through the iff.  Zero-axiom, STRUCTURAL.  `= true`. -/
def fxTab_hasOpDecisionTransport : Bool := true

end FX1Poly.Polygraph.Table
