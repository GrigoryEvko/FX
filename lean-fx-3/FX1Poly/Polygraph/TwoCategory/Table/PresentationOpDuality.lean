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

/-! ## Honesty marker -/

/-- ★ **Honesty marker — the `op` INVOLUTION on the presentation carrier SHIPS (WALKER-DUALITY B1).**  The
signature involution (`opSignature`, DEFINITIONAL involutivity), the free-2-cell involution (`opCell`, the cell
reversal `RawTwoCellExpr` lacked, with structural `opCell_involutive`), and the law-relation involution
(`opCellRel` with the row bridge `opCellRel_ofCells`) are all zero-axiom and STRUCTURAL.  This is the carrier a
co-monad / idempotent-comonad / co-KZ presentation is the `op` of its shipped dual; the Conv-iff decision
transport and the three decided-dual instances are the follow-on bricks.  `= true`. -/
def fxTab_hasOpInvolution : Bool := true

end FX1Poly.Polygraph.Table
