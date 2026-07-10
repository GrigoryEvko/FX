import FX1Poly.Polygraph.Computad.MonadSeed
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.Model

/-! # WalkingMonad/MonadSaturatedDeltaReps — the bespoke-free DEEP saturated-Δ representatives bridge

MONAD-R7 r4 (the deep-stratum relocation) collects the pure-bespoke saturated-Δ chain's conv-FREE lower stratum
into this bridge, so the SURVIVOR files (the idempotent reps, the Gen twins) can consume the walking-monad skeleton
(the law-composite cells, the monotone-map engine, the canonical words) WITHOUT importing the bespoke
`MonadSaturatedTwoCellConv` inductive.  Everything here is `RawTwoCellExpr` / `List Nat` / `Nat` combinatorics over
the already-bespoke-free monad seed (`Computad/MonadSeed`) and free-2-cell substrate (`FreeTwoCell/Model`); the
bridge imports NO file carrying the saturated-convertibility inductive, so a survivor importing only this bridge is
provably conv-decoupled.  This is the DEEP companion to the shallow `MonadSaturatedSkeletonReps` (the embed
stratum); the two together carry the whole conv-FREE skeleton the r3 layer banked.

## What this file ships (relocated VERBATIM from the chain, names / namespace / meaning preserved)

  * the unit / multiplication free 2-cells (`monadUnitTwoCell` / `monadMulTwoCell`) and the three law composites
    (`monadLeftUnitCell` / `monadRightUnitCell` / `monadAssocLeftCell` / `monadAssocRightCell` / `monadIdTCell`),
    relocated from `MonadSaturatedConv` — the RHS/LHS representatives the saturated relation's law constructors
    quote (`MonadSaturatedConv` now imports this bridge for exactly these, single home, no duplication).

Raw Lean 4 + Init; `propext`/`Quot.sound`/`Classical`/`sorry`/`native_decide`/`omega`-free (RawTwoCellExpr
constructors, no proposition).  Per-declaration `#assert_no_axioms` gated in the audit twin. -/

namespace FX1Poly.Polygraph

/-! ## The unit / multiplication as free 2-cells + the three law composites -/

/-- The seed's UNIT embeds as a free 2-cell `id_point ⇒ t`. -/
def monadUnitTwoCell :
    RawTwoCellExpr monadModeSignature (ModalityPath.nil (graph := monadGraph) MonadMode.point) monadT :=
  RawTwoCellExpr.gen MonadTwoCell.eta

/-- The seed's MULTIPLICATION embeds as a free 2-cell `t·t ⇒ t`. -/
def monadMulTwoCell :
    RawTwoCellExpr monadModeSignature monadTThenT monadT :=
  RawTwoCellExpr.gen MonadTwoCell.mu

/-- The **left-unit composite** `mu ∘ (eta ▷ t)` — the unit whiskered on the right by `t`, then the
multiplication.  A 2-cell `t ⇒ t`; the left-unit law asserts it is `id_t`. -/
def monadLeftUnitCell : RawTwoCellExpr monadModeSignature monadT monadT :=
  RawTwoCellExpr.vcomp
    (RawTwoCellExpr.whiskerRight (signature := monadModeSignature) monadT monadUnitTwoCell)
    monadMulTwoCell

/-- The **right-unit composite** `mu ∘ (t ◁ eta)` — the unit whiskered on the left by `t`, then the
multiplication.  A 2-cell `t ⇒ t`; the right-unit law asserts it is `id_t`. -/
def monadRightUnitCell : RawTwoCellExpr monadModeSignature monadT monadT :=
  RawTwoCellExpr.vcomp
    (RawTwoCellExpr.whiskerLeft (signature := monadModeSignature) monadT monadUnitTwoCell)
    monadMulTwoCell

/-- The **left-associativity composite** `mu ∘ (mu ▷ t)` — multiply the first two `t`'s, then multiply the
result with the third.  A 2-cell `t·t·t ⇒ t`. -/
def monadAssocLeftCell : RawTwoCellExpr monadModeSignature monadTThenTThenT monadT :=
  RawTwoCellExpr.vcomp
    (RawTwoCellExpr.whiskerRight (signature := monadModeSignature) monadT monadMulTwoCell)
    monadMulTwoCell

/-- The **right-associativity composite** `mu ∘ (t ◁ mu)` — multiply the last two `t`'s, then multiply the first
with the result.  A 2-cell `t·t·t ⇒ t` (the source `t·(t·t)` is DEFINITIONALLY `(t·t)·t`). -/
def monadAssocRightCell : RawTwoCellExpr monadModeSignature monadTThenTThenT monadT :=
  RawTwoCellExpr.vcomp
    (RawTwoCellExpr.whiskerLeft (signature := monadModeSignature) monadT monadMulTwoCell)
    monadMulTwoCell

/-- The identity 2-cell on `t` (the RHS of both unit laws). -/
def monadIdTCell : RawTwoCellExpr monadModeSignature monadT monadT :=
  RawTwoCellExpr.id (signature := monadModeSignature) monadT

end FX1Poly.Polygraph
