import FX1Poly.Polygraph.Computad.MonadSeed
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.Model

/-! # WalkingMonad/MonadCellSize — the conv-FREE structural-size floor lemma (micro-relocation)

`one_le_cellSize` (every free 2-cell has structural size at least one) is the sole conv-FREE fuel lemma the
walking-monad normalizers need; it depends only on the `RawTwoCellExpr` substrate (`FreeTwoCell/Model`) over the
monad mode signature (`Computad/MonadSeed`), carrying NO saturated-convertibility content.  Relocating it into this
leaf lets the native decider file (`MonadNormalizeGen`) drop its `MonadWordProblem` import — pruning that file's
build closure off the pure-bespoke Δ chain — while `MonadWordProblem` itself imports the leaf for its own fueled
recursion.

Raw Lean 4 + Init; `propext`/`Quot.sound`/`Classical`/`sorry`/`native_decide`/`omega`-free (a five-arm structural
match with a constant `Nat` motive).  Per-declaration `#assert_no_axioms` gated in the audit twin. -/

namespace FX1Poly.Polygraph

/-- Every free 2-cell has structural size at least one. -/
theorem one_le_cellSize {sourceMode targetMode : MonadMode}
    {sourcePath targetPath : ModalityPath monadGraph sourceMode targetMode}
    (cell : RawTwoCellExpr monadModeSignature sourcePath targetPath) : 1 ≤ cell.size :=
  match cell with
  | .gen _ => Nat.le_refl 1
  | .id _ => Nat.le_refl 1
  | .vcomp cellL cellR => Nat.le_add_left 1 (cellL.size + cellR.size)
  | .whiskerLeft _ body => Nat.le_add_left 1 body.size
  | .whiskerRight _ body => Nat.le_add_left 1 body.size

end FX1Poly.Polygraph
