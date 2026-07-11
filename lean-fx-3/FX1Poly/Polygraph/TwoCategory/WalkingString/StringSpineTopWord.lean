import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.SpineBoundaryWordChain

/-! # WalkingString — the SPINE TOP-WORD extractor: the cod-boundary 1-cell threaded through a spine
(FC-3 r12, the shared-top plumbing device)

The width-0 pure-cup sort pins its located partner cup to the head cup on their SHARED TOP boundary word — the fixed
codomain 1-cell every cup in a width-0 valley builds up to.  The shipped drop-in
`stringSpineAtom_eq_of_sharedCod_sameWindow` (`StringLastCupSharedTopPin`) consumes exactly that shared cod word, but
the width-0 determinacy Prop (`StringWidthZeroPureCupDeterminacy`) in its bare form throws the top word away — so the
adapter cannot even be called from it.  Strengthening the Prop with the shared top word (the r12 re-key) needs a
first-class EXTRACTOR of a spine's top boundary word; grep confirmed none exists.  This file ships it:

  * ★ `spineListTopWord` — thread the running cod boundary word through an atom list: the empty spine returns its
    bottom word; a cons discards the bottom word and recurses with the head atom's cod boundary word
    `leftContext · generatorCod · rightContext`.  So a non-empty spine's top word is the LAST atom's cod word — the
    1-cell at the spine's top boundary.  Structural recursion on the list (full nil/cons enumeration, no `dite`/fuel/
    `==`), so it stays propext-free.
  * ★ `spineListTopWord_spineDiff` — the production law: threading `spineListTopWord` through a cell's spine
    difference-list transforms the bottom-boundary accumulator (the cell's DOM word) into the top-boundary accumulator
    (its COD word).  The whisker arms re-associate the `composePath` accumulators via the shipped category
    associativity (`composePath_assoc`), exactly like the length version's `Nat.add_assoc`.
  * ★★ `RawTwoCellExpr.spineListTopWord_spine` — the initial-state seed: every cell's spine has top word equal to the
    cell's TARGET 1-cell (the identity accumulators collapse via `composePath_identityPath_left`/`_right`).  This is
    the fact the width-0 case-(a) dispatcher needs: both valleys share `targetPath`, so both cup suffixes share the
    top word the shared-cod pin consumes.

The definition is signature-generic (hosted in the string lane because that is where the width-0 sort consumes it);
the top-word production mirrors the shipped boundary-WORD-chain production `spineBoundaryWordChained_spineDiff`
arm-for-arm.  Pure `composePath` bookkeeping, cons-only / structural — no new list algebra.

Raw Lean 4 + Init; `propext`/`Quot.sound`/`Classical`/`sorry`/`native_decide`/`omega`-free; per-declaration
`#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## The top-word extractor -/

/-- Thread the running codomain boundary word through a spine atom list.  The empty spine returns its bottom
boundary word; a cons recurses with the head atom's codomain boundary word
`leftContext · generatorCod · rightContext` (discarding the bottom word — it is only the empty-spine fallback).  So a
non-empty spine's top word is the LAST atom's codomain word: the 1-cell at the top of the spine.  Structural
recursion on the list; the free-1-cell (`ModalityPath`) analog of reading a spine's top boundary. -/
def spineListTopWord {signature : ModeSignature} {sourceMode targetMode : signature.graph.Mode}
    (bottomWord : ModalityPath signature.graph sourceMode targetMode) :
    List (SpineAtom signature sourceMode targetMode) → ModalityPath signature.graph sourceMode targetMode
  | [] => bottomWord
  | atom :: rest =>
      spineListTopWord
        (composePath atom.leftContext (composePath atom.generatorCod atom.rightContext)) rest

/-- The empty spine's top word is its bottom word (the base case, isolated for `rw`). -/
theorem spineListTopWord_nil {signature : ModeSignature} {sourceMode targetMode : signature.graph.Mode}
    (bottomWord : ModalityPath signature.graph sourceMode targetMode) :
    spineListTopWord bottomWord ([] : List (SpineAtom signature sourceMode targetMode)) = bottomWord := by
  dsimp only [spineListTopWord]

/-! ## Production: threading the top word through a spine difference-list -/

/-- **Production.**  Threading `spineListTopWord` through a cell's spine difference-list transforms the
bottom-boundary accumulator (the cell's DOM word `leftAccumulator · localDom · rightAccumulator`) into the
top-boundary accumulator (its COD word `leftAccumulator · localCod · rightAccumulator`).  Each generator hands its
codomain word to the tail; vertical composition threads the middle boundary word; the whisker arms re-associate the
`composePath` accumulators via the shipped category associativity (`composePath_assoc`), the word analog of the length
version's `Nat.add_assoc`.  Mirrors the boundary-WORD-chain production `spineBoundaryWordChained_spineDiff`
arm-for-arm. -/
theorem spineListTopWord_spineDiff {signature : ModeSignature}
    {overallSource overallTarget : signature.graph.Mode} :
    {localSource localTarget : signature.graph.Mode} →
    (leftAccumulator : ModalityPath signature.graph overallSource localSource) →
    (rightAccumulator : ModalityPath signature.graph localTarget overallTarget) →
    {localDom localCod : ModalityPath signature.graph localSource localTarget} →
    (cell : RawTwoCellExpr signature localDom localCod) →
    (rest : List (SpineAtom signature overallSource overallTarget)) →
    spineListTopWord (composePath leftAccumulator (composePath localDom rightAccumulator))
        (cell.spineDiff leftAccumulator rightAccumulator rest)
      = spineListTopWord (composePath leftAccumulator (composePath localCod rightAccumulator)) rest
  | _, _, leftAccumulator, rightAccumulator, _, _, .gen generator, rest => by
      dsimp only [RawTwoCellExpr.spineDiff, spineListTopWord]
  | _, _, _, _, _, _, .id _, _ => by
      dsimp only [RawTwoCellExpr.spineDiff]
  | _, _, leftAccumulator, rightAccumulator, _, _, .vcomp cellAlpha cellBeta, rest =>
      (spineListTopWord_spineDiff leftAccumulator rightAccumulator cellAlpha
          (cellBeta.spineDiff leftAccumulator rightAccumulator rest)).trans
        (spineListTopWord_spineDiff leftAccumulator rightAccumulator cellBeta rest)
  | _, _, leftAccumulator, rightAccumulator, _, _,
      @RawTwoCellExpr.whiskerLeft _ _ _ _ oneCell bodySourcePath bodyTargetPath body, rest => by
      dsimp only [RawTwoCellExpr.spineDiff]
      have shiftDom :
          composePath leftAccumulator
              (composePath (composePath oneCell bodySourcePath) rightAccumulator)
            = composePath (composePath leftAccumulator oneCell)
                (composePath bodySourcePath rightAccumulator) := by
        rw [composePath_assoc oneCell bodySourcePath rightAccumulator,
          ← composePath_assoc leftAccumulator oneCell (composePath bodySourcePath rightAccumulator)]
      have shiftCod :
          composePath leftAccumulator
              (composePath (composePath oneCell bodyTargetPath) rightAccumulator)
            = composePath (composePath leftAccumulator oneCell)
                (composePath bodyTargetPath rightAccumulator) := by
        rw [composePath_assoc oneCell bodyTargetPath rightAccumulator,
          ← composePath_assoc leftAccumulator oneCell (composePath bodyTargetPath rightAccumulator)]
      rw [shiftDom, shiftCod]
      exact spineListTopWord_spineDiff (composePath leftAccumulator oneCell) rightAccumulator body rest
  | _, _, leftAccumulator, rightAccumulator, _, _,
      @RawTwoCellExpr.whiskerRight _ _ _ _ bodySourcePath bodyTargetPath oneCell body, rest => by
      dsimp only [RawTwoCellExpr.spineDiff]
      have shiftDom :
          composePath leftAccumulator
              (composePath (composePath bodySourcePath oneCell) rightAccumulator)
            = composePath leftAccumulator
                (composePath bodySourcePath (composePath oneCell rightAccumulator)) := by
        rw [composePath_assoc bodySourcePath oneCell rightAccumulator]
      have shiftCod :
          composePath leftAccumulator
              (composePath (composePath bodyTargetPath oneCell) rightAccumulator)
            = composePath leftAccumulator
                (composePath bodyTargetPath (composePath oneCell rightAccumulator)) := by
        rw [composePath_assoc bodyTargetPath oneCell rightAccumulator]
      rw [shiftDom, shiftCod]
      exact spineListTopWord_spineDiff leftAccumulator (composePath oneCell rightAccumulator) body rest

/-! ## The initial-state seed -/

/-- ★★ **A cell's spine top word is its target 1-cell.**  Threading `spineListTopWord` from the cell's source word
through its spine lands on the cell's target word — the top boundary of the flattened 2-cell.  The identity
accumulators collapse via the shipped category unit laws (`composePath_identityPath_left`/`_right`).  This is the fact
the width-0 case-(a) dispatcher rides: two valleys sharing `targetPath` have cup suffixes sharing the top word the
shared-cod last-cup pin consumes. -/
theorem RawTwoCellExpr.spineListTopWord_spine {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode}
    {sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode}
    (cell : RawTwoCellExpr signature sourcePath targetPath) :
    spineListTopWord sourcePath cell.spine = targetPath := by
  have topPadded := spineListTopWord_spineDiff (identityPath sourceMode) (identityPath targetMode) cell []
  have domCollapses :
      composePath (identityPath (graph := signature.graph) sourceMode)
        (composePath sourcePath (identityPath (graph := signature.graph) targetMode)) = sourcePath := by
    rw [composePath_identityPath_right sourcePath]
    exact composePath_identityPath_left sourcePath
  have codCollapses :
      composePath (identityPath (graph := signature.graph) sourceMode)
        (composePath targetPath (identityPath (graph := signature.graph) targetMode)) = targetPath := by
    rw [composePath_identityPath_right targetPath]
    exact composePath_identityPath_left targetPath
  rw [domCollapses, codCollapses] at topPadded
  dsimp only [RawTwoCellExpr.spine]
  exact topPadded.trans (spineListTopWord_nil targetPath)

/-! ## Honesty marker -/

/-- **★ ESTABLISHED — the spine TOP-WORD extractor is shipped (FC-3 r12, the shared-top plumbing device).**
`spineListTopWord` threads the running cod boundary word through an atom list (a non-empty spine's top word is the
last atom's cod word); `spineListTopWord_spineDiff` is the production law (threading through a cell's spine turns its
DOM word into its COD word, whisker arms via `composePath_assoc`); `RawTwoCellExpr.spineListTopWord_spine` is the seed
(a cell's spine top word is its target 1-cell).  This is the first-class extractor the strengthened width-0
determinacy Prop re-key needs — the shared top word the last-cup pin `stringSpineAtom_eq_of_sharedCod_sameWindow`
consumes, delivered from the two valleys' common `targetPath`.  All UNCONDITIONAL, zero-axiom.  `= true`. -/
def fxString_hasSpineTopWordExtractor : Bool := true

end FX1Poly.Polygraph
