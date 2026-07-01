import FX1Poly.Polygraph.Computad.WordProblem
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.InterchangeFree

/-! # mode-3 floor — the free 2-cell SPINE (the structural-law quotient, explicit)

The interchange-free fragment `TwoCellStepInterchangeFree` decides 2-cell equality up to the eleven STRUCTURAL
laws (`FreeTwoCellInterchangeFreeDecidable`); the remaining brick toward the full `TwoCellConv` decision is the
Godement / interchange quotient.  This file builds the bridge object both halves want: the **spine** — the flat
list of a 2-cell's generating-2-cell occurrences, each tagged with its left / right whiskering context.

  ★ `RawTwoCellExpr.spineDiff` / `RawTwoCellExpr.spine` — flatten a free 2-cell to its atom list.  Built as a
    CONS-ONLY difference list with the whisker contexts threaded as ACCUMULATORS (no `++`, no `List.map`), which
    (1) keeps it propext-free — `List.append_assoc` / `append_nil` / `map_append` all route through `propext`,
    the documented List trap — and (2) makes vertical re-association and whisker-distribution invariance hold
    DEFINITIONALLY (`rfl`).
  ★ `TwoCellStepInterchangeFree.spine_eq` — the spine is INVARIANT under the interchange-free structural rewrite:
    every one of the eleven structural laws preserves it (the four congruences via the strengthened
    `spineDiff_eq` over all boundary accumulators; the rest by `rfl`).  So the spine is a SOUND complete-up-to-
    structure invariant: interchange-free-convertible 2-cells share a spine.
  ★ `RawTwoCellExpr.spine_length` — the spine length is exactly the `generatorCount` (`ComputadWordProblem`), so
    the spine refines the shipped word-length conversion invariant.

## What the spine is NOT (the precise remaining hurdle)

The spine is NOT invariant under the Godement `interchange` law.  Interchange permutes two horizontally-
independent atoms in the spine AND shifts their whisker contexts: on `hcomp (α ⊟ α') (β ⊟ β')` versus its
exchanged form, the spines agree on the outer atoms `α`, `β'` but the inner atoms shift — `α'`'s right context
moves `dom β → cod β` and `β`'s left context moves `cod α' → dom α'` (the context records which independent atom
fired first).  So deciding the FULL `TwoCellConv` (interchange included) needs the spine canonicalized MODULO
this context-shifting permutation: a swap-invariant SOURCE-ANCHOR coordinate for each atom (its position traced
back to the fixed source 1-cell, stable under exchanging independent atoms), then a stable sort by that anchor —
the trace-monoid (Mazurkiewicz) normal form.  That source-anchor canonicalization is the genuine
confluence-modulo-interchange (Gratzer coherence) hurdle the keystone `fxMode_hasModeRelativeConvDecision` flip
awaits; this file ships the structural floor it builds on, not the anchor.

Raw Lean 4 + Init; `propext`/`Quot.sound`/`Classical`/`sorry`/`native_decide`/`omega`-free (the difference-list
flattening is cons-only; the invariance is `rfl` / induction-hypothesis; the length is `Nat.add` rearrangement).
Per-declaration `#assert_no_axioms` gated in the audit twin. -/

namespace FX1Poly.Tier0

/-! ## The spine atom + the cons-only flattening -/

/-- One atom of a flattened 2-cell spine: a generating 2-cell with a left and right whiskering context. -/
structure SpineAtom (signature : ModeSignature) (sourceMode targetMode : signature.graph.Mode) where
  /-- The mode at the generator's source boundary (after the left context). -/
  leftMidMode : signature.graph.Mode
  /-- The mode at the generator's target boundary (before the right context). -/
  rightMidMode : signature.graph.Mode
  /-- The whiskering 1-cell to the left of the generator. -/
  leftContext : ModalityPath signature.graph sourceMode leftMidMode
  /-- The generator's source 1-cell. -/
  generatorDom : ModalityPath signature.graph leftMidMode rightMidMode
  /-- The generator's target 1-cell. -/
  generatorCod : ModalityPath signature.graph leftMidMode rightMidMode
  /-- The generating 2-cell. -/
  generator : signature.twoCell generatorDom generatorCod
  /-- The whiskering 1-cell to the right of the generator. -/
  rightContext : ModalityPath signature.graph rightMidMode targetMode

/-- Flatten a free 2-cell into the list of its generating-2-cell atoms, threading the left / right whiskering
contexts as accumulators (a cons-only difference list — no `++` / `List.map`, so vertical re-association and
whisker-distribution invariance are definitional and the whole thing stays propext-free). -/
def RawTwoCellExpr.spineDiff {signature : ModeSignature} {overallSource overallTarget : signature.graph.Mode} :
    {localSource localTarget : signature.graph.Mode} →
    ModalityPath signature.graph overallSource localSource →
    ModalityPath signature.graph localTarget overallTarget →
    {localDom localCod : ModalityPath signature.graph localSource localTarget} →
    RawTwoCellExpr signature localDom localCod →
    List (SpineAtom signature overallSource overallTarget) →
    List (SpineAtom signature overallSource overallTarget)
  | _, _, leftAccumulator, rightAccumulator, _, _, .gen generator, rest =>
      ⟨_, _, leftAccumulator, _, _, generator, rightAccumulator⟩ :: rest
  | _, _, _, _, _, _, .id _, rest => rest
  | _, _, leftAccumulator, rightAccumulator, _, _, .vcomp cellAlpha cellBeta, rest =>
      cellAlpha.spineDiff leftAccumulator rightAccumulator
        (cellBeta.spineDiff leftAccumulator rightAccumulator rest)
  | _, _, leftAccumulator, rightAccumulator, _, _, .whiskerLeft oneCell body, rest =>
      body.spineDiff (composePath leftAccumulator oneCell) rightAccumulator rest
  | _, _, leftAccumulator, rightAccumulator, _, _, .whiskerRight oneCell body, rest =>
      body.spineDiff leftAccumulator (composePath oneCell rightAccumulator) rest

/-- The spine of a free 2-cell: its atoms with empty boundary accumulators. -/
def RawTwoCellExpr.spine {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode}
    {sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode}
    (cell : RawTwoCellExpr signature sourcePath targetPath) :
    List (SpineAtom signature sourceMode targetMode) :=
  cell.spineDiff (identityPath sourceMode) (identityPath targetMode) []

/-- Smoke: the spine of `unit ⊟ id` equals the spine of bare `unit` (the `vcompIdRight` law is spine-invariant). -/
theorem adjunctionUnitThenId_spine_eq_unit :
    adjunctionUnitThenId.spine = adjunctionUnitTwoCell.spine := rfl

/-! ## Invariance under the structural rewrite -/

/-- ★ The spine difference-list is invariant under the interchange-free structural rewrite, for ALL boundary
accumulators (the strengthened statement that lets the four one-hole congruences go through their IH). -/
theorem TwoCellStepInterchangeFree.spineDiff_eq {signature : ModeSignature}
    {overallSource overallTarget : signature.graph.Mode}
    {localSource localTarget : signature.graph.Mode}
    {localDom localCod : ModalityPath signature.graph localSource localTarget}
    {expr reduct : RawTwoCellExpr signature localDom localCod}
    (step : TwoCellStepInterchangeFree signature expr reduct) :
    ∀ (leftAccumulator : ModalityPath signature.graph overallSource localSource)
      (rightAccumulator : ModalityPath signature.graph localTarget overallTarget)
      (rest : List (SpineAtom signature overallSource overallTarget)),
      expr.spineDiff leftAccumulator rightAccumulator rest =
        reduct.spineDiff leftAccumulator rightAccumulator rest := by
  induction step with
  | vcompIdLeft _ => intro _ _ _; rfl
  | vcompIdRight _ => intro _ _ _; rfl
  | vcompAssoc _ _ _ => intro _ _ _; rfl
  | whiskerLeftId _ _ => intro _ _ _; rfl
  | whiskerRightId _ _ => intro _ _ _; rfl
  | whiskerLeftVcomp _ _ _ => intro _ _ _; rfl
  | whiskerRightVcomp _ _ _ => intro _ _ _; rfl
  | vcompCongrLeft _ _ inductionHypothesis =>
      intro leftAccumulator rightAccumulator rest
      dsimp only [RawTwoCellExpr.spineDiff]
      exact inductionHypothesis leftAccumulator rightAccumulator _
  | vcompCongrRight _ _ inductionHypothesis =>
      intro leftAccumulator rightAccumulator rest
      dsimp only [RawTwoCellExpr.spineDiff]
      rw [inductionHypothesis leftAccumulator rightAccumulator rest]
  | whiskerLeftCongr oneCell _ inductionHypothesis =>
      intro leftAccumulator rightAccumulator rest
      dsimp only [RawTwoCellExpr.spineDiff]
      exact inductionHypothesis (composePath leftAccumulator oneCell) rightAccumulator rest
  | whiskerRightCongr oneCell _ inductionHypothesis =>
      intro leftAccumulator rightAccumulator rest
      dsimp only [RawTwoCellExpr.spineDiff]
      exact inductionHypothesis leftAccumulator (composePath oneCell rightAccumulator) rest

/-- ★ **The spine is invariant under the interchange-free structural rewrite** — hence interchange-free-
convertible 2-cells share a spine (the sound, complete-up-to-structure invariant). -/
theorem TwoCellStepInterchangeFree.spine_eq {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode}
    {sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode}
    {expr reduct : RawTwoCellExpr signature sourcePath targetPath}
    (step : TwoCellStepInterchangeFree signature expr reduct) : expr.spine = reduct.spine :=
  step.spineDiff_eq (identityPath sourceMode) (identityPath targetMode) []

/-! ## The spine refines the generator-count invariant -/

/-- The spine difference-list adds exactly `generatorCount` atoms onto the rest. -/
theorem RawTwoCellExpr.spineDiff_length {signature : ModeSignature}
    {overallSource overallTarget : signature.graph.Mode} :
    {localSource localTarget : signature.graph.Mode} →
    (leftAccumulator : ModalityPath signature.graph overallSource localSource) →
    (rightAccumulator : ModalityPath signature.graph localTarget overallTarget) →
    {localDom localCod : ModalityPath signature.graph localSource localTarget} →
    (cell : RawTwoCellExpr signature localDom localCod) →
    (rest : List (SpineAtom signature overallSource overallTarget)) →
    (cell.spineDiff leftAccumulator rightAccumulator rest).length = cell.generatorCount + rest.length
  | _, _, _, _, _, _, .gen _, _ => by
      dsimp only [RawTwoCellExpr.spineDiff, RawTwoCellExpr.generatorCount, List.length]
      rw [Nat.add_comm]
  | _, _, _, _, _, _, .id _, _ => by
      dsimp only [RawTwoCellExpr.spineDiff, RawTwoCellExpr.generatorCount]; rw [Nat.zero_add]
  | _, _, leftAccumulator, rightAccumulator, _, _, .vcomp cellAlpha cellBeta, _ => by
      dsimp only [RawTwoCellExpr.spineDiff, RawTwoCellExpr.generatorCount]
      rw [RawTwoCellExpr.spineDiff_length leftAccumulator rightAccumulator cellAlpha,
        RawTwoCellExpr.spineDiff_length leftAccumulator rightAccumulator cellBeta, Nat.add_assoc]
  | _, _, leftAccumulator, rightAccumulator, _, _, .whiskerLeft oneCell body, rest => by
      dsimp only [RawTwoCellExpr.spineDiff, RawTwoCellExpr.generatorCount]
      exact RawTwoCellExpr.spineDiff_length (composePath leftAccumulator oneCell) rightAccumulator body rest
  | _, _, leftAccumulator, rightAccumulator, _, _, .whiskerRight oneCell body, rest => by
      dsimp only [RawTwoCellExpr.spineDiff, RawTwoCellExpr.generatorCount]
      exact RawTwoCellExpr.spineDiff_length leftAccumulator (composePath oneCell rightAccumulator) body rest

/-- ★ The spine length is exactly the generator count — the spine refines the word-length conversion invariant. -/
theorem RawTwoCellExpr.spine_length {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode}
    {sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode}
    (cell : RawTwoCellExpr signature sourcePath targetPath) :
    cell.spine.length = cell.generatorCount := by
  dsimp only [RawTwoCellExpr.spine]
  rw [RawTwoCellExpr.spineDiff_length, List.length, Nat.add_zero]

end FX1Poly.Tier0
