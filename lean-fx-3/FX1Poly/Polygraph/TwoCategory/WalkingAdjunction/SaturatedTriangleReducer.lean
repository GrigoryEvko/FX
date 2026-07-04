import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.SaturatedInterchangeFreeStep
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.AdjunctionTwoCellDecidable
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.AdjunctionTriangleObstruction

/-! # SaturatedTriangleReducer — the computable triangle ROOT recognizers (fragment reducer, root layer)

The saturated fragment normalizer needs a COMPUTABLE one-step reducer.  Its structural layer is
the shipped generic `RawTwoCellExpr.reduceOnce`; this file ships the TRIANGLE layer's root: for
each of the four triangle rules of `SaturatedStepInterchangeFree` (bare left/right snake,
left/right snake-prefix completion), a recognizer that fires exactly on the rule's redex shape
and returns its reduct.

DESIGN (the propext-safe recipe): the recognizers never match constructor-headed INDEX values
(that is the cons-index match leak).  They match only binder-form cell SHAPES with FULL
constructor enumeration (no wildcard arms — the prefix recognizers split into an outer
one-level match plus a completion probe on the second factor, mirroring the shipped
`reduceRootVcomp`/`dropRightIdentity` two-level template), then decide the boundary-path
equalities with `modalityPathDecEq`, transport the rule's literal factors across those
equalities with a single `Eq.rec` cast helper, and finish with the same-index cell comparison
`adjunctionRawTwoCellDecidableEq`.  Soundness per rule: the decisions pin the cell to the rule's
redex, so the rule's constructor applies after `subst`.  Everything computes — the bare-snake
and prefix firings close by `rfl`.

Raw Lean 4 + Init; per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## The boundary cast + the snake factor literals -/

/-- Transport a free 2-cell across boundary-path equalities (the one `Eq.rec` the recognizers
use — always instantiated at decEq-produced proofs, so it computes on concrete cells). -/
def castCellAlongBoundary {sourceMode targetMode : AdjunctionMode}
    {sourcePathOne targetPathOne sourcePathTwo targetPathTwo :
      ModalityPath adjunctionGraph sourceMode targetMode}
    (sourceEq : sourcePathOne = sourcePathTwo) (targetEq : targetPathOne = targetPathTwo)
    (cell : RawTwoCellExpr adjunctionModeSignature sourcePathOne targetPathOne) :
    RawTwoCellExpr adjunctionModeSignature sourcePathTwo targetPathTwo :=
  sourceEq ▸ targetEq ▸ cell

/-- The left snake's middle 1-cell `L·R·L` (as the unit factor's target association). -/
def leftSnakeMidPath : ModalityPath adjunctionGraph AdjunctionMode.base AdjunctionMode.tip :=
  composePath adjunctionLeftThenRight (singletonModalityPath AdjunctionModality.left)

/-- The right snake's middle 1-cell `R·L·R` (as the unit factor's target association). -/
def rightSnakeMidPath : ModalityPath adjunctionGraph AdjunctionMode.tip AdjunctionMode.base :=
  composePath (singletonModalityPath AdjunctionModality.right) adjunctionLeftThenRight

/-- The left snake's first factor `η ▷ L : L ⇒ L·R·L`. -/
def leftSnakeUnitFactor :
    RawTwoCellExpr adjunctionModeSignature
      (singletonModalityPath AdjunctionModality.left) leftSnakeMidPath :=
  RawTwoCellExpr.whiskerRight (signature := adjunctionModeSignature)
    (singletonModalityPath AdjunctionModality.left) adjunctionUnitTwoCell

/-- The left snake's second factor `L ◁ ε : L·R·L ⇒ L`. -/
def leftSnakeCounitFactor :
    RawTwoCellExpr adjunctionModeSignature
      leftSnakeMidPath (singletonModalityPath AdjunctionModality.left) :=
  RawTwoCellExpr.whiskerLeft (signature := adjunctionModeSignature)
    (singletonModalityPath AdjunctionModality.left) adjunctionCounitTwoCell

/-- The right snake's first factor `R ◁ η : R ⇒ R·L·R`. -/
def rightSnakeUnitFactor :
    RawTwoCellExpr adjunctionModeSignature
      (singletonModalityPath AdjunctionModality.right) rightSnakeMidPath :=
  RawTwoCellExpr.whiskerLeft (signature := adjunctionModeSignature)
    (singletonModalityPath AdjunctionModality.right) adjunctionUnitTwoCell

/-- The right snake's second factor `ε ▷ R : R·L·R ⇒ R`. -/
def rightSnakeCounitFactor :
    RawTwoCellExpr adjunctionModeSignature
      rightSnakeMidPath (singletonModalityPath AdjunctionModality.right) :=
  RawTwoCellExpr.whiskerRight (signature := adjunctionModeSignature)
    (singletonModalityPath AdjunctionModality.right) adjunctionCounitTwoCell

/-! ## The four root recognizers -/

/-- Recognize the bare LEFT triangle redex: the boundary must be `L ⇒ L` and the cell the left
snake; the reduct is `id_L`, transported back to the scrutinee's boundary. -/
def leftBareSnakeReduce?
    {sourcePath targetPath : ModalityPath adjunctionGraph AdjunctionMode.base AdjunctionMode.tip}
    (cell : RawTwoCellExpr adjunctionModeSignature sourcePath targetPath) :
    Option (RawTwoCellExpr adjunctionModeSignature sourcePath targetPath) :=
  match modalityPathDecEq adjunctionModeDecEq adjunctionModalityDecEq sourcePath
      (singletonModalityPath AdjunctionModality.left) with
  | Decidable.isFalse _ => none
  | Decidable.isTrue sourceIsLeft =>
      match modalityPathDecEq adjunctionModeDecEq adjunctionModalityDecEq targetPath
          (singletonModalityPath AdjunctionModality.left) with
      | Decidable.isFalse _ => none
      | Decidable.isTrue targetIsLeft =>
          match adjunctionRawTwoCellDecidableEq cell
              (castCellAlongBoundary sourceIsLeft.symm targetIsLeft.symm
                adjunctionSeedLeftSnake) with
          | Decidable.isFalse _ => none
          | Decidable.isTrue _ =>
              some (castCellAlongBoundary sourceIsLeft.symm targetIsLeft.symm
                (RawTwoCellExpr.id (signature := adjunctionModeSignature)
                  (singletonModalityPath AdjunctionModality.left)))

/-- Recognize the bare RIGHT triangle redex, dually. -/
def rightBareSnakeReduce?
    {sourcePath targetPath : ModalityPath adjunctionGraph AdjunctionMode.tip AdjunctionMode.base}
    (cell : RawTwoCellExpr adjunctionModeSignature sourcePath targetPath) :
    Option (RawTwoCellExpr adjunctionModeSignature sourcePath targetPath) :=
  match modalityPathDecEq adjunctionModeDecEq adjunctionModalityDecEq sourcePath
      (singletonModalityPath AdjunctionModality.right) with
  | Decidable.isFalse _ => none
  | Decidable.isTrue sourceIsRight =>
      match modalityPathDecEq adjunctionModeDecEq adjunctionModalityDecEq targetPath
          (singletonModalityPath AdjunctionModality.right) with
      | Decidable.isFalse _ => none
      | Decidable.isTrue targetIsRight =>
          match adjunctionRawTwoCellDecidableEq cell
              (castCellAlongBoundary sourceIsRight.symm targetIsRight.symm
                adjunctionSeedRightSnake) with
          | Decidable.isFalse _ => none
          | Decidable.isTrue _ =>
              some (castCellAlongBoundary sourceIsRight.symm targetIsRight.symm
                (RawTwoCellExpr.id (signature := adjunctionModeSignature)
                  (singletonModalityPath AdjunctionModality.right)))

/-- The LEFT snake-prefix completion probe: given the outer vcomp's two factors, fire when the
second factor splits as `(L◁ε) ⊟ rest` and the boundary decisions pin the pair to the snake
prefix; the reduct is `rest`, transported to the outer boundary.  Full constructor enumeration
on the second factor. -/
def leftSnakePrefixCompletion?
    {sourcePath midOnePath targetPath :
      ModalityPath adjunctionGraph AdjunctionMode.base AdjunctionMode.tip}
    (firstFactor : RawTwoCellExpr adjunctionModeSignature sourcePath midOnePath)
    (second : RawTwoCellExpr adjunctionModeSignature midOnePath targetPath) :
    Option (RawTwoCellExpr adjunctionModeSignature sourcePath targetPath) :=
  match second with
  | @RawTwoCellExpr.vcomp _ _ _ _ midTwoPath _ secondFactor rest =>
      match modalityPathDecEq adjunctionModeDecEq adjunctionModalityDecEq sourcePath
          (singletonModalityPath AdjunctionModality.left) with
      | Decidable.isFalse _ => none
      | Decidable.isTrue sourceIsLeft =>
          match modalityPathDecEq adjunctionModeDecEq adjunctionModalityDecEq midOnePath
              leftSnakeMidPath with
          | Decidable.isFalse _ => none
          | Decidable.isTrue midOneIsSnakeMid =>
              match modalityPathDecEq adjunctionModeDecEq adjunctionModalityDecEq midTwoPath
                  (singletonModalityPath AdjunctionModality.left) with
              | Decidable.isFalse _ => none
              | Decidable.isTrue midTwoIsLeft =>
                  match adjunctionRawTwoCellDecidableEq firstFactor
                      (castCellAlongBoundary sourceIsLeft.symm midOneIsSnakeMid.symm
                        leftSnakeUnitFactor) with
                  | Decidable.isFalse _ => none
                  | Decidable.isTrue _ =>
                      match adjunctionRawTwoCellDecidableEq secondFactor
                          (castCellAlongBoundary midOneIsSnakeMid.symm midTwoIsLeft.symm
                            leftSnakeCounitFactor) with
                      | Decidable.isFalse _ => none
                      | Decidable.isTrue _ =>
                          some (castCellAlongBoundary
                            (midTwoIsLeft.trans sourceIsLeft.symm) rfl rest)
  | RawTwoCellExpr.gen _ => none
  | RawTwoCellExpr.id _ => none
  | RawTwoCellExpr.whiskerLeft _ _ => none
  | RawTwoCellExpr.whiskerRight _ _ => none

/-- Recognize the LEFT snake-prefix redex `(η▷L) ⊟ ((L◁ε) ⊟ rest)`: one-level match on the
cell for the outer `vcomp`, then the completion probe.  Full constructor enumeration. -/
def leftSnakePrefixReduce?
    {sourcePath targetPath : ModalityPath adjunctionGraph AdjunctionMode.base AdjunctionMode.tip}
    (cell : RawTwoCellExpr adjunctionModeSignature sourcePath targetPath) :
    Option (RawTwoCellExpr adjunctionModeSignature sourcePath targetPath) :=
  match cell with
  | RawTwoCellExpr.vcomp firstFactor second => leftSnakePrefixCompletion? firstFactor second
  | RawTwoCellExpr.gen _ => none
  | RawTwoCellExpr.id _ => none
  | RawTwoCellExpr.whiskerLeft _ _ => none
  | RawTwoCellExpr.whiskerRight _ _ => none

/-- The RIGHT snake-prefix completion probe, dually: fire when the second factor splits as
`(ε▷R) ⊟ rest` under the right-snake boundary decisions. -/
def rightSnakePrefixCompletion?
    {sourcePath midOnePath targetPath :
      ModalityPath adjunctionGraph AdjunctionMode.tip AdjunctionMode.base}
    (firstFactor : RawTwoCellExpr adjunctionModeSignature sourcePath midOnePath)
    (second : RawTwoCellExpr adjunctionModeSignature midOnePath targetPath) :
    Option (RawTwoCellExpr adjunctionModeSignature sourcePath targetPath) :=
  match second with
  | @RawTwoCellExpr.vcomp _ _ _ _ midTwoPath _ secondFactor rest =>
      match modalityPathDecEq adjunctionModeDecEq adjunctionModalityDecEq sourcePath
          (singletonModalityPath AdjunctionModality.right) with
      | Decidable.isFalse _ => none
      | Decidable.isTrue sourceIsRight =>
          match modalityPathDecEq adjunctionModeDecEq adjunctionModalityDecEq midOnePath
              rightSnakeMidPath with
          | Decidable.isFalse _ => none
          | Decidable.isTrue midOneIsSnakeMid =>
              match modalityPathDecEq adjunctionModeDecEq adjunctionModalityDecEq midTwoPath
                  (singletonModalityPath AdjunctionModality.right) with
              | Decidable.isFalse _ => none
              | Decidable.isTrue midTwoIsRight =>
                  match adjunctionRawTwoCellDecidableEq firstFactor
                      (castCellAlongBoundary sourceIsRight.symm midOneIsSnakeMid.symm
                        rightSnakeUnitFactor) with
                  | Decidable.isFalse _ => none
                  | Decidable.isTrue _ =>
                      match adjunctionRawTwoCellDecidableEq secondFactor
                          (castCellAlongBoundary midOneIsSnakeMid.symm midTwoIsRight.symm
                            rightSnakeCounitFactor) with
                      | Decidable.isFalse _ => none
                      | Decidable.isTrue _ =>
                          some (castCellAlongBoundary
                            (midTwoIsRight.trans sourceIsRight.symm) rfl rest)
  | RawTwoCellExpr.gen _ => none
  | RawTwoCellExpr.id _ => none
  | RawTwoCellExpr.whiskerLeft _ _ => none
  | RawTwoCellExpr.whiskerRight _ _ => none

/-- Recognize the RIGHT snake-prefix redex `(R◁η) ⊟ ((ε▷R) ⊟ rest)`, dually. -/
def rightSnakePrefixReduce?
    {sourcePath targetPath : ModalityPath adjunctionGraph AdjunctionMode.tip AdjunctionMode.base}
    (cell : RawTwoCellExpr adjunctionModeSignature sourcePath targetPath) :
    Option (RawTwoCellExpr adjunctionModeSignature sourcePath targetPath) :=
  match cell with
  | RawTwoCellExpr.vcomp firstFactor second => rightSnakePrefixCompletion? firstFactor second
  | RawTwoCellExpr.gen _ => none
  | RawTwoCellExpr.id _ => none
  | RawTwoCellExpr.whiskerLeft _ _ => none
  | RawTwoCellExpr.whiskerRight _ _ => none

/-! ## The mode-dispatching root reducer -/

/-- ★ **The triangle ROOT reducer**: dispatch on the (plain-enum) boundary modes — the left
rules live at `base ⇒ tip`, the right rules at `tip ⇒ base`, and no triangle redex exists at
the endo boundaries.  Full mode enumeration.  The prefix completion is tried BEFORE the bare
snake: on a prefix redex every decision the prefix cascade makes is concrete (the free tail
never gets scrutinized), so progress on prefix steps closes by kernel computation, whereas the
bare probe would get stuck deciding the free target boundary first. -/
def triangleReduceRoot? :
    {sourceMode targetMode : AdjunctionMode} →
    {sourcePath targetPath : ModalityPath adjunctionGraph sourceMode targetMode} →
    (cell : RawTwoCellExpr adjunctionModeSignature sourcePath targetPath) →
    Option (RawTwoCellExpr adjunctionModeSignature sourcePath targetPath)
  | .base, .tip, _, _, cell =>
      match leftSnakePrefixReduce? cell with
      | some reduct => some reduct
      | none => leftBareSnakeReduce? cell
  | .tip, .base, _, _, cell =>
      match rightSnakePrefixReduce? cell with
      | some reduct => some reduct
      | none => rightBareSnakeReduce? cell
  | .base, .base, _, _, _ => none
  | .tip, .tip, _, _, _ => none

/-! ## Soundness — every firing is a fragment step -/

/-- Soundness of the bare-left recognizer: a firing pins the boundary to `L ⇒ L` and the cell
to the left snake, so `leftBareSnake` applies. -/
theorem leftBareSnakeReduce?_sound
    {sourcePath targetPath : ModalityPath adjunctionGraph AdjunctionMode.base AdjunctionMode.tip}
    {cell reduct : RawTwoCellExpr adjunctionModeSignature sourcePath targetPath}
    (fired : leftBareSnakeReduce? cell = some reduct) :
    SaturatedStepInterchangeFree cell reduct := by
  dsimp only [leftBareSnakeReduce?] at fired
  split at fired
  · exact nomatch fired
  · next sourceIsLeft _ =>
      split at fired
      · exact nomatch fired
      · next targetIsLeft _ =>
          split at fired
          · exact nomatch fired
          · next cellIsSnake _ =>
              subst sourceIsLeft
              subst targetIsLeft
              subst cellIsSnake
              injection fired with reductEq
              subst reductEq
              exact SaturatedStepInterchangeFree.leftBareSnake

/-- Soundness of the bare-right recognizer, dually. -/
theorem rightBareSnakeReduce?_sound
    {sourcePath targetPath : ModalityPath adjunctionGraph AdjunctionMode.tip AdjunctionMode.base}
    {cell reduct : RawTwoCellExpr adjunctionModeSignature sourcePath targetPath}
    (fired : rightBareSnakeReduce? cell = some reduct) :
    SaturatedStepInterchangeFree cell reduct := by
  dsimp only [rightBareSnakeReduce?] at fired
  split at fired
  · exact nomatch fired
  · next sourceIsRight _ =>
      split at fired
      · exact nomatch fired
      · next targetIsRight _ =>
          split at fired
          · exact nomatch fired
          · next cellIsSnake _ =>
              subst sourceIsRight
              subst targetIsRight
              subst cellIsSnake
              injection fired with reductEq
              subst reductEq
              exact SaturatedStepInterchangeFree.rightBareSnake

/-- Soundness of the left completion probe: the decisions pin the two factors to the snake
literals and the boundary paths to `L` / `L·R·L` / `L`, so `leftSnakePrefix rest` applies. -/
theorem leftSnakePrefixCompletion?_sound :
    {sourcePath midOnePath targetPath :
      ModalityPath adjunctionGraph AdjunctionMode.base AdjunctionMode.tip} →
    {firstFactor : RawTwoCellExpr adjunctionModeSignature sourcePath midOnePath} →
    {second : RawTwoCellExpr adjunctionModeSignature midOnePath targetPath} →
    {reduct : RawTwoCellExpr adjunctionModeSignature sourcePath targetPath} →
    leftSnakePrefixCompletion? firstFactor second = some reduct →
    SaturatedStepInterchangeFree (RawTwoCellExpr.vcomp firstFactor second) reduct
  | _, _, _, _, .gen _, _, fired => nomatch fired
  | _, _, _, _, .id _, _, fired => nomatch fired
  | _, _, _, _, .whiskerLeft _ _, _, fired => nomatch fired
  | _, _, _, _, .whiskerRight _ _, _, fired => nomatch fired
  | _, _, _, _, @RawTwoCellExpr.vcomp _ _ _ _ _ _ secondFactor rest, _, fired => by
      dsimp only [leftSnakePrefixCompletion?] at fired
      split at fired
      · exact nomatch fired
      · next sourceIsLeft _ =>
          split at fired
          · exact nomatch fired
          · next midOneIsSnakeMid _ =>
              split at fired
              · exact nomatch fired
              · next midTwoIsLeft _ =>
                  split at fired
                  · exact nomatch fired
                  · next firstIsUnit _ =>
                      split at fired
                      · exact nomatch fired
                      · next secondIsCounit _ =>
                          subst sourceIsLeft
                          subst midOneIsSnakeMid
                          subst midTwoIsLeft
                          subst firstIsUnit
                          subst secondIsCounit
                          injection fired with reductEq
                          subst reductEq
                          exact SaturatedStepInterchangeFree.leftSnakePrefix rest

/-- Soundness of the left snake-prefix recognizer: the outer match exposes the vcomp and
delegates to the completion probe. -/
theorem leftSnakePrefixReduce?_sound :
    {sourcePath targetPath :
      ModalityPath adjunctionGraph AdjunctionMode.base AdjunctionMode.tip} →
    {cell reduct : RawTwoCellExpr adjunctionModeSignature sourcePath targetPath} →
    leftSnakePrefixReduce? cell = some reduct →
    SaturatedStepInterchangeFree cell reduct
  | _, _, .gen _, _, fired => nomatch fired
  | _, _, .id _, _, fired => nomatch fired
  | _, _, .vcomp _ _, _, fired => leftSnakePrefixCompletion?_sound fired
  | _, _, .whiskerLeft _ _, _, fired => nomatch fired
  | _, _, .whiskerRight _ _, _, fired => nomatch fired

/-- Soundness of the right completion probe, dually. -/
theorem rightSnakePrefixCompletion?_sound :
    {sourcePath midOnePath targetPath :
      ModalityPath adjunctionGraph AdjunctionMode.tip AdjunctionMode.base} →
    {firstFactor : RawTwoCellExpr adjunctionModeSignature sourcePath midOnePath} →
    {second : RawTwoCellExpr adjunctionModeSignature midOnePath targetPath} →
    {reduct : RawTwoCellExpr adjunctionModeSignature sourcePath targetPath} →
    rightSnakePrefixCompletion? firstFactor second = some reduct →
    SaturatedStepInterchangeFree (RawTwoCellExpr.vcomp firstFactor second) reduct
  | _, _, _, _, .gen _, _, fired => nomatch fired
  | _, _, _, _, .id _, _, fired => nomatch fired
  | _, _, _, _, .whiskerLeft _ _, _, fired => nomatch fired
  | _, _, _, _, .whiskerRight _ _, _, fired => nomatch fired
  | _, _, _, _, @RawTwoCellExpr.vcomp _ _ _ _ _ _ secondFactor rest, _, fired => by
      dsimp only [rightSnakePrefixCompletion?] at fired
      split at fired
      · exact nomatch fired
      · next sourceIsRight _ =>
          split at fired
          · exact nomatch fired
          · next midOneIsSnakeMid _ =>
              split at fired
              · exact nomatch fired
              · next midTwoIsRight _ =>
                  split at fired
                  · exact nomatch fired
                  · next firstIsUnit _ =>
                      split at fired
                      · exact nomatch fired
                      · next secondIsCounit _ =>
                          subst sourceIsRight
                          subst midOneIsSnakeMid
                          subst midTwoIsRight
                          subst firstIsUnit
                          subst secondIsCounit
                          injection fired with reductEq
                          subst reductEq
                          exact SaturatedStepInterchangeFree.rightSnakePrefix rest

/-- Soundness of the right snake-prefix recognizer, dually. -/
theorem rightSnakePrefixReduce?_sound :
    {sourcePath targetPath :
      ModalityPath adjunctionGraph AdjunctionMode.tip AdjunctionMode.base} →
    {cell reduct : RawTwoCellExpr adjunctionModeSignature sourcePath targetPath} →
    rightSnakePrefixReduce? cell = some reduct →
    SaturatedStepInterchangeFree cell reduct
  | _, _, .gen _, _, fired => nomatch fired
  | _, _, .id _, _, fired => nomatch fired
  | _, _, .vcomp _ _, _, fired => rightSnakePrefixCompletion?_sound fired
  | _, _, .whiskerLeft _ _, _, fired => nomatch fired
  | _, _, .whiskerRight _ _, _, fired => nomatch fired

/-- ★ **Soundness of the triangle root reducer**: every firing is a fragment step. -/
theorem triangleReduceRoot?_sound
    {sourceMode targetMode : AdjunctionMode}
    {sourcePath targetPath : ModalityPath adjunctionGraph sourceMode targetMode}
    {cell reduct : RawTwoCellExpr adjunctionModeSignature sourcePath targetPath}
    (fired : triangleReduceRoot? cell = some reduct) :
    SaturatedStepInterchangeFree cell reduct := by
  cases sourceMode <;> cases targetMode <;> dsimp only [triangleReduceRoot?] at fired
  case base.base => exact nomatch fired
  case base.tip =>
      cases hPrefix : leftSnakePrefixReduce? cell with
      | some prefixReduct =>
          rw [hPrefix] at fired
          exact (Option.some.inj fired) ▸ leftSnakePrefixReduce?_sound hPrefix
      | none =>
          rw [hPrefix] at fired
          exact leftBareSnakeReduce?_sound fired
  case tip.base =>
      cases hPrefix : rightSnakePrefixReduce? cell with
      | some prefixReduct =>
          rw [hPrefix] at fired
          exact (Option.some.inj fired) ▸ rightSnakePrefixReduce?_sound hPrefix
      | none =>
          rw [hPrefix] at fired
          exact rightBareSnakeReduce?_sound fired
  case tip.tip => exact nomatch fired

/-! ## Firing smokes — the recognizers COMPUTE -/

/-- The bare-left recognizer fires on the left snake, by kernel computation. -/
theorem leftBareSnakeReduce?_firesOnSnake :
    leftBareSnakeReduce? adjunctionSeedLeftSnake
      = some (RawTwoCellExpr.id (signature := adjunctionModeSignature)
          (singletonModalityPath AdjunctionModality.left)) := rfl

/-- The bare-right recognizer fires on the right snake, by kernel computation. -/
theorem rightBareSnakeReduce?_firesOnSnake :
    rightBareSnakeReduce? adjunctionSeedRightSnake
      = some (RawTwoCellExpr.id (signature := adjunctionModeSignature)
          (singletonModalityPath AdjunctionModality.right)) := rfl

/-- The left-prefix recognizer fires on a snake-prefixed identity, returning the tail, by
kernel computation. -/
theorem leftSnakePrefixReduce?_firesOnPrefixedId :
    leftSnakePrefixReduce?
      (RawTwoCellExpr.vcomp leftSnakeUnitFactor
        (RawTwoCellExpr.vcomp leftSnakeCounitFactor
          (RawTwoCellExpr.id (signature := adjunctionModeSignature)
            (singletonModalityPath AdjunctionModality.left))))
      = some (RawTwoCellExpr.id (signature := adjunctionModeSignature)
          (singletonModalityPath AdjunctionModality.left)) := rfl

/-- The root reducer rewrites the LEFT SNAKE to the identity at the dispatch level too. -/
theorem triangleReduceRoot?_firesOnLeftSnake :
    triangleReduceRoot? adjunctionSeedLeftSnake
      = some (RawTwoCellExpr.id (signature := adjunctionModeSignature)
          (singletonModalityPath AdjunctionModality.left)) := rfl

/-! ## The anywhere descent + the saturated one-step reducer -/

/-- ★ **The triangle ANYWHERE reducer**: fire a triangle redex at the root or under any
`vcomp`/whisker congruence nest (root-first, then the leftmost reducible position).  Structural
recursion on the cell, mirroring the shipped structural `reduceOnce` descent; generators and
identities carry no triangle redex (all four triangle redexes are `vcomp`-headed). -/
def triangleReduce? :
    {sourceMode targetMode : AdjunctionMode} →
    {sourcePath targetPath : ModalityPath adjunctionGraph sourceMode targetMode} →
    (cell : RawTwoCellExpr adjunctionModeSignature sourcePath targetPath) →
    Option (RawTwoCellExpr adjunctionModeSignature sourcePath targetPath)
  | _, _, _, _, .gen _ => none
  | _, _, _, _, .id _ => none
  | _, _, _, _, .vcomp cellAlpha cellBeta =>
      match triangleReduceRoot? (RawTwoCellExpr.vcomp cellAlpha cellBeta) with
      | some rootReduct => some rootReduct
      | none =>
          match triangleReduce? cellAlpha with
          | some alphaReduct => some (.vcomp alphaReduct cellBeta)
          | none =>
              match triangleReduce? cellBeta with
              | some betaReduct => some (.vcomp cellAlpha betaReduct)
              | none => none
  | _, _, _, _, .whiskerLeft oneCell body =>
      match triangleReduce? body with
      | some bodyReduct => some (.whiskerLeft oneCell bodyReduct)
      | none => none
  | _, _, _, _, .whiskerRight oneCell body =>
      match triangleReduce? body with
      | some bodyReduct => some (.whiskerRight oneCell bodyReduct)
      | none => none

/-- Soundness of the anywhere descent: a root firing rides the root soundness, a descended
firing rides the matching fragment congruence constructor over the recursive soundness. -/
theorem triangleReduce?_sound :
    {sourceMode targetMode : AdjunctionMode} →
    {sourcePath targetPath : ModalityPath adjunctionGraph sourceMode targetMode} →
    {cell reduct : RawTwoCellExpr adjunctionModeSignature sourcePath targetPath} →
    triangleReduce? cell = some reduct →
    SaturatedStepInterchangeFree cell reduct
  | _, _, _, _, .gen _, _, fired => nomatch fired
  | _, _, _, _, .id _, _, fired => nomatch fired
  | _, _, _, _, .vcomp cellAlpha cellBeta, _, fired => by
      dsimp only [triangleReduce?] at fired
      cases hRoot : triangleReduceRoot? (RawTwoCellExpr.vcomp cellAlpha cellBeta) with
      | some rootReduct =>
          rw [hRoot] at fired
          exact (Option.some.inj fired) ▸ triangleReduceRoot?_sound hRoot
      | none =>
          rw [hRoot] at fired
          cases hAlpha : triangleReduce? cellAlpha with
          | some alphaReduct =>
              rw [hAlpha] at fired
              exact (Option.some.inj fired) ▸
                SaturatedStepInterchangeFree.vcompCongrLeft cellBeta
                  (triangleReduce?_sound hAlpha)
          | none =>
              rw [hAlpha] at fired
              cases hBeta : triangleReduce? cellBeta with
              | some betaReduct =>
                  rw [hBeta] at fired
                  exact (Option.some.inj fired) ▸
                    SaturatedStepInterchangeFree.vcompCongrRight cellAlpha
                      (triangleReduce?_sound hBeta)
              | none => rw [hBeta] at fired; exact nomatch fired
  | _, _, _, _, .whiskerLeft oneCell body, _, fired => by
      dsimp only [triangleReduce?] at fired
      cases hBody : triangleReduce? body with
      | some bodyReduct =>
          rw [hBody] at fired
          exact (Option.some.inj fired) ▸
            SaturatedStepInterchangeFree.whiskerLeftCongr oneCell
              (triangleReduce?_sound hBody)
      | none => rw [hBody] at fired; exact nomatch fired
  | _, _, _, _, .whiskerRight oneCell body, _, fired => by
      dsimp only [triangleReduce?] at fired
      cases hBody : triangleReduce? body with
      | some bodyReduct =>
          rw [hBody] at fired
          exact (Option.some.inj fired) ▸
            SaturatedStepInterchangeFree.whiskerRightCongr oneCell
              (triangleReduce?_sound hBody)
      | none => rw [hBody] at fired; exact nomatch fired

/-- ★ **The saturated fragment's one-step reducer**: try a triangle redex anywhere first, then
fall back to the shipped structural interchange-free reducer.  This is the computable front end
of the fragment normalizer. -/
def saturatedReduceOnce
    {sourceMode targetMode : AdjunctionMode}
    {sourcePath targetPath : ModalityPath adjunctionGraph sourceMode targetMode}
    (cell : RawTwoCellExpr adjunctionModeSignature sourcePath targetPath) :
    Option (RawTwoCellExpr adjunctionModeSignature sourcePath targetPath) :=
  match triangleReduce? cell with
  | some triangleReduct => some triangleReduct
  | none => cell.reduceOnce

/-- ★ **The saturated reducer is SOUND**: every firing is a fragment step — triangle firings
directly, structural firings through `ofStructural`. -/
theorem saturatedReduceOnce_sound
    {sourceMode targetMode : AdjunctionMode}
    {sourcePath targetPath : ModalityPath adjunctionGraph sourceMode targetMode}
    {cell reduct : RawTwoCellExpr adjunctionModeSignature sourcePath targetPath}
    (fired : saturatedReduceOnce cell = some reduct) :
    SaturatedStepInterchangeFree cell reduct := by
  dsimp only [saturatedReduceOnce] at fired
  cases hTriangle : triangleReduce? cell with
  | some triangleReduct =>
      rw [hTriangle] at fired
      exact (Option.some.inj fired) ▸ triangleReduce?_sound hTriangle
  | none =>
      rw [hTriangle] at fired
      exact SaturatedStepInterchangeFree.ofStructural (RawTwoCellExpr.reduceOnce_sound fired)

/-! ## Descent + saturated smokes — the full reducer stack COMPUTES -/

/-- The anywhere descent finds the left snake UNDER a right whiskering, by kernel
computation — the congruence layer really descends. -/
theorem triangleReduce?_firesUnderWhisker :
    triangleReduce?
      (RawTwoCellExpr.whiskerRight (signature := adjunctionModeSignature)
        (singletonModalityPath AdjunctionModality.right) adjunctionSeedLeftSnake)
      = some (RawTwoCellExpr.whiskerRight (signature := adjunctionModeSignature)
          (singletonModalityPath AdjunctionModality.right)
          (RawTwoCellExpr.id (singletonModalityPath AdjunctionModality.left))) := rfl

/-- The saturated reducer rewrites the left snake to the identity, by kernel computation. -/
theorem saturatedReduceOnce_firesOnLeftSnake :
    saturatedReduceOnce adjunctionSeedLeftSnake
      = some (RawTwoCellExpr.id (signature := adjunctionModeSignature)
          (singletonModalityPath AdjunctionModality.left)) := rfl

/-- On a triangle-free structural redex (an id-left vcomp) the saturated reducer falls through
to the structural layer, by kernel computation. -/
theorem saturatedReduceOnce_firesOnStructuralRedex :
    saturatedReduceOnce
      (RawTwoCellExpr.vcomp
        (RawTwoCellExpr.id (signature := adjunctionModeSignature)
          (singletonModalityPath AdjunctionModality.left))
        (RawTwoCellExpr.id (signature := adjunctionModeSignature)
          (singletonModalityPath AdjunctionModality.left)))
      = some (RawTwoCellExpr.id (signature := adjunctionModeSignature)
          (singletonModalityPath AdjunctionModality.left)) := rfl

end FX1Poly.Polygraph
