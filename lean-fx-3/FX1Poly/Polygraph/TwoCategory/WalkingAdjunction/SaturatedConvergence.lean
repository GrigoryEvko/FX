import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.SaturatedDecision
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.AdjunctionSaturatedNormalization
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.Confluence

/-! # mode-9 — the COMBINED saturated triangle rewrite: unconditional SN + the triangle critical pairs all join

`AdjunctionTriangleObstruction` shipped TWO SEPARATE Knuth–Bendix completions of the walking-adjunction word
problem — `AdjunctionLeftSaturatedStep` (the LEFT bare triangle + its snake-prefix) and
`AdjunctionRightSaturatedStep` (the RIGHT dual) — each with only the `vcompCongrLeft` congruence, each proven
strongly normalizing UNCONDITIONALLY (`adjunction{Left,Right}Saturated_isStronglyNormalizing`, fed by the now-
closed structural floor `twoCellStep_isStronglyNormalizing`).  But a single saturated 2-cell can carry BOTH a
left-snake and a right-snake subterm (e.g. `(R ◁ leftSnake) ⊟ (L ◁ rightSnake)`), and the existing per-side
relations cannot fire under a whiskering — so neither is the rewrite that NORMALIZES an arbitrary saturated
2-cell.  This file ships that rewrite and analyses its convergence.

## What this file ships (each piece zero-axiom)

  * ★ **`SaturatedTwoCellStep`** — the COMBINED both-triangle rewrite: every free strict-2-category 3-cell
    (`ofFree`), BOTH bare triangles (`leftBareSnake` / `rightBareSnake`), BOTH snake-prefix completions
    (`leftSnakePrefix` / `rightSnakePrefix`), AND the FULL one-hole congruence (all four of `vcompCongrLeft` /
    `vcompCongrRight` / `whiskerLeftCongr` / `whiskerRightCongr`) so a triangle redex fires in ANY sub-position.
    This is the genuine "normalize a saturated 2-cell" rewrite the per-side relations are not.
  * ★ **`SaturatedTwoCellStep.toSaturatedConv`** — SOUNDNESS: the combined rewrite computes WITHIN
    `SaturatedTwoCellConv` (every rule is a saturated convertibility — the free steps via `ofConv`, the snakes via
    `triangleLeft`/`triangleRight`, the prefixes via the shipped `leftSnakePrefixHolds`/`rightSnakePrefixHolds`,
    the congruences via the shipped saturated congruences), lifted to the reflexive-transitive closure.
  * ★ **`saturatedTwoCellStep_isStronglyNormalizing`** — TERMINATION, UNCONDITIONAL.  The combined rewrite is
    strongly normalizing outright: a lexicographic descent on `(generatorCount, structural-Acc)` where the four
    saturating completions STRICTLY drop `generatorCount` and every count-PRESERVING step is a free structural
    `TwoCellStep` (`generatorCountPreserving_isStructural`), handled by the closed structural floor.  Merges the
    two per-side SN proofs into one for the relation that carries both triangles.
  * ★ **the TRIANGLE-LAYER CRITICAL PAIRS ALL JOIN** — the crux positive content.  The four `vcompAssoc`
    critical pairs the saturating rules introduce (`{left,right} × {bareSnake, snakePrefix}`) every JOIN
    (`saturated{Left,Right}{BareSnake,Prefix}AssocCriticalPair_joins`).  The bare pairs reuse the obstruction
    file's joining; the PREFIX × assoc pairs are NEW here — the snake-prefix rule overlapping `vcompAssoc` in the
    left factor of a vertical composite, both reducts reaching `vcomp rest c`.  This completes the assoc critical-
    pair analysis of the KB completion for the combined relation.
  * ★ **`saturatedTwoCellStep_isConfluent`** — the Newman reduction: SN (above) + LOCAL confluence ⟹ confluence
    (Church-Rosser), at each parallel boundary, via the abstract `Core.newman`.  Isolates the SOLE remaining
    convergence obligation to `SaturatedTwoCellLocallyConfluent`.

## ★ The crux answered: the saturated rewrite is NOT confluent — but the obstruction is purely INHERITED

`SaturatedTwoCellLocallyConfluent` is FALSE, and the reason is NOT adjunction-specific: the combined rewrite
contains every free `TwoCellStep` (via `ofFree`), so it inherits the free `interchange × whiskerRightVcomp`
critical pair that `FreeTwoCellConfluence` already identified as NON-joining (the classic Godement / Eckmann–
Hilton non-confluence — the two 2×2-pasting decompositions are distinct terminal forms differing only in their
whiskering 1-cells, which no rule rewrites).  The triangle completion's snake/identity rules cannot repair it
(they never touch a whiskering 1-cell).  By contrast the triangle-layer critical pairs ALL join (the four
theorems above).  So the triangle saturation adds NO new confluence obstruction: the residual to a convergent
saturated presentation — and hence to `AdjunctionSaturatedCanonicalization` and the keystone — is EXACTLY the
pre-existing `fxMode_hasInterchangeAndWhiskerFunctoriality` floor, i.e. confluence MODULO the interchange
equation (the string/pasting-diagram quotient).  This is the rigorous form of "the triangle layer is clean".

Raw Lean 4 + Init.  Every declaration is `propext`/`Quot.sound`/`Classical`/`sorry`/`native_decide`/`omega`-free
(the rewrite is an inductive `Prop`; SN is a fuel-bounded `Acc` lexicographic descent on `Nat` order; the joins
are concrete `Core.ReflTransClosure` constructions; the Newman reduction is the abstract `Core.newman`).  Per-
declaration `#assert_no_axioms` gated in the audit twin. -/

namespace FX1Poly.Tier0

/-! ## A propext-free LEFT cancellation (the dual of `natAddRightCancel` for the right-factor congruence) -/

/-- Left-cancellation for `Nat` addition, propext-free — `sharedLeft + a = sharedLeft + b → a = b`.  Reduces to
the file-local `natAddRightCancel` (from `AdjunctionSaturatedNormalization`) by commuting the shared summand to
the right on both sides.  Needed for the RIGHT-factor `vcomp` congruence's count-preservation cancellation, where
the shared count sits on the LEFT. -/
theorem natAddLeftCancel {sharedLeft rightFirst rightSecond : Nat}
    (equalSums : sharedLeft + rightFirst = sharedLeft + rightSecond) : rightFirst = rightSecond :=
  natAddRightCancel
    ((Nat.add_comm rightFirst sharedLeft).trans
      (equalSums.trans (Nat.add_comm sharedLeft rightSecond)))

/-! ## The combined both-triangle saturated rewrite -/

/-- ★ The **combined both-triangle saturated rewrite** over the walking-adjunction signature: every free strict-
2-category 3-cell (`ofFree`), the LEFT and RIGHT bare triangles, the LEFT and RIGHT snake-prefix completions, and
the FULL one-hole congruence closure (left/right vertical-composite factor + left/right whiskering).  Unlike the
per-side `Adjunction{Left,Right}SaturatedStep`, this fires BOTH triangles and fires anywhere, so it normalizes an
arbitrary saturated 2-cell. -/
inductive SaturatedTwoCellStep :
    {sourceMode targetMode : AdjunctionMode} →
    {sourcePath targetPath : ModalityPath adjunctionGraph sourceMode targetMode} →
    RawTwoCellExpr adjunctionModeSignature sourcePath targetPath →
    RawTwoCellExpr adjunctionModeSignature sourcePath targetPath → Prop where
  /-- Embed any free strict-2-category 3-cell (`mode-3`'s `TwoCellStep`). -/
  | ofFree {sourceMode targetMode : AdjunctionMode}
      {sourcePath targetPath : ModalityPath adjunctionGraph sourceMode targetMode}
      {cellA cellB : RawTwoCellExpr adjunctionModeSignature sourcePath targetPath} :
      TwoCellStep adjunctionModeSignature cellA cellB → SaturatedTwoCellStep cellA cellB
  /-- The bare LEFT triangle `leftSnake ⤳ id_L`. -/
  | leftBareSnake :
      SaturatedTwoCellStep adjunctionSeedLeftSnake
        (RawTwoCellExpr.id (signature := adjunctionModeSignature)
          (singletonModalityPath AdjunctionModality.left))
  /-- The LEFT snake-prefix completion `(η▷L)⊟((L◁ε)⊟rest) ⤳ rest`. -/
  | leftSnakePrefix {targetPath : ModalityPath adjunctionGraph AdjunctionMode.base AdjunctionMode.tip}
      (rest : RawTwoCellExpr adjunctionModeSignature
        (singletonModalityPath AdjunctionModality.left) targetPath) :
      SaturatedTwoCellStep
        (RawTwoCellExpr.vcomp
          (RawTwoCellExpr.whiskerRight (signature := adjunctionModeSignature)
            (singletonModalityPath AdjunctionModality.left) adjunctionUnitTwoCell)
          (RawTwoCellExpr.vcomp
            (RawTwoCellExpr.whiskerLeft (signature := adjunctionModeSignature)
              (singletonModalityPath AdjunctionModality.left) adjunctionCounitTwoCell)
            rest))
        rest
  /-- The bare RIGHT triangle `rightSnake ⤳ id_R`. -/
  | rightBareSnake :
      SaturatedTwoCellStep adjunctionSeedRightSnake
        (RawTwoCellExpr.id (signature := adjunctionModeSignature)
          (singletonModalityPath AdjunctionModality.right))
  /-- The RIGHT snake-prefix completion `(R◁η)⊟((ε▷R)⊟rest) ⤳ rest`. -/
  | rightSnakePrefix {targetPath : ModalityPath adjunctionGraph AdjunctionMode.tip AdjunctionMode.base}
      (rest : RawTwoCellExpr adjunctionModeSignature
        (singletonModalityPath AdjunctionModality.right) targetPath) :
      SaturatedTwoCellStep
        (RawTwoCellExpr.vcomp
          (RawTwoCellExpr.whiskerLeft (signature := adjunctionModeSignature)
            (singletonModalityPath AdjunctionModality.right) adjunctionUnitTwoCell)
          (RawTwoCellExpr.vcomp
            (RawTwoCellExpr.whiskerRight (signature := adjunctionModeSignature)
              (singletonModalityPath AdjunctionModality.right) adjunctionCounitTwoCell)
            rest))
        rest
  /-- Congruence in the LEFT factor of a vertical composite. -/
  | vcompCongrLeft {sourceMode targetMode : AdjunctionMode}
      {oneCellF oneCellG oneCellH : ModalityPath adjunctionGraph sourceMode targetMode}
      {cellAlpha cellAlpha' : RawTwoCellExpr adjunctionModeSignature oneCellF oneCellG}
      (cellBeta : RawTwoCellExpr adjunctionModeSignature oneCellG oneCellH) :
      SaturatedTwoCellStep cellAlpha cellAlpha' →
      SaturatedTwoCellStep (RawTwoCellExpr.vcomp cellAlpha cellBeta)
        (RawTwoCellExpr.vcomp cellAlpha' cellBeta)
  /-- Congruence in the RIGHT factor of a vertical composite. -/
  | vcompCongrRight {sourceMode targetMode : AdjunctionMode}
      {oneCellF oneCellG oneCellH : ModalityPath adjunctionGraph sourceMode targetMode}
      (cellAlpha : RawTwoCellExpr adjunctionModeSignature oneCellF oneCellG)
      {cellBeta cellBeta' : RawTwoCellExpr adjunctionModeSignature oneCellG oneCellH} :
      SaturatedTwoCellStep cellBeta cellBeta' →
      SaturatedTwoCellStep (RawTwoCellExpr.vcomp cellAlpha cellBeta)
        (RawTwoCellExpr.vcomp cellAlpha cellBeta')
  /-- Congruence under a left whiskering. -/
  | whiskerLeftCongr {sourceMode middleMode targetMode : AdjunctionMode}
      (oneCell : ModalityPath adjunctionGraph sourceMode middleMode)
      {oneCellG oneCellH : ModalityPath adjunctionGraph middleMode targetMode}
      {cellBeta cellBeta' : RawTwoCellExpr adjunctionModeSignature oneCellG oneCellH} :
      SaturatedTwoCellStep cellBeta cellBeta' →
      SaturatedTwoCellStep (RawTwoCellExpr.whiskerLeft oneCell cellBeta)
        (RawTwoCellExpr.whiskerLeft oneCell cellBeta')
  /-- Congruence under a right whiskering. -/
  | whiskerRightCongr {sourceMode middleMode targetMode : AdjunctionMode}
      {oneCellF oneCellG : ModalityPath adjunctionGraph sourceMode middleMode}
      (oneCell : ModalityPath adjunctionGraph middleMode targetMode)
      {cellAlpha cellAlpha' : RawTwoCellExpr adjunctionModeSignature oneCellF oneCellG} :
      SaturatedTwoCellStep cellAlpha cellAlpha' →
      SaturatedTwoCellStep (RawTwoCellExpr.whiskerRight oneCell cellAlpha)
        (RawTwoCellExpr.whiskerRight oneCell cellAlpha')

/-! ## Soundness: the combined rewrite computes within `SaturatedTwoCellConv` -/

/-- ★ **One combined saturated step is a saturated convertibility.**  Each rule is realized in
`SaturatedTwoCellConv`: free steps by `ofConv`, the bare triangles by `triangleLeft`/`triangleRight`, the snake-
prefixes by the shipped `leftSnakePrefixHolds`/`rightSnakePrefixHolds`, the four congruences by the shipped
saturated congruences.  So `SaturatedTwoCellStep ⊆ SaturatedTwoCellConv`. -/
theorem SaturatedTwoCellStep.toSaturatedConv {sourceMode targetMode : AdjunctionMode}
    {sourcePath targetPath : ModalityPath adjunctionGraph sourceMode targetMode}
    {cellA cellB : RawTwoCellExpr adjunctionModeSignature sourcePath targetPath}
    (step : SaturatedTwoCellStep cellA cellB) : SaturatedTwoCellConv cellA cellB := by
  induction step with
  | ofFree freeStep => exact SaturatedTwoCellConv.ofConv (TwoCellConv.ofStep freeStep)
  | leftBareSnake => exact SaturatedTwoCellConv.triangleLeft
  | leftSnakePrefix rest => exact leftSnakePrefixHolds rest
  | rightBareSnake => exact SaturatedTwoCellConv.triangleRight
  | rightSnakePrefix rest => exact rightSnakePrefixHolds rest
  | vcompCongrLeft cellBeta _ inductionHypothesis =>
      exact SaturatedTwoCellConv.vcompCongrLeft cellBeta inductionHypothesis
  | vcompCongrRight cellAlpha _ inductionHypothesis =>
      exact SaturatedTwoCellConv.vcompCongrRight cellAlpha inductionHypothesis
  | whiskerLeftCongr oneCell _ inductionHypothesis =>
      exact SaturatedTwoCellConv.whiskerLeftCongr oneCell inductionHypothesis
  | whiskerRightCongr oneCell _ inductionHypothesis =>
      exact SaturatedTwoCellConv.whiskerRightCongr oneCell inductionHypothesis

/-- ★ **The whole combined saturated reduction is a saturated convertibility** — chain the single-step soundness
through `trans` along the reflexive-transitive closure. -/
theorem saturatedTwoCellReduces_toSaturatedConv {sourceMode targetMode : AdjunctionMode}
    {sourcePath targetPath : ModalityPath adjunctionGraph sourceMode targetMode}
    {cellA cellB : RawTwoCellExpr adjunctionModeSignature sourcePath targetPath}
    (reduction : Core.ReflTransClosure
      (fun (a b : RawTwoCellExpr adjunctionModeSignature sourcePath targetPath) => SaturatedTwoCellStep a b)
      cellA cellB) :
    SaturatedTwoCellConv cellA cellB := by
  induction reduction with
  | refl cell => exact SaturatedTwoCellConv.refl cell
  | head firstStep _ inductionHypothesis =>
      exact SaturatedTwoCellConv.trans firstStep.toSaturatedConv inductionHypothesis

/-! ## Termination — the major monovariant + the count-preserving-is-structural characterization -/

/-- ★ **One combined saturated step never increases `generatorCount`.**  `ofFree` preserves it; the bare
triangles drop `2 → 0`; the snake-prefixes drop `2 + rest → rest`; the congruences propagate the inductive
non-increase under their `+`-context (whiskerings pass the count through unchanged). -/
theorem SaturatedTwoCellStep.generatorCount_le {sourceMode targetMode : AdjunctionMode}
    {sourcePath targetPath : ModalityPath adjunctionGraph sourceMode targetMode}
    {cellA cellB : RawTwoCellExpr adjunctionModeSignature sourcePath targetPath}
    (step : SaturatedTwoCellStep cellA cellB) :
    cellB.generatorCount ≤ cellA.generatorCount := by
  induction step with
  | ofFree freeStep => exact Nat.le_of_eq freeStep.generatorCount_eq.symm
  | leftBareSnake => exact Nat.zero_le _
  | leftSnakePrefix rest =>
      exact Nat.le_trans (Nat.le_add_left rest.generatorCount _) (Nat.le_add_left _ _)
  | rightBareSnake => exact Nat.zero_le _
  | rightSnakePrefix rest =>
      exact Nat.le_trans (Nat.le_add_left rest.generatorCount _) (Nat.le_add_left _ _)
  | vcompCongrLeft cellBeta _ inductionHypothesis =>
      exact Nat.add_le_add_right inductionHypothesis cellBeta.generatorCount
  | vcompCongrRight cellAlpha _ inductionHypothesis =>
      exact Nat.add_le_add_left inductionHypothesis cellAlpha.generatorCount
  | whiskerLeftCongr _ _ inductionHypothesis => exact inductionHypothesis
  | whiskerRightCongr _ _ inductionHypothesis => exact inductionHypothesis

/-- ★ **A generator-count-preserving combined saturated step is a free structural `TwoCellStep`.**  The four
saturating completions STRICTLY drop the count (`bareSnake` 2→0, `snakePrefix` `2 + rest → rest`), so they cannot
preserve it; the only count-preserving combined steps are the free strict-2-category laws.  The congruence cases
cancel the shared factor's count (`natAddRightCancel` / `natAddLeftCancel`; whiskerings pass through) and recurse.
This is the combined merge of `AdjunctionSaturatedNormalization`'s per-side characterizations. -/
theorem SaturatedTwoCellStep.generatorCountPreserving_isStructural {sourceMode targetMode : AdjunctionMode}
    {sourcePath targetPath : ModalityPath adjunctionGraph sourceMode targetMode}
    {cellA cellB : RawTwoCellExpr adjunctionModeSignature sourcePath targetPath}
    (step : SaturatedTwoCellStep cellA cellB) :
    cellA.generatorCount = cellB.generatorCount →
      TwoCellStep adjunctionModeSignature cellA cellB := by
  induction step with
  | ofFree freeStep => exact fun _ => freeStep
  | leftBareSnake =>
      intro countPreserved
      exact absurd
        (adjunctionSeedLeftSnake_generatorCount.symm.trans
          (countPreserved.trans leftIdentityCell_generatorCount))
        (fun twoEqualsZero => Nat.noConfusion twoEqualsZero)
  | leftSnakePrefix rest =>
      intro countPreserved
      exact absurd
        (natAddRightCancel
          ((Nat.add_assoc 1 1 rest.generatorCount).trans
            (countPreserved.trans (Nat.zero_add rest.generatorCount).symm)))
        (fun twoEqualsZero => Nat.noConfusion twoEqualsZero)
  | rightBareSnake =>
      intro countPreserved
      exact absurd
        (adjunctionSeedRightSnake_generatorCount.symm.trans
          (countPreserved.trans
            (rfl : (RawTwoCellExpr.id (signature := adjunctionModeSignature)
              (singletonModalityPath AdjunctionModality.right)).generatorCount = 0)))
        (fun twoEqualsZero => Nat.noConfusion twoEqualsZero)
  | rightSnakePrefix rest =>
      intro countPreserved
      exact absurd
        (natAddRightCancel
          ((Nat.add_assoc 1 1 rest.generatorCount).trans
            (countPreserved.trans (Nat.zero_add rest.generatorCount).symm)))
        (fun twoEqualsZero => Nat.noConfusion twoEqualsZero)
  | vcompCongrLeft cellBeta _ structuralOfSub =>
      intro countPreserved
      exact TwoCellStep.vcompCongrLeft cellBeta (structuralOfSub (natAddRightCancel countPreserved))
  | vcompCongrRight cellAlpha _ structuralOfSub =>
      intro countPreserved
      exact TwoCellStep.vcompCongrRight cellAlpha (structuralOfSub (natAddLeftCancel countPreserved))
  | whiskerLeftCongr oneCell _ structuralOfSub =>
      intro countPreserved
      exact TwoCellStep.whiskerLeftCongr oneCell (structuralOfSub countPreserved)
  | whiskerRightCongr oneCell _ structuralOfSub =>
      intro countPreserved
      exact TwoCellStep.whiskerRightCongr oneCell (structuralOfSub countPreserved)

/-- ★ **The combined both-triangle saturated rewrite is strongly normalizing — UNCONDITIONALLY.**  Lexicographic
descent on `(generatorCount, structural-Acc)`: a saturated step either strictly drops `generatorCount` (the outer
fuel induction handles it) or preserves it and is therefore a free structural `TwoCellStep`
(`generatorCountPreserving_isStructural`, the inner `Acc` fed by the closed floor
`twoCellStep_isStronglyNormalizing` handles it).  The combined walking-adjunction completion — both triangles,
firing anywhere — adds NO termination obligation beyond the (now closed) structural floor. -/
theorem saturatedTwoCellStep_isStronglyNormalizing
    {sourceMode targetMode : AdjunctionMode}
    {sourcePath targetPath : ModalityPath adjunctionGraph sourceMode targetMode}
    (cell : RawTwoCellExpr adjunctionModeSignature sourcePath targetPath) :
    Acc (fun reduct expr => SaturatedTwoCellStep expr reduct) cell := by
  have fueled :
      ∀ (fuel : Nat) {sourceMode targetMode : AdjunctionMode}
        {sourcePath targetPath : ModalityPath adjunctionGraph sourceMode targetMode}
        (cell : RawTwoCellExpr adjunctionModeSignature sourcePath targetPath),
        cell.generatorCount < fuel →
          Acc (fun reduct expr => SaturatedTwoCellStep expr reduct) cell := by
    intro fuel
    induction fuel with
    | zero => intro _ _ _ _ _ countBelow; exact absurd countBelow (Nat.not_lt_zero _)
    | succ fuel outerIH =>
        have inner :
            ∀ {sourceMode targetMode : AdjunctionMode}
              {sourcePath targetPath : ModalityPath adjunctionGraph sourceMode targetMode}
              (cell : RawTwoCellExpr adjunctionModeSignature sourcePath targetPath),
              Acc (fun reduct expr => TwoCellStep adjunctionModeSignature expr reduct) cell →
                cell.generatorCount ≤ fuel →
                  Acc (fun reduct expr => SaturatedTwoCellStep expr reduct) cell := by
          intro _ _ _ _ _ structAcc
          induction structAcc with
          | intro current _ innerIH =>
              intro boundedByFuel
              refine Acc.intro current (fun reduct saturatedStep => ?_)
              rcases Nat.lt_or_eq_of_le saturatedStep.generatorCount_le with countDrops | countEqual
              · exact outerIH reduct (Nat.lt_of_lt_of_le countDrops boundedByFuel)
              · exact innerIH reduct
                  (saturatedStep.generatorCountPreserving_isStructural countEqual.symm)
                  (Nat.le_trans (Nat.le_of_eq countEqual) boundedByFuel)
        intro _ _ _ _ cell countBelow
        exact inner cell (twoCellStep_isStronglyNormalizing cell) (Nat.le_of_lt_succ countBelow)
  exact fueled (cell.generatorCount + 1) cell (Nat.lt_succ_self _)

/-! ## Newman: convergence reduced to LOCAL confluence -/

/-- **Local (weak) confluence of the combined saturated rewrite** — at every parallel boundary, divergent single
steps join.  This is the one remaining ingredient of a convergent saturated presentation.  It is NOT
dischargeable — FALSE for the same Godement/Eckmann–Hilton reason the free system is (see the module docstring):
the combined rewrite
contains every free `TwoCellStep` (via `ofFree`), inheriting the non-joining `interchange × whiskerRightVcomp`
critical pair `FreeTwoCellConfluence` isolated.  Recorded as the precise predicate the Newman reduction below
reduces to — a NEGATIVE result redirecting the keystone to confluence-modulo-interchange. -/
def SaturatedTwoCellLocallyConfluent : Prop :=
  ∀ {sourceMode targetMode : AdjunctionMode}
    {sourcePath targetPath : ModalityPath adjunctionGraph sourceMode targetMode},
    Core.WeaklyConfluent
      (fun (a b : RawTwoCellExpr adjunctionModeSignature sourcePath targetPath) => SaturatedTwoCellStep a b)

/-- ★ **The combined saturated rewrite is CONFLUENT (Church-Rosser), GIVEN local confluence.**  Newman's lemma at
each parallel boundary: the combined rewrite is strongly normalizing (`saturatedTwoCellStep_isStronglyNormalizing`,
packaged as the `WellFounded` of the flipped step), so SN + the supplied local confluence ⟹ confluence.  This
isolates the remaining convergence ingredient to EXACTLY `SaturatedTwoCellLocallyConfluent` — exactly as
`FreeTwoCellConfluence.twoCellStep_isConfluent` did for the free floor and `AdjunctionSaturatedNormalization` did
for termination. -/
theorem saturatedTwoCellStep_isConfluent (locallyConfluent : SaturatedTwoCellLocallyConfluent)
    {sourceMode targetMode : AdjunctionMode}
    {sourcePath targetPath : ModalityPath adjunctionGraph sourceMode targetMode} :
    Core.Confluent
      (fun (a b : RawTwoCellExpr adjunctionModeSignature sourcePath targetPath) => SaturatedTwoCellStep a b) :=
  Core.newman (WellFounded.intro (fun cell => saturatedTwoCellStep_isStronglyNormalizing cell)) locallyConfluent

/-! ## ★ The triangle-layer critical pairs ALL join (the crux positive content)

The combined rewrite adds to the free system exactly four saturating rules — `{left,right} × {bareSnake,
snakePrefix}`.  Each snake is a free-3-polygraph normal form (`AdjunctionTriangleObstruction`), so the saturating
rules overlap the free laws ONLY through `vcompAssoc` in the left factor of a vertical composite.  All four such
critical pairs JOIN. -/

/-- ★ **The LEFT bare-snake × `vcompAssoc` critical pair joins.**  The peak `vcomp leftSnake c` steps to
`vcomp id_L c` (the bare triangle under `vcompCongrLeft`) and to `vcomp (η▷L) ((L◁ε) ⊟ c)` (`vcompAssoc` at the
root); both reduce to `c` (`vcompIdLeft` resp. the LEFT snake-prefix).  Re-expresses the obstruction file's join
in the combined relation. -/
theorem saturatedLeftBareSnakeAssocCriticalPair_joins
    {targetPath : ModalityPath adjunctionGraph AdjunctionMode.base AdjunctionMode.tip}
    (continuation : RawTwoCellExpr adjunctionModeSignature
      (singletonModalityPath AdjunctionModality.left) targetPath) :
    Core.Joinable
      (fun (a b : RawTwoCellExpr adjunctionModeSignature
        (singletonModalityPath AdjunctionModality.left) targetPath) => SaturatedTwoCellStep a b)
      (RawTwoCellExpr.vcomp
        (RawTwoCellExpr.id (signature := adjunctionModeSignature)
          (singletonModalityPath AdjunctionModality.left)) continuation)
      (RawTwoCellExpr.vcomp
        (RawTwoCellExpr.whiskerRight (signature := adjunctionModeSignature)
          (singletonModalityPath AdjunctionModality.left) adjunctionUnitTwoCell)
        (RawTwoCellExpr.vcomp
          (RawTwoCellExpr.whiskerLeft (signature := adjunctionModeSignature)
            (singletonModalityPath AdjunctionModality.left) adjunctionCounitTwoCell)
          continuation)) :=
  ⟨continuation,
    Core.ReflTransClosure.single (SaturatedTwoCellStep.ofFree (TwoCellStep.vcompIdLeft continuation)),
    Core.ReflTransClosure.single (SaturatedTwoCellStep.leftSnakePrefix continuation)⟩

/-- ★ **The RIGHT bare-snake × `vcompAssoc` critical pair joins** — the dual of the left bare join. -/
theorem saturatedRightBareSnakeAssocCriticalPair_joins
    {targetPath : ModalityPath adjunctionGraph AdjunctionMode.tip AdjunctionMode.base}
    (continuation : RawTwoCellExpr adjunctionModeSignature
      (singletonModalityPath AdjunctionModality.right) targetPath) :
    Core.Joinable
      (fun (a b : RawTwoCellExpr adjunctionModeSignature
        (singletonModalityPath AdjunctionModality.right) targetPath) => SaturatedTwoCellStep a b)
      (RawTwoCellExpr.vcomp
        (RawTwoCellExpr.id (signature := adjunctionModeSignature)
          (singletonModalityPath AdjunctionModality.right)) continuation)
      (RawTwoCellExpr.vcomp
        (RawTwoCellExpr.whiskerLeft (signature := adjunctionModeSignature)
          (singletonModalityPath AdjunctionModality.right) adjunctionUnitTwoCell)
        (RawTwoCellExpr.vcomp
          (RawTwoCellExpr.whiskerRight (signature := adjunctionModeSignature)
            (singletonModalityPath AdjunctionModality.right) adjunctionCounitTwoCell)
          continuation)) :=
  ⟨continuation,
    Core.ReflTransClosure.single (SaturatedTwoCellStep.ofFree (TwoCellStep.vcompIdLeft continuation)),
    Core.ReflTransClosure.single (SaturatedTwoCellStep.rightSnakePrefix continuation)⟩

/-- ★★ **The LEFT snake-prefix × `vcompAssoc` critical pair joins** — NEW here.  The peak
`vcomp ((η▷L)⊟((L◁ε)⊟rest)) c` (the prefix LHS as the left factor of a vertical composite) steps to `vcomp rest c`
(the prefix under `vcompCongrLeft`) and to `vcomp (η▷L) (((L◁ε)⊟rest)⊟c)` (`vcompAssoc` at the root); the latter
re-associates inside (`vcompAssoc` under `vcompCongrRight`) to `vcomp (η▷L) ((L◁ε)⊟(rest⊟c))`, on which the LEFT
snake-prefix fires to `vcomp rest c`.  Both reach `vcomp rest c` — completing the assoc critical-pair analysis for
the LEFT completion rule. -/
theorem saturatedLeftPrefixAssocCriticalPair_joins
    {middlePath : ModalityPath adjunctionGraph AdjunctionMode.base AdjunctionMode.tip}
    {targetPath : ModalityPath adjunctionGraph AdjunctionMode.base AdjunctionMode.tip}
    (rest : RawTwoCellExpr adjunctionModeSignature
      (singletonModalityPath AdjunctionModality.left) middlePath)
    (continuation : RawTwoCellExpr adjunctionModeSignature middlePath targetPath) :
    Core.Joinable
      (fun (a b : RawTwoCellExpr adjunctionModeSignature
        (singletonModalityPath AdjunctionModality.left) targetPath) => SaturatedTwoCellStep a b)
      (RawTwoCellExpr.vcomp rest continuation)
      (RawTwoCellExpr.vcomp
        (RawTwoCellExpr.whiskerRight (signature := adjunctionModeSignature)
          (singletonModalityPath AdjunctionModality.left) adjunctionUnitTwoCell)
        (RawTwoCellExpr.vcomp
          (RawTwoCellExpr.vcomp
            (RawTwoCellExpr.whiskerLeft (signature := adjunctionModeSignature)
              (singletonModalityPath AdjunctionModality.left) adjunctionCounitTwoCell)
            rest)
          continuation)) :=
  ⟨RawTwoCellExpr.vcomp rest continuation,
    Core.ReflTransClosure.refl _,
    Core.ReflTransClosure.head
      (SaturatedTwoCellStep.vcompCongrRight
        (RawTwoCellExpr.whiskerRight (signature := adjunctionModeSignature)
          (singletonModalityPath AdjunctionModality.left) adjunctionUnitTwoCell)
        (SaturatedTwoCellStep.ofFree
          (TwoCellStep.vcompAssoc
            (RawTwoCellExpr.whiskerLeft (signature := adjunctionModeSignature)
              (singletonModalityPath AdjunctionModality.left) adjunctionCounitTwoCell)
            rest continuation)))
      (Core.ReflTransClosure.single
        (SaturatedTwoCellStep.leftSnakePrefix (RawTwoCellExpr.vcomp rest continuation)))⟩

/-- ★★ **The RIGHT snake-prefix × `vcompAssoc` critical pair joins** — the dual of the left prefix join. -/
theorem saturatedRightPrefixAssocCriticalPair_joins
    {middlePath : ModalityPath adjunctionGraph AdjunctionMode.tip AdjunctionMode.base}
    {targetPath : ModalityPath adjunctionGraph AdjunctionMode.tip AdjunctionMode.base}
    (rest : RawTwoCellExpr adjunctionModeSignature
      (singletonModalityPath AdjunctionModality.right) middlePath)
    (continuation : RawTwoCellExpr adjunctionModeSignature middlePath targetPath) :
    Core.Joinable
      (fun (a b : RawTwoCellExpr adjunctionModeSignature
        (singletonModalityPath AdjunctionModality.right) targetPath) => SaturatedTwoCellStep a b)
      (RawTwoCellExpr.vcomp rest continuation)
      (RawTwoCellExpr.vcomp
        (RawTwoCellExpr.whiskerLeft (signature := adjunctionModeSignature)
          (singletonModalityPath AdjunctionModality.right) adjunctionUnitTwoCell)
        (RawTwoCellExpr.vcomp
          (RawTwoCellExpr.vcomp
            (RawTwoCellExpr.whiskerRight (signature := adjunctionModeSignature)
              (singletonModalityPath AdjunctionModality.right) adjunctionCounitTwoCell)
            rest)
          continuation)) :=
  ⟨RawTwoCellExpr.vcomp rest continuation,
    Core.ReflTransClosure.refl _,
    Core.ReflTransClosure.head
      (SaturatedTwoCellStep.vcompCongrRight
        (RawTwoCellExpr.whiskerLeft (signature := adjunctionModeSignature)
          (singletonModalityPath AdjunctionModality.right) adjunctionUnitTwoCell)
        (SaturatedTwoCellStep.ofFree
          (TwoCellStep.vcompAssoc
            (RawTwoCellExpr.whiskerRight (signature := adjunctionModeSignature)
              (singletonModalityPath AdjunctionModality.right) adjunctionCounitTwoCell)
            rest continuation)))
      (Core.ReflTransClosure.single
        (SaturatedTwoCellStep.rightSnakePrefix (RawTwoCellExpr.vcomp rest continuation)))⟩

/-! ## The peaks are genuine: each join above resolves a real divergence of two single steps

Each `..._joins` theorem above joins the two REDUCTS; these companions certify those reducts are the two
single-step images of one common peak (so the joins are genuine critical-pair resolutions, not joins of unrelated
terms).  Together a `..._diverges` and its `..._joins` are exactly local confluence AT that peak. -/

/-- The LEFT bare-snake × `vcompAssoc` peak `vcomp leftSnake c` diverges to the two reducts
`saturatedLeftBareSnakeAssocCriticalPair_joins` then joins. -/
theorem saturatedLeftBareSnakeAssocPeak_diverges
    {targetPath : ModalityPath adjunctionGraph AdjunctionMode.base AdjunctionMode.tip}
    (continuation : RawTwoCellExpr adjunctionModeSignature
      (singletonModalityPath AdjunctionModality.left) targetPath) :
    SaturatedTwoCellStep (RawTwoCellExpr.vcomp adjunctionSeedLeftSnake continuation)
        (RawTwoCellExpr.vcomp
          (RawTwoCellExpr.id (signature := adjunctionModeSignature)
            (singletonModalityPath AdjunctionModality.left)) continuation)
      ∧ SaturatedTwoCellStep (RawTwoCellExpr.vcomp adjunctionSeedLeftSnake continuation)
        (RawTwoCellExpr.vcomp
          (RawTwoCellExpr.whiskerRight (signature := adjunctionModeSignature)
            (singletonModalityPath AdjunctionModality.left) adjunctionUnitTwoCell)
          (RawTwoCellExpr.vcomp
            (RawTwoCellExpr.whiskerLeft (signature := adjunctionModeSignature)
              (singletonModalityPath AdjunctionModality.left) adjunctionCounitTwoCell)
            continuation)) :=
  ⟨SaturatedTwoCellStep.vcompCongrLeft continuation SaturatedTwoCellStep.leftBareSnake,
    SaturatedTwoCellStep.ofFree
      (TwoCellStep.vcompAssoc
        (RawTwoCellExpr.whiskerRight (signature := adjunctionModeSignature)
          (singletonModalityPath AdjunctionModality.left) adjunctionUnitTwoCell)
        (RawTwoCellExpr.whiskerLeft (signature := adjunctionModeSignature)
          (singletonModalityPath AdjunctionModality.left) adjunctionCounitTwoCell)
        continuation)⟩

/-- The RIGHT bare-snake × `vcompAssoc` peak `vcomp rightSnake c` diverges to the reducts
`saturatedRightBareSnakeAssocCriticalPair_joins` then joins. -/
theorem saturatedRightBareSnakeAssocPeak_diverges
    {targetPath : ModalityPath adjunctionGraph AdjunctionMode.tip AdjunctionMode.base}
    (continuation : RawTwoCellExpr adjunctionModeSignature
      (singletonModalityPath AdjunctionModality.right) targetPath) :
    SaturatedTwoCellStep (RawTwoCellExpr.vcomp adjunctionSeedRightSnake continuation)
        (RawTwoCellExpr.vcomp
          (RawTwoCellExpr.id (signature := adjunctionModeSignature)
            (singletonModalityPath AdjunctionModality.right)) continuation)
      ∧ SaturatedTwoCellStep (RawTwoCellExpr.vcomp adjunctionSeedRightSnake continuation)
        (RawTwoCellExpr.vcomp
          (RawTwoCellExpr.whiskerLeft (signature := adjunctionModeSignature)
            (singletonModalityPath AdjunctionModality.right) adjunctionUnitTwoCell)
          (RawTwoCellExpr.vcomp
            (RawTwoCellExpr.whiskerRight (signature := adjunctionModeSignature)
              (singletonModalityPath AdjunctionModality.right) adjunctionCounitTwoCell)
            continuation)) :=
  ⟨SaturatedTwoCellStep.vcompCongrLeft continuation SaturatedTwoCellStep.rightBareSnake,
    SaturatedTwoCellStep.ofFree
      (TwoCellStep.vcompAssoc
        (RawTwoCellExpr.whiskerLeft (signature := adjunctionModeSignature)
          (singletonModalityPath AdjunctionModality.right) adjunctionUnitTwoCell)
        (RawTwoCellExpr.whiskerRight (signature := adjunctionModeSignature)
          (singletonModalityPath AdjunctionModality.right) adjunctionCounitTwoCell)
        continuation)⟩

/-- The LEFT snake-prefix × `vcompAssoc` peak `vcomp ((η▷L)⊟((L◁ε)⊟rest)) c` diverges to the two reducts
`saturatedLeftPrefixAssocCriticalPair_joins` then joins. -/
theorem saturatedLeftPrefixAssocPeak_diverges
    {middlePath : ModalityPath adjunctionGraph AdjunctionMode.base AdjunctionMode.tip}
    {targetPath : ModalityPath adjunctionGraph AdjunctionMode.base AdjunctionMode.tip}
    (rest : RawTwoCellExpr adjunctionModeSignature
      (singletonModalityPath AdjunctionModality.left) middlePath)
    (continuation : RawTwoCellExpr adjunctionModeSignature middlePath targetPath) :
    SaturatedTwoCellStep
        (RawTwoCellExpr.vcomp
          (RawTwoCellExpr.vcomp
            (RawTwoCellExpr.whiskerRight (signature := adjunctionModeSignature)
              (singletonModalityPath AdjunctionModality.left) adjunctionUnitTwoCell)
            (RawTwoCellExpr.vcomp
              (RawTwoCellExpr.whiskerLeft (signature := adjunctionModeSignature)
                (singletonModalityPath AdjunctionModality.left) adjunctionCounitTwoCell)
              rest))
          continuation)
        (RawTwoCellExpr.vcomp rest continuation)
      ∧ SaturatedTwoCellStep
        (RawTwoCellExpr.vcomp
          (RawTwoCellExpr.vcomp
            (RawTwoCellExpr.whiskerRight (signature := adjunctionModeSignature)
              (singletonModalityPath AdjunctionModality.left) adjunctionUnitTwoCell)
            (RawTwoCellExpr.vcomp
              (RawTwoCellExpr.whiskerLeft (signature := adjunctionModeSignature)
                (singletonModalityPath AdjunctionModality.left) adjunctionCounitTwoCell)
              rest))
          continuation)
        (RawTwoCellExpr.vcomp
          (RawTwoCellExpr.whiskerRight (signature := adjunctionModeSignature)
            (singletonModalityPath AdjunctionModality.left) adjunctionUnitTwoCell)
          (RawTwoCellExpr.vcomp
            (RawTwoCellExpr.vcomp
              (RawTwoCellExpr.whiskerLeft (signature := adjunctionModeSignature)
                (singletonModalityPath AdjunctionModality.left) adjunctionCounitTwoCell)
              rest)
            continuation)) :=
  ⟨SaturatedTwoCellStep.vcompCongrLeft continuation (SaturatedTwoCellStep.leftSnakePrefix rest),
    SaturatedTwoCellStep.ofFree
      (TwoCellStep.vcompAssoc
        (RawTwoCellExpr.whiskerRight (signature := adjunctionModeSignature)
          (singletonModalityPath AdjunctionModality.left) adjunctionUnitTwoCell)
        (RawTwoCellExpr.vcomp
          (RawTwoCellExpr.whiskerLeft (signature := adjunctionModeSignature)
            (singletonModalityPath AdjunctionModality.left) adjunctionCounitTwoCell)
          rest)
        continuation)⟩

/-- The RIGHT snake-prefix × `vcompAssoc` peak diverges to the two reducts
`saturatedRightPrefixAssocCriticalPair_joins` then joins. -/
theorem saturatedRightPrefixAssocPeak_diverges
    {middlePath : ModalityPath adjunctionGraph AdjunctionMode.tip AdjunctionMode.base}
    {targetPath : ModalityPath adjunctionGraph AdjunctionMode.tip AdjunctionMode.base}
    (rest : RawTwoCellExpr adjunctionModeSignature
      (singletonModalityPath AdjunctionModality.right) middlePath)
    (continuation : RawTwoCellExpr adjunctionModeSignature middlePath targetPath) :
    SaturatedTwoCellStep
        (RawTwoCellExpr.vcomp
          (RawTwoCellExpr.vcomp
            (RawTwoCellExpr.whiskerLeft (signature := adjunctionModeSignature)
              (singletonModalityPath AdjunctionModality.right) adjunctionUnitTwoCell)
            (RawTwoCellExpr.vcomp
              (RawTwoCellExpr.whiskerRight (signature := adjunctionModeSignature)
                (singletonModalityPath AdjunctionModality.right) adjunctionCounitTwoCell)
              rest))
          continuation)
        (RawTwoCellExpr.vcomp rest continuation)
      ∧ SaturatedTwoCellStep
        (RawTwoCellExpr.vcomp
          (RawTwoCellExpr.vcomp
            (RawTwoCellExpr.whiskerLeft (signature := adjunctionModeSignature)
              (singletonModalityPath AdjunctionModality.right) adjunctionUnitTwoCell)
            (RawTwoCellExpr.vcomp
              (RawTwoCellExpr.whiskerRight (signature := adjunctionModeSignature)
                (singletonModalityPath AdjunctionModality.right) adjunctionCounitTwoCell)
              rest))
          continuation)
        (RawTwoCellExpr.vcomp
          (RawTwoCellExpr.whiskerLeft (signature := adjunctionModeSignature)
            (singletonModalityPath AdjunctionModality.right) adjunctionUnitTwoCell)
          (RawTwoCellExpr.vcomp
            (RawTwoCellExpr.vcomp
              (RawTwoCellExpr.whiskerRight (signature := adjunctionModeSignature)
                (singletonModalityPath AdjunctionModality.right) adjunctionCounitTwoCell)
              rest)
            continuation)) :=
  ⟨SaturatedTwoCellStep.vcompCongrLeft continuation (SaturatedTwoCellStep.rightSnakePrefix rest),
    SaturatedTwoCellStep.ofFree
      (TwoCellStep.vcompAssoc
        (RawTwoCellExpr.whiskerLeft (signature := adjunctionModeSignature)
          (singletonModalityPath AdjunctionModality.right) adjunctionUnitTwoCell)
        (RawTwoCellExpr.vcomp
          (RawTwoCellExpr.whiskerRight (signature := adjunctionModeSignature)
            (singletonModalityPath AdjunctionModality.right) adjunctionCounitTwoCell)
          rest)
        continuation)⟩

/-! ## Smokes -/

/-- Smoke: the combined rewrite fires the LEFT triangle UNDER a right whiskering — `(R ◁ leftSnake) ⤳ (R ◁ id_L)`
— exercising the whisker congruence the per-side relations lack.  Witnesses the combined relation normalizes a
snake buried under a whiskering, which `AdjunctionLeftSaturatedStep` cannot reach. -/
theorem saturatedLeftSnakeUnderWhisker_step :
    SaturatedTwoCellStep
      (RawTwoCellExpr.whiskerLeft (signature := adjunctionModeSignature)
        (singletonModalityPath AdjunctionModality.right) adjunctionSeedLeftSnake)
      (RawTwoCellExpr.whiskerLeft (signature := adjunctionModeSignature)
        (singletonModalityPath AdjunctionModality.right)
        (RawTwoCellExpr.id (signature := adjunctionModeSignature)
          (singletonModalityPath AdjunctionModality.left))) :=
  SaturatedTwoCellStep.whiskerLeftCongr _ SaturatedTwoCellStep.leftBareSnake

/-- Smoke: that whiskered LEFT-triangle step is, via soundness, a saturated convertibility — the combined
rewrite's whisker-context firing lands inside `SaturatedTwoCellConv`. -/
theorem saturatedLeftSnakeUnderWhisker_conv :
    SaturatedTwoCellConv
      (RawTwoCellExpr.whiskerLeft (signature := adjunctionModeSignature)
        (singletonModalityPath AdjunctionModality.right) adjunctionSeedLeftSnake)
      (RawTwoCellExpr.whiskerLeft (signature := adjunctionModeSignature)
        (singletonModalityPath AdjunctionModality.right)
        (RawTwoCellExpr.id (signature := adjunctionModeSignature)
          (singletonModalityPath AdjunctionModality.left))) :=
  saturatedLeftSnakeUnderWhisker_step.toSaturatedConv

/-! ## Honesty markers (the parent owns the keystone flips) -/

/-- **ESTABLISHED.**  The COMBINED both-triangle saturated rewrite (`SaturatedTwoCellStep`) is shipped: SOUND
into `SaturatedTwoCellConv` (`SaturatedTwoCellStep.toSaturatedConv`), strongly normalizing UNCONDITIONALLY
(`saturatedTwoCellStep_isStronglyNormalizing`, the structural floor closed), and ALL FOUR of its triangle-layer
`vcompAssoc` critical pairs JOIN (`saturated{Left,Right}{BareSnake,Prefix}AssocCriticalPair_joins`).  So the
triangle saturation introduces no new confluence obstruction.  `= true`. -/
def fxMode_hasCombinedSaturatedTriangleRewrite : Bool := true

/-- **Honesty marker.**  Local confluence of the combined saturated rewrite
(`SaturatedTwoCellLocallyConfluent`) is FALSE — NOT for any adjunction/triangle reason (the triangle-layer
critical pairs all join), but because the combined rewrite INHERITS the free `interchange × whiskerRightVcomp`
critical pair via `ofFree`, the Godement/Eckmann–Hilton non-confluence `FreeTwoCellConfluence` identified as
non-joining (the two 2×2-pasting normal forms differ in their whiskering 1-cells, which no rule rewrites; the
snake/identity
completions cannot repair it).  Hence `saturatedTwoCellStep_isConfluent` is an HONEST Newman reduction whose
hypothesis is undischargeable: the convergent route is confluence MODULO the interchange equation (the
string/pasting-diagram quotient — the `fxMode_hasInterchangeAndWhiskerFunctoriality` floor).  So the residual to
a saturated monotone-map canonicalization, and to the keystone, is EXACTLY that pre-existing interchange floor,
not anything triangle-specific.  `fxMode_hasDecidableTwoCellEquality` / `fxMode_hasModeRelativeConvDecision` /
`fxMode_hasSaturatedTwoCellMonotoneMapDecision` / `fxMode_hasAdjunctionTriangleSaturation` are left for the
parent.  `= false`. -/
def fxMode_hasSaturatedTwoCellConfluence : Bool := false

end FX1Poly.Tier0
