import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.AdjunctionTriangleObstruction
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.WhiskerFunctoriality

/-! # mode-9 — the SATURATED adjunction's 2-cell convertibility + the monotone-map canonical shadow

`AdjunctionTriangleObstruction` proved RIGOROUSLY that the seed adjunction's TRIANGLE IDENTITIES are GENUINE new
relations the free 3-polygraph does NOT contain (`adjunctionSeedLeftSnake_not_conv_id` : the left snake, generator
count 2, is provably NOT `TwoCellConv` to `id_L`, count 0).  A walking adjunction WITHOUT its triangles is not an
adjunction; the genuine mode theory wants the SATURATED 2-cells — the free strict-2-category convertibility
(`TwoCellConvFull`) plus the two snake equations.  This file ships that saturated convertibility and the content a
decision rests on.

## Why saturation is the right move (the Schanuel–Street picture)

The free 2-category's 2-cell word problem cannot be decided by orienting the Godement / interchange steps: a
prior pass machine-checked `adjunctionCounitGodementStep` — a CONTRACTING counit/counit transposition whose both
endpoints are rewrite-normal and whose reverse is not Godement-shaped — so NO strongly-normalizing sub-relation of
Godement is complete (`FreeTwoCellOrientedReducer`).  The free system also has "bubbles" — the snakes are
non-trivial `L ⇒ L` 2-cells (the cup-cap zig-zags).  The TRIANGLE IDENTITIES are exactly what resolves this: they
STRAIGHTEN the zig-zags (collapse the snake bubbles to identities), the counit obstruction dissolves, and the
saturated hom-categories collapse to the augmented simplex category Δ₊ (Schanuel–Street, "The free adjunction"),
where 2-cells are MONOTONE MAPS between finite ordinals and equality is decidable by list comparison.

## What this file ships (each piece zero-axiom)

  * ★ **`SaturatedTwoCellConv`** — the saturated 2-cell convertibility at the seed: the completed free-strict-
    2-category convertibility `TwoCellConvFull` (embedded by `ofFull`), PLUS the two TRIANGLE IDENTITIES
    (`triangleLeft` : `adjunctionSeedLeftSnake ≈ id_L`, `triangleRight` : `adjunctionSeedRightSnake ≈ id_R`),
    PLUS the four one-hole CONGRUENCES (so the triangle fires under any vcomp / whisker context — a genuine
    congruence), PLUS `refl` / `symm` / `trans`.
  * ★ **`triangleLeftHolds` / `triangleRightHolds`** — the snake equations hold in the saturated relation (the
    witnesses the keystone's saturation flag flip consumes).
  * ★ **the BUBBLE COLLAPSE crux** (`saturatedCollapsesLeftBubble` + `leftSnakeSaturatedButNotFree`): the left
    snake is `SaturatedTwoCellConv` to `id_L` YET provably NOT `TwoCellConv` to it — so the saturation is
    GENUINELY stronger exactly on the zig-zag the free system could not straighten.  Same for the right snake.
    This is the rigorous form of "the triangles collapse the bubbles".
  * the `TwoCellConv` / `TwoCellConvFull` embeddings (`ofConv`) so all the free-system reasoning lifts.

Raw Lean 4 + Init; every declaration here is `propext`/`Quot.sound`/`Classical`/`sorry`/`native_decide`/`omega`-
free (the relation is an inductive `Prop`; the witnesses are constructors; the bubble crux pairs a constructor
with the imported obstruction theorem).  Per-declaration `#assert_no_axioms` gated in the audit twin. -/

namespace FX1Poly.Polygraph

/-! ## The saturated 2-cell convertibility -/

/-- ★ The **saturated 2-cell convertibility** of the seed walking adjunction: the completed free-strict-
2-category convertibility (`TwoCellConvFull`, embedded by `ofFull`) augmented with the two TRIANGLE IDENTITIES of
the seed adjunction `μ_affine ⊣ μ_affine†` as generating equations, made a genuine congruence by the four
one-hole congruence closures.  Two free 2-cells are equal AS 2-cells of the SATURATED (genuine) adjunction
2-category exactly when they are `SaturatedTwoCellConv`-related.

The two triangle generators are the content the free 3-polygraph lacks (`AdjunctionTriangleObstruction`): the
snakes have generator count 2 but the identities count 0, so no structural 3-cell relates them — they MUST be
posited, and they are exactly the snake equations a genuine adjunction satisfies. -/
inductive SaturatedTwoCellConv :
    {sourceMode targetMode : AdjunctionMode} →
    {sourcePath targetPath : ModalityPath adjunctionGraph sourceMode targetMode} →
    RawTwoCellExpr adjunctionModeSignature sourcePath targetPath →
    RawTwoCellExpr adjunctionModeSignature sourcePath targetPath → Prop where
  /-- Embed the completed free-strict-2-category convertibility (structural laws + interchange + whisker
  functoriality + congruence closure). -/
  | ofFull {sourceMode targetMode : AdjunctionMode}
      {sourcePath targetPath : ModalityPath adjunctionGraph sourceMode targetMode}
      {cellAlpha cellBeta : RawTwoCellExpr adjunctionModeSignature sourcePath targetPath} :
      TwoCellConvFull adjunctionModeSignature cellAlpha cellBeta →
      SaturatedTwoCellConv cellAlpha cellBeta
  /-- The **left triangle identity** `(η ▷ L) ⊟ (L ◁ ε) ≈ id_L` — the left snake collapses to the identity. -/
  | triangleLeft :
      SaturatedTwoCellConv adjunctionSeedLeftSnake
        (RawTwoCellExpr.id (signature := adjunctionModeSignature)
          (singletonModalityPath AdjunctionModality.left))
  /-- The **right triangle identity** `(R ◁ η) ⊟ (ε ▷ R) ≈ id_R` — the right snake collapses to the identity. -/
  | triangleRight :
      SaturatedTwoCellConv adjunctionSeedRightSnake
        (RawTwoCellExpr.id (signature := adjunctionModeSignature)
          (singletonModalityPath AdjunctionModality.right))
  /-- Congruence in the LEFT factor of a vertical composite (so the triangle fires under a following composite). -/
  | vcompCongrLeft {sourceMode targetMode : AdjunctionMode}
      {oneCellF oneCellG oneCellH : ModalityPath adjunctionGraph sourceMode targetMode}
      {cellAlpha cellAlpha' : RawTwoCellExpr adjunctionModeSignature oneCellF oneCellG}
      (cellBeta : RawTwoCellExpr adjunctionModeSignature oneCellG oneCellH) :
      SaturatedTwoCellConv cellAlpha cellAlpha' →
      SaturatedTwoCellConv (RawTwoCellExpr.vcomp cellAlpha cellBeta)
        (RawTwoCellExpr.vcomp cellAlpha' cellBeta)
  /-- Congruence in the RIGHT factor of a vertical composite. -/
  | vcompCongrRight {sourceMode targetMode : AdjunctionMode}
      {oneCellF oneCellG oneCellH : ModalityPath adjunctionGraph sourceMode targetMode}
      (cellAlpha : RawTwoCellExpr adjunctionModeSignature oneCellF oneCellG)
      {cellBeta cellBeta' : RawTwoCellExpr adjunctionModeSignature oneCellG oneCellH} :
      SaturatedTwoCellConv cellBeta cellBeta' →
      SaturatedTwoCellConv (RawTwoCellExpr.vcomp cellAlpha cellBeta)
        (RawTwoCellExpr.vcomp cellAlpha cellBeta')
  /-- Congruence under a left whiskering (so the triangle fires whiskered by a 1-cell). -/
  | whiskerLeftCongr {sourceMode middleMode targetMode : AdjunctionMode}
      (oneCell : ModalityPath adjunctionGraph sourceMode middleMode)
      {oneCellG oneCellH : ModalityPath adjunctionGraph middleMode targetMode}
      {cellBeta cellBeta' : RawTwoCellExpr adjunctionModeSignature oneCellG oneCellH} :
      SaturatedTwoCellConv cellBeta cellBeta' →
      SaturatedTwoCellConv (RawTwoCellExpr.whiskerLeft oneCell cellBeta)
        (RawTwoCellExpr.whiskerLeft oneCell cellBeta')
  /-- Congruence under a right whiskering. -/
  | whiskerRightCongr {sourceMode middleMode targetMode : AdjunctionMode}
      {oneCellF oneCellG : ModalityPath adjunctionGraph sourceMode middleMode}
      (oneCell : ModalityPath adjunctionGraph middleMode targetMode)
      {cellAlpha cellAlpha' : RawTwoCellExpr adjunctionModeSignature oneCellF oneCellG} :
      SaturatedTwoCellConv cellAlpha cellAlpha' →
      SaturatedTwoCellConv (RawTwoCellExpr.whiskerRight oneCell cellAlpha)
        (RawTwoCellExpr.whiskerRight oneCell cellAlpha')
  /-- ★ The **disjoint-whisker EXCHANGE** `(leftWhisker ◁ body) ▷ rightWhisker ≈ leftWhisker ◁ (body ▷
  rightWhisker)` — a LEFT whisker by `leftWhisker` and a RIGHT whisker by `rightWhisker` (over DISJOINT 1-cells)
  COMMUTE.  This is a genuine STRICT-2-CATEGORY coherence (horizontal composition is associative on 2-cells; it
  would most naturally live in `TwoCellConvFull` as the missing companion to `whiskerLeftComp` / `whiskerRightComp`),
  and its absence from the free presentation is exactly the single-atom case of the open spine-trace reconstruction
  (`FreeTwoCellWhiskerReconstruction`'s `AdjunctionNfTraceReconstructionFull`).  It is posited HERE, like the
  triangle identities, to complete the saturated relation.  SOUNDNESS is preserved: the two bracketings have the
  SAME spine (`monotoneMapOf` reads only the spine — `monotoneMapOf_congr_of_spine_eq`), so the augmented-simplex
  decision still factors through it.  Heterogeneous (`composePath` associativity), threaded through `castBoundary`. -/
  | whiskerExchange {sourceMode middleSourceMode middleTargetMode targetMode : AdjunctionMode}
      (leftWhisker : ModalityPath adjunctionGraph sourceMode middleSourceMode)
      {bodyDom bodyCod : ModalityPath adjunctionGraph middleSourceMode middleTargetMode}
      (rightWhisker : ModalityPath adjunctionGraph middleTargetMode targetMode)
      (body : RawTwoCellExpr adjunctionModeSignature bodyDom bodyCod) :
      SaturatedTwoCellConv
        (RawTwoCellExpr.whiskerLeft leftWhisker (RawTwoCellExpr.whiskerRight rightWhisker body))
        (RawTwoCellExpr.castBoundary (composePath_assoc leftWhisker bodyDom rightWhisker)
          (composePath_assoc leftWhisker bodyCod rightWhisker)
          (RawTwoCellExpr.whiskerRight rightWhisker (RawTwoCellExpr.whiskerLeft leftWhisker body)))
  /-- Reflexivity. -/
  | refl {sourceMode targetMode : AdjunctionMode}
      {sourcePath targetPath : ModalityPath adjunctionGraph sourceMode targetMode}
      (cell : RawTwoCellExpr adjunctionModeSignature sourcePath targetPath) :
      SaturatedTwoCellConv cell cell
  /-- Symmetry. -/
  | symm {sourceMode targetMode : AdjunctionMode}
      {sourcePath targetPath : ModalityPath adjunctionGraph sourceMode targetMode}
      {cellAlpha cellBeta : RawTwoCellExpr adjunctionModeSignature sourcePath targetPath} :
      SaturatedTwoCellConv cellAlpha cellBeta → SaturatedTwoCellConv cellBeta cellAlpha
  /-- Transitivity. -/
  | trans {sourceMode targetMode : AdjunctionMode}
      {sourcePath targetPath : ModalityPath adjunctionGraph sourceMode targetMode}
      {cellAlpha cellBeta cellGamma : RawTwoCellExpr adjunctionModeSignature sourcePath targetPath} :
      SaturatedTwoCellConv cellAlpha cellBeta → SaturatedTwoCellConv cellBeta cellGamma →
      SaturatedTwoCellConv cellAlpha cellGamma

/-! ## Embeddings: every free-system convertibility lifts to the saturated relation -/

/-- The free `TwoCellConv` (structural laws + interchange) lifts to the saturated relation (through
`TwoCellConvFull.ofConv` then `ofFull`). -/
theorem SaturatedTwoCellConv.ofConv {sourceMode targetMode : AdjunctionMode}
    {sourcePath targetPath : ModalityPath adjunctionGraph sourceMode targetMode}
    {cellAlpha cellBeta : RawTwoCellExpr adjunctionModeSignature sourcePath targetPath}
    (conv : TwoCellConv adjunctionModeSignature cellAlpha cellBeta) :
    SaturatedTwoCellConv cellAlpha cellBeta :=
  SaturatedTwoCellConv.ofFull (TwoCellConvFull.ofConv conv)

/-! ## The triangle witnesses (the saturation-flag content) -/

/-- ★ **The left triangle identity holds in the saturated relation** — `(η ▷ L) ⊟ (L ◁ ε) ≈ id_L`.  The witness
the keystone's `fxMode_hasSaturatedAdjunction` flag flip consumes. -/
theorem triangleLeftHolds :
    SaturatedTwoCellConv adjunctionSeedLeftSnake
      (RawTwoCellExpr.id (signature := adjunctionModeSignature)
        (singletonModalityPath AdjunctionModality.left)) :=
  SaturatedTwoCellConv.triangleLeft

/-- ★ **The right triangle identity holds in the saturated relation** — `(R ◁ η) ⊟ (ε ▷ R) ≈ id_R`. -/
theorem triangleRightHolds :
    SaturatedTwoCellConv adjunctionSeedRightSnake
      (RawTwoCellExpr.id (signature := adjunctionModeSignature)
        (singletonModalityPath AdjunctionModality.right)) :=
  SaturatedTwoCellConv.triangleRight

/-! ## ★ The bubble-collapse crux: the triangles straighten the zig-zags the free system could not -/

/-- ★ **The left snake bubble collapses to the identity** in the saturated relation (`= triangleLeftHolds`,
named for the crux). -/
theorem saturatedCollapsesLeftBubble :
    SaturatedTwoCellConv adjunctionSeedLeftSnake
      (RawTwoCellExpr.id (signature := adjunctionModeSignature)
        (singletonModalityPath AdjunctionModality.left)) :=
  SaturatedTwoCellConv.triangleLeft

/-- ★ **The right snake bubble collapses to the identity** in the saturated relation. -/
theorem saturatedCollapsesRightBubble :
    SaturatedTwoCellConv adjunctionSeedRightSnake
      (RawTwoCellExpr.id (signature := adjunctionModeSignature)
        (singletonModalityPath AdjunctionModality.right)) :=
  SaturatedTwoCellConv.triangleRight

/-- ★★ **The saturation is GENUINELY stronger on the left bubble.**  The left snake is `SaturatedTwoCellConv` to
`id_L` (the triangle) YET provably NOT `TwoCellConv` to it (the free obstruction
`adjunctionSeedLeftSnake_not_conv_id` : the snake fires two generators, the identity none, and generator count is
a free-conversion invariant).  So the triangle identity is a real new relation, and the saturation straightens
exactly the zig-zag bubble the free 3-polygraph leaves standing. -/
theorem leftSnakeSaturatedButNotFree :
    SaturatedTwoCellConv adjunctionSeedLeftSnake
        (RawTwoCellExpr.id (signature := adjunctionModeSignature)
          (singletonModalityPath AdjunctionModality.left))
      ∧ ¬ TwoCellConv adjunctionModeSignature adjunctionSeedLeftSnake
        (RawTwoCellExpr.id (signature := adjunctionModeSignature)
          (singletonModalityPath AdjunctionModality.left)) :=
  ⟨SaturatedTwoCellConv.triangleLeft, adjunctionSeedLeftSnake_not_conv_id⟩

/-- ★★ **The saturation is GENUINELY stronger on the right bubble** — the dual statement. -/
theorem rightSnakeSaturatedButNotFree :
    SaturatedTwoCellConv adjunctionSeedRightSnake
        (RawTwoCellExpr.id (signature := adjunctionModeSignature)
          (singletonModalityPath AdjunctionModality.right))
      ∧ ¬ TwoCellConv adjunctionModeSignature adjunctionSeedRightSnake
        (RawTwoCellExpr.id (signature := adjunctionModeSignature)
          (singletonModalityPath AdjunctionModality.right)) :=
  ⟨SaturatedTwoCellConv.triangleRight, adjunctionSeedRightSnake_not_conv_id⟩

/-- Smoke: the triangle fires UNDER a whisker context — `R ◁ (left snake) ≈ R ◁ id_L` — exercising the
congruence closure together with the triangle generator.  (The two sides have the same boundary `R L ⇒ R L`.) -/
theorem leftSnakeWhiskeredCollapses :
    SaturatedTwoCellConv
      (RawTwoCellExpr.whiskerLeft (signature := adjunctionModeSignature)
        (singletonModalityPath AdjunctionModality.right) adjunctionSeedLeftSnake)
      (RawTwoCellExpr.whiskerLeft (signature := adjunctionModeSignature)
        (singletonModalityPath AdjunctionModality.right)
        (RawTwoCellExpr.id (signature := adjunctionModeSignature)
          (singletonModalityPath AdjunctionModality.left))) :=
  SaturatedTwoCellConv.whiskerLeftCongr _ SaturatedTwoCellConv.triangleLeft

/-- Smoke: TWO stacked left snakes collapse to `id_L` — `(left snake) ⊟ (left snake) ≈ id_L`.  Collapse the
outer snake by the left triangle (`vcompCongrLeft`), drop the resulting `id_L ⊟ snake` (free `vcompIdLeft`), then
collapse the remaining snake (`triangleLeft`).  Iterated zig-zag straightening: the saturated relation removes a
whole stack of bubbles, not just one. -/
theorem leftDoubleBubbleCollapses :
    SaturatedTwoCellConv
      (RawTwoCellExpr.vcomp adjunctionSeedLeftSnake adjunctionSeedLeftSnake)
      (RawTwoCellExpr.id (signature := adjunctionModeSignature)
        (singletonModalityPath AdjunctionModality.left)) :=
  SaturatedTwoCellConv.trans
    (SaturatedTwoCellConv.vcompCongrLeft adjunctionSeedLeftSnake SaturatedTwoCellConv.triangleLeft)
    (SaturatedTwoCellConv.trans
      (SaturatedTwoCellConv.ofConv (TwoCellConv.ofStep (TwoCellStep.vcompIdLeft adjunctionSeedLeftSnake)))
      SaturatedTwoCellConv.triangleLeft)

/-! ## The Knuth–Bendix snake-prefix completions are DERIVED saturated convertibilities

`AdjunctionTriangleObstruction` adjoined the SNAKE-PREFIX completion rules
`(η▷L)⊟((ε◁L)⊟rest) ⤳ rest` (`leftSnakePrefix`) and its right dual to resolve the `vcompAssoc` critical pair of
the bare triangle.  Those rules were posited as rewrite generators; here they are PROVED to be theorems of the
saturated convertibility — `vcompAssoc` (free) re-associates the prefix into `(snake ⊟ rest)`, the triangle
collapses the snake, and `vcompIdLeft` (free) drops the resulting `id ⊟ rest`.  So the KB completion adds no new
identifications beyond `SaturatedTwoCellConv`: the saturated rewrite is SOUND for it (`ofLeftReduces` below). -/

/-- ★ **The left snake-prefix completion is a derived saturated convertibility.**
`(η▷L) ⊟ ((ε◁L) ⊟ rest) ≈ rest`: re-associate (free `vcompAssoc`, reversed) to `(snake ⊟ rest)`, collapse the
snake by the left triangle (`vcompCongrLeft`), then drop `id_L ⊟ rest` by free `vcompIdLeft`. -/
theorem leftSnakePrefixHolds
    {targetPath : ModalityPath adjunctionGraph AdjunctionMode.base AdjunctionMode.tip}
    (rest : RawTwoCellExpr adjunctionModeSignature
      (singletonModalityPath AdjunctionModality.left) targetPath) :
    SaturatedTwoCellConv
      (RawTwoCellExpr.vcomp
        (RawTwoCellExpr.whiskerRight (signature := adjunctionModeSignature)
          (singletonModalityPath AdjunctionModality.left) adjunctionUnitTwoCell)
        (RawTwoCellExpr.vcomp
          (RawTwoCellExpr.whiskerLeft (signature := adjunctionModeSignature)
            (singletonModalityPath AdjunctionModality.left) adjunctionCounitTwoCell)
          rest))
      rest :=
  SaturatedTwoCellConv.trans
    (SaturatedTwoCellConv.symm
      (SaturatedTwoCellConv.ofConv (TwoCellConv.ofStep
        (TwoCellStep.vcompAssoc
          (RawTwoCellExpr.whiskerRight (signature := adjunctionModeSignature)
            (singletonModalityPath AdjunctionModality.left) adjunctionUnitTwoCell)
          (RawTwoCellExpr.whiskerLeft (signature := adjunctionModeSignature)
            (singletonModalityPath AdjunctionModality.left) adjunctionCounitTwoCell)
          rest))))
    (SaturatedTwoCellConv.trans
      (SaturatedTwoCellConv.vcompCongrLeft rest SaturatedTwoCellConv.triangleLeft)
      (SaturatedTwoCellConv.ofConv (TwoCellConv.ofStep (TwoCellStep.vcompIdLeft rest))))

/-- ★ **The right snake-prefix completion is a derived saturated convertibility** — the dual. -/
theorem rightSnakePrefixHolds
    {targetPath : ModalityPath adjunctionGraph AdjunctionMode.tip AdjunctionMode.base}
    (rest : RawTwoCellExpr adjunctionModeSignature
      (singletonModalityPath AdjunctionModality.right) targetPath) :
    SaturatedTwoCellConv
      (RawTwoCellExpr.vcomp
        (RawTwoCellExpr.whiskerLeft (signature := adjunctionModeSignature)
          (singletonModalityPath AdjunctionModality.right) adjunctionUnitTwoCell)
        (RawTwoCellExpr.vcomp
          (RawTwoCellExpr.whiskerRight (signature := adjunctionModeSignature)
            (singletonModalityPath AdjunctionModality.right) adjunctionCounitTwoCell)
          rest))
      rest :=
  SaturatedTwoCellConv.trans
    (SaturatedTwoCellConv.symm
      (SaturatedTwoCellConv.ofConv (TwoCellConv.ofStep
        (TwoCellStep.vcompAssoc
          (RawTwoCellExpr.whiskerLeft (signature := adjunctionModeSignature)
            (singletonModalityPath AdjunctionModality.right) adjunctionUnitTwoCell)
          (RawTwoCellExpr.whiskerRight (signature := adjunctionModeSignature)
            (singletonModalityPath AdjunctionModality.right) adjunctionCounitTwoCell)
          rest))))
    (SaturatedTwoCellConv.trans
      (SaturatedTwoCellConv.vcompCongrLeft rest SaturatedTwoCellConv.triangleRight)
      (SaturatedTwoCellConv.ofConv (TwoCellConv.ofStep (TwoCellStep.vcompIdLeft rest))))

/-- ★ **One left-saturated rewrite step is a saturated convertibility.**  `ofFree` lifts a free 3-cell
(`ofConv ∘ ofStep`); `leftBareSnake` is the left triangle; `leftSnakePrefix` is the derived `leftSnakePrefixHolds`;
the left-factor congruence threads inductively.  So `AdjunctionLeftSaturatedStep ⊆ SaturatedTwoCellConv`. -/
theorem AdjunctionLeftSaturatedStep.toSaturatedConv {sourceMode targetMode : AdjunctionMode}
    {sourcePath targetPath : ModalityPath adjunctionGraph sourceMode targetMode}
    {cellA cellB : RawTwoCellExpr adjunctionModeSignature sourcePath targetPath}
    (step : AdjunctionLeftSaturatedStep cellA cellB) : SaturatedTwoCellConv cellA cellB := by
  induction step with
  | ofFree freeStep => exact SaturatedTwoCellConv.ofConv (TwoCellConv.ofStep freeStep)
  | leftBareSnake => exact SaturatedTwoCellConv.triangleLeft
  | leftSnakePrefix rest => exact leftSnakePrefixHolds rest
  | vcompCongrLeft cellBeta _ inductionHypothesis =>
      exact SaturatedTwoCellConv.vcompCongrLeft cellBeta inductionHypothesis

/-- ★ **The whole left-saturated reduction is a saturated convertibility** — the KB-completed walking-adjunction
rewrite (with its critical-pair joining and generator-count termination, `AdjunctionTriangleObstruction`) computes
WITHIN `SaturatedTwoCellConv`.  Chain the single-step soundness through `trans`. -/
theorem AdjunctionLeftSaturatedReduces.toSaturatedConv {sourceMode targetMode : AdjunctionMode}
    {sourcePath targetPath : ModalityPath adjunctionGraph sourceMode targetMode}
    {cellA cellB : RawTwoCellExpr adjunctionModeSignature sourcePath targetPath}
    (reduction : AdjunctionLeftSaturatedReduces cellA cellB) : SaturatedTwoCellConv cellA cellB := by
  induction reduction with
  | refl cell => exact SaturatedTwoCellConv.refl cell
  | head firstStep _ inductionHypothesis =>
      exact SaturatedTwoCellConv.trans firstStep.toSaturatedConv inductionHypothesis

/-- ★ **One right-saturated rewrite step is a saturated convertibility** — the dual. -/
theorem AdjunctionRightSaturatedStep.toSaturatedConv {sourceMode targetMode : AdjunctionMode}
    {sourcePath targetPath : ModalityPath adjunctionGraph sourceMode targetMode}
    {cellA cellB : RawTwoCellExpr adjunctionModeSignature sourcePath targetPath}
    (step : AdjunctionRightSaturatedStep cellA cellB) : SaturatedTwoCellConv cellA cellB := by
  induction step with
  | ofFree freeStep => exact SaturatedTwoCellConv.ofConv (TwoCellConv.ofStep freeStep)
  | rightBareSnake => exact SaturatedTwoCellConv.triangleRight
  | rightSnakePrefix rest => exact rightSnakePrefixHolds rest
  | vcompCongrLeft cellBeta _ inductionHypothesis =>
      exact SaturatedTwoCellConv.vcompCongrLeft cellBeta inductionHypothesis

/-- ★ **The whole right-saturated reduction is a saturated convertibility** — the dual. -/
theorem AdjunctionRightSaturatedReduces.toSaturatedConv {sourceMode targetMode : AdjunctionMode}
    {sourcePath targetPath : ModalityPath adjunctionGraph sourceMode targetMode}
    {cellA cellB : RawTwoCellExpr adjunctionModeSignature sourcePath targetPath}
    (reduction : AdjunctionRightSaturatedReduces cellA cellB) : SaturatedTwoCellConv cellA cellB := by
  induction reduction with
  | refl cell => exact SaturatedTwoCellConv.refl cell
  | head firstStep _ inductionHypothesis =>
      exact SaturatedTwoCellConv.trans firstStep.toSaturatedConv inductionHypothesis

/-! ## ★ The cheap free distinguishers are DEAD under saturation

The free 2-cell word problem had a CHEAP sound NO-direction: the generator count and the spine LENGTH are
`TwoCellConv` invariants (`ComputadWordProblem` / `FreeTwoCellSpine`), so unequal counts ⟹ not convertible.  Under
saturation that distinguisher COLLAPSES — the left triangle equates the snake (count 2) with `id_L` (count 0).
So the saturated decision cannot reuse the free count/length NO-direction; the ONLY surviving invariant that
distinguishes parallel 2-cells is the full Schanuel–Street MONOTONE MAP (the residual below).  This is a genuine
structural finding, not a gap: the bubbles the count once detected are now genuinely identified. -/

/-- ★ **Generator count is NOT a saturated-convertibility invariant.**  The left triangle is a counterexample:
`adjunctionSeedLeftSnake` (count 2) is `SaturatedTwoCellConv` to `id_L` (count 0).  Hence the free word-length
distinguisher (`TwoCellConv.not_of_generatorCount_ne`) does NOT transfer to the saturated relation — the cheap
NO-direction is dead, and a faithful decision needs the finer monotone-map invariant. -/
theorem saturatedConv_doesNotPreserveGeneratorCount :
    ¬ (∀ {sourceMode targetMode : AdjunctionMode}
        {sourcePath targetPath : ModalityPath adjunctionGraph sourceMode targetMode}
        (cellA cellB : RawTwoCellExpr adjunctionModeSignature sourcePath targetPath),
        SaturatedTwoCellConv cellA cellB → cellA.generatorCount = cellB.generatorCount) := by
  intro preserves
  exact Nat.noConfusion (preserves adjunctionSeedLeftSnake _ SaturatedTwoCellConv.triangleLeft)

/-! ## The Schanuel–Street monotone-map canonical form + the decision modulo it

By Schanuel–Street ("The free adjunction"), the SATURATED walking adjunction's hom-categories are the augmented
simplex category Δ₊: a 2-cell between a parallel pair of 1-cells is a MONOTONE MAP between finite ordinals, and
two 2-cells are saturated-equal exactly when their monotone maps agree.  A monotone map is encoded as the
weakly-increasing `List Nat` of its values, whose equality is decidable by list comparison (`List Nat`'s
`DecidableEq`, zero-axiom).  This is the canonical form the decision compares.

The CANONICALIZATION itself — the map `monotoneMapOf` together with its two invariance directions (SOUND: the
saturated generators, the triangles included, preserve it; COMPLETE: equal maps are saturated-convertible) — is
the genuine remaining Schanuel–Street content.  It is packaged here as the residual the decision consumes; the
decision assembly around it (the NO and YES branches) is shipped, zero-axiom. -/

/-- The **Schanuel–Street monotone-map canonical form**: a 2-cell of the saturated walking adjunction is a
monotone map between finite ordinals, encoded as the weakly-increasing `List Nat` of its values.  Equality is
decidable by list comparison (`List Nat`'s zero-axiom `DecidableEq`). -/
abbrev SaturatedCanonicalForm : Type := List Nat

/-- The seed's **saturated canonicalization** — the Schanuel–Street monotone-map normal form packaged with its two
invariance directions: `mapEqOfConv` (SOUND — saturated-convertible cells have equal maps, the triangles
collapsing the bubbles) and `convOfMapEq` (COMPLETE — equal maps reconstruct a saturated convertibility).  This is
the genuine remaining content ("the free adjunction" theorem mechanized); the decision below consumes it. -/
structure AdjunctionSaturatedCanonicalization where
  /-- The monotone-map normal form of a saturated 2-cell. -/
  monotoneMapOf : {sourceMode targetMode : AdjunctionMode} →
    {sourcePath targetPath : ModalityPath adjunctionGraph sourceMode targetMode} →
    RawTwoCellExpr adjunctionModeSignature sourcePath targetPath → SaturatedCanonicalForm
  /-- SOUNDNESS: saturated-convertible cells have equal monotone maps (the triangles' bubble collapse preserves
  the map — the NO-direction of the decision). -/
  mapEqOfConv : {sourceMode targetMode : AdjunctionMode} →
    {sourcePath targetPath : ModalityPath adjunctionGraph sourceMode targetMode} →
    {cellA cellB : RawTwoCellExpr adjunctionModeSignature sourcePath targetPath} →
    SaturatedTwoCellConv cellA cellB → monotoneMapOf cellA = monotoneMapOf cellB
  /-- COMPLETENESS: cells with equal monotone maps are saturated-convertible (the reconstruction — the
  YES-direction of the decision). -/
  convOfMapEq : {sourceMode targetMode : AdjunctionMode} →
    {sourcePath targetPath : ModalityPath adjunctionGraph sourceMode targetMode} →
    {cellA cellB : RawTwoCellExpr adjunctionModeSignature sourcePath targetPath} →
    monotoneMapOf cellA = monotoneMapOf cellB → SaturatedTwoCellConv cellA cellB

/-- ★ **Decide saturated convertibility via the monotone map.**  Given the canonicalization, compare the two
cells' monotone maps by list equality: equal maps ⟹ `isTrue` (via `convOfMapEq`); unequal maps ⟹ `isFalse`,
because `mapEqOfConv` (soundness) would force the maps equal.  Both branches are discharged from the
canonicalization's two directions — the decision assembly is complete. -/
def adjunctionDecideSaturatedConvViaMonotoneMap (canon : AdjunctionSaturatedCanonicalization)
    {sourceMode targetMode : AdjunctionMode}
    {sourcePath targetPath : ModalityPath adjunctionGraph sourceMode targetMode}
    (cellA cellB : RawTwoCellExpr adjunctionModeSignature sourcePath targetPath) :
    Decidable (SaturatedTwoCellConv cellA cellB) :=
  match (inferInstance : Decidable (canon.monotoneMapOf cellA = canon.monotoneMapOf cellB)) with
  | isTrue mapsEqual => isTrue (canon.convOfMapEq mapsEqual)
  | isFalse mapsDiffer => isFalse (fun conv => mapsDiffer (canon.mapEqOfConv conv))

/-- The seed's **saturated 2-cell word-problem interface**: saturated convertibility is decidable on every
parallel pair of free 2-cells.  The saturated analog of `mode-3`'s `DecidableTwoCellConvFor`. -/
abbrev DecidableSaturatedTwoCellConvFor : Type :=
  {sourceMode targetMode : AdjunctionMode} →
  {sourcePath targetPath : ModalityPath adjunctionGraph sourceMode targetMode} →
  (cellA cellB : RawTwoCellExpr adjunctionModeSignature sourcePath targetPath) →
  Decidable (SaturatedTwoCellConv cellA cellB)

/-- ★ **The seed's saturated 2-cell word problem, modulo the canonicalization.**  Supplying the Schanuel–Street
monotone-map canonicalization (the residual) inhabits the full saturated decision interface — it decides EVERY
parallel pair, the bubbles collapsed.  This is the saturated analog of
`adjunctionTwoCellWordProblemModuloTraceRoute`, with the residual sharpened from the free trace word problem to
the (strictly more collapsed) augmented-simplex monotone map. -/
@[reducible] def adjunctionSaturatedWordProblemModuloCanonicalization
    (canon : AdjunctionSaturatedCanonicalization) : DecidableSaturatedTwoCellConvFor :=
  fun cellA cellB => adjunctionDecideSaturatedConvViaMonotoneMap canon cellA cellB

/-! ## Smoke: the decision computes on the bubble pair -/

/-- Smoke: given any canonicalization, the decision on `(adjunctionSeedLeftSnake, id_L)` answers `isTrue` — the
monotone maps agree (both straighten to the identity map) because the snake collapses to `id_L` by the left
triangle, which `mapEqOfConv` honours.  The decision sees the bubble collapse. -/
theorem adjunctionDecideSaturated_leftSnake_isTrue (canon : AdjunctionSaturatedCanonicalization) :
    canon.monotoneMapOf adjunctionSeedLeftSnake
      = canon.monotoneMapOf (RawTwoCellExpr.id (signature := adjunctionModeSignature)
          (singletonModalityPath AdjunctionModality.left)) :=
  canon.mapEqOfConv SaturatedTwoCellConv.triangleLeft

/-! ## Honesty markers -/

/-- **ESTABLISHED.**  The SATURATED adjunction's 2-cell convertibility (`SaturatedTwoCellConv`) — the completed
free-strict-2-category convertibility plus the two TRIANGLE IDENTITIES as a congruence — is shipped, and the
triangles GENUINELY collapse the bubbles the free system could not (`leftSnakeSaturatedButNotFree` /
`rightSnakeSaturatedButNotFree`: the snakes are saturated-convertible to the identities yet provably NOT
`TwoCellConv` to them).  The KB-completed walking-adjunction rewrite (`AdjunctionTriangleObstruction`) is SOUND
for it (`AdjunctionLeftSaturatedReduces.toSaturatedConv`).  `= true`. -/
def fxMode_hasSaturatedTwoCellConvRelation : Bool := true

/-- **Honesty marker.**  The full saturated DECISION is shipped MODULO the Schanuel–Street monotone-map
canonicalization (`AdjunctionSaturatedCanonicalization`): the decision assembly
(`adjunctionDecideSaturatedConvViaMonotoneMap`) is complete and zero-axiom, but its residual — the map
`monotoneMapOf` with SOUNDNESS (`mapEqOfConv`: the triangles preserve the augmented-simplex map) and COMPLETENESS
(`convOfMapEq`: equal maps reconstruct a convertibility) — is the genuine remaining "free adjunction" content.
Unlike the free word problem, the saturated relation has NO cheap NO-direction
(`saturatedConv_doesNotPreserveGeneratorCount`: generator count is no longer an invariant), so BOTH directions of
the canonicalization are owed.  `fxMode_hasDecidableTwoCellEquality` / `fxMode_hasModeRelativeConvDecision` /
`fxMode_hasAdjunctionTriangleSaturation` are left for the parent to set.  `= false`. -/
def fxMode_hasSaturatedTwoCellMonotoneMapDecision : Bool := false

end FX1Poly.Polygraph
