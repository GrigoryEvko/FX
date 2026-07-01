import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.Confluence

/-! # mode-3 floor — the INTERCHANGE-FREE fragment of the `TwoCellStep` 3-polygraph

`FreeTwoCellConfluence` established (honestly) that the full `TwoCellStep` is NOT confluent: the
`interchange × whiskerRightVcomp` critical pair on `hcomp(vcomp α α')(vcomp β β')` diverges to two distinct
terminal forms (Godement/Eckmann–Hilton), so `TwoCellLocallyConfluent` is FALSE and no base-rule rewriting
flips `fxMode_hasConvergentThreeCellSystem`. The CORRECT route to the fib-3 keystone (decidable 2-cell equality
for the affine walking-adjunction) is **confluence MODULO the interchange equation**: orient only the eleven
STRUCTURAL laws, withdraw `interchange` from the oriented set, and let interchange live as the modulo-E
equivalence on the structural normal forms (the string/pasting-diagram quotient).

This file ships the first brick of that route: the **interchange-free fragment** `TwoCellStepInterchangeFree`
— exactly the eleven structural 3-cells of `TwoCellStep` (identity-drop, vertical associativity,
whisker-functoriality, and the four one-hole congruences) with the Godement `interchange` step removed — and
proves it is **strongly normalizing**.

  ★ `twoCellStepInterchangeFree_isStronglyNormalizing` — every free 2-cell is `Acc`-essible under the flipped
    interchange-free rewrite.

The termination proof is FREE: every interchange-free step embeds into a `TwoCellStep` step
(`twoCellStepInterchangeFree_isTwoCellStep`), and accessibility descends to a subrelation
(`accessible_ofSubrelation`), so the already-proven `twoCellStep_isStronglyNormalizing` (the left-heavy
polynomial weight in `FreeTwoCellStrongNormalization`) carries over verbatim — no fresh weight bookkeeping.
The remaining bricks of the modulo route are the fragment's LOCAL confluence (now genuinely joinable, with the
obstructing interchange peak removed) and the modulo-E capstone.

Zero external dependencies beyond `FreeTwoCellConfluence`. Raw Lean 4 + Init; every theorem
`propext`/`Quot.sound`/`Classical`/`sorry`/`omega`-free (the subrelation descent is a structural `Acc.rec`; the
embedding is a structural induction on the fragment with one congruence-IH per one-hole rule). -/

namespace FX1Poly.Tier0

/-- A subrelation inherits accessibility: if every `smaller` step is also a `larger` step, then any point
accessible under `larger` is accessible under `smaller`. Specialized to flipped reduction relations, this is
"strong normalization descends to a subrelation" — a smaller rewrite system terminates whenever the larger one
it embeds into does. -/
theorem accessible_ofSubrelation {Carrier : Type _}
    {smaller larger : Carrier → Carrier → Prop}
    (embed : ∀ {leftPoint rightPoint : Carrier}, smaller leftPoint rightPoint → larger leftPoint rightPoint)
    {point : Carrier} (accessibleLarger : Acc larger point) :
    Acc smaller point := by
  induction accessibleLarger with
  | intro current _reachable ih =>
      exact Acc.intro current (fun predecessor stepSmaller => ih predecessor (embed stepSmaller))

/-- The **interchange-free** 3-cell rewrite: exactly the eleven structural laws of `TwoCellStep`
(identity-drop, associativity, whisker-functoriality, the four congruences) with the Godement `interchange`
step WITHDRAWN. The full `TwoCellStep` is non-confluent precisely because of `interchange`; this fragment is the
oriented system that the modulo-E route normalizes, with interchange relegated to the conversion equation. -/
inductive TwoCellStepInterchangeFree (signature : ModeSignature) :
    {sourceMode targetMode : signature.graph.Mode} →
    {sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode} →
    RawTwoCellExpr signature sourcePath targetPath →
    RawTwoCellExpr signature sourcePath targetPath → Prop where
  /-- Drop a left identity: `id ⊟ α ⟶ α`. -/
  | vcompIdLeft {sourceMode targetMode : signature.graph.Mode}
      {oneCellF oneCellG : ModalityPath signature.graph sourceMode targetMode}
      (cellAlpha : RawTwoCellExpr signature oneCellF oneCellG) :
      TwoCellStepInterchangeFree signature (RawTwoCellExpr.vcomp (RawTwoCellExpr.id oneCellF) cellAlpha) cellAlpha
  /-- Drop a right identity: `α ⊟ id ⟶ α`. -/
  | vcompIdRight {sourceMode targetMode : signature.graph.Mode}
      {oneCellF oneCellG : ModalityPath signature.graph sourceMode targetMode}
      (cellAlpha : RawTwoCellExpr signature oneCellF oneCellG) :
      TwoCellStepInterchangeFree signature (RawTwoCellExpr.vcomp cellAlpha (RawTwoCellExpr.id oneCellG)) cellAlpha
  /-- Right-associate vertical composition: `(α ⊟ β) ⊟ γ ⟶ α ⊟ (β ⊟ γ)`. -/
  | vcompAssoc {sourceMode targetMode : signature.graph.Mode}
      {oneCellF oneCellG oneCellH oneCellK : ModalityPath signature.graph sourceMode targetMode}
      (cellAlpha : RawTwoCellExpr signature oneCellF oneCellG)
      (cellBeta : RawTwoCellExpr signature oneCellG oneCellH)
      (cellGamma : RawTwoCellExpr signature oneCellH oneCellK) :
      TwoCellStepInterchangeFree signature
        (RawTwoCellExpr.vcomp (RawTwoCellExpr.vcomp cellAlpha cellBeta) cellGamma)
        (RawTwoCellExpr.vcomp cellAlpha (RawTwoCellExpr.vcomp cellBeta cellGamma))
  /-- Whiskering an identity is an identity (left): `oneCell ◁ id ⟶ id`. -/
  | whiskerLeftId {sourceMode middleMode targetMode : signature.graph.Mode}
      (oneCell : ModalityPath signature.graph sourceMode middleMode)
      (path : ModalityPath signature.graph middleMode targetMode) :
      TwoCellStepInterchangeFree signature (RawTwoCellExpr.whiskerLeft oneCell (RawTwoCellExpr.id path))
        (RawTwoCellExpr.id (composePath oneCell path))
  /-- Whiskering an identity is an identity (right): `id ▷ oneCell ⟶ id`. -/
  | whiskerRightId {sourceMode middleMode targetMode : signature.graph.Mode}
      (path : ModalityPath signature.graph sourceMode middleMode)
      (oneCell : ModalityPath signature.graph middleMode targetMode) :
      TwoCellStepInterchangeFree signature (RawTwoCellExpr.whiskerRight oneCell (RawTwoCellExpr.id path))
        (RawTwoCellExpr.id (composePath path oneCell))
  /-- Left whiskering distributes over vertical composition: `oneCell ◁ (β ⊟ γ) ⟶ (oneCell ◁ β) ⊟ (oneCell ◁ γ)`. -/
  | whiskerLeftVcomp {sourceMode middleMode targetMode : signature.graph.Mode}
      (oneCell : ModalityPath signature.graph sourceMode middleMode)
      {oneCellG oneCellH oneCellK : ModalityPath signature.graph middleMode targetMode}
      (cellBeta : RawTwoCellExpr signature oneCellG oneCellH)
      (cellGamma : RawTwoCellExpr signature oneCellH oneCellK) :
      TwoCellStepInterchangeFree signature (RawTwoCellExpr.whiskerLeft oneCell (RawTwoCellExpr.vcomp cellBeta cellGamma))
        (RawTwoCellExpr.vcomp (RawTwoCellExpr.whiskerLeft oneCell cellBeta)
          (RawTwoCellExpr.whiskerLeft oneCell cellGamma))
  /-- Right whiskering distributes over vertical composition. -/
  | whiskerRightVcomp {sourceMode middleMode targetMode : signature.graph.Mode}
      {oneCellF oneCellG oneCellH : ModalityPath signature.graph sourceMode middleMode}
      (oneCell : ModalityPath signature.graph middleMode targetMode)
      (cellAlpha : RawTwoCellExpr signature oneCellF oneCellG)
      (cellBeta : RawTwoCellExpr signature oneCellG oneCellH) :
      TwoCellStepInterchangeFree signature (RawTwoCellExpr.whiskerRight oneCell (RawTwoCellExpr.vcomp cellAlpha cellBeta))
        (RawTwoCellExpr.vcomp (RawTwoCellExpr.whiskerRight oneCell cellAlpha)
          (RawTwoCellExpr.whiskerRight oneCell cellBeta))
  /-- Congruence: a step in the LEFT factor of a vertical composite. -/
  | vcompCongrLeft {sourceMode targetMode : signature.graph.Mode}
      {oneCellF oneCellG oneCellH : ModalityPath signature.graph sourceMode targetMode}
      {cellAlpha cellAlpha' : RawTwoCellExpr signature oneCellF oneCellG}
      (cellBeta : RawTwoCellExpr signature oneCellG oneCellH) :
      TwoCellStepInterchangeFree signature cellAlpha cellAlpha' →
      TwoCellStepInterchangeFree signature (RawTwoCellExpr.vcomp cellAlpha cellBeta)
        (RawTwoCellExpr.vcomp cellAlpha' cellBeta)
  /-- Congruence: a step in the RIGHT factor of a vertical composite. -/
  | vcompCongrRight {sourceMode targetMode : signature.graph.Mode}
      {oneCellF oneCellG oneCellH : ModalityPath signature.graph sourceMode targetMode}
      (cellAlpha : RawTwoCellExpr signature oneCellF oneCellG)
      {cellBeta cellBeta' : RawTwoCellExpr signature oneCellG oneCellH} :
      TwoCellStepInterchangeFree signature cellBeta cellBeta' →
      TwoCellStepInterchangeFree signature (RawTwoCellExpr.vcomp cellAlpha cellBeta)
        (RawTwoCellExpr.vcomp cellAlpha cellBeta')
  /-- Congruence: a step under a left whiskering. -/
  | whiskerLeftCongr {sourceMode middleMode targetMode : signature.graph.Mode}
      (oneCell : ModalityPath signature.graph sourceMode middleMode)
      {oneCellG oneCellH : ModalityPath signature.graph middleMode targetMode}
      {cellBeta cellBeta' : RawTwoCellExpr signature oneCellG oneCellH} :
      TwoCellStepInterchangeFree signature cellBeta cellBeta' →
      TwoCellStepInterchangeFree signature (RawTwoCellExpr.whiskerLeft oneCell cellBeta)
        (RawTwoCellExpr.whiskerLeft oneCell cellBeta')
  /-- Congruence: a step under a right whiskering. -/
  | whiskerRightCongr {sourceMode middleMode targetMode : signature.graph.Mode}
      {oneCellF oneCellG : ModalityPath signature.graph sourceMode middleMode}
      (oneCell : ModalityPath signature.graph middleMode targetMode)
      {cellAlpha cellAlpha' : RawTwoCellExpr signature oneCellF oneCellG} :
      TwoCellStepInterchangeFree signature cellAlpha cellAlpha' →
      TwoCellStepInterchangeFree signature (RawTwoCellExpr.whiskerRight oneCell cellAlpha)
        (RawTwoCellExpr.whiskerRight oneCell cellAlpha')

/-- Every interchange-free step is a `TwoCellStep` step — the fragment embeds into the full 3-polygraph,
constructor for constructor (the four congruence cases recurse through their one inner-step IH). -/
theorem twoCellStepInterchangeFree_isTwoCellStep {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode}
    {sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode}
    {redex reduct : RawTwoCellExpr signature sourcePath targetPath}
    (step : TwoCellStepInterchangeFree signature redex reduct) :
    TwoCellStep signature redex reduct := by
  induction step with
  | vcompIdLeft cellAlpha => exact TwoCellStep.vcompIdLeft cellAlpha
  | vcompIdRight cellAlpha => exact TwoCellStep.vcompIdRight cellAlpha
  | vcompAssoc cellAlpha cellBeta cellGamma => exact TwoCellStep.vcompAssoc cellAlpha cellBeta cellGamma
  | whiskerLeftId oneCell path => exact TwoCellStep.whiskerLeftId oneCell path
  | whiskerRightId path oneCell => exact TwoCellStep.whiskerRightId path oneCell
  | whiskerLeftVcomp oneCell cellBeta cellGamma => exact TwoCellStep.whiskerLeftVcomp oneCell cellBeta cellGamma
  | whiskerRightVcomp oneCell cellAlpha cellBeta => exact TwoCellStep.whiskerRightVcomp oneCell cellAlpha cellBeta
  | vcompCongrLeft cellBeta _innerStep ih => exact TwoCellStep.vcompCongrLeft cellBeta ih
  | vcompCongrRight cellAlpha _innerStep ih => exact TwoCellStep.vcompCongrRight cellAlpha ih
  | whiskerLeftCongr oneCell _innerStep ih => exact TwoCellStep.whiskerLeftCongr oneCell ih
  | whiskerRightCongr oneCell _innerStep ih => exact TwoCellStep.whiskerRightCongr oneCell ih

/-- ★ **The interchange-free fragment is strongly normalizing.** Its steps embed into `TwoCellStep`, whose SN
is already proven (`twoCellStep_isStronglyNormalizing`, the left-heavy polynomial weight), so accessibility
descends to the subrelation. This is the termination half of the modulo-interchange convergence — the half that
survives unchanged once `interchange` is withdrawn from the oriented set (its removal can only shrink the
relation, and a subrelation of a strongly-normalizing relation is strongly normalizing). -/
theorem twoCellStepInterchangeFree_isStronglyNormalizing {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode}
    {sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode}
    (cell : RawTwoCellExpr signature sourcePath targetPath) :
    Acc (fun reduct redex => TwoCellStepInterchangeFree signature redex reduct) cell :=
  accessible_ofSubrelation
    (fun step => twoCellStepInterchangeFree_isTwoCellStep step)
    (twoCellStep_isStronglyNormalizing cell)

end FX1Poly.Tier0
