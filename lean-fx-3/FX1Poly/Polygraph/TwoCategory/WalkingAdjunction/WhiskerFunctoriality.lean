import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.SpineGodement
import FX1Poly.Polygraph.Computad.AdjunctionSeed

/-! # mode-3 floor — whisker FUNCTORIALITY: the COMPLETED free-2-category convertibility + its spine soundness

`FreeTwoCellModel` shipped `TwoCellConv` — the reflexive-symmetric-transitive congruence closure of the oriented
strict-2-category laws (`TwoCellStep`), with the Godement `interchange` step included.  A prior machine-checked
pass found `TwoCellConv` is INCOMPLETE as free-strict-2-category convertibility: `TwoCellStep` has
`whisker{Left,Right}Id` (whiskering the identity *2-cell*) and `whisker{Left,Right}Vcomp`, but LACKS **whisker
FUNCTORIALITY** — the action of the 1-cell monoid on 2-cells:

  1. `whiskerLeft emptyPath X ≈ X`                                 (homogeneous — `composePath emptyPath p = p` definitionally)
  2. `whiskerRight emptyPath X ≈ X`                                (heterogeneous — needs `composePath p emptyPath = p`)
  3. `whiskerLeft (f ∘ g) X ≈ whiskerLeft f (whiskerLeft g X)`     (heterogeneous — needs `composePath` associativity)
  4. `whiskerRight (g ∘ f) X ≈ whiskerRight f (whiskerRight g X)`  (heterogeneous — the right dual)

Concretely (the prior pass' witness, in `FreeTwoCellRealizedChain`): `atomFrame` of the unit's spine atom
(`nil ◁ (nil ▷ gen unit)`) has the SAME `spine` as the bare `gen unit` but a DISTINCT interchange-free normal
form — the identity-1-cell whisker wrappers cannot be stripped by any `TwoCellStep`, because stripping them is
exactly whisker functoriality (laws 1/2).  So `TwoCellConv` is strictly coarser than the genuine convertibility,
and the spine→cell reconstruction is unsound on `TwoCellConv`.

This file ships the COMPLETED convertibility `TwoCellConvFull` as a NEW inductive (it cannot extend the
cross-file `TwoCellConv`), and proves it is SPINE-SOUND.

## What this file ships (each piece zero-axiom)

  * **`RawTwoCellExpr.castBoundary`** — transport a free 2-cell across boundary 1-cell EQUALITIES (a double
    `Eq.rec`).  The three heterogeneous whisker laws (2)/(3)/(4) thread their `composePath`-right-identity /
    associativity equalities through it; by definitional proof irrelevance of `Eq`, the specific equality proof
    never matters.  `castBoundary_spineDiff` / `castBoundary_spine` — casting is SPINE-INVISIBLE (the spine
    output type depends only on the boundary MODES, never the paths, so `cases` on the two equalities collapses
    the cast to the identity).
  * ★ **`TwoCellConvFull`** — the **completed free-strict-2-category convertibility**: the existing `TwoCellConv`
    embedded by `ofConv`, PLUS the four whisker-functoriality equations (the heterogeneous ones threaded through
    `castBoundary`), PLUS the four one-hole CONGRUENCES (vcomp left/right, whisker left/right — making it a genuine
    congruence, which the whisker-law equations do NOT come closed under), PLUS `refl` / `symm` / `trans`.  Each
    new whisker case relates SAME-SPINE cells.
  * ★ **`twoCellConvFull_spineTraceEquivDiff`** / **`twoCellConvFull_spineTraceEquiv`** — **spine SOUNDNESS** of
    the completed convertibility: `TwoCellConvFull` cells have trace-equivalent spines.  Proved in the
    all-boundary-accumulator (`spineDiff`) form (so the four congruences thread their inductive hypotheses under
    shifted accumulators, exactly as `TwoCellStep.spineTraceEquivDiff` does), then specialised at the empty
    boundary.  The four whisker-functoriality cases discharge by `SpineTraceEquiv.refl` after a propext-clean
    spine-equality (`castBoundary_spineDiff` + `composePath` right-identity / associativity); the `ofConv` case
    reuses the existing `TwoCellConv` soundness lifted to all accumulators.

This is the NECESSARY-condition (NO-direction) half of the trace-monoid word-problem characterisation of the
COMPLETED convertibility — strictly the same shape as `TwoCellConv.spineTraceEquiv`, now for the relation that is
faithful to the free strict 2-category.  The SUFFICIENT (YES-direction) reconstruction
(`SpineTraceEquiv → TwoCellConvFull`) is the companion development; see the honesty marker.

## The composePath path-category laws (reused, not re-proved)

`composePath_identityPath_right` (`composePath p emptyPath = p`, the `append_nil`-shape) and `composePath_assoc`
are ALREADY proved propext-clean by hand in `TwoCategoryCore` (structural induction on a `ModalityPath`, base
`rfl`, step `congrArg (ModalityPath.cons _)`); `composePath_identityPath_left` (`composePath emptyPath p = p`) is
definitional (`mode-0`).  This file REUSES them rather than duplicating — they are the landmine the heterogeneous
laws ride on, and they are zero-axiom in the substrate.

Raw Lean 4 + Init; every declaration `propext`/`Quot.sound`/`Classical`/`sorry`/`native_decide`/`omega`-free
(`castBoundary` is `Eq.rec`; its spine-invisibility is `cases` on the equalities then `rfl`; the soundness is
induction CONSTRUCTING `SpineTraceEquiv`, never casing it).  Per-declaration `#assert_no_axioms` gated in the
audit twin. -/

namespace FX1Poly.Polygraph

/-! ## The boundary cast + its spine-invisibility -/

/-- Transport a free 2-cell across EQUALITIES of its boundary 1-cells (a double `Eq.rec`).  The heterogeneous
whisker-functoriality laws relate cells whose boundaries are only PROPOSITIONALLY equal (`composePath`
right-identity / associativity); `castBoundary` moves one side onto the other's boundary so the convertibility
typechecks.  By definitional proof irrelevance of `Eq`, two casts to the same target boundary are definitionally
equal regardless of which equality proof is supplied. -/
def RawTwoCellExpr.castBoundary {signature : ModeSignature} {sourceMode targetMode : signature.graph.Mode}
    {sourcePath sourcePath' targetPath targetPath' : ModalityPath signature.graph sourceMode targetMode}
    (hsource : sourcePath = sourcePath') (htarget : targetPath = targetPath')
    (cell : RawTwoCellExpr signature sourcePath targetPath) :
    RawTwoCellExpr signature sourcePath' targetPath' :=
  hsource ▸ htarget ▸ cell

/-- **Casting is spine-invisible (difference-list form).**  The spine output type depends only on the boundary
MODES, never on the boundary PATHS, so substituting the two boundary equalities collapses `castBoundary` to the
identity and the spine difference-list is unchanged, for ALL boundary accumulators. -/
theorem RawTwoCellExpr.castBoundary_spineDiff {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode}
    {sourcePath sourcePath' targetPath targetPath' : ModalityPath signature.graph sourceMode targetMode}
    (hsource : sourcePath = sourcePath') (htarget : targetPath = targetPath')
    (cell : RawTwoCellExpr signature sourcePath targetPath)
    {overallSource overallTarget : signature.graph.Mode}
    (leftAcc : ModalityPath signature.graph overallSource sourceMode)
    (rightAcc : ModalityPath signature.graph targetMode overallTarget)
    (rest : List (SpineAtom signature overallSource overallTarget)) :
    (RawTwoCellExpr.castBoundary hsource htarget cell).spineDiff leftAcc rightAcc rest
      = cell.spineDiff leftAcc rightAcc rest := by
  cases hsource; cases htarget; rfl

/-- **Casting is spine-invisible.**  The reassembled spine is unchanged by a boundary cast (the empty-accumulator
specialisation of `castBoundary_spineDiff`). -/
theorem RawTwoCellExpr.castBoundary_spine {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode}
    {sourcePath sourcePath' targetPath targetPath' : ModalityPath signature.graph sourceMode targetMode}
    (hsource : sourcePath = sourcePath') (htarget : targetPath = targetPath')
    (cell : RawTwoCellExpr signature sourcePath targetPath) :
    (RawTwoCellExpr.castBoundary hsource htarget cell).spine = cell.spine := by
  cases hsource; cases htarget; rfl

/-- A list equality yields a (reflexive) trace equivalence — the bridge that discharges the whisker-functoriality
cases of soundness once their two spines are shown propext-clean equal. -/
theorem spineTraceEquiv_of_eq {signature : ModeSignature}
    {overallSource overallTarget : signature.graph.Mode}
    {firstList secondList : List (SpineAtom signature overallSource overallTarget)}
    (listsEqual : firstList = secondList) :
    SpineTraceEquiv signature firstList secondList := by
  cases listsEqual; exact SpineTraceEquiv.refl _

/-! ## The completed free-strict-2-category convertibility -/

/-- ★ The **completed free-strict-2-category 2-cell convertibility**: the existing `TwoCellConv` (embedded by
`ofConv`) plus whisker FUNCTORIALITY (the action of the 1-cell monoid on 2-cells) plus congruence closure.

The four whisker-functoriality constructors are the genuinely new content `TwoCellConv` lacked: stripping a
unit-1-cell whisker (`whiskerLeftUnit` / `whiskerRightUnit`) and splitting a composite-1-cell whisker into nested
single whiskers (`whiskerLeftComp` / `whiskerRightComp`).  The heterogeneous three thread their boundary
equalities through `castBoundary` (`composePath` right-identity for `whiskerRightUnit`, associativity for the two
`Comp` laws); each relates cells with the SAME spine.  The four one-hole congruences (`vcompCongr{Left,Right}`,
`whisker{Left,Right}Congr`) make this a genuine CONGRUENCE — `TwoCellConv` got its congruences from `TwoCellStep`'s
congruence rules, but the new whisker equations do NOT come congruence-closed, so they are added explicitly. -/
inductive TwoCellConvFull (signature : ModeSignature) :
    {sourceMode targetMode : signature.graph.Mode} →
    {sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode} →
    RawTwoCellExpr signature sourcePath targetPath →
    RawTwoCellExpr signature sourcePath targetPath → Prop where
  /-- Embed the existing convertibility (the structural laws + interchange). -/
  | ofConv {sourceMode targetMode : signature.graph.Mode}
      {sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode}
      {cellAlpha cellBeta : RawTwoCellExpr signature sourcePath targetPath} :
      TwoCellConv signature cellAlpha cellBeta → TwoCellConvFull signature cellAlpha cellBeta
  /-- Whisker functoriality (1): a unit-1-cell left whisker is the identity — `emptyPath ◁ X ≈ X`.  Homogeneous
      (`composePath emptyPath dom = dom` definitionally). -/
  | whiskerLeftUnit {sourceMode targetMode : signature.graph.Mode}
      {oneCellDom oneCellCod : ModalityPath signature.graph sourceMode targetMode}
      (body : RawTwoCellExpr signature oneCellDom oneCellCod) :
      TwoCellConvFull signature (RawTwoCellExpr.whiskerLeft (identityPath sourceMode) body) body
  /-- Whisker functoriality (2): a unit-1-cell right whisker is the identity — `X ▷ emptyPath ≈ X`.  Heterogeneous
      (`composePath dom emptyPath = dom` propositionally), threaded through `castBoundary`. -/
  | whiskerRightUnit {sourceMode targetMode : signature.graph.Mode}
      {oneCellDom oneCellCod : ModalityPath signature.graph sourceMode targetMode}
      (body : RawTwoCellExpr signature oneCellDom oneCellCod) :
      TwoCellConvFull signature (RawTwoCellExpr.whiskerRight (identityPath targetMode) body)
        (RawTwoCellExpr.castBoundary (composePath_identityPath_right oneCellDom).symm
          (composePath_identityPath_right oneCellCod).symm body)
  /-- Whisker functoriality (3): a composite-1-cell left whisker splits — `(f ∘ g) ◁ X ≈ f ◁ (g ◁ X)`.
      Heterogeneous (`composePath` associativity), threaded through `castBoundary`. -/
  | whiskerLeftComp {sourceMode middleModeOne middleModeTwo targetMode : signature.graph.Mode}
      (oneCellOuter : ModalityPath signature.graph sourceMode middleModeOne)
      (oneCellInner : ModalityPath signature.graph middleModeOne middleModeTwo)
      {oneCellDom oneCellCod : ModalityPath signature.graph middleModeTwo targetMode}
      (body : RawTwoCellExpr signature oneCellDom oneCellCod) :
      TwoCellConvFull signature
        (RawTwoCellExpr.whiskerLeft (composePath oneCellOuter oneCellInner) body)
        (RawTwoCellExpr.castBoundary (composePath_assoc oneCellOuter oneCellInner oneCellDom).symm
          (composePath_assoc oneCellOuter oneCellInner oneCellCod).symm
          (RawTwoCellExpr.whiskerLeft oneCellOuter (RawTwoCellExpr.whiskerLeft oneCellInner body)))
  /-- Whisker functoriality (4): a composite-1-cell right whisker splits — `(g ∘ f) ▷ X ≈ f ▷ (g ▷ X)`.  The
      right dual of (3); heterogeneous (`composePath` associativity), threaded through `castBoundary`. -/
  | whiskerRightComp {sourceMode middleModeOne middleModeTwo targetMode : signature.graph.Mode}
      {oneCellDom oneCellCod : ModalityPath signature.graph sourceMode middleModeOne}
      (oneCellInner : ModalityPath signature.graph middleModeOne middleModeTwo)
      (oneCellOuter : ModalityPath signature.graph middleModeTwo targetMode)
      (body : RawTwoCellExpr signature oneCellDom oneCellCod) :
      TwoCellConvFull signature
        (RawTwoCellExpr.whiskerRight (composePath oneCellInner oneCellOuter) body)
        (RawTwoCellExpr.castBoundary (composePath_assoc oneCellDom oneCellInner oneCellOuter)
          (composePath_assoc oneCellCod oneCellInner oneCellOuter)
          (RawTwoCellExpr.whiskerRight oneCellOuter (RawTwoCellExpr.whiskerRight oneCellInner body)))
  /-- Congruence in the LEFT factor of a vertical composite. -/
  | vcompCongrLeft {sourceMode targetMode : signature.graph.Mode}
      {oneCellF oneCellG oneCellH : ModalityPath signature.graph sourceMode targetMode}
      {cellAlpha cellAlpha' : RawTwoCellExpr signature oneCellF oneCellG}
      (cellBeta : RawTwoCellExpr signature oneCellG oneCellH) :
      TwoCellConvFull signature cellAlpha cellAlpha' →
      TwoCellConvFull signature (RawTwoCellExpr.vcomp cellAlpha cellBeta)
        (RawTwoCellExpr.vcomp cellAlpha' cellBeta)
  /-- Congruence in the RIGHT factor of a vertical composite. -/
  | vcompCongrRight {sourceMode targetMode : signature.graph.Mode}
      {oneCellF oneCellG oneCellH : ModalityPath signature.graph sourceMode targetMode}
      (cellAlpha : RawTwoCellExpr signature oneCellF oneCellG)
      {cellBeta cellBeta' : RawTwoCellExpr signature oneCellG oneCellH} :
      TwoCellConvFull signature cellBeta cellBeta' →
      TwoCellConvFull signature (RawTwoCellExpr.vcomp cellAlpha cellBeta)
        (RawTwoCellExpr.vcomp cellAlpha cellBeta')
  /-- Congruence under a left whiskering. -/
  | whiskerLeftCongr {sourceMode middleMode targetMode : signature.graph.Mode}
      (oneCell : ModalityPath signature.graph sourceMode middleMode)
      {oneCellG oneCellH : ModalityPath signature.graph middleMode targetMode}
      {cellBeta cellBeta' : RawTwoCellExpr signature oneCellG oneCellH} :
      TwoCellConvFull signature cellBeta cellBeta' →
      TwoCellConvFull signature (RawTwoCellExpr.whiskerLeft oneCell cellBeta)
        (RawTwoCellExpr.whiskerLeft oneCell cellBeta')
  /-- Congruence under a right whiskering. -/
  | whiskerRightCongr {sourceMode middleMode targetMode : signature.graph.Mode}
      {oneCellF oneCellG : ModalityPath signature.graph sourceMode middleMode}
      (oneCell : ModalityPath signature.graph middleMode targetMode)
      {cellAlpha cellAlpha' : RawTwoCellExpr signature oneCellF oneCellG} :
      TwoCellConvFull signature cellAlpha cellAlpha' →
      TwoCellConvFull signature (RawTwoCellExpr.whiskerRight oneCell cellAlpha)
        (RawTwoCellExpr.whiskerRight oneCell cellAlpha')
  /-- Reflexivity. -/
  | refl {sourceMode targetMode : signature.graph.Mode}
      {sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode}
      (cell : RawTwoCellExpr signature sourcePath targetPath) :
      TwoCellConvFull signature cell cell
  /-- Symmetry. -/
  | symm {sourceMode targetMode : signature.graph.Mode}
      {sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode}
      {cellAlpha cellBeta : RawTwoCellExpr signature sourcePath targetPath} :
      TwoCellConvFull signature cellAlpha cellBeta → TwoCellConvFull signature cellBeta cellAlpha
  /-- Transitivity. -/
  | trans {sourceMode targetMode : signature.graph.Mode}
      {sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode}
      {cellAlpha cellBeta cellGamma : RawTwoCellExpr signature sourcePath targetPath} :
      TwoCellConvFull signature cellAlpha cellBeta → TwoCellConvFull signature cellBeta cellGamma →
      TwoCellConvFull signature cellAlpha cellGamma

/-! ## Spine soundness of the completed convertibility -/

/-- The existing `TwoCellConv` soundness, strengthened to ALL boundary accumulators (the `spineDiff` form the
congruence cases of the completed soundness thread through).  A single step uses `TwoCellStep.spineTraceEquivDiff`;
reflexivity / symmetry / transitivity thread the matching `SpineTraceEquiv` constructors. -/
theorem twoCellConv_spineTraceEquivDiff {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode}
    {sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode}
    {cellAlpha cellBeta : RawTwoCellExpr signature sourcePath targetPath}
    (conv : TwoCellConv signature cellAlpha cellBeta) :
    ∀ {overallSource overallTarget : signature.graph.Mode}
      (leftAcc : ModalityPath signature.graph overallSource sourceMode)
      (rightAcc : ModalityPath signature.graph targetMode overallTarget)
      (rest : List (SpineAtom signature overallSource overallTarget)),
      SpineTraceEquiv signature (cellAlpha.spineDiff leftAcc rightAcc rest)
        (cellBeta.spineDiff leftAcc rightAcc rest) := by
  induction conv with
  | ofStep step => intro _ _ leftAcc rightAcc rest; exact step.spineTraceEquivDiff leftAcc rightAcc rest
  | refl _ => intro _ _ _ _ _; exact SpineTraceEquiv.refl _
  | symm _ ih => intro _ _ leftAcc rightAcc rest; exact SpineTraceEquiv.symm (ih leftAcc rightAcc rest)
  | trans _ _ ih1 ih2 =>
      intro _ _ leftAcc rightAcc rest; exact (ih1 leftAcc rightAcc rest).trans (ih2 leftAcc rightAcc rest)

/-- ★ **Spine soundness of the completed convertibility (difference-list form).**  Every `TwoCellConvFull`
transports the spine difference-list WITHIN trace equivalence, for all boundary accumulators.  By induction on
the conversion: `ofConv` reuses `twoCellConv_spineTraceEquivDiff`; each whisker-functoriality case relates
SAME-SPINE cells, discharged by `spineTraceEquiv_of_eq` of a propext-clean spine equality (`castBoundary` is
spine-invisible; `whiskerLeftUnit`'s accumulator shifts by `composePath` right-identity, the two `Comp` laws by
associativity); the four congruences thread the inductive hypothesis under shifted accumulators / via
`prependSpineDiff`, exactly as `TwoCellStep.spineTraceEquivDiff` does. -/
theorem twoCellConvFull_spineTraceEquivDiff {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode}
    {sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode}
    {cellAlpha cellBeta : RawTwoCellExpr signature sourcePath targetPath}
    (convFull : TwoCellConvFull signature cellAlpha cellBeta) :
    ∀ {overallSource overallTarget : signature.graph.Mode}
      (leftAcc : ModalityPath signature.graph overallSource sourceMode)
      (rightAcc : ModalityPath signature.graph targetMode overallTarget)
      (rest : List (SpineAtom signature overallSource overallTarget)),
      SpineTraceEquiv signature (cellAlpha.spineDiff leftAcc rightAcc rest)
        (cellBeta.spineDiff leftAcc rightAcc rest) := by
  induction convFull with
  | ofConv conv =>
      intro _ _ leftAcc rightAcc rest; exact twoCellConv_spineTraceEquivDiff conv leftAcc rightAcc rest
  | whiskerLeftUnit body =>
      intro _ _ leftAcc rightAcc rest
      exact spineTraceEquiv_of_eq
        (congrArg (fun acc => body.spineDiff acc rightAcc rest) (composePath_identityPath_right leftAcc))
  | whiskerRightUnit body =>
      intro _ _ leftAcc rightAcc rest
      exact spineTraceEquiv_of_eq (RawTwoCellExpr.castBoundary_spineDiff _ _ body leftAcc rightAcc rest).symm
  | whiskerLeftComp oneCellOuter oneCellInner body =>
      intro _ _ leftAcc rightAcc rest
      refine spineTraceEquiv_of_eq (Eq.trans ?_
        (RawTwoCellExpr.castBoundary_spineDiff _ _
          (RawTwoCellExpr.whiskerLeft oneCellOuter (RawTwoCellExpr.whiskerLeft oneCellInner body))
          leftAcc rightAcc rest).symm)
      dsimp only [RawTwoCellExpr.spineDiff]
      rw [composePath_assoc]
  | whiskerRightComp oneCellInner oneCellOuter body =>
      intro _ _ leftAcc rightAcc rest
      refine spineTraceEquiv_of_eq (Eq.trans ?_
        (RawTwoCellExpr.castBoundary_spineDiff _ _
          (RawTwoCellExpr.whiskerRight oneCellOuter (RawTwoCellExpr.whiskerRight oneCellInner body))
          leftAcc rightAcc rest).symm)
      dsimp only [RawTwoCellExpr.spineDiff]
      rw [composePath_assoc]
  | vcompCongrLeft cellBeta _ ih =>
      intro _ _ leftAcc rightAcc rest
      exact ih leftAcc rightAcc (cellBeta.spineDiff leftAcc rightAcc rest)
  | vcompCongrRight cellAlpha _ ih =>
      intro _ _ leftAcc rightAcc rest
      exact SpineTraceEquiv.prependSpineDiff leftAcc rightAcc cellAlpha (ih leftAcc rightAcc rest)
  | whiskerLeftCongr oneCell _ ih =>
      intro _ _ leftAcc rightAcc rest
      exact ih (composePath leftAcc oneCell) rightAcc rest
  | whiskerRightCongr oneCell _ ih =>
      intro _ _ leftAcc rightAcc rest
      exact ih leftAcc (composePath oneCell rightAcc) rest
  | refl _ => intro _ _ _ _ _; exact SpineTraceEquiv.refl _
  | symm _ ih => intro _ _ leftAcc rightAcc rest; exact SpineTraceEquiv.symm (ih leftAcc rightAcc rest)
  | trans _ _ ih1 ih2 =>
      intro _ _ leftAcc rightAcc rest; exact (ih1 leftAcc rightAcc rest).trans (ih2 leftAcc rightAcc rest)

/-- ★ **Spine soundness of the completed convertibility.**  `TwoCellConvFull` cells have trace-equivalent spines
(the empty-boundary specialisation).  This is the NO-direction of the trace-monoid word problem for the COMPLETED
convertibility — the relation faithful to the free strict 2-category, where the prior `TwoCellConv.spineTraceEquiv`
was only sound for the whisker-functoriality-INCOMPLETE relation.  The parent assembly uses its contrapositive for
the `isFalse` branch of `Decidable (TwoCellConvFull …)`. -/
theorem twoCellConvFull_spineTraceEquiv {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode}
    {sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode}
    {cellAlpha cellBeta : RawTwoCellExpr signature sourcePath targetPath}
    (convFull : TwoCellConvFull signature cellAlpha cellBeta) :
    SpineTraceEquiv signature cellAlpha.spine cellBeta.spine :=
  twoCellConvFull_spineTraceEquivDiff convFull (identityPath sourceMode) (identityPath targetMode) []

/-! ## Smoke: the new laws compute -/

/-- Smoke: the whisker-left-unit law `emptyPath ◁ X ≈ X` (general). -/
theorem whiskerLeftUnit_convFull {signature : ModeSignature} {sourceMode targetMode : signature.graph.Mode}
    {oneCellDom oneCellCod : ModalityPath signature.graph sourceMode targetMode}
    (body : RawTwoCellExpr signature oneCellDom oneCellCod) :
    TwoCellConvFull signature (RawTwoCellExpr.whiskerLeft (identityPath sourceMode) body) body :=
  TwoCellConvFull.whiskerLeftUnit body

/-- Smoke: the whisker-right-unit law `X ▷ emptyPath ≈ X` (general, through the boundary cast). -/
theorem whiskerRightUnit_convFull {signature : ModeSignature} {sourceMode targetMode : signature.graph.Mode}
    {oneCellDom oneCellCod : ModalityPath signature.graph sourceMode targetMode}
    (body : RawTwoCellExpr signature oneCellDom oneCellCod) :
    TwoCellConvFull signature (RawTwoCellExpr.whiskerRight (identityPath targetMode) body)
      (RawTwoCellExpr.castBoundary (composePath_identityPath_right oneCellDom).symm
        (composePath_identityPath_right oneCellCod).symm body) :=
  TwoCellConvFull.whiskerRightUnit body

/-- Smoke: on the adjunction seed, the unit-then-identity composite is `TwoCellConvFull` to the bare unit (the
existing `TwoCellConv` lifts through `ofConv`) — the completed relation contains the structural one. -/
theorem adjunctionUnitThenId_convFull_unit :
    TwoCellConvFull adjunctionModeSignature adjunctionUnitThenId adjunctionUnitTwoCell :=
  TwoCellConvFull.ofConv adjunctionUnitThenId_conv_unit

/-- Smoke: on the adjunction seed, the unit left-whiskered by the empty 1-cell has the SAME spine as the bare
unit (definitional) — the spine cannot tell `emptyPath ◁ unit` from `unit`, which is exactly what
`whiskerLeftUnit` makes a `TwoCellConvFull`.  (The whisker-left-unit conversion itself on the seed is
`whiskerLeftUnit_convFull adjunctionUnitTwoCell`.) -/
theorem adjunctionUnitWhiskerLeftEmpty_spine_eq_unit :
    (RawTwoCellExpr.whiskerLeft (identityPath (graph := adjunctionGraph) AdjunctionMode.base)
        adjunctionUnitTwoCell).spine
      = adjunctionUnitTwoCell.spine := rfl

/-! ## Honesty marker -/

/-- **Honesty marker.**  `TwoCellConvFull` is the COMPLETED free-strict-2-category 2-cell convertibility — the
existing `TwoCellConv` plus whisker FUNCTORIALITY plus congruence closure — and it is SPINE-SOUND
(`twoCellConvFull_spineTraceEquiv` : the NO-direction of the trace word problem).  The SUFFICIENT (YES-direction)
reconstruction `SpineTraceEquiv a.spine b.spine → TwoCellConvFull a b` (the readback past the `spine` quotient,
which whisker functoriality makes SOUND where it was unsound on `TwoCellConv`) is the companion development; this
file ships the completed relation and its soundness only.  The convergent-3-polygraph route stays blocked
(interchange non-confluence is real); the decision is via the trace route, with this soundness as its NO-branch.
`fxMode_hasConvergentThreeCellSystem` stays understood-false.  `= false`. -/
def fxMode_hasWhiskerFunctorialityConvertibility : Bool := false

end FX1Poly.Polygraph
