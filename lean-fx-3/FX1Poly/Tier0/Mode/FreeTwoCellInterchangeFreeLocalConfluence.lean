import FX1Poly.Tier0.Mode.FreeTwoCellInterchangeFreeConfluence

/-! # mode-3 floor — LOCAL CONFLUENCE of the interchange-free fragment

`FreeTwoCellInterchangeFreeConfluence` reduced the convergence of the interchange-free 2-cell fragment
(`TwoCellStepInterchangeFree`, the eleven structural laws with Godement `interchange` withdrawn) to its LOCAL
confluence `TwoCellInterchangeFreeLocallyConfluent` — and, unlike the full `TwoCellStep` (whose local confluence
is FALSE on the interchange peak), that obligation is genuinely dischargeable: every divergent peak is a
free-2-category coherence pair (pentagon, unit, whisker-distribution), all joinable.

★ This file **discharges that obligation** — `twoCellInterchangeFreeLocallyConfluent` is proven, and the
fragment's Church–Rosser property is upgraded to UNCONDITIONAL (`twoCellStepInterchangeFree_isConfluentUnconditional`).
It is built in three layers: (1) the critical-pair JOIN toolkit, (2) the whisker-source step reflection that
sidesteps the `composePath` index block, and (3) the `induction firstStep` tiling that dispatches to them.

## Layer 1 — the critical-pair JOIN toolkit

Each a standalone, zero-axiom, reusable lemma producing the common reduct and both reflexive-transitive
reductions to it:

  * `joinableSymm` — `Joinable` is symmetric (swap the two reduction witnesses), so a join proved with the
    peak's two steps in one order serves the mirror peak (firstStep/secondStep swapped) for free.
  * `stepFromIdentityCellIsImpossible` / `stepFromGeneratorCellIsImpossible` — the atomic-source inversions:
    an identity 2-cell and a generator 2-cell admit NO interchange-free step (via the already-audited
    `RawTwoCellExpr.isInterchangeNormal_irreducible` through the fragment embedding), so every congruence peak
    that would step inside an atom is vacuous.
  * `pentagonCriticalPairJoins` — the **pentagon**: the two reassociations of
    `vcomp (vcomp α β) (vcomp γ δ)` versus `vcomp (vcomp α (vcomp β γ)) δ` both reach
    `vcomp α (vcomp β (vcomp γ δ))` (one side via an extra `vcompCongrRight`-lifted associativity).
  * `associativityLeftFactorStepJoins` — associativity commuting with ANY step in the inner-left vcomp factor:
    `vcompAssoc` versus a step inside `vcomp α β` join (units drop, the pentagon fires, congruences slide
    through the reassociation). Covers both orientations of every `vcompAssoc × (left-factor step)` peak.
  * `whiskerLeftDistributionStepJoins` / `whiskerRightDistributionStepJoins` — whisker-distribution
    (`whisker{Left,Right}Vcomp`) commuting with ANY step in the whiskered vcomp body: the distribution and the
    inner step join (whisker-unit drops, whisker-distribution re-distributes through associativity, congruences
    slide under the whisker).

## Layer 2 — whisker-source step reflection

Taking apart the second step at a vcomp-headed source works by direct `cases` (the boundary 1-cells stay in
general position). At a WHISKER-headed source it does not: the source's boundary 1-cells are `composePath`
applications, and the dependent pattern matcher cannot unify two `composePath`s. `whiskerLeftStepReflect` /
`whiskerRightStepReflect` route around this — the case analysis is phrased as a function of the (generically
indexed) source cell (`whiskerLeftReflectGoal`) and proved by inducting a generic step, so the source-cell match
refines the `composePath` indices automatically and no `composePath` unification is ever attempted.

## Layer 3 — the main tiling

`twoCellLocalJoin` inducts on the first step and analyses the second: vcomp peaks by direct `cases`, whisker
peaks through the reflections. Incompatible pairs close by no-confusion; identity-source inner steps are vacuous
(`stepFromIdentityCellIsImpossible`); parallel redexes fire each other's residual (the four star-congruence
lifts in `FreeTwoCellInterchangeFreeConfluence`); same-subterm congruences close by the induction hypothesis;
and the genuine root overlaps are exactly the toolkit joins, with `joinableSymm` covering each mirror. The
headline `twoCellInterchangeFreeLocallyConfluent` packages it, and feeding it to the Newman reduction yields the
unconditional `twoCellStepInterchangeFree_isConfluentUnconditional`.

Zero external dependencies beyond `FreeTwoCellInterchangeFreeConfluence`. Raw Lean 4 + Init; every declaration
`propext`/`Quot.sound`/`Classical`/`sorry`/`omega`-free (per-decl `#assert_no_axioms` gated in the audit twin). -/

namespace FX1Poly.Tier0

/-! ## Symmetry of joinability + the atomic-source inversions -/

/-- **Joinability is symmetric** — swapping the two reduction witnesses turns a common-reduct join of
`leftValue` and `rightValue` into one of `rightValue` and `leftValue`. Lets a critical-pair join proved with the
peak's two steps in one order serve the mirror peak (the same overlap discovered with firstStep and secondStep
exchanged) without redoing the reductions. -/
theorem joinableSymm {Carrier : Type _} {rel : Carrier → Carrier → Prop} {leftValue rightValue : Carrier}
    (joined : Core.Joinable rel leftValue rightValue) : Core.Joinable rel rightValue leftValue := by
  obtain ⟨commonReduct, leftChain, rightChain⟩ := joined
  exact ⟨commonReduct, rightChain, leftChain⟩

/-- **An identity 2-cell admits no interchange-free step.** The recognizer `isInterchangeNormal` accepts every
identity cell, and `RawTwoCellExpr.isInterchangeNormal_irreducible` (already audited) shows an accepted cell is
irreducible under the full `TwoCellStep`; the fragment embeds into `TwoCellStep`
(`twoCellStepInterchangeFree_isTwoCellStep`), so it is irreducible here too. Closes every congruence peak whose
inner redex would sit inside an identity. -/
theorem stepFromIdentityCellIsImpossible {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode}
    {path : ModalityPath signature.graph sourceMode targetMode}
    {reduct : RawTwoCellExpr signature path path}
    (step : TwoCellStepInterchangeFree signature (RawTwoCellExpr.id path) reduct) : False :=
  RawTwoCellExpr.isInterchangeNormal_irreducible (expr := RawTwoCellExpr.id path) rfl
    (twoCellStepInterchangeFree_isTwoCellStep step)

/-- **A generator 2-cell admits no interchange-free step.** Same route as the identity case: a bare generator is
an interchange normal form, hence irreducible. -/
theorem stepFromGeneratorCellIsImpossible {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode}
    {sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode}
    {generator : signature.twoCell sourcePath targetPath}
    {reduct : RawTwoCellExpr signature sourcePath targetPath}
    (step : TwoCellStepInterchangeFree signature (RawTwoCellExpr.gen generator) reduct) : False :=
  RawTwoCellExpr.isInterchangeNormal_irreducible (expr := RawTwoCellExpr.gen generator) rfl
    (twoCellStepInterchangeFree_isTwoCellStep step)

/-! ## The pentagon -/

/-- **The pentagon critical pair joins.** The two ways of reassociating a four-fold vertical composite —
`vcomp (vcomp α β) (vcomp γ δ)` (the outer `vcompAssoc` reduct of `vcomp (vcomp (vcomp α β) γ) δ`) and
`vcomp (vcomp α (vcomp β γ)) δ` (its inner reduct) — both reduce to `vcomp α (vcomp β (vcomp γ δ))`: the first
by one `vcompAssoc`, the second by a `vcompAssoc` then a `vcompCongrRight`-lifted `vcompAssoc`. This is Mac
Lane's pentagon, oriented. -/
theorem pentagonCriticalPairJoins {signature : ModeSignature} {sourceMode targetMode : signature.graph.Mode}
    {oneCellF oneCellG oneCellH oneCellK oneCellL : ModalityPath signature.graph sourceMode targetMode}
    (cellAlpha : RawTwoCellExpr signature oneCellF oneCellG)
    (cellBeta : RawTwoCellExpr signature oneCellG oneCellH)
    (cellGamma : RawTwoCellExpr signature oneCellH oneCellK)
    (cellDelta : RawTwoCellExpr signature oneCellK oneCellL) :
    Core.Joinable (fun a b => TwoCellStepInterchangeFree signature a b)
      (RawTwoCellExpr.vcomp (RawTwoCellExpr.vcomp cellAlpha cellBeta)
        (RawTwoCellExpr.vcomp cellGamma cellDelta))
      (RawTwoCellExpr.vcomp (RawTwoCellExpr.vcomp cellAlpha (RawTwoCellExpr.vcomp cellBeta cellGamma))
        cellDelta) := by
  refine ⟨RawTwoCellExpr.vcomp cellAlpha
      (RawTwoCellExpr.vcomp cellBeta (RawTwoCellExpr.vcomp cellGamma cellDelta)), ?_, ?_⟩
  · exact Core.ReflTransClosure.single
      (TwoCellStepInterchangeFree.vcompAssoc cellAlpha cellBeta (RawTwoCellExpr.vcomp cellGamma cellDelta))
  · exact (Core.ReflTransClosure.single
        (TwoCellStepInterchangeFree.vcompAssoc cellAlpha (RawTwoCellExpr.vcomp cellBeta cellGamma)
          cellDelta)).trans
      (Core.ReflTransClosure.single
        (TwoCellStepInterchangeFree.vcompCongrRight cellAlpha
          (TwoCellStepInterchangeFree.vcompAssoc cellBeta cellGamma cellDelta)))

/-! ## Associativity versus a step in the inner-left factor -/

/-- **Associativity commutes with a step in the inner-left vcomp factor.** Given any step
`vcomp cellAlpha cellBeta ⟶ leftReduct`, the associativity reduct `vcomp cellAlpha (vcomp cellBeta cellGamma)`
and the congruence reduct `vcomp leftReduct cellGamma` join. By cases on the inner step: a left/right identity
drop slides through; an inner associativity is the pentagon; a left/right congruence reassociates then re-fires.
This is the full `vcompAssoc × (left-factor step)` critical-pair family in one orientation — its mirror is
`joinableSymm` of this. -/
theorem associativityLeftFactorStepJoins {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode}
    {oneCellF oneCellG oneCellH oneCellK : ModalityPath signature.graph sourceMode targetMode}
    {cellAlpha : RawTwoCellExpr signature oneCellF oneCellG}
    {cellBeta : RawTwoCellExpr signature oneCellG oneCellH}
    {leftReduct : RawTwoCellExpr signature oneCellF oneCellH}
    (innerStep : TwoCellStepInterchangeFree signature
      (RawTwoCellExpr.vcomp cellAlpha cellBeta) leftReduct)
    (cellGamma : RawTwoCellExpr signature oneCellH oneCellK) :
    Core.Joinable (fun a b => TwoCellStepInterchangeFree signature a b)
      (RawTwoCellExpr.vcomp cellAlpha (RawTwoCellExpr.vcomp cellBeta cellGamma))
      (RawTwoCellExpr.vcomp leftReduct cellGamma) := by
  cases innerStep with
  | vcompIdLeft cellInner =>
      exact ⟨_, Core.ReflTransClosure.single (TwoCellStepInterchangeFree.vcompIdLeft _),
        Core.ReflTransClosure.refl _⟩
  | vcompIdRight cellInner =>
      exact ⟨_, Core.ReflTransClosure.single
          (TwoCellStepInterchangeFree.vcompCongrRight _
            (TwoCellStepInterchangeFree.vcompIdLeft cellGamma)),
        Core.ReflTransClosure.refl _⟩
  | vcompAssoc cellP cellQ cellR =>
      exact pentagonCriticalPairJoins cellP cellQ cellBeta cellGamma
  | vcompCongrLeft cellInnerRight innerStepLeft =>
      exact ⟨_, Core.ReflTransClosure.single
          (TwoCellStepInterchangeFree.vcompCongrLeft _ innerStepLeft),
        Core.ReflTransClosure.single (TwoCellStepInterchangeFree.vcompAssoc _ _ _)⟩
  | vcompCongrRight cellInnerLeft innerStepRight =>
      exact ⟨_, Core.ReflTransClosure.single
          (TwoCellStepInterchangeFree.vcompCongrRight _
            (TwoCellStepInterchangeFree.vcompCongrLeft cellGamma innerStepRight)),
        Core.ReflTransClosure.single (TwoCellStepInterchangeFree.vcompAssoc _ _ _)⟩

/-! ## Whisker-distribution versus a step in the whiskered body -/

/-- **Left whisker-distribution commutes with a step in the whiskered vcomp body.** Given any step
`vcomp cellBeta cellGamma ⟶ bodyReduct`, the distributed form
`vcomp (whiskerLeft p cellBeta) (whiskerLeft p cellGamma)` and the congruence-under-whisker form
`whiskerLeft p bodyReduct` join: whisker-unit collapses then a vcomp-unit fires, an inner associativity
re-distributes through `vcompAssoc`, and inner congruences slide through one `whiskerLeftVcomp`. The full
`whiskerLeftVcomp × (body step)` critical-pair family. -/
theorem whiskerLeftDistributionStepJoins {signature : ModeSignature}
    {sourceMode middleMode targetMode : signature.graph.Mode}
    (oneCell : ModalityPath signature.graph sourceMode middleMode)
    {oneCellG oneCellH oneCellK : ModalityPath signature.graph middleMode targetMode}
    {cellBeta : RawTwoCellExpr signature oneCellG oneCellH}
    {cellGamma : RawTwoCellExpr signature oneCellH oneCellK}
    {bodyReduct : RawTwoCellExpr signature oneCellG oneCellK}
    (innerStep : TwoCellStepInterchangeFree signature
      (RawTwoCellExpr.vcomp cellBeta cellGamma) bodyReduct) :
    Core.Joinable (fun a b => TwoCellStepInterchangeFree signature a b)
      (RawTwoCellExpr.vcomp (RawTwoCellExpr.whiskerLeft oneCell cellBeta)
        (RawTwoCellExpr.whiskerLeft oneCell cellGamma))
      (RawTwoCellExpr.whiskerLeft oneCell bodyReduct) := by
  cases innerStep with
  | vcompIdLeft cellInner =>
      exact ⟨_, (Core.ReflTransClosure.single
          (TwoCellStepInterchangeFree.vcompCongrLeft _
            (TwoCellStepInterchangeFree.whiskerLeftId oneCell _))).trans
        (Core.ReflTransClosure.single (TwoCellStepInterchangeFree.vcompIdLeft _)),
        Core.ReflTransClosure.refl _⟩
  | vcompIdRight cellInner =>
      exact ⟨_, (Core.ReflTransClosure.single
          (TwoCellStepInterchangeFree.vcompCongrRight _
            (TwoCellStepInterchangeFree.whiskerLeftId oneCell _))).trans
        (Core.ReflTransClosure.single (TwoCellStepInterchangeFree.vcompIdRight _)),
        Core.ReflTransClosure.refl _⟩
  | vcompAssoc cellP cellQ cellR =>
      exact ⟨_,
        (Core.ReflTransClosure.single
          (TwoCellStepInterchangeFree.vcompCongrLeft _
            (TwoCellStepInterchangeFree.whiskerLeftVcomp oneCell cellP cellQ))).trans
        (Core.ReflTransClosure.single (TwoCellStepInterchangeFree.vcompAssoc _ _ _)),
        (Core.ReflTransClosure.single
          (TwoCellStepInterchangeFree.whiskerLeftVcomp oneCell cellP _)).trans
        (Core.ReflTransClosure.single
          (TwoCellStepInterchangeFree.vcompCongrRight _
            (TwoCellStepInterchangeFree.whiskerLeftVcomp oneCell cellQ cellGamma)))⟩
  | vcompCongrLeft cellInnerRight innerStepLeft =>
      exact ⟨_, Core.ReflTransClosure.single
          (TwoCellStepInterchangeFree.vcompCongrLeft _
            (TwoCellStepInterchangeFree.whiskerLeftCongr oneCell innerStepLeft)),
        Core.ReflTransClosure.single (TwoCellStepInterchangeFree.whiskerLeftVcomp oneCell _ _)⟩
  | vcompCongrRight cellInnerLeft innerStepRight =>
      exact ⟨_, Core.ReflTransClosure.single
          (TwoCellStepInterchangeFree.vcompCongrRight _
            (TwoCellStepInterchangeFree.whiskerLeftCongr oneCell innerStepRight)),
        Core.ReflTransClosure.single (TwoCellStepInterchangeFree.whiskerLeftVcomp oneCell _ _)⟩

/-- **Right whisker-distribution commutes with a step in the whiskered vcomp body.** The right-whisker dual of
`whiskerLeftDistributionStepJoins`: the full `whiskerRightVcomp × (body step)` critical-pair family. -/
theorem whiskerRightDistributionStepJoins {signature : ModeSignature}
    {sourceMode middleMode targetMode : signature.graph.Mode}
    (oneCell : ModalityPath signature.graph middleMode targetMode)
    {oneCellF oneCellG oneCellH : ModalityPath signature.graph sourceMode middleMode}
    {cellAlpha : RawTwoCellExpr signature oneCellF oneCellG}
    {cellBeta : RawTwoCellExpr signature oneCellG oneCellH}
    {bodyReduct : RawTwoCellExpr signature oneCellF oneCellH}
    (innerStep : TwoCellStepInterchangeFree signature
      (RawTwoCellExpr.vcomp cellAlpha cellBeta) bodyReduct) :
    Core.Joinable (fun a b => TwoCellStepInterchangeFree signature a b)
      (RawTwoCellExpr.vcomp (RawTwoCellExpr.whiskerRight oneCell cellAlpha)
        (RawTwoCellExpr.whiskerRight oneCell cellBeta))
      (RawTwoCellExpr.whiskerRight oneCell bodyReduct) := by
  cases innerStep with
  | vcompIdLeft cellInner =>
      exact ⟨_, (Core.ReflTransClosure.single
          (TwoCellStepInterchangeFree.vcompCongrLeft _
            (TwoCellStepInterchangeFree.whiskerRightId _ oneCell))).trans
        (Core.ReflTransClosure.single (TwoCellStepInterchangeFree.vcompIdLeft _)),
        Core.ReflTransClosure.refl _⟩
  | vcompIdRight cellInner =>
      exact ⟨_, (Core.ReflTransClosure.single
          (TwoCellStepInterchangeFree.vcompCongrRight _
            (TwoCellStepInterchangeFree.whiskerRightId _ oneCell))).trans
        (Core.ReflTransClosure.single (TwoCellStepInterchangeFree.vcompIdRight _)),
        Core.ReflTransClosure.refl _⟩
  | vcompAssoc cellP cellQ cellR =>
      exact ⟨_,
        (Core.ReflTransClosure.single
          (TwoCellStepInterchangeFree.vcompCongrLeft _
            (TwoCellStepInterchangeFree.whiskerRightVcomp oneCell cellP cellQ))).trans
        (Core.ReflTransClosure.single (TwoCellStepInterchangeFree.vcompAssoc _ _ _)),
        (Core.ReflTransClosure.single
          (TwoCellStepInterchangeFree.whiskerRightVcomp oneCell cellP _)).trans
        (Core.ReflTransClosure.single
          (TwoCellStepInterchangeFree.vcompCongrRight _
            (TwoCellStepInterchangeFree.whiskerRightVcomp oneCell cellQ cellBeta)))⟩
  | vcompCongrLeft cellInnerRight innerStepLeft =>
      exact ⟨_, Core.ReflTransClosure.single
          (TwoCellStepInterchangeFree.vcompCongrLeft _
            (TwoCellStepInterchangeFree.whiskerRightCongr oneCell innerStepLeft)),
        Core.ReflTransClosure.single (TwoCellStepInterchangeFree.whiskerRightVcomp oneCell _ _)⟩
  | vcompCongrRight cellInnerLeft innerStepRight =>
      exact ⟨_, Core.ReflTransClosure.single
          (TwoCellStepInterchangeFree.vcompCongrRight _
            (TwoCellStepInterchangeFree.whiskerRightCongr oneCell innerStepRight)),
        Core.ReflTransClosure.single (TwoCellStepInterchangeFree.whiskerRightVcomp oneCell _ _)⟩

/-! ## Reflection of a step from a whiskered cell

A step whose source is `whiskerLeft oneCell body` is one of three shapes: a congruence reflecting a step on the
body (`reflectStep`), a whisker-of-identity redex (`reflectIdRedex`, when the body is an identity), or a
whisker-of-vcomp redex (`reflectVcompRedex`, when the body is a vertical composite). The same case analysis on
the second step that the vcomp peaks do directly is, for a whiskered source, blocked at the tactic level: the
source's boundary 1-cells are `composePath` applications, and the dependent pattern matcher cannot unify two
`composePath`s. The reflection routes around this by phrasing the case analysis as a function of the (generically
indexed) source cell (`whiskerLeftReflectGoal`) and inducting on a generic step — the match refines the
`composePath` indices automatically, so no `composePath` unification is ever attempted. -/

/-- The three shapes a step from a left-whiskered cell can take. -/
inductive WhiskerLeftReflection {signature : ModeSignature} {sourceMode middleMode targetMode : signature.graph.Mode}
    (oneCell : ModalityPath signature.graph sourceMode middleMode) :
    {bodyDom bodyCod : ModalityPath signature.graph middleMode targetMode} →
    RawTwoCellExpr signature bodyDom bodyCod →
    RawTwoCellExpr signature (composePath oneCell bodyDom) (composePath oneCell bodyCod) → Prop where
  /-- The step is a congruence reflecting a step `body ⟶ bodyReduct`. -/
  | reflectStep {bodyDom bodyCod : ModalityPath signature.graph middleMode targetMode}
      {body bodyReduct : RawTwoCellExpr signature bodyDom bodyCod}
      (innerStep : TwoCellStepInterchangeFree signature body bodyReduct) :
      WhiskerLeftReflection oneCell body (RawTwoCellExpr.whiskerLeft oneCell bodyReduct)
  /-- The step is the whisker-of-identity redex `oneCell ◁ id ⟶ id`. -/
  | reflectIdRedex {pathMid : ModalityPath signature.graph middleMode targetMode} :
      WhiskerLeftReflection oneCell (RawTwoCellExpr.id pathMid)
        (RawTwoCellExpr.id (composePath oneCell pathMid))
  /-- The step is the whisker-of-vcomp redex `oneCell ◁ (β ⊟ γ) ⟶ (oneCell ◁ β) ⊟ (oneCell ◁ γ)`. -/
  | reflectVcompRedex {bodyDom bodyMid bodyCod : ModalityPath signature.graph middleMode targetMode}
      (cellBeta : RawTwoCellExpr signature bodyDom bodyMid)
      (cellGamma : RawTwoCellExpr signature bodyMid bodyCod) :
      WhiskerLeftReflection oneCell (RawTwoCellExpr.vcomp cellBeta cellGamma)
        (RawTwoCellExpr.vcomp (RawTwoCellExpr.whiskerLeft oneCell cellBeta)
          (RawTwoCellExpr.whiskerLeft oneCell cellGamma))

/-- The reflection goal as a function of the source cell: a left-whiskered cell demands the reflection, every
other head is trivially satisfied. Inducting a generic step against this goal lets the source-cell match refine
the `composePath` boundary indices, sidestepping the matcher's `composePath`-unification block. -/
def whiskerLeftReflectGoal {signature : ModeSignature} {sourceMode targetMode : signature.graph.Mode} :
    {sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode} →
    RawTwoCellExpr signature sourcePath targetPath →
    RawTwoCellExpr signature sourcePath targetPath → Prop
  | _, _, RawTwoCellExpr.gen _, _ => True
  | _, _, RawTwoCellExpr.id _, _ => True
  | _, _, RawTwoCellExpr.vcomp _ _, _ => True
  | _, _, RawTwoCellExpr.whiskerLeft oneCell body, reduct => WhiskerLeftReflection oneCell body reduct
  | _, _, RawTwoCellExpr.whiskerRight _ _, _ => True

/-- Every interchange-free step satisfies the left-whisker reflection goal. By induction on the step: the three
left-whisker rules supply the matching reflection constructor, every other rule lands in a trivial goal branch. -/
theorem stepSatisfiesWhiskerLeftReflectGoal {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode}
    {sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode}
    {cellSource cellReduct : RawTwoCellExpr signature sourcePath targetPath}
    (step : TwoCellStepInterchangeFree signature cellSource cellReduct) :
    whiskerLeftReflectGoal cellSource cellReduct := by
  induction step with
  | vcompIdLeft _ => exact True.intro
  | vcompIdRight _ => exact True.intro
  | vcompAssoc _ _ _ => exact True.intro
  | whiskerLeftId _ _ => exact WhiskerLeftReflection.reflectIdRedex
  | whiskerRightId _ _ => exact True.intro
  | whiskerLeftVcomp _ cellBeta cellGamma =>
      exact WhiskerLeftReflection.reflectVcompRedex cellBeta cellGamma
  | whiskerRightVcomp _ _ _ => exact True.intro
  | vcompCongrLeft _ _ _ => exact True.intro
  | vcompCongrRight _ _ _ => exact True.intro
  | whiskerLeftCongr _ innerStep _ => exact WhiskerLeftReflection.reflectStep innerStep
  | whiskerRightCongr _ _ _ => exact True.intro

/-- ★ **Reflection of a step from a left-whiskered cell.** Specializing the reflection goal to the
left-whiskered source collapses it (definitionally) to the reflection itself. -/
theorem whiskerLeftStepReflect {signature : ModeSignature}
    {sourceMode middleMode targetMode : signature.graph.Mode}
    (oneCell : ModalityPath signature.graph sourceMode middleMode)
    {bodyDom bodyCod : ModalityPath signature.graph middleMode targetMode}
    {body : RawTwoCellExpr signature bodyDom bodyCod}
    {reduct : RawTwoCellExpr signature (composePath oneCell bodyDom) (composePath oneCell bodyCod)}
    (step : TwoCellStepInterchangeFree signature (RawTwoCellExpr.whiskerLeft oneCell body) reduct) :
    WhiskerLeftReflection oneCell body reduct :=
  stepSatisfiesWhiskerLeftReflectGoal step

/-- The three shapes a step from a right-whiskered cell can take (the dual of `WhiskerLeftReflection`). -/
inductive WhiskerRightReflection {signature : ModeSignature} {sourceMode middleMode targetMode : signature.graph.Mode}
    (oneCell : ModalityPath signature.graph middleMode targetMode) :
    {bodyDom bodyCod : ModalityPath signature.graph sourceMode middleMode} →
    RawTwoCellExpr signature bodyDom bodyCod →
    RawTwoCellExpr signature (composePath bodyDom oneCell) (composePath bodyCod oneCell) → Prop where
  /-- The step is a congruence reflecting a step `body ⟶ bodyReduct`. -/
  | reflectStep {bodyDom bodyCod : ModalityPath signature.graph sourceMode middleMode}
      {body bodyReduct : RawTwoCellExpr signature bodyDom bodyCod}
      (innerStep : TwoCellStepInterchangeFree signature body bodyReduct) :
      WhiskerRightReflection oneCell body (RawTwoCellExpr.whiskerRight oneCell bodyReduct)
  /-- The step is the whisker-of-identity redex `id ▷ oneCell ⟶ id`. -/
  | reflectIdRedex {pathMid : ModalityPath signature.graph sourceMode middleMode} :
      WhiskerRightReflection oneCell (RawTwoCellExpr.id pathMid)
        (RawTwoCellExpr.id (composePath pathMid oneCell))
  /-- The step is the whisker-of-vcomp redex `(α ⊟ β) ▷ oneCell ⟶ (α ▷ oneCell) ⊟ (β ▷ oneCell)`. -/
  | reflectVcompRedex {bodyDom bodyMid bodyCod : ModalityPath signature.graph sourceMode middleMode}
      (cellAlpha : RawTwoCellExpr signature bodyDom bodyMid)
      (cellBeta : RawTwoCellExpr signature bodyMid bodyCod) :
      WhiskerRightReflection oneCell (RawTwoCellExpr.vcomp cellAlpha cellBeta)
        (RawTwoCellExpr.vcomp (RawTwoCellExpr.whiskerRight oneCell cellAlpha)
          (RawTwoCellExpr.whiskerRight oneCell cellBeta))

/-- The right-whisker reflection goal as a function of the source cell. -/
def whiskerRightReflectGoal {signature : ModeSignature} {sourceMode targetMode : signature.graph.Mode} :
    {sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode} →
    RawTwoCellExpr signature sourcePath targetPath →
    RawTwoCellExpr signature sourcePath targetPath → Prop
  | _, _, RawTwoCellExpr.gen _, _ => True
  | _, _, RawTwoCellExpr.id _, _ => True
  | _, _, RawTwoCellExpr.vcomp _ _, _ => True
  | _, _, RawTwoCellExpr.whiskerLeft _ _, _ => True
  | _, _, RawTwoCellExpr.whiskerRight oneCell body, reduct => WhiskerRightReflection oneCell body reduct

/-- Every interchange-free step satisfies the right-whisker reflection goal. -/
theorem stepSatisfiesWhiskerRightReflectGoal {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode}
    {sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode}
    {cellSource cellReduct : RawTwoCellExpr signature sourcePath targetPath}
    (step : TwoCellStepInterchangeFree signature cellSource cellReduct) :
    whiskerRightReflectGoal cellSource cellReduct := by
  induction step with
  | vcompIdLeft _ => exact True.intro
  | vcompIdRight _ => exact True.intro
  | vcompAssoc _ _ _ => exact True.intro
  | whiskerLeftId _ _ => exact True.intro
  | whiskerRightId _ _ => exact WhiskerRightReflection.reflectIdRedex
  | whiskerLeftVcomp _ _ _ => exact True.intro
  | whiskerRightVcomp _ cellAlpha cellBeta =>
      exact WhiskerRightReflection.reflectVcompRedex cellAlpha cellBeta
  | vcompCongrLeft _ _ _ => exact True.intro
  | vcompCongrRight _ _ _ => exact True.intro
  | whiskerLeftCongr _ _ _ => exact True.intro
  | whiskerRightCongr _ innerStep _ => exact WhiskerRightReflection.reflectStep innerStep

/-- ★ **Reflection of a step from a right-whiskered cell.** -/
theorem whiskerRightStepReflect {signature : ModeSignature}
    {sourceMode middleMode targetMode : signature.graph.Mode}
    (oneCell : ModalityPath signature.graph middleMode targetMode)
    {bodyDom bodyCod : ModalityPath signature.graph sourceMode middleMode}
    {body : RawTwoCellExpr signature bodyDom bodyCod}
    {reduct : RawTwoCellExpr signature (composePath bodyDom oneCell) (composePath bodyCod oneCell)}
    (step : TwoCellStepInterchangeFree signature (RawTwoCellExpr.whiskerRight oneCell body) reduct) :
    WhiskerRightReflection oneCell body reduct :=
  stepSatisfiesWhiskerRightReflectGoal step

/-! ## The main tiling: local confluence of the interchange-free fragment -/

/-- **Every divergent pair of single interchange-free steps from a common source joins.** By induction on the
first step, then analysis of the second step. For vcomp-headed sources the second step is taken apart directly
(`cases`); for whisker-headed sources it is taken apart through the reflection lemmas above (which sidestep the
`composePath` index block). Vacuous second steps close by no-confusion or `stepFromIdentityCellIsImpossible`;
parallel redexes fire each other's residual; same-subterm congruences close by the induction hypothesis; and the
genuine root overlaps are exactly the toolkit joins, with `joinableSymm` serving each mirror overlap. -/
theorem twoCellLocalJoin {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode}
    {sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode}
    {source leftReduct : RawTwoCellExpr signature sourcePath targetPath}
    (firstStep : TwoCellStepInterchangeFree signature source leftReduct) :
    ∀ {rightReduct : RawTwoCellExpr signature sourcePath targetPath},
      TwoCellStepInterchangeFree signature source rightReduct →
      Core.Joinable (fun a b => TwoCellStepInterchangeFree signature a b) leftReduct rightReduct := by
  induction firstStep with
  | vcompIdLeft cellAlpha =>
      intro rightReduct secondStep
      cases secondStep with
      | vcompIdLeft _ => exact ⟨_, Core.ReflTransClosure.refl _, Core.ReflTransClosure.refl _⟩
      | vcompIdRight _ => exact ⟨_, Core.ReflTransClosure.refl _, Core.ReflTransClosure.refl _⟩
      | vcompCongrLeft _ innerStepLeft => exact (stepFromIdentityCellIsImpossible innerStepLeft).elim
      | vcompCongrRight _ innerStepRight =>
          exact ⟨_, Core.ReflTransClosure.single innerStepRight,
            Core.ReflTransClosure.single (TwoCellStepInterchangeFree.vcompIdLeft _)⟩
  | vcompIdRight cellAlpha =>
      intro rightReduct secondStep
      cases secondStep with
      | vcompIdLeft _ => exact ⟨_, Core.ReflTransClosure.refl _, Core.ReflTransClosure.refl _⟩
      | vcompIdRight _ => exact ⟨_, Core.ReflTransClosure.refl _, Core.ReflTransClosure.refl _⟩
      | vcompAssoc cellAR cellBR _ =>
          exact ⟨_, Core.ReflTransClosure.refl _,
            Core.ReflTransClosure.single
              (TwoCellStepInterchangeFree.vcompCongrRight cellAR
                (TwoCellStepInterchangeFree.vcompIdRight cellBR))⟩
      | vcompCongrLeft _ innerStepLeft =>
          exact ⟨_, Core.ReflTransClosure.single innerStepLeft,
            Core.ReflTransClosure.single (TwoCellStepInterchangeFree.vcompIdRight _)⟩
      | vcompCongrRight _ innerStepRight => exact (stepFromIdentityCellIsImpossible innerStepRight).elim
  | vcompAssoc cellAlpha cellBeta cellGamma =>
      intro rightReduct secondStep
      cases secondStep with
      | vcompIdRight _ =>
          exact ⟨_, Core.ReflTransClosure.single
              (TwoCellStepInterchangeFree.vcompCongrRight cellAlpha
                (TwoCellStepInterchangeFree.vcompIdRight cellBeta)),
            Core.ReflTransClosure.refl _⟩
      | vcompAssoc _ _ _ => exact ⟨_, Core.ReflTransClosure.refl _, Core.ReflTransClosure.refl _⟩
      | vcompCongrLeft _ innerStepLeft =>
          exact associativityLeftFactorStepJoins innerStepLeft cellGamma
      | vcompCongrRight _ innerStepRight =>
          exact ⟨_, Core.ReflTransClosure.single
              (TwoCellStepInterchangeFree.vcompCongrRight cellAlpha
                (TwoCellStepInterchangeFree.vcompCongrRight cellBeta innerStepRight)),
            Core.ReflTransClosure.single (TwoCellStepInterchangeFree.vcompAssoc cellAlpha cellBeta _)⟩
  | whiskerLeftId oneCell path =>
      intro rightReduct secondStep
      cases whiskerLeftStepReflect oneCell secondStep with
      | reflectStep innerStep => exact (stepFromIdentityCellIsImpossible innerStep).elim
      | reflectIdRedex => exact ⟨_, Core.ReflTransClosure.refl _, Core.ReflTransClosure.refl _⟩
  | whiskerRightId path oneCell =>
      intro rightReduct secondStep
      cases whiskerRightStepReflect oneCell secondStep with
      | reflectStep innerStep => exact (stepFromIdentityCellIsImpossible innerStep).elim
      | reflectIdRedex => exact ⟨_, Core.ReflTransClosure.refl _, Core.ReflTransClosure.refl _⟩
  | whiskerLeftVcomp oneCell cellBeta cellGamma =>
      intro rightReduct secondStep
      cases whiskerLeftStepReflect oneCell secondStep with
      | reflectStep innerStep => exact whiskerLeftDistributionStepJoins oneCell innerStep
      | reflectVcompRedex _ _ => exact ⟨_, Core.ReflTransClosure.refl _, Core.ReflTransClosure.refl _⟩
  | whiskerRightVcomp oneCell cellAlpha cellBeta =>
      intro rightReduct secondStep
      cases whiskerRightStepReflect oneCell secondStep with
      | reflectStep innerStep => exact whiskerRightDistributionStepJoins oneCell innerStep
      | reflectVcompRedex _ _ => exact ⟨_, Core.ReflTransClosure.refl _, Core.ReflTransClosure.refl _⟩
  | vcompCongrLeft cellBeta innerStep ih =>
      intro rightReduct secondStep
      cases secondStep with
      | vcompIdLeft _ => exact (stepFromIdentityCellIsImpossible innerStep).elim
      | vcompIdRight _ =>
          exact ⟨_, Core.ReflTransClosure.single (TwoCellStepInterchangeFree.vcompIdRight _),
            Core.ReflTransClosure.single innerStep⟩
      | vcompAssoc _ _ _ => exact joinableSymm (associativityLeftFactorStepJoins innerStep cellBeta)
      | vcompCongrLeft _ innerStepLeft =>
          obtain ⟨commonReduct, leftChain, rightChain⟩ := ih innerStepLeft
          exact ⟨_, twoCellInterchangeFreeReducesStar_vcompCongrLeft cellBeta leftChain,
            twoCellInterchangeFreeReducesStar_vcompCongrLeft cellBeta rightChain⟩
      | vcompCongrRight _ innerStepRight =>
          exact ⟨_, Core.ReflTransClosure.single
              (TwoCellStepInterchangeFree.vcompCongrRight _ innerStepRight),
            Core.ReflTransClosure.single (TwoCellStepInterchangeFree.vcompCongrLeft _ innerStep)⟩
  | vcompCongrRight cellAlpha innerStep ih =>
      intro rightReduct secondStep
      cases secondStep with
      | vcompIdLeft _ =>
          exact ⟨_, Core.ReflTransClosure.single (TwoCellStepInterchangeFree.vcompIdLeft _),
            Core.ReflTransClosure.single innerStep⟩
      | vcompIdRight _ => exact (stepFromIdentityCellIsImpossible innerStep).elim
      | vcompAssoc cellAR cellBR _ =>
          exact ⟨_, Core.ReflTransClosure.single (TwoCellStepInterchangeFree.vcompAssoc cellAR cellBR _),
            Core.ReflTransClosure.single
              (TwoCellStepInterchangeFree.vcompCongrRight cellAR
                (TwoCellStepInterchangeFree.vcompCongrRight cellBR innerStep))⟩
      | vcompCongrLeft _ innerStepLeft =>
          exact ⟨_, Core.ReflTransClosure.single
              (TwoCellStepInterchangeFree.vcompCongrLeft _ innerStepLeft),
            Core.ReflTransClosure.single (TwoCellStepInterchangeFree.vcompCongrRight _ innerStep)⟩
      | vcompCongrRight _ innerStepRight =>
          obtain ⟨commonReduct, leftChain, rightChain⟩ := ih innerStepRight
          exact ⟨_, twoCellInterchangeFreeReducesStar_vcompCongrRight cellAlpha leftChain,
            twoCellInterchangeFreeReducesStar_vcompCongrRight cellAlpha rightChain⟩
  | whiskerLeftCongr oneCell innerStep ih =>
      intro rightReduct secondStep
      cases whiskerLeftStepReflect oneCell secondStep with
      | reflectStep innerStepInner =>
          obtain ⟨commonReduct, leftChain, rightChain⟩ := ih innerStepInner
          exact ⟨_, twoCellInterchangeFreeReducesStar_whiskerLeftCongr oneCell leftChain,
            twoCellInterchangeFreeReducesStar_whiskerLeftCongr oneCell rightChain⟩
      | reflectIdRedex => exact (stepFromIdentityCellIsImpossible innerStep).elim
      | reflectVcompRedex _ _ => exact joinableSymm (whiskerLeftDistributionStepJoins oneCell innerStep)
  | whiskerRightCongr oneCell innerStep ih =>
      intro rightReduct secondStep
      cases whiskerRightStepReflect oneCell secondStep with
      | reflectStep innerStepInner =>
          obtain ⟨commonReduct, leftChain, rightChain⟩ := ih innerStepInner
          exact ⟨_, twoCellInterchangeFreeReducesStar_whiskerRightCongr oneCell leftChain,
            twoCellInterchangeFreeReducesStar_whiskerRightCongr oneCell rightChain⟩
      | reflectIdRedex => exact (stepFromIdentityCellIsImpossible innerStep).elim
      | reflectVcompRedex _ _ => exact joinableSymm (whiskerRightDistributionStepJoins oneCell innerStep)

/-- ★ **Local (weak) confluence of the interchange-free fragment.** The headline `mode-3` obligation that
`FreeTwoCellInterchangeFreeConfluence` reduced the fragment's convergence to — discharged via `twoCellLocalJoin`
at every parallel boundary. Unlike the full `TwoCellStep` (whose local confluence is FALSE on the interchange
peak), this one is genuinely true: with `interchange` withdrawn every critical pair is a free-2-category
coherence pair, all joinable. -/
theorem twoCellInterchangeFreeLocallyConfluent (signature : ModeSignature) :
    TwoCellInterchangeFreeLocallyConfluent signature := by
  intro _ _ _ _ _ _ _ firstStep secondStep
  exact twoCellLocalJoin firstStep secondStep

/-- ★ **The interchange-free fragment is CONFLUENT, unconditionally.** Combining Newman's reduction
(`twoCellStepInterchangeFree_isConfluent`, SN supplied) with the now-proven local confluence flips the
fragment's Church–Rosser property from conditional to unconditional — divergent many-step interchange-free
reductions always join. This is the convergence backbone of the confluence-modulo-interchange route to the
fib-3 keystone (decidable 2-cell equality for the affine walking-adjunction). -/
theorem twoCellStepInterchangeFree_isConfluentUnconditional (signature : ModeSignature)
    {sourceMode targetMode : signature.graph.Mode}
    {sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode} :
    Core.Confluent (fun (a b : RawTwoCellExpr signature sourcePath targetPath) =>
      TwoCellStepInterchangeFree signature a b) :=
  twoCellStepInterchangeFree_isConfluent signature (twoCellInterchangeFreeLocallyConfluent signature)

end FX1Poly.Tier0
