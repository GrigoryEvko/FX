import FX1Poly.Tier0.Mode.FreeTwoCellInterchangeFreeConfluence

/-! # mode-3 floor — the critical-pair JOIN toolkit for the interchange-free fragment

`FreeTwoCellInterchangeFreeConfluence` reduced the convergence of the interchange-free 2-cell fragment
(`TwoCellStepInterchangeFree`, the eleven structural laws with Godement `interchange` withdrawn) to its LOCAL
confluence `TwoCellInterchangeFreeLocallyConfluent` — and, unlike the full `TwoCellStep` (whose local confluence
is FALSE on the interchange peak), that obligation is genuinely dischargeable: every divergent peak is a
free-2-category coherence pair (pentagon, unit, whisker-distribution), all joinable.

This file ships the **critical-pair JOIN toolkit** that discharges those genuine peaks — each a standalone,
zero-axiom, reusable lemma producing the common reduct and both reflexive-transitive reductions to it:

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

## What remains (the main assembly)

The headline `twoCellInterchangeFreeLocallyConfluent : TwoCellInterchangeFreeLocallyConfluent signature` is the
`induction firstStep ; cases secondStep` tiling that DISPATCHES to this toolkit: most (firstStep, secondStep)
constructor pairs have incompatible source shapes and close by `RawTwoCellExpr` no-confusion under `cases`; the
parallel-redex pairs join by firing each step's residual (the four star-congruence lifts in
`FreeTwoCellInterchangeFreeConfluence`); the same-subterm congruence pairs join by the induction hypothesis; and
the genuine root overlaps are exactly the peaks this file discharges (with `joinableSymm` covering the mirror
direction). That assembly is the next brick; it introduces no new mathematical content beyond this toolkit. It
is left as an honest open obligation here — NOT discharged by `sorry`/`axiom` — so this toolkit lands green and
audit-clean on its own.

Zero external dependencies beyond `FreeTwoCellInterchangeFreeConfluence`. Raw Lean 4 + Init; every theorem
`propext`/`Quot.sound`/`Classical`/`sorry`/`omega`-free. The join builders `cases` on a step whose source is a
constructor-headed cell (`vcomp α β`); this is propext-clean here because the step relation's cell indices stay
in general position under the elimination (the same reason `Core.ReflTransClosure` is `cases`-clean), and the
atomic-source impossibilities route through the already-audited recognizer-irreducibility, never a raw
impossible-case match. -/

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

end FX1Poly.Tier0
