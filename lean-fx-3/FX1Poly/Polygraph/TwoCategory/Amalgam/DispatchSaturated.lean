import FX1Poly.Polygraph.TwoCategory.Amalgam.MapCell
import FX1Poly.Polygraph.TwoCategory.Amalgam.SaturatedDispatch
import FX1Poly.Polygraph.TwoCategory.Amalgam.SaturatedComponentDecider
import FX1Poly.Polygraph.TwoCategory.Amalgam.DispatchLocallyThin

/-! # Polygraph/TwoCategory/Amalgam/DispatchSaturated — the pushout base relation, the cross-component commutation,
and the saturated dispatch through `mapCellAlong` (WP-AMALG r4, B + C)

`MapCell.lean` (r4 A) shipped the free 2-cell functor `mapCellAlong` along a `ComputadMorphismTwo`.  This file
uses it to CLOSE the two remaining r3 residuals of the saturated dispatch and to re-assemble the combination
theorem through the new machinery:

  * **Residual (B), the cross-component commutation** — SETTLED, and the r3 "arc-block-commute" citation RETIRED.
  * **Residual (A) at the relation level** — `SaturatedConvOverPushout`, the pushout's base relation as the
    disjoint union of the `mapCellAlong`-images of the two component relations, is now STATABLE.
  * **The dispatch (C)** — the thin fragment closes at the NEW `SaturatedConvOverPushout` interface (through the
    new coprojection lifts and the combined decider), non-vacuously; the soundness lift is the honest
    `mapCellAlong_preservesConv` conditional; completeness + the real-relation both-ways decision stay walled, the
    walls named precisely.

## Residual (B): the commutation is FREE — the old wall does not transfer (a finding)

The dispatch's literal need is: two elementary steps in DIFFERENT components at DISJOINT boundary positions
commute — the two orders are pushout-convertible.  At the `SaturatedConvOver` granularity this is
`crossComponentWhiskerCommute`, and it is discharged by a SINGLE constructor:
`SaturatedConvOver.ofFull (TwoCellConvFull.whiskerExchange ...)`.  The disjoint-whisker exchange
(`WhiskerFunctoriality`'s `whiskerExchange`, equivalently the Godement `interchange`) is ALREADY inside every
`SaturatedConvOver` for free, over any signature and any base relation — including the pushout.  So the
cross-component commutation needs ZERO new obligation.

The r3 docstrings (`SaturatedDispatch.lean`, `DispatchLocallyThin.lean`) cited `fxMode_hasArcBlockCommuteProof`
(`ArcGodementCommute`) as "the same open residual".  That is a MIS-ATTRIBUTION at this granularity:
`ArcGodementCommute` demands a bespoke Brauer/matching-diagram normal-form EXTRACTOR be Godement-invariant — a
strictly finer obligation about a DECISION invariant.  The dispatch needs only that the two orders be
CONVERTIBLE, and convertibility literally CONTAINS `whiskerExchange`/`interchange` as constructors.  The arc wall
is irrelevant here; the citation is retired.  (Literature grounding: the interchange / middle-four-exchange law
makes disjoint 2-cells order-irrelevant in the free strict 2-category — nLab "interchange law" / "strict
2-category".)

## The dispatch (C): what closes, what is walled

The combined decider through `mapCellAlong_preservesConv` gives the SOUNDNESS direction: a component convertibility
lifts to a pushout convertibility.  COMPLETENESS (every pushout derivation projects back to per-component
derivations — the Nelson-Oppen / Baader-Tinelli purification) stays open, and so does a REAL-relation both-ways
decision, for three named walls: (i) a genuine-generator coprojection `onTwoCell` needs `interpretWordFrom_map`
(`MapCell.lean`, `fxAmalg_hasRealGeneratorCoprojection = false`); (ii) the only shipped real saturated decider
(`decideSaturatedConvOverIdempotent`) lives over the BESPOKE `monadModeSignature`, not the RECONSTRUCTED
`monadComputad.toModeSignature`, so it cannot be wired into a computad pushout without the reconstruction
faithfulness iso (`fxMode_hasDecidableTwoCellEquality`); (iii) the purification/projection completeness itself.

Raw Lean 4 + Init.  Per-declaration `#assert_no_axioms` gated in the audit twin. -/

namespace FX1Poly.Polygraph.Amalgam

open FX1Poly.Polygraph

/-! ## A cast-congruence for the saturated conv -/

/-- **The saturated conv respects boundary casts** — casting both sides of a convertibility by the SAME boundary
equalities preserves it (both `castBoundary`s collapse when the equalities are substituted).  The bridge the
whisker-congruence cases of the lift ride through, since `mapCellAlong` of a whiskering carries a `castBoundary`.
`cases` on the equalities then `id` (propext-free). -/
theorem SaturatedConvOver.castBoundaryCongr {signature : ModeSignature} {baseRel : CellRel signature}
    {sourceMode targetMode : signature.graph.Mode}
    {sourcePath sourcePath' targetPath targetPath' : ModalityPath signature.graph sourceMode targetMode}
    (hsource : sourcePath = sourcePath') (htarget : targetPath = targetPath')
    {cellAlpha cellBeta : RawTwoCellExpr signature sourcePath targetPath} :
    SaturatedConvOver signature baseRel cellAlpha cellBeta →
    SaturatedConvOver signature baseRel
      (RawTwoCellExpr.castBoundary hsource htarget cellAlpha)
      (RawTwoCellExpr.castBoundary hsource htarget cellBeta) := by
  cases hsource; cases htarget; exact id

/-! ## Residual (B): the cross-component commutation (FREE) -/

/-- ★ **The cross-component commutation** — two whiskerings in DIFFERENT components at DISJOINT boundary positions
commute: `leftWhisker ◁ (body ▷ rightWhisker) ≈ (leftWhisker ◁ body) ▷ rightWhisker` (up to the associativity
boundary cast).  Discharged by a SINGLE constructor `SaturatedConvOver.ofFull (TwoCellConvFull.whiskerExchange
...)` — the disjoint-whisker exchange is inside every saturated conv for FREE, over any signature and any base
relation, including the pushout.  This SETTLES r3's residual (B): the cross-component block commutation the
dispatch needs is unconditional; the old `fxMode_hasArcBlockCommuteProof` (arc-block-commute) wall is about a
finer decision-invariant and does NOT transfer to this granularity. -/
theorem crossComponentWhiskerCommute {signature : ModeSignature} {baseRel : CellRel signature}
    {sourceMode middleSourceMode middleTargetMode targetMode : signature.graph.Mode}
    (leftWhisker : ModalityPath signature.graph sourceMode middleSourceMode)
    {bodyDom bodyCod : ModalityPath signature.graph middleSourceMode middleTargetMode}
    (rightWhisker : ModalityPath signature.graph middleTargetMode targetMode)
    (body : RawTwoCellExpr signature bodyDom bodyCod) :
    SaturatedConvOver signature baseRel
      (RawTwoCellExpr.whiskerLeft leftWhisker (RawTwoCellExpr.whiskerRight rightWhisker body))
      (RawTwoCellExpr.castBoundary (composePath_assoc leftWhisker bodyDom rightWhisker)
        (composePath_assoc leftWhisker bodyCod rightWhisker)
        (RawTwoCellExpr.whiskerRight rightWhisker (RawTwoCellExpr.whiskerLeft leftWhisker body))) :=
  SaturatedConvOver.ofFull (TwoCellConvFull.whiskerExchange leftWhisker rightWhisker body)

/-! ## Residual (A) at the relation level: the pushout base relation -/

/-- ★ **The pushout base relation** — `SaturatedConvOverPushout` is the disjoint union of the
`mapCellAlong`-images of the two component base relations along the coprojections.  A component-1 law row
`baseRel1 cellA cellB` becomes the pushout row relating `mapCellAlong inclLeft cellA` and `mapCellAlong inclLeft
cellB` (`left`); dually for component 2 (`right`).  This is the `baseRelPushout` r3 could not state (no
`mapCellAlong`); the saturated pushout convertibility is then `SaturatedConvOver pushout SaturatedConvOverPushout`.
For empty component relations it is the empty relation (no rows), so the thin dispatch's pushout conv is the pure
free convertibility again. -/
inductive SaturatedConvOverPushout (comp1 comp2 : ModeComputad)
    (sameModes : comp1.modeCount = comp2.modeCount)
    (inclLeft : ComputadMorphismTwo comp1 (pushoutShared comp1 comp2 sameModes))
    (inclRight : ComputadMorphismTwo comp2 (pushoutShared comp1 comp2 sameModes))
    (baseRel1 : CellRel comp1.toModeSignature) (baseRel2 : CellRel comp2.toModeSignature) :
    {sourceMode targetMode : (pushoutShared comp1 comp2 sameModes).toModeSignature.graph.Mode} →
    {sourcePath targetPath :
      ModalityPath (pushoutShared comp1 comp2 sameModes).toModeSignature.graph sourceMode targetMode} →
    RawTwoCellExpr (pushoutShared comp1 comp2 sameModes).toModeSignature sourcePath targetPath →
    RawTwoCellExpr (pushoutShared comp1 comp2 sameModes).toModeSignature sourcePath targetPath → Prop where
  /-- A component-1 law row, transported along the left coprojection. -/
  | left {sourceMode targetMode : Fin comp1.modeCount}
      {sourcePath targetPath : ModalityPath comp1.toModeGraph sourceMode targetMode}
      {cellA cellB : RawTwoCellExpr comp1.toModeSignature sourcePath targetPath} :
      baseRel1 cellA cellB →
      SaturatedConvOverPushout comp1 comp2 sameModes inclLeft inclRight baseRel1 baseRel2
        (mapCellAlong inclLeft cellA) (mapCellAlong inclLeft cellB)
  /-- A component-2 law row, transported along the right coprojection. -/
  | right {sourceMode targetMode : Fin comp2.modeCount}
      {sourcePath targetPath : ModalityPath comp2.toModeGraph sourceMode targetMode}
      {cellA cellB : RawTwoCellExpr comp2.toModeSignature sourcePath targetPath} :
      baseRel2 cellA cellB →
      SaturatedConvOverPushout comp1 comp2 sameModes inclLeft inclRight baseRel1 baseRel2
        (mapCellAlong inclRight cellA) (mapCellAlong inclRight cellB)

/-! ## The soundness lift (conditional on the structural functoriality) -/

/-- The **absorbing congruence** witnessing that the `mapCellAlong`-image relation absorbs the source saturated
congruence — the package `SaturatedConvOver.recInto` eliminates against (sidestepping the `induction`-tactic
`mkElimApp` failure on the computed-graph indices, exactly as the per-lane isos use `recInto`).  `ofFull` via the
structural functoriality `fullPreserved`, `ofRelation` via `rowMap`; the two `vcomp` congruences CAST-FREE
(`mapCellAlong` maps `vcomp` on the nose), the two `whisker` congruences through `SaturatedConvOver.castBoundaryCongr`
(since `mapCellAlong` of a whiskering carries the `mapPath_composePath` cast); `refl`/`symm`/`trans` structural. -/
def mapCellAlongCongruence {source target : ModeComputad} (morphism : ComputadMorphismTwo source target)
    {baseRelSrc : CellRel source.toModeSignature} {baseRelTgt : CellRel target.toModeSignature}
    (fullPreserved : {sourceMode targetMode : Fin source.modeCount} →
      {sourcePath targetPath : ModalityPath source.toModeGraph sourceMode targetMode} →
      {cellA cellB : RawTwoCellExpr source.toModeSignature sourcePath targetPath} →
      TwoCellConvFull source.toModeSignature cellA cellB →
      TwoCellConvFull target.toModeSignature (mapCellAlong morphism cellA) (mapCellAlong morphism cellB))
    (rowMap : {sourceMode targetMode : Fin source.modeCount} →
      {sourcePath targetPath : ModalityPath source.toModeGraph sourceMode targetMode} →
      {cellA cellB : RawTwoCellExpr source.toModeSignature sourcePath targetPath} →
      baseRelSrc cellA cellB →
      baseRelTgt (mapCellAlong morphism cellA) (mapCellAlong morphism cellB)) :
    IsSaturatedCongruence source.toModeSignature baseRelSrc
      (fun cellA cellB => SaturatedConvOver target.toModeSignature baseRelTgt
        (mapCellAlong morphism cellA) (mapCellAlong morphism cellB)) where
  ofFull full := SaturatedConvOver.ofFull (fullPreserved full)
  ofRelation row := SaturatedConvOver.ofRelation (rowMap row)
  vcompCongrLeft {_ _ _ _ _ _ _ cellBeta} ih :=
    SaturatedConvOver.vcompCongrLeft (mapCellAlong morphism cellBeta) ih
  vcompCongrRight {_ _ _ _ _ cellAlpha _ _} ih :=
    SaturatedConvOver.vcompCongrRight (mapCellAlong morphism cellAlpha) ih
  whiskerLeftCongr {_ _ _ oneCell _ _ _ _} ih :=
    SaturatedConvOver.castBoundaryCongr _ _
      (SaturatedConvOver.whiskerLeftCongr (mapPath morphism.toComputadMorphism oneCell) ih)
  whiskerRightCongr {_ _ _ _ _ oneCell _ _} ih :=
    SaturatedConvOver.castBoundaryCongr _ _
      (SaturatedConvOver.whiskerRightCongr (mapPath morphism.toComputadMorphism oneCell) ih)
  refl cell := SaturatedConvOver.refl (mapCellAlong morphism cell)
  symm ih := SaturatedConvOver.symm ih
  trans ihLeft ihRight := SaturatedConvOver.trans ihLeft ihRight

/-- ★ **The saturated-conv lift along `mapCellAlong`** — a component saturated convertibility transports to a
pushout saturated convertibility of the images, PROVIDED (i) the completed free convertibility is preserved
(`fullPreserved`, the structural functoriality — the honest residual) and (ii) the base rows map to target rows
(`rowMap`, discharged by construction of `SaturatedConvOverPushout`).  The SOUNDNESS direction of the dispatch,
via the universal property `SaturatedConvOver.recInto`. -/
theorem mapCellAlong_preservesConv {source target : ModeComputad} (morphism : ComputadMorphismTwo source target)
    {baseRelSrc : CellRel source.toModeSignature} {baseRelTgt : CellRel target.toModeSignature}
    (fullPreserved : {sourceMode targetMode : Fin source.modeCount} →
      {sourcePath targetPath : ModalityPath source.toModeGraph sourceMode targetMode} →
      {cellA cellB : RawTwoCellExpr source.toModeSignature sourcePath targetPath} →
      TwoCellConvFull source.toModeSignature cellA cellB →
      TwoCellConvFull target.toModeSignature (mapCellAlong morphism cellA) (mapCellAlong morphism cellB))
    (rowMap : {sourceMode targetMode : Fin source.modeCount} →
      {sourcePath targetPath : ModalityPath source.toModeGraph sourceMode targetMode} →
      {cellA cellB : RawTwoCellExpr source.toModeSignature sourcePath targetPath} →
      baseRelSrc cellA cellB →
      baseRelTgt (mapCellAlong morphism cellA) (mapCellAlong morphism cellB))
    {sourceMode targetMode : Fin source.modeCount}
    {sourcePath targetPath : ModalityPath source.toModeGraph sourceMode targetMode}
    {cellAlpha cellBeta : RawTwoCellExpr source.toModeSignature sourcePath targetPath}
    (conv : SaturatedConvOver source.toModeSignature baseRelSrc cellAlpha cellBeta) :
    SaturatedConvOver target.toModeSignature baseRelTgt
      (mapCellAlong morphism cellAlpha) (mapCellAlong morphism cellBeta) :=
  SaturatedConvOver.recInto (mapCellAlongCongruence morphism fullPreserved rowMap) conv

/-! ## The general thin decider (for any base relation) -/

/-- **The thin saturated decider, for ANY base relation** — in a no-generating-2-cell signature every parallel
free 2-cell pair is convertible (`allParallelConv_of_noGen` lifted through `ofConv`, which absorbs into
`SaturatedConvOver signature baseRel` for ANY `baseRel`), so the saturated decision is `isTrue` everywhere,
regardless of the (necessarily unfireable) rows.  Generalises `saturatedLocallyThinDecider` from `emptyCellRel`
to any relation — needed so the combined decider can decide `SaturatedConvOverPushout` directly. -/
def saturatedThinDeciderForAnyRel {signature : ModeSignature} {baseRel : CellRel signature}
    (noGen : SignatureHasNoTwoGen signature) : DecidableSaturatedConvForRel signature baseRel :=
  fun cellAlpha cellBeta =>
    Decidable.isTrue (SaturatedConvOver.ofConv (allParallelConv_of_noGen noGen cellAlpha cellBeta))

/-! ## The dispatch through the new interface: the thin fragment, at the pushout base relation -/

/-- ★ **The thin saturated dispatch through the new machinery** — a genuine `SaturatedDispatchDecidability` whose
combined base relation is the NEW `SaturatedConvOverPushout` (the disjoint union of the coprojection-images), not
`emptyCellRel`.  For two no-2-generator components the coprojections are the thin `inclusionLeftTwo` /
`inclusionRightTwo`; both component deciders and the combined decider are `saturatedThinDeciderForAnyRel`.  This
wires the r4 pieces — the coprojection `ComputadMorphismTwo` lifts and the pushout base relation — into the r3
dispatch statement, closing the thin fragment at the correct base-relation interface. -/
def saturatedPushoutThinDispatch {comp1 comp2 : ModeComputad} (sameModes : comp1.modeCount = comp2.modeCount)
    (leftThin : comp1.twoCellGenerators.length = 0)
    (rightThin : comp2.twoCellGenerators.length = 0)
    (disjoint :
      computadGeneratorsDisjoint comp1.modalityGenerators.length (pushoutShared comp1 comp2 sameModes) = true) :
    SaturatedDispatchDecidability comp1 comp2 sameModes
      (emptyCellRel comp1.toModeSignature) (emptyCellRel comp2.toModeSignature)
      (SaturatedConvOverPushout comp1 comp2 sameModes
        (inclusionLeftTwo comp1 comp2 sameModes leftThin)
        (inclusionRightTwo comp1 comp2 sameModes rightThin)
        (emptyCellRel comp1.toModeSignature) (emptyCellRel comp2.toModeSignature)) where
  componentOneDecider := saturatedThinDeciderForAnyRel (noGen_of_twoGenLenZero leftThin)
  componentTwoDecider := saturatedThinDeciderForAnyRel (noGen_of_twoGenLenZero rightThin)
  generatorsDisjoint := disjoint
  combinedDecider :=
    saturatedThinDeciderForAnyRel
      (noGen_of_twoGenLenZero (pushout_twoGenLenZero_of_components sameModes leftThin rightThin))

/-! ## The concrete inhabitant + non-vacuity at the new base relation -/

/-- ★ **The saturated dispatch at `involution +_M semiring`, through the new `SaturatedConvOverPushout`
interface.** -/
def involutionSecondSaturatedPushoutDispatch :
    SaturatedDispatchDecidability involutionComputad secondThinComputad involutionSecondSameModes
      (emptyCellRel involutionComputad.toModeSignature)
      (emptyCellRel secondThinComputad.toModeSignature)
      (SaturatedConvOverPushout involutionComputad secondThinComputad involutionSecondSameModes
        (inclusionLeftTwo involutionComputad secondThinComputad involutionSecondSameModes rfl)
        (inclusionRightTwo involutionComputad secondThinComputad involutionSecondSameModes rfl)
        (emptyCellRel involutionComputad.toModeSignature)
        (emptyCellRel secondThinComputad.toModeSignature)) :=
  saturatedPushoutThinDispatch involutionSecondSameModes rfl rfl thinPushout_disjoint

/-- The combined decider at the NEW base relation, applied to the genuinely-MIXED pair (a boundary over BOTH
components' letters, two DISTINCT expressions — the same pair `DispatchLocallyThin` uses), read off as a `Bool`.
Expect `true`: decided saturated-convertible at the `SaturatedConvOverPushout` interface. -/
def saturatedPushoutMixedVerdict : Bool :=
  match involutionSecondSaturatedPushoutDispatch.combinedDecider thinMixedAlpha thinMixedBeta with
  | isTrue _ => true
  | isFalse _ => false

-- The mixed pair over the real thin pushout, decided at the NEW SaturatedConvOverPushout interface: expect `true`.
#eval saturatedPushoutMixedVerdict

/-- The component-1 letter `s` as a length-1 path over the thin pushout. -/
def thinSPath : ModalityPath thinPushout.toModeSignature.graph thinMode thinMode :=
  ModalityPath.cons ⟨thinSLetter, rfl⟩ (ModalityPath.nil (graph := thinPushout.toModeSignature.graph) thinMode)

/-- The component-2 letter `u` as a length-1 path over the thin pushout. -/
def thinUPath : ModalityPath thinPushout.toModeSignature.graph thinMode thinMode :=
  ModalityPath.cons ⟨thinULetter, rfl⟩ (ModalityPath.nil (graph := thinPushout.toModeSignature.graph) thinMode)

/-- The identity 2-cell on the empty 1-cell at the thin pushout's single mode — the disjoint-whisker exchange body. -/
def thinIdBody :
    RawTwoCellExpr thinPushout.toModeSignature
      (ModalityPath.nil (graph := thinPushout.toModeSignature.graph) thinMode)
      (ModalityPath.nil (graph := thinPushout.toModeSignature.graph) thinMode) :=
  RawTwoCellExpr.id (ModalityPath.nil (graph := thinPushout.toModeSignature.graph) thinMode)

/-- ★ **The cross-component commutation, non-vacuously, over the real thin pushout** — the `s`-left-whiskering of
a `u`-right-whiskering of the identity is saturated-convertible to the reversed order (up to the associativity
cast).  A concrete inhabitant of `crossComponentWhiskerCommute` at `involution +_M semiring` with GENUINELY
different-component whiskers (`s` in component 1, `u` in component 2), discharged FREE. -/
def crossComponentCommuteWitness :=
  crossComponentWhiskerCommute (baseRel := emptyCellRel thinPushout.toModeSignature)
    thinSPath thinUPath thinIdBody

/-! ## Honesty markers -/

/-- ★ **Honesty marker — residual (B) SETTLED + residual (A) STATABLE + the thin dispatch re-based (r4 B + C
partial).**  The cross-component commutation `crossComponentWhiskerCommute` is discharged FREE by one
`ofFull (whiskerExchange ...)` (the r3 arc-block-commute citation is retired: it is a finer decision-invariant
obligation that does NOT transfer to this granularity); the pushout base relation `SaturatedConvOverPushout` (the
disjoint union of the `mapCellAlong`-images) is now statable; the soundness lift `mapCellAlong_preservesConv`
completes the congruence induction; the thin dispatch is re-based at the NEW `SaturatedConvOverPushout` interface
(`saturatedPushoutThinDispatch`, concrete at `involution +_M semiring`) with a genuine MIXED pair decided
non-vacuously (`saturatedPushoutMixedVerdict`) and a concrete cross-component commutation witness
(`crossComponentCommuteWitness`).  `= true`. -/
def fxAmalg_hasSaturatedPushoutBaseRelation : Bool := true

/-- **Honesty marker — the FULL saturated dispatch stays open, on THREE precisely-named walls (NOT the arc
wall).**  `fxAmalg_hasSaturatedDispatchTheorem` (`SaturatedDispatch.lean`) stays `false`.  For a REAL-relation
pushout the residuals are: (i) a genuine-generator coprojection `onTwoCell` needs `interpretWordFrom_map` (the
dependent seed-transport of the interpreter — `fxAmalg_hasRealGeneratorCoprojection = false`); (ii) the only
shipped real saturated decider `decideSaturatedConvOverIdempotent` lives over the BESPOKE `monadModeSignature`,
not the RECONSTRUCTED `monadComputad.toModeSignature`, so it needs the reconstruction-faithfulness iso
(`fxMode_hasDecidableTwoCellEquality`, coupled to fib-3) before it can serve as a computad-pushout component
decider; (iii) COMPLETENESS — every pushout derivation must project back to per-component derivations
(Nelson-Oppen / Baader-Tinelli purification, sound only for word-preserving / left-connected component
presentations; the unit/counit wire-creating generators break the convex-block projection).  The commutation is
NOT among the walls (it is free); `mapCellAlong_preservesConv` reduces the soundness lift to the single structural
functoriality `fullPreserved` (mapping `TwoCellConvFull`, the cast-reconciliation across the 12 `TwoCellStep`
constructors), the honest remaining brick.  `= false`. -/
def fxAmalg_hasFullSaturatedPushoutDispatch : Bool := false

end FX1Poly.Polygraph.Amalgam
