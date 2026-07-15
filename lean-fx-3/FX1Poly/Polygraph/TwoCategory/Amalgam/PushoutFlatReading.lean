import FX1Poly.Polygraph.TwoCategory.Amalgam.PushoutRunSlotReading
import FX1Poly.Polygraph.TwoCategory.WalkingMonad.MonadHcompMult

/-! # Polygraph/TwoCategory/Amalgam/PushoutFlatReading — the RUN READING structure, its transports, and the
`id` / `gen` arms with the flat identity collapse (WP-AMALG r30, Brick B1)

On the r30 substrate (`PushoutRunSlotReading`) this file ships the READING — the certificate that a pushout
2-cell is saturated-convertible to a flat wall/gap layout — with the two base arms of the total reader:

  * **`RunReading`** — slots + boundary reassembly equations + the convertibility to the flat layout cell.
  * **`RunReading.mapConv` / `RunReading.castTransport`** — the two transports every arm assembles through.
  * **`flatIdCollapse`** — the flat layout of identity slots collapses to the identity (cast-free: identity
    slots have equal dom/cod runs, so the layout is an endo cell on the nose).
  * **`idReading`** — the `id` arm: an identity 2-cell reads into its segmentation's identity slots.
  * **`genReading`** — the `gen` arm: a reconstructed 2-generator reads into ONE slot (its boundary is
    wall-free by the shipped word invariant `pushoutTwoGen_words_wallFree` + `interpretWordFrom_wallCount`).
  * **`hcompIdNilLeftConv` / `whiskerLeftHcompFuse`** — the head-absorption engines the whisker arms consume:
    an empty-1-cell left factor is inert, and a left whisker FUSES into the HEAD factor of a horizontal
    composite (via the Godement associator `hcompAssoc`).

Raw Lean 4 + Init.  Per-declaration `#assert_no_axioms` gated in the audit twin. -/

namespace FX1Poly.Polygraph.Amalgam

open FX1Poly.Polygraph

/-! ## The reading -/

/-- ★★ **The RUN READING** of a pushout 2-cell — the certificate that the cell is saturated-convertible (over
the REAL-law relation) to a flat wall/gap layout: the slots, the boundary reassembly equations, and the
convertibility to the flat layout cell (cast onto the cell's own boundary). -/
structure RunReading
    {sourcePath targetPath : ModalityPath involutionMonadPushout.toModeGraph monadPushMode monadPushMode}
    (cell : RawTwoCellExpr involutionMonadPushout.toModeSignature sourcePath targetPath) : Type where
  /-- The head gap slot. -/
  headSlot : GapSlot
  /-- The tail gap slots (one `s`-wall before each). -/
  tailSlots : List GapSlot
  /-- The domain reassembly equation. -/
  domEq : flatSlotsDom headSlot tailSlots = sourcePath
  /-- The codomain reassembly equation. -/
  codEq : flatSlotsCod headSlot tailSlots = targetPath
  /-- The convertibility to the flat layout cell. -/
  conv : SaturatedConvOver involutionMonadPushout.toModeSignature crossPairRealPushoutRel cell
      (RawTwoCellExpr.castBoundary domEq codEq (flatSlotsCell headSlot tailSlots))

/-- Transport a reading along a convertibility into the read cell. -/
def RunReading.mapConv
    {sourcePath targetPath : ModalityPath involutionMonadPushout.toModeGraph monadPushMode monadPushMode}
    {cellA cellB : RawTwoCellExpr involutionMonadPushout.toModeSignature sourcePath targetPath}
    (convBA : SaturatedConvOver involutionMonadPushout.toModeSignature crossPairRealPushoutRel cellB cellA)
    (reading : RunReading cellA) : RunReading cellB where
  headSlot := reading.headSlot
  tailSlots := reading.tailSlots
  domEq := reading.domEq
  codEq := reading.codEq
  conv := SaturatedConvOver.trans convBA reading.conv

/-- Transport a reading through a boundary cast of the read cell. -/
def RunReading.castTransport
    {sourcePath sourcePath' targetPath targetPath' :
      ModalityPath involutionMonadPushout.toModeGraph monadPushMode monadPushMode}
    (hsource : sourcePath = sourcePath') (htarget : targetPath = targetPath')
    {cell : RawTwoCellExpr involutionMonadPushout.toModeSignature sourcePath targetPath}
    (reading : RunReading cell) :
    RunReading (RawTwoCellExpr.castBoundary hsource htarget cell) := by
  subst hsource
  subst htarget
  exact reading

/-! ## The `id` arm -/

/-- The head wall-freeness of an all-wall-free cons list. -/
theorem allRunsWallFree_head
    {run : ModalityPath involutionMonadPushout.toModeGraph monadPushMode monadPushMode}
    {restRuns : List (ModalityPath involutionMonadPushout.toModeGraph monadPushMode monadPushMode)}
    (allWallFree : AllRunsWallFree (run :: restRuns)) : pathWallFree run :=
  match allWallFree with
  | AllRunsWallFree.cons _ _ wallFree _ => wallFree

/-- The tail wall-freeness of an all-wall-free cons list. -/
theorem allRunsWallFree_tail
    {run : ModalityPath involutionMonadPushout.toModeGraph monadPushMode monadPushMode}
    {restRuns : List (ModalityPath involutionMonadPushout.toModeGraph monadPushMode monadPushMode)}
    (allWallFree : AllRunsWallFree (run :: restRuns)) : AllRunsWallFree restRuns :=
  match allWallFree with
  | AllRunsWallFree.cons _ _ _ restWallFree => restWallFree

/-- Identity slots over a wall-free run list (structural on the LIST; the Prop witness is projected by the
inversion extractors, never matched into data). -/
def idSlotsOfRuns :
    (runs : List (ModalityPath involutionMonadPushout.toModeGraph monadPushMode monadPushMode)) →
    AllRunsWallFree runs → List GapSlot
  | [], _ => []
  | run :: restRuns, allWallFree =>
      ⟨run, run, allRunsWallFree_head allWallFree, allRunsWallFree_head allWallFree,
        RawTwoCellExpr.id (signature := involutionMonadPushout.toModeSignature) run⟩ ::
        idSlotsOfRuns restRuns (allRunsWallFree_tail allWallFree)

/-- The identity slots' domain runs are the given runs. -/
theorem idSlotsOfRuns_gapDom :
    (runs : List (ModalityPath involutionMonadPushout.toModeGraph monadPushMode monadPushMode)) →
    (allWallFree : AllRunsWallFree runs) →
    (idSlotsOfRuns runs allWallFree).map GapSlot.gapDom = runs
  | [], _ => rfl
  | run :: restRuns, allWallFree =>
      congrArg (run :: ·) (idSlotsOfRuns_gapDom restRuns (allRunsWallFree_tail allWallFree))

/-- The identity slots' codomain runs are the given runs. -/
theorem idSlotsOfRuns_gapCod :
    (runs : List (ModalityPath involutionMonadPushout.toModeGraph monadPushMode monadPushMode)) →
    (allWallFree : AllRunsWallFree runs) →
    (idSlotsOfRuns runs allWallFree).map GapSlot.gapCod = runs
  | [], _ => rfl
  | run :: restRuns, allWallFree =>
      congrArg (run :: ·) (idSlotsOfRuns_gapCod restRuns (allRunsWallFree_tail allWallFree))

/-- The identity head slot over a wall-free run. -/
def idHeadSlot (run : ModalityPath involutionMonadPushout.toModeGraph monadPushMode monadPushMode)
    (wallFree : pathWallFree run) : GapSlot :=
  ⟨run, run, wallFree, wallFree,
    RawTwoCellExpr.id (signature := involutionMonadPushout.toModeSignature) run⟩

/-- The identity slots' flat domain equals their flat codomain (their runs coincide). -/
theorem idSlots_flatDom_eq_flatCod
    (headRun : ModalityPath involutionMonadPushout.toModeGraph monadPushMode monadPushMode)
    (headWallFree : pathWallFree headRun)
    (runs : List (ModalityPath involutionMonadPushout.toModeGraph monadPushMode monadPushMode))
    (allWallFree : AllRunsWallFree runs) :
    flatSlotsDom (idHeadSlot headRun headWallFree) (idSlotsOfRuns runs allWallFree)
      = flatSlotsCod (idHeadSlot headRun headWallFree) (idSlotsOfRuns runs allWallFree) := by
  show interleaveRuns headRun ((idSlotsOfRuns runs allWallFree).map GapSlot.gapDom)
    = interleaveRuns headRun ((idSlotsOfRuns runs allWallFree).map GapSlot.gapCod)
  rw [idSlotsOfRuns_gapDom runs allWallFree, idSlotsOfRuns_gapCod runs allWallFree]

/-- ★★ **THE FLAT IDENTITY COLLAPSE** — the flat layout of identity slots is saturated-convertible to the
identity on its own domain layout (up to the dom/cod boundary cast).  Structural on the runs; each cons folds
the inert wall and the identity gap by `hcompId_conv_idComposite`, threading the tail cast out by
`hcomp_castBoundaryRight`. -/
theorem flatIdCollapse
    (headRun : ModalityPath involutionMonadPushout.toModeGraph monadPushMode monadPushMode)
    (headWallFree : pathWallFree headRun) :
    (runs : List (ModalityPath involutionMonadPushout.toModeGraph monadPushMode monadPushMode)) →
    (allWallFree : AllRunsWallFree runs) →
    SaturatedConvOver involutionMonadPushout.toModeSignature crossPairRealPushoutRel
      (flatSlotsCell (idHeadSlot headRun headWallFree) (idSlotsOfRuns runs allWallFree))
      (RawTwoCellExpr.castBoundary rfl
        (idSlots_flatDom_eq_flatCod headRun headWallFree runs allWallFree)
        (RawTwoCellExpr.id (signature := involutionMonadPushout.toModeSignature)
          (flatSlotsDom (idHeadSlot headRun headWallFree) (idSlotsOfRuns runs allWallFree))))
  | [], _ => SaturatedConvOver.refl _
  | run :: restRuns, allWallFree => by
    have tailCollapse := flatIdCollapse run (allRunsWallFree_head allWallFree) restRuns
      (allRunsWallFree_tail allWallFree)
    have innerStep :
        SaturatedConvOver involutionMonadPushout.toModeSignature crossPairRealPushoutRel
          (RawTwoCellExpr.hcomp
            (RawTwoCellExpr.id (signature := involutionMonadPushout.toModeSignature) monadPushSPath)
            (flatSlotsCell (idHeadSlot run (allRunsWallFree_head allWallFree))
              (idSlotsOfRuns restRuns (allRunsWallFree_tail allWallFree))))
          (RawTwoCellExpr.hcomp
            (RawTwoCellExpr.id (signature := involutionMonadPushout.toModeSignature) monadPushSPath)
            (RawTwoCellExpr.castBoundary rfl
              (idSlots_flatDom_eq_flatCod run (allRunsWallFree_head allWallFree) restRuns
                (allRunsWallFree_tail allWallFree))
              (RawTwoCellExpr.id (signature := involutionMonadPushout.toModeSignature)
                (flatSlotsDom (idHeadSlot run (allRunsWallFree_head allWallFree))
                  (idSlotsOfRuns restRuns (allRunsWallFree_tail allWallFree)))))) :=
      SaturatedConvOver.hcompCongrRight
        (RawTwoCellExpr.id (signature := involutionMonadPushout.toModeSignature) monadPushSPath)
        tailCollapse
    rw [RawTwoCellExpr.hcomp_castBoundaryRight] at innerStep
    have innerFolded := SaturatedConvOver.trans innerStep
      (SaturatedConvOver.castBoundaryCongr _ _
        (hcompId_conv_idComposite (signature := involutionMonadPushout.toModeSignature)
          (baseRel := crossPairRealPushoutRel) monadPushSPath
          (flatSlotsDom (idHeadSlot run (allRunsWallFree_head allWallFree))
            (idSlotsOfRuns restRuns (allRunsWallFree_tail allWallFree)))))
    have outerStep := SaturatedConvOver.hcompCongrRight
      (RawTwoCellExpr.id (signature := involutionMonadPushout.toModeSignature) headRun)
      innerFolded
    rw [RawTwoCellExpr.hcomp_castBoundaryRight] at outerStep
    refine SaturatedConvOver.trans outerStep ?_
    exact SaturatedConvOver.castBoundaryCongr _ _
      (hcompId_conv_idComposite (signature := involutionMonadPushout.toModeSignature)
        (baseRel := crossPairRealPushoutRel) headRun
        (composePath monadPushSPath
          (flatSlotsDom (idHeadSlot run (allRunsWallFree_head allWallFree))
            (idSlotsOfRuns restRuns (allRunsWallFree_tail allWallFree)))))

/-- The domain reassembly of the identity slots: the flat domain is the segmented path itself. -/
theorem idSlots_flatDom
    (path : ModalityPath involutionMonadPushout.toModeGraph monadPushMode monadPushMode) :
    flatSlotsDom (idHeadSlot (segmentRuns path).1 (segmentRuns_allWallFree path).1)
        (idSlotsOfRuns (segmentRuns path).2 (segmentRuns_allWallFree path).2)
      = path := by
  show interleaveRuns (segmentRuns path).1
      ((idSlotsOfRuns (segmentRuns path).2 (segmentRuns_allWallFree path).2).map GapSlot.gapDom) = path
  rw [idSlotsOfRuns_gapDom (segmentRuns path).2 (segmentRuns_allWallFree path).2]
  exact interleave_segmentRuns path

/-- The codomain reassembly of the identity slots. -/
theorem idSlots_flatCod
    (path : ModalityPath involutionMonadPushout.toModeGraph monadPushMode monadPushMode) :
    flatSlotsCod (idHeadSlot (segmentRuns path).1 (segmentRuns_allWallFree path).1)
        (idSlotsOfRuns (segmentRuns path).2 (segmentRuns_allWallFree path).2)
      = path := by
  show interleaveRuns (segmentRuns path).1
      ((idSlotsOfRuns (segmentRuns path).2 (segmentRuns_allWallFree path).2).map GapSlot.gapCod) = path
  rw [idSlotsOfRuns_gapCod (segmentRuns path).2 (segmentRuns_allWallFree path).2]
  exact interleave_segmentRuns path

/-- ★ **The generic id-reading conversion assembler** — from a collapse of a flat cell to a cast identity, the
identity on the common boundary converts to the cast flat cell (fresh boundary variables, so the equations
`cases` cleanly). -/
theorem idConvOfCollapse
    {flatDomPath flatCodPath boundaryPath :
      ModalityPath involutionMonadPushout.toModeGraph monadPushMode monadPushMode}
    (domEq : flatDomPath = boundaryPath) (codEq : flatCodPath = boundaryPath)
    (domCodEq : flatDomPath = flatCodPath)
    {flatCellValue :
      RawTwoCellExpr involutionMonadPushout.toModeSignature flatDomPath flatCodPath}
    (collapse : SaturatedConvOver involutionMonadPushout.toModeSignature crossPairRealPushoutRel
      flatCellValue
      (RawTwoCellExpr.castBoundary rfl domCodEq
        (RawTwoCellExpr.id (signature := involutionMonadPushout.toModeSignature) flatDomPath))) :
    SaturatedConvOver involutionMonadPushout.toModeSignature crossPairRealPushoutRel
      (RawTwoCellExpr.id (signature := involutionMonadPushout.toModeSignature) boundaryPath)
      (RawTwoCellExpr.castBoundary domEq codEq flatCellValue) := by
  cases domEq
  cases codEq
  exact SaturatedConvOver.symm collapse

/-- ★★★ **THE `id` ARM** — an identity 2-cell reads into its segmentation's identity slots: the boundary
reassembly is the segmentation round-trip and the convertibility is the flat identity collapse. -/
def idReading (path : ModalityPath involutionMonadPushout.toModeGraph monadPushMode monadPushMode) :
    RunReading (RawTwoCellExpr.id (signature := involutionMonadPushout.toModeSignature) path) where
  headSlot := idHeadSlot (segmentRuns path).1 (segmentRuns_allWallFree path).1
  tailSlots := idSlotsOfRuns (segmentRuns path).2 (segmentRuns_allWallFree path).2
  domEq := idSlots_flatDom path
  codEq := idSlots_flatCod path
  conv :=
    idConvOfCollapse (idSlots_flatDom path) (idSlots_flatCod path)
      (idSlots_flatDom_eq_flatCod (segmentRuns path).1 (segmentRuns_allWallFree path).1
        (segmentRuns path).2 (segmentRuns_allWallFree path).2)
      (flatIdCollapse (segmentRuns path).1 (segmentRuns_allWallFree path).1
        (segmentRuns path).2 (segmentRuns_allWallFree path).2)

/-! ## The `gen` arm -/

/-- A reconstructed 2-generator's SOURCE boundary is wall-free — its stored `lhs` word has zero walls
(`pushoutTwoGen_words_wallFree`), and the interpreter carries word wall count to path wall count. -/
theorem genSourceWallFree
    {sourceMode targetMode : Fin involutionMonadPushout.modeCount}
    {sourcePath targetPath : ModalityPath involutionMonadPushout.toModeGraph sourceMode targetMode}
    (generator : involutionMonadPushout.ReconstructedTwoCell sourcePath targetPath) :
    pathWallFree sourcePath :=
  pathWallFree_of_wallCountZero sourcePath
    ((interpretWordFrom_wallCount (involutionMonadPushout.twoCellGenerators.get generator.val).lhs
        sourceMode targetMode sourcePath generator.property.1).trans
      (pushoutTwoGen_words_wallFree generator.val).1)

/-- A reconstructed 2-generator's TARGET boundary is wall-free (`rhs` word, dually). -/
theorem genTargetWallFree
    {sourceMode targetMode : Fin involutionMonadPushout.modeCount}
    {sourcePath targetPath : ModalityPath involutionMonadPushout.toModeGraph sourceMode targetMode}
    (generator : involutionMonadPushout.ReconstructedTwoCell sourcePath targetPath) :
    pathWallFree targetPath :=
  pathWallFree_of_wallCountZero targetPath
    ((interpretWordFrom_wallCount (involutionMonadPushout.twoCellGenerators.get generator.val).rhs
        sourceMode targetMode targetPath generator.property.2).trans
      (pushoutTwoGen_words_wallFree generator.val).2)

/-- ★★★ **THE `gen` ARM** — a reconstructed 2-generator reads into ONE slot: its boundary is wall-free
(`genSourceWallFree` / `genTargetWallFree`), the reassembly equations are definitional, and the convertibility
is reflexivity. -/
def genReading
    {sourcePath targetPath : ModalityPath involutionMonadPushout.toModeGraph monadPushMode monadPushMode}
    (generator : involutionMonadPushout.ReconstructedTwoCell sourcePath targetPath) :
    RunReading (RawTwoCellExpr.gen (signature := involutionMonadPushout.toModeSignature) generator) where
  headSlot :=
    ⟨sourcePath, targetPath, genSourceWallFree generator, genTargetWallFree generator,
      RawTwoCellExpr.gen (signature := involutionMonadPushout.toModeSignature) generator⟩
  tailSlots := []
  domEq := rfl
  codEq := rfl
  conv := SaturatedConvOver.refl _

/-! ## The head-absorption engines (the whisker arms' fuel) -/

/-- An empty-1-cell LEFT factor of a horizontal composite is inert: `hcomp (id nil) Y ≈ Y`.  The whiskered
identity reduces (`whiskerRightId` at the empty path), `vcompIdLeft` drops it, and the empty left whisker
strips (`whiskerLeftUnit`). -/
theorem hcompIdNilLeftConv {signature : ModeSignature} {baseRel : CellRel signature}
    {oneMode targetMode : signature.graph.Mode}
    {bodyDom bodyCod : ModalityPath signature.graph oneMode targetMode}
    (body : RawTwoCellExpr signature bodyDom bodyCod) :
    SaturatedConvOver signature baseRel
      (RawTwoCellExpr.hcomp
        (RawTwoCellExpr.id (ModalityPath.nil (graph := signature.graph) oneMode)) body)
      body :=
  SaturatedConvOver.trans
    (SaturatedConvOver.ofConv (TwoCellConv.ofStep
      (TwoCellStep.vcompCongrLeft (RawTwoCellExpr.whiskerLeft (ModalityPath.nil oneMode) body)
        (TwoCellStep.whiskerRightId (ModalityPath.nil oneMode) bodyDom))))
    (SaturatedConvOver.trans
      (SaturatedConvOver.ofConv (TwoCellConv.ofStep
        (TwoCellStep.vcompIdLeft (RawTwoCellExpr.whiskerLeft (ModalityPath.nil oneMode) body))))
      (SaturatedConvOver.ofFull (TwoCellConvFull.whiskerLeftUnit body)))

/-- ★★ **THE HEAD FUSE** — a left whisker fuses into the HEAD factor of a horizontal composite:
`oc ◁ (A ⊠ B) ≈ (oc ◁ A) ⊠ B` up to the associator cast.  Via the `id`-whisker bridge
(`whiskerLeft_conv_hcompIdLeading`) and the Godement associator (`hcompAssoc`). -/
theorem whiskerLeftHcompFuse {signature : ModeSignature} {baseRel : CellRel signature}
    {frameMode sourceMode middleMode targetMode : signature.graph.Mode}
    (oneCell : ModalityPath signature.graph frameMode sourceMode)
    {oneCellADom oneCellACod : ModalityPath signature.graph sourceMode middleMode}
    {oneCellBDom oneCellBCod : ModalityPath signature.graph middleMode targetMode}
    (cellA : RawTwoCellExpr signature oneCellADom oneCellACod)
    (cellB : RawTwoCellExpr signature oneCellBDom oneCellBCod) :
    SaturatedConvOver signature baseRel
      (RawTwoCellExpr.whiskerLeft oneCell (RawTwoCellExpr.hcomp cellA cellB))
      (RawTwoCellExpr.castBoundary
        (composePath_assoc oneCell oneCellADom oneCellBDom)
        (composePath_assoc oneCell oneCellACod oneCellBCod)
        (RawTwoCellExpr.hcomp (RawTwoCellExpr.whiskerLeft oneCell cellA) cellB)) := by
  refine SaturatedConvOver.trans
    (whiskerLeft_conv_hcompIdLeading oneCell (RawTwoCellExpr.hcomp cellA cellB)) ?_
  refine SaturatedConvOver.trans
    (SaturatedConvOver.ofFull (hcompAssoc (RawTwoCellExpr.id oneCell) cellA cellB)) ?_
  exact SaturatedConvOver.castBoundaryCongr
    (composePath_assoc oneCell oneCellADom oneCellBDom)
    (composePath_assoc oneCell oneCellACod oneCellBCod)
    (SaturatedConvOver.hcompCongrLeft
      (SaturatedConvOver.symm (whiskerLeft_conv_hcompIdLeading oneCell cellA)) cellB)

/-! ## Honesty marker -/

/-- ★★ **Honesty marker — the RUN READING with its `id` / `gen` arms and head-absorption engines SHIPS
(WP-AMALG r30, Brick B1).**  `= true`.  `RunReading` (slots + reassembly + convertibility over the REAL-law
relation), the two transports (`mapConv` / `castTransport`), the cast-free flat identity collapse
(`flatIdCollapse`) feeding the `id` arm (`idReading`, keyed to the segmentation round-trip), the `gen` arm
(`genReading`, single slot, wall-freeness by the shipped word invariant), and the head-absorption engines
(`hcompIdNilLeftConv`, `whiskerLeftHcompFuse` via the Godement associator).  The whisker and vcomp arms are the
successor bricks; NO master flips here.  `= true`. -/
def fxAmalg_hasFlatReadingBaseArms : Bool := true

end FX1Poly.Polygraph.Amalgam
