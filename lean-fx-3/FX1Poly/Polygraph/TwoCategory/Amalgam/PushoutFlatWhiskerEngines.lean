import FX1Poly.Polygraph.TwoCategory.Amalgam.PushoutFlatReading
import FX1Poly.Polygraph.TwoCategory.Amalgam.PushoutWhiskerRightAppend

/-! # Polygraph/TwoCategory/Amalgam/PushoutFlatWhiskerEngines — the whisker arms of the flat reader: per-letter
`s` / `t` engines both sides, and the fueled per-letter peels (WP-AMALG r30, Brick B2)

The r21/r22 junction-merge rounds shipped the whisker arms on the slot-count-keyed subtype; this file ships them
on the r30 BOUNDARY-DETERMINED flat reading, per-letter:

  * **`readingConsSlot`** — the reading combinator: a slot horizontally prepended (through an `s`-wall) onto a
    read cell reads as the consed slot list.
  * **left `s`** (`whiskerLeftSCore`) — an `s`-frame PREPENDS an empty gap slot.
  * **left `t`** (`whiskerLeftTCore`) — a `t`-frame FUSES into the HEAD payload (`whiskerLeftHcompFuse`).
  * **right `s`** (`whiskerRightSCore`) — an `s`-frame APPENDS an empty gap slot at the tail, the frame pushed
    to the innermost factor by the shipped `whiskerRight_conv_hcompRight`.
  * **right `t`** (`whiskerRightTCore`) — a `t`-frame FUSES into the LAST payload, same push engine.
  * **`readingWhiskerLeft` / `readingWhiskerRight`** — the fueled per-letter peels: an arbitrary frame 1-cell
    peels letter-by-letter through `whiskerLeftComp` / `whiskerRightComp`, each letter dispatched to its
    engine by the two-letter alphabet.

Every engine consumes the reading transports (`mapConv` / `castTransport`); the junction bookkeeping is the
`castBoundary` algebra (`whiskerLeftCastBoundaryEq` / `whiskerRightCastBoundaryEq` / `hcomp_castBoundaryRight` /
`castBoundary_trans`).

Raw Lean 4 + Init.  STRUCTURAL (fuel `Nat` on the frame length, honest).  Per-declaration `#assert_no_axioms`
gated in the audit twin. -/

namespace FX1Poly.Polygraph.Amalgam

open FX1Poly.Polygraph

/-! ## The empty gap slot and shared path algebra -/

/-- The empty gap slot (an empty run on both sides, identity payload). -/
def emptyGapSlot : GapSlot :=
  ⟨ModalityPath.nil (graph := involutionMonadPushout.toModeGraph) monadPushMode,
    ModalityPath.nil (graph := involutionMonadPushout.toModeGraph) monadPushMode,
    True.intro, True.intro,
    RawTwoCellExpr.id (signature := involutionMonadPushout.toModeSignature)
      (ModalityPath.nil (graph := involutionMonadPushout.toModeGraph) monadPushMode)⟩

/-- Prepending a front run to the head run distributes over the interleave (`composePath` associativity). -/
theorem interleaveRuns_frontRun
    (frontRun headRun : ModalityPath involutionMonadPushout.toModeGraph monadPushMode monadPushMode) :
    (restRuns : List (ModalityPath involutionMonadPushout.toModeGraph monadPushMode monadPushMode)) →
    interleaveRuns (composePath frontRun headRun) restRuns
      = composePath frontRun (interleaveRuns headRun restRuns)
  | [] => rfl
  | _ :: _ => composePath_assoc frontRun headRun _

/-! ## The reading cons combinator -/

/-- ★★ **The reading CONS combinator** — a slot horizontally prepended (through an `s`-wall) onto a read cell
reads as the consed slot list: `slot.payload ⊠ id s ⊠ Y` reads with slots `slot :: (reading of Y)`. -/
def readingConsSlot (slot : GapSlot)
    {innerDom innerCod : ModalityPath involutionMonadPushout.toModeGraph monadPushMode monadPushMode}
    {innerCell : RawTwoCellExpr involutionMonadPushout.toModeSignature innerDom innerCod}
    (innerReading : RunReading innerCell) :
    RunReading
      (RawTwoCellExpr.hcomp slot.payload
        (RawTwoCellExpr.hcomp
          (RawTwoCellExpr.id (signature := involutionMonadPushout.toModeSignature) monadPushSPath)
          innerCell)) where
  headSlot := slot
  tailSlots := innerReading.headSlot :: innerReading.tailSlots
  domEq :=
    congrArg (fun tail => composePath slot.gapDom (composePath monadPushSPath tail)) innerReading.domEq
  codEq :=
    congrArg (fun tail => composePath slot.gapCod (composePath monadPushSPath tail)) innerReading.codEq
  conv := by
    have step := SaturatedConvOver.hcompCongrRight slot.payload
      (SaturatedConvOver.hcompCongrRight
        (RawTwoCellExpr.id (signature := involutionMonadPushout.toModeSignature) monadPushSPath)
        innerReading.conv)
    rw [RawTwoCellExpr.hcomp_castBoundaryRight, RawTwoCellExpr.hcomp_castBoundaryRight] at step
    exact step

/-! ## The left engines -/

/-- ★★ **The left `s` engine** — an `s`-frame PREPENDS an empty gap slot: `whiskerLeft s Y` reads with slots
`emptyGapSlot :: (reading of Y)`. -/
def whiskerLeftSEngine
    {innerDom innerCod : ModalityPath involutionMonadPushout.toModeGraph monadPushMode monadPushMode}
    {innerCell : RawTwoCellExpr involutionMonadPushout.toModeSignature innerDom innerCod}
    (innerReading : RunReading innerCell) :
    RunReading (RawTwoCellExpr.whiskerLeft (signature := involutionMonadPushout.toModeSignature)
      monadPushSPath innerCell) :=
  RunReading.mapConv
    (SaturatedConvOver.trans
      (whiskerLeft_conv_hcompIdLeading monadPushSPath innerCell)
      (SaturatedConvOver.symm
        (hcompIdNilLeftConv
          (RawTwoCellExpr.hcomp
            (RawTwoCellExpr.id (signature := involutionMonadPushout.toModeSignature) monadPushSPath)
            innerCell))))
    (readingConsSlot emptyGapSlot innerReading)

/-- The head-fused slot of a `t`-frame: the frame composes onto both runs and the payload is left-whiskered. -/
def tFuseHeadSlot (slot : GapSlot) : GapSlot :=
  ⟨composePath monadPushTPath slot.gapDom, composePath monadPushTPath slot.gapCod,
    pathWallFree_composePath_join monadPushTPath slot.gapDom monadPushTPath_wallFree slot.domWallFree,
    pathWallFree_composePath_join monadPushTPath slot.gapCod monadPushTPath_wallFree slot.codWallFree,
    RawTwoCellExpr.whiskerLeft (signature := involutionMonadPushout.toModeSignature)
      monadPushTPath slot.payload⟩

/-- ★★ **The left `t` engine, CORE** — a `t`-frame FUSES into the HEAD payload of a flat layout. -/
def whiskerLeftTCore (headSlot : GapSlot) :
    (tailSlots : List GapSlot) →
    RunReading (RawTwoCellExpr.whiskerLeft (signature := involutionMonadPushout.toModeSignature)
      monadPushTPath (flatSlotsCell headSlot tailSlots))
  | [] =>
    { headSlot := tFuseHeadSlot headSlot
      tailSlots := []
      domEq := rfl
      codEq := rfl
      conv := SaturatedConvOver.refl _ }
  | nextSlot :: restSlots =>
    { headSlot := tFuseHeadSlot headSlot
      tailSlots := nextSlot :: restSlots
      domEq := (interleaveRuns_frontRun monadPushTPath headSlot.gapDom
          ((nextSlot :: restSlots).map GapSlot.gapDom)).symm
      codEq := (interleaveRuns_frontRun monadPushTPath headSlot.gapCod
          ((nextSlot :: restSlots).map GapSlot.gapCod)).symm
      conv :=
        whiskerLeftHcompFuse monadPushTPath headSlot.payload
          (RawTwoCellExpr.hcomp
            (RawTwoCellExpr.id (signature := involutionMonadPushout.toModeSignature) monadPushSPath)
            (flatSlotsCell nextSlot restSlots)) }

/-- ★★ **The left `t` engine** — assembled onto an arbitrary read cell. -/
def whiskerLeftTEngine
    {innerDom innerCod : ModalityPath involutionMonadPushout.toModeGraph monadPushMode monadPushMode}
    {innerCell : RawTwoCellExpr involutionMonadPushout.toModeSignature innerDom innerCod}
    (innerReading : RunReading innerCell) :
    RunReading (RawTwoCellExpr.whiskerLeft (signature := involutionMonadPushout.toModeSignature)
      monadPushTPath innerCell) := by
  have chain := SaturatedConvOver.whiskerLeftCongr
    (signature := involutionMonadPushout.toModeSignature) (baseRel := crossPairRealPushoutRel)
    monadPushTPath innerReading.conv
  rw [whiskerLeftCastBoundaryEq] at chain
  exact RunReading.mapConv chain
    (RunReading.castTransport
      (congrArg (composePath monadPushTPath) innerReading.domEq)
      (congrArg (composePath monadPushTPath) innerReading.codEq)
      (whiskerLeftTCore innerReading.headSlot innerReading.tailSlots))

/-! ## The right engines -/

/-- The tail-fused slot of a right `t`-frame: the frame composes onto both runs at the RIGHT and the payload is
right-whiskered. -/
def tFuseTailSlot (slot : GapSlot) : GapSlot :=
  ⟨composePath slot.gapDom monadPushTPath, composePath slot.gapCod monadPushTPath,
    pathWallFree_composePath_join slot.gapDom monadPushTPath slot.domWallFree monadPushTPath_wallFree,
    pathWallFree_composePath_join slot.gapCod monadPushTPath slot.codWallFree monadPushTPath_wallFree,
    RawTwoCellExpr.whiskerRight (signature := involutionMonadPushout.toModeSignature)
      monadPushTPath slot.payload⟩

/-- ★★ **The right `t` engine, CORE** — a right `t`-frame pushes through the layout to the LAST payload
(`whiskerRight_conv_hcompRight`) and fuses there. -/
def whiskerRightTCore (headSlot : GapSlot) :
    (tailSlots : List GapSlot) →
    RunReading (RawTwoCellExpr.whiskerRight (signature := involutionMonadPushout.toModeSignature)
      monadPushTPath (flatSlotsCell headSlot tailSlots))
  | [] =>
    { headSlot := tFuseTailSlot headSlot
      tailSlots := []
      domEq := rfl
      codEq := rfl
      conv := SaturatedConvOver.refl _ }
  | nextSlot :: restSlots => by
    have innerReading := whiskerRightTCore nextSlot restSlots
    have pushOuter := whiskerRight_conv_hcompRight
      (baseRel := crossPairRealPushoutRel) monadPushTPath headSlot.payload
      (RawTwoCellExpr.hcomp
        (RawTwoCellExpr.id (signature := involutionMonadPushout.toModeSignature) monadPushSPath)
        (flatSlotsCell nextSlot restSlots))
    have pushInner := whiskerRight_conv_hcompRight
      (baseRel := crossPairRealPushoutRel) monadPushTPath
      (RawTwoCellExpr.id (signature := involutionMonadPushout.toModeSignature) monadPushSPath)
      (flatSlotsCell nextSlot restSlots)
    have innerChain := SaturatedConvOver.hcompCongrRight headSlot.payload pushInner
    rw [RawTwoCellExpr.hcomp_castBoundaryRight] at innerChain
    have wholeChain := SaturatedConvOver.trans pushOuter
      (SaturatedConvOver.castBoundaryCongr _ _ innerChain)
    rw [RawTwoCellExpr.castBoundary_trans] at wholeChain
    exact RunReading.mapConv wholeChain
      (RunReading.castTransport _ _ (readingConsSlot headSlot innerReading))

/-- ★★ **The right `t` engine** — assembled onto an arbitrary read cell. -/
def whiskerRightTEngine
    {innerDom innerCod : ModalityPath involutionMonadPushout.toModeGraph monadPushMode monadPushMode}
    {innerCell : RawTwoCellExpr involutionMonadPushout.toModeSignature innerDom innerCod}
    (innerReading : RunReading innerCell) :
    RunReading (RawTwoCellExpr.whiskerRight (signature := involutionMonadPushout.toModeSignature)
      monadPushTPath innerCell) := by
  have chain := SaturatedConvOver.whiskerRightCongr
    (signature := involutionMonadPushout.toModeSignature) (baseRel := crossPairRealPushoutRel)
    monadPushTPath innerReading.conv
  rw [whiskerRightCastBoundaryEq] at chain
  exact RunReading.mapConv chain
    (RunReading.castTransport
      (congrArg (composePath · monadPushTPath) innerReading.domEq)
      (congrArg (composePath · monadPushTPath) innerReading.codEq)
      (whiskerRightTCore innerReading.headSlot innerReading.tailSlots))

/-- ★★ **The right `s` engine, CORE** — a right `s`-frame pushes through the layout and APPENDS an empty gap
slot at the tail. -/
def whiskerRightSCore (headSlot : GapSlot) :
    (tailSlots : List GapSlot) →
    RunReading (RawTwoCellExpr.whiskerRight (signature := involutionMonadPushout.toModeSignature)
      monadPushSPath (flatSlotsCell headSlot tailSlots))
  | [] =>
    { headSlot := headSlot
      tailSlots := [emptyGapSlot]
      domEq := rfl
      codEq := rfl
      conv :=
        SaturatedConvOver.trans
          (whiskerRight_conv_hcompIdTrailing monadPushSPath headSlot.payload)
          (SaturatedConvOver.hcompCongrRight headSlot.payload
            (SaturatedConvOver.symm
              (hcompId_conv_idComposite (signature := involutionMonadPushout.toModeSignature)
                (baseRel := crossPairRealPushoutRel) monadPushSPath
                (ModalityPath.nil (graph := involutionMonadPushout.toModeGraph) monadPushMode)))) }
  | nextSlot :: restSlots => by
    have innerReading := whiskerRightSCore nextSlot restSlots
    have pushOuter := whiskerRight_conv_hcompRight
      (baseRel := crossPairRealPushoutRel) monadPushSPath headSlot.payload
      (RawTwoCellExpr.hcomp
        (RawTwoCellExpr.id (signature := involutionMonadPushout.toModeSignature) monadPushSPath)
        (flatSlotsCell nextSlot restSlots))
    have pushInner := whiskerRight_conv_hcompRight
      (baseRel := crossPairRealPushoutRel) monadPushSPath
      (RawTwoCellExpr.id (signature := involutionMonadPushout.toModeSignature) monadPushSPath)
      (flatSlotsCell nextSlot restSlots)
    have innerChain := SaturatedConvOver.hcompCongrRight headSlot.payload pushInner
    rw [RawTwoCellExpr.hcomp_castBoundaryRight] at innerChain
    have wholeChain := SaturatedConvOver.trans pushOuter
      (SaturatedConvOver.castBoundaryCongr _ _ innerChain)
    rw [RawTwoCellExpr.castBoundary_trans] at wholeChain
    exact RunReading.mapConv wholeChain
      (RunReading.castTransport _ _ (readingConsSlot headSlot innerReading))

/-- ★★ **The right `s` engine** — assembled onto an arbitrary read cell. -/
def whiskerRightSEngine
    {innerDom innerCod : ModalityPath involutionMonadPushout.toModeGraph monadPushMode monadPushMode}
    {innerCell : RawTwoCellExpr involutionMonadPushout.toModeSignature innerDom innerCod}
    (innerReading : RunReading innerCell) :
    RunReading (RawTwoCellExpr.whiskerRight (signature := involutionMonadPushout.toModeSignature)
      monadPushSPath innerCell) := by
  have chain := SaturatedConvOver.whiskerRightCongr
    (signature := involutionMonadPushout.toModeSignature) (baseRel := crossPairRealPushoutRel)
    monadPushSPath innerReading.conv
  rw [whiskerRightCastBoundaryEq] at chain
  exact RunReading.mapConv chain
    (RunReading.castTransport
      (congrArg (composePath · monadPushSPath) innerReading.domEq)
      (congrArg (composePath · monadPushSPath) innerReading.codEq)
      (whiskerRightSCore innerReading.headSlot innerReading.tailSlots))

/-! ## The fueled per-letter peels -/

/-- ★★★ **The LEFT whisker peel (fueled)** — an arbitrary frame 1-cell peels letter-by-letter
(`whiskerLeftComp`, splitting the head letter off), each letter dispatched to its `s` / `t` engine.  Fuel is the
frame length (honest structural `Nat`). -/
def readingWhiskerLeftFueled
    {innerDom innerCod : ModalityPath involutionMonadPushout.toModeGraph monadPushMode monadPushMode}
    {innerCell : RawTwoCellExpr involutionMonadPushout.toModeSignature innerDom innerCod} :
    (fuel : Nat) →
    (frame : ModalityPath involutionMonadPushout.toModeGraph monadPushMode monadPushMode) →
    frame.length ≤ fuel →
    RunReading innerCell →
    RunReading (RawTwoCellExpr.whiskerLeft (signature := involutionMonadPushout.toModeSignature)
      frame innerCell)
  | fuel, .nil _, _, innerReading =>
      RunReading.mapConv
        (SaturatedConvOver.ofFull (TwoCellConvFull.whiskerLeftUnit innerCell))
        innerReading
  | 0, .cons _ rest, hfuel, _ =>
      absurd hfuel (Nat.not_succ_le_zero rest.length)
  | fuel + 1, @ModalityPath.cons _ _ middleMode _ letter rest, hfuel, innerReading => by
    obtain rfl := pushoutModeUnique middleMode
    have restReading := readingWhiskerLeftFueled fuel rest (Nat.le_of_succ_le_succ hfuel) innerReading
    have letterReading :
        RunReading (RawTwoCellExpr.whiskerLeft (signature := involutionMonadPushout.toModeSignature)
          (ModalityPath.cons letter
            (ModalityPath.nil (graph := involutionMonadPushout.toModeGraph) monadPushMode))
          (RawTwoCellExpr.whiskerLeft (signature := involutionMonadPushout.toModeSignature)
            rest innerCell)) := by
      match letter with
      | ⟨⟨0, _⟩, _⟩ => exact whiskerLeftSEngine restReading
      | ⟨⟨1, _⟩, _⟩ => exact whiskerLeftTEngine restReading
      | ⟨⟨index + 2, isLtBig⟩, _⟩ =>
        exact absurd (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ isLtBig)) (Nat.not_lt_zero index)
    have peelConv := SaturatedConvOver.ofFull (baseRel := crossPairRealPushoutRel)
      (TwoCellConvFull.whiskerLeftComp
        (ModalityPath.cons letter
          (ModalityPath.nil (graph := involutionMonadPushout.toModeGraph) monadPushMode))
        rest innerCell)
    exact RunReading.mapConv peelConv (RunReading.castTransport _ _ letterReading)

/-- ★★★ **The RIGHT whisker peel (fueled)** — the right dual: the frame peels letter-by-letter
(`whiskerRightComp`, splitting the head letter off as the INNER whisker), each letter dispatched to its engine. -/
def readingWhiskerRightFueled
    {innerDom innerCod : ModalityPath involutionMonadPushout.toModeGraph monadPushMode monadPushMode}
    {innerCell : RawTwoCellExpr involutionMonadPushout.toModeSignature innerDom innerCod} :
    (fuel : Nat) →
    (frame : ModalityPath involutionMonadPushout.toModeGraph monadPushMode monadPushMode) →
    frame.length ≤ fuel →
    RunReading innerCell →
    RunReading (RawTwoCellExpr.whiskerRight (signature := involutionMonadPushout.toModeSignature)
      frame innerCell)
  | fuel, .nil _, _, innerReading => by
    refine RunReading.mapConv
      (SaturatedConvOver.ofFull (TwoCellConvFull.whiskerRightUnit innerCell)) ?_
    exact RunReading.castTransport _ _ innerReading
  | 0, .cons _ rest, hfuel, _ =>
      absurd hfuel (Nat.not_succ_le_zero rest.length)
  | fuel + 1, @ModalityPath.cons _ _ middleMode _ letter rest, hfuel, innerReading => by
    obtain rfl := pushoutModeUnique middleMode
    have letterReading :
        RunReading (RawTwoCellExpr.whiskerRight (signature := involutionMonadPushout.toModeSignature)
          (ModalityPath.cons letter
            (ModalityPath.nil (graph := involutionMonadPushout.toModeGraph) monadPushMode))
          innerCell) := by
      match letter with
      | ⟨⟨0, _⟩, _⟩ => exact whiskerRightSEngine innerReading
      | ⟨⟨1, _⟩, _⟩ => exact whiskerRightTEngine innerReading
      | ⟨⟨index + 2, isLtBig⟩, _⟩ =>
        exact absurd (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ isLtBig)) (Nat.not_lt_zero index)
    have restReading := readingWhiskerRightFueled fuel rest (Nat.le_of_succ_le_succ hfuel) letterReading
    have peelConv := SaturatedConvOver.ofFull (baseRel := crossPairRealPushoutRel)
      (TwoCellConvFull.whiskerRightComp
        (ModalityPath.cons letter
          (ModalityPath.nil (graph := involutionMonadPushout.toModeGraph) monadPushMode))
        rest innerCell)
    exact RunReading.mapConv peelConv (RunReading.castTransport _ _ restReading)

/-- The left whisker peel at its own length fuel. -/
def readingWhiskerLeft
    (frame : ModalityPath involutionMonadPushout.toModeGraph monadPushMode monadPushMode)
    {innerDom innerCod : ModalityPath involutionMonadPushout.toModeGraph monadPushMode monadPushMode}
    {innerCell : RawTwoCellExpr involutionMonadPushout.toModeSignature innerDom innerCod}
    (innerReading : RunReading innerCell) :
    RunReading (RawTwoCellExpr.whiskerLeft (signature := involutionMonadPushout.toModeSignature)
      frame innerCell) :=
  readingWhiskerLeftFueled frame.length frame (Nat.le_refl _) innerReading

/-- The right whisker peel at its own length fuel. -/
def readingWhiskerRight
    (frame : ModalityPath involutionMonadPushout.toModeGraph monadPushMode monadPushMode)
    {innerDom innerCod : ModalityPath involutionMonadPushout.toModeGraph monadPushMode monadPushMode}
    {innerCell : RawTwoCellExpr involutionMonadPushout.toModeSignature innerDom innerCod}
    (innerReading : RunReading innerCell) :
    RunReading (RawTwoCellExpr.whiskerRight (signature := involutionMonadPushout.toModeSignature)
      frame innerCell) :=
  readingWhiskerRightFueled frame.length frame (Nat.le_refl _) innerReading

/-! ## Honesty marker -/

/-- ★★ **Honesty marker — the flat reader's WHISKER ENGINES ship (WP-AMALG r30, Brick B2).**  `= true`.  The
reading cons combinator (`readingConsSlot`), the four per-letter engines (left/right × `s`/`t`: prepend an
empty slot, fuse into the head payload, append an empty slot, fuse into the last payload — the junction
bookkeeping carried by the shipped `castBoundary` algebra and the shipped push engine
`whiskerRight_conv_hcompRight`), and the two fueled per-letter peels (`readingWhiskerLeft` /
`readingWhiskerRight`, honest structural fuel on the frame length, letters dispatched by the two-letter
alphabet).  The vcomp zip and the total reader are the successor brick; NO master flips here.  `= true`. -/
def fxAmalg_hasFlatWhiskerEngines : Bool := true

end FX1Poly.Polygraph.Amalgam
