import FX1Poly.Polygraph.TwoCategory.Amalgam.PushoutFlatWhiskerEngines

/-! # Polygraph/TwoCategory/Amalgam/PushoutFlatVcompZip — THE VCOMP PAYLOAD ZIP and the TOTAL flat reader
(WP-AMALG r30, Brick B3)

THE JAM-A WALL, taken: the dispatch payload of a vertically-composed cell ZIPS from the two sub-cells'
payloads at the seam.  On the r30 boundary-determined flat reading the r19 "common-refinement re-slice"
obstruction is GONE — two readings meeting at the shared middle 1-cell automatically share their gap skeleton
(`flatBoundary_slots_aligned`, Brick A) — so the zip is a clean structural recursion firing the free
interchange per gap:

  * **`zipHeadSlot` / `zipTailSlots`** — the per-gap vertical composites of two aligned slot lists.
  * **`zipReading`** — ★ THE PAYLOAD ZIP: the vertical composite of two flat layout cells (aligned at the
    seam) READS as the zipped slots — per gap, the interchange (`SaturatedConvOver.vcompHcompSplit`, the
    Godement law) splits the seam, the inert walls collapse (`vcompIdLeft`), and the reading cons combinator
    reassembles.  This is `dispatch(vcomp p q) = seamSplice(dispatch p, dispatch q)` at the flat reading.
  * **`vcompReading`** — the vcomp ARM: two readings of composable cells zip into a reading of their
    vertical composite (the alignment supplied by parsing uniqueness).
  * **`readCellFueled` / `readCellIntoSlots`** — ★★ THE TOTAL READER: EVERY pushout 2-cell reads into a flat
    wall/gap layout with wall-free gap payloads — `gen` / `id` / `vcomp` / `whiskerLeft` / `whiskerRight` all
    covered (honest structural fuel on the cell size).

Raw Lean 4 + Init.  Per-declaration `#assert_no_axioms` gated in the audit twin. -/

namespace FX1Poly.Polygraph.Amalgam

open FX1Poly.Polygraph

/-! ## The cast algebra of the seam -/

/-- A domain-only boundary cast distributes over a horizontal composite whose two domain components are cast
componentwise (`cases`; `rfl` — any proof of the composite equality is irrelevant). -/
theorem castBoundary_hcomp_distribute {signature : ModeSignature}
    {sourceMode middleMode targetMode : signature.graph.Mode}
    {headDom headDom' : ModalityPath signature.graph sourceMode middleMode}
    {tailDom tailDom' : ModalityPath signature.graph middleMode targetMode}
    {headCod : ModalityPath signature.graph sourceMode middleMode}
    {tailCod : ModalityPath signature.graph middleMode targetMode}
    (hHead : headDom = headDom') (hTail : tailDom = tailDom')
    (cellHead : RawTwoCellExpr signature headDom headCod)
    (cellTail : RawTwoCellExpr signature tailDom tailCod)
    (hWhole : composePath headDom tailDom = composePath headDom' tailDom') :
    RawTwoCellExpr.castBoundary hWhole rfl (RawTwoCellExpr.hcomp cellHead cellTail)
      = RawTwoCellExpr.hcomp
          (RawTwoCellExpr.castBoundary hHead rfl cellHead)
          (RawTwoCellExpr.castBoundary hTail rfl cellTail) := by
  cases hHead
  cases hTail
  rfl

/-- Two composable boundary casts merge into one outer cast with the seam mismatch pushed onto the second
factor (`cases`; `rfl`). -/
theorem vcomp_castBoundary_merge {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode}
    {upDom upCod loDom loCod boundaryDom middlePath boundaryCod :
      ModalityPath signature.graph sourceMode targetMode}
    (hUpDom : upDom = boundaryDom) (hUpCod : upCod = middlePath)
    (hLoDom : loDom = middlePath) (hLoCod : loCod = boundaryCod)
    (cellUp : RawTwoCellExpr signature upDom upCod)
    (cellLo : RawTwoCellExpr signature loDom loCod) :
    RawTwoCellExpr.vcomp
        (RawTwoCellExpr.castBoundary hUpDom hUpCod cellUp)
        (RawTwoCellExpr.castBoundary hLoDom hLoCod cellLo)
      = RawTwoCellExpr.castBoundary hUpDom hLoCod
          (RawTwoCellExpr.vcomp cellUp
            (RawTwoCellExpr.castBoundary (hLoDom.trans hUpCod.symm) rfl cellLo)) := by
  cases hUpDom
  cases hUpCod
  cases hLoDom
  cases hLoCod
  rfl

/-- Head alignment extraction from a cons-level map alignment. -/
theorem consAlign_head {upSlot loSlot : GapSlot} {upRest loRest : List GapSlot}
    (tailAlign : (upSlot :: upRest).map GapSlot.gapCod = (loSlot :: loRest).map GapSlot.gapDom) :
    upSlot.gapCod = loSlot.gapDom := by
  injection tailAlign

/-- Tail alignment extraction from a cons-level map alignment. -/
theorem consAlign_tail {upSlot loSlot : GapSlot} {upRest loRest : List GapSlot}
    (tailAlign : (upSlot :: upRest).map GapSlot.gapCod = (loSlot :: loRest).map GapSlot.gapDom) :
    upRest.map GapSlot.gapCod = loRest.map GapSlot.gapDom := by
  injection tailAlign

/-- A cell equality is a saturated convertibility (transport of `refl`). -/
theorem SaturatedConvOver.ofCellEq {signature : ModeSignature} {baseRel : CellRel signature}
    {sourceMode targetMode : signature.graph.Mode}
    {sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode}
    {cellA cellB : RawTwoCellExpr signature sourcePath targetPath} (cellsEqual : cellA = cellB) :
    SaturatedConvOver signature baseRel cellA cellB :=
  cellsEqual ▸ SaturatedConvOver.refl cellA

/-- Transport a reading along a cell equality. -/
def RunReading.cellEqTransport
    {sourcePath targetPath : ModalityPath involutionMonadPushout.toModeGraph monadPushMode monadPushMode}
    {cellA cellB : RawTwoCellExpr involutionMonadPushout.toModeSignature sourcePath targetPath}
    (cellsEqual : cellA = cellB) (reading : RunReading cellA) : RunReading cellB :=
  cellsEqual ▸ reading

/-! ## The zipped slots -/

/-- The zipped HEAD slot — the per-gap vertical composite at the aligned seam. -/
def zipHeadSlot (upSlot loSlot : GapSlot) (headAlign : upSlot.gapCod = loSlot.gapDom) : GapSlot :=
  ⟨upSlot.gapDom, loSlot.gapCod, upSlot.domWallFree, loSlot.codWallFree,
    RawTwoCellExpr.vcomp upSlot.payload
      (RawTwoCellExpr.castBoundary headAlign.symm rfl loSlot.payload)⟩

/-- The zipped TAIL slots — pointwise vertical composites of two aligned slot lists. -/
def zipTailSlots :
    (upTail loTail : List GapSlot) →
    upTail.map GapSlot.gapCod = loTail.map GapSlot.gapDom → List GapSlot
  | [], [], _ => []
  | [], _ :: _, tailAlign => Nat.noConfusion (congrArg List.length tailAlign)
  | _ :: _, [], tailAlign => Nat.noConfusion (congrArg List.length tailAlign)
  | upSlot :: upRest, loSlot :: loRest, tailAlign =>
      zipHeadSlot upSlot loSlot (consAlign_head tailAlign) ::
        zipTailSlots upRest loRest (consAlign_tail tailAlign)

/-- The zipped tail's domain runs are the upper tail's domain runs. -/
theorem zipTailSlots_gapDom :
    (upTail loTail : List GapSlot) →
    (tailAlign : upTail.map GapSlot.gapCod = loTail.map GapSlot.gapDom) →
    (zipTailSlots upTail loTail tailAlign).map GapSlot.gapDom = upTail.map GapSlot.gapDom
  | [], [], _ => rfl
  | [], _ :: _, tailAlign => Nat.noConfusion (congrArg List.length tailAlign)
  | _ :: _, [], tailAlign => Nat.noConfusion (congrArg List.length tailAlign)
  | upSlot :: upRest, _loSlot :: loRest, tailAlign =>
      congrArg (upSlot.gapDom :: ·) (zipTailSlots_gapDom upRest loRest (consAlign_tail tailAlign))

/-- The zipped tail's codomain runs are the lower tail's codomain runs. -/
theorem zipTailSlots_gapCod :
    (upTail loTail : List GapSlot) →
    (tailAlign : upTail.map GapSlot.gapCod = loTail.map GapSlot.gapDom) →
    (zipTailSlots upTail loTail tailAlign).map GapSlot.gapCod = loTail.map GapSlot.gapCod
  | [], [], _ => rfl
  | [], _ :: _, tailAlign => Nat.noConfusion (congrArg List.length tailAlign)
  | _ :: _, [], tailAlign => Nat.noConfusion (congrArg List.length tailAlign)
  | _upSlot :: upRest, loSlot :: loRest, tailAlign =>
      congrArg (loSlot.gapCod :: ·) (zipTailSlots_gapCod upRest loRest (consAlign_tail tailAlign))

/-- The seam alignment at the flat boundaries: the lower layout's domain IS the upper layout's codomain. -/
theorem flatAlignEq (upHead loHead : GapSlot) (upTail loTail : List GapSlot)
    (headAlign : upHead.gapCod = loHead.gapDom)
    (tailAlign : upTail.map GapSlot.gapCod = loTail.map GapSlot.gapDom) :
    flatSlotsDom loHead loTail = flatSlotsCod upHead upTail := by
  show interleaveRuns loHead.gapDom (loTail.map GapSlot.gapDom)
    = interleaveRuns upHead.gapCod (upTail.map GapSlot.gapCod)
  rw [← headAlign, ← tailAlign]

/-! ## ★ THE VCOMP PAYLOAD ZIP -/

/-- ★★★ **THE VCOMP PAYLOAD ZIP** — the vertical composite of two flat layout cells, aligned at the seam,
READS as the zipped slots: per gap the free interchange (`SaturatedConvOver.vcompHcompSplit`, the Godement law)
splits the seam, the inert `s`-walls collapse (`vcompIdLeft`), and the reading cons combinator reassembles.
Structural on the two aligned slot lists.  This is the r20 ceiling ledger's arm (c) — the vcomp
common-refinement zip — DISCHARGED at the boundary-determined flat reading: `dispatch(vcomp p q) =
seamSplice(dispatch p, dispatch q)`. -/
def zipReading :
    (upHead : GapSlot) → (upTail : List GapSlot) → (loHead : GapSlot) → (loTail : List GapSlot) →
    (headAlign : upHead.gapCod = loHead.gapDom) →
    (tailAlign : upTail.map GapSlot.gapCod = loTail.map GapSlot.gapDom) →
    RunReading (RawTwoCellExpr.vcomp (flatSlotsCell upHead upTail)
      (RawTwoCellExpr.castBoundary (flatAlignEq upHead loHead upTail loTail headAlign tailAlign) rfl
        (flatSlotsCell loHead loTail)))
  | upHead, [], loHead, [], headAlign, _ =>
    { headSlot := zipHeadSlot upHead loHead headAlign
      tailSlots := []
      domEq := rfl
      codEq := rfl
      conv := SaturatedConvOver.refl _ }
  | _, [], _, _ :: _, _, tailAlign => Nat.noConfusion (congrArg List.length tailAlign)
  | _, _ :: _, _, [], _, tailAlign => Nat.noConfusion (congrArg List.length tailAlign)
  | upHead, upNext :: upRest, loHead, loNext :: loRest, headAlign, tailAlign => by
    have nextAlign : upNext.gapCod = loNext.gapDom := consAlign_head tailAlign
    have restAlign : upRest.map GapSlot.gapCod = loRest.map GapSlot.gapDom := consAlign_tail tailAlign
    have innerReading := zipReading upNext upRest loNext loRest nextAlign restAlign
    have distributeOuter :
        RawTwoCellExpr.castBoundary
            (flatAlignEq upHead loHead (upNext :: upRest) (loNext :: loRest) headAlign tailAlign :
              composePath loHead.gapDom (composePath monadPushSPath (flatSlotsDom loNext loRest))
                = composePath upHead.gapCod (composePath monadPushSPath (flatSlotsCod upNext upRest))) rfl
            (RawTwoCellExpr.hcomp loHead.payload
              (RawTwoCellExpr.hcomp
                (RawTwoCellExpr.id (signature := involutionMonadPushout.toModeSignature) monadPushSPath)
                (flatSlotsCell loNext loRest)))
          = RawTwoCellExpr.hcomp
              (RawTwoCellExpr.castBoundary headAlign.symm rfl loHead.payload)
              (RawTwoCellExpr.hcomp
                (RawTwoCellExpr.castBoundary rfl rfl
                  (RawTwoCellExpr.id (signature := involutionMonadPushout.toModeSignature) monadPushSPath))
                (RawTwoCellExpr.castBoundary
                  (flatAlignEq upNext loNext upRest loRest nextAlign restAlign) rfl
                  (flatSlotsCell loNext loRest))) :=
      (castBoundary_hcomp_distribute headAlign.symm
          (congrArg (composePath monadPushSPath)
            (flatAlignEq upNext loNext upRest loRest nextAlign restAlign))
          loHead.payload
          (RawTwoCellExpr.hcomp
            (RawTwoCellExpr.id (signature := involutionMonadPushout.toModeSignature) monadPushSPath)
            (flatSlotsCell loNext loRest))
          (flatAlignEq upHead loHead (upNext :: upRest) (loNext :: loRest) headAlign tailAlign)).trans
        (congrArg
          (RawTwoCellExpr.hcomp (RawTwoCellExpr.castBoundary headAlign.symm rfl loHead.payload))
          (castBoundary_hcomp_distribute rfl
            (flatAlignEq upNext loNext upRest loRest nextAlign restAlign)
            (RawTwoCellExpr.id (signature := involutionMonadPushout.toModeSignature) monadPushSPath)
            (flatSlotsCell loNext loRest)
            (congrArg (composePath monadPushSPath)
              (flatAlignEq upNext loNext upRest loRest nextAlign restAlign))))
    refine RunReading.cellEqTransport
      (congrArg
        (RawTwoCellExpr.vcomp
          (RawTwoCellExpr.hcomp upHead.payload
            (RawTwoCellExpr.hcomp
              (RawTwoCellExpr.id (signature := involutionMonadPushout.toModeSignature) monadPushSPath)
              (flatSlotsCell upNext upRest))))
        distributeOuter.symm) ?_
    refine RunReading.mapConv ?_ (readingConsSlot (zipHeadSlot upHead loHead headAlign) innerReading)
    refine SaturatedConvOver.trans
      (SaturatedConvOver.vcompHcompSplit upHead.payload
        (RawTwoCellExpr.castBoundary headAlign.symm rfl loHead.payload)
        (RawTwoCellExpr.hcomp
          (RawTwoCellExpr.id (signature := involutionMonadPushout.toModeSignature) monadPushSPath)
          (flatSlotsCell upNext upRest))
        (RawTwoCellExpr.hcomp
          (RawTwoCellExpr.castBoundary rfl rfl
            (RawTwoCellExpr.id (signature := involutionMonadPushout.toModeSignature) monadPushSPath))
          (RawTwoCellExpr.castBoundary
            (flatAlignEq upNext loNext upRest loRest nextAlign restAlign) rfl
            (flatSlotsCell loNext loRest)))) ?_
    refine SaturatedConvOver.hcompCongrRight
      (RawTwoCellExpr.vcomp upHead.payload
        (RawTwoCellExpr.castBoundary headAlign.symm rfl loHead.payload)) ?_
    refine SaturatedConvOver.trans
      (SaturatedConvOver.vcompHcompSplit
        (RawTwoCellExpr.id (signature := involutionMonadPushout.toModeSignature) monadPushSPath)
        (RawTwoCellExpr.castBoundary rfl rfl
          (RawTwoCellExpr.id (signature := involutionMonadPushout.toModeSignature) monadPushSPath))
        (flatSlotsCell upNext upRest)
        (RawTwoCellExpr.castBoundary
          (flatAlignEq upNext loNext upRest loRest nextAlign restAlign) rfl
          (flatSlotsCell loNext loRest))) ?_
    exact SaturatedConvOver.hcompCongrLeft
      (SaturatedConvOver.ofConv (TwoCellConv.ofStep
        (TwoCellStep.vcompIdLeft
          (RawTwoCellExpr.id (signature := involutionMonadPushout.toModeSignature) monadPushSPath))))
      (RawTwoCellExpr.vcomp (flatSlotsCell upNext upRest)
        (RawTwoCellExpr.castBoundary
          (flatAlignEq upNext loNext upRest loRest nextAlign restAlign) rfl
          (flatSlotsCell loNext loRest)))

/-! ## The vcomp arm -/

/-- ★★★ **THE VCOMP ARM** — two readings of composable pushout cells ZIP into a reading of their vertical
composite.  The seam alignment is a THEOREM (parsing uniqueness at the shared middle 1-cell,
`flatBoundary_slots_aligned`); the payload zip is `zipReading`. -/
def vcompReading
    {sourcePath middlePath targetPath :
      ModalityPath involutionMonadPushout.toModeGraph monadPushMode monadPushMode}
    {cellUp : RawTwoCellExpr involutionMonadPushout.toModeSignature sourcePath middlePath}
    {cellLo : RawTwoCellExpr involutionMonadPushout.toModeSignature middlePath targetPath}
    (readingUp : RunReading cellUp) (readingLo : RunReading cellLo) :
    RunReading (RawTwoCellExpr.vcomp cellUp cellLo) := by
  have align := flatBoundary_slots_aligned readingUp.headSlot readingLo.headSlot
    readingUp.tailSlots readingLo.tailSlots
    (readingUp.codEq.trans readingLo.domEq.symm)
  have chain :
      SaturatedConvOver involutionMonadPushout.toModeSignature crossPairRealPushoutRel
        (RawTwoCellExpr.vcomp cellUp cellLo)
        (RawTwoCellExpr.vcomp
          (RawTwoCellExpr.castBoundary readingUp.domEq readingUp.codEq
            (flatSlotsCell readingUp.headSlot readingUp.tailSlots))
          (RawTwoCellExpr.castBoundary readingLo.domEq readingLo.codEq
            (flatSlotsCell readingLo.headSlot readingLo.tailSlots))) :=
    SaturatedConvOver.trans
      (SaturatedConvOver.vcompCongrLeft cellLo readingUp.conv)
      (SaturatedConvOver.vcompCongrRight _ readingLo.conv)
  have mergedChain := SaturatedConvOver.trans chain
    (SaturatedConvOver.ofCellEq
      (vcomp_castBoundary_merge readingUp.domEq readingUp.codEq readingLo.domEq readingLo.codEq
        (flatSlotsCell readingUp.headSlot readingUp.tailSlots)
        (flatSlotsCell readingLo.headSlot readingLo.tailSlots)))
  exact RunReading.mapConv mergedChain
    (RunReading.castTransport readingUp.domEq readingLo.codEq
      (zipReading readingUp.headSlot readingUp.tailSlots readingLo.headSlot readingLo.tailSlots
        align.1 align.2))

/-! ## ★★ THE TOTAL READER -/

/-- ★★★ **THE TOTAL FLAT READER (fueled)** — EVERY pushout 2-cell reads into a flat wall/gap layout with
wall-free gap payloads: `gen` and `id` by the base arms, `vcomp` by the payload zip, the whiskers by the
per-letter peels.  Honest structural fuel on the cell size. -/
def readCellFueled :
    (fuel : Nat) →
    {sourcePath targetPath : ModalityPath involutionMonadPushout.toModeGraph monadPushMode monadPushMode} →
    (cell : RawTwoCellExpr involutionMonadPushout.toModeSignature sourcePath targetPath) →
    cell.size ≤ fuel →
    RunReading cell
  | _, _, _, .gen generator, _ => genReading generator
  | _, _, _, .id path, _ => idReading path
  | 0, _, _, .vcomp cellUp cellLo, hfuel =>
      absurd hfuel (Nat.not_succ_le_zero (cellUp.size + cellLo.size))
  | fuel + 1, _, _, .vcomp cellUp cellLo, hfuel =>
      vcompReading
        (readCellFueled fuel cellUp
          (Nat.le_trans (Nat.le_add_right cellUp.size cellLo.size) (Nat.le_of_succ_le_succ hfuel)))
        (readCellFueled fuel cellLo
          (Nat.le_trans (Nat.le_add_left cellLo.size cellUp.size) (Nat.le_of_succ_le_succ hfuel)))
  | 0, _, _, .whiskerLeft _ body, hfuel =>
      absurd hfuel (Nat.not_succ_le_zero body.size)
  | fuel + 1, _, _, @RawTwoCellExpr.whiskerLeft _ _ middleMode _ oneCell _ _ body, hfuel => by
      obtain rfl := pushoutModeUnique middleMode
      exact readingWhiskerLeft oneCell (readCellFueled fuel body (Nat.le_of_succ_le_succ hfuel))
  | 0, _, _, .whiskerRight _ body, hfuel =>
      absurd hfuel (Nat.not_succ_le_zero body.size)
  | fuel + 1, _, _, @RawTwoCellExpr.whiskerRight _ _ middleMode _ _ _ oneCell body, hfuel => by
      obtain rfl := pushoutModeUnique middleMode
      exact readingWhiskerRight oneCell (readCellFueled fuel body (Nat.le_of_succ_le_succ hfuel))

/-- ★★★ **THE TOTAL FLAT READER** — at its own size fuel. -/
def readCellIntoSlots
    {sourcePath targetPath : ModalityPath involutionMonadPushout.toModeGraph monadPushMode monadPushMode}
    (cell : RawTwoCellExpr involutionMonadPushout.toModeSignature sourcePath targetPath) :
    RunReading cell :=
  readCellFueled cell.size cell (Nat.le_refl _)

/-! ## Honesty markers -/

/-- ★★★ **Honesty marker — THE VCOMP PAYLOAD ZIP + THE TOTAL FLAT READER SHIP (WP-AMALG r30, Brick B3).**
`= true`.  `zipReading` discharges the r20 ceiling ledger's arm (c) shape at the flat reading: the vertical
composite of two seam-aligned flat layouts reads as the per-gap vertical composites, by structural recursion
firing the free interchange per gap — with the alignment a THEOREM (parsing uniqueness,
`flatBoundary_slots_aligned`), not an assumption, because the r30 gap geometry is boundary-determined.
`vcompReading` zips two arbitrary readings at a shared middle; `readCellIntoSlots` assembles the TOTAL reader
over ALL five cell constructors (`gen` / `id` / `vcomp` / `whiskerLeft` / `whiskerRight`).  The masters do NOT
flip here: the reader is the completeness INPUT; the fold decomposition + the decider are the successor
bricks.  `= true`. -/
def fxAmalg_hasVcompPayloadZip : Bool := true

end FX1Poly.Polygraph.Amalgam
