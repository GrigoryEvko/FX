import FX1Poly.Polygraph.TwoCategory.Amalgam.PushoutFlatFoldDecomposition

/-! # Polygraph/TwoCategory/Amalgam/PushoutFullSaturatedDecider — THE COMPLETENESS, THE TOTAL TWO-SIDED
DECIDER, and THE REAL-RELATION SATURATED DISPATCH INHABITANT (WP-AMALG r30, Brick D)

The #2043 endgame.  The r30 chain (flat reader + payload zip + block-diagonal fold decomposition) assembles
with the shipped semantic machinery (the arity-fold congruence over the REAL-law relation, the wall-free cell
converse with its backward round-trip, the reconstructed completeness, and the right-image soundness lift)
into:

  * **`pushoutConvOfFoldEq`** — ★ THE COMPLETENESS: equal arity folds imply saturated convertibility over the
    REAL-law pushout relation, for ARBITRARY parallel pushout 2-cells.  Read both cells into flat layouts
    (geometry boundary-determined), extract per-slot fold equality (block-diagonal decomposition), descend each
    gap to the monad component (`wallFreeCellInvert`), close per-gap by the reconstructed completeness
    (`reconstructed_convOfArityEq`), lift back (`pushoutRightImageCompletenessLift` + the backward round-trip
    equality), and reassemble by congruence.
  * **`pushoutFullSaturatedDecider`** — ★★ THE TOTAL TWO-SIDED DECIDER: compare the arity folds; `isTrue` by
    the completeness, `isFalse` by the shipped fold congruence (`arityFoldRealPushoutCongruence`).  This is
    the `isTrue` completeness `RealLawDispatch.lean` named as the wall ("equal fold ⟹ pushout-convertible"),
    DISCHARGED — the pushout normal form woven through the `s`-whisker contexts IS the flat reading.
  * **`involutionMonadRealSaturatedDispatch`** — ★★★ THE REAL-RELATION SATURATED DISPATCH: the LITERAL
    `SaturatedDispatchDecidability` inhabitant at `involution +_M monad` with the RIGHT component carrying the
    GENUINE `MonadLawRelReconstructed` and the pushout relation the retagged disjoint union
    (`crossPairRealPushoutRel = SaturatedConvOverPushout … emptyCellRel MonadLawRelReconstructed`) — the FULL
    cross-component saturated dispatch for a REAL-relation pushout.

Raw Lean 4 + Init.  Per-declaration `#assert_no_axioms` gated in the audit twin. -/

namespace FX1Poly.Polygraph.Amalgam

open FX1Poly.Polygraph

/-! ## Cast-stripping and fold-transfer plumbing -/

/-- A convertibility between equal casts strips to the underlying cells (`cases`; `id`). -/
theorem conv_uncast {pathP pathP' pathQ pathQ' :
      ModalityPath involutionMonadPushout.toModeGraph monadPushMode monadPushMode}
    (hsource : pathP = pathP') (htarget : pathQ = pathQ')
    {cellX cellY : RawTwoCellExpr involutionMonadPushout.toModeSignature pathP pathQ}
    (conv : SaturatedConvOver involutionMonadPushout.toModeSignature crossPairRealPushoutRel
      (RawTwoCellExpr.castBoundary hsource htarget cellX)
      (RawTwoCellExpr.castBoundary hsource htarget cellY)) :
    SaturatedConvOver involutionMonadPushout.toModeSignature crossPairRealPushoutRel cellX cellY := by
  cases hsource
  cases htarget
  exact conv

/-- A boundary cast preserves the arity fold, ACROSS the boundary indices (`cases`; `rfl`). -/
theorem arityFold_castBoundary {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode}
    {sourcePath sourcePath' targetPath targetPath' : ModalityPath signature.graph sourceMode targetMode}
    (hsource : sourcePath = sourcePath') (htarget : targetPath = targetPath')
    (cell : RawTwoCellExpr signature sourcePath targetPath) :
    arityMonotoneMapOf (RawTwoCellExpr.castBoundary hsource htarget cell) = arityMonotoneMapOf cell := by
  cases hsource
  cases htarget
  rfl

/-- The wall-free cell converse PRESERVES the arity fold — via the backward round-trip equality (the section
law), the functor fold-preservation, and the cast's fold-invisibility. -/
theorem arityFold_wallFreeCellInvert
    {sourcePath targetPath : ModalityPath involutionMonadPushout.toModeGraph monadPushMode monadPushMode}
    (cell : RawTwoCellExpr involutionMonadPushout.toModeSignature sourcePath targetPath)
    (wfS : pathWallFree sourcePath) (wfT : pathWallFree targetPath) :
    arityMonotoneMapOf (wallFreeCellInvert cell wfS wfT) = arityMonotoneMapOf cell :=
  (arityMonotoneMapOf_mapCellAlong pushoutRightCoprojectionTwo (wallFreeCellInvert cell wfS wfT)).symm.trans
    ((congrArg arityMonotoneMapOf (mapCellAlong_inclRight_wallFreeCellInvert cell wfS wfT)).trans
      (arityFold_castBoundary (mapPath_inclRight_pathInvert sourcePath wfS).symm
        (mapPath_inclRight_pathInvert targetPath wfT).symm cell))

/-! ## The per-gap completeness (the descended monad word problem) -/

/-- ★★ **THE PER-GAP COMPLETENESS** — two wall-free-boundary parallel pushout cells with EQUAL arity folds are
saturated-convertible over the REAL-law relation.  Descend both by the shipped `wallFreeCellInvert` (the folds
transfer), close at the monad component by the shipped reconstructed completeness
(`reconstructed_convOfArityEq`), lift back by the shipped right-image soundness
(`pushoutRightImageCompletenessLift`), and strip the backward-round-trip casts. -/
theorem wallFreePayload_conv_of_foldEq
    {gapDomPath gapCodPath : ModalityPath involutionMonadPushout.toModeGraph monadPushMode monadPushMode}
    (domWallFree : pathWallFree gapDomPath) (codWallFree : pathWallFree gapCodPath)
    (cellA cellB : RawTwoCellExpr involutionMonadPushout.toModeSignature gapDomPath gapCodPath)
    (foldEq : arityMonotoneMapOf cellA = arityMonotoneMapOf cellB) :
    SaturatedConvOver involutionMonadPushout.toModeSignature crossPairRealPushoutRel cellA cellB := by
  have invertFoldEq : arityMonotoneMapOf (wallFreeCellInvert cellA domWallFree codWallFree)
      = arityMonotoneMapOf (wallFreeCellInvert cellB domWallFree codWallFree) :=
    (arityFold_wallFreeCellInvert cellA domWallFree codWallFree).trans
      (foldEq.trans (arityFold_wallFreeCellInvert cellB domWallFree codWallFree).symm)
  have reconConv := reconstructed_convOfArityEq
    (wallFreeCellInvert cellA domWallFree codWallFree)
    (wallFreeCellInvert cellB domWallFree codWallFree) invertFoldEq
  have lifted := pushoutRightImageCompletenessLift reconConv
  have castConv := SaturatedConvOver.trans
    (SaturatedConvOver.ofCellEq (mapCellAlong_inclRight_wallFreeCellInvert cellA domWallFree codWallFree).symm)
    (SaturatedConvOver.trans lifted
      (SaturatedConvOver.ofCellEq (mapCellAlong_inclRight_wallFreeCellInvert cellB domWallFree codWallFree)))
  exact conv_uncast (mapPath_inclRight_pathInvert gapDomPath domWallFree).symm
    (mapPath_inclRight_pathInvert gapCodPath codWallFree).symm castConv

/-! ## Geometry alignment of two same-boundary readings -/

/-- Pointwise DOM alignment of two slot lists off their dom-length lists. -/
theorem slotDomRuns_aligned_of_lengths :
    (tailA tailB : List GapSlot) →
    tailA.map (fun slot => slot.gapDom.length) = tailB.map (fun slot => slot.gapDom.length) →
    tailA.map GapSlot.gapDom = tailB.map GapSlot.gapDom
  | [], [], _ => rfl
  | [], _ :: _, hmap => Nat.noConfusion (congrArg List.length hmap)
  | _ :: _, [], hmap => Nat.noConfusion (congrArg List.length hmap)
  | slotA :: restA, slotB :: restB, hmap => by
    injection hmap with headLenEq tailMapEq
    show slotA.gapDom :: restA.map GapSlot.gapDom = slotB.gapDom :: restB.map GapSlot.gapDom
    rw [wallFreeRun_eq_of_length slotA.gapDom slotB.gapDom slotA.domWallFree slotB.domWallFree headLenEq,
      slotDomRuns_aligned_of_lengths restA restB tailMapEq]

/-- Pointwise COD alignment of two slot lists off their cod-length lists. -/
theorem slotCodRuns_aligned_of_lengths :
    (tailA tailB : List GapSlot) →
    tailA.map (fun slot => slot.gapCod.length) = tailB.map (fun slot => slot.gapCod.length) →
    tailA.map GapSlot.gapCod = tailB.map GapSlot.gapCod
  | [], [], _ => rfl
  | [], _ :: _, hmap => Nat.noConfusion (congrArg List.length hmap)
  | _ :: _, [], hmap => Nat.noConfusion (congrArg List.length hmap)
  | slotA :: restA, slotB :: restB, hmap => by
    injection hmap with headLenEq tailMapEq
    show slotA.gapCod :: restA.map GapSlot.gapCod = slotB.gapCod :: restB.map GapSlot.gapCod
    rw [wallFreeRun_eq_of_length slotA.gapCod slotB.gapCod slotA.codWallFree slotB.codWallFree headLenEq,
      slotCodRuns_aligned_of_lengths restA restB tailMapEq]

/-- ★ **DOM parsing uniqueness** — two slot layouts assembling the same DOMAIN 1-cell share their dom
geometry. -/
theorem flatDom_slots_aligned (headA headB : GapSlot) (tailA tailB : List GapSlot)
    (domEq : flatSlotsDom headA tailA = flatSlotsDom headB tailB) :
    headA.gapDom = headB.gapDom ∧ tailA.map GapSlot.gapDom = tailB.map GapSlot.gapDom := by
  have wordEq := congrArg pushoutPathWord domEq
  rw [pushoutPathWord_flatDom headA tailA, pushoutPathWord_flatDom headB tailB] at wordEq
  obtain ⟨headLenEq, tailLensEq⟩ :=
    runsWord_parse_unique (tailA.map (fun slot => slot.gapDom.length))
      (tailB.map (fun slot => slot.gapDom.length)) headA.gapDom.length headB.gapDom.length wordEq
  exact ⟨wallFreeRun_eq_of_length headA.gapDom headB.gapDom headA.domWallFree headB.domWallFree headLenEq,
    slotDomRuns_aligned_of_lengths tailA tailB tailLensEq⟩

/-- ★ **COD parsing uniqueness** — two slot layouts assembling the same CODOMAIN 1-cell share their cod
geometry. -/
theorem flatCod_slots_aligned (headA headB : GapSlot) (tailA tailB : List GapSlot)
    (codEq : flatSlotsCod headA tailA = flatSlotsCod headB tailB) :
    headA.gapCod = headB.gapCod ∧ tailA.map GapSlot.gapCod = tailB.map GapSlot.gapCod := by
  have wordEq := congrArg pushoutPathWord codEq
  rw [pushoutPathWord_flatCod headA tailA, pushoutPathWord_flatCod headB tailB] at wordEq
  obtain ⟨headLenEq, tailLensEq⟩ :=
    runsWord_parse_unique (tailA.map (fun slot => slot.gapCod.length))
      (tailB.map (fun slot => slot.gapCod.length)) headA.gapCod.length headB.gapCod.length wordEq
  exact ⟨wallFreeRun_eq_of_length headA.gapCod headB.gapCod headA.codWallFree headB.codWallFree headLenEq,
    slotCodRuns_aligned_of_lengths tailA tailB tailLensEq⟩

/-! ## Fold-aligned flat layouts are convertible -/

/-- A both-sides cast distributes over a horizontal composite componentwise (`cases`; `rfl`). -/
theorem castBoundary_hcomp_distribute_both {signature : ModeSignature}
    {sourceMode middleMode targetMode : signature.graph.Mode}
    {headDom headDom' : ModalityPath signature.graph sourceMode middleMode}
    {tailDom tailDom' : ModalityPath signature.graph middleMode targetMode}
    {headCod headCod' : ModalityPath signature.graph sourceMode middleMode}
    {tailCod tailCod' : ModalityPath signature.graph middleMode targetMode}
    (hHeadDom : headDom = headDom') (hHeadCod : headCod = headCod')
    (hTailDom : tailDom = tailDom') (hTailCod : tailCod = tailCod')
    (cellHead : RawTwoCellExpr signature headDom headCod)
    (cellTail : RawTwoCellExpr signature tailDom tailCod)
    (hWholeDom : composePath headDom tailDom = composePath headDom' tailDom')
    (hWholeCod : composePath headCod tailCod = composePath headCod' tailCod') :
    RawTwoCellExpr.castBoundary hWholeDom hWholeCod (RawTwoCellExpr.hcomp cellHead cellTail)
      = RawTwoCellExpr.hcomp
          (RawTwoCellExpr.castBoundary hHeadDom hHeadCod cellHead)
          (RawTwoCellExpr.castBoundary hTailDom hTailCod cellTail) := by
  cases hHeadDom
  cases hHeadCod
  cases hTailDom
  cases hTailCod
  rfl

/-- The flat-boundary congruence off pointwise geometry equalities (dom side). -/
theorem flatSlotsDom_congr (headA headB : GapSlot) (tailA tailB : List GapSlot)
    (hHead : headA.gapDom = headB.gapDom)
    (hTail : tailA.map GapSlot.gapDom = tailB.map GapSlot.gapDom) :
    flatSlotsDom headA tailA = flatSlotsDom headB tailB := by
  show interleaveRuns headA.gapDom (tailA.map GapSlot.gapDom)
    = interleaveRuns headB.gapDom (tailB.map GapSlot.gapDom)
  rw [hHead, hTail]

/-- The flat-boundary congruence off pointwise geometry equalities (cod side). -/
theorem flatSlotsCod_congr (headA headB : GapSlot) (tailA tailB : List GapSlot)
    (hHead : headA.gapCod = headB.gapCod)
    (hTail : tailA.map GapSlot.gapCod = tailB.map GapSlot.gapCod) :
    flatSlotsCod headA tailA = flatSlotsCod headB tailB := by
  show interleaveRuns headA.gapCod (tailA.map GapSlot.gapCod)
    = interleaveRuns headB.gapCod (tailB.map GapSlot.gapCod)
  rw [hHead, hTail]

/-- ★★ **Fold-aligned flat layouts are CONVERTIBLE** — two flat layouts with pointwise equal geometry and
pointwise equal payload folds are saturated-convertible (per gap by the descended monad word problem, the
walls inert, reassembled by the horizontal congruences).  Structural recursion destructuring the B-side slots
so the geometry equalities `subst` cleanly. -/
theorem flatConv_of_aligned :
    (headA headB : GapSlot) → (tailA tailB : List GapSlot) →
    (hHeadDom : headA.gapDom = headB.gapDom) → (hHeadCod : headA.gapCod = headB.gapCod) →
    (hTailDom : tailA.map GapSlot.gapDom = tailB.map GapSlot.gapDom) →
    (hTailCod : tailA.map GapSlot.gapCod = tailB.map GapSlot.gapCod) →
    SlotPayloadFoldsAligned (headA :: tailA) (headB :: tailB) →
    SaturatedConvOver involutionMonadPushout.toModeSignature crossPairRealPushoutRel
      (flatSlotsCell headA tailA)
      (RawTwoCellExpr.castBoundary
        (flatSlotsDom_congr headB headA tailB tailA hHeadDom.symm hTailDom.symm)
        (flatSlotsCod_congr headB headA tailB tailA hHeadCod.symm hTailCod.symm)
        (flatSlotsCell headB tailB))
  | ⟨aDom, aCod, aDomWf, aCodWf, aPay⟩, ⟨bDom, bCod, bDomWf, bCodWf, bPay⟩, [], [],
      hHeadDom, hHeadCod, _, _, aligned => by
    cases hHeadDom
    cases hHeadCod
    match aligned with
    | SlotPayloadFoldsAligned.cons _ _ _ _ headFoldEq _ =>
      exact wallFreePayload_conv_of_foldEq aDomWf aCodWf aPay bPay headFoldEq
  | _, _, [], _ :: _, _, _, hTailDom, _, _ =>
      Nat.noConfusion (congrArg List.length hTailDom)
  | _, _, _ :: _, [], _, _, hTailDom, _, _ =>
      Nat.noConfusion (congrArg List.length hTailDom)
  | ⟨aDom, aCod, aDomWf, aCodWf, aPay⟩, ⟨bDom, bCod, bDomWf, bCodWf, bPay⟩,
      nextA :: restA, nextB :: restB, hHeadDom, hHeadCod, hTailDom, hTailCod, aligned => by
    cases hHeadDom
    cases hHeadCod
    have nextDomEq : nextA.gapDom = nextB.gapDom := by injection hTailDom
    have restDomEq : restA.map GapSlot.gapDom = restB.map GapSlot.gapDom := by injection hTailDom
    have nextCodEq : nextA.gapCod = nextB.gapCod := by injection hTailCod
    have restCodEq : restA.map GapSlot.gapCod = restB.map GapSlot.gapCod := by injection hTailCod
    have headFoldEq : arityMonotoneMapOf aPay = arityMonotoneMapOf bPay :=
      match aligned with
      | SlotPayloadFoldsAligned.cons _ _ _ _ headFoldEq _ => headFoldEq
    have tailAligned : SlotPayloadFoldsAligned (nextA :: restA) (nextB :: restB) :=
      match aligned with
      | SlotPayloadFoldsAligned.cons _ _ _ _ _ tailAligned => tailAligned
    have innerConv := flatConv_of_aligned nextA nextB restA restB
      nextDomEq nextCodEq restDomEq restCodEq tailAligned
    have headConv := wallFreePayload_conv_of_foldEq aDomWf aCodWf aPay bPay headFoldEq
    refine SaturatedConvOver.trans
      (SaturatedConvOver.hcompCongr headConv
        (SaturatedConvOver.hcompCongrRight
          (RawTwoCellExpr.id (signature := involutionMonadPushout.toModeSignature) monadPushSPath)
          innerConv)) ?_
    refine SaturatedConvOver.ofCellEq ?_
    have distributeOuter := castBoundary_hcomp_distribute_both rfl rfl
      (congrArg (composePath monadPushSPath)
        (flatSlotsDom_congr nextB nextA restB restA nextDomEq.symm restDomEq.symm))
      (congrArg (composePath monadPushSPath)
        (flatSlotsCod_congr nextB nextA restB restA nextCodEq.symm restCodEq.symm))
      bPay
      (RawTwoCellExpr.hcomp
        (RawTwoCellExpr.id (signature := involutionMonadPushout.toModeSignature) monadPushSPath)
        (flatSlotsCell nextB restB))
      (flatSlotsDom_congr
        ⟨aDom, aCod, bDomWf, bCodWf, bPay⟩ ⟨aDom, aCod, aDomWf, aCodWf, aPay⟩
        (nextB :: restB) (nextA :: restA) rfl hTailDom.symm)
      (flatSlotsCod_congr
        ⟨aDom, aCod, bDomWf, bCodWf, bPay⟩ ⟨aDom, aCod, aDomWf, aCodWf, aPay⟩
        (nextB :: restB) (nextA :: restA) rfl hTailCod.symm)
    have distributeInner := castBoundary_hcomp_distribute_both rfl rfl
      (flatSlotsDom_congr nextB nextA restB restA nextDomEq.symm restDomEq.symm)
      (flatSlotsCod_congr nextB nextA restB restA nextCodEq.symm restCodEq.symm)
      (RawTwoCellExpr.id (signature := involutionMonadPushout.toModeSignature) monadPushSPath)
      (flatSlotsCell nextB restB)
      (congrArg (composePath monadPushSPath)
        (flatSlotsDom_congr nextB nextA restB restA nextDomEq.symm restDomEq.symm))
      (congrArg (composePath monadPushSPath)
        (flatSlotsCod_congr nextB nextA restB restA nextCodEq.symm restCodEq.symm))
    exact (distributeOuter.trans
      (congrArg (RawTwoCellExpr.hcomp bPay) distributeInner)).symm

/-! ## ★ THE COMPLETENESS -/

/-- ★★★ **THE COMPLETENESS** — equal arity folds imply saturated convertibility over the REAL-law pushout
relation, for ARBITRARY parallel pushout 2-cells.  The equal-fold ⟹ pushout-convertible direction the
soundness round (`RealLawDispatch.lean`) named as the open wall, discharged by the r30 chain. -/
theorem pushoutConvOfFoldEq
    {sourcePath targetPath : ModalityPath involutionMonadPushout.toModeGraph monadPushMode monadPushMode}
    (cellAlpha cellBeta : RawTwoCellExpr involutionMonadPushout.toModeSignature sourcePath targetPath)
    (foldEq : arityMonotoneMapOf cellAlpha = arityMonotoneMapOf cellBeta) :
    SaturatedConvOver involutionMonadPushout.toModeSignature crossPairRealPushoutRel cellAlpha cellBeta := by
  have readingA := readCellIntoSlots cellAlpha
  have readingB := readCellIntoSlots cellBeta
  obtain ⟨headDomEq, tailDomEq⟩ := flatDom_slots_aligned readingA.headSlot readingB.headSlot
    readingA.tailSlots readingB.tailSlots (readingA.domEq.trans readingB.domEq.symm)
  obtain ⟨headCodEq, tailCodEq⟩ := flatCod_slots_aligned readingA.headSlot readingB.headSlot
    readingA.tailSlots readingB.tailSlots (readingA.codEq.trans readingB.codEq.symm)
  have flatFoldEq : arityMonotoneMapOf (flatSlotsCell readingA.headSlot readingA.tailSlots)
      = arityMonotoneMapOf (flatSlotsCell readingB.headSlot readingB.tailSlots) := by
    have foldA : arityMonotoneMapOf cellAlpha
        = arityMonotoneMapOf (flatSlotsCell readingA.headSlot readingA.tailSlots) :=
      (SaturatedConvOver.recInto arityFoldRealPushoutCongruence readingA.conv).trans
        (arityFold_castBoundary readingA.domEq readingA.codEq _)
    have foldB : arityMonotoneMapOf cellBeta
        = arityMonotoneMapOf (flatSlotsCell readingB.headSlot readingB.tailSlots) :=
      (SaturatedConvOver.recInto arityFoldRealPushoutCongruence readingB.conv).trans
        (arityFold_castBoundary readingB.domEq readingB.codEq _)
    exact foldA.symm.trans (foldEq.trans foldB)
  have aligned := flatFold_slots_aligned readingA.headSlot readingB.headSlot
    readingA.tailSlots readingB.tailSlots headDomEq headCodEq tailDomEq tailCodEq flatFoldEq
  have flatConv := flatConv_of_aligned readingA.headSlot readingB.headSlot
    readingA.tailSlots readingB.tailSlots headDomEq headCodEq tailDomEq tailCodEq aligned
  have castFlatConv := SaturatedConvOver.castBoundaryCongr readingA.domEq readingA.codEq flatConv
  rw [RawTwoCellExpr.castBoundary_trans] at castFlatConv
  exact SaturatedConvOver.trans readingA.conv
    (SaturatedConvOver.trans castFlatConv (SaturatedConvOver.symm readingB.conv))

/-! ## ★★ THE TOTAL TWO-SIDED DECIDER -/

/-- ★★★ **THE TOTAL TWO-SIDED DECIDER** — saturated convertibility over the REAL-law pushout relation is
DECIDABLE on every parallel pair: compare the arity folds (`List Nat` decidable equality); `isTrue` by THE
COMPLETENESS, `isFalse` by the shipped fold congruence.  The categorical Nelson-Oppen combined decision at
`involution +_M monad`, both directions proof-carrying. -/
def pushoutFullSaturatedDecider :
    DecidableSaturatedConvForRel involutionMonadPushout.toModeSignature crossPairRealPushoutRel :=
  fun {sourceMode targetMode} {sourcePath targetPath} cellAlpha cellBeta => by
    obtain rfl := pushoutModeUnique sourceMode
    obtain rfl := pushoutModeUnique targetMode
    exact
      if foldEq : arityMonotoneMapOf cellAlpha = arityMonotoneMapOf cellBeta then
        Decidable.isTrue (pushoutConvOfFoldEq cellAlpha cellBeta foldEq)
      else
        Decidable.isFalse (fun conv =>
          foldEq (SaturatedConvOver.recInto arityFoldRealPushoutCongruence conv))

/-! ## ★★★ THE REAL-RELATION SATURATED DISPATCH -/

/-- The disjoint-generator condition at the real pushout (`rfl` — the check computes). -/
theorem involutionMonadGeneratorsDisjoint :
    computadGeneratorsDisjoint involutionComputad.modalityGenerators.length
      (pushoutShared involutionComputad monadComputad involutionMonadSameModes) = true := by
  decide

/-- ★★★ **THE REAL-RELATION SATURATED DISPATCH** — the LITERAL `SaturatedDispatchDecidability` inhabitant for
a REAL-relation pushout: `involution +_M monad`, LEFT component thin (`emptyCellRel`), RIGHT component carrying
the GENUINE walking-monad law relation `MonadLawRelReconstructed`, and the pushout base relation the DISJOINT
UNION OF THE RETAGGED COMPONENT LAW RELATIONS (`crossPairRealPushoutRel = SaturatedConvOverPushout …
(emptyCellRel …) MonadLawRelReconstructed` along the real coprojections).  Component deciders: the shipped
thin decider and the shipped unconditional reconstructed decider; combined decider: THE TOTAL TWO-SIDED
DECIDER.  This is the arrow `fxAmalg_hasSaturatedDispatchTheorem` demands. -/
def involutionMonadRealSaturatedDispatch :
    SaturatedDispatchDecidability involutionComputad monadComputad involutionMonadSameModes
      (emptyCellRel involutionComputad.toModeSignature)
      MonadLawRelReconstructed
      crossPairRealPushoutRel where
  componentOneDecider := involutionSaturatedThinDecider
  componentTwoDecider := monadReconstructedDecisionGen
  generatorsDisjoint := involutionMonadGeneratorsDisjoint
  combinedDecider := pushoutFullSaturatedDecider

/-! ## Honesty marker -/

/-- ★★★ **Honesty marker — THE COMPLETENESS + THE TOTAL DECIDER + THE REAL-RELATION DISPATCH SHIP (WP-AMALG
r30, Brick D).**  `= true`.  `pushoutConvOfFoldEq` discharges the completeness wall named by
`fxAmalg_realLawCompletenessStaysWalled` ("equal semantic fold ⟹ pushout-convertible") — the pushout normal
form woven through the `s`-whisker contexts IS the r30 flat reading, and the wire-creating generators break
NOTHING (the fold factors block-diagonally; target widths are pinned by the shared codomain).
`pushoutFullSaturatedDecider` is the total two-sided `Decidable` for ARBITRARY parallel pushout pairs;
`involutionMonadRealSaturatedDispatch` inhabits `SaturatedDispatchDecidability` at the REAL-relation pushout
with the retagged-union base relation — the FULL cross-component saturated dispatch.  The master flips are
recorded in the successor content-marker file (the r3 owner is pinned by `rfl` re-recordings across the lane;
per the marker law it is superseded by a NEW-file content marker, never a line edit).  `= true`. -/
def fxAmalg_hasRealRelationSaturatedDispatchInhabitant : Bool := true

end FX1Poly.Polygraph.Amalgam
