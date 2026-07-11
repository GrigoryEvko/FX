import FX1Poly.Polygraph.TwoCategory.Amalgam.PushoutWallFreeCellInvert
import FX1Poly.Polygraph.TwoCategory.Amalgam.ConvFullFunctor
import FX1Poly.Polygraph.TwoCategory.Amalgam.ReconstructedDecision

/-! # Polygraph/TwoCategory/Amalgam/PushoutWallFreeCellInvertRoundTrip — the wall-free CELL converse's BACKWARD
round-trip: `mapCellAlong inclRight ∘ wallFreeCellInvert = castBoundary .. cell`, all five constructors, the
dim-2 bijection paired with the r11 dim-1 one (WP-AMALG-2 r13, the backward round-trip round)

The r12 ledger (`PushoutCellConverseLedger.lean`) shipped the FORWARD cell converse `wallFreeCellInvert` (all four
`RawTwoCellExpr` constructors) and its gen-case backward SECTION (`wallFreeGenInvert_onTwoCell_index_roundTrip`,
the reseat index round-trips through `inclusionRightTwoReal`'s `onTwoCell`).  It named the FULL cell backward
round-trip — `mapCellAlong inclRight ∘ wallFreeCellInvert = castBoundary .. cell` — as a
`reseatCellInv_reseatCell`-style FUEL assembly, scoped to a follow-on round.  This file discharges that residual.

## The mechanical mirror of `reseatCellInv_reseatCell`

The construction is byte-for-byte the shipped `reseatCellInv_reseatCell` (`ReconstructedDecision.lean`), with the
functor pair swapped: the INNER functor is `wallFreeCellInvert` (pushout ⟹ monad, boundaries by `pathInvert`) in
place of `reseatCell`, and the OUTER functor is `mapCellAlong inclusionRightTwoReal` (monad ⟹ pushout, boundaries
by `mapPath inclRight`) in place of `reseatCellInv`.  Every ingredient is a shipped, machine-checked mirror:

  * **`pushoutGenTransportCast`** — `gen (hs ▸ ht ▸ g) = castBoundary hs ht (gen g)` on the PUSHOUT reconstructed
    2-cell family (mirror of `genTransportCast`, `cases hs; cases ht; rfl`).
  * **`reconTwoCellPushout_doubleTransport_val`** — a double boundary-transport leaves the `Fin` index untouched
    (mirror of `reconTwoCell_doubleTransport_val`).
  * **`wallFreeGenInvert_onTwoCell_full`** — the gen-case FULL round-trip: `inclRight.onTwoCell (wallFreeGenInvert
    generator ..) = (transport) generator`, upgrading the shipped INDEX round-trip
    `wallFreeGenInvert_onTwoCell_index_roundTrip` to the full boundary-cast equation via `Subtype.ext` (the
    reconstructed family is a proof-irrelevant `Fin`-subtype).
  * **`mapCellAlongWallFreeInvertWhiskerLeftStep` / `..RightStep`** — the two cast-fusion step theorems reconciling
    the INNER `pathInvert_composePath` cast against the OUTER `mapPath_composePath` cast through the path round-trip
    `mapPath_inclRight_pathInvert`, via the shipped `RawTwoCellExpr.*` cast toolkit (`ConvFullFunctor.lean`).
  * **`mapCellAlongWallFreeInvertFueled` / `mapCellAlong_inclRight_wallFreeCellInvert`** — the structural cell-size
    fuel assembly (the free MIDDLE mode of the whisker arms is pinned by `pushoutModeUnique` + `subst`, the fuel
    measure independent of the subst) and its `cell.size`-instantiation.

The PATH leg is FREE: `mapPath_inclRight_pathInvert` (`PushoutWallFreePathInversion.lean`) was proved via the WORD
route, so — unlike the reseat lane, which needed its own `reseatPathInv_reseatPath_fueled` — this backward round-trip
is strictly cheaper than the reseat precedent.

## The dim-2 bijection (paired with the r11 dim-1 one)

With the forward converse `wallFreeCellInvert` (r12) and this backward round-trip, `mapCellAlong inclRight` and
`wallFreeCellInvert` witness a section at the CELL level, paired with the r11 1-cell BIJECTION
(`pathInvert` + `mapPath_inclRight_injective`, `PushoutWallFreePathInversion.lean`).

## What STAYS WALLED (no flip)

This is the backward CELL round-trip — the essential-surjectivity CONVERSE at the cell level.  It is NOT
purification/projection COMPLETENESS (residual (iii) of `fxAmalg_hasFullSaturatedPushoutDispatch`), NOT the
arbitrary-pair DECISION (`fxAmalg_hasGeneralPushoutDispatch`), NOT the top-level `pushoutFactorize` assembly
(`fxAmalg_topFactorizationInductionStaysWalled`).  The three masters STAY put.  #2043 does NOT close.

Raw Lean 4 + Init.  STRUCTURAL cell-size fuel (the free middle mode `subst`ed under the fuel measure); all
`Eq.rec` / no `HEq`.  Per-declaration `#assert_no_axioms` gated in the audit twin. -/

namespace FX1Poly.Polygraph.Amalgam

open FX1Poly.Polygraph

/-- The right coprojection lifted to a `ComputadMorphismTwo` with the genuine `onTwoCell` — the OUTER functor of the
backward round-trip.  A reducible abbreviation of `inclusionRightTwoReal` at the witness pushout, so the shipped
`inclusionRightTwoReal ..`-stated lemmas (`wallFreeGenInvert_onTwoCell_index_roundTrip`) unify with it. -/
abbrev pushoutRightCoprojectionTwo : ComputadMorphismTwo monadComputad involutionMonadPushout :=
  inclusionRightTwoReal involutionComputad monadComputad involutionMonadSameModes

/-! ## The gen leg — the full backward round-trip on a reconstructed generator -/

/-- A `gen` of a boundary-transported PUSHOUT generator IS the boundary cast of the `gen` (fresh targets so `cases`).
The pushout-side mirror of `genTransportCast`. -/
theorem pushoutGenTransportCast
    {sourcePath sourcePath' targetPath targetPath' :
      ModalityPath involutionMonadPushout.toModeGraph monadPushMode monadPushMode}
    (hsource : sourcePath = sourcePath') (htarget : targetPath = targetPath')
    (generator : involutionMonadPushout.ReconstructedTwoCell sourcePath targetPath) :
    RawTwoCellExpr.gen (signature := involutionMonadPushout.toModeSignature)
        (hsource ▸ htarget ▸ generator :
          involutionMonadPushout.ReconstructedTwoCell sourcePath' targetPath')
      = RawTwoCellExpr.castBoundary hsource htarget
          (RawTwoCellExpr.gen (signature := involutionMonadPushout.toModeSignature) generator) := by
  cases hsource; cases htarget; rfl

/-- Transporting a reconstructed PUSHOUT generator across boundary-path equalities leaves its `Fin` index untouched
(the index type is boundary-independent).  `cases` both equalities then `rfl`.  Mirror of
`reconTwoCell_doubleTransport_val`. -/
theorem reconTwoCellPushout_doubleTransport_val
    {sourcePath sourcePath' targetPath targetPath' :
      ModalityPath involutionMonadPushout.toModeGraph monadPushMode monadPushMode}
    (hsource : sourcePath = sourcePath') (htarget : targetPath = targetPath')
    (generator : involutionMonadPushout.ReconstructedTwoCell sourcePath targetPath) :
    (hsource ▸ htarget ▸ generator).val = generator.val := by
  cases hsource; cases htarget; rfl

/-- ★★★ **THE GEN-CASE FULL BACKWARD ROUND-TRIP.**  Inverting a reconstructed pushout 2-generator, then
re-coprojecting through `inclusionRightTwoReal`'s `onTwoCell`, is the boundary cast of the ORIGINAL generator back
onto the `mapPath inclRight (pathInvert ..)` image boundary.  Upgrades the shipped INDEX round-trip
(`wallFreeGenInvert_onTwoCell_index_roundTrip`, `embedRightTwoGen ∘ retractRightTwoGen = id`) to the full
boundary-cast equation: since the round-trip preserves the `Fin` index and the reconstructed family is a
proof-irrelevant `Fin`-subtype, `Subtype.ext` upgrades it (the RHS transport leaves the index fixed by
`reconTwoCellPushout_doubleTransport_val`).  The gen-case content the fuel assembly threads.  Mirror of
`reseatGenInv_reseatGen`. -/
theorem wallFreeGenInvert_onTwoCell_full
    {sourcePath targetPath : ModalityPath involutionMonadPushout.toModeGraph monadPushMode monadPushMode}
    (generator : involutionMonadPushout.ReconstructedTwoCell sourcePath targetPath)
    (wfS : pathWallFree sourcePath) (wfT : pathWallFree targetPath) :
    pushoutRightCoprojectionTwo.onTwoCell (wallFreeGenInvert generator wfS wfT)
      = ((mapPath_inclRight_pathInvert sourcePath wfS).symm ▸
          (mapPath_inclRight_pathInvert targetPath wfT).symm ▸ generator
          : involutionMonadPushout.ReconstructedTwoCell
              (mapPath pushoutRightCoprojectionTwo.toComputadMorphism (pathInvert sourcePath wfS))
              (mapPath pushoutRightCoprojectionTwo.toComputadMorphism (pathInvert targetPath wfT))) :=
  Subtype.ext
    ((wallFreeGenInvert_onTwoCell_index_roundTrip generator wfS wfT).trans
      (reconTwoCellPushout_doubleTransport_val (mapPath_inclRight_pathInvert sourcePath wfS).symm
        (mapPath_inclRight_pathInvert targetPath wfT).symm generator).symm)

/-! ## The two cast-fusion step theorems (the whisker arms) -/

/-- The whiskerLeft reconciliation step of the cell backward round-trip — the INNER `pathInvert_composePath` cast of
`wallFreeCellInvert`'s whisker arm reconciled against the OUTER `mapPath_composePath` cast of `mapCellAlong`'s
whisker arm, through the path round-trip `mapPath_inclRight_pathInvert oc`.  Byte-for-byte
`reseatCellInvReseatCellWhiskerLeftStep`. -/
theorem mapCellAlongWallFreeInvertWhiskerLeftStep
    (oc : ModalityPath involutionMonadPushout.toModeGraph monadPushMode monadPushMode)
    {bodyDom bodyCod : ModalityPath involutionMonadPushout.toModeGraph monadPushMode monadPushMode}
    (body : RawTwoCellExpr involutionMonadPushout.toModeSignature bodyDom bodyCod)
    (wfS : pathWallFree (composePath oc bodyDom))
    (wfT : pathWallFree (composePath oc bodyCod))
    (ihBody : mapCellAlong pushoutRightCoprojectionTwo (wallFreeCellInvert body
          (pathWallFree_composePath_split oc bodyDom wfS).2
          (pathWallFree_composePath_split oc bodyCod wfT).2)
        = RawTwoCellExpr.castBoundary
            (mapPath_inclRight_pathInvert bodyDom (pathWallFree_composePath_split oc bodyDom wfS).2).symm
            (mapPath_inclRight_pathInvert bodyCod (pathWallFree_composePath_split oc bodyCod wfT).2).symm
            body) :
    mapCellAlong pushoutRightCoprojectionTwo (wallFreeCellInvert (RawTwoCellExpr.whiskerLeft oc body) wfS wfT)
      = RawTwoCellExpr.castBoundary
          (mapPath_inclRight_pathInvert (composePath oc bodyDom) wfS).symm
          (mapPath_inclRight_pathInvert (composePath oc bodyCod) wfT).symm
          (RawTwoCellExpr.whiskerLeft oc body) := by
  have hWhiskerPath :
      RawTwoCellExpr.whiskerLeft
          (mapPath pushoutRightCoprojectionTwo.toComputadMorphism
            (pathInvert oc (pathWallFree_composePath_split oc bodyDom wfS).1)) body
        = RawTwoCellExpr.castBoundary
            (congrArg (fun path => composePath path bodyDom)
              (mapPath_inclRight_pathInvert oc (pathWallFree_composePath_split oc bodyDom wfS).1)).symm
            (congrArg (fun path => composePath path bodyCod)
              (mapPath_inclRight_pathInvert oc (pathWallFree_composePath_split oc bodyDom wfS).1)).symm
            (RawTwoCellExpr.whiskerLeft oc body) :=
    (castBoundarySymmCancel _ _
      (RawTwoCellExpr.whiskerLeft_pathCongr
        (mapPath_inclRight_pathInvert oc (pathWallFree_composePath_split oc bodyDom wfS).1) body)).symm
  show mapCellAlong pushoutRightCoprojectionTwo (RawTwoCellExpr.castBoundary
        (pathInvert_composePath oc bodyDom wfS
          (pathWallFree_composePath_split oc bodyDom wfS).1
          (pathWallFree_composePath_split oc bodyDom wfS).2).symm
        (pathInvert_composePath oc bodyCod wfT
          (pathWallFree_composePath_split oc bodyDom wfS).1
          (pathWallFree_composePath_split oc bodyCod wfT).2).symm
        (RawTwoCellExpr.whiskerLeft
          (pathInvert oc (pathWallFree_composePath_split oc bodyDom wfS).1)
          (wallFreeCellInvert body
            (pathWallFree_composePath_split oc bodyDom wfS).2
            (pathWallFree_composePath_split oc bodyCod wfT).2)))
      = RawTwoCellExpr.castBoundary
          (mapPath_inclRight_pathInvert (composePath oc bodyDom) wfS).symm
          (mapPath_inclRight_pathInvert (composePath oc bodyCod) wfT).symm
          (RawTwoCellExpr.whiskerLeft oc body)
  exact
    (mapCellAlong_castBoundary pushoutRightCoprojectionTwo _ _ _).trans
      ((congrArg (RawTwoCellExpr.castBoundary _ _)
          ((mapCellAlong_whiskerLeft pushoutRightCoprojectionTwo
                (pathInvert oc (pathWallFree_composePath_split oc bodyDom wfS).1)
                (wallFreeCellInvert body
                  (pathWallFree_composePath_split oc bodyDom wfS).2
                  (pathWallFree_composePath_split oc bodyCod wfT).2)).trans
            ((congrArg (RawTwoCellExpr.castBoundary _ _)
                (((congrArg (RawTwoCellExpr.whiskerLeft
                        (mapPath pushoutRightCoprojectionTwo.toComputadMorphism
                          (pathInvert oc (pathWallFree_composePath_split oc bodyDom wfS).1))) ihBody).trans
                    (RawTwoCellExpr.whiskerLeft_castBoundary
                      (mapPath pushoutRightCoprojectionTwo.toComputadMorphism
                        (pathInvert oc (pathWallFree_composePath_split oc bodyDom wfS).1)) _ _ body)).trans
                  ((congrArg (RawTwoCellExpr.castBoundary _ _) hWhiskerPath).trans
                    (RawTwoCellExpr.castBoundary_trans _ _ _ _ _)))).trans
              (RawTwoCellExpr.castBoundary_trans _ _ _ _ _)))).trans
        (RawTwoCellExpr.castBoundary_trans _ _ _ _ _))

/-- The whiskerRight reconciliation step of the cell backward round-trip — the `composePath _ oc` mirror of the
whiskerLeft step.  Byte-for-byte `reseatCellInvReseatCellWhiskerRightStep`. -/
theorem mapCellAlongWallFreeInvertWhiskerRightStep
    (oc : ModalityPath involutionMonadPushout.toModeGraph monadPushMode monadPushMode)
    {bodyDom bodyCod : ModalityPath involutionMonadPushout.toModeGraph monadPushMode monadPushMode}
    (body : RawTwoCellExpr involutionMonadPushout.toModeSignature bodyDom bodyCod)
    (wfS : pathWallFree (composePath bodyDom oc))
    (wfT : pathWallFree (composePath bodyCod oc))
    (ihBody : mapCellAlong pushoutRightCoprojectionTwo (wallFreeCellInvert body
          (pathWallFree_composePath_split bodyDom oc wfS).1
          (pathWallFree_composePath_split bodyCod oc wfT).1)
        = RawTwoCellExpr.castBoundary
            (mapPath_inclRight_pathInvert bodyDom (pathWallFree_composePath_split bodyDom oc wfS).1).symm
            (mapPath_inclRight_pathInvert bodyCod (pathWallFree_composePath_split bodyCod oc wfT).1).symm
            body) :
    mapCellAlong pushoutRightCoprojectionTwo (wallFreeCellInvert (RawTwoCellExpr.whiskerRight oc body) wfS wfT)
      = RawTwoCellExpr.castBoundary
          (mapPath_inclRight_pathInvert (composePath bodyDom oc) wfS).symm
          (mapPath_inclRight_pathInvert (composePath bodyCod oc) wfT).symm
          (RawTwoCellExpr.whiskerRight oc body) := by
  have hWhiskerPath :
      RawTwoCellExpr.whiskerRight
          (mapPath pushoutRightCoprojectionTwo.toComputadMorphism
            (pathInvert oc (pathWallFree_composePath_split bodyDom oc wfS).2)) body
        = RawTwoCellExpr.castBoundary
            (congrArg (composePath bodyDom)
              (mapPath_inclRight_pathInvert oc (pathWallFree_composePath_split bodyDom oc wfS).2)).symm
            (congrArg (composePath bodyCod)
              (mapPath_inclRight_pathInvert oc (pathWallFree_composePath_split bodyDom oc wfS).2)).symm
            (RawTwoCellExpr.whiskerRight oc body) :=
    (castBoundarySymmCancel _ _
      (RawTwoCellExpr.whiskerRight_pathCongr
        (mapPath_inclRight_pathInvert oc (pathWallFree_composePath_split bodyDom oc wfS).2) body)).symm
  show mapCellAlong pushoutRightCoprojectionTwo (RawTwoCellExpr.castBoundary
        (pathInvert_composePath bodyDom oc wfS
          (pathWallFree_composePath_split bodyDom oc wfS).1
          (pathWallFree_composePath_split bodyDom oc wfS).2).symm
        (pathInvert_composePath bodyCod oc wfT
          (pathWallFree_composePath_split bodyCod oc wfT).1
          (pathWallFree_composePath_split bodyDom oc wfS).2).symm
        (RawTwoCellExpr.whiskerRight
          (pathInvert oc (pathWallFree_composePath_split bodyDom oc wfS).2)
          (wallFreeCellInvert body
            (pathWallFree_composePath_split bodyDom oc wfS).1
            (pathWallFree_composePath_split bodyCod oc wfT).1)))
      = RawTwoCellExpr.castBoundary
          (mapPath_inclRight_pathInvert (composePath bodyDom oc) wfS).symm
          (mapPath_inclRight_pathInvert (composePath bodyCod oc) wfT).symm
          (RawTwoCellExpr.whiskerRight oc body)
  exact
    (mapCellAlong_castBoundary pushoutRightCoprojectionTwo _ _ _).trans
      ((congrArg (RawTwoCellExpr.castBoundary _ _)
          ((mapCellAlong_whiskerRight pushoutRightCoprojectionTwo
                (pathInvert oc (pathWallFree_composePath_split bodyDom oc wfS).2)
                (wallFreeCellInvert body
                  (pathWallFree_composePath_split bodyDom oc wfS).1
                  (pathWallFree_composePath_split bodyCod oc wfT).1)).trans
            ((congrArg (RawTwoCellExpr.castBoundary _ _)
                (((congrArg (RawTwoCellExpr.whiskerRight
                        (mapPath pushoutRightCoprojectionTwo.toComputadMorphism
                          (pathInvert oc (pathWallFree_composePath_split bodyDom oc wfS).2))) ihBody).trans
                    (RawTwoCellExpr.whiskerRight_castBoundary
                      (mapPath pushoutRightCoprojectionTwo.toComputadMorphism
                        (pathInvert oc (pathWallFree_composePath_split bodyDom oc wfS).2)) _ _ body)).trans
                  ((congrArg (RawTwoCellExpr.castBoundary _ _) hWhiskerPath).trans
                    (RawTwoCellExpr.castBoundary_trans _ _ _ _ _)))).trans
              (RawTwoCellExpr.castBoundary_trans _ _ _ _ _)))).trans
        (RawTwoCellExpr.castBoundary_trans _ _ _ _ _))

/-! ## The fuel assembly + the backward round-trip -/

/-- The cell backward round-trip, fuelled by structural cell size (the free MIDDLE mode of the whisker arms pinned
by `pushoutModeUnique` + `subst`, the fuel measure independent of the subst).  Mirror of
`reseatCellInvReseatCellFueled`. -/
theorem mapCellAlongWallFreeInvertFueled : (fuel : Nat) →
    {sourcePath targetPath :
      ModalityPath involutionMonadPushout.toModeGraph monadPushMode monadPushMode} →
    (cell : RawTwoCellExpr involutionMonadPushout.toModeSignature sourcePath targetPath) →
    (wfS : pathWallFree sourcePath) → (wfT : pathWallFree targetPath) →
    cell.size ≤ fuel →
    mapCellAlong pushoutRightCoprojectionTwo (wallFreeCellInvert cell wfS wfT)
      = RawTwoCellExpr.castBoundary (mapPath_inclRight_pathInvert sourcePath wfS).symm
          (mapPath_inclRight_pathInvert targetPath wfT).symm cell := by
  intro fuel
  induction fuel with
  | zero =>
      intro sourcePath targetPath cell _wfS _wfT hfuel
      exact absurd (Nat.le_trans (oneLeRawCellSize cell) hfuel) (Nat.not_succ_le_zero 0)
  | succ fuel ih =>
      intro sourcePath targetPath cell wfS wfT hfuel
      match cell, wfS, wfT, hfuel with
      | .gen generator, wfS, wfT, _ =>
          exact (congrArg (RawTwoCellExpr.gen (signature := involutionMonadPushout.toModeSignature))
              (wallFreeGenInvert_onTwoCell_full generator wfS wfT)).trans
            (pushoutGenTransportCast (mapPath_inclRight_pathInvert sourcePath wfS).symm
              (mapPath_inclRight_pathInvert targetPath wfT).symm generator)
      | .id path, wfS, _wfT, _ =>
          exact (RawTwoCellExpr.castBoundary_id (mapPath_inclRight_pathInvert path wfS).symm).symm
      | @RawTwoCellExpr.vcomp _ _ _ oneCellF oneCellG oneCellH cellL cellR, wfS, wfT, hf =>
          exact
            ((congrArg (fun leftCell => RawTwoCellExpr.vcomp leftCell
                    (mapCellAlong pushoutRightCoprojectionTwo
                      (wallFreeCellInvert cellR (wallFreeMiddleOfCell cellL wfS) wfT)))
                  (ih cellL wfS (wallFreeMiddleOfCell cellL wfS)
                    (Nat.le_trans (Nat.le_add_right cellL.size cellR.size)
                      (Nat.le_of_succ_le_succ hf)))).trans
              (congrArg (RawTwoCellExpr.vcomp (RawTwoCellExpr.castBoundary
                    (mapPath_inclRight_pathInvert oneCellF wfS).symm
                    (mapPath_inclRight_pathInvert oneCellG (wallFreeMiddleOfCell cellL wfS)).symm cellL))
                (ih cellR (wallFreeMiddleOfCell cellL wfS) wfT
                  (Nat.le_trans (Nat.le_add_left cellR.size cellL.size)
                    (Nat.le_of_succ_le_succ hf))))).trans
            (RawTwoCellExpr.castBoundary_vcomp (mapPath_inclRight_pathInvert oneCellF wfS).symm
              (mapPath_inclRight_pathInvert oneCellG (wallFreeMiddleOfCell cellL wfS)).symm
              (mapPath_inclRight_pathInvert oneCellH wfT).symm cellL cellR).symm
      | @RawTwoCellExpr.whiskerLeft _ _ mm _ oc bodyDom bodyCod body, wfS, wfT, hf =>
          have hmm : mm = monadPushMode := pushoutModeUnique mm
          subst hmm
          exact mapCellAlongWallFreeInvertWhiskerLeftStep oc body wfS wfT
            (ih body (pathWallFree_composePath_split oc bodyDom wfS).2
              (pathWallFree_composePath_split oc bodyCod wfT).2 (Nat.le_of_succ_le_succ hf))
      | @RawTwoCellExpr.whiskerRight _ _ mm _ bodyDom bodyCod oc body, wfS, wfT, hf =>
          have hmm : mm = monadPushMode := pushoutModeUnique mm
          subst hmm
          exact mapCellAlongWallFreeInvertWhiskerRightStep oc body wfS wfT
            (ih body (pathWallFree_composePath_split bodyDom oc wfS).1
              (pathWallFree_composePath_split bodyCod oc wfT).1 (Nat.le_of_succ_le_succ hf))

/-- ★★★ **THE WALL-FREE CELL CONVERSE'S BACKWARD ROUND-TRIP.**  Inverting a wall-free-boundary pushout 2-cell
(`wallFreeCellInvert`) then re-coprojecting through `mapCellAlong inclusionRightTwoReal` is the boundary cast of the
ORIGINAL cell back onto the `mapPath inclRight (pathInvert ..)` image boundary — the CELL-level analogue of the r11
1-cell forward round-trip `mapPath_inclRight_pathInvert`, and the exact mirror of `reseatCellInv_reseatCell`.  By
`mapCellAlongWallFreeInvertFueled` at `cell.size`. -/
theorem mapCellAlong_inclRight_wallFreeCellInvert
    {sourcePath targetPath : ModalityPath involutionMonadPushout.toModeGraph monadPushMode monadPushMode}
    (cell : RawTwoCellExpr involutionMonadPushout.toModeSignature sourcePath targetPath)
    (wfS : pathWallFree sourcePath) (wfT : pathWallFree targetPath) :
    mapCellAlong pushoutRightCoprojectionTwo (wallFreeCellInvert cell wfS wfT)
      = RawTwoCellExpr.castBoundary (mapPath_inclRight_pathInvert sourcePath wfS).symm
          (mapPath_inclRight_pathInvert targetPath wfT).symm cell :=
  mapCellAlongWallFreeInvertFueled cell.size cell wfS wfT (Nat.le_refl _)

/-! ## Truth probes — the backward round-trip fires on the r12 whiskered probes + fresh cells -/

/-- ★★ **TRUTH PROBE (whiskerLeft, the r12 probe).**  The r12 left-whisker probe `t ⊳ id_t : t·t ⇒ t·t`, inverted
then re-coprojected, is the boundary cast of itself.  The cast-fusion whiskerLeft step, machine-checked on the
concrete r12 cell (the recon's hand-worked self-attack 5a). -/
theorem mapCellAlongWallFreeInvert_whiskerLeftProbe :
    mapCellAlong pushoutRightCoprojectionTwo
        (wallFreeCellInvert probeWhiskerLeft tRunTwoWallFreeJoin tRunTwoWallFreeJoin)
      = RawTwoCellExpr.castBoundary
          (mapPath_inclRight_pathInvert (composePath monadPushTPath monadPushTPath) tRunTwoWallFreeJoin).symm
          (mapPath_inclRight_pathInvert (composePath monadPushTPath monadPushTPath) tRunTwoWallFreeJoin).symm
          probeWhiskerLeft :=
  mapCellAlong_inclRight_wallFreeCellInvert probeWhiskerLeft tRunTwoWallFreeJoin tRunTwoWallFreeJoin

/-- ★★ **TRUTH PROBE (whiskerRight, the r12 probe).**  The r12 right-whisker probe `id_t ⊲ t : t·t ⇒ t·t`, inverted
then re-coprojected, is the boundary cast of itself. -/
theorem mapCellAlongWallFreeInvert_whiskerRightProbe :
    mapCellAlong pushoutRightCoprojectionTwo
        (wallFreeCellInvert probeWhiskerRight tRunTwoWallFreeJoin tRunTwoWallFreeJoin)
      = RawTwoCellExpr.castBoundary
          (mapPath_inclRight_pathInvert (composePath monadPushTPath monadPushTPath) tRunTwoWallFreeJoin).symm
          (mapPath_inclRight_pathInvert (composePath monadPushTPath monadPushTPath) tRunTwoWallFreeJoin).symm
          probeWhiskerRight :=
  mapCellAlong_inclRight_wallFreeCellInvert probeWhiskerRight tRunTwoWallFreeJoin tRunTwoWallFreeJoin

/-- ★★ **TRUTH PROBE (vcomp, a fresh cell).**  The vertical composite `id_t ⊟ id_t : t ⇒ t`, inverted then
re-coprojected, is the boundary cast of itself — exercising the `vcomp` fuel arm on a fresh cell. -/
theorem mapCellAlongWallFreeInvert_vcompProbe :
    mapCellAlong pushoutRightCoprojectionTwo
        (wallFreeCellInvert probeVcomp monadPushTPath_wallFree monadPushTPath_wallFree)
      = RawTwoCellExpr.castBoundary
          (mapPath_inclRight_pathInvert monadPushTPath monadPushTPath_wallFree).symm
          (mapPath_inclRight_pathInvert monadPushTPath monadPushTPath_wallFree).symm
          probeVcomp :=
  mapCellAlong_inclRight_wallFreeCellInvert probeVcomp monadPushTPath_wallFree monadPushTPath_wallFree

/-- ★★ **TRUTH PROBE (gen, the pushout unit).**  The pushout monad unit `eta : id ⇒ t`, inverted then
re-coprojected, is the boundary cast of itself — the gen fuel arm on a real reconstructed generator. -/
theorem mapCellAlongWallFreeInvert_unitProbe :
    mapCellAlong pushoutRightCoprojectionTwo
        (wallFreeCellInvert pushoutEta True.intro monadPushTPath_wallFree)
      = RawTwoCellExpr.castBoundary
          (mapPath_inclRight_pathInvert
            (ModalityPath.nil (graph := involutionMonadPushout.toModeGraph) monadPushMode) True.intro).symm
          (mapPath_inclRight_pathInvert monadPushTPath monadPushTPath_wallFree).symm
          pushoutEta :=
  mapCellAlong_inclRight_wallFreeCellInvert pushoutEta True.intro monadPushTPath_wallFree

/-! ## The dim-2 bijection statement (paired with the r11 dim-1 one) -/

/-- ★★★ **THE CELL-LEVEL SECTION, PAIRED WITH THE r11 1-CELL BIJECTION.**  For a wall-free-boundary pushout 2-cell,
`mapCellAlong inclusionRightTwoReal ∘ wallFreeCellInvert` returns the cell up to the boundary cast induced by the
r11 1-cell forward round-trip `mapPath_inclRight_pathInvert` — the 2-dimensional companion of the r11 1-cell
bijection (`pathInvert` + `mapPath_inclRight_injective`).  Packaged as the pair (1-cell round-trip on the
boundaries, cell round-trip on the interior), the essential-surjectivity converse across both dimensions. -/
theorem pushoutCellRoundTripBijection
    {sourcePath targetPath : ModalityPath involutionMonadPushout.toModeGraph monadPushMode monadPushMode}
    (cell : RawTwoCellExpr involutionMonadPushout.toModeSignature sourcePath targetPath)
    (wfS : pathWallFree sourcePath) (wfT : pathWallFree targetPath) :
    (mapPath (inclusionRight involutionComputad monadComputad involutionMonadSameModes)
          (pathInvert sourcePath wfS) = sourcePath)
      ∧ (mapPath (inclusionRight involutionComputad monadComputad involutionMonadSameModes)
          (pathInvert targetPath wfT) = targetPath)
      ∧ mapCellAlong pushoutRightCoprojectionTwo (wallFreeCellInvert cell wfS wfT)
          = RawTwoCellExpr.castBoundary (mapPath_inclRight_pathInvert sourcePath wfS).symm
              (mapPath_inclRight_pathInvert targetPath wfT).symm cell :=
  ⟨mapPath_inclRight_pathInvert sourcePath wfS, mapPath_inclRight_pathInvert targetPath wfT,
    mapCellAlong_inclRight_wallFreeCellInvert cell wfS wfT⟩

/-! ## Honesty markers -/

/-- ★★★ **Honesty marker — the wall-free CELL converse's BACKWARD round-trip SHIPS (all five constructors), the
dim-2 bijection paired with the r11 dim-1 one; #2043 stays OPEN.**  `= true`.  r12 shipped the FORWARD cell converse
`wallFreeCellInvert` and its gen-case backward SECTION (index round-trip); r13 discharges the FULL backward cell
round-trip `mapCellAlong inclRight (wallFreeCellInvert cell ..) = castBoundary .. cell`
(`mapCellAlong_inclRight_wallFreeCellInvert`), the exact mirror of the shipped `reseatCellInv_reseatCell`: the two
cast-fusion step theorems (`mapCellAlongWallFreeInvertWhiskerLeftStep` / `..RightStep`) reconcile the inner
`pathInvert_composePath` cast against the outer `mapPath_composePath` cast through `mapPath_inclRight_pathInvert`;
the gen-case FULL round-trip (`wallFreeGenInvert_onTwoCell_full`) upgrades the r12 index round-trip via `Subtype.ext`;
the structural cell-size fuel (`mapCellAlongWallFreeInvertFueled`) pins the free middle mode with `pushoutModeUnique`.
The PATH leg is FREE (`mapPath_inclRight_pathInvert` is word-routed), so this round-trip is strictly cheaper than the
reseat precedent.  TRUTH-PROBED on the r12 whiskered probes (`whiskerLeftProbe` / `whiskerRightProbe`) and fresh
`vcomp` / `gen` cells.  Paired with the r11 1-cell bijection into `pushoutCellRoundTripBijection` (dim-1 boundary +
dim-2 interior).  FLIPPED NO master: `fxAmalg_hasFullSaturatedPushoutDispatch` STAYS `false`,
`fxAmalg_hasGeneralPushoutDispatch` STAYS `false`, `fxAmalg_topFactorizationInductionStaysWalled` STAYS `true`.  This
is the essential-surjectivity CONVERSE at the cell level, NOT purification/projection completeness (residual (iii)).
#2043 does NOT close — no fabricated flip.  `= true`. -/
def fxAmalg_hasCellConverseBackwardRoundTrip : Bool := true

end FX1Poly.Polygraph.Amalgam
