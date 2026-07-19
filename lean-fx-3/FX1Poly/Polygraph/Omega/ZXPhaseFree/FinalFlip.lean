import FX1Poly.Polygraph.Omega.ZXPhaseFree.SpiderRelationSeed
import FX1Poly.Polygraph.Omega.ZXPhaseFree.CompletenessGate
import FX1Poly.Polygraph.Omega.ZXPhaseFree.FusionRepair
import FX1Poly.Polygraph.Omega.ZXPhaseFree.NormalFormCensus
import FX1Poly.Polygraph.Omega.ZXPhaseFree.NormalFormLadder
import FX1Poly.Polygraph.Omega.ZXPhaseFree.ExchangeCompleteness
import FX1Poly.Polygraph.Omega.ZXPhaseFree.AbsorptionFlip
import FX1Poly.Polygraph.Omega.ZXPhaseFree.WiringFlip

/-! # Polygraph/Omega/ZXPhaseFree/FinalFlip — the generator-transport round:
elementary row operations as normal-form conversions

The WiringFlip round left two owner-false residuals before the completeness flip:
`zxwAbsorptionStatement` and `zxwGeneratorTransportStatement`, with the assembly
`zxwCompletenessOfAbsorptionAndTransport` already proved.  This round attacks the
TRANSPORT residual along its documented route — NF-to-NF conversion along
elementary row operations — and lands:

* (i)  ZERO-ROW DELETION, COMPLETE: the zero-row comb collapses to the empty
  diagram (`zxfZeroCombCollapse` — the discard consumes the crossing staircase
  through `slideRight (zSpider 1 0)` windows, then the create/discard pair dies
  by the `boneZ` row), lifted to the normal form as the first whole elementary
  operation: `zxfNormalFormZeroRowDrop`, fired at a literal instance.
* (ii) THE CONDITIONAL TRANSPORT ASSEMBLY, COMPLETE: the remaining two
  elementary moves are minted as Props on ADJACENT COMB PAIRS —
  `zxfCombSwapStatement` (row swap) and `zxfCombXorAbsorbStatement` (the
  transvection) — and `zxfTransportOfCombMoves` PROVES that those two moves
  imply the full `zxwGeneratorTransportStatement`: duplication
  (`zxfCombDuplicate`), duplication-out of the fold (`zxfCombDupOut`),
  absorption of any span member by induction on the span derivation
  (`zxfCombAbsorb`), comb-past-fold commutation (`zxfCombPastBlocks`),
  extension/shrinking of generator lists (`zxfBlocksExtend`/`zxfBlocksShrink`),
  and the span-decision soundness bridge, lifted between the shared init and
  kill layers.  Same honest shape as the committed
  `zxwCompletenessOfAbsorptionAndTransport`: the assembly is closed, the two
  named moves are the exact residual.
* (iii) THE MOVE-LEVEL BRICKS: the birth-side conjugation lemmas land WHOLE —
  `zxfCreatesCrossInsert` (a crossing after two creations dissolves) and
  `zxfCreatesCnotInsert` (a fork/merge CNOT gadget after two creations
  dissolves — cup recolouring, X-Frobenius, the mirrored X-unit, the dual
  unit-copy bialgebra row); THREE of the four crossing-ride windows are proven
  (`zxfCrossWindowFF` = Yang-Baxter, `zxfCrossWindowTF`, `zxfCrossWindowFT`)
  plus the merge-chain reassociation `zxfCrossIntoMergeChain`; the fourth
  window is walled owner-false with its exact configuration and a kernel span
  pin (`zxfCrossWindowTTStatement`).  The comb-shift/gadget-fission plumbing
  (`zxfCombLayersShift`, `zxfGadgetLayers`, `zxfCombLayersCons`) is in place
  for the ride assembly.  NOT LANDED (recorded on the markers, owners false):
  the parked/zipped double-carrier interleaving, the two ride inductions, and
  the four cnot windows — so `zxfCombSwapStatement`,
  `zxfCombXorAbsorbStatement`, and therefore `zxwGeneratorTransportStatement`
  remain open; the committed WiringFlip owners stay byte-intact.

Raw Lean 4 + Init only; zero-axiom; structural recursion only; no `List.append`,
no `Int`, no `Nat.sub/div/mod/min/max`, no wildcard match arms over inductive
scrutinees. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace FX1Poly.Polygraph.Omega.ZXPhaseFree

/-! ## Stage 0 — plumbing: row-list concatenation, comb shift, gadget fission -/

/-- Cons-only concatenation of generator-row lists. -/
def zxfCatRows : List (List Bool) -> List (List Bool) -> List (List Bool)
  | [], secondRows => secondRows
  | headRow :: restRows, secondRows => headRow :: zxfCatRows restRows secondRows

theorem zxfCatRowsAllWidth {rowWidth : Nat} :
    (firstRows secondRows : List (List Bool)) ->
    ZxpAllWidth rowWidth firstRows -> ZxpAllWidth rowWidth secondRows ->
    ZxpAllWidth rowWidth (zxfCatRows firstRows secondRows)
  | [], _secondRows, _hFirst, hSecond => hSecond
  | headRow :: restRows, secondRows, hFirst, hSecond => by
      cases hFirst with
      | cons hHead hRest =>
          exact ZxpAllWidth.cons hHead
            (zxfCatRowsAllWidth restRows secondRows hRest hSecond)

/-- The generator fold splits over row-list concatenation. -/
theorem zxfGeneratorBlockLayersCat : (firstRows secondRows : List (List Bool)) ->
    zxnGeneratorBlockLayers (zxfCatRows firstRows secondRows)
      = zxpCatLayers (zxnGeneratorBlockLayers firstRows)
          (zxnGeneratorBlockLayers secondRows)
  | [], _secondRows => rfl
  | headRow :: restRows, secondRows => by
      show zxpCatLayers (zxnXorRowLayers headRow)
          (zxnGeneratorBlockLayers (zxfCatRows restRows secondRows))
        = zxpCatLayers
            (zxpCatLayers (zxnXorRowLayers headRow) (zxnGeneratorBlockLayers restRows))
            (zxnGeneratorBlockLayers secondRows)
      rw [zxfGeneratorBlockLayersCat restRows secondRows,
        zxnCatLayersAssoc (zxnXorRowLayers headRow) (zxnGeneratorBlockLayers restRows)
          (zxnGeneratorBlockLayers secondRows)]

/-- Row membership survives concatenation on the right. -/
theorem zxfRowMemCatLeft {row : List Bool} :
    (firstRows : List (List Bool)) -> (secondRows : List (List Bool)) ->
    ZxpRowMem row firstRows -> ZxpRowMem row (zxfCatRows firstRows secondRows)
  | [], _secondRows, hMem => nomatch hMem
  | _headRow :: restRows, secondRows, hMem => by
      cases hMem with
      | head => exact ZxpRowMem.head _ (zxfCatRows restRows secondRows)
      | tail hRest =>
          exact ZxpRowMem.tail (zxfRowMemCatLeft restRows secondRows hRest)

/-- Row membership survives concatenation on the left. -/
theorem zxfRowMemCatRight {row : List Bool} :
    (firstRows : List (List Bool)) -> (secondRows : List (List Bool)) ->
    ZxpRowMem row secondRows -> ZxpRowMem row (zxfCatRows firstRows secondRows)
  | [], _secondRows, hMem => hMem
  | _headRow :: restRows, secondRows, hMem =>
      ZxpRowMem.tail (zxfRowMemCatRight restRows secondRows hMem)

/-- Span membership extends along left concatenation. -/
theorem zxfMemSpanCatRight {rowWidth : Nat} {vector : List Bool}
    (firstRows secondRows : List (List Bool))
    (hMem : ZxpMemSpan rowWidth secondRows vector) :
    ZxpMemSpan rowWidth (zxfCatRows firstRows secondRows) vector := by
  induction hMem with
  | zero => exact ZxpMemSpan.zero
  | pick row hRow _hVec innerMem =>
      exact ZxpMemSpan.pick row (zxfRowMemCatRight firstRows secondRows hRow) innerMem

/-- Span membership extends along right concatenation. -/
theorem zxfMemSpanCatLeft {rowWidth : Nat} {vector : List Bool}
    (firstRows secondRows : List (List Bool))
    (hMem : ZxpMemSpan rowWidth firstRows vector) :
    ZxpMemSpan rowWidth (zxfCatRows firstRows secondRows) vector := by
  induction hMem with
  | zero => exact ZxpMemSpan.zero
  | pick row hRow _hVec innerMem =>
      exact ZxpMemSpan.pick row (zxfRowMemCatLeft firstRows secondRows hRow) innerMem

/-- Whisker-shift for the comb: extra left wires are an outer whisker. -/
theorem zxfCombLayersShift (extraWires : Nat) : (rowBits : List Bool) ->
    (basePrefix : Nat) ->
    zxnCombLayers (extraWires + basePrefix) rowBits
      = zxpWhiskerLayers extraWires 0 (zxnCombLayers basePrefix rowBits)
  | [], basePrefix => by
      show [zxpWhiskerLayer (extraWires + basePrefix) 0 [ZxpCell.zSpider 1 0]]
        = [zxpWhiskerLayer extraWires 0
            (zxpWhiskerLayer basePrefix 0 [ZxpCell.zSpider 1 0])]
      rw [zxnWhiskerLayerCompose extraWires 0 basePrefix 0 [ZxpCell.zSpider 1 0]]
  | false :: restBits, basePrefix => by
      show zxpWhiskerLayer (extraWires + basePrefix) restBits.length [ZxpCell.crossing]
          :: zxnCombLayers ((extraWires + basePrefix) + 1) restBits
        = zxpWhiskerLayer extraWires 0
            (zxpWhiskerLayer basePrefix restBits.length [ZxpCell.crossing])
          :: zxpWhiskerLayers extraWires 0 (zxnCombLayers (basePrefix + 1) restBits)
      rw [zxnWhiskerLayerCompose extraWires 0 basePrefix restBits.length
        [ZxpCell.crossing]]
      exact congrArg
        (fun tailLayers =>
          zxpWhiskerLayer (extraWires + basePrefix) (restBits.length + 0)
            [ZxpCell.crossing] :: tailLayers)
        (zxfCombLayersShift extraWires restBits (basePrefix + 1))
  | true :: restBits, basePrefix => by
      show zxpWhiskerLayer (extraWires + basePrefix) (restBits.length + 1)
            [ZxpCell.zSpider 1 2]
          :: zxpWhiskerLayer ((extraWires + basePrefix) + 1) restBits.length
            [ZxpCell.xSpider 2 1]
          :: zxpWhiskerLayer (extraWires + basePrefix) restBits.length
            [ZxpCell.crossing]
          :: zxnCombLayers ((extraWires + basePrefix) + 1) restBits
        = zxpWhiskerLayer extraWires 0
            (zxpWhiskerLayer basePrefix (restBits.length + 1) [ZxpCell.zSpider 1 2])
          :: zxpWhiskerLayer extraWires 0
            (zxpWhiskerLayer (basePrefix + 1) restBits.length [ZxpCell.xSpider 2 1])
          :: zxpWhiskerLayer extraWires 0
            (zxpWhiskerLayer basePrefix restBits.length [ZxpCell.crossing])
          :: zxpWhiskerLayers extraWires 0 (zxnCombLayers (basePrefix + 1) restBits)
      rw [zxnWhiskerLayerCompose extraWires 0 basePrefix (restBits.length + 1)
          [ZxpCell.zSpider 1 2],
        zxnWhiskerLayerCompose extraWires 0 (basePrefix + 1) restBits.length
          [ZxpCell.xSpider 2 1],
        zxnWhiskerLayerCompose extraWires 0 basePrefix restBits.length
          [ZxpCell.crossing]]
      exact congrArg
        (fun tailLayers =>
          zxpWhiskerLayer (extraWires + basePrefix) ((restBits.length + 1) + 0)
              [ZxpCell.zSpider 1 2]
            :: zxpWhiskerLayer ((extraWires + basePrefix) + 1) (restBits.length + 0)
              [ZxpCell.xSpider 2 1]
            :: zxpWhiskerLayer (extraWires + basePrefix) (restBits.length + 0)
              [ZxpCell.crossing]
            :: tailLayers)
        (zxfCombLayersShift extraWires restBits (basePrefix + 1))

/-- A context-free whisker pad collapses to the bare whiskered window. -/
theorem zxfPadNoContext (contextSource leftWires rightWires : Nat)
    (window : ZxpDiagram) :
    zxpPadDiagram contextSource leftWires rightWires [] [] window
      = { sourceArity := contextSource
          layers := zxpWhiskerLayers leftWires rightWires window.layers } := by
  show ZxpDiagram.mk contextSource
      (zxpCatLayers (zxpWhiskerLayers leftWires rightWires window.layers) [])
    = ZxpDiagram.mk contextSource (zxpWhiskerLayers leftWires rightWires window.layers)
  rw [zxpCatLayersNilRight]

/-- The per-position gadget of the comb: crossing for a skipped strand, the
fork/xor/crossing triple for a tapped strand. -/
def zxfGadgetLayers (prefixWires rightWires : Nat) : Bool -> List (List ZxpCell)
  | false => [zxpWhiskerLayer prefixWires rightWires [ZxpCell.crossing]]
  | true =>
      [zxpWhiskerLayer prefixWires (rightWires + 1) [ZxpCell.zSpider 1 2],
        zxpWhiskerLayer (prefixWires + 1) rightWires [ZxpCell.xSpider 2 1],
        zxpWhiskerLayer prefixWires rightWires [ZxpCell.crossing]]

/-- The comb fissions into its head gadget and tail. -/
theorem zxfCombLayersCons (prefixWires : Nat) (headBit : Bool) (restBits : List Bool) :
    zxnCombLayers prefixWires (headBit :: restBits)
      = zxpCatLayers (zxfGadgetLayers prefixWires restBits.length headBit)
          (zxnCombLayers (prefixWires + 1) restBits) := by
  cases headBit with
  | false => exact rfl
  | true => exact rfl

/-! ## Stage 1 — ZERO-ROW DELETION, COMPLETE

The zero-row comb is create, a crossing staircase, discard.  The discard eats
the staircase from the right (each step is the `slideRight (zSpider 1 0)`
window read backwards), meets the create, and the pair dies by `boneZ`. -/

/-- The all-false comb collapses to the bare discard at its entry position:
`combLayers p (zeroRow m) ~ [discard at p]`. -/
theorem zxfZeroCombTail : (zeroCount prefixWires : Nat) ->
    ZxwConv
      { sourceArity := prefixWires + (1 + zeroCount)
        layers := zxnCombLayers prefixWires (zxpZeroRow zeroCount) }
      { sourceArity := prefixWires + (1 + zeroCount)
        layers := [zxpWhiskerLayer prefixWires zeroCount [ZxpCell.zSpider 1 0]] }
  | 0, prefixWires =>
      ZxwConv.refl _ (ZxpLayersWF.cons
        ((zxpWhiskerLayerDomArity prefixWires 0 [ZxpCell.zSpider 1 0]).trans rfl)
        (ZxpLayersWF.nil _))
  | zeroPred + 1, prefixWires => by
      have hRestLen : (zxpZeroRow zeroPred).length = zeroPred := zxpZeroRowLength zeroPred
      -- head layer: the crossing at the prefix; tail: the inner zero comb
      have hInner := zxfZeroCombTail zeroPred (prefixWires + 1)
      -- lift the inner collapse under the crossing layer
      have hCrossDom : zxpLayerDomArity
          (zxpWhiskerLayer prefixWires (zxpZeroRow zeroPred).length [ZxpCell.crossing])
          = prefixWires + (1 + (zeroPred + 1)) := by
        rw [zxpWhiskerLayerDomArity, hRestLen]
        show prefixWires + (2 + zeroPred) = prefixWires + (1 + (zeroPred + 1))
        exact congrArg (fun innerValue => prefixWires + innerValue)
          (zxnTwoPlusEqOnePlusSucc zeroPred)
      have hCrossCod : zxpLayersCodArity (prefixWires + (1 + (zeroPred + 1)))
          [zxpWhiskerLayer prefixWires (zxpZeroRow zeroPred).length [ZxpCell.crossing]]
          = (prefixWires + 1) + (1 + zeroPred) := by
        show zxpLayerCodArity
            (zxpWhiskerLayer prefixWires (zxpZeroRow zeroPred).length
              [ZxpCell.crossing])
          = (prefixWires + 1) + (1 + zeroPred)
        rw [zxpWhiskerLayerCodArity, hRestLen]
        show prefixWires + (2 + zeroPred) = (prefixWires + 1) + (1 + zeroPred)
        exact zxnStepArityShuffle prefixWires zeroPred
      have hCrossWF : ZxpLayersWF (prefixWires + (1 + (zeroPred + 1)))
          [zxpWhiskerLayer prefixWires (zxpZeroRow zeroPred).length
            [ZxpCell.crossing]] :=
        ZxpLayersWF.cons hCrossDom (ZxpLayersWF.nil _)
      have hLifted := zxwLiftConv (prefixWires + (1 + (zeroPred + 1)))
        [zxpWhiskerLayer prefixWires (zxpZeroRow zeroPred).length [ZxpCell.crossing]]
        [] hInner hCrossWF
        (hCrossCod.trans rfl)
        (ZxpLayersWF.nil _)
      rw [zxpCatLayersNilRight, zxpCatLayersNilRight] at hLifted
      -- the lifted result: crossing layer :: [discard at prefix+1]  ~ target via
      -- the slideRight(discard) window read backwards
      refine ZxwConv.trans ?_ (ZxwConv.trans hLifted ?_)
      · exact ZxwConv.refl _ (by
          show ZxpLayersWF (prefixWires + (1 + (zeroPred + 1)))
            (zxnCombLayers prefixWires (false :: zxpZeroRow zeroPred))
          have hWFraw := zxnCombLayersWF (false :: zxpZeroRow zeroPred) prefixWires
          have hLenEq : (false :: zxpZeroRow zeroPred).length = zeroPred + 1 := by
            show (zxpZeroRow zeroPred).length + 1 = zeroPred + 1
            rw [hRestLen]
          rw [hLenEq] at hWFraw
          exact hWFraw)
      · -- [cross at prefix][discard at prefix+1] ~ [discard at prefix]:
        -- whisker(prefix, zeroPred) of the slideRight(zSpider 1 0) window.
        have hSlide := ZxwConv.symm (zxwSlideRightConv (ZxpCell.zSpider 1 0))
        -- slideRightRhs (z10) = {2, [[crossing],[wire, z10]]}
        -- slideRightLhs (z10) = {2, [[z10, wire]]}
        have hWindowLift := zxwConvLift (prefixWires + (1 + (zeroPred + 1)))
          prefixWires zeroPred [] [] hSlide
          (ZxpLayersWF.nil _)
          (by
            show prefixWires + (1 + (zeroPred + 1))
              = prefixWires + ((zxwSlideRightRhs (ZxpCell.zSpider 1 0)).sourceArity
                + zeroPred)
            show prefixWires + (1 + (zeroPred + 1)) = prefixWires + (2 + zeroPred)
            exact congrArg (fun innerValue => prefixWires + innerValue)
              (zxnTwoPlusEqOnePlusSucc zeroPred).symm)
          (ZxpLayersWF.nil _)
        rw [zxfPadNoContext, zxfPadNoContext] at hWindowLift
        show ZxwConv
          { sourceArity := prefixWires + (1 + (zeroPred + 1))
            layers :=
              zxpWhiskerLayer prefixWires (zxpZeroRow zeroPred).length
                  [ZxpCell.crossing]
                :: [zxpWhiskerLayer (prefixWires + 1) zeroPred [ZxpCell.zSpider 1 0]] }
          { sourceArity := prefixWires + (1 + (zeroPred + 1))
            layers := [zxpWhiskerLayer prefixWires (zeroPred + 1) [ZxpCell.zSpider 1 0]] }
        have hLhsShape : zxpWhiskerLayers prefixWires zeroPred
            (zxwSlideRightRhs (ZxpCell.zSpider 1 0)).layers
            = zxpWhiskerLayer prefixWires (zxpZeroRow zeroPred).length
                  [ZxpCell.crossing]
              :: [zxpWhiskerLayer (prefixWires + 1) zeroPred [ZxpCell.zSpider 1 0]] := by
          show zxpWhiskerLayer prefixWires zeroPred [ZxpCell.crossing]
              :: zxpWhiskerLayer prefixWires zeroPred [ZxpCell.wire, ZxpCell.zSpider 1 0]
              :: []
            = zxpWhiskerLayer prefixWires (zxpZeroRow zeroPred).length
                  [ZxpCell.crossing]
              :: [zxpWhiskerLayer (prefixWires + 1) zeroPred [ZxpCell.zSpider 1 0]]
          rw [hRestLen]
          refine congrArg
            (fun innerLayer =>
              zxpWhiskerLayer prefixWires zeroPred [ZxpCell.crossing]
                :: [innerLayer]) ?_
          show zxpCatCells (zxpWireCells prefixWires)
              (ZxpCell.wire :: ZxpCell.zSpider 1 0 :: zxpWireCells zeroPred)
            = zxpCatCells (zxpWireCells (prefixWires + 1))
              (ZxpCell.zSpider 1 0 :: zxpWireCells zeroPred)
          exact zxaWiresConsWire prefixWires
            (ZxpCell.zSpider 1 0 :: zxpWireCells zeroPred)
        have hRhsShape : zxpWhiskerLayers prefixWires zeroPred
            (zxwSlideRightLhs (ZxpCell.zSpider 1 0)).layers
            = [zxpWhiskerLayer prefixWires (zeroPred + 1) [ZxpCell.zSpider 1 0]] := by
          show [zxpWhiskerLayer prefixWires zeroPred [ZxpCell.zSpider 1 0, ZxpCell.wire]]
            = [zxpWhiskerLayer prefixWires (zeroPred + 1) [ZxpCell.zSpider 1 0]]
          refine congrArg (fun innerLayer => [innerLayer]) ?_
          show zxpCatCells (zxpWireCells prefixWires)
              (ZxpCell.zSpider 1 0 :: ZxpCell.wire :: zxpWireCells zeroPred)
            = zxpCatCells (zxpWireCells prefixWires)
              (ZxpCell.zSpider 1 0 :: zxpWireCells (zeroPred + 1))
          exact rfl
        rw [hLhsShape, hRhsShape] at hWindowLift
        exact hWindowLift

/-- THE ZERO-COMB COLLAPSE: the conditional-xor block of the all-false row is
convertible to the empty diagram — create slides into discard, `boneZ` fires. -/
theorem zxfZeroCombCollapse (strandCount : Nat) :
    ZxwConv
      { sourceArity := strandCount
        layers := zxnXorRowLayers (zxpZeroRow strandCount) }
      { sourceArity := strandCount, layers := [] } := by
  have hLen : (zxpZeroRow strandCount).length = strandCount :=
    zxpZeroRowLength strandCount
  -- step 1: collapse the tail to the single discard layer, under the create layer
  have hTail := zxfZeroCombTail strandCount 0
  have hCreateDom : zxpLayerDomArity
      (zxpWhiskerLayer 0 (zxpZeroRow strandCount).length [ZxpCell.zSpider 0 1])
      = strandCount := by
    rw [zxpWhiskerLayerDomArity, hLen]
    show 0 + (0 + strandCount) = strandCount
    rw [Nat.zero_add, Nat.zero_add]
  have hCreateCod : zxpLayersCodArity strandCount
      [zxpWhiskerLayer 0 (zxpZeroRow strandCount).length [ZxpCell.zSpider 0 1]]
      = 0 + (1 + strandCount) := by
    show zxpLayerCodArity
        (zxpWhiskerLayer 0 (zxpZeroRow strandCount).length [ZxpCell.zSpider 0 1])
      = 0 + (1 + strandCount)
    rw [zxpWhiskerLayerCodArity, hLen]
    exact rfl
  have hCreateWF : ZxpLayersWF strandCount
      [zxpWhiskerLayer 0 (zxpZeroRow strandCount).length [ZxpCell.zSpider 0 1]] :=
    ZxpLayersWF.cons hCreateDom (ZxpLayersWF.nil _)
  have hLifted := zxwLiftConv strandCount
    [zxpWhiskerLayer 0 (zxpZeroRow strandCount).length [ZxpCell.zSpider 0 1]]
    [] hTail hCreateWF hCreateCod (ZxpLayersWF.nil _)
  rw [zxpCatLayersNilRight, zxpCatLayersNilRight] at hLifted
  refine ZxwConv.trans hLifted ?_
  -- step 2: [create at 0][discard at 0] ~ [] : the boneZ row whiskered (0, n)
  have hBone : ZxwConv (zxpRowLhs ZxpRowTag.boneZ) (zxpRowRhs ZxpRowTag.boneZ) :=
    zxwOfZxpConv (zxpRowConv ZxpRowTag.boneZ)
  have hBoneLift := zxwConvLift strandCount 0 strandCount [] [] hBone
    (ZxpLayersWF.nil _)
    (by
      show strandCount = 0 + ((zxpRowLhs ZxpRowTag.boneZ).sourceArity + strandCount)
      show strandCount = 0 + (0 + strandCount)
      rw [Nat.zero_add, Nat.zero_add])
    (ZxpLayersWF.nil _)
  rw [zxfPadNoContext, zxfPadNoContext] at hBoneLift
  have hLhsShape : zxpWhiskerLayers 0 strandCount (zxpRowLhs ZxpRowTag.boneZ).layers
      = zxpWhiskerLayer 0 (zxpZeroRow strandCount).length [ZxpCell.zSpider 0 1]
        :: [zxpWhiskerLayer 0 strandCount [ZxpCell.zSpider 1 0]] := by
    show zxpWhiskerLayer 0 strandCount [ZxpCell.zSpider 0 1]
        :: zxpWhiskerLayer 0 strandCount [ZxpCell.zSpider 1 0] :: []
      = zxpWhiskerLayer 0 (zxpZeroRow strandCount).length [ZxpCell.zSpider 0 1]
        :: [zxpWhiskerLayer 0 strandCount [ZxpCell.zSpider 1 0]]
    rw [hLen]
  have hRhsShape : zxpWhiskerLayers 0 strandCount (zxpRowRhs ZxpRowTag.boneZ).layers
      = ([] : List (List ZxpCell)) := rfl
  rw [hLhsShape, hRhsShape] at hBoneLift
  exact hBoneLift

/-! ## Stage 2 — the zero-row drop at the NORMAL FORM -/

/-- ZERO-ROW DELETION AT THE NORMAL FORM: prepending the zero generator row
gives a `ZxwConv`-convertible normal form — the first elementary row operation
of the documented transport route, whole. -/
theorem zxfNormalFormZeroRowDrop (domWidth codWidth : Nat)
    (generatorRows : List (List Bool))
    (hAll : ZxpAllWidth (domWidth + codWidth) generatorRows) :
    ZxwConv
      (zxnNormalForm domWidth codWidth (zxpZeroRow (domWidth + codWidth) :: generatorRows))
      (zxnNormalForm domWidth codWidth generatorRows) := by
  have hZeroLen : (zxpZeroRow (domWidth + codWidth)).length = domWidth + codWidth :=
    zxpZeroRowLength (domWidth + codWidth)
  -- the zero comb collapses; lift between init and (blocks ++ kill)
  have hCollapse := zxfZeroCombCollapse (domWidth + codWidth)
  have hZeroComb : ZxwConv
      { sourceArity := domWidth + codWidth
        layers := zxnXorRowLayers (zxpZeroRow (domWidth + codWidth)) }
      { sourceArity := domWidth + codWidth, layers := [] } := hCollapse
  have hInitWF : ZxpLayersWF domWidth [zxnInitLayer domWidth codWidth] :=
    ZxpLayersWF.cons (zxnInitLayerDomArity domWidth codWidth) (ZxpLayersWF.nil _)
  have hInitCod : zxpLayersCodArity domWidth [zxnInitLayer domWidth codWidth]
      = domWidth + codWidth := by
    show zxpLayerCodArity (zxnInitLayer domWidth codWidth) = domWidth + codWidth
    exact zxnInitLayerCodArity domWidth codWidth
  have hBlocksWF := zxnGeneratorBlockLayersWF generatorRows (domWidth + codWidth) hAll
  have hBlocksCod :=
    zxnGeneratorBlockLayersCodArity generatorRows (domWidth + codWidth) hAll
  have hKillWF : ZxpLayersWF (domWidth + codWidth) [zxnKillLayer domWidth codWidth] :=
    ZxpLayersWF.cons (zxnKillLayerDomArity domWidth codWidth) (ZxpLayersWF.nil _)
  have hAfterWF : ZxpLayersWF (domWidth + codWidth)
      (zxpCatLayers (zxnGeneratorBlockLayers generatorRows)
        [zxnKillLayer domWidth codWidth]) := by
    refine zxpLayersWFCat _ _ hBlocksWF ?_
    rw [hBlocksCod]
    exact hKillWF
  have hWindowCod : zxpDiagramCodArity
      { sourceArity := domWidth + codWidth
        layers := zxnXorRowLayers (zxpZeroRow (domWidth + codWidth)) }
      = domWidth + codWidth := by
    show zxpLayersCodArity (domWidth + codWidth)
        (zxnXorRowLayers (zxpZeroRow (domWidth + codWidth)))
      = domWidth + codWidth
    rw [zxnXorRowLayersCodArity, hZeroLen]
  have hLifted := zxwLiftConv domWidth [zxnInitLayer domWidth codWidth]
    (zxpCatLayers (zxnGeneratorBlockLayers generatorRows)
      [zxnKillLayer domWidth codWidth])
    hZeroComb hInitWF hInitCod (by rw [hWindowCod]; exact hAfterWF)
  -- reshape both sides to the literal normal-form layer lists
  show ZxwConv
    { sourceArity := domWidth
      layers := zxnInitLayer domWidth codWidth
        :: zxpCatLayers
          (zxpCatLayers (zxnXorRowLayers (zxpZeroRow (domWidth + codWidth)))
            (zxnGeneratorBlockLayers generatorRows))
          [zxnKillLayer domWidth codWidth] }
    (zxnNormalForm domWidth codWidth generatorRows)
  have hReassoc : zxpCatLayers
      (zxpCatLayers (zxnXorRowLayers (zxpZeroRow (domWidth + codWidth)))
        (zxnGeneratorBlockLayers generatorRows))
      [zxnKillLayer domWidth codWidth]
      = zxpCatLayers (zxnXorRowLayers (zxpZeroRow (domWidth + codWidth)))
          (zxpCatLayers (zxnGeneratorBlockLayers generatorRows)
            [zxnKillLayer domWidth codWidth]) :=
    zxnCatLayersAssoc (zxnXorRowLayers (zxpZeroRow (domWidth + codWidth)))
      (zxnGeneratorBlockLayers generatorRows) [zxnKillLayer domWidth codWidth]
  rw [hReassoc]
  exact hLifted

/-- Kernel fire: dropping the zero row over `F2^2` (one strand in, one out)
against the single generator `[true, true]` — both normal forms are literal,
the conversion is inhabited, and the span pin cross-checks it. -/
theorem zxfZeroRowDropFire :
    ZxwConv
      (zxnNormalForm 1 1 [[false, false], [true, true]])
      (zxnNormalForm 1 1 [[true, true]]) :=
  zxfNormalFormZeroRowDrop 1 1 [[true, true]]
    (ZxpAllWidth.cons rfl ZxpAllWidth.nil)

theorem zxfZeroRowDropFireSpanPin :
    zxpSpanEqB
      (zxpDiagramDenote (zxnNormalForm 1 1 [[false, false], [true, true]]))
      (zxpDiagramDenote (zxnNormalForm 1 1 [[true, true]])) = true := rfl

/-! ## Stage 3 — the conditional transport assembly

The two remaining elementary moves are named as Props on ADJACENT comb pairs:
the swap and the xor-absorption (the transvection).  Everything downstream —
duplication, absorption of any span member, extension/shrinking of generator
lists, and the full `zxwGeneratorTransportStatement` — is PROVED from those two
moves here, with the zero-row collapse (proven above) supplying the base case.
This is the same honest shape as the committed
`zxwCompletenessOfAbsorptionAndTransport`: the assembly is closed, the named
inputs are the exact residual. -/

/-- THE ADJACENT COMB SWAP (owner-false residual): two adjacent generator combs
commute.  Route documented in the file header: park + zip + the crossing ride
whose four windows are Yang-Baxter/slide/involution chains (three of the four
window derivations land below). -/
def zxfCombSwapStatement : Prop :=
  (strandWidth : Nat) -> (firstRow secondRow : List Bool) ->
    firstRow.length = strandWidth -> secondRow.length = strandWidth ->
    ZxwConv
      { sourceArity := strandWidth
        layers := zxpCatLayers (zxnXorRowLayers firstRow) (zxnXorRowLayers secondRow) }
      { sourceArity := strandWidth
        layers := zxpCatLayers (zxnXorRowLayers secondRow) (zxnXorRowLayers firstRow) }

/-- THE COMB TRANSVECTION (owner-false residual): xoring the second row into the
first comb of an adjacent pair preserves convertibility.  Route: the birth-side
CNOT insertion (proven below) plus the cnot ride whose four windows distribute
the bialgebra square over one tap position each. -/
def zxfCombXorAbsorbStatement : Prop :=
  (strandWidth : Nat) -> (firstRow secondRow : List Bool) ->
    firstRow.length = strandWidth -> secondRow.length = strandWidth ->
    ZxwConv
      { sourceArity := strandWidth
        layers := zxpCatLayers (zxnXorRowLayers (zxpRowXor firstRow secondRow))
          (zxnXorRowLayers secondRow) }
      { sourceArity := strandWidth
        layers := zxpCatLayers (zxnXorRowLayers firstRow) (zxnXorRowLayers secondRow) }

/-- Comb well-formedness at a stated width. -/
theorem zxfCombWFAt (strandWidth : Nat) (row : List Bool)
    (hLen : row.length = strandWidth) :
    ZxpLayersWF strandWidth (zxnXorRowLayers row) := by
  rw [<- hLen]
  exact zxnXorRowLayersWF row

/-- Comb output arity at a stated width (input arity arbitrary). -/
theorem zxfCombCodAt (strandWidth anyArity : Nat) (row : List Bool)
    (hLen : row.length = strandWidth) :
    zxpLayersCodArity anyArity (zxnXorRowLayers row) = strandWidth :=
  (zxnXorRowLayersCodArity row anyArity).trans hLen

/-- Lift a window conversion under a leading context (no trailing context). -/
theorem zxfLiftUnder (contextSource : Nat) (beforeLayers : List (List ZxpCell))
    {firstWindow secondWindow : ZxpDiagram} (hConv : ZxwConv firstWindow secondWindow)
    (hBeforeWF : ZxpLayersWF contextSource beforeLayers)
    (hBeforeCod : zxpLayersCodArity contextSource beforeLayers
      = firstWindow.sourceArity) :
    ZxwConv
      { sourceArity := contextSource
        layers := zxpCatLayers beforeLayers firstWindow.layers }
      { sourceArity := contextSource
        layers := zxpCatLayers beforeLayers secondWindow.layers } := by
  have hLifted := zxwLiftConv contextSource beforeLayers [] hConv hBeforeWF
    hBeforeCod (ZxpLayersWF.nil _)
  rw [zxpCatLayersNilRight, zxpCatLayersNilRight] at hLifted
  exact hLifted

/-- Lift a window conversion over a trailing context (no leading context). -/
theorem zxfLiftAfter (contextSource : Nat) (afterLayers : List (List ZxpCell))
    {firstWindow secondWindow : ZxpDiagram} (hConv : ZxwConv firstWindow secondWindow)
    (hSourceEq : firstWindow.sourceArity = contextSource)
    (hAfterWF : ZxpLayersWF (zxpDiagramCodArity firstWindow) afterLayers) :
    ZxwConv
      { sourceArity := contextSource
        layers := zxpCatLayers firstWindow.layers afterLayers }
      { sourceArity := contextSource
        layers := zxpCatLayers secondWindow.layers afterLayers } := by
  have hLifted := zxwLiftConv contextSource [] afterLayers hConv (ZxpLayersWF.nil _)
    (by
      show contextSource = firstWindow.sourceArity
      exact hSourceEq.symm)
    hAfterWF
  exact hLifted

/-- DUPLICATION from the transvection and the zero collapse:
`comb r ; comb r ~ comb r`. -/
theorem zxfCombDuplicate (hXorAbsorb : zxfCombXorAbsorbStatement)
    (strandWidth : Nat) (row : List Bool) (hLen : row.length = strandWidth) :
    ZxwConv
      { sourceArity := strandWidth
        layers := zxpCatLayers (zxnXorRowLayers row) (zxnXorRowLayers row) }
      { sourceArity := strandWidth, layers := zxnXorRowLayers row } := by
  have hZeroLen : (zxpZeroRow strandWidth).length = strandWidth :=
    zxpZeroRowLength strandWidth
  -- comb r ; comb r  ~  comb (0 xor r) ; comb r  =  comb 0 ; comb r
  have hStep := hXorAbsorb strandWidth (zxpZeroRow strandWidth) row hZeroLen hLen
  rw [zxpRowXorZeroLeft row strandWidth hLen] at hStep
  refine ZxwConv.trans hStep ?_
  -- comb 0 ; comb r ~ comb r  by the zero collapse under the trailing comb
  have hCollapse := zxfZeroCombCollapse strandWidth
  have hCodEq : zxpDiagramCodArity
      { sourceArity := strandWidth
        layers := zxnXorRowLayers (zxpZeroRow strandWidth) } = strandWidth := by
    show zxpLayersCodArity strandWidth (zxnXorRowLayers (zxpZeroRow strandWidth))
      = strandWidth
    exact zxfCombCodAt strandWidth strandWidth (zxpZeroRow strandWidth) hZeroLen
  have hLifted := zxfLiftAfter strandWidth (zxnXorRowLayers row) hCollapse rfl
    (by rw [hCodEq]; exact zxfCombWFAt strandWidth row hLen)
  exact hLifted

/-- DUPLICATION OUT OF THE FOLD: a listed generator row's comb can be pulled out
in front of the whole generator fold — by recursion on the list, the head case
by duplication, the tail case by the swap. -/
theorem zxfCombDupOut (hSwap : zxfCombSwapStatement)
    (hXorAbsorb : zxfCombXorAbsorbStatement) (strandWidth : Nat) {row : List Bool} :
    (generatorRows : List (List Bool)) ->
    ZxpAllWidth strandWidth generatorRows -> ZxpRowMem row generatorRows ->
    ZxwConv
      { sourceArity := strandWidth
        layers := zxnGeneratorBlockLayers generatorRows }
      { sourceArity := strandWidth
        layers := zxpCatLayers (zxnXorRowLayers row)
          (zxnGeneratorBlockLayers generatorRows) }
  | [], _hAll, hRowMem => nomatch hRowMem
  | headRow :: restRows, hAll, hRowMem => by
      have hHeadLen : headRow.length = strandWidth := by
        cases hAll with
        | cons hHead _hRest => exact hHead
      have hRestAll : ZxpAllWidth strandWidth restRows := by
        cases hAll with
        | cons _hHead hRest => exact hRest
      have hRestWF := zxnGeneratorBlockLayersWF restRows strandWidth hRestAll
      cases hRowMem with
      | head =>
          -- the head case: duplicate the head comb (`headRow` unified with `row`)
          have hDup := zxfCombDuplicate hXorAbsorb strandWidth row hHeadLen
          have hLifted := zxfLiftAfter strandWidth
            (zxnGeneratorBlockLayers restRows) (ZxwConv.symm hDup) rfl
            (by
              show ZxpLayersWF
                (zxpLayersCodArity strandWidth (zxnXorRowLayers row))
                (zxnGeneratorBlockLayers restRows)
              rw [zxfCombCodAt strandWidth strandWidth row hHeadLen]
              exact hRestWF)
          show ZxwConv
            { sourceArity := strandWidth
              layers := zxpCatLayers (zxnXorRowLayers row)
                (zxnGeneratorBlockLayers restRows) }
            { sourceArity := strandWidth
              layers := zxpCatLayers (zxnXorRowLayers row)
                (zxpCatLayers (zxnXorRowLayers row)
                  (zxnGeneratorBlockLayers restRows)) }
          rw [<- zxnCatLayersAssoc (zxnXorRowLayers row) (zxnXorRowLayers row)
            (zxnGeneratorBlockLayers restRows)]
          exact hLifted
      | tail hRestMem =>
          have hRowLen : row.length = strandWidth :=
            zxpAllWidthRow hRestAll hRestMem
          have hInner := zxfCombDupOut hSwap hXorAbsorb strandWidth restRows
            hRestAll hRestMem
          have hLifted := zxfLiftUnder strandWidth (zxnXorRowLayers headRow)
            (firstWindow :=
              { sourceArity := strandWidth
                layers := zxnGeneratorBlockLayers restRows })
            (secondWindow :=
              { sourceArity := strandWidth
                layers := zxpCatLayers (zxnXorRowLayers row)
                  (zxnGeneratorBlockLayers restRows) })
            hInner
            (zxfCombWFAt strandWidth headRow hHeadLen)
            (zxfCombCodAt strandWidth strandWidth headRow hHeadLen)
          show ZxwConv
            { sourceArity := strandWidth
              layers := zxpCatLayers (zxnXorRowLayers headRow)
                (zxnGeneratorBlockLayers restRows) }
            { sourceArity := strandWidth
              layers := zxpCatLayers (zxnXorRowLayers row)
                (zxpCatLayers (zxnXorRowLayers headRow)
                  (zxnGeneratorBlockLayers restRows)) }
          refine ZxwConv.trans hLifted ?_
          have hSwapInstance := hSwap strandWidth headRow row hHeadLen hRowLen
          have hSwapLifted := zxfLiftAfter strandWidth
            (zxnGeneratorBlockLayers restRows) hSwapInstance rfl
            (by
              show ZxpLayersWF
                (zxpLayersCodArity strandWidth
                  (zxpCatLayers (zxnXorRowLayers headRow) (zxnXorRowLayers row)))
                (zxnGeneratorBlockLayers restRows)
              rw [zxpLayersCodArityCat,
                zxfCombCodAt strandWidth strandWidth headRow hHeadLen,
                zxfCombCodAt strandWidth strandWidth row hRowLen]
              exact hRestWF)
          rw [zxnCatLayersAssoc (zxnXorRowLayers headRow) (zxnXorRowLayers row)
              (zxnGeneratorBlockLayers restRows),
            zxnCatLayersAssoc (zxnXorRowLayers row) (zxnXorRowLayers headRow)
              (zxnGeneratorBlockLayers restRows)] at hSwapLifted
          exact hSwapLifted

/-- ABSORPTION OF A SPAN MEMBER: `comb v ; blocks(rows) ~ blocks(rows)` whenever
`v` lies in the span of `rows` — by induction on the span derivation, the zero
constructor discharged by the PROVEN zero collapse, the pick constructor by
duplication-out plus the transvection. -/
theorem zxfCombAbsorb (hSwap : zxfCombSwapStatement)
    (hXorAbsorb : zxfCombXorAbsorbStatement)
    (strandWidth : Nat) (generatorRows : List (List Bool))
    (hAll : ZxpAllWidth strandWidth generatorRows) :
    (vector : List Bool) -> ZxpMemSpan strandWidth generatorRows vector ->
    ZxwConv
      { sourceArity := strandWidth
        layers := zxpCatLayers (zxnXorRowLayers vector)
          (zxnGeneratorBlockLayers generatorRows) }
      { sourceArity := strandWidth
        layers := zxnGeneratorBlockLayers generatorRows } := by
  have hBlocksWF : ZxpLayersWF strandWidth (zxnGeneratorBlockLayers generatorRows) :=
    zxnGeneratorBlockLayersWF generatorRows strandWidth hAll
  intro vector hMem
  induction hMem with
  | zero =>
      have hCollapse := zxfZeroCombCollapse strandWidth
      have hLifted := zxfLiftAfter strandWidth
        (zxnGeneratorBlockLayers generatorRows) hCollapse rfl
        (by
          show ZxpLayersWF
            (zxpLayersCodArity strandWidth
              (zxnXorRowLayers (zxpZeroRow strandWidth)))
            (zxnGeneratorBlockLayers generatorRows)
          rw [zxfCombCodAt strandWidth strandWidth (zxpZeroRow strandWidth)
            (zxpZeroRowLength strandWidth)]
          exact hBlocksWF)
      exact hLifted
  | pick row hRow hVec innerIH =>
      rename_i innerVector
      have hRowLen : row.length = strandWidth := zxpAllWidthRow hAll hRow
      have hVecLen : innerVector.length = strandWidth := zxpMemSpanWidth hAll hVec
      have hXorLen : (zxpRowXor row innerVector).length = strandWidth :=
        zxpRowXorLength row innerVector strandWidth hRowLen hVecLen
      have hDupOut := zxfCombDupOut hSwap hXorAbsorb strandWidth generatorRows
        hAll hRow
      -- comb(r (+) v) ; blocks ~ comb(r (+) v) ; comb r ; blocks
      have hStep1 := zxfLiftUnder strandWidth
        (zxnXorRowLayers (zxpRowXor row innerVector))
        (firstWindow :=
          { sourceArity := strandWidth
            layers := zxnGeneratorBlockLayers generatorRows })
        (secondWindow :=
          { sourceArity := strandWidth
            layers := zxpCatLayers (zxnXorRowLayers row)
              (zxnGeneratorBlockLayers generatorRows) })
        hDupOut
        (zxfCombWFAt strandWidth (zxpRowXor row innerVector) hXorLen)
        (zxfCombCodAt strandWidth strandWidth (zxpRowXor row innerVector) hXorLen)
      refine ZxwConv.trans hStep1 ?_
      -- comb(r (+) v) ; comb r ~ comb v ; comb r  (the transvection, commuted)
      have hXorComm : zxpRowXor row innerVector = zxpRowXor innerVector row :=
        zxpRowXorComm row innerVector
      have hTransvect := hXorAbsorb strandWidth innerVector row hVecLen hRowLen
      rw [<- hXorComm] at hTransvect
      have hTransvectLifted := zxfLiftAfter strandWidth
        (zxnGeneratorBlockLayers generatorRows) hTransvect rfl
        (by
          show ZxpLayersWF
            (zxpLayersCodArity strandWidth
              (zxpCatLayers (zxnXorRowLayers (zxpRowXor row innerVector))
                (zxnXorRowLayers row)))
            (zxnGeneratorBlockLayers generatorRows)
          rw [zxpLayersCodArityCat,
            zxfCombCodAt strandWidth strandWidth (zxpRowXor row innerVector) hXorLen,
            zxfCombCodAt strandWidth strandWidth row hRowLen]
          exact hBlocksWF)
      rw [zxnCatLayersAssoc (zxnXorRowLayers (zxpRowXor row innerVector))
          (zxnXorRowLayers row) (zxnGeneratorBlockLayers generatorRows),
        zxnCatLayersAssoc (zxnXorRowLayers innerVector) (zxnXorRowLayers row)
          (zxnGeneratorBlockLayers generatorRows)] at hTransvectLifted
      refine ZxwConv.trans hTransvectLifted ?_
      -- comb v ; comb r ; blocks ~ comb v ; blocks ~ blocks
      have hStep3 := zxfLiftUnder strandWidth (zxnXorRowLayers innerVector)
        (firstWindow :=
          { sourceArity := strandWidth
            layers := zxpCatLayers (zxnXorRowLayers row)
              (zxnGeneratorBlockLayers generatorRows) })
        (secondWindow :=
          { sourceArity := strandWidth
            layers := zxnGeneratorBlockLayers generatorRows })
        (ZxwConv.symm hDupOut)
        (zxfCombWFAt strandWidth innerVector hVecLen)
        (zxfCombCodAt strandWidth strandWidth innerVector hVecLen)
      exact ZxwConv.trans hStep3 innerIH

theorem zxfCatRowsNilRight : (rows : List (List Bool)) -> zxfCatRows rows [] = rows
  | [] => rfl
  | headRow :: restRows =>
      congrArg (fun tailRows => headRow :: tailRows) (zxfCatRowsNilRight restRows)

/-- A single comb commutes past the whole generator fold (from the swap). -/
theorem zxfCombPastBlocks (hSwap : zxfCombSwapStatement) (strandWidth : Nat)
    {row : List Bool} (hRowLen : row.length = strandWidth) :
    (generatorRows : List (List Bool)) ->
    ZxpAllWidth strandWidth generatorRows ->
    ZxwConv
      { sourceArity := strandWidth
        layers := zxpCatLayers (zxnXorRowLayers row)
          (zxnGeneratorBlockLayers generatorRows) }
      { sourceArity := strandWidth
        layers := zxpCatLayers (zxnGeneratorBlockLayers generatorRows)
          (zxnXorRowLayers row) }
  | [], _hAll => by
      show ZxwConv
        { sourceArity := strandWidth
          layers := zxpCatLayers (zxnXorRowLayers row) [] }
        { sourceArity := strandWidth, layers := zxnXorRowLayers row }
      rw [zxpCatLayersNilRight (zxnXorRowLayers row)]
      exact ZxwConv.refl _ (zxfCombWFAt strandWidth row hRowLen)
  | headRow :: restRows, hAll => by
      have hHeadLen : headRow.length = strandWidth := by
        cases hAll with
        | cons hHead _hRest => exact hHead
      have hRestAll : ZxpAllWidth strandWidth restRows := by
        cases hAll with
        | cons _hHead hRest => exact hRest
      have hRestWF := zxnGeneratorBlockLayersWF restRows strandWidth hRestAll
      show ZxwConv
        { sourceArity := strandWidth
          layers := zxpCatLayers (zxnXorRowLayers row)
            (zxpCatLayers (zxnXorRowLayers headRow)
              (zxnGeneratorBlockLayers restRows)) }
        { sourceArity := strandWidth
          layers := zxpCatLayers
            (zxpCatLayers (zxnXorRowLayers headRow)
              (zxnGeneratorBlockLayers restRows))
            (zxnXorRowLayers row) }
      rw [<- zxnCatLayersAssoc (zxnXorRowLayers row) (zxnXorRowLayers headRow)
        (zxnGeneratorBlockLayers restRows)]
      have hSwapLifted := zxfLiftAfter strandWidth
        (zxnGeneratorBlockLayers restRows)
        (hSwap strandWidth row headRow hRowLen hHeadLen) rfl
        (by
          show ZxpLayersWF
            (zxpLayersCodArity strandWidth
              (zxpCatLayers (zxnXorRowLayers row) (zxnXorRowLayers headRow)))
            (zxnGeneratorBlockLayers restRows)
          rw [zxpLayersCodArityCat,
            zxfCombCodAt strandWidth strandWidth row hRowLen,
            zxfCombCodAt strandWidth strandWidth headRow hHeadLen]
          exact hRestWF)
      refine ZxwConv.trans hSwapLifted ?_
      rw [zxnCatLayersAssoc (zxnXorRowLayers headRow) (zxnXorRowLayers row)
        (zxnGeneratorBlockLayers restRows)]
      have hInnerLifted := zxfLiftUnder strandWidth (zxnXorRowLayers headRow)
        (firstWindow :=
          { sourceArity := strandWidth
            layers := zxpCatLayers (zxnXorRowLayers row)
              (zxnGeneratorBlockLayers restRows) })
        (secondWindow :=
          { sourceArity := strandWidth
            layers := zxpCatLayers (zxnGeneratorBlockLayers restRows)
              (zxnXorRowLayers row) })
        (zxfCombPastBlocks hSwap strandWidth hRowLen restRows hRestAll)
        (zxfCombWFAt strandWidth headRow hHeadLen)
        (zxfCombCodAt strandWidth strandWidth headRow hHeadLen)
      refine ZxwConv.trans hInnerLifted ?_
      rw [<- zxnCatLayersAssoc (zxnXorRowLayers headRow)
        (zxnGeneratorBlockLayers restRows) (zxnXorRowLayers row)]
      exact ZxwConv.refl _ (by
        refine zxpLayersWFCat _ _ ?_ ?_
        · refine zxpLayersWFCat _ _ (zxfCombWFAt strandWidth headRow hHeadLen) ?_
          rw [zxfCombCodAt strandWidth strandWidth headRow hHeadLen]
          exact hRestWF
        · rw [zxpLayersCodArityCat,
            zxfCombCodAt strandWidth strandWidth headRow hHeadLen,
            zxnGeneratorBlockLayersCodArity restRows strandWidth hRestAll]
          exact zxfCombWFAt strandWidth row hRowLen)

/-- EXTENSION: prepending rows that already lie in the span preserves the fold
up to conversion. -/
theorem zxfBlocksExtend (hSwap : zxfCombSwapStatement)
    (hXorAbsorb : zxfCombXorAbsorbStatement) (strandWidth : Nat)
    (baseRows : List (List Bool)) (hBaseAll : ZxpAllWidth strandWidth baseRows) :
    (extraRows : List (List Bool)) ->
    ZxpAllWidth strandWidth extraRows ->
    ((row : List Bool) -> ZxpRowMem row extraRows ->
      ZxpMemSpan strandWidth baseRows row) ->
    ZxwConv
      { sourceArity := strandWidth
        layers := zxnGeneratorBlockLayers (zxfCatRows extraRows baseRows) }
      { sourceArity := strandWidth
        layers := zxnGeneratorBlockLayers baseRows }
  | [], _hExtraAll, _hCover =>
      ZxwConv.refl _ (zxnGeneratorBlockLayersWF baseRows strandWidth hBaseAll)
  | extraRow :: restRows, hExtraAll, hCover => by
      have hRestAll : ZxpAllWidth strandWidth restRows := by
        cases hExtraAll with
        | cons _hHead hRest => exact hRest
      have hCatAll : ZxpAllWidth strandWidth (zxfCatRows restRows baseRows) :=
        zxfCatRowsAllWidth restRows baseRows hRestAll hBaseAll
      have hMemHead : ZxpMemSpan strandWidth (zxfCatRows restRows baseRows) extraRow :=
        zxfMemSpanCatRight restRows baseRows
          (hCover extraRow (ZxpRowMem.head extraRow restRows))
      have hAbsorbed := zxfCombAbsorb hSwap hXorAbsorb strandWidth
        (zxfCatRows restRows baseRows) hCatAll extraRow hMemHead
      refine ZxwConv.trans hAbsorbed ?_
      exact zxfBlocksExtend hSwap hXorAbsorb strandWidth baseRows hBaseAll restRows
        hRestAll (fun row hRowMem => hCover row (ZxpRowMem.tail hRowMem))

/-- SHRINKING: appended rows that lie in the span of the front block delete. -/
theorem zxfBlocksShrink (hSwap : zxfCombSwapStatement)
    (hXorAbsorb : zxfCombXorAbsorbStatement) (strandWidth : Nat)
    (frontRows : List (List Bool)) (hFrontAll : ZxpAllWidth strandWidth frontRows) :
    (tailRows : List (List Bool)) ->
    ZxpAllWidth strandWidth tailRows ->
    ((row : List Bool) -> ZxpRowMem row tailRows ->
      ZxpMemSpan strandWidth frontRows row) ->
    ZxwConv
      { sourceArity := strandWidth
        layers := zxnGeneratorBlockLayers (zxfCatRows frontRows tailRows) }
      { sourceArity := strandWidth
        layers := zxnGeneratorBlockLayers frontRows }
  | [], _hTailAll, _hCover => by
      rw [zxfCatRowsNilRight frontRows]
      exact ZxwConv.refl _ (zxnGeneratorBlockLayersWF frontRows strandWidth hFrontAll)
  | tailRow :: restRows, hTailAll, hCover => by
      have hTailLen : tailRow.length = strandWidth := by
        cases hTailAll with
        | cons hHead _hRest => exact hHead
      have hRestAll : ZxpAllWidth strandWidth restRows := by
        cases hTailAll with
        | cons _hHead hRest => exact hRest
      have hFrontWF := zxnGeneratorBlockLayersWF frontRows strandWidth hFrontAll
      have hRestWF := zxnGeneratorBlockLayersWF restRows strandWidth hRestAll
      rw [zxfGeneratorBlockLayersCat frontRows (tailRow :: restRows)]
      show ZxwConv
        { sourceArity := strandWidth
          layers := zxpCatLayers (zxnGeneratorBlockLayers frontRows)
            (zxpCatLayers (zxnXorRowLayers tailRow)
              (zxnGeneratorBlockLayers restRows)) }
        { sourceArity := strandWidth
          layers := zxnGeneratorBlockLayers frontRows }
      rw [<- zxnCatLayersAssoc (zxnGeneratorBlockLayers frontRows)
        (zxnXorRowLayers tailRow) (zxnGeneratorBlockLayers restRows)]
      have hPast := ZxwConv.symm
        (zxfCombPastBlocks hSwap strandWidth hTailLen frontRows hFrontAll)
      have hPastLifted := zxfLiftAfter strandWidth
        (zxnGeneratorBlockLayers restRows) hPast rfl
        (by
          show ZxpLayersWF
            (zxpLayersCodArity strandWidth
              (zxpCatLayers (zxnGeneratorBlockLayers frontRows)
                (zxnXorRowLayers tailRow)))
            (zxnGeneratorBlockLayers restRows)
          rw [zxpLayersCodArityCat,
            zxnGeneratorBlockLayersCodArity frontRows strandWidth hFrontAll,
            zxfCombCodAt strandWidth strandWidth tailRow hTailLen]
          exact hRestWF)
      refine ZxwConv.trans hPastLifted ?_
      rw [zxnCatLayersAssoc (zxnXorRowLayers tailRow)
        (zxnGeneratorBlockLayers frontRows) (zxnGeneratorBlockLayers restRows),
        <- zxfGeneratorBlockLayersCat frontRows restRows]
      have hCatAll : ZxpAllWidth strandWidth (zxfCatRows frontRows restRows) :=
        zxfCatRowsAllWidth frontRows restRows hFrontAll hRestAll
      have hMemTail : ZxpMemSpan strandWidth (zxfCatRows frontRows restRows) tailRow :=
        zxfMemSpanCatLeft frontRows restRows
          (hCover tailRow (ZxpRowMem.head tailRow restRows))
      have hAbsorbed := zxfCombAbsorb hSwap hXorAbsorb strandWidth
        (zxfCatRows frontRows restRows) hCatAll tailRow hMemTail
      refine ZxwConv.trans hAbsorbed ?_
      exact zxfBlocksShrink hSwap hXorAbsorb strandWidth frontRows hFrontAll restRows
        hRestAll (fun row hRowMem => hCover row (ZxpRowMem.tail hRowMem))

/-- THE CONDITIONAL TRANSPORT ASSEMBLY: the two adjacent-comb moves IMPLY the
full generator-list transport statement.  Chain: soundness of the span decision
turns `zxpSpanEqB` into mutual span membership; the first fold extends by the
second list (extension), the concatenated fold shrinks to the second list
(shrinking, through comb-past-fold commutation); the blocks-level conversion
lifts between the shared init and kill layers.  The zero-row collapse used in
the base cases is PROVEN above — the exact residual is the two named moves. -/
theorem zxfTransportOfCombMoves (hSwap : zxfCombSwapStatement)
    (hXorAbsorb : zxfCombXorAbsorbStatement) : zxwGeneratorTransportStatement := by
  intro domWidth codWidth firstRows secondRows hFirstAll hSecondAll hSpanEq
  have hSpanIff := zxpSpanEqBSound hFirstAll hSecondAll hSpanEq
  have hExtend := zxfBlocksExtend hSwap hXorAbsorb (domWidth + codWidth)
    firstRows hFirstAll secondRows hSecondAll
    (fun row hRowMem => (hSpanIff row).mpr (zxpMemSpanElem hSecondAll hRowMem))
  have hShrink := zxfBlocksShrink hSwap hXorAbsorb (domWidth + codWidth)
    secondRows hSecondAll firstRows hFirstAll
    (fun row hRowMem => (hSpanIff row).mp (zxpMemSpanElem hFirstAll hRowMem))
  have hBlocksConv : ZxwConv
      { sourceArity := domWidth + codWidth
        layers := zxnGeneratorBlockLayers firstRows }
      { sourceArity := domWidth + codWidth
        layers := zxnGeneratorBlockLayers secondRows } := by
    refine ZxwConv.trans (ZxwConv.symm hExtend) ?_
    -- blocks(second (+) first) is the SAME layer list as the shrink source
    exact hShrink
  have hInitWF : ZxpLayersWF domWidth [zxnInitLayer domWidth codWidth] :=
    ZxpLayersWF.cons (zxnInitLayerDomArity domWidth codWidth) (ZxpLayersWF.nil _)
  have hInitCod : zxpLayersCodArity domWidth [zxnInitLayer domWidth codWidth]
      = domWidth + codWidth := by
    show zxpLayerCodArity (zxnInitLayer domWidth codWidth) = domWidth + codWidth
    exact zxnInitLayerCodArity domWidth codWidth
  have hKillWF : ZxpLayersWF (domWidth + codWidth) [zxnKillLayer domWidth codWidth] :=
    ZxpLayersWF.cons (zxnKillLayerDomArity domWidth codWidth) (ZxpLayersWF.nil _)
  have hFirstBlocksCod : zxpDiagramCodArity
      { sourceArity := domWidth + codWidth
        layers := zxnGeneratorBlockLayers firstRows } = domWidth + codWidth := by
    show zxpLayersCodArity (domWidth + codWidth) (zxnGeneratorBlockLayers firstRows)
      = domWidth + codWidth
    exact zxnGeneratorBlockLayersCodArity firstRows (domWidth + codWidth) hFirstAll
  have hLifted := zxwLiftConv domWidth [zxnInitLayer domWidth codWidth]
    [zxnKillLayer domWidth codWidth] hBlocksConv hInitWF hInitCod
    (by rw [hFirstBlocksCod]; exact hKillWF)
  exact hLifted

/-! ## Stage 4 — the birth-side gadget bricks and the landed ride windows

The two comb moves ride on a freshly created carrier pair.  The birth-side
conjugation lemmas land here WHOLE: inserting a crossing or a CNOT gadget
(fork-then-merge) right after two carrier creations is convertible to nothing —
these are the exact entry points of the swap ride and the transvection ride.
Three of the four crossing-ride windows land as well (the fourth is walled
below with its exact configuration). -/

/-- CROSSING INSERT AT BIRTH: two creations followed by a crossing convert to
the two creations — slide the right create over, exchange, split. -/
theorem zxfCreatesCrossInsert :
    ZxwConv
      { sourceArity := 0
        layers := [[ZxpCell.zSpider 0 1],
          [ZxpCell.wire, ZxpCell.zSpider 0 1], [ZxpCell.crossing]] }
      { sourceArity := 0
        layers := [[ZxpCell.zSpider 0 1], [ZxpCell.wire, ZxpCell.zSpider 0 1]] } := by
  -- step 1: [w, create] ; [crossing] ~ [create, w]  (slideLeft at the create)
  have hSlide := zxwSlideLeftConv (ZxpCell.zSpider 0 1)
  have hSlideLifted := zxwLiftConv 0 [[ZxpCell.zSpider 0 1]] [] hSlide
    (ZxpLayersWF.cons rfl (ZxpLayersWF.nil _)) rfl (ZxpLayersWF.nil _)
  rw [zxpCatLayersNilRight, zxpCatLayersNilRight] at hSlideLifted
  have hStep1 : ZxwConv
      { sourceArity := 0
        layers := [[ZxpCell.zSpider 0 1],
          [ZxpCell.wire, ZxpCell.zSpider 0 1], [ZxpCell.crossing]] }
      { sourceArity := 0
        layers := [[ZxpCell.zSpider 0 1], [ZxpCell.zSpider 0 1, ZxpCell.wire]] } :=
    hSlideLifted
  refine ZxwConv.trans hStep1 ?_
  -- step 2: right-first exchange backwards: [create],[create, w] ~ [create, create]
  have hExchange := zxwMoveConv (ZxwWindowMove.base
    (ZxeWindowMove.rightFirstExchange [ZxpCell.zSpider 0 1] [ZxpCell.zSpider 0 1]))
  have hStep2 : ZxwConv
      { sourceArity := 0
        layers := [[ZxpCell.zSpider 0 1], [ZxpCell.zSpider 0 1, ZxpCell.wire]] }
      { sourceArity := 0
        layers := [[ZxpCell.zSpider 0 1, ZxpCell.zSpider 0 1]] } := hExchange
  refine ZxwConv.trans hStep2 ?_
  -- step 3: split left-first: [create, create] ~ [create],[w, create]
  have hSplit := zxwMoveConv (ZxwWindowMove.base (ZxeWindowMove.base
    (ZxrWindowMove.seed
      (ZxpWindowMove.splitLayer [ZxpCell.zSpider 0 1] [ZxpCell.zSpider 0 1]))))
  exact hSplit

/-- THE FF CROSSING WINDOW: the ride step over a double skip position is exactly
Yang-Baxter (the `slideLeft crossing` instance, symmetrized). -/
theorem zxfCrossWindowFF :
    ZxwConv
      { sourceArity := 3
        layers := [[ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.crossing], [ZxpCell.crossing, ZxpCell.wire]] }
      { sourceArity := 3
        layers := [[ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.crossing, ZxpCell.wire], [ZxpCell.wire, ZxpCell.crossing]] } :=
  ZxwConv.symm (zxwSlideLeftConv ZxpCell.crossing)

/-- CNOT INSERT AT BIRTH: two creations followed by fork-of-the-second and
merge-into-the-first convert to the two creations.  Chain: recolour the
create/fork cup (`cupCoincide`), X-Frobenius, the mirrored X-unit (via
`xMonoidComm` and the `slideLeft` of the X-unit), strip, then the dual
unit-copy bialgebra row and one split. -/
theorem zxfCreatesCnotInsert :
    ZxwConv
      { sourceArity := 0
        layers := [[ZxpCell.zSpider 0 1], [ZxpCell.wire, ZxpCell.zSpider 0 1],
          [ZxpCell.wire, ZxpCell.zSpider 1 2], [ZxpCell.xSpider 2 1, ZxpCell.wire]] }
      { sourceArity := 0
        layers := [[ZxpCell.zSpider 0 1], [ZxpCell.wire, ZxpCell.zSpider 0 1]] } := by
  -- step 1: recolour the inner cup: [z01];[z12] ~ [x01];[x12], whiskered (1,0),
  -- under the first create, over the trailing merge layer
  have hCup : ZxwConv (zxpRowLhs ZxpRowTag.cupCoincide)
      (zxpRowRhs ZxpRowTag.cupCoincide) :=
    zxwOfZxpConv (zxpRowConv ZxpRowTag.cupCoincide)
  have hCupLift := zxwConvLift 0 1 0 [[ZxpCell.zSpider 0 1]]
    [[ZxpCell.xSpider 2 1, ZxpCell.wire]] (ZxwConv.symm hCup)
    (ZxpLayersWF.cons rfl (ZxpLayersWF.nil _)) rfl
    (zxpLayersWFOfB _ _ rfl)
  have hStep1 : ZxwConv
      { sourceArity := 0
        layers := [[ZxpCell.zSpider 0 1], [ZxpCell.wire, ZxpCell.zSpider 0 1],
          [ZxpCell.wire, ZxpCell.zSpider 1 2], [ZxpCell.xSpider 2 1, ZxpCell.wire]] }
      { sourceArity := 0
        layers := [[ZxpCell.zSpider 0 1], [ZxpCell.wire, ZxpCell.xSpider 0 1],
          [ZxpCell.wire, ZxpCell.xSpider 1 2], [ZxpCell.xSpider 2 1, ZxpCell.wire]] } :=
    hCupLift
  refine ZxwConv.trans hStep1 ?_
  -- step 2: X-Frobenius (right form) on the last two layers
  have hFrob : ZxwConv (zxpRowLhs ZxpRowTag.frobeniusXRight)
      (zxpRowRhs ZxpRowTag.frobeniusXRight) :=
    zxwOfZxpConv (zxpRowConv ZxpRowTag.frobeniusXRight)
  have hFrobLift := zxwLiftConv 0
    [[ZxpCell.zSpider 0 1], [ZxpCell.wire, ZxpCell.xSpider 0 1]] [] hFrob
    (zxpLayersWFOfB _ _ rfl) rfl (ZxpLayersWF.nil _)
  rw [zxpCatLayersNilRight, zxpCatLayersNilRight] at hFrobLift
  have hStep2 : ZxwConv
      { sourceArity := 0
        layers := [[ZxpCell.zSpider 0 1], [ZxpCell.wire, ZxpCell.xSpider 0 1],
          [ZxpCell.wire, ZxpCell.xSpider 1 2], [ZxpCell.xSpider 2 1, ZxpCell.wire]] }
      { sourceArity := 0
        layers := [[ZxpCell.zSpider 0 1], [ZxpCell.wire, ZxpCell.xSpider 0 1],
          [ZxpCell.xSpider 2 1], [ZxpCell.xSpider 1 2]] } := hFrobLift
  refine ZxwConv.trans hStep2 ?_
  -- step 3a: insert a crossing before the merge (xMonoidComm backwards)
  have hComm : ZxwConv (zxpRowLhs ZxpRowTag.xMonoidComm)
      (zxpRowRhs ZxpRowTag.xMonoidComm) :=
    zxwOfZxpConv (zxpRowConv ZxpRowTag.xMonoidComm)
  have hCommLift := zxwLiftConv 0
    [[ZxpCell.zSpider 0 1], [ZxpCell.wire, ZxpCell.xSpider 0 1]]
    [[ZxpCell.xSpider 1 2]] (ZxwConv.symm hComm)
    (zxpLayersWFOfB _ _ rfl) rfl (zxpLayersWFOfB _ _ rfl)
  have hStep3 : ZxwConv
      { sourceArity := 0
        layers := [[ZxpCell.zSpider 0 1], [ZxpCell.wire, ZxpCell.xSpider 0 1],
          [ZxpCell.xSpider 2 1], [ZxpCell.xSpider 1 2]] }
      { sourceArity := 0
        layers := [[ZxpCell.zSpider 0 1], [ZxpCell.wire, ZxpCell.xSpider 0 1],
          [ZxpCell.crossing], [ZxpCell.xSpider 2 1], [ZxpCell.xSpider 1 2]] } :=
    hCommLift
  refine ZxwConv.trans hStep3 ?_
  -- step 3b: slide the X-unit to the left through the crossing
  have hSlide := zxwSlideLeftConv (ZxpCell.xSpider 0 1)
  have hSlideLift := zxwLiftConv 0 [[ZxpCell.zSpider 0 1]]
    [[ZxpCell.xSpider 2 1], [ZxpCell.xSpider 1 2]] hSlide
    (ZxpLayersWF.cons rfl (ZxpLayersWF.nil _)) rfl
    (zxpLayersWFOfB _ _ rfl)
  have hStep4 : ZxwConv
      { sourceArity := 0
        layers := [[ZxpCell.zSpider 0 1], [ZxpCell.wire, ZxpCell.xSpider 0 1],
          [ZxpCell.crossing], [ZxpCell.xSpider 2 1], [ZxpCell.xSpider 1 2]] }
      { sourceArity := 0
        layers := [[ZxpCell.zSpider 0 1], [ZxpCell.xSpider 0 1, ZxpCell.wire],
          [ZxpCell.xSpider 2 1], [ZxpCell.xSpider 1 2]] } := hSlideLift
  refine ZxwConv.trans hStep4 ?_
  -- step 3c: the X-unit row proper
  have hUnit : ZxwConv (zxpRowLhs ZxpRowTag.xMonoidUnit)
      (zxpRowRhs ZxpRowTag.xMonoidUnit) :=
    zxwOfZxpConv (zxpRowConv ZxpRowTag.xMonoidUnit)
  have hUnitLift := zxwLiftConv 0 [[ZxpCell.zSpider 0 1]]
    [[ZxpCell.xSpider 1 2]] hUnit
    (ZxpLayersWF.cons rfl (ZxpLayersWF.nil _)) rfl
    (zxpLayersWFOfB _ _ rfl)
  have hStep5 : ZxwConv
      { sourceArity := 0
        layers := [[ZxpCell.zSpider 0 1], [ZxpCell.xSpider 0 1, ZxpCell.wire],
          [ZxpCell.xSpider 2 1], [ZxpCell.xSpider 1 2]] }
      { sourceArity := 0
        layers := [[ZxpCell.zSpider 0 1], [ZxpCell.wire], [ZxpCell.xSpider 1 2]] } :=
    hUnitLift
  refine ZxwConv.trans hStep5 ?_
  -- step 3d: strip the bare wire layer
  have hStrip := zxwOfZxeConv (zxeStripLeadingWireLayer [ZxpCell.xSpider 1 2])
  have hStripLift := zxwLiftConv 0 [[ZxpCell.zSpider 0 1]] [] hStrip
    (ZxpLayersWF.cons rfl (ZxpLayersWF.nil _)) rfl (ZxpLayersWF.nil _)
  rw [zxpCatLayersNilRight, zxpCatLayersNilRight] at hStripLift
  have hStep6 : ZxwConv
      { sourceArity := 0
        layers := [[ZxpCell.zSpider 0 1], [ZxpCell.wire], [ZxpCell.xSpider 1 2]] }
      { sourceArity := 0
        layers := [[ZxpCell.zSpider 0 1], [ZxpCell.xSpider 1 2]] } := hStripLift
  refine ZxwConv.trans hStep6 ?_
  -- step 4: the dual unit-copy bialgebra row: [z01];[x12] ~ [z01, z01]
  have hDual : ZxwConv (zxpRowLhs ZxpRowTag.bialgUnitCopyDual)
      (zxpRowRhs ZxpRowTag.bialgUnitCopyDual) :=
    zxwOfZxpConv (zxpRowConv ZxpRowTag.bialgUnitCopyDual)
  refine ZxwConv.trans hDual ?_
  -- step 5: split the double create left-first
  exact zxwMoveConv (ZxwWindowMove.base (ZxeWindowMove.base
    (ZxrWindowMove.seed
      (ZxpWindowMove.splitLayer [ZxpCell.zSpider 0 1] [ZxpCell.zSpider 0 1]))))

/-- THE FT CROSSING WINDOW: the ride step over a skip/tap position — the
crossing passes a passive-then-tapped strand pair.  Exchange, `slideLeft` at
the fork, `slideLeft` at the merge, one more exchange, Yang-Baxter. -/
theorem zxfCrossWindowFT :
    ZxwConv
      { sourceArity := 3
        layers := [[ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire],
          [ZxpCell.crossing, ZxpCell.wire]] }
      { sourceArity := 3
        layers := [[ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
          [ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.crossing]] } := by
  -- step 1: merge and re-split layers 2-3 the other way round
  have hMergeLift := zxwLiftConv 3 [[ZxpCell.crossing, ZxpCell.wire]]
    [[ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire],
      [ZxpCell.crossing, ZxpCell.wire]]
    (ZxwConv.trans
      (zxwMoveConv (ZxwWindowMove.base
        (ZxeWindowMove.rightFirstExchange [ZxpCell.zSpider 1 2] [ZxpCell.crossing])))
      (zxwMoveConv (ZxwWindowMove.base (ZxeWindowMove.base
        (ZxrWindowMove.seed
          (ZxpWindowMove.splitLayer [ZxpCell.zSpider 1 2] [ZxpCell.crossing]))))))
    (zxpLayersWFOfB _ _ rfl) rfl (zxpLayersWFOfB _ _ rfl)
  have hStep1 : ZxwConv
      { sourceArity := 3
        layers := [[ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire],
          [ZxpCell.crossing, ZxpCell.wire]] }
      { sourceArity := 3
        layers := [[ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire],
          [ZxpCell.crossing, ZxpCell.wire]] } := hMergeLift
  refine ZxwConv.trans hStep1 ?_
  -- step 2: slide the fork left through the crossing (whisker (0,1))
  have hForkSlide := ZxwConv.symm (zxwSlideLeftConv (ZxpCell.zSpider 1 2))
  have hForkLift := zxwConvLift 3 0 1 []
    [[ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing],
      [ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire],
      [ZxpCell.crossing, ZxpCell.wire]]
    hForkSlide (ZxpLayersWF.nil _) rfl (zxpLayersWFOfB _ _ rfl)
  have hStep2 : ZxwConv
      { sourceArity := 3
        layers := [[ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire],
          [ZxpCell.crossing, ZxpCell.wire]] }
      { sourceArity := 3
        layers := [[ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
          [ZxpCell.crossing, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire],
          [ZxpCell.crossing, ZxpCell.wire]] } := hForkLift
  refine ZxwConv.trans hStep2 ?_
  -- step 3: slide the merge left through its crossing pair (whisker (1,0))
  have hMergeSlide := zxwSlideLeftConv (ZxpCell.xSpider 2 1)
  have hMergeSlideLift := zxwConvLift 3 1 0
    [[ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
      [ZxpCell.crossing, ZxpCell.wire, ZxpCell.wire]]
    [[ZxpCell.crossing, ZxpCell.wire]]
    (ZxwConv.symm hMergeSlide) (zxpLayersWFOfB _ _ rfl) rfl
    (zxpLayersWFOfB _ _ rfl)
  have hStep3 : ZxwConv
      { sourceArity := 3
        layers := [[ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
          [ZxpCell.crossing, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire],
          [ZxpCell.crossing, ZxpCell.wire]] }
      { sourceArity := 3
        layers := [[ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
          [ZxpCell.crossing, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
          [ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.crossing, ZxpCell.wire]] } := hMergeSlideLift
  refine ZxwConv.trans hStep3 ?_
  -- step 4: exchange the leading crossing past the merge
  have hExchLift := zxwLiftConv 3
    [[ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire]]
    [[ZxpCell.wire, ZxpCell.crossing], [ZxpCell.crossing, ZxpCell.wire]]
    (ZxwConv.trans
      (ZxwConv.symm (zxwMoveConv (ZxwWindowMove.base (ZxeWindowMove.base
        (ZxrWindowMove.seed
          (ZxpWindowMove.splitLayer [ZxpCell.crossing] [ZxpCell.xSpider 2 1]))))))
      (ZxwConv.symm (zxwMoveConv (ZxwWindowMove.base
        (ZxeWindowMove.rightFirstExchange [ZxpCell.crossing] [ZxpCell.xSpider 2 1])))))
    (zxpLayersWFOfB _ _ rfl) rfl (zxpLayersWFOfB _ _ rfl)
  have hStep4 : ZxwConv
      { sourceArity := 3
        layers := [[ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
          [ZxpCell.crossing, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
          [ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.crossing, ZxpCell.wire]] }
      { sourceArity := 3
        layers := [[ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
          [ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.crossing, ZxpCell.wire]] } := hExchLift
  refine ZxwConv.trans hStep4 ?_
  -- step 5: Yang-Baxter on the trailing crossing triple
  have hYangBaxter := zxfCrossWindowFF
  have hYangBaxterLift := zxwLiftConv 3
    [[ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
      [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1]] [] hYangBaxter
    (zxpLayersWFOfB _ _ rfl) rfl (ZxpLayersWF.nil _)
  rw [zxpCatLayersNilRight, zxpCatLayersNilRight] at hYangBaxterLift
  exact hYangBaxterLift

/-- THE TF CROSSING WINDOW: the ride step over a tap/skip position.  Slide the
fork right through the crossing, exchange, Yang-Baxter, slide the merge, the
involution, strip, and one final exchange. -/
theorem zxfCrossWindowTF :
    ZxwConv
      { sourceArity := 3
        layers := [[ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
          [ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.crossing, ZxpCell.wire]] }
      { sourceArity := 3
        layers := [[ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire],
          [ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.crossing]] } := by
  -- step 1: slide the fork right through the leading crossing (whisker (0,1))
  have hForkSlide := ZxwConv.symm (zxwSlideRightConv (ZxpCell.zSpider 1 2))
  have hForkLift := zxwConvLift 3 0 1 []
    [[ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
      [ZxpCell.wire, ZxpCell.crossing], [ZxpCell.crossing, ZxpCell.wire]]
    hForkSlide (ZxpLayersWF.nil _) rfl (zxpLayersWFOfB _ _ rfl)
  have hStep1 : ZxwConv
      { sourceArity := 3
        layers := [[ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
          [ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.crossing, ZxpCell.wire]] }
      { sourceArity := 3
        layers := [[ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.crossing, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
          [ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.crossing, ZxpCell.wire]] } := hForkLift
  refine ZxwConv.trans hStep1 ?_
  -- step 2: exchange the crossing past the far merge
  have hExchLift := zxwLiftConv 3
    [[ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire],
      [ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire]]
    [[ZxpCell.wire, ZxpCell.crossing], [ZxpCell.crossing, ZxpCell.wire]]
    (ZxwConv.trans
      (ZxwConv.symm (zxwMoveConv (ZxwWindowMove.base (ZxeWindowMove.base
        (ZxrWindowMove.seed
          (ZxpWindowMove.splitLayer [ZxpCell.crossing] [ZxpCell.xSpider 2 1]))))))
      (ZxwConv.symm (zxwMoveConv (ZxwWindowMove.base
        (ZxeWindowMove.rightFirstExchange [ZxpCell.crossing] [ZxpCell.xSpider 2 1])))))
    (zxpLayersWFOfB _ _ rfl) rfl (zxpLayersWFOfB _ _ rfl)
  have hStep2 : ZxwConv
      { sourceArity := 3
        layers := [[ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.crossing, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
          [ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.crossing, ZxpCell.wire]] }
      { sourceArity := 3
        layers := [[ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
          [ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.crossing, ZxpCell.wire]] } := hExchLift
  refine ZxwConv.trans hStep2 ?_
  -- step 3: Yang-Baxter on the trailing crossing triple
  have hYangBaxterLift := zxwLiftConv 3
    [[ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire],
      [ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire],
      [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1]] [] zxfCrossWindowFF
    (zxpLayersWFOfB _ _ rfl) rfl (ZxpLayersWF.nil _)
  rw [zxpCatLayersNilRight, zxpCatLayersNilRight] at hYangBaxterLift
  have hStep3 : ZxwConv
      { sourceArity := 3
        layers := [[ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
          [ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.crossing, ZxpCell.wire]] }
      { sourceArity := 3
        layers := [[ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
          [ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.crossing]] } := hYangBaxterLift
  refine ZxwConv.trans hStep3 ?_
  -- step 4: slide the merge left into the crossing pair (whisker (1,0))
  have hMergeLift := zxwConvLift 3 1 0
    [[ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire],
      [ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire]]
    [[ZxpCell.crossing, ZxpCell.wire], [ZxpCell.wire, ZxpCell.crossing]]
    (zxwSlideLeftConv (ZxpCell.xSpider 2 1)) (zxpLayersWFOfB _ _ rfl) rfl
    (zxpLayersWFOfB _ _ rfl)
  have hStep4 : ZxwConv
      { sourceArity := 3
        layers := [[ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
          [ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.crossing]] }
      { sourceArity := 3
        layers := [[ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire],
          [ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.crossing]] } := hMergeLift
  refine ZxwConv.trans hStep4 ?_
  -- step 5: the sigma involution kills the doubled crossing (whisker (1,1))
  have hInvolutionLift := zxwConvLift 3 1 1
    [[ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire]]
    [[ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing],
      [ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire],
      [ZxpCell.crossing, ZxpCell.wire], [ZxpCell.wire, ZxpCell.crossing]]
    (zxwMoveConv ZxwWindowMove.sigmaInvolution)
    (zxpLayersWFOfB _ _ rfl) rfl (zxpLayersWFOfB _ _ rfl)
  have hStep5 : ZxwConv
      { sourceArity := 3
        layers := [[ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire],
          [ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.crossing]] }
      { sourceArity := 3
        layers := [[ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire],
          [ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.crossing]] } := hInvolutionLift
  refine ZxwConv.trans hStep5 ?_
  -- step 6: strip the full wire layer
  have hStripLift := zxwLiftConv 3
    [[ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire]]
    [[ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire],
      [ZxpCell.crossing, ZxpCell.wire], [ZxpCell.wire, ZxpCell.crossing]]
    (zxwOfZxeConv (zxeStripLeadingWireLayer
      [ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing]))
    (zxpLayersWFOfB _ _ rfl) rfl (zxpLayersWFOfB _ _ rfl)
  have hStep6 : ZxwConv
      { sourceArity := 3
        layers := [[ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire],
          [ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.crossing]] }
      { sourceArity := 3
        layers := [[ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire],
          [ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.crossing]] } := hStripLift
  refine ZxwConv.trans hStep6 ?_
  -- step 7: pull the trailing crossing of the fork block to the front
  have hFinalLift := zxwLiftConv 3 []
    [[ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire],
      [ZxpCell.crossing, ZxpCell.wire], [ZxpCell.wire, ZxpCell.crossing]]
    (ZxwConv.trans
      (ZxwConv.symm (zxwMoveConv (ZxwWindowMove.base (ZxeWindowMove.base
        (ZxrWindowMove.seed
          (ZxpWindowMove.splitLayer [ZxpCell.zSpider 1 2] [ZxpCell.crossing]))))))
      (ZxwConv.symm (zxwMoveConv (ZxwWindowMove.base
        (ZxeWindowMove.rightFirstExchange [ZxpCell.zSpider 1 2] [ZxpCell.crossing])))))
    (ZxpLayersWF.nil _) rfl (zxpLayersWFOfB _ _ rfl)
  exact hFinalLift

/-- Inner reassociation for the TT window: a crossing feeding a two-step merge
chain dissolves by X-associativity and X-commutativity. -/
theorem zxfCrossIntoMergeChain :
    ZxwConv
      { sourceArity := 3
        layers := [[ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.xSpider 2 1], [ZxpCell.xSpider 2 1]] }
      { sourceArity := 3
        layers := [[ZxpCell.wire, ZxpCell.xSpider 2 1], [ZxpCell.xSpider 2 1]] } := by
  -- reassociate the merge chain to expose the crossing (assoc backwards)
  have hAssoc : ZxwConv (zxpRowLhs ZxpRowTag.xMonoidAssoc)
      (zxpRowRhs ZxpRowTag.xMonoidAssoc) :=
    zxwOfZxpConv (zxpRowConv ZxpRowTag.xMonoidAssoc)
  have hAssocLift := zxwLiftConv 3 [[ZxpCell.crossing, ZxpCell.wire]] []
    (ZxwConv.symm hAssoc) (zxpLayersWFOfB _ _ rfl) rfl (ZxpLayersWF.nil _)
  rw [zxpCatLayersNilRight, zxpCatLayersNilRight] at hAssocLift
  have hStep1 : ZxwConv
      { sourceArity := 3
        layers := [[ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.xSpider 2 1], [ZxpCell.xSpider 2 1]] }
      { sourceArity := 3
        layers := [[ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.xSpider 2 1, ZxpCell.wire], [ZxpCell.xSpider 2 1]] } := hAssocLift
  refine ZxwConv.trans hStep1 ?_
  -- the crossing dies into the left merge (X-commutativity, whisker (0,1))
  have hComm : ZxwConv (zxpRowLhs ZxpRowTag.xMonoidComm)
      (zxpRowRhs ZxpRowTag.xMonoidComm) :=
    zxwOfZxpConv (zxpRowConv ZxpRowTag.xMonoidComm)
  have hCommLift := zxwConvLift 3 0 1 [] [[ZxpCell.xSpider 2 1]] hComm
    (ZxpLayersWF.nil _) rfl (zxpLayersWFOfB _ _ rfl)
  have hStep2 : ZxwConv
      { sourceArity := 3
        layers := [[ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.xSpider 2 1, ZxpCell.wire], [ZxpCell.xSpider 2 1]] }
      { sourceArity := 3
        layers := [[ZxpCell.xSpider 2 1, ZxpCell.wire], [ZxpCell.xSpider 2 1]] } :=
    hCommLift
  refine ZxwConv.trans hStep2 ?_
  exact zxwOfZxpConv (zxpRowConv ZxpRowTag.xMonoidAssoc)

/-- THE TT CROSSING WINDOW (owner-false residual): the ride step over a double
tap position — the crossing passes two fork/merge gadgets on the same strand.
The full move chain is derived on paper (fork slides through the leading
crossing, seven disjoint-block exchanges, the merge slide, Yang-Baxter twice,
the merge-chain reassociation `zxfCrossIntoMergeChain`, the sigma involution,
one wire strip — about twenty-four lifted moves); it is NOT machine-checked
this round.  This window is the exact remaining piece of the crossing-ride
window layer: FF/TF/FT are proven above. -/
def zxfCrossWindowTTStatement : Prop :=
  ZxwConv
    { sourceArity := 3
      layers := [[ZxpCell.crossing, ZxpCell.wire],
        [ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
        [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
        [ZxpCell.wire, ZxpCell.crossing],
        [ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire],
        [ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire],
        [ZxpCell.crossing, ZxpCell.wire]] }
    { sourceArity := 3
      layers := [[ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
        [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
        [ZxpCell.wire, ZxpCell.crossing],
        [ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire],
        [ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire],
        [ZxpCell.crossing, ZxpCell.wire],
        [ZxpCell.wire, ZxpCell.crossing]] }

/-- Kernel span pin: the TT window statement is semantically sound — its two
sides pass the span decision, so the candidate move is honest. -/
theorem zxfCrossWindowTTSpanPin :
    zxpSpanEqB
      (zxpDiagramDenote
        { sourceArity := 3
          layers := [[ZxpCell.crossing, ZxpCell.wire],
            [ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
            [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
            [ZxpCell.wire, ZxpCell.crossing],
            [ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire],
            [ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire],
            [ZxpCell.crossing, ZxpCell.wire]] })
      (zxpDiagramDenote
        { sourceArity := 3
          layers := [[ZxpCell.wire, ZxpCell.zSpider 1 2, ZxpCell.wire],
            [ZxpCell.wire, ZxpCell.wire, ZxpCell.xSpider 2 1],
            [ZxpCell.wire, ZxpCell.crossing],
            [ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire],
            [ZxpCell.wire, ZxpCell.xSpider 2 1, ZxpCell.wire],
            [ZxpCell.crossing, ZxpCell.wire],
            [ZxpCell.wire, ZxpCell.crossing]] }) = true := rfl

/-- OWNER MARKER (FALSE): the TT crossing window is not machine-checked. -/
def zxfCrossWindowTTIsProven : Bool := false

/-! ## Stage 6 — the honest marker ledger -/

/-- MARKER: the conditional transport assembly is LIVE — the zero-row
elementary operation whole (`zxfNormalFormZeroRowDrop`, fired), the reduction
of `zxwGeneratorTransportStatement` to the two named adjacent-comb moves
(`zxfTransportOfCombMoves`), the birth-side conjugation bricks
(`zxfCreatesCrossInsert`, `zxfCreatesCnotInsert`), and three of the four
crossing-ride windows (`zxfCrossWindowFF/TF/FT` + `zxfCrossIntoMergeChain`). -/
def zxfHasTransportConditionalAssembly : Bool := true

/-- MARKER (FALSE): the adjacent comb swap (`zxfCombSwapStatement`) is not
proven this round.  Landed toward it: the crossing insert at birth and the
FF/TF/FT ride windows (above).  Remaining: the TT window
(`zxfCrossWindowTTStatement`, derivation on paper, span-pinned), the
parked/zipped interleaving of the two solo comb chains, and the ride
induction with its boundary. -/
def zxfCombSwapIsProven : Bool := false

/-- MARKER (FALSE): the comb transvection (`zxfCombXorAbsorbStatement`) is not
proven this round.  Landed toward it: the birth-side CNOT insertion (above).
Remaining: the four cnot ride windows (fixed three-strand configurations whose
content is the bialgebra square distributed over one tap position — the
`zSpider 1 2`-fork of an `xSpider 2 1`-merged carrier against
`ZxpRowTag.bialgSquare`, plus coassociativity and routing), the interleaving,
and the ride induction. -/
def zxfCombXorAbsorbIsProven : Bool := false

/-- MARKER (FALSE): `zxwGeneratorTransportStatement` is NOT proven — the
assembly from the two named comb moves is proved (`zxfTransportOfCombMoves`),
the zero-row elementary operation is proved whole (`zxfNormalFormZeroRowDrop`),
and the residual is exactly `zxfCombSwapStatement` plus
`zxfCombXorAbsorbStatement`.  No inhabitant of the transport statement, of
`zxwAbsorptionStatement`, or of `zxwCompletenessStatement` exists in this
development; the committed WiringFlip owners stay byte-intact and false. -/
def zxfGeneratorTransportIsProven : Bool := false

/-- MARKER (FALSE): THE FULL PHASE-FREE DECISION did not flip this round.
The absorption residual (`zxwAbsorptionStatement`) was not attacked here; the
decision chain stays exactly as recorded on the committed
`zxwCompletenessOfAbsorptionAndTransport` / `zxwDecisionUnderCompleteness`,
now one proven conditional layer closer on the transport side. -/
def zxfHasFullDecision : Bool := false

end FX1Poly.Polygraph.Omega.ZXPhaseFree
