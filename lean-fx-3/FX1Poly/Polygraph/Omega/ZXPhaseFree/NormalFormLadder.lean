import FX1Poly.Polygraph.Omega.ZXPhaseFree.SpiderRelationSeed
import FX1Poly.Polygraph.Omega.ZXPhaseFree.CompletenessGate
import FX1Poly.Polygraph.Omega.ZXPhaseFree.FusionRepair

/-! # Polygraph/Omega/ZXPhaseFree/NormalFormLadder — the rewrite ladder toward the NF

The (C) ladder of the census commission: which `ZxrConv` rewrite steps toward the
Z-X normal form LAND as decided lemmas, and which resist — with the blocking
configuration named precisely.

## Landed

* THE PAD-LIFTING CONGRUENCE `zxnConvLift`: a whole `ZxrConv` derivation between
  windows lifts into ANY padding context (wire whiskering + before/after layers) —
  proved by recursion over the derivation with pad-composition
  (`zxnPadDiagramCompose`: a pad of a pad is one composite pad).  This is the
  missing congruence closure that lets window theorems fire in situ.
* ETA-EXPANSION `zxnEtaExpandWireZ` / `zxnEtaExpandWireX` (+ in-context corollaries
  via the lift): any wire converts to the identity spider of either colour
  (the seed's identity-spider rows read backwards).
* SEQUENTIALIZATION `zxnSequentializeAdjacentCells`: two adjacent cells in one
  layer convert to the left-first two-layer form (one `splitLayer` move) — the
  LEFT-FIRST exchange orientation is free.
* PARALLEL SAME-COLOUR FUSION at shared-wire counts 1, 2, 3, both colours, all
  boundary arities: `zxnParallelFusion{One,Two,Three}Wire{Z,X}` —
  `[[spider a k],[spider k d]] ~ [[spider a d]]` for k = 1 (one `zFuse`/`xFuse`
  move), k = 2 (fission + specialness + identity-layer strip, the FusionRepair
  Stage-7 recursion generalized to all `a`, `d`), and k = 3 (fission both sides,
  THE FROBENIUS ROW to re-associate the middle, then two LIFTED k = 2 fusions and
  a final k = 1 fusion).  These are the colour-alternation normalization steps for
  fully-shared adjacent same-colour spider pairs.

## THE WALL (named precisely)

* RIGHT-FIRST EXCHANGE `zxnRightFirstExchangeStatement` (owner FALSE): for disjoint
  cells placed as `[[wire^domL, R], [L, wire^codR]]` (the RIGHT cell firing first),
  no move of {published rows, splitLayer, zFuse, xFuse} applies: `splitLayer` only
  produces/merges the LEFT-FIRST orientation (the merged layer's left cell always
  fires first or simultaneously), and the fusion family only touches sequentially
  linked spiders.  Every route we attempted for shared-wire counts k >= 4 (and for
  the generalized Frobenius `[[wire, spider 1 k],[spider 2 1, wire^k]]` at k >= 3)
  reduces to exactly this configuration.  The instance span pin
  `zxnRightFirstExchangeInstanceSpanPin` shows the missing move is semantically
  SOUND (both sides denote the same relation, kernel) — and the FusionRepair gate
  re-run proved no per-cell counting invariant can refute it — so the repair is a
  candidate NEW MOVE (or a derivation from a richer permutation engine), not a
  refutation target.  Bill for the next commission, in order: (i) add (or derive)
  the right-first exchange, re-run the invariant gate; (ii) the general k-wire
  fusion then falls by the k = 3 pattern iterated; (iii) leg-permutation
  normalization for side-by-side spiders (crossings conjugation); (iv) the
  Kissinger Lemma 3.2/3.3 absorption induction (every WF diagram to the
  `zxnNormalForm` of its span) — the census gate for that induction is CLEARED by
  `NormalFormCensus.lean` (`zxnCensusComplete = true`), and this file's
  `zxnCompletenessViaCensusIsProven` stays FALSE until (i)-(iv) land.

Raw Lean 4 + Init only; zero-axiom; structural recursion only; no `List.append`,
no `Int`, no `Nat.sub/div/mod/min/max`, no wildcard match arms. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace FX1Poly.Polygraph.Omega.ZXPhaseFree

/-! ## Stage 0 — cat/whisker composition kit (list-level, cons-only) -/

theorem zxnWireCellsCat : (firstCount secondCount : Nat) ->
    zxpCatCells (zxpWireCells firstCount) (zxpWireCells secondCount)
      = zxpWireCells (firstCount + secondCount)
  | 0, secondCount => by
      show zxpWireCells secondCount = zxpWireCells (0 + secondCount)
      rw [Nat.zero_add]
  | firstPred + 1, secondCount => by
      show ZxpCell.wire :: zxpCatCells (zxpWireCells firstPred) (zxpWireCells secondCount)
        = zxpWireCells ((firstPred + 1) + secondCount)
      rw [zxnWireCellsCat firstPred secondCount, Nat.succ_add firstPred secondCount]
      rfl

theorem zxnCatCellsAssoc : (firstCells secondCells thirdCells : List ZxpCell) ->
    zxpCatCells (zxpCatCells firstCells secondCells) thirdCells
      = zxpCatCells firstCells (zxpCatCells secondCells thirdCells)
  | [], _secondCells, _thirdCells => rfl
  | headCell :: restCells, secondCells, thirdCells =>
      congrArg (fun innerCells => headCell :: innerCells)
        (zxnCatCellsAssoc restCells secondCells thirdCells)

/-- Whiskering twice is whiskering once with the composite wire counts. -/
theorem zxnWhiskerLayerCompose (outerLeft outerRight innerLeft innerRight : Nat)
    (layer : List ZxpCell) :
    zxpWhiskerLayer outerLeft outerRight (zxpWhiskerLayer innerLeft innerRight layer)
      = zxpWhiskerLayer (outerLeft + innerLeft) (innerRight + outerRight) layer := by
  show zxpCatCells (zxpWireCells outerLeft)
      (zxpCatCells
        (zxpCatCells (zxpWireCells innerLeft)
          (zxpCatCells layer (zxpWireCells innerRight)))
        (zxpWireCells outerRight))
    = zxpCatCells (zxpWireCells (outerLeft + innerLeft))
        (zxpCatCells layer (zxpWireCells (innerRight + outerRight)))
  rw [<- zxnWireCellsCat outerLeft innerLeft, <- zxnWireCellsCat innerRight outerRight,
    zxnCatCellsAssoc (zxpWireCells innerLeft)
      (zxpCatCells layer (zxpWireCells innerRight)) (zxpWireCells outerRight),
    zxnCatCellsAssoc layer (zxpWireCells innerRight) (zxpWireCells outerRight),
    <- zxnCatCellsAssoc (zxpWireCells outerLeft) (zxpWireCells innerLeft)
      (zxpCatCells layer
        (zxpCatCells (zxpWireCells innerRight) (zxpWireCells outerRight)))]

theorem zxnWhiskerLayersCompose (outerLeft outerRight innerLeft innerRight : Nat) :
    (layers : List (List ZxpCell)) ->
    zxpWhiskerLayers outerLeft outerRight
        (zxpWhiskerLayers innerLeft innerRight layers)
      = zxpWhiskerLayers (outerLeft + innerLeft) (innerRight + outerRight) layers
  | [] => rfl
  | layer :: restLayers => by
      show zxpWhiskerLayer outerLeft outerRight
            (zxpWhiskerLayer innerLeft innerRight layer)
          :: zxpWhiskerLayers outerLeft outerRight
            (zxpWhiskerLayers innerLeft innerRight restLayers)
        = zxpWhiskerLayer (outerLeft + innerLeft) (innerRight + outerRight) layer
          :: zxpWhiskerLayers (outerLeft + innerLeft) (innerRight + outerRight)
            restLayers
      rw [zxnWhiskerLayerCompose outerLeft outerRight innerLeft innerRight layer,
        zxnWhiskerLayersCompose outerLeft outerRight innerLeft innerRight restLayers]

theorem zxnWhiskerLayersCat (leftWires rightWires : Nat) :
    (firstLayers secondLayers : List (List ZxpCell)) ->
    zxpWhiskerLayers leftWires rightWires (zxpCatLayers firstLayers secondLayers)
      = zxpCatLayers (zxpWhiskerLayers leftWires rightWires firstLayers)
        (zxpWhiskerLayers leftWires rightWires secondLayers)
  | [], _secondLayers => rfl
  | layer :: restLayers, secondLayers => by
      show zxpWhiskerLayer leftWires rightWires layer
          :: zxpWhiskerLayers leftWires rightWires
            (zxpCatLayers restLayers secondLayers)
        = zxpWhiskerLayer leftWires rightWires layer
          :: zxpCatLayers (zxpWhiskerLayers leftWires rightWires restLayers)
            (zxpWhiskerLayers leftWires rightWires secondLayers)
      rw [zxnWhiskerLayersCat leftWires rightWires restLayers secondLayers]

theorem zxnCatLayersAssoc :
    (firstLayers secondLayers thirdLayers : List (List ZxpCell)) ->
    zxpCatLayers (zxpCatLayers firstLayers secondLayers) thirdLayers
      = zxpCatLayers firstLayers (zxpCatLayers secondLayers thirdLayers)
  | [], _secondLayers, _thirdLayers => rfl
  | headLayer :: restLayers, secondLayers, thirdLayers =>
      congrArg (fun innerLayers => headLayer :: innerLayers)
        (zxnCatLayersAssoc restLayers secondLayers thirdLayers)

/-- A pad of a pad is one composite pad. -/
theorem zxnPadDiagramCompose (outerSource outerLeft outerRight : Nat)
    (outerBefore outerAfter : List (List ZxpCell))
    (innerSource innerLeft innerRight : Nat)
    (innerBefore innerAfter : List (List ZxpCell)) (window : ZxpDiagram) :
    zxpPadDiagram outerSource outerLeft outerRight outerBefore outerAfter
        (zxpPadDiagram innerSource innerLeft innerRight innerBefore innerAfter window)
      = zxpPadDiagram outerSource (outerLeft + innerLeft) (innerRight + outerRight)
          (zxpCatLayers outerBefore
            (zxpWhiskerLayers outerLeft outerRight innerBefore))
          (zxpCatLayers (zxpWhiskerLayers outerLeft outerRight innerAfter) outerAfter)
          window := by
  show ZxpDiagram.mk outerSource
      (zxpCatLayers outerBefore
        (zxpCatLayers
          (zxpWhiskerLayers outerLeft outerRight
            (zxpCatLayers innerBefore
              (zxpCatLayers (zxpWhiskerLayers innerLeft innerRight window.layers)
                innerAfter)))
          outerAfter))
    = ZxpDiagram.mk outerSource
        (zxpCatLayers
          (zxpCatLayers outerBefore
            (zxpWhiskerLayers outerLeft outerRight innerBefore))
          (zxpCatLayers
            (zxpWhiskerLayers (outerLeft + innerLeft) (innerRight + outerRight)
              window.layers)
            (zxpCatLayers (zxpWhiskerLayers outerLeft outerRight innerAfter)
              outerAfter)))
  refine congrArg (ZxpDiagram.mk outerSource) ?_
  rw [zxnWhiskerLayersCat outerLeft outerRight innerBefore
      (zxpCatLayers (zxpWhiskerLayers innerLeft innerRight window.layers) innerAfter),
    zxnWhiskerLayersCat outerLeft outerRight
      (zxpWhiskerLayers innerLeft innerRight window.layers) innerAfter,
    zxnWhiskerLayersCompose outerLeft outerRight innerLeft innerRight window.layers,
    zxnCatLayersAssoc (zxpWhiskerLayers outerLeft outerRight innerBefore)
      (zxpCatLayers
        (zxpWhiskerLayers (outerLeft + innerLeft) (innerRight + outerRight)
          window.layers)
        (zxpWhiskerLayers outerLeft outerRight innerAfter))
      outerAfter,
    zxnCatLayersAssoc
      (zxpWhiskerLayers (outerLeft + innerLeft) (innerRight + outerRight)
        window.layers)
      (zxpWhiskerLayers outerLeft outerRight innerAfter) outerAfter,
    <- zxnCatLayersAssoc outerBefore
      (zxpWhiskerLayers outerLeft outerRight innerBefore)
      (zxpCatLayers
        (zxpWhiskerLayers (outerLeft + innerLeft) (innerRight + outerRight)
          window.layers)
        (zxpCatLayers (zxpWhiskerLayers outerLeft outerRight innerAfter) outerAfter))]

/-! ## Stage 1 — THE PAD-LIFTING CONGRUENCE -/

/-- Composite-arity shuffle used by the lift:
`l + ((il + (x + ir)) + r) = (l + il) + (x + (ir + r))`. -/
theorem zxnLiftArityShuffle (leftWires innerLeft middleArity innerRight
    rightWires : Nat) :
    leftWires + ((innerLeft + (middleArity + innerRight)) + rightWires)
      = (leftWires + innerLeft) + (middleArity + (innerRight + rightWires)) := by
  rw [<- Nat.add_assoc innerLeft middleArity innerRight,
    Nat.add_assoc (innerLeft + middleArity) innerRight rightWires,
    <- Nat.add_assoc leftWires (innerLeft + middleArity)
      (innerRight + rightWires),
    <- Nat.add_assoc leftWires innerLeft middleArity,
    Nat.add_assoc (leftWires + innerLeft) middleArity (innerRight + rightWires)]

/-- THE PAD-LIFTING CONGRUENCE: an extended-congruence derivation between windows
lifts into any padding context. -/
theorem zxnConvLift (contextSource leftWires rightWires : Nat)
    (beforeLayers afterLayers : List (List ZxpCell))
    {firstWindow secondWindow : ZxpDiagram}
    (hConv : ZxrConv firstWindow secondWindow)
    (hBeforeWF : ZxpLayersWF contextSource beforeLayers)
    (hBeforeCod : zxpLayersCodArity contextSource beforeLayers
      = leftWires + (firstWindow.sourceArity + rightWires))
    (hAfterWF : ZxpLayersWF
      (leftWires + (zxpDiagramCodArity firstWindow + rightWires)) afterLayers) :
    ZxrConv
      (zxpPadDiagram contextSource leftWires rightWires beforeLayers afterLayers
        firstWindow)
      (zxpPadDiagram contextSource leftWires rightWires beforeLayers afterLayers
        secondWindow) := by
  revert hBeforeCod hAfterWF
  induction hConv with
  | step hStep =>
      intro hBeforeCod hAfterWF
      cases hStep with
      | pad innerSource innerLeft innerRight innerBefore innerAfter hMove hInnerBWF
          hInnerBCod hInnerAWF =>
          rename_i innerWinFirst innerWinSecond
          have hPadSourceEq : (zxpPadDiagram innerSource innerLeft innerRight
              innerBefore innerAfter innerWinFirst).sourceArity = innerSource := rfl
          rw [hPadSourceEq] at hBeforeCod
          have hPadCodEq := zxpPadDiagramCodArity innerSource innerLeft innerRight
            innerBefore innerAfter innerWinFirst hInnerBCod
          rw [hPadCodEq] at hAfterWF
          rw [zxnPadDiagramCompose contextSource leftWires rightWires beforeLayers
              afterLayers innerSource innerLeft innerRight innerBefore innerAfter
              innerWinFirst,
            zxnPadDiagramCompose contextSource leftWires rightWires beforeLayers
              afterLayers innerSource innerLeft innerRight innerBefore innerAfter
              innerWinSecond]
          have hWhiskBeforeWF := zxpWhiskerLayersWF leftWires rightWires
            innerBefore hInnerBWF
          have hEBeforeWF : ZxpLayersWF contextSource
              (zxpCatLayers beforeLayers
                (zxpWhiskerLayers leftWires rightWires innerBefore)) := by
            refine zxpLayersWFCat beforeLayers _ hBeforeWF ?_
            rw [hBeforeCod]
            exact hWhiskBeforeWF
          have hEBeforeCod : zxpLayersCodArity contextSource
              (zxpCatLayers beforeLayers
                (zxpWhiskerLayers leftWires rightWires innerBefore))
              = (leftWires + innerLeft)
                + (innerWinFirst.sourceArity + (innerRight + rightWires)) := by
            rw [zxpLayersCodArityCat, hBeforeCod,
              zxpWhiskerLayersCodArity leftWires rightWires innerBefore innerSource,
              hInnerBCod]
            exact zxnLiftArityShuffle leftWires innerLeft
              innerWinFirst.sourceArity innerRight rightWires
          have hWhiskAfterWF := zxpWhiskerLayersWF leftWires rightWires
            innerAfter hInnerAWF
          have hEAfterWF : ZxpLayersWF ((leftWires + innerLeft)
              + (zxpDiagramCodArity innerWinFirst + (innerRight + rightWires)))
              (zxpCatLayers (zxpWhiskerLayers leftWires rightWires innerAfter)
                afterLayers) := by
            refine zxpLayersWFCat _ afterLayers ?_ ?_
            · rw [<- zxnLiftArityShuffle leftWires innerLeft
                (zxpDiagramCodArity innerWinFirst) innerRight rightWires]
              exact hWhiskAfterWF
            · rw [<- zxnLiftArityShuffle leftWires innerLeft
                (zxpDiagramCodArity innerWinFirst) innerRight rightWires,
                zxpWhiskerLayersCodArity leftWires rightWires innerAfter
                  (innerLeft + (zxpDiagramCodArity innerWinFirst + innerRight))]
              exact hAfterWF
          exact ZxrConv.step (ZxrStep.pad contextSource (leftWires + innerLeft)
            (innerRight + rightWires)
            (zxpCatLayers beforeLayers
              (zxpWhiskerLayers leftWires rightWires innerBefore))
            (zxpCatLayers (zxpWhiskerLayers leftWires rightWires innerAfter)
              afterLayers)
            hMove hEBeforeWF hEBeforeCod hEAfterWF)
  | refl diagram hWF =>
      intro hBeforeCod hAfterWF
      exact ZxrConv.refl _ (zxpPadDiagramWF contextSource leftWires rightWires
        beforeLayers afterLayers diagram hBeforeWF hBeforeCod hWF hAfterWF)
  | symm hInnerConv innerIH =>
      intro hBeforeCod hAfterWF
      have hBundle := zxrConvSound hInnerConv
      refine ZxrConv.symm (innerIH ?_ ?_)
      · rw [hBeforeCod, hBundle.left]
      · rw [hBundle.right.left]
        exact hAfterWF
  | trans hFirstConv _hSecondConv firstIH secondIH =>
      intro hBeforeCod hAfterWF
      have hFirstBundle := zxrConvSound hFirstConv
      refine ZxrConv.trans (firstIH hBeforeCod hAfterWF) (secondIH ?_ ?_)
      · rw [hBeforeCod, hFirstBundle.left]
      · rw [<- hFirstBundle.right.left]
        exact hAfterWF

/-! ## Stage 2 — eta expansion and left-first sequentialization -/

/-- The single wire as a window diagram. -/
def zxnWireDiagram : ZxpDiagram := { sourceArity := 1, layers := [[ZxpCell.wire]] }

/-- The Z identity spider as a window diagram. -/
def zxnZIdentitySpiderDiagram : ZxpDiagram :=
  { sourceArity := 1, layers := [[ZxpCell.zSpider 1 1]] }

/-- The X identity spider as a window diagram. -/
def zxnXIdentitySpiderDiagram : ZxpDiagram :=
  { sourceArity := 1, layers := [[ZxpCell.xSpider 1 1]] }

/-- ETA (Z): any wire converts to the Z identity spider. -/
theorem zxnEtaExpandWireZ : ZxrConv zxnWireDiagram zxnZIdentitySpiderDiagram :=
  ZxrConv.symm (zxrOfZxpConv (zxpRowConv ZxpRowTag.zIdentitySpider))

/-- ETA (X): any wire converts to the X identity spider. -/
theorem zxnEtaExpandWireX : ZxrConv zxnWireDiagram zxnXIdentitySpiderDiagram :=
  ZxrConv.symm (zxrOfZxpConv (zxpRowConv ZxpRowTag.xIdentitySpider))

/-- ETA in context: any single wire inside any padding context eta-expands to the
Z identity spider (the lift applied to the window eta). -/
theorem zxnEtaExpandWireZInContext (contextSource leftWires rightWires : Nat)
    (beforeLayers afterLayers : List (List ZxpCell))
    (hBeforeWF : ZxpLayersWF contextSource beforeLayers)
    (hBeforeCod : zxpLayersCodArity contextSource beforeLayers
      = leftWires + (1 + rightWires))
    (hAfterWF : ZxpLayersWF (leftWires + (1 + rightWires)) afterLayers) :
    ZxrConv
      (zxpPadDiagram contextSource leftWires rightWires beforeLayers afterLayers
        zxnWireDiagram)
      (zxpPadDiagram contextSource leftWires rightWires beforeLayers afterLayers
        zxnZIdentitySpiderDiagram) :=
  zxnConvLift contextSource leftWires rightWires beforeLayers afterLayers
    zxnEtaExpandWireZ hBeforeWF hBeforeCod hAfterWF

/-- LEFT-FIRST SEQUENTIALIZATION: two adjacent cells in one layer convert to the
left-cell-first two-layer form (one seed `splitLayer` move) — the free half of the
exchange law. -/
theorem zxnSequentializeAdjacentCells (leftCell rightCell : ZxpCell) :
    ZxrConv
      { sourceArity := zxpLayerDomArity [leftCell] + zxpLayerDomArity [rightCell]
        layers := [zxpCatCells [leftCell] [rightCell]] }
      { sourceArity := zxpLayerDomArity [leftCell] + zxpLayerDomArity [rightCell]
        layers := [zxpCatCells [leftCell] (zxpWireCells (zxpLayerDomArity [rightCell])),
          zxpCatCells (zxpWireCells (zxpLayerCodArity [leftCell])) [rightCell]] } := by
  have hStep := ZxrStep.pad
    (zxpLayerDomArity [leftCell] + zxpLayerDomArity [rightCell]) 0 0 [] []
    (ZxrWindowMove.seed (ZxpWindowMove.splitLayer [leftCell] [rightCell]))
    (ZxpLayersWF.nil _) (Nat.zero_add _).symm (ZxpLayersWF.nil _)
  rw [zxpPadDiagramIdentityAt
      (zxpLayerDomArity [leftCell] + zxpLayerDomArity [rightCell])
      { sourceArity := zxpLayerDomArity [leftCell] + zxpLayerDomArity [rightCell]
        layers := [zxpCatCells [leftCell] [rightCell]] } rfl,
    zxpPadDiagramIdentityAt
      (zxpLayerDomArity [leftCell] + zxpLayerDomArity [rightCell])
      { sourceArity := zxpLayerDomArity [leftCell] + zxpLayerDomArity [rightCell]
        layers := [zxpCatCells [leftCell]
            (zxpWireCells (zxpLayerDomArity [rightCell])),
          zxpCatCells (zxpWireCells (zxpLayerCodArity [leftCell])) [rightCell]] } rfl]
    at hStep
  exact ZxrConv.step hStep

/-! ## Stage 3 — parallel same-colour fusion at shared-wire counts 1, 2, 3 -/

/-- k = 1 (Z): `[[zSpider a 1],[zSpider 1 d]] ~ [[zSpider a d]]` — one `zFuse`. -/
theorem zxnParallelFusionOneWireZ (topLegs botLegs : Nat) :
    ZxrConv
      { sourceArity := topLegs
        layers := [[ZxpCell.zSpider topLegs 1], [ZxpCell.zSpider 1 botLegs]] }
      { sourceArity := topLegs, layers := [[ZxpCell.zSpider topLegs botLegs]] } := by
  have hStep := ZxrStep.pad (topLegs + 0) 0 0 [] []
    (ZxrWindowMove.zFuse topLegs 0 0 botLegs)
    (ZxpLayersWF.nil _) (Nat.zero_add _).symm (ZxpLayersWF.nil _)
  have hConv : ZxrConv
      { sourceArity := topLegs
        layers := [[ZxpCell.zSpider topLegs 1], [ZxpCell.zSpider 1 botLegs]] }
      { sourceArity := topLegs
        layers := [[ZxpCell.zSpider (topLegs + 0) (0 + botLegs)]] } :=
    ZxrConv.step hStep
  rw [Nat.zero_add botLegs] at hConv
  exact hConv

/-- k = 1 (X): the colour mirror. -/
theorem zxnParallelFusionOneWireX (topLegs botLegs : Nat) :
    ZxrConv
      { sourceArity := topLegs
        layers := [[ZxpCell.xSpider topLegs 1], [ZxpCell.xSpider 1 botLegs]] }
      { sourceArity := topLegs, layers := [[ZxpCell.xSpider topLegs botLegs]] } := by
  have hStep := ZxrStep.pad (topLegs + 0) 0 0 [] []
    (ZxrWindowMove.xFuse topLegs 0 0 botLegs)
    (ZxpLayersWF.nil _) (Nat.zero_add _).symm (ZxpLayersWF.nil _)
  have hConv : ZxrConv
      { sourceArity := topLegs
        layers := [[ZxpCell.xSpider topLegs 1], [ZxpCell.xSpider 1 botLegs]] }
      { sourceArity := topLegs
        layers := [[ZxpCell.xSpider (topLegs + 0) (0 + botLegs)]] } :=
    ZxrConv.step hStep
  rw [Nat.zero_add botLegs] at hConv
  exact hConv

/-- k = 2 (Z): `[[zSpider a 2],[zSpider 2 d]] ~ [[zSpider a d]]` — fission both
sides, kill the exposed hub by `specialZ`, strip the identity layer, refuse. -/
theorem zxnParallelFusionTwoWireZ (topLegs botLegs : Nat) :
    ZxrConv
      { sourceArity := topLegs
        layers := [[ZxpCell.zSpider topLegs 2], [ZxpCell.zSpider 2 botLegs]] }
      { sourceArity := topLegs, layers := [[ZxpCell.zSpider topLegs botLegs]] } := by
  -- E0 ~ E1: fission the top spider
  have hStepOne := ZxrStep.pad topLegs 0 0 [] [[ZxpCell.zSpider 2 botLegs]]
    (ZxrWindowMove.zFuse topLegs 0 0 2)
    (ZxpLayersWF.nil _) (Nat.zero_add _).symm
    (ZxpLayersWF.cons rfl (ZxpLayersWF.nil _))
  have hConvOne : ZxrConv
      { sourceArity := topLegs
        layers := [[ZxpCell.zSpider topLegs 2], [ZxpCell.zSpider 2 botLegs]] }
      { sourceArity := topLegs
        layers := [[ZxpCell.zSpider topLegs 1], [ZxpCell.zSpider 1 2],
          [ZxpCell.zSpider 2 botLegs]] } :=
    ZxrConv.symm (ZxrConv.step hStepOne)
  -- E1 ~ E2: fission the bottom spider
  have hStepTwo := ZxrStep.pad topLegs 0 0
    [[ZxpCell.zSpider topLegs 1], [ZxpCell.zSpider 1 2]] []
    (ZxrWindowMove.zFuse 2 0 0 botLegs)
    (ZxpLayersWF.cons rfl (ZxpLayersWF.cons rfl (ZxpLayersWF.nil _)))
    rfl (ZxpLayersWF.nil _)
  have hConvTwo : ZxrConv
      { sourceArity := topLegs
        layers := [[ZxpCell.zSpider topLegs 1], [ZxpCell.zSpider 1 2],
          [ZxpCell.zSpider 2 (0 + botLegs)]] }
      { sourceArity := topLegs
        layers := [[ZxpCell.zSpider topLegs 1], [ZxpCell.zSpider 1 2],
          [ZxpCell.zSpider 2 1], [ZxpCell.zSpider 1 botLegs]] } :=
    ZxrConv.symm (ZxrConv.step hStepTwo)
  rw [Nat.zero_add botLegs] at hConvTwo
  -- E2 ~ E3: the exposed hub pair dies by specialness
  have hStepThree := ZxrStep.pad topLegs 0 0 [[ZxpCell.zSpider topLegs 1]]
    [[ZxpCell.zSpider 1 botLegs]]
    (ZxrWindowMove.seed (ZxpWindowMove.row ZxpRowTag.specialZ))
    (ZxpLayersWF.cons rfl (ZxpLayersWF.nil _)) rfl
    (ZxpLayersWF.cons rfl (ZxpLayersWF.nil _))
  have hConvThree : ZxrConv
      { sourceArity := topLegs
        layers := [[ZxpCell.zSpider topLegs 1], [ZxpCell.zSpider 1 2],
          [ZxpCell.zSpider 2 1], [ZxpCell.zSpider 1 botLegs]] }
      { sourceArity := topLegs
        layers := [[ZxpCell.zSpider topLegs 1], [ZxpCell.wire],
          [ZxpCell.zSpider 1 botLegs]] } :=
    ZxrConv.step hStepThree
  -- E3 ~ E4: strip the identity layer
  have hStepFour := ZxrStep.pad topLegs 0 0 [] [[ZxpCell.zSpider 1 botLegs]]
    (ZxrWindowMove.seed (ZxpWindowMove.splitLayer [ZxpCell.zSpider topLegs 1] []))
    (ZxpLayersWF.nil _) (Nat.zero_add _).symm
    (ZxpLayersWF.cons rfl (ZxpLayersWF.nil _))
  have hConvFour : ZxrConv
      { sourceArity := topLegs
        layers := [[ZxpCell.zSpider topLegs 1], [ZxpCell.wire],
          [ZxpCell.zSpider 1 botLegs]] }
      { sourceArity := topLegs
        layers := [[ZxpCell.zSpider topLegs 1], [ZxpCell.zSpider 1 botLegs]] } :=
    ZxrConv.symm (ZxrConv.step hStepFour)
  -- E4 ~ E5: the final one-wire fusion
  have hConvFive := zxnParallelFusionOneWireZ topLegs botLegs
  exact ZxrConv.trans hConvOne (ZxrConv.trans hConvTwo
    (ZxrConv.trans hConvThree (ZxrConv.trans hConvFour hConvFive)))

/-- k = 2 (X): the colour mirror through `specialX`. -/
theorem zxnParallelFusionTwoWireX (topLegs botLegs : Nat) :
    ZxrConv
      { sourceArity := topLegs
        layers := [[ZxpCell.xSpider topLegs 2], [ZxpCell.xSpider 2 botLegs]] }
      { sourceArity := topLegs, layers := [[ZxpCell.xSpider topLegs botLegs]] } := by
  have hStepOne := ZxrStep.pad topLegs 0 0 [] [[ZxpCell.xSpider 2 botLegs]]
    (ZxrWindowMove.xFuse topLegs 0 0 2)
    (ZxpLayersWF.nil _) (Nat.zero_add _).symm
    (ZxpLayersWF.cons rfl (ZxpLayersWF.nil _))
  have hConvOne : ZxrConv
      { sourceArity := topLegs
        layers := [[ZxpCell.xSpider topLegs 2], [ZxpCell.xSpider 2 botLegs]] }
      { sourceArity := topLegs
        layers := [[ZxpCell.xSpider topLegs 1], [ZxpCell.xSpider 1 2],
          [ZxpCell.xSpider 2 botLegs]] } :=
    ZxrConv.symm (ZxrConv.step hStepOne)
  have hStepTwo := ZxrStep.pad topLegs 0 0
    [[ZxpCell.xSpider topLegs 1], [ZxpCell.xSpider 1 2]] []
    (ZxrWindowMove.xFuse 2 0 0 botLegs)
    (ZxpLayersWF.cons rfl (ZxpLayersWF.cons rfl (ZxpLayersWF.nil _)))
    rfl (ZxpLayersWF.nil _)
  have hConvTwo : ZxrConv
      { sourceArity := topLegs
        layers := [[ZxpCell.xSpider topLegs 1], [ZxpCell.xSpider 1 2],
          [ZxpCell.xSpider 2 (0 + botLegs)]] }
      { sourceArity := topLegs
        layers := [[ZxpCell.xSpider topLegs 1], [ZxpCell.xSpider 1 2],
          [ZxpCell.xSpider 2 1], [ZxpCell.xSpider 1 botLegs]] } :=
    ZxrConv.symm (ZxrConv.step hStepTwo)
  rw [Nat.zero_add botLegs] at hConvTwo
  have hStepThree := ZxrStep.pad topLegs 0 0 [[ZxpCell.xSpider topLegs 1]]
    [[ZxpCell.xSpider 1 botLegs]]
    (ZxrWindowMove.seed (ZxpWindowMove.row ZxpRowTag.specialX))
    (ZxpLayersWF.cons rfl (ZxpLayersWF.nil _)) rfl
    (ZxpLayersWF.cons rfl (ZxpLayersWF.nil _))
  have hConvThree : ZxrConv
      { sourceArity := topLegs
        layers := [[ZxpCell.xSpider topLegs 1], [ZxpCell.xSpider 1 2],
          [ZxpCell.xSpider 2 1], [ZxpCell.xSpider 1 botLegs]] }
      { sourceArity := topLegs
        layers := [[ZxpCell.xSpider topLegs 1], [ZxpCell.wire],
          [ZxpCell.xSpider 1 botLegs]] } :=
    ZxrConv.step hStepThree
  have hStepFour := ZxrStep.pad topLegs 0 0 [] [[ZxpCell.xSpider 1 botLegs]]
    (ZxrWindowMove.seed (ZxpWindowMove.splitLayer [ZxpCell.xSpider topLegs 1] []))
    (ZxpLayersWF.nil _) (Nat.zero_add _).symm
    (ZxpLayersWF.cons rfl (ZxpLayersWF.nil _))
  have hConvFour : ZxrConv
      { sourceArity := topLegs
        layers := [[ZxpCell.xSpider topLegs 1], [ZxpCell.wire],
          [ZxpCell.xSpider 1 botLegs]] }
      { sourceArity := topLegs
        layers := [[ZxpCell.xSpider topLegs 1], [ZxpCell.xSpider 1 botLegs]] } :=
    ZxrConv.symm (ZxrConv.step hStepFour)
  have hConvFive := zxnParallelFusionOneWireX topLegs botLegs
  exact ZxrConv.trans hConvOne (ZxrConv.trans hConvTwo
    (ZxrConv.trans hConvThree (ZxrConv.trans hConvFour hConvFive)))

/-- k = 3 (Z): `[[zSpider a 3],[zSpider 3 d]] ~ [[zSpider a d]]` — fission both
sides, re-associate the middle by THE FROBENIUS ROW, collapse with two LIFTED
k = 2 fusions and one k = 1 fusion. -/
theorem zxnParallelFusionThreeWireZ (topLegs botLegs : Nat) :
    ZxrConv
      { sourceArity := topLegs
        layers := [[ZxpCell.zSpider topLegs 3], [ZxpCell.zSpider 3 botLegs]] }
      { sourceArity := topLegs, layers := [[ZxpCell.zSpider topLegs botLegs]] } := by
  -- D0 ~ D1: fission the top spider at its last output
  have hStepOne := ZxrStep.pad topLegs 0 0 [] [[ZxpCell.zSpider 3 botLegs]]
    (ZxrWindowMove.zFuse topLegs 1 0 2)
    (ZxpLayersWF.nil _) (Nat.zero_add _).symm
    (ZxpLayersWF.cons rfl (ZxpLayersWF.nil _))
  have hConvOne : ZxrConv
      { sourceArity := topLegs
        layers := [[ZxpCell.zSpider topLegs 3], [ZxpCell.zSpider 3 botLegs]] }
      { sourceArity := topLegs
        layers := [[ZxpCell.zSpider topLegs 2], [ZxpCell.wire, ZxpCell.zSpider 1 2],
          [ZxpCell.zSpider 3 botLegs]] } :=
    ZxrConv.symm (ZxrConv.step hStepOne)
  -- D1 ~ D2: fission the bottom spider at its first input
  have hStepTwo := ZxrStep.pad topLegs 0 0
    [[ZxpCell.zSpider topLegs 2], [ZxpCell.wire, ZxpCell.zSpider 1 2]] []
    (ZxrWindowMove.zFuse 2 0 1 botLegs)
    (ZxpLayersWF.cons rfl (ZxpLayersWF.cons rfl (ZxpLayersWF.nil _)))
    rfl (ZxpLayersWF.nil _)
  have hConvTwo : ZxrConv
      { sourceArity := topLegs
        layers := [[ZxpCell.zSpider topLegs 2], [ZxpCell.wire, ZxpCell.zSpider 1 2],
          [ZxpCell.zSpider 3 (0 + botLegs)]] }
      { sourceArity := topLegs
        layers := [[ZxpCell.zSpider topLegs 2], [ZxpCell.wire, ZxpCell.zSpider 1 2],
          [ZxpCell.zSpider 2 1, ZxpCell.wire], [ZxpCell.zSpider 2 botLegs]] } :=
    ZxrConv.symm (ZxrConv.step hStepTwo)
  rw [Nat.zero_add botLegs] at hConvTwo
  -- D2 ~ D3: THE FROBENIUS ROW re-associates the middle
  have hStepThree := ZxrStep.pad topLegs 0 0 [[ZxpCell.zSpider topLegs 2]]
    [[ZxpCell.zSpider 2 botLegs]]
    (ZxrWindowMove.seed (ZxpWindowMove.row ZxpRowTag.frobeniusZRight))
    (ZxpLayersWF.cons rfl (ZxpLayersWF.nil _)) rfl
    (ZxpLayersWF.cons rfl (ZxpLayersWF.nil _))
  have hConvThree : ZxrConv
      { sourceArity := topLegs
        layers := [[ZxpCell.zSpider topLegs 2], [ZxpCell.wire, ZxpCell.zSpider 1 2],
          [ZxpCell.zSpider 2 1, ZxpCell.wire], [ZxpCell.zSpider 2 botLegs]] }
      { sourceArity := topLegs
        layers := [[ZxpCell.zSpider topLegs 2], [ZxpCell.zSpider 2 1],
          [ZxpCell.zSpider 1 2], [ZxpCell.zSpider 2 botLegs]] } :=
    ZxrConv.step hStepThree
  -- D3 ~ D4: LIFTED k = 2 fusion on the top pair
  have hConvFour : ZxrConv
      { sourceArity := topLegs
        layers := [[ZxpCell.zSpider topLegs 2], [ZxpCell.zSpider 2 1],
          [ZxpCell.zSpider 1 2], [ZxpCell.zSpider 2 botLegs]] }
      { sourceArity := topLegs
        layers := [[ZxpCell.zSpider topLegs 1],
          [ZxpCell.zSpider 1 2], [ZxpCell.zSpider 2 botLegs]] } :=
    zxnConvLift topLegs 0 0 []
      [[ZxpCell.zSpider 1 2], [ZxpCell.zSpider 2 botLegs]]
      (zxnParallelFusionTwoWireZ topLegs 1)
      (ZxpLayersWF.nil _) (Nat.zero_add _).symm
      (ZxpLayersWF.cons rfl (ZxpLayersWF.cons rfl (ZxpLayersWF.nil _)))
  -- D4 ~ D5: LIFTED k = 2 fusion on the bottom pair
  have hConvFive : ZxrConv
      { sourceArity := topLegs
        layers := [[ZxpCell.zSpider topLegs 1],
          [ZxpCell.zSpider 1 2], [ZxpCell.zSpider 2 botLegs]] }
      { sourceArity := topLegs
        layers := [[ZxpCell.zSpider topLegs 1], [ZxpCell.zSpider 1 botLegs]] } :=
    zxnConvLift topLegs 0 0 [[ZxpCell.zSpider topLegs 1]] []
      (zxnParallelFusionTwoWireZ 1 botLegs)
      (ZxpLayersWF.cons rfl (ZxpLayersWF.nil _)) rfl (ZxpLayersWF.nil _)
  -- D5 ~ D6: the final one-wire fusion
  have hConvSix := zxnParallelFusionOneWireZ topLegs botLegs
  exact ZxrConv.trans hConvOne (ZxrConv.trans hConvTwo (ZxrConv.trans hConvThree
    (ZxrConv.trans hConvFour (ZxrConv.trans hConvFive hConvSix))))

/-- k = 3 (X): the colour mirror through `frobeniusXRight`. -/
theorem zxnParallelFusionThreeWireX (topLegs botLegs : Nat) :
    ZxrConv
      { sourceArity := topLegs
        layers := [[ZxpCell.xSpider topLegs 3], [ZxpCell.xSpider 3 botLegs]] }
      { sourceArity := topLegs, layers := [[ZxpCell.xSpider topLegs botLegs]] } := by
  have hStepOne := ZxrStep.pad topLegs 0 0 [] [[ZxpCell.xSpider 3 botLegs]]
    (ZxrWindowMove.xFuse topLegs 1 0 2)
    (ZxpLayersWF.nil _) (Nat.zero_add _).symm
    (ZxpLayersWF.cons rfl (ZxpLayersWF.nil _))
  have hConvOne : ZxrConv
      { sourceArity := topLegs
        layers := [[ZxpCell.xSpider topLegs 3], [ZxpCell.xSpider 3 botLegs]] }
      { sourceArity := topLegs
        layers := [[ZxpCell.xSpider topLegs 2], [ZxpCell.wire, ZxpCell.xSpider 1 2],
          [ZxpCell.xSpider 3 botLegs]] } :=
    ZxrConv.symm (ZxrConv.step hStepOne)
  have hStepTwo := ZxrStep.pad topLegs 0 0
    [[ZxpCell.xSpider topLegs 2], [ZxpCell.wire, ZxpCell.xSpider 1 2]] []
    (ZxrWindowMove.xFuse 2 0 1 botLegs)
    (ZxpLayersWF.cons rfl (ZxpLayersWF.cons rfl (ZxpLayersWF.nil _)))
    rfl (ZxpLayersWF.nil _)
  have hConvTwo : ZxrConv
      { sourceArity := topLegs
        layers := [[ZxpCell.xSpider topLegs 2], [ZxpCell.wire, ZxpCell.xSpider 1 2],
          [ZxpCell.xSpider 3 (0 + botLegs)]] }
      { sourceArity := topLegs
        layers := [[ZxpCell.xSpider topLegs 2], [ZxpCell.wire, ZxpCell.xSpider 1 2],
          [ZxpCell.xSpider 2 1, ZxpCell.wire], [ZxpCell.xSpider 2 botLegs]] } :=
    ZxrConv.symm (ZxrConv.step hStepTwo)
  rw [Nat.zero_add botLegs] at hConvTwo
  have hStepThree := ZxrStep.pad topLegs 0 0 [[ZxpCell.xSpider topLegs 2]]
    [[ZxpCell.xSpider 2 botLegs]]
    (ZxrWindowMove.seed (ZxpWindowMove.row ZxpRowTag.frobeniusXRight))
    (ZxpLayersWF.cons rfl (ZxpLayersWF.nil _)) rfl
    (ZxpLayersWF.cons rfl (ZxpLayersWF.nil _))
  have hConvThree : ZxrConv
      { sourceArity := topLegs
        layers := [[ZxpCell.xSpider topLegs 2], [ZxpCell.wire, ZxpCell.xSpider 1 2],
          [ZxpCell.xSpider 2 1, ZxpCell.wire], [ZxpCell.xSpider 2 botLegs]] }
      { sourceArity := topLegs
        layers := [[ZxpCell.xSpider topLegs 2], [ZxpCell.xSpider 2 1],
          [ZxpCell.xSpider 1 2], [ZxpCell.xSpider 2 botLegs]] } :=
    ZxrConv.step hStepThree
  have hConvFour : ZxrConv
      { sourceArity := topLegs
        layers := [[ZxpCell.xSpider topLegs 2], [ZxpCell.xSpider 2 1],
          [ZxpCell.xSpider 1 2], [ZxpCell.xSpider 2 botLegs]] }
      { sourceArity := topLegs
        layers := [[ZxpCell.xSpider topLegs 1],
          [ZxpCell.xSpider 1 2], [ZxpCell.xSpider 2 botLegs]] } :=
    zxnConvLift topLegs 0 0 []
      [[ZxpCell.xSpider 1 2], [ZxpCell.xSpider 2 botLegs]]
      (zxnParallelFusionTwoWireX topLegs 1)
      (ZxpLayersWF.nil _) (Nat.zero_add _).symm
      (ZxpLayersWF.cons rfl (ZxpLayersWF.cons rfl (ZxpLayersWF.nil _)))
  have hConvFive : ZxrConv
      { sourceArity := topLegs
        layers := [[ZxpCell.xSpider topLegs 1],
          [ZxpCell.xSpider 1 2], [ZxpCell.xSpider 2 botLegs]] }
      { sourceArity := topLegs
        layers := [[ZxpCell.xSpider topLegs 1], [ZxpCell.xSpider 1 botLegs]] } :=
    zxnConvLift topLegs 0 0 [[ZxpCell.xSpider topLegs 1]] []
      (zxnParallelFusionTwoWireX 1 botLegs)
      (ZxpLayersWF.cons rfl (ZxpLayersWF.nil _)) rfl (ZxpLayersWF.nil _)
  have hConvSix := zxnParallelFusionOneWireX topLegs botLegs
  exact ZxrConv.trans hConvOne (ZxrConv.trans hConvTwo (ZxrConv.trans hConvThree
    (ZxrConv.trans hConvFour (ZxrConv.trans hConvFive hConvSix))))

/-! ## Stage 4 — THE WALL and the honesty markers -/

/-- THE MISSING MOVE (owner FALSE, see the header): the RIGHT-FIRST exchange —
disjoint adjacent cells with the right cell firing first merge into one layer.
Well-formed and span-sound (see the instance pin), but not derivable by any route
we found from {rows, splitLayer, zFuse, xFuse}; every k >= 4 parallel-fusion route
reduces to it. -/
def zxnRightFirstExchangeStatement : Prop :=
  (leftCell rightCell : ZxpCell) ->
    ZxrConv
      { sourceArity := zxpLayerDomArity [leftCell] + zxpLayerDomArity [rightCell]
        layers := [zxpCatCells (zxpWireCells (zxpLayerDomArity [leftCell])) [rightCell],
          zxpCatCells [leftCell] (zxpWireCells (zxpLayerCodArity [rightCell]))] }
      { sourceArity := zxpLayerDomArity [leftCell] + zxpLayerDomArity [rightCell]
        layers := [zxpCatCells [leftCell] [rightCell]] }

/-- OWNER MARKER: the right-first exchange is NOT proven (and not refuted — the
FusionRepair gate re-run shows the per-cell weight family cannot separate it). -/
def zxnRightFirstExchangeIsProven : Bool := false

set_option maxRecDepth 8192 in
/-- Instance span pin: at `leftCell = zSpider 2 1`, `rightCell = zSpider 1 2`, the
right-first two-layer form and the merged layer denote THE SAME relation (kernel) —
the missing move is semantically sound. -/
theorem zxnRightFirstExchangeInstanceSpanPin :
    zxpSpanEqB
      (zxpDiagramDenote
        { sourceArity := 3
          layers := [[ZxpCell.wire, ZxpCell.wire, ZxpCell.zSpider 1 2],
            [ZxpCell.zSpider 2 1, ZxpCell.wire, ZxpCell.wire]] })
      (zxpDiagramDenote
        { sourceArity := 3
          layers := [[ZxpCell.zSpider 2 1, ZxpCell.zSpider 1 2]] }) = true := rfl

/-- LADDER MARKER: the pad-lifting congruence is shipped (`zxnConvLift`). -/
def zxnHasPadLiftingCongruence : Bool := true

/-- LADDER MARKER: eta-expansion of wires into identity spiders of both colours
is shipped, window-level and in-context. -/
def zxnLadderEtaExpansionLanded : Bool := true

/-- LADDER MARKER: parallel same-colour fusion at shared-wire counts 1, 2, 3
(both colours, all boundary arities) is shipped. -/
def zxnLadderParallelFusionUpToThreeLanded : Bool := true

/-- LADDER MARKER (owner FALSE): the GENERAL k-wire fusion is NOT proven — every
route at k >= 4 reduces to the right-first exchange configuration
(`zxnRightFirstExchangeStatement`); with that move granted, the k = 3 pattern
iterates.  Precisely: fissioning `zSpider a (k+1)` at its last output and
`zSpider (k+1) d` at its first input leaves the disjoint pair
`[[wire^(k-1), zSpider 1 2], [zSpider 2 1, wire^(k-1)]]` in right-first
orientation for k >= 2 — merged only in the other orientation by `splitLayer`. -/
def zxnLadderGeneralKWireFusionLanded : Bool := false

/-- LADDER MARKER (owner FALSE): colour-alternation normalization of ARBITRARY
adjacent same-colour blocks is not shipped — fully-shared single-spider pairs fuse
up to k = 3 (above); side-by-side spiders need the leg-permutation engine
(crossings conjugation), which is the wall's bill item (iii). -/
def zxnLadderColourAlternationLanded : Bool := false

/-- COMPLETENESS OWNER (FALSE): the full completeness induction (every well-formed
diagram `ZxrConv`-converts to `zxnNormalForm` of its span) is NOT proven.  The
census gate demanded by `zxrCompletenessStatement`'s docstring is CLEARED
(`NormalFormCensus.zxnCensusComplete = true`); the remaining bill is the header's
(i)-(iv): right-first exchange, general k-wire fusion, leg permutation, and the
Kissinger Lemma 3.2/3.3 absorption induction.  `zxrCompletenessIsProven` in
`FusionRepair.lean` stays byte-intact FALSE. -/
def zxnCompletenessViaCensusIsProven : Bool := false

end FX1Poly.Polygraph.Omega.ZXPhaseFree
