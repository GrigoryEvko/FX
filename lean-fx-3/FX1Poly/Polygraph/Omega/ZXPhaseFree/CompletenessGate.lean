import FX1Poly.Polygraph.Omega.ZXPhaseFree.SpiderRelationSeed

/-! # Polygraph/Omega/ZXPhaseFree/CompletenessGate — THE INVARIANT-FIRST GATE

The mandatory refutation-before-proof gate for `zxpCompletenessStatement` (the arc law:
five prior missing-row defects in this workstream were caught invariant-first; this gate
is the sixth catch).  VERDICT: **(a) REFUTED** — `zxgCompletenessRefuted` derives `False`
from `zxpCompletenessStatement`; the marker is `zxgGateVerdictIsRefuted := true`.

THE SEPARATOR (an arity-weighted count from the commissioned count-vector family): the
number of spider cells with at least 4 total legs (`zxgCellBigSpiderWeight`).  Every cell
occurring in any of the 33 published row diagrams is a spider drawn from the fixed
small-arity set {(0,1), (1,0), (1,1), (1,2), (2,1)} (both colours) or a wire/crossing;
the `splitLayer` move re-wraps the same cells plus wires; padding adds context layers
IDENTICAL on both sides plus whisker wires.  So no `ZxpConv` derivation can ever create
or destroy a >= 4-leg spider — the count is a full congruence invariant, machine-checked
below under EVERY constructor (`zxgConvFoldEq` structural induction; the 33 rows by
kernel decision).  The seed's own fusion fire supplies the separated pair:
`zxpZFusedTripleDiagram` = [[zSpider 3 1]] and `zxpZChainedPairDiagram`
= [[zSpider 2 1, wire], [zSpider 2 1]] are span-equal (kernel), well-formed (kernel),
share boundaries 3 -> 1 (kernel), yet carry big-spider counts 1 vs 0 — hence NOT
convertible, and completeness as stated is FALSE.

THE ROW-EFFECT DELTA TABLE (the commissioned method, shipped as kernel-decided facts):
for the base count vector (zSpider count, xSpider count, wire count, crossing count,
layer count, zSpider legs, xSpider legs) the mod-2 lhs/rhs delta of each of the 33 rows
is pinned as the explicit 33x7 Bool matrix `zxgRowDeltaTableValue`; two `splitLayer`
witnesses are pinned; the row space of the full generator table equals the 6-dimensional
basis {e_zCount, e_xCount, e_wireCount, e_crossingCount, e_layerCount,
e_zLegs + e_xLegs} (`zxgDeltaTableSpanBasisPin`, decided by `zxpSpanEqB`); the preserved
mod-2 functional lattice — the orthogonal complement, computed by enumerating ALL 128
functionals (`zxgPreservedLatticeClassified`) — is exactly {0, legs-parity}; and the
sole survivor legs-parity is BOUNDARY-DETERMINED on well-formed diagrams
(`zxgLegsParityFunctionalBoundaryDetermined`: total spider legs are congruent mod 2 to
sourceArity + codArity).  Conclusion: the base count space holds NO separator — the base
gate is clean, and the refutation necessarily lives in the arity-REFINED extension of the
count vector (per-spider-type counts), which is exactly where the row set has a hole.

DIAGNOSIS AND WHAT A FUTURE COMPLETENESS PUSH MAY ASSUME: Kissinger's (sp) n-ary fusion
family is derived-not-primitive in IH only because the IH syntax has no n-ary spider
generators; `ZxpCell` DOES carry arbitrary-arity primitive spiders, so fusion must be
primitive here.  Repair options recorded for the (separately commissioned) push:
  (R1) extend `ZxpRowTag` with the arity-recursion fusion rows (e.g. zSpider (m+1) n
       against its two-cell decomposition, both colours, plus the 0/1-leg collapses),
       then RE-RUN THIS GATE: the per-spider-type counts must all become unbalanced
       (the generic engine `zxgConvFoldEq` makes that check one kernel decision per
       weight), and only then attempt the Lemma 3.2/3.3/Thm 3.4 induction; or
  (R2) restrict the completeness statement to diagrams whose spiders all lie in the
       small-arity generator set (the honest IH sub-syntax); the Z-X normal-form census
       of Kissinger eq. (5)/(6) is then the next gate stage.
`zxpCompletenessStatement` STAYS owner-false — and is now machine-refuted as stated.

Raw Lean 4 + Init only; zero-axiom; structural recursion only; no `List.append`, no
`Int`, no `Nat.sub/div/mod/min/max`, full-enumeration matches only. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace FX1Poly.Polygraph.Omega.ZXPhaseFree

/-! ## Stage 0 — parity / equality kit (fresh, cons-only, four-case Bool tables) -/

/-- Structural parity of a `Nat` (its image in F2). -/
def zxgParityB : Nat -> Bool
  | 0 => false
  | valuePred + 1 => zxpXorB true (zxgParityB valuePred)

/-- Fresh four-case Bool equality decision. -/
def zxgBoolEqB : Bool -> Bool -> Bool
  | false, false => true
  | false, true => false
  | true, false => false
  | true, true => true

/-- The seed's structural Nat equality decision fires on the diagonal. -/
theorem zxgNatEqBRefl : (value : Nat) -> zxpNatEqB value value = true
  | 0 => rfl
  | valuePred + 1 => zxgNatEqBRefl valuePred

/-- Medial exchange for xor: `(a+b)+(c+d) = (a+c)+(b+d)` in F2, by truth table. -/
theorem zxgXorBMedial : (firstBit secondBit thirdBit fourthBit : Bool) ->
    zxpXorB (zxpXorB firstBit secondBit) (zxpXorB thirdBit fourthBit)
      = zxpXorB (zxpXorB firstBit thirdBit) (zxpXorB secondBit fourthBit)
  | false, false, false, false => rfl
  | false, false, false, true => rfl
  | false, false, true, false => rfl
  | false, false, true, true => rfl
  | false, true, false, false => rfl
  | false, true, false, true => rfl
  | false, true, true, false => rfl
  | false, true, true, true => rfl
  | true, false, false, false => rfl
  | true, false, false, true => rfl
  | true, false, true, false => rfl
  | true, false, true, true => rfl
  | true, true, false, false => rfl
  | true, true, false, true => rfl
  | true, true, true, false => rfl
  | true, true, true, true => rfl

/-- Middle cancellation for xor: `(a+b)+(b+c) = a+c` in F2, by truth table. -/
theorem zxgXorBCancelMiddle : (firstBit secondBit thirdBit : Bool) ->
    zxpXorB (zxpXorB firstBit secondBit) (zxpXorB secondBit thirdBit)
      = zxpXorB firstBit thirdBit
  | false, false, false => rfl
  | false, false, true => rfl
  | false, true, false => rfl
  | false, true, true => rfl
  | true, false, false => rfl
  | true, false, true => rfl
  | true, true, false => rfl
  | true, true, true => rfl

/-- Parity is additive: `parity (a + b) = parity a xor parity b`. -/
theorem zxgParityBAdd : (firstValue secondValue : Nat) ->
    zxgParityB (firstValue + secondValue)
      = zxpXorB (zxgParityB firstValue) (zxgParityB secondValue)
  | firstValue, 0 => (zxpXorBFalseRight (zxgParityB firstValue)).symm
  | firstValue, secondPred + 1 => by
      show zxpXorB true (zxgParityB (firstValue + secondPred))
        = zxpXorB (zxgParityB firstValue) (zxpXorB true (zxgParityB secondPred))
      rw [zxgParityBAdd firstValue secondPred,
        <- zxpXorBAssoc true (zxgParityB firstValue) (zxgParityB secondPred),
        zxpXorBComm true (zxgParityB firstValue),
        zxpXorBAssoc (zxgParityB firstValue) true (zxgParityB secondPred)]

/-- Left commutation for Nat addition: `a + (b + c) = b + (a + c)`. -/
theorem zxgAddLeftComm (firstValue secondValue thirdValue : Nat) :
    firstValue + (secondValue + thirdValue) = secondValue + (firstValue + thirdValue) := by
  rw [<- Nat.add_assoc firstValue secondValue thirdValue,
    Nat.add_comm firstValue secondValue,
    Nat.add_assoc secondValue firstValue thirdValue]

/-- Medial exchange for Nat addition: `(a+b)+(c+d) = (a+c)+(b+d)`. -/
theorem zxgAddMedial (firstValue secondValue thirdValue fourthValue : Nat) :
    (firstValue + secondValue) + (thirdValue + fourthValue)
      = (firstValue + thirdValue) + (secondValue + fourthValue) := by
  rw [Nat.add_assoc firstValue secondValue (thirdValue + fourthValue),
    zxgAddLeftComm secondValue thirdValue fourthValue,
    <- Nat.add_assoc firstValue thirdValue (secondValue + fourthValue)]

/-! ## Stage 1 — the generic cell-weight fold engine

One engine decides the whole preserved-functional question: ANY per-cell Nat weight that
(i) vanishes on the wire cell and (ii) balances every published row is a full `ZxpConv`
invariant.  (i) kills the whisker/split wire bookkeeping; the context layers of a padded
step are identical on both sides and cancel in the equality. -/

/-- Sum a per-cell weight over one layer. -/
def zxgCellFold (cellWeight : ZxpCell -> Nat) : List ZxpCell -> Nat
  | [] => 0
  | headCell :: restCells => cellWeight headCell + zxgCellFold cellWeight restCells

/-- Sum a per-cell weight over a layer list. -/
def zxgLayersFold (cellWeight : ZxpCell -> Nat) : List (List ZxpCell) -> Nat
  | [] => 0
  | headLayer :: restLayers =>
      zxgCellFold cellWeight headLayer + zxgLayersFold cellWeight restLayers

/-- Sum a per-cell weight over a whole diagram. -/
def zxgDiagramFold (cellWeight : ZxpCell -> Nat) (diagram : ZxpDiagram) : Nat :=
  zxgLayersFold cellWeight diagram.layers

/-- Cell folds split across cell-list concatenation. -/
theorem zxgCellFoldCat (cellWeight : ZxpCell -> Nat) :
    (firstCells secondCells : List ZxpCell) ->
    zxgCellFold cellWeight (zxpCatCells firstCells secondCells)
      = zxgCellFold cellWeight firstCells + zxgCellFold cellWeight secondCells
  | [], secondCells => (Nat.zero_add (zxgCellFold cellWeight secondCells)).symm
  | headCell :: restCells, secondCells => by
      show cellWeight headCell + zxgCellFold cellWeight (zxpCatCells restCells secondCells)
        = (cellWeight headCell + zxgCellFold cellWeight restCells)
          + zxgCellFold cellWeight secondCells
      rw [zxgCellFoldCat cellWeight restCells secondCells]
      exact (Nat.add_assoc (cellWeight headCell) (zxgCellFold cellWeight restCells)
        (zxgCellFold cellWeight secondCells)).symm

/-- A wire-vanishing weight sums to zero over any wire layer. -/
theorem zxgCellFoldWires (cellWeight : ZxpCell -> Nat)
    (hWireZero : cellWeight ZxpCell.wire = 0) :
    (strandCount : Nat) -> zxgCellFold cellWeight (zxpWireCells strandCount) = 0
  | 0 => rfl
  | strandPred + 1 => by
      show cellWeight ZxpCell.wire + zxgCellFold cellWeight (zxpWireCells strandPred) = 0
      rw [hWireZero, zxgCellFoldWires cellWeight hWireZero strandPred]

/-- Whiskering one layer with wires does not change a wire-vanishing fold. -/
theorem zxgCellFoldWhiskerLayer (cellWeight : ZxpCell -> Nat)
    (hWireZero : cellWeight ZxpCell.wire = 0) (leftWires rightWires : Nat)
    (layer : List ZxpCell) :
    zxgCellFold cellWeight (zxpWhiskerLayer leftWires rightWires layer)
      = zxgCellFold cellWeight layer := by
  show zxgCellFold cellWeight (zxpCatCells (zxpWireCells leftWires)
      (zxpCatCells layer (zxpWireCells rightWires)))
    = zxgCellFold cellWeight layer
  rw [zxgCellFoldCat cellWeight (zxpWireCells leftWires)
      (zxpCatCells layer (zxpWireCells rightWires)),
    zxgCellFoldCat cellWeight layer (zxpWireCells rightWires),
    zxgCellFoldWires cellWeight hWireZero leftWires,
    zxgCellFoldWires cellWeight hWireZero rightWires,
    Nat.add_zero (zxgCellFold cellWeight layer),
    Nat.zero_add (zxgCellFold cellWeight layer)]

/-- Whiskering a whole window does not change a wire-vanishing fold. -/
theorem zxgLayersFoldWhisker (cellWeight : ZxpCell -> Nat)
    (hWireZero : cellWeight ZxpCell.wire = 0) (leftWires rightWires : Nat) :
    (layers : List (List ZxpCell)) ->
    zxgLayersFold cellWeight (zxpWhiskerLayers leftWires rightWires layers)
      = zxgLayersFold cellWeight layers
  | [] => rfl
  | layer :: restLayers => by
      show zxgCellFold cellWeight (zxpWhiskerLayer leftWires rightWires layer)
          + zxgLayersFold cellWeight (zxpWhiskerLayers leftWires rightWires restLayers)
        = zxgCellFold cellWeight layer + zxgLayersFold cellWeight restLayers
      rw [zxgCellFoldWhiskerLayer cellWeight hWireZero leftWires rightWires layer,
        zxgLayersFoldWhisker cellWeight hWireZero leftWires rightWires restLayers]

/-- Layer folds split across layer-list concatenation. -/
theorem zxgLayersFoldCat (cellWeight : ZxpCell -> Nat) :
    (firstLayers secondLayers : List (List ZxpCell)) ->
    zxgLayersFold cellWeight (zxpCatLayers firstLayers secondLayers)
      = zxgLayersFold cellWeight firstLayers + zxgLayersFold cellWeight secondLayers
  | [], secondLayers => (Nat.zero_add (zxgLayersFold cellWeight secondLayers)).symm
  | headLayer :: restLayers, secondLayers => by
      show zxgCellFold cellWeight headLayer
          + zxgLayersFold cellWeight (zxpCatLayers restLayers secondLayers)
        = (zxgCellFold cellWeight headLayer + zxgLayersFold cellWeight restLayers)
          + zxgLayersFold cellWeight secondLayers
      rw [zxgLayersFoldCat cellWeight restLayers secondLayers]
      exact (Nat.add_assoc (zxgCellFold cellWeight headLayer)
        (zxgLayersFold cellWeight restLayers)
        (zxgLayersFold cellWeight secondLayers)).symm

/-- Fold decomposition of the pad combinator: context plus the bare window. -/
theorem zxgDiagramFoldPad (cellWeight : ZxpCell -> Nat)
    (hWireZero : cellWeight ZxpCell.wire = 0)
    (contextSource leftWires rightWires : Nat)
    (beforeLayers afterLayers : List (List ZxpCell)) (window : ZxpDiagram) :
    zxgDiagramFold cellWeight
        (zxpPadDiagram contextSource leftWires rightWires beforeLayers afterLayers window)
      = zxgLayersFold cellWeight beforeLayers
          + (zxgLayersFold cellWeight window.layers
            + zxgLayersFold cellWeight afterLayers) := by
  show zxgLayersFold cellWeight (zxpCatLayers beforeLayers
      (zxpCatLayers (zxpWhiskerLayers leftWires rightWires window.layers) afterLayers))
    = zxgLayersFold cellWeight beforeLayers
        + (zxgLayersFold cellWeight window.layers
          + zxgLayersFold cellWeight afterLayers)
  rw [zxgLayersFoldCat cellWeight beforeLayers
      (zxpCatLayers (zxpWhiskerLayers leftWires rightWires window.layers) afterLayers),
    zxgLayersFoldCat cellWeight (zxpWhiskerLayers leftWires rightWires window.layers)
      afterLayers,
    zxgLayersFoldWhisker cellWeight hWireZero leftWires rightWires window.layers]

/-- The layer-split move preserves every wire-vanishing fold. -/
theorem zxgSplitLayerFoldEq (cellWeight : ZxpCell -> Nat)
    (hWireZero : cellWeight ZxpCell.wire = 0) (leftCells rightCells : List ZxpCell) :
    zxgLayersFold cellWeight [zxpCatCells leftCells rightCells]
      = zxgLayersFold cellWeight
          [zxpCatCells leftCells (zxpWireCells (zxpLayerDomArity rightCells)),
            zxpCatCells (zxpWireCells (zxpLayerCodArity leftCells)) rightCells] := by
  show zxgCellFold cellWeight (zxpCatCells leftCells rightCells) + 0
    = zxgCellFold cellWeight
        (zxpCatCells leftCells (zxpWireCells (zxpLayerDomArity rightCells)))
      + (zxgCellFold cellWeight
          (zxpCatCells (zxpWireCells (zxpLayerCodArity leftCells)) rightCells) + 0)
  rw [zxgCellFoldCat cellWeight leftCells rightCells,
    zxgCellFoldCat cellWeight leftCells (zxpWireCells (zxpLayerDomArity rightCells)),
    zxgCellFoldCat cellWeight (zxpWireCells (zxpLayerCodArity leftCells)) rightCells,
    zxgCellFoldWires cellWeight hWireZero (zxpLayerDomArity rightCells),
    zxgCellFoldWires cellWeight hWireZero (zxpLayerCodArity leftCells),
    Nat.zero_add (zxgCellFold cellWeight rightCells),
    Nat.add_zero (zxgCellFold cellWeight leftCells),
    Nat.add_zero (zxgCellFold cellWeight rightCells),
    Nat.add_zero (zxgCellFold cellWeight leftCells + zxgCellFold cellWeight rightCells)]

/-- Row balance of a weight: every published row has equal lhs/rhs fold. -/
def ZxgRowBalancedWeight (cellWeight : ZxpCell -> Nat) : Prop :=
  (tag : ZxpRowTag) ->
    zxgLayersFold cellWeight (zxpRowLhs tag).layers
      = zxgLayersFold cellWeight (zxpRowRhs tag).layers

/-- INVARIANCE, window level: a wire-vanishing row-balanced weight is preserved by every
window move (rows by hypothesis; the split by the wire algebra). -/
theorem zxgWindowMoveFoldEq (cellWeight : ZxpCell -> Nat)
    (hWireZero : cellWeight ZxpCell.wire = 0)
    (hRowsBalanced : ZxgRowBalancedWeight cellWeight)
    {firstWindow secondWindow : ZxpDiagram}
    (hMove : ZxpWindowMove firstWindow secondWindow) :
    zxgLayersFold cellWeight firstWindow.layers
      = zxgLayersFold cellWeight secondWindow.layers := by
  cases hMove with
  | row tag => exact hRowsBalanced tag
  | splitLayer leftCells rightCells =>
      exact zxgSplitLayerFoldEq cellWeight hWireZero leftCells rightCells

/-- INVARIANCE, step level: the padded contexts are identical on both sides and cancel. -/
theorem zxgStepFoldEq (cellWeight : ZxpCell -> Nat)
    (hWireZero : cellWeight ZxpCell.wire = 0)
    (hRowsBalanced : ZxgRowBalancedWeight cellWeight)
    {firstDiagram secondDiagram : ZxpDiagram}
    (hStep : ZxpStep firstDiagram secondDiagram) :
    zxgDiagramFold cellWeight firstDiagram = zxgDiagramFold cellWeight secondDiagram := by
  cases hStep with
  | pad contextSource leftWires rightWires beforeLayers afterLayers hMove hBeforeWF
      hBeforeCod hAfterWF =>
      rename_i firstWindow secondWindow
      rw [zxgDiagramFoldPad cellWeight hWireZero contextSource leftWires rightWires
          beforeLayers afterLayers firstWindow,
        zxgDiagramFoldPad cellWeight hWireZero contextSource leftWires rightWires
          beforeLayers afterLayers secondWindow,
        zxgWindowMoveFoldEq cellWeight hWireZero hRowsBalanced hMove]

/-- INVARIANCE, full congruence: structural induction over EVERY `ZxpConv` constructor. -/
theorem zxgConvFoldEq (cellWeight : ZxpCell -> Nat)
    (hWireZero : cellWeight ZxpCell.wire = 0)
    (hRowsBalanced : ZxgRowBalancedWeight cellWeight)
    {firstDiagram secondDiagram : ZxpDiagram}
    (hConv : ZxpConv firstDiagram secondDiagram) :
    zxgDiagramFold cellWeight firstDiagram = zxgDiagramFold cellWeight secondDiagram := by
  induction hConv with
  | step hStep => exact zxgStepFoldEq cellWeight hWireZero hRowsBalanced hStep
  | refl diagram hWF => exact rfl
  | symm _hConv innerEq => exact innerEq.symm
  | trans _hFirst _hSecond firstEq secondEq => exact firstEq.trans secondEq

/-! ## Stage 2 — THE ROW-EFFECT DELTA TABLE over the base count vector

Components, in order: zSpider count, xSpider count, wire count, crossing count, layer
count, zSpider legs (arity-weighted), xSpider legs (arity-weighted). -/

/-- Indicator weight of Z spiders. -/
def zxgCellZCountWeight : ZxpCell -> Nat
  | ZxpCell.zSpider _domArity _codArity => 1
  | ZxpCell.xSpider _domArity _codArity => 0
  | ZxpCell.wire => 0
  | ZxpCell.crossing => 0

/-- Indicator weight of X spiders. -/
def zxgCellXCountWeight : ZxpCell -> Nat
  | ZxpCell.zSpider _domArity _codArity => 0
  | ZxpCell.xSpider _domArity _codArity => 1
  | ZxpCell.wire => 0
  | ZxpCell.crossing => 0

/-- Indicator weight of wire cells. -/
def zxgCellWireCountWeight : ZxpCell -> Nat
  | ZxpCell.zSpider _domArity _codArity => 0
  | ZxpCell.xSpider _domArity _codArity => 0
  | ZxpCell.wire => 1
  | ZxpCell.crossing => 0

/-- Indicator weight of crossing cells. -/
def zxgCellCrossCountWeight : ZxpCell -> Nat
  | ZxpCell.zSpider _domArity _codArity => 0
  | ZxpCell.xSpider _domArity _codArity => 0
  | ZxpCell.wire => 0
  | ZxpCell.crossing => 1

/-- Leg-weighted count of Z spiders. -/
def zxgCellZLegsWeight : ZxpCell -> Nat
  | ZxpCell.zSpider domArity codArity => domArity + codArity
  | ZxpCell.xSpider _domArity _codArity => 0
  | ZxpCell.wire => 0
  | ZxpCell.crossing => 0

/-- Leg-weighted count of X spiders. -/
def zxgCellXLegsWeight : ZxpCell -> Nat
  | ZxpCell.zSpider _domArity _codArity => 0
  | ZxpCell.xSpider domArity codArity => domArity + codArity
  | ZxpCell.wire => 0
  | ZxpCell.crossing => 0

/-- Number of layers of a layer list. -/
def zxgLayerCount : List (List ZxpCell) -> Nat
  | [] => 0
  | _headLayer :: restLayers => zxgLayerCount restLayers + 1

/-- The base count vector of a diagram (7 components, order fixed above). -/
def zxgCountVector (diagram : ZxpDiagram) : List Nat :=
  [zxgLayersFold zxgCellZCountWeight diagram.layers,
    zxgLayersFold zxgCellXCountWeight diagram.layers,
    zxgLayersFold zxgCellWireCountWeight diagram.layers,
    zxgLayersFold zxgCellCrossCountWeight diagram.layers,
    zxgLayerCount diagram.layers,
    zxgLayersFold zxgCellZLegsWeight diagram.layers,
    zxgLayersFold zxgCellXLegsWeight diagram.layers]

/-- Pointwise mod-2 difference of two count vectors. -/
def zxgVectorDeltaMod2 : List Nat -> List Nat -> List Bool
  | [], [] => []
  | [], _secondValue :: _secondRest => []
  | _firstValue :: _firstRest, [] => []
  | firstValue :: firstRest, secondValue :: secondRest =>
      zxpXorB (zxgParityB firstValue) (zxgParityB secondValue)
        :: zxgVectorDeltaMod2 firstRest secondRest

/-- The mod-2 delta of one published row on the base count vector. -/
def zxgRowDeltaMod2 (tag : ZxpRowTag) : List Bool :=
  zxgVectorDeltaMod2 (zxgCountVector (zxpRowLhs tag)) (zxgCountVector (zxpRowRhs tag))

/-- All 33 published row tags, in declaration order. -/
def zxgAllRowTags : List ZxpRowTag :=
  [ZxpRowTag.xMonoidAssoc, ZxpRowTag.xMonoidComm, ZxpRowTag.xMonoidUnit,
    ZxpRowTag.zComonoidCoassoc, ZxpRowTag.zComonoidCocomm, ZxpRowTag.zComonoidCounit,
    ZxpRowTag.zMonoidAssoc, ZxpRowTag.zMonoidComm, ZxpRowTag.zMonoidUnit,
    ZxpRowTag.xComonoidCoassoc, ZxpRowTag.xComonoidCocomm, ZxpRowTag.xComonoidCounit,
    ZxpRowTag.bialgCopyMult, ZxpRowTag.bialgSquare, ZxpRowTag.bialgUnitCopy,
    ZxpRowTag.bialgBone, ZxpRowTag.bialgCopyMultDual, ZxpRowTag.bialgSquareDual,
    ZxpRowTag.bialgUnitCopyDual, ZxpRowTag.bialgBoneDual, ZxpRowTag.hopf,
    ZxpRowTag.boneX, ZxpRowTag.boneZ, ZxpRowTag.frobeniusXLeft,
    ZxpRowTag.frobeniusXRight, ZxpRowTag.frobeniusZLeft, ZxpRowTag.frobeniusZRight,
    ZxpRowTag.specialZ, ZxpRowTag.specialX, ZxpRowTag.cupCoincide,
    ZxpRowTag.capCoincide, ZxpRowTag.zIdentitySpider, ZxpRowTag.xIdentitySpider]

/-- Map the delta computation over a tag list. -/
def zxgMapTagsToDeltas : List ZxpRowTag -> List (List Bool)
  | [] => []
  | headTag :: restTags => zxgRowDeltaMod2 headTag :: zxgMapTagsToDeltas restTags

/-- THE DELTA TABLE: the 33 rows' mod-2 deltas on the base count vector. -/
def zxgRowDeltaTable : List (List Bool) :=
  zxgMapTagsToDeltas zxgAllRowTags

/-- The delta table, kernel-computed to its explicit 33x7 literal.  Reading order of
components: [zCount, xCount, wireCount, crossingCount, layerCount, zLegs, xLegs]. -/
theorem zxgRowDeltaTableValue : zxgRowDeltaTable =
    [[false, false, false, false, false, false, false],
      [false, false, false, true, true, false, false],
      [false, false, false, false, true, false, false],
      [false, false, false, false, false, false, false],
      [false, false, false, true, true, false, false],
      [false, false, false, false, true, false, false],
      [false, false, false, false, false, false, false],
      [false, false, false, true, true, false, false],
      [false, false, false, false, true, false, false],
      [false, false, false, false, false, false, false],
      [false, false, false, true, true, false, false],
      [false, false, false, false, true, false, false],
      [true, true, false, false, true, true, true],
      [true, true, false, true, true, true, true],
      [true, true, false, false, true, true, true],
      [true, true, false, false, false, true, true],
      [true, true, false, false, true, true, true],
      [true, true, false, true, true, true, true],
      [true, true, false, false, true, true, true],
      [true, true, false, false, false, true, true],
      [false, false, false, false, false, false, false],
      [false, false, false, false, false, false, false],
      [false, false, false, false, false, false, false],
      [false, false, false, false, false, false, false],
      [false, false, false, false, false, false, false],
      [false, false, false, false, false, false, false],
      [false, false, false, false, false, false, false],
      [false, false, true, false, true, false, false],
      [false, false, true, false, true, false, false],
      [false, false, false, false, false, false, false],
      [false, false, false, false, false, false, false],
      [true, false, true, false, false, false, false],
      [false, true, true, false, false, false, false]] := rfl

/-- Mod-2 delta of one `splitLayer` window-move instance on the base count vector. -/
def zxgSplitWitnessDelta (leftCells rightCells : List ZxpCell) : List Bool :=
  zxgVectorDeltaMod2
    (zxgCountVector
      { sourceArity := zxpLayerDomArity leftCells + zxpLayerDomArity rightCells
        layers := [zxpCatCells leftCells rightCells] })
    (zxgCountVector
      { sourceArity := zxpLayerDomArity leftCells + zxpLayerDomArity rightCells
        layers := [zxpCatCells leftCells (zxpWireCells (zxpLayerDomArity rightCells)),
          zxpCatCells (zxpWireCells (zxpLayerCodArity leftCells)) rightCells] })

/-- Split witness with an odd wire delta (left cells = one wire). -/
def zxgSplitDeltaWitnessWire : List Bool :=
  zxgSplitWitnessDelta [ZxpCell.wire] []

/-- Split witness with an even wire delta (left cells = one crossing). -/
def zxgSplitDeltaWitnessCrossing : List Bool :=
  zxgSplitWitnessDelta [ZxpCell.crossing] []

theorem zxgSplitDeltaWitnessWireValue :
    zxgSplitDeltaWitnessWire = [false, false, true, false, true, false, false] := rfl

theorem zxgSplitDeltaWitnessCrossingValue :
    zxgSplitDeltaWitnessCrossing = [false, false, false, false, true, false, false] := rfl

/-- The full generator delta table: the 33 rows plus the two split witnesses.  (The
general `splitLayer` family only ever contributes vectors in span{wire, layer} — its
spider components cancel exactly, by `zxgSplitLayerFoldEq` applied to each spider weight
— so the two witnesses saturate its contribution to the mod-2 row space.) -/
def zxgFullDeltaTable : List (List Bool) :=
  zxpCatRows zxgRowDeltaTable [zxgSplitDeltaWitnessWire, zxgSplitDeltaWitnessCrossing]

/-- The computed row-space basis of the full delta table: all five plain counts move
independently, and the two leg columns move only TOGETHER. -/
def zxgDeltaSpanBasis : List (List Bool) :=
  [[true, false, false, false, false, false, false],
    [false, true, false, false, false, false, false],
    [false, false, true, false, false, false, false],
    [false, false, false, true, false, false, false],
    [false, false, false, false, true, false, false],
    [false, false, false, false, false, true, true]]

/-- KERNEL PIN: the delta row space is exactly the 6-dimensional basis span. -/
theorem zxgDeltaTableSpanBasisPin :
    zxpSpanEqB zxgFullDeltaTable zxgDeltaSpanBasis = true := rfl

/-- F2 dot product of two Bool vectors (truncating; widths match in all uses). -/
def zxgDotB : List Bool -> List Bool -> Bool
  | [], [] => false
  | [], _secondBit :: _secondRest => false
  | _firstBit :: _firstRest, [] => false
  | firstBit :: firstRest, secondBit :: secondRest =>
      zxpXorB (cond firstBit secondBit false) (zxgDotB firstRest secondRest)

/-- Is the functional orthogonal to every delta row? -/
def zxgIsOrthogonalToAllB (functional : List Bool) : List (List Bool) -> Bool
  | [] => true
  | headDelta :: restDeltas =>
      cond (zxgDotB functional headDelta) false
        (zxgIsOrthogonalToAllB functional restDeltas)

/-- Componentwise Bool-vector equality decision. -/
def zxgRowEqB : List Bool -> List Bool -> Bool
  | [], [] => true
  | [], _secondBit :: _secondRest => false
  | _firstBit :: _firstRest, [] => false
  | firstBit :: firstRest, secondBit :: secondRest =>
      cond (zxgBoolEqB firstBit secondBit) (zxgRowEqB firstRest secondRest) false

/-- Prepend a fixed bit to every vector of a list. -/
def zxgConsToAll (headBit : Bool) : List (List Bool) -> List (List Bool)
  | [] => []
  | headVector :: restVectors => (headBit :: headVector) :: zxgConsToAll headBit restVectors

/-- All `2 ^ length` Bool vectors of the given length. -/
def zxgAllBoolVectors : Nat -> List (List Bool)
  | 0 => [] :: []
  | lengthPred + 1 =>
      zxpCatRows (zxgConsToAll false (zxgAllBoolVectors lengthPred))
        (zxgConsToAll true (zxgAllBoolVectors lengthPred))

/-- The zero functional on the base count vector. -/
def zxgZeroFunctional : List Bool :=
  [false, false, false, false, false, false, false]

/-- The total-spider-legs-parity functional (the two leg columns together). -/
def zxgLegsParityFunctional : List Bool :=
  [false, false, false, false, false, true, true]

/-- Classifier: over the given candidate functionals, orthogonality to the full delta
table holds EXACTLY for the zero functional and the legs-parity functional. -/
def zxgIsPreservedExactlyLegsParityB : List (List Bool) -> Bool
  | [] => true
  | headFunctional :: restFunctionals =>
      cond (zxgBoolEqB (zxgIsOrthogonalToAllB headFunctional zxgFullDeltaTable)
          (cond (zxgRowEqB headFunctional zxgZeroFunctional) true
            (zxgRowEqB headFunctional zxgLegsParityFunctional)))
        (zxgIsPreservedExactlyLegsParityB restFunctionals) false

/-- KERNEL PIN: over ALL 128 mod-2 functionals on the base count vector, the preserved
lattice (orthogonal complement of the generator deltas) is exactly {0, legs-parity}. -/
theorem zxgPreservedLatticeClassified :
    zxgIsPreservedExactlyLegsParityB (zxgAllBoolVectors 7) = true := rfl

/-- Direct pin: the legs-parity functional is orthogonal to every generator delta. -/
theorem zxgLegsParityOrthogonalPin :
    zxgIsOrthogonalToAllB zxgLegsParityFunctional zxgFullDeltaTable = true := rfl

/-! ### The survivor is boundary-determined: total spider legs mod 2 = source + cod

So the ONLY preserved base functional carries no information beyond the boundary arities
(which `zxpConvSound` already preserves) — the base count space holds no separator. -/

/-- Combined spider-leg weight (both colours). -/
def zxgCellSpiderLegsWeight : ZxpCell -> Nat
  | ZxpCell.zSpider domArity codArity => domArity + codArity
  | ZxpCell.xSpider domArity codArity => domArity + codArity
  | ZxpCell.wire => 0
  | ZxpCell.crossing => 0

/-- Per cell, the combined leg weight is the sum of the two colour leg weights. -/
theorem zxgCellLegsWeightSplit : (cell : ZxpCell) ->
    zxgCellSpiderLegsWeight cell = zxgCellZLegsWeight cell + zxgCellXLegsWeight cell
  | ZxpCell.zSpider domArity codArity => (Nat.add_zero (domArity + codArity)).symm
  | ZxpCell.xSpider domArity codArity => (Nat.zero_add (domArity + codArity)).symm
  | ZxpCell.wire => rfl
  | ZxpCell.crossing => rfl

/-- Per layer, the combined leg fold is the sum of the two colour leg folds. -/
theorem zxgCellFoldLegsSplit : (cells : List ZxpCell) ->
    zxgCellFold zxgCellSpiderLegsWeight cells
      = zxgCellFold zxgCellZLegsWeight cells + zxgCellFold zxgCellXLegsWeight cells
  | [] => rfl
  | headCell :: restCells => by
      show zxgCellSpiderLegsWeight headCell + zxgCellFold zxgCellSpiderLegsWeight restCells
        = (zxgCellZLegsWeight headCell + zxgCellFold zxgCellZLegsWeight restCells)
          + (zxgCellXLegsWeight headCell + zxgCellFold zxgCellXLegsWeight restCells)
      rw [zxgCellLegsWeightSplit headCell, zxgCellFoldLegsSplit restCells]
      exact zxgAddMedial (zxgCellZLegsWeight headCell) (zxgCellXLegsWeight headCell)
        (zxgCellFold zxgCellZLegsWeight restCells)
        (zxgCellFold zxgCellXLegsWeight restCells)

/-- Per layer list, the combined leg fold is the sum of the two colour leg folds. -/
theorem zxgLayersFoldLegsSplit : (layers : List (List ZxpCell)) ->
    zxgLayersFold zxgCellSpiderLegsWeight layers
      = zxgLayersFold zxgCellZLegsWeight layers + zxgLayersFold zxgCellXLegsWeight layers
  | [] => rfl
  | headLayer :: restLayers => by
      show zxgCellFold zxgCellSpiderLegsWeight headLayer
          + zxgLayersFold zxgCellSpiderLegsWeight restLayers
        = (zxgCellFold zxgCellZLegsWeight headLayer
            + zxgLayersFold zxgCellZLegsWeight restLayers)
          + (zxgCellFold zxgCellXLegsWeight headLayer
            + zxgLayersFold zxgCellXLegsWeight restLayers)
      rw [zxgCellFoldLegsSplit headLayer, zxgLayersFoldLegsSplit restLayers]
      exact zxgAddMedial (zxgCellFold zxgCellZLegsWeight headLayer)
        (zxgCellFold zxgCellXLegsWeight headLayer)
        (zxgLayersFold zxgCellZLegsWeight restLayers)
        (zxgLayersFold zxgCellXLegsWeight restLayers)

/-- Per cell, leg parity equals boundary parity (wires and crossings have as many
domain as codomain legs; spiders carry their legs verbatim). -/
theorem zxgCellLegsParityBoundary : (cell : ZxpCell) ->
    zxgParityB (zxgCellSpiderLegsWeight cell)
      = zxpXorB (zxgParityB (zxpCellDomArity cell)) (zxgParityB (zxpCellCodArity cell))
  | ZxpCell.zSpider domArity codArity => zxgParityBAdd domArity codArity
  | ZxpCell.xSpider domArity codArity => zxgParityBAdd domArity codArity
  | ZxpCell.wire => rfl
  | ZxpCell.crossing => rfl

/-- Per layer, spider-leg parity equals the parity of dom + cod arity. -/
theorem zxgLayerLegsParityBoundary : (layer : List ZxpCell) ->
    zxgParityB (zxgCellFold zxgCellSpiderLegsWeight layer)
      = zxpXorB (zxgParityB (zxpLayerDomArity layer))
          (zxgParityB (zxpLayerCodArity layer))
  | [] => rfl
  | headCell :: restCells => by
      show zxgParityB (zxgCellSpiderLegsWeight headCell
          + zxgCellFold zxgCellSpiderLegsWeight restCells)
        = zxpXorB (zxgParityB (zxpCellDomArity headCell + zxpLayerDomArity restCells))
            (zxgParityB (zxpCellCodArity headCell + zxpLayerCodArity restCells))
      rw [zxgParityBAdd (zxgCellSpiderLegsWeight headCell)
          (zxgCellFold zxgCellSpiderLegsWeight restCells),
        zxgParityBAdd (zxpCellDomArity headCell) (zxpLayerDomArity restCells),
        zxgParityBAdd (zxpCellCodArity headCell) (zxpLayerCodArity restCells),
        zxgCellLegsParityBoundary headCell,
        zxgLayerLegsParityBoundary restCells]
      exact zxgXorBMedial (zxgParityB (zxpCellDomArity headCell))
        (zxgParityB (zxpCellCodArity headCell))
        (zxgParityB (zxpLayerDomArity restCells))
        (zxgParityB (zxpLayerCodArity restCells))

/-- Per well-formed layer list, spider-leg parity telescopes to source + cod parity. -/
theorem zxgLayersLegsParityBoundary : {currentArity : Nat} ->
    (layers : List (List ZxpCell)) -> ZxpLayersWF currentArity layers ->
    zxgParityB (zxgLayersFold zxgCellSpiderLegsWeight layers)
      = zxpXorB (zxgParityB currentArity)
          (zxgParityB (zxpLayersCodArity currentArity layers))
  | currentArity, [], _hWF => (zxpXorBSelf (zxgParityB currentArity)).symm
  | currentArity, layer :: restLayers, hWF => by
      cases hWF with
      | cons hDom hRest =>
          show zxgParityB (zxgCellFold zxgCellSpiderLegsWeight layer
              + zxgLayersFold zxgCellSpiderLegsWeight restLayers)
            = zxpXorB (zxgParityB currentArity)
                (zxgParityB (zxpLayersCodArity (zxpLayerCodArity layer) restLayers))
          rw [zxgParityBAdd (zxgCellFold zxgCellSpiderLegsWeight layer)
              (zxgLayersFold zxgCellSpiderLegsWeight restLayers),
            zxgLayerLegsParityBoundary layer, hDom,
            zxgLayersLegsParityBoundary restLayers hRest]
          exact zxgXorBCancelMiddle (zxgParityB currentArity)
            (zxgParityB (zxpLayerCodArity layer))
            (zxgParityB (zxpLayersCodArity (zxpLayerCodArity layer) restLayers))

/-- THE BASE-SPACE COLLAPSE: the sole surviving base functional (legs parity, i.e. the
xor of the two leg-column parities) is determined by the boundary arities alone on every
well-formed diagram — it separates nothing that the boundaries do not already separate. -/
theorem zxgLegsParityFunctionalBoundaryDetermined (diagram : ZxpDiagram)
    (hWF : ZxpDiagramWF diagram) :
    zxpXorB (zxgParityB (zxgLayersFold zxgCellZLegsWeight diagram.layers))
        (zxgParityB (zxgLayersFold zxgCellXLegsWeight diagram.layers))
      = zxpXorB (zxgParityB diagram.sourceArity)
          (zxgParityB (zxpDiagramCodArity diagram)) := by
  rw [<- zxgParityBAdd (zxgLayersFold zxgCellZLegsWeight diagram.layers)
      (zxgLayersFold zxgCellXLegsWeight diagram.layers),
    <- zxgLayersFoldLegsSplit diagram.layers]
  exact zxgLayersLegsParityBoundary diagram.layers hWF

/-! ## Stage 3 — THE SEPARATOR: the big-spider count refutes completeness

The arity-refined extension of the count vector: the indicator of spiders with >= 4
total legs.  It vanishes on every cell of every published row, on wires, and on
crossings — so it is row-balanced by 33 kernel decisions and wire-vanishing by `rfl`,
hence a full congruence invariant by the Stage-1 engine.  The seed's fusion pair
separates it while being span-equal, well-formed, and boundary-matched. -/

/-- Indicator weight of spiders with at least 4 total legs (either colour). -/
def zxgCellBigSpiderWeight : ZxpCell -> Nat
  | ZxpCell.zSpider domArity codArity => cond (zxpNatLe 4 (domArity + codArity)) 1 0
  | ZxpCell.xSpider domArity codArity => cond (zxpNatLe 4 (domArity + codArity)) 1 0
  | ZxpCell.wire => 0
  | ZxpCell.crossing => 0

/-- KERNEL DECISION x33: every published row is balanced for the big-spider count —
every cell either side of every row is a small spider, a wire, or a crossing. -/
theorem zxgBigSpiderRowBalanced : ZxgRowBalancedWeight zxgCellBigSpiderWeight
  | ZxpRowTag.xMonoidAssoc => rfl
  | ZxpRowTag.xMonoidComm => rfl
  | ZxpRowTag.xMonoidUnit => rfl
  | ZxpRowTag.zComonoidCoassoc => rfl
  | ZxpRowTag.zComonoidCocomm => rfl
  | ZxpRowTag.zComonoidCounit => rfl
  | ZxpRowTag.zMonoidAssoc => rfl
  | ZxpRowTag.zMonoidComm => rfl
  | ZxpRowTag.zMonoidUnit => rfl
  | ZxpRowTag.xComonoidCoassoc => rfl
  | ZxpRowTag.xComonoidCocomm => rfl
  | ZxpRowTag.xComonoidCounit => rfl
  | ZxpRowTag.bialgCopyMult => rfl
  | ZxpRowTag.bialgSquare => rfl
  | ZxpRowTag.bialgUnitCopy => rfl
  | ZxpRowTag.bialgBone => rfl
  | ZxpRowTag.bialgCopyMultDual => rfl
  | ZxpRowTag.bialgSquareDual => rfl
  | ZxpRowTag.bialgUnitCopyDual => rfl
  | ZxpRowTag.bialgBoneDual => rfl
  | ZxpRowTag.hopf => rfl
  | ZxpRowTag.boneX => rfl
  | ZxpRowTag.boneZ => rfl
  | ZxpRowTag.frobeniusXLeft => rfl
  | ZxpRowTag.frobeniusXRight => rfl
  | ZxpRowTag.frobeniusZLeft => rfl
  | ZxpRowTag.frobeniusZRight => rfl
  | ZxpRowTag.specialZ => rfl
  | ZxpRowTag.specialX => rfl
  | ZxpRowTag.cupCoincide => rfl
  | ZxpRowTag.capCoincide => rfl
  | ZxpRowTag.zIdentitySpider => rfl
  | ZxpRowTag.xIdentitySpider => rfl

/-- THE CONSERVED QUANTITY: the big-spider count is invariant under the FULL congruence
(every constructor: padded row steps, padded splits, refl, symm, trans). -/
theorem zxgConvBigSpiderCountEq {firstDiagram secondDiagram : ZxpDiagram}
    (hConv : ZxpConv firstDiagram secondDiagram) :
    zxgDiagramFold zxgCellBigSpiderWeight firstDiagram
      = zxgDiagramFold zxgCellBigSpiderWeight secondDiagram :=
  zxgConvFoldEq zxgCellBigSpiderWeight rfl zxgBigSpiderRowBalanced hConv

/-- Bool form of the invariant collision, for the refutation bridge. -/
theorem zxgConvBigSpiderCountEqB {firstDiagram secondDiagram : ZxpDiagram}
    (hConv : ZxpConv firstDiagram secondDiagram) :
    zxpNatEqB (zxgDiagramFold zxgCellBigSpiderWeight firstDiagram)
      (zxgDiagramFold zxgCellBigSpiderWeight secondDiagram) = true := by
  rw [zxgConvBigSpiderCountEq hConv]
  exact zxgNatEqBRefl (zxgDiagramFold zxgCellBigSpiderWeight secondDiagram)

/-! ### The separated pair: the seed's own fusion instance -/

/-- The fused triple [[zSpider 3 1]] contains exactly one big spider. -/
theorem zxgFusedTripleBigCountOne :
    zxgDiagramFold zxgCellBigSpiderWeight zxpZFusedTripleDiagram = 1 := rfl

/-- The chained pair [[zSpider 2 1, wire], [zSpider 2 1]] contains no big spider. -/
theorem zxgChainedPairBigCountZero :
    zxgDiagramFold zxgCellBigSpiderWeight zxpZChainedPairDiagram = 0 := rfl

/-- The two big-spider counts are distinct (kernel decision). -/
theorem zxgFusedChainedBigCountDistinctB :
    zxpNatEqB (zxgDiagramFold zxgCellBigSpiderWeight zxpZFusedTripleDiagram)
      (zxgDiagramFold zxgCellBigSpiderWeight zxpZChainedPairDiagram) = false := rfl

/-- The pair is span-equal in the fused -> chained orientation (kernel decision; the
seed fired the chained -> fused orientation as `zxpZFusionFire`). -/
theorem zxgFusedChainedSpanEqTrue :
    zxpSpanEqB (zxpDiagramDenote zxpZFusedTripleDiagram)
      (zxpDiagramDenote zxpZChainedPairDiagram) = true := rfl

/-- Executable well-formedness of the fused triple. -/
theorem zxgFusedTripleWFBTrue : zxpDiagramWFB zxpZFusedTripleDiagram = true := rfl

/-- Executable well-formedness of the chained pair. -/
theorem zxgChainedPairWFBTrue : zxpDiagramWFB zxpZChainedPairDiagram = true := rfl

/-- The pair shares its source arity (both 3). -/
theorem zxgFusedChainedSameSourcePin :
    zxpZFusedTripleDiagram.sourceArity = zxpZChainedPairDiagram.sourceArity := rfl

/-- The pair shares its target arity (both 1). -/
theorem zxgFusedChainedSameCodPin :
    zxpDiagramCodArity zxpZFusedTripleDiagram
      = zxpDiagramCodArity zxpZChainedPairDiagram := rfl

/-- THE SEPARATION: the span-equal, well-formed, boundary-matched fusion pair is NOT
convertible — the big-spider count blocks every derivation. -/
theorem zxgFusedChainedNotConv :
    Not (ZxpConv zxpZFusedTripleDiagram zxpZChainedPairDiagram) :=
  fun hConv =>
    Bool.noConfusion
      ((zxgConvBigSpiderCountEqB hConv).symm.trans zxgFusedChainedBigCountDistinctB)

/-- THE GATE VERDICT: `zxpCompletenessStatement` is FALSE as stated.  Instantiating it
at the fusion pair (span-equal by `zxgFusedChainedSpanEqTrue` through the seed's
soundness bridge, well-formed, boundary-matched) would produce a conversion that the
big-spider invariant forbids.  The missing-row defect is the arity-recursion spider
fusion family — see the header for the recorded repair options. -/
theorem zxgCompletenessRefuted : zxpCompletenessStatement -> False :=
  fun hCompleteness =>
    zxgFusedChainedNotConv
      (hCompleteness zxpZFusedTripleDiagram zxpZChainedPairDiagram
        (zxpDiagramWFOfB zxpZFusedTripleDiagram zxgFusedTripleWFBTrue)
        (zxpDiagramWFOfB zxpZChainedPairDiagram zxgChainedPairWFBTrue)
        zxgFusedChainedSameSourcePin
        zxgFusedChainedSameCodPin
        (zxpRelEquivOfSpanEqB
          (zxpDiagramDenoteWidth zxpZFusedTripleDiagram
            (zxpDiagramWFOfB zxpZFusedTripleDiagram zxgFusedTripleWFBTrue))
          (zxpDiagramDenoteWidth zxpZChainedPairDiagram
            (zxpDiagramWFOfB zxpZChainedPairDiagram zxgChainedPairWFBTrue))
          zxgFusedChainedSpanEqTrue))

/-! ## Stage 4 — the gate marker -/

/-- THE INVARIANT-FIRST GATE VERDICT: outcome (a), REFUTED.  `zxgCompletenessRefuted`
machine-derives `False` from `zxpCompletenessStatement`; the base-count delta table is
clean (Stage 2), and the separator is the arity-refined big-spider count (Stage 3).
`fxWpZx_hasCompleteness` stays false in the seed; any completeness push must first
repair the presentation per the header's (R1)/(R2). -/
def zxgGateVerdictIsRefuted : Bool := true

end FX1Poly.Polygraph.Omega.ZXPhaseFree
