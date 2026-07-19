import FX1Poly.Polygraph.Omega.ZXPhaseFree.SpiderRelationSeed
import FX1Poly.Polygraph.Omega.ZXPhaseFree.CompletenessGate
import FX1Poly.Polygraph.Omega.ZXPhaseFree.FusionRepair
import FX1Poly.Polygraph.Omega.ZXPhaseFree.NormalFormCensus
import FX1Poly.Polygraph.Omega.ZXPhaseFree.NormalFormLadder
import FX1Poly.Polygraph.Omega.ZXPhaseFree.ExchangeCompleteness
import FX1Poly.Polygraph.Omega.ZXPhaseFree.AbsorptionFlip

/-! # Polygraph/Omega/ZXPhaseFree/WiringFlip — THE WIRING SCHEMA: the symmetric
structure lands as gated window moves

The AbsorptionFlip round named THE WIRING WALL: the committed move set
`{rows, splitLayer, fusion, exchange}` does not present the free SYMMETRIC monoidal
structure on the generators — no committed move consumes a crossing whose two legs do
not both enter one spider (the one-legged configuration), and the two minimal blocked
instances (`zxaCounitSlideStatement`, `zxaSigmaInvolutionStatement`) were minted
owner-false with kernel span pins proving each is a semantically sound CANDIDATE MOVE.
This round executes the honest next move recorded there: the r30-style NEW MOVE
family.

## (A) THE WIRING MOVES — `ZxwConv`

`ZxwConv` = every `ZxeConv` move + the wiring schema as gated window moves:

* NATURALITY SLIDES (`ZxwWindowMove.slideRight/.slideLeft`): ONE passive strand
  crosses an ARBITRARY single cell (`zSpider a b` / `xSpider a b` / `wire` /
  `crossing`), both orientations.  The passive strand crosses the cell's whole
  output bundle as an adjacent-crossing STAIRCASE (`zxwStairFromRightLayers` /
  `zxwStairFromLeftLayers` — `cod` crossings on the lhs, `dom` crossings on the
  rhs), so the family is stated at ALL arities, not just the minimal instances:
  `[[cell, wire]] ; stairR(cod) ~ stairR(dom) ; [[wire, cell]]` and the left-side
  mirror.  The counit slide IS the `slideLeft (zSpider 1 0)` instance;
  Yang-Baxter IS the `slideLeft ZxpCell.crossing` instance (DERIVED, not
  primitive — checked and documented at `zxwYangBaxter`).
* SIGMA INVOLUTION (`ZxwWindowMove.sigmaInvolution`):
  `[[crossing],[crossing]] ~ [[wire, wire]]`, the other blocked minimal instance,
  soundness kernel-decided (closed diagrams).

SOUNDNESS IS STRUCTURAL AT ALL ARITIES: the staircase denotes the rotation
relation (`zxwStairFromRightPairIff` / `zxwStairFromLeftPairIff`, by induction on
the staircase through the census pair-level toolkit), the padded cell relates
blockwise (`zxnPadCellPairIff`), and both sides of each slide reduce to the same
canonical pair predicate GENERICALLY IN THE CELL'S RELATION (`zxwSlideRightBundle`
/ `zxwSlideLeftBundle`) — no per-arity kernel enumeration anywhere in the family.
The full embedding is `zxwOfZxeConv`; the fusion and leg-permutation engines
transport across it (`zxwParallelFusionZ/X`, `zxwMidMergeFuseZ/X`,
`zxwCrossingAbsorbInputZ/X`, `zxwWalkAbsorbOutputZ/X`, ...).

## (B) THE GATE RE-RUN over `ZxwConv` (arc law) — verdict CLEAN

Honest crossing-count analysis: THE SLIDES ARE **NOT** CROSSING-COUNT BALANCED —
`slideRight cell` trades the `cod cell` staircase crossings for `dom cell`
staircase crossings, so the crossing-count delta is `cod - dom` (the
`slideRight (zSpider 0 1)` instance creates a crossing from none:
`zxwCrossCountNotSlideBalanced`), and any wire-vanishing per-cell weight balanced
on the slide family is FORCED to vanish on the crossing
(`zxwSlideBalanceForcesCrossingZero` — kernel-honest, no hand-waving).  The
FusionRepair collapse therefore carries and STRENGTHENS: every `ZxwConv`-admissible
per-cell weight is identically zero (`zxwBalancedWeightCollapse`) — the whole
counting family, home of both prior refutations of this workstream, holds no
`ZxwConv` separator.  Base 7-vector mod-2 deltas: the general slide delta is
`[0,0,0, parity(dom+cod), parity(dom+cod), 0,0]` (`zxwSlideRightDeltaGeneral` /
`zxwSlideLeftDeltaGeneral`, saturated by two literals via the case lemmas), the
involution delta is the layer-parity literal — ALL inside the gate's committed
6-dimensional span (`zxwExtendedDeltaSpanBasisPin`), the 128-functional lattice is
still exactly {0, legs-parity} (`zxwPreservedLatticeReclassified`), the survivor
is boundary-determined (gate theorem, untouched) and orthogonal to every slide
delta at every arity (`zxwLegsParityOrthogonalSlideDelta`).  The refutation
instrument survives: `zxwBigColourNotConv`.  Verdict marker:
`zxwGateVerdictIsClean := true`.

## (C) THE DERIVED SYMMETRIC STRUCTURE

* The wall's exact demanded instances, now DERIVED over `ZxwConv`:
  `zxwCounitSlideZ` (byte-shape of `zxaCounitSlideStatement`, whose `ZxeConv`
  original stays owner-false and byte-intact in its home file), the X mirror, the
  unit-side mirrors, and `zxwSigmaInvolutionFire` (byte-shape of
  `zxaSigmaInvolutionStatement`).
* YANG-BAXTER DERIVES: `zxwYangBaxter` is literally the `slideLeft crossing`
  instance of the naturality family — no separate YB axiom is needed (documented
  check demanded by the commission).
* CROSSING-BLOCK ROUTING: disjoint side-by-side blocks commute
  (`zxwLayerPastRightLayers` / `zxwLayersPastRightLayer` — over `ZxeConv`
  already, by merge/re-split chains), the staircase splits into whiskered
  staircase blocks (`zxwStairFromRightSplit`), and THE LAYER SLIDE
  (`zxwLayerSlideFromRight`): one passive strand routes past an ARBITRARY layer
  (any cell list), by induction on the layer through the primitive cell slides —
  any block of adjacent crossings generated this way routes whole layers.

## (D) THE ABSORPTION + THE FLIP — honest partial

`zxwAbsorptionStatement` (every WF diagram `ZxwConv`-converts to `zxnNormalForm`
of its own denotation) and `zxwCompletenessStatement` (the exact prior shape with
the `ZxwConv` conclusion) are MINTED; the zero-generator instances land
transported (`zxwEmptyDiagramAbsorbed`, `zxwKillCreateAbsorbedFire`), and the
conditional decision corollary is in place (`zxwDecisionUnderCompleteness`).
NOT PROVEN this round (owner false, `zxwAbsorptionIsProven := false`,
`zxwCompletenessIsProven := false`, `zxwHasFullDecision := false`): the wiring
wall itself is GONE (every one-legged configuration in the normal-form carrier is
now derivable — the exact blocking configuration of the prior round dissolves
into the slide family), and what remains is the per-cell absorption bookkeeping
into `zxnNormalForm` (composite-generator-matrix transport per absorbed cell) plus
the generator-list transport lemma (span-equal generator lists give convertible
normal forms).  That is engineering on an UNBLOCKED route, recorded precisely at
the markers; committed owners stay byte-intact.

Raw Lean 4 + Init only; zero-axiom; structural recursion only; no `List.append`,
no `Int`, no `Nat.sub/div/mod/min/max`, no wildcard match arms over inductive
scrutinees. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace FX1Poly.Polygraph.Omega.ZXPhaseFree

/-! ## Stage 0 — the adjacent-crossing staircases

`zxwStairFromRightLayers n` acts on `n + 1` strands and routes the LAST strand to
the FRONT through `n` adjacent crossings (one per layer, positions `n-1` down to
`0`); `zxwStairFromLeftLayers n` routes the FIRST strand of `1 + n` to the BACK.
Both are built by cons plus the seed's whisker combinator, so every committed
whisker lemma applies. -/

/-- Staircase routing the last of `stepCount + 1` strands to the front. -/
def zxwStairFromRightLayers : Nat -> List (List ZxpCell)
  | 0 => []
  | stepPred + 1 =>
      zxpCatCells (zxpWireCells stepPred) [ZxpCell.crossing]
        :: zxpWhiskerLayers 0 1 (zxwStairFromRightLayers stepPred)

/-- Staircase routing the first of `1 + stepCount` strands to the back. -/
def zxwStairFromLeftLayers : Nat -> List (List ZxpCell)
  | 0 => []
  | stepPred + 1 =>
      (ZxpCell.crossing :: zxpWireCells stepPred)
        :: zxpWhiskerLayers 1 0 (zxwStairFromLeftLayers stepPred)

/-- `1 + (1 + n) = 2 + n` (right-associated two-step head). -/
theorem zxwOnePlusOnePlus (anyCount : Nat) : 1 + (1 + anyCount) = 2 + anyCount :=
  (Nat.add_assoc 1 1 anyCount).symm

theorem zxwWiresCrossingDomArity (frontWires : Nat) :
    zxpLayerDomArity (zxpCatCells (zxpWireCells frontWires) [ZxpCell.crossing])
      = frontWires + 2 := by
  rw [zxpCatCellsDomArity, zxpWireCellsDomArity]
  exact rfl

theorem zxwWiresCrossingCodArity (frontWires : Nat) :
    zxpLayerCodArity (zxpCatCells (zxpWireCells frontWires) [ZxpCell.crossing])
      = frontWires + 2 := by
  rw [zxpCatCellsCodArity, zxpWireCellsCodArity]
  exact rfl

theorem zxwCrossingWiresDomArity (tailWires : Nat) :
    zxpLayerDomArity (ZxpCell.crossing :: zxpWireCells tailWires) = 2 + tailWires := by
  show zxpCellDomArity ZxpCell.crossing + zxpLayerDomArity (zxpWireCells tailWires)
    = 2 + tailWires
  rw [zxpWireCellsDomArity]
  exact rfl

theorem zxwCrossingWiresCodArity (tailWires : Nat) :
    zxpLayerCodArity (ZxpCell.crossing :: zxpWireCells tailWires) = 2 + tailWires := by
  show zxpCellCodArity ZxpCell.crossing + zxpLayerCodArity (zxpWireCells tailWires)
    = 2 + tailWires
  rw [zxpWireCellsCodArity]
  exact rfl

theorem zxwStairFromRightWF : (stepCount : Nat) ->
    ZxpLayersWF (stepCount + 1) (zxwStairFromRightLayers stepCount)
  | 0 => ZxpLayersWF.nil 1
  | stepPred + 1 => by
      refine ZxpLayersWF.cons (zxwWiresCrossingDomArity stepPred) ?_
      have hCodHead : zxpLayerCodArity
          (zxpCatCells (zxpWireCells stepPred) [ZxpCell.crossing])
          = 0 + ((stepPred + 1) + 1) :=
        (zxwWiresCrossingCodArity stepPred).trans
          (Nat.zero_add ((stepPred + 1) + 1)).symm
      rw [hCodHead]
      exact zxpWhiskerLayersWF 0 1 (zxwStairFromRightLayers stepPred)
        (zxwStairFromRightWF stepPred)

theorem zxwStairFromLeftWF : (stepCount : Nat) ->
    ZxpLayersWF (1 + stepCount) (zxwStairFromLeftLayers stepCount)
  | 0 => ZxpLayersWF.nil (1 + 0)
  | stepPred + 1 => by
      refine ZxpLayersWF.cons
        ((zxwCrossingWiresDomArity stepPred).trans
          (zxnTwoPlusEqOnePlusSucc stepPred)) ?_
      have hCodHead : zxpLayerCodArity
          (ZxpCell.crossing :: zxpWireCells stepPred)
          = 1 + ((1 + stepPred) + 0) :=
        (zxwCrossingWiresCodArity stepPred).trans
          ((zxwOnePlusOnePlus stepPred).symm.trans
            (congrArg (fun innerValue => 1 + innerValue)
              (Nat.add_zero (1 + stepPred)).symm))
      rw [hCodHead]
      exact zxpWhiskerLayersWF 1 0 (zxwStairFromLeftLayers stepPred)
        (zxwStairFromLeftWF stepPred)

theorem zxwStairFromRightCodArity : (stepCount : Nat) ->
    zxpLayersCodArity (stepCount + 1) (zxwStairFromRightLayers stepCount)
      = 1 + stepCount
  | 0 => rfl
  | stepPred + 1 => by
      show zxpLayersCodArity
          (zxpLayerCodArity (zxpCatCells (zxpWireCells stepPred) [ZxpCell.crossing]))
          (zxpWhiskerLayers 0 1 (zxwStairFromRightLayers stepPred))
        = 1 + (stepPred + 1)
      have hCodHead : zxpLayerCodArity
          (zxpCatCells (zxpWireCells stepPred) [ZxpCell.crossing])
          = 0 + ((stepPred + 1) + 1) :=
        (zxwWiresCrossingCodArity stepPred).trans
          (Nat.zero_add ((stepPred + 1) + 1)).symm
      rw [hCodHead,
        zxpWhiskerLayersCodArity 0 1 (zxwStairFromRightLayers stepPred) (stepPred + 1),
        zxwStairFromRightCodArity stepPred, Nat.zero_add]
      exact Nat.add_assoc 1 stepPred 1

theorem zxwStairFromLeftCodArity : (stepCount : Nat) ->
    zxpLayersCodArity (1 + stepCount) (zxwStairFromLeftLayers stepCount)
      = stepCount + 1
  | 0 => rfl
  | stepPred + 1 => by
      show zxpLayersCodArity
          (zxpLayerCodArity (ZxpCell.crossing :: zxpWireCells stepPred))
          (zxpWhiskerLayers 1 0 (zxwStairFromLeftLayers stepPred))
        = (stepPred + 1) + 1
      have hCodHead : zxpLayerCodArity
          (ZxpCell.crossing :: zxpWireCells stepPred)
          = 1 + ((1 + stepPred) + 0) :=
        (zxwCrossingWiresCodArity stepPred).trans
          ((zxwOnePlusOnePlus stepPred).symm.trans
            (congrArg (fun innerValue => 1 + innerValue)
              (Nat.add_zero (1 + stepPred)).symm))
      rw [hCodHead,
        zxpWhiskerLayersCodArity 1 0 (zxwStairFromLeftLayers stepPred) (1 + stepPred),
        zxwStairFromLeftCodArity stepPred, Nat.add_zero]
      exact Nat.add_comm 1 (stepPred + 1)

/-! ## Stage 1 — the whiskered-window pair characterization

The census shipped the padded-CELL workhorse; the staircases and the slide proofs
need the same characterization for a whiskered LAYER LIST: the whiskered window
relates exactly the vectors that agree on the pass strands and relate through the
window inside.  Same proof skeleton as `zxnPadCellPairIff` (whisker denotation +
tensor spec + identity spec), stated once and specialized by boundary equations. -/

theorem zxwWhiskerLayersPairIff (leftWires rightWires : Nat)
    (windowLayers : List (List ZxpCell)) (entryArity : Nat)
    (hWindowWF : ZxpLayersWF entryArity windowLayers) (domVec codVec : List Bool) :
    ZxpPairMem (leftWires + (entryArity + rightWires))
        (leftWires + (zxpLayersCodArity entryArity windowLayers + rightWires))
        (zxpLayersDenote (leftWires + (entryArity + rightWires))
          (zxpWhiskerLayers leftWires rightWires windowLayers)) domVec codVec
      <-> Exists fun passVec => Exists fun innerDomVec => Exists fun sideVec =>
          Exists fun innerCodVec =>
          domVec = zxpCat passVec (zxpCat innerDomVec sideVec)
            /\ codVec = zxpCat passVec (zxpCat innerCodVec sideVec)
            /\ passVec.length = leftWires
            /\ sideVec.length = rightWires
            /\ ZxpPairMem entryArity (zxpLayersCodArity entryArity windowLayers)
                (zxpLayersDenote entryArity windowLayers) innerDomVec innerCodVec := by
  have hWindowAll := zxpLayersDenoteWidth windowLayers hWindowWF
  have hInnerAll : ZxpAllWidth
      ((entryArity + rightWires)
        + (zxpLayersCodArity entryArity windowLayers + rightWires))
      (zxpTensorRows entryArity (zxpLayersCodArity entryArity windowLayers)
        rightWires rightWires (zxpLayersDenote entryArity windowLayers)
        (zxpIdRows rightWires)) :=
    zxpTensorRowsWidth entryArity (zxpLayersCodArity entryArity windowLayers)
      rightWires rightWires (zxpLayersDenote entryArity windowLayers)
      (zxpIdRows rightWires) hWindowAll (zxpIdRowsWidth rightWires)
  refine Iff.trans
    (zxpWhiskerLayersDenote leftWires rightWires windowLayers hWindowWF
      domVec codVec) ?_
  refine Iff.trans (zxpTensorSpec leftWires leftWires
    (entryArity + rightWires)
    (zxpLayersCodArity entryArity windowLayers + rightWires)
    (zxpIdRows leftWires)
    (zxpTensorRows entryArity (zxpLayersCodArity entryArity windowLayers)
      rightWires rightWires (zxpLayersDenote entryArity windowLayers)
      (zxpIdRows rightWires))
    (zxpIdRowsWidth leftWires) hInnerAll domVec codVec) ?_
  refine Iff.intro ?_ ?_
  · intro hPacked
    obtain ⟨passDomVec, restDomVec, passCodVec, restCodVec,
      hDomCat, hCodCat, hPassPair, hRestPair⟩ := hPacked
    have hPassSame := (zxpIdSpec leftWires passDomVec passCodVec).mp hPassPair
    have hRest := (zxpTensorSpec entryArity
      (zxpLayersCodArity entryArity windowLayers) rightWires rightWires
      (zxpLayersDenote entryArity windowLayers) (zxpIdRows rightWires)
      hWindowAll (zxpIdRowsWidth rightWires) restDomVec restCodVec).mp hRestPair
    obtain ⟨innerDomVec, sideDomVec, innerCodVec, sideCodVec,
      hRestDomCat, hRestCodCat, hInnerPair, hSidePair⟩ := hRest
    have hSideSame := (zxpIdSpec rightWires sideDomVec sideCodVec).mp hSidePair
    refine Exists.intro passDomVec (Exists.intro innerDomVec
      (Exists.intro sideDomVec (Exists.intro innerCodVec
        (And.intro ?_ (And.intro ?_ (And.intro hPassSame.right
          (And.intro ?_ hInnerPair)))))))
    · rw [hDomCat, hRestDomCat]
    · rw [hCodCat, hRestCodCat, <- hPassSame.left, <- hSideSame.left]
    · exact hSideSame.right
  · intro hPacked
    obtain ⟨passVec, innerDomVec, sideVec, innerCodVec,
      hDomEq, hCodEq, hPassLen, hSideLen, hInnerPair⟩ := hPacked
    refine Exists.intro passVec (Exists.intro (zxpCat innerDomVec sideVec)
      (Exists.intro passVec (Exists.intro (zxpCat innerCodVec sideVec)
        (And.intro hDomEq (And.intro hCodEq (And.intro ?_ ?_))))))
    · exact (zxpIdSpec leftWires passVec passVec).mpr (And.intro rfl hPassLen)
    · refine (zxpTensorSpec entryArity
        (zxpLayersCodArity entryArity windowLayers) rightWires rightWires
        (zxpLayersDenote entryArity windowLayers) (zxpIdRows rightWires)
        hWindowAll (zxpIdRowsWidth rightWires)
        (zxpCat innerDomVec sideVec) (zxpCat innerCodVec sideVec)).mpr ?_
      refine Exists.intro innerDomVec (Exists.intro sideVec
        (Exists.intro innerCodVec (Exists.intro sideVec
          (And.intro rfl (And.intro rfl (And.intro hInnerPair ?_))))))
      exact (zxpIdSpec rightWires sideVec sideVec).mpr (And.intro rfl hSideLen)

/-- The whiskered-window workhorse with all four boundary arities supplied by
equations. -/
theorem zxwWhiskerLayersPairIffAt (leftWires rightWires : Nat)
    (windowLayers : List (List ZxpCell)) (entryArity exitArity : Nat)
    (currentArity nextArity : Nat)
    (hWindowWF : ZxpLayersWF entryArity windowLayers)
    (hExit : zxpLayersCodArity entryArity windowLayers = exitArity)
    (hDomEq : leftWires + (entryArity + rightWires) = currentArity)
    (hCodEq : leftWires + (exitArity + rightWires) = nextArity)
    (domVec codVec : List Bool) :
    ZxpPairMem currentArity nextArity
        (zxpLayersDenote currentArity
          (zxpWhiskerLayers leftWires rightWires windowLayers)) domVec codVec
      <-> Exists fun passVec => Exists fun innerDomVec => Exists fun sideVec =>
          Exists fun innerCodVec =>
          domVec = zxpCat passVec (zxpCat innerDomVec sideVec)
            /\ codVec = zxpCat passVec (zxpCat innerCodVec sideVec)
            /\ passVec.length = leftWires
            /\ sideVec.length = rightWires
            /\ ZxpPairMem entryArity exitArity
                (zxpLayersDenote entryArity windowLayers) innerDomVec innerCodVec := by
  subst hExit
  subst hDomEq
  subst hCodEq
  exact zxwWhiskerLayersPairIff leftWires rightWires windowLayers entryArity
    hWindowWF domVec codVec

/-! ## Stage 2 — the staircase pair characterizations (the rotation relations) -/

/-- A row of length `n + 1` splits as `front ++ [lastBit]` with `front` of
length `n`. -/
theorem zxwSnocSplit : (row : List Bool) -> (frontLength : Nat) ->
    row.length = frontLength + 1 ->
    Exists fun frontRow => Exists fun lastBit =>
      row = zxpCat frontRow [lastBit] /\ frontRow.length = frontLength
  | [], _frontLength, hLen => nomatch hLen
  | headBit :: restBits, 0, hLen => by
      have hRestNil : restBits = [] := zxpLengthZeroNil restBits (Nat.succ.inj hLen)
      refine Exists.intro [] (Exists.intro headBit (And.intro ?_ rfl))
      rw [hRestNil]
      exact rfl
  | headBit :: restBits, frontPred + 1, hLen => by
      obtain ⟨innerFront, innerLast, hInnerEq, hInnerLen⟩ :=
        zxwSnocSplit restBits frontPred (Nat.succ.inj hLen)
      refine Exists.intro (headBit :: innerFront) (Exists.intro innerLast
        (And.intro ?_ ?_))
      · show headBit :: restBits = headBit :: zxpCat innerFront [innerLast]
        rw [hInnerEq]
      · show innerFront.length + 1 = frontPred + 1
        rw [hInnerLen]

/-- THE RIGHT STAIRCASE ROTATION: `zxwStairFromRightLayers n` relates exactly
`front ++ [t]  |->  t :: front`. -/
theorem zxwStairFromRightPairIff : (stepCount : Nat) -> (domVec codVec : List Bool) ->
    (ZxpPairMem (stepCount + 1) (1 + stepCount)
        (zxpLayersDenote (stepCount + 1) (zxwStairFromRightLayers stepCount))
        domVec codVec
      <-> Exists fun frontRow => Exists fun lastBit =>
          domVec = zxpCat frontRow [lastBit] /\ frontRow.length = stepCount
            /\ codVec = lastBit :: frontRow)
  | 0, domVec, codVec => by
      refine Iff.trans (zxpIdSpec 1 domVec codVec) ?_
      refine Iff.intro ?_ ?_
      · intro hSame
        obtain ⟨onlyBit, hShape⟩ := zxnLengthOneShape domVec hSame.right
        refine Exists.intro [] (Exists.intro onlyBit (And.intro ?_
          (And.intro rfl ?_)))
        · rw [hShape]
          exact rfl
        · rw [<- hSame.left, hShape]
      · intro hPacked
        obtain ⟨frontRow, lastBit, hDomEq, hFrontLen, hCodEq⟩ := hPacked
        have hFrontNil : frontRow = [] := zxpLengthZeroNil frontRow hFrontLen
        rw [hDomEq, hCodEq, hFrontNil]
        exact And.intro rfl rfl
  | stepPred + 1, domVec, codVec => by
      have hRestWF : ZxpLayersWF (stepPred + 2)
          (zxpWhiskerLayers 0 1 (zxwStairFromRightLayers stepPred)) := by
        have hRaw := zxpWhiskerLayersWF 0 1 (zxwStairFromRightLayers stepPred)
          (zxwStairFromRightWF stepPred)
        rw [Nat.zero_add] at hRaw
        exact hRaw
      have hRestCod : zxpLayersCodArity (stepPred + 2)
          (zxpWhiskerLayers 0 1 (zxwStairFromRightLayers stepPred))
          = 1 + (stepPred + 1) := by
        have hEntry : stepPred + 2 = 0 + ((stepPred + 1) + 1) :=
          (Nat.zero_add ((stepPred + 1) + 1)).symm
        rw [hEntry,
          zxpWhiskerLayersCodArity 0 1 (zxwStairFromRightLayers stepPred)
            (stepPred + 1),
          zxwStairFromRightCodArity stepPred, Nat.zero_add]
        exact Nat.add_assoc 1 stepPred 1
      refine Iff.trans
        (zxnConsLayerPairIffAt (stepPred + 2) (stepPred + 2) (1 + (stepPred + 1))
          (zxpCatCells (zxpWireCells stepPred) [ZxpCell.crossing])
          (zxpWhiskerLayers 0 1 (zxwStairFromRightLayers stepPred))
          (zxwWiresCrossingDomArity stepPred) (zxwWiresCrossingCodArity stepPred)
          hRestWF hRestCod domVec codVec) ?_
      refine Iff.intro ?_ ?_
      · intro hPacked
        obtain ⟨midVec, hHeadPair, hRestPair⟩ := hPacked
        have hHead := (zxnPadCellPairIffAt stepPred 0 ZxpCell.crossing
          (stepPred + 2) (stepPred + 2) rfl rfl domVec midVec).mp hHeadPair
        obtain ⟨passVec, cellDomVec, sideVec, cellCodVec,
          hDomCat, hMidCat, hPassLen, hSideLen, hCellPair⟩ := hHead
        have hSideNil : sideVec = [] := zxpLengthZeroNil sideVec hSideLen
        obtain ⟨firstBit, secondBit, hCellDomShape, hCellCodShape⟩ :=
          (zxnCrossingPairIff cellDomVec cellCodVec).mp hCellPair
        have hRest := (zxwWhiskerLayersPairIffAt 0 1
          (zxwStairFromRightLayers stepPred) (stepPred + 1) (1 + stepPred)
          (stepPred + 2) (1 + (stepPred + 1))
          (zxwStairFromRightWF stepPred) (zxwStairFromRightCodArity stepPred)
          (Nat.zero_add ((stepPred + 1) + 1))
          ((Nat.zero_add ((1 + stepPred) + 1)).trans (Nat.add_assoc 1 stepPred 1))
          midVec codVec).mp hRestPair
        obtain ⟨passVec2, innerDomVec, sideVec2, innerCodVec,
          hMidCat2, hCodCat2, hPassLen2, hSideLen2, hInnerPair⟩ := hRest
        have hPass2Nil : passVec2 = [] := zxpLengthZeroNil passVec2 hPassLen2
        obtain ⟨sideBit, hSideShape2⟩ := zxnLengthOneShape sideVec2 hSideLen2
        obtain ⟨innerFront, innerLast, hInnerDomEq, hInnerFrontLen, hInnerCodEq⟩ :=
          (zxwStairFromRightPairIff stepPred innerDomVec innerCodVec).mp hInnerPair
        have hInnerDomLen : innerDomVec.length = stepPred + 1 := hInnerPair.left
        rw [hPass2Nil, hSideShape2] at hMidCat2
        have hMidCat2Clean : midVec = zxpCat innerDomVec [sideBit] := hMidCat2
        rw [hSideNil, hCellCodShape] at hMidCat
        have hMidCatClean : midVec = zxpCat passVec [secondBit, firstBit] := by
          rw [hMidCat, zxpCatNilRight]
        have hMidBoth : zxpCat (zxpCat passVec [secondBit]) [firstBit]
            = zxpCat innerDomVec [sideBit] := by
          rw [zxpCatAssoc passVec [secondBit] [firstBit], <- hMidCat2Clean,
            hMidCatClean]
          exact rfl
        have hFirstBlockLen : (zxpCat passVec [secondBit]).length
            = innerDomVec.length := by
          rw [zxpCatLength, hPassLen, hInnerDomLen]
          exact rfl
        have hSplitBoth := zxpCatInj (zxpCat passVec [secondBit]) [firstBit]
          innerDomVec [sideBit] hFirstBlockLen hMidBoth
        have hInnerDomIs : innerDomVec = zxpCat passVec [secondBit] :=
          hSplitBoth.left.symm
        have hSideBitIs : firstBit = sideBit := by
          have hHeads := congrArg (fun fullRow => zxpGetBit fullRow 0)
            hSplitBoth.right
          exact hHeads
        rw [hInnerDomIs] at hInnerDomEq
        have hInnerSplit := zxpCatInj passVec [secondBit] innerFront [innerLast]
          (by rw [hPassLen, hInnerFrontLen]) hInnerDomEq
        have hFrontIs : innerFront = passVec := hInnerSplit.left.symm
        have hLastIs : innerLast = secondBit := by
          have hHeads := congrArg (fun fullRow => zxpGetBit fullRow 0)
            hInnerSplit.right
          exact hHeads.symm
        refine Exists.intro (zxpCat passVec [firstBit]) (Exists.intro secondBit
          (And.intro ?_ (And.intro ?_ ?_)))
        · rw [hDomCat, hSideNil, hCellDomShape, zxpCatNilRight,
            zxpCatAssoc passVec [firstBit] [secondBit]]
          exact rfl
        · rw [zxpCatLength, hPassLen]
          exact rfl
        · rw [hCodCat2, hPass2Nil, hSideShape2, hInnerCodEq, hFrontIs, hLastIs,
            <- hSideBitIs]
          exact rfl
      · intro hPacked
        obtain ⟨frontRow, lastBit, hDomEq, hFrontLen, hCodEq⟩ := hPacked
        obtain ⟨passVec, endBit, hFrontSplit, hPassLen⟩ :=
          zxwSnocSplit frontRow stepPred hFrontLen
        refine Exists.intro (zxpCat passVec [lastBit, endBit])
          (And.intro ?_ ?_)
        · refine (zxnPadCellPairIffAt stepPred 0 ZxpCell.crossing
            (stepPred + 2) (stepPred + 2) rfl rfl domVec
            (zxpCat passVec [lastBit, endBit])).mpr ?_
          refine Exists.intro passVec (Exists.intro [endBit, lastBit]
            (Exists.intro [] (Exists.intro [lastBit, endBit]
              (And.intro ?_ (And.intro ?_ (And.intro hPassLen (And.intro rfl ?_)))))))
          · rw [hDomEq, hFrontSplit, zxpCatAssoc passVec [endBit] [lastBit]]
            exact rfl
          · rw [zxpCatNilRight]
          · exact (zxnCrossingPairIff [endBit, lastBit] [lastBit, endBit]).mpr
              (Exists.intro endBit (Exists.intro lastBit (And.intro rfl rfl)))
        · refine (zxwWhiskerLayersPairIffAt 0 1
            (zxwStairFromRightLayers stepPred) (stepPred + 1) (1 + stepPred)
            (stepPred + 2) (1 + (stepPred + 1))
            (zxwStairFromRightWF stepPred) (zxwStairFromRightCodArity stepPred)
            (Nat.zero_add ((stepPred + 1) + 1))
            ((Nat.zero_add ((1 + stepPred) + 1)).trans (Nat.add_assoc 1 stepPred 1))
            (zxpCat passVec [lastBit, endBit]) codVec).mpr ?_
          refine Exists.intro [] (Exists.intro (zxpCat passVec [lastBit])
            (Exists.intro [endBit] (Exists.intro (lastBit :: passVec)
              (And.intro ?_ (And.intro ?_ (And.intro rfl (And.intro rfl ?_)))))))
          · show zxpCat passVec [lastBit, endBit]
              = zxpCat (zxpCat passVec [lastBit]) [endBit]
            rw [zxpCatAssoc passVec [lastBit] [endBit]]
            exact rfl
          · show codVec = zxpCat (lastBit :: passVec) [endBit]
            rw [hCodEq, hFrontSplit]
            exact rfl
          · refine (zxwStairFromRightPairIff stepPred (zxpCat passVec [lastBit])
              (lastBit :: passVec)).mpr ?_
            exact Exists.intro passVec (Exists.intro lastBit
              (And.intro rfl (And.intro hPassLen rfl)))

/-- THE LEFT STAIRCASE ROTATION: `zxwStairFromLeftLayers n` relates exactly
`t :: tail  |->  tail ++ [t]`. -/
theorem zxwStairFromLeftPairIff : (stepCount : Nat) -> (domVec codVec : List Bool) ->
    (ZxpPairMem (1 + stepCount) (stepCount + 1)
        (zxpLayersDenote (1 + stepCount) (zxwStairFromLeftLayers stepCount))
        domVec codVec
      <-> Exists fun headBit => Exists fun tailRow =>
          domVec = headBit :: tailRow /\ tailRow.length = stepCount
            /\ codVec = zxpCat tailRow [headBit])
  | 0, domVec, codVec => by
      refine Iff.trans (zxpIdSpec 1 domVec codVec) ?_
      refine Iff.intro ?_ ?_
      · intro hSame
        obtain ⟨onlyBit, hShape⟩ := zxnLengthOneShape domVec hSame.right
        refine Exists.intro onlyBit (Exists.intro [] (And.intro hShape
          (And.intro rfl ?_)))
        rw [<- hSame.left, hShape]
        exact rfl
      · intro hPacked
        obtain ⟨headBit, tailRow, hDomEq, hTailLen, hCodEq⟩ := hPacked
        have hTailNil : tailRow = [] := zxpLengthZeroNil tailRow hTailLen
        rw [hDomEq, hCodEq, hTailNil]
        exact And.intro rfl rfl
  | stepPred + 1, domVec, codVec => by
      have hRestWF : ZxpLayersWF (2 + stepPred)
          (zxpWhiskerLayers 1 0 (zxwStairFromLeftLayers stepPred)) := by
        have hRaw := zxpWhiskerLayersWF 1 0 (zxwStairFromLeftLayers stepPred)
          (zxwStairFromLeftWF stepPred)
        rw [Nat.add_zero, zxwOnePlusOnePlus stepPred] at hRaw
        exact hRaw
      have hRestCod : zxpLayersCodArity (2 + stepPred)
          (zxpWhiskerLayers 1 0 (zxwStairFromLeftLayers stepPred))
          = (stepPred + 1) + 1 := by
        have hEntry : 2 + stepPred = 1 + ((1 + stepPred) + 0) :=
          ((zxwOnePlusOnePlus stepPred).symm.trans
            (congrArg (fun innerValue => 1 + innerValue)
              (Nat.add_zero (1 + stepPred)).symm))
        rw [hEntry,
          zxpWhiskerLayersCodArity 1 0 (zxwStairFromLeftLayers stepPred)
            (1 + stepPred),
          zxwStairFromLeftCodArity stepPred, Nat.add_zero]
        exact Nat.add_comm 1 (stepPred + 1)
      refine Iff.trans
        (zxnConsLayerPairIffAt (1 + (stepPred + 1)) (2 + stepPred)
          ((stepPred + 1) + 1)
          (ZxpCell.crossing :: zxpWireCells stepPred)
          (zxpWhiskerLayers 1 0 (zxwStairFromLeftLayers stepPred))
          ((zxwCrossingWiresDomArity stepPred).trans
            (zxnTwoPlusEqOnePlusSucc stepPred))
          (zxwCrossingWiresCodArity stepPred)
          hRestWF hRestCod domVec codVec) ?_
      refine Iff.intro ?_ ?_
      · intro hPacked
        obtain ⟨midVec, hHeadPair, hRestPair⟩ := hPacked
        have hHead := (zxnPadCellPairIffAt 0 stepPred ZxpCell.crossing
          (1 + (stepPred + 1)) (2 + stepPred)
          ((Nat.zero_add (2 + stepPred)).trans (zxnTwoPlusEqOnePlusSucc stepPred))
          (Nat.zero_add (2 + stepPred)) domVec midVec).mp hHeadPair
        obtain ⟨passVec, cellDomVec, sideVec, cellCodVec,
          hDomCat, hMidCat, hPassLen, hSideLen, hCellPair⟩ := hHead
        have hPassNil : passVec = [] := zxpLengthZeroNil passVec hPassLen
        obtain ⟨firstBit, secondBit, hCellDomShape, hCellCodShape⟩ :=
          (zxnCrossingPairIff cellDomVec cellCodVec).mp hCellPair
        have hRest := (zxwWhiskerLayersPairIffAt 1 0
          (zxwStairFromLeftLayers stepPred) (1 + stepPred) (stepPred + 1)
          (2 + stepPred) ((stepPred + 1) + 1)
          (zxwStairFromLeftWF stepPred) (zxwStairFromLeftCodArity stepPred)
          ((congrArg (fun innerValue => 1 + innerValue)
              (Nat.add_zero (1 + stepPred))).trans (zxwOnePlusOnePlus stepPred))
          ((congrArg (fun innerValue => 1 + innerValue)
              (Nat.add_zero (stepPred + 1))).trans
            (Nat.add_comm 1 (stepPred + 1)))
          midVec codVec).mp hRestPair
        obtain ⟨passVec2, innerDomVec, sideVec2, innerCodVec,
          hMidCat2, hCodCat2, hPassLen2, hSideLen2, hInnerPair⟩ := hRest
        obtain ⟨passBit, hPass2Shape⟩ := zxnLengthOneShape passVec2 hPassLen2
        have hSide2Nil : sideVec2 = [] := zxpLengthZeroNil sideVec2 hSideLen2
        obtain ⟨innerHead, innerTail, hInnerDomEq, hInnerTailLen, hInnerCodEq⟩ :=
          (zxwStairFromLeftPairIff stepPred innerDomVec innerCodVec).mp hInnerPair
        rw [hPassNil, hCellCodShape] at hMidCat
        rw [hPass2Shape, hSide2Nil] at hMidCat2
        have hMidCat2Clean : midVec = passBit :: innerDomVec := by
          rw [hMidCat2, zxpCatNilRight]
          exact rfl
        have hMidCatClean : midVec = secondBit :: firstBit :: sideVec := hMidCat
        have hMidBoth : passBit :: innerDomVec = secondBit :: firstBit :: sideVec :=
          hMidCat2Clean.symm.trans hMidCatClean
        have hPassBitIs : passBit = secondBit := by
          have hHeads := congrArg (fun fullRow => zxpGetBit fullRow 0) hMidBoth
          exact hHeads
        have hInnerDomIs : innerDomVec = firstBit :: sideVec := by
          have hTails := congrArg (fun fullRow =>
            match fullRow with
            | [] => ([] : List Bool)
            | _headBit :: tailBits => tailBits) hMidBoth
          exact hTails
        rw [hInnerDomIs] at hInnerDomEq
        have hInnerHeadIs : innerHead = firstBit := by
          have hHeads := congrArg (fun fullRow => zxpGetBit fullRow 0) hInnerDomEq
          exact hHeads.symm
        have hInnerTailIs : innerTail = sideVec := by
          have hTails := congrArg (fun fullRow =>
            match fullRow with
            | [] => ([] : List Bool)
            | _headBit :: tailBits => tailBits) hInnerDomEq
          exact hTails.symm
        refine Exists.intro firstBit (Exists.intro (secondBit :: sideVec)
          (And.intro ?_ (And.intro ?_ ?_)))
        · rw [hDomCat, hPassNil, hCellDomShape]
          exact rfl
        · show sideVec.length + 1 = stepPred + 1
          rw [hSideLen]
        · rw [hCodCat2, hPass2Shape, hSide2Nil, hInnerCodEq, hInnerHeadIs,
            hInnerTailIs, hPassBitIs, zxpCatNilRight]
          exact rfl
      · intro hPacked
        obtain ⟨headBit, tailRow, hDomEq, hTailLen, hCodEq⟩ := hPacked
        obtain ⟨nextBit, restTail, hTailSplit, hRestLen⟩ :=
          zxnLengthSuccShape tailRow stepPred hTailLen
        refine Exists.intro (nextBit :: headBit :: restTail) (And.intro ?_ ?_)
        · refine (zxnPadCellPairIffAt 0 stepPred ZxpCell.crossing
            (1 + (stepPred + 1)) (2 + stepPred)
            ((Nat.zero_add (2 + stepPred)).trans (zxnTwoPlusEqOnePlusSucc stepPred))
            (Nat.zero_add (2 + stepPred)) domVec
            (nextBit :: headBit :: restTail)).mpr ?_
          refine Exists.intro [] (Exists.intro [headBit, nextBit]
            (Exists.intro restTail (Exists.intro [nextBit, headBit]
              (And.intro ?_ (And.intro rfl (And.intro rfl
                (And.intro hRestLen ?_)))))))
          · rw [hDomEq, hTailSplit]
            exact rfl
          · exact (zxnCrossingPairIff [headBit, nextBit] [nextBit, headBit]).mpr
              (Exists.intro headBit (Exists.intro nextBit (And.intro rfl rfl)))
        · refine (zxwWhiskerLayersPairIffAt 1 0
            (zxwStairFromLeftLayers stepPred) (1 + stepPred) (stepPred + 1)
            (2 + stepPred) ((stepPred + 1) + 1)
            (zxwStairFromLeftWF stepPred) (zxwStairFromLeftCodArity stepPred)
            ((congrArg (fun innerValue => 1 + innerValue)
                (Nat.add_zero (1 + stepPred))).trans (zxwOnePlusOnePlus stepPred))
            ((congrArg (fun innerValue => 1 + innerValue)
                (Nat.add_zero (stepPred + 1))).trans
              (Nat.add_comm 1 (stepPred + 1)))
            (nextBit :: headBit :: restTail) codVec).mpr ?_
          refine Exists.intro [nextBit] (Exists.intro (headBit :: restTail)
            (Exists.intro [] (Exists.intro (zxpCat restTail [headBit])
              (And.intro ?_ (And.intro ?_ (And.intro rfl (And.intro rfl ?_)))))))
          · rw [zxpCatNilRight]
            exact rfl
          · rw [hCodEq, hTailSplit, zxpCatNilRight]
            exact rfl
          · refine (zxwStairFromLeftPairIff stepPred (headBit :: restTail)
              (zxpCat restTail [headBit])).mpr ?_
            exact Exists.intro headBit (Exists.intro restTail
              (And.intro rfl (And.intro hRestLen rfl)))

/-! ## Stage 3 — the slide window family and its structural soundness -/

/-- Naturality slide, passive strand entering on the RIGHT, cell-first side:
`[[cell, wire]] ; stairR(cod cell)`. -/
def zxwSlideRightLhs (cell : ZxpCell) : ZxpDiagram :=
  { sourceArity := zxpCellDomArity cell + 1
    layers := [cell, ZxpCell.wire] :: zxwStairFromRightLayers (zxpCellCodArity cell) }

/-- Naturality slide, passive strand entering on the RIGHT, staircase-first side:
`stairR(dom cell) ; [[wire, cell]]`. -/
def zxwSlideRightRhs (cell : ZxpCell) : ZxpDiagram :=
  { sourceArity := zxpCellDomArity cell + 1
    layers := zxpCatLayers (zxwStairFromRightLayers (zxpCellDomArity cell))
      [[ZxpCell.wire, cell]] }

/-- Naturality slide, passive strand entering on the LEFT, cell-first side. -/
def zxwSlideLeftLhs (cell : ZxpCell) : ZxpDiagram :=
  { sourceArity := 1 + zxpCellDomArity cell
    layers := [ZxpCell.wire, cell] :: zxwStairFromLeftLayers (zxpCellCodArity cell) }

/-- Naturality slide, passive strand entering on the LEFT, staircase-first side. -/
def zxwSlideLeftRhs (cell : ZxpCell) : ZxpDiagram :=
  { sourceArity := 1 + zxpCellDomArity cell
    layers := zxpCatLayers (zxwStairFromLeftLayers (zxpCellDomArity cell))
      [[cell, ZxpCell.wire]] }

theorem zxwSlideRightLhsWF (cell : ZxpCell) : ZxpDiagramWF (zxwSlideRightLhs cell) :=
  ZxpLayersWF.cons rfl (zxwStairFromRightWF (zxpCellCodArity cell))

theorem zxwSlideRightRhsWF (cell : ZxpCell) : ZxpDiagramWF (zxwSlideRightRhs cell) := by
  refine zxpLayersWFCat (zxwStairFromRightLayers (zxpCellDomArity cell))
    [[ZxpCell.wire, cell]] (zxwStairFromRightWF (zxpCellDomArity cell)) ?_
  show ZxpLayersWF (zxpLayersCodArity (zxpCellDomArity cell + 1)
    (zxwStairFromRightLayers (zxpCellDomArity cell))) [[ZxpCell.wire, cell]]
  rw [zxwStairFromRightCodArity (zxpCellDomArity cell)]
  exact ZxpLayersWF.cons rfl (ZxpLayersWF.nil _)

theorem zxwSlideLeftLhsWF (cell : ZxpCell) : ZxpDiagramWF (zxwSlideLeftLhs cell) :=
  ZxpLayersWF.cons rfl (zxwStairFromLeftWF (zxpCellCodArity cell))

theorem zxwSlideLeftRhsWF (cell : ZxpCell) : ZxpDiagramWF (zxwSlideLeftRhs cell) := by
  refine zxpLayersWFCat (zxwStairFromLeftLayers (zxpCellDomArity cell))
    [[cell, ZxpCell.wire]] (zxwStairFromLeftWF (zxpCellDomArity cell)) ?_
  show ZxpLayersWF (zxpLayersCodArity (1 + zxpCellDomArity cell)
    (zxwStairFromLeftLayers (zxpCellDomArity cell))) [[cell, ZxpCell.wire]]
  rw [zxwStairFromLeftCodArity (zxpCellDomArity cell)]
  exact ZxpLayersWF.cons rfl (ZxpLayersWF.nil _)

theorem zxwSlideRightLhsCodArity (cell : ZxpCell) :
    zxpDiagramCodArity (zxwSlideRightLhs cell) = 1 + zxpCellCodArity cell := by
  show zxpLayersCodArity (zxpLayerCodArity [cell, ZxpCell.wire])
      (zxwStairFromRightLayers (zxpCellCodArity cell)) = 1 + zxpCellCodArity cell
  exact zxwStairFromRightCodArity (zxpCellCodArity cell)

theorem zxwSlideRightRhsCodArity (cell : ZxpCell) :
    zxpDiagramCodArity (zxwSlideRightRhs cell) = 1 + zxpCellCodArity cell := by
  show zxpLayersCodArity (zxpCellDomArity cell + 1)
      (zxpCatLayers (zxwStairFromRightLayers (zxpCellDomArity cell))
        [[ZxpCell.wire, cell]]) = 1 + zxpCellCodArity cell
  rw [zxpLayersCodArityCat, zxwStairFromRightCodArity (zxpCellDomArity cell)]
  exact rfl

theorem zxwSlideLeftLhsCodArity (cell : ZxpCell) :
    zxpDiagramCodArity (zxwSlideLeftLhs cell) = zxpCellCodArity cell + 1 := by
  show zxpLayersCodArity (zxpLayerCodArity [ZxpCell.wire, cell])
      (zxwStairFromLeftLayers (zxpCellCodArity cell)) = zxpCellCodArity cell + 1
  exact zxwStairFromLeftCodArity (zxpCellCodArity cell)

theorem zxwSlideLeftRhsCodArity (cell : ZxpCell) :
    zxpDiagramCodArity (zxwSlideLeftRhs cell) = zxpCellCodArity cell + 1 := by
  show zxpLayersCodArity (1 + zxpCellDomArity cell)
      (zxpCatLayers (zxwStairFromLeftLayers (zxpCellDomArity cell))
        [[cell, ZxpCell.wire]]) = zxpCellCodArity cell + 1
  rw [zxpLayersCodArityCat, zxwStairFromLeftCodArity (zxpCellDomArity cell)]
  exact rfl

/-- The cell-first slide side relates exactly
`cellDom ++ [t]  |->  t :: cellCod` with `(cellDom, cellCod)` in the cell's
relation — GENERIC in the cell. -/
theorem zxwSlideRightLhsPairIff (cell : ZxpCell) (domVec codVec : List Bool) :
    ZxpPairMem (zxpCellDomArity cell + 1) (1 + zxpCellCodArity cell)
        (zxpDiagramDenote (zxwSlideRightLhs cell)) domVec codVec
      <-> Exists fun cellDomVec => Exists fun passBit => Exists fun cellCodVec =>
          domVec = zxpCat cellDomVec [passBit]
            /\ codVec = passBit :: cellCodVec
            /\ ZxpPairMem (zxpCellDomArity cell) (zxpCellCodArity cell)
                (zxpCellRows cell) cellDomVec cellCodVec := by
  refine Iff.trans
    (zxnConsLayerPairIffAt (zxpCellDomArity cell + 1) (zxpCellCodArity cell + 1)
      (1 + zxpCellCodArity cell) [cell, ZxpCell.wire]
      (zxwStairFromRightLayers (zxpCellCodArity cell)) rfl rfl
      (zxwStairFromRightWF (zxpCellCodArity cell))
      (zxwStairFromRightCodArity (zxpCellCodArity cell)) domVec codVec) ?_
  refine Iff.intro ?_ ?_
  · intro hPacked
    obtain ⟨midVec, hHeadPair, hStairPair⟩ := hPacked
    have hHead := (zxnPadCellPairIffAt 0 1 cell (zxpCellDomArity cell + 1)
      (zxpCellCodArity cell + 1) (Nat.zero_add (zxpCellDomArity cell + 1))
      (Nat.zero_add (zxpCellCodArity cell + 1)) domVec midVec).mp hHeadPair
    obtain ⟨passVec, cellDomVec, sideVec, cellCodVec,
      hDomCat, hMidCat, hPassLen, hSideLen, hCellPair⟩ := hHead
    have hPassNil : passVec = [] := zxpLengthZeroNil passVec hPassLen
    obtain ⟨sideBit, hSideShape⟩ := zxnLengthOneShape sideVec hSideLen
    obtain ⟨frontRow, lastBit, hMidEq, hFrontLen, hCodEq⟩ :=
      (zxwStairFromRightPairIff (zxpCellCodArity cell) midVec codVec).mp hStairPair
    rw [hPassNil, hSideShape] at hMidCat
    have hMidClean : midVec = zxpCat cellCodVec [sideBit] := hMidCat
    rw [hMidClean] at hMidEq
    have hCellCodLen : cellCodVec.length = zxpCellCodArity cell :=
      hCellPair.right.left
    have hSplit := zxpCatInj cellCodVec [sideBit] frontRow [lastBit]
      (by rw [hCellCodLen, hFrontLen]) hMidEq
    have hFrontIs : frontRow = cellCodVec := hSplit.left.symm
    have hLastIs : lastBit = sideBit := by
      have hHeads := congrArg (fun fullRow => zxpGetBit fullRow 0) hSplit.right
      exact hHeads.symm
    refine Exists.intro cellDomVec (Exists.intro sideBit
      (Exists.intro cellCodVec (And.intro ?_ (And.intro ?_ hCellPair))))
    · rw [hDomCat, hPassNil, hSideShape]
      exact rfl
    · rw [hCodEq, hFrontIs, hLastIs]
  · intro hPacked
    obtain ⟨cellDomVec, passBit, cellCodVec, hDomEq, hCodEq, hCellPair⟩ := hPacked
    refine Exists.intro (zxpCat cellCodVec [passBit]) (And.intro ?_ ?_)
    · refine (zxnPadCellPairIffAt 0 1 cell (zxpCellDomArity cell + 1)
        (zxpCellCodArity cell + 1) (Nat.zero_add (zxpCellDomArity cell + 1))
        (Nat.zero_add (zxpCellCodArity cell + 1)) domVec
        (zxpCat cellCodVec [passBit])).mpr ?_
      refine Exists.intro [] (Exists.intro cellDomVec (Exists.intro [passBit]
        (Exists.intro cellCodVec (And.intro ?_ (And.intro rfl
          (And.intro rfl (And.intro rfl hCellPair)))))))
      rw [hDomEq]
      exact rfl
    · refine (zxwStairFromRightPairIff (zxpCellCodArity cell)
        (zxpCat cellCodVec [passBit]) codVec).mpr ?_
      exact Exists.intro cellCodVec (Exists.intro passBit
        (And.intro rfl (And.intro hCellPair.right.left hCodEq)))

/-- The staircase-first slide side relates exactly the SAME canonical predicate. -/
theorem zxwSlideRightRhsPairIff (cell : ZxpCell) (domVec codVec : List Bool) :
    ZxpPairMem (zxpCellDomArity cell + 1) (1 + zxpCellCodArity cell)
        (zxpDiagramDenote (zxwSlideRightRhs cell)) domVec codVec
      <-> Exists fun cellDomVec => Exists fun passBit => Exists fun cellCodVec =>
          domVec = zxpCat cellDomVec [passBit]
            /\ codVec = passBit :: cellCodVec
            /\ ZxpPairMem (zxpCellDomArity cell) (zxpCellCodArity cell)
                (zxpCellRows cell) cellDomVec cellCodVec := by
  refine Iff.trans
    (zxnCatLayersPairIffAt (zxpCellDomArity cell + 1) (1 + zxpCellDomArity cell)
      (1 + zxpCellCodArity cell)
      (zxwStairFromRightLayers (zxpCellDomArity cell)) [[ZxpCell.wire, cell]]
      (zxwStairFromRightWF (zxpCellDomArity cell))
      (zxwStairFromRightCodArity (zxpCellDomArity cell))
      (ZxpLayersWF.cons rfl (ZxpLayersWF.nil _)) rfl domVec codVec) ?_
  refine Iff.intro ?_ ?_
  · intro hPacked
    obtain ⟨midVec, hStairPair, hTailPair⟩ := hPacked
    obtain ⟨frontRow, lastBit, hDomEq, hFrontLen, hMidEq⟩ :=
      (zxwStairFromRightPairIff (zxpCellDomArity cell) domVec midVec).mp hStairPair
    have hTailSingle := (zxnSingleLayerPairIffAt (1 + zxpCellDomArity cell)
      (1 + zxpCellCodArity cell) [ZxpCell.wire, cell] rfl rfl midVec codVec).mp
      hTailPair
    have hTail := (zxnPadCellPairIffAt 1 0 cell (1 + zxpCellDomArity cell)
      (1 + zxpCellCodArity cell) rfl rfl midVec codVec).mp hTailSingle
    obtain ⟨passVec, cellDomVec, sideVec, cellCodVec,
      hMidCat, hCodCat, hPassLen, hSideLen, hCellPair⟩ := hTail
    obtain ⟨passBit, hPassShape⟩ := zxnLengthOneShape passVec hPassLen
    have hSideNil : sideVec = [] := zxpLengthZeroNil sideVec hSideLen
    rw [hPassShape, hSideNil, zxpCatNilRight] at hMidCat
    rw [hPassShape, hSideNil, zxpCatNilRight] at hCodCat
    have hMidCatClean : midVec = passBit :: cellDomVec := by
      rw [hMidCat]
      exact rfl
    have hMidBoth : lastBit :: frontRow = passBit :: cellDomVec :=
      hMidEq.symm.trans hMidCatClean
    have hLastIs : lastBit = passBit := by
      have hHeads := congrArg (fun fullRow => zxpGetBit fullRow 0) hMidBoth
      exact hHeads
    have hFrontIs : frontRow = cellDomVec := by
      have hTails := congrArg (fun fullRow =>
        match fullRow with
        | [] => ([] : List Bool)
        | _headBit :: tailBits => tailBits) hMidBoth
      exact hTails
    refine Exists.intro cellDomVec (Exists.intro passBit
      (Exists.intro cellCodVec (And.intro ?_ (And.intro ?_ hCellPair))))
    · rw [hDomEq, hFrontIs, hLastIs]
    · rw [hCodCat]
      exact rfl
  · intro hPacked
    obtain ⟨cellDomVec, passBit, cellCodVec, hDomEq, hCodEq, hCellPair⟩ := hPacked
    refine Exists.intro (passBit :: cellDomVec) (And.intro ?_ ?_)
    · refine (zxwStairFromRightPairIff (zxpCellDomArity cell) domVec
        (passBit :: cellDomVec)).mpr ?_
      exact Exists.intro cellDomVec (Exists.intro passBit
        (And.intro hDomEq (And.intro hCellPair.left rfl)))
    · refine (zxnSingleLayerPairIffAt (1 + zxpCellDomArity cell)
        (1 + zxpCellCodArity cell) [ZxpCell.wire, cell] rfl rfl
        (passBit :: cellDomVec) codVec).mpr ?_
      refine (zxnPadCellPairIffAt 1 0 cell (1 + zxpCellDomArity cell)
        (1 + zxpCellCodArity cell) rfl rfl (passBit :: cellDomVec) codVec).mpr ?_
      refine Exists.intro [passBit] (Exists.intro cellDomVec (Exists.intro []
        (Exists.intro cellCodVec (And.intro ?_ (And.intro ?_
          (And.intro rfl (And.intro rfl hCellPair)))))))
      · rw [zxpCatNilRight]
        exact rfl
      · rw [hCodEq, zxpCatNilRight]
        exact rfl

/-- The left-orientation cell-first side relates exactly
`t :: cellDom  |->  cellCod ++ [t]`. -/
theorem zxwSlideLeftLhsPairIff (cell : ZxpCell) (domVec codVec : List Bool) :
    ZxpPairMem (1 + zxpCellDomArity cell) (zxpCellCodArity cell + 1)
        (zxpDiagramDenote (zxwSlideLeftLhs cell)) domVec codVec
      <-> Exists fun passBit => Exists fun cellDomVec => Exists fun cellCodVec =>
          domVec = passBit :: cellDomVec
            /\ codVec = zxpCat cellCodVec [passBit]
            /\ ZxpPairMem (zxpCellDomArity cell) (zxpCellCodArity cell)
                (zxpCellRows cell) cellDomVec cellCodVec := by
  refine Iff.trans
    (zxnConsLayerPairIffAt (1 + zxpCellDomArity cell) (1 + zxpCellCodArity cell)
      (zxpCellCodArity cell + 1) [ZxpCell.wire, cell]
      (zxwStairFromLeftLayers (zxpCellCodArity cell)) rfl rfl
      (zxwStairFromLeftWF (zxpCellCodArity cell))
      (zxwStairFromLeftCodArity (zxpCellCodArity cell)) domVec codVec) ?_
  refine Iff.intro ?_ ?_
  · intro hPacked
    obtain ⟨midVec, hHeadPair, hStairPair⟩ := hPacked
    have hHead := (zxnPadCellPairIffAt 1 0 cell (1 + zxpCellDomArity cell)
      (1 + zxpCellCodArity cell) rfl rfl domVec midVec).mp hHeadPair
    obtain ⟨passVec, cellDomVec, sideVec, cellCodVec,
      hDomCat, hMidCat, hPassLen, hSideLen, hCellPair⟩ := hHead
    obtain ⟨passBit, hPassShape⟩ := zxnLengthOneShape passVec hPassLen
    have hSideNil : sideVec = [] := zxpLengthZeroNil sideVec hSideLen
    rw [hPassShape, hSideNil, zxpCatNilRight] at hDomCat
    rw [hPassShape, hSideNil, zxpCatNilRight] at hMidCat
    obtain ⟨headBit, tailRow, hMidEq, hTailLen, hCodEq⟩ :=
      (zxwStairFromLeftPairIff (zxpCellCodArity cell) midVec codVec).mp hStairPair
    have hMidCatClean : midVec = passBit :: cellCodVec := by
      rw [hMidCat]
      exact rfl
    have hMidBoth : headBit :: tailRow = passBit :: cellCodVec :=
      hMidEq.symm.trans hMidCatClean
    have hHeadIs : headBit = passBit := by
      have hHeads := congrArg (fun fullRow => zxpGetBit fullRow 0) hMidBoth
      exact hHeads
    have hTailIs : tailRow = cellCodVec := by
      have hTails := congrArg (fun fullRow =>
        match fullRow with
        | [] => ([] : List Bool)
        | _headBit :: tailBits => tailBits) hMidBoth
      exact hTails
    refine Exists.intro passBit (Exists.intro cellDomVec
      (Exists.intro cellCodVec (And.intro ?_ (And.intro ?_ hCellPair))))
    · rw [hDomCat]
      exact rfl
    · rw [hCodEq, hHeadIs, hTailIs]
  · intro hPacked
    obtain ⟨passBit, cellDomVec, cellCodVec, hDomEq, hCodEq, hCellPair⟩ := hPacked
    refine Exists.intro (passBit :: cellCodVec) (And.intro ?_ ?_)
    · refine (zxnPadCellPairIffAt 1 0 cell (1 + zxpCellDomArity cell)
        (1 + zxpCellCodArity cell) rfl rfl domVec (passBit :: cellCodVec)).mpr ?_
      refine Exists.intro [passBit] (Exists.intro cellDomVec (Exists.intro []
        (Exists.intro cellCodVec (And.intro ?_ (And.intro ?_
          (And.intro rfl (And.intro rfl hCellPair)))))))
      · rw [hDomEq, zxpCatNilRight]
        exact rfl
      · rw [zxpCatNilRight]
        exact rfl
    · refine (zxwStairFromLeftPairIff (zxpCellCodArity cell)
        (passBit :: cellCodVec) codVec).mpr ?_
      exact Exists.intro passBit (Exists.intro cellCodVec
        (And.intro rfl (And.intro hCellPair.right.left hCodEq)))

/-- The left-orientation staircase-first side relates exactly the SAME canonical
predicate. -/
theorem zxwSlideLeftRhsPairIff (cell : ZxpCell) (domVec codVec : List Bool) :
    ZxpPairMem (1 + zxpCellDomArity cell) (zxpCellCodArity cell + 1)
        (zxpDiagramDenote (zxwSlideLeftRhs cell)) domVec codVec
      <-> Exists fun passBit => Exists fun cellDomVec => Exists fun cellCodVec =>
          domVec = passBit :: cellDomVec
            /\ codVec = zxpCat cellCodVec [passBit]
            /\ ZxpPairMem (zxpCellDomArity cell) (zxpCellCodArity cell)
                (zxpCellRows cell) cellDomVec cellCodVec := by
  refine Iff.trans
    (zxnCatLayersPairIffAt (1 + zxpCellDomArity cell) (zxpCellDomArity cell + 1)
      (zxpCellCodArity cell + 1)
      (zxwStairFromLeftLayers (zxpCellDomArity cell)) [[cell, ZxpCell.wire]]
      (zxwStairFromLeftWF (zxpCellDomArity cell))
      (zxwStairFromLeftCodArity (zxpCellDomArity cell))
      (ZxpLayersWF.cons rfl (ZxpLayersWF.nil _)) rfl domVec codVec) ?_
  refine Iff.intro ?_ ?_
  · intro hPacked
    obtain ⟨midVec, hStairPair, hTailPair⟩ := hPacked
    obtain ⟨headBit, tailRow, hDomEq, hTailLen, hMidEq⟩ :=
      (zxwStairFromLeftPairIff (zxpCellDomArity cell) domVec midVec).mp hStairPair
    have hTailSingle := (zxnSingleLayerPairIffAt (zxpCellDomArity cell + 1)
      (zxpCellCodArity cell + 1) [cell, ZxpCell.wire] rfl rfl midVec codVec).mp
      hTailPair
    have hTail := (zxnPadCellPairIffAt 0 1 cell (zxpCellDomArity cell + 1)
      (zxpCellCodArity cell + 1) (Nat.zero_add (zxpCellDomArity cell + 1))
      (Nat.zero_add (zxpCellCodArity cell + 1)) midVec codVec).mp hTailSingle
    obtain ⟨passVec, cellDomVec, sideVec, cellCodVec,
      hMidCat, hCodCat, hPassLen, hSideLen, hCellPair⟩ := hTail
    have hPassNil : passVec = [] := zxpLengthZeroNil passVec hPassLen
    obtain ⟨sideBit, hSideShape⟩ := zxnLengthOneShape sideVec hSideLen
    rw [hPassNil, hSideShape] at hMidCat
    rw [hPassNil, hSideShape] at hCodCat
    have hMidClean : midVec = zxpCat cellDomVec [sideBit] := hMidCat
    rw [hMidClean] at hMidEq
    have hCellDomLen : cellDomVec.length = zxpCellDomArity cell := hCellPair.left
    have hSplit := zxpCatInj tailRow [headBit] cellDomVec [sideBit]
      (by rw [hTailLen, hCellDomLen]) hMidEq.symm
    have hTailIs : tailRow = cellDomVec := hSplit.left
    have hHeadIs : headBit = sideBit := by
      have hHeads := congrArg (fun fullRow => zxpGetBit fullRow 0) hSplit.right
      exact hHeads
    refine Exists.intro headBit (Exists.intro cellDomVec
      (Exists.intro cellCodVec (And.intro ?_ (And.intro ?_ hCellPair))))
    · rw [hDomEq, hTailIs]
    · rw [hCodCat, hHeadIs]
      exact rfl
  · intro hPacked
    obtain ⟨passBit, cellDomVec, cellCodVec, hDomEq, hCodEq, hCellPair⟩ := hPacked
    refine Exists.intro (zxpCat cellDomVec [passBit]) (And.intro ?_ ?_)
    · refine (zxwStairFromLeftPairIff (zxpCellDomArity cell) domVec
        (zxpCat cellDomVec [passBit])).mpr ?_
      exact Exists.intro passBit (Exists.intro cellDomVec
        (And.intro hDomEq (And.intro hCellPair.left rfl)))
    · refine (zxnSingleLayerPairIffAt (zxpCellDomArity cell + 1)
        (zxpCellCodArity cell + 1) [cell, ZxpCell.wire] rfl rfl
        (zxpCat cellDomVec [passBit]) codVec).mpr ?_
      refine (zxnPadCellPairIffAt 0 1 cell (zxpCellDomArity cell + 1)
        (zxpCellCodArity cell + 1) (Nat.zero_add (zxpCellDomArity cell + 1))
        (Nat.zero_add (zxpCellCodArity cell + 1))
        (zxpCat cellDomVec [passBit]) codVec).mpr ?_
      refine Exists.intro [] (Exists.intro cellDomVec (Exists.intro [passBit]
        (Exists.intro cellCodVec (And.intro rfl (And.intro ?_
          (And.intro rfl (And.intro rfl hCellPair)))))))
      rw [hCodEq]
      exact rfl

/-- SOUNDNESS OF THE RIGHT SLIDE at every cell and every arity (bundle form):
both sides denote the same relation, generically in the cell's own relation. -/
theorem zxwSlideRightBundle (cell : ZxpCell) :
    ZxpConvBundle (zxwSlideRightLhs cell) (zxwSlideRightRhs cell) := by
  refine And.intro rfl (And.intro ?_ (And.intro (zxwSlideRightLhsWF cell)
    (And.intro (zxwSlideRightRhsWF cell) ?_)))
  · exact (zxwSlideRightLhsCodArity cell).trans
      (zxwSlideRightRhsCodArity cell).symm
  · refine zxpRelEquivCast rfl (zxwSlideRightLhsCodArity cell).symm ?_
    exact fun domVec codVec =>
      Iff.trans (zxwSlideRightLhsPairIff cell domVec codVec)
        (zxwSlideRightRhsPairIff cell domVec codVec).symm

/-- SOUNDNESS OF THE LEFT SLIDE at every cell and every arity (bundle form). -/
theorem zxwSlideLeftBundle (cell : ZxpCell) :
    ZxpConvBundle (zxwSlideLeftLhs cell) (zxwSlideLeftRhs cell) := by
  refine And.intro rfl (And.intro ?_ (And.intro (zxwSlideLeftLhsWF cell)
    (And.intro (zxwSlideLeftRhsWF cell) ?_)))
  · exact (zxwSlideLeftLhsCodArity cell).trans (zxwSlideLeftRhsCodArity cell).symm
  · refine zxpRelEquivCast rfl (zxwSlideLeftLhsCodArity cell).symm ?_
    exact fun domVec codVec =>
      Iff.trans (zxwSlideLeftLhsPairIff cell domVec codVec)
        (zxwSlideLeftRhsPairIff cell domVec codVec).symm

/-- Sigma involution, crossing-pair side. -/
def zxwInvolutionLhs : ZxpDiagram :=
  { sourceArity := 2, layers := [[ZxpCell.crossing], [ZxpCell.crossing]] }

/-- Sigma involution, identity side. -/
def zxwInvolutionRhs : ZxpDiagram :=
  { sourceArity := 2, layers := [[ZxpCell.wire, ZxpCell.wire]] }

/-- Involution soundness: kernel-decided on the closed pair. -/
theorem zxwInvolutionBundle : ZxpConvBundle zxwInvolutionLhs zxwInvolutionRhs :=
  zxpConvBundleOfChecks zxwInvolutionLhs zxwInvolutionRhs rfl rfl rfl rfl rfl

/-! ## Stage 4 — THE WIRING-EXTENDED CONGRUENCE `ZxwConv` -/

/-- Wiring-extended window move: any `ZxeConv` window move, a naturality slide in
either orientation at any cell, or the sigma involution. -/
inductive ZxwWindowMove : ZxpDiagram -> ZxpDiagram -> Prop where
  | base {firstWindow secondWindow : ZxpDiagram}
      (hMove : ZxeWindowMove firstWindow secondWindow) :
      ZxwWindowMove firstWindow secondWindow
  | slideRight (cell : ZxpCell) :
      ZxwWindowMove (zxwSlideRightLhs cell) (zxwSlideRightRhs cell)
  | slideLeft (cell : ZxpCell) :
      ZxwWindowMove (zxwSlideLeftLhs cell) (zxwSlideLeftRhs cell)
  | sigmaInvolution : ZxwWindowMove zxwInvolutionLhs zxwInvolutionRhs

/-- Every wiring-extended window move is sound (bundle form). -/
theorem zxwWindowMoveBundle {firstWindow secondWindow : ZxpDiagram}
    (hMove : ZxwWindowMove firstWindow secondWindow) :
    ZxpConvBundle firstWindow secondWindow := by
  cases hMove with
  | base hBaseMove => exact zxeWindowMoveBundle hBaseMove
  | slideRight cell => exact zxwSlideRightBundle cell
  | slideLeft cell => exact zxwSlideLeftBundle cell
  | sigmaInvolution => exact zxwInvolutionBundle

/-- One wiring-extended rewriting step: a wiring window move fired inside the
seed's pad combinator (identical constructor shape to `ZxeStep`). -/
inductive ZxwStep : ZxpDiagram -> ZxpDiagram -> Prop where
  | pad (contextSource leftWires rightWires : Nat)
      (beforeLayers afterLayers : List (List ZxpCell))
      {firstWindow secondWindow : ZxpDiagram}
      (hMove : ZxwWindowMove firstWindow secondWindow)
      (hBeforeWF : ZxpLayersWF contextSource beforeLayers)
      (hBeforeCod : zxpLayersCodArity contextSource beforeLayers
        = leftWires + (firstWindow.sourceArity + rightWires))
      (hAfterWF : ZxpLayersWF
        (leftWires + (zxpDiagramCodArity firstWindow + rightWires)) afterLayers) :
      ZxwStep
        (zxpPadDiagram contextSource leftWires rightWires beforeLayers afterLayers
          firstWindow)
        (zxpPadDiagram contextSource leftWires rightWires beforeLayers afterLayers
          secondWindow)

/-- Soundness of one wiring-extended padded step (rides FusionRepair's
`zxrPadBundle`, factored over an arbitrary window bundle). -/
theorem zxwStepBundle {firstDiagram secondDiagram : ZxpDiagram}
    (hStep : ZxwStep firstDiagram secondDiagram) :
    ZxpConvBundle firstDiagram secondDiagram := by
  cases hStep with
  | pad contextSource leftWires rightWires beforeLayers afterLayers hMove hBeforeWF
      hBeforeCod hAfterWF =>
      exact zxrPadBundle contextSource leftWires rightWires beforeLayers afterLayers
        (zxwWindowMoveBundle hMove) hBeforeWF hBeforeCod hAfterWF

/-- THE WIRING-EXTENDED CONGRUENCE: wiring-aware steps under the seed's groupoid
closure. -/
inductive ZxwConv : ZxpDiagram -> ZxpDiagram -> Prop where
  | step {firstDiagram secondDiagram : ZxpDiagram}
      (hStep : ZxwStep firstDiagram secondDiagram) : ZxwConv firstDiagram secondDiagram
  | refl (diagram : ZxpDiagram) (hWF : ZxpDiagramWF diagram) : ZxwConv diagram diagram
  | symm {firstDiagram secondDiagram : ZxpDiagram}
      (hConv : ZxwConv firstDiagram secondDiagram) : ZxwConv secondDiagram firstDiagram
  | trans {firstDiagram secondDiagram thirdDiagram : ZxpDiagram}
      (hFirst : ZxwConv firstDiagram secondDiagram)
      (hSecond : ZxwConv secondDiagram thirdDiagram) : ZxwConv firstDiagram thirdDiagram

/-- SOUNDNESS AT ALL ARITIES: wiring-extended-convertible diagrams share
boundaries, are well-formed, and denote the same F2 linear relation. -/
theorem zxwConvSound {firstDiagram secondDiagram : ZxpDiagram}
    (hConv : ZxwConv firstDiagram secondDiagram) :
    ZxpConvBundle firstDiagram secondDiagram := by
  induction hConv with
  | step hStep => exact zxwStepBundle hStep
  | refl diagram hWF =>
      exact And.intro rfl (And.intro rfl (And.intro hWF (And.intro hWF
        (zxpRelEquivRefl diagram.sourceArity (zxpDiagramCodArity diagram)
          (zxpDiagramDenote diagram)))))
  | symm _hConv innerBundle => exact zxpConvBundleSymm innerBundle
  | trans _hFirst _hSecond firstBundle secondBundle =>
      exact zxpConvBundleTrans firstBundle secondBundle

/-- THE REFUTATION BRIDGE for the wiring-extended congruence. -/
theorem zxwConvSpanEqB {firstDiagram secondDiagram : ZxpDiagram}
    (hConv : ZxwConv firstDiagram secondDiagram) :
    zxpSpanEqB (zxpDiagramDenote firstDiagram) (zxpDiagramDenote secondDiagram)
      = true := by
  have hBundle := zxwConvSound hConv
  exact zxpSpanEqBOfRelEquiv
    (zxpDiagramDenoteWidth firstDiagram hBundle.right.right.left)
    (zxpAllWidthCast (by rw [hBundle.left, hBundle.right.left])
      (zxpDiagramDenoteWidth secondDiagram hBundle.right.right.right.left))
    hBundle.right.right.right.right

/-- EVERY `ZxeConv` CONVERSION EMBEDS: the exchange-extended congruence is a
sub-congruence of the wiring-extended one. -/
theorem zxwOfZxeConv {firstDiagram secondDiagram : ZxpDiagram}
    (hConv : ZxeConv firstDiagram secondDiagram) :
    ZxwConv firstDiagram secondDiagram := by
  induction hConv with
  | step hStep =>
      cases hStep with
      | pad contextSource leftWires rightWires beforeLayers afterLayers hMove hBeforeWF
          hBeforeCod hAfterWF =>
          exact ZxwConv.step (ZxwStep.pad contextSource leftWires rightWires
            beforeLayers afterLayers (ZxwWindowMove.base hMove) hBeforeWF hBeforeCod
            hAfterWF)
  | refl diagram hWF => exact ZxwConv.refl diagram hWF
  | symm _hConv innerConv => exact ZxwConv.symm innerConv
  | trans _hFirst _hSecond firstConv secondConv =>
      exact ZxwConv.trans firstConv secondConv

/-- Every fusion-congruence conversion embeds (through the exchange embedding). -/
theorem zxwOfZxrConv {firstDiagram secondDiagram : ZxpDiagram}
    (hConv : ZxrConv firstDiagram secondDiagram) :
    ZxwConv firstDiagram secondDiagram :=
  zxwOfZxeConv (zxeOfZxrConv hConv)

/-- Every seed conversion embeds. -/
theorem zxwOfZxpConv {firstDiagram secondDiagram : ZxpDiagram}
    (hConv : ZxpConv firstDiagram secondDiagram) :
    ZxwConv firstDiagram secondDiagram :=
  zxwOfZxeConv (zxeOfZxpConv hConv)

/-- THE PAD-LIFTING CONGRUENCE for `ZxwConv`: a wiring-extended derivation between
windows lifts into any padding context (the ladder's lift ported verbatim). -/
theorem zxwConvLift (contextSource leftWires rightWires : Nat)
    (beforeLayers afterLayers : List (List ZxpCell))
    {firstWindow secondWindow : ZxpDiagram}
    (hConv : ZxwConv firstWindow secondWindow)
    (hBeforeWF : ZxpLayersWF contextSource beforeLayers)
    (hBeforeCod : zxpLayersCodArity contextSource beforeLayers
      = leftWires + (firstWindow.sourceArity + rightWires))
    (hAfterWF : ZxpLayersWF
      (leftWires + (zxpDiagramCodArity firstWindow + rightWires)) afterLayers) :
    ZxwConv
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
          exact ZxwConv.step (ZxwStep.pad contextSource (leftWires + innerLeft)
            (innerRight + rightWires)
            (zxpCatLayers beforeLayers
              (zxpWhiskerLayers leftWires rightWires innerBefore))
            (zxpCatLayers (zxpWhiskerLayers leftWires rightWires innerAfter)
              afterLayers)
            hMove hEBeforeWF hEBeforeCod hEAfterWF)
  | refl diagram hWF =>
      intro hBeforeCod hAfterWF
      exact ZxwConv.refl _ (zxpPadDiagramWF contextSource leftWires rightWires
        beforeLayers afterLayers diagram hBeforeWF hBeforeCod hWF hAfterWF)
  | symm hInnerConv innerIH =>
      intro hBeforeCod hAfterWF
      have hBundle := zxwConvSound hInnerConv
      refine ZxwConv.symm (innerIH ?_ ?_)
      · rw [hBeforeCod, hBundle.left]
      · rw [hBundle.right.left]
        exact hAfterWF
  | trans hFirstConv _hSecondConv firstIH secondIH =>
      intro hBeforeCod hAfterWF
      have hFirstBundle := zxwConvSound hFirstConv
      refine ZxwConv.trans (firstIH hBeforeCod hAfterWF) (secondIH ?_ ?_)
      · rw [hBeforeCod, hFirstBundle.left]
      · rw [<- hFirstBundle.right.left]
        exact hAfterWF

/-- One wiring window move fired between plain (whisker-free) context layers. -/
theorem zxwStepConv (contextSource : Nat)
    (beforeLayers afterLayers : List (List ZxpCell))
    {firstWindow secondWindow : ZxpDiagram}
    (hMove : ZxwWindowMove firstWindow secondWindow)
    (hBeforeWF : ZxpLayersWF contextSource beforeLayers)
    (hBeforeCod : zxpLayersCodArity contextSource beforeLayers
      = firstWindow.sourceArity)
    (hAfterWF : ZxpLayersWF (zxpDiagramCodArity firstWindow) afterLayers) :
    ZxwConv
      { sourceArity := contextSource
        layers := zxpCatLayers beforeLayers
          (zxpCatLayers firstWindow.layers afterLayers) }
      { sourceArity := contextSource
        layers := zxpCatLayers beforeLayers
          (zxpCatLayers secondWindow.layers afterLayers) } := by
  have hBeforeCodPadded : zxpLayersCodArity contextSource beforeLayers
      = 0 + (firstWindow.sourceArity + 0) :=
    hBeforeCod.trans (Nat.zero_add firstWindow.sourceArity).symm
  have hAfterWFPadded : ZxpLayersWF (0 + (zxpDiagramCodArity firstWindow + 0))
      afterLayers := by
    rw [Nat.zero_add]
    exact hAfterWF
  have hStep := ZxwConv.step (ZxwStep.pad contextSource 0 0 beforeLayers afterLayers
    hMove hBeforeWF hBeforeCodPadded hAfterWFPadded)
  rw [zxePadPlainLayers contextSource beforeLayers afterLayers firstWindow,
    zxePadPlainLayers contextSource beforeLayers afterLayers secondWindow] at hStep
  exact hStep

/-- A whole wiring derivation fired between plain (whisker-free) context layers. -/
theorem zxwLiftConv (contextSource : Nat)
    (beforeLayers afterLayers : List (List ZxpCell))
    {firstWindow secondWindow : ZxpDiagram}
    (hConv : ZxwConv firstWindow secondWindow)
    (hBeforeWF : ZxpLayersWF contextSource beforeLayers)
    (hBeforeCod : zxpLayersCodArity contextSource beforeLayers
      = firstWindow.sourceArity)
    (hAfterWF : ZxpLayersWF (zxpDiagramCodArity firstWindow) afterLayers) :
    ZxwConv
      { sourceArity := contextSource
        layers := zxpCatLayers beforeLayers
          (zxpCatLayers firstWindow.layers afterLayers) }
      { sourceArity := contextSource
        layers := zxpCatLayers beforeLayers
          (zxpCatLayers secondWindow.layers afterLayers) } := by
  have hBeforeCodPadded : zxpLayersCodArity contextSource beforeLayers
      = 0 + (firstWindow.sourceArity + 0) :=
    hBeforeCod.trans (Nat.zero_add firstWindow.sourceArity).symm
  have hAfterWFPadded : ZxpLayersWF (0 + (zxpDiagramCodArity firstWindow + 0))
      afterLayers := by
    rw [Nat.zero_add]
    exact hAfterWF
  have hLifted := zxwConvLift contextSource 0 0 beforeLayers afterLayers hConv
    hBeforeWF hBeforeCodPadded hAfterWFPadded
  rw [zxePadPlainLayers contextSource beforeLayers afterLayers firstWindow,
    zxePadPlainLayers contextSource beforeLayers afterLayers secondWindow] at hLifted
  exact hLifted

/-- Fire a bare wiring window move as a conversion (empty context pad dissolves). -/
theorem zxwMoveConv {firstWindow secondWindow : ZxpDiagram}
    (hMove : ZxwWindowMove firstWindow secondWindow) :
    ZxwConv firstWindow secondWindow := by
  have hBundle := zxwWindowMoveBundle hMove
  have hStep := ZxwStep.pad firstWindow.sourceArity 0 0 [] [] hMove
    (ZxpLayersWF.nil _) (Nat.zero_add (firstWindow.sourceArity + 0)).symm
    (ZxpLayersWF.nil _)
  rw [zxpPadDiagramIdentityAt firstWindow.sourceArity firstWindow rfl,
    zxpPadDiagramIdentityAt firstWindow.sourceArity secondWindow hBundle.left.symm]
    at hStep
  exact ZxwConv.step hStep

/-- The right slide fired as a conversion, every cell. -/
theorem zxwSlideRightConv (cell : ZxpCell) :
    ZxwConv (zxwSlideRightLhs cell) (zxwSlideRightRhs cell) :=
  zxwMoveConv (ZxwWindowMove.slideRight cell)

/-- The left slide fired as a conversion, every cell. -/
theorem zxwSlideLeftConv (cell : ZxpCell) :
    ZxwConv (zxwSlideLeftLhs cell) (zxwSlideLeftRhs cell) :=
  zxwMoveConv (ZxwWindowMove.slideLeft cell)

/-! ## Stage 5 — engine transports across the embedding -/

/-- Transport: general-k parallel fusion (Z), all arities and shared counts. -/
theorem zxwParallelFusionZ (topLegs botLegs sharedPred : Nat) :
    ZxwConv
      { sourceArity := topLegs
        layers := [[ZxpCell.zSpider topLegs (sharedPred + 1)],
          [ZxpCell.zSpider (sharedPred + 1) botLegs]] }
      { sourceArity := topLegs, layers := [[ZxpCell.zSpider topLegs botLegs]] } :=
  zxwOfZxeConv (zxeParallelFusionZ topLegs botLegs sharedPred)

/-- Transport: general-k parallel fusion (X). -/
theorem zxwParallelFusionX (topLegs botLegs sharedPred : Nat) :
    ZxwConv
      { sourceArity := topLegs
        layers := [[ZxpCell.xSpider topLegs (sharedPred + 1)],
          [ZxpCell.xSpider (sharedPred + 1) botLegs]] }
      { sourceArity := topLegs, layers := [[ZxpCell.xSpider topLegs botLegs]] } :=
  zxwOfZxeConv (zxeParallelFusionX topLegs botLegs sharedPred)

/-- Transport: middle-pair merge fusion (Z), any wire position. -/
theorem zxwMidMergeFuseZ (botOutputs passRight passLeft : Nat) :
    ZxwConv
      { sourceArity := passLeft + (2 + passRight)
        layers := [zxaMidLayer (ZxpCell.zSpider 2 1) passLeft passRight,
          [ZxpCell.zSpider (passLeft + (1 + passRight)) botOutputs]] }
      { sourceArity := passLeft + (2 + passRight)
        layers := [[ZxpCell.zSpider (passLeft + (2 + passRight)) botOutputs]] } :=
  zxwOfZxeConv (zxaMidMergeFuseZ botOutputs passRight passLeft)

/-- Transport: middle-pair merge fusion (X). -/
theorem zxwMidMergeFuseX (botOutputs passRight passLeft : Nat) :
    ZxwConv
      { sourceArity := passLeft + (2 + passRight)
        layers := [zxaMidLayer (ZxpCell.xSpider 2 1) passLeft passRight,
          [ZxpCell.xSpider (passLeft + (1 + passRight)) botOutputs]] }
      { sourceArity := passLeft + (2 + passRight)
        layers := [[ZxpCell.xSpider (passLeft + (2 + passRight)) botOutputs]] } :=
  zxwOfZxeConv (zxaMidMergeFuseX botOutputs passRight passLeft)

/-- Transport: middle-pair fork fusion (Z), any wire position. -/
theorem zxwMidForkFuseZ (topInputs passLeft passRight : Nat) :
    ZxwConv
      { sourceArity := topInputs
        layers := [[ZxpCell.zSpider topInputs (passLeft + (1 + passRight))],
          zxaMidLayer (ZxpCell.zSpider 1 2) passLeft passRight] }
      { sourceArity := topInputs
        layers := [[ZxpCell.zSpider topInputs (passLeft + (2 + passRight))]] } :=
  zxwOfZxeConv (zxaMidForkFuseZ topInputs passLeft passRight)

/-- Transport: middle-pair fork fusion (X). -/
theorem zxwMidForkFuseX (topInputs passLeft passRight : Nat) :
    ZxwConv
      { sourceArity := topInputs
        layers := [[ZxpCell.xSpider topInputs (passLeft + (1 + passRight))],
          zxaMidLayer (ZxpCell.xSpider 1 2) passLeft passRight] }
      { sourceArity := topInputs
        layers := [[ZxpCell.xSpider topInputs (passLeft + (2 + passRight))]] } :=
  zxwOfZxeConv (zxaMidForkFuseX topInputs passLeft passRight)

/-- Transport: within-spider crossing absorption, input side (Z). -/
theorem zxwCrossingAbsorbInputZ (passLeft passRight botOutputs : Nat) :
    ZxwConv
      { sourceArity := passLeft + (2 + passRight)
        layers := [zxaMidLayer ZxpCell.crossing passLeft passRight,
          [ZxpCell.zSpider (passLeft + (2 + passRight)) botOutputs]] }
      { sourceArity := passLeft + (2 + passRight)
        layers := [[ZxpCell.zSpider (passLeft + (2 + passRight)) botOutputs]] } :=
  zxwOfZxeConv (zxaCrossingAbsorbInputZ passLeft passRight botOutputs)

/-- Transport: within-spider crossing absorption, input side (X). -/
theorem zxwCrossingAbsorbInputX (passLeft passRight botOutputs : Nat) :
    ZxwConv
      { sourceArity := passLeft + (2 + passRight)
        layers := [zxaMidLayer ZxpCell.crossing passLeft passRight,
          [ZxpCell.xSpider (passLeft + (2 + passRight)) botOutputs]] }
      { sourceArity := passLeft + (2 + passRight)
        layers := [[ZxpCell.xSpider (passLeft + (2 + passRight)) botOutputs]] } :=
  zxwOfZxeConv (zxaCrossingAbsorbInputX passLeft passRight botOutputs)

/-- Transport: within-spider crossing absorption, output side (Z). -/
theorem zxwCrossingAbsorbOutputZ (topInputs passLeft passRight : Nat) :
    ZxwConv
      { sourceArity := topInputs
        layers := [[ZxpCell.zSpider topInputs (passLeft + (2 + passRight))],
          zxaMidLayer ZxpCell.crossing passLeft passRight] }
      { sourceArity := topInputs
        layers := [[ZxpCell.zSpider topInputs (passLeft + (2 + passRight))]] } :=
  zxwOfZxeConv (zxaCrossingAbsorbOutputZ topInputs passLeft passRight)

/-- Transport: within-spider crossing absorption, output side (X). -/
theorem zxwCrossingAbsorbOutputX (topInputs passLeft passRight : Nat) :
    ZxwConv
      { sourceArity := topInputs
        layers := [[ZxpCell.xSpider topInputs (passLeft + (2 + passRight))],
          zxaMidLayer ZxpCell.crossing passLeft passRight] }
      { sourceArity := topInputs
        layers := [[ZxpCell.xSpider topInputs (passLeft + (2 + passRight))]] } :=
  zxwOfZxeConv (zxaCrossingAbsorbOutputX topInputs passLeft passRight)

/-- Transport: arbitrary crossing walks absorb on output legs (Z). -/
theorem zxwWalkAbsorbOutputZ (topInputs strandCount : Nat)
    {walkLayers : List (List ZxpCell)} (hWalk : ZxaSwapWalk strandCount walkLayers) :
    ZxwConv
      { sourceArity := topInputs
        layers := [ZxpCell.zSpider topInputs strandCount] :: walkLayers }
      { sourceArity := topInputs
        layers := [[ZxpCell.zSpider topInputs strandCount]] } :=
  zxwOfZxeConv (zxaWalkAbsorbOutputZ topInputs strandCount hWalk)

/-- Transport: arbitrary crossing walks absorb on output legs (X). -/
theorem zxwWalkAbsorbOutputX (topInputs strandCount : Nat)
    {walkLayers : List (List ZxpCell)} (hWalk : ZxaSwapWalk strandCount walkLayers) :
    ZxwConv
      { sourceArity := topInputs
        layers := [ZxpCell.xSpider topInputs strandCount] :: walkLayers }
      { sourceArity := topInputs
        layers := [[ZxpCell.xSpider topInputs strandCount]] } :=
  zxwOfZxeConv (zxaWalkAbsorbOutputX topInputs strandCount hWalk)

/-- Transport: arbitrary crossing walks absorb on input legs (Z). -/
theorem zxwWalkAbsorbInputZ (strandCount botOutputs : Nat)
    {walkLayers : List (List ZxpCell)} (hWalk : ZxaSwapWalk strandCount walkLayers) :
    ZxwConv
      { sourceArity := strandCount
        layers := zxpCatLayers walkLayers
          [[ZxpCell.zSpider strandCount botOutputs]] }
      { sourceArity := strandCount
        layers := [[ZxpCell.zSpider strandCount botOutputs]] } :=
  zxwOfZxeConv (zxaWalkAbsorbInputZ strandCount botOutputs hWalk)

/-- Transport: arbitrary crossing walks absorb on input legs (X). -/
theorem zxwWalkAbsorbInputX (strandCount botOutputs : Nat)
    {walkLayers : List (List ZxpCell)} (hWalk : ZxaSwapWalk strandCount walkLayers) :
    ZxwConv
      { sourceArity := strandCount
        layers := zxpCatLayers walkLayers
          [[ZxpCell.xSpider strandCount botOutputs]] }
      { sourceArity := strandCount
        layers := [[ZxpCell.xSpider strandCount botOutputs]] } :=
  zxwOfZxeConv (zxaWalkAbsorbInputX strandCount botOutputs hWalk)

/-! ## Stage 6 — THE GATE RE-RUN over `ZxwConv` (arc law: refutation pass first)

The wire-vanishing fold engine extended to the wiring moves.  THE HONEST CORE:
the slides are NOT balanced for the crossing count — `slideRight cell` carries
`cod cell` staircase crossings on one side and `dom cell` on the other — so slide
balance is a REAL new constraint, computed below (`zxwSlideBalanceForcesCrossingZero`),
not a free pass like the exchange was. -/

/-- Right-cancellation for Nat addition, structural (no Init order lemmas). -/
theorem zxwAddCancelRight : (firstValue secondValue : Nat) -> (baseValue : Nat) ->
    firstValue + baseValue = secondValue + baseValue -> firstValue = secondValue
  | _firstValue, _secondValue, 0, hEq => hEq
  | firstValue, secondValue, basePred + 1, hEq =>
      zxwAddCancelRight firstValue secondValue basePred (Nat.succ.inj hEq)

/-- Any weight vanishing on wire AND crossing folds to zero over the right
staircase. -/
theorem zxwStairFromRightFoldVanishing (cellWeight : ZxpCell -> Nat)
    (hWireZero : cellWeight ZxpCell.wire = 0)
    (hCrossingZero : cellWeight ZxpCell.crossing = 0) :
    (stepCount : Nat) ->
    zxgLayersFold cellWeight (zxwStairFromRightLayers stepCount) = 0
  | 0 => rfl
  | stepPred + 1 => by
      show zxgCellFold cellWeight
          (zxpCatCells (zxpWireCells stepPred) [ZxpCell.crossing])
        + zxgLayersFold cellWeight
            (zxpWhiskerLayers 0 1 (zxwStairFromRightLayers stepPred)) = 0
      rw [zxgCellFoldCat cellWeight (zxpWireCells stepPred) [ZxpCell.crossing],
        zxgCellFoldWires cellWeight hWireZero stepPred,
        zxgLayersFoldWhisker cellWeight hWireZero 0 1
          (zxwStairFromRightLayers stepPred),
        zxwStairFromRightFoldVanishing cellWeight hWireZero hCrossingZero stepPred]
      show 0 + (cellWeight ZxpCell.crossing + 0) + 0 = 0
      rw [hCrossingZero]

/-- Any weight vanishing on wire AND crossing folds to zero over the left
staircase. -/
theorem zxwStairFromLeftFoldVanishing (cellWeight : ZxpCell -> Nat)
    (hWireZero : cellWeight ZxpCell.wire = 0)
    (hCrossingZero : cellWeight ZxpCell.crossing = 0) :
    (stepCount : Nat) ->
    zxgLayersFold cellWeight (zxwStairFromLeftLayers stepCount) = 0
  | 0 => rfl
  | stepPred + 1 => by
      show (cellWeight ZxpCell.crossing
          + zxgCellFold cellWeight (zxpWireCells stepPred))
        + zxgLayersFold cellWeight
            (zxpWhiskerLayers 1 0 (zxwStairFromLeftLayers stepPred)) = 0
      rw [hCrossingZero, zxgCellFoldWires cellWeight hWireZero stepPred,
        zxgLayersFoldWhisker cellWeight hWireZero 1 0
          (zxwStairFromLeftLayers stepPred),
        zxwStairFromLeftFoldVanishing cellWeight hWireZero hCrossingZero stepPred]

/-- Crossing count of the right staircase: exactly `stepCount`. -/
theorem zxwStairFromRightCrossFold : (stepCount : Nat) ->
    zxgLayersFold zxgCellCrossCountWeight (zxwStairFromRightLayers stepCount)
      = stepCount
  | 0 => rfl
  | stepPred + 1 => by
      show zxgCellFold zxgCellCrossCountWeight
          (zxpCatCells (zxpWireCells stepPred) [ZxpCell.crossing])
        + zxgLayersFold zxgCellCrossCountWeight
            (zxpWhiskerLayers 0 1 (zxwStairFromRightLayers stepPred))
        = stepPred + 1
      rw [zxgCellFoldCat zxgCellCrossCountWeight (zxpWireCells stepPred)
          [ZxpCell.crossing],
        zxgCellFoldWires zxgCellCrossCountWeight rfl stepPred,
        zxgLayersFoldWhisker zxgCellCrossCountWeight rfl 0 1
          (zxwStairFromRightLayers stepPred),
        zxwStairFromRightCrossFold stepPred, Nat.zero_add]
      show 1 + stepPred = stepPred + 1
      exact Nat.add_comm 1 stepPred

/-- Crossing count of the left staircase: exactly `stepCount`. -/
theorem zxwStairFromLeftCrossFold : (stepCount : Nat) ->
    zxgLayersFold zxgCellCrossCountWeight (zxwStairFromLeftLayers stepCount)
      = stepCount
  | 0 => rfl
  | stepPred + 1 => by
      show (zxgCellCrossCountWeight ZxpCell.crossing
          + zxgCellFold zxgCellCrossCountWeight (zxpWireCells stepPred))
        + zxgLayersFold zxgCellCrossCountWeight
            (zxpWhiskerLayers 1 0 (zxwStairFromLeftLayers stepPred))
        = stepPred + 1
      rw [zxgCellFoldWires zxgCellCrossCountWeight rfl stepPred,
        zxgLayersFoldWhisker zxgCellCrossCountWeight rfl 1 0
          (zxwStairFromLeftLayers stepPred),
        zxwStairFromLeftCrossFold stepPred]
      show 1 + stepPred = stepPred + 1
      exact Nat.add_comm 1 stepPred

/-- Whiskering preserves the layer count. -/
theorem zxwLayerCountWhisker (leftWires rightWires : Nat) :
    (windowLayers : List (List ZxpCell)) ->
    zxgLayerCount (zxpWhiskerLayers leftWires rightWires windowLayers)
      = zxgLayerCount windowLayers
  | [] => rfl
  | layer :: restLayers => by
      show zxgLayerCount (zxpWhiskerLayers leftWires rightWires restLayers) + 1
        = zxgLayerCount restLayers + 1
      rw [zxwLayerCountWhisker leftWires rightWires restLayers]

/-- Layer count distributes over layer-list concatenation. -/
theorem zxwLayerCountCat : (firstLayers secondLayers : List (List ZxpCell)) ->
    zxgLayerCount (zxpCatLayers firstLayers secondLayers)
      = zxgLayerCount firstLayers + zxgLayerCount secondLayers
  | [], secondLayers => (Nat.zero_add (zxgLayerCount secondLayers)).symm
  | headLayer :: restLayers, secondLayers => by
      show zxgLayerCount (zxpCatLayers restLayers secondLayers) + 1
        = (zxgLayerCount restLayers + 1) + zxgLayerCount secondLayers
      rw [zxwLayerCountCat restLayers secondLayers,
        Nat.add_assoc (zxgLayerCount restLayers) (zxgLayerCount secondLayers) 1,
        Nat.add_comm (zxgLayerCount secondLayers) 1,
        <- Nat.add_assoc (zxgLayerCount restLayers) 1
          (zxgLayerCount secondLayers)]

theorem zxwStairFromRightLayerCount : (stepCount : Nat) ->
    zxgLayerCount (zxwStairFromRightLayers stepCount) = stepCount
  | 0 => rfl
  | stepPred + 1 => by
      show zxgLayerCount
          (zxpWhiskerLayers 0 1 (zxwStairFromRightLayers stepPred)) + 1
        = stepPred + 1
      rw [zxwLayerCountWhisker 0 1 (zxwStairFromRightLayers stepPred),
        zxwStairFromRightLayerCount stepPred]

theorem zxwStairFromLeftLayerCount : (stepCount : Nat) ->
    zxgLayerCount (zxwStairFromLeftLayers stepCount) = stepCount
  | 0 => rfl
  | stepPred + 1 => by
      show zxgLayerCount
          (zxpWhiskerLayers 1 0 (zxwStairFromLeftLayers stepPred)) + 1
        = stepPred + 1
      rw [zxwLayerCountWhisker 1 0 (zxwStairFromLeftLayers stepPred),
        zxwStairFromLeftLayerCount stepPred]

/-- Wire count of a right-whiskered window: one fresh wire per layer. -/
theorem zxwWireFoldWhisker01 : (windowLayers : List (List ZxpCell)) ->
    zxgLayersFold zxgCellWireCountWeight (zxpWhiskerLayers 0 1 windowLayers)
      = zxgLayersFold zxgCellWireCountWeight windowLayers
        + zxgLayerCount windowLayers
  | [] => rfl
  | layer :: restLayers => by
      show zxgCellFold zxgCellWireCountWeight (zxpWhiskerLayer 0 1 layer)
          + zxgLayersFold zxgCellWireCountWeight
            (zxpWhiskerLayers 0 1 restLayers)
        = (zxgCellFold zxgCellWireCountWeight layer
            + zxgLayersFold zxgCellWireCountWeight restLayers)
          + (zxgLayerCount restLayers + 1)
      have hLayer : zxgCellFold zxgCellWireCountWeight (zxpWhiskerLayer 0 1 layer)
          = zxgCellFold zxgCellWireCountWeight layer + 1 := by
        show zxgCellFold zxgCellWireCountWeight
            (zxpCatCells (zxpWireCells 0) (zxpCatCells layer (zxpWireCells 1)))
          = zxgCellFold zxgCellWireCountWeight layer + 1
        rw [zxgCellFoldCat zxgCellWireCountWeight (zxpWireCells 0)
            (zxpCatCells layer (zxpWireCells 1)),
          zxgCellFoldCat zxgCellWireCountWeight layer (zxpWireCells 1),
          zxrWireCountFoldWires 0, zxrWireCountFoldWires 1, Nat.zero_add]
      rw [hLayer, zxwWireFoldWhisker01 restLayers,
        zxgAddMedial (zxgCellFold zxgCellWireCountWeight layer) 1
          (zxgLayersFold zxgCellWireCountWeight restLayers)
          (zxgLayerCount restLayers),
        Nat.add_comm 1 (zxgLayerCount restLayers)]

/-- Wire count of a left-whiskered window: one fresh wire per layer. -/
theorem zxwWireFoldWhisker10 : (windowLayers : List (List ZxpCell)) ->
    zxgLayersFold zxgCellWireCountWeight (zxpWhiskerLayers 1 0 windowLayers)
      = zxgLayersFold zxgCellWireCountWeight windowLayers
        + zxgLayerCount windowLayers
  | [] => rfl
  | layer :: restLayers => by
      show zxgCellFold zxgCellWireCountWeight (zxpWhiskerLayer 1 0 layer)
          + zxgLayersFold zxgCellWireCountWeight
            (zxpWhiskerLayers 1 0 restLayers)
        = (zxgCellFold zxgCellWireCountWeight layer
            + zxgLayersFold zxgCellWireCountWeight restLayers)
          + (zxgLayerCount restLayers + 1)
      have hLayer : zxgCellFold zxgCellWireCountWeight (zxpWhiskerLayer 1 0 layer)
          = zxgCellFold zxgCellWireCountWeight layer + 1 := by
        show zxgCellFold zxgCellWireCountWeight
            (zxpCatCells (zxpWireCells 1) (zxpCatCells layer (zxpWireCells 0)))
          = zxgCellFold zxgCellWireCountWeight layer + 1
        rw [zxgCellFoldCat zxgCellWireCountWeight (zxpWireCells 1)
            (zxpCatCells layer (zxpWireCells 0)),
          zxgCellFoldCat zxgCellWireCountWeight layer (zxpWireCells 0)]
        show 1 + 0 + (zxgCellFold zxgCellWireCountWeight layer + 0)
          = zxgCellFold zxgCellWireCountWeight layer + 1
        exact Nat.add_comm (1 + 0) (zxgCellFold zxgCellWireCountWeight layer + 0)
      rw [hLayer, zxwWireFoldWhisker10 restLayers,
        zxgAddMedial (zxgCellFold zxgCellWireCountWeight layer) 1
          (zxgLayersFold zxgCellWireCountWeight restLayers)
          (zxgLayerCount restLayers),
        Nat.add_comm 1 (zxgLayerCount restLayers)]

/-- The right staircase's wire count is even. -/
theorem zxwStairFromRightWireFoldParity : (stepCount : Nat) ->
    zxgParityB (zxgLayersFold zxgCellWireCountWeight
      (zxwStairFromRightLayers stepCount)) = false
  | 0 => rfl
  | stepPred + 1 => by
      show zxgParityB (zxgCellFold zxgCellWireCountWeight
          (zxpCatCells (zxpWireCells stepPred) [ZxpCell.crossing])
        + zxgLayersFold zxgCellWireCountWeight
            (zxpWhiskerLayers 0 1 (zxwStairFromRightLayers stepPred))) = false
      rw [zxgCellFoldCat zxgCellWireCountWeight (zxpWireCells stepPred)
          [ZxpCell.crossing],
        zxrWireCountFoldWires stepPred,
        zxwWireFoldWhisker01 (zxwStairFromRightLayers stepPred),
        zxwStairFromRightLayerCount stepPred]
      show zxgParityB ((stepPred + (0 + 0))
        + (zxgLayersFold zxgCellWireCountWeight
            (zxwStairFromRightLayers stepPred) + stepPred)) = false
      rw [Nat.add_zero 0, Nat.add_zero stepPred,
        zxgParityBAdd stepPred
          (zxgLayersFold zxgCellWireCountWeight
            (zxwStairFromRightLayers stepPred) + stepPred),
        zxgParityBAdd
          (zxgLayersFold zxgCellWireCountWeight (zxwStairFromRightLayers stepPred))
          stepPred,
        zxwStairFromRightWireFoldParity stepPred, zxpXorBFalseLeft]
      exact zxpXorBSelf (zxgParityB stepPred)

/-- The left staircase's wire count is even. -/
theorem zxwStairFromLeftWireFoldParity : (stepCount : Nat) ->
    zxgParityB (zxgLayersFold zxgCellWireCountWeight
      (zxwStairFromLeftLayers stepCount)) = false
  | 0 => rfl
  | stepPred + 1 => by
      show zxgParityB ((zxgCellWireCountWeight ZxpCell.crossing
          + zxgCellFold zxgCellWireCountWeight (zxpWireCells stepPred))
        + zxgLayersFold zxgCellWireCountWeight
            (zxpWhiskerLayers 1 0 (zxwStairFromLeftLayers stepPred))) = false
      rw [zxrWireCountFoldWires stepPred,
        zxwWireFoldWhisker10 (zxwStairFromLeftLayers stepPred),
        zxwStairFromLeftLayerCount stepPred]
      show zxgParityB ((0 + stepPred)
        + (zxgLayersFold zxgCellWireCountWeight
            (zxwStairFromLeftLayers stepPred) + stepPred)) = false
      rw [Nat.zero_add stepPred,
        zxgParityBAdd stepPred
          (zxgLayersFold zxgCellWireCountWeight
            (zxwStairFromLeftLayers stepPred) + stepPred),
        zxgParityBAdd
          (zxgLayersFold zxgCellWireCountWeight (zxwStairFromLeftLayers stepPred))
          stepPred,
        zxwStairFromLeftWireFoldParity stepPred, zxpXorBFalseLeft]
      exact zxpXorBSelf (zxgParityB stepPred)

/-! ### Per-component fold equalities for the slide families -/

/-- Any weight vanishing on wire and crossing is EXACTLY balanced on every right
slide (the cell appears once on each side; the staircases are invisible). -/
theorem zxwSlideRightFoldSpiderWeightEq (cellWeight : ZxpCell -> Nat)
    (hWireZero : cellWeight ZxpCell.wire = 0)
    (hCrossingZero : cellWeight ZxpCell.crossing = 0) (cell : ZxpCell) :
    zxgLayersFold cellWeight (zxwSlideRightLhs cell).layers
      = zxgLayersFold cellWeight (zxwSlideRightRhs cell).layers := by
  have hLhs : zxgLayersFold cellWeight (zxwSlideRightLhs cell).layers
      = cellWeight cell := by
    show zxgCellFold cellWeight [cell, ZxpCell.wire]
        + zxgLayersFold cellWeight
            (zxwStairFromRightLayers (zxpCellCodArity cell))
      = cellWeight cell
    rw [zxwStairFromRightFoldVanishing cellWeight hWireZero hCrossingZero
      (zxpCellCodArity cell)]
    show (cellWeight cell + (cellWeight ZxpCell.wire + 0)) + 0 = cellWeight cell
    rw [hWireZero]
    exact rfl
  have hRhs : zxgLayersFold cellWeight (zxwSlideRightRhs cell).layers
      = cellWeight cell := by
    show zxgLayersFold cellWeight
        (zxpCatLayers (zxwStairFromRightLayers (zxpCellDomArity cell))
          [[ZxpCell.wire, cell]])
      = cellWeight cell
    rw [zxgLayersFoldCat cellWeight
        (zxwStairFromRightLayers (zxpCellDomArity cell)) [[ZxpCell.wire, cell]],
      zxwStairFromRightFoldVanishing cellWeight hWireZero hCrossingZero
        (zxpCellDomArity cell),
      Nat.zero_add]
    show (cellWeight ZxpCell.wire + (cellWeight cell + 0)) + 0 = cellWeight cell
    rw [hWireZero, Nat.zero_add]
    exact rfl
  exact hLhs.trans hRhs.symm

/-- Any weight vanishing on wire and crossing is EXACTLY balanced on every left
slide. -/
theorem zxwSlideLeftFoldSpiderWeightEq (cellWeight : ZxpCell -> Nat)
    (hWireZero : cellWeight ZxpCell.wire = 0)
    (hCrossingZero : cellWeight ZxpCell.crossing = 0) (cell : ZxpCell) :
    zxgLayersFold cellWeight (zxwSlideLeftLhs cell).layers
      = zxgLayersFold cellWeight (zxwSlideLeftRhs cell).layers := by
  have hLhs : zxgLayersFold cellWeight (zxwSlideLeftLhs cell).layers
      = cellWeight cell := by
    show zxgCellFold cellWeight [ZxpCell.wire, cell]
        + zxgLayersFold cellWeight
            (zxwStairFromLeftLayers (zxpCellCodArity cell))
      = cellWeight cell
    rw [zxwStairFromLeftFoldVanishing cellWeight hWireZero hCrossingZero
      (zxpCellCodArity cell)]
    show (cellWeight ZxpCell.wire + (cellWeight cell + 0)) + 0 = cellWeight cell
    rw [hWireZero, Nat.zero_add]
    exact rfl
  have hRhs : zxgLayersFold cellWeight (zxwSlideLeftRhs cell).layers
      = cellWeight cell := by
    show zxgLayersFold cellWeight
        (zxpCatLayers (zxwStairFromLeftLayers (zxpCellDomArity cell))
          [[cell, ZxpCell.wire]])
      = cellWeight cell
    rw [zxgLayersFoldCat cellWeight
        (zxwStairFromLeftLayers (zxpCellDomArity cell)) [[cell, ZxpCell.wire]],
      zxwStairFromLeftFoldVanishing cellWeight hWireZero hCrossingZero
        (zxpCellDomArity cell),
      Nat.zero_add]
    show (cellWeight cell + (cellWeight ZxpCell.wire + 0)) + 0 = cellWeight cell
    rw [hWireZero]
    exact rfl
  exact hLhs.trans hRhs.symm

/-- The right slide's wire-count parities agree on both sides. -/
theorem zxwSlideRightWireParityEq (cell : ZxpCell) :
    zxgParityB (zxgLayersFold zxgCellWireCountWeight
        (zxwSlideRightLhs cell).layers)
      = zxgParityB (zxgLayersFold zxgCellWireCountWeight
          (zxwSlideRightRhs cell).layers) := by
  have hLhs : zxgLayersFold zxgCellWireCountWeight (zxwSlideRightLhs cell).layers
      = (zxgCellWireCountWeight cell + 1)
        + zxgLayersFold zxgCellWireCountWeight
            (zxwStairFromRightLayers (zxpCellCodArity cell)) := rfl
  have hRhs : zxgLayersFold zxgCellWireCountWeight (zxwSlideRightRhs cell).layers
      = zxgLayersFold zxgCellWireCountWeight
          (zxwStairFromRightLayers (zxpCellDomArity cell))
        + (1 + zxgCellWireCountWeight cell) := by
    show zxgLayersFold zxgCellWireCountWeight
        (zxpCatLayers (zxwStairFromRightLayers (zxpCellDomArity cell))
          [[ZxpCell.wire, cell]])
      = _
    rw [zxgLayersFoldCat zxgCellWireCountWeight
      (zxwStairFromRightLayers (zxpCellDomArity cell)) [[ZxpCell.wire, cell]]]
    exact rfl
  rw [hLhs, hRhs,
    zxgParityBAdd (zxgCellWireCountWeight cell + 1)
      (zxgLayersFold zxgCellWireCountWeight
        (zxwStairFromRightLayers (zxpCellCodArity cell))),
    zxgParityBAdd
      (zxgLayersFold zxgCellWireCountWeight
        (zxwStairFromRightLayers (zxpCellDomArity cell)))
      (1 + zxgCellWireCountWeight cell),
    zxwStairFromRightWireFoldParity (zxpCellCodArity cell),
    zxwStairFromRightWireFoldParity (zxpCellDomArity cell),
    zxpXorBFalseRight (zxgParityB (zxgCellWireCountWeight cell + 1)),
    zxpXorBFalseLeft (zxgParityB (1 + zxgCellWireCountWeight cell)),
    zxgParityBAdd (zxgCellWireCountWeight cell) 1,
    zxgParityBAdd 1 (zxgCellWireCountWeight cell)]
  exact zxpXorBComm (zxgParityB (zxgCellWireCountWeight cell)) (zxgParityB 1)

/-- The left slide's wire-count parities agree on both sides. -/
theorem zxwSlideLeftWireParityEq (cell : ZxpCell) :
    zxgParityB (zxgLayersFold zxgCellWireCountWeight
        (zxwSlideLeftLhs cell).layers)
      = zxgParityB (zxgLayersFold zxgCellWireCountWeight
          (zxwSlideLeftRhs cell).layers) := by
  have hLhs : zxgLayersFold zxgCellWireCountWeight (zxwSlideLeftLhs cell).layers
      = (1 + zxgCellWireCountWeight cell)
        + zxgLayersFold zxgCellWireCountWeight
            (zxwStairFromLeftLayers (zxpCellCodArity cell)) := rfl
  have hRhs : zxgLayersFold zxgCellWireCountWeight (zxwSlideLeftRhs cell).layers
      = zxgLayersFold zxgCellWireCountWeight
          (zxwStairFromLeftLayers (zxpCellDomArity cell))
        + (zxgCellWireCountWeight cell + 1) := by
    show zxgLayersFold zxgCellWireCountWeight
        (zxpCatLayers (zxwStairFromLeftLayers (zxpCellDomArity cell))
          [[cell, ZxpCell.wire]])
      = _
    rw [zxgLayersFoldCat zxgCellWireCountWeight
      (zxwStairFromLeftLayers (zxpCellDomArity cell)) [[cell, ZxpCell.wire]]]
    exact rfl
  rw [hLhs, hRhs,
    zxgParityBAdd (1 + zxgCellWireCountWeight cell)
      (zxgLayersFold zxgCellWireCountWeight
        (zxwStairFromLeftLayers (zxpCellCodArity cell))),
    zxgParityBAdd
      (zxgLayersFold zxgCellWireCountWeight
        (zxwStairFromLeftLayers (zxpCellDomArity cell)))
      (zxgCellWireCountWeight cell + 1),
    zxwStairFromLeftWireFoldParity (zxpCellCodArity cell),
    zxwStairFromLeftWireFoldParity (zxpCellDomArity cell),
    zxpXorBFalseRight (zxgParityB (1 + zxgCellWireCountWeight cell)),
    zxpXorBFalseLeft (zxgParityB (zxgCellWireCountWeight cell + 1)),
    zxgParityBAdd 1 (zxgCellWireCountWeight cell),
    zxgParityBAdd (zxgCellWireCountWeight cell) 1]
  exact zxpXorBComm (zxgParityB 1) (zxgParityB (zxgCellWireCountWeight cell))

/-- THE HONEST CROSSING-COUNT DELTA (right): the slide trades `cod` staircase
crossings for `dom` staircase crossings — mod 2, exactly `parity(dom + cod)`. -/
theorem zxwSlideRightCrossDelta (cell : ZxpCell) :
    zxpXorB
        (zxgParityB (zxgLayersFold zxgCellCrossCountWeight
          (zxwSlideRightLhs cell).layers))
        (zxgParityB (zxgLayersFold zxgCellCrossCountWeight
          (zxwSlideRightRhs cell).layers))
      = zxgParityB (zxpCellDomArity cell + zxpCellCodArity cell) := by
  have hLhs : zxgLayersFold zxgCellCrossCountWeight (zxwSlideRightLhs cell).layers
      = zxgCellCrossCountWeight cell + zxpCellCodArity cell := by
    show zxgCellFold zxgCellCrossCountWeight [cell, ZxpCell.wire]
        + zxgLayersFold zxgCellCrossCountWeight
            (zxwStairFromRightLayers (zxpCellCodArity cell))
      = zxgCellCrossCountWeight cell + zxpCellCodArity cell
    rw [zxwStairFromRightCrossFold (zxpCellCodArity cell)]
    exact rfl
  have hRhs : zxgLayersFold zxgCellCrossCountWeight (zxwSlideRightRhs cell).layers
      = zxpCellDomArity cell + (0 + zxgCellCrossCountWeight cell) := by
    show zxgLayersFold zxgCellCrossCountWeight
        (zxpCatLayers (zxwStairFromRightLayers (zxpCellDomArity cell))
          [[ZxpCell.wire, cell]])
      = _
    rw [zxgLayersFoldCat zxgCellCrossCountWeight
        (zxwStairFromRightLayers (zxpCellDomArity cell)) [[ZxpCell.wire, cell]],
      zxwStairFromRightCrossFold (zxpCellDomArity cell)]
    exact rfl
  rw [hLhs, hRhs, Nat.zero_add,
    zxgParityBAdd (zxgCellCrossCountWeight cell) (zxpCellCodArity cell),
    zxgParityBAdd (zxpCellDomArity cell) (zxgCellCrossCountWeight cell),
    zxpXorBComm (zxgParityB (zxgCellCrossCountWeight cell))
      (zxgParityB (zxpCellCodArity cell)),
    zxpXorBComm (zxgParityB (zxpCellDomArity cell))
      (zxgParityB (zxgCellCrossCountWeight cell)),
    zxgXorBCancelMiddle (zxgParityB (zxpCellCodArity cell))
      (zxgParityB (zxgCellCrossCountWeight cell))
      (zxgParityB (zxpCellDomArity cell)),
    zxpXorBComm (zxgParityB (zxpCellCodArity cell))
      (zxgParityB (zxpCellDomArity cell)),
    zxgParityBAdd (zxpCellDomArity cell) (zxpCellCodArity cell)]

/-- THE HONEST CROSSING-COUNT DELTA (left). -/
theorem zxwSlideLeftCrossDelta (cell : ZxpCell) :
    zxpXorB
        (zxgParityB (zxgLayersFold zxgCellCrossCountWeight
          (zxwSlideLeftLhs cell).layers))
        (zxgParityB (zxgLayersFold zxgCellCrossCountWeight
          (zxwSlideLeftRhs cell).layers))
      = zxgParityB (zxpCellDomArity cell + zxpCellCodArity cell) := by
  have hLhs : zxgLayersFold zxgCellCrossCountWeight (zxwSlideLeftLhs cell).layers
      = (0 + zxgCellCrossCountWeight cell) + zxpCellCodArity cell := by
    show zxgCellFold zxgCellCrossCountWeight [ZxpCell.wire, cell]
        + zxgLayersFold zxgCellCrossCountWeight
            (zxwStairFromLeftLayers (zxpCellCodArity cell))
      = (0 + zxgCellCrossCountWeight cell) + zxpCellCodArity cell
    rw [zxwStairFromLeftCrossFold (zxpCellCodArity cell)]
    exact rfl
  have hRhs : zxgLayersFold zxgCellCrossCountWeight (zxwSlideLeftRhs cell).layers
      = zxpCellDomArity cell + zxgCellCrossCountWeight cell := by
    show zxgLayersFold zxgCellCrossCountWeight
        (zxpCatLayers (zxwStairFromLeftLayers (zxpCellDomArity cell))
          [[cell, ZxpCell.wire]])
      = _
    rw [zxgLayersFoldCat zxgCellCrossCountWeight
        (zxwStairFromLeftLayers (zxpCellDomArity cell)) [[cell, ZxpCell.wire]],
      zxwStairFromLeftCrossFold (zxpCellDomArity cell)]
    exact rfl
  rw [hLhs, hRhs, Nat.zero_add,
    zxgParityBAdd (zxgCellCrossCountWeight cell) (zxpCellCodArity cell),
    zxgParityBAdd (zxpCellDomArity cell) (zxgCellCrossCountWeight cell),
    zxpXorBComm (zxgParityB (zxgCellCrossCountWeight cell))
      (zxgParityB (zxpCellCodArity cell)),
    zxpXorBComm (zxgParityB (zxpCellDomArity cell))
      (zxgParityB (zxgCellCrossCountWeight cell)),
    zxgXorBCancelMiddle (zxgParityB (zxpCellCodArity cell))
      (zxgParityB (zxgCellCrossCountWeight cell))
      (zxgParityB (zxpCellDomArity cell)),
    zxpXorBComm (zxgParityB (zxpCellCodArity cell))
      (zxgParityB (zxpCellDomArity cell)),
    zxgParityBAdd (zxpCellDomArity cell) (zxpCellCodArity cell)]

/-- Layer-count delta of the right slide: also `parity(dom + cod)`. -/
theorem zxwSlideRightLayerDelta (cell : ZxpCell) :
    zxpXorB (zxgParityB (zxgLayerCount (zxwSlideRightLhs cell).layers))
        (zxgParityB (zxgLayerCount (zxwSlideRightRhs cell).layers))
      = zxgParityB (zxpCellDomArity cell + zxpCellCodArity cell) := by
  have hLhs : zxgLayerCount (zxwSlideRightLhs cell).layers
      = zxpCellCodArity cell + 1 := by
    show zxgLayerCount (zxwStairFromRightLayers (zxpCellCodArity cell)) + 1
      = zxpCellCodArity cell + 1
    rw [zxwStairFromRightLayerCount (zxpCellCodArity cell)]
  have hRhs : zxgLayerCount (zxwSlideRightRhs cell).layers
      = zxpCellDomArity cell + 1 := by
    show zxgLayerCount
        (zxpCatLayers (zxwStairFromRightLayers (zxpCellDomArity cell))
          [[ZxpCell.wire, cell]])
      = zxpCellDomArity cell + 1
    rw [zxwLayerCountCat (zxwStairFromRightLayers (zxpCellDomArity cell))
        [[ZxpCell.wire, cell]],
      zxwStairFromRightLayerCount (zxpCellDomArity cell)]
    exact rfl
  rw [hLhs, hRhs, zxgParityBAdd (zxpCellCodArity cell) 1,
    zxgParityBAdd (zxpCellDomArity cell) 1,
    zxgXorBMedial (zxgParityB (zxpCellCodArity cell)) (zxgParityB 1)
      (zxgParityB (zxpCellDomArity cell)) (zxgParityB 1),
    zxpXorBSelf (zxgParityB 1),
    zxpXorBFalseRight (zxpXorB (zxgParityB (zxpCellCodArity cell))
      (zxgParityB (zxpCellDomArity cell))),
    zxpXorBComm (zxgParityB (zxpCellCodArity cell))
      (zxgParityB (zxpCellDomArity cell)),
    zxgParityBAdd (zxpCellDomArity cell) (zxpCellCodArity cell)]

/-- Layer-count delta of the left slide. -/
theorem zxwSlideLeftLayerDelta (cell : ZxpCell) :
    zxpXorB (zxgParityB (zxgLayerCount (zxwSlideLeftLhs cell).layers))
        (zxgParityB (zxgLayerCount (zxwSlideLeftRhs cell).layers))
      = zxgParityB (zxpCellDomArity cell + zxpCellCodArity cell) := by
  have hLhs : zxgLayerCount (zxwSlideLeftLhs cell).layers
      = zxpCellCodArity cell + 1 := by
    show zxgLayerCount (zxwStairFromLeftLayers (zxpCellCodArity cell)) + 1
      = zxpCellCodArity cell + 1
    rw [zxwStairFromLeftLayerCount (zxpCellCodArity cell)]
  have hRhs : zxgLayerCount (zxwSlideLeftRhs cell).layers
      = zxpCellDomArity cell + 1 := by
    show zxgLayerCount
        (zxpCatLayers (zxwStairFromLeftLayers (zxpCellDomArity cell))
          [[cell, ZxpCell.wire]])
      = zxpCellDomArity cell + 1
    rw [zxwLayerCountCat (zxwStairFromLeftLayers (zxpCellDomArity cell))
        [[cell, ZxpCell.wire]],
      zxwStairFromLeftLayerCount (zxpCellDomArity cell)]
    exact rfl
  rw [hLhs, hRhs, zxgParityBAdd (zxpCellCodArity cell) 1,
    zxgParityBAdd (zxpCellDomArity cell) 1,
    zxgXorBMedial (zxgParityB (zxpCellCodArity cell)) (zxgParityB 1)
      (zxgParityB (zxpCellDomArity cell)) (zxgParityB 1),
    zxpXorBSelf (zxgParityB 1),
    zxpXorBFalseRight (zxpXorB (zxgParityB (zxpCellCodArity cell))
      (zxgParityB (zxpCellDomArity cell))),
    zxpXorBComm (zxgParityB (zxpCellCodArity cell))
      (zxgParityB (zxpCellDomArity cell)),
    zxgParityBAdd (zxpCellDomArity cell) (zxpCellCodArity cell)]

/-! ### The general slide deltas on the base 7-vector, saturated by two literals -/

/-- THE GENERAL RIGHT-SLIDE DELTA (proved saturation, every cell): the mod-2 delta
on the base count vector is `[0,0,0, parity(dom+cod), parity(dom+cod), 0,0]` —
crossing count and layer count move TOGETHER, everything else is balanced. -/
theorem zxwSlideRightDeltaGeneral (cell : ZxpCell) :
    zxgVectorDeltaMod2 (zxgCountVector (zxwSlideRightLhs cell))
        (zxgCountVector (zxwSlideRightRhs cell))
      = [false, false, false,
          zxgParityB (zxpCellDomArity cell + zxpCellCodArity cell),
          zxgParityB (zxpCellDomArity cell + zxpCellCodArity cell), false, false] := by
  have hZEq := zxwSlideRightFoldSpiderWeightEq zxgCellZCountWeight rfl rfl cell
  have hXEq := zxwSlideRightFoldSpiderWeightEq zxgCellXCountWeight rfl rfl cell
  have hZLegsEq := zxwSlideRightFoldSpiderWeightEq zxgCellZLegsWeight rfl rfl cell
  have hXLegsEq := zxwSlideRightFoldSpiderWeightEq zxgCellXLegsWeight rfl rfl cell
  have hWireEq := zxwSlideRightWireParityEq cell
  have hCrossDelta := zxwSlideRightCrossDelta cell
  have hLayerDelta := zxwSlideRightLayerDelta cell
  show [zxpXorB
      (zxgParityB (zxgLayersFold zxgCellZCountWeight (zxwSlideRightLhs cell).layers))
      (zxgParityB (zxgLayersFold zxgCellZCountWeight (zxwSlideRightRhs cell).layers)),
    zxpXorB
      (zxgParityB (zxgLayersFold zxgCellXCountWeight (zxwSlideRightLhs cell).layers))
      (zxgParityB (zxgLayersFold zxgCellXCountWeight (zxwSlideRightRhs cell).layers)),
    zxpXorB
      (zxgParityB (zxgLayersFold zxgCellWireCountWeight
        (zxwSlideRightLhs cell).layers))
      (zxgParityB (zxgLayersFold zxgCellWireCountWeight
        (zxwSlideRightRhs cell).layers)),
    zxpXorB
      (zxgParityB (zxgLayersFold zxgCellCrossCountWeight
        (zxwSlideRightLhs cell).layers))
      (zxgParityB (zxgLayersFold zxgCellCrossCountWeight
        (zxwSlideRightRhs cell).layers)),
    zxpXorB (zxgParityB (zxgLayerCount (zxwSlideRightLhs cell).layers))
      (zxgParityB (zxgLayerCount (zxwSlideRightRhs cell).layers)),
    zxpXorB
      (zxgParityB (zxgLayersFold zxgCellZLegsWeight (zxwSlideRightLhs cell).layers))
      (zxgParityB (zxgLayersFold zxgCellZLegsWeight (zxwSlideRightRhs cell).layers)),
    zxpXorB
      (zxgParityB (zxgLayersFold zxgCellXLegsWeight (zxwSlideRightLhs cell).layers))
      (zxgParityB (zxgLayersFold zxgCellXLegsWeight (zxwSlideRightRhs cell).layers))]
    = [false, false, false,
        zxgParityB (zxpCellDomArity cell + zxpCellCodArity cell),
        zxgParityB (zxpCellDomArity cell + zxpCellCodArity cell), false, false]
  rw [hZEq, hXEq, hZLegsEq, hXLegsEq, hWireEq, hCrossDelta, hLayerDelta,
    zxpXorBSelf (zxgParityB (zxgLayersFold zxgCellZCountWeight
      (zxwSlideRightRhs cell).layers)),
    zxpXorBSelf (zxgParityB (zxgLayersFold zxgCellXCountWeight
      (zxwSlideRightRhs cell).layers)),
    zxpXorBSelf (zxgParityB (zxgLayersFold zxgCellWireCountWeight
      (zxwSlideRightRhs cell).layers)),
    zxpXorBSelf (zxgParityB (zxgLayersFold zxgCellZLegsWeight
      (zxwSlideRightRhs cell).layers)),
    zxpXorBSelf (zxgParityB (zxgLayersFold zxgCellXLegsWeight
      (zxwSlideRightRhs cell).layers))]

/-- THE GENERAL LEFT-SLIDE DELTA: the same two-component vector. -/
theorem zxwSlideLeftDeltaGeneral (cell : ZxpCell) :
    zxgVectorDeltaMod2 (zxgCountVector (zxwSlideLeftLhs cell))
        (zxgCountVector (zxwSlideLeftRhs cell))
      = [false, false, false,
          zxgParityB (zxpCellDomArity cell + zxpCellCodArity cell),
          zxgParityB (zxpCellDomArity cell + zxpCellCodArity cell), false, false] := by
  have hZEq := zxwSlideLeftFoldSpiderWeightEq zxgCellZCountWeight rfl rfl cell
  have hXEq := zxwSlideLeftFoldSpiderWeightEq zxgCellXCountWeight rfl rfl cell
  have hZLegsEq := zxwSlideLeftFoldSpiderWeightEq zxgCellZLegsWeight rfl rfl cell
  have hXLegsEq := zxwSlideLeftFoldSpiderWeightEq zxgCellXLegsWeight rfl rfl cell
  have hWireEq := zxwSlideLeftWireParityEq cell
  have hCrossDelta := zxwSlideLeftCrossDelta cell
  have hLayerDelta := zxwSlideLeftLayerDelta cell
  show [zxpXorB
      (zxgParityB (zxgLayersFold zxgCellZCountWeight (zxwSlideLeftLhs cell).layers))
      (zxgParityB (zxgLayersFold zxgCellZCountWeight (zxwSlideLeftRhs cell).layers)),
    zxpXorB
      (zxgParityB (zxgLayersFold zxgCellXCountWeight (zxwSlideLeftLhs cell).layers))
      (zxgParityB (zxgLayersFold zxgCellXCountWeight (zxwSlideLeftRhs cell).layers)),
    zxpXorB
      (zxgParityB (zxgLayersFold zxgCellWireCountWeight
        (zxwSlideLeftLhs cell).layers))
      (zxgParityB (zxgLayersFold zxgCellWireCountWeight
        (zxwSlideLeftRhs cell).layers)),
    zxpXorB
      (zxgParityB (zxgLayersFold zxgCellCrossCountWeight
        (zxwSlideLeftLhs cell).layers))
      (zxgParityB (zxgLayersFold zxgCellCrossCountWeight
        (zxwSlideLeftRhs cell).layers)),
    zxpXorB (zxgParityB (zxgLayerCount (zxwSlideLeftLhs cell).layers))
      (zxgParityB (zxgLayerCount (zxwSlideLeftRhs cell).layers)),
    zxpXorB
      (zxgParityB (zxgLayersFold zxgCellZLegsWeight (zxwSlideLeftLhs cell).layers))
      (zxgParityB (zxgLayersFold zxgCellZLegsWeight (zxwSlideLeftRhs cell).layers)),
    zxpXorB
      (zxgParityB (zxgLayersFold zxgCellXLegsWeight (zxwSlideLeftLhs cell).layers))
      (zxgParityB (zxgLayersFold zxgCellXLegsWeight (zxwSlideLeftRhs cell).layers))]
    = [false, false, false,
        zxgParityB (zxpCellDomArity cell + zxpCellCodArity cell),
        zxgParityB (zxpCellDomArity cell + zxpCellCodArity cell), false, false]
  rw [hZEq, hXEq, hZLegsEq, hXLegsEq, hWireEq, hCrossDelta, hLayerDelta,
    zxpXorBSelf (zxgParityB (zxgLayersFold zxgCellZCountWeight
      (zxwSlideLeftRhs cell).layers)),
    zxpXorBSelf (zxgParityB (zxgLayersFold zxgCellXCountWeight
      (zxwSlideLeftRhs cell).layers)),
    zxpXorBSelf (zxgParityB (zxgLayersFold zxgCellWireCountWeight
      (zxwSlideLeftRhs cell).layers)),
    zxpXorBSelf (zxgParityB (zxgLayersFold zxgCellZLegsWeight
      (zxwSlideLeftRhs cell).layers)),
    zxpXorBSelf (zxgParityB (zxgLayersFold zxgCellXLegsWeight
      (zxwSlideLeftRhs cell).layers))]

/-- The odd slide delta literal (crossing parity and layer parity move together). -/
def zxwSlideDeltaOddLiteral : List Bool :=
  [false, false, false, true, true, false, false]

/-- The involution delta literal (one layer disappears, crossings and wires cancel
mod 2). -/
def zxwInvolutionDeltaLiteral : List Bool :=
  [false, false, false, false, true, false, false]

/-- Kernel pin: the involution's delta computes to its literal. -/
theorem zxwInvolutionDeltaValue :
    zxgVectorDeltaMod2 (zxgCountVector zxwInvolutionLhs)
      (zxgCountVector zxwInvolutionRhs) = zxwInvolutionDeltaLiteral := rfl

/-- SATURATION, case form (right): every right-slide delta is zero or the odd
literal. -/
theorem zxwSlideRightDeltaCases (cell : ZxpCell) :
    zxgVectorDeltaMod2 (zxgCountVector (zxwSlideRightLhs cell))
        (zxgCountVector (zxwSlideRightRhs cell)) = zxgZeroFunctional
      \/ zxgVectorDeltaMod2 (zxgCountVector (zxwSlideRightLhs cell))
          (zxgCountVector (zxwSlideRightRhs cell)) = zxwSlideDeltaOddLiteral := by
  cases hParity : zxgParityB (zxpCellDomArity cell + zxpCellCodArity cell) with
  | false =>
      refine Or.inl ?_
      rw [zxwSlideRightDeltaGeneral cell, hParity]
      exact rfl
  | true =>
      refine Or.inr ?_
      rw [zxwSlideRightDeltaGeneral cell, hParity]
      exact rfl

/-- SATURATION, case form (left). -/
theorem zxwSlideLeftDeltaCases (cell : ZxpCell) :
    zxgVectorDeltaMod2 (zxgCountVector (zxwSlideLeftLhs cell))
        (zxgCountVector (zxwSlideLeftRhs cell)) = zxgZeroFunctional
      \/ zxgVectorDeltaMod2 (zxgCountVector (zxwSlideLeftLhs cell))
          (zxgCountVector (zxwSlideLeftRhs cell)) = zxwSlideDeltaOddLiteral := by
  cases hParity : zxgParityB (zxpCellDomArity cell + zxpCellCodArity cell) with
  | false =>
      refine Or.inl ?_
      rw [zxwSlideLeftDeltaGeneral cell, hParity]
      exact rfl
  | true =>
      refine Or.inr ?_
      rw [zxwSlideLeftDeltaGeneral cell, hParity]
      exact rfl

/-- THE WIRING-EXTENDED DELTA TABLE: the exchange-extended table plus the slide
literal and the involution literal (which saturate the whole new-move family by
the case lemmas above). -/
def zxwExtendedDeltaTable : List (List Bool) :=
  zxpCatRows zxeExtendedDeltaTable [zxwSlideDeltaOddLiteral, zxwInvolutionDeltaLiteral]

/-- KERNEL PIN: the wiring-extended delta row space equals the gate's SAME
6-dimensional basis — the wiring schema adds moves but NO new mod-2 direction
(crossing parity and layer parity were already independently movable). -/
theorem zxwExtendedDeltaSpanBasisPin :
    zxpSpanEqB zxwExtendedDeltaTable zxgDeltaSpanBasis = true := rfl

/-- Classifier over the wiring-extended table: orthogonality holds exactly for the
zero functional and the legs-parity functional. -/
def zxwIsPreservedExactlyLegsParityB : List (List Bool) -> Bool
  | [] => true
  | headFunctional :: restFunctionals =>
      cond (zxgBoolEqB (zxgIsOrthogonalToAllB headFunctional zxwExtendedDeltaTable)
          (cond (zxgRowEqB headFunctional zxgZeroFunctional) true
            (zxgRowEqB headFunctional zxgLegsParityFunctional)))
        (zxwIsPreservedExactlyLegsParityB restFunctionals) false

/-- KERNEL PIN: over ALL 128 mod-2 functionals, the preserved lattice of the
wiring-extended move set is STILL exactly {0, legs-parity} — and the survivor stays
boundary-determined by the gate's per-diagram theorem
(`zxgLegsParityFunctionalBoundaryDetermined`), untouched by any move-set
extension. -/
theorem zxwPreservedLatticeReclassified :
    zxwIsPreservedExactlyLegsParityB (zxgAllBoolVectors 7) = true := rfl

/-- The survivor is orthogonal to EVERY right-slide delta at every cell. -/
theorem zxwLegsParityOrthogonalSlideRightDelta (cell : ZxpCell) :
    zxgDotB zxgLegsParityFunctional
        (zxgVectorDeltaMod2 (zxgCountVector (zxwSlideRightLhs cell))
          (zxgCountVector (zxwSlideRightRhs cell)))
      = false := by
  cases zxwSlideRightDeltaCases cell with
  | inl hZero =>
      rw [hZero]
      exact rfl
  | inr hOdd =>
      rw [hOdd]
      exact rfl

/-- The survivor is orthogonal to EVERY left-slide delta at every cell. -/
theorem zxwLegsParityOrthogonalSlideLeftDelta (cell : ZxpCell) :
    zxgDotB zxgLegsParityFunctional
        (zxgVectorDeltaMod2 (zxgCountVector (zxwSlideLeftLhs cell))
          (zxgCountVector (zxwSlideLeftRhs cell)))
      = false := by
  cases zxwSlideLeftDeltaCases cell with
  | inl hZero =>
      rw [hZero]
      exact rfl
  | inr hOdd =>
      rw [hOdd]
      exact rfl

/-! ### The wire-vanishing fold engine over `ZxwConv` -/

/-- Slide balance of a per-cell weight: both orientations at every cell. -/
def ZxwSlideBalancedWeight (cellWeight : ZxpCell -> Nat) : Prop :=
  (cell : ZxpCell) ->
    zxgLayersFold cellWeight (zxwSlideRightLhs cell).layers
        = zxgLayersFold cellWeight (zxwSlideRightRhs cell).layers
      /\ zxgLayersFold cellWeight (zxwSlideLeftLhs cell).layers
        = zxgLayersFold cellWeight (zxwSlideLeftRhs cell).layers

/-- Involution balance of a per-cell weight. -/
def ZxwInvolutionBalancedWeight (cellWeight : ZxpCell -> Nat) : Prop :=
  zxgLayersFold cellWeight zxwInvolutionLhs.layers
    = zxgLayersFold cellWeight zxwInvolutionRhs.layers

/-- INVARIANCE, window level, wiring-extended move set: the exchange-extended four
hypotheses PLUS honest slide and involution balance (the slides are NOT free —
see the forcing theorem below). -/
theorem zxwWindowMoveFoldEq (cellWeight : ZxpCell -> Nat)
    (hWireZero : cellWeight ZxpCell.wire = 0)
    (hRowsBalanced : ZxgRowBalancedWeight cellWeight)
    (hZFuseBalanced : ZxrZFuseBalancedWeight cellWeight)
    (hXFuseBalanced : ZxrXFuseBalancedWeight cellWeight)
    (hSlideBalanced : ZxwSlideBalancedWeight cellWeight)
    (hInvolutionBalanced : ZxwInvolutionBalancedWeight cellWeight)
    {firstWindow secondWindow : ZxpDiagram}
    (hMove : ZxwWindowMove firstWindow secondWindow) :
    zxgLayersFold cellWeight firstWindow.layers
      = zxgLayersFold cellWeight secondWindow.layers := by
  cases hMove with
  | base hBaseMove =>
      exact zxeWindowMoveFoldEq cellWeight hWireZero hRowsBalanced hZFuseBalanced
        hXFuseBalanced hBaseMove
  | slideRight cell => exact (hSlideBalanced cell).left
  | slideLeft cell => exact (hSlideBalanced cell).right
  | sigmaInvolution => exact hInvolutionBalanced

/-- INVARIANCE, step level (padded contexts cancel). -/
theorem zxwStepFoldEq (cellWeight : ZxpCell -> Nat)
    (hWireZero : cellWeight ZxpCell.wire = 0)
    (hRowsBalanced : ZxgRowBalancedWeight cellWeight)
    (hZFuseBalanced : ZxrZFuseBalancedWeight cellWeight)
    (hXFuseBalanced : ZxrXFuseBalancedWeight cellWeight)
    (hSlideBalanced : ZxwSlideBalancedWeight cellWeight)
    (hInvolutionBalanced : ZxwInvolutionBalancedWeight cellWeight)
    {firstDiagram secondDiagram : ZxpDiagram}
    (hStep : ZxwStep firstDiagram secondDiagram) :
    zxgDiagramFold cellWeight firstDiagram = zxgDiagramFold cellWeight secondDiagram := by
  cases hStep with
  | pad contextSource leftWires rightWires beforeLayers afterLayers hMove hBeforeWF
      hBeforeCod hAfterWF =>
      rename_i firstWindow secondWindow
      rw [zxgDiagramFoldPad cellWeight hWireZero contextSource leftWires rightWires
          beforeLayers afterLayers firstWindow,
        zxgDiagramFoldPad cellWeight hWireZero contextSource leftWires rightWires
          beforeLayers afterLayers secondWindow,
        zxwWindowMoveFoldEq cellWeight hWireZero hRowsBalanced hZFuseBalanced
          hXFuseBalanced hSlideBalanced hInvolutionBalanced hMove]

/-- INVARIANCE, full wiring-extended congruence. -/
theorem zxwConvFoldEq (cellWeight : ZxpCell -> Nat)
    (hWireZero : cellWeight ZxpCell.wire = 0)
    (hRowsBalanced : ZxgRowBalancedWeight cellWeight)
    (hZFuseBalanced : ZxrZFuseBalancedWeight cellWeight)
    (hXFuseBalanced : ZxrXFuseBalancedWeight cellWeight)
    (hSlideBalanced : ZxwSlideBalancedWeight cellWeight)
    (hInvolutionBalanced : ZxwInvolutionBalancedWeight cellWeight)
    {firstDiagram secondDiagram : ZxpDiagram}
    (hConv : ZxwConv firstDiagram secondDiagram) :
    zxgDiagramFold cellWeight firstDiagram = zxgDiagramFold cellWeight secondDiagram := by
  induction hConv with
  | step hStep =>
      exact zxwStepFoldEq cellWeight hWireZero hRowsBalanced hZFuseBalanced
        hXFuseBalanced hSlideBalanced hInvolutionBalanced hStep
  | refl diagram hWF => exact rfl
  | symm _hConv innerEq => exact innerEq.symm
  | trans _hFirst _hSecond firstEq secondEq => exact firstEq.trans secondEq

/-- THE HONEST CROSSING-COUNT COMPUTATION: slide balance is NOT free — any
wire-vanishing weight balanced on the slide family is FORCED to vanish on the
crossing (instantiate the unit slide `slideRight (zSpider 0 1)`, which trades one
staircase crossing for none, and cancel). -/
theorem zxwSlideBalanceForcesCrossingZero (cellWeight : ZxpCell -> Nat)
    (hWireZero : cellWeight ZxpCell.wire = 0)
    (hSlideBalanced : ZxwSlideBalancedWeight cellWeight) :
    cellWeight ZxpCell.crossing = 0 := by
  have hEq : (cellWeight (ZxpCell.zSpider 0 1) + cellWeight ZxpCell.wire)
      + cellWeight ZxpCell.crossing
      = cellWeight ZxpCell.wire + cellWeight (ZxpCell.zSpider 0 1) :=
    (hSlideBalanced (ZxpCell.zSpider 0 1)).left
  rw [hWireZero] at hEq
  have hEq2 : cellWeight (ZxpCell.zSpider 0 1) + cellWeight ZxpCell.crossing
      = 0 + cellWeight (ZxpCell.zSpider 0 1) := hEq
  have hEq3 : cellWeight ZxpCell.crossing + cellWeight (ZxpCell.zSpider 0 1)
      = 0 + cellWeight (ZxpCell.zSpider 0 1) :=
    (Nat.add_comm (cellWeight ZxpCell.crossing)
      (cellWeight (ZxpCell.zSpider 0 1))).trans hEq2
  exact zxwAddCancelRight (cellWeight ZxpCell.crossing) 0
    (cellWeight (ZxpCell.zSpider 0 1)) hEq3

/-- Kernel pin of the imbalance instance: the unit slide's crossing-count fold
drops by exactly one. -/
theorem zxwUnitSlideCrossCountShift :
    zxgLayersFold zxgCellCrossCountWeight
        (zxwSlideRightLhs (ZxpCell.zSpider 0 1)).layers
      = zxgLayersFold zxgCellCrossCountWeight
          (zxwSlideRightRhs (ZxpCell.zSpider 0 1)).layers + 1 := rfl

/-- THE CROSSING COUNT IS DEAD as a `ZxwConv` invariant: it is wire-vanishing and
balanced on every committed `ZxeConv` family, but NOT slide-balanced. -/
theorem zxwCrossCountNotSlideBalanced :
    Not (ZxwSlideBalancedWeight zxgCellCrossCountWeight) :=
  fun hBalanced =>
    Nat.noConfusion
      (zxwSlideBalanceForcesCrossingZero zxgCellCrossCountWeight rfl hBalanced)

/-- THE COLLAPSE CARRIES AND STRENGTHENS: every wire-vanishing weight admissible
for the `ZxwConv` engine is identically zero (already forced by the four
`ZxeConv` hypotheses; the slide hypothesis independently re-forces the crossing
component by the theorem above).  The whole per-cell counting family — home of
BOTH prior refutations of this workstream — holds no `ZxwConv` separator. -/
theorem zxwBalancedWeightCollapse (cellWeight : ZxpCell -> Nat)
    (hWireZero : cellWeight ZxpCell.wire = 0)
    (hRowsBalanced : ZxgRowBalancedWeight cellWeight)
    (hZFuseBalanced : ZxrZFuseBalancedWeight cellWeight)
    (hXFuseBalanced : ZxrXFuseBalancedWeight cellWeight)
    (_hSlideBalanced : ZxwSlideBalancedWeight cellWeight)
    (_hInvolutionBalanced : ZxwInvolutionBalancedWeight cellWeight) :
    (cell : ZxpCell) -> cellWeight cell = 0 :=
  zxrBalancedWeightCollapse cellWeight hWireZero hRowsBalanced hZFuseBalanced
    hXFuseBalanced

/-- Corollary: every engine-admissible weight folds to constant zero. -/
theorem zxwBalancedWeightFoldZero (cellWeight : ZxpCell -> Nat)
    (hWireZero : cellWeight ZxpCell.wire = 0)
    (hRowsBalanced : ZxgRowBalancedWeight cellWeight)
    (hZFuseBalanced : ZxrZFuseBalancedWeight cellWeight)
    (hXFuseBalanced : ZxrXFuseBalancedWeight cellWeight)
    (_hSlideBalanced : ZxwSlideBalancedWeight cellWeight)
    (_hInvolutionBalanced : ZxwInvolutionBalancedWeight cellWeight)
    (diagram : ZxpDiagram) : zxgDiagramFold cellWeight diagram = 0 :=
  zxrBalancedWeightFoldZero cellWeight hWireZero hRowsBalanced hZFuseBalanced
    hXFuseBalanced diagram

/-- NEGATIVE CONTROL: the refutation instrument survives the wiring extension —
span-distinct diagrams stay non-convertible in `ZxwConv`. -/
theorem zxwBigColourNotConv : Not (ZxwConv zxrZPentaDiagram zxrXPentaDiagram) :=
  fun hConv =>
    Bool.noConfusion ((zxwConvSpanEqB hConv).symm.trans zxrBigColourSpanDistinct)

/-- THE GATE RE-RUN VERDICT MARKER: outcome CLEAN.  Checked precisely, with the
crossing-count analysis done HONESTLY: (1) the slides are NOT balanced for the
crossing count — the general delta is `cod - dom` staircase crossings
(`zxwUnitSlideCrossCountShift` pins the unit instance, `zxwCrossCountNotSlideBalanced`
kills the weight) — so slide balance is a genuine new engine hypothesis, and any
weight satisfying it loses its crossing component
(`zxwSlideBalanceForcesCrossingZero`); (2) the FusionRepair collapse carries and
a-fortiori strengthens (`zxwBalancedWeightCollapse` — the counting family holds no
`ZxwConv` separator); (3) the general slide deltas are pinned to
`[0,0,0,p(dom+cod),p(dom+cod),0,0]` at every cell and orientation
(`zxwSlideRightDeltaGeneral`/`zxwSlideLeftDeltaGeneral`, saturated by the odd
literal via the case lemmas), the involution delta is the layer literal, the
extended table spans the SAME committed 6-dimensional basis
(`zxwExtendedDeltaSpanBasisPin` — crossing parity and layer parity were already
independently movable by the comm rows and splitLayer), the 128-functional
lattice is still exactly {0, legs-parity} (`zxwPreservedLatticeReclassified`),
and the survivor is boundary-determined (gate theorem, untouched) and orthogonal
to every slide delta (`zxwLegsParityOrthogonalSlide{Right,Left}Delta`); (4) the
refutation instrument still bites (`zxwBigColourNotConv`).  No separator exists
in the commissioned families; the extension is semantically sound at all arities
by construction (`zxwSlideRightBundle`/`zxwSlideLeftBundle`/`zxwInvolutionBundle`). -/
def zxwGateVerdictIsClean : Bool := true

/-! ## Stage 7 — (C) THE DERIVED SYMMETRIC STRUCTURE: the wall's instances fall -/

/-- THE COUNIT SLIDE (Z), the wall's first minimal blocked instance, in its exact
committed shape (`zxaCounitSlideStatement` with `ZxwConv`): DERIVED — it is the
`slideLeft (zSpider 1 0)` instance.  The `ZxeConv` original stays owner-false and
byte-intact in its home file. -/
theorem zxwCounitSlideZ :
    ZxwConv
      { sourceArity := 2
        layers := [[ZxpCell.crossing], [ZxpCell.zSpider 1 0, ZxpCell.wire]] }
      { sourceArity := 2, layers := [[ZxpCell.wire, ZxpCell.zSpider 1 0]] } :=
  ZxwConv.symm (zxwSlideLeftConv (ZxpCell.zSpider 1 0))

/-- The counit slide, X colour mirror. -/
theorem zxwCounitSlideX :
    ZxwConv
      { sourceArity := 2
        layers := [[ZxpCell.crossing], [ZxpCell.xSpider 1 0, ZxpCell.wire]] }
      { sourceArity := 2, layers := [[ZxpCell.wire, ZxpCell.xSpider 1 0]] } :=
  ZxwConv.symm (zxwSlideLeftConv (ZxpCell.xSpider 1 0))

/-- The unit slide (Z): a crossing dies against a fresh unit state on its first
input — the state mirror of the counit slide. -/
theorem zxwUnitSlideZ :
    ZxwConv
      { sourceArity := 1
        layers := [[ZxpCell.wire, ZxpCell.zSpider 0 1], [ZxpCell.crossing]] }
      { sourceArity := 1, layers := [[ZxpCell.zSpider 0 1, ZxpCell.wire]] } :=
  zxwSlideLeftConv (ZxpCell.zSpider 0 1)

/-- The unit slide, X colour mirror. -/
theorem zxwUnitSlideX :
    ZxwConv
      { sourceArity := 1
        layers := [[ZxpCell.wire, ZxpCell.xSpider 0 1], [ZxpCell.crossing]] }
      { sourceArity := 1, layers := [[ZxpCell.xSpider 0 1, ZxpCell.wire]] } :=
  zxwSlideLeftConv (ZxpCell.xSpider 0 1)

/-- SIGMA INVOLUTION in the wall's exact committed shape
(`zxaSigmaInvolutionStatement` with `ZxwConv`): the primitive fired bare. -/
theorem zxwSigmaInvolutionFire :
    ZxwConv
      { sourceArity := 2, layers := [[ZxpCell.crossing], [ZxpCell.crossing]] }
      { sourceArity := 2, layers := [[ZxpCell.wire, ZxpCell.wire]] } :=
  zxwMoveConv ZxwWindowMove.sigmaInvolution

/-- YANG-BAXTER DERIVES (the commissioned check): the braid relation is LITERALLY
the `slideLeft ZxpCell.crossing` instance of the naturality family — sliding the
passive strand past a crossing IS the third Reidemeister move, so no separate YB
primitive is needed in the move set. -/
theorem zxwYangBaxter :
    ZxwConv
      { sourceArity := 3
        layers := [[ZxpCell.wire, ZxpCell.crossing], [ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.crossing]] }
      { sourceArity := 3
        layers := [[ZxpCell.crossing, ZxpCell.wire], [ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.crossing, ZxpCell.wire]] } :=
  zxwSlideLeftConv ZxpCell.crossing

/-- FIRE (fresh instance 1): the passive strand slides right-to-left past a
`zSpider 2 3` — three staircase crossings trade for two, all shapes literal. -/
theorem zxwSlideSpiderRightFire :
    ZxwConv
      { sourceArity := 3
        layers := [[ZxpCell.zSpider 2 3, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.crossing, ZxpCell.wire, ZxpCell.wire]] }
      { sourceArity := 3
        layers := [[ZxpCell.wire, ZxpCell.crossing], [ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.zSpider 2 3]] } :=
  zxwSlideRightConv (ZxpCell.zSpider 2 3)

/-- FIRE (fresh instance 2): the passive strand slides left-to-right past an
`xSpider 1 2`. -/
theorem zxwSlideSpiderLeftFire :
    ZxwConv
      { sourceArity := 2
        layers := [[ZxpCell.wire, ZxpCell.xSpider 1 2],
          [ZxpCell.crossing, ZxpCell.wire], [ZxpCell.wire, ZxpCell.crossing]] }
      { sourceArity := 2
        layers := [[ZxpCell.crossing], [ZxpCell.xSpider 1 2, ZxpCell.wire]] } :=
  zxwSlideLeftConv (ZxpCell.xSpider 1 2)

/-- Independent kernel cross-check of fire 1: the slide instance is span-equal by
direct span decision (the conversion is honest). -/
theorem zxwSlideSpiderRightFireSpanPin :
    zxpSpanEqB
      (zxpDiagramDenote
        { sourceArity := 3
          layers := [[ZxpCell.zSpider 2 3, ZxpCell.wire],
            [ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing],
            [ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire],
            [ZxpCell.crossing, ZxpCell.wire, ZxpCell.wire]] })
      (zxpDiagramDenote
        { sourceArity := 3
          layers := [[ZxpCell.wire, ZxpCell.crossing],
            [ZxpCell.crossing, ZxpCell.wire],
            [ZxpCell.wire, ZxpCell.zSpider 2 3]] }) = true := rfl

/-! ## Stage 7b — CROSSING-BLOCK ROUTING: disjoint blocks commute, the staircase
splits, and one passive strand routes past an ARBITRARY layer

The commutation lemmas live over `ZxeConv` already (they are merge/re-split
chains through splitLayer and the exchange); the layer slide needs the wiring
primitives and lives over `ZxwConv`. -/

/-- A right-zero whisker of one layer is a left wire block. -/
theorem zxwWhiskerLayerRightZero (leftWires : Nat) (layer : List ZxpCell) :
    zxpWhiskerLayer leftWires 0 layer
      = zxpCatCells (zxpWireCells leftWires) layer := by
  show zxpCatCells (zxpWireCells leftWires) (zxpCatCells layer [])
    = zxpCatCells (zxpWireCells leftWires) layer
  rw [zxpCatCellsNilRight layer]

/-- Cons shape of a right-zero whisker. -/
theorem zxwWhiskerRightZeroCons (leftWires : Nat) (layer : List ZxpCell)
    (restLayers : List (List ZxpCell)) :
    zxpWhiskerLayers leftWires 0 (layer :: restLayers)
      = zxpCatCells (zxpWireCells leftWires) layer
        :: zxpWhiskerLayers leftWires 0 restLayers := by
  show zxpWhiskerLayer leftWires 0 layer
      :: zxpWhiskerLayers leftWires 0 restLayers
    = zxpCatCells (zxpWireCells leftWires) layer
      :: zxpWhiskerLayers leftWires 0 restLayers
  rw [zxwWhiskerLayerRightZero leftWires layer]

/-- DISJOINT BLOCKS COMMUTE, block-left form: a layer block fires first on the
left strands, then a whole layer LIST on the right strands — equivalently the
list fires first and the block last.  Merge/re-split chain: one splitLayer
backward, one exchange forward, per list layer. -/
theorem zxwLayerPastRightLayers (blockCells : List ZxpCell) :
    (rightLayers : List (List ZxpCell)) -> (entryArity : Nat) ->
    ZxpLayersWF entryArity rightLayers ->
    ZxeConv
      { sourceArity := zxpLayerDomArity blockCells + entryArity
        layers := zxpCatCells blockCells (zxpWireCells entryArity)
          :: zxpWhiskerLayers (zxpLayerCodArity blockCells) 0 rightLayers }
      { sourceArity := zxpLayerDomArity blockCells + entryArity
        layers := zxpCatLayers
          (zxpWhiskerLayers (zxpLayerDomArity blockCells) 0 rightLayers)
          [zxpCatCells blockCells
            (zxpWireCells (zxpLayersCodArity entryArity rightLayers))] }
  | [], entryArity, _hWF => by
      refine ZxeConv.refl _ ?_
      refine ZxpLayersWF.cons ?_ (ZxpLayersWF.nil _)
      rw [zxpCatCellsDomArity, zxpWireCellsDomArity]
  | rightLayer :: restLayers, entryArity, hWF => by
      cases hWF with
      | cons hDom hRest =>
          subst hDom
          rw [zxwWhiskerRightZeroCons (zxpLayerCodArity blockCells) rightLayer
              restLayers,
            zxwWhiskerRightZeroCons (zxpLayerDomArity blockCells) rightLayer
              restLayers]
          have hRestWhiskWF : ZxpLayersWF
              (zxpLayerCodArity blockCells + zxpLayerCodArity rightLayer)
              (zxpWhiskerLayers (zxpLayerCodArity blockCells) 0 restLayers) := by
            have hRaw := zxpWhiskerLayersWF (zxpLayerCodArity blockCells) 0
              restLayers hRest
            rw [Nat.add_zero] at hRaw
            exact hRaw
          -- E0 ~ E1 : merge the two disjoint layers (splitLayer backward)
          have hMergeAfterWF : ZxpLayersWF
              (zxpDiagramCodArity
                { sourceArity := zxpLayerDomArity blockCells
                    + zxpLayerDomArity rightLayer
                  layers := [zxpCatCells blockCells rightLayer] })
              (zxpWhiskerLayers (zxpLayerCodArity blockCells) 0 restLayers) := by
            show ZxpLayersWF (zxpLayerCodArity (zxpCatCells blockCells rightLayer))
              (zxpWhiskerLayers (zxpLayerCodArity blockCells) 0 restLayers)
            rw [zxpCatCellsCodArity]
            exact hRestWhiskWF
          have hMerge := zxeStepConv
            (zxpLayerDomArity blockCells + zxpLayerDomArity rightLayer)
            [] (zxpWhiskerLayers (zxpLayerCodArity blockCells) 0 restLayers)
            (ZxeWindowMove.base (ZxrWindowMove.seed
              (ZxpWindowMove.splitLayer blockCells rightLayer)))
            (ZxpLayersWF.nil _) rfl hMergeAfterWF
          -- E2 ~ E1 : the exchange re-splits right-first
          have hExchangeAfterWF : ZxpLayersWF
              (zxpDiagramCodArity (zxeExchangeLhs blockCells rightLayer))
              (zxpWhiskerLayers (zxpLayerCodArity blockCells) 0 restLayers) := by
            rw [zxeExchangeLhsCodArity blockCells rightLayer]
            exact hRestWhiskWF
          have hExchange := zxeStepConv
            (zxpLayerDomArity blockCells + zxpLayerDomArity rightLayer)
            [] (zxpWhiskerLayers (zxpLayerCodArity blockCells) 0 restLayers)
            (ZxeWindowMove.rightFirstExchange blockCells rightLayer)
            (ZxpLayersWF.nil _) rfl hExchangeAfterWF
          -- E2 ~ E3 : the inner commutation lifted under the leading layer
          have hInner := zxwLayerPastRightLayers blockCells restLayers
            (zxpLayerCodArity rightLayer) hRest
          have hLiftBeforeWF : ZxpLayersWF
              (zxpLayerDomArity blockCells + zxpLayerDomArity rightLayer)
              [zxpCatCells (zxpWireCells (zxpLayerDomArity blockCells)) rightLayer] := by
            refine ZxpLayersWF.cons ?_ (ZxpLayersWF.nil _)
            rw [zxpCatCellsDomArity, zxpWireCellsDomArity]
          have hLiftBeforeCod : zxpLayersCodArity
              (zxpLayerDomArity blockCells + zxpLayerDomArity rightLayer)
              [zxpCatCells (zxpWireCells (zxpLayerDomArity blockCells)) rightLayer]
              = zxpLayerDomArity blockCells + zxpLayerCodArity rightLayer := by
            show zxpLayerCodArity
                (zxpCatCells (zxpWireCells (zxpLayerDomArity blockCells)) rightLayer)
              = zxpLayerDomArity blockCells + zxpLayerCodArity rightLayer
            rw [zxpCatCellsCodArity, zxpWireCellsCodArity]
          have hLifted := zxeLiftConv
            (zxpLayerDomArity blockCells + zxpLayerDomArity rightLayer)
            [zxpCatCells (zxpWireCells (zxpLayerDomArity blockCells)) rightLayer]
            [] hInner hLiftBeforeWF hLiftBeforeCod (ZxpLayersWF.nil _)
          rw [zxpCatLayersNilRight, zxpCatLayersNilRight] at hLifted
          exact ZxeConv.trans (ZxeConv.symm hMerge)
            (ZxeConv.trans (ZxeConv.symm hExchange) hLifted)

/-- DISJOINT BLOCKS COMMUTE, block-right form: a layer block fires first on the
right strands, then a whole layer LIST on the left strands — equivalently the
list fires first and the block last. -/
theorem zxwLayersPastRightLayer (blockCells : List ZxpCell) :
    (leftLayers : List (List ZxpCell)) -> (entryArity : Nat) ->
    ZxpLayersWF entryArity leftLayers ->
    ZxeConv
      { sourceArity := entryArity + zxpLayerDomArity blockCells
        layers := zxpCatCells (zxpWireCells entryArity) blockCells
          :: zxpWhiskerLayers 0 (zxpLayerCodArity blockCells) leftLayers }
      { sourceArity := entryArity + zxpLayerDomArity blockCells
        layers := zxpCatLayers
          (zxpWhiskerLayers 0 (zxpLayerDomArity blockCells) leftLayers)
          [zxpCatCells (zxpWireCells (zxpLayersCodArity entryArity leftLayers))
            blockCells] }
  | [], entryArity, _hWF => by
      refine ZxeConv.refl _ ?_
      refine ZxpLayersWF.cons ?_ (ZxpLayersWF.nil _)
      rw [zxpCatCellsDomArity, zxpWireCellsDomArity]
  | leftLayer :: restLayers, entryArity, hWF => by
      cases hWF with
      | cons hDom hRest =>
          subst hDom
          have hRestWhiskWF : ZxpLayersWF
              (zxpLayerCodArity leftLayer + zxpLayerCodArity blockCells)
              (zxpWhiskerLayers 0 (zxpLayerCodArity blockCells) restLayers) := by
            have hRaw := zxpWhiskerLayersWF 0 (zxpLayerCodArity blockCells)
              restLayers hRest
            rw [Nat.zero_add] at hRaw
            exact hRaw
          -- E0 ~ E1 : the exchange merges the two disjoint layers (backward)
          have hExchangeAfterWF : ZxpLayersWF
              (zxpDiagramCodArity (zxeExchangeLhs leftLayer blockCells))
              (zxpWhiskerLayers 0 (zxpLayerCodArity blockCells) restLayers) := by
            rw [zxeExchangeLhsCodArity leftLayer blockCells]
            exact hRestWhiskWF
          have hExchange := zxeStepConv
            (zxpLayerDomArity leftLayer + zxpLayerDomArity blockCells)
            [] (zxpWhiskerLayers 0 (zxpLayerCodArity blockCells) restLayers)
            (ZxeWindowMove.rightFirstExchange leftLayer blockCells)
            (ZxpLayersWF.nil _) rfl hExchangeAfterWF
          -- E1 ~ E2 : one splitLayer re-splits left-first
          have hSplitAfterWF : ZxpLayersWF
              (zxpDiagramCodArity
                { sourceArity := zxpLayerDomArity leftLayer
                    + zxpLayerDomArity blockCells
                  layers := [zxpCatCells leftLayer blockCells] })
              (zxpWhiskerLayers 0 (zxpLayerCodArity blockCells) restLayers) := by
            show ZxpLayersWF (zxpLayerCodArity (zxpCatCells leftLayer blockCells))
              (zxpWhiskerLayers 0 (zxpLayerCodArity blockCells) restLayers)
            rw [zxpCatCellsCodArity]
            exact hRestWhiskWF
          have hSplit := zxeStepConv
            (zxpLayerDomArity leftLayer + zxpLayerDomArity blockCells)
            [] (zxpWhiskerLayers 0 (zxpLayerCodArity blockCells) restLayers)
            (ZxeWindowMove.base (ZxrWindowMove.seed
              (ZxpWindowMove.splitLayer leftLayer blockCells)))
            (ZxpLayersWF.nil _) rfl hSplitAfterWF
          -- E2 ~ E3 : the inner commutation lifted under the leading layer
          have hInner := zxwLayersPastRightLayer blockCells restLayers
            (zxpLayerCodArity leftLayer) hRest
          have hLiftBeforeWF : ZxpLayersWF
              (zxpLayerDomArity leftLayer + zxpLayerDomArity blockCells)
              [zxpCatCells leftLayer
                (zxpWireCells (zxpLayerDomArity blockCells))] := by
            refine ZxpLayersWF.cons ?_ (ZxpLayersWF.nil _)
            rw [zxpCatCellsDomArity, zxpWireCellsDomArity]
          have hLiftBeforeCod : zxpLayersCodArity
              (zxpLayerDomArity leftLayer + zxpLayerDomArity blockCells)
              [zxpCatCells leftLayer (zxpWireCells (zxpLayerDomArity blockCells))]
              = zxpLayerCodArity leftLayer + zxpLayerDomArity blockCells := by
            show zxpLayerCodArity
                (zxpCatCells leftLayer (zxpWireCells (zxpLayerDomArity blockCells)))
              = zxpLayerCodArity leftLayer + zxpLayerDomArity blockCells
            rw [zxpCatCellsCodArity, zxpWireCellsCodArity]
          have hLifted := zxeLiftConv
            (zxpLayerDomArity leftLayer + zxpLayerDomArity blockCells)
            [zxpCatCells leftLayer (zxpWireCells (zxpLayerDomArity blockCells))]
            [] hInner hLiftBeforeWF hLiftBeforeCod (ZxpLayersWF.nil _)
          rw [zxpCatLayersNilRight, zxpCatLayersNilRight] at hLifted
          exact ZxeConv.trans hExchange (ZxeConv.trans hSplit hLifted)

/-- THE STAIRCASE SPLITS: routing the last strand across `front + back` positions
is routing it across the back block (under `front` pass wires) and then across
the front block (over `back` pass wires) — a LITERAL layer-list identity. -/
theorem zxwStairFromRightSplit (frontSteps : Nat) : (backSteps : Nat) ->
    zxwStairFromRightLayers (frontSteps + backSteps)
      = zxpCatLayers
          (zxpWhiskerLayers frontSteps 0 (zxwStairFromRightLayers backSteps))
          (zxpWhiskerLayers 0 backSteps (zxwStairFromRightLayers frontSteps))
  | 0 => by
      show zxwStairFromRightLayers frontSteps
        = zxpWhiskerLayers 0 0 (zxwStairFromRightLayers frontSteps)
      rw [zxpWhiskerLayersZero (zxwStairFromRightLayers frontSteps)]
  | backPred + 1 => by
      show zxpCatCells (zxpWireCells (frontSteps + backPred)) [ZxpCell.crossing]
          :: zxpWhiskerLayers 0 1 (zxwStairFromRightLayers (frontSteps + backPred))
        = zxpCatLayers
            (zxpWhiskerLayer frontSteps 0
                (zxpCatCells (zxpWireCells backPred) [ZxpCell.crossing])
              :: zxpWhiskerLayers frontSteps 0
                (zxpWhiskerLayers 0 1 (zxwStairFromRightLayers backPred)))
            (zxpWhiskerLayers 0 (backPred + 1) (zxwStairFromRightLayers frontSteps))
      have hHead : zxpWhiskerLayer frontSteps 0
          (zxpCatCells (zxpWireCells backPred) [ZxpCell.crossing])
          = zxpCatCells (zxpWireCells (frontSteps + backPred)) [ZxpCell.crossing] := by
        rw [zxwWhiskerLayerRightZero frontSteps
          (zxpCatCells (zxpWireCells backPred) [ZxpCell.crossing])]
        exact zxaWiresWiresCat frontSteps backPred [ZxpCell.crossing]
      have hInnerCompose : zxpWhiskerLayers frontSteps 0
          (zxpWhiskerLayers 0 1 (zxwStairFromRightLayers backPred))
          = zxpWhiskerLayers frontSteps 1 (zxwStairFromRightLayers backPred) := by
        rw [zxnWhiskerLayersCompose frontSteps 0 0 1 (zxwStairFromRightLayers backPred),
          Nat.add_zero frontSteps]
      have hOuterCompose : zxpWhiskerLayers 0 1
          (zxpWhiskerLayers frontSteps 0 (zxwStairFromRightLayers backPred))
          = zxpWhiskerLayers frontSteps 1 (zxwStairFromRightLayers backPred) := by
        rw [zxnWhiskerLayersCompose 0 1 frontSteps 0 (zxwStairFromRightLayers backPred),
          Nat.zero_add frontSteps]
      have hSecondCompose : zxpWhiskerLayers 0 1
          (zxpWhiskerLayers 0 backPred (zxwStairFromRightLayers frontSteps))
          = zxpWhiskerLayers 0 (backPred + 1) (zxwStairFromRightLayers frontSteps) := by
        rw [zxnWhiskerLayersCompose 0 1 0 backPred (zxwStairFromRightLayers frontSteps)]
      rw [zxwStairFromRightSplit frontSteps backPred,
        zxnWhiskerLayersCat 0 1
          (zxpWhiskerLayers frontSteps 0 (zxwStairFromRightLayers backPred))
          (zxpWhiskerLayers 0 backPred (zxwStairFromRightLayers frontSteps)),
        hHead, hInnerCompose, hOuterCompose, hSecondCompose]
      exact rfl

/-! ### THE CROSSING-BLOCK PERMUTATION ENGINE

`ZxaSwapWalk` is exactly "a permutation block generated by adjacent crossings";
the commutation lemmas above specialize to: ANY such block on one side routes ANY
layer block on the other side past it, in both relative positions.  Together with
the cell-level slides (a crossing block THROUGH a cell's boundary — the
staircases are themselves `ZxaSwapWalk`-shaped) and the derived Yang-Baxter and
involution, this is the crossing-block routing toolkit; the single-statement
"one passive strand past a whole multi-cell layer" form assembles from
`zxwStairFromRightSplit` + these commutes + the cell slides and is the natural
first lemma of the absorption round (documented at `zxwAbsorptionStatement`). -/

/-- Any adjacent-crossing permutation block (right strands) routes past any layer
block (left strands). -/
theorem zxwWalkPastBlock (blockCells : List ZxpCell) (strandCount : Nat)
    {walkLayers : List (List ZxpCell)}
    (hWalk : ZxaSwapWalk strandCount walkLayers) :
    ZxeConv
      { sourceArity := zxpLayerDomArity blockCells + strandCount
        layers := zxpCatCells blockCells (zxpWireCells strandCount)
          :: zxpWhiskerLayers (zxpLayerCodArity blockCells) 0 walkLayers }
      { sourceArity := zxpLayerDomArity blockCells + strandCount
        layers := zxpCatLayers
          (zxpWhiskerLayers (zxpLayerDomArity blockCells) 0 walkLayers)
          [zxpCatCells blockCells
            (zxpWireCells (zxpLayersCodArity strandCount walkLayers))] } :=
  zxwLayerPastRightLayers blockCells walkLayers strandCount (zxaSwapWalkWF hWalk)

/-- Any adjacent-crossing permutation block (left strands) routes past any layer
block (right strands). -/
theorem zxwBlockPastWalk (blockCells : List ZxpCell) (strandCount : Nat)
    {walkLayers : List (List ZxpCell)}
    (hWalk : ZxaSwapWalk strandCount walkLayers) :
    ZxeConv
      { sourceArity := strandCount + zxpLayerDomArity blockCells
        layers := zxpCatCells (zxpWireCells strandCount) blockCells
          :: zxpWhiskerLayers 0 (zxpLayerCodArity blockCells) walkLayers }
      { sourceArity := strandCount + zxpLayerDomArity blockCells
        layers := zxpCatLayers
          (zxpWhiskerLayers 0 (zxpLayerDomArity blockCells) walkLayers)
          [zxpCatCells (zxpWireCells (zxpLayersCodArity strandCount walkLayers))
            blockCells] } :=
  zxwLayersPastRightLayer blockCells walkLayers strandCount (zxaSwapWalkWF hWalk)

/-- FIRE: a fresh two-crossing walk on three right strands routes past a
`zSpider 1 2` block — all shapes literal, the walk ends up BEFORE the spider. -/
theorem zxwWalkPastBlockFire :
    ZxeConv
      { sourceArity := 4
        layers := [[ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing]] }
      { sourceArity := 4
        layers := [[ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.wire, ZxpCell.crossing],
          [ZxpCell.zSpider 1 2, ZxpCell.wire, ZxpCell.wire, ZxpCell.wire]] } :=
  zxwWalkPastBlock [ZxpCell.zSpider 1 2] 3
    (ZxaSwapWalk.cons 0 1 rfl (ZxaSwapWalk.cons 1 0 rfl ZxaSwapWalk.nil))

/-! ## Stage 8 — (D) THE ABSORPTION + THE FLIP: honest partial

The wiring wall itself is gone: every configuration the AbsorptionFlip round
named as blocking (a crossing with one leg into a cell and one leg on a passive
strand — the normal-form carrier crossings between the Z-tree and the X-chain)
is now DERIVABLE, either as a slide instance or through the routing lemmas
above.  What remains for the flip is bookkeeping on an UNBLOCKED route, recorded
precisely below; the statements are minted in the exact committed shapes with
`ZxwConv` conclusions, and the owners stay FALSE until the inductions land. -/

/-- THE ABSORPTION STATEMENT over `ZxwConv` (Kissinger Lemma 3.2/3.3 over the
census normal form): every well-formed diagram converts to `zxnNormalForm` of its
own denotation.  OWNER FALSE — NOT PROVEN.  The prior round's blocking
configuration (one-legged carrier crossings) is DERIVABLE in `ZxwConv`; the
remaining work is (i) per-cell absorption bookkeeping — for each cell kind at
each mid position, `cell ; NF(G)` converts to `NF(G')` where `G'` presents the
composite relation (spider cells via the transported general-k fusion + the
bialgebra rows + the slides; crossings via `zxwSigmaInvolutionFire` + the slides;
wires via the strip lemmas) — and (ii) the generator-list transport below. -/
def zxwAbsorptionStatement : Prop :=
  (diagram : ZxpDiagram) -> ZxpDiagramWF diagram ->
    ZxwConv diagram
      (zxnNormalForm diagram.sourceArity (zxpDiagramCodArity diagram)
        (zxpDiagramDenote diagram))

/-- OWNER MARKER (FALSE): the absorption induction is not proven this round. -/
def zxwAbsorptionIsProven : Bool := false

/-- THE GENERATOR-LIST TRANSPORT STATEMENT (the residual named on
`zxaAbsorptionStatement`): span-equal generator lists give `ZxwConv`-convertible
normal forms.  OWNER FALSE — NOT PROVEN.  Documented route choice: the census
substrate supports NF-to-NF conversion along ELEMENTARY ROW OPERATIONS (each
`zxnXorRowLayers` comb is one generator row; row swap = crossing-block routing of
whole comb blocks past each other, now available; row xor = the bialgebra square
family through the shared strand bundle; zero-row deletion = the kill-create
collapse) chained along `zxpEchelonize`'s insertion order — mutual reduction of
either list against the common echelon form, exactly the shape of the committed
span decision `zxpSpanEqB`. -/
def zxwGeneratorTransportStatement : Prop :=
  (domWidth codWidth : Nat) -> (firstRows secondRows : List (List Bool)) ->
    ZxpAllWidth (domWidth + codWidth) firstRows ->
    ZxpAllWidth (domWidth + codWidth) secondRows ->
    zxpSpanEqB firstRows secondRows = true ->
    ZxwConv (zxnNormalForm domWidth codWidth firstRows)
      (zxnNormalForm domWidth codWidth secondRows)

/-- OWNER MARKER (FALSE): the generator-list transport is not proven this round. -/
def zxwGeneratorTransportIsProven : Bool := false

/-- (D) base case transported: the empty diagram at boundary 0 converts to the
normal form of its own denotation. -/
theorem zxwEmptyDiagramAbsorbed :
    ZxwConv { sourceArity := 0, layers := [] }
      (zxnNormalForm 0 0
        (zxpDiagramDenote { sourceArity := 0, layers := [] })) :=
  zxwOfZxeConv zxaEmptyDiagramAbsorbed

/-- (D) zero-generator fire transported: the kill-create diagram lands on
`zxnNormalForm` of its own denotation. -/
theorem zxwKillCreateAbsorbedFire :
    ZxwConv
      { sourceArity := 1
        layers := [[ZxpCell.xSpider 1 0], [ZxpCell.xSpider 0 1]] }
      (zxnNormalForm 1 1 (zxpDiagramDenote
        { sourceArity := 1
          layers := [[ZxpCell.xSpider 1 0], [ZxpCell.xSpider 0 1]] })) :=
  zxwOfZxeConv zxaKillCreateAbsorbedFire

/-- COMPLETENESS statement over the WIRING-EXTENDED congruence — VERBATIM the
committed shape (`zxeCompletenessStatement`) with `ZxwConv` in the conclusion.
OWNER FALSE — NOT PROVEN.  The precise delta to the flip: `zxwAbsorptionStatement`
plus `zxwGeneratorTransportStatement` (absorb both diagrams to the normal forms of
their own denotation matrices, then transport between the span-equal generator
lists).  Both residuals are named owner-false above; the wiring wall that blocked
the prior round is not among them. -/
def zxwCompletenessStatement : Prop :=
  (firstDiagram secondDiagram : ZxpDiagram) ->
    ZxpDiagramWF firstDiagram -> ZxpDiagramWF secondDiagram ->
    firstDiagram.sourceArity = secondDiagram.sourceArity ->
    zxpDiagramCodArity firstDiagram = zxpDiagramCodArity secondDiagram ->
    ZxpRelEquiv firstDiagram.sourceArity (zxpDiagramCodArity firstDiagram)
      (zxpDiagramDenote firstDiagram) (zxpDiagramDenote secondDiagram) ->
    ZxwConv firstDiagram secondDiagram

/-- OWNER MARKER (FALSE): completeness over `ZxwConv` is NOT proven. -/
def zxwCompletenessIsProven : Bool := false

/-- Completeness reduces to the two named residuals: absorption plus generator
transport IMPLY the full completeness statement (the assembly is proved; only the
two inputs are open). -/
theorem zxwCompletenessOfAbsorptionAndTransport
    (hAbsorption : zxwAbsorptionStatement)
    (hTransport : zxwGeneratorTransportStatement) :
    zxwCompletenessStatement := by
  intro firstDiagram secondDiagram hFirstWF hSecondWF hSourceEq hCodEq hEquiv
  have hFirstNF := hAbsorption firstDiagram hFirstWF
  have hSecondNF := hAbsorption secondDiagram hSecondWF
  have hSpan : zxpSpanEqB (zxpDiagramDenote firstDiagram)
      (zxpDiagramDenote secondDiagram) = true :=
    zxpSpanEqBOfRelEquiv
      (zxpDiagramDenoteWidth firstDiagram hFirstWF)
      (zxpAllWidthCast (by rw [hSourceEq, hCodEq])
        (zxpDiagramDenoteWidth secondDiagram hSecondWF))
      hEquiv
  have hTransported := hTransport firstDiagram.sourceArity
    (zxpDiagramCodArity firstDiagram)
    (zxpDiagramDenote firstDiagram) (zxpDiagramDenote secondDiagram)
    (zxpDiagramDenoteWidth firstDiagram hFirstWF)
    (zxpAllWidthCast (by rw [hSourceEq, hCodEq])
      (zxpDiagramDenoteWidth secondDiagram hSecondWF))
    hSpan
  have hSecondNFCast : ZxwConv secondDiagram
      (zxnNormalForm firstDiagram.sourceArity (zxpDiagramCodArity firstDiagram)
        (zxpDiagramDenote secondDiagram)) := by
    rw [hSourceEq, hCodEq]
    exact hSecondNF
  exact ZxwConv.trans hFirstNF
    (ZxwConv.trans hTransported (ZxwConv.symm hSecondNFCast))

/-- THE CONDITIONAL DECISION COROLLARY: under the completeness statement,
`ZxwConv` convertibility of well-formed boundary-matched diagrams IS the kernel
span decision. -/
theorem zxwDecisionUnderCompleteness (hCompleteness : zxwCompletenessStatement)
    (firstDiagram secondDiagram : ZxpDiagram)
    (hFirstWF : ZxpDiagramWF firstDiagram) (hSecondWF : ZxpDiagramWF secondDiagram)
    (hSourceEq : firstDiagram.sourceArity = secondDiagram.sourceArity)
    (hCodEq : zxpDiagramCodArity firstDiagram = zxpDiagramCodArity secondDiagram) :
    Iff (ZxwConv firstDiagram secondDiagram)
      (zxpSpanEqB (zxpDiagramDenote firstDiagram) (zxpDiagramDenote secondDiagram)
        = true) := by
  refine Iff.intro ?_ ?_
  · intro hConv
    exact zxwConvSpanEqB hConv
  · intro hSpan
    refine hCompleteness firstDiagram secondDiagram hFirstWF hSecondWF hSourceEq
      hCodEq ?_
    exact zxpRelEquivOfSpanEqB
      (zxpDiagramDenoteWidth firstDiagram hFirstWF)
      (zxpAllWidthCast (by rw [hSourceEq, hCodEq])
        (zxpDiagramDenoteWidth secondDiagram hSecondWF))
      hSpan

/-! ## Stage 9 — the honest marker ledger -/

/-- MARKER: THE WIRING SCHEMA IS LIVE — naturality slides at every cell and both
orientations with structural all-arity soundness
(`zxwSlideRightBundle`/`zxwSlideLeftBundle` through the staircase rotation
characterizations), sigma involution kernel-decided, the full embedding
`zxwOfZxeConv`, the engines transported, the gate re-run CLEAN with the honest
crossing-count analysis, and the wall's committed minimal instances DERIVED
(`zxwCounitSlideZ/X`, `zxwUnitSlideZ/X`, `zxwSigmaInvolutionFire`) plus
Yang-Baxter as a slide instance (`zxwYangBaxter`).  The committed `ZxeConv`
owners (`zxaCounitSlideStatement`, `zxaSigmaInvolutionStatement`,
`zxaCrossingSlideIsProven := false`) stay byte-intact in their home file — the
schema lands as NEW MOVES, exactly the honest next move recorded there. -/
def zxwHasWiringSchema : Bool := true

/-- MARKER (FALSE): THE FULL PHASE-FREE DECISION did not flip this round.
`zxwCompletenessStatement` is owner-false; the assembly from the two named
residuals is proved (`zxwCompletenessOfAbsorptionAndTransport`), the conditional
decision is in place (`zxwDecisionUnderCompleteness`), and the residuals are
`zxwAbsorptionIsProven := false` (per-cell normal-form bookkeeping, route
unblocked) and `zxwGeneratorTransportIsProven := false` (row-operation transport,
route documented).  No inhabitant of any completeness statement and no
unconditional decision instance exist in this development. -/
def zxwHasFullDecision : Bool := false

end FX1Poly.Polygraph.Omega.ZXPhaseFree
