import FX1Poly.Polygraph.Omega.ZXPhaseFree.CrossingResidual

/-! # Polygraph/Omega/ZXPhaseFree/CrossingKillDeath — the middle-band
interchange that inhabits the crossing kill-death wall

The r14 `CrossingResidual` reduced the phase-free crossing residual
`zxbCrossingAbsorbStatement` to EXACTLY ONE named cell-level statement, the
kill-death `zxcCrossIntoKillStatement`: a strand crossing whiskered anywhere
above the kill layer dies, both crossed legs feeding adjacent kill collectors
with spectator KILL cells on the side bands and wire cells on the codomain
band.  The width-2 death is the committed r13 `zxbCrossingIntoKillPairFire`; the
general-position death with WIRE spectators is the committed r13/r14
`zxcCrossIntoKillPairWhiskered`.  The remaining gap was exactly the SPECTATOR
KILL CELLS on the side bands — a genuine tensor-band interchange (a killed
middle band with kill-cell contexts left and right) that the existing
disjoint-block engines `zxwLayerPastRightLayers` / `zxwLayersPastRightLayer` do
not directly instantiate.

This round BUILDS the missing middle-band interchange and INHABITS the wall:

* THE KILL-CELLS SPLIT (`zxkKillCellsCat`): a block of `killCount` X-collectors
  factors as the cat of two shorter blocks (the analogue of `zxnWireCellsCat`).
* THE RIGHT-KILL PEEL (`zxkRightKillPeel`): a single kill layer `M (x) x10^r`
  splits into two sequential layers, `M` firing first (right kills passing as
  wires), then the right kills last — ONE `splitLayer` move.
* THE LEFT-KILL PEEL (`zxkLeftKillPeel`): a single kill layer `x10^l (x) M`
  splits into `M` firing first (left kills passing as wires), then the left
  kills last — one `splitLayer` plus one firing of the disjoint-block engine
  `zxwLayerPastRightLayers` (the right-first interchange the left kills need).
* THE MIDDLE-BAND INTERCHANGE (`zxkKillLayerMiddleSplit`): the full kill layer
  `x10^l (x) killpair (x) x10^r` factors as the middle kill (killpair with WIRE
  spectators on both sides — exactly the shape the whiskered death consumes)
  followed by the two side kills as trailing layers.  Left peel + right peel.
* THE CORE DEATH (`zxkCrossIntoKillCore`): a crossing whiskered at any strand
  pair dies into its own two adjacent kill collectors WITH kill spectators on
  both side bands (codomain width 0).  The interchange floats the middle kill
  up under the crossing, the whiskered death fires, the interchange refolds.
* THE WALL, INHABITED (`zxkCrossIntoKillHolds : zxcCrossIntoKillStatement`): the
  core death lifted with codomain wire spectators on the right — one firing of
  the pad-lift with `rightWires := codWidth`.
* THE CROSSING ABSORPTION, UNCONDITIONAL (`zxkCrossingAbsorbHolds`): feeding the
  inhabited wall to the committed conditional `zxcCrossingAbsorbOfKillDeath`
  discharges `zxbCrossingAbsorbStatement` with no residual.

Raw Lean 4 + Init only; zero-axiom; structural recursion only; no
`List.append`, no `Int`, no `Nat.sub/div/mod/min/max`, no wildcard match arms
over inductive scrutinees.  The committed owner-false flags in
`AbsorptionInduction` and `CrossingResidual` stay byte-intact; the fresh true
content markers are `zxkHasCrossIntoKillDeath` and
`zxkHasUnconditionalCrossingAbsorb`. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 8192

namespace FX1Poly.Polygraph.Omega.ZXPhaseFree

/-! ## Stage 0 — the kill-cells split (the counit-collector analogue of the
wire split) -/

/-- A block of `leftCount + rightCount` X-collectors is the cat of the two
shorter collector blocks.  The counit-side analogue of `zxnWireCellsCat`. -/
theorem zxkKillCellsCat : (leftCount rightCount : Nat) ->
    zxnKillCells (leftCount + rightCount)
      = zxpCatCells (zxnKillCells leftCount) (zxnKillCells rightCount)
  | 0, rightCount => by
      show zxnKillCells (0 + rightCount) = zxnKillCells rightCount
      rw [Nat.zero_add]
  | leftPred + 1, rightCount => by
      rw [Nat.succ_add leftPred rightCount]
      show ZxpCell.xSpider 1 0 :: zxnKillCells (leftPred + rightCount)
        = zxpCatCells (zxnKillCells (leftPred + 1)) (zxnKillCells rightCount)
      rw [zxkKillCellsCat leftPred rightCount]
      rfl

/-! ## Stage 1 — the two side-kill peels (single-layer kill splits into a
sequential factoring) -/

/-- THE RIGHT-KILL PEEL: a single layer `middleCells (x) x10^rightCount` splits
into the middle firing first (right kills passing as wires) and the right kills
last.  One `splitLayer` window move (`splitLayer` fires the LEFT group first,
and the middle is on the left here). -/
theorem zxkRightKillPeel (middleCells : List ZxpCell) (rightCount : Nat) :
    ZxwConv
      { sourceArity := zxpLayerDomArity middleCells + rightCount
        layers := [zxpCatCells middleCells (zxnKillCells rightCount)] }
      { sourceArity := zxpLayerDomArity middleCells + rightCount
        layers := [zxpCatCells middleCells (zxpWireCells rightCount),
          zxpCatCells (zxpWireCells (zxpLayerCodArity middleCells))
            (zxnKillCells rightCount)] } := by
  have hMove := zxwMoveConv (ZxwWindowMove.base (ZxeWindowMove.base
    (ZxrWindowMove.seed (ZxpWindowMove.splitLayer middleCells (zxnKillCells rightCount)))))
  rw [zxnKillCellsDomArity rightCount] at hMove
  exact hMove

/-- THE LEFT-KILL PEEL: a single layer `x10^leftCount (x) middleCells` splits
into the middle firing first (left kills passing as wires) and the left kills
last.  One `splitLayer` to expose the block-first form, then one firing of the
disjoint-block engine `zxwLayerPastRightLayers` (the right-first interchange the
physically-left kills need to fire last). -/
theorem zxkLeftKillPeel (leftCount : Nat) (middleCells : List ZxpCell) :
    ZxwConv
      { sourceArity := leftCount + zxpLayerDomArity middleCells
        layers := [zxpCatCells (zxnKillCells leftCount) middleCells] }
      { sourceArity := leftCount + zxpLayerDomArity middleCells
        layers := [zxpCatCells (zxpWireCells leftCount) middleCells,
          zxpCatCells (zxnKillCells leftCount)
            (zxpWireCells (zxpLayerCodArity middleCells))] } := by
  -- step 1: splitLayer exposes the block-first form `[x10^l (x) wire, middle]`
  have hSplit := zxwMoveConv (ZxwWindowMove.base (ZxeWindowMove.base
    (ZxrWindowMove.seed (ZxpWindowMove.splitLayer (zxnKillCells leftCount) middleCells))))
  rw [zxnKillCellsDomArity leftCount, zxnKillCellsCodArity leftCount] at hSplit
  -- step 2: the disjoint-block engine moves the left kill to fire last
  have hEngine := zxwOfZxeConv (zxwLayerPastRightLayers (zxnKillCells leftCount)
    [middleCells] (zxpLayerDomArity middleCells)
    (ZxpLayersWF.cons rfl (ZxpLayersWF.nil _)))
  rw [zxnKillCellsDomArity leftCount, zxnKillCellsCodArity leftCount] at hEngine
  -- the engine's whiskered layers reduce (right-zero whisker, zero-zero whisker)
  rw [zxwWhiskerRightZeroCons leftCount middleCells [],
    show zxpWhiskerLayers leftCount 0 ([] : List (List ZxpCell)) = [] from rfl,
    zxpWhiskerLayersZero [middleCells],
    show zxpLayersCodArity (zxpLayerDomArity middleCells) [middleCells]
      = zxpLayerCodArity middleCells from rfl] at hEngine
  exact ZxwConv.trans hSplit hEngine

/-- The right-kill peel with the middle boundary arities supplied explicitly. -/
theorem zxkRightKillPeelAt (middleCells : List ZxpCell)
    (middleDom middleCod rightCount : Nat)
    (hDom : zxpLayerDomArity middleCells = middleDom)
    (hCod : zxpLayerCodArity middleCells = middleCod) :
    ZxwConv
      { sourceArity := middleDom + rightCount
        layers := [zxpCatCells middleCells (zxnKillCells rightCount)] }
      { sourceArity := middleDom + rightCount
        layers := [zxpCatCells middleCells (zxpWireCells rightCount),
          zxpCatCells (zxpWireCells middleCod) (zxnKillCells rightCount)] } := by
  subst hDom
  subst hCod
  exact zxkRightKillPeel middleCells rightCount

/-- The left-kill peel with the middle boundary arities supplied explicitly. -/
theorem zxkLeftKillPeelAt (leftCount : Nat) (middleCells : List ZxpCell)
    (middleDom middleCod : Nat)
    (hDom : zxpLayerDomArity middleCells = middleDom)
    (hCod : zxpLayerCodArity middleCells = middleCod) :
    ZxwConv
      { sourceArity := leftCount + middleDom
        layers := [zxpCatCells (zxnKillCells leftCount) middleCells] }
      { sourceArity := leftCount + middleDom
        layers := [zxpCatCells (zxpWireCells leftCount) middleCells,
          zxpCatCells (zxnKillCells leftCount) (zxpWireCells middleCod)] } := by
  subst hDom
  subst hCod
  exact zxkLeftKillPeel leftCount middleCells

/-! ## Stage 2 — THE MIDDLE-BAND INTERCHANGE: the full kill layer factors as the
middle kill (wire spectators both sides) followed by the two side kills -/

/-- THE MIDDLE-BAND INTERCHANGE (the one piece the r14 note named as missing):
the full kill layer `x10^l (x) killpair (x) x10^r` factors as the middle killpair
with WIRE spectators on both sides — exactly the shape the whiskered crossing
death consumes — followed by the left and right kills as two trailing layers.
Left-kill peel plus right-kill peel plus one lift; no new primitive. -/
theorem zxkKillLayerMiddleSplit (leftWires rightWires : Nat) :
    ZxwConv
      { sourceArity := leftWires + (2 + rightWires)
        layers := [zxnKillLayer (leftWires + (2 + rightWires)) 0] }
      { sourceArity := leftWires + (2 + rightWires)
        layers := [zxpWhiskerLayer leftWires rightWires (zxnKillLayer 2 0),
          zxpCatCells (zxpWireCells leftWires) (zxnKillCells rightWires),
          zxpCatCells (zxnKillCells leftWires) (zxpWireCells 0)] } := by
  -- eqLHS: the merged kill layer is `x10^l (x) (x10^2 (x) x10^r)`
  have eqLHS : zxnKillLayer (leftWires + (2 + rightWires)) 0
      = zxpCatCells (zxnKillCells leftWires)
          (zxpCatCells (zxnKillCells 2) (zxnKillCells rightWires)) := by
    show zxpCatCells (zxnKillCells (leftWires + (2 + rightWires)))
        (zxpWireCells 0) = _
    rw [show zxpWireCells 0 = ([] : List ZxpCell) from rfl, zxpCatCellsNilRight,
      zxkKillCellsCat leftWires (2 + rightWires), zxkKillCellsCat 2 rightWires]
  -- the reassociation of the middle band
  have hReassoc : zxpCatCells (zxpWireCells leftWires)
        (zxpCatCells (zxnKillCells 2) (zxnKillCells rightWires))
      = zxpCatCells (zxpCatCells (zxpWireCells leftWires) (zxnKillCells 2))
        (zxnKillCells rightWires) :=
    (zxnCatCellsAssoc (zxpWireCells leftWires) (zxnKillCells 2)
      (zxnKillCells rightWires)).symm
  -- the whisker bridge: `(wire^l (x) x10^2) (x) wire^r = whisker l r (killpair)`
  have hWhiskerBridge : zxpCatCells
        (zxpCatCells (zxpWireCells leftWires) (zxnKillCells 2)) (zxpWireCells rightWires)
      = zxpWhiskerLayer leftWires rightWires (zxnKillLayer 2 0) := by
    rw [zxnCatCellsAssoc (zxpWireCells leftWires) (zxnKillCells 2) (zxpWireCells rightWires)]
    rfl
  -- the left peel
  have hLeftPeel := zxkLeftKillPeelAt leftWires
    (zxpCatCells (zxnKillCells 2) (zxnKillCells rightWires)) (2 + rightWires) 0
    (by rw [zxpCatCellsDomArity, zxnKillCellsDomArity, zxnKillCellsDomArity])
    (by rw [zxpCatCellsCodArity, zxnKillCellsCodArity, zxnKillCellsCodArity])
  -- the right peel, cast to the `l + (2 + r)` frame and bridged to the whisker form
  have hRightPeel : ZxwConv
      { sourceArity := leftWires + (2 + rightWires)
        layers := [zxpCatCells (zxpWireCells leftWires)
          (zxpCatCells (zxnKillCells 2) (zxnKillCells rightWires))] }
      { sourceArity := leftWires + (2 + rightWires)
        layers := [zxpWhiskerLayer leftWires rightWires (zxnKillLayer 2 0),
          zxpCatCells (zxpWireCells leftWires) (zxnKillCells rightWires)] } := by
    have hRaw := zxkRightKillPeelAt
      (zxpCatCells (zxpWireCells leftWires) (zxnKillCells 2))
      (leftWires + 2) leftWires rightWires
      (by rw [zxpCatCellsDomArity, zxpWireCellsDomArity, zxnKillCellsDomArity])
      (by rw [zxpCatCellsCodArity, zxpWireCellsCodArity, zxnKillCellsCodArity, Nat.add_zero])
    rw [Nat.add_assoc leftWires 2 rightWires, <- hReassoc, hWhiskerBridge] at hRaw
    exact hRaw
  -- lift the right peel under the trailing left-kill layer
  have hRightLifted := zxwLiftConv (leftWires + (2 + rightWires)) []
    [zxpCatCells (zxnKillCells leftWires) (zxpWireCells 0)] hRightPeel
    (ZxpLayersWF.nil _) rfl
    (ZxpLayersWF.cons
      (by
        show zxpLayerDomArity
            (zxpCatCells (zxnKillCells leftWires) (zxpWireCells 0))
          = zxpLayerCodArity (zxpCatCells (zxpWireCells leftWires)
              (zxpCatCells (zxnKillCells 2) (zxnKillCells rightWires)))
        rw [zxpCatCellsDomArity, zxnKillCellsDomArity, zxpWireCellsDomArity,
          zxpCatCellsCodArity, zxpWireCellsCodArity, zxpCatCellsCodArity,
          zxnKillCellsCodArity, zxnKillCellsCodArity])
      (ZxpLayersWF.nil _))
  rw [eqLHS]
  exact ZxwConv.trans hLeftPeel hRightLifted

/-! ## Stage 3 — THE CORE DEATH (codomain width 0): a whiskered crossing dies
into its own kill collectors WITH kill spectators on both side bands -/

/-- THE CORE DEATH: a strand crossing whiskered at any strand pair, above its
own two adjacent kill collectors WITH kill-cell spectators on both side bands
(and NO codomain band), dies.  The interchange floats the middle kill up under
the crossing, the whiskered death fires, the interchange refolds. -/
theorem zxkCrossIntoKillCore (leftWires rightWires : Nat) :
    ZxwConv
      { sourceArity := leftWires + (2 + rightWires)
        layers := [zxpWhiskerLayer leftWires rightWires [ZxpCell.crossing],
          zxnKillLayer (leftWires + (2 + rightWires)) 0] }
      { sourceArity := leftWires + (2 + rightWires)
        layers := [zxnKillLayer (leftWires + (2 + rightWires)) 0] } := by
  have hSplit := zxkKillLayerMiddleSplit leftWires rightWires
  -- step 1: float the middle kill up under the crossing
  have hStep1 := zxwLiftConv (leftWires + (2 + rightWires))
    [zxpWhiskerLayer leftWires rightWires [ZxpCell.crossing]] [] hSplit
    (ZxpLayersWF.cons
      (by rw [zxpWhiskerLayerDomArity,
        show zxpLayerDomArity [ZxpCell.crossing] = 2 from rfl])
      (ZxpLayersWF.nil _))
    (by
      show zxpLayerCodArity (zxpWhiskerLayer leftWires rightWires [ZxpCell.crossing])
        = leftWires + (2 + rightWires)
      rw [zxpWhiskerLayerCodArity,
        show zxpLayerCodArity [ZxpCell.crossing] = 2 from rfl])
    (ZxpLayersWF.nil _)
  rw [zxpCatLayersNilRight, zxpCatLayersNilRight] at hStep1
  -- step 2: the whiskered death fires under the trailing side kills
  have hStep2 := zxwLiftConv (leftWires + (2 + rightWires)) []
    [zxpCatCells (zxpWireCells leftWires) (zxnKillCells rightWires),
      zxpCatCells (zxnKillCells leftWires) (zxpWireCells 0)]
    (zxcCrossIntoKillPairWhiskered leftWires rightWires)
    (ZxpLayersWF.nil _) rfl
    (ZxpLayersWF.cons
      (by
        show zxpLayerDomArity
            (zxpCatCells (zxpWireCells leftWires) (zxnKillCells rightWires))
          = zxpLayerCodArity (zxpWhiskerLayer leftWires rightWires (zxnKillLayer 2 0))
        rw [zxpCatCellsDomArity, zxpWireCellsDomArity, zxnKillCellsDomArity,
          zxpWhiskerLayerCodArity,
          show zxpLayerCodArity (zxnKillLayer 2 0) = 0 from rfl, Nat.zero_add])
      (ZxpLayersWF.cons
        (by
          show zxpLayerDomArity (zxpCatCells (zxnKillCells leftWires) (zxpWireCells 0))
            = zxpLayerCodArity
                (zxpCatCells (zxpWireCells leftWires) (zxnKillCells rightWires))
          rw [zxpCatCellsDomArity, zxnKillCellsDomArity, zxpWireCellsDomArity,
            zxpCatCellsCodArity, zxpWireCellsCodArity, zxnKillCellsCodArity])
        (ZxpLayersWF.nil _)))
  -- chain: cross+kill -> cross+middle+sides -> middle+sides -> kill
  exact ZxwConv.trans hStep1 (ZxwConv.trans hStep2 (ZxwConv.symm hSplit))

/-! ## Stage 4 — THE WALL, INHABITED: the core death lifted with codomain wire
spectators discharges `zxcCrossIntoKillStatement` -/

/-- THE KILL-DEATH, INHABITED: the r14 wall `zxcCrossIntoKillStatement` holds.
The codomain-width-0 core death (`zxkCrossIntoKillCore`) is lifted with `codWidth`
codomain wire spectators on the right by a single firing of the pad-lift — the
crossing's right band widens from `rightWires` to `rightWires + codWidth`, and
the kill layer's codomain band widens from `0` to `codWidth`. -/
theorem zxkCrossIntoKillHolds : zxcCrossIntoKillStatement := by
  intro leftWires rightWires codWidth
  have hLift := zxwConvLift ((leftWires + (2 + rightWires)) + codWidth) 0 codWidth [] []
    (zxkCrossIntoKillCore leftWires rightWires)
    (ZxpLayersWF.nil _)
    (by
      show (leftWires + (2 + rightWires)) + codWidth
        = 0 + ((leftWires + (2 + rightWires)) + codWidth)
      rw [Nat.zero_add])
    (ZxpLayersWF.nil _)
  have hCrossEq : zxpWhiskerLayer 0 codWidth
        (zxpWhiskerLayer leftWires rightWires [ZxpCell.crossing])
      = zxpWhiskerLayer leftWires (rightWires + codWidth) [ZxpCell.crossing] := by
    rw [zxnWhiskerLayerCompose 0 codWidth leftWires rightWires [ZxpCell.crossing],
      Nat.zero_add]
  have hKillEq : zxpWhiskerLayer 0 codWidth
        (zxnKillLayer (leftWires + (2 + rightWires)) 0)
      = zxnKillLayer (leftWires + (2 + rightWires)) codWidth := by
    show zxpCatCells (zxpCatCells (zxnKillCells (leftWires + (2 + rightWires)))
        (zxpWireCells 0)) (zxpWireCells codWidth)
      = zxpCatCells (zxnKillCells (leftWires + (2 + rightWires))) (zxpWireCells codWidth)
    rw [show zxpWireCells 0 = ([] : List ZxpCell) from rfl, zxpCatCellsNilRight]
  dsimp only [zxpPadDiagram, zxpWhiskerLayers, zxpCatLayers] at hLift
  rw [hCrossEq, hKillEq] at hLift
  exact hLift

/-! ## Stage 5 — THE CROSSING ABSORPTION, UNCONDITIONAL: feed the inhabited wall
to the committed conditional -/

/-- THE CROSSING RESIDUAL, DISCHARGED: with the kill-death now inhabited, the
committed conditional `zxcCrossingAbsorbOfKillDeath` yields the whole crossing
residual `zxbCrossingAbsorbStatement` with no residual hypothesis. -/
theorem zxkCrossingAbsorbHolds : zxbCrossingAbsorbStatement :=
  zxcCrossingAbsorbOfKillDeath zxkCrossIntoKillHolds

/-! ## Stage 6 — fires, span pins, and the honest marker ledger -/

/-- Fire: the kill-death at the edge instance the wall note named — one left
wire, no right wire, one codomain wire (`leftWires = 1`, `rightWires = 0`,
`codWidth = 1`).  A single left-band kill spectator and a codomain wire. -/
theorem zxkCrossIntoKillFireEdge :
    ZxwConv
      { sourceArity := (1 + (2 + 0)) + 1
        layers := [zxpWhiskerLayer 1 (0 + 1) [ZxpCell.crossing],
          zxnKillLayer (1 + (2 + 0)) 1] }
      { sourceArity := (1 + (2 + 0)) + 1
        layers := [zxnKillLayer (1 + (2 + 0)) 1] } :=
  zxkCrossIntoKillHolds 1 0 1

/-- Kernel span pin for the edge fire. -/
theorem zxkCrossIntoKillFireEdgeSpanPin :
    zxpSpanEqB
      (zxpDiagramDenote
        { sourceArity := (1 + (2 + 0)) + 1
          layers := [zxpWhiskerLayer 1 (0 + 1) [ZxpCell.crossing],
            zxnKillLayer (1 + (2 + 0)) 1] })
      (zxpDiagramDenote
        { sourceArity := (1 + (2 + 0)) + 1
          layers := [zxnKillLayer (1 + (2 + 0)) 1] }) = true := rfl

/-- Fire: the kill-death with NONZERO side bands on BOTH sides plus a codomain
wire (`leftWires = 1`, `rightWires = 1`, `codWidth = 1`) — a left kill spectator,
a right kill spectator, and a passing codomain wire, the general position the
r14 note said the existing engines could not reach. -/
theorem zxkCrossIntoKillFireBands :
    ZxwConv
      { sourceArity := (1 + (2 + 1)) + 1
        layers := [zxpWhiskerLayer 1 (1 + 1) [ZxpCell.crossing],
          zxnKillLayer (1 + (2 + 1)) 1] }
      { sourceArity := (1 + (2 + 1)) + 1
        layers := [zxnKillLayer (1 + (2 + 1)) 1] } :=
  zxkCrossIntoKillHolds 1 1 1

/-- Kernel span pin for the both-bands fire. -/
theorem zxkCrossIntoKillFireBandsSpanPin :
    zxpSpanEqB
      (zxpDiagramDenote
        { sourceArity := (1 + (2 + 1)) + 1
          layers := [zxpWhiskerLayer 1 (1 + 1) [ZxpCell.crossing],
            zxnKillLayer (1 + (2 + 1)) 1] })
      (zxpDiagramDenote
        { sourceArity := (1 + (2 + 1)) + 1
          layers := [zxnKillLayer (1 + (2 + 1)) 1] }) = true := rfl

/-- Fire: the middle-band interchange at a both-bands instance — the merged kill
layer factors as the middle kill (wire spectators both sides) then the two side
kills. -/
theorem zxkKillLayerMiddleSplitFire :
    ZxwConv
      { sourceArity := 1 + (2 + 1)
        layers := [zxnKillLayer (1 + (2 + 1)) 0] }
      { sourceArity := 1 + (2 + 1)
        layers := [zxpWhiskerLayer 1 1 (zxnKillLayer 2 0),
          zxpCatCells (zxpWireCells 1) (zxnKillCells 1),
          zxpCatCells (zxnKillCells 1) (zxpWireCells 0)] } :=
  zxkKillLayerMiddleSplit 1 1

/-- CONTENT MARKER (TRUE): the kill-death wall is INHABITED this round — the
middle-band interchange `zxkKillLayerMiddleSplit` is built and
`zxkCrossIntoKillHolds : zxcCrossIntoKillStatement` is a zero-axiom inhabitant. -/
def zxkHasCrossIntoKillDeath : Bool := true

/-- CONTENT MARKER (TRUE): the phase-free crossing residual
`zxbCrossingAbsorbStatement` is discharged UNCONDITIONALLY this round
(`zxkCrossingAbsorbHolds`), the r14 residual hypothesis now supplied. -/
def zxkHasUnconditionalCrossingAbsorb : Bool := true

/-! ## Stage 7 — THE IDENTITY RESIDUAL (stretch): walled, with the two burned
attacks and a soundness pin -/

/-- Kernel span pin: the identity residual `zxbIdentityAbsorbStatement` is
semantically SOUND at `wireCount = 2` (fresh) — the empty two-wire diagram and
the normal form of its own identity denotation denote the same span.  This is
the soundness certificate the walled identity residual would consume. -/
theorem zxkIdentityResidualSpanPinTwo :
    zxpSpanEqB
      (zxpDiagramDenote { sourceArity := 2, layers := [] })
      (zxpDiagramDenote (zxnNormalForm 2 2
        (zxpDiagramDenote { sourceArity := 2, layers := [] }))) = true := rfl

/-- OWNER MARKER (FALSE): the identity residual `zxbIdentityAbsorbStatement` is
NOT proven this round.  With the crossing kill-death now closed
(`zxkCrossIntoKillHolds`) the identity residual is no longer blocked on an OPEN
wall, but its ASSEMBLY is a distinct construction that this round does not build.

Two attacks burned:

* (a) DIRECT ENGINE INSTANTIATION.  The committed rides
  (`zxcGeneratorBlocksCrossRide`, and this round's `zxkCrossIntoKillHolds`) RIDE
  a crossing THROUGH an existing normal form or KILL a crossing at the boundary;
  none MATERIALIZES the normal form `zxnNormalForm n n (idRows n)` from the empty
  diagram.  The empty-diagram base `zxwEmptyDiagramAbsorbed` is `wireCount = 0`
  only; no committed engine lifts it to positive `wireCount`.

* (b) INDUCTION ON `wireCount`.  Base `zxbIdentityAbsorbZeroFire`; the step needs
  `zxnNormalForm (n+1) (n+1) (idRows (n+1))` to decompose as the width-`n` normal
  form plus one strand's create-route-discard comb.  It does NOT: `idRows (n+1)`
  is `[[true,false,true,false,...],[false,true,...]]` (the interleaved identity
  generator, confirmed by kernel `#eval` = `[[true,false,true,false],
  [false,true,false,true]]` at `n = 2`), so the added strand's created state must
  ROUTE PAST the existing `n` generator combs.  That routing is a CREATE-state
  ride past a block, NOT a crossing ride and NOT a kill-death — it is not among
  the committed engines nor built here.  The comb-column routing the r14 note
  named is now UNBLOCKED (the crossing wall is closed) but the create-state ride
  and the `wireCount` induction that reshapes `idRows` per added strand remain a
  separate arc. -/
def zxkIdentityAbsorbIsProven : Bool := false

end FX1Poly.Polygraph.Omega.ZXPhaseFree
