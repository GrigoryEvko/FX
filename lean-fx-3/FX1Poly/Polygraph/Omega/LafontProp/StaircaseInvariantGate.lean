import FX1Poly.Polygraph.Omega.LafontProp.StrictLayerEmbedding

/-! # Polygraph/Omega/LafontProp/StaircaseInvariantGate — the invariant-first refutation gate
(LAFONT-REPAIR stage 2 phase 1: THE ADVERSARIAL HUNT, verdict CLEAN BILL)

TARGET UNDER GATE (not proven here, not claimed): every composable `SldDiagram` is
`SldAreConvertibleLayers`-convertible to a canonical diagram determined by its Mat(N)
denotation (boundary pair + matrix rectangle).  This arc has eaten FOUR missing-row defects,
each caught by a conserved-quantity refutation and never by soundness — so before any
completeness push, this file hunts for a Z2-or-richer invariant of the 24-constructor
congruence that is NOT a function of the (boundary, matrix) data.  A single such invariant
with an equal-matrix separator pair refutes the target outright.

## The 24 edges being audited

Groupoid closure (`fromReflexivity`/`fromSymmetry`/`fromTransitivity`), congruence under a
free-index leading layer (`underLayerPrefix`), the two layer-split moves
(`layerSplitTopActsFirst`/`layerSplitBottomActsFirst` — generator cells preserved, `srcY+tgtX`
resp. `srcX+tgtY` wire cells and one layer created), and the 18 padded-row fires, each a
family over `(padAboveCount, padBelowCount, suffixLayers)` where `sldPadWindow` adds
`padAbove+padBelow` wire cells PER WINDOW LAYER (so a row's wire delta varies within its own
family: base + (p+q)*layerDelta).

## THE ROW-EFFECT TABLE (machine-checked below as `lstRowEffectTableHolds`, kernel `rfl`)

Count vectors per window: (mu, eta, delta, eps, cross, wire | layers).

| row  | left window            | counts L          | right window          | counts R          | delta R-L                 |
|------|------------------------|-------------------|-----------------------|-------------------|---------------------------|
| M1   | [[mu,w],[mu]]          | (2,0,0,0,0,1 | 2) | [[w,mu],[mu]]         | (2,0,0,0,0,1 | 2) | 0                         |
| M2   | [[eta,w],[mu]]         | (1,1,0,0,0,1 | 2) | []                    | 0                 | (-1,-1,0,0,0,-1 | -2)     |
| M3   | [[w,eta],[mu]]         | (1,1,0,0,0,1 | 2) | []                    | 0                 | (-1,-1,0,0,0,-1 | -2)     |
| M4   | [[cr],[mu]]            | (1,0,0,0,1,0 | 2) | [[mu]]                | (1,0,0,0,0,0 | 1) | (0,0,0,0,-1,0 | -1)       |
| C1   | [[d],[d,w]]            | (0,0,2,0,0,1 | 2) | [[d],[w,d]]           | (0,0,2,0,0,1 | 2) | 0                         |
| C2   | [[d],[eps,w]]          | (0,0,1,1,0,1 | 2) | []                    | 0                 | (0,0,-1,-1,0,-1 | -2)     |
| C3   | [[d],[w,eps]]          | (0,0,1,1,0,1 | 2) | []                    | 0                 | (0,0,-1,-1,0,-1 | -2)     |
| C4   | [[d],[cr]]             | (0,0,1,0,1,0 | 2) | [[d]]                 | (0,0,1,0,0,0 | 1) | (0,0,0,0,-1,0 | -1)       |
| B1   | [[mu],[d]]             | (1,0,1,0,0,0 | 2) | [[d,d],[w,cr,w],[mu,mu]] | (2,0,2,0,1,2 | 3) | (+1,0,+1,0,+1,+2 | +1) |
| B2   | [[eta],[d]]            | (0,1,1,0,0,0 | 2) | [[eta,eta]]           | (0,2,0,0,0,0 | 1) | (0,+1,-1,0,0,0 | -1)      |
| B3   | [[mu],[eps]]           | (1,0,0,1,0,0 | 2) | [[eps,eps]]           | (0,0,0,2,0,0 | 1) | (-1,0,0,+1,0,0 | -1)      |
| B4   | [[eta],[eps]]          | (0,1,0,1,0,0 | 2) | []                    | 0                 | (0,-1,0,-1,0,0 | -2)      |
| S1   | [[cr],[cr]]            | (0,0,0,0,2,0 | 2) | []                    | 0                 | (0,0,0,0,-2,0 | -2)       |
| S2   | YB left, 3 layers      | (0,0,0,0,3,3 | 3) | YB right, 3 layers    | (0,0,0,0,3,3 | 3) | 0                         |
| Nmu  | [[mu,w],[cr]]          | (1,0,0,0,1,1 | 2) | [[w,cr],[cr,w],[w,mu]] | (1,0,0,0,2,3 | 3) | (0,0,0,0,+1,+2 | +1)     |
| Neta | [[eta,w],[cr]]         | (0,1,0,0,1,1 | 2) | [[w,eta]]             | (0,1,0,0,0,1 | 1) | (0,0,0,0,-1,0 | -1)       |
| Nd   | [[cr],[d,w]]           | (0,0,1,0,1,1 | 2) | [[w,d],[cr,w],[w,cr]] | (0,0,1,0,2,3 | 3) | (0,0,0,0,+1,+2 | +1)      |
| Neps | [[cr],[eps,w]]         | (0,0,0,1,1,1 | 2) | [[w,eps]]             | (0,0,0,1,0,1 | 1) | (0,0,0,0,-1,0 | -1)       |

Split instances (fired below): `[[mu]] ~ [[mu],[wire]]` gives (0,0,0,0,0,+1 | +1);
`[[mu,w]] ~ [[mu,w],[w,w]]` gives (0,0,0,0,0,+2 | +1).  `underLayerPrefix` adds the same
layer to both sides — every per-cell-weight functional is trivially conserved on it.

## THE JOINT KERNEL, BY HAND (family (a) of the commission, and its (b) extension)

Seek `(aMu, aEta, aDelta, aEps, aCross, aWire; cLayers)` with `a.delta + c*layerDelta = 0`
for EVERY edge instance.

1. narrow split:  aWire + c = 0.
2. wide split:    2*aWire + c = 0.        (1)-(2):  aWire = 0, hence c = 0.
   [Over Z2: (2) reads c = 0 directly, then (1) gives aWire = 0 — same conclusion.]
3. M4 at zero pads: -aCross - c = 0    => aCross = 0.   (C4/Neta/Neps identical;
   Nmu/Nd give +aCross + 2 aWire + c = 0, consistent; S1 gives -2 aCross - 2c = 0 which is
   VACUOUS mod 2 — aCross is pinned by M4, not by the involution.)
4. M2/M3: -aMu - aEta - aWire - 2c = 0  => aEta  = -aMu.
5. C2/C3: -aDelta - aEps - aWire - 2c = 0 => aEps = -aDelta.
6. B1:  aMu + aDelta + aCross + 2 aWire + c = 0  => aDelta = -aMu.
7. B2:  aEta - aDelta - c = 0   — consistent ((-aMu) - (-aMu) = 0).
8. B3: -aMu + aEps - c = 0      — consistent (aEps = -aDelta = aMu).
9. B4: -aEta - aEps - 2c = 0    — consistent (aMu - aMu = 0).
10. M1/C1/S2: zero deltas, vacuous.

JOINT KERNEL over Z:  exactly t * (1, -1, -1, +1, 0, 0; 0) — the EULER COUNT
`Phi = countMu - countEta - countDelta + countEps`.  Over Z2 the same elimination leaves
{0, (1,1,1,1,0,0;0)}, which IS `Phi mod 2` (since -1 = 1 mod 2): the Z2 refinement adds NO
new element.  Torsion: the delta lattice restricted to (mu,eta,delta,eps) is generated by
(0,1,-1,0) [B2], (-1,0,0,1) [B3], (1,1,0,0) [M2]; row reduction has unit pivots (Smith
invariants 1,1,1), so Z^4 / lattice = Z, TORSION-FREE — no hidden Z_k invariant factors
through the count vector either.  Any function of the count vector conserved by all edges
factors through Phi.

## WHY Phi CANNOT SEPARATE (the surviving element is boundary-determined)

Phi is the per-cell strand drop `srcArity - tgtArity` (wire 0, mu +1, eta -1, delta -1,
eps +1, crossing 0), summed.  For a COMPOSABLE-from-b list the per-layer sources telescope:
`Phi = b - targetArityFrom b layers` — pure boundary data, part of the denotation data the
canonical form is indexed by.  Machine-checked below in three stages: the conservation
theorem `lstConvertibleLayersConserveEulerCount` (Phi conserved over all 24 constructors —
this VALIDATES the whole table against the real congruence: a mis-transcribed window would
break the induction), the pinning theorem `lstEulerCountIsBoundaryPinned`
(`drop + target = raise + source` in subtraction-free Nat form), and the punchline
`lstEqualBoundaryDataPinsEulerBalance`: ANY two composable lists with the same source and
target boundaries — convertible or not — already balance.  Phi separates nothing the
boundary does not.

## THE KILLED CANDIDATE FAMILIES (each with a formal fire)

* (a) generator-count parities: the kernel above is complete for ALL linear functionals of
  the six cell counts, over Z and over Z2.  Individual axes die concretely:
  mu/eta (`sldRefutedUnitPairIsConvertible`, substrate: [[w,eta],[mu]] ~ [] flips both),
  eta/delta (`lstCopyAfterZeroWindowsConvert` + record: eta 1->2, delta 1->0 — kills
  eta-eps, eta+eps mod 2, eta alone), mu/eps (`lstDiscardAfterAddWindowsConvert` + record).
* (b) layer-count-weighted quantities: the two split fires change layers by +1 with zero
  generator deltas and wire deltas +1 resp. +2 — any `c*layers + aWire*wires` combination
  dies (`lstNarrowSplitGrowsWireAndLayerCounts` / `lstWideSplitGrowsWireCountByTwo`).
  Depth-weighted counts die on the same fires (the suffix shifts down one level while all
  its cells persist).
* (c) crossing parity vs permutation sign: crossing count changes by -1 on M4
  (`lstCommutativityWindowsConvert` + parity record via `lstIsOddCount`) — a crossing DIES
  against a mu, exactly the commissioned question; Neta/C4/Neps likewise, Nmu/Nd create one.
  Coxeter parity (equal-length-parity of transposition words of one permutation) survives
  only in the pure-crossing stratum: S1 removes TWO crossings, S2 preserves three-vs-three
  — but stratum MEMBERSHIP is itself not conserved
  (`lstGeneratorMaterialConvertsToPureCrossing`: a generator-bearing diagram converts to the
  bare crossing, both sides composable with EQUAL matrices, kernel-pinned record), so no
  "parity inside the stratum, constant outside" extension is conserved either: the M2-family
  edge carries an arbitrary suffix — here of odd crossing count — from generator-material to
  pure-crossing syntax.
* (d) eta/eps loop counts: `eta - eps` dies on B2 (delta +1 on eta, 0 on eps — see the
  record), `eta + eps` mod 2 dies on the same edge; the closed-loop row B4 changes the pair
  (-1,-1), so loop COUNT (min(eta,eps) in the closed fragment) is deliberately killable —
  Mat(N) cannot see closed loops and the presentation erases them (`B4` right window empty).
* (r3-analog) SYNTACTIC RESIDUE counts — the exact shape of the anomaly parity that refuted
  the old carrier (counting `id0`-tensor nodes).  The strict-layer analogs are "number of
  empty layers" and "number of pure-wire layers".  Both DIE, by derived conversions shipped
  here: `lstEmptyLayerDissolvesIntoNoSyntax` (`[[]] ~ []` at boundary 0: materialize an
  eta/eps ghost pair with the empty layer as suffix, absorb the empty layer into the eps
  layer by an inverse split, collapse the ghost pair by B4) and
  `lstWireLayerDissolvesIntoNoSyntax` (`[[wire]] ~ []` at boundary 1, same ghost-pair trick
  under a 1-wire pad).  Layer-count parity flips on the narrow split; empty-layer-count
  parity flips on the `X = Y = []` split instance ([[]] ~ [[],[]]).
* position-weighted sums (strands-above-cell weights and kin): M1 has ZERO count delta on
  every kind (see table) yet moves the top mu one strand down — any above-strand weighting
  changes by the weight difference on M1's own two sides, so none is conserved; no formal
  fire needed beyond the table row (equal counts) plus M1 being a congruence row.

## VERDICT: NO REFUTING INVARIANT FOUND — `fxLafontStrictLayer_invariantGateClean := true`

Every checked family is either not conserved (killed by a formal fire above) or conserved
but a function of the boundary data (Phi, layer-boundary telescope).  This is a CLEAN BILL
for the checked families — the complete linear analysis over the count lattice (Z, Z2, and
torsion), the fragment-conditional extensions, and the syntactic-residue analogs of every
historical defect in this arc.  It is NOT a completeness proof: the residual risk is
plumbing-completeness (whether splits + prefix + 18 rows generate ENOUGH conversions, the
[Lafont2003] staircase grind via [DelpeuchVicary2018] recumbent normalization), not a new
conserved quantity; [Lafont2003]/[Pirashvili2002]/[Zanasi2015] pin the true invariant
content of the bicommutative-bimonoid PROP at exactly the matrix.  Negative controls:
distinct-matrix pairs stay machine-separated (`lstWireLayerStaysApartFromDoubling`,
`lstEmptyListStaysApartFromCrossing`) — the dissolution fires did not collapse semantics.

Raw Lean 4 + Init only; zero-axiom; structural recursion only; audit twin with per-decl
`#assert_no_axioms` plus an independent `#print axioms` probe. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace FX1Poly.Polygraph.Omega.LafontProp

/-! ## Cell-kind weights and the count folds -/

/-- Weight 1 on the mu (add) generator, 0 elsewhere. -/
def lstMuWeight : SldCell -> Nat
  | SldCell.wire => 0
  | SldCell.generatorMu => 1
  | SldCell.generatorEta => 0
  | SldCell.generatorDelta => 0
  | SldCell.generatorEpsilon => 0
  | SldCell.crossing => 0

/-- Weight 1 on the eta (zero) generator, 0 elsewhere. -/
def lstEtaWeight : SldCell -> Nat
  | SldCell.wire => 0
  | SldCell.generatorMu => 0
  | SldCell.generatorEta => 1
  | SldCell.generatorDelta => 0
  | SldCell.generatorEpsilon => 0
  | SldCell.crossing => 0

/-- Weight 1 on the delta (copy) generator, 0 elsewhere. -/
def lstDeltaWeight : SldCell -> Nat
  | SldCell.wire => 0
  | SldCell.generatorMu => 0
  | SldCell.generatorEta => 0
  | SldCell.generatorDelta => 1
  | SldCell.generatorEpsilon => 0
  | SldCell.crossing => 0

/-- Weight 1 on the epsilon (discard) generator, 0 elsewhere. -/
def lstEpsilonWeight : SldCell -> Nat
  | SldCell.wire => 0
  | SldCell.generatorMu => 0
  | SldCell.generatorEta => 0
  | SldCell.generatorDelta => 0
  | SldCell.generatorEpsilon => 1
  | SldCell.crossing => 0

/-- Weight 1 on the crossing, 0 elsewhere. -/
def lstCrossingWeight : SldCell -> Nat
  | SldCell.wire => 0
  | SldCell.generatorMu => 0
  | SldCell.generatorEta => 0
  | SldCell.generatorDelta => 0
  | SldCell.generatorEpsilon => 0
  | SldCell.crossing => 1

/-- Weight 1 on the identity wire, 0 elsewhere. -/
def lstWireWeight : SldCell -> Nat
  | SldCell.wire => 1
  | SldCell.generatorMu => 0
  | SldCell.generatorEta => 0
  | SldCell.generatorDelta => 0
  | SldCell.generatorEpsilon => 0
  | SldCell.crossing => 0

/-- Weight 1 on the STRAND-DROPPING cells (source exceeds target: mu 2->1, epsilon 1->0). -/
def lstStrandDroppingWeight : SldCell -> Nat
  | SldCell.wire => 0
  | SldCell.generatorMu => 1
  | SldCell.generatorEta => 0
  | SldCell.generatorDelta => 0
  | SldCell.generatorEpsilon => 1
  | SldCell.crossing => 0

/-- Weight 1 on the STRAND-RAISING cells (target exceeds source: eta 0->1, delta 1->2). -/
def lstStrandRaisingWeight : SldCell -> Nat
  | SldCell.wire => 0
  | SldCell.generatorMu => 0
  | SldCell.generatorEta => 1
  | SldCell.generatorDelta => 1
  | SldCell.generatorEpsilon => 0
  | SldCell.crossing => 0

/-- Total weighted cell count of a layer list (cons-only fold over `sldLayerArityBy`). -/
def lstCountLayersBy (cellWeight : SldCell -> Nat) : List SldLayer -> Nat
  | [] => 0
  | headLayer :: tailLayers =>
      sldLayerArityBy cellWeight headLayer + lstCountLayersBy cellWeight tailLayers

/-- Number of layers in a list (cons-only length). -/
def lstCountLayers : List SldLayer -> Nat
  | [] => 0
  | _headLayer :: tailLayers => lstCountLayers tailLayers + 1

/-- Structural parity tester (no `Nat.mod`): is the count odd? -/
def lstIsOddCount : Nat -> Bool
  | 0 => false
  | countPred + 1 => not (lstIsOddCount countPred)

end FX1Poly.Polygraph.Omega.LafontProp

namespace FX1Poly.Polygraph.Omega.LafontProp

/-! ## Count plumbing: appends, wire layers, pad windows -/

/-- Weighted count distributes over layer-list append as a sum. -/
theorem lstCountLayersByOfAppendLayers (cellWeight : SldCell -> Nat) :
    (firstLayers secondLayers : List SldLayer) ->
    lstCountLayersBy cellWeight (sldAppendLayers firstLayers secondLayers)
      = lstCountLayersBy cellWeight firstLayers + lstCountLayersBy cellWeight secondLayers
  | [], secondLayers => (Nat.zero_add (lstCountLayersBy cellWeight secondLayers)).symm
  | headLayer :: tailLayers, secondLayers => by
      show sldLayerArityBy cellWeight headLayer
          + lstCountLayersBy cellWeight (sldAppendLayers tailLayers secondLayers)
        = (sldLayerArityBy cellWeight headLayer + lstCountLayersBy cellWeight tailLayers)
          + lstCountLayersBy cellWeight secondLayers
      rw [lstCountLayersByOfAppendLayers cellWeight tailLayers secondLayers]
      exact (Nat.add_assoc (sldLayerArityBy cellWeight headLayer)
        (lstCountLayersBy cellWeight tailLayers)
        (lstCountLayersBy cellWeight secondLayers)).symm

/-- A wire layer carries zero weighted cells for any wire-weightless weighting. -/
theorem lstWireLayerHasNoWeightedCells (cellWeight : SldCell -> Nat)
    (isWireWeightless : cellWeight SldCell.wire = 0) :
    (strandCount : Nat) -> sldLayerArityBy cellWeight (sldWireLayerOfArity strandCount) = 0
  | 0 => rfl
  | strandPred + 1 => by
      show cellWeight SldCell.wire
          + sldLayerArityBy cellWeight (sldWireLayerOfArity strandPred) = 0
      rw [isWireWeightless,
        lstWireLayerHasNoWeightedCells cellWeight isWireWeightless strandPred]

/-- Padding a layer with wires keeps its weighted count. -/
theorem lstPadLayerKeepsWeightedCount (cellWeight : SldCell -> Nat)
    (isWireWeightless : cellWeight SldCell.wire = 0)
    (padAboveCount padBelowCount : Nat) (windowLayer : SldLayer) :
    sldLayerArityBy cellWeight (sldPadLayer padAboveCount padBelowCount windowLayer)
      = sldLayerArityBy cellWeight windowLayer := by
  show sldLayerArityBy cellWeight (sldAppendCells (sldWireLayerOfArity padAboveCount)
      (sldAppendCells windowLayer (sldWireLayerOfArity padBelowCount)))
    = sldLayerArityBy cellWeight windowLayer
  rw [sldAppendCellsArityBy cellWeight (sldWireLayerOfArity padAboveCount)
      (sldAppendCells windowLayer (sldWireLayerOfArity padBelowCount)),
    sldAppendCellsArityBy cellWeight windowLayer (sldWireLayerOfArity padBelowCount),
    lstWireLayerHasNoWeightedCells cellWeight isWireWeightless padAboveCount,
    lstWireLayerHasNoWeightedCells cellWeight isWireWeightless padBelowCount,
    Nat.add_zero (sldLayerArityBy cellWeight windowLayer),
    Nat.zero_add (sldLayerArityBy cellWeight windowLayer)]

/-- Padding a whole window with wires keeps its weighted count. -/
theorem lstPadWindowKeepsWeightedCount (cellWeight : SldCell -> Nat)
    (isWireWeightless : cellWeight SldCell.wire = 0) (padAboveCount padBelowCount : Nat) :
    (windowLayers : List SldLayer) ->
    lstCountLayersBy cellWeight (sldPadWindow padAboveCount padBelowCount windowLayers)
      = lstCountLayersBy cellWeight windowLayers
  | [] => rfl
  | headLayer :: tailLayers => by
      show sldLayerArityBy cellWeight (sldPadLayer padAboveCount padBelowCount headLayer)
          + lstCountLayersBy cellWeight (sldPadWindow padAboveCount padBelowCount tailLayers)
        = sldLayerArityBy cellWeight headLayer + lstCountLayersBy cellWeight tailLayers
      rw [lstPadLayerKeepsWeightedCount cellWeight isWireWeightless padAboveCount
          padBelowCount headLayer,
        lstPadWindowKeepsWeightedCount cellWeight isWireWeightless padAboveCount
          padBelowCount tailLayers]

/-! ## Additive helpers (no order lemmas, no subtraction anywhere in this file) -/

/-- Four-summand exchange: `(a + x) + (b + y) = (a + b) + (x + y)`. -/
theorem lstAddFourExchange (firstLeft firstRight secondLeft secondRight : Nat) :
    (firstLeft + firstRight) + (secondLeft + secondRight)
      = (firstLeft + secondLeft) + (firstRight + secondRight) := by
  rw [Nat.add_assoc firstLeft firstRight (secondLeft + secondRight),
    (Nat.add_assoc firstRight secondLeft secondRight).symm,
    Nat.add_comm firstRight secondLeft,
    Nat.add_assoc secondLeft firstRight secondRight,
    (Nat.add_assoc firstLeft secondLeft (firstRight + secondRight)).symm]

/-- Right cancellation for Nat addition, hand-rolled on the structural recursion of
`Nat.add` (no order lemmas involved). -/
theorem lstAddRightCancel : (cancelCount : Nat) -> {firstNat secondNat : Nat} ->
    firstNat + cancelCount = secondNat + cancelCount -> firstNat = secondNat
  | 0, _, _, sumsEqual => sumsEqual
  | cancelPred + 1, _, _, sumsEqual =>
      lstAddRightCancel cancelPred (Nat.succ.inj sumsEqual)

/-! ## THE ROW-EFFECT TABLE, kernel-checked -/

/-- Does a window carry exactly the stated count vector
(mu, eta, delta, epsilon, crossing, wire, layers)? -/
def lstDoWindowCountsMatch (windowLayers : List SldLayer)
    (muCount etaCount deltaCount epsilonCount crossingCount wireCount layerCount : Nat) :
    Bool :=
  Nat.beq (lstCountLayersBy lstMuWeight windowLayers) muCount
    && Nat.beq (lstCountLayersBy lstEtaWeight windowLayers) etaCount
    && Nat.beq (lstCountLayersBy lstDeltaWeight windowLayers) deltaCount
    && Nat.beq (lstCountLayersBy lstEpsilonWeight windowLayers) epsilonCount
    && Nat.beq (lstCountLayersBy lstCrossingWeight windowLayers) crossingCount
    && Nat.beq (lstCountLayersBy lstWireWeight windowLayers) wireCount
    && Nat.beq (lstCountLayers windowLayers) layerCount

/-- The full 36-window count table backing the docstring joint-kernel analysis. -/
def lstDoesRowEffectTableHold : Bool :=
  lstDoWindowCountsMatch sldAddAssociativityLeftWindow 2 0 0 0 0 1 2
    && lstDoWindowCountsMatch sldAddAssociativityRightWindow 2 0 0 0 0 1 2
    && lstDoWindowCountsMatch sldAddLeftUnitLeftWindow 1 1 0 0 0 1 2
    && lstDoWindowCountsMatch sldAddLeftUnitRightWindow 0 0 0 0 0 0 0
    && lstDoWindowCountsMatch sldAddRightUnitLeftWindow 1 1 0 0 0 1 2
    && lstDoWindowCountsMatch sldAddRightUnitRightWindow 0 0 0 0 0 0 0
    && lstDoWindowCountsMatch sldAddCommutativityLeftWindow 1 0 0 0 1 0 2
    && lstDoWindowCountsMatch sldAddCommutativityRightWindow 1 0 0 0 0 0 1
    && lstDoWindowCountsMatch sldCopyCoassociativityLeftWindow 0 0 2 0 0 1 2
    && lstDoWindowCountsMatch sldCopyCoassociativityRightWindow 0 0 2 0 0 1 2
    && lstDoWindowCountsMatch sldCopyLeftCounitLeftWindow 0 0 1 1 0 1 2
    && lstDoWindowCountsMatch sldCopyLeftCounitRightWindow 0 0 0 0 0 0 0
    && lstDoWindowCountsMatch sldCopyRightCounitLeftWindow 0 0 1 1 0 1 2
    && lstDoWindowCountsMatch sldCopyRightCounitRightWindow 0 0 0 0 0 0 0
    && lstDoWindowCountsMatch sldCopyCocommutativityLeftWindow 0 0 1 0 1 0 2
    && lstDoWindowCountsMatch sldCopyCocommutativityRightWindow 0 0 1 0 0 0 1
    && lstDoWindowCountsMatch sldBimonoidSquareLeftWindow 1 0 1 0 0 0 2
    && lstDoWindowCountsMatch sldBimonoidSquareRightWindow 2 0 2 0 1 2 3
    && lstDoWindowCountsMatch sldCopyAfterZeroLeftWindow 0 1 1 0 0 0 2
    && lstDoWindowCountsMatch sldCopyAfterZeroRightWindow 0 2 0 0 0 0 1
    && lstDoWindowCountsMatch sldDiscardAfterAddLeftWindow 1 0 0 1 0 0 2
    && lstDoWindowCountsMatch sldDiscardAfterAddRightWindow 0 0 0 2 0 0 1
    && lstDoWindowCountsMatch sldDiscardAfterZeroLeftWindow 0 1 0 1 0 0 2
    && lstDoWindowCountsMatch sldDiscardAfterZeroRightWindow 0 0 0 0 0 0 0
    && lstDoWindowCountsMatch sldSwapInvolutionLeftWindow 0 0 0 0 2 0 2
    && lstDoWindowCountsMatch sldSwapInvolutionRightWindow 0 0 0 0 0 0 0
    && lstDoWindowCountsMatch sldSwapYangBaxterLeftWindow 0 0 0 0 3 3 3
    && lstDoWindowCountsMatch sldSwapYangBaxterRightWindow 0 0 0 0 3 3 3
    && lstDoWindowCountsMatch sldSwapPastAddLeftWindow 1 0 0 0 1 1 2
    && lstDoWindowCountsMatch sldSwapPastAddRightWindow 1 0 0 0 2 3 3
    && lstDoWindowCountsMatch sldSwapPastZeroLeftWindow 0 1 0 0 1 1 2
    && lstDoWindowCountsMatch sldSwapPastZeroRightWindow 0 1 0 0 0 1 1
    && lstDoWindowCountsMatch sldCopyPastSwapLeftWindow 0 0 1 0 1 1 2
    && lstDoWindowCountsMatch sldCopyPastSwapRightWindow 0 0 1 0 2 3 3
    && lstDoWindowCountsMatch sldDiscardPastSwapLeftWindow 0 0 0 1 1 1 2
    && lstDoWindowCountsMatch sldDiscardPastSwapRightWindow 0 0 0 1 0 1 1

/-- THE TABLE GATE (kernel `rfl`): all 36 window count vectors match the docstring table. -/
theorem lstRowEffectTableHolds : lstDoesRowEffectTableHold = true := rfl

/-! ## The surviving kernel element: conservation of the Euler count

`Phi = (mu + eps) - (eta + delta)`, stated subtraction-free as the cross-balance
`drop(L) + raise(R) = drop(R) + raise(L)`. -/

/-- Cross-balance form of `Phi(left) = Phi(right)` (subtraction-free). -/
abbrev lstDoEulerCountsBalance (leftLayers rightLayers : List SldLayer) : Prop :=
  lstCountLayersBy lstStrandDroppingWeight leftLayers
      + lstCountLayersBy lstStrandRaisingWeight rightLayers
    = lstCountLayersBy lstStrandDroppingWeight rightLayers
      + lstCountLayersBy lstStrandRaisingWeight leftLayers

/-- Equal counts on both axes give the balance. -/
theorem lstEulerBalanceOfCountsEqual {leftLayers rightLayers : List SldLayer}
    (doDroppingCountsMatch : lstCountLayersBy lstStrandDroppingWeight leftLayers
      = lstCountLayersBy lstStrandDroppingWeight rightLayers)
    (doRaisingCountsMatch : lstCountLayersBy lstStrandRaisingWeight leftLayers
      = lstCountLayersBy lstStrandRaisingWeight rightLayers) :
    lstDoEulerCountsBalance leftLayers rightLayers := by
  show lstCountLayersBy lstStrandDroppingWeight leftLayers
      + lstCountLayersBy lstStrandRaisingWeight rightLayers
    = lstCountLayersBy lstStrandDroppingWeight rightLayers
      + lstCountLayersBy lstStrandRaisingWeight leftLayers
  rw [doDroppingCountsMatch, doRaisingCountsMatch]

/-- Pure arithmetic of the transitivity case: two chained balances compose. -/
theorem lstBalanceChainArithmetic
    (dropLeft raiseLeft dropMiddle raiseMiddle dropRight raiseRight : Nat)
    (firstBalance : dropLeft + raiseMiddle = dropMiddle + raiseLeft)
    (secondBalance : dropMiddle + raiseRight = dropRight + raiseMiddle) :
    dropLeft + raiseRight = dropRight + raiseLeft := by
  have expandedChain : (dropLeft + raiseMiddle) + (dropMiddle + raiseRight)
      = (dropMiddle + raiseLeft) + (dropRight + raiseMiddle) := by
    rw [firstBalance, secondBalance]
  have leftReshuffled : (dropLeft + raiseMiddle) + (dropMiddle + raiseRight)
      = (dropLeft + raiseRight) + (dropMiddle + raiseMiddle) := by
    rw [lstAddFourExchange dropLeft raiseMiddle dropMiddle raiseRight,
      lstAddFourExchange dropLeft raiseRight dropMiddle raiseMiddle,
      Nat.add_comm raiseMiddle raiseRight]
  have rightReshuffled : (dropMiddle + raiseLeft) + (dropRight + raiseMiddle)
      = (dropRight + raiseLeft) + (dropMiddle + raiseMiddle) := by
    rw [lstAddFourExchange dropMiddle raiseLeft dropRight raiseMiddle,
      lstAddFourExchange dropRight raiseLeft dropMiddle raiseMiddle,
      Nat.add_comm dropMiddle dropRight]
  exact lstAddRightCancel (dropMiddle + raiseMiddle)
    (leftReshuffled.symm.trans (expandedChain.trans rightReshuffled))

/-- Pure arithmetic of the prefix case: a shared leading constant pair preserves balance. -/
theorem lstBalanceUnderAddedConstants (dropAdded raiseAdded : Nat)
    {dropLeft raiseLeft dropRight raiseRight : Nat}
    (innerBalance : dropLeft + raiseRight = dropRight + raiseLeft) :
    (dropAdded + dropLeft) + (raiseAdded + raiseRight)
      = (dropAdded + dropRight) + (raiseAdded + raiseLeft) := by
  rw [lstAddFourExchange dropAdded dropLeft raiseAdded raiseRight,
    lstAddFourExchange dropAdded dropRight raiseAdded raiseLeft,
    innerBalance]

/-- Pure arithmetic of the row case: a shared trailing suffix pair preserves balance. -/
theorem lstBalanceWithSharedSuffix (dropSuffix raiseSuffix : Nat)
    {dropLeftWindow raiseLeftWindow dropRightWindow raiseRightWindow : Nat}
    (windowBalance : dropLeftWindow + raiseRightWindow
      = dropRightWindow + raiseLeftWindow) :
    (dropLeftWindow + dropSuffix) + (raiseRightWindow + raiseSuffix)
      = (dropRightWindow + dropSuffix) + (raiseLeftWindow + raiseSuffix) := by
  rw [lstAddFourExchange dropLeftWindow dropSuffix raiseRightWindow raiseSuffix,
    lstAddFourExchange dropRightWindow dropSuffix raiseLeftWindow raiseSuffix,
    windowBalance]

/-- ONE ENGINE FOR ALL 18 ROW CASES: a balanced window pair stays balanced under any pad and
any shared suffix — the pads add only wires, the suffix is common. -/
theorem lstEulerBalanceAcrossPaddedRowEdge (leftWindow rightWindow : List SldLayer)
    (windowBalance : lstCountLayersBy lstStrandDroppingWeight leftWindow
        + lstCountLayersBy lstStrandRaisingWeight rightWindow
      = lstCountLayersBy lstStrandDroppingWeight rightWindow
        + lstCountLayersBy lstStrandRaisingWeight leftWindow)
    (padAboveCount padBelowCount : Nat) (suffixLayers : List SldLayer) :
    lstDoEulerCountsBalance
      (sldAppendLayers (sldPadWindow padAboveCount padBelowCount leftWindow) suffixLayers)
      (sldAppendLayers (sldPadWindow padAboveCount padBelowCount rightWindow) suffixLayers) := by
  show lstCountLayersBy lstStrandDroppingWeight
      (sldAppendLayers (sldPadWindow padAboveCount padBelowCount leftWindow) suffixLayers)
      + lstCountLayersBy lstStrandRaisingWeight
        (sldAppendLayers (sldPadWindow padAboveCount padBelowCount rightWindow) suffixLayers)
    = lstCountLayersBy lstStrandDroppingWeight
        (sldAppendLayers (sldPadWindow padAboveCount padBelowCount rightWindow) suffixLayers)
      + lstCountLayersBy lstStrandRaisingWeight
        (sldAppendLayers (sldPadWindow padAboveCount padBelowCount leftWindow) suffixLayers)
  rw [lstCountLayersByOfAppendLayers lstStrandDroppingWeight
      (sldPadWindow padAboveCount padBelowCount leftWindow) suffixLayers,
    lstCountLayersByOfAppendLayers lstStrandRaisingWeight
      (sldPadWindow padAboveCount padBelowCount rightWindow) suffixLayers,
    lstCountLayersByOfAppendLayers lstStrandDroppingWeight
      (sldPadWindow padAboveCount padBelowCount rightWindow) suffixLayers,
    lstCountLayersByOfAppendLayers lstStrandRaisingWeight
      (sldPadWindow padAboveCount padBelowCount leftWindow) suffixLayers,
    lstPadWindowKeepsWeightedCount lstStrandDroppingWeight rfl padAboveCount padBelowCount
      leftWindow,
    lstPadWindowKeepsWeightedCount lstStrandRaisingWeight rfl padAboveCount padBelowCount
      rightWindow,
    lstPadWindowKeepsWeightedCount lstStrandDroppingWeight rfl padAboveCount padBelowCount
      rightWindow,
    lstPadWindowKeepsWeightedCount lstStrandRaisingWeight rfl padAboveCount padBelowCount
      leftWindow]
  exact lstBalanceWithSharedSuffix (lstCountLayersBy lstStrandDroppingWeight suffixLayers)
    (lstCountLayersBy lstStrandRaisingWeight suffixLayers) windowBalance

/-- The top-acts-first split keeps every wire-weightless count (the two new part-layers carry
exactly the old cells plus wires). -/
theorem lstTopSplitKeepsWeightedCount (cellWeight : SldCell -> Nat)
    (isWireWeightless : cellWeight SldCell.wire = 0)
    (topCells bottomCells : SldLayer) (suffixLayers : List SldLayer) :
    lstCountLayersBy cellWeight
        (sldAppendCells topCells (sldWireLayerOfArity (sldLayerSourceArity bottomCells))
          :: sldAppendCells (sldWireLayerOfArity (sldLayerTargetArity topCells)) bottomCells
          :: suffixLayers)
      = lstCountLayersBy cellWeight (sldAppendCells topCells bottomCells :: suffixLayers) := by
  show sldLayerArityBy cellWeight
      (sldAppendCells topCells (sldWireLayerOfArity (sldLayerSourceArity bottomCells)))
      + (sldLayerArityBy cellWeight
          (sldAppendCells (sldWireLayerOfArity (sldLayerTargetArity topCells)) bottomCells)
        + lstCountLayersBy cellWeight suffixLayers)
    = sldLayerArityBy cellWeight (sldAppendCells topCells bottomCells)
      + lstCountLayersBy cellWeight suffixLayers
  rw [sldAppendCellsArityBy cellWeight topCells
      (sldWireLayerOfArity (sldLayerSourceArity bottomCells)),
    sldAppendCellsArityBy cellWeight (sldWireLayerOfArity (sldLayerTargetArity topCells))
      bottomCells,
    sldAppendCellsArityBy cellWeight topCells bottomCells,
    lstWireLayerHasNoWeightedCells cellWeight isWireWeightless
      (sldLayerSourceArity bottomCells),
    lstWireLayerHasNoWeightedCells cellWeight isWireWeightless
      (sldLayerTargetArity topCells),
    Nat.add_zero (sldLayerArityBy cellWeight topCells),
    Nat.zero_add (sldLayerArityBy cellWeight bottomCells),
    Nat.add_assoc (sldLayerArityBy cellWeight topCells)
      (sldLayerArityBy cellWeight bottomCells) (lstCountLayersBy cellWeight suffixLayers)]

/-- The bottom-acts-first split keeps every wire-weightless count. -/
theorem lstBottomSplitKeepsWeightedCount (cellWeight : SldCell -> Nat)
    (isWireWeightless : cellWeight SldCell.wire = 0)
    (topCells bottomCells : SldLayer) (suffixLayers : List SldLayer) :
    lstCountLayersBy cellWeight
        (sldAppendCells (sldWireLayerOfArity (sldLayerSourceArity topCells)) bottomCells
          :: sldAppendCells topCells (sldWireLayerOfArity (sldLayerTargetArity bottomCells))
          :: suffixLayers)
      = lstCountLayersBy cellWeight (sldAppendCells topCells bottomCells :: suffixLayers) := by
  show sldLayerArityBy cellWeight
      (sldAppendCells (sldWireLayerOfArity (sldLayerSourceArity topCells)) bottomCells)
      + (sldLayerArityBy cellWeight
          (sldAppendCells topCells (sldWireLayerOfArity (sldLayerTargetArity bottomCells)))
        + lstCountLayersBy cellWeight suffixLayers)
    = sldLayerArityBy cellWeight (sldAppendCells topCells bottomCells)
      + lstCountLayersBy cellWeight suffixLayers
  rw [sldAppendCellsArityBy cellWeight (sldWireLayerOfArity (sldLayerSourceArity topCells))
      bottomCells,
    sldAppendCellsArityBy cellWeight topCells
      (sldWireLayerOfArity (sldLayerTargetArity bottomCells)),
    sldAppendCellsArityBy cellWeight topCells bottomCells,
    lstWireLayerHasNoWeightedCells cellWeight isWireWeightless
      (sldLayerSourceArity topCells),
    lstWireLayerHasNoWeightedCells cellWeight isWireWeightless
      (sldLayerTargetArity bottomCells),
    Nat.zero_add (sldLayerArityBy cellWeight bottomCells),
    Nat.add_zero (sldLayerArityBy cellWeight topCells),
    (Nat.add_assoc (sldLayerArityBy cellWeight bottomCells)
      (sldLayerArityBy cellWeight topCells) (lstCountLayersBy cellWeight suffixLayers)).symm,
    Nat.add_comm (sldLayerArityBy cellWeight bottomCells)
      (sldLayerArityBy cellWeight topCells),
    Nat.add_assoc (sldLayerArityBy cellWeight topCells)
      (sldLayerArityBy cellWeight bottomCells) (lstCountLayersBy cellWeight suffixLayers)]

/-- THE CONSERVATION THEOREM: the Euler cross-balance holds across EVERY edge of the
24-constructor congruence — groupoid closure, layer prefix, both splits, all 18 padded rows.
This machine-validates the docstring's joint-kernel analysis against the real constructors:
the sole surviving linear functional of the cell counts is genuinely conserved. -/
theorem lstConvertibleLayersConserveEulerCount {boundaryArity : Nat}
    {leftLayers rightLayers : List SldLayer}
    (areConvertible : SldAreConvertibleLayers boundaryArity leftLayers rightLayers) :
    lstDoEulerCountsBalance leftLayers rightLayers := by
  induction areConvertible with
  | fromReflexivity _ _ => exact rfl
  | fromSymmetry _ flippedBalance => exact Eq.symm flippedBalance
  | fromTransitivity _ _ leftBalance rightBalance =>
      exact lstBalanceChainArithmetic _ _ _ _ _ _ leftBalance rightBalance
  | underLayerPrefix _ contextLayer _ tailBalance =>
      exact lstBalanceUnderAddedConstants
        (sldLayerArityBy lstStrandDroppingWeight contextLayer)
        (sldLayerArityBy lstStrandRaisingWeight contextLayer) tailBalance
  | layerSplitTopActsFirst topCells bottomCells suffixLayers =>
      exact lstEulerBalanceOfCountsEqual
        (Eq.symm (lstTopSplitKeepsWeightedCount lstStrandDroppingWeight rfl topCells
          bottomCells suffixLayers))
        (Eq.symm (lstTopSplitKeepsWeightedCount lstStrandRaisingWeight rfl topCells
          bottomCells suffixLayers))
  | layerSplitBottomActsFirst topCells bottomCells suffixLayers =>
      exact lstEulerBalanceOfCountsEqual
        (Eq.symm (lstBottomSplitKeepsWeightedCount lstStrandDroppingWeight rfl topCells
          bottomCells suffixLayers))
        (Eq.symm (lstBottomSplitKeepsWeightedCount lstStrandRaisingWeight rfl topCells
          bottomCells suffixLayers))
  | fromAddAssociativityRow padAboveCount padBelowCount suffixLayers =>
      exact lstEulerBalanceAcrossPaddedRowEdge sldAddAssociativityLeftWindow
        sldAddAssociativityRightWindow rfl padAboveCount padBelowCount suffixLayers
  | fromAddLeftUnitRow padAboveCount padBelowCount suffixLayers =>
      exact lstEulerBalanceAcrossPaddedRowEdge sldAddLeftUnitLeftWindow
        sldAddLeftUnitRightWindow rfl padAboveCount padBelowCount suffixLayers
  | fromAddRightUnitRow padAboveCount padBelowCount suffixLayers =>
      exact lstEulerBalanceAcrossPaddedRowEdge sldAddRightUnitLeftWindow
        sldAddRightUnitRightWindow rfl padAboveCount padBelowCount suffixLayers
  | fromAddCommutativityRow padAboveCount padBelowCount suffixLayers =>
      exact lstEulerBalanceAcrossPaddedRowEdge sldAddCommutativityLeftWindow
        sldAddCommutativityRightWindow rfl padAboveCount padBelowCount suffixLayers
  | fromCopyCoassociativityRow padAboveCount padBelowCount suffixLayers =>
      exact lstEulerBalanceAcrossPaddedRowEdge sldCopyCoassociativityLeftWindow
        sldCopyCoassociativityRightWindow rfl padAboveCount padBelowCount suffixLayers
  | fromCopyLeftCounitRow padAboveCount padBelowCount suffixLayers =>
      exact lstEulerBalanceAcrossPaddedRowEdge sldCopyLeftCounitLeftWindow
        sldCopyLeftCounitRightWindow rfl padAboveCount padBelowCount suffixLayers
  | fromCopyRightCounitRow padAboveCount padBelowCount suffixLayers =>
      exact lstEulerBalanceAcrossPaddedRowEdge sldCopyRightCounitLeftWindow
        sldCopyRightCounitRightWindow rfl padAboveCount padBelowCount suffixLayers
  | fromCopyCocommutativityRow padAboveCount padBelowCount suffixLayers =>
      exact lstEulerBalanceAcrossPaddedRowEdge sldCopyCocommutativityLeftWindow
        sldCopyCocommutativityRightWindow rfl padAboveCount padBelowCount suffixLayers
  | fromBimonoidSquareRow padAboveCount padBelowCount suffixLayers =>
      exact lstEulerBalanceAcrossPaddedRowEdge sldBimonoidSquareLeftWindow
        sldBimonoidSquareRightWindow rfl padAboveCount padBelowCount suffixLayers
  | fromCopyAfterZeroRow padAboveCount padBelowCount suffixLayers =>
      exact lstEulerBalanceAcrossPaddedRowEdge sldCopyAfterZeroLeftWindow
        sldCopyAfterZeroRightWindow rfl padAboveCount padBelowCount suffixLayers
  | fromDiscardAfterAddRow padAboveCount padBelowCount suffixLayers =>
      exact lstEulerBalanceAcrossPaddedRowEdge sldDiscardAfterAddLeftWindow
        sldDiscardAfterAddRightWindow rfl padAboveCount padBelowCount suffixLayers
  | fromDiscardAfterZeroRow padAboveCount padBelowCount suffixLayers =>
      exact lstEulerBalanceAcrossPaddedRowEdge sldDiscardAfterZeroLeftWindow
        sldDiscardAfterZeroRightWindow rfl padAboveCount padBelowCount suffixLayers
  | fromSwapInvolutionRow padAboveCount padBelowCount suffixLayers =>
      exact lstEulerBalanceAcrossPaddedRowEdge sldSwapInvolutionLeftWindow
        sldSwapInvolutionRightWindow rfl padAboveCount padBelowCount suffixLayers
  | fromSwapYangBaxterRow padAboveCount padBelowCount suffixLayers =>
      exact lstEulerBalanceAcrossPaddedRowEdge sldSwapYangBaxterLeftWindow
        sldSwapYangBaxterRightWindow rfl padAboveCount padBelowCount suffixLayers
  | fromSwapPastAddRow padAboveCount padBelowCount suffixLayers =>
      exact lstEulerBalanceAcrossPaddedRowEdge sldSwapPastAddLeftWindow
        sldSwapPastAddRightWindow rfl padAboveCount padBelowCount suffixLayers
  | fromSwapPastZeroRow padAboveCount padBelowCount suffixLayers =>
      exact lstEulerBalanceAcrossPaddedRowEdge sldSwapPastZeroLeftWindow
        sldSwapPastZeroRightWindow rfl padAboveCount padBelowCount suffixLayers
  | fromCopyPastSwapRow padAboveCount padBelowCount suffixLayers =>
      exact lstEulerBalanceAcrossPaddedRowEdge sldCopyPastSwapLeftWindow
        sldCopyPastSwapRightWindow rfl padAboveCount padBelowCount suffixLayers
  | fromDiscardPastSwapRow padAboveCount padBelowCount suffixLayers =>
      exact lstEulerBalanceAcrossPaddedRowEdge sldDiscardPastSwapLeftWindow
        sldDiscardPastSwapRightWindow rfl padAboveCount padBelowCount suffixLayers

/-! ## The surviving element is boundary data: the telescope -/

/-- Per-cell Euler relation: `drop + target = raise + source` (all six cells, kernel). -/
theorem lstCellArityBalance : (cell : SldCell) ->
    lstStrandDroppingWeight cell + sldCellTargetArity cell
      = lstStrandRaisingWeight cell + sldCellSourceArity cell
  | SldCell.wire => rfl
  | SldCell.generatorMu => rfl
  | SldCell.generatorEta => rfl
  | SldCell.generatorDelta => rfl
  | SldCell.generatorEpsilon => rfl
  | SldCell.crossing => rfl

/-- Per-layer Euler relation, summed from the cells. -/
theorem lstLayerArityBalance : (layer : SldLayer) ->
    sldLayerArityBy lstStrandDroppingWeight layer + sldLayerTargetArity layer
      = sldLayerArityBy lstStrandRaisingWeight layer + sldLayerSourceArity layer
  | [] => rfl
  | headCell :: tailCells => by
      show (lstStrandDroppingWeight headCell
            + sldLayerArityBy lstStrandDroppingWeight tailCells)
          + (sldCellTargetArity headCell + sldLayerTargetArity tailCells)
        = (lstStrandRaisingWeight headCell
            + sldLayerArityBy lstStrandRaisingWeight tailCells)
          + (sldCellSourceArity headCell + sldLayerSourceArity tailCells)
      rw [lstAddFourExchange (lstStrandDroppingWeight headCell)
          (sldLayerArityBy lstStrandDroppingWeight tailCells)
          (sldCellTargetArity headCell) (sldLayerTargetArity tailCells),
        lstAddFourExchange (lstStrandRaisingWeight headCell)
          (sldLayerArityBy lstStrandRaisingWeight tailCells)
          (sldCellSourceArity headCell) (sldLayerSourceArity tailCells),
        lstCellArityBalance headCell, lstLayerArityBalance tailCells]

/-- THE TELESCOPE: on a composable-from-b list, `drop + target = raise + b` — the Euler
count is the boundary drop `b - target`, i.e. pure denotation data. -/
theorem lstEulerCountIsBoundaryPinned : (layers : List SldLayer) -> (boundaryArity : Nat) ->
    sldLayersAreComposableFrom boundaryArity layers = true ->
    lstCountLayersBy lstStrandDroppingWeight layers
        + sldLayersTargetArityFrom boundaryArity layers
      = lstCountLayersBy lstStrandRaisingWeight layers + boundaryArity
  | [], _, _ => rfl
  | headLayer :: tailLayers, boundaryArity, isChainComposable => by
      have doesHeadMatch : sldLayerSourceArity headLayer = boundaryArity :=
        eqOfBeqIsTrue (leftIsTrueOfAndTrue isChainComposable)
      have doesTailCompose := rightIsTrueOfAndTrue isChainComposable
      have tailPinned := lstEulerCountIsBoundaryPinned tailLayers
        (sldLayerTargetArity headLayer) doesTailCompose
      show (sldLayerArityBy lstStrandDroppingWeight headLayer
            + lstCountLayersBy lstStrandDroppingWeight tailLayers)
          + sldLayersTargetArityFrom (sldLayerTargetArity headLayer) tailLayers
        = (sldLayerArityBy lstStrandRaisingWeight headLayer
            + lstCountLayersBy lstStrandRaisingWeight tailLayers)
          + boundaryArity
      rw [Nat.add_assoc (sldLayerArityBy lstStrandDroppingWeight headLayer)
          (lstCountLayersBy lstStrandDroppingWeight tailLayers)
          (sldLayersTargetArityFrom (sldLayerTargetArity headLayer) tailLayers),
        tailPinned,
        Nat.add_comm (lstCountLayersBy lstStrandRaisingWeight tailLayers)
          (sldLayerTargetArity headLayer),
        (Nat.add_assoc (sldLayerArityBy lstStrandDroppingWeight headLayer)
          (sldLayerTargetArity headLayer)
          (lstCountLayersBy lstStrandRaisingWeight tailLayers)).symm,
        lstLayerArityBalance headLayer, doesHeadMatch,
        Nat.add_assoc (sldLayerArityBy lstStrandRaisingWeight headLayer) boundaryArity
          (lstCountLayersBy lstStrandRaisingWeight tailLayers),
        Nat.add_comm boundaryArity (lstCountLayersBy lstStrandRaisingWeight tailLayers),
        (Nat.add_assoc (sldLayerArityBy lstStrandRaisingWeight headLayer)
          (lstCountLayersBy lstStrandRaisingWeight tailLayers) boundaryArity).symm]

/-- Pure arithmetic: two boundary-pinned lists at shared boundaries balance. -/
theorem lstPinnedPairBalancesArithmetic
    (dropLeft raiseLeft dropRight raiseRight sharedTarget sharedBoundary : Nat)
    (leftPinned : dropLeft + sharedTarget = raiseLeft + sharedBoundary)
    (rightPinned : dropRight + sharedTarget = raiseRight + sharedBoundary) :
    dropLeft + raiseRight = dropRight + raiseLeft := by
  have expandedEquation : (dropLeft + raiseRight) + (sharedTarget + sharedBoundary)
      = (dropRight + raiseLeft) + (sharedTarget + sharedBoundary) := by
    rw [lstAddFourExchange dropLeft raiseRight sharedTarget sharedBoundary,
      lstAddFourExchange dropRight raiseLeft sharedTarget sharedBoundary,
      leftPinned, rightPinned]
    exact Nat.add_comm (raiseLeft + sharedBoundary) (raiseRight + sharedBoundary)
  exact lstAddRightCancel (sharedTarget + sharedBoundary) expandedEquation

/-- THE NO-SEPARATION-POWER COROLLARY: any two composable lists sharing source AND target
boundaries already balance — NO CONVERTIBILITY NEEDED.  The unique surviving invariant of
the joint kernel is a function of the boundary data every equal-denotation pair shares, so
it can refute nothing. -/
theorem lstEqualBoundaryDataPinsEulerBalance {boundaryArity : Nat}
    (leftLayers rightLayers : List SldLayer)
    (isLeftComposable : sldLayersAreComposableFrom boundaryArity leftLayers = true)
    (isRightComposable : sldLayersAreComposableFrom boundaryArity rightLayers = true)
    (doTargetsMatch : sldLayersTargetArityFrom boundaryArity leftLayers
      = sldLayersTargetArityFrom boundaryArity rightLayers) :
    lstDoEulerCountsBalance leftLayers rightLayers := by
  have leftPinned := lstEulerCountIsBoundaryPinned leftLayers boundaryArity isLeftComposable
  have rightPinned := lstEulerCountIsBoundaryPinned rightLayers boundaryArity
    isRightComposable
  rw [doTargetsMatch] at leftPinned
  exact lstPinnedPairBalancesArithmetic _ _ _ _ _ _ leftPinned rightPinned

/-! ## Kill-fires: each excluded axis dies on a concrete convertible edge -/

/-- FIRE (family c): the M4 window pair converts — one crossing dies against a mu. -/
theorem lstCommutativityWindowsConvert :
    SldAreConvertibleLayers 2 sldAddCommutativityLeftWindow
      sldAddCommutativityRightWindow := by
  have rowInstance := SldAreConvertibleLayers.fromAddCommutativityRow 0 0 []
  rw [sldPadWindowZeroIsSelf sldAddCommutativityLeftWindow,
    sldPadWindowZeroIsSelf sldAddCommutativityRightWindow,
    sldAppendLayersNilRightIsSelf sldAddCommutativityLeftWindow,
    sldAppendLayersNilRightIsSelf sldAddCommutativityRightWindow] at rowInstance
  exact rowInstance

/-- Record (family c): crossing counts 1 vs 0 across the M4 fire — crossing count AND its
parity change on a convertible (hence equal-matrix) pair. -/
theorem lstCrossingCountsAcrossCommutativityFire :
    lstCountLayersBy lstCrossingWeight sldAddCommutativityLeftWindow = 1
      ∧ lstCountLayersBy lstCrossingWeight sldAddCommutativityRightWindow = 0 :=
  ⟨rfl, rfl⟩

/-- Record (family c), parity form via the structural odd tester. -/
theorem lstCrossingParityFlipsAcrossCommutativityFire :
    lstIsOddCount (lstCountLayersBy lstCrossingWeight sldAddCommutativityLeftWindow) = true
      ∧ lstIsOddCount (lstCountLayersBy lstCrossingWeight sldAddCommutativityRightWindow)
          = false :=
  ⟨rfl, rfl⟩

/-- Genuineness pin: the M4 fire's two sides denote the SAME matrix on the 1x2 rectangle. -/
theorem lstCommutativityFireSidesDenoteEqually :
    doEntriesAgreeUpTo 1 2 (sldLayersDenote sldAddCommutativityLeftWindow)
      (sldLayersDenote sldAddCommutativityRightWindow) = true := rfl

/-- FIRE (family d): the B2 window pair converts. -/
theorem lstCopyAfterZeroWindowsConvert :
    SldAreConvertibleLayers 0 sldCopyAfterZeroLeftWindow sldCopyAfterZeroRightWindow := by
  have rowInstance := SldAreConvertibleLayers.fromCopyAfterZeroRow 0 0 []
  rw [sldPadWindowZeroIsSelf sldCopyAfterZeroLeftWindow,
    sldPadWindowZeroIsSelf sldCopyAfterZeroRightWindow,
    sldAppendLayersNilRightIsSelf sldCopyAfterZeroLeftWindow,
    sldAppendLayersNilRightIsSelf sldCopyAfterZeroRightWindow] at rowInstance
  exact rowInstance

/-- Record (family d): across B2, eta goes 1 -> 2 while epsilon stays 0 -> 0 — the loop
difference `eta - eps`, the sum `eta + eps` mod 2, and the bare eta count all change on a
convertible pair; delta simultaneously drops 1 -> 0. -/
theorem lstEtaDeltaEpsilonCountsAcrossCopyAfterZeroFire :
    (lstCountLayersBy lstEtaWeight sldCopyAfterZeroLeftWindow = 1
      ∧ lstCountLayersBy lstEtaWeight sldCopyAfterZeroRightWindow = 2)
    ∧ (lstCountLayersBy lstDeltaWeight sldCopyAfterZeroLeftWindow = 1
      ∧ lstCountLayersBy lstDeltaWeight sldCopyAfterZeroRightWindow = 0)
    ∧ (lstCountLayersBy lstEpsilonWeight sldCopyAfterZeroLeftWindow = 0
      ∧ lstCountLayersBy lstEpsilonWeight sldCopyAfterZeroRightWindow = 0) :=
  ⟨⟨rfl, rfl⟩, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩⟩

/-- FIRE (families a/d): the B3 window pair converts — mu 1 -> 0, epsilon 1 -> 2. -/
theorem lstDiscardAfterAddWindowsConvert :
    SldAreConvertibleLayers 2 sldDiscardAfterAddLeftWindow
      sldDiscardAfterAddRightWindow := by
  have rowInstance := SldAreConvertibleLayers.fromDiscardAfterAddRow 0 0 []
  rw [sldPadWindowZeroIsSelf sldDiscardAfterAddLeftWindow,
    sldPadWindowZeroIsSelf sldDiscardAfterAddRightWindow,
    sldAppendLayersNilRightIsSelf sldDiscardAfterAddLeftWindow,
    sldAppendLayersNilRightIsSelf sldDiscardAfterAddRightWindow] at rowInstance
  exact rowInstance

/-- Record for the B3 fire. -/
theorem lstMuEpsilonCountsAcrossDiscardAfterAddFire :
    (lstCountLayersBy lstMuWeight sldDiscardAfterAddLeftWindow = 1
      ∧ lstCountLayersBy lstMuWeight sldDiscardAfterAddRightWindow = 0)
    ∧ (lstCountLayersBy lstEpsilonWeight sldDiscardAfterAddLeftWindow = 1
      ∧ lstCountLayersBy lstEpsilonWeight sldDiscardAfterAddRightWindow = 2) :=
  ⟨⟨rfl, rfl⟩, ⟨rfl, rfl⟩⟩

/-- FIRE (family b): the narrow split — one wire and one layer appear from nothing. -/
theorem lstNarrowSplitGrowsWireAndLayerCounts :
    SldAreConvertibleLayers 2 [[SldCell.generatorMu]]
      [[SldCell.generatorMu], [SldCell.wire]] :=
  SldAreConvertibleLayers.layerSplitTopActsFirst [SldCell.generatorMu] [] []

/-- FIRE (family b): the wide split — TWO wires and one layer appear.  Together with the
narrow split this kills every `aWire*wires + c*layers` functional over Z and over Z2. -/
theorem lstWideSplitGrowsWireCountByTwo :
    SldAreConvertibleLayers 3 [[SldCell.generatorMu, SldCell.wire]]
      [[SldCell.generatorMu, SldCell.wire], [SldCell.wire, SldCell.wire]] :=
  SldAreConvertibleLayers.layerSplitTopActsFirst [SldCell.generatorMu] [SldCell.wire] []

/-- Record (family b): wire and layer counts across the two split fires. -/
theorem lstWireAndLayerCountsAcrossSplitFires :
    (lstCountLayersBy lstWireWeight [[SldCell.generatorMu]] = 0
      ∧ lstCountLayersBy lstWireWeight [[SldCell.generatorMu], [SldCell.wire]] = 1
      ∧ lstCountLayersBy lstWireWeight [[SldCell.generatorMu, SldCell.wire]] = 1
      ∧ lstCountLayersBy lstWireWeight
          [[SldCell.generatorMu, SldCell.wire], [SldCell.wire, SldCell.wire]] = 3)
    ∧ (lstCountLayers [[SldCell.generatorMu]] = 1
      ∧ lstCountLayers [[SldCell.generatorMu], [SldCell.wire]] = 2
      ∧ lstCountLayers [[SldCell.generatorMu, SldCell.wire]] = 1
      ∧ lstCountLayers
          [[SldCell.generatorMu, SldCell.wire], [SldCell.wire, SldCell.wire]] = 2) :=
  ⟨⟨rfl, rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl, rfl⟩⟩

/-- FIRE (family c, stratum membership): a generator-bearing diagram converts to the BARE
crossing — the M3-family row fired at pad (1,0) with the crossing as suffix.  Purity
(generator-freeness) is not conserved, so no "Coxeter parity inside the pure stratum,
constant outside" invariant survives: this edge enters the stratum carrying ODD crossing
count. -/
theorem lstGeneratorMaterialConvertsToPureCrossing :
    SldAreConvertibleLayers 2
      [[SldCell.wire, SldCell.generatorEta, SldCell.wire],
        [SldCell.wire, SldCell.generatorMu], [SldCell.crossing]]
      [[SldCell.crossing]] :=
  SldAreConvertibleLayers.fromAddLeftUnitRow 1 0 [[SldCell.crossing]]

/-- Genuineness pin for the purity fire: both sides composable from boundary 2, equal
matrices on the full 2x2 rectangle, generator counts (mu 1, eta 1) -> (0, 0), crossing
count 1 on BOTH sides (odd — the stratum is entered at odd parity). -/
theorem lstPurityFireRecord :
    (sldLayersAreComposableFrom 2
        [[SldCell.wire, SldCell.generatorEta, SldCell.wire],
          [SldCell.wire, SldCell.generatorMu], [SldCell.crossing]]
      && sldLayersAreComposableFrom 2 [[SldCell.crossing]]
      && doEntriesAgreeUpTo 2 2
          (sldLayersDenote
            [[SldCell.wire, SldCell.generatorEta, SldCell.wire],
              [SldCell.wire, SldCell.generatorMu], [SldCell.crossing]])
          (sldLayersDenote [[SldCell.crossing]])
      && Nat.beq (lstCountLayersBy lstMuWeight
          [[SldCell.wire, SldCell.generatorEta, SldCell.wire],
            [SldCell.wire, SldCell.generatorMu], [SldCell.crossing]]) 1
      && Nat.beq (lstCountLayersBy lstCrossingWeight
          [[SldCell.wire, SldCell.generatorEta, SldCell.wire],
            [SldCell.wire, SldCell.generatorMu], [SldCell.crossing]]) 1
      && Nat.beq (lstCountLayersBy lstCrossingWeight [[SldCell.crossing]]) 1) = true := rfl

/-! ## The r3-analog kill: syntactic residues dissolve

The old carrier fell to a parity of `id0`-tensor SYNTAX nodes.  The strict-layer analogs are
empty layers and pure-wire layers — identity residue the matrix cannot see.  Both dissolve
by DERIVED conversions: materialize an eta/eps ghost pair (B4 backward) with the residue as
suffix, absorb the residue into the epsilon layer by an inverse split (a wire block equal to
the previous layer's target boundary IS the split's wire remainder), collapse the ghost pair
(B4 forward). -/

/-- FIRE (r3-analog): the one-empty-layer diagram converts to the EMPTY diagram at
boundary 0 — empty-layer count is NOT conserved, no residue invariant survives. -/
theorem lstEmptyLayerDissolvesIntoNoSyntax :
    SldAreConvertibleLayers 0 [([] : SldLayer)] [] := by
  have materializeGhostPair : SldAreConvertibleLayers 0
      [[SldCell.generatorEta], [SldCell.generatorEpsilon], ([] : SldLayer)]
      [([] : SldLayer)] :=
    SldAreConvertibleLayers.fromDiscardAfterZeroRow 0 0 [([] : SldLayer)]
  have emptyLayerEntersEpsilon : SldAreConvertibleLayers 1
      [[SldCell.generatorEpsilon]] [[SldCell.generatorEpsilon], ([] : SldLayer)] :=
    SldAreConvertibleLayers.layerSplitTopActsFirst [SldCell.generatorEpsilon] [] []
  have trailingEmptyLayerDies : SldAreConvertibleLayers 0
      [[SldCell.generatorEta], [SldCell.generatorEpsilon], ([] : SldLayer)]
      [[SldCell.generatorEta], [SldCell.generatorEpsilon]] :=
    SldAreConvertibleLayers.underLayerPrefix 0 [SldCell.generatorEta]
      (SldAreConvertibleLayers.fromSymmetry emptyLayerEntersEpsilon)
  have ghostPairCollapses : SldAreConvertibleLayers 0
      [[SldCell.generatorEta], [SldCell.generatorEpsilon]] [] :=
    SldAreConvertibleLayers.fromDiscardAfterZeroRow 0 0 []
  exact SldAreConvertibleLayers.fromTransitivity
    (SldAreConvertibleLayers.fromSymmetry materializeGhostPair)
    (SldAreConvertibleLayers.fromTransitivity trailingEmptyLayerDies ghostPairCollapses)

/-- FIRE (r3-analog): the one-wire-layer diagram converts to the EMPTY diagram at
boundary 1 — pure-wire-layer count is NOT conserved either. -/
theorem lstWireLayerDissolvesIntoNoSyntax :
    SldAreConvertibleLayers 1 [[SldCell.wire]] [] := by
  have materializeGhostPair : SldAreConvertibleLayers 1
      [[SldCell.wire, SldCell.generatorEta], [SldCell.wire, SldCell.generatorEpsilon],
        [SldCell.wire]]
      [[SldCell.wire]] :=
    SldAreConvertibleLayers.fromDiscardAfterZeroRow 1 0 [[SldCell.wire]]
  have wireLayerEntersEpsilon : SldAreConvertibleLayers 2
      [[SldCell.wire, SldCell.generatorEpsilon]]
      [[SldCell.wire, SldCell.generatorEpsilon], [SldCell.wire]] :=
    SldAreConvertibleLayers.layerSplitTopActsFirst
      [SldCell.wire, SldCell.generatorEpsilon] [] []
  have trailingWireLayerDies : SldAreConvertibleLayers 1
      [[SldCell.wire, SldCell.generatorEta], [SldCell.wire, SldCell.generatorEpsilon],
        [SldCell.wire]]
      [[SldCell.wire, SldCell.generatorEta], [SldCell.wire, SldCell.generatorEpsilon]] :=
    SldAreConvertibleLayers.underLayerPrefix 1 [SldCell.wire, SldCell.generatorEta]
      (SldAreConvertibleLayers.fromSymmetry wireLayerEntersEpsilon)
  have ghostPairCollapses : SldAreConvertibleLayers 1
      [[SldCell.wire, SldCell.generatorEta], [SldCell.wire, SldCell.generatorEpsilon]]
      [] :=
    SldAreConvertibleLayers.fromDiscardAfterZeroRow 1 0 []
  exact SldAreConvertibleLayers.fromTransitivity
    (SldAreConvertibleLayers.fromSymmetry materializeGhostPair)
    (SldAreConvertibleLayers.fromTransitivity trailingWireLayerDies ghostPairCollapses)

/-- Record (r3-analog): the dissolution fires change layer count 1 -> 0 and, for the second,
wire count 1 -> 0 — and both endpoints are composable with vacuously equal denotation data
(the identity boundary walk). -/
theorem lstDissolutionFireRecord :
    (sldLayersAreComposableFrom 0 [([] : SldLayer)]
      && sldLayersAreComposableFrom 0 []
      && sldLayersAreComposableFrom 1 [[SldCell.wire]]
      && sldLayersAreComposableFrom 1 []
      && Nat.beq (lstCountLayers [([] : SldLayer)]) 1
      && Nat.beq (lstCountLayers ([] : List SldLayer)) 0
      && Nat.beq (lstCountLayersBy lstWireWeight [[SldCell.wire]]) 1
      && Nat.beq (sldLayersTargetArityFrom 1 [[SldCell.wire]]) 1
      && Nat.beq (sldLayersTargetArityFrom 1 []) 1) = true := rfl

/-! ## Negative controls: the dissolution machinery does NOT collapse semantics -/

/-- Negative control 1: the wire layer stays separated from the doubling composite
`delta ; mu` (denotations 1 vs 2 at entry (0,0)). -/
theorem lstWireLayerStaysApartFromDoubling :
    SldAreConvertibleLayers 1 [[SldCell.wire]]
      [[SldCell.generatorDelta], [SldCell.generatorMu]] -> False :=
  sldNotConvertibleOfDistinctDenotes [[SldCell.wire]]
    [[SldCell.generatorDelta], [SldCell.generatorMu]] 1 rfl

/-- Negative control 2: the empty diagram at boundary 2 stays separated from the bare
crossing (identity vs swap at entry (0,0)). -/
theorem lstEmptyListStaysApartFromCrossing :
    SldAreConvertibleLayers 2 [] [[SldCell.crossing]] -> False :=
  sldNotConvertibleOfDistinctDenotes [] [[SldCell.crossing]] 1 rfl

/-! ## THE MARKER -/

/-- PHASE-1 GATE VERDICT: NO invariant of the 24-constructor congruence separating
equal-denotation composable diagrams was found.  The complete linear kernel over the cell
counts (Z, Z2, torsion-free) is spanned by the Euler count, which
`lstEqualBoundaryDataPinsEulerBalance` shows is pinned by the shared boundary data alone;
every commissioned candidate family — generator parities, layer/wire weights, crossing
parity vs permutation sign, eta/eps loop counts, and the r3-analog syntactic residues —
dies on a formal fire in this file.  CLEAN BILL for the checked families: the completeness
push may proceed; the residual risk is move-plumbing completeness, not a conserved
quantity.  (`fxLafontStrictLayer_hasCanonicalCompleteness` stays false — this gate proves
no completeness.) -/
def fxLafontStrictLayer_invariantGateClean : Bool := true

#eval decide (lstDoesRowEffectTableHold = true)
#eval decide (lstIsOddCount
  (lstCountLayersBy lstCrossingWeight sldAddCommutativityLeftWindow) = true)
#eval decide (lstIsOddCount
  (lstCountLayersBy lstCrossingWeight sldAddCommutativityRightWindow) = false)
#eval decide (doEntriesAgreeUpTo 1 2 (sldLayersDenote sldAddCommutativityLeftWindow)
  (sldLayersDenote sldAddCommutativityRightWindow) = true)
#eval decide (doEntriesAgreeUpTo 1 1 (sldLayersDenote [[SldCell.wire]])
  (sldLayersDenote [[SldCell.generatorDelta], [SldCell.generatorMu]]) = false)
#eval decide (doEntriesAgreeUpTo 1 2 (sldLayersDenote ([] : List SldLayer))
  (sldLayersDenote [[SldCell.crossing]]) = false)
#eval decide (sldLayersAreComposableFrom 0 [([] : SldLayer)] = true)
#eval decide (sldLayersAreComposableFrom 1 [[SldCell.wire]] = true)
#eval decide ((lstCountLayersBy lstStrandDroppingWeight sldBimonoidSquareRightWindow
  + lstCountLayersBy lstStrandRaisingWeight sldBimonoidSquareLeftWindow)
  = (lstCountLayersBy lstStrandDroppingWeight sldBimonoidSquareLeftWindow
    + lstCountLayersBy lstStrandRaisingWeight sldBimonoidSquareRightWindow))

end FX1Poly.Polygraph.Omega.LafontProp
