import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescFoldTargetHonest
import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescBoundaryPartneredFold
import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescWellFormedFoldWidth

/-! # BRAUER r22 — the T-CONNECT routing collapse + the per-arc-class connectivity probes

The r5 ledger named **T-CONNECT** verbatim (`Brauer/WiringDescStandardFoldR5Ledger.lean:35`): *for every arc
`(i, j)` of `d`, the six-phase fold state has `matchingSameComponent … i j = true`*.  r11/r12 shipped the
partner READ-OFF (`partnerIndexOf_reads_matchingPartner` over any T-DISJOINT state) and the partner-totality FOLD
(`partnerIndexOf_readsPartner_reachable`).  r21 shipped the connectivity-free half — the GENERAL corrected-word
`WellFormedBrauerFold` (`wellFormedBrauerFold_correctedWord_general`).  This file assembles those into the
**routing collapse** and probes the arc-class connectivity that feeds it.

## The routing collapse (the headline — GENERAL, machine-checked)

`partnerIndexOf_reads_arc_general` shows the entire six-phase endgame reduces to ONE datum: for EVERY well-formed
boundary involution `d`, and for any boundary pair `(probeIndex, partnerIndex)` that is same-component in the
corrected-word fold state `F` (`partnerShares : matchingSameComponent d.bottomCount F probeIndex partnerIndex =
true`), the extractor's partner map reads exactly that partner: `partnerIndexOf F.links … probeIndex =
partnerIndex`.  The proof chains the r21 general well-formedness → the r10 T-DISJOINT fold
(`boundedBoundaryComponents_reachable`) → the r11 uniqueness read-off (`partnerIndexOf_reads_matchingPartner`).
So `partnerShares` — the per-arc `matchingSameComponent` fact — is the SOLE remaining input to close
`extractDiagram F = d` at every slot.  `partnerShares` IS T-CONNECT.

## The bottom–bottom reduction (the cap-arc join-site fact — GENERAL)

`matchingSameComponent_bottomBottom_eq_isSameComponent` records that for a CAP arc `(i, j)` — both feet bottom
ports, `i, j < bottomCount` — the boundary matching goal is literally node connectivity `isSameComponent
state.links i j` (each boundary read of a bottom index is the seed node itself,
`matchingBoundaryNodes_getAt_bottom`).  This is the join-site reduction the cap-class T-CONNECT rests on: the
recon's cap chain `i ~ openWire[2k] ~ openWire[2k+1] ~ partner[i]` lands, after transport to `F`, exactly as an
`isSameComponent F.links i partner[i]` obligation.

## Per-arc-class connectivity — probed by evaluation (the r18 discipline, eval FIRST)

The per-class connectivity is TRUE on the wild witnesses (kernel-decided):

  * **CAP** (both feet bottom): all-caps `{4,0,[3,2,1,0]}` — arcs `(0,3)`, `(1,2)` both same-component in `F`;
    triple-axis adversarial-B `{3,3,[2,4,0,5,1,3],1}` — the cap `0↔2` same-component.
  * **THROUGH** (one bottom, one top): adversarial-B `1↔top1` (index `4`) same-component.
  * **CUP** (both top): adversarial-B `top0↔top2` (indices `3,5`) same-component.
  * **LOOP**: adversarial-B carries `loops := 1` — the circle `[cupAt 0, capAt 0]` block adds a fresh joined pair
    then closes it, leaving the boundary matching untouched (the connectivity probe runs on the FULL word, circle
    included, and the non-arc triple stays `false`).

Each class's connectivity, fed as `partnerShares`, ROUTES through `partnerIndexOf_reads_arc_general` to the read-off
`partnerIndexOf F.links … i = partner[i]` — demonstrated firing on all four all-caps / adversarial-B arcs.

## Honest scope — the GENERAL per-arc T-CONNECT PROOF stays the wall (no fabricated flip)

This file discharges the connectivity CONCRETELY (per class, on wild witnesses) and the routing GENERALLY.  It does
NOT prove the general per-arc `matchingSameComponent d.bottomCount F i (partner[i]) = true`.  For the CAP class that
proof is the position-bookkeeping assembly of the shipped bricks (r18 `crossingWord_openWire_sameComponent_bottomPort`
⊕ `correctedBottomPerm_decodesReadOff` ⊕ `capThenCupFold_connects` ⊕ `processBrauer_isSameComponent_ofBase`),
aligning `flattenNatPairs` cap-foot pairs with the boundary reads (T-ENUM territory).  For the CUP and THROUGH
classes it additionally needs a GENERAL non-seed crossing open-wire tracker (the `topPerm` / `middle` phases run on a
NON-seed state, off the seed-locked `StateIsPermGraph`), the r19-named fresh-id bridge.  So
`fxBrauer_hasFoldAlignmentE3`, `fxBrauer_hasFoldTargetHonestAssembly`, `fxBrauer_hasTagCorrDisjoint`,
`fxBrauer_hasTagCorrExtraction` stay honestly `false`; #2013 does NOT close.

Raw Lean 4 + Init; structural, no `omega` / `simp`-AC / `native_decide` / `WellFounded.fix`.  `decide` only on closed
literals.  Per-declaration `#assert_no_axioms` in the audit twin; independent `#print axioms` clean. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## The bottom–bottom cap-arc join-site reduction (GENERAL) -/

/-- ★★ **A CAP arc's boundary matching IS node connectivity.**  For two BOTTOM ports `i, j < bottomCount` (the two
feet of a bottom–bottom cap arc), `matchingSameComponent bottomCount state i j` reduces to `isSameComponent
state.links i j`: each bottom boundary read is the seed node itself (`matchingBoundaryNodes_getAt_bottom`).  The
join-site reduction the cap-class T-CONNECT lands on — the recon's cap chain `i ~ openWire[2k] ~ openWire[2k+1] ~
partner[i]`, after transport to the fold end, is exactly an `isSameComponent … i partner[i]` obligation. -/
theorem matchingSameComponent_bottomBottom_eq_isSameComponent (bottomCount : Nat) (state : WireState)
    (i j : Nat) (iLt : i < bottomCount) (jLt : j < bottomCount) :
    matchingSameComponent bottomCount state i j = isSameComponent state.links i j := by
  show isSameComponent state.links (natListGetAt (matchingBoundaryNodes bottomCount state) i)
      (natListGetAt (matchingBoundaryNodes bottomCount state) j)
    = isSameComponent state.links i j
  rw [matchingBoundaryNodes_getAt_bottom bottomCount state i iLt,
    matchingBoundaryNodes_getAt_bottom bottomCount state j jLt]

/-! ## The T-CONNECT routing collapse (the headline — GENERAL) -/

/-- ★★★ **THE T-CONNECT ROUTING COLLAPSE.**  For EVERY well-formed boundary involution `d`, the six-phase endgame
reduces to the single per-arc datum `partnerShares`: if boundary indices `probeIndex ≠ partnerIndex` (both in range)
are same-component in the corrected-word fold state, then the extractor's partner map reads exactly that partner.
The chain: the r21 general well-formedness `wellFormedBrauerFold_correctedWord_general` supplies the
`WellFormedBrauerFold` premise; `boundedBoundaryComponents_reachable` (r10) turns it into T-DISJOINT; and the r11
uniqueness read-off `partnerIndexOf_reads_matchingPartner` reads the exhibited partner off the T-DISJOINT state.  So
`partnerShares` (the per-arc `matchingSameComponent` fact — this IS T-CONNECT) is the SOLE remaining input to close
`extractDiagram F = d` at every boundary slot. -/
theorem partnerIndexOf_reads_arc_general (d : DiagramType) (bottomPos : 0 < d.bottomCount)
    (wf : IsBoundaryInvolution (d.bottomCount + d.topCount) d.partner)
    (probeIndex partnerIndex : Nat)
    (probeInRange : probeIndex < d.bottomCount
      + (processBrauer (brauerSeed d.bottomCount)
          (standardFormWordExt5 (reconstructStandardFormExt5Corrected d))).openWires.length)
    (partnerInRange : partnerIndex < d.bottomCount
      + (processBrauer (brauerSeed d.bottomCount)
          (standardFormWordExt5 (reconstructStandardFormExt5Corrected d))).openWires.length)
    (partnerNeProbe : partnerIndex ≠ probeIndex)
    (partnerShares : matchingSameComponent d.bottomCount
        (processBrauer (brauerSeed d.bottomCount)
          (standardFormWordExt5 (reconstructStandardFormExt5Corrected d))) probeIndex partnerIndex = true) :
    partnerIndexOf
        (processBrauer (brauerSeed d.bottomCount)
          (standardFormWordExt5 (reconstructStandardFormExt5Corrected d))).links
        (matchingBoundaryNodes d.bottomCount
          (processBrauer (brauerSeed d.bottomCount)
            (standardFormWordExt5 (reconstructStandardFormExt5Corrected d))))
        (d.bottomCount + (processBrauer (brauerSeed d.bottomCount)
          (standardFormWordExt5 (reconstructStandardFormExt5Corrected d))).openWires.length)
        probeIndex
      = partnerIndex :=
  partnerIndexOf_reads_matchingPartner d.bottomCount
    (processBrauer (brauerSeed d.bottomCount)
      (standardFormWordExt5 (reconstructStandardFormExt5Corrected d)))
    (boundedBoundaryComponents_reachable d.bottomCount bottomPos _
      (wellFormedBrauerFold_correctedWord_general d wf))
    probeIndex partnerIndex probeInRange partnerInRange partnerNeProbe partnerShares

/-! ## B1 — the per-arc-class connectivity, probed by evaluation (eval FIRST)

The all-caps `{4,0,[3,2,1,0]}` self-attack diagram (`2·#caps = bottomCount`, `#through = #cups = 0`, the cleanest
cap-only class) and the triple-axis adversarial-B `{3,3,[2,4,0,5,1,3],1}` (crossing cap + through + crossing cup +
loop).  Fold-end states spelled through the corrected word; connectivity `decide`d on the closed literals. -/

/-- The all-caps self-attack diagram — cap arcs only, `#through = #cups = 0`. -/
def capClassAllCapsDiagram : DiagramType := { bottomCount := 4, topCount := 0, partner := [3, 2, 1, 0], loops := 0 }

/-- ★ **CAP-class connectivity (all-caps).**  Both cap arcs `(0,3)` and `(1,2)` are same-component in the
corrected-word fold state — the cap class discharged concretely on the tight `2·#caps = bottomCount` witness. -/
theorem tConnectCapClass_connectivity_allCaps :
    (matchingSameComponent 4
        (processBrauer (brauerSeed 4)
          (standardFormWordExt5 (reconstructStandardFormExt5Corrected capClassAllCapsDiagram))) 0 3 = true)
    ∧ (matchingSameComponent 4
        (processBrauer (brauerSeed 4)
          (standardFormWordExt5 (reconstructStandardFormExt5Corrected capClassAllCapsDiagram))) 1 2 = true) :=
  ⟨by decide, by decide⟩

/-- ★ **The all-caps corrected word reads back to the all-caps diagram** — the cap-only six-phase fold closes the
roundtrip (T-CONNECT ∧ T-DISJOINT witnessed jointly, decidably). -/
theorem tConnectCapClass_roundtrip_allCaps :
    extractDiagram 4
        (processBrauer (brauerSeed 4)
          (standardFormWordExt5 (reconstructStandardFormExt5Corrected capClassAllCapsDiagram)))
      = capClassAllCapsDiagram := by decide

/-- ★ **All-three-class connectivity (adversarial-B).**  The crossing cap `0↔2`, the through `1↔top1` (index `4`),
and the crossing cup `top0↔top2` (indices `3,5`) are EACH same-component in the full six-phase fold (circle
included) — the three arc classes discharged concretely on the triple-axis witness. -/
theorem tConnectCapClass_connectivity_adversarialB :
    (matchingSameComponent 3
        (processBrauer (brauerSeed 3)
          (standardFormWordExt5 (reconstructStandardFormExt5Corrected adversarialBDiagram))) 0 2 = true)
    ∧ (matchingSameComponent 3
        (processBrauer (brauerSeed 3)
          (standardFormWordExt5 (reconstructStandardFormExt5Corrected adversarialBDiagram))) 1 4 = true)
    ∧ (matchingSameComponent 3
        (processBrauer (brauerSeed 3)
          (standardFormWordExt5 (reconstructStandardFormExt5Corrected adversarialBDiagram))) 3 5 = true) :=
  ⟨by decide, by decide, by decide⟩

/-- ★ **Non-arc disconnection (adversarial-B).**  Pairs that are NOT arcs of the diagram — `(0,1)`, `(0,4)`,
`(1,3)` — are each disconnected in the fold: T-DISJOINT witnessed concretely, so the connectivity probe is not
vacuously all-true. -/
theorem tConnectCapClass_nonArc_adversarialB :
    (matchingSameComponent 3
        (processBrauer (brauerSeed 3)
          (standardFormWordExt5 (reconstructStandardFormExt5Corrected adversarialBDiagram))) 0 1 = false)
    ∧ (matchingSameComponent 3
        (processBrauer (brauerSeed 3)
          (standardFormWordExt5 (reconstructStandardFormExt5Corrected adversarialBDiagram))) 0 4 = false)
    ∧ (matchingSameComponent 3
        (processBrauer (brauerSeed 3)
          (standardFormWordExt5 (reconstructStandardFormExt5Corrected adversarialBDiagram))) 1 3 = false) :=
  ⟨by decide, by decide, by decide⟩

/-! ## B4 — the routed firings: per-class connectivity FED through the routing collapse

Each concrete `partnerShares` (a `matchingSameComponent` fact from B1) routes through
`partnerIndexOf_reads_arc_general` to `partnerIndexOf F.links … i = partner[i]` — the extractor read-off the
six-phase roundtrip closes on. -/

/-- ★★ **CAP arc routed (all-caps, smaller foot `0`).**  Boundary index `0`'s partner reads `3` — the cap
connectivity `0↔3` fed as `partnerShares` through the general routing collapse (over the shipped all-caps
involution + r21 well-formedness). -/
theorem partnerIndexOf_readsCapArc_allCaps_zero :
    partnerIndexOf
        (processBrauer (brauerSeed 4)
          (standardFormWordExt5 (reconstructStandardFormExt5Corrected capClassAllCapsDiagram))).links
        (matchingBoundaryNodes 4
          (processBrauer (brauerSeed 4)
            (standardFormWordExt5 (reconstructStandardFormExt5Corrected capClassAllCapsDiagram))))
        (4 + (processBrauer (brauerSeed 4)
          (standardFormWordExt5 (reconstructStandardFormExt5Corrected capClassAllCapsDiagram))).openWires.length)
        0
      = 3 :=
  partnerIndexOf_reads_arc_general capClassAllCapsDiagram (by decide) isBoundaryInvolution_allCapsBoundary
    0 3 (by decide) (by decide) (by decide) (by decide)

/-- ★★ **CAP arc routed (all-caps, smaller foot `1`).**  Boundary index `1`'s partner reads `2`. -/
theorem partnerIndexOf_readsCapArc_allCaps_one :
    partnerIndexOf
        (processBrauer (brauerSeed 4)
          (standardFormWordExt5 (reconstructStandardFormExt5Corrected capClassAllCapsDiagram))).links
        (matchingBoundaryNodes 4
          (processBrauer (brauerSeed 4)
            (standardFormWordExt5 (reconstructStandardFormExt5Corrected capClassAllCapsDiagram))))
        (4 + (processBrauer (brauerSeed 4)
          (standardFormWordExt5 (reconstructStandardFormExt5Corrected capClassAllCapsDiagram))).openWires.length)
        1
      = 2 :=
  partnerIndexOf_reads_arc_general capClassAllCapsDiagram (by decide) isBoundaryInvolution_allCapsBoundary
    1 2 (by decide) (by decide) (by decide) (by decide)

/-- ★ **The triple-axis adversarial-B boundary is a boundary involution** — length `6`, self-inverse `0↔2, 1↔4,
3↔5`, fixed-point-free.  The involution witness the routing collapse needs at the adversarial-B instance (used
below to route all three arc classes). -/
theorem isBoundaryInvolution_adversarialBDiagram :
    IsBoundaryInvolution (adversarialBDiagram.bottomCount + adversarialBDiagram.topCount)
      adversarialBDiagram.partner where
  hasBoundaryLength := rfl
  mapsInRange := by decide
  isSelfInverse := by decide
  isFixedPointFree := by decide

/-- ★★ **CAP arc routed (adversarial-B, `0↔2`).**  The crossing-cap connectivity fed through the routing collapse:
boundary index `0`'s partner reads `2`. -/
theorem partnerIndexOf_readsArc_adversarialB_cap :
    partnerIndexOf
        (processBrauer (brauerSeed 3)
          (standardFormWordExt5 (reconstructStandardFormExt5Corrected adversarialBDiagram))).links
        (matchingBoundaryNodes 3
          (processBrauer (brauerSeed 3)
            (standardFormWordExt5 (reconstructStandardFormExt5Corrected adversarialBDiagram))))
        (3 + (processBrauer (brauerSeed 3)
          (standardFormWordExt5 (reconstructStandardFormExt5Corrected adversarialBDiagram))).openWires.length)
        0
      = 2 :=
  partnerIndexOf_reads_arc_general adversarialBDiagram (by decide) isBoundaryInvolution_adversarialBDiagram
    0 2 (by decide) (by decide) (by decide) (by decide)

/-- ★★ **THROUGH arc routed (adversarial-B, `1↔top1`).**  The through-strand connectivity fed through the routing
collapse: boundary index `1`'s partner reads `4` (top port `1`). -/
theorem partnerIndexOf_readsArc_adversarialB_through :
    partnerIndexOf
        (processBrauer (brauerSeed 3)
          (standardFormWordExt5 (reconstructStandardFormExt5Corrected adversarialBDiagram))).links
        (matchingBoundaryNodes 3
          (processBrauer (brauerSeed 3)
            (standardFormWordExt5 (reconstructStandardFormExt5Corrected adversarialBDiagram))))
        (3 + (processBrauer (brauerSeed 3)
          (standardFormWordExt5 (reconstructStandardFormExt5Corrected adversarialBDiagram))).openWires.length)
        1
      = 4 :=
  partnerIndexOf_reads_arc_general adversarialBDiagram (by decide) isBoundaryInvolution_adversarialBDiagram
    1 4 (by decide) (by decide) (by decide) (by decide)

/-- ★★ **CUP arc routed (adversarial-B, `top0↔top2`).**  The crossing-cup connectivity fed through the routing
collapse: boundary index `3` (top port `0`) partners `5` (top port `2`). -/
theorem partnerIndexOf_readsArc_adversarialB_cup :
    partnerIndexOf
        (processBrauer (brauerSeed 3)
          (standardFormWordExt5 (reconstructStandardFormExt5Corrected adversarialBDiagram))).links
        (matchingBoundaryNodes 3
          (processBrauer (brauerSeed 3)
            (standardFormWordExt5 (reconstructStandardFormExt5Corrected adversarialBDiagram))))
        (3 + (processBrauer (brauerSeed 3)
          (standardFormWordExt5 (reconstructStandardFormExt5Corrected adversarialBDiagram))).openWires.length)
        3
      = 5 :=
  partnerIndexOf_reads_arc_general adversarialBDiagram (by decide) isBoundaryInvolution_adversarialBDiagram
    3 5 (by decide) (by decide) (by decide) (by decide)

/-! ## B2 (CUP, partial) — the top–top / bottom–top join-site matching reductions + the fresh interleaved-cups probe

The cap-arc join site reduces via `matchingSameComponent_bottomBottom_eq_isSameComponent` (both feet bottom).  The CUP
arc's two feet are both TOP ports, and the THROUGH arc has one bottom + one top foot, so the CUP / THROUGH chains need
the top–top and bottom–top analogs — cheap reductions via `matchingBoundaryNodes_getAt_top` (a top port
`bottomCount + offset` reads the open wire at `offset`, no range hypothesis).  These are the join-site reductions the
general CUP / THROUGH `partnerShares` will feed the routing collapse; the connectivity BUILD (the `foldFactorsThroughCup`
six-phase factor + the `permInverse` cup-rank arithmetic for CUP, the 5-phase node-identity assembly for THROUGH) stays
WALLED — see `fxBrauer_hasTConnectThroughWall`. -/

/-- ★★ **The CUP arc join-site reduction (top–top).**  Both cup feet are top ports, so
`matchingSameComponent bottomCount state (bottomCount + a) (bottomCount + b)` reduces to node connectivity of the open
wires at offsets `a`, `b` — the top-side analog of `matchingSameComponent_bottomBottom_eq_isSameComponent`, via
`matchingBoundaryNodes_getAt_top` (no range hypothesis needed). -/
theorem matchingSameComponent_topTop_eq_isSameComponent (bottomCount : Nat) (state : WireState) (a b : Nat) :
    matchingSameComponent bottomCount state (bottomCount + a) (bottomCount + b)
      = isSameComponent state.links (natListGetAt state.openWires a) (natListGetAt state.openWires b) := by
  show isSameComponent state.links (natListGetAt (matchingBoundaryNodes bottomCount state) (bottomCount + a))
      (natListGetAt (matchingBoundaryNodes bottomCount state) (bottomCount + b))
    = isSameComponent state.links (natListGetAt state.openWires a) (natListGetAt state.openWires b)
  rw [matchingBoundaryNodes_getAt_top bottomCount state a, matchingBoundaryNodes_getAt_top bottomCount state b]

/-- ★★ **The THROUGH arc join-site reduction (bottom–top).**  A through arc has one bottom foot `i < bottomCount` and
one top foot `bottomCount + b`, so `matchingSameComponent bottomCount state i (bottomCount + b)` reduces to node
connectivity of `i` and the open wire at offset `b`. -/
theorem matchingSameComponent_bottomTop_eq_isSameComponent (bottomCount : Nat) (state : WireState)
    (i b : Nat) (iLt : i < bottomCount) :
    matchingSameComponent bottomCount state i (bottomCount + b)
      = isSameComponent state.links i (natListGetAt state.openWires b) := by
  show isSameComponent state.links (natListGetAt (matchingBoundaryNodes bottomCount state) i)
      (natListGetAt (matchingBoundaryNodes bottomCount state) (bottomCount + b))
    = isSameComponent state.links i (natListGetAt state.openWires b)
  rw [matchingBoundaryNodes_getAt_bottom bottomCount state i iLt,
    matchingBoundaryNodes_getAt_top bottomCount state b]

/-- The FRESH interleaved crossing cups diagram: two top-only cup arcs `0↔2` and `1↔3`, INTERLEAVED (each spans one
foot of the other), distinct from the r24 NESTED `{0,4,[3,2,1,0]}`.  A boundary involution on `0 + 4` ports. -/
def interleavedCupsDiagram : DiagramType :=
  { bottomCount := 0, topCount := 4, partner := [2, 3, 0, 1], loops := 0 }

/-- The interleaved cups diagram is a boundary involution (each field `decide`-checked). -/
theorem isBoundaryInvolution_interleavedCups :
    IsBoundaryInvolution (interleavedCupsDiagram.bottomCount + interleavedCupsDiagram.topCount)
      interleavedCupsDiagram.partner where
  hasBoundaryLength := rfl
  mapsInRange := by decide
  isSelfInverse := by decide
  isFixedPointFree := by decide

/-- ★ **CUP-chain TOP-DECODE probe (interleaved cups).**  The corrected `topPerm` staircase decodes to `[0, 2, 1, 3]`
— the interleaved routing (distinct from the nested `[0, 2, 3, 1]`). -/
theorem cupChainTopDecodeProbe_interleavedCups :
    permuteOfCrossingWord 4 (reconstructStandardFormExt5Corrected interleavedCupsDiagram).topPerm
      = permInverse (throughStrandTops 0 4 interleavedCupsDiagram.partner
          ++ cupArcTops 0 4 interleavedCupsDiagram.partner) := by decide

/-- ★ **CUP-chain JOIN probe (fresh interleaved cups).**  The two interleaved cup arcs `top0↔top2`, `top1↔top3` are
each same-component in the corrected six-phase fold, and the non-arc `top0↔top1` is disconnected — the CUP join
witnessed on a FRESH interleaved diagram (the general CUP T-CONNECT would prove this for every cup rank; the build
stays walled at the `foldFactorsThroughCup` factor + `permInverse` cup-rank arithmetic). -/
theorem cupChainJoinProbe_interleavedCups :
    (matchingSameComponent 0
        (processBrauer (brauerSeed 0)
          (standardFormWordExt5 (reconstructStandardFormExt5Corrected interleavedCupsDiagram))) 0 2 = true)
    ∧ (matchingSameComponent 0
        (processBrauer (brauerSeed 0)
          (standardFormWordExt5 (reconstructStandardFormExt5Corrected interleavedCupsDiagram))) 1 3 = true)
    ∧ (matchingSameComponent 0
        (processBrauer (brauerSeed 0)
          (standardFormWordExt5 (reconstructStandardFormExt5Corrected interleavedCupsDiagram))) 0 1 = false) :=
  ⟨by decide, by decide, by decide⟩

/-- ★★ **Honesty marker — the CUP / THROUGH join-site matching reductions are SHIPPED (r25, ingredient).**  The top–top
(`matchingSameComponent_topTop_eq_isSameComponent`) and bottom–top (`matchingSameComponent_bottomTop_eq_isSameComponent`)
reductions — the CUP / THROUGH analogs of the shipped bottom–bottom cap reduction — reduce each arc's `partnerShares` to
node connectivity of the open wires at the arc's top offsets.  A NEW ingredient marker; it flips NO master — the CUP
connectivity BUILD (`foldFactorsThroughCup` + `permInverse` cup-rank arithmetic) and the THROUGH 5-phase assembly stay
walled (`fxBrauer_hasTConnectThroughWall = false`).  `= true`. -/
def fxBrauer_hasTopTopMatchingReduction : Bool := true

/-! ## Honesty markers + the r22 ledger -/

/-- ★★ **Honesty marker — the T-CONNECT ROUTING COLLAPSE is SHIPPED (r22).**  `partnerIndexOf_reads_arc_general`
reduces the entire six-phase endgame, for EVERY well-formed boundary involution, to the single per-arc datum
`partnerShares` (= T-CONNECT): the r21 general well-formedness → the r10 T-DISJOINT fold → the r11 uniqueness
read-off, chained.  And `matchingSameComponent_bottomBottom_eq_isSameComponent` records the cap-arc join-site
reduction (bottom–bottom matching IS node connectivity).  So closing `extractDiagram F = d` now needs ONLY the
per-arc connectivity `matchingSameComponent d.bottomCount F i (partner[i]) = true`.  `= true`. -/
def fxBrauer_hasTConnectRoutingCollapse : Bool := true

/-- ★★ **Honesty marker — the per-arc-class T-CONNECT connectivity is PROBED and ROUTED per class (r22).**  Each
arc class's connectivity is kernel-decided on a wild witness — CAP (`tConnectCapClass_connectivity_allCaps`,
`…_adversarialB`), THROUGH and CUP (`…_adversarialB`), with T-DISJOINT witnessed by the non-arc disconnection
(`tConnectCapClass_nonArc_adversarialB`) and the all-caps roundtrip (`tConnectCapClass_roundtrip_allCaps`) — and
each is FED through the routing collapse to `partnerIndexOf F.links … i = partner[i]`
(`partnerIndexOf_readsCapArc_allCaps_zero` / `_one`, `partnerIndexOf_readsArc_adversarialB_cap` / `_through` /
`_cup`).  The LOOP class carries no boundary obligation — the adversarial-B `loops := 1` circle is exercised inside
the full-word probes, leaving the boundary matching untouched.  `= true`. -/
def fxBrauer_hasTConnectPerClassProbed : Bool := true

/-- **Honesty WALL marker — the GENERAL per-arc T-CONNECT PROOF stays UNBUILT (the r19 fresh-id bridge).**  The
routing collapse is general, but the per-arc connectivity `matchingSameComponent d.bottomCount F i (partner[i]) =
true` is discharged only CONCRETELY (per class, on wild witnesses), not in general.  For the CAP class the general
proof is the position-bookkeeping assembly of the shipped bricks (r18 `crossingWord_openWire_sameComponent_bottomPort`
⊕ `correctedBottomPerm_decodesReadOff` ⊕ `capThenCupFold_connects` ⊕ `processBrauer_isSameComponent_ofBase`),
aligning `flattenNatPairs` cap-foot pairs with the boundary reads (T-ENUM territory).  For CUP and THROUGH it
additionally needs a GENERAL non-seed crossing open-wire tracker (the `topPerm` / `middle` phases run on a NON-seed
state, off the seed-locked `StateIsPermGraph`) — the r19-named fresh-id bridge, UNBUILT.  So
`fxBrauer_hasFoldAlignmentE3` / `fxBrauer_hasFoldTargetHonestAssembly` / `fxBrauer_hasTagCorrDisjoint` /
`fxBrauer_hasTagCorrExtraction` stay honestly `false`; #2013 does NOT close.  `= false`. -/
def fxBrauer_hasTConnectThroughWall : Bool := false

/-- ★★★ **The BRAUER r22 GRAND LEDGER — MACHINE-CHECKED.**  The two shipped r22 markers
(`fxBrauer_hasTConnectRoutingCollapse` = the general endgame→T-CONNECT collapse,
`fxBrauer_hasTConnectPerClassProbed` = per-class connectivity probed and routed) are `true`, on top of the shipped
r18 crossing-phase correspondence (`fxBrauer_hasCrossingStaircaseConnectivity`), the r19 corrected fold target
(`fxBrauer_hasFoldTargetCorrected`), and the r5 six-phase glue (`fxBrauer_hasSixPhaseGlue`); and EVERY wall — the
through-strand fresh-id bridge (`fxBrauer_hasTConnectThroughWall`), the E3 fold alignment
(`fxBrauer_hasFoldAlignmentE3`), the honest six-phase assembly (`fxBrauer_hasFoldTargetHonestAssembly`), the
tag-correspondence masters, and the completeness masters — is `false`.  A `rfl`-conjunction the kernel checks: r22
collapses the endgame to T-CONNECT and probes/routes every arc class, but the GENERAL per-arc T-CONNECT proof (the
r19 fresh-id bridge) is unbuilt, so no master flip is fabricated and #2013 does NOT close. -/
theorem fxBrauer_r22GrandLedger :
    (fxBrauer_hasTConnectRoutingCollapse = true
      ∧ fxBrauer_hasTConnectPerClassProbed = true)
    ∧ (fxBrauer_hasCrossingStaircaseConnectivity = true
      ∧ fxBrauer_hasFoldTargetCorrected = true
      ∧ fxBrauer_hasSixPhaseGlue = true)
    ∧ (fxBrauer_hasTConnectThroughWall = false
      ∧ fxBrauer_hasFoldAlignmentE3 = false
      ∧ fxBrauer_hasFoldTargetHonestAssembly = false)
    ∧ (fxBrauer_hasTagCorrDisjoint = false
      ∧ fxBrauer_hasTagCorrExtraction = false)
    ∧ (fxBrauer_hasBrauerV2FullCompleteness = false
      ∧ fxBrauer_hasBrauerCompleteness = false
      ∧ fxBrauer_hasFreeBrauerStraighteningNF = false) :=
  ⟨⟨rfl, rfl⟩, ⟨rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl⟩, ⟨rfl, rfl⟩, ⟨rfl, rfl, rfl⟩⟩

end FX1Poly.Polygraph
