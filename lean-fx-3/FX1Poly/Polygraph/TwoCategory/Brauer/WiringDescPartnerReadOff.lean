import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.MatchingBoundaryIndexCensus
import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescBoundedBoundaryFold

/-! # BRAUER-MIDDLE r11 B2 — the EXTRACTION READ-OFF: `partnerIndexOf` reads the exhibited partner over
any T-DISJOINT state

The r5 ledger named the tag correspondence's **T-DISJOINT** long pole, and r10 shipped its two halves: the
per-atom preservations (`boundedBoundaryComponents_stepCap` / `_stepCup` / `_stepCrossing`), the generator
bridges, and the whole-fold lift (`boundedBoundaryComponents_reachable`).  What r10 explicitly did NOT close is
the EXTRACTION consequence — that `partnerIndexOf`, the map `extractDiagram` reads at every boundary index,
returns exactly the exhibited same-component partner.  This file ships that consequence at WORD granularity,
carrier-free, over any state carrying `boundedBoundaryComponents`.

The recon's headline: the uniqueness + read-off machinery is ALREADY shipped, public and carrier-free, in
`WalkingAdjunction/MatchingBoundaryIndexCensus.lean` (`partnerIndexOf_uniqueSameComponent_generic`,
`partnerIndexOf_isInvolution_ofBoundaryIndexCensus`), phrased over the abstract union-find datum
`(links, boundaryNodes, total)` through the index-form `BoundaryIndexCensus`.  So the r11 read-off is NOT new
machinery — it is an INSTANTIATION at the Brauer state, gated only by an existence witness.  The one-line bridge
that makes the instantiation apply is `boundaryIndexCensus_ofBoundedBoundaryComponents`: the Brauer T-DISJOINT
invariant `boundedBoundaryComponents bottomCount state` IS the index-form census at
`links := state.links`, `boundaryNodes := matchingBoundaryNodes bottomCount state =
List.range bottomCount ++ state.openWires`, `total := bottomCount + state.openWires.length` — the SAME datum
`extractDiagram` reads (`matchingSameComponent` unfolds to `isSameComponent state.links` on the boundary reads,
`propext`-free).

  * ★ `boundaryIndexCensus_ofBoundedBoundaryComponents` — the census bridge (`¬ (A ∧ B)` ⟺ `A → B → False`,
    modulo the `matchingSameComponent` / `isSameComponent` defeq).

  * ★ `partnerIndexOf_reads_matchingPartner` — THE EXTRACTION READ-OFF.  Over a T-DISJOINT state, any in-range
    boundary index `partnerIndex ≠ probeIndex` sharing the probe's component IS `partnerIndexOf` at the probe —
    i.e. the value `extractDiagram` writes at that boundary slot.  The existence of the partner is a HYPOTHESIS
    (`partnerShares`): T-DISJOINT alone gives uniqueness; totality of the partner map is the separate B1 leg.

  * ★ `partnerIndexOf_involution_ofBoundedBoundaryComponents` — the fixed-point-free involution corollary over a
    T-DISJOINT state (given a genuine, non-fixed partner), free from
    `partnerIndexOf_isInvolution_ofBoundaryIndexCensus`.

This flips the NEW sub-marker `fxBrauer_hasPartnerReadOff`.  It does NOT flip `fxBrauer_hasTagCorrDisjoint` /
`fxBrauer_hasTagCorrExtraction`: those additionally demand the read-off WIRED to a specific diagram `d` over the
six-phase standard-form word — the two-source existence assembly (T-CONNECT arc pairs + through-perm
connectivity feeding `partnerShares` at every `d`-arc), which is B3, not this abstract read-off.

Raw Lean 4 + Init; structural, no `omega` / `simp`-AC / `native_decide` / `WellFounded.fix`.
Per-declaration `#assert_no_axioms` in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## The census bridge -/

/-- ★ **The Brauer T-DISJOINT invariant IS the index-form boundary census at the extract's datum.**  Unfolding
the two forms: `boundedBoundaryComponents bottomCount state` forbids any three distinct in-range indices from
pairwise sharing a `matchingSameComponent` class, and `matchingSameComponent bottomCount state i j` is
definitionally `isSameComponent state.links (natListGetAt (matchingBoundaryNodes bottomCount state) i) (… j)`
(both reduce to `unionFindRootOf state.links _ == unionFindRootOf state.links _`).  So the invariant supplies
`BoundaryIndexCensus state.links (matchingBoundaryNodes bottomCount state) (bottomCount +
state.openWires.length)` — the exact datum `extractDiagram`'s partner map reads.  The only reshaping is the
propositional `¬ (A ∧ B)` ⟹ `A → B → False`. -/
theorem boundaryIndexCensus_ofBoundedBoundaryComponents (bottomCount : Nat) (state : WireState)
    (bounded : boundedBoundaryComponents bottomCount state) :
    BoundaryIndexCensus state.links (matchingBoundaryNodes bottomCount state)
      (bottomCount + state.openWires.length) := by
  intro indexOne indexTwo indexThree oneBelow twoBelow threeBelow
    oneNeTwo oneNeThree twoNeThree sameOneTwo sameOneThree
  exact bounded indexOne indexTwo indexThree oneBelow twoBelow threeBelow
    oneNeTwo oneNeThree twoNeThree ⟨sameOneTwo, sameOneThree⟩

/-! ## The extraction read-off -/

/-- ★ **THE EXTRACTION READ-OFF (r11 B2).**  Over any state satisfying T-DISJOINT, the partner map
`partnerIndexOf` that `extractDiagram` evaluates at each boundary slot returns exactly the exhibited partner: if
`partnerIndex` is an in-range boundary index other than `probeIndex` whose boundary read shares `probeIndex`'s
union-find component, then `partnerIndexOf state.links (matchingBoundaryNodes …) total probeIndex =
partnerIndex`.  A direct instantiation of the shipped carrier-free `partnerIndexOf_uniqueSameComponent_generic`
through the census bridge — no crossing-only `permPartnerAt` machinery, valid for ANY (cap / cup / crossing)
mixed Brauer state.  The existence of `partnerIndex` is a hypothesis; totality of the partner map is the
separate B1 leg. -/
theorem partnerIndexOf_reads_matchingPartner (bottomCount : Nat) (state : WireState)
    (bounded : boundedBoundaryComponents bottomCount state)
    (probeIndex partnerIndex : Nat)
    (probeInRange : probeIndex < bottomCount + state.openWires.length)
    (partnerInRange : partnerIndex < bottomCount + state.openWires.length)
    (partnerNeProbe : partnerIndex ≠ probeIndex)
    (partnerShares : matchingSameComponent bottomCount state probeIndex partnerIndex = true) :
    partnerIndexOf state.links (matchingBoundaryNodes bottomCount state)
        (bottomCount + state.openWires.length) probeIndex
      = partnerIndex :=
  partnerIndexOf_uniqueSameComponent_generic state.links (matchingBoundaryNodes bottomCount state)
    (bottomCount + state.openWires.length)
    (boundaryIndexCensus_ofBoundedBoundaryComponents bottomCount state bounded)
    probeIndex partnerIndex probeInRange partnerInRange partnerNeProbe partnerShares

/-! ## The involution corollary -/

/-- ★ **The T-DISJOINT boundary matching is a fixed-point-free involution (given a genuine partner).**  At a
T-DISJOINT state, if the probe's partner is genuine (`partnerIndexOf … probeIndex ≠ probeIndex`), applying
`partnerIndexOf` again returns the probe.  Free from the shipped
`partnerIndexOf_isInvolution_ofBoundaryIndexCensus` through the census bridge; the exact interface a partner
LIST-vs-`d` matching consumer needs once B1 supplies the non-fixedness (totality) witness. -/
theorem partnerIndexOf_involution_ofBoundedBoundaryComponents (bottomCount : Nat) (state : WireState)
    (bounded : boundedBoundaryComponents bottomCount state)
    (probeIndex : Nat) (probeInRange : probeIndex < bottomCount + state.openWires.length)
    (notFixed : partnerIndexOf state.links (matchingBoundaryNodes bottomCount state)
        (bottomCount + state.openWires.length) probeIndex ≠ probeIndex) :
    partnerIndexOf state.links (matchingBoundaryNodes bottomCount state)
        (bottomCount + state.openWires.length)
        (partnerIndexOf state.links (matchingBoundaryNodes bottomCount state)
          (bottomCount + state.openWires.length) probeIndex)
      = probeIndex :=
  partnerIndexOf_isInvolution_ofBoundaryIndexCensus state.links (matchingBoundaryNodes bottomCount state)
    (bottomCount + state.openWires.length)
    (boundaryIndexCensus_ofBoundedBoundaryComponents bottomCount state bounded)
    probeIndex probeInRange notFixed

/-! ## Non-vacuity — mixed-diagram read-off firings (closed decidable literals) -/

/-- ★ **Read-off firing (crossing).**  The single crossing over two bottom strands extracts partner
`[3, 2, 1, 0]`; the partner map at boundary index `0` computes to `3` — the value the read-off theorem pins
against the exhibited same-component partner `3`. -/
theorem partnerIndexOf_reads_crossing :
    partnerIndexOf (processBrauer (brauerSeed 2) [crossingAt 0]).links
        (matchingBoundaryNodes 2 (processBrauer (brauerSeed 2) [crossingAt 0])) 4 0 = 3 := by decide

/-- ★ **Read-off firing (cap then cup).**  Capping the two bottom strands then cupping a fresh pair extracts
partner `[1, 0, 3, 2]`; the partner map at boundary index `0` computes to `1` — a mixed cap/cup diagram (no
`permPartnerAt` crossing-only formula applies), showing the read-off covers the full Brauer alphabet. -/
theorem partnerIndexOf_reads_capThenCup :
    partnerIndexOf (processBrauer (brauerSeed 2) [capAt 0, cupAt 0]).links
        (matchingBoundaryNodes 2 (processBrauer (brauerSeed 2) [capAt 0, cupAt 0])) 4 0 = 1 := by decide

/-! ## Honesty marker -/

/-- ★ **Honesty marker — the r11 EXTRACTION READ-OFF is SHIPPED (B2).**  Over any T-DISJOINT state,
`partnerIndexOf` — the map `extractDiagram` reads at each boundary slot — returns exactly the exhibited
same-component partner (`partnerIndexOf_reads_matchingPartner`), through the one-line census bridge
`boundaryIndexCensus_ofBoundedBoundaryComponents` into the shipped carrier-free
`partnerIndexOf_uniqueSameComponent_generic`, with the fixed-point-free involution corollary
(`partnerIndexOf_involution_ofBoundedBoundaryComponents`) free from
`partnerIndexOf_isInvolution_ofBoundaryIndexCensus`.  Valid for the whole Brauer alphabet (cap / cup / crossing),
NOT the crossing-only `partnerIndexOf_eq_permPartnerAt`.  Cross-checked firing on the crossing (`… 0 = 3`) and
the mixed cap-then-cup (`… 0 = 1`) diagrams.

  What this marker does NOT close (no gate flag flipped): the existence half — that the partner map is TOTAL
  (every in-range index has a genuine partner, `partnerIndexOf … i ≠ i`) — is the separate B1 leg; and the
  WIRING of this read-off to a specific diagram `d` over the six-phase standard-form word (feeding
  `partnerShares` at every `d`-arc from the T-CONNECT existence witnesses) is B3.  So
  `fxBrauer_hasTagCorrDisjoint` / `fxBrauer_hasTagCorrExtraction`, the roundtrip flags, and the masters stay
  `false`; #2013 does NOT close.  `= true`. -/
def fxBrauer_hasPartnerReadOff : Bool := true

end FX1Poly.Polygraph
