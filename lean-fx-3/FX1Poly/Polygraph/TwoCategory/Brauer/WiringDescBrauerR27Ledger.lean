import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescBrauerR26Ledger
import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescThroughStrandRoundtrip

/-! # BRAUER r27 — THE THROUGH-STRAND ROUNDTRIP CRUX + THE P1 DECODE LEG, and the exact #2013 ledger

r27 lands the THROUGH per-arc chain's single genuinely-new lemma (the P1 seam crux) and its first consumer (the P1
decode read-off), each machine-checked zero-axiom:

  * **The THROUGH-STRAND ROUNDTRIP CRUX** (`fxBrauer_hasThroughStrandRoundtrip`, `WiringDescThroughStrandRoundtrip`).
    `throughStrandBottoms_getAt_arcMiddleCountBelow` : on the strictly-ascending distinct list `throughStrandBottoms`,
    reading at the count-strictly-below rank inverts `natListGetAt` — `natListGetAt (throughStrandBottoms …)
    (arcMiddleCountBelow (throughStrandBottoms …) value) = value` for `value ∈ throughStrandBottoms`.  The
    direction-DUAL of the r26 rank↔position keystone (position→value under count-below, not value→position under
    `natIndexOfValue`); the two agree only because the list is strictly ascending.  The genuine new content: (1) a
    filterMap over `List.range` preserves strict ascent, (2) count-below inverts getAt on an ascending list.  Fired on
    the monster bottoms `4`, `5` and the 3-cycle 3-through.  The recon's risk pole (crux) — CLOSED.

  * **The P1 SEAM DECODE READ-OFF** (`fxBrauer_hasThroughReadOffFoot`, `WiringDescTConnectThroughChain`).
    `throughReadOffBottom_reads_throughFoot` : for EVERY well-formed involution and through-top rank, the bottom
    read-off order `capArcFeet ++ throughStrandBottoms` at the through wire's slot `|capArcFeet| +
    throughStrandPerm[topRank]` reads back the arc's bottom foot `partner[bottomCount + throughStrandTops[topRank]]` —
    the exact node the seed `bottomPerm` tracker lands on at S1.  Consumes the crux through the through-strand-perm map
    factorization (`throughStrandPerm_eq_throughStrandTops_map`) + getAt-map + the membership
    `throughStrandTop_partner_memThroughBottoms`.  Fired on the monster and the 3-cycle.  The P1 leg — general.

## B3 / B4 — the ALL-CLASS T-CONNECT stays WALLED at the THROUGH FIVE-PHASE WELD; no master is flipped

The all-class per-arc T-CONNECT needs the per-arc `partnerShares` in all four boundary classes.  CAP (r24) and CUP (r26)
are general; THROUGH is not.  The remaining THROUGH per-arc connectivity goal, with its named nodes
(`i := partner[bottomCount + t]`, `t := throughStrandTops[topRank]`, `r := throughStrandPerm[topRank]`):

    matchingSameComponent d.bottomCount F i (d.bottomCount + t) = true
      = isSameComponent F.links i (natListGetAt F.openWires t) = true   (matchingSameComponent_bottomTop, i < bottomCount)

is blocked ONLY at the FIVE-PHASE node-survival WELD, `fxBrauer_hasThroughClassGeneral = false`.  What r27 SHIPPED, and
the exact residual, seam-by-seam with each NAMED node:

  * **P1** (SHIPPED, `throughReadOffBottom_reads_throughFoot`): the seed `bottomPerm` tracker
    (`crossingWordFold_openWire_sameComponent_incomingPort_seed`) + `correctedBottomPerm_decodesReadOff` land S1's slot
    `|capArcFeet| + r` on node `i` — the read-off is now the shipped general lemma consuming the r27 crux.
  * **P2** (RESIDUAL): `S1.openWires[|capArcFeet| + r] = S2.openWires[r]` — the cap block consumes the front
    `doublePos |capArcFeetIndices|` wires (`capFold_consumes .1`, the `chunkFrontPairs` / `dropFrontPairs` split re-run
    exactly as inside `cupChainS3Width`), an append-right read `natListGetAtAppendRightCup`.  No new lemma.
  * **P3** (RESIDUAL): `S3.openWires[topRank] ~ S2.openWires[r]` — the interior `middle` tracker
    (`crossingWordFold_openWire_sameComponent_afterPrefix`) + GAP β (`natListGetAt_foldlAdjacentSwapBase`) +
    `correctedMiddle_decodesReadOff` (`permuteOfCrossingWord #throughBottoms middle = throughStrandPerm`), with the rank
    glue `throughStrandPerm[topRank] = r` DEFINITIONAL.  No new lemma.
  * **P4** (RESIDUAL): `S4.openWires[topRank] = S3.openWires[topRank]` — the cup block fires at offset `#throughBottoms`
    (`cupFold_creates_atOffset`, `front = S3.openWires`, `back = []`), so `S4.ow = S3.ow ++ flatten fresh` and
    `topRank < #throughBottoms` is an append-left read `natListGetAtAppendLeftCap`.  No new lemma.
  * **P5** (RESIDUAL): `F.openWires[t] ~ S4.openWires[topRank]` — the interior `topPerm` tracker + GAP β +
    `correctedTopPerm_decodesInverseReadOff` (`= permInverse (throughStrandTops ++ cupArcTops)`) + the r26 keystone
    `natListGetAtPermInverse_natListGetAt_ofPermutationOfRange` at `readOffTopOrder[topRank] = t`, with
    `circleFold_openWires` carrying `F.ow = S5.ow` past the circle phase.  The EXACT CUP P5 machinery landing on
    `S4.ow[topRank]` instead of the fresh block.  No new lemma.
  * **the WELD** (RESIDUAL): `isSameComponent_trans` / `_flip` chaining P5·P4·P3·P2·P1 in `F.links`, each local fact
    transported by `processBrauer_isSameComponent_ofBase` — a direct scale of `cupArcConnectViaState`'s two-tier weld.

So `throughArcConnect_general` / `throughArcMatching_general` do NOT land, the all-class classifier
(`partitionThree_of_involution` case split → three `…ArcMatching_general` → `partnerIndexOf_reads_arc_general`) has one
of three arm-classes unbuilt, and `fxBrauer_hasTConnectThroughWall` stays `false`.  With it: `fxBrauer_hasFoldAlignmentE3`,
`fxBrauer_hasFoldTargetHonestAssembly`, the tag-correspondence and completeness masters.  **#2013 does NOT close.**  Even
were the THROUGH weld to land, E3 / T-ENUM additionally owes the separate **T-CLOSE(b)** `extractDiagram F = d`
reassembly (`foldRealizesTargetDiagramCorrected`) — the r28 endgame is the five-phase WELD (P2–P5 + trans/flip) then
T-CLOSE(b).  NO flip is fabricated.

Raw Lean 4 + Init; a `rfl`-conjunction the kernel checks.  Per-declaration `#assert_no_axioms` in the audit twin;
independent `#print axioms` clean. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-- ★★★ **THE BRAUER r27 GRAND LEDGER — MACHINE-CHECKED.**  The r27 markers — the THROUGH-STRAND ROUNDTRIP CRUX
(`fxBrauer_hasThroughStrandRoundtrip`, the recon risk pole) and the P1 seam decode read-off
(`fxBrauer_hasThroughReadOffFoot`, the crux consumed in the fold decode) — are `true`, on top of the r26 keystone /
CUP-class general / GAP β / γ (`fxBrauer_hasRankPositionDuality`, `fxBrauer_hasCupClassTConnect`,
`fxBrauer_hasBasePermuteBridge`, `fxBrauer_hasThroughStrandPermPerm`) and the r24 CAP class
(`fxBrauer_hasTConnectCapClass`); and EVERY master wall — the THROUGH GENERAL (`fxBrauer_hasThroughClassGeneral`, the
five-phase WELD), the through-strand T-CONNECT (`fxBrauer_hasTConnectThroughWall`), the E3 fold alignment
(`fxBrauer_hasFoldAlignmentE3`), the honest six-phase assembly (`fxBrauer_hasFoldTargetHonestAssembly`), the
tag-correspondence and completeness masters — is `false`.  A `rfl`-conjunction: r27 CLOSED the single new THROUGH crux
and its P1 decode leg, but the P2–P5 node-survival weld is unbuilt, so no master flip is fabricated and #2013 does NOT
close — the five-phase WELD then T-CLOSE(b) is the r28 endgame. -/
theorem fxBrauer_r27GrandLedger :
    (fxBrauer_hasThroughStrandRoundtrip = true
      ∧ fxBrauer_hasThroughReadOffFoot = true
      ∧ fxBrauer_hasThroughWidth12Probe = true)
    ∧ (fxBrauer_hasRankPositionDuality = true
      ∧ fxBrauer_hasCupClassTConnect = true
      ∧ fxBrauer_hasTConnectCapClass = true)
    ∧ (fxBrauer_hasBasePermuteBridge = true
      ∧ fxBrauer_hasThroughStrandPermPerm = true)
    ∧ (fxBrauer_hasThroughClassGeneral = false
      ∧ fxBrauer_hasTConnectThroughWall = false)
    ∧ (fxBrauer_hasFoldAlignmentE3 = false
      ∧ fxBrauer_hasFoldTargetHonestAssembly = false)
    ∧ (fxBrauer_hasTagCorrDisjoint = false
      ∧ fxBrauer_hasTagCorrExtraction = false)
    ∧ (fxBrauer_hasBrauerV2FullCompleteness = false
      ∧ fxBrauer_hasBrauerCompleteness = false
      ∧ fxBrauer_hasFreeBrauerStraighteningNF = false) :=
  ⟨⟨rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl⟩, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩, ⟨rfl, rfl, rfl⟩⟩

/-- **Honesty marker — BRAUER r27 did NOT close #2013.**  r27 CLOSED the THROUGH per-arc chain's single genuinely-new
lemma — the ROUNDTRIP CRUX (`throughStrandBottoms_getAt_arcMiddleCountBelow`, the recon risk pole) — and shipped its P1
decode leg (`throughReadOffBottom_reads_throughFoot`) general, consuming the crux in the fold read-off.  But the THROUGH
GENERAL's five-phase node-survival WELD (P2 cap-survival read, P3 middle tracker, P4 cup-survival read, P5 top tracker +
keystone, the trans/flip weld) is named, not built (`fxBrauer_hasThroughClassGeneral = false`), so the all-class
T-CONNECT does not close, `extractDiagram F = d` does not close, and the tag-correspondence / completeness masters stay
`false`.  Every residual a ROUTE gap, never a truth gap (the THROUGH connectivity is probed general-shape-true at
boundary 12; the crux and P1 decode are now general).  The r28 endgame: the five-phase WELD (all ingredients shipped)
then T-CLOSE(b).  `= false`. -/
def fxBrauer_hasBrauerR27Complete : Bool := false

end FX1Poly.Polygraph
