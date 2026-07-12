import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescExtractionClose
import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescWithCapValidInvolutionScope

/-! # BRAUER r54 — R3-A ATTACK ROUND ONE: the ROUNDTRIP BRIDGE — the r31 close surfaced at the wall marker's
verbatim phrasing, census-decoded to the r53 valid-involution arena (the FIRST TRANCHE; the master does NOT flip)

The R3-A wall marker `fxBrauer_hasExt5CorrectedRoundtripProof` (`Brauer/WiringDescArcExtractorRec.lean:217`) and its
prose ("the roundtrip `standardFormDiagramExt5 (reconstructStandardFormExt5Corrected d) = d` is a TRUE theorem — but
its PROOF is the `stepWiring`-connectivity structural induction … unbuilt") is STALE: that induction was built across
r21–r31 and shipped as `extractDiagram_correctedWord_general` (`Brauer/WiringDescExtractionClose.lean:37`), machine-
checked axiom-clean.  The gap is only in the PHRASING — the r31 close reads over `extractDiagram d.bottomCount
(processBrauer (brauerSeed d.bottomCount) (standardFormWordExt5 …))`, while the marker asks for
`standardFormDiagramExt5 (reconstructStandardFormExt5Corrected d) = d`.  These are DEFINITIONALLY the same LHS:

    standardFormDiagramExt5 form              := brauerDiagramOf form.bottomCount (standardFormWordExt5 form)   (r2)
    brauerDiagramOf bc atoms                  := extractDiagram bc (processBrauer (brauerSeed bc) atoms)        (WP-BRAUER-2)
    (reconstructStandardFormExt5Corrected d).bottomCount = d.bottomCount                                        (rfl)

so `standardFormDiagramExt5 (reconstructStandardFormExt5Corrected d)` reduces to the r31 close's LHS by `rfl`.

## What this file ships (the FIRST TRANCHE — each probed by `#eval` BEFORE proof, fired on concrete instances, zero-axiom)

  * ★★★ **Brick A — the marker-bridge** `ext5CorrectedRoundtrip_ofPos`: for `0 < d.bottomCount` and a boundary
    involution `d`, the marker's VERBATIM roundtrip `standardFormDiagramExt5 (reconstructStandardFormExt5Corrected d)
    = d`, proven by one application of `extractDiagram_correctedWord_general` (the LHS unfolds by `rfl`).
  * ★★ **Brick B — the census bridge** `isBoundaryInvolution_ofValidCensus`: the r53 Bool census `isInvolutionPartner`
    (`Brauer/WiringDescWithCapValidInvolutionScope.lean:84`), plus a boundary-length equation, DECODES to the Prop
    `IsBoundaryInvolution`.  Structural over `List.all`/`List.range`/`Nat.beq`/`Nat.blt` (propext-free micro-helpers
    reconstructed locally; the shipped versions are `private`).  Combined into the payoff
    `ext5CorrectedRoundtrip_ofValidCensus`: the roundtrip holds for EVERY `0 < d.bottomCount` diagram whose partner
    passes the r53 census — the roundtrip stated in the lane's own valid-involution vocabulary.
  * ★★ **the tranche FIRED on concrete instances** — the with-cap ENTANGLED monster (two caps + two throughs + two
    cups + one loop, width 12), adversarial-B (crossing cap + through + crossing cup + loop), wild cap/through (two
    bottom caps), wild cross/through (crossing routing) — each roundtrips through BOTH entry points (the `_ofPos`
    involution path and the `_ofValidCensus` census path).
  * ★ **the sole residual, pinned honestly** — the `bottomCount = 0` class (`nestedCupsDiagram`): it roundtrips
    COMPUTATIONALLY (`ext5CorrectedRoundtrip_nestedCups_decide` by `decide`) but the general path is gated on
    `0 < bottomCount` (`brauerSeed 0` has `nextFresh = 0`, the r31 `boundedBoundaryComponents_reachable` gate).  Named
    for r55 (Route D-pad: insert one bottom through-strand, reuse the frozen `0 < bc` stack, strip).
  * ★ **content markers** — `fxBrauer_hasExt5CorrectedRoundtripPosBottom` (the delivery, `= true`) and the terminal
    state pinning the R3-A wall marker byte-intact `false`.

## The honesty ledger (the FLIP LAW)

`fxBrauer_hasExt5CorrectedRoundtripProof` stays `false` (byte-intact in `WiringDescArcExtractorRec.lean`): it flips
ONLY on the COMPLETE structural roundtrip — every class, `bottomCount = 0` INCLUDED — which this partial tranche does
NOT supply.  The truth-probes (`#eval`) all came back TRUE (no invariant refuted this round); the deliverables are
BRIDGES surfacing the already-won `0 < bc` induction, not a new induction.  r55 owns the `bottomCount = 0` reduction
(and, if desired, the census-bridge CONVERSE `IsBoundaryInvolution → isInvolutionPartner`, stated below as a residual).

Raw Lean 4 + Init.  Per-declaration `#assert_no_axioms` in the audit twin + an independent `#print axioms` witness. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## Propext-free micro-helpers (structural; the shipped versions are `private` to their files) -/

/-- Left projection of a true boolean conjunction — full-enum `Bool` match, propext-free. -/
private theorem boolAndLeftBridge : (leftFlag rightFlag : Bool) → (leftFlag && rightFlag) = true → leftFlag = true
  | true, _, _ => rfl
  | false, _, conj => Bool.noConfusion conj

/-- Right projection of a true boolean conjunction. -/
private theorem boolAndRightBridge : (leftFlag rightFlag : Bool) → (leftFlag && rightFlag) = true → rightFlag = true
  | true, _, conj => conj
  | false, _, conj => Bool.noConfusion conj

/-- `not flag = true → flag = false` — full-enum `Bool` match. -/
private theorem boolFalseOfNotTrueBridge : (flag : Bool) → not flag = true → flag = false
  | true, conj => Bool.noConfusion conj
  | false, _ => rfl

/-- `Nat.ble a b = true → a ≤ b` — structural on `a`. -/
private theorem natLeOfBleBridge : (a b : Nat) → Nat.ble a b = true → a ≤ b
  | 0, _, _ => Nat.zero_le _
  | _ + 1, 0, conj => Bool.noConfusion conj
  | a + 1, b + 1, conj => Nat.succ_le_succ (natLeOfBleBridge a b conj)

/-- `Nat.blt a b = true → a < b`. -/
private theorem natLtOfBltBridge (a b : Nat) (conj : Nat.blt a b = true) : a < b :=
  natLeOfBleBridge (a + 1) b conj

/-- `Nat.beq a b = true → a = b` — structural on both operands. -/
private theorem natEqOfBeqBridge : (a b : Nat) → Nat.beq a b = true → a = b
  | 0, 0, _ => rfl
  | 0, _ + 1, conj => Bool.noConfusion conj
  | _ + 1, 0, conj => Bool.noConfusion conj
  | a + 1, b + 1, conj => congrArg (· + 1) (natEqOfBeqBridge a b conj)

/-- `Nat.beq n n = true` — structural on `n`. -/
private theorem natBeqSelfBridge : (n : Nat) → Nat.beq n n = true
  | 0 => rfl
  | n + 1 => natBeqSelfBridge n

/-- `Nat.beq a b = false → a ≠ b` — via the self-`beq`. -/
private theorem natNeOfBeqFalseBridge (a b : Nat) (beqFalse : Nat.beq a b = false) : a ≠ b := by
  intro isEqual
  subst isEqual
  rw [natBeqSelfBridge a] at beqFalse
  exact Bool.noConfusion beqFalse

/-- Membership in `acc` survives the range-loop fold. -/
private theorem memRangeLoopOfMemAccBridge : (count : Nat) → (acc : List Nat) → (value : Nat) →
    value ∈ acc → value ∈ List.range.loop count acc
  | 0, _, _, memAcc => memAcc
  | count + 1, acc, value, memAcc =>
      memRangeLoopOfMemAccBridge count (count :: acc) value (List.Mem.tail count memAcc)

/-- Every index below `count` occurs in `List.range.loop count acc`. -/
private theorem memRangeLoopOfLtBridge : (count : Nat) → (acc : List Nat) → (index : Nat) → index < count →
    index ∈ List.range.loop count acc
  | 0, _, index, isBelow => absurd isBelow (Nat.not_lt_zero index)
  | count + 1, acc, index, isBelow => by
      cases Nat.lt_or_ge index count with
      | inl isBelowCount => exact memRangeLoopOfLtBridge count (count :: acc) index isBelowCount
      | inr atLeastCount =>
          have indexEq : index = count := Nat.le_antisymm (Nat.le_of_lt_succ isBelow) atLeastCount
          exact indexEq ▸ memRangeLoopOfMemAccBridge count (count :: acc) count (List.Mem.head acc)

/-- `index < count → index ∈ List.range count` — the propext-free `List.mem_range.mpr`. -/
private theorem memRangeOfLtBridge (index count : Nat) (isBelow : index < count) : index ∈ List.range count :=
  memRangeLoopOfLtBridge count [] index isBelow

/-- `List.all` decode — a true `all` yields the predicate on every member.  Structural on the list, `cases` on the
membership witness (never the iff `List.all_eq_true`, which leaks propext). -/
private theorem allTrueOfMemBridge {elementType : Type} (predicate : elementType → Bool) :
    (elements : List elementType) → elements.all predicate = true → (element : elementType) →
    element ∈ elements → predicate element = true
  | [], _, _, membership => nomatch membership
  | headElement :: remaining, allTrue, element, membership => by
      have headTrue : predicate headElement = true := boolAndLeftBridge _ _ allTrue
      have remainingTrue : remaining.all predicate = true := boolAndRightBridge _ _ allTrue
      cases membership with
      | head => exact headTrue
      | tail _ tailMembership => exact allTrueOfMemBridge predicate remaining remainingTrue element tailMembership

/-! ## Brick A — the marker-bridge: the r31 close at the wall marker's verbatim phrasing -/

/-- ★★★ **Brick A — the R3-A roundtrip at the marker's VERBATIM phrasing, for `0 < bottomCount`.**  For every
well-formed boundary involution `d` with a non-empty bottom boundary, the corrected reconstruction is a section of the
fold-extract stated exactly as the wall marker asks:
`standardFormDiagramExt5 (reconstructStandardFormExt5Corrected d) = d`.  The LHS unfolds by `rfl` to the r31 close's
LHS (`standardFormDiagramExt5 := brauerDiagramOf ·.bottomCount ·`, `brauerDiagramOf := extractDiagram · (processBrauer
(brauerSeed ·) ·)`, and `(reconstruct d).bottomCount = d.bottomCount`), so this is one application of the shipped
`extractDiagram_correctedWord_general` — the r53 lane never stated the bridge. -/
theorem ext5CorrectedRoundtrip_ofPos (d : DiagramType) (bottomPos : 0 < d.bottomCount)
    (wf : IsBoundaryInvolution (d.bottomCount + d.topCount) d.partner) :
    standardFormDiagramExt5 (reconstructStandardFormExt5Corrected d) = d :=
  extractDiagram_correctedWord_general d bottomPos wf

/-! ## Brick B — the census bridge: the r53 Bool census decodes to the Prop `IsBoundaryInvolution` -/

/-- ★★ **Brick B — the valid-involution census DECODES to `IsBoundaryInvolution`.**  The r53 Bool census
`isInvolutionPartner partner = true` (over `List.range partner.length`), plus a boundary-length equation
`partner.length = total`, yields the Prop `IsBoundaryInvolution total partner`.  Each field is read off a single
member of the `all`: `mapsInRange` from the `Nat.blt … partner.length` conjunct, `isSelfInverse` from the
`Nat.beq partner[partner[·]] ·` conjunct, `isFixedPointFree` from the `not (Nat.beq partner[·] ·)` conjunct.  This is
the FORWARD direction of the exact-iff the r53 census census-pins (`countRepresentativeRealizeXorValid = 0`); the
CONVERSE is named for r55. -/
theorem isBoundaryInvolution_ofValidCensus (partner : List Nat) (total : Nat)
    (lengthEq : partner.length = total) (census : isInvolutionPartner partner = true) :
    IsBoundaryInvolution total partner where
  hasBoundaryLength := lengthEq
  mapsInRange := by
    intro index indexBelow
    have memberProof : index ∈ List.range partner.length :=
      memRangeOfLtBridge index partner.length (lengthEq ▸ indexBelow)
    have predTrue :
        (Nat.blt (natListGetAt partner index) partner.length
          && Nat.beq (natListGetAt partner (natListGetAt partner index)) index
          && not (Nat.beq (natListGetAt partner index) index)) = true :=
      allTrueOfMemBridge _ (List.range partner.length) census index memberProof
    have bltTrue : Nat.blt (natListGetAt partner index) partner.length = true :=
      boolAndLeftBridge _ _ (boolAndLeftBridge _ _ predTrue)
    exact lengthEq ▸ natLtOfBltBridge _ _ bltTrue
  isSelfInverse := by
    intro index indexBelow
    have memberProof : index ∈ List.range partner.length :=
      memRangeOfLtBridge index partner.length (lengthEq ▸ indexBelow)
    have predTrue :
        (Nat.blt (natListGetAt partner index) partner.length
          && Nat.beq (natListGetAt partner (natListGetAt partner index)) index
          && not (Nat.beq (natListGetAt partner index) index)) = true :=
      allTrueOfMemBridge _ (List.range partner.length) census index memberProof
    have beqTrue : Nat.beq (natListGetAt partner (natListGetAt partner index)) index = true :=
      boolAndRightBridge _ _ (boolAndLeftBridge _ _ predTrue)
    exact natEqOfBeqBridge _ _ beqTrue
  isFixedPointFree := by
    intro index indexBelow
    have memberProof : index ∈ List.range partner.length :=
      memRangeOfLtBridge index partner.length (lengthEq ▸ indexBelow)
    have predTrue :
        (Nat.blt (natListGetAt partner index) partner.length
          && Nat.beq (natListGetAt partner (natListGetAt partner index)) index
          && not (Nat.beq (natListGetAt partner index) index)) = true :=
      allTrueOfMemBridge _ (List.range partner.length) census index memberProof
    have notBeqTrue : not (Nat.beq (natListGetAt partner index) index) = true :=
      boolAndRightBridge _ _ predTrue
    exact natNeOfBeqFalseBridge _ _ (boolFalseOfNotTrueBridge _ notBeqTrue)

/-- ★★ **The payoff — the roundtrip for EVERY `0 < bottomCount` valid-census diagram.**  Bricks A and B composed: a
diagram `d` with a non-empty bottom boundary, boundary-length `d.partner.length = d.bottomCount + d.topCount`, and a
passing r53 census `isInvolutionPartner d.partner` roundtrips exactly.  The roundtrip stated in the r53 lane's own
valid-involution vocabulary — the task's with-cap valid-target arena on the `0 < bc` slice. -/
theorem ext5CorrectedRoundtrip_ofValidCensus (d : DiagramType) (bottomPos : 0 < d.bottomCount)
    (lengthEq : d.partner.length = d.bottomCount + d.topCount)
    (census : isInvolutionPartner d.partner = true) :
    standardFormDiagramExt5 (reconstructStandardFormExt5Corrected d) = d :=
  ext5CorrectedRoundtrip_ofPos d bottomPos
    (isBoundaryInvolution_ofValidCensus d.partner (d.bottomCount + d.topCount) lengthEq census)

/-! ## The tranche FIRED on concrete instances (with-cap valid targets + entangled words), through both entry points -/

/-- ★★ **The ENTANGLED monster roundtrips through the involution path.**  Width-12: two bottom caps, two through
strands, two top cups, one loop — the recon self-attack #5 witness, `0 < bottomCount = 6`.  Fired through Brick A with
the shipped `monster_isBoundaryInvolution`. -/
theorem ext5CorrectedRoundtrip_monster :
    standardFormDiagramExt5 (reconstructStandardFormExt5Corrected monsterDiagram) = monsterDiagram :=
  ext5CorrectedRoundtrip_ofPos monsterDiagram (by decide) monster_isBoundaryInvolution

/-- ★★ **The monster roundtrips through the CENSUS path too** — the r53 Bool census `isInvolutionPartner` on the
monster's partner (`by decide`) drives Brick B into Brick A.  The two entry points agree on the entangled witness. -/
theorem ext5CorrectedRoundtrip_monster_viaCensus :
    standardFormDiagramExt5 (reconstructStandardFormExt5Corrected monsterDiagram) = monsterDiagram :=
  ext5CorrectedRoundtrip_ofValidCensus monsterDiagram (by decide) rfl (by decide)

/-- ★★ **Adversarial-B roundtrips through the census path.**  Crossing cap + through + crossing cup + loop,
`bottomCount = 3` — all three ∗-dual axes plus a loop in one with-cap valid target. -/
theorem ext5CorrectedRoundtrip_adversarialB :
    standardFormDiagramExt5 (reconstructStandardFormExt5Corrected adversarialBDiagram) = adversarialBDiagram :=
  ext5CorrectedRoundtrip_ofValidCensus adversarialBDiagram (by decide) rfl (by decide)

/-- ★★ **Wild cap/through roundtrips through the census path.**  Two bottom caps + two through strands over a
6-bottom / 2-top split, `bottomCount = 6`. -/
theorem ext5CorrectedRoundtrip_wildCapThrough :
    standardFormDiagramExt5 (reconstructStandardFormExt5Corrected wildCapThroughDiagram) = wildCapThroughDiagram :=
  ext5CorrectedRoundtrip_ofValidCensus wildCapThroughDiagram (by decide) rfl (by decide)

/-- ★★ **Wild cross/through roundtrips through the census path.**  Four through strands with crossing routing,
`bottomCount = 4`. -/
theorem ext5CorrectedRoundtrip_wildCrossThrough :
    standardFormDiagramExt5 (reconstructStandardFormExt5Corrected wildCrossThroughDiagram) = wildCrossThroughDiagram :=
  ext5CorrectedRoundtrip_ofValidCensus wildCrossThroughDiagram (by decide) rfl (by decide)

/-! ## The sole residual — the `bottomCount = 0` class, pinned honestly (named for r55) -/

/-- ★ **The `bottomCount = 0` residual has a non-empty bottom boundary — FALSE.**  `nestedCupsDiagram.bottomCount =
0`, so neither `ext5CorrectedRoundtrip_ofPos` nor `_ofValidCensus` (both gated on `0 < bottomCount`) reaches it: the
r31 stack's `boundedBoundaryComponents_reachable` needs `0 < nextFresh`, and `brauerSeed 0` has `nextFresh = 0`. -/
theorem nestedCups_bottomCount_zero : nestedCupsDiagram.bottomCount = 0 := rfl

/-- ★ **Yet the `bottomCount = 0` class DOES roundtrip — computationally.**  `nestedCupsDiagram` (four top ports,
fully-nested crossing cups `[3,2,1,0]`, zero bottoms) roundtrips by `decide` — the truth is KNOWN.  What is missing is
the GENERAL path for `bottomCount = 0`; r55 owns it (Route D-pad: insert one bottom through-strand to reach `bc = 1`,
reuse the frozen `0 < bc` stack, then strip the pad).  This pin is the residual class' concrete witness — the
invariant is TRUE, the route is the gap (never a truth gap). -/
theorem ext5CorrectedRoundtrip_nestedCups_decide :
    standardFormDiagramExt5 (reconstructStandardFormExt5Corrected nestedCupsDiagram) = nestedCupsDiagram := by decide

/-! ### The tranche census — FROZEN `#eval` truth-probes (run BEFORE the universals above) -/

-- The roundtrip holds on the entangled + with-cap witnesses (1 = holds; DiagramType `diagramBeq`).
#eval diagramBeq (standardFormDiagramExt5 (reconstructStandardFormExt5Corrected monsterDiagram)) monsterDiagram         -- true
#eval diagramBeq (standardFormDiagramExt5 (reconstructStandardFormExt5Corrected adversarialBDiagram)) adversarialBDiagram -- true
#eval diagramBeq (standardFormDiagramExt5 (reconstructStandardFormExt5Corrected wildCapThroughDiagram)) wildCapThroughDiagram -- true
#eval diagramBeq (standardFormDiagramExt5 (reconstructStandardFormExt5Corrected wildCrossThroughDiagram)) wildCrossThroughDiagram -- true
-- The census agrees with well-formedness on the witnesses (valid) and rejects the r53 malformed boundary-overrun target.
#eval isInvolutionPartner monsterDiagram.partner                              -- true
#eval isInvolutionPartner adversarialBDiagram.partner                        -- true
#eval isInvolutionPartner (brauerDiagramOf 6 [capAt 0, crossingAt 3, cupAt 0]).partner  -- false (malformed, r53 §C)
-- The bottomCount = 0 residual: roundtrips computationally, but the bottom boundary is empty.
#eval diagramBeq (standardFormDiagramExt5 (reconstructStandardFormExt5Corrected nestedCupsDiagram)) nestedCupsDiagram    -- true
#eval nestedCupsDiagram.bottomCount                                          -- 0

/-! ## Content markers + the honest terminal state -/

/-- ★★★ **Honesty marker — the R3-A roundtrip is DELIVERED at the wall marker's phrasing for `0 < bottomCount` (r54
first tranche).**  `ext5CorrectedRoundtrip_ofPos` proves `standardFormDiagramExt5 (reconstructStandardFormExt5Corrected
d) = d` for every well-formed boundary involution with a non-empty bottom boundary — the exact demand of the R3-A wall
marker `fxBrauer_hasExt5CorrectedRoundtripProof`, delivered by the r31 close (the marker's "unbuilt induction" prose is
STALE).  `isBoundaryInvolution_ofValidCensus` census-decodes the r53 Bool `isInvolutionPartner` into the Prop premise,
so `ext5CorrectedRoundtrip_ofValidCensus` reads the roundtrip for every `0 < bc` valid-census diagram (with-cap
included), fired on the entangled monster / adversarial-B / wild cap-through / wild cross-through.  Recorded
additively; the master wall marker is LEFT byte-intact `false` (it flips only on the complete induction, `bc = 0`
included, expected r55+).  `= true`. -/
def fxBrauer_hasExt5CorrectedRoundtripPosBottom : Bool := true

/-- ★★ **The r54 first-tranche terminal state — MACHINE-CHECKED.**  The new content marker is `true`; the R3-A wall
marker `fxBrauer_hasExt5CorrectedRoundtripProof` (`WiringDescArcExtractorRec.lean:217`), the r53 valid-involution-fold
discharge marker, and the two completeness masters ALL STAY `false` — the partial tranche does NOT flip the master
(only the COMPLETE roundtrip, `bottomCount = 0` included, does).  Same-commit `rfl`-conjunction; purely additive. -/
theorem fxBrauer_ext5CorrectedRoundtripBridgeTerminalState :
    fxBrauer_hasExt5CorrectedRoundtripPosBottom = true
      ∧ fxBrauer_hasExt5CorrectedRoundtripProof = false
      ∧ fxBrauer_hasValidInvolutionFoldDischarged = false
      ∧ fxBrauer_hasBrauerV2FullCompleteness = false
      ∧ fxBrauer_hasBrauerCompleteness = false :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-! ## The r55 bill (the remaining bricks, named)

  * **Brick D — the `bottomCount = 0` reduction (the sole residual class).**  Route D-pad: `padOneThrough d` inserts
    one bottom through-strand (adding BOTH boundary ports and shifting all top indices with reciprocal edges — the
    naive one-port pad is malformed, roundtrip `false`), reuse the frozen `0 < bc` stack on the padded diagram, then a
    STRIP lemma `extractDiagram (padded word) = pad (extractDiagram (base word))`.  On success the roundtrip is
    complete for ALL valid involutions and `fxBrauer_hasExt5CorrectedRoundtripProof` may flip (subject to the additive
    precedent).  Alternative Route D-direct: re-derive T-DISJOINT + cup-connect for the `nextFresh = 0` seed in a new
    file (additive-only forbids editing the frozen `nfPos`-gated lemmas).
  * **Brick E — the census-bridge CONVERSE** `isInvolutionPartner_ofIsBoundaryInvolution` (Prop → Bool): completes the
    exact iff the r53 census pins (`countRepresentativeRealizeXorValid = 0`), needing the `all`-builder + `Nat.blt`/
    `Nat.beq` builders (the mirror of the forward micro-helpers here). -/

end FX1Poly.Polygraph
