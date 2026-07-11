import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescTConnectCapChainLedger
import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescBasePermuteBridge
import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescThroughStrandPerm

/-! # BRAUER r25 — GAP β + GAP γ-witness + the CUP join-site reductions, and the exact #2013 ledger

r25 ships three NEW ingredient markers, each machine-checked zero-axiom, none flipping a master:

  * **GAP β — the base-permute bridge** (`fxBrauer_hasBasePermuteBridge`, `WiringDescBasePermuteBridge`).
    `natListGetAt_foldlAdjacentSwapBase`: reading the abstract adjacent-swap fold over ANY base at an in-range index
    equals reading the base at the permuted index `natListGetAt (permuteOfCrossingWord base.length positions) index`.
    The MAP-fusion route (naturality of the swap under `map`, boundedness firing once); the CUP `topPerm` and THROUGH
    `middle` / `topPerm` positional bridge on POST-cup / POST-cap NON-seed states — the seed-only CAP chain never
    needed it.

  * **GAP γ (witness) — `throughStrandPerm` is a range-permutation** (`fxBrauer_hasThroughStrandPermPerm`,
    `WiringDescThroughStrandPerm`).  `throughStrandPerm_isPermutationOfRange`: DISTINCT (rank injectivity from
    `arcMiddleCountBelow` strict-monotone-on-members), of the right LENGTH (the r17 through-count symmetry), BOUNDED
    (shipped) — so the corrected `middle` block decodes to it (`correctedMiddle_decodesReadOff`) through the shipped
    conjugator roundtrip.  The ledger implied the whole roundtrip was unbuilt; only the `isDistinct` field was genuine
    new content.

  * **The CUP / THROUGH join-site matching reductions** (`fxBrauer_hasTopTopMatchingReduction`,
    `WiringDescTConnectCapClass`).  `matchingSameComponent_topTop_eq_isSameComponent` /
    `matchingSameComponent_bottomTop_eq_isSameComponent`: the top–top and bottom–top analogs of the shipped
    bottom–bottom cap reduction, reducing each CUP / THROUGH arc's `partnerShares` to open-wire node connectivity.

## B4 — the ALL-CLASS T-CONNECT stays WALLED; no master is flipped

The general per-arc T-CONNECT needs, for every well-formed boundary involution, the per-arc `partnerShares` in ALL FOUR
boundary classes.  Only the CAP class is general (r24 `capArcMatching_general` + `partnerIndexOf_readsCapArc_general`).
The remaining classes are BUILT no further than their join-site reductions (r25) + concrete probes:

  * **CUP** — the connectivity BUILD needs a six-phase `foldFactorsThroughCup` factor (exposing `topPerm` as the trailing
    crossing word), the fresh cup-pair join (`capThenCupFold_connects_survivesTail`, shipped) surfaced at the top ports
    via the interior tracker + GAP β, and the `permInverse` cup-rank arithmetic locating the cup ranks through
    `correctedTopPerm_decodesInverseReadOff` + a NEW `expandCupTopPairs_getAt_fst/_snd` kit.  The exact jammed goal:
    `matchingSameComponent d.bottomCount F (d.bottomCount + cupTopA) (d.bottomCount + cupTopB) = true` for each cup arc.
    Probed general-shape-true on the NESTED (r24) and the FRESH INTERLEAVED (r25 `cupChainJoinProbe_interleavedCups`,
    join `(true, true, false)`) diagrams; the general BUILD is UNBUILT (the `permInverse` cup-rank arithmetic).

  * **THROUGH** — additionally needs the 5-phase node-identity assembly threading a bottom rank through
    `throughStrandPerm` (now a decodable range-permutation, GAP γ), the cup-preserved position, and `topPerm`⁻¹.  Probed
    on adversarial-B (r24 `throughChainProbe_adversarialB`); the general BUILD is UNBUILT.

  * The boundary-index CLASSIFIER (each `i < d.bottomCount + d.topCount` with `partner i ≠ i` is exactly one of
    cap-foot / through-bottom / through-top / cup-end, decidable by two `Nat.blt`s) is trivial and would only dispatch
    the four class chains — not built as a decl because three of the four chains it dispatches are unbuilt.

So `fxBrauer_hasTConnectThroughWall`, `fxBrauer_hasFoldAlignmentE3`, `fxBrauer_hasFoldTargetHonestAssembly`, the
tag-correspondence masters and the completeness masters all stay `false`.  **#2013 does NOT close; T-ENUM / E3 stays the
r26 target** — the CUP `foldFactorsThroughCup` + `permInverse` cup-rank arithmetic and the THROUGH 5-phase assembly are
the two named residuals.  NO flip is fabricated.

Raw Lean 4 + Init; a `rfl`-conjunction the kernel checks.  Per-declaration `#assert_no_axioms` in the audit twin;
independent `#print axioms` clean. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-- ★★★ **THE BRAUER r25 GAP LEDGER — MACHINE-CHECKED.**  The three NEW r25 ingredient markers (GAP β base-permute
bridge, GAP γ `throughStrandPerm` range-permutation witness, the CUP / THROUGH join-site matching reductions) are
`true`, on top of the r24 general CAP-class T-CONNECT + its routed read-off; and EVERY master wall — the through-strand
per-arc T-CONNECT (`fxBrauer_hasTConnectThroughWall`, still walled by the CUP `foldFactorsThroughCup` + `permInverse`
cup-rank arithmetic and the THROUGH 5-phase assembly), the E3 fold alignment (`fxBrauer_hasFoldAlignmentE3`), the honest
six-phase assembly (`fxBrauer_hasFoldTargetHonestAssembly`), the tag-correspondence masters, and the completeness
masters — is `false`.  A `rfl`-conjunction: r25 de-risked and BUILT the two named gaps' witnesses (β full, γ the
IsPermutationOfRange) and the CUP join-site reductions, but the CUP / THROUGH connectivity BUILDS are unbuilt, so no
master flip is fabricated and #2013 does NOT close — T-ENUM / E3 stays the r26 target. -/
theorem fxBrauer_r25GapLedger :
    (fxBrauer_hasBasePermuteBridge = true
      ∧ fxBrauer_hasThroughStrandPermPerm = true
      ∧ fxBrauer_hasTopTopMatchingReduction = true)
    ∧ (fxBrauer_hasTConnectCapClass = true
      ∧ fxBrauer_hasTConnectCapClassRouted = true)
    ∧ (fxBrauer_hasTConnectThroughWall = false
      ∧ fxBrauer_hasFoldAlignmentE3 = false
      ∧ fxBrauer_hasFoldTargetHonestAssembly = false)
    ∧ (fxBrauer_hasTagCorrDisjoint = false
      ∧ fxBrauer_hasTagCorrExtraction = false)
    ∧ (fxBrauer_hasBrauerV2FullCompleteness = false
      ∧ fxBrauer_hasBrauerCompleteness = false
      ∧ fxBrauer_hasFreeBrauerStraighteningNF = false) :=
  ⟨⟨rfl, rfl, rfl⟩, ⟨rfl, rfl⟩, ⟨rfl, rfl, rfl⟩, ⟨rfl, rfl⟩, ⟨rfl, rfl, rfl⟩⟩

/-- **Honesty marker — BRAUER r25 did NOT close #2013.**  r25 shipped the two named gaps' witnesses (GAP β base-permute
bridge in full; GAP γ the `throughStrandPerm` `IsPermutationOfRange` + `middle` decode) and the CUP / THROUGH join-site
matching reductions — each zero-axiom, each a NEW ingredient flipping NO master.  The CUP connectivity BUILD
(`foldFactorsThroughCup` + the `permInverse` cup-rank arithmetic) and the THROUGH 5-phase node-identity assembly remain
named, not built, so the all-class T-CONNECT does not close, `extractDiagram F = d` does not close, and both
tag-correspondence masters and the completeness flags stay `false`.  Every residual a ROUTE gap, never a truth gap
(each blocked chain is probed general-shape-true).  `= false`. -/
def fxBrauer_hasBrauerR25Complete : Bool := false

end FX1Poly.Polygraph
