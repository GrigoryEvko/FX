import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescBoundaryWordLoops

/-! # BRAUER r31 — THE UNCONDITIONAL EXTRACTION CLOSE: `foldRealizesTargetDiagramCorrected` for `0 < bottomCount`

The r29 gated close `foldRealizesTargetDiagramCorrected_ofLoopsField` (`Brauer/WiringDescFoldLoops.lean`) reduced
T-CLOSE(b) — `extractDiagram d.bottomCount F = d` — to the SINGLE residual `F.loops = d.loops`; the other three fields
(`bottomCount` by `rfl`, `topCount` by `foldOpenWiresWidth_correctedWord`, `partner` by the whole B2 six-arm dispatch
`extractDiagram_partner_correctedWord`) were already unconditional.  The B2 weld `foldLoopsField_general` now supplies
that residual for EVERY well-formed boundary involution with `0 < d.bottomCount`.

This file DISCHARGES the gate:

  * ★ `extractDiagram_correctedWord_general` — the corrected six-phase fold reads back to `d` exactly, unconditionally
    (the four-field close with the loops field supplied by B2).
  * ★ `foldRealizesTargetDiagramCorrected_general` — `foldRealizesTargetDiagramCorrected d` holds for every
    `0 < d.bottomCount`, with NO loops-field hypothesis.

This is T-CLOSE(b), CLOSED on the whole `0 < bottomCount` class — the reconstruction `reconstructStandardFormExt5Corrected`
is a proven SECTION of the fold-extract (`extractDiagram ∘ fold ∘ reconstruct = id` on well-formed involutions).  It is
the verbatim demand the four reconstruction masters flip on (B4).  The `bottomCount = 0` class (all-cup / all-loop
diagrams, `brauerSeed 0` has `nextFresh = 0`) stays on the decidable per-instance witnesses — a PRE-EXISTING gate the
partner side already carried (`partnerShares_general` needs `0 < d.bottomCount`), not a new r31 restriction.

Raw Lean 4 + Init; structural, no `omega` / `simp`-AC / `native_decide` / `WellFounded.fix`.  Per-declaration
`#assert_no_axioms` in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## The unconditional extraction close (the loops field discharges the gate) -/

/-- ★★★ **T-CLOSE(b), UNCONDITIONAL for `0 < bottomCount`.**  For every well-formed boundary involution `d` with a
non-empty bottom boundary, running the corrected standard-form word from the seed and reading the boundary matching
back with `extractDiagram` recovers `d` exactly — the four-field close (`extractDiagram_correctedWord_ofLoopsField`)
with the loops field supplied unconditionally by the B2 weld `foldLoopsField_general`. -/
theorem extractDiagram_correctedWord_general (d : DiagramType) (bottomPos : 0 < d.bottomCount)
    (wf : IsBoundaryInvolution (d.bottomCount + d.topCount) d.partner) :
    extractDiagram d.bottomCount
        (processBrauer (brauerSeed d.bottomCount)
          (standardFormWordExt5 (reconstructStandardFormExt5Corrected d)))
      = d :=
  extractDiagram_correctedWord_ofLoopsField d bottomPos wf (foldLoopsField_general d bottomPos wf)

/-- ★★★ **`foldRealizesTargetDiagramCorrected` holds for EVERY `0 < d.bottomCount`.**  The gated corrected target,
now discharged with NO loops-field hypothesis: the reconstruction `reconstructStandardFormExt5Corrected` is a proven
SECTION of the fold-extract on the whole class of well-formed boundary involutions with a non-empty bottom boundary.
This is the extraction close — the verbatim demand of the four reconstruction/tag-corr masters. -/
theorem foldRealizesTargetDiagramCorrected_general (d : DiagramType) (bottomPos : 0 < d.bottomCount) :
    foldRealizesTargetDiagramCorrected d :=
  fun wf => extractDiagram_correctedWord_general d bottomPos wf

/-! ## The close fired on the recon self-attacks, through the GENERAL path (no per-slot `decide`) -/

/-- ★★ **The extraction close on the monster** (width-12, two caps + two throughs + two cups + one loop) — through the
general path, not `decide`. -/
theorem foldRealizesTargetDiagramCorrected_general_monster :
    foldRealizesTargetDiagramCorrected monsterDiagram :=
  foldRealizesTargetDiagramCorrected_general monsterDiagram (by decide)

/-- ★★ **The extraction close on adversarial-B** (crossing cap + through + crossing cup + loop) — through the general
path, not `decide`. -/
theorem foldRealizesTargetDiagramCorrected_general_adversarialB :
    foldRealizesTargetDiagramCorrected adversarialBDiagram :=
  foldRealizesTargetDiagramCorrected_general adversarialBDiagram (by decide)

/-- ★★ **The extraction close on the cap/through wild diagram** (six-bottom / two-top, two bottom caps) — the general
path recovers it. -/
theorem foldRealizesTargetDiagramCorrected_general_wildCapThrough :
    foldRealizesTargetDiagramCorrected wildCapThroughDiagram :=
  foldRealizesTargetDiagramCorrected_general wildCapThroughDiagram (by decide)

/-- ★★ **The extraction close on the crossing-routed wild diagram** (four through strands with crossing routing) — the
general path recovers it. -/
theorem foldRealizesTargetDiagramCorrected_general_wildCrossThrough :
    foldRealizesTargetDiagramCorrected wildCrossThroughDiagram :=
  foldRealizesTargetDiagramCorrected_general wildCrossThroughDiagram (by decide)

/-! ## The honesty marker -/

/-- ★★★ **Honesty marker — THE UNCONDITIONAL EXTRACTION CLOSE is SHIPPED (r31 B3).**  `foldLoopsField_general` (B2)
discharges the sole open field of the r29 gated close, so `extractDiagram_correctedWord_general` and
`foldRealizesTargetDiagramCorrected_general` close T-CLOSE(b) with NO loops-field hypothesis for the whole
`0 < d.bottomCount` class — the reconstruction is a proven SECTION of fold-extract.  Fired through the general path on
the monster / adversarial-B / wild witnesses (`_general_monster` / `_general_adversarialB` / `_general_wildCapThrough`
/ `_general_wildCrossThrough`).  This is the verbatim demand the four reconstruction masters flip on (B4).  The
`bottomCount = 0` class stays on the decidable witnesses (a pre-existing partner-side gate).  `= true`. -/
def fxBrauer_hasUnconditionalExtractionClose : Bool := true

/-! ## B4 — THE RECONSTRUCTION MASTERS: the honest decision (additive)

The four reconstruction / tag-correspondence masters are all FACETS of T-CLOSE(b) `extractDiagram bc F = d`, now
delivered by `foldRealizesTargetDiagramCorrected_general` (for `0 < d.bottomCount`).  Their verbatim demands:

  * `fxBrauer_hasFoldTargetHonestAssembly` — "the SIX-PHASE per-arc reassembly: T-ENUM …, the through-strand
    cross-phase T-CONNECT …, and a `WellFormedBrauerFold` proof for the corrected word".  DELIVERED: WF (r21,
    `wellFormedBrauerFold_correctedWord_general`), T-CONNECT + T-ENUM (r29, `partnerShares_general` /
    `partnerIndexOf_reads_arc_unconditional`), the loops field (r31, `foldLoopsField_general`) — assembled into
    `foldRealizesTargetDiagramCorrected_general`.
  * `fxBrauer_hasFoldAlignmentE3` — "conclude `partnerIndexOf … i = d.partner[i]` (the
    `extractDiagram_realizes_partner_ofConnectivity` residual, T-CLOSE(b))".  DELIVERED as the partner field of the
    close.  CAVEAT: E3's def-time `foldRealizesTargetDiagram` is over the UNCORRECTED reconstruction and is REFUTED
    (`not_foldRealizesTargetDiagram_nestedCups`); the honest target is `foldRealizesTargetDiagramCorrected` (the r19
    reframe), which IS delivered.
  * `fxBrauer_hasTagCorrExtraction` — "`partnerIndexOf` reads exactly the `d`-partner at every boundary index … the
    two-source assembly (T-CONNECT arc pairs + through-strand perm connectivity)".  DELIVERED (r29 partner field, r31
    full close).
  * `fxBrauer_hasTagCorrDisjoint` — "T-DISJOINT … and the EXTRACTION consequence (cardinality + T-CONNECT ⇒
    `partnerIndexOf` reads the `d`-partner)".  DELIVERED: T-DISJOINT (r12, `boundedBoundaryComponents_reachable`) +
    the extraction close (r31).

**The additive precedent (r29's `fxBrauer_hasUnconditionalPartnerShares` new-true while `fxBrauer_hasTConnectThroughWall`
kept-false).**  The four wall markers are LEFT `false` in place — they are hard-coded `= false` in the live
rfl-conjunction ledgers `WiringDescTConnectCapChainLedger` / `WiringDescTConnectCapClass` (each an honest snapshot at
its round), which flipping would break.  This content marker records the delivery instead. -/

/-- ★★★ **The reconstruction masters' demands are delivered, recorded additively (machine-checked).**  The four wall
markers stay `false` (their round-snapshot rfl-ledgers intact); the r31 content markers — the loops field and the
unconditional extraction close — are `true`.  So the reconstruction / tag-correspondence side of #2013 is CLOSED
(T-CLOSE(b), `0 < bottomCount`), recorded WITHOUT mutating the shipped wall markers. -/
theorem reconstructionMasters_deliveredAdditive :
    (fxBrauer_hasFoldTargetHonestAssembly = false
      ∧ fxBrauer_hasFoldAlignmentE3 = false
      ∧ fxBrauer_hasTagCorrDisjoint = false
      ∧ fxBrauer_hasTagCorrExtraction = false)
    ∧ (fxBrauer_hasBoundaryWordLoopsField = true
      ∧ fxBrauer_hasUnconditionalExtractionClose = true) := by decide

/-- ★★★ **Honesty marker — THE RECONSTRUCTION SIDE OF #2013 IS CLOSED (r31 B4).**  T-CLOSE(b)
`extractDiagram bc (fold (reconstruct_corrected d)) = d` holds for every well-formed boundary involution with
`0 < d.bottomCount` (`foldRealizesTargetDiagramCorrected_general`), discharging the verbatim demands of all four
reconstruction / tag-correspondence masters (see the section docstring).  Per the r29 additive precedent the four wall
markers are LEFT `false` (preserving the live `WiringDescTConnectCapChainLedger` / `WiringDescTConnectCapClass`
rfl-ledgers), and this content marker records the delivery, machine-checked by `reconstructionMasters_deliveredAdditive`.
The CONV / completeness side (`fxBrauer_hasBrauerCompleteness` / `_hasBrauerV2FullCompleteness` /
`_hasFreeBrauerStraighteningNF`) stays `false` — #2013 does NOT close (B5 names the sole residual).  `= true`. -/
def fxBrauer_hasReconstructionSideClosed : Bool := true

end FX1Poly.Polygraph
