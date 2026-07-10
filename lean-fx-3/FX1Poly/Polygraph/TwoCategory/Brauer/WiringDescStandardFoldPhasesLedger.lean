import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescStandardFoldPhases
import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescCorrectedLedger

/-! # BRAUER-MIDDLE r4 B4 — THE LEDGER: the machine-checked terminal state + the NAMED R3-A-PROOF residual node

This is the honest terminal ledger for the BRAUER-MIDDLE r4 round (#2013).  The round SHIPPED, zero-axiom, ONE
brick that advances the r3 state toward the R3-A roundtrip PROOF:

  * **B1 — the cup / cap PHASE-FOLD connectivity inductions** (`fxBrauer_hasCupCapPhaseFolds = true`).  The R3-A
    roundtrip PROOF (`standardFormDiagramExt5 (reconstructStandardFormExt5Corrected d) = d`) reduces — exactly as the
    FROB spider realization reduced to `spiderPartition_of_allConnected` — to a `stepWiring`-connectivity structural
    induction over the six-phase standard-form fold (three crossing phases + cap + cup + circle).  This round builds
    the two genuinely NEW phase folds FROB's comb lacked: `stepWiring_cup_head` (`0 ⇒ 2`) / `stepWiring_cap_head`
    (`2 ⇒ 0`) are the phase-atom lemmas, and `capFold_consumes` / `cupFold_creates` fold them into the cap-consumption
    and cup-creation phase inductions (the Brauer analogs of FROB's `mergeFold_connects_all` / `fanFold_connects`),
    each zero-axiom and structural, cross-checked FIRING on the concrete pure-cap / pure-cup instances
    (`capFold_consumes_twoCaps` / `cupFold_creates_twoCups` / `cupFold_twoCups_diagram`).

The round did NOT close R3-A-PROOF, let alone #2013.  The two phase folds are the position-0 cup / cap atoms —
directly load-bearing for the through-strand-free subclass (`throughBottoms.length = 0`) — but the R3-A roundtrip
still needs the general interior-position fold, the crossing-phase composition (`processBrauer_append` with the
already-proven `stateIsPermGraph` / `extractDiagram_eq_permutationDiagram_ofPermGraph`), and above all the TAG
CORRESPONDENCE (that `capArcFeet` / `throughStrandPerm` / `cupArcTops` / `permInverse` actually enumerate `d`'s arcs
in the order the phases consume / produce them — the read-off-correctness long pole with no FROB analog).  So
`fxBrauer_hasExt5CorrectedRoundtripProof` / `fxBrauer_hasExt5TotalExtractorRoundtrip` STAY `false` (no flip is
fabricated), and `fxBrauer_hasBrauerV2FullCompleteness` / `fxBrauer_hasBrauerCompleteness` STAY `false`; #2013 does
not close.  Per the 110-percent directive the residual is a ROUTE / totality gap, NEVER a truth gap (Lehrer–Zhang
arXiv:1207.5889 Thm 2.6 guarantees the presentation is complete, and the corrected extractor's exhaustive size-8
readback makes the roundtrip's TRUTH concrete).

## The sharpened R3-A wall — the phase folds shipped, three legs remaining, machine-checked `false`

Discharging `fxBrauer_hasExt5CorrectedRoundtripProof` (the R3-A-PROOF node) now needs, on top of the shipped phase
folds:

  * **R3-A-CROSSING-GLUE**: compose the three crossing phases (already a solved permutation/connectivity induction)
    with the cap / cup phase folds via `processBrauer_append` — the six-phase split assembly (FROB's
    `canonicalSpiderFold_connected` analog).
  * **R3-A-TAGCORR** (the long pole): the tag correspondence — that the read-offs enumerate `d`'s arcs in fold order,
    closed against `d` by the Brauer analog of `extractDiagram_eq_of_connectivityView`.  No FROB analog (FROB's target
    had no per-arc structure).
  * **R3-A-INTERIOR**: the interior-position cup / cap fold generalizing the shipped position-0 folds to the
    `throughBottoms.length`-offset cup block the standard form uses when through-strands are present.

Raw Lean 4 + Init.  Per-declaration `#assert_no_axioms` in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## The grand r4 ledger — one machine-checked terminal state -/

/-- ★★★ **The BRAUER-MIDDLE r4 GRAND LEDGER — MACHINE-CHECKED.**  The B1 shipped marker (the cup / cap phase-fold
connectivity inductions) is `true`, and every wall — the R3-A-PROOF roundtrip node, the r3 residual nodes (still
open), and the master V2 / connectivity completeness flags — is `false`.  A `rfl`-conjunction the kernel checks over
the shipped markers: the round shipped the two new phase folds (the FROB-shaped R3-A machinery), but the roundtrip
proof is not assembled, so #2013 does NOT close and no master flip is fabricated. -/
theorem fxBrauer_r4GrandLedger :
    fxBrauer_hasCupCapPhaseFolds = true
    ∧ (fxBrauer_hasExt5CorrectedRoundtripFromPhaseFolds = false
      ∧ fxBrauer_hasExt5CorrectedRoundtripProof = false
      ∧ fxBrauer_hasExt5TotalExtractorRoundtrip = false)
    ∧ (fxBrauer_hasStagedInnerDescentDischarged = false
      ∧ fxBrauer_hasCorrectedFoldDischarged = false)
    ∧ (fxBrauer_hasBrauerV2FullCompleteness = false
      ∧ fxBrauer_hasBrauerCompleteness = false
      ∧ fxBrauer_hasFreeBrauerStraighteningNF = false) :=
  ⟨rfl, ⟨rfl, rfl, rfl⟩, ⟨rfl, rfl⟩, ⟨rfl, rfl, rfl⟩⟩

/-! ## The terminal honesty marker -/

/-- ★★ **Honesty marker — BRAUER-MIDDLE r4 did NOT close #2013 (the honest wall, R3-A phase machinery shipped).**
The round shipped the two new Brauer cup / cap phase-fold connectivity inductions (B1) — the `0 ⇒ 2` /  `2 ⇒ 0`
phase-atom lemmas FROB's comb lacked and their cap-consumption / cup-creation folds — each zero-axiom and structural,
cross-checked firing on concrete instances.  This is the load-bearing new mathematics the R3-A roundtrip needs, in
the exact FROB shape.  But the six-phase assembly (crossing-glue), the interior-position fold, and above all the tag
correspondence (the read-off-correctness long pole) are unbuilt, so `fxBrauer_hasExt5CorrectedRoundtripProof` /
`fxBrauer_hasExt5TotalExtractorRoundtrip` stay `false`, the masters stay `false`, and #2013 does not close.  The
exact wall is R3-A-CROSSING-GLUE ∧ R3-A-TAGCORR ∧ R3-A-INTERIOR (then, above R3-A, still R3-B-INNER ∧ R3-C-DRIVER) —
every one a ROUTE / totality gap, never a truth gap.  `= false`. -/
def fxBrauer_hasBrauerMiddleR4Complete : Bool := false

end FX1Poly.Polygraph
