import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescClassRepresentativeReadjudication

/-! # BRAUER r51 — THE DOCUMENTED WALL-TEXT AMENDMENT: the r50 straw flip-criterion corrected to the
(i,j)-representative family; the amended flip law; the original wall files stay byte-intact

This file is the DOCUMENTED amendment mandated by the WALL-AMENDMENT LAW: the r50 irreducibility file's docstring
asserts a flip criterion — "reduce every survivor to a bare cup / zero cup-touching crossings" — that its OWN
unreachability theorem refutes.  That prose misidentifies the flip criterion.  The honest move is to SUPERSEDE it by
addition (a new file), never to silently reinterpret the wall.  The r50 file
(`WiringDescCupTouchingIrreducible.lean`) and the three flag files stay BYTE-INTACT; their flip flags still live at
their original sites and flip only per the AMENDED criterion once recorded.

## (a) THE ORIGINAL r50 STRAW-CRITERION PROSE, QUOTED VERBATIM

From `WiringDescCupTouchingIrreducible.lean` (the module docstring, lines 16-18):

    "The two dispatch flip flags (`fxBrauer_hasRegionDriverTotalDispatch`, owned r39;
    `fxBrauer_hasSingleCupTotalDecision`, owned r38) flip only if the iterated driver reduces EVERY single-cup survivor
    to the canonical form "cup at its slot, ZERO cup-touching crossings" and the census EMPTIES.  This round's autopsy
    proves that target is UNREACHABLE"

and (lines 60-62):

    "A single genuine driveCanonical pass therefore leaves the straddle / crossingLeft / distant residues STUCK at a
    cup-touching crossing — the census does NOT empty, and emptying it to the stated canonical form is impossible, not
    merely unbuilt."

## (b) THE UNREACHABILITY THEOREM IT PROVED (byte-intact in r50, referenced not re-derived)

`cupTouchingCrossing_notBareCup_b3` : the residue `[cupAt 1, crossingAt 0]` reads a `brauerDiagramOf 3` diagram no bare
cup `[cupAt barePos]` reads (a bounded `∀ barePos < 5`, `decide`).  This is CORRECT as a refutation of the bare-cup
target, and it stays.  What is amended is the CLAIM that the bare cup was the flip criterion.

## (c) THE CORRECTED CRITERION — the (i,j)-representative family, not the bare cup

The correct flip target is the CLASS REPRESENTATIVE of each survivor's diagram — the Kudryavtseva–Mazorchuk two-sided
sandwich `u . e_{i,j}` (arXiv:math/0511730; walled-Brauer `w_L . (cups) . w_R`, arXiv:1912.12869 eq. 1.8), realised in
FX as `classRepresentativeOf b word = standardFormWordExt5 (reconstructStandardFormExt5Corrected (brauerDiagramOf b
word))` (`WiringDescClassRepresentativeReadjudication.lean`).  Under this criterion the r50 residue `[cupAt 1,
crossingAt 0]` is NOT a stuck non-canonical form: it IS the straddle class's representative
(`straddleRepresentativeIsJamResidue`), realising its own diagram (`straddleRepresentativeRealizes`) and a fixed point
of the representative map (`straddleRepresentativeIsFixedPoint`).  The r50 "jam" is an ARRIVAL — the shipped
`correctedFold_straddle_reaches` proves the straddle `BrauerConvFree8`-reaches it by one cup-slide.  The correctness of
the criterion in general is exactly the shipped open `BrauerExt5CorrectedFoldReaches` (the r52 target).

## (d) THE FLAG WALLS ACCOMMODATE THE FAMILY AS WRITTEN — no amendment to the flag files

The three flip/wall flags never demanded the bare cup; their load-bearing phrasing is criterion-agnostic totality:

  * `fxBrauer_hasRegionDriverTotalDispatch` (`WiringDescSingleCupRegionDriver.lean:374`): the residuals are
    "(J-transport) ... `Eq.rec`/`▸` transport across the cons-indexed family; (J-loop) ... loop non-emptiness;
    (J-geometry) the straddle-then-cap ordering trap" — a synthesis/totality gap over `classifyFirstCupNeighbour`, NO
    bare cup.
  * `fxBrauer_hasSingleCupTotalDecision` (`WiringDescSingleCupPeelDriver.lean:268`): the arrival target is the
    "working-region-factored `cupHasArrived`", explicitly tolerating "a topPerm crossing left of the cup" — the
    permutation residue the (i,j)-representative carries.
  * `fxBrauer_hasSingleCupPeelDischarged` (`WiringDescCupArrivalPeel.lean:374`, a MULTI-CUP wall): the target is "the
    `DiagramType` driver" + "the `bottomCount = 0` class" — the diagram-indexed representative, not a bare cup.

So those walls accommodate the (i,j)-representative family as written; the amendment corrects ONLY the r50 autopsy
prose.

## (e) THE AMENDED FLIP LAW

A flip of a dispatch/wall flag now requires, JOINTLY: (a) the drive reaches the CLASS REPRESENTATIVE for EVERY survivor
(machine-checked per class family), AND (b) the committed census confirms full coverage, AND (c) this amendment records
the criterion mapping.  This round supplies (c) and the census (b) on the cap-free arena, but NOT (a) unconditionally
(that is the unconditional `BrauerExt5CorrectedFoldReaches`, the r52 target).  Therefore this round is the SEVENTH
honest zero-flip: the criterion is corrected, no flag is discharged.

Raw Lean 4 + Init.  Per-declaration `#assert_no_axioms` in the audit twin + an independent `#print axioms` witness. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## The amendment, machine-checked -/

/-- ★★ **THE CORRECTED CRITERION SATISFIED WHERE THE STRAW ONE WAS REFUTED.**  Under the amended criterion the straddle
class's representative is the r50 jam residue `[cupAt 1, crossingAt 0]` — a genuine cup-touching crossing
(`crossingCount = 1`), NOT a bare cup.  So the r50 unreachability theorem `cupTouchingCrossing_notBareCup_b3` (the
residue is no bare cup) is exactly WHY the criterion is amended: the residue is an arrival at the representative, and
the bare-cup target was the wrong flip criterion. -/
theorem amendedCriterion_straddleRepresentativeIsCupTouching :
    classRepresentativeOf 1 [cupAt 0, crossingAt 1] = [cupAt 1, crossingAt 0]
      ∧ crossingCount [cupAt 1, crossingAt 0] = 1 :=
  ⟨straddleRepresentativeIsJamResidue, residueIrreducibleCrossingCount⟩

/-- ★★ **The r50 bare-cup unreachability, re-exported as the amendment's justification.**  The straddle representative
`[cupAt 1, crossingAt 0]` reads a `brauerDiagramOf 3` diagram no bare cup reads — the r50 theorem, byte-intact,
now read as: the class representative is a cup-touching crossing, so demanding a bare cup was the straw criterion. -/
theorem amendedCriterion_representativeIsNoBareCup :
    ∀ barePos, barePos < 5 →
      brauerDiagramOf 3 [cupAt 1, crossingAt 0] ≠ brauerDiagramOf 3 [cupAt barePos] :=
  cupTouchingCrossing_notBareCup_b3

/-! ## Honesty markers -/

/-- ★★ **Honesty marker — the CUP-TOUCHING CRITERION AMENDMENT is RECORDED.**  The r50 straw flip-criterion ("reduce
every survivor to a bare cup") is superseded by addition: the corrected criterion is the (i,j)-representative family
(`classRepresentativeOf`), under which the r50 jam residue is an arrival, not a stuck form
(`amendedCriterion_straddleRepresentativeIsCupTouching`); the r50 unreachability theorem is re-read as the
amendment's justification (`amendedCriterion_representativeIsNoBareCup`); the three flag walls accommodate the family as
written; and the r50 file plus the three flag files stay BYTE-INTACT.  All zero-axiom.  `= true`. -/
def fxBrauer_hasCupTouchingCriterionAmendment : Bool := true

/-! ## The amended flip law, machine-checked (the SEVENTH honest zero-flip) -/

/-- ★★ **The BRAUER r51 amended-criterion terminal state — MACHINE-CHECKED (the SEVENTH honest zero-flip).**  The
criterion amendment SHIPS (`fxBrauer_hasCupTouchingCriterionAmendment = true`) on top of the class-representative
re-adjudication (`fxBrauer_hasClassRepresentativeReadjudication = true`) and the r50 cup-touching irreducibility
(`fxBrauer_hasCupTouchingIrreducibility = true`, byte-intact).  The amendment corrects the flip CRITERION; it does NOT
discharge `BrauerExt5CorrectedFoldReaches`.  So the two dispatch flip flags
(`fxBrauer_hasRegionDriverTotalDispatch`, owned r39; `fxBrauer_hasSingleCupTotalDecision`, owned r38) STAY `false`, WALL
A (`fxBrauer_hasSingleCupPeelDischarged`) STAYS `false`, the corrected-fold discharge
(`fxBrauer_hasCorrectedFoldDischarged`) STAYS `false`, and the inner-descent / straightening / completeness masters ALL
STAY `false`.  A `rfl`-conjunction the kernel checks; purely additive, no flag flipped on the old or the amended
criterion. -/
theorem fxBrauer_cupTouchingCriterionAmendmentTerminalState :
    fxBrauer_hasCupTouchingCriterionAmendment = true
      ∧ fxBrauer_hasClassRepresentativeReadjudication = true
      ∧ fxBrauer_hasCupTouchingIrreducibility = true
      ∧ fxBrauer_hasClassRepresentativeDischarged = false
      ∧ fxBrauer_hasCorrectedFoldDischarged = false
      ∧ fxBrauer_hasRegionDriverTotalDispatch = false
      ∧ fxBrauer_hasSingleCupTotalDecision = false
      ∧ fxBrauer_hasSingleCupPeelDischarged = false
      ∧ fxBrauer_hasStagedInnerDescentDischarged = false
      ∧ fxBrauer_hasFreeBrauerStraighteningNF = false
      ∧ fxBrauer_hasBrauerCompleteness = false
      ∧ fxBrauer_hasBrauerV2FullCompleteness = false :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end FX1Poly.Polygraph
