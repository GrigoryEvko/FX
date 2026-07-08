import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCupReselectionOrbit

/-! # ArcCupHeadFrontedReselection — the cup case discharges from the swap-NF FRONTING (no bubble bookkeeping)

The on-zone route for the walking-adjunction cup case is the FM (Forest–Mimram, arXiv:2109.05369, §4.2)
convergent swap-normal-form: the length-preserving INTERCHANGERS (`AtomicTraceEquiv`, the shipped
disjoint-window swaps) SORT the located head cup to the FRONT — the canonical representative — and the tail is
then RESELECTED within its own fixed-length swap orbit; the length-CHANGING snakes appear only when reducing to
the representative, never as a swap step (`AtomicTraceEquiv` is length-preserving).

`ArcCupReselectionOrbit` shipped `arcCupOrbitWitness_ofReselection`: the full `ArcCupOrbitWitness` assembles
from the located split + `BubblesToFront` witness + `windowPin` + the tail re-selection.  But the mixed
`locateAux` REALIZE step (`arcCupMixedFrontsCup_ofCupCountPos`, `ArcCupMixedBubbleFront.lean`) hands back a
plain `AtomicTraceEquiv secondList (movedTarget :: movedRest)` — the swap sequence that fronts a cup — NOT a
`BubblesToFront` witness with the head-split exposed.  This brick closes that shape mismatch: it discharges the
ENTIRE cup-case head-extraction conclusion directly from

  * a FRONTING `AtomicTraceEquiv secondList (headAtom :: movedRest)` — the interchanger sort landing the HEAD
    cup at the front (this IS `windowPin` already collapsed to head-identity: by
    `frontCupToucher_eq_head_ofWindowPin` a matched window forces the fronted cup to BE the head atom), and
  * a tail RESELECTION `AtomicTraceEquiv tailList movedRest` — the fixed-length tail swap orbit.

No `BubblesToFront` witness, no split.  This is the FM swap-NF statement at cup granularity: two arc-equal
cells reduce (via interchangers) to the SAME head cup fronted + a reselected tail.  `tailsCancel` is FREE
(arc structure is trace-invariant, `extractArc_eq_of_atomicTraceEquiv` at the `codBoundaryLength` seed), and
the fronting IS the `SpineTraceEquiv` half of the conclusion (`AtomicTraceEquiv.toSpineTraceEquiv`).

  * ★ `cupHeadExtractionConclusion_ofFrontedHeadReselection` — the cup-case head extraction from the two
    trace-equivs (fronting-to-head + tail reselection), the swap-NF discharge with no bubble bookkeeping.

What this brick does NOT provide — and what the honest marker names precisely — is the two trace-equivs
THEMSELVES: (a) that the interchanger sort lands the HEAD cup (`windowPin`, the on-zone content the census
CANNOT read, `headCupWindowReadoff_isFalse`), and (b) the tail reselection (the recursive completeness).  Those
are the sole open leaf `arcCupReselection_exists`; no gate flip.

Raw Lean 4 + Init; STRUCTURAL (rides the shipped trace-equiv peel), zero-axiom; per-declaration
`#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## Range length plumbing (private copy — the seed files' kits are file-private) -/

private theorem rangeLoopLength : (count : Nat) → (accumulated : List Nat) →
    (List.range.loop count accumulated).length = count + accumulated.length
  | 0, accumulated => (Nat.zero_add accumulated.length).symm
  | count + 1, accumulated => by
      have inner := rangeLoopLength count (count :: accumulated)
      show (List.range.loop count (count :: accumulated)).length
        = count + 1 + accumulated.length
      rw [inner]
      show count + (accumulated.length + 1) = count + 1 + accumulated.length
      rw [← Nat.add_assoc count accumulated.length 1,
        Nat.add_right_comm count accumulated.length 1]

private theorem rangeLength (count : Nat) : (List.range count).length = count := by
  show (List.range.loop count []).length = count
  rw [rangeLoopLength count []]
  exact Nat.add_zero count

/-! ## The swap-NF cup-case discharge -/

/-- ★ **The cup case discharges from the swap-NF fronting + tail reselection (no bubble bookkeeping).**
For a cup-arity head, granted the interchanger sort that fronts the HEAD cup as an `AtomicTraceEquiv secondList
(headAtom :: movedRest)` (with the fronted list chained at `bottomCount`) and the tail reselection
`AtomicTraceEquiv tailList movedRest`, the full cup-case head-extraction conclusion follows: `secondList` is
`SpineTraceEquiv` to `headAtom :: movedRest` (the fronting, included via `toSpineTraceEquiv`), `movedRest` is
chained at the head's target boundary (`spineBoundaryChained_tail` of the fronted list), and the tails arc-agree
there (`tailsCancel` is FREE — arc structure is trace-invariant, `extractArc_eq_of_atomicTraceEquiv` at the
canonical `headAtom.codBoundaryLength` seed).  This is the FM swap-NF discharge: the located cup fronted by
interchangers (canonical representative) + a fixed-length tail orbit, with NO `BubblesToFront` witness and NO
split — the shape the mixed `locateAux` REALIZE step (`arcCupMixedFrontsCup_ofCupCountPos`) actually produces. -/
theorem cupHeadExtractionConclusion_ofFrontedHeadReselection
    {overallSource overallTarget : adjunctionGraph.Mode}
    (headAtom : SpineAtom adjunctionModeSignature overallSource overallTarget)
    (hasCupCodArity : headAtom.generatorCod.length = 2)
    (tailList secondList movedRest :
      List (SpineAtom adjunctionModeSignature overallSource overallTarget))
    (fronting : AtomicTraceEquiv adjunctionModeSignature secondList (headAtom :: movedRest))
    (frontedChained : SpineBoundaryChained (headAtom.domBoundaryLength) (headAtom :: movedRest))
    (tailChained : SpineBoundaryChained headAtom.codBoundaryLength tailList)
    (reselection : AtomicTraceEquiv adjunctionModeSignature tailList movedRest) :
    ∃ matchedRemainder,
      SpineTraceEquiv adjunctionModeSignature secondList (headAtom :: matchedRemainder)
        ∧ SpineBoundaryChained headAtom.codBoundaryLength matchedRemainder
        ∧ arcStructureOfSpineList headAtom.codBoundaryLength tailList
            = arcStructureOfSpineList headAtom.codBoundaryLength matchedRemainder := by
  have hasPositiveWidth : 0 < headAtom.codBoundaryLength := by
    show 0 < headAtom.leftContext.length + headAtom.generatorCod.length
      + headAtom.rightContext.length
    rw [hasCupCodArity]
    exact Nat.lt_of_lt_of_le (Nat.succ_pos (headAtom.leftContext.length + 1))
      (Nat.le_add_right (headAtom.leftContext.length + 2) headAtom.rightContext.length)
  have seedLengthEq :
      (ArcWireState.mk (List.range headAtom.codBoundaryLength) [] headAtom.codBoundaryLength
        0 [] []).openWires.length = headAtom.codBoundaryLength :=
    rangeLength headAtom.codBoundaryLength
  have tailsCancel : arcStructureOfSpineList headAtom.codBoundaryLength tailList
      = arcStructureOfSpineList headAtom.codBoundaryLength movedRest :=
    extractArc_eq_of_atomicTraceEquiv reselection
      (ArcWireState.mk (List.range headAtom.codBoundaryLength) [] headAtom.codBoundaryLength 0 [] [])
      headAtom.codBoundaryLength headAtom.codBoundaryLength
      (arcStateFresh_initial headAtom.codBoundaryLength)
      (isUnionFindForest_initialLinks headAtom.codBoundaryLength) hasPositiveWidth
      (Nat.le_refl headAtom.codBoundaryLength) seedLengthEq tailChained
  exact ⟨movedRest, fronting.toSpineTraceEquiv,
    (spineBoundaryChained_tail frontedChained).2, tailsCancel⟩

/-! ## Honesty marker -/

/-- **Honesty marker — the cup case discharges from the swap-NF FRONTING, no bubble bookkeeping (flag-B R7,
PART II route lock).**  `cupHeadExtractionConclusion_ofFrontedHeadReselection`: the entire cup-case head
extraction follows from two `AtomicTraceEquiv`s — the interchanger sort fronting the HEAD cup
(`AtomicTraceEquiv secondList (headAtom :: movedRest)`, which by seed rigidity IS `windowPin` collapsed to
head-identity) and the fixed-length tail reselection (`AtomicTraceEquiv tailList movedRest`).  `tailsCancel` is
FREE (arc structure trace-invariant), the fronting IS the conclusion's `SpineTraceEquiv` half.  This is the FM
convergent swap-normal-form at cup granularity: length-preserving interchangers sort the head cup to the front
(canonical representative), the tail is reselected within its fixed-length orbit; the length-changing snakes
appear only in reducing to the representative, NEVER as a swap step.  It matches the shape the mixed `locateAux`
REALIZE step (`arcCupMixedFrontsCup_ofCupCountPos`) actually produces — a plain `AtomicTraceEquiv`, NOT a
`BubblesToFront` witness — so it strictly generalizes the split-carrying `arcCupOrbitWitness_ofReselection`.

What this marker does NOT claim: the two trace-equivs themselves — (a) that the interchanger sort lands the
HEAD cup at its window (`windowPin`, the ON-ZONE content the census CANNOT read, machine-refuted by
`headCupWindowReadoff_isFalse`; the swap-NF, NOT the census, is the complete invariant there — precisely FM's
escalation from the cospan `Con` to the convergent RS), and (b) the tail reselection (the recursive
completeness).  Those two together are the sole open leaf `arcCupReselection_exists`.  No gate flip:
`fxMode_hasArcStructureReconstruction` and `fxMode_hasModeRelativeConvDecision` stay as is.  `= true`. -/
def fxMode_hasArcCupHeadFrontedReselection : Bool := true

end FX1Poly.Polygraph
