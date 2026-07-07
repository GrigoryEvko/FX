import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCupSortComplete
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCupReselectionOrbit

/-! # ArcCupOrbitPureCupFront — the front-head orbit witness is UNCONDITIONAL on the pure-cup fragment

The cup-head crux reduces (`ArcCupReselectionOrbit`) to producing the leg-aligned re-selection
`AtomicTraceEquiv tailList suffixAtoms` — the single open leaf `arcCupReselection_exists`, the genuine
planar content of the walking-adjunction Joyal-Street completeness.  Every shipped orbit brick leaves
that re-selection as a HYPOTHESIS.

★ This brick DISCHARGES it — with NO re-selection hypothesis — on the PURE-CUP fragment, by consuming the
shipped pure-cup completeness `pureCupSpine_sort` (#2184).  When the head cup already sits at the front of
the second spine (`secondList = headAtom :: suffixAtoms`) and BOTH tails are pure cup and boundary-chained
at the head's codomain boundary with equal arc structure, `pureCupSpine_sort` produces the tail
`SpineTraceEquiv`, `spineTraceEquiv_iff_atomicTraceEquiv` (FREE-5) crosses it to the atomic granularity the
re-selection needs, and `arcCupOrbitWitness_ofFrontHead` assembles the full `ArcCupOrbitWitness`.

This is the honest answer to "does `pureCupSpine_sort` unblock the orbit": YES on the pure-cup front-head
fragment, the base case (cap-count `0`) of the mixed cup/cap induction.  What it does NOT close: the MIXED
re-selection (a tail carrying caps), which is the irreducible geometric core `arcCupReselection_exists` —
the pure-cup completeness gives no cap content, so the general leaf stays open.

Raw Lean 4 + Init; per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-- ★ **The front-head orbit witness, UNCONDITIONAL on the pure-cup fragment.**  When the head cup is
already at the front of the second spine (`headAtom :: suffixAtoms`) and both tails are pure cup,
boundary-chained at the head's codomain boundary, and arc-equal there, the full `ArcCupOrbitWitness`
follows with NO re-selection hypothesis: `pureCupSpine_sort` (the shipped pure-cup completeness) produces
the tail `SpineTraceEquiv`, `spineTraceEquiv_iff_atomicTraceEquiv` crosses to the atomic granularity, and
`arcCupOrbitWitness_ofFrontHead` assembles the witness.  The codomain boundary is positive because the cup
codomain arity is `2` (`hasCupCodArity`).  This closes the cup-head orbit on its pure-cup base case — the
first machine-checked discharge of an `ArcCupOrbitWitness` instance without an orbit residual. -/
theorem arcCupOrbitWitness_ofFrontHead_pureCup
    {overallSource overallTarget : adjunctionGraph.Mode}
    (headAtom : SpineAtom adjunctionModeSignature overallSource overallTarget)
    (hasCupDomArity : headAtom.generatorDom.length = 0)
    (hasCupCodArity : headAtom.generatorCod.length = 2)
    (tailList suffixAtoms :
      List (SpineAtom adjunctionModeSignature overallSource overallTarget))
    (tailChained : SpineBoundaryChained headAtom.codBoundaryLength tailList)
    (suffixChained : SpineBoundaryChained headAtom.codBoundaryLength suffixAtoms)
    (tailPureCup : AllCupArity tailList)
    (suffixPureCup : AllCupArity suffixAtoms)
    (arcEqual : arcStructureOfSpineList headAtom.codBoundaryLength tailList
        = arcStructureOfSpineList headAtom.codBoundaryLength suffixAtoms) :
    ArcCupOrbitWitness headAtom tailList (headAtom :: suffixAtoms) := by
  have codPositive : 0 < headAtom.codBoundaryLength := by
    show 0 < headAtom.leftContext.length + headAtom.generatorCod.length
      + headAtom.rightContext.length
    rw [hasCupCodArity]
    exact Nat.lt_of_lt_of_le (Nat.succ_pos (headAtom.leftContext.length + 1))
      (Nat.le_add_right (headAtom.leftContext.length + 2) headAtom.rightContext.length)
  have tailTrace : SpineTraceEquiv adjunctionModeSignature tailList suffixAtoms :=
    pureCupSpine_sort headAtom.codBoundaryLength tailList suffixAtoms
      tailChained suffixChained tailPureCup suffixPureCup codPositive arcEqual
  exact arcCupOrbitWitness_ofFrontHead headAtom hasCupDomArity hasCupCodArity tailList suffixAtoms
    tailChained (spineTraceEquiv_iff_atomicTraceEquiv.mp tailTrace)

/-! ## Honesty marker -/

/-- **Honesty marker — the orbit witness is DISCHARGED, re-selection-free, on the pure-cup front-head
fragment.**  `arcCupOrbitWitness_ofFrontHead_pureCup` produces a full `ArcCupOrbitWitness` with NO
re-selection hypothesis when the head cup is at the front and both tails are pure cup, boundary-chained,
and arc-equal — the re-selection `arcCupReselection_exists` is supplied by the shipped `pureCupSpine_sort`
(#2184) crossed to atomic granularity by `spineTraceEquiv_iff_atomicTraceEquiv`.  This is the cup-head
orbit's pure-cup BASE CASE (cap-count `0`) closed unconditionally — the concrete confirmation that
`pureCupSpine_sort` unblocks the orbit interface on its cap-free fragment.  What this marker does NOT
claim: the MIXED re-selection (a tail carrying caps), which the pure-cup completeness cannot supply and
which remains the irreducible open leaf `fxMode_hasArcCellReconstruction`.  `= true`. -/
def fxMode_hasArcCupOrbitPureCupFront : Bool := true

end FX1Poly.Polygraph
