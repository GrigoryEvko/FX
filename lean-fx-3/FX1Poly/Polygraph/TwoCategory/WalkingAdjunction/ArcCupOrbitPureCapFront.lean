import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCapSortComplete
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCupReselectionOrbit

/-! # ArcCupOrbitPureCapFront — the front-head orbit witness is UNCONDITIONAL on the pure-CAP tail

The cup-head crux reduces (`ArcCupReselectionOrbit`) to producing the leg-aligned re-selection
`AtomicTraceEquiv tailList suffixAtoms` — the single open leaf `arcCupReselection_exists`, the genuine
planar content of the walking-adjunction Joyal-Street completeness.  `ArcCupOrbitPureCupFront` discharged
that with NO re-selection hypothesis on ONE extreme of the mixed cup/cap spectrum — the pure-cup tail
(cap-count `0`, the induction base) — by consuming the shipped pure-cup completeness `pureCupSpine_sort`.

★ This brick discharges it on the OTHER extreme: the pure-CAP tail (cup-count-in-tail `0`, the dual base
of the mixed cup/cap induction).  The head is still a cup (`domArity 0`, `codArity 2`), but its whole
tail carries ONLY caps.  When the head cup already sits at the front of the second spine (`secondList =
headAtom :: suffixAtoms`) and BOTH tails are pure cap, boundary-chained at the head's codomain boundary
with equal arc structure, the shipped pure-cap completeness `pureCapSpine_sort` produces the tail
`SpineTraceEquiv`, `spineTraceEquiv_iff_atomicTraceEquiv` crosses it to the atomic granularity the
re-selection needs, and `arcCupOrbitWitness_ofFrontHead` assembles the full `ArcCupOrbitWitness`.

This is the honest dual answer to "does `pureCapSpine_sort` unblock the orbit": YES on the pure-cap
front-head fragment, the dual base of the mixed cup/cap induction.  Note the cup-head positivity is still
required (the cup codomain arity `2` gives it) even though the pure-cap SORT itself needs no positivity —
the orbit-witness assembly (`arcCupOrbitWitness_ofFrontHead`) reads the seed width off the head cup.

What it does NOT close: the MIXED re-selection (a tail carrying BOTH cups AND caps at once), which is the
irreducible geometric core `arcCupReselection_exists` — a single pure regime, cup OR cap, gives no
cup-cap CROSS content, so the general leaf stays open.  Two disjoint base cases (cap-count `0` and
cup-count-in-tail `0`) do not compose into the mixed interior; that is the FM Prop 4.3.9 connected-cell
residual, provable only along the whole width-induction, not by gluing the two extremes.

Raw Lean 4 + Init; per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-- ★ **The front-head orbit witness, UNCONDITIONAL on the pure-CAP tail.**  Dual base of the mixed
cup/cap induction (cup-count-in-tail `0`).  When the head cup is already at the front of the second spine
(`headAtom :: suffixAtoms`) and both tails are pure CAP, boundary-chained at the head's codomain boundary,
and arc-equal there, the full `ArcCupOrbitWitness` follows with NO re-selection hypothesis:
`pureCapSpine_sort` (the shipped pure-cap completeness) produces the tail `SpineTraceEquiv`,
`spineTraceEquiv_iff_atomicTraceEquiv` crosses to the atomic granularity, and
`arcCupOrbitWitness_ofFrontHead` assembles the witness.  The head cup's codomain arity `2`
(`hasCupCodArity`) supplies the positive seed width that the orbit-witness assembly reads (the pure-cap
sort itself needs none).  This closes the cup-head orbit on its DUAL base case — a cup head over a
fully-cap tail — the second machine-checked discharge of an `ArcCupOrbitWitness` instance without an
orbit residual, complementing the pure-cup base. -/
theorem arcCupOrbitWitness_ofFrontHead_pureCap
    {overallSource overallTarget : adjunctionGraph.Mode}
    (headAtom : SpineAtom adjunctionModeSignature overallSource overallTarget)
    (hasCupDomArity : headAtom.generatorDom.length = 0)
    (hasCupCodArity : headAtom.generatorCod.length = 2)
    (tailList suffixAtoms :
      List (SpineAtom adjunctionModeSignature overallSource overallTarget))
    (tailChained : SpineBoundaryChained headAtom.codBoundaryLength tailList)
    (suffixChained : SpineBoundaryChained headAtom.codBoundaryLength suffixAtoms)
    (tailPureCap : AllCapArity tailList)
    (suffixPureCap : AllCapArity suffixAtoms)
    (arcEqual : arcStructureOfSpineList headAtom.codBoundaryLength tailList
        = arcStructureOfSpineList headAtom.codBoundaryLength suffixAtoms) :
    ArcCupOrbitWitness headAtom tailList (headAtom :: suffixAtoms) := by
  have tailTrace : SpineTraceEquiv adjunctionModeSignature tailList suffixAtoms :=
    pureCapSpine_sort headAtom.codBoundaryLength tailList suffixAtoms
      tailChained suffixChained tailPureCap suffixPureCap arcEqual
  exact arcCupOrbitWitness_ofFrontHead headAtom hasCupDomArity hasCupCodArity tailList suffixAtoms
    tailChained (spineTraceEquiv_iff_atomicTraceEquiv.mp tailTrace)

/-! ## Honesty marker -/

/-- **Honesty marker — the orbit witness is DISCHARGED, re-selection-free, on the pure-CAP front-head
tail (the DUAL base).**  `arcCupOrbitWitness_ofFrontHead_pureCap` produces a full `ArcCupOrbitWitness`
with NO re-selection hypothesis when the head cup is at the front and both tails are pure cap,
boundary-chained, and arc-equal — the re-selection `arcCupReselection_exists` is supplied by the shipped
`pureCapSpine_sort` crossed to atomic granularity by `spineTraceEquiv_iff_atomicTraceEquiv`.  This is the
cup-head orbit's pure-cap DUAL BASE (cup-count-in-tail `0`) closed unconditionally, complementing the
pure-cup base (`arcCupOrbitWitness_ofFrontHead_pureCup`, cap-count `0`).  What this marker does NOT
claim: the MIXED re-selection (a tail carrying BOTH cups AND caps), which neither pure regime supplies —
the two disjoint extremes do not glue into the mixed interior — and which remains the irreducible open
leaf `arcCupReselection_exists`.  No gate flip.  `= true`. -/
def fxMode_hasArcCupOrbitPureCapFront : Bool := true

end FX1Poly.Polygraph
