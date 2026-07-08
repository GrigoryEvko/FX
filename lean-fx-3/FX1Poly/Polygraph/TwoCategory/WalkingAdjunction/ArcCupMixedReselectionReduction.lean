import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCupOrbitPureCupFront
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCupOrbitPureCapFront

/-! # ArcCupMixedReselectionReduction — the mixed re-selection UNIFIED as one completeness target

The cup-head orbit reduces (`ArcCupReselectionOrbit`) to producing the leg-aligned re-selection
`AtomicTraceEquiv tailList suffixAtoms` — the open leaf `arcCupReselection_exists`, the walking-adjunction
Joyal–Street planar content.  Two disjoint fragments are shipped, each feeding the SAME assembly
(`arcCupOrbitWitness_ofFrontHead`) with a pure sort crossed to atomic granularity:

  * `arcCupOrbitWitness_ofFrontHead_pureCup` — pure-cup tail (cap-count `0`), via `pureCupSpine_sort`;
  * `arcCupOrbitWitness_ofFrontHead_pureCap` — pure-cap tail (cup-count-in-tail `0`), via
    `pureCapSpine_sort`.

Both markers record the same honest gap: "the two disjoint extremes do not glue into the mixed interior."
This brick NAMES the common target both fronts factor through and reduces the WHOLE cup-front residual to
it in one shot:

  * ★ `MixedTailArcCompleteness` — the completeness of the arc invariant at a positive seed: any two
    boundary-chained spines with equal arc structure are `SpineTraceEquiv`.  This is exactly
    `arcCupReselection_exists` phrased as completeness (soundness — trace equivalence gives equal arc
    structure — is the shipped `extractArc_eq_of_atomicTraceEquiv`).  It carries NO purity hypothesis, so
    the mixed cup/cap tail is in scope.
  * ★ `arcCupOrbitWitness_ofFrontHead_ofCompleteness` — GRANTED `MixedTailArcCompleteness`, the front-head
    orbit witness follows for an ARBITRARY (mixed) tail: the completeness produces the tail
    `SpineTraceEquiv`, `spineTraceEquiv_iff_atomicTraceEquiv` crosses to atomic granularity, and
    `arcCupOrbitWitness_ofFrontHead` assembles.  This collapses BOTH shipped pure fronts and the open mixed
    interior into ONE grep-able dependency: the front-head cup residual is EXACTLY
    `MixedTailArcCompleteness`.

What this brick does NOT close: `MixedTailArcCompleteness` itself on the mixed interior.  Its head-cup
disambiguation sub-crux is the census-inversion window read-off (`internalCupCounts` PINS a cup's window);
its base case (empty tail) is shipped (`singleCupHeadWindowPinned`), and the mixed last cup is diagram-
readable as an adjacent short chord (`mixedSpine_lastCup_isShortChord`), but the peel-and-recurse mixed
`locateAux` — bubbling the identified cup to front across a mixed cup/cap prefix over the shipped cross-swap
arc simulations — is the residual.  No gate flip; `fxMode_hasArcStructureReconstruction` stays as is.

Raw Lean 4 + Init; per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## The unified completeness target -/

/-- ★ **The completeness of the arc invariant (the unified mixed re-selection target).**  Any two
boundary-chained spines over a positive bottom boundary whose arc structures agree are `SpineTraceEquiv`.
This is `arcCupReselection_exists` stated as completeness of the extracted arc invariant, carrying NO
purity restriction — the mixed cup/cap tail is exactly the open interior.  Soundness (the converse — a
trace equivalence forces equal arc structure) is the shipped `extractArc_eq_of_atomicTraceEquiv`; the two
directions together are the walking-adjunction Joyal–Street word-problem statement at atom granularity. -/
def MixedTailArcCompleteness : Prop :=
  ∀ {overallSource overallTarget : adjunctionGraph.Mode} (bottomCount : Nat)
    (firstList secondList :
      List (SpineAtom adjunctionModeSignature overallSource overallTarget)),
    SpineBoundaryChained bottomCount firstList →
    SpineBoundaryChained bottomCount secondList →
    0 < bottomCount →
    arcStructureOfSpineList bottomCount firstList
        = arcStructureOfSpineList bottomCount secondList →
    SpineTraceEquiv adjunctionModeSignature firstList secondList

/-! ## The unified front-head reduction -/

/-- ★ **The front-head orbit witness from the unified completeness.**  Granted
`MixedTailArcCompleteness`, the front-head cup orbit witness follows for an ARBITRARY tail — cup, cap, or
BOTH — with NO purity hypothesis and NO re-selection hypothesis: the completeness at the head's codomain
boundary produces the tail `SpineTraceEquiv tailList suffixAtoms`,
`spineTraceEquiv_iff_atomicTraceEquiv` crosses it to the atomic granularity the re-selection needs, and
`arcCupOrbitWitness_ofFrontHead` assembles the witness.  The codomain boundary is positive because the cup
codomain arity is `2` (`hasCupCodArity`).

This is the exact generalization of the two shipped pure fronts
(`arcCupOrbitWitness_ofFrontHead_pureCup` / `…pureCap`): each of those consumes a pure SORT on its
fragment; this consumes the unified completeness on the whole (possibly mixed) tail.  Hence the entire
front-head cup residual — both discharged extremes AND the open mixed interior — is precisely
`MixedTailArcCompleteness`, one grep-able proposition. -/
theorem arcCupOrbitWitness_ofFrontHead_ofCompleteness
    (completeness : MixedTailArcCompleteness)
    {overallSource overallTarget : adjunctionGraph.Mode}
    (headAtom : SpineAtom adjunctionModeSignature overallSource overallTarget)
    (hasCupDomArity : headAtom.generatorDom.length = 0)
    (hasCupCodArity : headAtom.generatorCod.length = 2)
    (tailList suffixAtoms :
      List (SpineAtom adjunctionModeSignature overallSource overallTarget))
    (tailChained : SpineBoundaryChained headAtom.codBoundaryLength tailList)
    (suffixChained : SpineBoundaryChained headAtom.codBoundaryLength suffixAtoms)
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
    completeness headAtom.codBoundaryLength tailList suffixAtoms
      tailChained suffixChained codPositive arcEqual
  exact arcCupOrbitWitness_ofFrontHead headAtom hasCupDomArity hasCupCodArity tailList suffixAtoms
    tailChained (spineTraceEquiv_iff_atomicTraceEquiv.mp tailTrace)

/-! ## Honesty marker -/

/-- **Honesty marker — the whole front-head cup residual is UNIFIED as `MixedTailArcCompleteness`.**
`arcCupOrbitWitness_ofFrontHead_ofCompleteness`: granting the completeness of the arc invariant (no
purity), the front-head cup orbit witness follows for an arbitrary — including mixed cup/cap — tail, by
feeding the tail `SpineTraceEquiv` (crossed to atomic granularity) into `arcCupOrbitWitness_ofFrontHead`.
This is the common generalization of the two shipped pure fronts
(`arcCupOrbitWitness_ofFrontHead_pureCup`, via `pureCupSpine_sort`;
`arcCupOrbitWitness_ofFrontHead_pureCap`, via `pureCapSpine_sort`): both discharged extremes AND the open
mixed interior collapse to ONE proposition, `MixedTailArcCompleteness`.

What this marker does NOT claim: `MixedTailArcCompleteness` itself on the mixed interior.  Precise remaining
geometry — the head-cup disambiguation sub-crux is the census-inversion window read-off (`internalCupCounts`
PINS a cup's window through a moved leg strand); its base case (empty tail) is shipped
(`singleCupHeadWindowPinned`) and the mixed last cup is diagram-readable as an adjacent short chord
(`mixedSpine_lastCup_isShortChord`), but the peel-and-recurse mixed `locateAux` — bubbling the identified
cup to the front across a mixed cup/cap prefix, driven by the shipped cross-swap arc simulations
(`ArcCupCupSwapSimulation` / `ArcCupCapSwapSimulation` / `ArcCapCupSwapSimulation`) — is not assembled.
The FM Prop 4.3.1 width-induction `N(phi) = (N1, N2^eta, N2^eps)` is the frame; the two pure sorts are the
`N2^eta = 0` / `N2^eps = 0` corners; the mixed interior (both positive) is where the cup peel needs the
census disambiguation.  No gate flip.  `= true`. -/
def fxMode_hasArcCupMixedReselectionReduction : Bool := true

end FX1Poly.Polygraph
