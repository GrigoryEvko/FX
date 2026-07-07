import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcPureCapSpine
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCapHeadDischarge

/-! # ArcCapSortComplete — pure-cap completeness `pureCapSpine_sort` (peel-first mirror of #2184)

The pure-CAP mirror of `pureCupSpine_sort`.  Where the cup completeness peels the LAST cup (cups
create fresh legs at the top, so the last cup's legs are undisturbed and read off as a short chord),
the cap completeness peels the FIRST cap: caps CONSUME two existing bottom ports, so the head cap is
arc-anchored — the shipped cap-head discharge `spineArcHeadExtractionChained_ofCapArity` already
LOCATES the matching cap in the other spine, BUBBLES it to the front, IDENTIFIES it with the head,
and CANCELS both cap-headed folds in one shot, returning the two remainders arc-equal at the head's
TARGET boundary.

This collapses the whole cup machinery — `locateAux` (fuel unsnoc bubble), `dropLastCup_arc_injective`
(the S3 merge-inversion linchpin), `cupSwapStep*`, and the `chordShift_*` descent — into a single
shipped call.  The peel-first cap recursion is a thin fuel driver over that discharge:

  1. peel the head cap `C1` off `firstList = C1 :: t1` (`headCapArity`, `allCapArity_ofCons`);
  2. `spineArcHeadExtractionChained_ofCapArity` extracts `C1`'s partner from `secondList` as
     `C1 :: matchedRemainder`, chained at `C1.codBoundaryLength`, with the two remainders arc-equal
     there;
  3. `matchedRemainder` is pure cap by arc transfer (`allCapArity_ofArcEqualToPureCap`, via the
     cup-count reflection — a pure-cap tail has zero cup tally, and arc equality carries it);
  4. recurse on `(t1, matchedRemainder)` at the SHRUNK boundary `C1.codBoundaryLength`;
  5. re-glue the head with `SpineTraceEquiv.consCongr` and compose with the extraction bubble.

Op-variance verdict: the cap arc-anchoring makes the peel-first route STRICTLY EASIER than the cup
peel-last route — it needs NO positivity hypothesis (`0 < bottomCount`, which the cup transpositions
require) because the discharge derives the width from the presence of the cap head, and it never
touches the merge-inversion injectivity linchpin (the discharge's front campaign already absorbed the
yank/merge reasoning).  The one genuine mirror asymmetry is that the recursion boundary SHRINKS per
cap (`C1.codBoundaryLength < bottomCount`), so `bottomCount` is a recursion variable here, whereas
the cup driver holds it fixed.

Raw Lean 4 + Init; per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## Count reflections (private copies — the transfer file's kit is file-private) -/

/-- The arc structure's total `capCount` reflects the boundary-independent cap-atom count —
re-derived locally (the transfer file `ArcPureCupTransfer` owns the shared private copy). -/
private theorem capCountReflect
    {overallSource overallTarget : adjunctionGraph.Mode} (bottomCount : Nat)
    (atoms : List (SpineAtom adjunctionModeSignature overallSource overallTarget)) :
    (arcStructureOfSpineList bottomCount atoms).capCount = capAtomCount atoms := by
  show (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
      atoms).capEventNodes.length = capAtomCount atoms
  rw [processArcSpine_capEventNodes_length]
  exact Nat.zero_add _

/-- The dual reflection: the arc structure's total `cupCount` reflects the boundary-independent
cup-atom count. -/
private theorem cupCountReflect
    {overallSource overallTarget : adjunctionGraph.Mode} (bottomCount : Nat)
    (atoms : List (SpineAtom adjunctionModeSignature overallSource overallTarget)) :
    (arcStructureOfSpineList bottomCount atoms).cupCount = cupAtomCount atoms := by
  show (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
      atoms).cupEventNodes.length = cupAtomCount atoms
  rw [processArcSpine_cupEventNodes_length]
  exact Nat.zero_add _

/-- A list of length zero is nil — a `noConfusion` peel, staying `propext`-free where
`List.eq_nil_of_length_eq_zero` (an iff-backed lemma) could leak. -/
private theorem listEqNilOfLengthZero {carrier : Type _} :
    (elems : List carrier) → elems.length = 0 → elems = []
  | [], _ => rfl
  | _ :: _, lengthZero => Nat.noConfusion lengthZero

/-! ## Arc-transfer of the pure-cap regime -/

/-- ★ **The pure-cap regime transfers across arc equality.**  If `firstList` is pure cap and its arc
structure equals `secondList`'s, then `secondList` is pure cap: a pure-cap spine has zero cup tally
(`cupAtomCount_ofAllCapArity`), the arc structure's total `cupCount` reflects the cup-atom count
(`cupCountReflect`), so arc-equal spines carry equal cup tallies, and a zero tally forces `AllCapArity`
(`allCapArity_ofCupAtomCountZero`).  This is what supplies `AllCapArity` on the extracted remainder in
the peel-first recursion — no arity-preservation over the trace equivalence needed. -/
theorem allCapArity_ofArcEqualToPureCap
    {overallSource overallTarget : adjunctionGraph.Mode} (bottomCount : Nat)
    (firstList secondList : List (SpineAtom adjunctionModeSignature overallSource overallTarget))
    (firstPureCap : AllCapArity firstList)
    (arcEqual : arcStructureOfSpineList bottomCount firstList
      = arcStructureOfSpineList bottomCount secondList) :
    AllCapArity secondList := by
  have firstCupZero : cupAtomCount firstList = 0 :=
    cupAtomCount_ofAllCapArity firstList firstPureCap
  have cupCountsAgree : cupAtomCount firstList = cupAtomCount secondList := by
    have congrCupCount := congrArg FullArcStructure.cupCount arcEqual
    rw [cupCountReflect bottomCount firstList, cupCountReflect bottomCount secondList] at congrCupCount
    exact congrCupCount
  exact allCapArity_ofCupAtomCountZero secondList (cupCountsAgree.symm.trans firstCupZero)

/-- ★ **Equal-arc pure-cap spines have equal length.**  The arc structure's total `capCount` reflects
the cap-atom count (`capCountReflect`), and a pure-cap spine's cap count IS its length
(`capAtomCount_ofAllCapArity`), so arc-equal pure-cap spines carry equal length. -/
theorem pureCapSpines_sameLength_ofArcEqual
    {overallSource overallTarget : adjunctionGraph.Mode} (bottomCount : Nat)
    (firstList secondList : List (SpineAtom adjunctionModeSignature overallSource overallTarget))
    (firstPureCap : AllCapArity firstList) (secondPureCap : AllCapArity secondList)
    (arcEqual : arcStructureOfSpineList bottomCount firstList
      = arcStructureOfSpineList bottomCount secondList) :
    firstList.length = secondList.length := by
  have capCountsAgree : capAtomCount firstList = capAtomCount secondList := by
    have congrCapCount := congrArg FullArcStructure.capCount arcEqual
    rw [capCountReflect bottomCount firstList, capCountReflect bottomCount secondList] at congrCapCount
    exact congrCapCount
  rw [← capAtomCount_ofAllCapArity firstList firstPureCap,
    ← capAtomCount_ofAllCapArity secondList secondPureCap]
  exact capCountsAgree

/-! ## The empty base case -/

/-- ★ **The empty base case of the pure-cap sort.**  A pure-cap spine whose arc structure equals the
empty spine's is itself empty: equal arc forces equal length (`pureCapSpines_sameLength_ofArcEqual`
with the empty side pure-cap by `AllCapArity.nil`), a zero-length list is nil
(`listEqNilOfLengthZero`), and trace equivalence to `[]` collapses to reflexivity. -/
theorem pureCapSpine_sort_nil
    {overallSource overallTarget : adjunctionGraph.Mode} (bottomCount : Nat)
    (secondList : List (SpineAtom adjunctionModeSignature overallSource overallTarget))
    (secondPureCap : AllCapArity secondList)
    (arcEqual : arcStructureOfSpineList bottomCount
        ([] : List (SpineAtom adjunctionModeSignature overallSource overallTarget))
      = arcStructureOfSpineList bottomCount secondList) :
    SpineTraceEquiv adjunctionModeSignature [] secondList := by
  have secondNil : secondList = [] :=
    listEqNilOfLengthZero secondList
      (pureCapSpines_sameLength_ofArcEqual bottomCount [] secondList AllCapArity.nil
        secondPureCap arcEqual).symm
  rw [secondNil]
  exact SpineTraceEquiv.refl []

/-! ## `pureCapSpine_sort` — the pure-cap completeness theorem -/

/-- Fuel-driven core of the pure-cap sort (structural on `fuel ≥ firstList.length`).  Peels the head
cap `C1` off `firstList = C1 :: t1`, EXTRACTS its partner from `secondList` as `C1 :: matchedRemainder`
via the shipped cap-head discharge (which locates, bubbles, identifies, and cancels in one shot),
transfers the pure-cap regime to `matchedRemainder`, recurses on the shrunk boundary
`C1.codBoundaryLength`, and re-glues `C1` with `SpineTraceEquiv.consCongr`. -/
private theorem pureCapSpineSortFueled
    {overallSource overallTarget : adjunctionGraph.Mode} :
    (fuel : Nat) →
    (bottomCount : Nat) →
    (firstList secondList :
      List (SpineAtom adjunctionModeSignature overallSource overallTarget)) →
    firstList.length ≤ fuel →
    SpineBoundaryChained bottomCount firstList →
    SpineBoundaryChained bottomCount secondList →
    AllCapArity firstList →
    AllCapArity secondList →
    arcStructureOfSpineList bottomCount firstList
      = arcStructureOfSpineList bottomCount secondList →
    SpineTraceEquiv adjunctionModeSignature firstList secondList
  | 0, bottomCount, firstList, secondList, lengthBound, _, chainedSecond, _, secondPureCap, arcEqual => by
      match firstList, lengthBound, arcEqual with
      | [], _, arcEqual => exact pureCapSpine_sort_nil bottomCount secondList secondPureCap arcEqual
      | _ :: _, lengthBound, _ => exact absurd lengthBound (Nat.not_succ_le_zero _)
  | fuel + 1, bottomCount, firstList, secondList, lengthBound, chainedFirst, chainedSecond,
      firstPureCap, secondPureCap, arcEqual => by
      match firstList, lengthBound, chainedFirst, firstPureCap, arcEqual with
      | [], _, _, _, arcEqual => exact pureCapSpine_sort_nil bottomCount secondList secondPureCap arcEqual
      | C1 :: t1, lengthBound, chainedFirst, firstPureCap, arcEqual =>
          obtain ⟨c1Dom, c1Cod⟩ := headCapArity firstPureCap
          have t1Pure : AllCapArity t1 := allCapArity_ofCons firstPureCap
          have tailChainedFirst : SpineBoundaryChained C1.codBoundaryLength t1 :=
            (spineBoundaryChained_tail chainedFirst).2
          have t1LenBound : t1.length ≤ fuel := Nat.le_of_succ_le_succ lengthBound
          obtain ⟨matchedRemainder, extractEquiv, remainderChained, tailArcEqual⟩ :=
            spineArcHeadExtractionChained_ofCapArity bottomCount C1 c1Dom c1Cod t1 secondList
              chainedFirst chainedSecond arcEqual
          have matchedPure : AllCapArity matchedRemainder :=
            allCapArity_ofArcEqualToPureCap C1.codBoundaryLength t1 matchedRemainder t1Pure tailArcEqual
          have tailTrace : SpineTraceEquiv adjunctionModeSignature t1 matchedRemainder :=
            pureCapSpineSortFueled fuel C1.codBoundaryLength t1 matchedRemainder t1LenBound
              tailChainedFirst remainderChained t1Pure matchedPure tailArcEqual
          exact (SpineTraceEquiv.consCongr C1 tailTrace).trans extractEquiv.symm

/-- ★ **Pure-cap completeness (peel-first mirror of #2184).**  Two boundary-chained pure-cap spines
over a bottom boundary with EQUAL arc structure are trace-equivalent.  The walking-adjunction word
problem restricted to pure caps is thus DECIDED by the arc structure: equal planar-arc data forces a
chain of head-cap extractions between the two spines.  Proved by peeling the FIRST cap of one spine,
extracting and cancelling its partner in the other via the shipped arc-anchored cap-head discharge
`spineArcHeadExtractionChained_ofCapArity`, transferring the pure-cap regime to the remainder, and
recursing at the shrunk boundary.

Note the asymmetry with the cup case: NO positivity hypothesis (`0 < bottomCount`) is required — the
cap discharge derives the boundary width from the presence of the cap head, whereas the cup
transpositions need a positive seed. -/
theorem pureCapSpine_sort
    {overallSource overallTarget : adjunctionGraph.Mode} (bottomCount : Nat)
    (firstList secondList :
      List (SpineAtom adjunctionModeSignature overallSource overallTarget))
    (chainedFirst : SpineBoundaryChained bottomCount firstList)
    (chainedSecond : SpineBoundaryChained bottomCount secondList)
    (firstPureCap : AllCapArity firstList)
    (secondPureCap : AllCapArity secondList)
    (arcEqual : arcStructureOfSpineList bottomCount firstList
      = arcStructureOfSpineList bottomCount secondList) :
    SpineTraceEquiv adjunctionModeSignature firstList secondList :=
  pureCapSpineSortFueled firstList.length bottomCount firstList secondList
    (Nat.le_refl firstList.length) chainedFirst chainedSecond firstPureCap secondPureCap arcEqual

/-! ## Honesty marker -/

/-- **Honesty marker — pure-cap completeness `pureCapSpine_sort` is SHIPPED (peel-first mirror of
#2184).**  The full assembly is landed, zero-axiom, and NO gate flag is flipped (this is an INGREDIENT
of reify, not the whole reconstruction): the arc-transfer of the pure-cap regime
(`allCapArity_ofArcEqualToPureCap`), the equal-length reflection (`pureCapSpines_sameLength_ofArcEqual`),
the empty base case (`pureCapSpine_sort_nil`), and the top theorem `pureCapSpine_sort` — two
boundary-chained pure-cap spines over a bottom boundary with equal arc structure are `SpineTraceEquiv`,
with NO positivity assumption.  The heavy lifting rides the shipped cap-head discharge
`spineArcHeadExtractionChained_ofCapArity`; the cap arc-anchoring makes this STRICTLY EASIER than the
cup peel-last route (no merge-inversion linchpin, no positivity, no fuel-unsnoc locate).  What this
marker does NOT claim: the cup/cap-mixed word problem (this is the pure-cap restriction).  `= true`. -/
def fxMode_hasArcCapSortComplete : Bool := true

end FX1Poly.Polygraph
