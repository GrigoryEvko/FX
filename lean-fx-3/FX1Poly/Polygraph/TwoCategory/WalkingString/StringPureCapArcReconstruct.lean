import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.GodementIndependence
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringPureCapSpineSort

/-! # WalkingString/StringPureCapArcReconstruct — the cap tails-cancel from `diagram` + internal cap counts
(FC-3 r27 B2a)

The mid-zero valley reassembly's CAP arm needs, from the cap block's boundary `diagram` agreement plus the
per-port `internalCapCounts` agreement, the FULL cap arc-structure equality that the unconditional pure-cap sort
consumes.  This is the string clone of the walking-adjunction `pureCapTailsCancel_ofDiagramAndInternalCap`
(`ValleyMatchingSpineTraceEquiv`), whose proof reconstructs the five `FullArcStructure` fields:

  * the boundary `diagram` (a hypothesis);
  * the total `cupCount` — `0` on both spines (`stringCupCountReflect` + `stringCupAtomCount_ofAllCapArity`);
  * the total `capCount` — the block length on both spines (`stringCapCountReflect` +
    `stringCapAtomCount_ofAllCapArity`, aligned by the length hypothesis);
  * the per-port `internalCupCounts` — uniformly `List.replicate total 0` on a pure-cap spine (no cup events),
    the two totals aligned through the shared `diagram.topCount` (`stringPureCapSpines_internalCupCountsAgree_ofDiagram`);
  * the per-port `internalCapCounts` (a hypothesis).

The two private `…CountReflect` lemmas are file-private in `StringPureCapSpineSort`, so this file re-declares its
own copies (the codebase pattern).  The internal-cup free leg is the cap dual of the shipped internal-cap
pointwise agreement: a pure-cap string spine records no cup events, so its whole `internalCupCounts` vector is a
constant-zero replicate, and equal `diagram`s force equal totals.

Raw Lean 4 + Init; structural / definitional, no `omega` / `simp`-AC / `WellFounded.fix`.  Per-declaration
`#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## Private range / list plumbing (per-file copies, following the codebase pattern) -/

/-- The range-loop's length is the count plus the seed length — hand-rolled (core `List.length_range`
leaks `propext` in this Init-only setting). -/
private theorem rangeLoopLength : (count : Nat) → (accumulated : List Nat) →
    (List.range.loop count accumulated).length = count + accumulated.length
  | 0, accumulated => (Nat.zero_add accumulated.length).symm
  | count + 1, accumulated => by
      have inner := rangeLoopLength count (count :: accumulated)
      show (List.range.loop count (count :: accumulated)).length = count + 1 + accumulated.length
      rw [inner]
      show count + (accumulated.length + 1) = count + 1 + accumulated.length
      rw [← Nat.add_assoc count accumulated.length 1, Nat.add_right_comm count accumulated.length 1]

/-- `(List.range count).length = count` — hand-rolled off `rangeLoopLength`. -/
private theorem rangeLength (count : Nat) : (List.range count).length = count := by
  show (List.range.loop count []).length = count
  rw [rangeLoopLength count []]
  exact Nat.add_zero count

/-- A list of length zero is nil — a `noConfusion` peel, staying `propext`-free. -/
private theorem listEqNilOfLengthZero {carrier : Type _} :
    (elems : List carrier) → elems.length = 0 → elems = []
  | [], _ => rfl
  | _ :: _, lengthZero => Nat.noConfusion lengthZero

/-- Mapping a constantly-zero function over any list yields `List.replicate` of zeros — structural. -/
private theorem mapConst0EqReplicate {carrier : Type _} (weightOf : carrier → Nat)
    (allZero : ∀ elem, weightOf elem = 0) :
    (elems : List carrier) → elems.map weightOf = List.replicate elems.length 0
  | [] => rfl
  | headElem :: restElems => by
      show weightOf headElem :: restElems.map weightOf = List.replicate (restElems.length + 1) 0
      rw [allZero headElem, mapConst0EqReplicate weightOf allZero restElems]
      rfl

/-! ## The arc COUNT reflections (file-private copies of `StringPureCapSpineSort`'s private kit) -/

/-- The arc structure's total `cupCount` reflects the boundary-independent cup-atom count — file-private copy of
`StringPureCapSpineSort`'s `stringCupCountReflect` (that copy is `private`, so it is re-derived here off the same
shared `processArcSpine_cupEventNodes_length`). -/
private theorem stringCupCountReflect
    {overallSource overallTarget : adjointTripleGraph.Mode} (bottomCount : Nat)
    (atoms : List (SpineAtom adjointTripleModeSignature overallSource overallTarget)) :
    (arcStructureOfSpineList bottomCount atoms).cupCount = cupAtomCount atoms := by
  show (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
      atoms).cupEventNodes.length = cupAtomCount atoms
  rw [processArcSpine_cupEventNodes_length]
  exact Nat.zero_add _

/-- The dual reflection: the arc structure's total `capCount` reflects the boundary-independent cap-atom count —
file-private copy of `StringPureCapSpineSort`'s `stringCapCountReflect`. -/
private theorem stringCapCountReflect
    {overallSource overallTarget : adjointTripleGraph.Mode} (bottomCount : Nat)
    (atoms : List (SpineAtom adjointTripleModeSignature overallSource overallTarget)) :
    (arcStructureOfSpineList bottomCount atoms).capCount = capAtomCount atoms := by
  show (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
      atoms).capEventNodes.length = capAtomCount atoms
  rw [processArcSpine_capEventNodes_length]
  exact Nat.zero_add _

/-! ## The cap-side internal CUP-count free leg (dual of the shipped internal-cap pointwise agreement) -/

/-- The arc `internalCupCounts` of a state with no cup events is `List.replicate total 0` — the per-port cup
turnback scan reads `internalEventCountAt … [] = 0` at every boundary port.  File-private copy of the
walking-adjunction `extractArc_internalCupCounts_eq_replicate_of_cupNil`; the body is `{signature}`-generic
(quantifies only over `bottomCount` and the raw `ArcWireState`). -/
private theorem extractArc_internalCupCounts_eq_replicate_of_cupNil
    (bottomCount : Nat) (state : ArcWireState) (cupNil : state.cupEventNodes = []) :
    (extractArc bottomCount state).internalCupCounts
      = List.replicate (bottomCount + state.openWires.length) 0 := by
  have expandMap : (extractArc bottomCount state).internalCupCounts
      = (List.range (bottomCount + state.openWires.length)).map
          (internalEventCountAt state.links (List.range bottomCount ++ state.openWires) []) := by
    dsimp only [extractArc]
    rw [cupNil]
  have allZero : ∀ index,
      internalEventCountAt state.links (List.range bottomCount ++ state.openWires) [] index = 0 :=
    fun _ => rfl
  rw [expandMap, mapConst0EqReplicate _ allZero, rangeLength]

/-- The arc structure's `diagram.topCount` IS the final open-wire count — a definitional projection through
`extractArc` / `extractDiagram`. -/
private theorem topCount_eq_openWiresLength
    {overallSource overallTarget : adjointTripleGraph.Mode} (bottomCount : Nat)
    (atoms : List (SpineAtom adjointTripleModeSignature overallSource overallTarget)) :
    (arcStructureOfSpineList bottomCount atoms).diagram.topCount
      = (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
          atoms).openWires.length := rfl

/-- ★ **A pure-cap string spine's internal cup-counts vanish.**  Every atom is a cap, so the arc fold records no
cup events (`cupEventNodes = []`, via `stringCupAtomCount_ofAllCapArity` and the boundary-independent
`processArcSpine_cupEventNodes_length`), and the per-port cup-turnback scan reads zero at every boundary port —
so the whole `internalCupCounts` vector is `List.replicate total 0`.  The three-generator analog of the
walking-adjunction `pureCapSpine_internalCupCounts_eq_replicate`. -/
theorem stringPureCapSpine_internalCupCounts_eq_replicate
    {overallSource overallTarget : adjointTripleGraph.Mode} (bottomCount : Nat)
    (atoms : List (SpineAtom adjointTripleModeSignature overallSource overallTarget))
    (pureCap : AllCapArity atoms) :
    (arcStructureOfSpineList bottomCount atoms).internalCupCounts
      = List.replicate
          (bottomCount
            + (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
                atoms).openWires.length)
          0 := by
  have cupZero : cupAtomCount atoms = 0 := stringCupAtomCount_ofAllCapArity atoms pureCap
  have cupNil :
      (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
          atoms).cupEventNodes = [] := by
    apply listEqNilOfLengthZero
    rw [processArcSpine_cupEventNodes_length]
    show (0 : Nat) + cupAtomCount atoms = 0
    rw [Nat.zero_add]
    exact cupZero
  exact extractArc_internalCupCounts_eq_replicate_of_cupNil bottomCount
    (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) atoms) cupNil

/-- ★ **Equal-diagram pure-cap string spines have agreeing internal cup-counts.**  Both spines' `internalCupCounts`
vectors are `List.replicate total 0` (`stringPureCapSpine_internalCupCounts_eq_replicate`), and their `diagram`
agreement forces `topCount = openWires.length` agreement, hence equal `total` — so the two vectors coincide.  The
cap block's cup-count free leg, phrased on the block `diagram` datum the valley hypothesis carries.  The
three-generator analog of the walking-adjunction `pureCapSpines_internalCupCountsAgree_ofDiagram`. -/
theorem stringPureCapSpines_internalCupCountsAgree_ofDiagram
    {overallSource overallTarget : adjointTripleGraph.Mode} (bottomCount : Nat)
    (firstList secondList : List (SpineAtom adjointTripleModeSignature overallSource overallTarget))
    (firstPureCap : AllCapArity firstList) (secondPureCap : AllCapArity secondList)
    (diagramAgree : (arcStructureOfSpineList bottomCount firstList).diagram
      = (arcStructureOfSpineList bottomCount secondList).diagram) :
    (arcStructureOfSpineList bottomCount firstList).internalCupCounts
      = (arcStructureOfSpineList bottomCount secondList).internalCupCounts := by
  have openWiresAgree :
      (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
          firstList).openWires.length
        = (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
          secondList).openWires.length := by
    rw [← topCount_eq_openWiresLength bottomCount firstList,
      ← topCount_eq_openWiresLength bottomCount secondList]
    exact congrArg DiagramType.topCount diagramAgree
  rw [stringPureCapSpine_internalCupCounts_eq_replicate bottomCount firstList firstPureCap,
    stringPureCapSpine_internalCupCounts_eq_replicate bottomCount secondList secondPureCap, openWiresAgree]

/-! ## The cap tails-cancel from its two genuine residuals -/

/-- ★ **The pure-cap base-case peel from its two genuine residuals.**  For equal-length pure-cap string spines,
the full arc equality `arc(firstList) = arc(secondList)` follows from just the boundary `diagram` agreement and
the `internalCapCounts` agreement: the two total count legs are supplied internally (`cupCount = 0` on both,
`capCount = length` on both, via the reflections and the pure-cap tallies) and the `internalCupCounts` leg by
`stringPureCapSpines_internalCupCountsAgree_ofDiagram` (a pure-cap spine has no cup events).  The three-generator
analog of the walking-adjunction `pureCapTailsCancel_ofDiagramAndInternalCap` — the small enabling clone the
mid-zero valley reassembly's CAP arm consumes. -/
theorem stringPureCapTailsCancel_ofDiagramAndInternalCap
    {overallSource overallTarget : adjointTripleGraph.Mode} (bottomCount : Nat)
    (firstList secondList : List (SpineAtom adjointTripleModeSignature overallSource overallTarget))
    (firstPureCap : AllCapArity firstList) (secondPureCap : AllCapArity secondList)
    (lengthEq : firstList.length = secondList.length)
    (diagramAgree : (arcStructureOfSpineList bottomCount firstList).diagram
        = (arcStructureOfSpineList bottomCount secondList).diagram)
    (internalCapCountsAgree :
      (arcStructureOfSpineList bottomCount firstList).internalCapCounts
        = (arcStructureOfSpineList bottomCount secondList).internalCapCounts) :
    arcStructureOfSpineList bottomCount firstList
      = arcStructureOfSpineList bottomCount secondList := by
  refine fullArcStructure_eq_of_fields diagramAgree ?_ ?_ ?_ internalCapCountsAgree
  · rw [stringCupCountReflect bottomCount firstList, stringCupCountReflect bottomCount secondList,
      stringCupAtomCount_ofAllCapArity firstList firstPureCap,
      stringCupAtomCount_ofAllCapArity secondList secondPureCap]
  · rw [stringCapCountReflect bottomCount firstList, stringCapCountReflect bottomCount secondList,
      stringCapAtomCount_ofAllCapArity firstList firstPureCap,
      stringCapAtomCount_ofAllCapArity secondList secondPureCap, lengthEq]
  · exact stringPureCapSpines_internalCupCountsAgree_ofDiagram bottomCount firstList secondList
      firstPureCap secondPureCap diagramAgree

end FX1Poly.Polygraph
