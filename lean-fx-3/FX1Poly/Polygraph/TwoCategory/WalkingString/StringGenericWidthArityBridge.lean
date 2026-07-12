import FX1Poly.Polygraph.TwoCategory.WalkingString.StringAdjointStringSignatureClass
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringWidthZeroProcessSpineTracking

/-! # WalkingString — the GENERIC WIDTH-ARITY BRIDGE: the total cup/cap classifier + the open-wire boundary
tracking, over an arbitrary adjoint-string signature (FC-4 r5, B3 — the first generic sort brick)

The width-`0` pure-cup SORT's partner-LOCATE recursion rests on ONE colour-blind connectivity foundation: folding the
prefix of a boundary-chained pure-cup/cap spine moves the processed open-wire count along the boundary chain, and after
the prefix the open-wire count is exactly the last cup's dom-boundary width.  The shipped `k = 2` lane ships this as
`stringProcessSpine_openWires_length_ofChainedAppend` / `stringProcessSpine_prefix_openWires_eq_lastDomBoundary`
(`StringWidthZeroProcessSpineTracking`), whose ONLY signature-specific node is the TOTAL cup/cap classifier
`adjointTripleSpineAtom_hasCupOrCapArity` (every generator is a `(0, 2)` cup or a `(2, 0)` cap).

This file re-founds that connectivity foundation ONCE, uniform in colour count, over the class shipped in FC-4 r5 B1.
The `AdjointStringSignature` of B1 carries the DOM-arity discipline (`generatorDomLenZeroOrTwo`) the DETERMINACY
keystone consumes; the CONNECTIVITY engine needs the FULL `(dom, cod)` arity `AtomHasCupOrCapArity`, so this file
EXTENDS the class:

  * ★ `AdjointStringConnectivity` — `AdjointStringSignature` plus the full-arity field `generatorFullArity`
    (`(dom = 0 ∧ cod = 2) ∨ (dom = 2 ∧ cod = 0)`), instantiated at the shipped adjoint-TRIPLE seed
    (`adjointStringConnectivityAtTwo`, `k = 2`) AND the adjoint-QUADRUPLE seed (`adjointStringConnectivityAtThree`,
    `k = 3`).
  * ★ `genericSpineAtom_hasCupOrCapArity` — the generic TOTAL cup/cap classifier, a one-liner off the full-arity field
    (the `{signature}`-generic `AtomHasCupOrCapArity` is exactly the full-arity disjunction on the atom's generator
    boundary lengths).
  * ★★ `genericProcessSpine_openWires_length_ofChainedAppend` / `genericProcessSpine_prefix_openWires_eq_lastDomBoundary`
    — the open-wire boundary tracking, the FROZEN `k = 2` tracking proofs generic over the class: structural recursion
    on the prefix, each head atom's arity read off `genericSpineAtom_hasCupOrCapArity` feeding the already-generic
    tracking step `stepAtom_openWires_tracksBoundary`.

## The HONESTY LAW — the generic tracking fired at `k = 2` AND `k = 3`

  * ★ `k = 2` recovery — the generic tracking at `adjointStringConnectivityAtTwo` re-derives the NAMED shipped
    `stringProcessSpine_prefix_openWires_eq_lastDomBoundary` (the shipped lemma named as the recovery TARGET,
    inhabiting the same statement).
  * ★ `k = 3` fire — the generic tracking at `adjointStringConnectivityAtThree` fires on a genuine adjoint-quadruple
    cup, computing its dom-boundary width (non-vacuity).

## What this file does NOT do (the FLIP LAW, honest round boundary)

This lands the connectivity FOUNDATION the sort's LOCATE sits on (the `k = 2` lane's r15 brick, generic).  The
drop-injectivity linchpin (F1 `stringDropLastCup_matching_injective`), the chord-shift descents (F3), the fueled
partner-LOCATE (F4), and the fueled pure-cup SORT (F5) — each consuming this tracking — are the NAMED r6 bill, over
`signature × midWidth`.  The census marker `fxString_hasNColourAtomPinReroute` (`StringKParameterizationCensus`) STAYS
`false` (its bill is that full width-`0` quad sort).

ADDITIVE ONLY: no shipped WalkingString file is touched; the FROZEN `k = 2` tracking and the r5 B1 class are CONSUMED,
never edited.  Raw Lean 4 + Init; the full-arity fields are `cases`-`first` (propext-clean full enum), the classifier
is defeq, the tracking is STRUCTURAL recursion on the prefix (no `WellFounded.fix`), the recovery is an `abbrev`
inhabited by the shipped lemma and re-derived through the class, the fire is a concrete `SpineBoundaryChained`;
`propext`/`Quot.sound`/`Classical`/`sorry`/`native_decide`/`omega`-free.  Per-declaration `#assert_no_axioms` gated in
the audit twin plus an INDEPENDENT `#print axioms` witness. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## Private plumbing — `List.range` length (per-file copy, `propext`-free) -/

private theorem rangeLoopLength : (count : Nat) → (accumulated : List Nat) →
    (List.range.loop count accumulated).length = count + accumulated.length
  | 0, accumulated => (Nat.zero_add accumulated.length).symm
  | count + 1, accumulated => by
      have inner := rangeLoopLength count (count :: accumulated)
      show (List.range.loop count (count :: accumulated)).length = count + 1 + accumulated.length
      rw [inner]
      show count + (accumulated.length + 1) = count + 1 + accumulated.length
      rw [← Nat.add_assoc count accumulated.length 1, Nat.add_right_comm count accumulated.length 1]

private theorem rangeLength (count : Nat) : (List.range count).length = count := by
  show (List.range.loop count []).length = count
  rw [rangeLoopLength count []]; exact Nat.add_zero count

/-! ## The connectivity extension of the adjoint-string signature class -/

/-- ★★ **The adjoint-string CONNECTIVITY class.**  An `AdjointStringSignature` (the B1 determinacy carrier) extended
with the FULL `(dom, cod)` arity discipline the width-`0` connectivity engine consumes: every generator is a `(0, 2)`
cup or a `(2, 0)` cap.  Where the determinacy keystone (B2) needed only the DOM arity, the open-wire tracking needs the
full `AtomHasCupOrCapArity`, which this field supplies. -/
structure AdjointStringConnectivity extends AdjointStringSignature where
  /-- The full cup/cap arity: a generator has dom `0` / cod `2` (cup) or dom `2` / cod `0` (cap). -/
  generatorFullArity :
    ∀ {sourceMode targetMode : signature.graph.Mode}
      {generatorDom generatorCod : ModalityPath signature.graph sourceMode targetMode}
      (_generator : signature.twoCell generatorDom generatorCod),
      (generatorDom.length = 0 ∧ generatorCod.length = 2)
        ∨ (generatorDom.length = 2 ∧ generatorCod.length = 0)

/-! ## The `k = 2` / `k = 3` full-arity fields -/

/-- The `k = 2` full arity: a `StringTwoCell` is a `(0, 2)` cup (units) or a `(2, 0)` cap (counits). -/
theorem stringTripleGeneratorFullArity
    {sourceMode targetMode : AdjointTripleMode}
    {generatorDom generatorCod : ModalityPath adjointTripleGraph sourceMode targetMode}
    (generator : StringTwoCell generatorDom generatorCod) :
    (generatorDom.length = 0 ∧ generatorCod.length = 2)
      ∨ (generatorDom.length = 2 ∧ generatorCod.length = 0) := by
  cases generator <;> first | exact Or.inl ⟨rfl, rfl⟩ | exact Or.inr ⟨rfl, rfl⟩

/-- The `k = 3` full arity: a `StringQuadTwoCell` is a `(0, 2)` cup (three units) or a `(2, 0)` cap (three counits). -/
theorem quadGeneratorFullArity
    {sourceMode targetMode : AdjointQuadrupleMode}
    {generatorDom generatorCod : ModalityPath adjointQuadrupleGraph sourceMode targetMode}
    (generator : StringQuadTwoCell generatorDom generatorCod) :
    (generatorDom.length = 0 ∧ generatorCod.length = 2)
      ∨ (generatorDom.length = 2 ∧ generatorCod.length = 0) := by
  cases generator <;> first | exact Or.inl ⟨rfl, rfl⟩ | exact Or.inr ⟨rfl, rfl⟩

/-! ## The two connectivity instances -/

/-- ★ **The `k = 2` connectivity instance** — the shipped adjoint-TRIPLE class plus the four-generator full arity. -/
def adjointStringConnectivityAtTwo : AdjointStringConnectivity where
  toAdjointStringSignature := adjointStringSignatureAtTwo
  generatorFullArity := stringTripleGeneratorFullArity

/-- ★ **The `k = 3` connectivity instance** — the adjoint-QUADRUPLE class plus the six-generator full arity. -/
def adjointStringConnectivityAtThree : AdjointStringConnectivity where
  toAdjointStringSignature := adjointStringSignatureAtThree
  generatorFullArity := quadGeneratorFullArity

/-! ## The generic total cup/cap classifier -/

/-- ★ **The generic TOTAL cup/cap classifier.**  Every spine atom over a connectivity signature has cup-or-cap arity:
its generator's `(dom, cod)` boundary lengths are the full-arity disjunction, which is exactly `AtomHasCupOrCapArity`.
The `{signature}`-generic replacement for `adjointTripleSpineAtom_hasCupOrCapArity`. -/
theorem genericSpineAtom_hasCupOrCapArity (cls : AdjointStringConnectivity)
    {sourceMode targetMode : cls.signature.graph.Mode}
    (atom : SpineAtom cls.signature sourceMode targetMode) : AtomHasCupOrCapArity atom :=
  cls.generatorFullArity atom.generator

/-! ## The generic open-wire boundary tracking -/

/-- ★★ **The prefix fold's open-wire count tracks the boundary chain (generic).**  Structural recursion on the prefix:
each head atom's arity is read off the generic total classifier `genericSpineAtom_hasCupOrCapArity`, feeding the generic
tracking step `stepAtom_openWires_tracksBoundary`; the boundary advances to the head's cod and the tail stays chained.
The FROZEN `k = 2` `stringProcessSpine_openWires_length_ofChainedAppend`, generic over the class. -/
theorem genericProcessSpine_openWires_length_ofChainedAppend (cls : AdjointStringConnectivity)
    {overallSource overallTarget : cls.signature.graph.Mode} :
    (prefixAtoms suffixAtoms :
      List (SpineAtom cls.signature overallSource overallTarget)) →
    (state : WireState) → (boundaryLength : Nat) →
    state.openWires.length = boundaryLength →
    SpineBoundaryChained boundaryLength (prefixAtoms ++ suffixAtoms) →
    ∃ midBoundary : Nat,
      (processSpine state prefixAtoms).openWires.length = midBoundary
        ∧ SpineBoundaryChained midBoundary suffixAtoms
  | [], _, _, boundaryLength, tracks, chained => ⟨boundaryLength, tracks, chained⟩
  | headAtom :: restPrefix, suffixAtoms, state, _, tracks, chained => by
      obtain ⟨headFires, tailChained⟩ := spineBoundaryChained_tail chained
      have headArity := genericSpineAtom_hasCupOrCapArity cls headAtom
      have tracksEntry : state.openWires.length = headAtom.domBoundaryLength :=
        tracks.trans headFires.symm
      show ∃ midBoundary,
        (processSpine (stepAtom state headAtom) restPrefix).openWires.length = midBoundary
          ∧ SpineBoundaryChained midBoundary suffixAtoms
      exact genericProcessSpine_openWires_length_ofChainedAppend cls restPrefix suffixAtoms
        (stepAtom state headAtom) headAtom.codBoundaryLength
        (stepAtom_openWires_tracksBoundary state headAtom headArity tracksEntry) tailChained

/-- ★★ **After the prefix, the open-wire count equals the last cup's dom-boundary width (generic).**  The prefix fold
from the width-`bottomCount` seed lands its open-wire count at the boundary the trailing `lastCup` fires at, which the
chain pins to `lastCup.domBoundaryLength`.  The FROZEN `k = 2` `stringProcessSpine_prefix_openWires_eq_lastDomBoundary`,
generic over the class; bounds the last cup's window for the short-chord read-off. -/
theorem genericProcessSpine_prefix_openWires_eq_lastDomBoundary (cls : AdjointStringConnectivity)
    {overallSource overallTarget : cls.signature.graph.Mode} (bottomCount : Nat)
    (prefixAtoms : List (SpineAtom cls.signature overallSource overallTarget))
    (lastCup : SpineAtom cls.signature overallSource overallTarget)
    (chained : SpineBoundaryChained bottomCount (prefixAtoms ++ [lastCup])) :
    (processSpine ⟨List.range bottomCount, [], bottomCount, 0⟩ prefixAtoms).openWires.length
      = lastCup.domBoundaryLength := by
  obtain ⟨midBoundary, lenEq, chainedSuffix⟩ :=
    genericProcessSpine_openWires_length_ofChainedAppend cls prefixAtoms [lastCup]
      ⟨List.range bottomCount, [], bottomCount, 0⟩ bottomCount (rangeLength bottomCount) chained
  have lastFires : lastCup.domBoundaryLength = midBoundary :=
    (spineBoundaryChained_tail chainedSuffix).1
  rw [lenEq]; exact lastFires.symm

/-! ## `k = 2` RECOVERY — the generic tracking re-derives the NAMED shipped `k = 2` tracking -/

/-- The statement of the shipped `k = 2` prefix open-wire tracking, named as the recovery TARGET. -/
abbrev StringPrefixOpenWiresStatement : Prop :=
  ∀ {overallSource overallTarget : adjointTripleGraph.Mode} (bottomCount : Nat)
    (prefixAtoms : List (SpineAtom adjointTripleModeSignature overallSource overallTarget))
    (lastCup : SpineAtom adjointTripleModeSignature overallSource overallTarget),
    SpineBoundaryChained bottomCount (prefixAtoms ++ [lastCup]) →
    (processSpine ⟨List.range bottomCount, [], bottomCount, 0⟩ prefixAtoms).openWires.length
      = lastCup.domBoundaryLength

/-- ★ **The shipped `k = 2` tracking inhabits the named statement** —
`stringProcessSpine_prefix_openWires_eq_lastDomBoundary` IS the recovery target. -/
theorem stringPrefixOpenWires_shippedInhabitant : StringPrefixOpenWiresStatement :=
  @stringProcessSpine_prefix_openWires_eq_lastDomBoundary

/-- ★★ **The generic tracking, at `k = 2`, RE-DERIVES the shipped tracking** — the genuine consumption check at
`k = 2`. -/
theorem stringPrefixOpenWires_viaGenericClassAtTwo : StringPrefixOpenWiresStatement :=
  fun bottomCount prefixAtoms lastCup chained =>
    genericProcessSpine_prefix_openWires_eq_lastDomBoundary adjointStringConnectivityAtTwo
      bottomCount prefixAtoms lastCup chained

/-! ## `k = 3` FIRE — the generic tracking computes on a genuine adjoint-quadruple cup -/

/-- A genuine `k = 3` singleton cup chain: the unit `η1` (dom `nil`, cod `L1·L2`) fires at the width-`0` boundary. -/
def quadCupChainSingleton : SpineBoundaryChained 0 [quadCupAtomBase] :=
  SpineBoundaryChained.cons quadCupAtomBase rfl (SpineBoundaryChained.nil _)

/-- ★ **The generic tracking FIRES at `k = 3` on a genuine adjoint-quadruple cup.**  The empty-prefix fold's open-wire
count equals the cup `η1`'s dom-boundary width (`0`), computed through the class instance
`adjointStringConnectivityAtThree` — non-vacuity of the generic tracking at three colours. -/
theorem genericPrefixOpenWires_firesAtThreeOnCup :
    (processSpine ⟨List.range 0, [], 0, 0⟩
        ([] : List (SpineAtom adjointQuadrupleModeSignature AdjointQuadrupleMode.base AdjointQuadrupleMode.base))).openWires.length
      = quadCupAtomBase.domBoundaryLength :=
  genericProcessSpine_prefix_openWires_eq_lastDomBoundary adjointStringConnectivityAtThree
    0 [] quadCupAtomBase quadCupChainSingleton

/-! ## Road marker -/

/-- **★ ESTABLISHED — the generic width-arity bridge is machine-checked (FC-4 r5, B3, the first generic sort brick).**
`AdjointStringConnectivity` extends the r5 B1 class with the FULL `(dom, cod)` arity the width-`0` connectivity engine
consumes; `genericSpineAtom_hasCupOrCapArity` is the generic total cup/cap classifier off that field; and
`genericProcessSpine_openWires_length_ofChainedAppend` / `genericProcessSpine_prefix_openWires_eq_lastDomBoundary`
re-found the open-wire boundary tracking (the sort's LOCATE foundation) ONCE over the class — the FROZEN `k = 2`
tracking proofs with the total classifier swapped for the class field.  The HONESTY LAW discharged: the generic
tracking is instantiated at `k = 2` recovering the NAMED shipped
`stringProcessSpine_prefix_openWires_eq_lastDomBoundary` (`stringPrefixOpenWires_shippedInhabitant` /
`..._viaGenericClassAtTwo`) AND fired at `k = 3` on a genuine adjoint-quadruple cup
(`genericPrefixOpenWires_firesAtThreeOnCup`).

  What this marker does NOT close: the census marker `fxString_hasNColourAtomPinReroute`
  (`StringKParameterizationCensus`) STAYS `false` — its bill is the FULL width-`0` quad SORT.  This lands the
  connectivity FOUNDATION; the generic drop-injectivity (F1), chord-shift descents (F3), fueled partner-LOCATE (F4),
  and fueled pure-cup SORT (F5) — each consuming this tracking, over `signature × midWidth` — are the NAMED r6 bill.
  `= true`. -/
def fxString_hasGenericWidthArityBridge : Bool := true

end FX1Poly.Polygraph
