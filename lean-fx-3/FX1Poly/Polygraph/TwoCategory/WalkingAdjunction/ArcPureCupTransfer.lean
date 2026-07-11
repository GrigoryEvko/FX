import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcPureCupSpine
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.AllCupAritySwapTransport
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.AtomCountTraceInvariance

/-! # ArcPureCupTransfer — arc equality carries the pure-cup regime across both spines (cap-first base case)

The cap-first reconstruction route (#2168) peels caps preferentially until the spine has none left,
then finishes the pure-cup remainder by cup-interchange (Godement) alone.  Its base case fires on the
guard `capAtomCount firstList = 0` (no caps to peel).  At that point the caller also holds the
whole-spine arc equality `arcStructureOfSpineList bottomCount firstList = arcStructureOfSpineList
bottomCount secondList` with the OTHER spine.  This brick shows the guard PROPAGATES across that
equality: BOTH spines are pure cup.

The total `capCount` of an arc structure reflects the boundary-independent cap-ATOM count
(`capCountReflect`, re-derived locally to keep this off the gate file `ArcReconstruction`, whose
reconstruction marker would cycle if imported).  So arc-equal spines carry equal cap-atom counts, and
a zero count on one side forces zero on the other — whence `AllCupArity` on both
(`allCupArity_ofCapAtomCountZero`).

  * `capAtomCount_ofAllCupArity` — the converse of `allCupArity_ofCapAtomCountZero`: a pure-cup spine
    has zero cap tally.  Together they make `AllCupArity ↔ capAtomCount = 0` a clean characterization
    the interchange base case can phrase in either direction.
  * ★ `bothPureCup_ofCapCountZeroAndArcEqual` — the transfer: the base-case guard plus the whole-spine
    arc equality force `AllCupArity` on BOTH spines.

What this brick does NOT claim: the base case's own content (equal-arc pure-cup spines are
cup-interchange equivalent) nor the cap-first recursion itself.

Raw Lean 4 + Init; per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-- The arc structure's total `capCount` reflects the boundary-independent cap-atom count — re-derived
locally (the gate file `ArcReconstruction` owns the shared copy; the transfer chain must not import it,
or flipping the reconstruction marker would cycle). -/
private theorem capCountReflect {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode} (bottomCount : Nat)
    (atoms : List (SpineAtom signature sourceMode targetMode)) :
    (arcStructureOfSpineList bottomCount atoms).capCount = capAtomCount atoms := by
  show (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
      atoms).capEventNodes.length = capAtomCount atoms
  rw [processArcSpine_capEventNodes_length]
  exact Nat.zero_add _

/-- The dual reflection: the arc structure's total `cupCount` reflects the boundary-independent cup-atom
count — re-derived locally for the same reason (keeping the length transfer off the gate file). -/
private theorem cupCountReflect {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode} (bottomCount : Nat)
    (atoms : List (SpineAtom signature sourceMode targetMode)) :
    (arcStructureOfSpineList bottomCount atoms).cupCount = cupAtomCount atoms := by
  show (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
      atoms).cupEventNodes.length = cupAtomCount atoms
  rw [processArcSpine_cupEventNodes_length]
  exact Nat.zero_add _

/-- **The converse of `allCupArity_ofCapAtomCountZero`.**  A pure-cup spine has zero cap tally: every
atom has cup arity `(0, 2)`, so its domain length is `0`, not `2`, and the cap guard never fires.  By
induction on the `AllCupArity` witness. -/
theorem capAtomCount_ofAllCupArity
    {overallSource overallTarget : adjunctionGraph.Mode}
    (atoms : List (SpineAtom adjunctionModeSignature overallSource overallTarget)) :
    AllCupArity atoms → capAtomCount atoms = 0 := by
  intro allCup
  induction allCup with
  | nil => rfl
  | cons hasCupDomArity hasCupCodArity restAllCup restCapZero =>
      rename_i headAtom rest
      dsimp only [capAtomCount]
      have guardFalse :
          ¬ (headAtom.generatorDom.length == 2 && headAtom.generatorCod.length == 0) = true := by
        rw [hasCupDomArity]
        exact Bool.noConfusion
      rw [if_neg guardFalse, Nat.zero_add]
      exact restCapZero

/-- **A pure-cup spine's cup tally is its length.**  Every atom has cup arity `(0, 2)`, so the cup guard
fires at every position and the fold counts one per atom.  By induction on the `AllCupArity` witness. -/
theorem cupAtomCount_ofAllCupArity
    {overallSource overallTarget : adjunctionGraph.Mode}
    (atoms : List (SpineAtom adjunctionModeSignature overallSource overallTarget)) :
    AllCupArity atoms → cupAtomCount atoms = atoms.length := by
  intro allCup
  induction allCup with
  | nil => rfl
  | cons hasCupDomArity hasCupCodArity restAllCup restLengthEq =>
      rename_i headAtom rest
      have guardTrue :
          (headAtom.generatorDom.length == 0 && headAtom.generatorCod.length == 2) = true := by
        rw [hasCupDomArity, hasCupCodArity]
        rfl
      show (if (headAtom.generatorDom.length == 0 && headAtom.generatorCod.length == 2) then 1 else 0)
          + cupAtomCount rest = (headAtom :: rest).length
      rw [if_pos guardTrue, List.length_cons, restLengthEq]
      exact Nat.add_comm 1 rest.length

/-- ★ **The pure-cup regime transfers across arc equality.**  The cap-first base-case guard
`capAtomCount firstList = 0` plus the whole-spine arc equality between the two spines force
`AllCupArity` on BOTH: the arc structure's total `capCount` reflects the cap-atom count
(`capCountReflect`), so arc-equal spines carry equal cap tallies; a zero tally on the first side
forces zero on the second, and both discharge through `allCupArity_ofCapAtomCountZero`. -/
theorem bothPureCup_ofCapCountZeroAndArcEqual
    {overallSource overallTarget : adjunctionGraph.Mode} (bottomCount : Nat)
    (firstList secondList : List (SpineAtom adjunctionModeSignature overallSource overallTarget))
    (firstCapZero : capAtomCount firstList = 0)
    (arcEqual : arcStructureOfSpineList bottomCount firstList
      = arcStructureOfSpineList bottomCount secondList) :
    AllCupArity firstList ∧ AllCupArity secondList := by
  have capCountsAgree : capAtomCount firstList = capAtomCount secondList := by
    have congrCapCount := congrArg FullArcStructure.capCount arcEqual
    rw [capCountReflect bottomCount firstList, capCountReflect bottomCount secondList] at congrCapCount
    exact congrCapCount
  have secondCapZero : capAtomCount secondList = 0 := capCountsAgree.symm.trans firstCapZero
  exact ⟨allCupArity_ofCapAtomCountZero firstList firstCapZero,
    allCupArity_ofCapAtomCountZero secondList secondCapZero⟩

/-- ★ **Equal-arc pure-cup spines have equal length.**  The cup-interchange base case reorders one pure-cup
spine into the other by disjoint-cup transpositions, which preserve length; this brick supplies the
prerequisite that the two spines it must relate ARE the same length.  The arc structure's total `cupCount`
reflects the cup-atom count (`cupCountReflect`), and a pure-cup spine's cup count IS its length
(`cupAtomCount_ofAllCupArity`), so arc-equal pure-cup spines carry equal length. -/
theorem pureCupSpines_sameLength_ofArcEqual
    {overallSource overallTarget : adjunctionGraph.Mode} (bottomCount : Nat)
    (firstList secondList : List (SpineAtom adjunctionModeSignature overallSource overallTarget))
    (firstPureCup : AllCupArity firstList) (secondPureCup : AllCupArity secondList)
    (arcEqual : arcStructureOfSpineList bottomCount firstList
      = arcStructureOfSpineList bottomCount secondList) :
    firstList.length = secondList.length := by
  have cupCountsAgree : cupAtomCount firstList = cupAtomCount secondList := by
    have congrCupCount := congrArg FullArcStructure.cupCount arcEqual
    rw [cupCountReflect bottomCount firstList, cupCountReflect bottomCount secondList] at congrCupCount
    exact congrCupCount
  rw [← cupAtomCount_ofAllCupArity firstList firstPureCup,
    ← cupAtomCount_ofAllCupArity secondList secondPureCup]
  exact cupCountsAgree

/-- ★ **The pure-cup regime is closed under interchange.**  If two spines are trace-equivalent
(`AtomicTraceEquiv` — the disjoint-atom-transposition closure) and the first is pure cup, so is the
second: interchange permutes the atom multiset, keeping each atom's generator, so the cup arities
transport directly.  Routed through the signature-generic `allCupArity_iff_ofAtomicTraceEquiv`
(Route B — the swap constructor is matched and the two head arities inverted), which drops the
walking-adjunction classifier `adjunctionSpineAtom_isCupOrCap` from this leg's closure and widens
it to any signature; probe-confirmed `propext`-free. -/
theorem allCupArity_preservedOfAtomicTraceEquiv {signature : ModeSignature}
    {overallSource overallTarget : signature.graph.Mode}
    {firstList secondList : List (SpineAtom signature overallSource overallTarget)}
    (atomicEquiv : AtomicTraceEquiv signature firstList secondList)
    (firstPureCup : AllCupArity firstList) : AllCupArity secondList :=
  (allCupArity_iff_ofAtomicTraceEquiv atomicEquiv).1 firstPureCup

/-- The right summand of a `Nat` sum that vanishes is itself zero — a `noConfusion` peel (the succ case's
`leftSummand + succ predRight` is defeq `succ (leftSummand + predRight)`, refuting `= 0`), staying
`propext`-free where `Nat.eq_zero_of_add_eq_zero_left` / `Nat.succ_ne_zero` would leak. -/
private theorem addRightZero {leftSummand rightSummand : Nat}
    (sumZero : leftSummand + rightSummand = 0) : rightSummand = 0 := by
  cases rightSummand with
  | zero => rfl
  | succ predRight => exact Nat.noConfusion sumZero

/-- ★ **`AllCupArity` cons-inversion, `propext`-free.**  A pure-cup spine's tail is pure cup.  The
completeness induction peels a head cup and recurses on the tail, so it needs `AllCupArity rest` from
`AllCupArity (headAtom :: rest)`.  Discharged by a DIRECT `cases` on the witness (the tail field falls
out) — machine-checked axiom-clean (`scratchpad/probe.lean`: the double-`cases` transport pattern
carries no `propext`), signature-generic, superseding the old cap-count detour. -/
theorem allCupArity_ofCons {signature : ModeSignature}
    {overallSource overallTarget : signature.graph.Mode}
    {headAtom : SpineAtom signature overallSource overallTarget}
    {rest : List (SpineAtom signature overallSource overallTarget)}
    (consPureCup : AllCupArity (headAtom :: rest)) : AllCupArity rest := by
  cases consPureCup with
  | cons _ _ restPureCup => exact restPureCup

/-- ★ **The last cup of a pure-cup append carries cup arity `(0, 2)`, classifier-free.**  Structural
recursion on `prefixAtoms`: at `[]` the append is the singleton `[lastCup]`, whose sole cup witness a
DIRECT `cases` reads as `lastCup`'s dom/cod arity; each cons peels the head and recurses on the shorter
append.  Route B (the `cases`-on-`AllCupArity` pattern is `propext`-free, `scratchpad/probe.lean`),
signature-generic — the string-usable replacement for the cap-count/`adjunctionSpineAtom_isCupOrCap`
`singletonCupArity`, so the width-0 machinery's last-cup arity read-off no longer routes through the
walking-adjunction classifier. -/
theorem allCupArity_lastCup_arity {signature : ModeSignature}
    {overallSource overallTarget : signature.graph.Mode} :
    (prefixAtoms : List (SpineAtom signature overallSource overallTarget)) →
    (lastCup : SpineAtom signature overallSource overallTarget) →
    AllCupArity (prefixAtoms ++ [lastCup]) →
    lastCup.generatorDom.length = 0 ∧ lastCup.generatorCod.length = 2
  | [], lastCup, appendPureCup => by
      cases appendPureCup with
      | cons hasCupDomArity hasCupCodArity _ => exact ⟨hasCupDomArity, hasCupCodArity⟩
  | headAtom :: restPrefix, lastCup, appendPureCup => by
      cases appendPureCup with
      | cons _ _ restAppendPureCup =>
          exact allCupArity_lastCup_arity restPrefix lastCup restAppendPureCup

/-! ## Pure-cup cap-count vanishing (the peel step's cap-count leg)

The cup peel step (`arcCupTailsCancel_ofCupHead_diagramAndInternals`) owes three orbit residuals: the
fresh boundary DIAGRAM leg and the two per-port INTERNAL count legs `internalCupCounts` /
`internalCapCounts`.  In the CAP-FIRST base case both peeled spines are pure cup, and a pure-cup spine
has NO cap events (`capEventNodes = []`), so its `internalCapCounts` is uniformly zero — collapsing the
`internalCapCounts` residual to a boundary-port (total) count agreement. -/

/-- A list of length zero is nil — a `noConfusion` peel on the cons case's `succ`-headed length,
staying `propext`-free where `List.eq_nil_of_length_eq_zero` (an iff-backed lemma) could leak. -/
private theorem listEqNilOfLengthZero {carrier : Type _} :
    (elems : List carrier) → elems.length = 0 → elems = []
  | [], _ => rfl
  | _ :: _, lengthZero => Nat.noConfusion lengthZero

/-- The range-loop's length is the count plus the seed length — hand-rolled (core `List.length_range`
leaks `propext` in this Init-only setting). -/
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

/-- `(List.range count).length = count` — hand-rolled off `rangeLoopLength` (core `List.length_range`
leaks `propext`). -/
private theorem rangeLength (count : Nat) : (List.range count).length = count := by
  show (List.range.loop count []).length = count
  rw [rangeLoopLength count []]
  exact Nat.add_zero count

/-- Mapping a constantly-zero function over any list yields `List.replicate` of zeros — structural on
the list, propext-free (each cons step is a defeq `replicate (n+1)` unfolding). -/
private theorem mapConst0EqReplicate {carrier : Type _} (weightOf : carrier → Nat)
    (allZero : ∀ elem, weightOf elem = 0) :
    (elems : List carrier) → elems.map weightOf = List.replicate elems.length 0
  | [] => rfl
  | headElem :: restElems => by
      show weightOf headElem :: restElems.map weightOf = List.replicate (restElems.length + 1) 0
      rw [allZero headElem, mapConst0EqReplicate weightOf allZero restElems]
      rfl

/-- The arc `internalCapCounts` of a state with no cap events is `List.replicate total 0` — the per-port
turnback scan reads `countEventsInRoot … [] = 0` at every boundary port, so the whole vector is zeros.
`total` is the boundary-port count `bottomCount + openWires.length`. -/
private theorem extractArc_internalCapCounts_eq_replicate_of_capNil
    (bottomCount : Nat) (state : ArcWireState) (capNil : state.capEventNodes = []) :
    (extractArc bottomCount state).internalCapCounts
      = List.replicate (bottomCount + state.openWires.length) 0 := by
  have expandMap : (extractArc bottomCount state).internalCapCounts
      = (List.range (bottomCount + state.openWires.length)).map
          (internalEventCountAt state.links (List.range bottomCount ++ state.openWires) []) := by
    dsimp only [extractArc]
    rw [capNil]
  have allZero : ∀ index,
      internalEventCountAt state.links (List.range bottomCount ++ state.openWires) [] index = 0 :=
    fun _ => rfl
  rw [expandMap, mapConst0EqReplicate _ allZero, rangeLength]

/-- ★ **A pure-cup spine's internal cap-counts vanish.**  Every atom is a cup, so the arc fold records
no cap events (`capEventNodes = []`, via `capAtomCount_ofAllCupArity` and the boundary-independent
`capCount` reflection), and the per-port cap-turnback scan reads zero at every boundary port.  So the
whole `internalCapCounts` vector is `List.replicate total 0` at the boundary-port count `total =
bottomCount + openWires.length`.  This is the cap-first base case's cap-count leg: the `internalCapCounts`
orbit residual collapses to a `total` (boundary-port) agreement. -/
theorem pureCupSpine_internalCapCounts_eq_replicate
    {overallSource overallTarget : adjunctionGraph.Mode}
    (bottomCount : Nat)
    (atoms : List (SpineAtom adjunctionModeSignature overallSource overallTarget))
    (pureCup : AllCupArity atoms) :
    (arcStructureOfSpineList bottomCount atoms).internalCapCounts
      = List.replicate
          (bottomCount
            + (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
                atoms).openWires.length)
          0 := by
  have capZero : capAtomCount atoms = 0 := capAtomCount_ofAllCupArity atoms pureCup
  have capNil :
      (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
          atoms).capEventNodes = [] := by
    apply listEqNilOfLengthZero
    rw [processArcSpine_capEventNodes_length]
    show (0 : Nat) + capAtomCount atoms = 0
    rw [Nat.zero_add]
    exact capZero
  exact extractArc_internalCapCounts_eq_replicate_of_capNil bottomCount
    (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) atoms) capNil

/-- ★ **Equal-total pure-cup spines have agreeing internal cap-counts.**  Both spines' `internalCapCounts`
vectors are `List.replicate total 0` (`pureCupSpine_internalCapCounts_eq_replicate`), so once their
boundary-port totals agree the two vectors are equal — the peel step's `internalCapCountsAgree` residual
in the cap-first base case, reduced to the `total` bookkeeping the diagram leg already carries. -/
theorem pureCupSpines_internalCapCountsAgree
    {overallSource overallTarget : adjunctionGraph.Mode} (bottomCount : Nat)
    (firstList secondList : List (SpineAtom adjunctionModeSignature overallSource overallTarget))
    (firstPureCup : AllCupArity firstList) (secondPureCup : AllCupArity secondList)
    (totalAgree :
      bottomCount + (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
          firstList).openWires.length
        = bottomCount + (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
          secondList).openWires.length) :
    (arcStructureOfSpineList bottomCount firstList).internalCapCounts
      = (arcStructureOfSpineList bottomCount secondList).internalCapCounts := by
  rw [pureCupSpine_internalCapCounts_eq_replicate bottomCount firstList firstPureCup,
    pureCupSpine_internalCapCounts_eq_replicate bottomCount secondList secondPureCup, totalAgree]

/-! ## The pure-cup boundary-port count (discharging the `total` agreement from equal length)

The `internalCapCounts` agreement above takes the two spines' boundary-port `total`
(`bottomCount + openWires.length`) as a hypothesis.  A pure-cup spine allocates exactly two open
wires per cup (`stepCupArc` splices `[leftLeg, rightLeg]`), so its final `openWires.length` is the
seed length plus `2 * (number of cups) = 2 * length`.  Equal-length pure-cup spines therefore carry
equal `total`, discharging the hypothesis — the peel step supplies tail length equality, not tail arc
equality. -/

/-- `(xs ++ ys).length = xs.length + ys.length` — hand-rolled (core `List.length_append` leaks
`propext` in this Init-only setting), structural on `xs`. -/
private theorem lengthAppend : (xs ys : List Nat) → (xs ++ ys).length = xs.length + ys.length
  | [], ys => (Nat.zero_add ys.length).symm
  | headWire :: restWires, ys => by
      show (restWires ++ ys).length + 1 = (restWires.length + 1) + ys.length
      rw [lengthAppend restWires ys]
      exact Nat.add_right_comm restWires.length ys.length 1

/-- Inserting a `block` at any position grows the wire list's length by `block.length` — the position
is irrelevant (out-of-range inserts append the block onto the exhausted tail).  Structural, mirroring
`natListInsertAt`'s three arms. -/
private theorem natListInsertAt_length :
    (wires : List Nat) → (position : Nat) → (block : List Nat) →
    (natListInsertAt wires position block).length = wires.length + block.length
  | [], 0, block => by
      show (block ++ ([] : List Nat)).length = ([] : List Nat).length + block.length
      rw [lengthAppend block []]
      exact Nat.add_comm block.length ([] : List Nat).length
  | [], _ + 1, block => (Nat.zero_add block.length).symm
  | headWire :: restWires, 0, block => by
      show (block ++ (headWire :: restWires)).length
        = (headWire :: restWires).length + block.length
      rw [lengthAppend block (headWire :: restWires)]
      exact Nat.add_comm block.length (headWire :: restWires).length
  | headWire :: restWires, position + 1, block => by
      show (natListInsertAt restWires position block).length + 1
        = (restWires.length + 1) + block.length
      rw [natListInsertAt_length restWires position block]
      exact Nat.add_right_comm restWires.length block.length 1

/-- A cup arc step adds exactly two open wires — it splices the two fresh leg ids at its window. -/
private theorem stepCupArc_openWires_length (state : ArcWireState) (position : Nat) :
    (stepCupArc state position).openWires.length = state.openWires.length + 2 := by
  show (natListInsertAt state.openWires position [state.nextFresh, state.nextFresh + 1]).length
    = state.openWires.length + 2
  rw [natListInsertAt_length]
  rfl

/-- A cup-arity atom's arc step IS the cup step at its window — the two arity equalities pick the cup
branch of `stepArcAtom`'s arity match (inlined to keep this off `ArcDisciplineFold`). -/
private theorem stepArcAtom_cupReduce {overallSource overallTarget : adjunctionGraph.Mode}
    (state : ArcWireState)
    (atom : SpineAtom adjunctionModeSignature overallSource overallTarget)
    (hasCupDomArity : atom.generatorDom.length = 0)
    (hasCupCodArity : atom.generatorCod.length = 2) :
    stepArcAtom state atom = stepCupArc state atom.leftContext.length := by
  dsimp only [stepArcAtom]
  rw [hasCupDomArity, hasCupCodArity]

/-- **A pure-cup spine's final open-wire count is the seed plus `2 * length`.**  Every atom is a cup,
so every fold step is `stepCupArc`, which adds two wires; the count accumulates `2` per atom.  By
induction on the `AllCupArity` witness, generalized over the running state. -/
private theorem pureCupProcessArcSpine_openWires_length
    {overallSource overallTarget : adjunctionGraph.Mode}
    (atoms : List (SpineAtom adjunctionModeSignature overallSource overallTarget))
    (pureCup : AllCupArity atoms) :
    ∀ (state : ArcWireState),
      (processArcSpine state atoms).openWires.length
        = state.openWires.length + 2 * atoms.length := by
  induction pureCup with
  | nil =>
      intro state
      show state.openWires.length = state.openWires.length + 2 * 0
      rw [Nat.mul_zero, Nat.add_zero]
  | cons hasCupDomArity hasCupCodArity restAllCup restIH =>
      rename_i headAtom rest
      intro state
      show (processArcSpine (stepArcAtom state headAtom) rest).openWires.length
        = state.openWires.length + 2 * (rest.length + 1)
      rw [stepArcAtom_cupReduce state headAtom hasCupDomArity hasCupCodArity,
        restIH (stepCupArc state headAtom.leftContext.length),
        stepCupArc_openWires_length]
      show state.openWires.length + 2 + 2 * rest.length
        = state.openWires.length + (2 * rest.length + 2)
      rw [Nat.add_assoc, Nat.add_comm 2 (2 * rest.length)]

/-- ★ **Equal-length pure-cup spines have agreeing internal cap-counts.**  A pure-cup spine's boundary
port count `total = bottomCount + openWires.length` is `bottomCount + (List.range bottomCount).length
+ 2 * length` (`pureCupProcessArcSpine_openWires_length`), so equal length forces equal `total`,
discharging the `total` hypothesis of `pureCupSpines_internalCapCountsAgree`.  This is the peel step's
`internalCapCounts` residual in the cap-first base case, phrased on the datum the peel actually holds:
tail length equality (from the whole-spine equal-length fact through the located bubble). -/
theorem pureCupSpines_internalCapCountsAgree_ofLengthEq
    {overallSource overallTarget : adjunctionGraph.Mode} (bottomCount : Nat)
    (firstList secondList : List (SpineAtom adjunctionModeSignature overallSource overallTarget))
    (firstPureCup : AllCupArity firstList) (secondPureCup : AllCupArity secondList)
    (lengthEq : firstList.length = secondList.length) :
    (arcStructureOfSpineList bottomCount firstList).internalCapCounts
      = (arcStructureOfSpineList bottomCount secondList).internalCapCounts := by
  apply pureCupSpines_internalCapCountsAgree bottomCount firstList secondList firstPureCup
    secondPureCup
  rw [pureCupProcessArcSpine_openWires_length firstList firstPureCup
        (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []),
    pureCupProcessArcSpine_openWires_length secondList secondPureCup
        (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []),
    lengthEq]

/-! ## The pure-cup base-case peel reduced to its two genuine residuals

`FullArcStructure` is a flat five-field record, so the peel equality
`arc(firstList) = arc(secondList)` reconstructs field by field.  For equal-length pure-cup spines
THREE of the five fields are already discharged: both total count legs (`capCount = 0`, `cupCount =
length`) via the shipped reflections, and the `internalCapCounts` leg via
`pureCupSpines_internalCapCountsAgree_ofLengthEq`.  This isolates the pure-cup base case to EXACTLY
its two genuine residuals — the fresh boundary `diagram` and the `internalCupCounts` de-merge — the
same two the general cup peel owes, mirroring `arcCupTailsCancel_ofCupHead_diagramAndInternals`. -/

/-- ★ **The pure-cup base-case peel from its two genuine residuals.**  For equal-length pure-cup
spines, the full peel equality `arc(firstList) = arc(secondList)` follows from just the fresh boundary
`diagram` agreement and the `internalCupCounts` agreement: the two total count legs are supplied
internally (`capCount = 0` on both, `cupCount = length` on both, via the shipped reflections and the
pure-cup tallies) and the `internalCapCounts` leg by `pureCupSpines_internalCapCountsAgree_ofLengthEq`.
This is the cap-first base case's own tails-cancel, reduced to exactly the diagram + cup-count-de-merge
residuals — the same two the general cup peel is charged with. -/
theorem pureCupTailsCancel_ofDiagramAndInternalCup
    {overallSource overallTarget : adjunctionGraph.Mode} (bottomCount : Nat)
    (firstList secondList : List (SpineAtom adjunctionModeSignature overallSource overallTarget))
    (firstPureCup : AllCupArity firstList) (secondPureCup : AllCupArity secondList)
    (lengthEq : firstList.length = secondList.length)
    (diagramAgree : (arcStructureOfSpineList bottomCount firstList).diagram
        = (arcStructureOfSpineList bottomCount secondList).diagram)
    (internalCupCountsAgree :
      (arcStructureOfSpineList bottomCount firstList).internalCupCounts
        = (arcStructureOfSpineList bottomCount secondList).internalCupCounts) :
    arcStructureOfSpineList bottomCount firstList
      = arcStructureOfSpineList bottomCount secondList := by
  refine fullArcStructure_eq_of_fields diagramAgree ?_ ?_ internalCupCountsAgree ?_
  · rw [cupCountReflect bottomCount firstList, cupCountReflect bottomCount secondList,
      cupAtomCount_ofAllCupArity firstList firstPureCup,
      cupAtomCount_ofAllCupArity secondList secondPureCup, lengthEq]
  · rw [capCountReflect bottomCount firstList, capCountReflect bottomCount secondList,
      capAtomCount_ofAllCupArity firstList firstPureCup,
      capAtomCount_ofAllCupArity secondList secondPureCup]
  · exact pureCupSpines_internalCapCountsAgree_ofLengthEq bottomCount firstList secondList
      firstPureCup secondPureCup lengthEq

/-! ## Honesty marker -/

/-- **Honesty marker — arc equality carries the pure-cup regime across both spines (cap-first base
case).**  `bothPureCup_ofCapCountZeroAndArcEqual`: the base-case guard `capAtomCount firstList = 0`
plus the whole-spine arc equality force `AllCupArity` on both spines; `capAtomCount_ofAllCupArity`
supplies the converse characterization; and `pureCupSpines_sameLength_ofArcEqual` (via
`cupAtomCount_ofAllCupArity`, a pure-cup spine's cup tally is its length) discharges the base case's
length-matching prerequisite; and `allCupArity_preservedOfAtomicTraceEquiv` shows the pure-cup regime
is closed under interchange, so the base-case induction may reorder freely; and `allCupArity_ofCons`
gives the `propext`-free cons-inversion (a pure-cup tail) the peel-and-recurse induction needs; and
`pureCupSpine_internalCapCounts_eq_replicate` / `pureCupSpines_internalCapCountsAgree` discharge the
cup peel step's `internalCapCounts` orbit residual in the cap-first base case — a pure-cup spine has no
cap events, so its internal cap-count vector is uniformly zero and two equal-total pure-cup spines'
vectors agree.  What this marker does NOT claim: the base case's own cup-interchange completeness, the
peel step's remaining two residuals (the fresh boundary diagram leg + the `internalCupCounts` leg), nor
the cap-first recursion.  `= true`. -/
def fxMode_hasArcPureCupTransfer : Bool := true

end FX1Poly.Polygraph
