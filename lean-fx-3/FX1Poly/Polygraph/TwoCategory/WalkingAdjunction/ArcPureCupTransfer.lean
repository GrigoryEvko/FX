import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcPureCupSpine
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
second: interchange permutes the atom multiset, and the cap tally is a trace invariant
(`capAtomCount_eq_of_atomicTraceEquiv`), so a zero tally is preserved.  This lets the cup-interchange
base-case induction reorder a spine freely while staying pure cup.  Routed through the Nat cap count
(via the shipped `AllCupArity ↔ capAtomCount = 0` characterization) rather than an indexed inversion,
so it stays `propext`-free. -/
theorem allCupArity_preservedOfAtomicTraceEquiv
    {overallSource overallTarget : adjunctionGraph.Mode}
    {firstList secondList : List (SpineAtom adjunctionModeSignature overallSource overallTarget)}
    (atomicEquiv : AtomicTraceEquiv adjunctionModeSignature firstList secondList)
    (firstPureCup : AllCupArity firstList) : AllCupArity secondList := by
  have firstCapZero : capAtomCount firstList = 0 :=
    capAtomCount_ofAllCupArity firstList firstPureCup
  have countsAgree : capAtomCount firstList = capAtomCount secondList :=
    capAtomCount_eq_of_atomicTraceEquiv atomicEquiv
  exact allCupArity_ofCapAtomCountZero secondList (countsAgree.symm.trans firstCapZero)

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
`AllCupArity (headAtom :: rest)`.  A direct `cases` on the head-indexed `AllCupArity` would leak
`propext` (partial match on an indexed inductive); instead route through the cap count — the head
contributes a non-negative summand, so the tail's cap tally is still zero
(`addRightZero`) — and rebuild via `allCupArity_ofCapAtomCountZero`. -/
theorem allCupArity_ofCons
    {overallSource overallTarget : adjunctionGraph.Mode}
    {headAtom : SpineAtom adjunctionModeSignature overallSource overallTarget}
    {rest : List (SpineAtom adjunctionModeSignature overallSource overallTarget)}
    (consPureCup : AllCupArity (headAtom :: rest)) : AllCupArity rest := by
  have consCapZero : capAtomCount (headAtom :: rest) = 0 :=
    capAtomCount_ofAllCupArity (headAtom :: rest) consPureCup
  have restCapZero : capAtomCount rest = 0 := by
    dsimp only [capAtomCount] at consCapZero
    exact addRightZero consCapZero
  exact allCupArity_ofCapAtomCountZero rest restCapZero

/-! ## Honesty marker -/

/-- **Honesty marker — arc equality carries the pure-cup regime across both spines (cap-first base
case).**  `bothPureCup_ofCapCountZeroAndArcEqual`: the base-case guard `capAtomCount firstList = 0`
plus the whole-spine arc equality force `AllCupArity` on both spines; `capAtomCount_ofAllCupArity`
supplies the converse characterization; and `pureCupSpines_sameLength_ofArcEqual` (via
`cupAtomCount_ofAllCupArity`, a pure-cup spine's cup tally is its length) discharges the base case's
length-matching prerequisite; and `allCupArity_preservedOfAtomicTraceEquiv` shows the pure-cup regime
is closed under interchange, so the base-case induction may reorder freely; and `allCupArity_ofCons`
gives the `propext`-free cons-inversion (a pure-cup tail) the peel-and-recurse induction needs.  What
this marker does NOT claim: the base case's own cup-interchange completeness nor the cap-first
recursion.  `= true`. -/
def fxMode_hasArcPureCupTransfer : Bool := true

end FX1Poly.Polygraph
