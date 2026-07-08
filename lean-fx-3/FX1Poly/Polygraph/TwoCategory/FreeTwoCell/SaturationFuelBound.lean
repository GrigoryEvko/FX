import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.ClassSaturation
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.FrontExtraction

/-! # SaturationFuelBound — a complete class enumeration discharges the BFS fuel gate (FREE-7)

The shipped saturation decider (`ClassSaturation.lean`) is gated on `didExhaustFrontier`:
the fuel must empty the frontier.  This file discharges that gate CONDITIONALLY on a
finite enumeration of the seed's ~-class, via a potential-function argument:

  * the potential of a search state is `frontier.length + (bound + 1) * unvisited`, where
    `unvisited` counts the class-enumeration entries not yet visited and `bound` caps the
    per-trace successor count;
  * every worker step strictly decreases it — popping a frontier trace costs one, and each
    batch of fresh successors pays for its own frontier growth by newly visiting at least
    one enumeration entry (`fresh ⊆ ~-class ⊆ classList`, and fresh traces are unvisited
    by the filter);
  * `swapSuccessors_lengthBound` — the successor cap: at most two candidates per adjacent
    position, so `2 * length` many, and trace-equivalent lists share their length, so ONE
    cap serves the whole class;
  * ★ `didExhaustFrontier_ofPotentialBound` — fuel at least the potential exhausts the
    frontier (the conditional termination theorem);
  * ★ `decideAtomicTraceEquivOfCompleteClassList` — the decider, UN-gated on fuel: any
    list containing every trace equivalent to the seed (no dup-freedom, no exactness
    required) yields `Decidable (AtomicTraceEquiv seed target)` outright with the
    computable fuel `classSaturationFuel`.

HONESTY: this file discharges the fuel CONDITIONALLY on a complete class list.  The
remaining hypothesis — CONSTRUCTING a complete class enumeration — has since LANDED via
the bounded-atom-universe route (`TotalWordProblemDecision.chainedSeedClassList_isComplete`,
all words of the seed's length over its finite atom universe), which this file's
`decideAtomicTraceEquivOfCompleteClassList` turns into the unconditional total decision
`decideTwoCellConvFull`, flipping `fxMode_hasUngatedFreeTwoCellDecision = true`.

Also ships the hand-rolled zero-axiom length kit (`listLengthAppend`, `listLengthMap`,
`listLengthFilterLe`, `listLengthFilterMono`, `listLengthFilterStrictMono`,
`natMulLeftMono`) — the core `List.length_append` / `List.length_map` lemmas leak
`propext`, the documented trap.

Raw Lean 4 + Init; per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## The hand-rolled length kit -/

/-- List append adds lengths — reproved by hand (`List.length_append` leaks `propext`). -/
theorem listLengthAppend {elementType : Type} :
    (front back : List elementType) →
    (front ++ back).length = front.length + back.length
  | [], back => (Nat.zero_add back.length).symm
  | _headElement :: tail, back => by
      show (tail ++ back).length + 1 = tail.length + 1 + back.length
      rw [listLengthAppend tail back, Nat.add_right_comm]

/-- List map preserves length — reproved by hand (`List.length_map` leaks `propext`). -/
theorem listLengthMap {sourceType targetType : Type} (transform : sourceType → targetType) :
    (inputList : List sourceType) →
    (inputList.map transform).length = inputList.length
  | [] => rfl
  | _headElement :: tail => congrArg (· + 1) (listLengthMap transform tail)

/-- A filter never lengthens its input. -/
theorem listLengthFilterLe {elementType : Type} (predicate : elementType → Bool) :
    (inputList : List elementType) →
    (inputList.filter predicate).length ≤ inputList.length
  | [] => Nat.le.refl
  | headElement :: tail => by
      show (match predicate headElement with
        | true => headElement :: tail.filter predicate
        | false => tail.filter predicate).length ≤ tail.length + 1
      cases predicate headElement with
      | true => exact Nat.succ_le_succ (listLengthFilterLe predicate tail)
      | false => exact Nat.le_succ_of_le (listLengthFilterLe predicate tail)

/-- Filter length is monotone under pointwise predicate implication. -/
theorem listLengthFilterMono {elementType : Type}
    {strongPredicate weakPredicate : elementType → Bool} :
    (inputList : List elementType) →
    (∀ element, element ∈ inputList →
      strongPredicate element = true → weakPredicate element = true) →
    (inputList.filter strongPredicate).length ≤ (inputList.filter weakPredicate).length
  | [], _implication => Nat.le.refl
  | headElement :: tail, implication => by
      have tailImplication : ∀ element, element ∈ tail →
          strongPredicate element = true → weakPredicate element = true :=
        fun element elementMem =>
          implication element (List.Mem.tail headElement elementMem)
      show (match strongPredicate headElement with
        | true => headElement :: tail.filter strongPredicate
        | false => tail.filter strongPredicate).length ≤
        (match weakPredicate headElement with
          | true => headElement :: tail.filter weakPredicate
          | false => tail.filter weakPredicate).length
      cases strongRuns : strongPredicate headElement with
      | true =>
          rw [implication headElement (List.Mem.head tail) strongRuns]
          exact Nat.succ_le_succ (listLengthFilterMono tail tailImplication)
      | false =>
          cases weakPredicate headElement with
          | true => exact Nat.le_succ_of_le (listLengthFilterMono tail tailImplication)
          | false => exact listLengthFilterMono tail tailImplication

/-- Filter length drops STRICTLY under pointwise implication when a witness passes the
weak predicate but fails the strong one. -/
theorem listLengthFilterStrictMono {elementType : Type}
    {strongPredicate weakPredicate : elementType → Bool} {witness : elementType} :
    (inputList : List elementType) →
    (∀ element, element ∈ inputList →
      strongPredicate element = true → weakPredicate element = true) →
    witness ∈ inputList →
    strongPredicate witness = false →
    weakPredicate witness = true →
    (inputList.filter strongPredicate).length + 1 ≤
      (inputList.filter weakPredicate).length
  | [], _implication, witnessMem, _strongRefutes, _weakFires => nomatch witnessMem
  | headElement :: tail, implication, witnessMem, strongRefutes, weakFires => by
      have tailImplication : ∀ element, element ∈ tail →
          strongPredicate element = true → weakPredicate element = true :=
        fun element elementMem =>
          implication element (List.Mem.tail headElement elementMem)
      show (match strongPredicate headElement with
        | true => headElement :: tail.filter strongPredicate
        | false => tail.filter strongPredicate).length + 1 ≤
        (match weakPredicate headElement with
          | true => headElement :: tail.filter weakPredicate
          | false => tail.filter weakPredicate).length
      cases witnessMem with
      | head =>
          rw [strongRefutes, weakFires]
          exact Nat.succ_le_succ (listLengthFilterMono tail
            (fun element elementMem =>
              implication element (List.Mem.tail _ elementMem)))
      | tail _headElement innerMem =>
          cases strongRuns : strongPredicate headElement with
          | true =>
              rw [implication headElement (List.Mem.head tail) strongRuns]
              exact Nat.succ_le_succ (listLengthFilterStrictMono tail tailImplication
                innerMem strongRefutes weakFires)
          | false =>
              cases weakPredicate headElement with
              | true =>
                  exact Nat.le_succ_of_le (listLengthFilterStrictMono tail
                    tailImplication innerMem strongRefutes weakFires)
              | false =>
                  exact listLengthFilterStrictMono tail tailImplication innerMem
                    strongRefutes weakFires

/-- Left multiplication is monotone — by induction on the order witness (the core
multiplication-monotonicity lemmas route through `propext`-leaking rewrites). -/
theorem natMulLeftMono (factor : Nat) {smaller larger : Nat}
    (isLessEqual : smaller ≤ larger) : factor * smaller ≤ factor * larger := by
  induction isLessEqual with
  | refl => exact Nat.le.refl
  | step _boundStep innerHypothesis =>
      exact Nat.le_trans innerHypothesis (Nat.le_add_right _ factor)

/-! ## The successor cap -/

/-- ★ **The successor cap**: a trace has at most `2 * length` one-swap successors — at
most one forward and one reverse candidate per adjacent position. -/
theorem swapSuccessors_lengthBound {signature : ModeSignature}
    (modeDecEq : DecidableEq signature.graph.Mode)
    (modalityDecEq : (sourceMode targetMode : signature.graph.Mode) →
      DecidableEq (signature.graph.Modality sourceMode targetMode))
    {overallSource overallTarget : signature.graph.Mode} :
    (trace : List (SpineAtom signature overallSource overallTarget)) →
    (swapSuccessors modeDecEq modalityDecEq trace).length ≤ 2 * trace.length
  | [] => Nat.le.refl
  | [_lastAtom] => Nat.zero_le _
  | firstAtom :: secondAtom :: rest => by
      show ((match recognizeAdjacentSwap modeDecEq modalityDecEq firstAtom secondAtom with
          | PSum.inl witness =>
              [witness.firstAfterSwap :: witness.secondAfterSwap :: rest]
          | PSum.inr _ => []) ++
        ((match recognizeReverseAdjacentSwap modeDecEq modalityDecEq firstAtom
              secondAtom with
          | PSum.inl witness => [witness.movedFront :: witness.stayedBehind :: rest]
          | PSum.inr _ => []) ++
          (swapSuccessors modeDecEq modalityDecEq (secondAtom :: rest)).map
            (fun deeperTrace => firstAtom :: deeperTrace))).length ≤
        2 * (rest.length + 1 + 1)
      rw [listLengthAppend, listLengthAppend, listLengthMap]
      have forwardArmBound : (match recognizeAdjacentSwap modeDecEq modalityDecEq
          firstAtom secondAtom with
        | PSum.inl witness =>
            [witness.firstAfterSwap :: witness.secondAfterSwap :: rest]
        | PSum.inr _ => []).length ≤ 1 := by
        cases recognizeAdjacentSwap modeDecEq modalityDecEq firstAtom secondAtom with
        | inl _witness => exact Nat.le.refl
        | inr _refuted => exact Nat.zero_le 1
      have reverseArmBound : (match recognizeReverseAdjacentSwap modeDecEq modalityDecEq
          firstAtom secondAtom with
        | PSum.inl witness => [witness.movedFront :: witness.stayedBehind :: rest]
        | PSum.inr _ => []).length ≤ 1 := by
        cases recognizeReverseAdjacentSwap modeDecEq modalityDecEq firstAtom
            secondAtom with
        | inl _witness => exact Nat.le.refl
        | inr _refuted => exact Nat.zero_le 1
      have deeperBound := swapSuccessors_lengthBound modeDecEq modalityDecEq
        (secondAtom :: rest)
      refine Nat.le_trans
        (Nat.add_le_add forwardArmBound (Nat.add_le_add reverseArmBound deeperBound))
        (Nat.le_of_eq ?_)
      rw [← Nat.add_assoc]
      exact Nat.add_comm 2 (2 * (rest.length + 1))

/-! ## Fresh-candidate counting -/

/-- Is the candidate NOT yet on the visited list?  The saturation filter's predicate,
factored out so the counting lemmas can speak about it. -/
def isFreshAgainst {elementType : Type} (elementDecEq : DecidableEq elementType)
    (visited : List elementType) (candidate : elementType) : Bool :=
  match listMemDecidable elementDecEq candidate visited with
  | Decidable.isTrue _ => false
  | Decidable.isFalse _ => true

/-- How many enumeration entries are not yet visited — the potential's decreasing
component. -/
def freshCandidateCount {elementType : Type} (elementDecEq : DecidableEq elementType)
    (visited classList : List elementType) : Nat :=
  (classList.filter (isFreshAgainst elementDecEq visited)).length

/-- An unvisited candidate is fresh. -/
theorem isFreshAgainst_ofNotMem {elementType : Type}
    (elementDecEq : DecidableEq elementType) {visited : List elementType}
    {candidate : elementType} (notVisited : ¬ candidate ∈ visited) :
    isFreshAgainst elementDecEq visited candidate = true := by
  show (match listMemDecidable elementDecEq candidate visited with
    | Decidable.isTrue _ => false
    | Decidable.isFalse _ => true) = true
  cases listMemDecidable elementDecEq candidate visited with
  | isTrue visitedMem => exact absurd visitedMem notVisited
  | isFalse _ => rfl

/-- A visited candidate is not fresh. -/
theorem isFreshAgainst_ofMem {elementType : Type}
    (elementDecEq : DecidableEq elementType) {visited : List elementType}
    {candidate : elementType} (visitedMem : candidate ∈ visited) :
    isFreshAgainst elementDecEq visited candidate = false := by
  show (match listMemDecidable elementDecEq candidate visited with
    | Decidable.isTrue _ => false
    | Decidable.isFalse _ => true) = false
  cases listMemDecidable elementDecEq candidate visited with
  | isTrue _ => rfl
  | isFalse notMem => exact absurd visitedMem notMem

/-- A fresh candidate is unvisited (the inversion of `isFreshAgainst_ofNotMem`). -/
theorem notMem_ofIsFreshAgainst {elementType : Type}
    (elementDecEq : DecidableEq elementType) {visited : List elementType}
    {candidate : elementType}
    (isFresh : isFreshAgainst elementDecEq visited candidate = true) :
    ¬ candidate ∈ visited := by
  intro visitedMem
  rw [isFreshAgainst_ofMem elementDecEq visitedMem] at isFresh
  exact (nomatch isFresh)

/-- Growing the visited list never raises the fresh count. -/
theorem freshCandidateCount_appendLe {elementType : Type}
    (elementDecEq : DecidableEq elementType)
    (visited extraVisited classList : List elementType) :
    freshCandidateCount elementDecEq (visited ++ extraVisited) classList ≤
      freshCandidateCount elementDecEq visited classList :=
  listLengthFilterMono classList (fun _element _elementMem extendedFresh =>
    isFreshAgainst_ofNotMem elementDecEq (fun visitedMem =>
      notMem_ofIsFreshAgainst elementDecEq extendedFresh
        (listMemAppendOfLeft extraVisited visitedMem)))

/-- ★ Newly visiting an enumeration entry drops the fresh count STRICTLY. -/
theorem freshCandidateCount_strictDecrease {elementType : Type}
    (elementDecEq : DecidableEq elementType)
    {visited extraVisited classList : List elementType} {freshWitness : elementType}
    (witnessInClass : freshWitness ∈ classList)
    (witnessNotVisited : ¬ freshWitness ∈ visited)
    (witnessNowVisited : freshWitness ∈ visited ++ extraVisited) :
    freshCandidateCount elementDecEq (visited ++ extraVisited) classList + 1 ≤
      freshCandidateCount elementDecEq visited classList :=
  listLengthFilterStrictMono classList
    (fun _element _elementMem extendedFresh =>
      isFreshAgainst_ofNotMem elementDecEq (fun visitedMem =>
        notMem_ofIsFreshAgainst elementDecEq extendedFresh
          (listMemAppendOfLeft extraVisited visitedMem)))
    witnessInClass
    (isFreshAgainst_ofMem elementDecEq witnessNowVisited)
    (isFreshAgainst_ofNotMem elementDecEq witnessNotVisited)

/-- The fresh count never exceeds the enumeration's length. -/
theorem freshCandidateCount_leClassLength {elementType : Type}
    (elementDecEq : DecidableEq elementType)
    (visited classList : List elementType) :
    freshCandidateCount elementDecEq visited classList ≤ classList.length :=
  listLengthFilterLe (isFreshAgainst elementDecEq visited) classList

/-! ## The potential step -/

/-- The one-step potential inequality: frontier growth capped by the successor bound is
paid for by one strictly-newly-visited enumeration entry. -/
theorem saturationPotentialStep {restLength freshLength successorBound
    unvisitedAfter unvisitedBefore : Nat}
    (freshWithinBound : freshLength ≤ successorBound)
    (unvisitedDropped : unvisitedAfter + 1 ≤ unvisitedBefore) :
    (restLength + freshLength) + (successorBound + 1) * unvisitedAfter + 1 ≤
      restLength + (successorBound + 1) * unvisitedBefore := by
  have freshStep : (restLength + freshLength) +
      (successorBound + 1) * unvisitedAfter + 1 ≤
      (restLength + successorBound) + (successorBound + 1) * unvisitedAfter + 1 :=
    Nat.succ_le_succ (Nat.add_le_add_right
      (Nat.add_le_add_left freshWithinBound restLength) _)
  have shuffled : (restLength + successorBound) +
      (successorBound + 1) * unvisitedAfter + 1 =
      restLength + ((successorBound + 1) * unvisitedAfter + (successorBound + 1)) := by
    have core : (restLength + successorBound) +
        (successorBound + 1) * unvisitedAfter =
        restLength + ((successorBound + 1) * unvisitedAfter + successorBound) := by
      rw [Nat.add_assoc]
      exact congrArg (restLength + ·)
        (Nat.add_comm successorBound ((successorBound + 1) * unvisitedAfter))
    exact congrArg (· + 1) core
  have dropStep : restLength + ((successorBound + 1) * unvisitedAfter +
      (successorBound + 1)) ≤
      restLength + (successorBound + 1) * unvisitedBefore :=
    Nat.add_le_add_left (natMulLeftMono (successorBound + 1) unvisitedDropped)
      restLength
  refine Nat.le_trans freshStep ?_
  rw [shuffled]
  exact dropStep

/-! ## The conditional exhaustion theorem -/

/-- ★ **Conditional exhaustion**: given a list containing EVERY trace equivalent to the
seed, fuel at least the potential `frontier.length + (2·|seed| + 1) · unvisited` empties
the frontier.  Each worker step decreases the potential: popping costs one, and a
nonempty fresh batch (at most `2·|seed|` traces, all class members by soundness, all
unvisited by the filter) newly visits at least its head. -/
theorem didExhaustFrontier_ofPotentialBound {signature : ModeSignature}
    (modeDecEq : DecidableEq signature.graph.Mode)
    (modalityDecEq : (sourceMode targetMode : signature.graph.Mode) →
      DecidableEq (signature.graph.Modality sourceMode targetMode))
    (twoCellDecEq : {sourceMode targetMode : signature.graph.Mode} →
      (sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode) →
      DecidableEq (signature.twoCell sourcePath targetPath))
    {overallSource overallTarget : signature.graph.Mode}
    (seedTrace : List (SpineAtom signature overallSource overallTarget))
    (classList : List (List (SpineAtom signature overallSource overallTarget)))
    (classComplete : ∀ member, AtomicTraceEquiv signature seedTrace member →
      member ∈ classList)
    (fuel : Nat) :
    ∀ {frontier visited : List (List (SpineAtom signature overallSource overallTarget))},
      (∀ frontierMember, frontierMember ∈ frontier →
        OneAdjacentSwapChain signature seedTrace frontierMember) →
      frontier.length + (2 * seedTrace.length + 1) *
          freshCandidateCount (spineListDecEq modeDecEq modalityDecEq twoCellDecEq)
            visited classList ≤ fuel →
      didExhaustFrontier modeDecEq modalityDecEq twoCellDecEq fuel frontier visited
        = true := by
  induction fuel with
  | zero =>
      intro frontier visited _frontierReachable potentialBound
      cases frontier with
      | nil => rfl
      | cons nextTrace restFrontier =>
          have frontierLengthZero : (nextTrace :: restFrontier).length ≤ 0 :=
            Nat.le_trans (Nat.le_add_right _ _) potentialBound
          exact absurd frontierLengthZero (Nat.not_succ_le_zero restFrontier.length)
  | succ fuel innerHypothesis =>
      intro frontier visited frontierReachable potentialBound
      cases frontier with
      | nil => rfl
      | cons nextTrace restFrontier =>
          have nextReachable : OneAdjacentSwapChain signature seedTrace nextTrace :=
            frontierReachable nextTrace (List.Mem.head restFrontier)
          have frontierStillReachable : ∀ frontierMember,
              frontierMember ∈ restFrontier ++ freshSwapSuccessors modeDecEq
                modalityDecEq twoCellDecEq visited nextTrace →
              OneAdjacentSwapChain signature seedTrace frontierMember := by
            intro frontierMember frontierMemberMem
            rcases listMemAppendCases _ frontierMemberMem with restMem | freshMem
            · exact frontierReachable frontierMember (List.Mem.tail nextTrace restMem)
            · exact freshSwapSuccessors_areReachable modeDecEq modalityDecEq
                twoCellDecEq nextReachable freshMem
          have reducedBound : restFrontier.length + (2 * seedTrace.length + 1) *
              freshCandidateCount (spineListDecEq modeDecEq modalityDecEq twoCellDecEq)
                visited classList ≤ fuel := by
            have lengthShaped : restFrontier.length + 1 + (2 * seedTrace.length + 1) *
                freshCandidateCount
                  (spineListDecEq modeDecEq modalityDecEq twoCellDecEq)
                  visited classList ≤ fuel + 1 := potentialBound
            rw [Nat.add_right_comm] at lengthShaped
            exact Nat.le_of_succ_le_succ lengthShaped
          have freshLengthBound : (freshSwapSuccessors modeDecEq modalityDecEq
              twoCellDecEq visited nextTrace).length ≤ 2 * seedTrace.length := by
            have filterBound : (freshSwapSuccessors modeDecEq modalityDecEq twoCellDecEq
                visited nextTrace).length ≤
                (swapSuccessors modeDecEq modalityDecEq nextTrace).length :=
              listLengthFilterLe _ (swapSuccessors modeDecEq modalityDecEq nextTrace)
            have successorsBound := swapSuccessors_lengthBound modeDecEq modalityDecEq
              nextTrace
            have lengthsAgree : seedTrace.length = nextTrace.length :=
              nextReachable.toAtomicTraceEquiv.lengthEq
            rw [← lengthsAgree] at successorsBound
            exact Nat.le_trans filterBound successorsBound
          cases freshShape : freshSwapSuccessors modeDecEq modalityDecEq twoCellDecEq
              visited nextTrace with
          | nil =>
              have newBound : (restFrontier ++ freshSwapSuccessors modeDecEq
                  modalityDecEq twoCellDecEq visited nextTrace).length +
                  (2 * seedTrace.length + 1) * freshCandidateCount
                    (spineListDecEq modeDecEq modalityDecEq twoCellDecEq)
                    (visited ++ freshSwapSuccessors modeDecEq modalityDecEq twoCellDecEq
                      visited nextTrace)
                    classList ≤ fuel := by
                rw [freshShape, listLengthAppend]
                exact Nat.le_trans
                  (Nat.add_le_add_left
                    (natMulLeftMono (2 * seedTrace.length + 1)
                      (freshCandidateCount_appendLe
                        (spineListDecEq modeDecEq modalityDecEq twoCellDecEq)
                        visited [] classList))
                    restFrontier.length)
                  reducedBound
              exact (innerHypothesis frontierStillReachable newBound :
                didExhaustFrontier modeDecEq modalityDecEq twoCellDecEq fuel
                  (restFrontier ++ freshSwapSuccessors modeDecEq modalityDecEq
                    twoCellDecEq visited nextTrace)
                  (visited ++ freshSwapSuccessors modeDecEq modalityDecEq twoCellDecEq
                    visited nextTrace) = true)
          | cons freshHead freshRest =>
              have freshHeadMem : freshHead ∈ freshSwapSuccessors modeDecEq
                  modalityDecEq twoCellDecEq visited nextTrace := by
                rw [freshShape]
                exact List.Mem.head freshRest
              obtain ⟨successorMem, predicateFires⟩ := listMemFilterInverted
                (freshHeadMem :
                  freshHead ∈ (swapSuccessors modeDecEq modalityDecEq nextTrace).filter
                    (fun successor =>
                      match listMemDecidable
                          (spineListDecEq modeDecEq modalityDecEq twoCellDecEq)
                          successor visited with
                      | Decidable.isTrue _ => false
                      | Decidable.isFalse _ => true))
              have freshHeadNotVisited : ¬ freshHead ∈ visited := by
                intro visitedMem
                have predicateShaped : (match listMemDecidable
                    (spineListDecEq modeDecEq modalityDecEq twoCellDecEq)
                    freshHead visited with
                  | Decidable.isTrue _ => false
                  | Decidable.isFalse _ => true) = true := predicateFires
                cases decided : listMemDecidable
                    (spineListDecEq modeDecEq modalityDecEq twoCellDecEq)
                    freshHead visited with
                | isTrue _ =>
                    rw [decided] at predicateShaped
                    exact (nomatch predicateShaped)
                | isFalse notMem => exact notMem visitedMem
              have freshHeadInClass : freshHead ∈ classList :=
                classComplete freshHead
                  (freshSwapSuccessors_areReachable modeDecEq modalityDecEq twoCellDecEq
                    nextReachable freshHeadMem).toAtomicTraceEquiv
              have freshHeadNowVisited : freshHead ∈ visited ++ freshSwapSuccessors
                  modeDecEq modalityDecEq twoCellDecEq visited nextTrace :=
                listMemAppendOfRight visited freshHeadMem
              have strictCount : freshCandidateCount
                  (spineListDecEq modeDecEq modalityDecEq twoCellDecEq)
                  (visited ++ freshSwapSuccessors modeDecEq modalityDecEq twoCellDecEq
                    visited nextTrace)
                  classList + 1 ≤
                  freshCandidateCount
                    (spineListDecEq modeDecEq modalityDecEq twoCellDecEq)
                    visited classList :=
                freshCandidateCount_strictDecrease
                  (spineListDecEq modeDecEq modalityDecEq twoCellDecEq)
                  freshHeadInClass freshHeadNotVisited freshHeadNowVisited
              have newBound : (restFrontier ++ freshSwapSuccessors modeDecEq
                  modalityDecEq twoCellDecEq visited nextTrace).length +
                  (2 * seedTrace.length + 1) * freshCandidateCount
                    (spineListDecEq modeDecEq modalityDecEq twoCellDecEq)
                    (visited ++ freshSwapSuccessors modeDecEq modalityDecEq twoCellDecEq
                      visited nextTrace)
                    classList ≤ fuel := by
                rw [listLengthAppend]
                exact Nat.le_of_succ_le
                  (Nat.le_trans
                    (saturationPotentialStep freshLengthBound strictCount)
                    reducedBound)
              exact (innerHypothesis frontierStillReachable newBound :
                didExhaustFrontier modeDecEq modalityDecEq twoCellDecEq fuel
                  (restFrontier ++ freshSwapSuccessors modeDecEq modalityDecEq
                    twoCellDecEq visited nextTrace)
                  (visited ++ freshSwapSuccessors modeDecEq modalityDecEq twoCellDecEq
                    visited nextTrace) = true)

/-! ## The un-gated decider, modulo the class enumeration -/

/-- The computable fuel a complete class enumeration certifies: one pop for the seed plus
`(2·|seed| + 1)` per enumeration entry. -/
def classSaturationFuel {signature : ModeSignature}
    {overallSource overallTarget : signature.graph.Mode}
    (seedTrace : List (SpineAtom signature overallSource overallTarget))
    (classList : List (List (SpineAtom signature overallSource overallTarget))) : Nat :=
  1 + (2 * seedTrace.length + 1) * classList.length

/-- ★ **The fuel gate discharges**: with a complete class enumeration in hand,
`classSaturationFuel` provably exhausts the frontier from the seed. -/
theorem didExhaustFrontier_ofCompleteClassList {signature : ModeSignature}
    (modeDecEq : DecidableEq signature.graph.Mode)
    (modalityDecEq : (sourceMode targetMode : signature.graph.Mode) →
      DecidableEq (signature.graph.Modality sourceMode targetMode))
    (twoCellDecEq : {sourceMode targetMode : signature.graph.Mode} →
      (sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode) →
      DecidableEq (signature.twoCell sourcePath targetPath))
    {overallSource overallTarget : signature.graph.Mode}
    (seedTrace : List (SpineAtom signature overallSource overallTarget))
    (classList : List (List (SpineAtom signature overallSource overallTarget)))
    (classComplete : ∀ member, AtomicTraceEquiv signature seedTrace member →
      member ∈ classList) :
    didExhaustFrontier modeDecEq modalityDecEq twoCellDecEq
      (classSaturationFuel seedTrace classList) [seedTrace] [seedTrace] = true := by
  have seedListReachable : ∀ frontierMember, frontierMember ∈ [seedTrace] →
      OneAdjacentSwapChain signature seedTrace frontierMember := by
    intro frontierMember frontierMemberMem
    rcases listMemConsCases frontierMemberMem with seedEq | impossibleMem
    · rw [seedEq]; exact OneAdjacentSwapChain.refl seedTrace
    · exact (nomatch impossibleMem)
  refine didExhaustFrontier_ofPotentialBound modeDecEq modalityDecEq twoCellDecEq
    seedTrace classList classComplete (classSaturationFuel seedTrace classList)
    seedListReachable ?_
  exact Nat.add_le_add_left
    (natMulLeftMono (2 * seedTrace.length + 1)
      (freshCandidateCount_leClassLength
        (spineListDecEq modeDecEq modalityDecEq twoCellDecEq) [seedTrace] classList))
    1

/-- ★ **The decider, un-gated on fuel**: ANY list containing every trace equivalent to
the seed — no dup-freedom, no exactness required — decides `AtomicTraceEquiv` outright.
The whole remaining FREE-7 gap is constructing that enumeration (the occurrence-tagged
determination rungs). -/
def decideAtomicTraceEquivOfCompleteClassList {signature : ModeSignature}
    (modeDecEq : DecidableEq signature.graph.Mode)
    (modalityDecEq : (sourceMode targetMode : signature.graph.Mode) →
      DecidableEq (signature.graph.Modality sourceMode targetMode))
    (twoCellDecEq : {sourceMode targetMode : signature.graph.Mode} →
      (sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode) →
      DecidableEq (signature.twoCell sourcePath targetPath))
    {overallSource overallTarget : signature.graph.Mode}
    (seedTrace target : List (SpineAtom signature overallSource overallTarget))
    (classList : List (List (SpineAtom signature overallSource overallTarget)))
    (classComplete : ∀ member, AtomicTraceEquiv signature seedTrace member →
      member ∈ classList) :
    Decidable (AtomicTraceEquiv signature seedTrace target) :=
  decideAtomicTraceEquivViaSaturation modeDecEq modalityDecEq twoCellDecEq
    (classSaturationFuel seedTrace classList) seedTrace target
    (didExhaustFrontier_ofCompleteClassList modeDecEq modalityDecEq twoCellDecEq
      seedTrace classList classComplete)

end FX1Poly.Polygraph
