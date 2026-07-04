import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.SwapSuccessorEnumeration
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.SpineListDecEq

/-! # ClassSaturation — the BFS saturation worker (FREE-6c brick 2)

The class-saturation route decides `AtomicTraceEquiv` by saturating the seed's ~-class
under the one-swap move layer (`swapSuccessors`, brick 1).  This file ships the search
itself with its safety half:

  * `listMemDecidable` / `listMemFilterInverted` — hand-rolled decidable list
    membership and `filter` inversion (continuing the `ExtractionMembership` kit);
  * `freshSwapSuccessors` — the successors of a frontier trace not already visited;
  * `saturateClassWorker` — fuel-indexed breadth-first closure: pop a frontier trace,
    push its genuinely new successors onto BOTH the frontier and the visited list;
  * `saturateClassWorker_keepsVisited` / `saturateClass_containsSeed` — the visited
    list only grows, so the seed stays in its own saturation;
  * `saturateClassWorker_isSound` / `saturateClass_isSound` ★ — every trace the search
    visits is `OneAdjacentSwapChain`-reachable from the seed, hence `AtomicTraceEquiv`
    to it (`SwapChain.lean`'s closure identification).

The completeness half (at a fixpoint the visited list is swap-closed, hence contains
the whole ~-class) is the next brick; the fuel is the honest intermediate until the
class-size bound discharges it.

Raw Lean 4 + Init; per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## List membership as choice data -/

/-- Decidable list membership from decidable equality (hand-rolled so the audit sees
only structural recursion and the `ExtractionMembership` destructor). -/
def listMemDecidable {elementType : Type} (elementDecEq : DecidableEq elementType)
    (candidate : elementType) :
    (inputList : List elementType) → Decidable (candidate ∈ inputList)
  | [] => Decidable.isFalse (fun absurdMem => nomatch absurdMem)
  | headElement :: remaining =>
      match elementDecEq candidate headElement with
      | Decidable.isTrue headEq =>
          Decidable.isTrue (by rw [headEq]; exact List.Mem.head remaining)
      | Decidable.isFalse headNe =>
          match listMemDecidable elementDecEq candidate remaining with
          | Decidable.isTrue restMem =>
              Decidable.isTrue (List.Mem.tail headElement restMem)
          | Decidable.isFalse restNotMem =>
              Decidable.isFalse (fun consMem =>
                match listMemConsCases consMem with
                | Or.inl headEq => headNe headEq
                | Or.inr restMemProof => restNotMem restMemProof)

/-- Membership in a `filter` inverts to source membership plus the predicate firing. -/
theorem listMemFilterInverted {elementType : Type} {predicate : elementType → Bool}
    {element : elementType} :
    {inputList : List elementType} → element ∈ inputList.filter predicate →
    element ∈ inputList ∧ predicate element = true
  | [], filteredMem => nomatch filteredMem
  | headElement :: remaining, filteredMem => by
      have filteredMemShaped : element ∈ (match predicate headElement with
          | true => headElement :: remaining.filter predicate
          | false => remaining.filter predicate) := filteredMem
      cases predicateRuns : predicate headElement with
      | true =>
          rw [predicateRuns] at filteredMemShaped
          rcases listMemConsCases filteredMemShaped with headEq | tailMem
          · constructor
            · rw [headEq]; exact List.Mem.head remaining
            · rw [headEq]; exact predicateRuns
          · obtain ⟨sourceMem, predicateHolds⟩ := listMemFilterInverted tailMem
            exact ⟨List.Mem.tail headElement sourceMem, predicateHolds⟩
      | false =>
          rw [predicateRuns] at filteredMemShaped
          obtain ⟨sourceMem, predicateHolds⟩ := listMemFilterInverted filteredMemShaped
          exact ⟨List.Mem.tail headElement sourceMem, predicateHolds⟩

/-! ## The saturation worker -/

/-- The one-swap successors of a frontier trace that are NOT already visited — the
worker's per-step frontier growth. -/
def freshSwapSuccessors {signature : ModeSignature}
    (modeDecEq : DecidableEq signature.graph.Mode)
    (modalityDecEq : (sourceMode targetMode : signature.graph.Mode) →
      DecidableEq (signature.graph.Modality sourceMode targetMode))
    (twoCellDecEq : {sourceMode targetMode : signature.graph.Mode} →
      (sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode) →
      DecidableEq (signature.twoCell sourcePath targetPath))
    {overallSource overallTarget : signature.graph.Mode}
    (visited : List (List (SpineAtom signature overallSource overallTarget)))
    (nextTrace : List (SpineAtom signature overallSource overallTarget)) :
    List (List (SpineAtom signature overallSource overallTarget)) :=
  (swapSuccessors modeDecEq modalityDecEq nextTrace).filter
    (fun successor =>
      match listMemDecidable
          (spineListDecEq modeDecEq modalityDecEq twoCellDecEq) successor visited with
      | Decidable.isTrue _ => false
      | Decidable.isFalse _ => true)

/-- ★ **Fuel-indexed breadth-first saturation**: pop a frontier trace, keep only its
swap successors not already visited, push them onto both the frontier and the visited
list.  Fuel-structural — the honest intermediate until the class-size bound lands. -/
def saturateClassWorker {signature : ModeSignature}
    (modeDecEq : DecidableEq signature.graph.Mode)
    (modalityDecEq : (sourceMode targetMode : signature.graph.Mode) →
      DecidableEq (signature.graph.Modality sourceMode targetMode))
    (twoCellDecEq : {sourceMode targetMode : signature.graph.Mode} →
      (sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode) →
      DecidableEq (signature.twoCell sourcePath targetPath))
    {overallSource overallTarget : signature.graph.Mode} :
    Nat →
    List (List (SpineAtom signature overallSource overallTarget)) →
    List (List (SpineAtom signature overallSource overallTarget)) →
    List (List (SpineAtom signature overallSource overallTarget))
  | 0, _frontier, visited => visited
  | _fuel + 1, [], visited => visited
  | fuel + 1, nextTrace :: restFrontier, visited =>
      let freshSuccessors :=
        freshSwapSuccessors modeDecEq modalityDecEq twoCellDecEq visited nextTrace
      saturateClassWorker modeDecEq modalityDecEq twoCellDecEq fuel
        (restFrontier ++ freshSuccessors) (visited ++ freshSuccessors)

/-- Saturate the seed's ~-class: both lists start at the singleton seed. -/
def saturateClass {signature : ModeSignature}
    (modeDecEq : DecidableEq signature.graph.Mode)
    (modalityDecEq : (sourceMode targetMode : signature.graph.Mode) →
      DecidableEq (signature.graph.Modality sourceMode targetMode))
    (twoCellDecEq : {sourceMode targetMode : signature.graph.Mode} →
      (sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode) →
      DecidableEq (signature.twoCell sourcePath targetPath))
    {overallSource overallTarget : signature.graph.Mode} (fuel : Nat)
    (seedTrace : List (SpineAtom signature overallSource overallTarget)) :
    List (List (SpineAtom signature overallSource overallTarget)) :=
  saturateClassWorker modeDecEq modalityDecEq twoCellDecEq fuel [seedTrace] [seedTrace]

/-! ## Growth -/

/-- The visited list only grows: anything visited stays in the worker's output. -/
theorem saturateClassWorker_keepsVisited {signature : ModeSignature}
    (modeDecEq : DecidableEq signature.graph.Mode)
    (modalityDecEq : (sourceMode targetMode : signature.graph.Mode) →
      DecidableEq (signature.graph.Modality sourceMode targetMode))
    (twoCellDecEq : {sourceMode targetMode : signature.graph.Mode} →
      (sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode) →
      DecidableEq (signature.twoCell sourcePath targetPath))
    {overallSource overallTarget : signature.graph.Mode} (fuel : Nat) :
    ∀ {frontier visited : List (List (SpineAtom signature overallSource overallTarget))}
      {member : List (SpineAtom signature overallSource overallTarget)},
      member ∈ visited →
      member ∈ saturateClassWorker modeDecEq modalityDecEq twoCellDecEq fuel
        frontier visited := by
  induction fuel with
  | zero =>
      intro frontier visited member memberMem
      cases frontier with
      | nil => exact memberMem
      | cons nextTrace restFrontier => exact memberMem
  | succ fuel innerHypothesis =>
      intro frontier visited member memberMem
      cases frontier with
      | nil => exact memberMem
      | cons nextTrace restFrontier =>
          exact (innerHypothesis (listMemAppendOfLeft _ memberMem) :
            member ∈ saturateClassWorker modeDecEq modalityDecEq twoCellDecEq fuel
              (restFrontier ++ freshSwapSuccessors modeDecEq modalityDecEq twoCellDecEq
                visited nextTrace)
              (visited ++ freshSwapSuccessors modeDecEq modalityDecEq twoCellDecEq
                visited nextTrace))

/-- The seed belongs to its own saturated class. -/
theorem saturateClass_containsSeed {signature : ModeSignature}
    (modeDecEq : DecidableEq signature.graph.Mode)
    (modalityDecEq : (sourceMode targetMode : signature.graph.Mode) →
      DecidableEq (signature.graph.Modality sourceMode targetMode))
    (twoCellDecEq : {sourceMode targetMode : signature.graph.Mode} →
      (sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode) →
      DecidableEq (signature.twoCell sourcePath targetPath))
    {overallSource overallTarget : signature.graph.Mode} (fuel : Nat)
    (seedTrace : List (SpineAtom signature overallSource overallTarget)) :
    seedTrace ∈ saturateClass modeDecEq modalityDecEq twoCellDecEq fuel seedTrace :=
  saturateClassWorker_keepsVisited modeDecEq modalityDecEq twoCellDecEq fuel
    (List.Mem.head [])

/-! ## Soundness -/

/-- Every genuinely-new successor of a reachable frontier trace is reachable: filter
inversion recovers the enumeration membership, move soundness gives the single swap,
and the chain extends through the frontier trace. -/
theorem freshSwapSuccessors_areReachable {signature : ModeSignature}
    (modeDecEq : DecidableEq signature.graph.Mode)
    (modalityDecEq : (sourceMode targetMode : signature.graph.Mode) →
      DecidableEq (signature.graph.Modality sourceMode targetMode))
    (twoCellDecEq : {sourceMode targetMode : signature.graph.Mode} →
      (sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode) →
      DecidableEq (signature.twoCell sourcePath targetPath))
    {overallSource overallTarget : signature.graph.Mode}
    {seedTrace nextTrace : List (SpineAtom signature overallSource overallTarget)}
    {visited : List (List (SpineAtom signature overallSource overallTarget))}
    (nextReachable : OneAdjacentSwapChain signature seedTrace nextTrace)
    {freshMember : List (SpineAtom signature overallSource overallTarget)}
    (freshMem : freshMember ∈ freshSwapSuccessors modeDecEq modalityDecEq twoCellDecEq
      visited nextTrace) :
    OneAdjacentSwapChain signature seedTrace freshMember := by
  obtain ⟨successorMem, _predicateFires⟩ := listMemFilterInverted freshMem
  exact OneAdjacentSwapChain.trans nextReachable
    (OneAdjacentSwapChain.single
      (swapSuccessors_isSound modeDecEq modalityDecEq nextTrace successorMem))

/-- The worker preserves reachability: when every frontier and visited trace is
chain-reachable from the seed, so is everything the worker returns. -/
theorem saturateClassWorker_isSound {signature : ModeSignature}
    (modeDecEq : DecidableEq signature.graph.Mode)
    (modalityDecEq : (sourceMode targetMode : signature.graph.Mode) →
      DecidableEq (signature.graph.Modality sourceMode targetMode))
    (twoCellDecEq : {sourceMode targetMode : signature.graph.Mode} →
      (sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode) →
      DecidableEq (signature.twoCell sourcePath targetPath))
    {overallSource overallTarget : signature.graph.Mode}
    (seedTrace : List (SpineAtom signature overallSource overallTarget)) (fuel : Nat) :
    ∀ {frontier visited : List (List (SpineAtom signature overallSource overallTarget))}
      {member : List (SpineAtom signature overallSource overallTarget)},
      (∀ frontierMember, frontierMember ∈ frontier →
        OneAdjacentSwapChain signature seedTrace frontierMember) →
      (∀ visitedMember, visitedMember ∈ visited →
        OneAdjacentSwapChain signature seedTrace visitedMember) →
      member ∈ saturateClassWorker modeDecEq modalityDecEq twoCellDecEq fuel
        frontier visited →
      OneAdjacentSwapChain signature seedTrace member := by
  induction fuel with
  | zero =>
      intro frontier visited member _frontierReachable visitedReachable memberMem
      cases frontier with
      | nil => exact visitedReachable member memberMem
      | cons nextTrace restFrontier => exact visitedReachable member memberMem
  | succ fuel innerHypothesis =>
      intro frontier visited member frontierReachable visitedReachable memberMem
      cases frontier with
      | nil => exact visitedReachable member memberMem
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
            · exact freshSwapSuccessors_areReachable modeDecEq modalityDecEq twoCellDecEq
                nextReachable freshMem
          have visitedStillReachable : ∀ visitedMember,
              visitedMember ∈ visited ++ freshSwapSuccessors modeDecEq modalityDecEq
                twoCellDecEq visited nextTrace →
              OneAdjacentSwapChain signature seedTrace visitedMember := by
            intro visitedMember visitedMemberMem
            rcases listMemAppendCases _ visitedMemberMem with oldMem | freshMem
            · exact visitedReachable visitedMember oldMem
            · exact freshSwapSuccessors_areReachable modeDecEq modalityDecEq twoCellDecEq
                nextReachable freshMem
          exact innerHypothesis frontierStillReachable visitedStillReachable memberMem

/-- ★ **Saturation soundness**: everything the saturation search visits is
trace-equivalent to the seed. -/
theorem saturateClass_isSound {signature : ModeSignature}
    (modeDecEq : DecidableEq signature.graph.Mode)
    (modalityDecEq : (sourceMode targetMode : signature.graph.Mode) →
      DecidableEq (signature.graph.Modality sourceMode targetMode))
    (twoCellDecEq : {sourceMode targetMode : signature.graph.Mode} →
      (sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode) →
      DecidableEq (signature.twoCell sourcePath targetPath))
    {overallSource overallTarget : signature.graph.Mode} {fuel : Nat}
    {seedTrace member : List (SpineAtom signature overallSource overallTarget)}
    (memberMem : member ∈ saturateClass modeDecEq modalityDecEq twoCellDecEq
      fuel seedTrace) :
    AtomicTraceEquiv signature seedTrace member := by
  have seedListReachable : ∀ listMember,
      listMember ∈ [seedTrace] → OneAdjacentSwapChain signature seedTrace listMember := by
    intro listMember listMemberMem
    rcases listMemConsCases listMemberMem with seedEq | impossibleMem
    · rw [seedEq]; exact OneAdjacentSwapChain.refl seedTrace
    · exact (nomatch impossibleMem)
  exact (saturateClassWorker_isSound modeDecEq modalityDecEq twoCellDecEq seedTrace fuel
    seedListReachable seedListReachable memberMem).toAtomicTraceEquiv

end FX1Poly.Polygraph
