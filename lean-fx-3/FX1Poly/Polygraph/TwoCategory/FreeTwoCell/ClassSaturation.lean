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
    to it (`SwapChain.lean`'s closure identification);
  * `didExhaustFrontier` / `saturateClassWorker_isSwapClosedAtFixpoint` /
    `saturateClass_isComplete` ★ — the completeness half: when the run exhausts its
    frontier (computable check), the visited list is swap-closed — the worklist
    invariant `IsPendingOrExpanded` (every visited trace is still pending or fully
    expanded) is seeded trivially and preserved by each step because a processed
    trace's successors are each already visited or caught by the fresh filter — and
    a swap-closed list containing the seed absorbs every chain, hence the whole
    ~-class.

Together with soundness: gated on `didExhaustFrontier = true`, membership in
`saturateClass` DECIDES `AtomicTraceEquiv` (packaged next brick).  The fuel stays the
honest intermediate until the class-size bound discharges it.

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

/-- Membership in a `filter`, constructed from source membership plus the predicate
firing. -/
theorem listMemFilterOfMem {elementType : Type} {predicate : elementType → Bool}
    {element : elementType} {inputList : List elementType}
    (elementMem : element ∈ inputList) (predicateFires : predicate element = true) :
    element ∈ inputList.filter predicate := by
  induction elementMem with
  | head remaining =>
      show element ∈ (match predicate element with
        | true => element :: remaining.filter predicate
        | false => remaining.filter predicate)
      rw [predicateFires]
      exact List.Mem.head _
  | @tail headElement rest _innerMem innerHypothesis =>
      show element ∈ (match predicate headElement with
        | true => headElement :: rest.filter predicate
        | false => rest.filter predicate)
      cases _predicateRuns : predicate headElement with
      | true => exact List.Mem.tail headElement innerHypothesis
      | false => exact innerHypothesis

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

/-! ## Completeness -/

/-- A trace list closed under single adjacent swaps. -/
abbrev IsSwapClosed {signature : ModeSignature}
    (modeDecEq : DecidableEq signature.graph.Mode)
    (modalityDecEq : (sourceMode targetMode : signature.graph.Mode) →
      DecidableEq (signature.graph.Modality sourceMode targetMode))
    {overallSource overallTarget : signature.graph.Mode}
    (visited : List (List (SpineAtom signature overallSource overallTarget))) : Prop :=
  ∀ trace, trace ∈ visited →
    ∀ successor, successor ∈ swapSuccessors modeDecEq modalityDecEq trace →
      successor ∈ visited

/-- The worklist invariant: every visited trace is still pending on the frontier or
already has all its swap successors visited. -/
abbrev IsPendingOrExpanded {signature : ModeSignature}
    (modeDecEq : DecidableEq signature.graph.Mode)
    (modalityDecEq : (sourceMode targetMode : signature.graph.Mode) →
      DecidableEq (signature.graph.Modality sourceMode targetMode))
    {overallSource overallTarget : signature.graph.Mode}
    (frontier visited : List (List (SpineAtom signature overallSource overallTarget))) :
    Prop :=
  ∀ trace, trace ∈ visited →
    trace ∈ frontier ∨
      ∀ successor, successor ∈ swapSuccessors modeDecEq modalityDecEq trace →
        successor ∈ visited

/-- Every swap successor of a frontier trace is already visited or lands in the fresh
filter — the dichotomy the processing step turns into full expansion. -/
theorem freshSwapSuccessors_coverSuccessors {signature : ModeSignature}
    (modeDecEq : DecidableEq signature.graph.Mode)
    (modalityDecEq : (sourceMode targetMode : signature.graph.Mode) →
      DecidableEq (signature.graph.Modality sourceMode targetMode))
    (twoCellDecEq : {sourceMode targetMode : signature.graph.Mode} →
      (sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode) →
      DecidableEq (signature.twoCell sourcePath targetPath))
    {overallSource overallTarget : signature.graph.Mode}
    {visited : List (List (SpineAtom signature overallSource overallTarget))}
    {nextTrace successor : List (SpineAtom signature overallSource overallTarget)}
    (successorMem : successor ∈ swapSuccessors modeDecEq modalityDecEq nextTrace) :
    successor ∈ visited ∨
      successor ∈ freshSwapSuccessors modeDecEq modalityDecEq twoCellDecEq
        visited nextTrace := by
  cases decided : listMemDecidable
      (spineListDecEq modeDecEq modalityDecEq twoCellDecEq) successor visited with
  | isTrue alreadyVisited => exact Or.inl alreadyVisited
  | isFalse _notVisited =>
      have predicateFires : (fun candidate =>
          match listMemDecidable
              (spineListDecEq modeDecEq modalityDecEq twoCellDecEq)
              candidate visited with
          | Decidable.isTrue _ => false
          | Decidable.isFalse _ => true) successor = true := by
        show (match listMemDecidable
            (spineListDecEq modeDecEq modalityDecEq twoCellDecEq)
            successor visited with
          | Decidable.isTrue _ => false
          | Decidable.isFalse _ => true) = true
        rw [decided]
      exact Or.inr (listMemFilterOfMem successorMem predicateFires)

/-- The worklist invariant survives one processing step: fresh traces are pending,
old pending traces stay pending or were just processed (and the processed head is now
fully expanded by the cover dichotomy), old expanded traces stay expanded. -/
theorem isPendingOrExpanded_stepPreserved {signature : ModeSignature}
    (modeDecEq : DecidableEq signature.graph.Mode)
    (modalityDecEq : (sourceMode targetMode : signature.graph.Mode) →
      DecidableEq (signature.graph.Modality sourceMode targetMode))
    (twoCellDecEq : {sourceMode targetMode : signature.graph.Mode} →
      (sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode) →
      DecidableEq (signature.twoCell sourcePath targetPath))
    {overallSource overallTarget : signature.graph.Mode}
    {nextTrace : List (SpineAtom signature overallSource overallTarget)}
    {restFrontier visited : List (List (SpineAtom signature overallSource overallTarget))}
    (invariantHolds : IsPendingOrExpanded modeDecEq modalityDecEq
      (nextTrace :: restFrontier) visited) :
    IsPendingOrExpanded modeDecEq modalityDecEq
      (restFrontier ++ freshSwapSuccessors modeDecEq modalityDecEq twoCellDecEq
        visited nextTrace)
      (visited ++ freshSwapSuccessors modeDecEq modalityDecEq twoCellDecEq
        visited nextTrace) := by
  intro trace traceMem
  rcases listMemAppendCases _ traceMem with oldMem | freshMem
  · rcases invariantHolds trace oldMem with pendingMem | expanded
    · rcases listMemConsCases pendingMem with headEq | restMem
      · have expandedNow : ∀ successor,
            successor ∈ swapSuccessors modeDecEq modalityDecEq trace →
            successor ∈ visited ++ freshSwapSuccessors modeDecEq modalityDecEq
              twoCellDecEq visited nextTrace := by
          intro successor successorMem
          rw [headEq] at successorMem
          rcases freshSwapSuccessors_coverSuccessors modeDecEq modalityDecEq
              twoCellDecEq successorMem with visitedMem | freshSuccessorMem
          · exact listMemAppendOfLeft _ visitedMem
          · exact listMemAppendOfRight visited freshSuccessorMem
        exact Or.inr expandedNow
      · exact Or.inl (listMemAppendOfLeft _ restMem)
    · have expandedStill : ∀ successor,
          successor ∈ swapSuccessors modeDecEq modalityDecEq trace →
          successor ∈ visited ++ freshSwapSuccessors modeDecEq modalityDecEq
            twoCellDecEq visited nextTrace := by
        intro successor successorMem
        exact listMemAppendOfLeft _ (expanded successor successorMem)
      exact Or.inr expandedStill
  · exact Or.inl (listMemAppendOfRight restFrontier freshMem)

/-- Does the saturation run empty its frontier within the given fuel?  Mirrors
`saturateClassWorker` step for step, so the fixpoint theorem transports along it by
definitional unfolding. -/
def didExhaustFrontier {signature : ModeSignature}
    (modeDecEq : DecidableEq signature.graph.Mode)
    (modalityDecEq : (sourceMode targetMode : signature.graph.Mode) →
      DecidableEq (signature.graph.Modality sourceMode targetMode))
    (twoCellDecEq : {sourceMode targetMode : signature.graph.Mode} →
      (sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode) →
      DecidableEq (signature.twoCell sourcePath targetPath))
    {overallSource overallTarget : signature.graph.Mode} :
    Nat →
    List (List (SpineAtom signature overallSource overallTarget)) →
    List (List (SpineAtom signature overallSource overallTarget)) → Bool
  | 0, [], _visited => true
  | 0, _nextTrace :: _restFrontier, _visited => false
  | _fuel + 1, [], _visited => true
  | fuel + 1, nextTrace :: restFrontier, visited =>
      let freshSuccessors :=
        freshSwapSuccessors modeDecEq modalityDecEq twoCellDecEq visited nextTrace
      didExhaustFrontier modeDecEq modalityDecEq twoCellDecEq fuel
        (restFrontier ++ freshSuccessors) (visited ++ freshSuccessors)

/-- ★ **Fixpoint closedness**: a run that empties its frontier returns a swap-closed
visited list — the worklist invariant degenerates to full expansion once nothing is
pending. -/
theorem saturateClassWorker_isSwapClosedAtFixpoint {signature : ModeSignature}
    (modeDecEq : DecidableEq signature.graph.Mode)
    (modalityDecEq : (sourceMode targetMode : signature.graph.Mode) →
      DecidableEq (signature.graph.Modality sourceMode targetMode))
    (twoCellDecEq : {sourceMode targetMode : signature.graph.Mode} →
      (sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode) →
      DecidableEq (signature.twoCell sourcePath targetPath))
    {overallSource overallTarget : signature.graph.Mode} (fuel : Nat) :
    ∀ {frontier visited : List (List (SpineAtom signature overallSource overallTarget))},
      didExhaustFrontier modeDecEq modalityDecEq twoCellDecEq fuel frontier visited
        = true →
      IsPendingOrExpanded modeDecEq modalityDecEq frontier visited →
      IsSwapClosed modeDecEq modalityDecEq
        (saturateClassWorker modeDecEq modalityDecEq twoCellDecEq fuel frontier
          visited) := by
  induction fuel with
  | zero =>
      intro frontier visited didExhaust invariantHolds
      cases frontier with
      | nil =>
          intro trace traceMem successor successorMem
          have traceMemVisited : trace ∈ visited := traceMem
          rcases invariantHolds trace traceMemVisited with pendingMem | expanded
          · exact (nomatch pendingMem)
          · exact expanded successor successorMem
      | cons nextTrace restFrontier =>
          have falseIsTrue : false = true := didExhaust
          exact (nomatch falseIsTrue)
  | succ fuel innerHypothesis =>
      intro frontier visited didExhaust invariantHolds
      cases frontier with
      | nil =>
          intro trace traceMem successor successorMem
          have traceMemVisited : trace ∈ visited := traceMem
          rcases invariantHolds trace traceMemVisited with pendingMem | expanded
          · exact (nomatch pendingMem)
          · exact expanded successor successorMem
      | cons nextTrace restFrontier =>
          have didExhaustNext : didExhaustFrontier modeDecEq modalityDecEq twoCellDecEq
              fuel
              (restFrontier ++ freshSwapSuccessors modeDecEq modalityDecEq twoCellDecEq
                visited nextTrace)
              (visited ++ freshSwapSuccessors modeDecEq modalityDecEq twoCellDecEq
                visited nextTrace) = true := didExhaust
          have invariantNext := isPendingOrExpanded_stepPreserved modeDecEq
            modalityDecEq twoCellDecEq invariantHolds
          exact (innerHypothesis didExhaustNext invariantNext :
            IsSwapClosed modeDecEq modalityDecEq
              (saturateClassWorker modeDecEq modalityDecEq twoCellDecEq fuel
                (restFrontier ++ freshSwapSuccessors modeDecEq modalityDecEq
                  twoCellDecEq visited nextTrace)
                (visited ++ freshSwapSuccessors modeDecEq modalityDecEq twoCellDecEq
                  visited nextTrace)))

/-- The saturated class is swap-closed whenever the run exhausts its frontier: the
singleton seed trivially satisfies the worklist invariant (it is pending). -/
theorem saturateClass_isSwapClosed {signature : ModeSignature}
    (modeDecEq : DecidableEq signature.graph.Mode)
    (modalityDecEq : (sourceMode targetMode : signature.graph.Mode) →
      DecidableEq (signature.graph.Modality sourceMode targetMode))
    (twoCellDecEq : {sourceMode targetMode : signature.graph.Mode} →
      (sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode) →
      DecidableEq (signature.twoCell sourcePath targetPath))
    {overallSource overallTarget : signature.graph.Mode} (fuel : Nat)
    (seedTrace : List (SpineAtom signature overallSource overallTarget))
    (didExhaust : didExhaustFrontier modeDecEq modalityDecEq twoCellDecEq fuel
      [seedTrace] [seedTrace] = true) :
    IsSwapClosed modeDecEq modalityDecEq
      (saturateClass modeDecEq modalityDecEq twoCellDecEq fuel seedTrace) := by
  have seedInvariant : IsPendingOrExpanded modeDecEq modalityDecEq
      [seedTrace] [seedTrace] := by
    intro trace traceMem
    exact Or.inl traceMem
  exact saturateClassWorker_isSwapClosedAtFixpoint modeDecEq modalityDecEq twoCellDecEq
    fuel didExhaust seedInvariant

/-- A swap-closed trace list absorbs chains: walk the chain, each hop stays inside by
closedness (move completeness feeds the enumeration membership). -/
theorem isSwapClosed_containsChainTargets {signature : ModeSignature}
    (modeDecEq : DecidableEq signature.graph.Mode)
    (modalityDecEq : (sourceMode targetMode : signature.graph.Mode) →
      DecidableEq (signature.graph.Modality sourceMode targetMode))
    {overallSource overallTarget : signature.graph.Mode}
    {visited : List (List (SpineAtom signature overallSource overallTarget))}
    (visitedClosed : IsSwapClosed modeDecEq modalityDecEq visited)
    {startTrace target : List (SpineAtom signature overallSource overallTarget)}
    (chain : OneAdjacentSwapChain signature startTrace target) :
    startTrace ∈ visited → target ∈ visited := by
  induction chain with
  | refl _ => exact fun startMem => startMem
  | advance headSwap _restChain innerHypothesis =>
      exact fun startMem =>
        innerHypothesis (visitedClosed _ startMem _
          (swapSuccessors_isComplete modeDecEq modalityDecEq headSwap))

/-- ★ **Saturation completeness**: gated on the frontier exhausting, the saturated
class contains EVERY trace equivalent to the seed — the closure identification turns
the equivalence into a chain, and the swap-closed visited list absorbs it from the
seed. -/
theorem saturateClass_isComplete {signature : ModeSignature}
    (modeDecEq : DecidableEq signature.graph.Mode)
    (modalityDecEq : (sourceMode targetMode : signature.graph.Mode) →
      DecidableEq (signature.graph.Modality sourceMode targetMode))
    (twoCellDecEq : {sourceMode targetMode : signature.graph.Mode} →
      (sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode) →
      DecidableEq (signature.twoCell sourcePath targetPath))
    {overallSource overallTarget : signature.graph.Mode} {fuel : Nat}
    {seedTrace target : List (SpineAtom signature overallSource overallTarget)}
    (didExhaust : didExhaustFrontier modeDecEq modalityDecEq twoCellDecEq fuel
      [seedTrace] [seedTrace] = true)
    (traceEquiv : AtomicTraceEquiv signature seedTrace target) :
    target ∈ saturateClass modeDecEq modalityDecEq twoCellDecEq fuel seedTrace :=
  isSwapClosed_containsChainTargets modeDecEq modalityDecEq
    (saturateClass_isSwapClosed modeDecEq modalityDecEq twoCellDecEq fuel seedTrace
      didExhaust)
    traceEquiv.toOneAdjacentSwapChain
    (saturateClass_containsSeed modeDecEq modalityDecEq twoCellDecEq fuel seedTrace)

end FX1Poly.Polygraph
