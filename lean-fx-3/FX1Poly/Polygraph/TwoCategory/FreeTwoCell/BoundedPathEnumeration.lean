import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.LetterInventory
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.ExtractionMembership
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.SwapSuccessorEnumeration

/-! # BoundedPathEnumeration — every disciplined bounded path is enumerated (FREE-7)

Enumeration leg of the BOUNDED-ATOM-UNIVERSE route: the invariance legs pin every
whisker context of every class member to letters from a finite inventory and length
below a budget, so the contexts live in the FINITE set of inventory-lettered paths of
bounded length.  This brick makes that set a computable list and proves it complete —
the last dependent-typed obstacle before the universe product.

  * `nilPathCandidates` — the (at most one) empty path between two modes, produced by
    deciding mode equality and transporting `nil` along the proof;
  * `consEdgeCandidates` — for each inventory letter leaving `sourceMode`, cons its
    (transported) modality onto every continuation from its target;
  * `enumeratePathsUpTo` — fuel recursion on the length bound: the empty candidate
    plus one letter followed by a shorter enumeration;
  * `nilPath_mem_nilPathCandidates` — the empty path is always found (the transported
    representative is definitionally `nil` by proof irrelevance);
  * `consEdgeCandidates_containsCons` — induction on the letter's inventory
    membership; at the head the decision procedure must answer `isTrue`, and the
    transported letter is definitionally the original;
  * ★ `enumeratePathsUpTo_containsPath` — **completeness**: every path drawing its
    letters from the inventory with length within the bound is in the enumeration.

Soundness (enumerated paths are disciplined and short) is deliberately not stated:
the universe only needs a complete superset — junk candidates cost nothing.

Raw Lean 4 + Init; per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## The enumerator -/

/-- The empty-path candidates between two modes: exactly one when the modes agree
(transport `nil` along the decided equality), none otherwise. -/
def nilPathCandidates {graph : ModeGraph} (modeDecEq : DecidableEq graph.Mode)
    (sourceMode targetMode : graph.Mode) :
    List (ModalityPath graph sourceMode targetMode) :=
  match modeDecEq sourceMode targetMode with
  | Decidable.isTrue endpointsEqual =>
      [Eq.rec (motive := fun endMode _ => ModalityPath graph sourceMode endMode)
        (ModalityPath.nil sourceMode) endpointsEqual]
  | Decidable.isFalse _ => []

/-- For each inventory letter leaving `sourceMode`, cons its transported modality onto
every continuation path from the letter's target mode. -/
def consEdgeCandidates {graph : ModeGraph} (modeDecEq : DecidableEq graph.Mode)
    {targetMode : graph.Mode}
    (continuationsFrom :
      (middleMode : graph.Mode) → List (ModalityPath graph middleMode targetMode))
    (sourceMode : graph.Mode) :
    List (PackedModality graph) → List (ModalityPath graph sourceMode targetMode)
  | [] => []
  | entry :: remainingEntries =>
      (match modeDecEq entry.edgeSourceMode sourceMode with
        | Decidable.isTrue sourceEqual =>
            (continuationsFrom entry.edgeTargetMode).map
              (fun continuation =>
                ModalityPath.cons
                  (Eq.rec (motive := fun fromMode _ =>
                      graph.Modality fromMode entry.edgeTargetMode)
                    entry.edgeModality sourceEqual)
                  continuation)
        | Decidable.isFalse _ => [])
        ++ consEdgeCandidates modeDecEq continuationsFrom sourceMode remainingEntries

/-- All paths of length at most `lengthBound` drawing their letters from `edgeList`
(fuel recursion on the bound; a complete superset, junk candidates allowed). -/
def enumeratePathsUpTo {graph : ModeGraph} (modeDecEq : DecidableEq graph.Mode)
    (edgeList : List (PackedModality graph)) :
    Nat → (sourceMode targetMode : graph.Mode) →
    List (ModalityPath graph sourceMode targetMode)
  | 0 => fun sourceMode targetMode =>
      nilPathCandidates modeDecEq sourceMode targetMode
  | lengthBudget + 1 => fun sourceMode targetMode =>
      nilPathCandidates modeDecEq sourceMode targetMode
        ++ consEdgeCandidates modeDecEq
          (fun middleMode =>
            enumeratePathsUpTo modeDecEq edgeList lengthBudget middleMode targetMode)
          sourceMode edgeList

/-! ## Completeness -/

/-- The empty path is among its own candidates: the decision procedure answers
`isTrue`, and the transported representative is definitionally `nil` because the
self-equality proof is definitionally `rfl`. -/
theorem nilPath_mem_nilPathCandidates {graph : ModeGraph}
    (modeDecEq : DecidableEq graph.Mode) (pathMode : graph.Mode) :
    ModalityPath.nil pathMode ∈ nilPathCandidates modeDecEq pathMode pathMode := by
  dsimp only [nilPathCandidates]
  cases decision : modeDecEq pathMode pathMode with
  | isTrue _endpointsEqual => exact List.Mem.head _
  | isFalse notEqual => exact absurd rfl notEqual

/-- A cons whose letter is in the inventory and whose continuation is enumerated is
among the cons candidates: induction on the inventory membership; at the head the
decision procedure must answer `isTrue`, and the transported letter is definitionally
the original. -/
theorem consEdgeCandidates_containsCons {graph : ModeGraph}
    (modeDecEq : DecidableEq graph.Mode) {targetMode : graph.Mode}
    {continuationsFrom :
      (middleMode : graph.Mode) → List (ModalityPath graph middleMode targetMode)}
    {sourceMode middleMode : graph.Mode}
    {edgeModality : graph.Modality sourceMode middleMode}
    {continuation : ModalityPath graph middleMode targetMode}
    {entries : List (PackedModality graph)}
    (entryMem :
      (⟨sourceMode, middleMode, edgeModality⟩ : PackedModality graph) ∈ entries)
    (continuationMem : continuation ∈ continuationsFrom middleMode) :
    ModalityPath.cons edgeModality continuation
      ∈ consEdgeCandidates modeDecEq continuationsFrom sourceMode entries := by
  induction entryMem with
  | head remainingEntries =>
      dsimp only [consEdgeCandidates]
      cases decision : modeDecEq sourceMode sourceMode with
      | isTrue _sourceEqual =>
          exact listMemAppendOfLeft _ (listMemMapOfMem continuationMem)
      | isFalse notEqual => exact absurd rfl notEqual
  | tail headEntry _entryMemTail innerHypothesis =>
      exact listMemAppendOfRight _ innerHypothesis

/-- ★ **The bounded enumeration is complete**: every path drawing its letters from the
inventory, with length within the bound, is among the enumerated candidates. -/
theorem enumeratePathsUpTo_containsPath {graph : ModeGraph}
    (modeDecEq : DecidableEq graph.Mode)
    {edgeList : List (PackedModality graph)} :
    {sourceMode targetMode : graph.Mode} →
    (path : ModalityPath graph sourceMode targetMode) →
    pathUsesOnly edgeList path →
    (lengthBound : Nat) → path.length ≤ lengthBound →
    path ∈ enumeratePathsUpTo modeDecEq edgeList lengthBound sourceMode targetMode
  | _, _, ModalityPath.nil pathMode, _pathUses, 0, _lengthLe =>
      nilPath_mem_nilPathCandidates modeDecEq pathMode
  | _, _, ModalityPath.nil pathMode, _pathUses, _lengthBudget + 1, _lengthLe =>
      listMemAppendOfLeft _ (nilPath_mem_nilPathCandidates modeDecEq pathMode)
  | _, _, ModalityPath.cons _edgeModality _rest, _pathUses, 0, lengthLe =>
      nomatch lengthLe
  | _, _, ModalityPath.cons _edgeModality rest, pathUses, lengthBudget + 1, lengthLe =>
      listMemAppendOfRight _
        (consEdgeCandidates_containsCons modeDecEq pathUses.1
          (enumeratePathsUpTo_containsPath modeDecEq rest pathUses.2 lengthBudget
            (Nat.le_of_succ_le_succ lengthLe)))

end FX1Poly.Polygraph
