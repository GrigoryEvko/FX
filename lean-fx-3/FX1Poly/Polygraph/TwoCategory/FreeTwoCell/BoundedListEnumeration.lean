import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.ExtractionMembership
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.SwapSuccessorEnumeration

/-! # BoundedListEnumeration — the class-list shape (FREE-7)

The last generic ingredient of the BOUNDED-ATOM-UNIVERSE route: class members are
LISTS over the finite atom universe, and their length is pinned — trace length rides
the class (the already-shipped `FrontExtraction.AtomicTraceEquiv.lengthEq`).  The
candidate class list is therefore "all lists of the seed's length over the universe".

  * `consEachCandidateOnto` / `allListsOfLength` — the type-generic promotion of the
    tag-order enumerator (`TaggedReplay.consEachTagOnto`), repetition allowed;
  * `consEachCandidateOnto_containsCons` — a cons lands in its head's block;
  * ★ `allListsOfLength_containsList` — **completeness**: every list drawing its
    elements from the pool, of exactly the target length, is enumerated.

Raw Lean 4 + Init; per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## The generic bounded-length enumeration -/

/-- Cons each candidate onto each suffix (one length step of the enumeration). -/
def consEachCandidateOnto {candidateType : Type} :
    List candidateType → List (List candidateType) → List (List candidateType)
  | [], _suffixes => []
  | candidate :: remainingCandidates, suffixes =>
      suffixes.map (fun suffix => candidate :: suffix)
        ++ consEachCandidateOnto remainingCandidates suffixes

/-- All lists of exactly the given length over a candidate pool (repetition allowed —
completeness only needs coverage, junk candidates cost nothing). -/
def allListsOfLength {candidateType : Type} :
    Nat → List candidateType → List (List candidateType)
  | 0, _candidates => [[]]
  | lengthBudget + 1, candidates =>
      consEachCandidateOnto candidates (allListsOfLength lengthBudget candidates)

/-- A cons lands in the block of its head candidate. -/
theorem consEachCandidateOnto_containsCons {candidateType : Type}
    {candidate : candidateType} {suffix : List candidateType}
    {candidates : List candidateType} {suffixes : List (List candidateType)}
    (candidateMem : candidate ∈ candidates) (suffixMem : suffix ∈ suffixes) :
    candidate :: suffix ∈ consEachCandidateOnto candidates suffixes := by
  induction candidateMem with
  | head remainingCandidates =>
      exact listMemAppendOfLeft _ (listMemMapOfMem suffixMem)
  | tail headCandidate _candidateMemTail innerHypothesis =>
      exact listMemAppendOfRight _ innerHypothesis

/-- ★ **The bounded-length enumeration is complete**: every list drawing its elements
from the pool, of exactly the target length, is among the enumerated lists. -/
theorem allListsOfLength_containsList {candidateType : Type}
    {candidates : List candidateType} :
    (listedList : List candidateType) →
    (∀ element, element ∈ listedList → element ∈ candidates) →
    (targetLength : Nat) → listedList.length = targetLength →
    listedList ∈ allListsOfLength targetLength candidates
  | [], _isCovered, 0, _lengthEq => List.Mem.head _
  | [], _isCovered, _lengthBudget + 1, impossibleLength => nomatch impossibleLength
  | _headElement :: _restElements, _isCovered, 0, impossibleLength =>
      nomatch impossibleLength
  | headElement :: restElements, isCovered, lengthBudget + 1, lengthEq =>
      consEachCandidateOnto_containsCons
        (isCovered headElement (List.Mem.head restElements))
        (allListsOfLength_containsList restElements
          (fun element elementMem =>
            isCovered element (List.Mem.tail headElement elementMem))
          lengthBudget (Nat.succ.inj lengthEq))

end FX1Poly.Polygraph
