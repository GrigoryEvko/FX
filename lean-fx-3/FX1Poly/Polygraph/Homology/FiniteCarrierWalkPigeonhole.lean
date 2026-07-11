import FX1Poly.Polygraph.Homology.AcyclicTruncationClosedFormAndDisjointUnionAdditivity

/-! # FX1Poly/Polygraph/Homology/FiniteCarrierWalkPigeonhole — the classical finite-carrier walk
    pigeonhole `listOverCarrierRepeats` (ingredient (i) of the general-graph acyclicity-soundness node),
    zero-axiom, alphabet-agnostic (TOWER-ANICK r11, #2144)

The r10 file `AcyclicTruncationClosedFormAndDisjointUnionAdditivity` NAMED the general-graph
`acyclic ==> census 0` soundness (`generalGraphLongestPathBoundIsNamedNode`), reducing it to three
separately-hard zero-axiom ingredients recorded in its docstring:

  (i)   the classical pigeonhole `listOverCarrierRepeats` — a walk over a finite vertex carrier longer
        than the carrier repeats a vertex ("a genuinely substantial proof — its own round");
  (ii)  checker saturation — that `obstructionReachableWithin edges vertexCount` captures ALL reachable
        vertices;
  (iii) the topological-sort longest-path bound — an acyclic graph's longest walk is `≤ vertexCount`.

This module SHIPS ingredient (i): `listOverCarrierRepeats`, the pigeonhole, standalone and reusable over
ANY natural-number alphabet.  The r10 `{xy}` closed form (`linearCensusZeroAboveDegreeOne`) still stands
in the bespoke `noLinearChainOfLengthThreeOrMore` for the length-1-carrier case; the pigeonhole is the
alphabet-agnostic replacement the general node requires.

## Truth-probes FIRST (the three hostile graphs, machine-checked by `rfl` on the computed oracle)

Before proving anything, the recon ran the census / acyclicity oracle on three hostile graphs; the
verdicts are pinned here as permanent `rfl` smokes:

  * `threeCycleIsNonAcyclicAtSaturatingFuel` — the directed 3-cycle `[(0,1),(1,2),(2,0)]` is correctly
    reported NON-acyclic at fuel `2` and `4` (the soundness theorem is inapplicable, as it should be).
  * `dagChainIsAcyclicWithVanishingBinaryCensus` — the DAG chain `[(0,1),(1,2),(2,3)]` is acyclic and its
    census already vanishes at degree `2`.
  * `diamondIsAcyclicWithVanishingBinaryCensus` — the diamond `[(0,1),(0,2),(1,3),(2,3)]` likewise.

Two structural findings surfaced (recorded in `generalGraphSoundnessResidualsAfterPigeonhole` below):

  * **FINDING A — the alphabet wall.**  `allWordsOfLength` enumerates only BINARY words (`0 :: _` /
    `1 :: _`), so `multiObstructionChainRankOracle` is BLIND to any letter `≥ 2`.  Both the DAG chain and
    the diamond, though they live on `≥ 3` letters, produce the SAME census as `{xy}`.  A genuine n-ary
    application of the pigeonhole therefore needs a NEW prerequisite absent from r10's three-ingredient
    list: (0) an n-ary alphabet enumerator + a re-based census oracle.  The general node has FOUR
    ingredients, not three.
  * **FINDING B — fuel starvation.**  `isAcyclicUfnarovskiGraph edges fuel` returns `true` (acyclic)
    UNDER-fuelled — a cycle of length `L` is detected only at `fuel ≥ L - 1`.  Soundness of the checker's
    verdict is therefore load-bearing on ingredient (ii) and orthogonal to the pigeonhole.

## The pigeonhole, zero-axiom (the design)

`listOverCarrierRepeats` is STRUCTURAL on the CARRIER (not the walk): the carrier sheds its front vertex
per step, and the walk sheds ALL copies of that vertex (`removeAllVertexOccurrences`, not a `removeFirst`
— carrier-induction needs every copy gone so the pruned walk lives over the smaller carrier).  The step
dichotomises on `countVertexOccurrences frontVertex walk`: `2 ≤ count` exhibits the repeat directly
(`countGeTwoImpliesRepeat`); `count ≤ 1` recurses on the pruned walk (`removeAllVertexOccurrences`) whose
length still exceeds the smaller carrier's (`removeAllLengthPlusCount`, the ADDITIVE identity that
sidesteps `Nat.sub`), then lifts the pruned repeat back (`repeatRemoveAllImpliesRepeat`).

## Zero-axiom design decisions (the lane's propext minefield)

  * The Bool-match reductions of `countVertexOccurrences` / `removeAllVertexOccurrences` are isolated in
    `countConsTrue/False` and `removeAllConsTrue/False`, each closed by `rw [hEq]` then an EXPLICIT `rfl`
    where the residue is `count + 0` / `true || _` (default-transparency `rfl` reduces `Nat.add`/`Bool.or`
    — `rw`'s trailing reducible-only `rfl` does not; the r10 `sorryAx` trap).
  * The length bound threads through the ADDITIVE `removeAllLengthPlusCount`
    (`(removeAll).length + count = walk.length`) — never `walk.length - count` (`Nat.sub` leaks propext).
  * Every case split on `natEqBool _ _` is `cases hMatch : natEqBool _ _ with | true | false` (full-enum,
    never a wildcard arm, never `by_cases`/`decide` on the equality).
  * Membership is destructured only via `List.Mem.head` / `List.Mem.tail` `cases`, never `decide` on
    `List.Mem` and never `mem_flatMap` / `mem_append`.
  * `natListContains`'s argument order compares `natEqBool head target`; `removeAll` compares
    `natEqBool vertex target` — so `natEqBoolSymm` is load-bearing at the carrier-membership transport.

No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.  STRUCTURAL
recursion (carrier / walk lists, count `Nat`).  Per-declaration gated (and independently `#print
axioms`-checked for the load-bearing decls) in
`FX1PolyAudit/Polygraph/Homology/FiniteCarrierWalkPigeonhole.lean`. -/

namespace FX1Poly.Polygraph.Homology

/-! ## Truth-probes: the three hostile graphs (machine-checked `rfl` on the computed oracle) -/

/-- **The directed 3-cycle is correctly NON-acyclic at saturating fuel.**  `[(0,1),(1,2),(2,0)]` is a
length-3 cycle; the checker reports it non-acyclic at fuel `2` and `4` (so the acyclicity-soundness
theorem is inapplicable — exactly the intended behaviour, not a soundness gap). -/
theorem threeCycleIsNonAcyclicAtSaturatingFuel :
    isAcyclicUfnarovskiGraph [(0, 1), (1, 2), (2, 0)] 2 = false ∧
    isAcyclicUfnarovskiGraph [(0, 1), (1, 2), (2, 0)] 4 = false :=
  ⟨rfl, rfl⟩

/-- **The DAG chain is acyclic with an already-vanishing (binary) census.**  `[(0,1),(1,2),(2,3)]` lives
on four letters yet its census — blind to letters `≥ 2` (FINDING A) — already vanishes at degree `2`. -/
theorem dagChainIsAcyclicWithVanishingBinaryCensus :
    isAcyclicUfnarovskiGraph [(0, 1), (1, 2), (2, 3)] 4 = true ∧
    multiObstructionChainRankOracle [(0, 1), (1, 2), (2, 3)] 2 = 0 :=
  ⟨rfl, rfl⟩

/-- **The diamond is acyclic with an already-vanishing (binary) census.**  `[(0,1),(0,2),(1,3),(2,3)]`
degenerates to the `{xy}` census for the same alphabet-wall reason. -/
theorem diamondIsAcyclicWithVanishingBinaryCensus :
    isAcyclicUfnarovskiGraph [(0, 1), (0, 2), (1, 3), (2, 3)] 4 = true ∧
    multiObstructionChainRankOracle [(0, 1), (0, 2), (1, 3), (2, 3)] 2 = 0 :=
  ⟨rfl, rfl⟩

/-! ## Definitions -/

/-- **Does this walk revisit a vertex?**  `true` iff some vertex occurs at least twice (each head checked
against its own tail via `natListContains`). -/
def hasRepeatedVertex : List Nat → Bool
  | [] => false
  | vertex :: remainingWalk => natListContains remainingWalk vertex || hasRepeatedVertex remainingWalk

/-- The number of times `target` occurs in a walk.  The `natEqBool` verdict is added on the RIGHT so the
cons-case reduces to `count + 1` / `count + 0` DEFINITIONALLY (`Nat.add _ (succ/zero)`). -/
def countVertexOccurrences (target : Nat) : List Nat → Nat
  | [] => 0
  | vertex :: remainingWalk =>
      countVertexOccurrences target remainingWalk
        + (match natEqBool vertex target with | true => 1 | false => 0)

/-- Drop EVERY occurrence of `target` from a walk (not just the first — carrier-induction needs the whole
class of copies gone so the pruned walk lives over the smaller carrier). -/
def removeAllVertexOccurrences (target : Nat) : List Nat → List Nat
  | [] => []
  | vertex :: remainingWalk =>
      match natEqBool vertex target with
      | true => removeAllVertexOccurrences target remainingWalk
      | false => vertex :: removeAllVertexOccurrences target remainingWalk

/-! ## Cons-reduction lemmas (isolate the Bool-match reduction; explicit `rfl` beats the reducible trap) -/

/-- When the head matches `target`, the count of the cons is the tail count plus one. -/
theorem countConsTrue (target vertex : Nat) (remainingWalk : List Nat)
    (hEq : natEqBool vertex target = true) :
    countVertexOccurrences target (vertex :: remainingWalk)
      = countVertexOccurrences target remainingWalk + 1 := by
  show countVertexOccurrences target remainingWalk
      + (match natEqBool vertex target with | true => 1 | false => 0)
      = countVertexOccurrences target remainingWalk + 1
  rw [hEq]

/-- When the head misses `target`, the count of the cons is the tail count. -/
theorem countConsFalse (target vertex : Nat) (remainingWalk : List Nat)
    (hEq : natEqBool vertex target = false) :
    countVertexOccurrences target (vertex :: remainingWalk)
      = countVertexOccurrences target remainingWalk := by
  show countVertexOccurrences target remainingWalk
      + (match natEqBool vertex target with | true => 1 | false => 0)
      = countVertexOccurrences target remainingWalk
  rw [hEq]
  rfl

/-- When the head matches `target`, `removeAll` drops it and keeps the tail's removal. -/
theorem removeAllConsTrue (target vertex : Nat) (remainingWalk : List Nat)
    (hEq : natEqBool vertex target = true) :
    removeAllVertexOccurrences target (vertex :: remainingWalk)
      = removeAllVertexOccurrences target remainingWalk := by
  show (match natEqBool vertex target with
        | true => removeAllVertexOccurrences target remainingWalk
        | false => vertex :: removeAllVertexOccurrences target remainingWalk)
      = removeAllVertexOccurrences target remainingWalk
  rw [hEq]

/-- When the head misses `target`, `removeAll` keeps it in front of the tail's removal. -/
theorem removeAllConsFalse (target vertex : Nat) (remainingWalk : List Nat)
    (hEq : natEqBool vertex target = false) :
    removeAllVertexOccurrences target (vertex :: remainingWalk)
      = vertex :: removeAllVertexOccurrences target remainingWalk := by
  show (match natEqBool vertex target with
        | true => removeAllVertexOccurrences target remainingWalk
        | false => vertex :: removeAllVertexOccurrences target remainingWalk)
      = vertex :: removeAllVertexOccurrences target remainingWalk
  rw [hEq]

/-! ## `natEqBool` symmetry + the `Nat` dichotomy -/

/-- `natEqBool` is symmetric (double `Nat` induction; the successor arm is the recursive call, the
mixed base arms are `rfl` on `false`). -/
theorem natEqBoolSymm : ∀ (first second : Nat), natEqBool first second = natEqBool second first
  | 0, 0 => rfl
  | 0, _ + 1 => rfl
  | _ + 1, 0 => rfl
  | first + 1, second + 1 => natEqBoolSymm first second

/-- Every `Nat` is either `≤ 1` or `≥ 2` (structural on the value; `≥ 2` via `Nat.le_add_left`). -/
theorem natLeOneOrGeTwo : ∀ (value : Nat), value ≤ 1 ∨ 2 ≤ value
  | 0 => Or.inl (Nat.zero_le 1)
  | 1 => Or.inl (Nat.le_refl 1)
  | _ + 2 => Or.inr (Nat.le_add_left 2 _)

/-! ## `natListContains` helpers -/

/-- Consing a fresh head preserves membership: if the tail contains `other`, so does the cons. -/
theorem consPreservesContains (vertex other : Nat) (remainingWalk : List Nat)
    (hTail : natListContains remainingWalk other = true) :
    natListContains (vertex :: remainingWalk) other = true := by
  show (natEqBool vertex other || natListContains remainingWalk other) = true
  rw [hTail]
  exact Bool.or_true _

/-- A positive occurrence count forces membership (structural on the walk; the false head recurses on the
tail via `countConsFalse`). -/
theorem countPositiveImpliesContains (target : Nat) :
    ∀ walk, 1 ≤ countVertexOccurrences target walk → natListContains walk target = true
  | [], hPos => absurd hPos (Nat.not_succ_le_zero 0)
  | vertex :: remainingWalk, hPos => by
      cases hMatch : natEqBool vertex target with
      | true =>
          show (natEqBool vertex target || natListContains remainingWalk target) = true
          rw [hMatch]
          rfl
      | false =>
          have hCountEq := countConsFalse target vertex remainingWalk hMatch
          rw [hCountEq] at hPos
          exact consPreservesContains vertex target remainingWalk
            (countPositiveImpliesContains target remainingWalk hPos)

/-- **A vertex occurring `≥ 2` times makes the walk repeat.**  Structural on the walk: at a matching head
the tail already contains the (equal) vertex (`countPositiveImpliesContains`), firing the head disjunct;
at a missing head the IH fires the tail disjunct. -/
theorem countGeTwoImpliesRepeat (target : Nat) :
    ∀ walk, 2 ≤ countVertexOccurrences target walk → hasRepeatedVertex walk = true
  | [], hGe => absurd hGe (Nat.not_succ_le_zero 1)
  | vertex :: remainingWalk, hGe => by
      cases hMatch : natEqBool vertex target with
      | true =>
          have hCountEq := countConsTrue target vertex remainingWalk hMatch
          rw [hCountEq] at hGe
          have hTailPos : 1 ≤ countVertexOccurrences target remainingWalk :=
            Nat.le_of_succ_le_succ hGe
          have hVertexEqTarget : vertex = target := natEqBoolTrueImpliesEq vertex target hMatch
          have hContainsTarget : natListContains remainingWalk target = true :=
            countPositiveImpliesContains target remainingWalk hTailPos
          show (natListContains remainingWalk vertex || hasRepeatedVertex remainingWalk) = true
          rw [hVertexEqTarget, hContainsTarget]
          rfl
      | false =>
          have hCountEq := countConsFalse target vertex remainingWalk hMatch
          rw [hCountEq] at hGe
          have hRec := countGeTwoImpliesRepeat target remainingWalk hGe
          show (natListContains remainingWalk vertex || hasRepeatedVertex remainingWalk) = true
          rw [hRec]
          exact Bool.or_true _

/-! ## The additive length identity (sidesteps `Nat.sub`) -/

/-- **The pruned length plus the removed count equals the original length.**  ADDITIVE by design — the
length bound in the pigeonhole reads off `(removeAll).length + count = walk.length`, never
`walk.length - count`.  Structural on the walk; the successor rearrangements are `Nat.add_assoc` /
`Nat.add_right_comm` (both propext-clean). -/
theorem removeAllLengthPlusCount (target : Nat) :
    ∀ walk, (removeAllVertexOccurrences target walk).length + countVertexOccurrences target walk
              = walk.length
  | [] => rfl
  | vertex :: remainingWalk => by
      have hIH := removeAllLengthPlusCount target remainingWalk
      cases hMatch : natEqBool vertex target with
      | true =>
          rw [removeAllConsTrue target vertex remainingWalk hMatch,
              countConsTrue target vertex remainingWalk hMatch]
          show (removeAllVertexOccurrences target remainingWalk).length
              + (countVertexOccurrences target remainingWalk + 1)
              = remainingWalk.length + 1
          rw [← Nat.add_assoc]
          exact congrArg (fun measured => measured + 1) hIH
      | false =>
          rw [removeAllConsFalse target vertex remainingWalk hMatch,
              countConsFalse target vertex remainingWalk hMatch]
          show ((removeAllVertexOccurrences target remainingWalk).length + 1)
              + countVertexOccurrences target remainingWalk
              = remainingWalk.length + 1
          rw [Nat.add_right_comm]
          exact congrArg (fun measured => measured + 1) hIH

/-! ## `removeAll` membership transport -/

/-- Membership survives pruning: if `other` is in the pruned walk it was in the original.  Structural on
the walk; both Bool-splits reduce via the cons lemmas, then recurse. -/
theorem containsRemoveAllImpliesContains (target other : Nat) :
    ∀ walk, natListContains (removeAllVertexOccurrences target walk) other = true →
            natListContains walk other = true
  | [], hContains => Bool.noConfusion hContains
  | vertex :: remainingWalk, hContains => by
      cases hMatch : natEqBool vertex target with
      | true =>
          rw [removeAllConsTrue target vertex remainingWalk hMatch] at hContains
          exact consPreservesContains vertex other remainingWalk
            (containsRemoveAllImpliesContains target other remainingWalk hContains)
      | false =>
          rw [removeAllConsFalse target vertex remainingWalk hMatch] at hContains
          have hExpand :
              natListContains (vertex :: removeAllVertexOccurrences target remainingWalk) other
              = (natEqBool vertex other
                 || natListContains (removeAllVertexOccurrences target remainingWalk) other) := rfl
          rw [hExpand] at hContains
          cases hOther : natEqBool vertex other with
          | true =>
              show (natEqBool vertex other || natListContains remainingWalk other) = true
              rw [hOther]
              rfl
          | false =>
              rw [hOther] at hContains
              have hTail :
                  natListContains (removeAllVertexOccurrences target remainingWalk) other = true :=
                hContains
              exact consPreservesContains vertex other remainingWalk
                (containsRemoveAllImpliesContains target other remainingWalk hTail)

/-- **A repeat in the pruned walk lifts to a repeat in the original.**  Structural on the walk; a pruned
head-membership transports via `containsRemoveAllImpliesContains`, a pruned tail-repeat via the IH. -/
theorem repeatRemoveAllImpliesRepeat (target : Nat) :
    ∀ walk, hasRepeatedVertex (removeAllVertexOccurrences target walk) = true →
            hasRepeatedVertex walk = true
  | [], hRepeat => Bool.noConfusion hRepeat
  | vertex :: remainingWalk, hRepeat => by
      cases hMatch : natEqBool vertex target with
      | true =>
          rw [removeAllConsTrue target vertex remainingWalk hMatch] at hRepeat
          have hRec := repeatRemoveAllImpliesRepeat target remainingWalk hRepeat
          show (natListContains remainingWalk vertex || hasRepeatedVertex remainingWalk) = true
          rw [hRec]
          exact Bool.or_true _
      | false =>
          rw [removeAllConsFalse target vertex remainingWalk hMatch] at hRepeat
          have hExpand :
              hasRepeatedVertex (vertex :: removeAllVertexOccurrences target remainingWalk)
              = (natListContains (removeAllVertexOccurrences target remainingWalk) vertex
                 || hasRepeatedVertex (removeAllVertexOccurrences target remainingWalk)) := rfl
          rw [hExpand] at hRepeat
          cases hHead : natListContains (removeAllVertexOccurrences target remainingWalk) vertex with
          | true =>
              have hInRemaining : natListContains remainingWalk vertex = true :=
                containsRemoveAllImpliesContains target vertex remainingWalk hHead
              show (natListContains remainingWalk vertex || hasRepeatedVertex remainingWalk) = true
              rw [hInRemaining]
              rfl
          | false =>
              rw [hHead] at hRepeat
              have hRecRepeat :
                  hasRepeatedVertex (removeAllVertexOccurrences target remainingWalk) = true :=
                hRepeat
              have hRw := repeatRemoveAllImpliesRepeat target remainingWalk hRecRepeat
              show (natListContains remainingWalk vertex || hasRepeatedVertex remainingWalk) = true
              rw [hRw]
              exact Bool.or_true _

/-- **A member of the pruned walk is a distinct member of the original.**  `List.Mem`-constructor route:
the `head` case unifies the pruned head with the queried vertex (its distinctness IS `hMatch`), the `tail`
case recurses.  Feeds the carrier-membership transport in the pigeonhole. -/
theorem memRemoveAllImpliesMemAndDistinct (target vertex : Nat) :
    ∀ walk, vertex ∈ removeAllVertexOccurrences target walk →
            vertex ∈ walk ∧ natEqBool vertex target = false
  | [], hMem => by
      have hMemNil : vertex ∈ ([] : List Nat) := hMem
      cases hMemNil
  | headVertex :: remainingWalk, hMem => by
      cases hMatch : natEqBool headVertex target with
      | true =>
          rw [removeAllConsTrue target headVertex remainingWalk hMatch] at hMem
          have hRec := memRemoveAllImpliesMemAndDistinct target vertex remainingWalk hMem
          exact ⟨List.Mem.tail headVertex hRec.left, hRec.right⟩
      | false =>
          rw [removeAllConsFalse target headVertex remainingWalk hMatch] at hMem
          cases hMem with
          | head => exact ⟨List.Mem.head remainingWalk, hMatch⟩
          | tail _ hMemTail =>
              have hRec := memRemoveAllImpliesMemAndDistinct target vertex remainingWalk hMemTail
              exact ⟨List.Mem.tail headVertex hRec.left, hRec.right⟩

/-! ## The pigeonhole — ingredient (i) of `generalGraphLongestPathBoundIsNamedNode` -/

/-- ★★ **THE FINITE-CARRIER WALK PIGEONHOLE** (r10 named ingredient (i), delivered): a walk over a finite
vertex carrier strictly longer than the carrier repeats a vertex.  STRUCTURAL on the CARRIER; the step
dichotomises on `countVertexOccurrences frontVertex walk` — `2 ≤ count` exhibits the repeat directly, and
`count ≤ 1` recurses on the pruned walk (all copies of `frontVertex` removed) over the smaller carrier,
its length still exceeding the carrier's by the additive identity, then lifts the pruned repeat back.
Alphabet-agnostic (the carrier is any `List Nat`), zero-axiom. -/
theorem listOverCarrierRepeats :
    ∀ (carrier walk : List Nat),
      (∀ vertex, vertex ∈ walk → natListContains carrier vertex = true) →
      carrier.length < walk.length →
      hasRepeatedVertex walk = true
  | [], walk, hAllInCarrier, hLenLt => by
      cases walk with
      | nil => exact absurd hLenLt (Nat.lt_irrefl 0)
      | cons headWalk tailWalk =>
          have hIn : natListContains [] headWalk = true :=
            hAllInCarrier headWalk (List.Mem.head tailWalk)
          exact Bool.noConfusion hIn
  | frontVertex :: restCarrier, walk, hAllInCarrier, hLenLt => by
      cases natLeOneOrGeTwo (countVertexOccurrences frontVertex walk) with
      | inr hGeTwo =>
          exact countGeTwoImpliesRepeat frontVertex walk hGeTwo
      | inl hLeOne =>
          have hPrunedMembers : ∀ vertex, vertex ∈ removeAllVertexOccurrences frontVertex walk →
              natListContains restCarrier vertex = true := by
            intro vertex hMemPruned
            have hSplit := memRemoveAllImpliesMemAndDistinct frontVertex vertex walk hMemPruned
            have hInCarrier : natListContains (frontVertex :: restCarrier) vertex = true :=
              hAllInCarrier vertex hSplit.left
            have hExpand : natListContains (frontVertex :: restCarrier) vertex
                = (natEqBool frontVertex vertex || natListContains restCarrier vertex) := rfl
            rw [hExpand] at hInCarrier
            have hFrontNe : natEqBool frontVertex vertex = false := by
              rw [natEqBoolSymm frontVertex vertex]; exact hSplit.right
            rw [hFrontNe] at hInCarrier
            exact hInCarrier
          have hLenPruned : restCarrier.length
              < (removeAllVertexOccurrences frontVertex walk).length := by
            have hAdd := removeAllLengthPlusCount frontVertex walk
            have hWalkLe : walk.length
                ≤ (removeAllVertexOccurrences frontVertex walk).length + 1 := by
              rw [← hAdd]
              exact Nat.add_le_add_left hLeOne _
            have hSuccLt : restCarrier.length + 1
                < (removeAllVertexOccurrences frontVertex walk).length + 1 :=
              Nat.lt_of_lt_of_le hLenLt hWalkLe
            exact Nat.lt_of_succ_lt_succ hSuccLt
          have hPrunedRepeat :
              hasRepeatedVertex (removeAllVertexOccurrences frontVertex walk) = true :=
            listOverCarrierRepeats restCarrier (removeAllVertexOccurrences frontVertex walk)
              hPrunedMembers hLenPruned
          exact repeatRemoveAllImpliesRepeat frontVertex walk hPrunedRepeat

/-! ## Ship-gate witnesses -/

/-- Concrete smoke: the length-4 walk `[0, 1, 2, 0]` over the 3-element carrier `{0, 1, 2}` repeats. -/
theorem hasRepeatedVertexOnConcreteWalk : hasRepeatedVertex [0, 1, 2, 0] = true := rfl

/-- **Alphabet-agnostic witness**: the pigeonhole fires over a NON-`{0, 1}` carrier (`{10, 20}`, walk
`[10, 20, 10]`), confirming the brick is genuinely reusable once the n-ary census oracle (prerequisite
(0), FINDING A) lands. -/
theorem pigeonholeHoldsOverNonBinaryCarrier :
    hasRepeatedVertex [10, 20, 10] = true :=
  listOverCarrierRepeats [10, 20] [10, 20, 10]
    (fun vertex hMem => by
      cases hMem with
      | head => rfl
      | tail _ hInner =>
          cases hInner with
          | head => rfl
          | tail _ hInnermost =>
              cases hInnermost with
              | head => rfl
              | tail _ hEmpty => cases hEmpty)
    (by decide)

/-! ## Ledger — the r11 delivery and the standing residuals -/

/-- ★ **The general-graph acyclicity-soundness node still stands, with ingredient (i) DELIVERED.**  This
module ships `listOverCarrierRepeats` (the classical finite-carrier walk pigeonhole, alphabet-agnostic,
zero-axiom), which is r10's named ingredient (i) of `generalGraphLongestPathBoundIsNamedNode`.  The
general statement `isAcyclicUfnarovskiGraph edges vertexCount = true ==> ∀ degree, vertexCount ≤ degree
==> multiObstructionChainRankOracle edges degree = 0` still needs the following (residual (0) now
DELIVERED in r12; (ii)/(iii)/assembly still open), recorded honestly:

  (0) **the n-ary alphabet enumerator** — DELIVERED (r12,
      `FX1Poly.Polygraph.Homology.NaryAlphabetObstructionChainEnumerator`).  The shipped
      `allWordsOfLength` / `multiObstructionChainRankOracle` were BINARY-hardwired (blind to letters
      `≥ 2`) — the wall FINDING A named — so the pigeonhole could not connect to the census at any
      alphabet `> {0, 1}`.  r12 ships `allWordsOverAlphabet` + the re-based census oracle
      `multiObstructionChainRankOracleOver`, PROVEN to subsume the binary enumerator
      (`binaryEnumeratorAgrees` / `binaryOracleAgrees`, so no regression), with the reconnection
      corollaries healing the alphabet-blind censuses (the DAG chain / diamond truncating at their TRUE
      longest path, the 3-cycle constant).  The general node has FOUR ingredients, not the three r10
      recorded — this one now supplied.
  (ii) **checker saturation** — FINDING B: `isAcyclicUfnarovskiGraph edges vertexCount = true` is sound
      only at saturating fuel (a length-`L` cycle is caught only at `fuel ≥ L - 1`); proving `fuel =
      vertexCount` captures every cycle is a separate hard lemma the pigeonhole does not touch.
  (iii) **the topological-sort longest-path bound** — a valid walk in an acyclic graph has no repeated
      vertex (the semantic converse the pigeonhole's `hasRepeatedVertex` contradicts), so chains die above
      `vertexCount`.
  plus the final assembly wiring (0)+(i)+(ii)+(iii) into the census-zero closed form.

Read the meaning from THIS docstring.  `= true`. -/
def generalGraphSoundnessResidualsAfterPigeonhole : Bool := true

/-- ★ **The TOWER-ANICK (#2144) r11 ledger marker.**  What stands, zero-axiom, additively over r10: the
finite-carrier walk pigeonhole `listOverCarrierRepeats` (r10 named ingredient (i)), STRUCTURAL on the
carrier via `removeAllVertexOccurrences` + the additive `removeAllLengthPlusCount` (no `Nat.sub`) + the
`List.Mem`-constructor membership transport, with the three hostile-graph verdicts pinned as `rfl`
truth-probes and an alphabet-agnostic ship-gate witness.  Ingredient (i) DELIVERED; residual (0) n-ary
alphabet enumerator (FINDING A) DELIVERED in r12
(`FX1Poly.Polygraph.Homology.NaryAlphabetObstructionChainEnumerator`); residuals (ii) checker saturation
(FINDING B), (iii) topological-sort longest-path bound, plus assembly — all NAMED in
`generalGraphSoundnessResidualsAfterPigeonhole`, never papered.  Read the meaning from THIS docstring
(the honest-record convention). -/
def finiteCarrierWalkPigeonholeIsShipped : Bool := true

end FX1Poly.Polygraph.Homology
