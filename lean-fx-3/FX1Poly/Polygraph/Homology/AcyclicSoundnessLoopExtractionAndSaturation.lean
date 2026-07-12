import FX1Poly.Polygraph.Homology.NaryAlphabetObstructionChainEnumerator

/-! # FX1Poly/Polygraph/Homology/AcyclicSoundnessLoopExtractionAndSaturation — the checker-soundness
    core (residuals (ii) checker saturation + (iii) longest-path loop extraction of
    `generalGraphSoundnessResidualsAfterPigeonhole`): from an edge-respecting word with a repeated
    vertex, extract a SIMPLE closed subwalk and drive the checker's detection branch to `true`
    (TOWER-ANICK r13, #2144)

The r11 file `FiniteCarrierWalkPigeonhole` shipped the classical finite-carrier walk pigeonhole
`listOverCarrierRepeats` (ingredient (i)) and named residuals (ii) checker saturation (FINDING B: a
length-`L` cycle is caught only at `fuel >= L - 1`) and (iii) the topological-sort longest-path bound.
The r12 file `NaryAlphabetObstructionChainEnumerator` shipped residual (0), the n-ary enumerator.  This
module ships the SATURATION + EXTRACTION core, residuals (ii) + (iii):

## (b) SATURATION — walk reaches its end within its own length, monotone in fuel

`walkReachesLast`: an edge-respecting walk `first :: rest` whose head is in the seed `frontier` reaches
its last vertex within `rest.length` frontier-expansion rounds (each edge advances exactly one BFS
layer, matching `obstructionReachableWithin`'s `frontier ++ (... frontierStep ...)` recursion —
structural on the walk tail, additive fuel `rest.length`, NEVER `Nat.sub`).  `reachableWithinMonotone`:
more fuel keeps every earlier-reached vertex (structural on the `Nat.le` proof, no `Nat.sub`).
Combined at `fuel = vertexCount` these drive `obstructionSourceReachesItself` to `true`
(`loopImpliesReachesItself`), then `reachesItselfImpliesCheckerFalse` folds it through
`anyObstructionSourceOnCycle`, negated by `isAcyclicUfnarovskiGraph = Bool.not (...)`.  A SIMPLE loop of
`<= vertexCount` edges (bounded by the CONTRAPOSITIVE of the shipped pigeonhole, no new pigeonhole) makes
the single fixed fuel `vertexCount` suffice — subsuming residual (ii) by the length bound rather than a
fixpoint lemma.

## (a) EXTRACTION — first-repeat simple-loop cut

`scanForRepeat` scans left-to-right carrying the (distinct, in-order) `seen` prefix, stops at the first
vertex already in `seen` (`splitAtFirst`), and returns the loop start + interior body.  The closed walk
`source :: loopBody ++ [source]` is a contiguous infix of the original (guard transported by
`guardTakePrefix` / `guardDropPrefix`), and `source :: loopBody` is DISTINCT (no interior repeat), so the
pigeonhole contrapositive bounds its length by `vertexCount` for free.  `scanForRepeatSpec` is the one
correctness theorem (structural on the walk, invariant `seen ++ walk = original` + `seen` distinct + all
letters in the alphabet).

## Honest scope (NO overclaim)

This ships residuals (ii) + (iii): `shortSimpleLoopImpliesCheckerFalse` (the checker is sound on any
simple short edge-loop) and `closedEdgeWalkImpliesCheckerFalse` (any edge-respecting word with a repeat
and letters in an `alphabet` drives the checker at `fuel = alphabet.length` to `false`).  r13 itself does
NOT ship (c) the census-zero closed form nor (d) the eventual-exactness assembly; those are SHIPPED in the
r14 file `AcyclicSystemTruncationCertificate` (`acyclicCensusZeroAboveAlphabetLength` (c) +
`acyclicSystemExactAboveAlphabetLength` (d), the monomial model at the loose `alphabet.length` bound).  No
Smith import, no Homology<->Omega edge.

## Zero-axiom design decisions (the lane's propext minefield)

  * `Bool` conjunction / disjunction are split by HAND-ROLLED `boolAndElim*` / `boolOrElim` (`cases` on the
    Bool value + `Bool.noConfusion`) — never `Bool.and_eq_true` / `Bool.or_eq_true` (both leak `propext`).
  * `List.append` associativity / nil are hand-rolled `appendAssoc` / `appendNil` (`congrArg` on the cons
    step) — never `List.append_assoc` (leaks `propext`).
  * Membership is `natListContains`-Bool or `List.Mem`-constructor (`List.Mem.head` / `List.Mem.tail`
    `cases`) — never `decide` on `List.Mem`, never `mem_append` / `mem_map`.
  * `natEqBool`-argument order matters: `obstructionOutNeighbours` compares `natEqBool source0 vertex`,
    `isObstructionPair` compares `natEqBool letter pair.1` — `natEqBoolSymm` is load-bearing at every
    bridge.  Every split is `cases h : natEqBool _ _`, never `by_cases` / `decide`.
  * Fuel is additive (`rest.length`, the `Nat.le` recursor) — NEVER `Nat.sub`.

No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.  STRUCTURAL
recursion (walk / edge / frontier lists, fuel `Nat`, `Nat.le` proof).  Per-declaration gated (and
independently `#print axioms`-checked for the load-bearing decls) in
`FX1PolyAudit/Polygraph/Homology/AcyclicSoundnessLoopExtractionAndSaturation.lean`. -/

namespace FX1Poly.Polygraph.Homology

/-! ## A0 — hand-rolled `Bool` splitters (never the propext-leaking `Bool.and_eq_true` / `or_eq_true`) -/

/-- From `(a && b) = true`, the left factor is `true`.  `cases` on `a`; the `false` arm is `false = true`. -/
theorem boolAndElimLeft {leftBit rightBit : Bool} (hAnd : (leftBit && rightBit) = true) : leftBit = true := by
  cases hLeft : leftBit with
  | true => rfl
  | false => rw [hLeft] at hAnd; exact Bool.noConfusion hAnd

/-- From `(a && b) = true`, the right factor is `true`.  `cases` on `a`; `true && b` reduces to `b`. -/
theorem boolAndElimRight {leftBit rightBit : Bool} (hAnd : (leftBit && rightBit) = true) : rightBit = true := by
  cases hLeft : leftBit with
  | true => rw [hLeft] at hAnd; exact hAnd
  | false => rw [hLeft] at hAnd; exact Bool.noConfusion hAnd

/-- Build `(a && b) = true` from both factors true.  `subst` both to `true && true = true`. -/
theorem boolAndIntro {leftBit rightBit : Bool} (hLeft : leftBit = true) (hRight : rightBit = true) :
    (leftBit && rightBit) = true := by
  subst hLeft; subst hRight; rfl

/-- From `(a || b) = true` with `a = false`, the right disjunct is `true`.  `false || b` reduces to `b`. -/
theorem boolOrLeftFalse {leftBit rightBit : Bool} (hOr : (leftBit || rightBit) = true)
    (hLeftFalse : leftBit = false) : rightBit = true := by
  rw [hLeftFalse] at hOr; exact hOr

/-- Case-split `(a || b) = true` into which disjunct holds.  `cases` on `a`. -/
theorem boolOrElim {leftBit rightBit : Bool} (hOr : (leftBit || rightBit) = true) :
    leftBit = true ∨ rightBit = true := by
  cases hLeft : leftBit with
  | true => exact Or.inl rfl
  | false => rw [hLeft] at hOr; exact Or.inr hOr

/-- From `(a || b) = false`, the left disjunct is `false`.  A `true` left forces the whole to `true`. -/
theorem boolOrFalseElimLeft {leftBit rightBit : Bool} (hOr : (leftBit || rightBit) = false) : leftBit = false := by
  cases hLeft : leftBit with
  | true => rw [hLeft] at hOr; exact Bool.noConfusion hOr
  | false => rfl

/-- From `(a || b) = false`, the right disjunct is `false`. -/
theorem boolOrFalseElimRight {leftBit rightBit : Bool} (hOr : (leftBit || rightBit) = false) : rightBit = false := by
  cases hLeft : leftBit with
  | true => rw [hLeft] at hOr; exact Bool.noConfusion hOr
  | false => rw [hLeft] at hOr; exact hOr

/-! ## A1 — `natListContains` over `++` (Bool membership, hand-rolled, no `mem_append`) -/

/-- Membership in the left half survives `++`.  Structural on the left list. -/
theorem natListContainsAppendLeft (target : Nat) :
    ∀ (leftList rightList : List Nat),
      natListContains leftList target = true → natListContains (leftList ++ rightList) target = true
  | [], _, hMem => Bool.noConfusion hMem
  | headVertex :: remainingLeft, rightList, hMem => by
      show (natEqBool headVertex target || natListContains (remainingLeft ++ rightList) target) = true
      have hSplit : (natEqBool headVertex target || natListContains remainingLeft target) = true := hMem
      cases hHead : natEqBool headVertex target with
      | true => rfl
      | false =>
          have hTail : natListContains remainingLeft target = true := boolOrLeftFalse hSplit hHead
          exact natListContainsAppendLeft target remainingLeft rightList hTail

/-- Membership in the right half survives `++`.  Structural on the left list. -/
theorem natListContainsAppendRight (target : Nat) :
    ∀ (leftList rightList : List Nat),
      natListContains rightList target = true → natListContains (leftList ++ rightList) target = true
  | [], _, hMem => hMem
  | headVertex :: remainingLeft, rightList, hMem => by
      show (natEqBool headVertex target || natListContains (remainingLeft ++ rightList) target) = true
      have hRec : natListContains (remainingLeft ++ rightList) target = true :=
        natListContainsAppendRight target remainingLeft rightList hMem
      rw [hRec]
      exact Bool.or_true _

/-- Membership in `A ++ B` splits into membership in `A` or in `B`.  Structural on the left list. -/
theorem natListContainsAppendCases (target : Nat) :
    ∀ (leftList rightList : List Nat),
      natListContains (leftList ++ rightList) target = true →
      natListContains leftList target = true ∨ natListContains rightList target = true
  | [], _, hMem => Or.inr hMem
  | headVertex :: remainingLeft, rightList, hMem => by
      have hSplit : (natEqBool headVertex target || natListContains (remainingLeft ++ rightList) target) = true := hMem
      cases hHead : natEqBool headVertex target with
      | true =>
          apply Or.inl
          show (natEqBool headVertex target || natListContains remainingLeft target) = true
          rw [hHead]; rfl
      | false =>
          have hRest : natListContains (remainingLeft ++ rightList) target = true := boolOrLeftFalse hSplit hHead
          cases natListContainsAppendCases target remainingLeft rightList hRest with
          | inl hInLeft =>
              apply Or.inl
              show (natEqBool headVertex target || natListContains remainingLeft target) = true
              rw [hInLeft]; exact Bool.or_true _
          | inr hInRight => exact Or.inr hInRight

/-- Non-membership in both halves gives non-membership in `++`.  Structural on the left list. -/
theorem natListContainsAppendFalse (target : Nat) :
    ∀ (leftList rightList : List Nat),
      natListContains leftList target = false → natListContains rightList target = false →
      natListContains (leftList ++ rightList) target = false
  | [], _, _, hRight => hRight
  | headVertex :: remainingLeft, rightList, hLeft, hRight => by
      show (natEqBool headVertex target || natListContains (remainingLeft ++ rightList) target) = false
      have hHead : natEqBool headVertex target = false := boolOrFalseElimLeft hLeft
      have hTail : natListContains remainingLeft target = false := boolOrFalseElimRight hLeft
      rw [hHead]
      exact natListContainsAppendFalse target remainingLeft rightList hTail hRight

/-! ## A2 — the multi-obstruction guard over `++` (drop prefix / take prefix / first pair) -/

/-- Dropping ONE head from a guard-true walk keeps the tail guard-true.  `cases` on the tail. -/
theorem guardTailStep (edges : List (Nat × Nat)) (headVertex : Nat) (tailWalk : List Nat)
    (hGuard : allAdjacentPairsAreObstructions edges (headVertex :: tailWalk) = true) :
    allAdjacentPairsAreObstructions edges tailWalk = true := by
  cases tailWalk with
  | nil => rfl
  | cons secondVertex remainingWalk =>
      have hGuard' :
          (isObstructionPair edges headVertex secondVertex
            && allAdjacentPairsAreObstructions edges (secondVertex :: remainingWalk)) = true := hGuard
      exact boolAndElimRight hGuard'

/-- The first adjacent pair of a guard-true walk of length `>= 2` is an obstruction. -/
theorem guardFirstPair (edges : List (Nat × Nat)) (firstVertex secondVertex : Nat) (remainingWalk : List Nat)
    (hGuard : allAdjacentPairsAreObstructions edges (firstVertex :: secondVertex :: remainingWalk) = true) :
    isObstructionPair edges firstVertex secondVertex = true := by
  have hGuard' :
      (isObstructionPair edges firstVertex secondVertex
        && allAdjacentPairsAreObstructions edges (secondVertex :: remainingWalk)) = true := hGuard
  exact boolAndElimLeft hGuard'

/-- Dropping a whole prefix keeps the suffix guard-true.  Structural on the prefix via `guardTailStep`. -/
theorem guardDropPrefix (edges : List (Nat × Nat)) :
    ∀ (prefixWalk suffixWalk : List Nat),
      allAdjacentPairsAreObstructions edges (prefixWalk ++ suffixWalk) = true →
      allAdjacentPairsAreObstructions edges suffixWalk = true
  | [], _, hGuard => hGuard
  | prefixHead :: remainingPrefix, suffixWalk, hGuard => by
      have hDropOne : allAdjacentPairsAreObstructions edges (remainingPrefix ++ suffixWalk) = true :=
        guardTailStep edges prefixHead (remainingPrefix ++ suffixWalk) hGuard
      exact guardDropPrefix edges remainingPrefix suffixWalk hDropOne

/-- Taking a whole prefix from a guard-true walk keeps the prefix guard-true.  Structural on the prefix. -/
theorem guardTakePrefix (edges : List (Nat × Nat)) :
    ∀ (prefixWalk suffixWalk : List Nat),
      allAdjacentPairsAreObstructions edges (prefixWalk ++ suffixWalk) = true →
      allAdjacentPairsAreObstructions edges prefixWalk = true
  | [], _, _ => rfl
  | [_], _, _ => rfl
  | firstVertex :: secondVertex :: remainingPrefix, suffixWalk, hGuard => by
      have hGuard' :
          (isObstructionPair edges firstVertex secondVertex
            && allAdjacentPairsAreObstructions edges ((secondVertex :: remainingPrefix) ++ suffixWalk)) = true :=
        hGuard
      have hPair : isObstructionPair edges firstVertex secondVertex = true := boolAndElimLeft hGuard'
      have hTailGuard : allAdjacentPairsAreObstructions edges ((secondVertex :: remainingPrefix) ++ suffixWalk) = true :=
        boolAndElimRight hGuard'
      have hRec : allAdjacentPairsAreObstructions edges (secondVertex :: remainingPrefix) = true :=
        guardTakePrefix edges (secondVertex :: remainingPrefix) suffixWalk hTailGuard
      show (isObstructionPair edges firstVertex secondVertex
              && allAdjacentPairsAreObstructions edges (secondVertex :: remainingPrefix)) = true
      exact boolAndIntro hPair hRec

/-! ## A3 — obstruction-pair bridges (isObstructionPair -> out-neighbour / edge-source) -/

/-- An obstruction pair `(source, target)` puts `target` in `source`'s out-neighbours.  Structural on
the edge list; the argument order flips via `natEqBoolSymm`. -/
theorem obstructionPairImpliesOutNeighbour (edges : List (Nat × Nat)) (source target : Nat) :
    isObstructionPair edges source target = true →
    natListContains (obstructionOutNeighbours edges source) target = true := by
  induction edges with
  | nil => intro hPair; exact Bool.noConfusion hPair
  | cons edgePair remainingEdges ih =>
      intro hPair
      obtain ⟨edgeSource, edgeTarget⟩ := edgePair
      have hPair' :
          ((natEqBool source edgeSource && natEqBool target edgeTarget)
            || isObstructionPair remainingEdges source target) = true := hPair
      show natListContains
          (match natEqBool edgeSource source with
            | true => edgeTarget :: obstructionOutNeighbours remainingEdges source
            | false => obstructionOutNeighbours remainingEdges source) target = true
      cases hEdgeSource : natEqBool edgeSource source with
      | true =>
          show (natEqBool edgeTarget target
                || natListContains (obstructionOutNeighbours remainingEdges source) target) = true
          cases hEdgeTarget : natEqBool edgeTarget target with
          | true => rfl
          | false =>
              have hTargetNe : natEqBool target edgeTarget = false := by
                rw [natEqBoolSymm target edgeTarget]; exact hEdgeTarget
              have hLeftFalse : (natEqBool source edgeSource && natEqBool target edgeTarget) = false := by
                rw [hTargetNe]; exact Bool.and_false _
              have hRight : isObstructionPair remainingEdges source target = true :=
                boolOrLeftFalse hPair' hLeftFalse
              exact ih hRight
      | false =>
          have hSourceNe : natEqBool source edgeSource = false := by
            rw [natEqBoolSymm source edgeSource]; exact hEdgeSource
          have hLeftFalse : (natEqBool source edgeSource && natEqBool target edgeTarget) = false := by
            rw [hSourceNe]; rfl
          have hRight : isObstructionPair remainingEdges source target = true :=
            boolOrLeftFalse hPair' hLeftFalse
          exact ih hRight

/-- An obstruction pair `(source, _)` makes `source` an edge-source.  Structural on the edge list. -/
theorem obstructionPairImpliesSource (edges : List (Nat × Nat)) (source target : Nat) :
    isObstructionPair edges source target = true →
    natListContains (obstructionSources edges) source = true := by
  induction edges with
  | nil => intro hPair; exact Bool.noConfusion hPair
  | cons edgePair remainingEdges ih =>
      intro hPair
      obtain ⟨edgeSource, edgeTarget⟩ := edgePair
      have hPair' :
          ((natEqBool source edgeSource && natEqBool target edgeTarget)
            || isObstructionPair remainingEdges source target) = true := hPair
      show (natEqBool edgeSource source || natListContains (obstructionSources remainingEdges) source) = true
      cases hEdgeSource : natEqBool edgeSource source with
      | true => rfl
      | false =>
          have hSourceNe : natEqBool source edgeSource = false := by
            rw [natEqBoolSymm source edgeSource]; exact hEdgeSource
          have hLeftFalse : (natEqBool source edgeSource && natEqBool target edgeTarget) = false := by
            rw [hSourceNe]; rfl
          have hRight : isObstructionPair remainingEdges source target = true :=
            boolOrLeftFalse hPair' hLeftFalse
          exact ih hRight

/-- If `source` is in the frontier and `target` is an out-neighbour of `source`, then `target` is in the
next frontier layer.  Structural on the frontier list. -/
theorem outNeighbourInFrontierStep (edges : List (Nat × Nat)) (source target : Nat) :
    ∀ (frontier : List Nat),
      natListContains frontier source = true →
      natListContains (obstructionOutNeighbours edges source) target = true →
      natListContains (obstructionFrontierStep edges frontier) target = true
  | [], hFront, _ => Bool.noConfusion hFront
  | frontVertex :: remainingFrontier, hFront, hOut => by
      cases hMatch : natEqBool frontVertex source with
      | true =>
          have hVeqS : frontVertex = source := natEqBoolTrueImpliesEq frontVertex source hMatch
          show natListContains
              (obstructionOutNeighbours edges frontVertex ++ obstructionFrontierStep edges remainingFrontier)
              target = true
          rw [hVeqS]
          exact natListContainsAppendLeft target (obstructionOutNeighbours edges source)
            (obstructionFrontierStep edges remainingFrontier) hOut
      | false =>
          have hRestContains : natListContains remainingFrontier source = true := by
            have hExpand : natListContains (frontVertex :: remainingFrontier) source
                = (natEqBool frontVertex source || natListContains remainingFrontier source) := rfl
            rw [hExpand, hMatch] at hFront
            exact hFront
          have hRec := outNeighbourInFrontierStep edges source target remainingFrontier hRestContains hOut
          exact natListContainsAppendRight target (obstructionOutNeighbours edges frontVertex)
            (obstructionFrontierStep edges remainingFrontier) hRec

/-! ## B — SATURATION: walk reaches its last vertex; fuel monotonicity -/

/-- The last vertex of `first :: rest`.  A total structural function (no `List.getLast` proof obligation). -/
def lastVertex : Nat → List Nat → Nat
  | first, [] => first
  | _, second :: more => lastVertex second more

/-- `lastVertex` of a snoc is the appended element.  Structural on the list. -/
theorem lastVertexSnoc : ∀ (listPrefix : List Nat) (first vertex : Nat),
    lastVertex first (listPrefix ++ [vertex]) = vertex
  | [], _, _ => rfl
  | frontVertex :: remainingList, _, vertex => by
      show lastVertex frontVertex (remainingList ++ [vertex]) = vertex
      exact lastVertexSnoc remainingList frontVertex vertex

/-- One BFS layer per fuel: more fuel keeps every earlier-reached vertex.  Structural on the fuel,
frontier generalized (the recursion uses the stepped frontier). -/
theorem reachableStepMonotone (edges : List (Nat × Nat)) (target : Nat) :
    ∀ (fuel : Nat) (frontier : List Nat),
      natListContains (obstructionReachableWithin edges fuel frontier) target = true →
      natListContains (obstructionReachableWithin edges (fuel + 1) frontier) target = true
  | 0, frontier, hReach =>
      natListContainsAppendLeft target frontier
        (obstructionReachableWithin edges 0 (obstructionFrontierStep edges frontier)) hReach
  | nextFuel + 1, frontier, hReach => by
      cases natListContainsAppendCases target frontier
          (obstructionReachableWithin edges nextFuel (obstructionFrontierStep edges frontier)) hReach with
      | inl hInFrontier =>
          exact natListContainsAppendLeft target frontier
            (obstructionReachableWithin edges (nextFuel + 1) (obstructionFrontierStep edges frontier)) hInFrontier
      | inr hInRec =>
          have hStep := reachableStepMonotone edges target nextFuel (obstructionFrontierStep edges frontier) hInRec
          exact natListContainsAppendRight target frontier
            (obstructionReachableWithin edges (nextFuel + 1) (obstructionFrontierStep edges frontier)) hStep

/-- Fuel monotonicity: `lo <= hi` transports reachability.  Structural on the `Nat.le` proof (no `Nat.sub`). -/
theorem reachableWithinMonotone (edges : List (Nat × Nat)) (frontier : List Nat) (target : Nat) :
    ∀ (lowFuel highFuel : Nat), lowFuel ≤ highFuel →
      natListContains (obstructionReachableWithin edges lowFuel frontier) target = true →
      natListContains (obstructionReachableWithin edges highFuel frontier) target = true := by
  intro lowFuel highFuel hLe
  induction hLe with
  | refl => intro hReach; exact hReach
  | step _ ih => intro hReach; exact reachableStepMonotone edges target _ frontier (ih hReach)

/-- ★ **THE WALK-REACHES-LAST CORE**: an edge-respecting walk `first :: rest` whose head is in the seed
frontier reaches its last vertex within `rest.length` frontier-expansion rounds.  Structural on the walk
tail; each edge advances exactly one BFS layer (additive fuel `rest.length`, no `Nat.sub`). -/
theorem walkReachesLast (edges : List (Nat × Nat)) :
    ∀ (rest : List Nat) (frontier : List Nat) (first : Nat),
      natListContains frontier first = true →
      allAdjacentPairsAreObstructions edges (first :: rest) = true →
      natListContains (obstructionReachableWithin edges rest.length frontier) (lastVertex first rest) = true
  | [], _, _, hFront, _ => hFront
  | secondVertex :: more, frontier, first, hFront, hGuard => by
      have hPair : isObstructionPair edges first secondVertex = true :=
        guardFirstPair edges first secondVertex more hGuard
      have hTail : allAdjacentPairsAreObstructions edges (secondVertex :: more) = true :=
        guardTailStep edges first (secondVertex :: more) hGuard
      have hSecondIn : natListContains (obstructionFrontierStep edges frontier) secondVertex = true :=
        outNeighbourInFrontierStep edges first secondVertex frontier hFront
          (obstructionPairImpliesOutNeighbour edges first secondVertex hPair)
      have hRec := walkReachesLast edges more (obstructionFrontierStep edges frontier) secondVertex hSecondIn hTail
      exact natListContainsAppendRight (lastVertex secondVertex more) frontier
        (obstructionReachableWithin edges more.length (obstructionFrontierStep edges frontier)) hRec

/-- Seeded at `source`'s out-neighbours: an edge-respecting `source :: second :: more` reaches its last
vertex within `more.length` rounds. -/
theorem edgeWalkReachesEnd (edges : List (Nat × Nat)) (source secondVertex : Nat) (more : List Nat)
    (hPair : isObstructionPair edges source secondVertex = true)
    (hTail : allAdjacentPairsAreObstructions edges (secondVertex :: more) = true) :
    natListContains (obstructionReachableWithin edges more.length (obstructionOutNeighbours edges source))
      (lastVertex secondVertex more) = true :=
  walkReachesLast edges more (obstructionOutNeighbours edges source) secondVertex
    (obstructionPairImpliesOutNeighbour edges source secondVertex hPair) hTail

/-! ## C — the checker's detection branch fires; a short simple loop drives it to `false` -/

/-- The length of a snoc is one more.  Structural on the list; `congrArg (· + 1)` on the cons step
(never `List.length_append`, which leaks `propext`). -/
theorem lengthAppendSingleton {carrier : Type} :
    ∀ (listPrefix : List carrier) (appended : carrier), (listPrefix ++ [appended]).length = listPrefix.length + 1
  | [], _ => rfl
  | _ :: remainingList, appended => congrArg (· + 1) (lengthAppendSingleton remainingList appended)

/-- ★ **THE DETECTION BRANCH FIRES**: a short simple edge-loop makes `source` reach itself within
`vertexCount` rounds.  `edgeWalkReachesEnd` (walk -> reachability, additive fuel) + `reachableWithinMonotone`
(bump to `vertexCount`).  Cases on `loopBody` to peel the first edge; the degenerate `loopBody = []` is a
self-loop caught at fuel `0`. -/
theorem loopImpliesReachesItself (edges : List (Nat × Nat)) (vertexCount : Nat) (source : Nat)
    (loopBody : List Nat)
    (hEdge : allAdjacentPairsAreObstructions edges ((source :: loopBody) ++ [source]) = true)
    (hShort : loopBody.length + 1 ≤ vertexCount) :
    obstructionSourceReachesItself edges vertexCount source = true := by
  cases loopBody with
  | nil =>
      have hPair : isObstructionPair edges source source = true :=
        guardFirstPair edges source source [] hEdge
      have hTail : allAdjacentPairsAreObstructions edges (source :: []) = true :=
        guardTailStep edges source (source :: []) hEdge
      have hReach := edgeWalkReachesEnd edges source source [] hPair hTail
      exact reachableWithinMonotone edges (obstructionOutNeighbours edges source) source 0 vertexCount
        (Nat.zero_le vertexCount) hReach
  | cons secondVertex bodyTail =>
      have hPair : isObstructionPair edges source secondVertex = true :=
        guardFirstPair edges source secondVertex (bodyTail ++ [source]) hEdge
      have hTail : allAdjacentPairsAreObstructions edges (secondVertex :: (bodyTail ++ [source])) = true :=
        guardTailStep edges source (secondVertex :: (bodyTail ++ [source])) hEdge
      have hReach := edgeWalkReachesEnd edges source secondVertex (bodyTail ++ [source]) hPair hTail
      rw [lastVertexSnoc bodyTail secondVertex source, lengthAppendSingleton bodyTail source] at hReach
      have hLe : bodyTail.length + 1 ≤ vertexCount := Nat.le_of_succ_le hShort
      exact reachableWithinMonotone edges (obstructionOutNeighbours edges source) source
        (bodyTail.length + 1) vertexCount hLe hReach

/-- The fold that lands the detection witness in `anyObstructionSourceOnCycle`.  Structural on the source
list. -/
theorem anyContainsReaches (edges : List (Nat × Nat)) (fuel source : Nat) :
    ∀ (sourceList : List Nat),
      natListContains sourceList source = true →
      obstructionSourceReachesItself edges fuel source = true →
      anyObstructionSourceOnCycle edges fuel sourceList = true
  | [], hContains, _ => Bool.noConfusion hContains
  | frontSource :: remainingSources, hContains, hReaches => by
      cases hMatch : natEqBool frontSource source with
      | true =>
          have hVeqS : frontSource = source := natEqBoolTrueImpliesEq frontSource source hMatch
          show (obstructionSourceReachesItself edges fuel frontSource
                || anyObstructionSourceOnCycle edges fuel remainingSources) = true
          rw [hVeqS, hReaches]; rfl
      | false =>
          have hRest : natListContains remainingSources source = true := by
            have hExpand : natListContains (frontSource :: remainingSources) source
                = (natEqBool frontSource source || natListContains remainingSources source) := rfl
            rw [hExpand, hMatch] at hContains
            exact hContains
          have hRec := anyContainsReaches edges fuel source remainingSources hRest hReaches
          show (obstructionSourceReachesItself edges fuel frontSource
                || anyObstructionSourceOnCycle edges fuel remainingSources) = true
          rw [hRec]; exact Bool.or_true _

/-- ★ **THE CHECKER IS DRIVEN TO `false`**: an edge-source reaching itself refutes the acyclicity verdict.
`anyContainsReaches` into `anyObstructionSourceOnCycle`, negated by `isAcyclicUfnarovskiGraph = Bool.not`. -/
theorem reachesItselfImpliesCheckerFalse (edges : List (Nat × Nat)) (fuel source : Nat)
    (hSource : natListContains (obstructionSources edges) source = true)
    (hReaches : obstructionSourceReachesItself edges fuel source = true) :
    isAcyclicUfnarovskiGraph edges fuel = false := by
  have hAny : anyObstructionSourceOnCycle edges fuel (obstructionSources edges) = true :=
    anyContainsReaches edges fuel source (obstructionSources edges) hSource hReaches
  show Bool.not (anyObstructionSourceOnCycle edges fuel (obstructionSources edges)) = false
  rw [hAny]; rfl

/-! ## D — the pigeonhole contrapositive (loop length bound) and the intermediate headline -/

/-- ★ **THE LOOP IS SHORT** (the fuel bound (iii) FOR FREE): a SIMPLE walk over the alphabet has length
`<= alphabet.length`, the CONTRApositive of the shipped `listOverCarrierRepeats` (no new pigeonhole).
`Nat.lt_or_ge` — no `by_contra` (which would pull `Classical`). -/
theorem loopIsShort (alphabet : List Nat) (source : Nat) (loopBody : List Nat)
    (hSimple : hasRepeatedVertex (source :: loopBody) = false)
    (hLetters : ∀ vertex, vertex ∈ (source :: loopBody) → natListContains alphabet vertex = true) :
    (source :: loopBody).length ≤ alphabet.length := by
  cases Nat.lt_or_ge alphabet.length (source :: loopBody).length with
  | inl hLt =>
      have hRepeat : hasRepeatedVertex (source :: loopBody) = true :=
        listOverCarrierRepeats alphabet (source :: loopBody) hLetters hLt
      rw [hSimple] at hRepeat
      exact Bool.noConfusion hRepeat
  | inr hGe => exact hGe

/-- `source` is an edge-source of any loop it heads (its first pair is an obstruction).  Cases on `loopBody`. -/
theorem loopSourceIsEdgeSource (edges : List (Nat × Nat)) (source : Nat) (loopBody : List Nat)
    (hEdge : allAdjacentPairsAreObstructions edges ((source :: loopBody) ++ [source]) = true) :
    natListContains (obstructionSources edges) source = true := by
  cases loopBody with
  | nil =>
      have hPair : isObstructionPair edges source source = true := guardFirstPair edges source source [] hEdge
      exact obstructionPairImpliesSource edges source source hPair
  | cons secondVertex bodyTail =>
      have hPair : isObstructionPair edges source secondVertex = true :=
        guardFirstPair edges source secondVertex (bodyTail ++ [source]) hEdge
      exact obstructionPairImpliesSource edges source secondVertex hPair

/-- ★★ **THE CHECKER-SOUNDNESS CORE (simple-loop form)**: any SIMPLE short edge-loop over `alphabet`
drives `isAcyclicUfnarovskiGraph edges alphabet.length` to `false`.  Composes the loop-length bound
(`loopIsShort`), the detection-branch firing (`loopImpliesReachesItself`), the edge-source witness
(`loopSourceIsEdgeSource`), and the negation (`reachesItselfImpliesCheckerFalse`).  This is residual (ii)
+ (iii) delivered for a given simple loop; the extraction (a) supplies the loop from any repeating walk. -/
theorem shortSimpleLoopImpliesCheckerFalse (edges : List (Nat × Nat)) (alphabet : List Nat)
    (source : Nat) (loopBody : List Nat)
    (hEdge : allAdjacentPairsAreObstructions edges ((source :: loopBody) ++ [source]) = true)
    (hSimple : hasRepeatedVertex (source :: loopBody) = false)
    (hLetters : ∀ vertex, vertex ∈ (source :: loopBody) → natListContains alphabet vertex = true) :
    isAcyclicUfnarovskiGraph edges alphabet.length = false := by
  have hShort : (source :: loopBody).length ≤ alphabet.length :=
    loopIsShort alphabet source loopBody hSimple hLetters
  have hReaches : obstructionSourceReachesItself edges alphabet.length source = true :=
    loopImpliesReachesItself edges alphabet.length source loopBody hEdge hShort
  have hSourceIsEdge : natListContains (obstructionSources edges) source = true :=
    loopSourceIsEdgeSource edges source loopBody hEdge
  exact reachesItselfImpliesCheckerFalse edges alphabet.length source hSourceIsEdge hReaches

/-! ## E — EXTRACTION: hand-rolled `List.append` laws, the first-repeat splitter, its correctness -/

/-- Hand-rolled `List.append_nil` (`List.append_nil` from Init leaks `propext`).  `congrArg` on the cons step. -/
theorem appendNil {carrier : Type} : ∀ (listVal : List carrier), listVal ++ [] = listVal
  | [] => rfl
  | headVal :: remainingList => congrArg (headVal :: ·) (appendNil remainingList)

/-- Hand-rolled `List.append_assoc` (`List.append_assoc` from Init leaks `propext`).  `congrArg` on the
cons step. -/
theorem appendAssoc {carrier : Type} :
    ∀ (firstList secondList thirdList : List carrier),
      (firstList ++ secondList) ++ thirdList = firstList ++ (secondList ++ thirdList)
  | [], _, _ => rfl
  | headVal :: remainingFirst, secondList, thirdList =>
      congrArg (headVal :: ·) (appendAssoc remainingFirst secondList thirdList)

/-- Membership in the right half survives `++` (`List.Mem`-constructor route).  Structural on the left list. -/
theorem memAppendRight {carrier : Type} (element : carrier) :
    ∀ (leftList rightList : List carrier), element ∈ rightList → element ∈ leftList ++ rightList
  | [], _, hMem => hMem
  | headVal :: remainingLeft, rightList, hMem =>
      List.Mem.tail headVal (memAppendRight element remainingLeft rightList hMem)

/-- A suffix of a repeat-free list is repeat-free.  Structural on the prefix. -/
theorem hasRepeatedVertexSuffix :
    ∀ (prefixList suffixList : List Nat),
      hasRepeatedVertex (prefixList ++ suffixList) = false → hasRepeatedVertex suffixList = false
  | [], _, hRepeat => hRepeat
  | _ :: remainingPrefix, suffixList, hRepeat => by
      have hRepeat' :
          (natListContains (remainingPrefix ++ suffixList) _
            || hasRepeatedVertex (remainingPrefix ++ suffixList)) = false := hRepeat
      exact hasRepeatedVertexSuffix remainingPrefix suffixList (boolOrFalseElimRight hRepeat')

/-- Appending a fresh vertex to a distinct list keeps it distinct.  Structural on the list. -/
theorem distinctAppendFresh :
    ∀ (seenList : List Nat) (freshVertex : Nat),
      hasRepeatedVertex seenList = false → natListContains seenList freshVertex = false →
      hasRepeatedVertex (seenList ++ [freshVertex]) = false
  | [], _, _, _ => rfl
  | headVertex :: remainingSeen, freshVertex, hDistinct, hFresh => by
      have hDistinct' : (natListContains remainingSeen headVertex || hasRepeatedVertex remainingSeen) = false :=
        hDistinct
      have hHeadNotInRest : natListContains remainingSeen headVertex = false := boolOrFalseElimLeft hDistinct'
      have hTailDistinct : hasRepeatedVertex remainingSeen = false := boolOrFalseElimRight hDistinct'
      have hFresh' : (natEqBool headVertex freshVertex || natListContains remainingSeen freshVertex) = false :=
        hFresh
      have hHeadNeFresh : natEqBool headVertex freshVertex = false := boolOrFalseElimLeft hFresh'
      have hFreshNotInRest : natListContains remainingSeen freshVertex = false := boolOrFalseElimRight hFresh'
      have hFreshNeHead : natEqBool freshVertex headVertex = false := by
        rw [natEqBoolSymm freshVertex headVertex]; exact hHeadNeFresh
      have hSingletonFalse : natListContains [freshVertex] headVertex = false := by
        show (natEqBool freshVertex headVertex || natListContains ([] : List Nat) headVertex) = false
        rw [hFreshNeHead]; rfl
      have hHeadNotInAppended : natListContains (remainingSeen ++ [freshVertex]) headVertex = false :=
        natListContainsAppendFalse headVertex remainingSeen [freshVertex] hHeadNotInRest hSingletonFalse
      have hTailAppendedDistinct : hasRepeatedVertex (remainingSeen ++ [freshVertex]) = false :=
        distinctAppendFresh remainingSeen freshVertex hTailDistinct hFreshNotInRest
      show (natListContains (remainingSeen ++ [freshVertex]) headVertex
            || hasRepeatedVertex (remainingSeen ++ [freshVertex])) = false
      rw [hHeadNotInAppended, hTailAppendedDistinct]; rfl

/-- Split a list at the first occurrence of `target` (full-enum `Option`; `natEqBool`, never `decide` on
`List.Mem`).  Returns the vertices before / after that first occurrence. -/
def splitAtFirst (target : Nat) : List Nat → Option (List Nat × List Nat)
  | [] => none
  | vertex :: rest =>
      match natEqBool vertex target with
      | true  => some ([], rest)
      | false =>
          match splitAtFirst target rest with
          | some (before, after) => some (vertex :: before, after)
          | none => none

/-- The split spec: `some (before, after)` means the list is `before ++ target :: after`.  Structural on
the list; the match reductions are isolated `show` + `rw [hMatch]`, the pair equalities by `injection`. -/
theorem splitAtFirstSome (target : Nat) :
    ∀ (listWalk before after : List Nat),
      splitAtFirst target listWalk = some (before, after) →
      listWalk = before ++ (target :: after)
  | [], beforeNil, afterNil, hSplit => by
      have hAbsurd : (none : Option (List Nat × List Nat)) = some (beforeNil, afterNil) := hSplit
      nomatch hAbsurd
  | vertex :: rest, before, after, hSplit => by
      cases hMatch : natEqBool vertex target with
      | true =>
          have hVeqT : vertex = target := natEqBoolTrueImpliesEq vertex target hMatch
          have hReduce : splitAtFirst target (vertex :: rest) = some ([], rest) := by
            show (match natEqBool vertex target with
                  | true => some ([], rest)
                  | false =>
                      match splitAtFirst target rest with
                      | some (beforeRec, afterRec) => some (vertex :: beforeRec, afterRec)
                      | none => none) = some ([], rest)
            rw [hMatch]
          rw [hReduce] at hSplit
          injection hSplit with hPairEq
          injection hPairEq with hBeforeEq hAfterEq
          subst hBeforeEq; subst hAfterEq
          exact congrArg (· :: rest) hVeqT
      | false =>
          have hReduce :
              splitAtFirst target (vertex :: rest)
                = match splitAtFirst target rest with
                  | some (beforeRec, afterRec) => some (vertex :: beforeRec, afterRec)
                  | none => none := by
            show (match natEqBool vertex target with
                  | true => some ([], rest)
                  | false =>
                      match splitAtFirst target rest with
                      | some (beforeRec, afterRec) => some (vertex :: beforeRec, afterRec)
                      | none => none)
                = match splitAtFirst target rest with
                  | some (beforeRec, afterRec) => some (vertex :: beforeRec, afterRec)
                  | none => none
            rw [hMatch]
          rw [hReduce] at hSplit
          cases hRec : splitAtFirst target rest with
          | none =>
              rw [hRec] at hSplit
              have hAbsurd : (none : Option (List Nat × List Nat)) = some (before, after) := hSplit
              nomatch hAbsurd
          | some pairRec =>
              obtain ⟨beforeRec, afterRec⟩ := pairRec
              rw [hRec] at hSplit
              injection hSplit with hPairEq
              injection hPairEq with hBeforeEq hAfterEq
              have hRestEq : rest = beforeRec ++ (target :: afterRec) :=
                splitAtFirstSome target rest beforeRec afterRec hRec
              subst hBeforeEq; subst hAfterEq
              show vertex :: rest = vertex :: (beforeRec ++ (target :: afterRec))
              exact congrArg (vertex :: ·) hRestEq

/-- `splitAtFirst target list = none` means `target` is not in the list.  Structural on the list. -/
theorem splitAtFirstNoneImpliesNotContains (target : Nat) :
    ∀ (listWalk : List Nat), splitAtFirst target listWalk = none → natListContains listWalk target = false
  | [], _ => rfl
  | vertex :: rest, hNone => by
      cases hMatch : natEqBool vertex target with
      | true =>
          have hReduce : splitAtFirst target (vertex :: rest) = some ([], rest) := by
            show (match natEqBool vertex target with
                  | true => some ([], rest)
                  | false =>
                      match splitAtFirst target rest with
                      | some (beforeRec, afterRec) => some (vertex :: beforeRec, afterRec)
                      | none => none) = some ([], rest)
            rw [hMatch]
          rw [hReduce] at hNone
          have hAbsurd : (some ([], rest) : Option (List Nat × List Nat)) = none := hNone
          nomatch hAbsurd
      | false =>
          have hRecNone : splitAtFirst target rest = none := by
            have hReduce :
                splitAtFirst target (vertex :: rest)
                  = match splitAtFirst target rest with
                    | some (beforeRec, afterRec) => some (vertex :: beforeRec, afterRec)
                    | none => none := by
              show (match natEqBool vertex target with
                    | true => some ([], rest)
                    | false =>
                        match splitAtFirst target rest with
                        | some (beforeRec, afterRec) => some (vertex :: beforeRec, afterRec)
                        | none => none)
                  = match splitAtFirst target rest with
                    | some (beforeRec, afterRec) => some (vertex :: beforeRec, afterRec)
                    | none => none
              rw [hMatch]
            rw [hReduce] at hNone
            cases hRec : splitAtFirst target rest with
            | none => rfl
            | some pairRec =>
                obtain ⟨beforeRec, afterRec⟩ := pairRec
                rw [hRec] at hNone
                have hAbsurd : (some (vertex :: beforeRec, afterRec) : Option (List Nat × List Nat)) = none := hNone
                nomatch hAbsurd
          have hRestFalse : natListContains rest target = false :=
            splitAtFirstNoneImpliesNotContains target rest hRecNone
          show (natEqBool vertex target || natListContains rest target) = false
          rw [hMatch, hRestFalse]; rfl

/-- The infix reshape: the original walk exposes the first-repeat loop `(vertex :: after) ++ [vertex]` as
a contiguous middle segment.  Built from `appendAssoc` (never `List.append_assoc`). -/
theorem loopInfixReshape (before after rest : List Nat) (vertex : Nat) :
    (before ++ (vertex :: after)) ++ (vertex :: rest)
      = before ++ (((vertex :: after) ++ [vertex]) ++ rest) := by
  have hInner : (vertex :: after) ++ (vertex :: rest) = ((vertex :: after) ++ [vertex]) ++ rest := by
    show vertex :: (after ++ (vertex :: rest)) = vertex :: ((after ++ [vertex]) ++ rest)
    exact congrArg (vertex :: ·) (appendAssoc after [vertex] rest).symm
  rw [appendAssoc before (vertex :: after) (vertex :: rest), hInner]

/-- ★ **THE FIRST-REPEAT SCAN**: carry the distinct `seen` prefix; stop at the first vertex already in it,
returning the loop start `vertex` and interior body (`after`).  Structural on the walk. -/
def scanForRepeat : List Nat → List Nat → Option (Nat × List Nat)
  | _, [] => none
  | seen, vertex :: rest =>
      match splitAtFirst vertex seen with
      | some (_before, after) => some (vertex, after)
      | none => scanForRepeat (seen ++ [vertex]) rest

/-- The whole-walk entry: extract the first-repeat simple loop of `walk`. -/
def extractFirstRepeatLoop (walk : List Nat) : Option (Nat × List Nat) := scanForRepeat [] walk

/-- Reduction: the scan found the repeat at `vertex`. -/
theorem scanFound (seen rest : List Nat) (vertex : Nat) (before after : List Nat)
    (hSplit : splitAtFirst vertex seen = some (before, after)) :
    scanForRepeat seen (vertex :: rest) = some (vertex, after) := by
  show (match splitAtFirst vertex seen with
        | some (ignoredBefore, foundAfter) => some (vertex, foundAfter)
        | none => scanForRepeat (seen ++ [vertex]) rest) = some (vertex, after)
  rw [hSplit]

/-- Reduction: the scan continues past a fresh `vertex`. -/
theorem scanCont (seen rest : List Nat) (vertex : Nat)
    (hSplit : splitAtFirst vertex seen = none) :
    scanForRepeat seen (vertex :: rest) = scanForRepeat (seen ++ [vertex]) rest := by
  show (match splitAtFirst vertex seen with
        | some (ignoredBefore, foundAfter) => some (vertex, foundAfter)
        | none => scanForRepeat (seen ++ [vertex]) rest) = scanForRepeat (seen ++ [vertex]) rest
  rw [hSplit]

/-! ## F — the scan is correct, and the closed-edge-walk headline -/

/-- ★★ **THE EXTRACTION IS CORRECT**: over the invariant `seen ++ walk = original` with `seen` distinct and
all letters in `alphabet`, the scan returns a SIMPLE closed sub-loop that is edge-respecting and stays over
the alphabet.  Structural on the walk.  The found case reshapes the infix (`loopInfixReshape`) and
transports the guard (`guardDropPrefix` / `guardTakePrefix`), the distinctness (`hasRepeatedVertexSuffix`),
and the letters (`memAppendRight`); the fresh case preserves the invariant and recurses. -/
theorem scanForRepeatSpec (edges : List (Nat × Nat)) (alphabet : List Nat) :
    ∀ (walk seen : List Nat),
      allAdjacentPairsAreObstructions edges (seen ++ walk) = true →
      hasRepeatedVertex seen = false →
      hasRepeatedVertex (seen ++ walk) = true →
      (∀ vertex, vertex ∈ seen → natListContains alphabet vertex = true) →
      (∀ vertex, vertex ∈ walk → natListContains alphabet vertex = true) →
      ∃ source loopBody,
        scanForRepeat seen walk = some (source, loopBody) ∧
        allAdjacentPairsAreObstructions edges ((source :: loopBody) ++ [source]) = true ∧
        hasRepeatedVertex (source :: loopBody) = false ∧
        (∀ vertex, vertex ∈ (source :: loopBody) → natListContains alphabet vertex = true)
  | [], seen, _, hSeenDistinct, hRepeat, _, _ => by
      rw [appendNil seen, hSeenDistinct] at hRepeat
      exact Bool.noConfusion hRepeat
  | vertex :: rest, seen, hGuard, hSeenDistinct, hRepeat, hSeenLetters, hWalkLetters => by
      cases hSplit : splitAtFirst vertex seen with
      | some pair =>
          obtain ⟨before, after⟩ := pair
          have hSeenEq : seen = before ++ (vertex :: after) :=
            splitAtFirstSome vertex seen before after hSplit
          refine ⟨vertex, after, scanFound seen rest vertex before after hSplit, ?_, ?_, ?_⟩
          · have hGuardReshaped :
                allAdjacentPairsAreObstructions edges (before ++ (((vertex :: after) ++ [vertex]) ++ rest)) = true := by
              rw [← loopInfixReshape before after rest vertex, ← hSeenEq]; exact hGuard
            have hAfterDrop :
                allAdjacentPairsAreObstructions edges (((vertex :: after) ++ [vertex]) ++ rest) = true :=
              guardDropPrefix edges before (((vertex :: after) ++ [vertex]) ++ rest) hGuardReshaped
            exact guardTakePrefix edges ((vertex :: after) ++ [vertex]) rest hAfterDrop
          · have hSeenRepeatFalse : hasRepeatedVertex (before ++ (vertex :: after)) = false := by
              rw [← hSeenEq]; exact hSeenDistinct
            exact hasRepeatedVertexSuffix before (vertex :: after) hSeenRepeatFalse
          · intro queryVertex hQueryMem
            have hInSeen : queryVertex ∈ seen := by
              rw [hSeenEq]; exact memAppendRight queryVertex before (vertex :: after) hQueryMem
            exact hSeenLetters queryVertex hInSeen
      | none =>
          have hNotInSeen : natListContains seen vertex = false :=
            splitAtFirstNoneImpliesNotContains vertex seen hSplit
          have hGuardReassoc : allAdjacentPairsAreObstructions edges ((seen ++ [vertex]) ++ rest) = true := by
            rw [appendAssoc seen [vertex] rest]; exact hGuard
          have hSeenDistinct' : hasRepeatedVertex (seen ++ [vertex]) = false :=
            distinctAppendFresh seen vertex hSeenDistinct hNotInSeen
          have hRepeatReassoc : hasRepeatedVertex ((seen ++ [vertex]) ++ rest) = true := by
            rw [appendAssoc seen [vertex] rest]; exact hRepeat
          have hSeenLetters' :
              ∀ queryVertex, queryVertex ∈ (seen ++ [vertex]) → natListContains alphabet queryVertex = true := by
            intro queryVertex hQueryMem
            cases memAppendCases [vertex] queryVertex seen hQueryMem with
            | inl hInSeen => exact hSeenLetters queryVertex hInSeen
            | inr hInSingleton =>
                have hEqVertex : queryVertex = vertex := by
                  cases hInSingleton with
                  | head => rfl
                  | tail _ hEmpty => cases hEmpty
                rw [hEqVertex]; exact hWalkLetters vertex (List.Mem.head rest)
          have hWalkLetters' :
              ∀ queryVertex, queryVertex ∈ rest → natListContains alphabet queryVertex = true := by
            intro queryVertex hQueryMem
            exact hWalkLetters queryVertex (List.Mem.tail vertex hQueryMem)
          have hRec := scanForRepeatSpec edges alphabet rest (seen ++ [vertex])
            hGuardReassoc hSeenDistinct' hRepeatReassoc hSeenLetters' hWalkLetters'
          obtain ⟨source, loopBody, hScanEq, hLoopGuard, hLoopSimple, hLoopLetters⟩ := hRec
          refine ⟨source, loopBody, ?_, hLoopGuard, hLoopSimple, hLoopLetters⟩
          rw [scanCont seen rest vertex hSplit]; exact hScanEq

/-- ★★ **THE CHECKER-SOUNDNESS HEADLINE**: any edge-respecting walk with a REPEATED vertex whose letters
lie in `alphabet` drives `isAcyclicUfnarovskiGraph edges alphabet.length` to `false`.  `scanForRepeatSpec`
(seeded at `seen = []`) extracts the simple loop; `shortSimpleLoopImpliesCheckerFalse` closes.  This is the
r13 combined delivery of residuals (ii) checker saturation + (iii) the longest-path loop extraction. -/
theorem closedEdgeWalkImpliesCheckerFalse (edges : List (Nat × Nat)) (alphabet : List Nat) (walk : List Nat)
    (hGuard : allAdjacentPairsAreObstructions edges walk = true)
    (hRepeat : hasRepeatedVertex walk = true)
    (hLetters : ∀ vertex, vertex ∈ walk → natListContains alphabet vertex = true) :
    isAcyclicUfnarovskiGraph edges alphabet.length = false := by
  have hSpec := scanForRepeatSpec edges alphabet walk [] hGuard rfl hRepeat
    (by intro queryVertex hQueryMem; cases hQueryMem) hLetters
  obtain ⟨source, loopBody, _hScanEq, hLoopGuard, hLoopSimple, hLoopLetters⟩ := hSpec
  exact shortSimpleLoopImpliesCheckerFalse edges alphabet source loopBody hLoopGuard hLoopSimple hLoopLetters

/-! ## G — pinned truth-probe smokes and the end-to-end witness -/

/-- Smoke: the extractor cuts the first-repeat SIMPLE loop.  `[0,1,2,0]` -> loop start `0`, body `[1,2]`;
`[0,1,2,1,3,0]` -> the first repeat is `1` (not the later `0`), body `[2]` (a genuinely simple cut).  `rfl`. -/
theorem extractFirstRepeatLoopSmoke :
    extractFirstRepeatLoop [0, 1, 2, 0] = some (0, [1, 2]) ∧
    extractFirstRepeatLoop [0, 1, 2, 1, 3, 0] = some (1, [2]) :=
  ⟨rfl, rfl⟩

/-- Smoke: the detection branch fires at `fuel = L - 1` exactly (the 5-cycle, `L = 5`).  `rfl`. -/
theorem detectionFuelBoundarySmoke :
    obstructionSourceReachesItself [(0, 1), (1, 2), (2, 3), (3, 4), (4, 0)] 4 0 = true ∧
    obstructionSourceReachesItself [(0, 1), (1, 2), (2, 3), (3, 4), (4, 0)] 3 0 = false :=
  ⟨rfl, rfl⟩

/-- Smoke: one fuel round adds exactly one BFS layer (`0` appears only at the fifth layer).  `rfl`. -/
theorem reachabilityLayerSmoke :
    obstructionReachableWithin [(0, 1), (1, 2), (2, 3), (3, 4), (4, 0)] 4 [1] = [1, 2, 3, 4, 0] :=
  rfl

/-- ★★ **THE END-TO-END WITNESS**: the directed 3-cycle's edge-respecting closed walk `[0, 1, 2, 0]`
(all letters in `[0, 1, 2]`, one repeat) drives the acyclicity checker at `fuel = 3` to `false` THROUGH
`closedEdgeWalkImpliesCheckerFalse` — not by `rfl` on the checker, but by the extraction + saturation
pipeline recognising the cycle.  The guard/repeat facts are `rfl`; the letter membership is the
`List.Mem`-constructor walk. -/
theorem threeCycleClosedWalkRefutesAcyclicity :
    isAcyclicUfnarovskiGraph [(0, 1), (1, 2), (2, 0)] ([0, 1, 2] : List Nat).length = false :=
  closedEdgeWalkImpliesCheckerFalse [(0, 1), (1, 2), (2, 0)] [0, 1, 2] [0, 1, 2, 0]
    rfl rfl
    (fun _ hMem => by
      cases hMem with
      | head => rfl
      | tail _ hRest1 =>
          cases hRest1 with
          | head => rfl
          | tail _ hRest2 =>
              cases hRest2 with
              | head => rfl
              | tail _ hRest3 =>
                  cases hRest3 with
                  | head => rfl
                  | tail _ hEmpty => cases hEmpty)

/-- ★ **The TOWER-ANICK (#2144) r13 ledger marker.**  What stands, zero-axiom, additively over r12:
residuals (ii) checker saturation + (iii) the longest-path loop extraction of
`generalGraphSoundnessResidualsAfterPigeonhole`.  (b) SATURATION: `walkReachesLast` (walk -> reachability,
additive fuel), `reachableWithinMonotone` (`Nat.le`-structural), `loopImpliesReachesItself` +
`reachesItselfImpliesCheckerFalse` driving the checker's `obstructionSourceReachesItself` branch, and
`shortSimpleLoopImpliesCheckerFalse` (a simple short edge-loop refutes acyclicity).  (a) EXTRACTION:
`splitAtFirst` + `scanForRepeat` + the correctness theorem `scanForRepeatSpec` (a first-repeat SIMPLE loop,
guard transported by `guardTakePrefix`/`guardDropPrefix`, length bounded by the CONTRAPOSITIVE of the
shipped `listOverCarrierRepeats`).  Assembled in ★★ `closedEdgeWalkImpliesCheckerFalse`: any edge-walk with
a repeated vertex over `alphabet` drives `isAcyclicUfnarovskiGraph edges alphabet.length` to `false` — the
checker-soundness core.  Witnessed end-to-end on the 3-cycle (`threeCycleClosedWalkRefutesAcyclicity`).
r13 itself does NOT ship (c) the census-zero closed form nor (d) the eventual-exactness assembly; those are
SHIPPED in the r14 file `AcyclicSystemTruncationCertificate` (`acyclicCensusZeroAboveAlphabetLength` (c) +
`acyclicSystemExactAboveAlphabetLength` (d), the monomial model at the loose `alphabet.length` bound).  No
Smith import, no Homology<->Omega edge.  Read the meaning from THIS
docstring (the honest-record convention). -/
def acyclicSoundnessLoopExtractionAndSaturationIsComplete : Bool := true

end FX1Poly.Polygraph.Homology
