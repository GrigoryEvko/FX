import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.DisjointWindowFactorization
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.AtomicSwap

/-! # DisjointWindowSwap — the realized adjacent swap at the seed (ARC-2b brick ii-b)

Brick (ii-a) produced the whisker factorization; this brick APPLIES it: two adjacent
boundary-chained seed atoms whose windows are separated by a gap genuinely TRANSPOSE — the pair
is literally an instance of the `SpineAtomSwap` constructor's redex shape, and the swap fires.
The moved atoms are described EXPLICITLY as record updates of the originals:

  * the moved second atom keeps its generator, boundaries, and right context, with its left
    context re-threaded through the first atom's SOURCE 1-cell (the window slides by the
    first generator's arity change);
  * the moved first atom keeps its generator, boundaries, and left context, with its right
    context re-threaded through the second generator's TARGET 1-cell;
  * the inert middle path is returned with its gap-length pin, so the peel's bubbling
    iteration can recompute windows after the move.

The single mismatch between the factorization's shape and the constructor's redex is one
`composePath` association, bridged by `composePath_assoc`.

The companion `adjunctionSwappedPair_isBoundaryChained` is the swap's ITERATION INVARIANT: the
swapped pair is boundary-chained at the same running boundary, so the peel's bubbling can apply
the next swap one position to the left.  Chainedness only reads LENGTHS, so the invariant is
pure `Nat` bookkeeping over the record updates — no path equations needed.

Raw Lean 4 + Init; per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-- ★ **The realized disjoint-window swap.**  Adjacent seed atoms at chained boundaries with the
second window a `windowGap` to the right of the first's produced window transpose by a genuine
`SpineAtomSwap`: the factorization (ii-a) exhibits the constructor's whisker shape (up to one
`composePath_assoc`), and the swap fires with the moved atoms given as record updates — the
second atom's left context re-threads through the first's source 1-cell, the first atom's right
context re-threads through the second's target 1-cell, everything else unchanged.  The inert
path's gap-length pin rides along for the peel's window bookkeeping. -/
theorem adjunctionSpineAtomSwap_of_disjointWindows
    {overallSource overallTarget : adjunctionGraph.Mode}
    (atomFirst atomSecond : SpineAtom adjunctionModeSignature overallSource overallTarget)
    (rest : List (SpineAtom adjunctionModeSignature overallSource overallTarget))
    (boundariesChain : atomSecond.domBoundaryLength = atomFirst.codBoundaryLength)
    (windowGap : Nat)
    (windowsDisjoint :
      atomFirst.leftContext.length + atomFirst.generatorCod.length + windowGap
        = atomSecond.leftContext.length) :
    ∃ inertPath : ModalityPath adjunctionGraph atomFirst.rightMidMode atomSecond.leftMidMode,
      inertPath.length = windowGap
        ∧ SpineAtomSwap adjunctionModeSignature
            (atomFirst :: atomSecond :: rest)
            ({ atomSecond with
                leftContext :=
                  composePath (composePath atomFirst.leftContext atomFirst.generatorDom)
                    inertPath }
              :: { atomFirst with
                    rightContext :=
                      composePath (composePath inertPath atomSecond.generatorCod)
                        atomSecond.rightContext }
              :: rest) := by
  obtain ⟨inertPath, leftFactor, rightFactor, inertLength⟩ :=
    adjunctionSpineAtom_contextsFactor_of_disjointWindows atomFirst atomSecond boundariesChain
      windowGap windowsDisjoint
  refine ⟨inertPath, inertLength, ?_⟩
  obtain ⟨leftMidA, rightMidA, leftContextA, generatorDomA, generatorCodA, generatorA,
    rightContextA⟩ := atomFirst
  obtain ⟨leftMidB, rightMidB, leftContextB, generatorDomB, generatorCodB, generatorB,
    rightContextB⟩ := atomSecond
  dsimp only at leftFactor rightFactor ⊢
  rw [leftFactor, rightFactor, ← composePath_assoc inertPath generatorDomB rightContextB]
  exact SpineAtomSwap.swap generatorA generatorB leftContextA inertPath rightContextB rest

/-- ★ **The realized mirrored (left-of) disjoint-window swap.**  Adjacent seed atoms at chained
boundaries where the SECOND atom's window lies entirely to the LEFT of the first's zone also
transpose — but here the original pair matches the `SpineAtomSwap` constructor's TARGET shape
(the constructor's source is the other temporal order, where the left-window atom fires first),
so the swap is produced with the moved pair as its source and the original pair as its target.
The peel's bubbling consumes it through symmetry at the trace-equivalence level.  The moved
atoms are again explicit record updates: the moved second atom keeps its window and left
context, its right context re-threading through the first generator's SOURCE 1-cell; the moved
first atom keeps its window and right context, its left context re-threading through the second
generator's TARGET 1-cell. -/
theorem adjunctionSpineAtomSwapLeft_of_disjointWindows
    {overallSource overallTarget : adjunctionGraph.Mode}
    (atomFirst atomSecond : SpineAtom adjunctionModeSignature overallSource overallTarget)
    (rest : List (SpineAtom adjunctionModeSignature overallSource overallTarget))
    (boundariesChain : atomSecond.domBoundaryLength = atomFirst.codBoundaryLength)
    (windowGap : Nat)
    (windowsDisjoint :
      atomSecond.leftContext.length + atomSecond.generatorDom.length + windowGap
        = atomFirst.leftContext.length) :
    ∃ inertPath : ModalityPath adjunctionModeSignature.graph
        atomSecond.rightMidMode atomFirst.leftMidMode,
      inertPath.length = windowGap
        ∧ SpineAtomSwap adjunctionModeSignature
            ({ atomSecond with
                rightContext :=
                  composePath (composePath inertPath atomFirst.generatorDom)
                    atomFirst.rightContext }
              :: { atomFirst with
                    leftContext :=
                      composePath (composePath atomSecond.leftContext atomSecond.generatorCod)
                        inertPath }
              :: rest)
            (atomFirst :: atomSecond :: rest) := by
  obtain ⟨inertPath, leftFactor, rightFactor, inertLength⟩ :=
    adjunctionSpineAtom_contextsFactorLeft_of_disjointWindows atomFirst atomSecond
      boundariesChain windowGap windowsDisjoint
  refine ⟨inertPath, inertLength, ?_⟩
  obtain ⟨leftMidA, rightMidA, leftContextA, generatorDomA, generatorCodA, generatorA,
    rightContextA⟩ := atomFirst
  obtain ⟨leftMidB, rightMidB, leftContextB, generatorDomB, generatorCodB, generatorB,
    rightContextB⟩ := atomSecond
  dsimp only at leftFactor rightFactor ⊢
  rw [leftFactor, rightFactor, ← composePath_assoc inertPath generatorCodA rightContextA]
  exact SpineAtomSwap.swap generatorB generatorA leftContextB inertPath rightContextA rest

/-! ## Chain preservation — the swap's iteration invariant -/

/-- Left-cancellation for `Nat` addition, hand-rolled (core `Nat.add_left_cancel` is
propext-tainted; `DisjointWindowFactorization`'s copy is file-private, so it is re-rolled
here). -/
private theorem natAddLeftCancel (base : Nat) :
    ∀ {leftValue rightValue : Nat},
      base + leftValue = base + rightValue → leftValue = rightValue := by
  induction base with
  | zero =>
      intro leftValue rightValue sumsEqual
      rw [Nat.zero_add, Nat.zero_add] at sumsEqual
      exact sumsEqual
  | succ basePred inductionHypothesis =>
      intro leftValue rightValue sumsEqual
      rw [Nat.succ_add, Nat.succ_add] at sumsEqual
      exact inductionHypothesis (Nat.succ.inj sumsEqual)

/-- ★ **The swapped pair stays boundary-chained.**  If `atomFirst :: atomSecond :: rest` is
boundary-chained at the running boundary and the windows are disjoint with an inert path of the
gap's length, then the transposed list produced by `adjunctionSpineAtomSwap_of_disjointWindows`
is boundary-chained at the SAME running boundary.  Chainedness reads only boundary LENGTHS, so
the proof is pure `Nat` bookkeeping: the moved second atom fires at the original running
boundary (the gap identity `windowGap + window = rightContext` re-associates the sum), the
moved first atom fires exactly at the moved second's target boundary, and the tail's boundary
is unchanged.  This is the peel's iteration invariant — after each bubble step the next swap's
chainedness premise is available. -/
theorem adjunctionSwappedPair_isBoundaryChained
    {overallSource overallTarget : adjunctionGraph.Mode}
    (atomFirst atomSecond : SpineAtom adjunctionModeSignature overallSource overallTarget)
    {rest : List (SpineAtom adjunctionModeSignature overallSource overallTarget)}
    {boundaryLength : Nat}
    (pairChained : SpineBoundaryChained boundaryLength (atomFirst :: atomSecond :: rest))
    (windowGap : Nat)
    (windowsDisjoint :
      atomFirst.leftContext.length + atomFirst.generatorCod.length + windowGap
        = atomSecond.leftContext.length)
    (inertPath : ModalityPath adjunctionModeSignature.graph
      atomFirst.rightMidMode atomSecond.leftMidMode)
    (inertHasGapLength : inertPath.length = windowGap) :
    SpineBoundaryChained boundaryLength
      ({ atomSecond with
          leftContext :=
            composePath (composePath atomFirst.leftContext atomFirst.generatorDom) inertPath }
        :: { atomFirst with
              rightContext :=
                composePath (composePath inertPath atomSecond.generatorCod)
                  atomSecond.rightContext }
        :: rest) := by
  obtain ⟨firstFires, tailChained⟩ := spineBoundaryChained_tail pairChained
  obtain ⟨secondFires, restChained⟩ := spineBoundaryChained_tail tailChained
  obtain ⟨leftMidA, rightMidA, leftContextA, generatorDomA, generatorCodA, generatorA,
    rightContextA⟩ := atomFirst
  obtain ⟨leftMidB, rightMidB, leftContextB, generatorDomB, generatorCodB, generatorB,
    rightContextB⟩ := atomSecond
  dsimp only [SpineAtom.domBoundaryLength, SpineAtom.codBoundaryLength] at firstFires secondFires
  dsimp only [SpineAtom.codBoundaryLength] at restChained
  dsimp only at windowsDisjoint inertHasGapLength ⊢
  rw [← windowsDisjoint] at secondFires
  rw [Nat.add_assoc (leftContextA.length + generatorCodA.length + windowGap)
        generatorDomB.length rightContextB.length,
      Nat.add_assoc (leftContextA.length + generatorCodA.length) windowGap
        (generatorDomB.length + rightContextB.length)] at secondFires
  have gapPlusWindow := natAddLeftCancel _ secondFires
  refine SpineBoundaryChained.cons _ ?_ (SpineBoundaryChained.cons _ ?_ ?_)
  · dsimp only [SpineAtom.domBoundaryLength]
    rw [ModalityPath.length_composePath, ModalityPath.length_composePath, inertHasGapLength,
        Nat.add_assoc (leftContextA.length + generatorDomA.length + windowGap)
          generatorDomB.length rightContextB.length,
        Nat.add_assoc (leftContextA.length + generatorDomA.length) windowGap
          (generatorDomB.length + rightContextB.length),
        gapPlusWindow]
    exact firstFires
  · dsimp only [SpineAtom.domBoundaryLength, SpineAtom.codBoundaryLength]
    rw [ModalityPath.length_composePath, ModalityPath.length_composePath,
        ModalityPath.length_composePath, ModalityPath.length_composePath, inertHasGapLength,
        Nat.add_assoc windowGap generatorCodB.length rightContextB.length,
        Nat.add_assoc (leftContextA.length + generatorDomA.length + windowGap)
          generatorCodB.length rightContextB.length,
        Nat.add_assoc (leftContextA.length + generatorDomA.length) windowGap
          (generatorCodB.length + rightContextB.length)]
  · dsimp only [SpineAtom.codBoundaryLength]
    have boundariesMatch :
        leftContextA.length + generatorCodA.length
            + (composePath (composePath inertPath generatorCodB) rightContextB).length
          = leftContextB.length + generatorCodB.length + rightContextB.length := by
      rw [ModalityPath.length_composePath, ModalityPath.length_composePath, inertHasGapLength,
          ← windowsDisjoint,
          Nat.add_assoc windowGap generatorCodB.length rightContextB.length,
          Nat.add_assoc (leftContextA.length + generatorCodA.length + windowGap)
            generatorCodB.length rightContextB.length,
          Nat.add_assoc (leftContextA.length + generatorCodA.length) windowGap
            (generatorCodB.length + rightContextB.length)]
    rw [boundariesMatch]
    exact restChained

/-- ★ **The mirrored swapped pair stays boundary-chained.**  The left-of analogue of
`adjunctionSwappedPair_isBoundaryChained`: if `atomFirst :: atomSecond :: rest` is
boundary-chained and the second window lies a gap LEFT of the first's zone with an inert path
of the gap's length, then the mirrored swap's SOURCE list (the moved pair, where the
left-window atom fires first) is boundary-chained at the SAME running boundary.  Again pure
`Nat` bookkeeping — chainedness reads only lengths, and here the gap identity is
`rightContextB = windowGap + window`. -/
theorem adjunctionSwappedPairLeft_isBoundaryChained
    {overallSource overallTarget : adjunctionGraph.Mode}
    (atomFirst atomSecond : SpineAtom adjunctionModeSignature overallSource overallTarget)
    {rest : List (SpineAtom adjunctionModeSignature overallSource overallTarget)}
    {boundaryLength : Nat}
    (pairChained : SpineBoundaryChained boundaryLength (atomFirst :: atomSecond :: rest))
    (windowGap : Nat)
    (windowsDisjoint :
      atomSecond.leftContext.length + atomSecond.generatorDom.length + windowGap
        = atomFirst.leftContext.length)
    (inertPath : ModalityPath adjunctionModeSignature.graph
      atomSecond.rightMidMode atomFirst.leftMidMode)
    (inertHasGapLength : inertPath.length = windowGap) :
    SpineBoundaryChained boundaryLength
      ({ atomSecond with
          rightContext :=
            composePath (composePath inertPath atomFirst.generatorDom)
              atomFirst.rightContext }
        :: { atomFirst with
              leftContext :=
                composePath (composePath atomSecond.leftContext atomSecond.generatorCod)
                  inertPath }
        :: rest) := by
  obtain ⟨firstFires, tailChained⟩ := spineBoundaryChained_tail pairChained
  obtain ⟨secondFires, restChained⟩ := spineBoundaryChained_tail tailChained
  obtain ⟨leftMidA, rightMidA, leftContextA, generatorDomA, generatorCodA, generatorA,
    rightContextA⟩ := atomFirst
  obtain ⟨leftMidB, rightMidB, leftContextB, generatorDomB, generatorCodB, generatorB,
    rightContextB⟩ := atomSecond
  dsimp only [SpineAtom.domBoundaryLength, SpineAtom.codBoundaryLength] at firstFires secondFires
  dsimp only [SpineAtom.codBoundaryLength] at restChained
  dsimp only at windowsDisjoint inertHasGapLength ⊢
  rw [← windowsDisjoint] at secondFires
  rw [Nat.add_assoc (leftContextB.length + generatorDomB.length + windowGap)
        generatorCodA.length rightContextA.length,
      Nat.add_assoc (leftContextB.length + generatorDomB.length) windowGap
        (generatorCodA.length + rightContextA.length)] at secondFires
  have windowPlusGap := natAddLeftCancel _ secondFires
  rw [← windowsDisjoint] at firstFires
  rw [Nat.add_assoc (leftContextB.length + generatorDomB.length + windowGap)
        generatorDomA.length rightContextA.length,
      Nat.add_assoc (leftContextB.length + generatorDomB.length) windowGap
        (generatorDomA.length + rightContextA.length)] at firstFires
  refine SpineBoundaryChained.cons _ ?_ (SpineBoundaryChained.cons _ ?_ ?_)
  · dsimp only [SpineAtom.domBoundaryLength]
    rw [ModalityPath.length_composePath, ModalityPath.length_composePath, inertHasGapLength,
        Nat.add_assoc windowGap generatorDomA.length rightContextA.length]
    exact firstFires
  · dsimp only [SpineAtom.domBoundaryLength, SpineAtom.codBoundaryLength]
    rw [ModalityPath.length_composePath, ModalityPath.length_composePath,
        ModalityPath.length_composePath, ModalityPath.length_composePath, inertHasGapLength,
        Nat.add_assoc windowGap generatorDomA.length rightContextA.length,
        Nat.add_assoc (leftContextB.length + generatorCodB.length + windowGap)
          generatorDomA.length rightContextA.length,
        Nat.add_assoc (leftContextB.length + generatorCodB.length) windowGap
          (generatorDomA.length + rightContextA.length)]
  · dsimp only [SpineAtom.codBoundaryLength]
    have boundariesMatch :
        (composePath (composePath leftContextB generatorCodB) inertPath).length
            + generatorCodA.length + rightContextA.length
          = leftContextB.length + generatorCodB.length + rightContextB.length := by
      rw [ModalityPath.length_composePath, ModalityPath.length_composePath, inertHasGapLength,
          windowPlusGap,
          Nat.add_assoc (leftContextB.length + generatorCodB.length + windowGap)
            generatorCodA.length rightContextA.length,
          Nat.add_assoc (leftContextB.length + generatorCodB.length) windowGap
            (generatorCodA.length + rightContextA.length)]
    rw [boundariesMatch]
    exact restChained

/-! ## Honesty markers -/

/-- **Honesty marker — the realized disjoint-window swap is SHIPPED (ARC-2b brick ii-b).**
`adjunctionSpineAtomSwap_of_disjointWindows` fires a genuine `SpineAtomSwap` on any adjacent
boundary-chained seed pair with a right-of window gap, with the moved atoms explicit (record
updates) and the inert gap pin returned for window bookkeeping.  NOT yet shipped: the mirrored
LEFT-of direction (the peel may bubble past atoms on either side) and the cup/cap peel itself
(iii) — the sole residual of the seed reconstruction.  `= true`. -/
def fxMode_hasRealizedDisjointWindowSwap : Bool := true

/-- **Honesty marker — the swap's chain preservation is SHIPPED (ARC-2b brick ii-c-1).**
`adjunctionSwappedPair_isBoundaryChained` threads the transposed pair back into
`SpineBoundaryChained` at the same running boundary, so the peel's bubbling iterates: each
swap step re-establishes the chainedness premise the NEXT swap needs.  Pure length
bookkeeping — no path equations consumed.  `= true`. -/
def fxMode_hasSwapChainPreservation : Bool := true

/-- **Honesty marker — the mirrored disjoint-window swap is SHIPPED (ARC-2b brick ii-c-2b).**
`adjunctionSpineAtomSwapLeft_of_disjointWindows` covers the left-of direction: the original
pair matches the constructor's TARGET, so the realized swap runs moved-pair → original-pair
and the peel consumes it through trace-equivalence symmetry.  `= true`. -/
def fxMode_hasMirroredWindowSwap : Bool := true

/-- **Honesty marker — the mirrored swap's chain preservation is SHIPPED (ARC-2b brick
ii-c-2c).**  `adjunctionSwappedPairLeft_isBoundaryChained` threads the mirrored moved pair
back into `SpineBoundaryChained` at the same running boundary.  With both directions'
realized swaps and both chain preservations in hand, the ONLY residual of the seed
reconstruction is the cup/cap peel (iii): read the head's partner off the arc structure,
prove the intervening windows disjoint, bubble it front, pin by atom rigidity.  `= true`. -/
def fxMode_hasMirroredSwapChainPreservation : Bool := true

end FX1Poly.Polygraph
