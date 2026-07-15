import FX1Poly.Polygraph.Omega.LafontProp.MatrixNormalForm

/-! # Polygraph/Omega/LafontProp/ConvertibilitySoundness — the congruence-closure soundness lift
(LAFONT-PROP r2, brick B: RESIDUAL 1 DISCHARGED)

The r1 presentation shipped per-ROW matrix soundness (18 kernel-rfl fires) and NAMED the
congruence-closure lift as `convertibilityMatrixSoundnessStatement` (owner false).  This file
PROVES it: every pair of diagrams convertible in the presented congruence
`AreConvertibleDiagrams` denotes EQUAL matrices on the full rectangle
(`convertibleDiagramsDenoteEqualMatrices`, packaged as `convertibilityMatrixSoundnessHolds`).

The proof is a single induction over the 28 constructors of the congruence:

* the 18 relation-row constructors close by the shipped per-row soundness fires;
* reflexivity / symmetry / transitivity lift pointwise through the Bool bridge;
* congruence under sequential composition is `sumBelow` congruence;
* congruence under parallel tensor is the four-block case analysis on the direct sum;
* the identity laws are single-support sum collapses against the identity matrix;
* reassociation of sequential composition is the sum-exchange (Fubini) argument with both
  distributivities and multiplication associativity — all built here from scratch;
* identity-tensor fusion is the block-diagonal identity computation
  (`Nat.beq` left-addition cancellation);
* the middle-four interchange is the block-split of the composition sum
  (`sumBelowSplitsAtBlock`) with the off-diagonal blocks annihilating.

COROLLARY (`notConvertibleOfDistinctMatrices`): diagrams with DIFFERENT matrices are NOT
convertible — the negative half of the word-problem decision procedure.  Together with
`completenessReducesToCanonicalReduction` (brick A) the full decision reduces to the single
named residual `canonicalReductionStatement`.

Raw Lean 4 + Init only; zero-axiom; structural recursion only; audit twin with per-decl
`#assert_no_axioms` plus an independent `#print axioms` witness. -/

namespace FX1Poly.Polygraph.Omega.LafontProp

/-! ## Nat kit extensions (own proofs; distributivity built from scratch) -/

/-- Ordered pairs are never reverse-ordered (`bigNat ≤ smallNat` refutes `smallNat < bigNat`). -/
theorem noLtOfGe {smallNat bigNat : Nat} (isAtMost : bigNat ≤ smallNat)
    (isBelow : smallNat < bigNat) : False :=
  Nat.lt_irrefl smallNat (Nat.le_trans isBelow isAtMost)

/-- A false `Nat.ble` test reverses the order strictly. -/
theorem bleFalseGivesReverseLt : {smallNat bigNat : Nat} -> Nat.ble smallNat bigNat = false ->
    bigNat < smallNat
  | 0, _, testFails => Bool.noConfusion testFails
  | smallPred + 1, 0, _ => Nat.succ_le_succ (Nat.zero_le smallPred)
  | smallPred + 1, bigPred + 1, testFails =>
      Nat.succ_le_succ
        (bleFalseGivesReverseLt (smallNat := smallPred) (bigNat := bigPred) testFails)

/-- A false `Nat.blt` test yields the reverse (non-strict) order. -/
theorem leOfBltIsFalse {leftNat rightNat : Nat} (testFails : Nat.blt leftNat rightNat = false) :
    rightNat ≤ leftNat :=
  Nat.le_of_succ_le_succ (bleFalseGivesReverseLt testFails)

/-- Left-addition cancels in subtraction under an order premise:
`blockSize + (indexNat - blockSize) = indexNat`. -/
theorem leGivesAddSubCancel : {blockSize indexNat : Nat} -> blockSize ≤ indexNat ->
    blockSize + (indexNat - blockSize) = indexNat
  | 0, indexNat, _ => Nat.zero_add indexNat
  | blockPred + 1, 0, isAtMost => absurd isAtMost (Nat.not_succ_le_zero blockPred)
  | blockPred + 1, indexPred + 1, isAtMost =>
      (congrArg (fun innerNat => (blockPred + 1) + innerNat)
          (succSubSucc blockPred indexPred)).trans
        ((Nat.succ_add blockPred (indexPred - blockPred)).trans
          (congrArg Nat.succ
            (leGivesAddSubCancel (blockSize := blockPred) (indexNat := indexPred)
              (Nat.le_of_succ_le_succ isAtMost))))

/-- Every index is either inside the block or a block-offset. -/
theorem decomposeIndexAgainstBlock (blockSize indexNat : Nat) :
    indexNat < blockSize ∨ ∃ offsetNat, indexNat = blockSize + offsetNat :=
  match bltObserved : Nat.blt indexNat blockSize with
  | true => Or.inl (ltOfBltIsTrue bltObserved)
  | false =>
      Or.inr ⟨indexNat - blockSize, (leGivesAddSubCancel (leOfBltIsFalse bltObserved)).symm⟩

/-- Left-addition cancels in `≤`. -/
theorem leOfAddLeAddLeft (base : Nat) : ∀ {firstNat secondNat : Nat},
    base + firstNat ≤ base + secondNat -> firstNat ≤ secondNat := by
  induction base with
  | zero =>
      intro firstNat secondNat isAtMost
      rw [Nat.zero_add, Nat.zero_add] at isAtMost
      exact isAtMost
  | succ basePred inductiveHypothesis =>
      intro firstNat secondNat isAtMost
      rw [Nat.succ_add, Nat.succ_add] at isAtMost
      exact inductiveHypothesis (Nat.le_of_succ_le_succ isAtMost)

/-- Left-addition cancels in `<`. -/
theorem ltOfAddLtAddLeft (base : Nat) {firstNat secondNat : Nat}
    (isBelow : base + firstNat < base + secondNat) : firstNat < secondNat :=
  leOfAddLeAddLeft base (firstNat := firstNat + 1) (secondNat := secondNat) isBelow

/-- `Nat.beq` cancels a common left addend. -/
theorem beqAddLeftCancel : (base leftNat rightNat : Nat) ->
    Nat.beq (base + leftNat) (base + rightNat) = Nat.beq leftNat rightNat
  | 0, leftNat, rightNat => by rw [Nat.zero_add, Nat.zero_add]
  | basePred + 1, leftNat, rightNat => by
      rw [Nat.succ_add basePred leftNat, Nat.succ_add basePred rightNat]
      exact beqAddLeftCancel basePred leftNat rightNat

/-- Left distributivity, built from scratch (the core right-distributivity kit is
propext-risky). -/
theorem mulAddDistribLeft (leftFactor : Nat) :
    ∀ (firstAddend secondAddend : Nat),
      leftFactor * (firstAddend + secondAddend)
        = leftFactor * firstAddend + leftFactor * secondAddend := by
  intro firstAddend secondAddend
  induction secondAddend with
  | zero => rfl
  | succ secondPred inductiveHypothesis =>
      show leftFactor * (firstAddend + secondPred) + leftFactor
        = leftFactor * firstAddend + (leftFactor * secondPred + leftFactor)
      rw [inductiveHypothesis]
      exact Nat.add_assoc (leftFactor * firstAddend) (leftFactor * secondPred) leftFactor

/-- Four-summand exchange: `(w + x) + (y + z) = (w + y) + (x + z)`. -/
theorem addFourExchange (firstNat secondNat thirdNat fourthNat : Nat) :
    (firstNat + secondNat) + (thirdNat + fourthNat)
      = (firstNat + thirdNat) + (secondNat + fourthNat) := by
  rw [(Nat.add_assoc (firstNat + secondNat) thirdNat fourthNat).symm,
    Nat.add_assoc firstNat secondNat thirdNat,
    Nat.add_comm secondNat thirdNat,
    (Nat.add_assoc firstNat thirdNat secondNat).symm,
    Nat.add_assoc (firstNat + thirdNat) secondNat fourthNat]

/-- Right distributivity, built from scratch. -/
theorem addMulDistribRight (firstAddend secondAddend : Nat) :
    ∀ (rightFactor : Nat),
      (firstAddend + secondAddend) * rightFactor
        = firstAddend * rightFactor + secondAddend * rightFactor := by
  intro rightFactor
  induction rightFactor with
  | zero => rfl
  | succ factorPred inductiveHypothesis =>
      show (firstAddend + secondAddend) * factorPred + (firstAddend + secondAddend)
        = (firstAddend * factorPred + firstAddend)
          + (secondAddend * factorPred + secondAddend)
      rw [inductiveHypothesis]
      exact addFourExchange (firstAddend * factorPred) (secondAddend * factorPred)
        firstAddend secondAddend

/-- Multiplication associativity, built from scratch on top of the own distributivity. -/
theorem mulAssoc (firstFactor secondFactor : Nat) :
    ∀ (thirdFactor : Nat),
      (firstFactor * secondFactor) * thirdFactor
        = firstFactor * (secondFactor * thirdFactor) := by
  intro thirdFactor
  induction thirdFactor with
  | zero => rfl
  | succ thirdPred inductiveHypothesis =>
      show (firstFactor * secondFactor) * thirdPred + firstFactor * secondFactor
        = firstFactor * (secondFactor * thirdPred + secondFactor)
      rw [inductiveHypothesis, mulAddDistribLeft firstFactor]

/-! ## Structural-sum kit extensions -/

/-- Pointwise-equal terms give equal sums. -/
theorem sumBelowRespectsPointwise (firstTermAt secondTermAt : Nat -> Nat) :
    (bound : Nat) ->
    (∀ termIndex, termIndex < bound -> firstTermAt termIndex = secondTermAt termIndex) ->
    sumBelow firstTermAt bound = sumBelow secondTermAt bound
  | 0, _ => rfl
  | boundPred + 1, agreeBelow => by
      have tailAgrees := sumBelowRespectsPointwise firstTermAt secondTermAt boundPred
        (fun termIndex isBelow => agreeBelow termIndex (Nat.le.step isBelow))
      show sumBelow firstTermAt boundPred + firstTermAt boundPred
        = sumBelow secondTermAt boundPred + secondTermAt boundPred
      rw [tailAgrees, agreeBelow boundPred (Nat.lt_succ_self boundPred)]

/-- A sum over a block-plus-tail bound splits into the block sum and the offset tail sum. -/
theorem sumBelowSplitsAtBlock (termAt : Nat -> Nat) (blockSize : Nat) :
    (tailSize : Nat) ->
    sumBelow termAt (blockSize + tailSize)
      = sumBelow termAt blockSize
        + sumBelow (fun offsetIndex => termAt (blockSize + offsetIndex)) tailSize
  | 0 => rfl
  | tailPred + 1 => by
      show sumBelow termAt (blockSize + tailPred) + termAt (blockSize + tailPred)
        = sumBelow termAt blockSize
          + (sumBelow (fun offsetIndex => termAt (blockSize + offsetIndex)) tailPred
            + termAt (blockSize + tailPred))
      rw [sumBelowSplitsAtBlock termAt blockSize tailPred]
      exact Nat.add_assoc (sumBelow termAt blockSize)
        (sumBelow (fun offsetIndex => termAt (blockSize + offsetIndex)) tailPred)
        (termAt (blockSize + tailPred))

/-- Sums distribute over pointwise addition of the terms. -/
theorem sumBelowOfPointwiseAdd (firstTermAt secondTermAt : Nat -> Nat) :
    (bound : Nat) ->
    sumBelow (fun termIndex => firstTermAt termIndex + secondTermAt termIndex) bound
      = sumBelow firstTermAt bound + sumBelow secondTermAt bound
  | 0 => rfl
  | boundPred + 1 => by
      show sumBelow (fun termIndex => firstTermAt termIndex + secondTermAt termIndex) boundPred
          + (firstTermAt boundPred + secondTermAt boundPred)
        = (sumBelow firstTermAt boundPred + firstTermAt boundPred)
          + (sumBelow secondTermAt boundPred + secondTermAt boundPred)
      rw [sumBelowOfPointwiseAdd firstTermAt secondTermAt boundPred]
      exact addFourExchange (sumBelow firstTermAt boundPred) (sumBelow secondTermAt boundPred)
        (firstTermAt boundPred) (secondTermAt boundPred)

/-- A constant left factor distributes into the sum. -/
theorem sumBelowMulLeft (leftFactor : Nat) (termAt : Nat -> Nat) :
    (bound : Nat) ->
    leftFactor * sumBelow termAt bound
      = sumBelow (fun termIndex => leftFactor * termAt termIndex) bound
  | 0 => rfl
  | boundPred + 1 => by
      show leftFactor * (sumBelow termAt boundPred + termAt boundPred)
        = sumBelow (fun termIndex => leftFactor * termAt termIndex) boundPred
          + leftFactor * termAt boundPred
      rw [mulAddDistribLeft leftFactor (sumBelow termAt boundPred) (termAt boundPred),
        sumBelowMulLeft leftFactor termAt boundPred]

/-- A constant right factor distributes into the sum. -/
theorem sumBelowMulRight (termAt : Nat -> Nat) (rightFactor : Nat) :
    (bound : Nat) ->
    sumBelow termAt bound * rightFactor
      = sumBelow (fun termIndex => termAt termIndex * rightFactor) bound
  | 0 => zeroMulIsZero rightFactor
  | boundPred + 1 => by
      show (sumBelow termAt boundPred + termAt boundPred) * rightFactor
        = sumBelow (fun termIndex => termAt termIndex * rightFactor) boundPred
          + termAt boundPred * rightFactor
      rw [addMulDistribRight (sumBelow termAt boundPred) (termAt boundPred) rightFactor,
        sumBelowMulRight termAt rightFactor boundPred]

/-- Sum exchange (finite Fubini): the double sum is order-independent. -/
theorem sumBelowExchange (pairTermAt : Nat -> Nat -> Nat) (innerBound : Nat) :
    (outerBound : Nat) ->
    sumBelow (fun outerIndex =>
        sumBelow (fun innerIndex => pairTermAt outerIndex innerIndex) innerBound) outerBound
      = sumBelow (fun innerIndex =>
          sumBelow (fun outerIndex => pairTermAt outerIndex innerIndex) outerBound) innerBound
  | 0 => (sumBelowOfAllZeroIsZero _ innerBound (fun _ _ => rfl)).symm
  | outerPred + 1 => by
      show sumBelow (fun outerIndex =>
            sumBelow (fun innerIndex => pairTermAt outerIndex innerIndex) innerBound) outerPred
          + sumBelow (fun innerIndex => pairTermAt outerPred innerIndex) innerBound
        = sumBelow (fun innerIndex =>
            sumBelow (fun outerIndex => pairTermAt outerIndex innerIndex) (outerPred + 1))
            innerBound
      rw [sumBelowExchange pairTermAt innerBound outerPred,
        (sumBelowOfPointwiseAdd
          (fun innerIndex => sumBelow (fun outerIndex => pairTermAt outerIndex innerIndex)
            outerPred)
          (fun innerIndex => pairTermAt outerPred innerIndex) innerBound).symm]
      rfl

/-! ## THE CONGRUENCE SOUNDNESS THEOREM -/

/-- CONVERTIBLE DIAGRAMS DENOTE EQUAL MATRICES: the congruence-closure lift of the 18 per-row
soundness fires, by induction over the presented congruence. -/
theorem convertibleDiagramsDenoteEqualMatrices {sourceArity targetArity : Nat}
    {leftDiagram rightDiagram : WireDiagram sourceArity targetArity}
    (areConvertible : AreConvertibleDiagrams leftDiagram rightDiagram) :
    doEntriesAgreeUpTo targetArity sourceArity
      (denoteEntries leftDiagram) (denoteEntries rightDiagram) = true := by
  induction areConvertible with
  | fromReflexivity diagram =>
      exact agreeUpToOfPointwise _ _ _ _ (fun _ _ _ _ => rfl)
  | fromSymmetry _ flippedAgree =>
      exact agreeUpToOfPointwise _ _ _ _
        (fun rowIndex colIndex isRowInRange isColInRange =>
          (pointwiseOfAgreeUpTo _ _ _ _ flippedAgree rowIndex colIndex isRowInRange
            isColInRange).symm)
  | fromTransitivity _ _ leftAgree rightAgree =>
      exact agreeUpToOfPointwise _ _ _ _
        (fun rowIndex colIndex isRowInRange isColInRange =>
          (pointwiseOfAgreeUpTo _ _ _ _ leftAgree rowIndex colIndex isRowInRange
            isColInRange).trans
            (pointwiseOfAgreeUpTo _ _ _ _ rightAgree rowIndex colIndex isRowInRange
              isColInRange))
  | @underComposeSequential innerSourceArity middleArity innerTargetArity
      firstLeft firstRight secondLeft secondRight _ _ firstAgree secondAgree =>
      exact agreeUpToOfPointwise _ _ _ _
        (fun rowIndex colIndex isRowInRange isColInRange =>
          sumBelowRespectsPointwise
            (fun midIndex => denoteEntries secondLeft rowIndex midIndex
              * denoteEntries firstLeft midIndex colIndex)
            (fun midIndex => denoteEntries secondRight rowIndex midIndex
              * denoteEntries firstRight midIndex colIndex)
            middleArity
            (fun midIndex isMidInRange => by
              show denoteEntries secondLeft rowIndex midIndex
                  * denoteEntries firstLeft midIndex colIndex
                = denoteEntries secondRight rowIndex midIndex
                  * denoteEntries firstRight midIndex colIndex
              rw [pointwiseOfAgreeUpTo _ _ _ _ secondAgree rowIndex midIndex isRowInRange
                  isMidInRange,
                pointwiseOfAgreeUpTo _ _ _ _ firstAgree midIndex colIndex isMidInRange
                  isColInRange]))
  | @underTensorParallel topSourceArity topTargetArity bottomSourceArity bottomTargetArity
      topLeft topRight bottomLeft bottomRight _ _ topAgree bottomAgree =>
      refine agreeUpToOfPointwise _ _ _ _
        (fun rowIndex colIndex isRowInRange isColInRange => ?_)
      show directSumEntries topTargetArity topSourceArity
          (denoteEntries topLeft) (denoteEntries bottomLeft) rowIndex colIndex
        = directSumEntries topTargetArity topSourceArity
            (denoteEntries topRight) (denoteEntries bottomRight) rowIndex colIndex
      cases decomposeIndexAgainstBlock topTargetArity rowIndex with
      | inl isRowInTop =>
          cases decomposeIndexAgainstBlock topSourceArity colIndex with
          | inl isColInTop =>
              rw [directSumEntryInTopBlock _ _ isRowInTop isColInTop,
                directSumEntryInTopBlock _ _ isRowInTop isColInTop]
              exact pointwiseOfAgreeUpTo _ _ _ _ topAgree rowIndex colIndex isRowInTop
                isColInTop
          | inr colHasOffset =>
              cases colHasOffset with
              | intro colOffset colSplits =>
                  rw [colSplits, directSumEntryInTopRightBlock _ _ colOffset isRowInTop,
                    directSumEntryInTopRightBlock _ _ colOffset isRowInTop]
      | inr rowHasOffset =>
          cases rowHasOffset with
          | intro rowOffset rowSplits =>
              cases decomposeIndexAgainstBlock topSourceArity colIndex with
              | inl isColInTop =>
                  rw [rowSplits, directSumEntryInBottomLeftBlock _ _ rowOffset isColInTop,
                    directSumEntryInBottomLeftBlock _ _ rowOffset isColInTop]
              | inr colHasOffset =>
                  cases colHasOffset with
                  | intro colOffset colSplits =>
                      rw [rowSplits] at isRowInRange
                      rw [colSplits] at isColInRange
                      rw [rowSplits, colSplits,
                        directSumEntryInBottomBlock _ _ rowOffset colOffset,
                        directSumEntryInBottomBlock _ _ rowOffset colOffset]
                      exact pointwiseOfAgreeUpTo _ _ _ _ bottomAgree rowOffset colOffset
                        (ltOfAddLtAddLeft topTargetArity isRowInRange)
                        (ltOfAddLtAddLeft topSourceArity isColInRange)
  | @composeIdentitySource innerSourceArity innerTargetArity diagram =>
      refine agreeUpToOfPointwise _ _ _ _
        (fun rowIndex colIndex isRowInRange isColInRange => ?_)
      refine (sumBelowOfSingleSupport _ innerSourceArity colIndex isColInRange ?_).trans ?_
      · intro midIndex _ isMidOffSupport
        show denoteEntries diagram rowIndex midIndex * identityEntries midIndex colIndex = 0
        rw [identityEntryOffDiagonal isMidOffSupport]
        rfl
      · show denoteEntries diagram rowIndex colIndex * identityEntries colIndex colIndex
          = denoteEntries diagram rowIndex colIndex
        rw [identityEntryOnDiagonal colIndex]
        exact mulOneIsSelf (denoteEntries diagram rowIndex colIndex)
  | @composeIdentityTarget innerSourceArity innerTargetArity diagram =>
      refine agreeUpToOfPointwise _ _ _ _
        (fun rowIndex colIndex isRowInRange isColInRange => ?_)
      refine (sumBelowOfSingleSupport _ innerTargetArity rowIndex isRowInRange ?_).trans ?_
      · intro midIndex _ isMidOffSupport
        show identityEntries rowIndex midIndex * denoteEntries diagram midIndex colIndex = 0
        rw [identityEntryOffDiagonal (fun isRowAtMid => isMidOffSupport isRowAtMid.symm)]
        exact zeroMulIsZero (denoteEntries diagram midIndex colIndex)
      · show identityEntries rowIndex rowIndex * denoteEntries diagram rowIndex colIndex
          = denoteEntries diagram rowIndex colIndex
        rw [identityEntryOnDiagonal rowIndex]
        exact oneMulIsSelf (denoteEntries diagram rowIndex colIndex)
  | @composeReassociate innerSourceArity secondArity thirdArity innerTargetArity
      firstStage secondStage thirdStage =>
      refine agreeUpToOfPointwise _ _ _ _
        (fun rowIndex colIndex isRowInRange isColInRange => ?_)
      show sumBelow (fun thirdIndex => denoteEntries thirdStage rowIndex thirdIndex
          * sumBelow (fun secondIndex => denoteEntries secondStage thirdIndex secondIndex
              * denoteEntries firstStage secondIndex colIndex) secondArity) thirdArity
        = sumBelow (fun secondIndex =>
            sumBelow (fun thirdIndex => denoteEntries thirdStage rowIndex thirdIndex
              * denoteEntries secondStage thirdIndex secondIndex) thirdArity
            * denoteEntries firstStage secondIndex colIndex) secondArity
      rw [sumBelowRespectsPointwise _
          (fun thirdIndex => sumBelow (fun secondIndex =>
            denoteEntries thirdStage rowIndex thirdIndex
              * (denoteEntries secondStage thirdIndex secondIndex
                * denoteEntries firstStage secondIndex colIndex)) secondArity) thirdArity
          (fun thirdIndex _ => sumBelowMulLeft (denoteEntries thirdStage rowIndex thirdIndex)
            (fun secondIndex => denoteEntries secondStage thirdIndex secondIndex
              * denoteEntries firstStage secondIndex colIndex) secondArity),
        sumBelowExchange (fun thirdIndex secondIndex =>
          denoteEntries thirdStage rowIndex thirdIndex
            * (denoteEntries secondStage thirdIndex secondIndex
              * denoteEntries firstStage secondIndex colIndex)) secondArity thirdArity]
      exact sumBelowRespectsPointwise _ _ secondArity
        (fun secondIndex _ => by
          rw [sumBelowMulRight (fun thirdIndex =>
              denoteEntries thirdStage rowIndex thirdIndex
                * denoteEntries secondStage thirdIndex secondIndex)
            (denoteEntries firstStage secondIndex colIndex) thirdArity]
          exact sumBelowRespectsPointwise _ _ thirdArity
            (fun thirdIndex _ =>
              (mulAssoc (denoteEntries thirdStage rowIndex thirdIndex)
                (denoteEntries secondStage thirdIndex secondIndex)
                (denoteEntries firstStage secondIndex colIndex)).symm))
  | tensorIdentityFusion topStrandCount bottomStrandCount =>
      refine agreeUpToOfPointwise _ _ _ _
        (fun rowIndex colIndex isRowInRange isColInRange => ?_)
      show directSumEntries topStrandCount topStrandCount identityEntries identityEntries
          rowIndex colIndex
        = identityEntries rowIndex colIndex
      cases decomposeIndexAgainstBlock topStrandCount rowIndex with
      | inl isRowInTop =>
          cases decomposeIndexAgainstBlock topStrandCount colIndex with
          | inl isColInTop =>
              rw [directSumEntryInTopBlock _ _ isRowInTop isColInTop]
          | inr colHasOffset =>
              cases colHasOffset with
              | intro colOffset colSplits =>
                  rw [colSplits, directSumEntryInTopRightBlock _ _ colOffset isRowInTop,
                    identityEntryOffDiagonal (fun isRowAtOffset => by
                      rw [isRowAtOffset] at isRowInTop
                      exact noLtOfGe (Nat.le_add_right topStrandCount colOffset) isRowInTop)]
      | inr rowHasOffset =>
          cases rowHasOffset with
          | intro rowOffset rowSplits =>
              cases decomposeIndexAgainstBlock topStrandCount colIndex with
              | inl isColInTop =>
                  rw [rowSplits, directSumEntryInBottomLeftBlock _ _ rowOffset isColInTop,
                    identityEntryOffDiagonal (fun isOffsetAtCol => by
                      rw [isOffsetAtCol.symm] at isColInTop
                      exact noLtOfGe (Nat.le_add_right topStrandCount rowOffset) isColInTop)]
              | inr colHasOffset =>
                  cases colHasOffset with
                  | intro colOffset colSplits =>
                      rw [rowSplits, colSplits,
                        directSumEntryInBottomBlock _ _ rowOffset colOffset]
                      show cond (Nat.beq rowOffset colOffset) 1 0
                        = cond (Nat.beq (topStrandCount + rowOffset)
                            (topStrandCount + colOffset)) 1 0
                      rw [beqAddLeftCancel topStrandCount rowOffset colOffset]
  | @middleFourInterchange topSourceArity topMiddleArity topTargetArity
      bottomSourceArity bottomMiddleArity bottomTargetArity
      topFirst topSecond bottomFirst bottomSecond =>
      refine agreeUpToOfPointwise _ _ _ _
        (fun rowIndex colIndex isRowInRange isColInRange => ?_)
      show directSumEntries topTargetArity topSourceArity
          (composeEntries topMiddleArity (denoteEntries topSecond) (denoteEntries topFirst))
          (composeEntries bottomMiddleArity (denoteEntries bottomSecond)
            (denoteEntries bottomFirst))
          rowIndex colIndex
        = sumBelow (fun midIndex =>
            directSumEntries topTargetArity topMiddleArity
              (denoteEntries topSecond) (denoteEntries bottomSecond) rowIndex midIndex
            * directSumEntries topMiddleArity topSourceArity
                (denoteEntries topFirst) (denoteEntries bottomFirst) midIndex colIndex)
          (topMiddleArity + bottomMiddleArity)
      simp only [sumBelowSplitsAtBlock]
      cases decomposeIndexAgainstBlock topTargetArity rowIndex with
      | inl isRowInTop =>
          have tailVanishes : sumBelow (fun offsetIndex =>
              directSumEntries topTargetArity topMiddleArity
                (denoteEntries topSecond) (denoteEntries bottomSecond) rowIndex
                (topMiddleArity + offsetIndex)
              * directSumEntries topMiddleArity topSourceArity
                  (denoteEntries topFirst) (denoteEntries bottomFirst)
                  (topMiddleArity + offsetIndex) colIndex) bottomMiddleArity = 0 :=
            sumBelowOfAllZeroIsZero _ bottomMiddleArity (fun offsetIndex _ => by
              rw [directSumEntryInTopRightBlock _ _ offsetIndex isRowInTop]
              exact zeroMulIsZero _)
          rw [tailVanishes, Nat.add_zero]
          cases decomposeIndexAgainstBlock topSourceArity colIndex with
          | inl isColInTop =>
              rw [directSumEntryInTopBlock _ _ isRowInTop isColInTop]
              exact sumBelowRespectsPointwise _ _ topMiddleArity
                (fun midIndex isMidInTop => by
                  rw [directSumEntryInTopBlock _ _ isRowInTop isMidInTop,
                    directSumEntryInTopBlock _ _ isMidInTop isColInTop])
          | inr colHasOffset =>
              cases colHasOffset with
              | intro colOffset colSplits =>
                  rw [colSplits, directSumEntryInTopRightBlock _ _ colOffset isRowInTop]
                  exact (sumBelowOfAllZeroIsZero _ topMiddleArity
                    (fun midIndex isMidInTop => by
                      rw [directSumEntryInTopRightBlock _ _ colOffset isMidInTop]
                      rfl)).symm
      | inr rowHasOffset =>
          cases rowHasOffset with
          | intro rowOffset rowSplits =>
              have headVanishes : sumBelow (fun midIndex =>
                  directSumEntries topTargetArity topMiddleArity
                    (denoteEntries topSecond) (denoteEntries bottomSecond) rowIndex midIndex
                  * directSumEntries topMiddleArity topSourceArity
                      (denoteEntries topFirst) (denoteEntries bottomFirst) midIndex colIndex)
                  topMiddleArity = 0 :=
                sumBelowOfAllZeroIsZero _ topMiddleArity (fun midIndex isMidInTop => by
                  rw [rowSplits, directSumEntryInBottomLeftBlock _ _ rowOffset isMidInTop]
                  exact zeroMulIsZero _)
              rw [headVanishes, Nat.zero_add]
              cases decomposeIndexAgainstBlock topSourceArity colIndex with
              | inl isColInTop =>
                  rw [rowSplits, directSumEntryInBottomLeftBlock _ _ rowOffset isColInTop]
                  exact (sumBelowOfAllZeroIsZero _ bottomMiddleArity
                    (fun offsetIndex _ => by
                      rw [directSumEntryInBottomLeftBlock _ _ offsetIndex isColInTop]
                      rfl)).symm
              | inr colHasOffset =>
                  cases colHasOffset with
                  | intro colOffset colSplits =>
                      rw [rowSplits, colSplits,
                        directSumEntryInBottomBlock _ _ rowOffset colOffset]
                      exact sumBelowRespectsPointwise _ _ bottomMiddleArity
                        (fun offsetIndex _ => by
                          rw [directSumEntryInBottomBlock _ _ rowOffset offsetIndex,
                            directSumEntryInBottomBlock _ _ offsetIndex colOffset])
  | fromAddAssociativityRow => exact addAssociativityRow_isSoundOverMatrices
  | fromAddLeftUnitRow => exact addLeftUnitRow_isSoundOverMatrices
  | fromAddRightUnitRow => exact addRightUnitRow_isSoundOverMatrices
  | fromAddCommutativityRow => exact addCommutativityRow_isSoundOverMatrices
  | fromCopyCoassociativityRow => exact copyCoassociativityRow_isSoundOverMatrices
  | fromCopyLeftCounitRow => exact copyLeftCounitRow_isSoundOverMatrices
  | fromCopyRightCounitRow => exact copyRightCounitRow_isSoundOverMatrices
  | fromCopyCocommutativityRow => exact copyCocommutativityRow_isSoundOverMatrices
  | fromCopyAfterAddBimonoidRow => exact copyAfterAddBimonoidRow_isSoundOverMatrices
  | fromCopyAfterZeroBimonoidRow => exact copyAfterZeroBimonoidRow_isSoundOverMatrices
  | fromDiscardAfterAddBimonoidRow => exact discardAfterAddBimonoidRow_isSoundOverMatrices
  | fromDiscardAfterZeroBimonoidRow => exact discardAfterZeroBimonoidRow_isSoundOverMatrices
  | fromSwapInvolutionRow => exact swapInvolutionRow_isSoundOverMatrices
  | fromSwapYangBaxterRow => exact swapYangBaxterRow_isSoundOverMatrices
  | fromSwapPastAddNaturalityRow => exact swapPastAddNaturalityRow_isSoundOverMatrices
  | fromSwapPastZeroNaturalityRow => exact swapPastZeroNaturalityRow_isSoundOverMatrices
  | fromCopyPastSwapNaturalityRow => exact copyPastSwapNaturalityRow_isSoundOverMatrices
  | fromDiscardPastSwapNaturalityRow => exact discardPastSwapNaturalityRow_isSoundOverMatrices

/-- RESIDUAL 1 DISCHARGED: the r1 named statement `convertibilityMatrixSoundnessStatement`
now HOLDS. -/
theorem convertibilityMatrixSoundnessHolds : convertibilityMatrixSoundnessStatement :=
  fun _sourceArity _targetArity _leftDiagram _rightDiagram areConvertible =>
    convertibleDiagramsDenoteEqualMatrices areConvertible

/-- THE NEGATIVE DECISION DIRECTION: diagrams whose matrices DIFFER on the rectangle are NOT
convertible — soundness contraposed.  This is what makes a `false` matrix comparison a
machine-checked refutation of convertibility. -/
theorem notConvertibleOfDistinctMatrices {sourceArity targetArity : Nat}
    (leftDiagram rightDiagram : WireDiagram sourceArity targetArity)
    (doMatricesDiffer : doEntriesAgreeUpTo targetArity sourceArity
      (denoteEntries leftDiagram) (denoteEntries rightDiagram) = false) :
    AreConvertibleDiagrams leftDiagram rightDiagram -> False :=
  fun areConvertible =>
    Bool.noConfusion
      (doMatricesDiffer.symm.trans (convertibleDiagramsDenoteEqualMatrices areConvertible))

/-- Consumption fire: the r1 three-step derived chain, pushed through the soundness theorem —
its endpoint matrices agree (here BY THE THEOREM, not by kernel computation). -/
theorem derivedChainMatricesAgreeViaSoundness :
    doEntriesAgreeUpTo 1 0 (denoteEntries derivedZeroThenLeftUnitChain)
      (denoteEntries WireDiagram.zeroGen) = true :=
  convertibleDiagramsDenoteEqualMatrices derivedZeroThenLeftUnitChainConverts

end FX1Poly.Polygraph.Omega.LafontProp
