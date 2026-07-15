import FX1Poly.Polygraph.Omega.LafontProp.BicommutativeBimonoidPresentation

/-! # Polygraph/Omega/LafontProp/MatrixNormalForm — the canonical diagram of a matrix
(LAFONT-PROP r2, brick A: THE NORMAL FORM + ITS SOUNDNESS)

The completeness half of the Lafont presentation runs through CANONICAL FORMS ([Lafont2003]
Sections 2-3: "any diagram reduces to a canonical form", unique per represented map; the
[BSZ2017]/[Lack2004] factorisation route reads the same object as the comonoid-then-monoid span
form).  This file builds the canonical-form machine for Mat(N):

* `canonicalDiagramOfEntries sourceArity targetArity entries` — the canonical wire diagram of an
  arbitrary `targetArity x sourceArity` natural-number matrix, built column by column: each input
  strand is merged into the accumulated outputs by a `mergeColumnFan` ladder whose rungs are
  copy-scale-add gadgets (`scaleThenSwapGadget`), with scalar multiplication by a natural number
  implemented as the `scaleWire` copy-add tower.  The construction is TOTAL, STRUCTURAL (no
  `WellFounded.fix`), and uses only the five Lafont generators plus identities.
* SOUNDNESS OF THE NORMAL FORM (proved here, the round's theorem): the canonical diagram of a
  matrix DENOTES that matrix — `canonicalDiagramDenotesEntriesWithin` pointwise on the full
  rectangle, packaged as `canonicalFormIsSoundOverMatrices` in the kernel-decidable Bool form.
* `normalFormOfDiagram` — the normal form of a diagram is the canonical diagram of its
  denotation; `normalFormPreservesDenotation` instantiates soundness.
* RECTANGLE EXTENSIONALITY: the canonical diagram reads its matrix ONLY on the denoted rectangle
  (`canonicalDiagramRespectsRectangleAgreement`), hence diagrams with EQUAL matrices have
  syntactically EQUAL normal forms (`equalMatricesGiveEqualNormalForms`).
* THE REDUCTION THEOREM (`completenessReducesToCanonicalReduction`): full completeness
  (`matNatCompletenessStatement`) REDUCES to the single named residual
  `canonicalReductionStatement` — "every diagram is convertible to its own normal form".  The
  residual is stated (owner false), NOT proven: it is the rewrite-system half of [Lafont2003]'s
  argument and remains the named target of the next round.

Everything below the diagram layer is a self-built greenfield kit: comparison/subtraction lemmas
on `Nat`, support lemmas for the structural `sumBelow`, block lemmas for `directSumEntries`, and
the pointwise/Bool rectangle-agreement bridge.  Raw Lean 4 + Init only; zero-axiom; structural
recursion only; audit twin with per-decl `#assert_no_axioms` plus an independent `#print axioms`
witness. -/

namespace FX1Poly.Polygraph.Omega.LafontProp

/-! ## Greenfield Nat comparison kit (zero-axiom; own proofs, no risky core lemmas) -/

/-- `Nat.beq` is reflexive. -/
theorem beqSelfIsTrue : (valueNat : Nat) -> Nat.beq valueNat valueNat = true
  | 0 => rfl
  | valuePred + 1 => beqSelfIsTrue valuePred

/-- `Nat.beq` sound direction: a true test yields a propositional equality. -/
theorem eqOfBeqIsTrue : {leftNat rightNat : Nat} -> Nat.beq leftNat rightNat = true ->
    leftNat = rightNat
  | 0, 0, _ => rfl
  | 0, _ + 1, testHolds => Bool.noConfusion testHolds
  | _ + 1, 0, testHolds => Bool.noConfusion testHolds
  | leftPred + 1, rightPred + 1, testHolds =>
      congrArg Nat.succ (eqOfBeqIsTrue (leftNat := leftPred) (rightNat := rightPred) testHolds)

/-- `Nat.beq` on provably different arguments is `false`. -/
theorem beqIsFalseOfNe {leftNat rightNat : Nat} (areDifferent : leftNat ≠ rightNat) :
    Nat.beq leftNat rightNat = false := by
  cases beqObserved : Nat.beq leftNat rightNat with
  | false => rfl
  | true => exact absurd (eqOfBeqIsTrue beqObserved) areDifferent

/-- `Nat.ble` complete direction: an order fact makes the test true. -/
theorem bleIsTrueOfLe : {smallNat bigNat : Nat} -> smallNat ≤ bigNat ->
    Nat.ble smallNat bigNat = true
  | 0, _, _ => rfl
  | smallPred + 1, 0, isAtMost => absurd isAtMost (Nat.not_succ_le_zero smallPred)
  | smallPred + 1, bigPred + 1, isAtMost =>
      bleIsTrueOfLe (smallNat := smallPred) (bigNat := bigPred)
        (Nat.le_of_succ_le_succ isAtMost)

/-- `Nat.ble` sound direction. -/
theorem leOfBleIsTrue : {smallNat bigNat : Nat} -> Nat.ble smallNat bigNat = true ->
    smallNat ≤ bigNat
  | 0, bigNat, _ => Nat.zero_le bigNat
  | _ + 1, 0, testHolds => Bool.noConfusion testHolds
  | smallPred + 1, bigPred + 1, testHolds =>
      Nat.succ_le_succ
        (leOfBleIsTrue (smallNat := smallPred) (bigNat := bigPred) testHolds)

/-- `Nat.blt` complete direction (`blt leftNat rightNat` is `ble (leftNat+1) rightNat`). -/
theorem bltIsTrueOfLt {leftNat rightNat : Nat} (isBelow : leftNat < rightNat) :
    Nat.blt leftNat rightNat = true := bleIsTrueOfLe isBelow

/-- `Nat.blt` sound direction. -/
theorem ltOfBltIsTrue {leftNat rightNat : Nat} (testHolds : Nat.blt leftNat rightNat = true) :
    leftNat < rightNat := leOfBleIsTrue testHolds

/-- `Nat.blt` on a reverse-ordered pair is `false`. -/
theorem bltIsFalseOfGe {leftNat rightNat : Nat} (isAtMost : rightNat ≤ leftNat) :
    Nat.blt leftNat rightNat = false := by
  cases bltObserved : Nat.blt leftNat rightNat with
  | false => rfl
  | true =>
      exact absurd (Nat.le_trans (ltOfBltIsTrue bltObserved) isAtMost) (Nat.lt_irrefl leftNat)

/-- Equal naturals are never strictly ordered (case on the equality — no rewrite-motive
guessing). -/
theorem noLtOfEq {firstNat secondNat : Nat} (areEqual : firstNat = secondNat)
    (isBelow : firstNat < secondNat) : False := by
  cases areEqual
  exact Nat.lt_irrefl firstNat isBelow

/-- Split a strict bound below a successor into the tail bound or the head equality. -/
theorem ltOrEqOfLtSucc {smallNat bigNat : Nat} (isBelowSucc : smallNat < bigNat + 1) :
    smallNat < bigNat ∨ smallNat = bigNat :=
  match Nat.le_of_succ_le_succ isBelowSucc with
  | Nat.le.refl => Or.inr rfl
  | Nat.le.step deeperBound => Or.inl (Nat.succ_le_succ deeperBound)

/-- Successor subtraction peels one successor from each side (own structural proof; the core
`Nat.sub` rewrite kit is propext-risky). -/
theorem succSubSucc : (subtrahend minuend : Nat) ->
    (minuend + 1) - (subtrahend + 1) = minuend - subtrahend
  | 0, _ => rfl
  | subPred + 1, minuend => congrArg Nat.pred (succSubSucc subPred minuend)

/-- Left-addition cancels against subtraction: `(baseNat + offsetNat) - baseNat = offsetNat`. -/
theorem addSubCancelLeft : (baseNat offsetNat : Nat) -> (baseNat + offsetNat) - baseNat = offsetNat
  | 0, offsetNat => congrArg (fun strippedNat => strippedNat - 0) (Nat.zero_add offsetNat)
      |>.trans rfl
  | basePred + 1, offsetNat =>
      (congrArg (fun shiftedNat => shiftedNat - (basePred + 1))
          (Nat.succ_add basePred offsetNat)).trans
        ((succSubSucc basePred (basePred + offsetNat)).trans (addSubCancelLeft basePred offsetNat))

/-! ## Greenfield Nat multiplication mini-kit -/

/-- `valueNat * 1 = valueNat` (definitional down to `0 + valueNat`). -/
theorem mulOneIsSelf (valueNat : Nat) : valueNat * 1 = valueNat := Nat.zero_add valueNat

/-- `1 * valueNat = valueNat`. -/
theorem oneMulIsSelf : (valueNat : Nat) -> 1 * valueNat = valueNat
  | 0 => rfl
  | valuePred + 1 => congrArg (fun innerNat => innerNat + 1) (oneMulIsSelf valuePred)

/-- `0 * valueNat = 0`. -/
theorem zeroMulIsZero : (valueNat : Nat) -> 0 * valueNat = 0
  | 0 => rfl
  | valuePred + 1 => zeroMulIsZero valuePred

/-! ## Support lemmas for the structural sum -/

/-- A sum all of whose terms vanish below the bound is zero. -/
theorem sumBelowOfAllZeroIsZero (termAt : Nat -> Nat) (bound : Nat)
    (doAllTermsVanish : ∀ termIndex, termIndex < bound -> termAt termIndex = 0) :
    sumBelow termAt bound = 0 := by
  induction bound with
  | zero => rfl
  | succ boundPred inductiveHypothesis =>
      have tailVanishes := inductiveHypothesis
        (fun termIndex isBelow => doAllTermsVanish termIndex (Nat.le.step isBelow))
      have headVanishes := doAllTermsVanish boundPred (Nat.lt_succ_self boundPred)
      show sumBelow termAt boundPred + termAt boundPred = 0
      rw [tailVanishes, headVanishes]

/-- A sum whose terms vanish everywhere except one supported index collapses to that term. -/
theorem sumBelowOfSingleSupport (termAt : Nat -> Nat) (bound supportIndex : Nat)
    (isSupportInBound : supportIndex < bound)
    (doOtherTermsVanish : ∀ termIndex, termIndex < bound -> termIndex ≠ supportIndex ->
      termAt termIndex = 0) :
    sumBelow termAt bound = termAt supportIndex := by
  induction bound with
  | zero => exact absurd isSupportInBound (Nat.not_succ_le_zero supportIndex)
  | succ boundPred inductiveHypothesis =>
      cases ltOrEqOfLtSucc isSupportInBound with
      | inl isSupportInTail =>
          have headVanishes := doOtherTermsVanish boundPred (Nat.lt_succ_self boundPred)
            (fun isHeadSupport => noLtOfEq isHeadSupport.symm isSupportInTail)
          have tailCollapses := inductiveHypothesis isSupportInTail
            (fun termIndex isInTail notSupport =>
              doOtherTermsVanish termIndex (Nat.le.step isInTail) notSupport)
          show sumBelow termAt boundPred + termAt boundPred = termAt supportIndex
          rw [tailCollapses, headVanishes]
          rfl
      | inr isSupportAtHead =>
          have tailVanishes := sumBelowOfAllZeroIsZero termAt boundPred
            (fun termIndex isInTail =>
              doOtherTermsVanish termIndex (Nat.le.step isInTail)
                (fun isTermSupport =>
                  noLtOfEq (isTermSupport.trans isSupportAtHead) isInTail))
          show sumBelow termAt boundPred + termAt boundPred = termAt supportIndex
          rw [tailVanishes, isSupportAtHead]
          exact Nat.zero_add (termAt boundPred)

/-! ## Block lemmas for the direct sum and the identity entries -/

/-- Identity entries on the diagonal are 1. -/
theorem identityEntryOnDiagonal (diagonalIndex : Nat) :
    identityEntries diagonalIndex diagonalIndex = 1 := by
  show cond (Nat.beq diagonalIndex diagonalIndex) 1 0 = 1
  rw [beqSelfIsTrue diagonalIndex]
  rfl

/-- Identity entries off the diagonal are 0. -/
theorem identityEntryOffDiagonal {rowIndex colIndex : Nat} (areDifferent : rowIndex ≠ colIndex) :
    identityEntries rowIndex colIndex = 0 := by
  show cond (Nat.beq rowIndex colIndex) 1 0 = 0
  rw [beqIsFalseOfNe areDifferent]
  rfl

/-- Direct-sum entry inside the top-left block. -/
theorem directSumEntryInTopBlock {topRowCount topColCount : Nat}
    (topEntries bottomEntries : MatrixEntries) {rowIndex colIndex : Nat}
    (isRowInTop : rowIndex < topRowCount) (isColInTop : colIndex < topColCount) :
    directSumEntries topRowCount topColCount topEntries bottomEntries rowIndex colIndex
      = topEntries rowIndex colIndex := by
  show cond (Nat.blt rowIndex topRowCount)
      (cond (Nat.blt colIndex topColCount) (topEntries rowIndex colIndex) 0)
      (cond (Nat.blt colIndex topColCount) 0
        (bottomEntries (rowIndex - topRowCount) (colIndex - topColCount)))
    = topEntries rowIndex colIndex
  rw [bltIsTrueOfLt isRowInTop, bltIsTrueOfLt isColInTop]
  rfl

/-- Direct-sum entry inside the bottom-right block, addressed by offsets. -/
theorem directSumEntryInBottomBlock {topRowCount topColCount : Nat}
    (topEntries bottomEntries : MatrixEntries) (rowOffset colOffset : Nat) :
    directSumEntries topRowCount topColCount topEntries bottomEntries
      (topRowCount + rowOffset) (topColCount + colOffset) = bottomEntries rowOffset colOffset := by
  show cond (Nat.blt (topRowCount + rowOffset) topRowCount)
      (cond (Nat.blt (topColCount + colOffset) topColCount)
        (topEntries (topRowCount + rowOffset) (topColCount + colOffset)) 0)
      (cond (Nat.blt (topColCount + colOffset) topColCount) 0
        (bottomEntries ((topRowCount + rowOffset) - topRowCount)
          ((topColCount + colOffset) - topColCount)))
    = bottomEntries rowOffset colOffset
  rw [bltIsFalseOfGe (Nat.le_add_right topRowCount rowOffset),
    bltIsFalseOfGe (Nat.le_add_right topColCount colOffset),
    addSubCancelLeft topRowCount rowOffset, addSubCancelLeft topColCount colOffset]
  rfl

/-- Direct-sum entry in the top-right off-diagonal block is 0. -/
theorem directSumEntryInTopRightBlock {topRowCount topColCount : Nat}
    (topEntries bottomEntries : MatrixEntries) {rowIndex : Nat} (colOffset : Nat)
    (isRowInTop : rowIndex < topRowCount) :
    directSumEntries topRowCount topColCount topEntries bottomEntries
      rowIndex (topColCount + colOffset) = 0 := by
  show cond (Nat.blt rowIndex topRowCount)
      (cond (Nat.blt (topColCount + colOffset) topColCount)
        (topEntries rowIndex (topColCount + colOffset)) 0)
      (cond (Nat.blt (topColCount + colOffset) topColCount) 0
        (bottomEntries (rowIndex - topRowCount) ((topColCount + colOffset) - topColCount)))
    = 0
  rw [bltIsTrueOfLt isRowInTop, bltIsFalseOfGe (Nat.le_add_right topColCount colOffset)]
  rfl

/-- Direct-sum entry in the bottom-left off-diagonal block is 0. -/
theorem directSumEntryInBottomLeftBlock {topRowCount topColCount : Nat}
    (topEntries bottomEntries : MatrixEntries) {colIndex : Nat} (rowOffset : Nat)
    (isColInTop : colIndex < topColCount) :
    directSumEntries topRowCount topColCount topEntries bottomEntries
      (topRowCount + rowOffset) colIndex = 0 := by
  show cond (Nat.blt (topRowCount + rowOffset) topRowCount)
      (cond (Nat.blt colIndex topColCount) (topEntries (topRowCount + rowOffset) colIndex) 0)
      (cond (Nat.blt colIndex topColCount) 0
        (bottomEntries ((topRowCount + rowOffset) - topRowCount) (colIndex - topColCount)))
    = 0
  rw [bltIsFalseOfGe (Nat.le_add_right topRowCount rowOffset), bltIsTrueOfLt isColInTop]
  rfl

/-! ## The pointwise/Bool rectangle-agreement bridge -/

/-- Left conjunct of a true `&&`. -/
theorem leftIsTrueOfAndTrue {leftFlag rightFlag : Bool}
    (doBothHold : (leftFlag && rightFlag) = true) : leftFlag = true := by
  cases leftFlag with
  | true => rfl
  | false => exact Bool.noConfusion doBothHold

/-- Right conjunct of a true `&&`. -/
theorem rightIsTrueOfAndTrue {leftFlag rightFlag : Bool}
    (doBothHold : (leftFlag && rightFlag) = true) : rightFlag = true := by
  cases leftFlag with
  | true => exact doBothHold
  | false => exact Bool.noConfusion doBothHold

/-- Pointwise row agreement makes the row checker true. -/
theorem agreeOnRowOfPointwise (leftEntries rightEntries : MatrixEntries) (rowIndex : Nat)
    (colBound : Nat)
    (agreePointwise : ∀ colIndex, colIndex < colBound ->
      leftEntries rowIndex colIndex = rightEntries rowIndex colIndex) :
    doEntriesAgreeOnRow leftEntries rightEntries rowIndex colBound = true := by
  induction colBound with
  | zero => rfl
  | succ colBoundPred inductiveHypothesis =>
      have tailAgrees := inductiveHypothesis
        (fun colIndex isBelow => agreePointwise colIndex (Nat.le.step isBelow))
      have headAgrees : Nat.beq (leftEntries rowIndex colBoundPred)
          (rightEntries rowIndex colBoundPred) = true := by
        rw [agreePointwise colBoundPred (Nat.lt_succ_self colBoundPred)]
        exact beqSelfIsTrue (rightEntries rowIndex colBoundPred)
      show (doEntriesAgreeOnRow leftEntries rightEntries rowIndex colBoundPred
          && Nat.beq (leftEntries rowIndex colBoundPred) (rightEntries rowIndex colBoundPred))
        = true
      rw [tailAgrees, headAgrees]
      rfl

/-- A true row checker yields pointwise agreement on that row. -/
theorem pointwiseOfAgreeOnRow (leftEntries rightEntries : MatrixEntries) (rowIndex : Nat) :
    (colBound : Nat) ->
    doEntriesAgreeOnRow leftEntries rightEntries rowIndex colBound = true ->
    ∀ colIndex, colIndex < colBound ->
      leftEntries rowIndex colIndex = rightEntries rowIndex colIndex
  | 0, _, colIndex, isBelowZero => absurd isBelowZero (Nat.not_succ_le_zero colIndex)
  | colBoundPred + 1, checkerHolds, colIndex, isBelow => by
      have tailFlag := leftIsTrueOfAndTrue checkerHolds
      have headFlag := rightIsTrueOfAndTrue checkerHolds
      cases ltOrEqOfLtSucc isBelow with
      | inl isInTail =>
          exact pointwiseOfAgreeOnRow leftEntries rightEntries rowIndex colBoundPred
            tailFlag colIndex isInTail
      | inr isAtHead =>
          rw [isAtHead]
          exact eqOfBeqIsTrue headFlag

/-- Pointwise rectangle agreement makes the all-rows checker true. -/
theorem agreeOnRowsOfPointwise (leftEntries rightEntries : MatrixEntries) (colCount : Nat)
    (rowBound : Nat)
    (agreePointwise : ∀ rowIndex colIndex, rowIndex < rowBound -> colIndex < colCount ->
      leftEntries rowIndex colIndex = rightEntries rowIndex colIndex) :
    doEntriesAgreeOnRows leftEntries rightEntries colCount rowBound = true := by
  induction rowBound with
  | zero => rfl
  | succ rowBoundPred inductiveHypothesis =>
      have tailAgrees := inductiveHypothesis
        (fun rowIndex colIndex isRowBelow isColBelow =>
          agreePointwise rowIndex colIndex (Nat.le.step isRowBelow) isColBelow)
      have headAgrees := agreeOnRowOfPointwise leftEntries rightEntries rowBoundPred colCount
        (fun colIndex isColBelow =>
          agreePointwise rowBoundPred colIndex (Nat.lt_succ_self rowBoundPred) isColBelow)
      show (doEntriesAgreeOnRows leftEntries rightEntries colCount rowBoundPred
          && doEntriesAgreeOnRow leftEntries rightEntries rowBoundPred colCount) = true
      rw [tailAgrees, headAgrees]
      rfl

/-- A true all-rows checker yields pointwise rectangle agreement. -/
theorem pointwiseOfAgreeOnRows (leftEntries rightEntries : MatrixEntries) (colCount : Nat) :
    (rowBound : Nat) ->
    doEntriesAgreeOnRows leftEntries rightEntries colCount rowBound = true ->
    ∀ rowIndex colIndex, rowIndex < rowBound -> colIndex < colCount ->
      leftEntries rowIndex colIndex = rightEntries rowIndex colIndex
  | 0, _, rowIndex, _, isRowBelowZero, _ => absurd isRowBelowZero (Nat.not_succ_le_zero rowIndex)
  | rowBoundPred + 1, checkerHolds, rowIndex, colIndex, isRowBelow, isColBelow => by
      have tailFlag := leftIsTrueOfAndTrue checkerHolds
      have headFlag := rightIsTrueOfAndTrue checkerHolds
      cases ltOrEqOfLtSucc isRowBelow with
      | inl isInTail =>
          exact pointwiseOfAgreeOnRows leftEntries rightEntries colCount rowBoundPred
            tailFlag rowIndex colIndex isInTail isColBelow
      | inr isAtHead =>
          rw [isAtHead]
          exact pointwiseOfAgreeOnRow leftEntries rightEntries rowBoundPred colCount
            headFlag colIndex isColBelow

/-- Pointwise agreement on the rectangle makes `doEntriesAgreeUpTo` true. -/
theorem agreeUpToOfPointwise (rowCount colCount : Nat) (leftEntries rightEntries : MatrixEntries)
    (agreePointwise : ∀ rowIndex colIndex, rowIndex < rowCount -> colIndex < colCount ->
      leftEntries rowIndex colIndex = rightEntries rowIndex colIndex) :
    doEntriesAgreeUpTo rowCount colCount leftEntries rightEntries = true :=
  agreeOnRowsOfPointwise leftEntries rightEntries colCount rowCount agreePointwise

/-- A true `doEntriesAgreeUpTo` yields pointwise agreement on the rectangle. -/
theorem pointwiseOfAgreeUpTo (rowCount colCount : Nat) (leftEntries rightEntries : MatrixEntries)
    (checkerHolds : doEntriesAgreeUpTo rowCount colCount leftEntries rightEntries = true) :
    ∀ rowIndex colIndex, rowIndex < rowCount -> colIndex < colCount ->
      leftEntries rowIndex colIndex = rightEntries rowIndex colIndex :=
  pointwiseOfAgreeOnRows leftEntries rightEntries colCount rowCount checkerHolds

/-! ## The canonical-form construction

Column-by-column ([Lack2004] Section 5.3 reads the matrix as the span form; here the comonoid
part is the copy tower inside `scaleWire`/`scaleThenSwapGadget`, the monoid part the add rungs):

* `scaleWire scaleFactor : 1 -> 1` — multiply a wire by a natural number (copy-add tower).
* `scaleThenSwapGadget scaleFactor : 2 -> 2` — `[inputWire, sourceWire]` becomes
  `[sourceWire, inputWire + scaleFactor * sourceWire]`: copy the source, scale one copy, add it
  into the input, swap so the source continues upward.
* `mergeColumnFan vectorLength columnEntries : vectorLength + 1 -> vectorLength` — the ladder
  merging one fresh source strand (the LAST input) into `vectorLength` accumulated strands:
  output `i` is `input i + columnEntries i * source`; the spent source is discarded at the top.
* `canonicalDiagramOfEntries sourceArity targetArity entries` — fold `mergeColumnFan` over the
  columns; the base case is the eta row `zeroVectorDiagram`.

All strand-count arithmetic keeps the open variable LEFT of `+` so every index equation is
definitional — no casts, no `Eq.rec` over arities. -/

/-- Multiply one wire by a scalar: 0 is discard-then-zero, `scaleFactorPred + 1` is
copy, scale one branch by `scaleFactorPred`, add. -/
def scaleWire : Nat -> WireDiagram 1 1
  | 0 => WireDiagram.composeSequential WireDiagram.discardGen WireDiagram.zeroGen
  | scaleFactorPred + 1 =>
      WireDiagram.composeSequential WireDiagram.copyGen
        (WireDiagram.composeSequential
          (WireDiagram.tensorParallel (scaleWire scaleFactorPred) singleWire)
          WireDiagram.addGen)

/-- The merge rung: `[inputWire, sourceWire]` to `[sourceWire, inputWire + scaleFactor * sourceWire]`
(copy the source, scale the middle copy, add into the input, swap). -/
def scaleThenSwapGadget (scaleFactor : Nat) : WireDiagram 2 2 :=
  WireDiagram.composeSequential
    (WireDiagram.composeSequential
      (WireDiagram.composeSequential
        (WireDiagram.tensorParallel singleWire WireDiagram.copyGen : WireDiagram 2 3)
        (WireDiagram.tensorParallel
          (WireDiagram.tensorParallel singleWire (scaleWire scaleFactor) : WireDiagram 2 2)
          singleWire : WireDiagram 3 3))
      (WireDiagram.tensorParallel WireDiagram.addGen singleWire : WireDiagram 3 2))
    WireDiagram.swapGen

/-- The column-merge ladder: `vectorLength` accumulated strands plus one fresh source strand at
the bottom; output `i` is `input i + columnEntries i * source`.  Each rung applies the gadget to
the bottom two strands and lets the source strand climb; the spent source is discarded by the
base-case `discardGen`. -/
def mergeColumnFan : (vectorLength : Nat) -> (columnEntries : Nat -> Nat) ->
    WireDiagram (vectorLength + 1) vectorLength
  | 0, _ => WireDiagram.discardGen
  | vectorLengthPred + 1, columnEntries =>
      WireDiagram.composeSequential
        (WireDiagram.tensorParallel (WireDiagram.identityWires vectorLengthPred)
          (scaleThenSwapGadget (columnEntries vectorLengthPred))
          : WireDiagram (vectorLengthPred + 2) (vectorLengthPred + 2))
        (WireDiagram.tensorParallel (mergeColumnFan vectorLengthPred columnEntries) singleWire
          : WireDiagram ((vectorLengthPred + 1) + 1) (vectorLengthPred + 1))

/-- The eta row `0 -> targetArity`: every output is the constant zero. -/
def zeroVectorDiagram : (targetArity : Nat) -> WireDiagram 0 targetArity
  | 0 => WireDiagram.identityWires 0
  | targetArityPred + 1 =>
      WireDiagram.tensorParallel (zeroVectorDiagram targetArityPred) WireDiagram.zeroGen

/-- THE CANONICAL DIAGRAM of a `targetArity x sourceArity` matrix: fold the column-merge ladder
over the columns, newest column entering as the bottom strand. -/
def canonicalDiagramOfEntries : (sourceArity targetArity : Nat) -> MatrixEntries ->
    WireDiagram sourceArity targetArity
  | 0, targetArity, _ => zeroVectorDiagram targetArity
  | sourceArityPred + 1, targetArity, entries =>
      WireDiagram.composeSequential
        (WireDiagram.tensorParallel
          (canonicalDiagramOfEntries sourceArityPred targetArity entries) singleWire)
        (mergeColumnFan targetArity (fun mergeRow => entries mergeRow sourceArityPred))

/-- THE NORMAL FORM of a diagram: the canonical diagram of its denotation. -/
def normalFormOfDiagram {sourceArity targetArity : Nat}
    (diagram : WireDiagram sourceArity targetArity) : WireDiagram sourceArity targetArity :=
  canonicalDiagramOfEntries sourceArity targetArity (denoteEntries diagram)

/-! ## Denotation of the construction blocks

Each lemma opens with a `show` of the MINIMAL DEFEQ SKELETON of the composite entry: every
ground subtree is folded to its literal value by definitional reduction (multiplications by a
LITERAL-0 right factor collapse even over the stuck scale entry), so only the additive chain
around the stuck `denoteEntries (scaleWire _) 0 0` survives; a short clean `rw` chain
(never `simp`, which closes goals through the propext-carrying `eq_true`) then finishes. -/

/-- The scale tower denotes multiplication: its single matrix entry is the scale factor. -/
theorem scaleWireDenotesScalar (scaleFactor : Nat) :
    denoteEntries (scaleWire scaleFactor) 0 0 = scaleFactor := by
  induction scaleFactor with
  | zero => rfl
  | succ scaleFactorPred inductiveHypothesis =>
      show 0 + (0 + 1 * denoteEntries (scaleWire scaleFactorPred) 0 0) * 1 + 1
        = scaleFactorPred + 1
      rw [inductiveHypothesis, oneMulIsSelf scaleFactorPred, Nat.zero_add scaleFactorPred,
        mulOneIsSelf scaleFactorPred, Nat.zero_add scaleFactorPred]

/-- Gadget matrix, entry (0,0): the source output does not read the input wire. -/
theorem gadgetEntryZeroZero (scaleFactor : Nat) :
    denoteEntries (scaleThenSwapGadget scaleFactor) 0 0 = 0 := rfl

/-- Gadget matrix, entry (0,1): the source output copies the source wire. -/
theorem gadgetEntryZeroOne (scaleFactor : Nat) :
    denoteEntries (scaleThenSwapGadget scaleFactor) 0 1 = 1 := by
  show 0 + 0 * (0 + 1 * (0 + denoteEntries (scaleWire scaleFactor) 0 0 * 1))
      + 1 * ((0 + 0 * (0 + denoteEntries (scaleWire scaleFactor) 0 0 * 1)) + 1)
    = 1
  rw [scaleWireDenotesScalar, mulOneIsSelf scaleFactor, Nat.zero_add scaleFactor,
    zeroMulIsZero scaleFactor, oneMulIsSelf scaleFactor, Nat.zero_add scaleFactor,
    zeroMulIsZero scaleFactor]

/-- Gadget matrix, entry (1,0): the merged output keeps the input wire once. -/
theorem gadgetEntryOneZero (scaleFactor : Nat) :
    denoteEntries (scaleThenSwapGadget scaleFactor) 1 0 = 1 := rfl

/-- Gadget matrix, entry (1,1): the merged output takes the source scaled by the factor. -/
theorem gadgetEntryOneOne (scaleFactor : Nat) :
    denoteEntries (scaleThenSwapGadget scaleFactor) 1 1 = scaleFactor := by
  show 0 + 1 * (0 + 1 * (0 + denoteEntries (scaleWire scaleFactor) 0 0 * 1))
      + 0 * ((0 + 0 * (0 + denoteEntries (scaleWire scaleFactor) 0 0 * 1)) + 1)
    = scaleFactor
  rw [scaleWireDenotesScalar, mulOneIsSelf scaleFactor, Nat.zero_add scaleFactor,
    zeroMulIsZero scaleFactor, oneMulIsSelf scaleFactor, Nat.zero_add scaleFactor,
    oneMulIsSelf scaleFactor, Nat.zero_add scaleFactor]
  rfl

/-- The target entries of the column-merge ladder: identity on the first `vectorLength` columns,
the column vector on the last. -/
def mergeColumnFanEntries (vectorLength : Nat) (columnEntries : Nat -> Nat) : MatrixEntries :=
  fun rowIndex colIndex =>
    cond (Nat.blt colIndex vectorLength) (identityEntries rowIndex colIndex)
      (columnEntries rowIndex)

/-- The recursion stage of a merge rung, as entries: the shorter ladder beside a passing wire. -/
def mergeRecursionStageEntries (vectorLength : Nat) (columnEntries : Nat -> Nat) : MatrixEntries :=
  directSumEntries vectorLength (vectorLength + 1)
    (denoteEntries (mergeColumnFan vectorLength columnEntries)) identityEntries

/-- The gadget stage of a merge rung, as entries: identities above the bottom-two gadget. -/
def mergeGadgetStageEntries (vectorLength : Nat) (scaleFactor : Nat) : MatrixEntries :=
  directSumEntries vectorLength vectorLength identityEntries
    (denoteEntries (scaleThenSwapGadget scaleFactor))

/-- SOUNDNESS OF THE LADDER: within the `vectorLength x (vectorLength + 1)` rectangle the
column-merge ladder denotes `[identity | column]`. -/
theorem mergeColumnFanDenotesWithin (vectorLength : Nat) :
    ∀ (columnEntries : Nat -> Nat) (rowIndex colIndex : Nat),
      rowIndex < vectorLength -> colIndex < vectorLength + 1 ->
      denoteEntries (mergeColumnFan vectorLength columnEntries) rowIndex colIndex
        = mergeColumnFanEntries vectorLength columnEntries rowIndex colIndex := by
  induction vectorLength with
  | zero =>
      intro columnEntries rowIndex colIndex isRowBelowZero _
      exact absurd isRowBelowZero (Nat.not_succ_le_zero rowIndex)
  | succ vectorLengthPred inductiveHypothesis =>
      intro columnEntries rowIndex colIndex isRowInRange isColInRange
      show sumBelow (fun midIndex =>
          mergeRecursionStageEntries vectorLengthPred columnEntries rowIndex midIndex
          * mergeGadgetStageEntries vectorLengthPred (columnEntries vectorLengthPred)
              midIndex colIndex)
        (vectorLengthPred + 2)
        = mergeColumnFanEntries (vectorLengthPred + 1) columnEntries rowIndex colIndex
      cases ltOrEqOfLtSucc isRowInRange with
      | inl isRowInTail =>
          -- rowIndex < vectorLengthPred: the recursion row.
          have recursionRowEndVanishes :
              mergeRecursionStageEntries vectorLengthPred columnEntries rowIndex
                ((vectorLengthPred + 1) + 0) = 0 :=
            directSumEntryInTopRightBlock _ _ 0 isRowInTail
          cases ltOrEqOfLtSucc isColInRange with
          | inl isColBelowLadderTop =>
              cases ltOrEqOfLtSucc isColBelowLadderTop with
              | inl isColInTail =>
                  -- colIndex < vectorLengthPred: identity column; support at midIndex = colIndex.
                  refine (sumBelowOfSingleSupport _ (vectorLengthPred + 2) colIndex
                    (Nat.le.step (Nat.le.step isColInTail)) ?_).trans ?_
                  · intro midIndex isMidInBound isMidOffSupport
                    show mergeRecursionStageEntries vectorLengthPred columnEntries
                        rowIndex midIndex
                      * mergeGadgetStageEntries vectorLengthPred
                          (columnEntries vectorLengthPred) midIndex colIndex = 0
                    cases ltOrEqOfLtSucc isMidInBound with
                    | inr isMidAtSourceCopy =>
                        rw [isMidAtSourceCopy]
                        rw [show mergeRecursionStageEntries vectorLengthPred columnEntries
                              rowIndex (vectorLengthPred + 1) = 0 from recursionRowEndVanishes]
                        exact zeroMulIsZero _
                    | inl isMidBelowSourceCopy =>
                        cases ltOrEqOfLtSucc isMidBelowSourceCopy with
                        | inr isMidAtGadgetTop =>
                            rw [isMidAtGadgetTop]
                            rw [show mergeGadgetStageEntries vectorLengthPred
                                  (columnEntries vectorLengthPred)
                                  vectorLengthPred colIndex = 0 from
                              directSumEntryInBottomLeftBlock _ _ 0 isColInTail]
                            rfl
                        | inl isMidInGadgetIdentity =>
                            rw [show mergeGadgetStageEntries vectorLengthPred
                                  (columnEntries vectorLengthPred) midIndex colIndex
                                = identityEntries midIndex colIndex from
                              directSumEntryInTopBlock _ _ isMidInGadgetIdentity isColInTail]
                            rw [identityEntryOffDiagonal isMidOffSupport]
                            rfl
                  · show mergeRecursionStageEntries vectorLengthPred columnEntries
                        rowIndex colIndex
                      * mergeGadgetStageEntries vectorLengthPred
                          (columnEntries vectorLengthPred) colIndex colIndex
                      = mergeColumnFanEntries (vectorLengthPred + 1) columnEntries
                          rowIndex colIndex
                    rw [show mergeRecursionStageEntries vectorLengthPred columnEntries
                          rowIndex colIndex
                        = denoteEntries (mergeColumnFan vectorLengthPred columnEntries)
                            rowIndex colIndex from
                      directSumEntryInTopBlock _ _ isRowInTail (Nat.le.step isColInTail)]
                    rw [show mergeGadgetStageEntries vectorLengthPred
                          (columnEntries vectorLengthPred) colIndex colIndex
                        = identityEntries colIndex colIndex from
                      directSumEntryInTopBlock _ _ isColInTail isColInTail]
                    rw [identityEntryOnDiagonal colIndex, mulOneIsSelf]
                    rw [inductiveHypothesis columnEntries rowIndex colIndex isRowInTail
                      (Nat.le.step isColInTail)]
                    show cond (Nat.blt colIndex vectorLengthPred)
                        (identityEntries rowIndex colIndex) (columnEntries rowIndex)
                      = cond (Nat.blt colIndex (vectorLengthPred + 1))
                          (identityEntries rowIndex colIndex) (columnEntries rowIndex)
                    rw [bltIsTrueOfLt isColInTail, bltIsTrueOfLt (Nat.le.step isColInTail)]
              | inr isColAtGadgetTop =>
                  -- colIndex = vectorLengthPred: every term vanishes; the target is 0 too.
                  rw [isColAtGadgetTop]
                  refine (sumBelowOfAllZeroIsZero _ (vectorLengthPred + 2) ?_).trans ?_
                  · intro midIndex isMidInBound
                    show mergeRecursionStageEntries vectorLengthPred columnEntries
                        rowIndex midIndex
                      * mergeGadgetStageEntries vectorLengthPred
                          (columnEntries vectorLengthPred) midIndex vectorLengthPred = 0
                    cases ltOrEqOfLtSucc isMidInBound with
                    | inr isMidAtSourceCopy =>
                        rw [isMidAtSourceCopy]
                        rw [show mergeRecursionStageEntries vectorLengthPred columnEntries
                              rowIndex (vectorLengthPred + 1) = 0 from recursionRowEndVanishes]
                        exact zeroMulIsZero _
                    | inl isMidBelowSourceCopy =>
                        cases ltOrEqOfLtSucc isMidBelowSourceCopy with
                        | inr isMidAtGadgetTop =>
                            rw [isMidAtGadgetTop]
                            rw [show mergeGadgetStageEntries vectorLengthPred
                                  (columnEntries vectorLengthPred)
                                  vectorLengthPred vectorLengthPred
                                = denoteEntries
                                    (scaleThenSwapGadget (columnEntries vectorLengthPred)) 0 0
                                  from directSumEntryInBottomBlock _ _ 0 0]
                            rw [gadgetEntryZeroZero]
                            rfl
                        | inl isMidInGadgetIdentity =>
                            rw [show mergeGadgetStageEntries vectorLengthPred
                                  (columnEntries vectorLengthPred) midIndex
                                  vectorLengthPred = 0 from
                              directSumEntryInTopRightBlock _ _ 0 isMidInGadgetIdentity]
                            rfl
                  · show 0 = mergeColumnFanEntries (vectorLengthPred + 1) columnEntries
                        rowIndex vectorLengthPred
                    show 0 = cond (Nat.blt vectorLengthPred (vectorLengthPred + 1))
                        (identityEntries rowIndex vectorLengthPred) (columnEntries rowIndex)
                    rw [bltIsTrueOfLt (Nat.lt_succ_self vectorLengthPred)]
                    rw [identityEntryOffDiagonal
                      (fun isRowAtTop => noLtOfEq isRowAtTop isRowInTail)]
                    rfl
          | inr isColAtSourceCopy =>
              -- colIndex = vectorLengthPred + 1: the column entry; support at the gadget top.
              rw [isColAtSourceCopy]
              refine (sumBelowOfSingleSupport _ (vectorLengthPred + 2) vectorLengthPred
                (Nat.le.step (Nat.lt_succ_self vectorLengthPred)) ?_).trans ?_
              · intro midIndex isMidInBound isMidOffSupport
                show mergeRecursionStageEntries vectorLengthPred columnEntries rowIndex midIndex
                  * mergeGadgetStageEntries vectorLengthPred (columnEntries vectorLengthPred)
                      midIndex (vectorLengthPred + 1) = 0
                cases ltOrEqOfLtSucc isMidInBound with
                | inr isMidAtSourceCopy =>
                    rw [isMidAtSourceCopy]
                    rw [show mergeRecursionStageEntries vectorLengthPred columnEntries
                          rowIndex (vectorLengthPred + 1) = 0 from recursionRowEndVanishes]
                    exact zeroMulIsZero _
                | inl isMidBelowSourceCopy =>
                    cases ltOrEqOfLtSucc isMidBelowSourceCopy with
                    | inr isMidAtGadgetTop => exact absurd isMidAtGadgetTop isMidOffSupport
                    | inl isMidInGadgetIdentity =>
                        rw [show mergeGadgetStageEntries vectorLengthPred
                              (columnEntries vectorLengthPred) midIndex
                              (vectorLengthPred + 1) = 0 from
                          directSumEntryInTopRightBlock _ _ 1 isMidInGadgetIdentity]
                        rfl
              · show mergeRecursionStageEntries vectorLengthPred columnEntries
                    rowIndex vectorLengthPred
                  * mergeGadgetStageEntries vectorLengthPred (columnEntries vectorLengthPred)
                      vectorLengthPred (vectorLengthPred + 1)
                  = mergeColumnFanEntries (vectorLengthPred + 1) columnEntries rowIndex
                      (vectorLengthPred + 1)
                rw [show mergeRecursionStageEntries vectorLengthPred columnEntries
                      rowIndex vectorLengthPred
                    = denoteEntries (mergeColumnFan vectorLengthPred columnEntries)
                        rowIndex vectorLengthPred from
                  directSumEntryInTopBlock _ _ isRowInTail (Nat.lt_succ_self vectorLengthPred)]
                rw [show mergeGadgetStageEntries vectorLengthPred
                      (columnEntries vectorLengthPred) vectorLengthPred
                      (vectorLengthPred + 1)
                    = denoteEntries (scaleThenSwapGadget (columnEntries vectorLengthPred)) 0 1
                      from directSumEntryInBottomBlock _ _ 0 1]
                rw [gadgetEntryZeroOne, mulOneIsSelf]
                rw [inductiveHypothesis columnEntries rowIndex vectorLengthPred isRowInTail
                  (Nat.lt_succ_self vectorLengthPred)]
                show cond (Nat.blt vectorLengthPred vectorLengthPred)
                    (identityEntries rowIndex vectorLengthPred) (columnEntries rowIndex)
                  = cond (Nat.blt (vectorLengthPred + 1) (vectorLengthPred + 1))
                      (identityEntries rowIndex (vectorLengthPred + 1)) (columnEntries rowIndex)
                rw [bltIsFalseOfGe (Nat.le.refl), bltIsFalseOfGe (Nat.le.refl)]
                rfl
      | inr isRowAtLadderTop =>
          -- rowIndex = vectorLengthPred: the freshly merged output row.
          rw [isRowAtLadderTop]
          have mergedRowVanishesLeft : ∀ midIndex, midIndex < vectorLengthPred + 1 ->
              mergeRecursionStageEntries vectorLengthPred columnEntries vectorLengthPred
                midIndex = 0 := fun midIndex isMidInLeft =>
            directSumEntryInBottomLeftBlock _ _ 0 isMidInLeft
          have mergedRowEndIsOne :
              mergeRecursionStageEntries vectorLengthPred columnEntries
                (vectorLengthPred + 0) ((vectorLengthPred + 1) + 0) = identityEntries 0 0 :=
            directSumEntryInBottomBlock _ _ 0 0
          cases ltOrEqOfLtSucc isColInRange with
          | inl isColBelowLadderTop =>
              cases ltOrEqOfLtSucc isColBelowLadderTop with
              | inl isColInTail =>
                  -- colIndex < vectorLengthPred: identity column, off-diagonal: all zero.
                  refine (sumBelowOfAllZeroIsZero _ (vectorLengthPred + 2) ?_).trans ?_
                  · intro midIndex isMidInBound
                    show mergeRecursionStageEntries vectorLengthPred columnEntries
                        vectorLengthPred midIndex
                      * mergeGadgetStageEntries vectorLengthPred
                          (columnEntries vectorLengthPred) midIndex colIndex = 0
                    cases ltOrEqOfLtSucc isMidInBound with
                    | inr isMidAtSourceCopy =>
                        rw [isMidAtSourceCopy]
                        rw [show mergeGadgetStageEntries vectorLengthPred
                              (columnEntries vectorLengthPred)
                              (vectorLengthPred + 1) colIndex = 0 from
                          directSumEntryInBottomLeftBlock _ _ 1 isColInTail]
                        rfl
                    | inl isMidBelowSourceCopy =>
                        rw [mergedRowVanishesLeft midIndex isMidBelowSourceCopy]
                        exact zeroMulIsZero _
                  · show 0 = mergeColumnFanEntries (vectorLengthPred + 1) columnEntries
                        vectorLengthPred colIndex
                    show 0 = cond (Nat.blt colIndex (vectorLengthPred + 1))
                        (identityEntries vectorLengthPred colIndex) (columnEntries vectorLengthPred)
                    rw [bltIsTrueOfLt (Nat.le.step isColInTail)]
                    rw [identityEntryOffDiagonal
                      (fun isTopAtCol => noLtOfEq isTopAtCol.symm isColInTail)]
                    rfl
              | inr isColAtGadgetTop =>
                  -- colIndex = vectorLengthPred: diagonal 1 via the gadget (1,0) entry.
                  rw [isColAtGadgetTop]
                  refine (sumBelowOfSingleSupport _ (vectorLengthPred + 2)
                    (vectorLengthPred + 1) (Nat.lt_succ_self (vectorLengthPred + 1)) ?_).trans ?_
                  · intro midIndex isMidInBound isMidOffSupport
                    show mergeRecursionStageEntries vectorLengthPred columnEntries
                        vectorLengthPred midIndex
                      * mergeGadgetStageEntries vectorLengthPred
                          (columnEntries vectorLengthPred) midIndex vectorLengthPred = 0
                    cases ltOrEqOfLtSucc isMidInBound with
                    | inr isMidAtSourceCopy => exact absurd isMidAtSourceCopy isMidOffSupport
                    | inl isMidBelowSourceCopy =>
                        rw [mergedRowVanishesLeft midIndex isMidBelowSourceCopy]
                        exact zeroMulIsZero _
                  · show mergeRecursionStageEntries vectorLengthPred columnEntries
                        vectorLengthPred (vectorLengthPred + 1)
                      * mergeGadgetStageEntries vectorLengthPred
                          (columnEntries vectorLengthPred) (vectorLengthPred + 1)
                          vectorLengthPred
                      = mergeColumnFanEntries (vectorLengthPred + 1) columnEntries
                          vectorLengthPred vectorLengthPred
                    rw [show mergeRecursionStageEntries vectorLengthPred columnEntries
                          vectorLengthPred (vectorLengthPred + 1) = identityEntries 0 0 from
                      mergedRowEndIsOne]
                    rw [show mergeGadgetStageEntries vectorLengthPred
                          (columnEntries vectorLengthPred) (vectorLengthPred + 1)
                          vectorLengthPred
                        = denoteEntries (scaleThenSwapGadget (columnEntries vectorLengthPred)) 1 0
                          from directSumEntryInBottomBlock _ _ 1 0]
                    rw [gadgetEntryOneZero, identityEntryOnDiagonal 0]
                    show 1 * 1 = mergeColumnFanEntries (vectorLengthPred + 1) columnEntries
                        vectorLengthPred vectorLengthPred
                    show 1 * 1 = cond (Nat.blt vectorLengthPred (vectorLengthPred + 1))
                        (identityEntries vectorLengthPred vectorLengthPred)
                        (columnEntries vectorLengthPred)
                    rw [bltIsTrueOfLt (Nat.lt_succ_self vectorLengthPred),
                      identityEntryOnDiagonal vectorLengthPred]
                    rfl
          | inr isColAtSourceCopy =>
              -- colIndex = vectorLengthPred + 1: the merged output reads the source scaled.
              rw [isColAtSourceCopy]
              refine (sumBelowOfSingleSupport _ (vectorLengthPred + 2)
                (vectorLengthPred + 1) (Nat.lt_succ_self (vectorLengthPred + 1)) ?_).trans ?_
              · intro midIndex isMidInBound isMidOffSupport
                show mergeRecursionStageEntries vectorLengthPred columnEntries
                    vectorLengthPred midIndex
                  * mergeGadgetStageEntries vectorLengthPred (columnEntries vectorLengthPred)
                      midIndex (vectorLengthPred + 1) = 0
                cases ltOrEqOfLtSucc isMidInBound with
                | inr isMidAtSourceCopy => exact absurd isMidAtSourceCopy isMidOffSupport
                | inl isMidBelowSourceCopy =>
                    rw [mergedRowVanishesLeft midIndex isMidBelowSourceCopy]
                    exact zeroMulIsZero _
              · show mergeRecursionStageEntries vectorLengthPred columnEntries
                    vectorLengthPred (vectorLengthPred + 1)
                  * mergeGadgetStageEntries vectorLengthPred (columnEntries vectorLengthPred)
                      (vectorLengthPred + 1) (vectorLengthPred + 1)
                  = mergeColumnFanEntries (vectorLengthPred + 1) columnEntries
                      vectorLengthPred (vectorLengthPred + 1)
                rw [show mergeRecursionStageEntries vectorLengthPred columnEntries
                      vectorLengthPred (vectorLengthPred + 1) = identityEntries 0 0 from
                  mergedRowEndIsOne]
                rw [show mergeGadgetStageEntries vectorLengthPred
                      (columnEntries vectorLengthPred) (vectorLengthPred + 1)
                      (vectorLengthPred + 1)
                    = denoteEntries (scaleThenSwapGadget (columnEntries vectorLengthPred)) 1 1
                      from directSumEntryInBottomBlock _ _ 1 1]
                rw [gadgetEntryOneOne, identityEntryOnDiagonal 0,
                  oneMulIsSelf (columnEntries vectorLengthPred)]
                show columnEntries vectorLengthPred
                  = cond (Nat.blt (vectorLengthPred + 1) (vectorLengthPred + 1))
                      (identityEntries vectorLengthPred (vectorLengthPred + 1))
                      (columnEntries vectorLengthPred)
                rw [bltIsFalseOfGe (Nat.le.refl)]
                rfl

/-- The tensor stage of one canonical fold step, as entries: the shorter canonical diagram
beside the passing fresh strand. -/
def canonicalRecursionStageEntries (sourceArityPred targetArity : Nat)
    (entries : MatrixEntries) : MatrixEntries :=
  directSumEntries targetArity sourceArityPred
    (denoteEntries (canonicalDiagramOfEntries sourceArityPred targetArity entries))
    identityEntries

/-- SOUNDNESS OF THE NORMAL FORM, pointwise: within the `targetArity x sourceArity` rectangle
the canonical diagram denotes exactly the matrix it was built from. -/
theorem canonicalDiagramDenotesEntriesWithin (sourceArity : Nat) :
    ∀ (targetArity : Nat) (entries : MatrixEntries) (rowIndex colIndex : Nat),
      rowIndex < targetArity -> colIndex < sourceArity ->
      denoteEntries (canonicalDiagramOfEntries sourceArity targetArity entries)
          rowIndex colIndex
        = entries rowIndex colIndex := by
  induction sourceArity with
  | zero =>
      intro targetArity entries rowIndex colIndex _ isColBelowZero
      exact absurd isColBelowZero (Nat.not_succ_le_zero colIndex)
  | succ sourceArityPred inductiveHypothesis =>
      intro targetArity entries rowIndex colIndex isRowInRange isColInRange
      show sumBelow (fun midIndex =>
          denoteEntries (mergeColumnFan targetArity (fun mergeRow => entries mergeRow
            sourceArityPred)) rowIndex midIndex
          * canonicalRecursionStageEntries sourceArityPred targetArity entries
              midIndex colIndex)
        (targetArity + 1)
        = entries rowIndex colIndex
      cases ltOrEqOfLtSucc isColInRange with
      | inl isColInEarlierColumns =>
          -- colIndex < sourceArityPred: the recursion carries the value; support at rowIndex.
          refine (sumBelowOfSingleSupport _ (targetArity + 1) rowIndex
            (Nat.le.step isRowInRange) ?_).trans ?_
          · intro midIndex isMidInBound isMidOffSupport
            show denoteEntries (mergeColumnFan targetArity
                  (fun mergeRow => entries mergeRow sourceArityPred)) rowIndex midIndex
              * canonicalRecursionStageEntries sourceArityPred targetArity entries
                  midIndex colIndex = 0
            cases ltOrEqOfLtSucc isMidInBound with
            | inr isMidAtSource =>
                rw [isMidAtSource]
                rw [show canonicalRecursionStageEntries sourceArityPred targetArity entries
                      targetArity colIndex = 0 from
                  directSumEntryInBottomLeftBlock _ _ 0 isColInEarlierColumns]
                rfl
            | inl isMidInOutputs =>
                rw [mergeColumnFanDenotesWithin targetArity
                  (fun mergeRow => entries mergeRow sourceArityPred) rowIndex midIndex
                  isRowInRange (Nat.le.step isMidInOutputs)]
                show cond (Nat.blt midIndex targetArity)
                    (identityEntries rowIndex midIndex)
                    (entries rowIndex sourceArityPred)
                  * canonicalRecursionStageEntries sourceArityPred targetArity entries
                      midIndex colIndex = 0
                rw [bltIsTrueOfLt isMidInOutputs]
                rw [identityEntryOffDiagonal
                  (fun isRowAtMid => isMidOffSupport isRowAtMid.symm)]
                exact zeroMulIsZero _
          · show denoteEntries (mergeColumnFan targetArity
                (fun mergeRow => entries mergeRow sourceArityPred)) rowIndex rowIndex
              * canonicalRecursionStageEntries sourceArityPred targetArity entries
                  rowIndex colIndex
              = entries rowIndex colIndex
            rw [mergeColumnFanDenotesWithin targetArity
              (fun mergeRow => entries mergeRow sourceArityPred) rowIndex rowIndex
              isRowInRange (Nat.le.step isRowInRange)]
            show cond (Nat.blt rowIndex targetArity) (identityEntries rowIndex rowIndex)
                (entries rowIndex sourceArityPred)
              * canonicalRecursionStageEntries sourceArityPred targetArity entries
                  rowIndex colIndex
              = entries rowIndex colIndex
            rw [bltIsTrueOfLt isRowInRange, identityEntryOnDiagonal rowIndex]
            rw [show canonicalRecursionStageEntries sourceArityPred targetArity entries
                  rowIndex colIndex
                = denoteEntries (canonicalDiagramOfEntries sourceArityPred targetArity entries)
                    rowIndex colIndex from
              directSumEntryInTopBlock _ _ isRowInRange isColInEarlierColumns]
            exact (oneMulIsSelf (denoteEntries (canonicalDiagramOfEntries sourceArityPred
                targetArity entries) rowIndex colIndex)).trans
              (inductiveHypothesis targetArity entries rowIndex colIndex isRowInRange
                isColInEarlierColumns)
      | inr isColAtNewestColumn =>
          -- colIndex = sourceArityPred: the fresh strand carries the value; support at the top.
          rw [isColAtNewestColumn]
          refine (sumBelowOfSingleSupport _ (targetArity + 1) targetArity
            (Nat.lt_succ_self targetArity) ?_).trans ?_
          · intro midIndex isMidInBound isMidOffSupport
            show denoteEntries (mergeColumnFan targetArity
                  (fun mergeRow => entries mergeRow sourceArityPred)) rowIndex midIndex
              * canonicalRecursionStageEntries sourceArityPred targetArity entries
                  midIndex sourceArityPred = 0
            cases ltOrEqOfLtSucc isMidInBound with
            | inr isMidAtSource => exact absurd isMidAtSource isMidOffSupport
            | inl isMidInOutputs =>
                rw [show canonicalRecursionStageEntries sourceArityPred targetArity entries
                      midIndex sourceArityPred = 0 from
                  directSumEntryInTopRightBlock _ _ 0 isMidInOutputs]
                rfl
          · show denoteEntries (mergeColumnFan targetArity
                (fun mergeRow => entries mergeRow sourceArityPred)) rowIndex targetArity
              * canonicalRecursionStageEntries sourceArityPred targetArity entries
                  targetArity sourceArityPred
              = entries rowIndex sourceArityPred
            rw [mergeColumnFanDenotesWithin targetArity
              (fun mergeRow => entries mergeRow sourceArityPred) rowIndex targetArity
              isRowInRange (Nat.lt_succ_self targetArity)]
            show cond (Nat.blt targetArity targetArity) (identityEntries rowIndex targetArity)
                (entries rowIndex sourceArityPred)
              * canonicalRecursionStageEntries sourceArityPred targetArity entries
                  targetArity sourceArityPred
              = entries rowIndex sourceArityPred
            rw [bltIsFalseOfGe (Nat.le.refl)]
            rw [show canonicalRecursionStageEntries sourceArityPred targetArity entries
                  targetArity sourceArityPred = identityEntries 0 0 from
              directSumEntryInBottomBlock _ _ 0 0]
            rw [identityEntryOnDiagonal 0]
            exact mulOneIsSelf (entries rowIndex sourceArityPred)

/-! ## Headline theorems: soundness, extensionality, the completeness reduction -/

/-- SOUNDNESS OF THE NORMAL FORM (Bool form): the canonical diagram of any matrix agrees with
that matrix on the full denoted rectangle — kernel-decidable on closed instances, proved here
for ALL matrices and arities. -/
theorem canonicalFormIsSoundOverMatrices (sourceArity targetArity : Nat)
    (entries : MatrixEntries) :
    doEntriesAgreeUpTo targetArity sourceArity
      (denoteEntries (canonicalDiagramOfEntries sourceArity targetArity entries)) entries
      = true :=
  agreeUpToOfPointwise targetArity sourceArity _ entries
    (fun rowIndex colIndex isRowInRange isColInRange =>
      canonicalDiagramDenotesEntriesWithin sourceArity targetArity entries rowIndex colIndex
        isRowInRange isColInRange)

/-- The normal form of a diagram denotes the same matrix as the diagram. -/
theorem normalFormPreservesDenotation {sourceArity targetArity : Nat}
    (diagram : WireDiagram sourceArity targetArity) :
    doEntriesAgreeUpTo targetArity sourceArity
      (denoteEntries (normalFormOfDiagram diagram)) (denoteEntries diagram) = true :=
  canonicalFormIsSoundOverMatrices sourceArity targetArity (denoteEntries diagram)

/-- The ladder reads its column only below the vector length. -/
theorem mergeColumnFanRespectsColumnAgreement (vectorLength : Nat) :
    ∀ (firstColumn secondColumn : Nat -> Nat),
      (∀ rowIndex, rowIndex < vectorLength -> firstColumn rowIndex = secondColumn rowIndex) ->
      mergeColumnFan vectorLength firstColumn = mergeColumnFan vectorLength secondColumn := by
  induction vectorLength with
  | zero => intro _ _ _; rfl
  | succ vectorLengthPred inductiveHypothesis =>
      intro firstColumn secondColumn agreeBelow
      simp only [mergeColumnFan]
      rw [agreeBelow vectorLengthPred (Nat.lt_succ_self vectorLengthPred),
        inductiveHypothesis firstColumn secondColumn
          (fun rowIndex isBelow => agreeBelow rowIndex (Nat.le.step isBelow))]

/-- RECTANGLE EXTENSIONALITY: the canonical diagram is a function of the matrix restricted to
the denoted rectangle — matrices agreeing there give SYNTACTICALLY EQUAL canonical diagrams. -/
theorem canonicalDiagramRespectsRectangleAgreement (sourceArity : Nat) :
    ∀ (targetArity : Nat) (firstEntries secondEntries : MatrixEntries),
      (∀ rowIndex colIndex, rowIndex < targetArity -> colIndex < sourceArity ->
        firstEntries rowIndex colIndex = secondEntries rowIndex colIndex) ->
      canonicalDiagramOfEntries sourceArity targetArity firstEntries
        = canonicalDiagramOfEntries sourceArity targetArity secondEntries := by
  induction sourceArity with
  | zero => intro _ _ _ _; rfl
  | succ sourceArityPred inductiveHypothesis =>
      intro targetArity firstEntries secondEntries agreeOnRectangle
      simp only [canonicalDiagramOfEntries]
      rw [inductiveHypothesis targetArity firstEntries secondEntries
          (fun rowIndex colIndex isRowBelow isColBelow =>
            agreeOnRectangle rowIndex colIndex isRowBelow (Nat.le.step isColBelow)),
        mergeColumnFanRespectsColumnAgreement targetArity
          (fun mergeRow => firstEntries mergeRow sourceArityPred)
          (fun mergeRow => secondEntries mergeRow sourceArityPred)
          (fun rowIndex isRowBelow =>
            agreeOnRectangle rowIndex sourceArityPred isRowBelow
              (Nat.lt_succ_self sourceArityPred))]

/-- EQUAL MATRICES GIVE EQUAL NORMAL FORMS — the syntactic half of completeness: two diagrams
whose denotations agree on the rectangle have the SAME canonical diagram. -/
theorem equalMatricesGiveEqualNormalForms {sourceArity targetArity : Nat}
    (leftDiagram rightDiagram : WireDiagram sourceArity targetArity)
    (doMatricesAgree : doEntriesAgreeUpTo targetArity sourceArity
      (denoteEntries leftDiagram) (denoteEntries rightDiagram) = true) :
    normalFormOfDiagram leftDiagram = normalFormOfDiagram rightDiagram :=
  canonicalDiagramRespectsRectangleAgreement sourceArity targetArity
    (denoteEntries leftDiagram) (denoteEntries rightDiagram)
    (pointwiseOfAgreeUpTo targetArity sourceArity
      (denoteEntries leftDiagram) (denoteEntries rightDiagram) doMatricesAgree)

/-- THE NAMED RESIDUAL (owner false — stated, NOT proven): every diagram is convertible to its
own normal form.  This is the rewrite-system half of [Lafont2003]'s completeness argument
("any diagram reduces to a canonical form"); with it, completeness follows by the reduction
theorem below. -/
def canonicalReductionStatement : Prop :=
  ∀ (sourceArity targetArity : Nat) (diagram : WireDiagram sourceArity targetArity),
    AreConvertibleDiagrams diagram (normalFormOfDiagram diagram)

/-- THE REDUCTION THEOREM: full completeness REDUCES to the canonical-reduction residual.
Given that every diagram converts to its normal form, two diagrams with equal matrices convert
to the SAME normal form (`equalMatricesGiveEqualNormalForms`) and hence to each other. -/
theorem completenessReducesToCanonicalReduction
    (doAllDiagramsReduce : canonicalReductionStatement) : matNatCompletenessStatement := by
  intro sourceArity targetArity leftDiagram rightDiagram doMatricesAgree
  have leftReduces := doAllDiagramsReduce sourceArity targetArity leftDiagram
  have rightReduces := doAllDiagramsReduce sourceArity targetArity rightDiagram
  have formsCoincide := equalMatricesGiveEqualNormalForms leftDiagram rightDiagram
    doMatricesAgree
  rw [formsCoincide] at leftReduces
  exact AreConvertibleDiagrams.fromTransitivity leftReduces
    (AreConvertibleDiagrams.fromSymmetry rightReduces)

/-! ## Closed-instance fires (kernel rfl) -/

/-- Fire: the canonical diagram of the swap matrix denotes the swap matrix (kernel rfl). -/
theorem canonicalFormOfSwapMatrixIsSound :
    doEntriesAgreeUpTo 2 2
      (denoteEntries (canonicalDiagramOfEntries 2 2 swapGenEntries)) swapGenEntries = true := rfl

/-- Fire: the canonical diagram of the doubling matrix [[2]] (the mu-after-delta composite)
denotes [[2]] (kernel rfl). -/
theorem canonicalFormOfDoublingMatrixIsSound :
    doEntriesAgreeUpTo 1 1
      (denoteEntries (canonicalDiagramOfEntries 1 1
        (composeEntries 2 addGenEntries copyGenEntries)))
      (composeEntries 2 addGenEntries copyGenEntries) = true := rfl

/-- Fire: the normal form of the bialgebra-square left side (mu ; delta) has the same matrix as
the diagram itself (kernel rfl through the whole normal-form machine). -/
theorem normalFormOfBimonoidSquareLeftSideIsSound :
    doEntriesAgreeUpTo 2 2
      (denoteEntries (normalFormOfDiagram copyAfterAddLeftSide))
      (denoteEntries copyAfterAddLeftSide) = true := rfl

end FX1Poly.Polygraph.Omega.LafontProp
