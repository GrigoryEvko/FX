/-! # Polygraph/Omega/RelProp/BooleanRelationProp — the cartesian bicategory of relations,
decided by Boolean (OR-AND) matrices (WP-REL)

GREENFIELD LAW: fresh namespace, imports NOTHING from the retired `WalkingBunchedBimonoid*` scope
nor from the sibling `LafontProp` (which is hard-wired to the rig N).  A relation diagram
`sourceArity -> targetArity` denotes a `targetArity x sourceArity` Boolean matrix; the word problem
is decided by Boolean-matrix equality.

## Why a FRESH Boolean kit (the rig flip is the whole point)

The sibling `LafontProp` decides the free bicommutative BIMONOID over the rig N (`Mat(N)`), whose
distinguishing theorem is `copyThenAddDoublesNotIdentity` — copy-then-merge doubles: `mu . delta = 2`.
Over the idempotent Boolean semiring (OR = add, AND = mul, `false` = 0, `true` = 1) that exact
computation FLIPS to `mu . delta = 1` — the SPECIAL Frobenius law (Carboni-Walters "diamond = 1").
So the presentation of `Rel` is the bimonoid presentation PLUS the special law, and the semantics is
`Mat(Bool)`.  The N kit cannot be reused: it is neither generic over a semiring nor over the right
one, and its soundness would be VIOLATED by the special law.  This file builds Boolean OR-AND matrix
arithmetic afresh (bounded, idempotent, no carry — strictly simpler than the N kit) and transports the
diagram/congruence scaffold over it.

## THE SOURCES (the citable presentation)

* [CarboniWalters1987] A. Carboni, R.F.C. Walters, *Cartesian bicategories I*, J. Pure Appl. Algebra
  49 (1987) 11-32: the bicategory of relations of a regular category; each object carries a coherent
  cocommutative comonoid (copy `delta`, delete `epsilon`); the maps are exactly the comonoid
  homomorphisms; `Rel` is the walking cartesian bicategory whose homs are Boolean matrices.
* [Lafont2003] Y. Lafont, *Towards an algebraic theory of Boolean circuits*, J. Pure Appl. Algebra 184
  (2003) 257-310, Section 3: the five generators `tau, delta, epsilon, mu, eta` with matrices
  `[[0,1],[1,0]], [[1],[1]], (0x1), [[1,1]], (1x0)`; "Vertical composition corresponds to the product
  of matrices, and horizontal composition to the direct sum".  His EXTRA relation `mu . delta =
  eta . epsilon`, "specific to Z2", is the special law's shadow; over Bool `mu . delta = id`.
* [BSZ2017] Bonchi-Sobocinski-Zanasi, *Interacting Hopf Algebras*, JPAA 221(1) (2017): the SMT of
  commutative bimonoids (A1)-(A10) = `Span(F)`; the special Frobenius quotient collapses `Span(F)` to
  the PROP of relations `Rel`.
* [Lack2004] S. Lack, *Composing PROPs*, TAC 13 (2004), Section 5.3: `Rel` as the composite of the
  comonoid and monoid PROPs; every relation factors comonoid-then-monoid.
* [RSW2008] Rosebrugh-Sabadini-Walters and the Coya-Fong corelation line: the special-commutative
  Frobenius / bialgebra presentation of `Rel`.

## THE GENERATOR TABLE (diagram `m -> n` denotes an `n x m` Boolean matrix; `.` = OR-of-ANDs product)

  | generator     | arity  | Boolean matrix    | relation             |
  |---------------|--------|-------------------|----------------------|
  | merge  mu     | 2 -> 1 | `[[1,1]]`         | both inputs -> out   |
  | create eta    | 0 -> 1 | `1 x 0` (empty)   | unit slot            |
  | copy   delta  | 1 -> 2 | `[[1],[1]]`       | in -> both outs      |
  | discard eps   | 1 -> 0 | `0 x 1` (empty)   | counit slot          |
  | swap   tau    | 2 -> 2 | `[[0,1],[1,0]]`   | exchange two wires   |
  | cap           | 0 -> 2 | `2 x 0` (empty)   | Frobenius unit       |
  | cup           | 2 -> 0 | `0 x 2` (empty)   | Frobenius counit     |

  Composition = OR-AND Boolean matrix product (second stage on the LEFT); monoidal product =
  block-diagonal direct sum.  The empty-rectangle generators (`create`, `discard`, `cap`, `cup`) all
  denote the unique empty Boolean matrix of their shape: at the linear/matrix level the compact-closed
  content of cap/cup is invisible (both empty), so `cap` and `create;copy` denote the same empty
  `2 x 0` matrix — they are convertible, and the caps/cups carry no separating power over Bool.  What
  DOES separate is the special law `copy;merge = id`, unsound over N, sound and required over Bool.

## WHAT LANDS

* T1 signature + Boolean-matrix semantics: `RelDiagram` carrier over the seven generators;
  `denoteBoolEntries` the strict-monoidal functor to `Mat(Bool)`; well-definedness = the width-checked
  rectangle reading (`denoteBoolEntries` is total, junk-outside-rectangle).
* T2 soundness: the presented congruence `RelConv` (bimonoid rows + symmetry + naturality + the special
  Frobenius law + the cap/cup definitions) is SOUND over `Mat(Bool)` — every row by kernel `rfl`, and
  the full congruence-closure lift `convertibleRelDiagramsDenoteEqualBoolMatrices` by induction over the
  congruence (matrix functoriality: product/direct-sum congruence, composition associativity via the
  OR-Fubini exchange, the middle-four interchange via the block split).
* T3 decision: `decideRelConvBool` = Boolean-matrix equality of the two denotations; SOUNDNESS one
  direction (`decisionIsImpliedByRelConv`, `notRelConvOfDistinctBoolMatrices`).  COMPLETENESS
  (Carboni-Walters: equal Boolean matrix => RelConv) is WALLED — owner marker
  `rcwHasCarboniWaltersCompleteness := false` naming the precise unjoined step and the two burned attacks.

Raw Lean 4 + Init only; zero-axiom; structural recursion only; audit twin with per-decl
`#assert_no_axioms` plus an independent `#print axioms` witness. -/

namespace FX1Poly.Polygraph.Omega.RelProp

/-! ## Section 1 — Boolean OR-AND matrix kit -/

/-- Entries view of a Boolean matrix: `entries rowIndex colIndex` is the coefficient.  Only the
rectangle fixed by the consuming operation is meaningful; entries outside it are junk (`false`). -/
abbrev BoolMatrixEntries : Type := Nat -> Nat -> Bool

/-- The all-`false` matrix (every rectangle of it) — the empty-generator denotation. -/
def falseEntries : BoolMatrixEntries := fun _rowIndex _colIndex => false

/-- The identity Boolean matrix: `true` on the diagonal, `false` elsewhere. -/
def identityBoolEntries : BoolMatrixEntries := fun rowIndex colIndex => Nat.beq rowIndex colIndex

/-- `orBelow termAt bound = termAt 0 || ... || termAt (bound - 1)` — structural on the bound.  The
Boolean semiring's additive fold; idempotent, no carry. -/
def orBelow (termAt : Nat -> Bool) : Nat -> Bool
  | 0 => false
  | boundPred + 1 => orBelow termAt boundPred || termAt boundPred

/-- Boolean matrix product entries.  `composeBoolEntries middleDimension afterEntries beforeEntries`
is the OR-AND product `after . before` where `after` has `middleDimension` columns and `before` has
`middleDimension` rows: entry `(r,c)` = `OR_{k < middleDimension} after r k && before k c`.  In diagram
terms `before` is the FIRST stage, `after` the SECOND. -/
def composeBoolEntries (middleDimension : Nat) (afterEntries beforeEntries : BoolMatrixEntries) :
    BoolMatrixEntries :=
  fun rowIndex colIndex =>
    orBelow (fun middleIndex => afterEntries rowIndex middleIndex && beforeEntries middleIndex colIndex)
      middleDimension

/-- Block-diagonal direct sum (monoidal product): the top-left block is `topRowCount x topColCount`
of `topEntries`; the bottom-right is `bottomEntries` re-based; off-diagonal blocks are `false`. -/
def directSumBoolEntries (topRowCount topColCount : Nat)
    (topEntries bottomEntries : BoolMatrixEntries) : BoolMatrixEntries :=
  fun rowIndex colIndex =>
    cond (Nat.blt rowIndex topRowCount)
      (cond (Nat.blt colIndex topColCount) (topEntries rowIndex colIndex) false)
      (cond (Nat.blt colIndex topColCount) false
        (bottomEntries (rowIndex - topRowCount) (colIndex - topColCount)))

/-! ### The seven generator matrices -/

/-- merge mu : 2 -> 1, the 1x2 matrix `[[1,1]]`. -/
def mergeGenEntries : BoolMatrixEntries :=
  fun rowIndex colIndex => Nat.beq rowIndex 0 && Nat.blt colIndex 2

/-- create eta : 0 -> 1, the empty 1x0 matrix. -/
def createGenEntries : BoolMatrixEntries := falseEntries

/-- copy delta : 1 -> 2, the 2x1 matrix `[[1],[1]]`. -/
def copyGenEntries : BoolMatrixEntries :=
  fun rowIndex colIndex => Nat.beq colIndex 0 && Nat.blt rowIndex 2

/-- discard epsilon : 1 -> 0, the empty 0x1 matrix. -/
def discardGenEntries : BoolMatrixEntries := falseEntries

/-- swap tau : 2 -> 2, the permutation matrix `[[0,1],[1,0]]`. -/
def swapGenEntries : BoolMatrixEntries :=
  fun rowIndex colIndex =>
    (Nat.beq rowIndex 0 && Nat.beq colIndex 1) || (Nat.beq rowIndex 1 && Nat.beq colIndex 0)

/-- cap : 0 -> 2, the empty 2x0 matrix (the Frobenius unit; over Bool = create;copy, empty). -/
def capGenEntries : BoolMatrixEntries := falseEntries

/-- cup : 2 -> 0, the empty 0x2 matrix (the Frobenius counit; over Bool = merge;discard, empty). -/
def cupGenEntries : BoolMatrixEntries := falseEntries

/-! ### Rectangle agreement — the kernel-decidable Boolean matrix equality -/

/-- Boolean equality of two Boolean coefficients (full enumeration — no wildcard arm). -/
def areBoolsEqual : Bool -> Bool -> Bool
  | true, true => true
  | true, false => false
  | false, true => false
  | false, false => true

/-- Do two entry functions agree on row `rowIndex` at all columns below the bound? -/
def doBoolEntriesAgreeOnRow (leftEntries rightEntries : BoolMatrixEntries) (rowIndex : Nat) :
    Nat -> Bool
  | 0 => true
  | colBoundPred + 1 =>
      doBoolEntriesAgreeOnRow leftEntries rightEntries rowIndex colBoundPred
        && areBoolsEqual (leftEntries rowIndex colBoundPred) (rightEntries rowIndex colBoundPred)

/-- Do two entry functions agree on all rows below the bound (each over `colCount` columns)? -/
def doBoolEntriesAgreeOnRows (leftEntries rightEntries : BoolMatrixEntries) (colCount : Nat) :
    Nat -> Bool
  | 0 => true
  | rowBoundPred + 1 =>
      doBoolEntriesAgreeOnRows leftEntries rightEntries colCount rowBoundPred
        && doBoolEntriesAgreeOnRow leftEntries rightEntries rowBoundPred colCount

/-- Do two matrices agree on the full `rowCount x colCount` rectangle?  On closed instances it closes
by kernel `rfl`. -/
def doBoolEntriesAgreeUpTo (rowCount colCount : Nat) (leftEntries rightEntries : BoolMatrixEntries) :
    Bool :=
  doBoolEntriesAgreeOnRows leftEntries rightEntries colCount rowCount

/-! ### Kit smoke fires (kernel rfl) -/

/-- Smoke: tau . tau = identity on the 2x2 rectangle. -/
theorem swapComposeSwapIsIdentity :
    doBoolEntriesAgreeUpTo 2 2 (composeBoolEntries 2 swapGenEntries swapGenEntries)
      identityBoolEntries = true := rfl

/-- THE RIG-FLIP SMOKE: copy-then-merge is the IDENTITY over Bool (`mu . delta = 1`), the special
Frobenius law — the exact `= 2` computation of the N kit collapsing to `= 1` under idempotency. -/
theorem copyThenMergeIsIdentityEntry :
    composeBoolEntries 2 mergeGenEntries copyGenEntries 0 0 = true := rfl

/-- Smoke: copy-then-merge agrees with the identity on the 1x1 rectangle (the special law, matrix
form). -/
theorem copyThenMergeAgreesWithIdentity :
    doBoolEntriesAgreeUpTo 1 1 (composeBoolEntries 2 mergeGenEntries copyGenEntries)
      identityBoolEntries = true := rfl

/-! ## Section 2 — Boolean semiring micro-algebra (all by finite cases, propext-free) -/

theorem orFalse (flag : Bool) : (flag || false) = flag := by cases flag <;> rfl
theorem falseOr (flag : Bool) : (false || flag) = flag := rfl
theorem andFalse (flag : Bool) : (flag && false) = false := by cases flag <;> rfl
theorem falseAnd (flag : Bool) : (false && flag) = false := rfl
theorem andTrue (flag : Bool) : (flag && true) = flag := by cases flag <;> rfl
theorem trueAnd (flag : Bool) : (true && flag) = flag := rfl
theorem orAssoc (firstFlag secondFlag thirdFlag : Bool) :
    ((firstFlag || secondFlag) || thirdFlag) = (firstFlag || (secondFlag || thirdFlag)) := by
  cases firstFlag <;> cases secondFlag <;> cases thirdFlag <;> rfl
theorem andAssoc (firstFlag secondFlag thirdFlag : Bool) :
    ((firstFlag && secondFlag) && thirdFlag) = (firstFlag && (secondFlag && thirdFlag)) := by
  cases firstFlag <;> cases secondFlag <;> cases thirdFlag <;> rfl
theorem andOrDistribLeft (leftFlag firstFlag secondFlag : Bool) :
    (leftFlag && (firstFlag || secondFlag)) = ((leftFlag && firstFlag) || (leftFlag && secondFlag)) := by
  cases leftFlag <;> cases firstFlag <;> cases secondFlag <;> rfl
theorem andOrDistribRight (firstFlag secondFlag rightFlag : Bool) :
    ((firstFlag || secondFlag) && rightFlag) = ((firstFlag && rightFlag) || (secondFlag && rightFlag)) := by
  cases firstFlag <;> cases secondFlag <;> cases rightFlag <;> rfl
theorem orFourExchange (firstFlag secondFlag thirdFlag fourthFlag : Bool) :
    ((firstFlag || secondFlag) || (thirdFlag || fourthFlag))
      = ((firstFlag || thirdFlag) || (secondFlag || fourthFlag)) := by
  cases firstFlag <;> cases secondFlag <;> cases thirdFlag <;> cases fourthFlag <;> rfl

/-- `areBoolsEqual` is reflexive. -/
theorem areBoolsEqualSelf : (flag : Bool) -> areBoolsEqual flag flag = true
  | true => rfl
  | false => rfl

/-- `areBoolsEqual` sound direction. -/
theorem eqOfAreBoolsEqual : {leftFlag rightFlag : Bool} -> areBoolsEqual leftFlag rightFlag = true ->
    leftFlag = rightFlag
  | true, true, _ => rfl
  | false, false, _ => rfl
  | true, false, testHolds => Bool.noConfusion testHolds
  | false, true, testHolds => Bool.noConfusion testHolds

/-! ## Section 3 — Nat index kit (rig-independent; own proofs, no risky core lemmas) -/

theorem beqSelfIsTrue : (valueNat : Nat) -> Nat.beq valueNat valueNat = true
  | 0 => rfl
  | valuePred + 1 => beqSelfIsTrue valuePred

theorem eqOfBeqIsTrue : {leftNat rightNat : Nat} -> Nat.beq leftNat rightNat = true ->
    leftNat = rightNat
  | 0, 0, _ => rfl
  | 0, _ + 1, testHolds => Bool.noConfusion testHolds
  | _ + 1, 0, testHolds => Bool.noConfusion testHolds
  | leftPred + 1, rightPred + 1, testHolds =>
      congrArg Nat.succ (eqOfBeqIsTrue (leftNat := leftPred) (rightNat := rightPred) testHolds)

theorem beqIsFalseOfNe {leftNat rightNat : Nat} (areDifferent : leftNat ≠ rightNat) :
    Nat.beq leftNat rightNat = false := by
  cases beqObserved : Nat.beq leftNat rightNat with
  | false => rfl
  | true => exact absurd (eqOfBeqIsTrue beqObserved) areDifferent

theorem bleIsTrueOfLe : {smallNat bigNat : Nat} -> smallNat ≤ bigNat -> Nat.ble smallNat bigNat = true
  | 0, _, _ => rfl
  | smallPred + 1, 0, isAtMost => absurd isAtMost (Nat.not_succ_le_zero smallPred)
  | smallPred + 1, bigPred + 1, isAtMost =>
      bleIsTrueOfLe (smallNat := smallPred) (bigNat := bigPred) (Nat.le_of_succ_le_succ isAtMost)

theorem leOfBleIsTrue : {smallNat bigNat : Nat} -> Nat.ble smallNat bigNat = true -> smallNat ≤ bigNat
  | 0, bigNat, _ => Nat.zero_le bigNat
  | _ + 1, 0, testHolds => Bool.noConfusion testHolds
  | smallPred + 1, bigPred + 1, testHolds =>
      Nat.succ_le_succ (leOfBleIsTrue (smallNat := smallPred) (bigNat := bigPred) testHolds)

theorem bltIsTrueOfLt {leftNat rightNat : Nat} (isBelow : leftNat < rightNat) :
    Nat.blt leftNat rightNat = true := bleIsTrueOfLe isBelow

theorem ltOfBltIsTrue {leftNat rightNat : Nat} (testHolds : Nat.blt leftNat rightNat = true) :
    leftNat < rightNat := leOfBleIsTrue testHolds

theorem bltIsFalseOfGe {leftNat rightNat : Nat} (isAtMost : rightNat ≤ leftNat) :
    Nat.blt leftNat rightNat = false := by
  cases bltObserved : Nat.blt leftNat rightNat with
  | false => rfl
  | true =>
      exact absurd (Nat.le_trans (ltOfBltIsTrue bltObserved) isAtMost) (Nat.lt_irrefl leftNat)

theorem noLtOfEq {firstNat secondNat : Nat} (areEqual : firstNat = secondNat)
    (isBelow : firstNat < secondNat) : False := by
  cases areEqual
  exact Nat.lt_irrefl firstNat isBelow

theorem noLtOfGe {smallNat bigNat : Nat} (isAtMost : bigNat ≤ smallNat)
    (isBelow : smallNat < bigNat) : False :=
  Nat.lt_irrefl smallNat (Nat.le_trans isBelow isAtMost)

theorem ltOrEqOfLtSucc {smallNat bigNat : Nat} (isBelowSucc : smallNat < bigNat + 1) :
    smallNat < bigNat ∨ smallNat = bigNat :=
  match Nat.le_of_succ_le_succ isBelowSucc with
  | Nat.le.refl => Or.inr rfl
  | Nat.le.step deeperBound => Or.inl (Nat.succ_le_succ deeperBound)

theorem succSubSucc : (subtrahend minuend : Nat) -> (minuend + 1) - (subtrahend + 1) = minuend - subtrahend
  | 0, _ => rfl
  | subPred + 1, minuend => congrArg Nat.pred (succSubSucc subPred minuend)

theorem addSubCancelLeft : (baseNat offsetNat : Nat) -> (baseNat + offsetNat) - baseNat = offsetNat
  | 0, offsetNat => congrArg (fun strippedNat => strippedNat - 0) (Nat.zero_add offsetNat) |>.trans rfl
  | basePred + 1, offsetNat =>
      (congrArg (fun shiftedNat => shiftedNat - (basePred + 1)) (Nat.succ_add basePred offsetNat)).trans
        ((succSubSucc basePred (basePred + offsetNat)).trans (addSubCancelLeft basePred offsetNat))

theorem bleFalseGivesReverseLt : {smallNat bigNat : Nat} -> Nat.ble smallNat bigNat = false ->
    bigNat < smallNat
  | 0, _, testFails => Bool.noConfusion testFails
  | smallPred + 1, 0, _ => Nat.succ_le_succ (Nat.zero_le smallPred)
  | smallPred + 1, bigPred + 1, testFails =>
      Nat.succ_le_succ (bleFalseGivesReverseLt (smallNat := smallPred) (bigNat := bigPred) testFails)

theorem leOfBltIsFalse {leftNat rightNat : Nat} (testFails : Nat.blt leftNat rightNat = false) :
    rightNat ≤ leftNat := Nat.le_of_succ_le_succ (bleFalseGivesReverseLt testFails)

theorem leGivesAddSubCancel : {blockSize indexNat : Nat} -> blockSize ≤ indexNat ->
    blockSize + (indexNat - blockSize) = indexNat
  | 0, indexNat, _ => Nat.zero_add indexNat
  | blockPred + 1, 0, isAtMost => absurd isAtMost (Nat.not_succ_le_zero blockPred)
  | blockPred + 1, indexPred + 1, isAtMost =>
      (congrArg (fun innerNat => (blockPred + 1) + innerNat) (succSubSucc blockPred indexPred)).trans
        ((Nat.succ_add blockPred (indexPred - blockPred)).trans
          (congrArg Nat.succ
            (leGivesAddSubCancel (blockSize := blockPred) (indexNat := indexPred)
              (Nat.le_of_succ_le_succ isAtMost))))

theorem decomposeIndexAgainstBlock (blockSize indexNat : Nat) :
    indexNat < blockSize ∨ ∃ offsetNat, indexNat = blockSize + offsetNat :=
  match bltObserved : Nat.blt indexNat blockSize with
  | true => Or.inl (ltOfBltIsTrue bltObserved)
  | false => Or.inr ⟨indexNat - blockSize, (leGivesAddSubCancel (leOfBltIsFalse bltObserved)).symm⟩

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

theorem ltOfAddLtAddLeft (base : Nat) {firstNat secondNat : Nat}
    (isBelow : base + firstNat < base + secondNat) : firstNat < secondNat :=
  leOfAddLeAddLeft base (firstNat := firstNat + 1) (secondNat := secondNat) isBelow

theorem beqAddLeftCancel : (base leftNat rightNat : Nat) ->
    Nat.beq (base + leftNat) (base + rightNat) = Nat.beq leftNat rightNat
  | 0, leftNat, rightNat => by rw [Nat.zero_add, Nat.zero_add]
  | basePred + 1, leftNat, rightNat => by
      rw [Nat.succ_add basePred leftNat, Nat.succ_add basePred rightNat]
      exact beqAddLeftCancel basePred leftNat rightNat

/-! ## Section 4 — the OR-fold structural kit -/

theorem orBelowRespectsPointwise (firstTermAt secondTermAt : Nat -> Bool) :
    (bound : Nat) ->
    (∀ termIndex, termIndex < bound -> firstTermAt termIndex = secondTermAt termIndex) ->
    orBelow firstTermAt bound = orBelow secondTermAt bound
  | 0, _ => rfl
  | boundPred + 1, agreeBelow => by
      have tailAgrees := orBelowRespectsPointwise firstTermAt secondTermAt boundPred
        (fun termIndex isBelow => agreeBelow termIndex (Nat.le.step isBelow))
      show (orBelow firstTermAt boundPred || firstTermAt boundPred)
        = (orBelow secondTermAt boundPred || secondTermAt boundPred)
      rw [tailAgrees, agreeBelow boundPred (Nat.lt_succ_self boundPred)]

theorem orBelowOfAllFalse (termAt : Nat -> Bool) (bound : Nat)
    (doAllTermsVanish : ∀ termIndex, termIndex < bound -> termAt termIndex = false) :
    orBelow termAt bound = false := by
  induction bound with
  | zero => rfl
  | succ boundPred inductiveHypothesis =>
      have tailVanishes := inductiveHypothesis
        (fun termIndex isBelow => doAllTermsVanish termIndex (Nat.le.step isBelow))
      have headVanishes := doAllTermsVanish boundPred (Nat.lt_succ_self boundPred)
      show (orBelow termAt boundPred || termAt boundPred) = false
      rw [tailVanishes, headVanishes]
      rfl

theorem orBelowOfSingleSupport (termAt : Nat -> Bool) (bound supportIndex : Nat)
    (isSupportInBound : supportIndex < bound)
    (doOtherTermsVanish : ∀ termIndex, termIndex < bound -> termIndex ≠ supportIndex ->
      termAt termIndex = false) :
    orBelow termAt bound = termAt supportIndex := by
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
          show (orBelow termAt boundPred || termAt boundPred) = termAt supportIndex
          rw [tailCollapses, headVanishes]
          exact orFalse (termAt supportIndex)
      | inr isSupportAtHead =>
          have tailVanishes := orBelowOfAllFalse termAt boundPred
            (fun termIndex isInTail =>
              doOtherTermsVanish termIndex (Nat.le.step isInTail)
                (fun isTermSupport => noLtOfEq (isTermSupport.trans isSupportAtHead) isInTail))
          show (orBelow termAt boundPred || termAt boundPred) = termAt supportIndex
          rw [tailVanishes, isSupportAtHead]
          rfl

theorem orBelowSplitsAtBlock (termAt : Nat -> Bool) (blockSize : Nat) :
    (tailSize : Nat) ->
    orBelow termAt (blockSize + tailSize)
      = (orBelow termAt blockSize
        || orBelow (fun offsetIndex => termAt (blockSize + offsetIndex)) tailSize)
  | 0 => (orFalse (orBelow termAt blockSize)).symm
  | tailPred + 1 => by
      show (orBelow termAt (blockSize + tailPred) || termAt (blockSize + tailPred))
        = (orBelow termAt blockSize
          || (orBelow (fun offsetIndex => termAt (blockSize + offsetIndex)) tailPred
            || termAt (blockSize + tailPred)))
      rw [orBelowSplitsAtBlock termAt blockSize tailPred]
      exact orAssoc (orBelow termAt blockSize)
        (orBelow (fun offsetIndex => termAt (blockSize + offsetIndex)) tailPred)
        (termAt (blockSize + tailPred))

theorem orBelowOfPointwiseOr (firstTermAt secondTermAt : Nat -> Bool) :
    (bound : Nat) ->
    orBelow (fun termIndex => firstTermAt termIndex || secondTermAt termIndex) bound
      = (orBelow firstTermAt bound || orBelow secondTermAt bound)
  | 0 => rfl
  | boundPred + 1 => by
      show (orBelow (fun termIndex => firstTermAt termIndex || secondTermAt termIndex) boundPred
          || (firstTermAt boundPred || secondTermAt boundPred))
        = ((orBelow firstTermAt boundPred || firstTermAt boundPred)
          || (orBelow secondTermAt boundPred || secondTermAt boundPred))
      rw [orBelowOfPointwiseOr firstTermAt secondTermAt boundPred]
      exact orFourExchange (orBelow firstTermAt boundPred) (orBelow secondTermAt boundPred)
        (firstTermAt boundPred) (secondTermAt boundPred)

theorem orBelowAndLeft (leftFactor : Bool) (termAt : Nat -> Bool) :
    (bound : Nat) ->
    (leftFactor && orBelow termAt bound)
      = orBelow (fun termIndex => leftFactor && termAt termIndex) bound
  | 0 => andFalse leftFactor
  | boundPred + 1 => by
      show (leftFactor && (orBelow termAt boundPred || termAt boundPred))
        = (orBelow (fun termIndex => leftFactor && termAt termIndex) boundPred
          || (leftFactor && termAt boundPred))
      rw [andOrDistribLeft leftFactor (orBelow termAt boundPred) (termAt boundPred),
        orBelowAndLeft leftFactor termAt boundPred]

theorem orBelowAndRight (termAt : Nat -> Bool) (rightFactor : Bool) :
    (bound : Nat) ->
    (orBelow termAt bound && rightFactor)
      = orBelow (fun termIndex => termAt termIndex && rightFactor) bound
  | 0 => falseAnd rightFactor
  | boundPred + 1 => by
      show ((orBelow termAt boundPred || termAt boundPred) && rightFactor)
        = (orBelow (fun termIndex => termAt termIndex && rightFactor) boundPred
          || (termAt boundPred && rightFactor))
      rw [andOrDistribRight (orBelow termAt boundPred) (termAt boundPred) rightFactor,
        orBelowAndRight termAt rightFactor boundPred]

theorem orBelowExchange (pairTermAt : Nat -> Nat -> Bool) (innerBound : Nat) :
    (outerBound : Nat) ->
    orBelow (fun outerIndex =>
        orBelow (fun innerIndex => pairTermAt outerIndex innerIndex) innerBound) outerBound
      = orBelow (fun innerIndex =>
          orBelow (fun outerIndex => pairTermAt outerIndex innerIndex) outerBound) innerBound
  | 0 => (orBelowOfAllFalse _ innerBound (fun _ _ => rfl)).symm
  | outerPred + 1 => by
      show (orBelow (fun outerIndex =>
            orBelow (fun innerIndex => pairTermAt outerIndex innerIndex) innerBound) outerPred
          || orBelow (fun innerIndex => pairTermAt outerPred innerIndex) innerBound)
        = orBelow (fun innerIndex =>
            orBelow (fun outerIndex => pairTermAt outerIndex innerIndex) (outerPred + 1)) innerBound
      rw [orBelowExchange pairTermAt innerBound outerPred,
        (orBelowOfPointwiseOr
          (fun innerIndex => orBelow (fun outerIndex => pairTermAt outerIndex innerIndex) outerPred)
          (fun innerIndex => pairTermAt outerPred innerIndex) innerBound).symm]
      rfl

/-! ## Section 5 — direct-sum block and identity-entry lemmas over Bool -/

theorem identityBoolOnDiagonal (diagonalIndex : Nat) :
    identityBoolEntries diagonalIndex diagonalIndex = true := beqSelfIsTrue diagonalIndex

theorem identityBoolOffDiagonal {rowIndex colIndex : Nat} (areDifferent : rowIndex ≠ colIndex) :
    identityBoolEntries rowIndex colIndex = false := beqIsFalseOfNe areDifferent

theorem directSumBoolInTopBlock {topRowCount topColCount : Nat}
    (topEntries bottomEntries : BoolMatrixEntries) {rowIndex colIndex : Nat}
    (isRowInTop : rowIndex < topRowCount) (isColInTop : colIndex < topColCount) :
    directSumBoolEntries topRowCount topColCount topEntries bottomEntries rowIndex colIndex
      = topEntries rowIndex colIndex := by
  show cond (Nat.blt rowIndex topRowCount)
      (cond (Nat.blt colIndex topColCount) (topEntries rowIndex colIndex) false)
      (cond (Nat.blt colIndex topColCount) false
        (bottomEntries (rowIndex - topRowCount) (colIndex - topColCount)))
    = topEntries rowIndex colIndex
  rw [bltIsTrueOfLt isRowInTop, bltIsTrueOfLt isColInTop]
  rfl

theorem directSumBoolInBottomBlock {topRowCount topColCount : Nat}
    (topEntries bottomEntries : BoolMatrixEntries) (rowOffset colOffset : Nat) :
    directSumBoolEntries topRowCount topColCount topEntries bottomEntries
      (topRowCount + rowOffset) (topColCount + colOffset) = bottomEntries rowOffset colOffset := by
  show cond (Nat.blt (topRowCount + rowOffset) topRowCount)
      (cond (Nat.blt (topColCount + colOffset) topColCount)
        (topEntries (topRowCount + rowOffset) (topColCount + colOffset)) false)
      (cond (Nat.blt (topColCount + colOffset) topColCount) false
        (bottomEntries ((topRowCount + rowOffset) - topRowCount)
          ((topColCount + colOffset) - topColCount)))
    = bottomEntries rowOffset colOffset
  rw [bltIsFalseOfGe (Nat.le_add_right topRowCount rowOffset),
    bltIsFalseOfGe (Nat.le_add_right topColCount colOffset),
    addSubCancelLeft topRowCount rowOffset, addSubCancelLeft topColCount colOffset]
  rfl

theorem directSumBoolInTopRightBlock {topRowCount topColCount : Nat}
    (topEntries bottomEntries : BoolMatrixEntries) {rowIndex : Nat} (colOffset : Nat)
    (isRowInTop : rowIndex < topRowCount) :
    directSumBoolEntries topRowCount topColCount topEntries bottomEntries
      rowIndex (topColCount + colOffset) = false := by
  show cond (Nat.blt rowIndex topRowCount)
      (cond (Nat.blt (topColCount + colOffset) topColCount)
        (topEntries rowIndex (topColCount + colOffset)) false)
      (cond (Nat.blt (topColCount + colOffset) topColCount) false
        (bottomEntries (rowIndex - topRowCount) ((topColCount + colOffset) - topColCount)))
    = false
  rw [bltIsTrueOfLt isRowInTop, bltIsFalseOfGe (Nat.le_add_right topColCount colOffset)]
  rfl

theorem directSumBoolInBottomLeftBlock {topRowCount topColCount : Nat}
    (topEntries bottomEntries : BoolMatrixEntries) {colIndex : Nat} (rowOffset : Nat)
    (isColInTop : colIndex < topColCount) :
    directSumBoolEntries topRowCount topColCount topEntries bottomEntries
      (topRowCount + rowOffset) colIndex = false := by
  show cond (Nat.blt (topRowCount + rowOffset) topRowCount)
      (cond (Nat.blt colIndex topColCount) (topEntries (topRowCount + rowOffset) colIndex) false)
      (cond (Nat.blt colIndex topColCount) false
        (bottomEntries ((topRowCount + rowOffset) - topRowCount) (colIndex - topColCount)))
    = false
  rw [bltIsFalseOfGe (Nat.le_add_right topRowCount rowOffset), bltIsTrueOfLt isColInTop]
  rfl

/-! ## Section 6 — the pointwise/Bool rectangle-agreement bridge -/

theorem leftIsTrueOfAndTrue {leftFlag rightFlag : Bool} (doBothHold : (leftFlag && rightFlag) = true) :
    leftFlag = true := by
  cases leftFlag with
  | true => rfl
  | false => exact Bool.noConfusion doBothHold

theorem rightIsTrueOfAndTrue {leftFlag rightFlag : Bool} (doBothHold : (leftFlag && rightFlag) = true) :
    rightFlag = true := by
  cases leftFlag with
  | true => exact doBothHold
  | false => exact Bool.noConfusion doBothHold

theorem agreeOnRowOfPointwise (leftEntries rightEntries : BoolMatrixEntries) (rowIndex : Nat)
    (colBound : Nat)
    (agreePointwise : ∀ colIndex, colIndex < colBound ->
      leftEntries rowIndex colIndex = rightEntries rowIndex colIndex) :
    doBoolEntriesAgreeOnRow leftEntries rightEntries rowIndex colBound = true := by
  induction colBound with
  | zero => rfl
  | succ colBoundPred inductiveHypothesis =>
      have tailAgrees := inductiveHypothesis
        (fun colIndex isBelow => agreePointwise colIndex (Nat.le.step isBelow))
      have headAgrees : areBoolsEqual (leftEntries rowIndex colBoundPred)
          (rightEntries rowIndex colBoundPred) = true := by
        rw [agreePointwise colBoundPred (Nat.lt_succ_self colBoundPred)]
        exact areBoolsEqualSelf (rightEntries rowIndex colBoundPred)
      show (doBoolEntriesAgreeOnRow leftEntries rightEntries rowIndex colBoundPred
          && areBoolsEqual (leftEntries rowIndex colBoundPred) (rightEntries rowIndex colBoundPred))
        = true
      rw [tailAgrees, headAgrees]
      rfl

theorem pointwiseOfAgreeOnRow (leftEntries rightEntries : BoolMatrixEntries) (rowIndex : Nat) :
    (colBound : Nat) ->
    doBoolEntriesAgreeOnRow leftEntries rightEntries rowIndex colBound = true ->
    ∀ colIndex, colIndex < colBound -> leftEntries rowIndex colIndex = rightEntries rowIndex colIndex
  | 0, _, colIndex, isBelowZero => absurd isBelowZero (Nat.not_succ_le_zero colIndex)
  | colBoundPred + 1, checkerHolds, colIndex, isBelow => by
      have tailFlag := leftIsTrueOfAndTrue checkerHolds
      have headFlag := rightIsTrueOfAndTrue checkerHolds
      cases ltOrEqOfLtSucc isBelow with
      | inl isInTail =>
          exact pointwiseOfAgreeOnRow leftEntries rightEntries rowIndex colBoundPred tailFlag
            colIndex isInTail
      | inr isAtHead =>
          rw [isAtHead]
          exact eqOfAreBoolsEqual headFlag

theorem agreeOnRowsOfPointwise (leftEntries rightEntries : BoolMatrixEntries) (colCount : Nat)
    (rowBound : Nat)
    (agreePointwise : ∀ rowIndex colIndex, rowIndex < rowBound -> colIndex < colCount ->
      leftEntries rowIndex colIndex = rightEntries rowIndex colIndex) :
    doBoolEntriesAgreeOnRows leftEntries rightEntries colCount rowBound = true := by
  induction rowBound with
  | zero => rfl
  | succ rowBoundPred inductiveHypothesis =>
      have tailAgrees := inductiveHypothesis
        (fun rowIndex colIndex isRowBelow isColBelow =>
          agreePointwise rowIndex colIndex (Nat.le.step isRowBelow) isColBelow)
      have headAgrees := agreeOnRowOfPointwise leftEntries rightEntries rowBoundPred colCount
        (fun colIndex isColBelow =>
          agreePointwise rowBoundPred colIndex (Nat.lt_succ_self rowBoundPred) isColBelow)
      show (doBoolEntriesAgreeOnRows leftEntries rightEntries colCount rowBoundPred
          && doBoolEntriesAgreeOnRow leftEntries rightEntries rowBoundPred colCount) = true
      rw [tailAgrees, headAgrees]
      rfl

theorem pointwiseOfAgreeOnRows (leftEntries rightEntries : BoolMatrixEntries) (colCount : Nat) :
    (rowBound : Nat) ->
    doBoolEntriesAgreeOnRows leftEntries rightEntries colCount rowBound = true ->
    ∀ rowIndex colIndex, rowIndex < rowBound -> colIndex < colCount ->
      leftEntries rowIndex colIndex = rightEntries rowIndex colIndex
  | 0, _, rowIndex, _, isRowBelowZero, _ => absurd isRowBelowZero (Nat.not_succ_le_zero rowIndex)
  | rowBoundPred + 1, checkerHolds, rowIndex, colIndex, isRowBelow, isColBelow => by
      have tailFlag := leftIsTrueOfAndTrue checkerHolds
      have headFlag := rightIsTrueOfAndTrue checkerHolds
      cases ltOrEqOfLtSucc isRowBelow with
      | inl isInTail =>
          exact pointwiseOfAgreeOnRows leftEntries rightEntries colCount rowBoundPred tailFlag
            rowIndex colIndex isInTail isColBelow
      | inr isAtHead =>
          rw [isAtHead]
          exact pointwiseOfAgreeOnRow leftEntries rightEntries rowBoundPred colCount headFlag
            colIndex isColBelow

theorem agreeUpToOfPointwise (rowCount colCount : Nat) (leftEntries rightEntries : BoolMatrixEntries)
    (agreePointwise : ∀ rowIndex colIndex, rowIndex < rowCount -> colIndex < colCount ->
      leftEntries rowIndex colIndex = rightEntries rowIndex colIndex) :
    doBoolEntriesAgreeUpTo rowCount colCount leftEntries rightEntries = true :=
  agreeOnRowsOfPointwise leftEntries rightEntries colCount rowCount agreePointwise

theorem pointwiseOfAgreeUpTo (rowCount colCount : Nat) (leftEntries rightEntries : BoolMatrixEntries)
    (checkerHolds : doBoolEntriesAgreeUpTo rowCount colCount leftEntries rightEntries = true) :
    ∀ rowIndex colIndex, rowIndex < rowCount -> colIndex < colCount ->
      leftEntries rowIndex colIndex = rightEntries rowIndex colIndex :=
  pointwiseOfAgreeOnRows leftEntries rightEntries colCount rowCount checkerHolds

/-! ## Section 7 — the relation-diagram carrier and its Boolean denotation (T1) -/

/-- Formal relation diagrams over the seven Carboni-Walters generators.  A diagram
`sourceArity -> targetArity` denotes a `targetArity x sourceArity` Boolean matrix. -/
inductive RelDiagram : Nat -> Nat -> Type where
  | identityWires : (strandCount : Nat) -> RelDiagram strandCount strandCount
  | composeSequential :
      {sourceArity : Nat} -> {middleArity : Nat} -> {targetArity : Nat} ->
      RelDiagram sourceArity middleArity -> RelDiagram middleArity targetArity ->
      RelDiagram sourceArity targetArity
  | tensorParallel :
      {topSourceArity : Nat} -> {topTargetArity : Nat} ->
      {bottomSourceArity : Nat} -> {bottomTargetArity : Nat} ->
      RelDiagram topSourceArity topTargetArity -> RelDiagram bottomSourceArity bottomTargetArity ->
      RelDiagram (topSourceArity + bottomSourceArity) (topTargetArity + bottomTargetArity)
  | mergeGen : RelDiagram 2 1
  | createGen : RelDiagram 0 1
  | copyGen : RelDiagram 1 2
  | discardGen : RelDiagram 1 0
  | swapGen : RelDiagram 2 2
  | capGen : RelDiagram 0 2
  | cupGen : RelDiagram 2 0

/-- The single identity wire — the workhorse whisker block. -/
def singleWire : RelDiagram 1 1 := RelDiagram.identityWires 1

/-- Matrix denotation: identity to the identity Boolean matrix, sequential composition to the OR-AND
product (second stage on the left), tensor to block-diagonal direct sum, generators to their table
matrices. -/
def denoteBoolEntries : {sourceArity targetArity : Nat} ->
    RelDiagram sourceArity targetArity -> BoolMatrixEntries
  | _, _, RelDiagram.identityWires _ => identityBoolEntries
  | _, _, @RelDiagram.composeSequential _ middleArity _ firstStage secondStage =>
      composeBoolEntries middleArity (denoteBoolEntries secondStage) (denoteBoolEntries firstStage)
  | _, _, @RelDiagram.tensorParallel topSourceArity topTargetArity _ _ topDiagram bottomDiagram =>
      directSumBoolEntries topTargetArity topSourceArity (denoteBoolEntries topDiagram)
        (denoteBoolEntries bottomDiagram)
  | _, _, RelDiagram.mergeGen => mergeGenEntries
  | _, _, RelDiagram.createGen => createGenEntries
  | _, _, RelDiagram.copyGen => copyGenEntries
  | _, _, RelDiagram.discardGen => discardGenEntries
  | _, _, RelDiagram.swapGen => swapGenEntries
  | _, _, RelDiagram.capGen => capGenEntries
  | _, _, RelDiagram.cupGen => cupGenEntries

/-! ### Well-definedness fires: the generator matrices read on their declared rectangle (T1) -/

/-- copy denotes `[[1],[1]]` on the 2x1 rectangle. -/
theorem copyDenotesColumnOfOnes :
    doBoolEntriesAgreeUpTo 2 1 (denoteBoolEntries RelDiagram.copyGen)
      (fun rowIndex _colIndex => Nat.blt rowIndex 2) = true := rfl

/-- merge denotes `[[1,1]]` on the 1x2 rectangle. -/
theorem mergeDenotesRowOfOnes :
    doBoolEntriesAgreeUpTo 1 2 (denoteBoolEntries RelDiagram.mergeGen)
      (fun _rowIndex colIndex => Nat.blt colIndex 2) = true := rfl

/-- cap denotes the empty 2x0 matrix (its rectangle reading is vacuously the all-false matrix). -/
theorem capDenotesEmptyRectangle :
    doBoolEntriesAgreeUpTo 2 0 (denoteBoolEntries RelDiagram.capGen) falseEntries = true := rfl

/-- swap denotes the permutation `[[0,1],[1,0]]` on the 2x2 rectangle. -/
theorem swapDenotesTransposition :
    doBoolEntriesAgreeUpTo 2 2 (denoteBoolEntries RelDiagram.swapGen) swapGenEntries = true := rfl

/-! ## Section 8 — the relation laws (row sides) and per-row Boolean-matrix soundness (T2) -/

/-! ### Named whisker stages -/

def swapBesideWire : RelDiagram 3 3 := RelDiagram.tensorParallel RelDiagram.swapGen singleWire
def wireBesideSwap : RelDiagram 3 3 := RelDiagram.tensorParallel singleWire RelDiagram.swapGen
def mergeBesideWire : RelDiagram 3 2 := RelDiagram.tensorParallel RelDiagram.mergeGen singleWire
def wireBesideMerge : RelDiagram 3 2 := RelDiagram.tensorParallel singleWire RelDiagram.mergeGen
def copyBesideWire : RelDiagram 2 3 := RelDiagram.tensorParallel RelDiagram.copyGen singleWire
def wireBesideCopy : RelDiagram 2 3 := RelDiagram.tensorParallel singleWire RelDiagram.copyGen
def discardBesideWire : RelDiagram 2 1 := RelDiagram.tensorParallel RelDiagram.discardGen singleWire
def wireBesideDiscard : RelDiagram 2 1 := RelDiagram.tensorParallel singleWire RelDiagram.discardGen
def createBesideWire : RelDiagram 1 2 := RelDiagram.tensorParallel RelDiagram.createGen singleWire
def wireBesideCreate : RelDiagram 1 2 := RelDiagram.tensorParallel singleWire RelDiagram.createGen
def copyPairStage : RelDiagram 2 4 := RelDiagram.tensorParallel RelDiagram.copyGen RelDiagram.copyGen
def innerSwapWindowStage : RelDiagram 4 4 :=
  RelDiagram.tensorParallel singleWire (RelDiagram.tensorParallel RelDiagram.swapGen singleWire)
def mergePairStage : RelDiagram 4 2 := RelDiagram.tensorParallel RelDiagram.mergeGen RelDiagram.mergeGen

/-! ### Monoid rows -/

def mergeAssocLeftSide : RelDiagram 3 1 := RelDiagram.composeSequential mergeBesideWire RelDiagram.mergeGen
def mergeAssocRightSide : RelDiagram 3 1 := RelDiagram.composeSequential wireBesideMerge RelDiagram.mergeGen
theorem mergeAssocRowIsSound :
    doBoolEntriesAgreeUpTo 1 3 (denoteBoolEntries mergeAssocLeftSide)
      (denoteBoolEntries mergeAssocRightSide) = true := rfl

def mergeLeftUnitLeftSide : RelDiagram 1 1 := RelDiagram.composeSequential createBesideWire RelDiagram.mergeGen
def mergeLeftUnitRightSide : RelDiagram 1 1 := RelDiagram.identityWires 1
theorem mergeLeftUnitRowIsSound :
    doBoolEntriesAgreeUpTo 1 1 (denoteBoolEntries mergeLeftUnitLeftSide)
      (denoteBoolEntries mergeLeftUnitRightSide) = true := rfl

def mergeRightUnitLeftSide : RelDiagram 1 1 := RelDiagram.composeSequential wireBesideCreate RelDiagram.mergeGen
def mergeRightUnitRightSide : RelDiagram 1 1 := RelDiagram.identityWires 1
theorem mergeRightUnitRowIsSound :
    doBoolEntriesAgreeUpTo 1 1 (denoteBoolEntries mergeRightUnitLeftSide)
      (denoteBoolEntries mergeRightUnitRightSide) = true := rfl

def mergeCommLeftSide : RelDiagram 2 1 := RelDiagram.composeSequential RelDiagram.swapGen RelDiagram.mergeGen
def mergeCommRightSide : RelDiagram 2 1 := RelDiagram.mergeGen
theorem mergeCommRowIsSound :
    doBoolEntriesAgreeUpTo 1 2 (denoteBoolEntries mergeCommLeftSide)
      (denoteBoolEntries mergeCommRightSide) = true := rfl

/-! ### Comonoid rows -/

def copyCoassocLeftSide : RelDiagram 1 3 := RelDiagram.composeSequential RelDiagram.copyGen copyBesideWire
def copyCoassocRightSide : RelDiagram 1 3 := RelDiagram.composeSequential RelDiagram.copyGen wireBesideCopy
theorem copyCoassocRowIsSound :
    doBoolEntriesAgreeUpTo 3 1 (denoteBoolEntries copyCoassocLeftSide)
      (denoteBoolEntries copyCoassocRightSide) = true := rfl

def copyLeftCounitLeftSide : RelDiagram 1 1 := RelDiagram.composeSequential RelDiagram.copyGen discardBesideWire
def copyLeftCounitRightSide : RelDiagram 1 1 := RelDiagram.identityWires 1
theorem copyLeftCounitRowIsSound :
    doBoolEntriesAgreeUpTo 1 1 (denoteBoolEntries copyLeftCounitLeftSide)
      (denoteBoolEntries copyLeftCounitRightSide) = true := rfl

def copyRightCounitLeftSide : RelDiagram 1 1 := RelDiagram.composeSequential RelDiagram.copyGen wireBesideDiscard
def copyRightCounitRightSide : RelDiagram 1 1 := RelDiagram.identityWires 1
theorem copyRightCounitRowIsSound :
    doBoolEntriesAgreeUpTo 1 1 (denoteBoolEntries copyRightCounitLeftSide)
      (denoteBoolEntries copyRightCounitRightSide) = true := rfl

def copyCocommLeftSide : RelDiagram 1 2 := RelDiagram.composeSequential RelDiagram.copyGen RelDiagram.swapGen
def copyCocommRightSide : RelDiagram 1 2 := RelDiagram.copyGen
theorem copyCocommRowIsSound :
    doBoolEntriesAgreeUpTo 2 1 (denoteBoolEntries copyCocommLeftSide)
      (denoteBoolEntries copyCocommRightSide) = true := rfl

/-! ### Bialgebra squares -/

def copyAfterMergeLeftSide : RelDiagram 2 2 := RelDiagram.composeSequential RelDiagram.mergeGen RelDiagram.copyGen
def copyAfterMergeRightSide : RelDiagram 2 2 :=
  RelDiagram.composeSequential (RelDiagram.composeSequential copyPairStage innerSwapWindowStage) mergePairStage
theorem copyAfterMergeRowIsSound :
    doBoolEntriesAgreeUpTo 2 2 (denoteBoolEntries copyAfterMergeLeftSide)
      (denoteBoolEntries copyAfterMergeRightSide) = true := rfl

def copyAfterCreateLeftSide : RelDiagram 0 2 := RelDiagram.composeSequential RelDiagram.createGen RelDiagram.copyGen
def copyAfterCreateRightSide : RelDiagram 0 2 := RelDiagram.tensorParallel RelDiagram.createGen RelDiagram.createGen
theorem copyAfterCreateRowIsSound :
    doBoolEntriesAgreeUpTo 2 0 (denoteBoolEntries copyAfterCreateLeftSide)
      (denoteBoolEntries copyAfterCreateRightSide) = true := rfl

def discardAfterMergeLeftSide : RelDiagram 2 0 := RelDiagram.composeSequential RelDiagram.mergeGen RelDiagram.discardGen
def discardAfterMergeRightSide : RelDiagram 2 0 :=
  RelDiagram.tensorParallel RelDiagram.discardGen RelDiagram.discardGen
theorem discardAfterMergeRowIsSound :
    doBoolEntriesAgreeUpTo 0 2 (denoteBoolEntries discardAfterMergeLeftSide)
      (denoteBoolEntries discardAfterMergeRightSide) = true := rfl

def discardAfterCreateLeftSide : RelDiagram 0 0 := RelDiagram.composeSequential RelDiagram.createGen RelDiagram.discardGen
def discardAfterCreateRightSide : RelDiagram 0 0 := RelDiagram.identityWires 0
theorem discardAfterCreateRowIsSound :
    doBoolEntriesAgreeUpTo 0 0 (denoteBoolEntries discardAfterCreateLeftSide)
      (denoteBoolEntries discardAfterCreateRightSide) = true := rfl

/-! ### Symmetry rows -/

def swapInvolutionLeftSide : RelDiagram 2 2 := RelDiagram.composeSequential RelDiagram.swapGen RelDiagram.swapGen
def swapInvolutionRightSide : RelDiagram 2 2 := RelDiagram.identityWires 2
theorem swapInvolutionRowIsSound :
    doBoolEntriesAgreeUpTo 2 2 (denoteBoolEntries swapInvolutionLeftSide)
      (denoteBoolEntries swapInvolutionRightSide) = true := rfl

def swapYangBaxterLeftSide : RelDiagram 3 3 :=
  RelDiagram.composeSequential (RelDiagram.composeSequential swapBesideWire wireBesideSwap) swapBesideWire
def swapYangBaxterRightSide : RelDiagram 3 3 :=
  RelDiagram.composeSequential (RelDiagram.composeSequential wireBesideSwap swapBesideWire) wireBesideSwap
theorem swapYangBaxterRowIsSound :
    doBoolEntriesAgreeUpTo 3 3 (denoteBoolEntries swapYangBaxterLeftSide)
      (denoteBoolEntries swapYangBaxterRightSide) = true := rfl

/-! ### Naturality rows -/

def swapPastMergeLeftSide : RelDiagram 3 2 := RelDiagram.composeSequential mergeBesideWire RelDiagram.swapGen
def swapPastMergeRightSide : RelDiagram 3 2 :=
  RelDiagram.composeSequential (RelDiagram.composeSequential wireBesideSwap swapBesideWire) wireBesideMerge
theorem swapPastMergeRowIsSound :
    doBoolEntriesAgreeUpTo 2 3 (denoteBoolEntries swapPastMergeLeftSide)
      (denoteBoolEntries swapPastMergeRightSide) = true := rfl

def swapPastCreateLeftSide : RelDiagram 1 2 := RelDiagram.composeSequential createBesideWire RelDiagram.swapGen
def swapPastCreateRightSide : RelDiagram 1 2 := wireBesideCreate
theorem swapPastCreateRowIsSound :
    doBoolEntriesAgreeUpTo 2 1 (denoteBoolEntries swapPastCreateLeftSide)
      (denoteBoolEntries swapPastCreateRightSide) = true := rfl

def copyPastSwapLeftSide : RelDiagram 2 3 := RelDiagram.composeSequential RelDiagram.swapGen copyBesideWire
def copyPastSwapRightSide : RelDiagram 2 3 :=
  RelDiagram.composeSequential (RelDiagram.composeSequential wireBesideCopy swapBesideWire) wireBesideSwap
theorem copyPastSwapRowIsSound :
    doBoolEntriesAgreeUpTo 3 2 (denoteBoolEntries copyPastSwapLeftSide)
      (denoteBoolEntries copyPastSwapRightSide) = true := rfl

def discardPastSwapLeftSide : RelDiagram 2 1 := RelDiagram.composeSequential RelDiagram.swapGen discardBesideWire
def discardPastSwapRightSide : RelDiagram 2 1 := wireBesideDiscard
theorem discardPastSwapRowIsSound :
    doBoolEntriesAgreeUpTo 1 2 (denoteBoolEntries discardPastSwapLeftSide)
      (denoteBoolEntries discardPastSwapRightSide) = true := rfl

/-! ### THE SPECIAL FROBENIUS LAW — the Bool-specific content (`copy;merge = id`) -/

def specialFrobeniusLeftSide : RelDiagram 1 1 := RelDiagram.composeSequential RelDiagram.copyGen RelDiagram.mergeGen
def specialFrobeniusRightSide : RelDiagram 1 1 := RelDiagram.identityWires 1
/-- SPECIAL FROBENIUS soundness over Bool: copy-then-merge denotes the identity `[[1]]`.  Over N this
row is UNSOUND (`= [[2]]`); the idempotent Boolean semiring is precisely what makes it hold — the
Carboni-Walters "diamond = 1". -/
theorem specialFrobeniusRowIsSound :
    doBoolEntriesAgreeUpTo 1 1 (denoteBoolEntries specialFrobeniusLeftSide)
      (denoteBoolEntries specialFrobeniusRightSide) = true := rfl

/-! ### Cap / cup definitions (Frobenius unit/counit as create;copy and merge;discard) -/

def capDefinitionLeftSide : RelDiagram 0 2 := RelDiagram.capGen
def capDefinitionRightSide : RelDiagram 0 2 := RelDiagram.composeSequential RelDiagram.createGen RelDiagram.copyGen
theorem capDefinitionRowIsSound :
    doBoolEntriesAgreeUpTo 2 0 (denoteBoolEntries capDefinitionLeftSide)
      (denoteBoolEntries capDefinitionRightSide) = true := rfl

def cupDefinitionLeftSide : RelDiagram 2 0 := RelDiagram.cupGen
def cupDefinitionRightSide : RelDiagram 2 0 := RelDiagram.composeSequential RelDiagram.mergeGen RelDiagram.discardGen
theorem cupDefinitionRowIsSound :
    doBoolEntriesAgreeUpTo 0 2 (denoteBoolEntries cupDefinitionLeftSide)
      (denoteBoolEntries cupDefinitionRightSide) = true := rfl

/-! ## Section 9 — the presented congruence RelConv and the soundness lift (T2) -/

/-- The smallest congruence on relation diagrams containing the relation rows and the strict-monoidal
structural laws (identities, sequential reassociation, identity-tensor fusion, and the middle-four
interchange — interchange lives HERE as structural glue, never as a relation row).  This is the
Carboni-Walters presentation of `Rel`: bicommutative bimonoid + symmetry + the special Frobenius law
+ the cap/cup definitions. -/
inductive RelConv :
    {sourceArity : Nat} -> {targetArity : Nat} ->
    RelDiagram sourceArity targetArity -> RelDiagram sourceArity targetArity -> Prop where
  | fromReflexivity {sourceArity targetArity : Nat} (diagram : RelDiagram sourceArity targetArity) :
      RelConv diagram diagram
  | fromSymmetry {sourceArity targetArity : Nat}
      {leftDiagram rightDiagram : RelDiagram sourceArity targetArity} :
      RelConv leftDiagram rightDiagram -> RelConv rightDiagram leftDiagram
  | fromTransitivity {sourceArity targetArity : Nat}
      {leftDiagram middleDiagram rightDiagram : RelDiagram sourceArity targetArity} :
      RelConv leftDiagram middleDiagram -> RelConv middleDiagram rightDiagram ->
      RelConv leftDiagram rightDiagram
  | underComposeSequential {sourceArity middleArity targetArity : Nat}
      {firstLeft firstRight : RelDiagram sourceArity middleArity}
      {secondLeft secondRight : RelDiagram middleArity targetArity} :
      RelConv firstLeft firstRight -> RelConv secondLeft secondRight ->
      RelConv (RelDiagram.composeSequential firstLeft secondLeft)
        (RelDiagram.composeSequential firstRight secondRight)
  | underTensorParallel {topSourceArity topTargetArity bottomSourceArity bottomTargetArity : Nat}
      {topLeft topRight : RelDiagram topSourceArity topTargetArity}
      {bottomLeft bottomRight : RelDiagram bottomSourceArity bottomTargetArity} :
      RelConv topLeft topRight -> RelConv bottomLeft bottomRight ->
      RelConv (RelDiagram.tensorParallel topLeft bottomLeft)
        (RelDiagram.tensorParallel topRight bottomRight)
  | composeIdentitySource {sourceArity targetArity : Nat} (diagram : RelDiagram sourceArity targetArity) :
      RelConv (RelDiagram.composeSequential (RelDiagram.identityWires sourceArity) diagram) diagram
  | composeIdentityTarget {sourceArity targetArity : Nat} (diagram : RelDiagram sourceArity targetArity) :
      RelConv (RelDiagram.composeSequential diagram (RelDiagram.identityWires targetArity)) diagram
  | composeReassociate {sourceArity secondArity thirdArity targetArity : Nat}
      (firstStage : RelDiagram sourceArity secondArity)
      (secondStage : RelDiagram secondArity thirdArity)
      (thirdStage : RelDiagram thirdArity targetArity) :
      RelConv
        (RelDiagram.composeSequential (RelDiagram.composeSequential firstStage secondStage) thirdStage)
        (RelDiagram.composeSequential firstStage (RelDiagram.composeSequential secondStage thirdStage))
  | tensorIdentityFusion (topStrandCount bottomStrandCount : Nat) :
      RelConv
        (RelDiagram.tensorParallel (RelDiagram.identityWires topStrandCount)
          (RelDiagram.identityWires bottomStrandCount))
        (RelDiagram.identityWires (topStrandCount + bottomStrandCount))
  | middleFourInterchange {topSourceArity topMiddleArity topTargetArity
      bottomSourceArity bottomMiddleArity bottomTargetArity : Nat}
      (topFirst : RelDiagram topSourceArity topMiddleArity)
      (topSecond : RelDiagram topMiddleArity topTargetArity)
      (bottomFirst : RelDiagram bottomSourceArity bottomMiddleArity)
      (bottomSecond : RelDiagram bottomMiddleArity bottomTargetArity) :
      RelConv
        (RelDiagram.tensorParallel (RelDiagram.composeSequential topFirst topSecond)
          (RelDiagram.composeSequential bottomFirst bottomSecond))
        (RelDiagram.composeSequential (RelDiagram.tensorParallel topFirst bottomFirst)
          (RelDiagram.tensorParallel topSecond bottomSecond))
  | fromMergeAssocRow : RelConv mergeAssocLeftSide mergeAssocRightSide
  | fromMergeLeftUnitRow : RelConv mergeLeftUnitLeftSide mergeLeftUnitRightSide
  | fromMergeRightUnitRow : RelConv mergeRightUnitLeftSide mergeRightUnitRightSide
  | fromMergeCommRow : RelConv mergeCommLeftSide mergeCommRightSide
  | fromCopyCoassocRow : RelConv copyCoassocLeftSide copyCoassocRightSide
  | fromCopyLeftCounitRow : RelConv copyLeftCounitLeftSide copyLeftCounitRightSide
  | fromCopyRightCounitRow : RelConv copyRightCounitLeftSide copyRightCounitRightSide
  | fromCopyCocommRow : RelConv copyCocommLeftSide copyCocommRightSide
  | fromCopyAfterMergeRow : RelConv copyAfterMergeLeftSide copyAfterMergeRightSide
  | fromCopyAfterCreateRow : RelConv copyAfterCreateLeftSide copyAfterCreateRightSide
  | fromDiscardAfterMergeRow : RelConv discardAfterMergeLeftSide discardAfterMergeRightSide
  | fromDiscardAfterCreateRow : RelConv discardAfterCreateLeftSide discardAfterCreateRightSide
  | fromSwapInvolutionRow : RelConv swapInvolutionLeftSide swapInvolutionRightSide
  | fromSwapYangBaxterRow : RelConv swapYangBaxterLeftSide swapYangBaxterRightSide
  | fromSwapPastMergeRow : RelConv swapPastMergeLeftSide swapPastMergeRightSide
  | fromSwapPastCreateRow : RelConv swapPastCreateLeftSide swapPastCreateRightSide
  | fromCopyPastSwapRow : RelConv copyPastSwapLeftSide copyPastSwapRightSide
  | fromDiscardPastSwapRow : RelConv discardPastSwapLeftSide discardPastSwapRightSide
  | fromSpecialFrobeniusRow : RelConv specialFrobeniusLeftSide specialFrobeniusRightSide
  | fromCapDefinitionRow : RelConv capDefinitionLeftSide capDefinitionRightSide
  | fromCupDefinitionRow : RelConv cupDefinitionLeftSide cupDefinitionRightSide

/-- CONVERTIBLE RELATION DIAGRAMS DENOTE EQUAL BOOLEAN MATRICES: the congruence-closure lift of the
per-row soundness fires, by induction over `RelConv` (Boolean matrix functoriality). -/
theorem convertibleRelDiagramsDenoteEqualBoolMatrices {sourceArity targetArity : Nat}
    {leftDiagram rightDiagram : RelDiagram sourceArity targetArity}
    (areConvertible : RelConv leftDiagram rightDiagram) :
    doBoolEntriesAgreeUpTo targetArity sourceArity
      (denoteBoolEntries leftDiagram) (denoteBoolEntries rightDiagram) = true := by
  induction areConvertible with
  | fromReflexivity diagram => exact agreeUpToOfPointwise _ _ _ _ (fun _ _ _ _ => rfl)
  | fromSymmetry _ flippedAgree =>
      exact agreeUpToOfPointwise _ _ _ _
        (fun rowIndex colIndex isRowInRange isColInRange =>
          (pointwiseOfAgreeUpTo _ _ _ _ flippedAgree rowIndex colIndex isRowInRange isColInRange).symm)
  | fromTransitivity _ _ leftAgree rightAgree =>
      exact agreeUpToOfPointwise _ _ _ _
        (fun rowIndex colIndex isRowInRange isColInRange =>
          (pointwiseOfAgreeUpTo _ _ _ _ leftAgree rowIndex colIndex isRowInRange isColInRange).trans
            (pointwiseOfAgreeUpTo _ _ _ _ rightAgree rowIndex colIndex isRowInRange isColInRange))
  | @underComposeSequential innerSourceArity middleArity innerTargetArity
      firstLeft firstRight secondLeft secondRight _ _ firstAgree secondAgree =>
      exact agreeUpToOfPointwise _ _ _ _
        (fun rowIndex colIndex isRowInRange isColInRange =>
          orBelowRespectsPointwise
            (fun midIndex => denoteBoolEntries secondLeft rowIndex midIndex
              && denoteBoolEntries firstLeft midIndex colIndex)
            (fun midIndex => denoteBoolEntries secondRight rowIndex midIndex
              && denoteBoolEntries firstRight midIndex colIndex)
            middleArity
            (fun midIndex isMidInRange => by
              show (denoteBoolEntries secondLeft rowIndex midIndex
                  && denoteBoolEntries firstLeft midIndex colIndex)
                = (denoteBoolEntries secondRight rowIndex midIndex
                  && denoteBoolEntries firstRight midIndex colIndex)
              rw [pointwiseOfAgreeUpTo _ _ _ _ secondAgree rowIndex midIndex isRowInRange isMidInRange,
                pointwiseOfAgreeUpTo _ _ _ _ firstAgree midIndex colIndex isMidInRange isColInRange]))
  | @underTensorParallel topSourceArity topTargetArity bottomSourceArity bottomTargetArity
      topLeft topRight bottomLeft bottomRight _ _ topAgree bottomAgree =>
      refine agreeUpToOfPointwise _ _ _ _
        (fun rowIndex colIndex isRowInRange isColInRange => ?_)
      show directSumBoolEntries topTargetArity topSourceArity
          (denoteBoolEntries topLeft) (denoteBoolEntries bottomLeft) rowIndex colIndex
        = directSumBoolEntries topTargetArity topSourceArity
            (denoteBoolEntries topRight) (denoteBoolEntries bottomRight) rowIndex colIndex
      cases decomposeIndexAgainstBlock topTargetArity rowIndex with
      | inl isRowInTop =>
          cases decomposeIndexAgainstBlock topSourceArity colIndex with
          | inl isColInTop =>
              rw [directSumBoolInTopBlock _ _ isRowInTop isColInTop,
                directSumBoolInTopBlock _ _ isRowInTop isColInTop]
              exact pointwiseOfAgreeUpTo _ _ _ _ topAgree rowIndex colIndex isRowInTop isColInTop
          | inr colHasOffset =>
              cases colHasOffset with
              | intro colOffset colSplits =>
                  rw [colSplits, directSumBoolInTopRightBlock _ _ colOffset isRowInTop,
                    directSumBoolInTopRightBlock _ _ colOffset isRowInTop]
      | inr rowHasOffset =>
          cases rowHasOffset with
          | intro rowOffset rowSplits =>
              cases decomposeIndexAgainstBlock topSourceArity colIndex with
              | inl isColInTop =>
                  rw [rowSplits, directSumBoolInBottomLeftBlock _ _ rowOffset isColInTop,
                    directSumBoolInBottomLeftBlock _ _ rowOffset isColInTop]
              | inr colHasOffset =>
                  cases colHasOffset with
                  | intro colOffset colSplits =>
                      rw [rowSplits] at isRowInRange
                      rw [colSplits] at isColInRange
                      rw [rowSplits, colSplits,
                        directSumBoolInBottomBlock _ _ rowOffset colOffset,
                        directSumBoolInBottomBlock _ _ rowOffset colOffset]
                      exact pointwiseOfAgreeUpTo _ _ _ _ bottomAgree rowOffset colOffset
                        (ltOfAddLtAddLeft topTargetArity isRowInRange)
                        (ltOfAddLtAddLeft topSourceArity isColInRange)
  | @composeIdentitySource innerSourceArity innerTargetArity diagram =>
      refine agreeUpToOfPointwise _ _ _ _
        (fun rowIndex colIndex isRowInRange isColInRange => ?_)
      refine (orBelowOfSingleSupport _ innerSourceArity colIndex isColInRange ?_).trans ?_
      · intro midIndex _ isMidOffSupport
        show (denoteBoolEntries diagram rowIndex midIndex && identityBoolEntries midIndex colIndex) = false
        rw [identityBoolOffDiagonal isMidOffSupport]
        exact andFalse _
      · show (denoteBoolEntries diagram rowIndex colIndex && identityBoolEntries colIndex colIndex)
          = denoteBoolEntries diagram rowIndex colIndex
        rw [identityBoolOnDiagonal colIndex]
        exact andTrue (denoteBoolEntries diagram rowIndex colIndex)
  | @composeIdentityTarget innerSourceArity innerTargetArity diagram =>
      refine agreeUpToOfPointwise _ _ _ _
        (fun rowIndex colIndex isRowInRange isColInRange => ?_)
      refine (orBelowOfSingleSupport _ innerTargetArity rowIndex isRowInRange ?_).trans ?_
      · intro midIndex _ isMidOffSupport
        show (identityBoolEntries rowIndex midIndex && denoteBoolEntries diagram midIndex colIndex) = false
        rw [identityBoolOffDiagonal (fun isRowAtMid => isMidOffSupport isRowAtMid.symm)]
        exact falseAnd _
      · show (identityBoolEntries rowIndex rowIndex && denoteBoolEntries diagram rowIndex colIndex)
          = denoteBoolEntries diagram rowIndex colIndex
        rw [identityBoolOnDiagonal rowIndex]
        exact trueAnd (denoteBoolEntries diagram rowIndex colIndex)
  | @composeReassociate innerSourceArity secondArity thirdArity innerTargetArity
      firstStage secondStage thirdStage =>
      refine agreeUpToOfPointwise _ _ _ _
        (fun rowIndex colIndex isRowInRange isColInRange => ?_)
      show orBelow (fun thirdIndex => denoteBoolEntries thirdStage rowIndex thirdIndex
          && orBelow (fun secondIndex => denoteBoolEntries secondStage thirdIndex secondIndex
              && denoteBoolEntries firstStage secondIndex colIndex) secondArity) thirdArity
        = orBelow (fun secondIndex =>
            orBelow (fun thirdIndex => denoteBoolEntries thirdStage rowIndex thirdIndex
              && denoteBoolEntries secondStage thirdIndex secondIndex) thirdArity
            && denoteBoolEntries firstStage secondIndex colIndex) secondArity
      rw [orBelowRespectsPointwise _
          (fun thirdIndex => orBelow (fun secondIndex =>
            denoteBoolEntries thirdStage rowIndex thirdIndex
              && (denoteBoolEntries secondStage thirdIndex secondIndex
                && denoteBoolEntries firstStage secondIndex colIndex)) secondArity) thirdArity
          (fun thirdIndex _ => orBelowAndLeft (denoteBoolEntries thirdStage rowIndex thirdIndex)
            (fun secondIndex => denoteBoolEntries secondStage thirdIndex secondIndex
              && denoteBoolEntries firstStage secondIndex colIndex) secondArity),
        orBelowExchange (fun thirdIndex secondIndex =>
          denoteBoolEntries thirdStage rowIndex thirdIndex
            && (denoteBoolEntries secondStage thirdIndex secondIndex
              && denoteBoolEntries firstStage secondIndex colIndex)) secondArity thirdArity]
      exact orBelowRespectsPointwise _ _ secondArity
        (fun secondIndex _ => by
          rw [orBelowAndRight (fun thirdIndex =>
              denoteBoolEntries thirdStage rowIndex thirdIndex
                && denoteBoolEntries secondStage thirdIndex secondIndex)
            (denoteBoolEntries firstStage secondIndex colIndex) thirdArity]
          exact orBelowRespectsPointwise _ _ thirdArity
            (fun thirdIndex _ =>
              (andAssoc (denoteBoolEntries thirdStage rowIndex thirdIndex)
                (denoteBoolEntries secondStage thirdIndex secondIndex)
                (denoteBoolEntries firstStage secondIndex colIndex)).symm))
  | tensorIdentityFusion topStrandCount bottomStrandCount =>
      refine agreeUpToOfPointwise _ _ _ _
        (fun rowIndex colIndex isRowInRange isColInRange => ?_)
      show directSumBoolEntries topStrandCount topStrandCount identityBoolEntries identityBoolEntries
          rowIndex colIndex
        = identityBoolEntries rowIndex colIndex
      cases decomposeIndexAgainstBlock topStrandCount rowIndex with
      | inl isRowInTop =>
          cases decomposeIndexAgainstBlock topStrandCount colIndex with
          | inl isColInTop =>
              rw [directSumBoolInTopBlock _ _ isRowInTop isColInTop]
          | inr colHasOffset =>
              cases colHasOffset with
              | intro colOffset colSplits =>
                  rw [colSplits, directSumBoolInTopRightBlock _ _ colOffset isRowInTop,
                    identityBoolOffDiagonal (fun isRowAtOffset => by
                      rw [isRowAtOffset] at isRowInTop
                      exact noLtOfGe (Nat.le_add_right topStrandCount colOffset) isRowInTop)]
      | inr rowHasOffset =>
          cases rowHasOffset with
          | intro rowOffset rowSplits =>
              cases decomposeIndexAgainstBlock topStrandCount colIndex with
              | inl isColInTop =>
                  rw [rowSplits, directSumBoolInBottomLeftBlock _ _ rowOffset isColInTop,
                    identityBoolOffDiagonal (fun isOffsetAtCol => by
                      rw [isOffsetAtCol.symm] at isColInTop
                      exact noLtOfGe (Nat.le_add_right topStrandCount rowOffset) isColInTop)]
              | inr colHasOffset =>
                  cases colHasOffset with
                  | intro colOffset colSplits =>
                      rw [rowSplits, colSplits, directSumBoolInBottomBlock _ _ rowOffset colOffset]
                      show identityBoolEntries rowOffset colOffset
                        = identityBoolEntries (topStrandCount + rowOffset) (topStrandCount + colOffset)
                      show Nat.beq rowOffset colOffset
                        = Nat.beq (topStrandCount + rowOffset) (topStrandCount + colOffset)
                      rw [beqAddLeftCancel topStrandCount rowOffset colOffset]
  | @middleFourInterchange topSourceArity topMiddleArity topTargetArity
      bottomSourceArity bottomMiddleArity bottomTargetArity
      topFirst topSecond bottomFirst bottomSecond =>
      refine agreeUpToOfPointwise _ _ _ _
        (fun rowIndex colIndex isRowInRange isColInRange => ?_)
      show directSumBoolEntries topTargetArity topSourceArity
          (composeBoolEntries topMiddleArity (denoteBoolEntries topSecond) (denoteBoolEntries topFirst))
          (composeBoolEntries bottomMiddleArity (denoteBoolEntries bottomSecond)
            (denoteBoolEntries bottomFirst))
          rowIndex colIndex
        = orBelow (fun midIndex =>
            directSumBoolEntries topTargetArity topMiddleArity
              (denoteBoolEntries topSecond) (denoteBoolEntries bottomSecond) rowIndex midIndex
            && directSumBoolEntries topMiddleArity topSourceArity
                (denoteBoolEntries topFirst) (denoteBoolEntries bottomFirst) midIndex colIndex)
          (topMiddleArity + bottomMiddleArity)
      simp only [orBelowSplitsAtBlock]
      cases decomposeIndexAgainstBlock topTargetArity rowIndex with
      | inl isRowInTop =>
          have tailVanishes : orBelow (fun offsetIndex =>
              directSumBoolEntries topTargetArity topMiddleArity
                (denoteBoolEntries topSecond) (denoteBoolEntries bottomSecond) rowIndex
                (topMiddleArity + offsetIndex)
              && directSumBoolEntries topMiddleArity topSourceArity
                  (denoteBoolEntries topFirst) (denoteBoolEntries bottomFirst)
                  (topMiddleArity + offsetIndex) colIndex) bottomMiddleArity = false :=
            orBelowOfAllFalse _ bottomMiddleArity (fun offsetIndex _ => by
              rw [directSumBoolInTopRightBlock _ _ offsetIndex isRowInTop]
              exact falseAnd _)
          rw [tailVanishes, orFalse]
          cases decomposeIndexAgainstBlock topSourceArity colIndex with
          | inl isColInTop =>
              rw [directSumBoolInTopBlock _ _ isRowInTop isColInTop]
              exact orBelowRespectsPointwise _ _ topMiddleArity
                (fun midIndex isMidInTop => by
                  rw [directSumBoolInTopBlock _ _ isRowInTop isMidInTop,
                    directSumBoolInTopBlock _ _ isMidInTop isColInTop])
          | inr colHasOffset =>
              cases colHasOffset with
              | intro colOffset colSplits =>
                  rw [colSplits, directSumBoolInTopRightBlock _ _ colOffset isRowInTop]
                  exact (orBelowOfAllFalse _ topMiddleArity
                    (fun midIndex isMidInTop => by
                      rw [directSumBoolInTopRightBlock _ _ colOffset isMidInTop]
                      exact andFalse _)).symm
      | inr rowHasOffset =>
          cases rowHasOffset with
          | intro rowOffset rowSplits =>
              have headVanishes : orBelow (fun midIndex =>
                  directSumBoolEntries topTargetArity topMiddleArity
                    (denoteBoolEntries topSecond) (denoteBoolEntries bottomSecond) rowIndex midIndex
                  && directSumBoolEntries topMiddleArity topSourceArity
                      (denoteBoolEntries topFirst) (denoteBoolEntries bottomFirst) midIndex colIndex)
                  topMiddleArity = false :=
                orBelowOfAllFalse _ topMiddleArity (fun midIndex isMidInTop => by
                  rw [rowSplits, directSumBoolInBottomLeftBlock _ _ rowOffset isMidInTop]
                  exact falseAnd _)
              rw [headVanishes, falseOr]
              cases decomposeIndexAgainstBlock topSourceArity colIndex with
              | inl isColInTop =>
                  rw [rowSplits, directSumBoolInBottomLeftBlock _ _ rowOffset isColInTop]
                  exact (orBelowOfAllFalse _ bottomMiddleArity
                    (fun offsetIndex _ => by
                      rw [directSumBoolInBottomLeftBlock _ _ offsetIndex isColInTop]
                      exact andFalse _)).symm
              | inr colHasOffset =>
                  cases colHasOffset with
                  | intro colOffset colSplits =>
                      rw [rowSplits, colSplits, directSumBoolInBottomBlock _ _ rowOffset colOffset]
                      exact orBelowRespectsPointwise _ _ bottomMiddleArity
                        (fun offsetIndex _ => by
                          rw [directSumBoolInBottomBlock _ _ rowOffset offsetIndex,
                            directSumBoolInBottomBlock _ _ offsetIndex colOffset])
  | fromMergeAssocRow => exact mergeAssocRowIsSound
  | fromMergeLeftUnitRow => exact mergeLeftUnitRowIsSound
  | fromMergeRightUnitRow => exact mergeRightUnitRowIsSound
  | fromMergeCommRow => exact mergeCommRowIsSound
  | fromCopyCoassocRow => exact copyCoassocRowIsSound
  | fromCopyLeftCounitRow => exact copyLeftCounitRowIsSound
  | fromCopyRightCounitRow => exact copyRightCounitRowIsSound
  | fromCopyCocommRow => exact copyCocommRowIsSound
  | fromCopyAfterMergeRow => exact copyAfterMergeRowIsSound
  | fromCopyAfterCreateRow => exact copyAfterCreateRowIsSound
  | fromDiscardAfterMergeRow => exact discardAfterMergeRowIsSound
  | fromDiscardAfterCreateRow => exact discardAfterCreateRowIsSound
  | fromSwapInvolutionRow => exact swapInvolutionRowIsSound
  | fromSwapYangBaxterRow => exact swapYangBaxterRowIsSound
  | fromSwapPastMergeRow => exact swapPastMergeRowIsSound
  | fromSwapPastCreateRow => exact swapPastCreateRowIsSound
  | fromCopyPastSwapRow => exact copyPastSwapRowIsSound
  | fromDiscardPastSwapRow => exact discardPastSwapRowIsSound
  | fromSpecialFrobeniusRow => exact specialFrobeniusRowIsSound
  | fromCapDefinitionRow => exact capDefinitionRowIsSound
  | fromCupDefinitionRow => exact cupDefinitionRowIsSound

/-! ## Section 10 — the decision procedure (T3) -/

/-- THE DECISION: two relation diagrams are declared convertible iff their Boolean matrices agree on
the full `targetArity x sourceArity` rectangle. -/
def decideRelConvBool {sourceArity targetArity : Nat}
    (leftDiagram rightDiagram : RelDiagram sourceArity targetArity) : Bool :=
  doBoolEntriesAgreeUpTo targetArity sourceArity
    (denoteBoolEntries leftDiagram) (denoteBoolEntries rightDiagram)

/-- SOUND DIRECTION: convertible diagrams pass the decision. -/
theorem decisionIsImpliedByRelConv {sourceArity targetArity : Nat}
    {leftDiagram rightDiagram : RelDiagram sourceArity targetArity}
    (areConvertible : RelConv leftDiagram rightDiagram) :
    decideRelConvBool leftDiagram rightDiagram = true :=
  convertibleRelDiagramsDenoteEqualBoolMatrices areConvertible

/-- THE NEGATIVE DECISION: diagrams whose Boolean matrices DIFFER are NOT convertible — soundness
contraposed.  This is what makes a `false` matrix comparison a machine-checked refutation of
convertibility (the useful half of the word-problem decision). -/
theorem notRelConvOfDistinctBoolMatrices {sourceArity targetArity : Nat}
    (leftDiagram rightDiagram : RelDiagram sourceArity targetArity)
    (doMatricesDiffer : decideRelConvBool leftDiagram rightDiagram = false) :
    RelConv leftDiagram rightDiagram -> False :=
  fun areConvertible =>
    Bool.noConfusion
      (doMatricesDiffer.symm.trans (convertibleRelDiagramsDenoteEqualBoolMatrices areConvertible))

/-! ## Section 11 — completeness: statement and WALL (T3) -/

/-- THE CARBONI-WALTERS COMPLETENESS STATEMENT (the converse of the decision): equal Boolean matrices
imply RelConv-convertibility.  Stated as the named target; WALLED below. -/
def carboniWaltersCompletenessStatement : Prop :=
  ∀ (sourceArity targetArity : Nat) (leftDiagram rightDiagram : RelDiagram sourceArity targetArity),
    doBoolEntriesAgreeUpTo targetArity sourceArity
      (denoteBoolEntries leftDiagram) (denoteBoolEntries rightDiagram) = true ->
    RelConv leftDiagram rightDiagram

/-- OWNER MARKER (false): the general Carboni-Walters completeness of this presentation is NOT proven
here.

THE PRECISE UNJOINED STEP: the canonical-reduction lemma "every relation diagram is RelConv-convertible
to the canonical diagram of its own Boolean matrix" (`d ~ normalForm d`).  Given that lemma,
completeness is immediate: equal matrices give the SAME canonical diagram, and both sides convert to
it.  The lemma is the rewrite-confluence half of the argument and is not built.

TWO BURNED ATTACKS:
* Attack 1 (canonical/normal-form reduction, [Lafont2003] Sections 2-3 staircase forms): build the
  canonical Boolean diagram of a matrix (an OR-AND analogue of the sibling `LafontProp`
  `canonicalDiagramOfEntries` copy/merge fan tower) and prove every diagram rewrites to it by orienting
  the rows.  The construction transports, but the REDUCTION (`d ~ normalForm d`) hits the same open
  fan-core confluence residual that the sibling N lane leaves as `canonicalReductionStatement`
  (owner false) — the Boolean idempotency collapses the multiplicity fans but does NOT by itself close
  the crossing/naturality rewrite confluence, which needs a terminating Squier-style completion not
  built here.
* Attack 2 (comonoid-then-monoid span factorisation, [BSZ2017] Section 2.2 / [Lack2004] Section 5.3):
  factor every diagram as a comonoid part followed by a monoid part (`n <- p -> m` span form), unique up
  to permutation, then read equal matrices off the factorisation.  Blocks on proving the factorisation
  EXISTS and is unique-up-to-permutation inside RelConv — an induction over diagram structure pushing
  copies past merges via the bialgebra square, whose termination is the same unbuilt completion. -/
def rcwHasCarboniWaltersCompleteness : Bool := false

/-! ## Section 12 — ground fires (T4) -/

/-- FIRE 1: the Boolean matrix of copy (1 -> 2) reads `[[1],[1]]` on its 2x1 rectangle (both output
strands relate to the single input). -/
theorem fireCopyBoolMatrix :
    denoteBoolEntries RelDiagram.copyGen 0 0 = true
      ∧ denoteBoolEntries RelDiagram.copyGen 1 0 = true := ⟨rfl, rfl⟩

/-- FIRE 2: the Boolean matrix of cap (0 -> 2) is the empty 2x0 matrix (vacuous on 0 columns), and cap
is convertible to create;copy. -/
theorem fireCapBoolMatrixAndDefinition :
    doBoolEntriesAgreeUpTo 2 0 (denoteBoolEntries RelDiagram.capGen) falseEntries = true
      ∧ RelConv capDefinitionLeftSide capDefinitionRightSide :=
  ⟨rfl, RelConv.fromCapDefinitionRow⟩

/-- FIRE 3: two convertible diagrams — the special Frobenius pair `copy;merge` and `id1` — decide
`true` (equal Boolean matrices), witnessing the Bool-specific law. -/
theorem fireSpecialFrobeniusDecidesTrue :
    decideRelConvBool specialFrobeniusLeftSide specialFrobeniusRightSide = true
      ∧ RelConv specialFrobeniusLeftSide specialFrobeniusRightSide :=
  ⟨rfl, RelConv.fromSpecialFrobeniusRow⟩

/-- FIRE 4: two NON-convertible diagrams — copy (1 -> 2, matrix `[[1],[1]]`) and create;copy... no:
merge-vs-copy have different arities.  Here: `copy` versus `swap;copy... ` — take copy `1 -> 2`
against the diagram `create-then-copy`?  Use two genuine `2 -> 2` diagrams with different matrices:
the identity id2 versus swap tau.  Their matrices differ (id has `[[1,0],[0,1]]`, tau `[[0,1],[1,0]]`),
so the decision is `false` and they are provably NOT convertible. -/
theorem fireIdentityVersusSwapDecidesFalse :
    decideRelConvBool (RelDiagram.identityWires 2) RelDiagram.swapGen = false :=
  rfl

/-- FIRE 4 (the refutation): identity and swap are NOT RelConv-convertible (distinct Boolean
matrices). -/
theorem fireIdentityNotConvertibleToSwap :
    RelConv (RelDiagram.identityWires 2) RelDiagram.swapGen -> False :=
  notRelConvOfDistinctBoolMatrices (RelDiagram.identityWires 2) RelDiagram.swapGen rfl

end FX1Poly.Polygraph.Omega.RelProp
