/-! # Polygraph/Omega/Quantale/WeightedQuantaleProp — weighted (quantale-enriched) word problems,
decided by matrices over a finite quantale (WP-QUANTALE)

GREENFIELD LAW: fresh namespace, self-contained, imports NOTHING (Init only).  A weighted diagram
`sourceArity -> targetArity` denotes a `targetArity x sourceArity` matrix over a finite quantale; the
weighted word problem is decided by quantale-matrix equality.  This is the third rig-instance beside
the sibling `RelProp` (the 2-element Boolean quantale) and `LafontProp` (the semiring N): the identical
join-of-tensors matrix engine, parameterised over an arbitrary small quantale carrier.

## The finite quantale

The carrier is the 3-element chain `QuantaleThree = bot < mid < top`:

* join `joinQ` = max (the complete-lattice join; `bot` is the least, `top` the greatest),
* tensor `tensorQ` = min, with unit `top` (`top` is the monoidal unit, so `tensorQ top q = q`),
* bottom `bot` (the least element and the tensor annihilator).

This is a genuinely finer instance than Bool: the middle grade `mid` lets weighted diagrams carry
three connection strengths.  Composition of weighted wires TENSORS (mins) their weights — the
Lawvere generalised-metric-space / quantale-enriched-category composition rule.  Every quantale law
(tensor associativity and unitality, tensor distributes over join, bottom annihilation) is a finite
`cases <;> cases <;> rfl` on the small carrier — fully kernel-decidable, propext-free, mirroring the
rcw `orAssoc`/`andOrDistrib*` micro-algebra.

## The sources (the citable structure)

* [Lawvere1973] F.W. Lawvere, *Metric spaces, generalized logic, and closed categories*, Rend. Sem.
  Mat. Fis. Milano 43 (1973): categories enriched in a quantale; a hom-matrix over the quantale, with
  composition the join-of-tensors product.
* [Lafont2003] Y. Lafont, *Towards an algebraic theory of Boolean circuits*, JPAA 184 (2003): the
  matrix semantics "vertical composition = product of matrices, horizontal = direct sum"; the sibling
  `LafontProp` is the N instance, `RelProp` the Bool instance, this file the quantale instance.
* [Rosenthal1990] K.I. Rosenthal, *Quantales and their applications*, Pitman Research Notes 234:
  a quantale is a complete lattice with an associative tensor distributing over arbitrary joins.

## The generator table (diagram `m -> n` denotes an `n x m` quantale matrix; `.` = join-of-tensors)

  | generator       | arity  | quantale matrix       | meaning                     |
  |-----------------|--------|-----------------------|-----------------------------|
  | weight `q`      | 1 -> 1 | `[[q]]`               | a wire weighted by `q`      |
  | copy  delta     | 1 -> 2 | `[[top],[top]]`       | in -> both outs             |
  | merge mu        | 2 -> 1 | `[[top,top]]`         | both inputs -> out          |
  | swap  tau       | 2 -> 2 | `[[bot,top],[top,bot]]`| exchange two wires         |

  Composition = join-of-tensors matrix product (second stage on the LEFT); monoidal product =
  block-diagonal direct sum.  The distinguishing weighted law is `weight a ; weight b = weight (b (x) a)`:
  composing weighted wires tensors their weights.

## What lands

* T1 signature + quantale-matrix semantics: `QuantaleThree` carrier with all quantale laws by finite
  cases; `WeightedDiagram` over the four generators; `denoteQEntries` the strict-monoidal functor to
  `Mat(QuantaleThree)`; well-definedness = the width-checked rectangle reading.
* T2 soundness: the presented congruence `WeightedConv` (strict-monoidal glue + the weighted rows) is
  SOUND — every row by kernel `rfl` / a carrier lemma, and the full congruence-closure lift
  `convertibleWeightedDiagramsDenoteEqualQMatrices` by induction (quantale-matrix functoriality: the
  join-of-tensors Fubini exchange + the direct-sum block lemmas).
* T3 decision: `decideWeightedConvBool` = quantale-matrix equality of the two denotations;
  `decisionIsImpliedByWeightedConv` (convertible => decides true) and
  `notWeightedConvOfDistinctQMatrices` (distinct quantale matrices => NOT convertible).
* T4 completeness WALL: presentation completeness (equal quantale matrix => WeightedConv) is the
  quantale analogue of the walled Carboni-Walters / Lafont completeness — owner marker
  `qwmHasQuantalePresentationCompleteness := false` naming the canonical-reduction obstruction and two
  burned attacks.

Raw Lean 4 + Init only; zero-axiom; structural recursion on `Nat` bounds only; audit twin with
per-decl `#assert_no_axioms` plus an independent `#print axioms` witness. -/

namespace FX1Poly.Polygraph.Omega.QuantaleProp

/-! ## Section 1 — the finite quantale carrier and its laws (all by finite cases) -/

/-- The 3-element chain quantale carrier `bot < mid < top`. -/
inductive QuantaleThree : Type where
  | bot
  | mid
  | top

/-- Join = max on the chain (the complete-lattice join), full 9-case enumeration (no wildcard). -/
def joinQ : QuantaleThree → QuantaleThree → QuantaleThree
  | QuantaleThree.bot, QuantaleThree.bot => QuantaleThree.bot
  | QuantaleThree.bot, QuantaleThree.mid => QuantaleThree.mid
  | QuantaleThree.bot, QuantaleThree.top => QuantaleThree.top
  | QuantaleThree.mid, QuantaleThree.bot => QuantaleThree.mid
  | QuantaleThree.mid, QuantaleThree.mid => QuantaleThree.mid
  | QuantaleThree.mid, QuantaleThree.top => QuantaleThree.top
  | QuantaleThree.top, QuantaleThree.bot => QuantaleThree.top
  | QuantaleThree.top, QuantaleThree.mid => QuantaleThree.top
  | QuantaleThree.top, QuantaleThree.top => QuantaleThree.top

/-- Tensor = min on the chain, monoidal unit `top`; full 9-case enumeration. -/
def tensorQ : QuantaleThree → QuantaleThree → QuantaleThree
  | QuantaleThree.bot, QuantaleThree.bot => QuantaleThree.bot
  | QuantaleThree.bot, QuantaleThree.mid => QuantaleThree.bot
  | QuantaleThree.bot, QuantaleThree.top => QuantaleThree.bot
  | QuantaleThree.mid, QuantaleThree.bot => QuantaleThree.bot
  | QuantaleThree.mid, QuantaleThree.mid => QuantaleThree.mid
  | QuantaleThree.mid, QuantaleThree.top => QuantaleThree.mid
  | QuantaleThree.top, QuantaleThree.bot => QuantaleThree.bot
  | QuantaleThree.top, QuantaleThree.mid => QuantaleThree.mid
  | QuantaleThree.top, QuantaleThree.top => QuantaleThree.top

/-- Decidable-equality-as-`Bool` on the carrier, full 9-case enumeration (no wildcard → propext-free). -/
def areQEqual : QuantaleThree → QuantaleThree → Bool
  | QuantaleThree.bot, QuantaleThree.bot => true
  | QuantaleThree.bot, QuantaleThree.mid => false
  | QuantaleThree.bot, QuantaleThree.top => false
  | QuantaleThree.mid, QuantaleThree.bot => false
  | QuantaleThree.mid, QuantaleThree.mid => true
  | QuantaleThree.mid, QuantaleThree.top => false
  | QuantaleThree.top, QuantaleThree.bot => false
  | QuantaleThree.top, QuantaleThree.mid => false
  | QuantaleThree.top, QuantaleThree.top => true

/-! ### The quantale laws (mirroring the rcw Boolean micro-algebra `orFalse`/`andOrDistrib*`) -/

theorem joinBotQ (element : QuantaleThree) : joinQ element QuantaleThree.bot = element := by
  cases element <;> rfl
theorem botJoinQ (element : QuantaleThree) : joinQ QuantaleThree.bot element = element := by
  cases element <;> rfl
theorem tensorBotQ (element : QuantaleThree) : tensorQ element QuantaleThree.bot = QuantaleThree.bot := by
  cases element <;> rfl
theorem botTensorQ (element : QuantaleThree) : tensorQ QuantaleThree.bot element = QuantaleThree.bot := by
  cases element <;> rfl
theorem tensorTopQ (element : QuantaleThree) : tensorQ element QuantaleThree.top = element := by
  cases element <;> rfl
theorem topTensorQ (element : QuantaleThree) : tensorQ QuantaleThree.top element = element := by
  cases element <;> rfl
theorem joinAssocQ (firstElement secondElement thirdElement : QuantaleThree) :
    joinQ (joinQ firstElement secondElement) thirdElement
      = joinQ firstElement (joinQ secondElement thirdElement) := by
  cases firstElement <;> cases secondElement <;> cases thirdElement <;> rfl
theorem tensorAssocQ (firstElement secondElement thirdElement : QuantaleThree) :
    tensorQ (tensorQ firstElement secondElement) thirdElement
      = tensorQ firstElement (tensorQ secondElement thirdElement) := by
  cases firstElement <;> cases secondElement <;> cases thirdElement <;> rfl
theorem tensorJoinDistribLeftQ (leftElement firstElement secondElement : QuantaleThree) :
    tensorQ leftElement (joinQ firstElement secondElement)
      = joinQ (tensorQ leftElement firstElement) (tensorQ leftElement secondElement) := by
  cases leftElement <;> cases firstElement <;> cases secondElement <;> rfl
theorem tensorJoinDistribRightQ (firstElement secondElement rightElement : QuantaleThree) :
    tensorQ (joinQ firstElement secondElement) rightElement
      = joinQ (tensorQ firstElement rightElement) (tensorQ secondElement rightElement) := by
  cases firstElement <;> cases secondElement <;> cases rightElement <;> rfl
theorem joinFourExchangeQ (firstElement secondElement thirdElement fourthElement : QuantaleThree) :
    joinQ (joinQ firstElement secondElement) (joinQ thirdElement fourthElement)
      = joinQ (joinQ firstElement thirdElement) (joinQ secondElement fourthElement) := by
  cases firstElement <;> cases secondElement <;> cases thirdElement <;> cases fourthElement <;> rfl

/-- `areQEqual` is reflexive. -/
theorem areQEqualSelf : (element : QuantaleThree) → areQEqual element element = true
  | QuantaleThree.bot => rfl
  | QuantaleThree.mid => rfl
  | QuantaleThree.top => rfl

/-- `areQEqual` sound direction (full enumeration; the false-off-diagonal arms are `noConfusion`). -/
theorem eqOfAreQEqual : {leftElement rightElement : QuantaleThree} →
    areQEqual leftElement rightElement = true → leftElement = rightElement
  | QuantaleThree.bot, QuantaleThree.bot, _ => rfl
  | QuantaleThree.mid, QuantaleThree.mid, _ => rfl
  | QuantaleThree.top, QuantaleThree.top, _ => rfl
  | QuantaleThree.bot, QuantaleThree.mid, testHolds => Bool.noConfusion testHolds
  | QuantaleThree.bot, QuantaleThree.top, testHolds => Bool.noConfusion testHolds
  | QuantaleThree.mid, QuantaleThree.bot, testHolds => Bool.noConfusion testHolds
  | QuantaleThree.mid, QuantaleThree.top, testHolds => Bool.noConfusion testHolds
  | QuantaleThree.top, QuantaleThree.bot, testHolds => Bool.noConfusion testHolds
  | QuantaleThree.top, QuantaleThree.mid, testHolds => Bool.noConfusion testHolds

/-! ## Section 2 — quantale-matrix kit -/

/-- Entries view of a quantale matrix: `entries rowIndex colIndex` is the coefficient.  Only the
rectangle fixed by the consuming operation is meaningful; entries outside it are junk (`bot`). -/
abbrev QMatrixEntries : Type := Nat → Nat → QuantaleThree

/-- The all-`bot` matrix (the bottom matrix). -/
def botEntries : QMatrixEntries := fun _rowIndex _colIndex => QuantaleThree.bot

/-- The identity quantale matrix: `top` (the tensor unit) on the diagonal, `bot` elsewhere. -/
def identityQEntries : QMatrixEntries :=
  fun rowIndex colIndex => cond (Nat.beq rowIndex colIndex) QuantaleThree.top QuantaleThree.bot

/-- `joinBelowQ termAt bound = termAt 0 (v) ... (v) termAt (bound - 1)` — the quantale additive fold. -/
def joinBelowQ (termAt : Nat → QuantaleThree) : Nat → QuantaleThree
  | 0 => QuantaleThree.bot
  | boundPred + 1 => joinQ (joinBelowQ termAt boundPred) (termAt boundPred)

/-- Quantale matrix product entries.  `composeQEntries middleDimension afterEntries beforeEntries` is
the join-of-tensors product `after . before`: entry `(r,c)` = join over `k < middleDimension` of
`after r k (x) before k c`.  In diagram terms `before` is the FIRST stage, `after` the SECOND. -/
def composeQEntries (middleDimension : Nat) (afterEntries beforeEntries : QMatrixEntries) :
    QMatrixEntries :=
  fun rowIndex colIndex =>
    joinBelowQ (fun middleIndex => tensorQ (afterEntries rowIndex middleIndex)
      (beforeEntries middleIndex colIndex)) middleDimension

/-- Block-diagonal direct sum (monoidal product): top-left block `topRowCount x topColCount` of
`topEntries`; bottom-right `bottomEntries` re-based; off-diagonal blocks `bot`. -/
def directSumQEntries (topRowCount topColCount : Nat)
    (topEntries bottomEntries : QMatrixEntries) : QMatrixEntries :=
  fun rowIndex colIndex =>
    cond (Nat.blt rowIndex topRowCount)
      (cond (Nat.blt colIndex topColCount) (topEntries rowIndex colIndex) QuantaleThree.bot)
      (cond (Nat.blt colIndex topColCount) QuantaleThree.bot
        (bottomEntries (rowIndex - topRowCount) (colIndex - topColCount)))

/-! ### The four generator matrices -/

/-- weight `q` : 1 -> 1, the 1x1 matrix `[[q]]`. -/
def weightGenQEntries (weight : QuantaleThree) : QMatrixEntries :=
  fun rowIndex colIndex => cond (Nat.beq rowIndex 0 && Nat.beq colIndex 0) weight QuantaleThree.bot

/-- copy delta : 1 -> 2, the 2x1 matrix `[[top],[top]]`. -/
def copyGenQEntries : QMatrixEntries :=
  fun rowIndex colIndex => cond (Nat.beq colIndex 0 && Nat.blt rowIndex 2) QuantaleThree.top QuantaleThree.bot

/-- merge mu : 2 -> 1, the 1x2 matrix `[[top,top]]`. -/
def mergeGenQEntries : QMatrixEntries :=
  fun rowIndex colIndex => cond (Nat.beq rowIndex 0 && Nat.blt colIndex 2) QuantaleThree.top QuantaleThree.bot

/-- swap tau : 2 -> 2, the permutation matrix `[[bot,top],[top,bot]]`. -/
def swapGenQEntries : QMatrixEntries :=
  fun rowIndex colIndex =>
    cond ((Nat.beq rowIndex 0 && Nat.beq colIndex 1) || (Nat.beq rowIndex 1 && Nat.beq colIndex 0))
      QuantaleThree.top QuantaleThree.bot

/-! ### Rectangle agreement — the kernel-decidable quantale-matrix equality -/

/-- Do two entry functions agree on row `rowIndex` at all columns below the bound? -/
def doQEntriesAgreeOnRow (leftEntries rightEntries : QMatrixEntries) (rowIndex : Nat) :
    Nat → Bool
  | 0 => true
  | colBoundPred + 1 =>
      doQEntriesAgreeOnRow leftEntries rightEntries rowIndex colBoundPred
        && areQEqual (leftEntries rowIndex colBoundPred) (rightEntries rowIndex colBoundPred)

/-- Do two entry functions agree on all rows below the bound (each over `colCount` columns)? -/
def doQEntriesAgreeOnRows (leftEntries rightEntries : QMatrixEntries) (colCount : Nat) :
    Nat → Bool
  | 0 => true
  | rowBoundPred + 1 =>
      doQEntriesAgreeOnRows leftEntries rightEntries colCount rowBoundPred
        && doQEntriesAgreeOnRow leftEntries rightEntries rowBoundPred colCount

/-- Do two matrices agree on the full `rowCount x colCount` rectangle?  Closed by kernel `rfl` on
closed instances. -/
def doQEntriesAgreeUpTo (rowCount colCount : Nat) (leftEntries rightEntries : QMatrixEntries) :
    Bool :=
  doQEntriesAgreeOnRows leftEntries rightEntries colCount rowCount

/-! ### Kit smoke fires (kernel rfl) -/

/-- Smoke: tau . tau = identity on the 2x2 rectangle. -/
theorem swapComposeSwapIsIdentity :
    doQEntriesAgreeUpTo 2 2 (composeQEntries 2 swapGenQEntries swapGenQEntries)
      identityQEntries = true := rfl

/-- Smoke: copy-then-merge is the IDENTITY over the quantale (`mu . delta = 1`), the special law,
holding because join is idempotent. -/
theorem copyThenMergeAgreesWithIdentity :
    doQEntriesAgreeUpTo 1 1 (composeQEntries 2 mergeGenQEntries copyGenQEntries)
      identityQEntries = true := rfl

/-! ## Section 3 — Nat index kit (carrier-independent; own proofs, no risky core lemmas) -/

theorem beqSelfIsTrue : (valueNat : Nat) → Nat.beq valueNat valueNat = true
  | 0 => rfl
  | valuePred + 1 => beqSelfIsTrue valuePred

theorem eqOfBeqIsTrue : {leftNat rightNat : Nat} → Nat.beq leftNat rightNat = true →
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

theorem bleIsTrueOfLe : {smallNat bigNat : Nat} → smallNat ≤ bigNat → Nat.ble smallNat bigNat = true
  | 0, _, _ => rfl
  | smallPred + 1, 0, isAtMost => absurd isAtMost (Nat.not_succ_le_zero smallPred)
  | smallPred + 1, bigPred + 1, isAtMost =>
      bleIsTrueOfLe (smallNat := smallPred) (bigNat := bigPred) (Nat.le_of_succ_le_succ isAtMost)

theorem leOfBleIsTrue : {smallNat bigNat : Nat} → Nat.ble smallNat bigNat = true → smallNat ≤ bigNat
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

theorem succSubSucc : (subtrahend minuend : Nat) → (minuend + 1) - (subtrahend + 1) = minuend - subtrahend
  | 0, _ => rfl
  | subPred + 1, minuend => congrArg Nat.pred (succSubSucc subPred minuend)

theorem addSubCancelLeft : (baseNat offsetNat : Nat) → (baseNat + offsetNat) - baseNat = offsetNat
  | 0, offsetNat => congrArg (fun strippedNat => strippedNat - 0) (Nat.zero_add offsetNat) |>.trans rfl
  | basePred + 1, offsetNat =>
      (congrArg (fun shiftedNat => shiftedNat - (basePred + 1)) (Nat.succ_add basePred offsetNat)).trans
        ((succSubSucc basePred (basePred + offsetNat)).trans (addSubCancelLeft basePred offsetNat))

theorem bleFalseGivesReverseLt : {smallNat bigNat : Nat} → Nat.ble smallNat bigNat = false →
    bigNat < smallNat
  | 0, _, testFails => Bool.noConfusion testFails
  | smallPred + 1, 0, _ => Nat.succ_le_succ (Nat.zero_le smallPred)
  | smallPred + 1, bigPred + 1, testFails =>
      Nat.succ_le_succ (bleFalseGivesReverseLt (smallNat := smallPred) (bigNat := bigPred) testFails)

theorem leOfBltIsFalse {leftNat rightNat : Nat} (testFails : Nat.blt leftNat rightNat = false) :
    rightNat ≤ leftNat := Nat.le_of_succ_le_succ (bleFalseGivesReverseLt testFails)

theorem leGivesAddSubCancel : {blockSize indexNat : Nat} → blockSize ≤ indexNat →
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
    base + firstNat ≤ base + secondNat → firstNat ≤ secondNat := by
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

theorem beqAddLeftCancel : (base leftNat rightNat : Nat) →
    Nat.beq (base + leftNat) (base + rightNat) = Nat.beq leftNat rightNat
  | 0, leftNat, rightNat => by rw [Nat.zero_add, Nat.zero_add]
  | basePred + 1, leftNat, rightNat => by
      rw [Nat.succ_add basePred leftNat, Nat.succ_add basePred rightNat]
      exact beqAddLeftCancel basePred leftNat rightNat

/-! ## Section 4 — the join-below structural fold kit (ported to the quantale) -/

theorem joinBelowQRespectsPointwise (firstTermAt secondTermAt : Nat → QuantaleThree) :
    (bound : Nat) →
    (∀ termIndex, termIndex < bound → firstTermAt termIndex = secondTermAt termIndex) →
    joinBelowQ firstTermAt bound = joinBelowQ secondTermAt bound
  | 0, _ => rfl
  | boundPred + 1, agreeBelow => by
      have tailAgrees := joinBelowQRespectsPointwise firstTermAt secondTermAt boundPred
        (fun termIndex isBelow => agreeBelow termIndex (Nat.le.step isBelow))
      show joinQ (joinBelowQ firstTermAt boundPred) (firstTermAt boundPred)
        = joinQ (joinBelowQ secondTermAt boundPred) (secondTermAt boundPred)
      rw [tailAgrees, agreeBelow boundPred (Nat.lt_succ_self boundPred)]

theorem joinBelowQOfAllBot (termAt : Nat → QuantaleThree) (bound : Nat)
    (doAllTermsVanish : ∀ termIndex, termIndex < bound → termAt termIndex = QuantaleThree.bot) :
    joinBelowQ termAt bound = QuantaleThree.bot := by
  induction bound with
  | zero => rfl
  | succ boundPred inductiveHypothesis =>
      have tailVanishes := inductiveHypothesis
        (fun termIndex isBelow => doAllTermsVanish termIndex (Nat.le.step isBelow))
      have headVanishes := doAllTermsVanish boundPred (Nat.lt_succ_self boundPred)
      show joinQ (joinBelowQ termAt boundPred) (termAt boundPred) = QuantaleThree.bot
      rw [tailVanishes, headVanishes]
      rfl

theorem joinBelowQOfSingleSupport (termAt : Nat → QuantaleThree) (bound supportIndex : Nat)
    (isSupportInBound : supportIndex < bound)
    (doOtherTermsVanish : ∀ termIndex, termIndex < bound → termIndex ≠ supportIndex →
      termAt termIndex = QuantaleThree.bot) :
    joinBelowQ termAt bound = termAt supportIndex := by
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
          show joinQ (joinBelowQ termAt boundPred) (termAt boundPred) = termAt supportIndex
          rw [tailCollapses, headVanishes]
          exact joinBotQ (termAt supportIndex)
      | inr isSupportAtHead =>
          have tailVanishes := joinBelowQOfAllBot termAt boundPred
            (fun termIndex isInTail =>
              doOtherTermsVanish termIndex (Nat.le.step isInTail)
                (fun isTermSupport => noLtOfEq (isTermSupport.trans isSupportAtHead) isInTail))
          show joinQ (joinBelowQ termAt boundPred) (termAt boundPred) = termAt supportIndex
          rw [tailVanishes, isSupportAtHead]
          exact botJoinQ (termAt boundPred)

theorem joinBelowQSplitsAtBlock (termAt : Nat → QuantaleThree) (blockSize : Nat) :
    (tailSize : Nat) →
    joinBelowQ termAt (blockSize + tailSize)
      = joinQ (joinBelowQ termAt blockSize)
        (joinBelowQ (fun offsetIndex => termAt (blockSize + offsetIndex)) tailSize)
  | 0 => (joinBotQ (joinBelowQ termAt blockSize)).symm
  | tailPred + 1 => by
      show joinQ (joinBelowQ termAt (blockSize + tailPred)) (termAt (blockSize + tailPred))
        = joinQ (joinBelowQ termAt blockSize)
          (joinQ (joinBelowQ (fun offsetIndex => termAt (blockSize + offsetIndex)) tailPred)
            (termAt (blockSize + tailPred)))
      rw [joinBelowQSplitsAtBlock termAt blockSize tailPred]
      exact joinAssocQ (joinBelowQ termAt blockSize)
        (joinBelowQ (fun offsetIndex => termAt (blockSize + offsetIndex)) tailPred)
        (termAt (blockSize + tailPred))

theorem joinBelowQOfPointwiseJoin (firstTermAt secondTermAt : Nat → QuantaleThree) :
    (bound : Nat) →
    joinBelowQ (fun termIndex => joinQ (firstTermAt termIndex) (secondTermAt termIndex)) bound
      = joinQ (joinBelowQ firstTermAt bound) (joinBelowQ secondTermAt bound)
  | 0 => rfl
  | boundPred + 1 => by
      show joinQ (joinBelowQ (fun termIndex => joinQ (firstTermAt termIndex) (secondTermAt termIndex))
            boundPred) (joinQ (firstTermAt boundPred) (secondTermAt boundPred))
        = joinQ (joinQ (joinBelowQ firstTermAt boundPred) (firstTermAt boundPred))
          (joinQ (joinBelowQ secondTermAt boundPred) (secondTermAt boundPred))
      rw [joinBelowQOfPointwiseJoin firstTermAt secondTermAt boundPred]
      exact joinFourExchangeQ (joinBelowQ firstTermAt boundPred) (joinBelowQ secondTermAt boundPred)
        (firstTermAt boundPred) (secondTermAt boundPred)

theorem joinBelowQTensorLeft (leftFactor : QuantaleThree) (termAt : Nat → QuantaleThree) :
    (bound : Nat) →
    tensorQ leftFactor (joinBelowQ termAt bound)
      = joinBelowQ (fun termIndex => tensorQ leftFactor (termAt termIndex)) bound
  | 0 => tensorBotQ leftFactor
  | boundPred + 1 => by
      show tensorQ leftFactor (joinQ (joinBelowQ termAt boundPred) (termAt boundPred))
        = joinQ (joinBelowQ (fun termIndex => tensorQ leftFactor (termAt termIndex)) boundPred)
          (tensorQ leftFactor (termAt boundPred))
      rw [tensorJoinDistribLeftQ leftFactor (joinBelowQ termAt boundPred) (termAt boundPred),
        joinBelowQTensorLeft leftFactor termAt boundPred]

theorem joinBelowQTensorRight (termAt : Nat → QuantaleThree) (rightFactor : QuantaleThree) :
    (bound : Nat) →
    tensorQ (joinBelowQ termAt bound) rightFactor
      = joinBelowQ (fun termIndex => tensorQ (termAt termIndex) rightFactor) bound
  | 0 => botTensorQ rightFactor
  | boundPred + 1 => by
      show tensorQ (joinQ (joinBelowQ termAt boundPred) (termAt boundPred)) rightFactor
        = joinQ (joinBelowQ (fun termIndex => tensorQ (termAt termIndex) rightFactor) boundPred)
          (tensorQ (termAt boundPred) rightFactor)
      rw [tensorJoinDistribRightQ (joinBelowQ termAt boundPred) (termAt boundPred) rightFactor,
        joinBelowQTensorRight termAt rightFactor boundPred]

theorem joinBelowQExchange (pairTermAt : Nat → Nat → QuantaleThree) (innerBound : Nat) :
    (outerBound : Nat) →
    joinBelowQ (fun outerIndex =>
        joinBelowQ (fun innerIndex => pairTermAt outerIndex innerIndex) innerBound) outerBound
      = joinBelowQ (fun innerIndex =>
          joinBelowQ (fun outerIndex => pairTermAt outerIndex innerIndex) outerBound) innerBound
  | 0 => (joinBelowQOfAllBot _ innerBound (fun _ _ => rfl)).symm
  | outerPred + 1 => by
      show joinQ (joinBelowQ (fun outerIndex =>
            joinBelowQ (fun innerIndex => pairTermAt outerIndex innerIndex) innerBound) outerPred)
          (joinBelowQ (fun innerIndex => pairTermAt outerPred innerIndex) innerBound)
        = joinBelowQ (fun innerIndex =>
            joinBelowQ (fun outerIndex => pairTermAt outerIndex innerIndex) (outerPred + 1)) innerBound
      rw [joinBelowQExchange pairTermAt innerBound outerPred,
        (joinBelowQOfPointwiseJoin
          (fun innerIndex => joinBelowQ (fun outerIndex => pairTermAt outerIndex innerIndex) outerPred)
          (fun innerIndex => pairTermAt outerPred innerIndex) innerBound).symm]
      rfl

/-! ## Section 5 — direct-sum block and identity-entry lemmas over the quantale -/

theorem identityQOnDiagonal (diagonalIndex : Nat) :
    identityQEntries diagonalIndex diagonalIndex = QuantaleThree.top := by
  show cond (Nat.beq diagonalIndex diagonalIndex) QuantaleThree.top QuantaleThree.bot = QuantaleThree.top
  rw [beqSelfIsTrue diagonalIndex]
  rfl

theorem identityQOffDiagonal {rowIndex colIndex : Nat} (areDifferent : rowIndex ≠ colIndex) :
    identityQEntries rowIndex colIndex = QuantaleThree.bot := by
  show cond (Nat.beq rowIndex colIndex) QuantaleThree.top QuantaleThree.bot = QuantaleThree.bot
  rw [beqIsFalseOfNe areDifferent]
  rfl

theorem directSumQInTopBlock {topRowCount topColCount : Nat}
    (topEntries bottomEntries : QMatrixEntries) {rowIndex colIndex : Nat}
    (isRowInTop : rowIndex < topRowCount) (isColInTop : colIndex < topColCount) :
    directSumQEntries topRowCount topColCount topEntries bottomEntries rowIndex colIndex
      = topEntries rowIndex colIndex := by
  show cond (Nat.blt rowIndex topRowCount)
      (cond (Nat.blt colIndex topColCount) (topEntries rowIndex colIndex) QuantaleThree.bot)
      (cond (Nat.blt colIndex topColCount) QuantaleThree.bot
        (bottomEntries (rowIndex - topRowCount) (colIndex - topColCount)))
    = topEntries rowIndex colIndex
  rw [bltIsTrueOfLt isRowInTop, bltIsTrueOfLt isColInTop]
  rfl

theorem directSumQInBottomBlock {topRowCount topColCount : Nat}
    (topEntries bottomEntries : QMatrixEntries) (rowOffset colOffset : Nat) :
    directSumQEntries topRowCount topColCount topEntries bottomEntries
      (topRowCount + rowOffset) (topColCount + colOffset) = bottomEntries rowOffset colOffset := by
  show cond (Nat.blt (topRowCount + rowOffset) topRowCount)
      (cond (Nat.blt (topColCount + colOffset) topColCount)
        (topEntries (topRowCount + rowOffset) (topColCount + colOffset)) QuantaleThree.bot)
      (cond (Nat.blt (topColCount + colOffset) topColCount) QuantaleThree.bot
        (bottomEntries ((topRowCount + rowOffset) - topRowCount)
          ((topColCount + colOffset) - topColCount)))
    = bottomEntries rowOffset colOffset
  rw [bltIsFalseOfGe (Nat.le_add_right topRowCount rowOffset),
    bltIsFalseOfGe (Nat.le_add_right topColCount colOffset),
    addSubCancelLeft topRowCount rowOffset, addSubCancelLeft topColCount colOffset]
  rfl

theorem directSumQInTopRightBlock {topRowCount topColCount : Nat}
    (topEntries bottomEntries : QMatrixEntries) {rowIndex : Nat} (colOffset : Nat)
    (isRowInTop : rowIndex < topRowCount) :
    directSumQEntries topRowCount topColCount topEntries bottomEntries
      rowIndex (topColCount + colOffset) = QuantaleThree.bot := by
  show cond (Nat.blt rowIndex topRowCount)
      (cond (Nat.blt (topColCount + colOffset) topColCount)
        (topEntries rowIndex (topColCount + colOffset)) QuantaleThree.bot)
      (cond (Nat.blt (topColCount + colOffset) topColCount) QuantaleThree.bot
        (bottomEntries (rowIndex - topRowCount) ((topColCount + colOffset) - topColCount)))
    = QuantaleThree.bot
  rw [bltIsTrueOfLt isRowInTop, bltIsFalseOfGe (Nat.le_add_right topColCount colOffset)]
  rfl

theorem directSumQInBottomLeftBlock {topRowCount topColCount : Nat}
    (topEntries bottomEntries : QMatrixEntries) {colIndex : Nat} (rowOffset : Nat)
    (isColInTop : colIndex < topColCount) :
    directSumQEntries topRowCount topColCount topEntries bottomEntries
      (topRowCount + rowOffset) colIndex = QuantaleThree.bot := by
  show cond (Nat.blt (topRowCount + rowOffset) topRowCount)
      (cond (Nat.blt colIndex topColCount) (topEntries (topRowCount + rowOffset) colIndex) QuantaleThree.bot)
      (cond (Nat.blt colIndex topColCount) QuantaleThree.bot
        (bottomEntries ((topRowCount + rowOffset) - topRowCount) (colIndex - topColCount)))
    = QuantaleThree.bot
  rw [bltIsFalseOfGe (Nat.le_add_right topRowCount rowOffset), bltIsTrueOfLt isColInTop]
  rfl

/-! ## Section 6 — the pointwise/rectangle-agreement bridge -/

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

theorem agreeOnRowOfPointwise (leftEntries rightEntries : QMatrixEntries) (rowIndex : Nat)
    (colBound : Nat)
    (agreePointwise : ∀ colIndex, colIndex < colBound →
      leftEntries rowIndex colIndex = rightEntries rowIndex colIndex) :
    doQEntriesAgreeOnRow leftEntries rightEntries rowIndex colBound = true := by
  induction colBound with
  | zero => rfl
  | succ colBoundPred inductiveHypothesis =>
      have tailAgrees := inductiveHypothesis
        (fun colIndex isBelow => agreePointwise colIndex (Nat.le.step isBelow))
      have headAgrees : areQEqual (leftEntries rowIndex colBoundPred)
          (rightEntries rowIndex colBoundPred) = true := by
        rw [agreePointwise colBoundPred (Nat.lt_succ_self colBoundPred)]
        exact areQEqualSelf (rightEntries rowIndex colBoundPred)
      show (doQEntriesAgreeOnRow leftEntries rightEntries rowIndex colBoundPred
          && areQEqual (leftEntries rowIndex colBoundPred) (rightEntries rowIndex colBoundPred))
        = true
      rw [tailAgrees, headAgrees]
      rfl

theorem pointwiseOfAgreeOnRow (leftEntries rightEntries : QMatrixEntries) (rowIndex : Nat) :
    (colBound : Nat) →
    doQEntriesAgreeOnRow leftEntries rightEntries rowIndex colBound = true →
    ∀ colIndex, colIndex < colBound → leftEntries rowIndex colIndex = rightEntries rowIndex colIndex
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
          exact eqOfAreQEqual headFlag

theorem agreeOnRowsOfPointwise (leftEntries rightEntries : QMatrixEntries) (colCount : Nat)
    (rowBound : Nat)
    (agreePointwise : ∀ rowIndex colIndex, rowIndex < rowBound → colIndex < colCount →
      leftEntries rowIndex colIndex = rightEntries rowIndex colIndex) :
    doQEntriesAgreeOnRows leftEntries rightEntries colCount rowBound = true := by
  induction rowBound with
  | zero => rfl
  | succ rowBoundPred inductiveHypothesis =>
      have tailAgrees := inductiveHypothesis
        (fun rowIndex colIndex isRowBelow isColBelow =>
          agreePointwise rowIndex colIndex (Nat.le.step isRowBelow) isColBelow)
      have headAgrees := agreeOnRowOfPointwise leftEntries rightEntries rowBoundPred colCount
        (fun colIndex isColBelow =>
          agreePointwise rowBoundPred colIndex (Nat.lt_succ_self rowBoundPred) isColBelow)
      show (doQEntriesAgreeOnRows leftEntries rightEntries colCount rowBoundPred
          && doQEntriesAgreeOnRow leftEntries rightEntries rowBoundPred colCount) = true
      rw [tailAgrees, headAgrees]
      rfl

theorem pointwiseOfAgreeOnRows (leftEntries rightEntries : QMatrixEntries) (colCount : Nat) :
    (rowBound : Nat) →
    doQEntriesAgreeOnRows leftEntries rightEntries colCount rowBound = true →
    ∀ rowIndex colIndex, rowIndex < rowBound → colIndex < colCount →
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

theorem agreeUpToOfPointwise (rowCount colCount : Nat) (leftEntries rightEntries : QMatrixEntries)
    (agreePointwise : ∀ rowIndex colIndex, rowIndex < rowCount → colIndex < colCount →
      leftEntries rowIndex colIndex = rightEntries rowIndex colIndex) :
    doQEntriesAgreeUpTo rowCount colCount leftEntries rightEntries = true :=
  agreeOnRowsOfPointwise leftEntries rightEntries colCount rowCount agreePointwise

theorem pointwiseOfAgreeUpTo (rowCount colCount : Nat) (leftEntries rightEntries : QMatrixEntries)
    (checkerHolds : doQEntriesAgreeUpTo rowCount colCount leftEntries rightEntries = true) :
    ∀ rowIndex colIndex, rowIndex < rowCount → colIndex < colCount →
      leftEntries rowIndex colIndex = rightEntries rowIndex colIndex :=
  pointwiseOfAgreeOnRows leftEntries rightEntries colCount rowCount checkerHolds

/-! ## Section 7 — the weighted-diagram carrier and its quantale denotation (T1) -/

/-- Formal weighted diagrams over the weighted generators.  A diagram `sourceArity -> targetArity`
denotes a `targetArity x sourceArity` quantale matrix. -/
inductive WeightedDiagram : Nat → Nat → Type where
  | identityWires : (strandCount : Nat) → WeightedDiagram strandCount strandCount
  | composeSequential :
      {sourceArity : Nat} → {middleArity : Nat} → {targetArity : Nat} →
      WeightedDiagram sourceArity middleArity → WeightedDiagram middleArity targetArity →
      WeightedDiagram sourceArity targetArity
  | tensorParallel :
      {topSourceArity : Nat} → {topTargetArity : Nat} →
      {bottomSourceArity : Nat} → {bottomTargetArity : Nat} →
      WeightedDiagram topSourceArity topTargetArity → WeightedDiagram bottomSourceArity bottomTargetArity →
      WeightedDiagram (topSourceArity + bottomSourceArity) (topTargetArity + bottomTargetArity)
  | weightGen : QuantaleThree → WeightedDiagram 1 1
  | copyGen : WeightedDiagram 1 2
  | mergeGen : WeightedDiagram 2 1
  | swapGen : WeightedDiagram 2 2

/-- The single identity wire — the workhorse whisker block. -/
def singleWire : WeightedDiagram 1 1 := WeightedDiagram.identityWires 1

/-- Matrix denotation: identity to the identity quantale matrix, sequential composition to the
join-of-tensors product (second stage on the left), tensor to block-diagonal direct sum, generators to
their table matrices. -/
def denoteQEntries : {sourceArity targetArity : Nat} →
    WeightedDiagram sourceArity targetArity → QMatrixEntries
  | _, _, WeightedDiagram.identityWires _ => identityQEntries
  | _, _, @WeightedDiagram.composeSequential _ middleArity _ firstStage secondStage =>
      composeQEntries middleArity (denoteQEntries secondStage) (denoteQEntries firstStage)
  | _, _, @WeightedDiagram.tensorParallel topSourceArity topTargetArity _ _ topDiagram bottomDiagram =>
      directSumQEntries topTargetArity topSourceArity (denoteQEntries topDiagram)
        (denoteQEntries bottomDiagram)
  | _, _, WeightedDiagram.weightGen weight => weightGenQEntries weight
  | _, _, WeightedDiagram.copyGen => copyGenQEntries
  | _, _, WeightedDiagram.mergeGen => mergeGenQEntries
  | _, _, WeightedDiagram.swapGen => swapGenQEntries

/-! ### Well-definedness fires: the generator matrices read on their declared rectangle (T1) -/

/-- copy denotes `[[top],[top]]` on the 2x1 rectangle. -/
theorem copyDenotesColumnOfTops :
    doQEntriesAgreeUpTo 2 1 (denoteQEntries WeightedDiagram.copyGen)
      (fun rowIndex _colIndex => cond (Nat.blt rowIndex 2) QuantaleThree.top QuantaleThree.bot) = true := rfl

/-- a weighted wire denotes `[[q]]` on the 1x1 rectangle. -/
theorem weightDenotesSingleton :
    doQEntriesAgreeUpTo 1 1 (denoteQEntries (WeightedDiagram.weightGen QuantaleThree.mid))
      (fun _rowIndex _colIndex => QuantaleThree.mid) = true := rfl

/-- swap denotes the permutation on the 2x2 rectangle. -/
theorem swapDenotesTransposition :
    doQEntriesAgreeUpTo 2 2 (denoteQEntries WeightedDiagram.swapGen) swapGenQEntries = true := rfl

/-! ## Section 8 — the weighted rows and per-row soundness (T2) -/

/-- THE WEIGHTED LAW: composing two weighted wires tensors (mins) their weights — the quantale-enriched
composition rule that Bool cannot express (three grades genuinely separate). -/
def weightComposeLeftSide (firstWeight secondWeight : QuantaleThree) : WeightedDiagram 1 1 :=
  WeightedDiagram.composeSequential (WeightedDiagram.weightGen firstWeight)
    (WeightedDiagram.weightGen secondWeight)
def weightComposeRightSide (firstWeight secondWeight : QuantaleThree) : WeightedDiagram 1 1 :=
  WeightedDiagram.weightGen (tensorQ secondWeight firstWeight)
theorem weightComposeRowIsSound (firstWeight secondWeight : QuantaleThree) :
    doQEntriesAgreeUpTo 1 1 (denoteQEntries (weightComposeLeftSide firstWeight secondWeight))
      (denoteQEntries (weightComposeRightSide firstWeight secondWeight)) = true := by
  refine agreeUpToOfPointwise 1 1 _ _ (fun rowIndex colIndex isRowInRange isColInRange => ?_)
  have rowIsZero : rowIndex = 0 := by
    cases ltOrEqOfLtSucc isRowInRange with
    | inl deepBound => exact absurd deepBound (Nat.not_lt_zero rowIndex)
    | inr atHead => exact atHead
  have colIsZero : colIndex = 0 := by
    cases ltOrEqOfLtSucc isColInRange with
    | inl deepBound => exact absurd deepBound (Nat.not_lt_zero colIndex)
    | inr atHead => exact atHead
  rw [rowIsZero, colIsZero]
  show joinQ QuantaleThree.bot (tensorQ secondWeight firstWeight) = tensorQ secondWeight firstWeight
  exact botJoinQ (tensorQ secondWeight firstWeight)

/-- A `top`-weighted wire is the identity wire (`top` is the tensor unit). -/
def weightTopUnitLeftSide : WeightedDiagram 1 1 := WeightedDiagram.weightGen QuantaleThree.top
def weightTopUnitRightSide : WeightedDiagram 1 1 := WeightedDiagram.identityWires 1
theorem weightTopUnitRowIsSound :
    doQEntriesAgreeUpTo 1 1 (denoteQEntries weightTopUnitLeftSide)
      (denoteQEntries weightTopUnitRightSide) = true := rfl

/-- THE SPECIAL FROBENIUS LAW over the quantale: copy-then-merge denotes the identity, holding
because join is idempotent (`top (v) top = top`). -/
def specialFrobeniusLeftSide : WeightedDiagram 1 1 :=
  WeightedDiagram.composeSequential WeightedDiagram.copyGen WeightedDiagram.mergeGen
def specialFrobeniusRightSide : WeightedDiagram 1 1 := WeightedDiagram.identityWires 1
theorem specialFrobeniusRowIsSound :
    doQEntriesAgreeUpTo 1 1 (denoteQEntries specialFrobeniusLeftSide)
      (denoteQEntries specialFrobeniusRightSide) = true := rfl

/-- Cocommutativity: copy then swap = copy. -/
def copyCocommLeftSide : WeightedDiagram 1 2 :=
  WeightedDiagram.composeSequential WeightedDiagram.copyGen WeightedDiagram.swapGen
def copyCocommRightSide : WeightedDiagram 1 2 := WeightedDiagram.copyGen
theorem copyCocommRowIsSound :
    doQEntriesAgreeUpTo 2 1 (denoteQEntries copyCocommLeftSide)
      (denoteQEntries copyCocommRightSide) = true := rfl

/-- Commutativity: swap then merge = merge. -/
def mergeCommLeftSide : WeightedDiagram 2 1 :=
  WeightedDiagram.composeSequential WeightedDiagram.swapGen WeightedDiagram.mergeGen
def mergeCommRightSide : WeightedDiagram 2 1 := WeightedDiagram.mergeGen
theorem mergeCommRowIsSound :
    doQEntriesAgreeUpTo 1 2 (denoteQEntries mergeCommLeftSide)
      (denoteQEntries mergeCommRightSide) = true := rfl

/-- Swap is an involution: swap then swap = identity. -/
def swapInvolutionLeftSide : WeightedDiagram 2 2 :=
  WeightedDiagram.composeSequential WeightedDiagram.swapGen WeightedDiagram.swapGen
def swapInvolutionRightSide : WeightedDiagram 2 2 := WeightedDiagram.identityWires 2
theorem swapInvolutionRowIsSound :
    doQEntriesAgreeUpTo 2 2 (denoteQEntries swapInvolutionLeftSide)
      (denoteQEntries swapInvolutionRightSide) = true := rfl

/-! ## Section 9 — the presented congruence WeightedConv and the soundness lift (T2) -/

/-- The smallest congruence on weighted diagrams containing the weighted rows and the strict-monoidal
structural laws (identities, sequential reassociation, identity-tensor fusion, and the middle-four
interchange — interchange lives HERE as structural glue). -/
inductive WeightedConv :
    {sourceArity : Nat} → {targetArity : Nat} →
    WeightedDiagram sourceArity targetArity → WeightedDiagram sourceArity targetArity → Prop where
  | fromReflexivity {sourceArity targetArity : Nat} (diagram : WeightedDiagram sourceArity targetArity) :
      WeightedConv diagram diagram
  | fromSymmetry {sourceArity targetArity : Nat}
      {leftDiagram rightDiagram : WeightedDiagram sourceArity targetArity} :
      WeightedConv leftDiagram rightDiagram → WeightedConv rightDiagram leftDiagram
  | fromTransitivity {sourceArity targetArity : Nat}
      {leftDiagram middleDiagram rightDiagram : WeightedDiagram sourceArity targetArity} :
      WeightedConv leftDiagram middleDiagram → WeightedConv middleDiagram rightDiagram →
      WeightedConv leftDiagram rightDiagram
  | underComposeSequential {sourceArity middleArity targetArity : Nat}
      {firstLeft firstRight : WeightedDiagram sourceArity middleArity}
      {secondLeft secondRight : WeightedDiagram middleArity targetArity} :
      WeightedConv firstLeft firstRight → WeightedConv secondLeft secondRight →
      WeightedConv (WeightedDiagram.composeSequential firstLeft secondLeft)
        (WeightedDiagram.composeSequential firstRight secondRight)
  | underTensorParallel {topSourceArity topTargetArity bottomSourceArity bottomTargetArity : Nat}
      {topLeft topRight : WeightedDiagram topSourceArity topTargetArity}
      {bottomLeft bottomRight : WeightedDiagram bottomSourceArity bottomTargetArity} :
      WeightedConv topLeft topRight → WeightedConv bottomLeft bottomRight →
      WeightedConv (WeightedDiagram.tensorParallel topLeft bottomLeft)
        (WeightedDiagram.tensorParallel topRight bottomRight)
  | composeIdentitySource {sourceArity targetArity : Nat} (diagram : WeightedDiagram sourceArity targetArity) :
      WeightedConv (WeightedDiagram.composeSequential (WeightedDiagram.identityWires sourceArity) diagram) diagram
  | composeIdentityTarget {sourceArity targetArity : Nat} (diagram : WeightedDiagram sourceArity targetArity) :
      WeightedConv (WeightedDiagram.composeSequential diagram (WeightedDiagram.identityWires targetArity)) diagram
  | composeReassociate {sourceArity secondArity thirdArity targetArity : Nat}
      (firstStage : WeightedDiagram sourceArity secondArity)
      (secondStage : WeightedDiagram secondArity thirdArity)
      (thirdStage : WeightedDiagram thirdArity targetArity) :
      WeightedConv
        (WeightedDiagram.composeSequential (WeightedDiagram.composeSequential firstStage secondStage) thirdStage)
        (WeightedDiagram.composeSequential firstStage (WeightedDiagram.composeSequential secondStage thirdStage))
  | tensorIdentityFusion (topStrandCount bottomStrandCount : Nat) :
      WeightedConv
        (WeightedDiagram.tensorParallel (WeightedDiagram.identityWires topStrandCount)
          (WeightedDiagram.identityWires bottomStrandCount))
        (WeightedDiagram.identityWires (topStrandCount + bottomStrandCount))
  | middleFourInterchange {topSourceArity topMiddleArity topTargetArity
      bottomSourceArity bottomMiddleArity bottomTargetArity : Nat}
      (topFirst : WeightedDiagram topSourceArity topMiddleArity)
      (topSecond : WeightedDiagram topMiddleArity topTargetArity)
      (bottomFirst : WeightedDiagram bottomSourceArity bottomMiddleArity)
      (bottomSecond : WeightedDiagram bottomMiddleArity bottomTargetArity) :
      WeightedConv
        (WeightedDiagram.tensorParallel (WeightedDiagram.composeSequential topFirst topSecond)
          (WeightedDiagram.composeSequential bottomFirst bottomSecond))
        (WeightedDiagram.composeSequential (WeightedDiagram.tensorParallel topFirst bottomFirst)
          (WeightedDiagram.tensorParallel topSecond bottomSecond))
  | fromWeightComposeRow (firstWeight secondWeight : QuantaleThree) :
      WeightedConv (weightComposeLeftSide firstWeight secondWeight)
        (weightComposeRightSide firstWeight secondWeight)
  | fromWeightTopUnitRow : WeightedConv weightTopUnitLeftSide weightTopUnitRightSide
  | fromSpecialFrobeniusRow : WeightedConv specialFrobeniusLeftSide specialFrobeniusRightSide
  | fromCopyCocommRow : WeightedConv copyCocommLeftSide copyCocommRightSide
  | fromMergeCommRow : WeightedConv mergeCommLeftSide mergeCommRightSide
  | fromSwapInvolutionRow : WeightedConv swapInvolutionLeftSide swapInvolutionRightSide

/-- CONVERTIBLE WEIGHTED DIAGRAMS DENOTE EQUAL QUANTALE MATRICES: the congruence-closure lift of the
per-row soundness fires, by induction over `WeightedConv` (quantale-matrix functoriality). -/
theorem convertibleWeightedDiagramsDenoteEqualQMatrices {sourceArity targetArity : Nat}
    {leftDiagram rightDiagram : WeightedDiagram sourceArity targetArity}
    (areConvertible : WeightedConv leftDiagram rightDiagram) :
    doQEntriesAgreeUpTo targetArity sourceArity
      (denoteQEntries leftDiagram) (denoteQEntries rightDiagram) = true := by
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
          joinBelowQRespectsPointwise
            (fun midIndex => tensorQ (denoteQEntries secondLeft rowIndex midIndex)
              (denoteQEntries firstLeft midIndex colIndex))
            (fun midIndex => tensorQ (denoteQEntries secondRight rowIndex midIndex)
              (denoteQEntries firstRight midIndex colIndex))
            middleArity
            (fun midIndex isMidInRange => by
              show tensorQ (denoteQEntries secondLeft rowIndex midIndex)
                  (denoteQEntries firstLeft midIndex colIndex)
                = tensorQ (denoteQEntries secondRight rowIndex midIndex)
                  (denoteQEntries firstRight midIndex colIndex)
              rw [pointwiseOfAgreeUpTo _ _ _ _ secondAgree rowIndex midIndex isRowInRange isMidInRange,
                pointwiseOfAgreeUpTo _ _ _ _ firstAgree midIndex colIndex isMidInRange isColInRange]))
  | @underTensorParallel topSourceArity topTargetArity bottomSourceArity bottomTargetArity
      topLeft topRight bottomLeft bottomRight _ _ topAgree bottomAgree =>
      refine agreeUpToOfPointwise _ _ _ _
        (fun rowIndex colIndex isRowInRange isColInRange => ?_)
      show directSumQEntries topTargetArity topSourceArity
          (denoteQEntries topLeft) (denoteQEntries bottomLeft) rowIndex colIndex
        = directSumQEntries topTargetArity topSourceArity
            (denoteQEntries topRight) (denoteQEntries bottomRight) rowIndex colIndex
      cases decomposeIndexAgainstBlock topTargetArity rowIndex with
      | inl isRowInTop =>
          cases decomposeIndexAgainstBlock topSourceArity colIndex with
          | inl isColInTop =>
              rw [directSumQInTopBlock _ _ isRowInTop isColInTop,
                directSumQInTopBlock _ _ isRowInTop isColInTop]
              exact pointwiseOfAgreeUpTo _ _ _ _ topAgree rowIndex colIndex isRowInTop isColInTop
          | inr colHasOffset =>
              cases colHasOffset with
              | intro colOffset colSplits =>
                  rw [colSplits, directSumQInTopRightBlock _ _ colOffset isRowInTop,
                    directSumQInTopRightBlock _ _ colOffset isRowInTop]
      | inr rowHasOffset =>
          cases rowHasOffset with
          | intro rowOffset rowSplits =>
              cases decomposeIndexAgainstBlock topSourceArity colIndex with
              | inl isColInTop =>
                  rw [rowSplits, directSumQInBottomLeftBlock _ _ rowOffset isColInTop,
                    directSumQInBottomLeftBlock _ _ rowOffset isColInTop]
              | inr colHasOffset =>
                  cases colHasOffset with
                  | intro colOffset colSplits =>
                      rw [rowSplits] at isRowInRange
                      rw [colSplits] at isColInRange
                      rw [rowSplits, colSplits,
                        directSumQInBottomBlock _ _ rowOffset colOffset,
                        directSumQInBottomBlock _ _ rowOffset colOffset]
                      exact pointwiseOfAgreeUpTo _ _ _ _ bottomAgree rowOffset colOffset
                        (ltOfAddLtAddLeft topTargetArity isRowInRange)
                        (ltOfAddLtAddLeft topSourceArity isColInRange)
  | @composeIdentitySource innerSourceArity innerTargetArity diagram =>
      refine agreeUpToOfPointwise _ _ _ _
        (fun rowIndex colIndex isRowInRange isColInRange => ?_)
      refine (joinBelowQOfSingleSupport _ innerSourceArity colIndex isColInRange ?_).trans ?_
      · intro midIndex _ isMidOffSupport
        show tensorQ (denoteQEntries diagram rowIndex midIndex) (identityQEntries midIndex colIndex)
          = QuantaleThree.bot
        rw [identityQOffDiagonal isMidOffSupport]
        exact tensorBotQ _
      · show tensorQ (denoteQEntries diagram rowIndex colIndex) (identityQEntries colIndex colIndex)
          = denoteQEntries diagram rowIndex colIndex
        rw [identityQOnDiagonal colIndex]
        exact tensorTopQ (denoteQEntries diagram rowIndex colIndex)
  | @composeIdentityTarget innerSourceArity innerTargetArity diagram =>
      refine agreeUpToOfPointwise _ _ _ _
        (fun rowIndex colIndex isRowInRange isColInRange => ?_)
      refine (joinBelowQOfSingleSupport _ innerTargetArity rowIndex isRowInRange ?_).trans ?_
      · intro midIndex _ isMidOffSupport
        show tensorQ (identityQEntries rowIndex midIndex) (denoteQEntries diagram midIndex colIndex)
          = QuantaleThree.bot
        rw [identityQOffDiagonal (fun isRowAtMid => isMidOffSupport isRowAtMid.symm)]
        exact botTensorQ _
      · show tensorQ (identityQEntries rowIndex rowIndex) (denoteQEntries diagram rowIndex colIndex)
          = denoteQEntries diagram rowIndex colIndex
        rw [identityQOnDiagonal rowIndex]
        exact topTensorQ (denoteQEntries diagram rowIndex colIndex)
  | @composeReassociate innerSourceArity secondArity thirdArity innerTargetArity
      firstStage secondStage thirdStage =>
      refine agreeUpToOfPointwise _ _ _ _
        (fun rowIndex colIndex isRowInRange isColInRange => ?_)
      show joinBelowQ (fun thirdIndex => tensorQ (denoteQEntries thirdStage rowIndex thirdIndex)
          (joinBelowQ (fun secondIndex => tensorQ (denoteQEntries secondStage thirdIndex secondIndex)
              (denoteQEntries firstStage secondIndex colIndex)) secondArity)) thirdArity
        = joinBelowQ (fun secondIndex =>
            tensorQ (joinBelowQ (fun thirdIndex => tensorQ (denoteQEntries thirdStage rowIndex thirdIndex)
              (denoteQEntries secondStage thirdIndex secondIndex)) thirdArity)
              (denoteQEntries firstStage secondIndex colIndex)) secondArity
      rw [joinBelowQRespectsPointwise _
          (fun thirdIndex => joinBelowQ (fun secondIndex =>
            tensorQ (denoteQEntries thirdStage rowIndex thirdIndex)
              (tensorQ (denoteQEntries secondStage thirdIndex secondIndex)
                (denoteQEntries firstStage secondIndex colIndex))) secondArity) thirdArity
          (fun thirdIndex _ => joinBelowQTensorLeft (denoteQEntries thirdStage rowIndex thirdIndex)
            (fun secondIndex => tensorQ (denoteQEntries secondStage thirdIndex secondIndex)
              (denoteQEntries firstStage secondIndex colIndex)) secondArity),
        joinBelowQExchange (fun thirdIndex secondIndex =>
          tensorQ (denoteQEntries thirdStage rowIndex thirdIndex)
            (tensorQ (denoteQEntries secondStage thirdIndex secondIndex)
              (denoteQEntries firstStage secondIndex colIndex))) secondArity thirdArity]
      exact joinBelowQRespectsPointwise _ _ secondArity
        (fun secondIndex _ => by
          rw [joinBelowQTensorRight (fun thirdIndex =>
              tensorQ (denoteQEntries thirdStage rowIndex thirdIndex)
                (denoteQEntries secondStage thirdIndex secondIndex))
            (denoteQEntries firstStage secondIndex colIndex) thirdArity]
          exact joinBelowQRespectsPointwise _ _ thirdArity
            (fun thirdIndex _ =>
              (tensorAssocQ (denoteQEntries thirdStage rowIndex thirdIndex)
                (denoteQEntries secondStage thirdIndex secondIndex)
                (denoteQEntries firstStage secondIndex colIndex)).symm))
  | tensorIdentityFusion topStrandCount bottomStrandCount =>
      refine agreeUpToOfPointwise _ _ _ _
        (fun rowIndex colIndex isRowInRange isColInRange => ?_)
      show directSumQEntries topStrandCount topStrandCount identityQEntries identityQEntries
          rowIndex colIndex
        = identityQEntries rowIndex colIndex
      cases decomposeIndexAgainstBlock topStrandCount rowIndex with
      | inl isRowInTop =>
          cases decomposeIndexAgainstBlock topStrandCount colIndex with
          | inl isColInTop =>
              rw [directSumQInTopBlock _ _ isRowInTop isColInTop]
          | inr colHasOffset =>
              cases colHasOffset with
              | intro colOffset colSplits =>
                  rw [colSplits, directSumQInTopRightBlock _ _ colOffset isRowInTop,
                    identityQOffDiagonal (fun isRowAtOffset => by
                      rw [isRowAtOffset] at isRowInTop
                      exact noLtOfGe (Nat.le_add_right topStrandCount colOffset) isRowInTop)]
      | inr rowHasOffset =>
          cases rowHasOffset with
          | intro rowOffset rowSplits =>
              cases decomposeIndexAgainstBlock topStrandCount colIndex with
              | inl isColInTop =>
                  rw [rowSplits, directSumQInBottomLeftBlock _ _ rowOffset isColInTop,
                    identityQOffDiagonal (fun isOffsetAtCol => by
                      rw [isOffsetAtCol.symm] at isColInTop
                      exact noLtOfGe (Nat.le_add_right topStrandCount rowOffset) isColInTop)]
              | inr colHasOffset =>
                  cases colHasOffset with
                  | intro colOffset colSplits =>
                      rw [rowSplits, colSplits, directSumQInBottomBlock _ _ rowOffset colOffset]
                      show identityQEntries rowOffset colOffset
                        = identityQEntries (topStrandCount + rowOffset) (topStrandCount + colOffset)
                      show cond (Nat.beq rowOffset colOffset) QuantaleThree.top QuantaleThree.bot
                        = cond (Nat.beq (topStrandCount + rowOffset) (topStrandCount + colOffset))
                          QuantaleThree.top QuantaleThree.bot
                      rw [beqAddLeftCancel topStrandCount rowOffset colOffset]
  | @middleFourInterchange topSourceArity topMiddleArity topTargetArity
      bottomSourceArity bottomMiddleArity bottomTargetArity
      topFirst topSecond bottomFirst bottomSecond =>
      refine agreeUpToOfPointwise _ _ _ _
        (fun rowIndex colIndex isRowInRange isColInRange => ?_)
      show directSumQEntries topTargetArity topSourceArity
          (composeQEntries topMiddleArity (denoteQEntries topSecond) (denoteQEntries topFirst))
          (composeQEntries bottomMiddleArity (denoteQEntries bottomSecond)
            (denoteQEntries bottomFirst))
          rowIndex colIndex
        = joinBelowQ (fun midIndex =>
            tensorQ (directSumQEntries topTargetArity topMiddleArity
              (denoteQEntries topSecond) (denoteQEntries bottomSecond) rowIndex midIndex)
            (directSumQEntries topMiddleArity topSourceArity
                (denoteQEntries topFirst) (denoteQEntries bottomFirst) midIndex colIndex))
          (topMiddleArity + bottomMiddleArity)
      simp only [joinBelowQSplitsAtBlock]
      cases decomposeIndexAgainstBlock topTargetArity rowIndex with
      | inl isRowInTop =>
          have tailVanishes : joinBelowQ (fun offsetIndex =>
              tensorQ (directSumQEntries topTargetArity topMiddleArity
                (denoteQEntries topSecond) (denoteQEntries bottomSecond) rowIndex
                (topMiddleArity + offsetIndex))
              (directSumQEntries topMiddleArity topSourceArity
                  (denoteQEntries topFirst) (denoteQEntries bottomFirst)
                  (topMiddleArity + offsetIndex) colIndex)) bottomMiddleArity = QuantaleThree.bot :=
            joinBelowQOfAllBot _ bottomMiddleArity (fun offsetIndex _ => by
              rw [directSumQInTopRightBlock _ _ offsetIndex isRowInTop]
              exact botTensorQ _)
          rw [tailVanishes, joinBotQ]
          cases decomposeIndexAgainstBlock topSourceArity colIndex with
          | inl isColInTop =>
              rw [directSumQInTopBlock _ _ isRowInTop isColInTop]
              exact joinBelowQRespectsPointwise _ _ topMiddleArity
                (fun midIndex isMidInTop => by
                  rw [directSumQInTopBlock _ _ isRowInTop isMidInTop,
                    directSumQInTopBlock _ _ isMidInTop isColInTop])
          | inr colHasOffset =>
              cases colHasOffset with
              | intro colOffset colSplits =>
                  rw [colSplits, directSumQInTopRightBlock _ _ colOffset isRowInTop]
                  exact (joinBelowQOfAllBot _ topMiddleArity
                    (fun midIndex isMidInTop => by
                      rw [directSumQInTopRightBlock _ _ colOffset isMidInTop]
                      exact tensorBotQ _)).symm
      | inr rowHasOffset =>
          cases rowHasOffset with
          | intro rowOffset rowSplits =>
              have headVanishes : joinBelowQ (fun midIndex =>
                  tensorQ (directSumQEntries topTargetArity topMiddleArity
                    (denoteQEntries topSecond) (denoteQEntries bottomSecond) rowIndex midIndex)
                  (directSumQEntries topMiddleArity topSourceArity
                      (denoteQEntries topFirst) (denoteQEntries bottomFirst) midIndex colIndex))
                  topMiddleArity = QuantaleThree.bot :=
                joinBelowQOfAllBot _ topMiddleArity (fun midIndex isMidInTop => by
                  rw [rowSplits, directSumQInBottomLeftBlock _ _ rowOffset isMidInTop]
                  exact botTensorQ _)
              rw [headVanishes, botJoinQ]
              cases decomposeIndexAgainstBlock topSourceArity colIndex with
              | inl isColInTop =>
                  rw [rowSplits, directSumQInBottomLeftBlock _ _ rowOffset isColInTop]
                  exact (joinBelowQOfAllBot _ bottomMiddleArity
                    (fun offsetIndex _ => by
                      rw [directSumQInBottomLeftBlock _ _ offsetIndex isColInTop]
                      exact tensorBotQ _)).symm
              | inr colHasOffset =>
                  cases colHasOffset with
                  | intro colOffset colSplits =>
                      rw [rowSplits, colSplits, directSumQInBottomBlock _ _ rowOffset colOffset]
                      exact joinBelowQRespectsPointwise _ _ bottomMiddleArity
                        (fun offsetIndex _ => by
                          rw [directSumQInBottomBlock _ _ rowOffset offsetIndex,
                            directSumQInBottomBlock _ _ offsetIndex colOffset])
  | fromWeightComposeRow firstWeight secondWeight => exact weightComposeRowIsSound firstWeight secondWeight
  | fromWeightTopUnitRow => exact weightTopUnitRowIsSound
  | fromSpecialFrobeniusRow => exact specialFrobeniusRowIsSound
  | fromCopyCocommRow => exact copyCocommRowIsSound
  | fromMergeCommRow => exact mergeCommRowIsSound
  | fromSwapInvolutionRow => exact swapInvolutionRowIsSound

/-! ## Section 10 — the decision procedure (T3) -/

/-- THE DECISION: two weighted diagrams are declared convertible iff their quantale matrices agree on
the full `targetArity x sourceArity` rectangle. -/
def decideWeightedConvBool {sourceArity targetArity : Nat}
    (leftDiagram rightDiagram : WeightedDiagram sourceArity targetArity) : Bool :=
  doQEntriesAgreeUpTo targetArity sourceArity
    (denoteQEntries leftDiagram) (denoteQEntries rightDiagram)

/-- SOUND DIRECTION: convertible diagrams pass the decision. -/
theorem decisionIsImpliedByWeightedConv {sourceArity targetArity : Nat}
    {leftDiagram rightDiagram : WeightedDiagram sourceArity targetArity}
    (areConvertible : WeightedConv leftDiagram rightDiagram) :
    decideWeightedConvBool leftDiagram rightDiagram = true :=
  convertibleWeightedDiagramsDenoteEqualQMatrices areConvertible

/-- THE NEGATIVE DECISION: diagrams whose quantale matrices DIFFER are NOT convertible — soundness
contraposed.  This is what makes a `false` matrix comparison a machine-checked refutation of
convertibility (the useful half of the weighted word-problem decision). -/
theorem notWeightedConvOfDistinctQMatrices {sourceArity targetArity : Nat}
    (leftDiagram rightDiagram : WeightedDiagram sourceArity targetArity)
    (doMatricesDiffer : decideWeightedConvBool leftDiagram rightDiagram = false) :
    WeightedConv leftDiagram rightDiagram → False :=
  fun areConvertible =>
    Bool.noConfusion
      (doMatricesDiffer.symm.trans (convertibleWeightedDiagramsDenoteEqualQMatrices areConvertible))

/-! ## Section 11 — completeness: statement and WALL (T4) -/

/-- THE QUANTALE PRESENTATION-COMPLETENESS STATEMENT (the converse of the decision): equal quantale
matrices imply WeightedConv-convertibility.  Stated as the named target; WALLED below. -/
def quantaleCompletenessStatement : Prop :=
  ∀ (sourceArity targetArity : Nat) (leftDiagram rightDiagram : WeightedDiagram sourceArity targetArity),
    doQEntriesAgreeUpTo targetArity sourceArity
      (denoteQEntries leftDiagram) (denoteQEntries rightDiagram) = true →
    WeightedConv leftDiagram rightDiagram

/-- OWNER MARKER (false): the general quantale presentation completeness is NOT proven here.

THE PRECISE UNJOINED STEP: the canonical-reduction lemma "every weighted diagram is
WeightedConv-convertible to the canonical diagram of its own quantale matrix" (`d ~ normalForm d`).
Given that lemma, completeness is immediate: equal quantale matrices give the SAME canonical diagram,
and both sides convert to it.  The lemma is the rewrite-confluence half of the argument and is not
built.  The quantale wrinkle over the Boolean case: the canonical form must additionally canonicalise
the WEIGHT VALUES living on each strand (each canonical entry is the join, over all diagram paths from
its input to its output, of the tensor of the weights along the path), so the reduction must merge
parallel weighted paths by join and push weights through copy/merge — whose confluence with the
crossing/naturality rewrites is the same unbuilt Squier-style completion.

TWO BURNED ATTACKS:
* Attack 1 (Lafont staircase canonical form, [Lafont2003] Sections 2-3, weight-decorated): build the
  canonical weighted diagram of a matrix — a copy/merge fan tower with a `weightGen` on each
  input-to-output path — and prove every diagram rewrites to it by orienting the rows.  The
  construction transports, but the REDUCTION (`d ~ normalForm d`) hits the same open fan-core
  confluence residual as the sibling Bool / N lanes: idempotency of join collapses the multiplicity
  fans but does NOT by itself close the crossing/naturality rewrite confluence, AND the new
  weight-merge step (joining the weights of two parallel paths) introduces its own critical pair with
  the swap-past-copy naturality row that is not resolved by a terminating rewrite system here.
* Attack 2 (comonoid-then-monoid span factorisation, [BSZ2017] Section 2.2 / [Lack2004] Section 5.3,
  weight-graded): factor every diagram as a comonoid part, then a diagonal of weighted wires, then a
  monoid part (`n <- p ->[weights] p -> m` weighted-span form), unique up to permutation, and read the
  quantale matrix off the factorisation.  Blocks on proving the weighted factorisation EXISTS and is
  unique-up-to-permutation-and-weight-join inside WeightedConv — an induction pushing copies past
  merges via the bialgebra square while accumulating weights by tensor, whose termination is the same
  unbuilt completion. -/
def qwmHasQuantalePresentationCompleteness : Bool := false

/-! ## Section 12 — ground fires (T5) -/

/-- FIRE 1 (quantale-matrix of a concrete weighted generator): a `mid`-weighted wire reads `[[mid]]`. -/
theorem fireWeightMidMatrix :
    denoteQEntries (WeightedDiagram.weightGen QuantaleThree.mid) 0 0 = QuantaleThree.mid := rfl

/-- FIRE 2 (two convertible weighted diagrams decide true): a `top`-weighted wire in series with a
`mid`-weighted wire has the same quantale matrix as a single `mid`-weighted wire (`top` is the tensor
unit), and the two are WeightedConv-convertible. -/
theorem fireWeightTopThenMidDecidesTrue :
    decideWeightedConvBool (weightComposeLeftSide QuantaleThree.top QuantaleThree.mid)
        (WeightedDiagram.weightGen QuantaleThree.mid) = true
      ∧ WeightedConv (weightComposeLeftSide QuantaleThree.top QuantaleThree.mid)
        (WeightedDiagram.weightGen QuantaleThree.mid) :=
  ⟨rfl, WeightedConv.fromWeightComposeRow QuantaleThree.top QuantaleThree.mid⟩

/-- FIRE 3 (two diagrams with different quantale matrices decide false, hence NOT convertible): a
`mid`-weighted wire and a `top`-weighted wire have distinct matrices (`[[mid]]` vs `[[top]]`). -/
theorem fireMidVersusTopWeightDecidesFalse :
    decideWeightedConvBool (WeightedDiagram.weightGen QuantaleThree.mid)
      (WeightedDiagram.weightGen QuantaleThree.top) = false := rfl

theorem fireMidWeightNotConvertibleToTopWeight :
    WeightedConv (WeightedDiagram.weightGen QuantaleThree.mid)
      (WeightedDiagram.weightGen QuantaleThree.top) → False :=
  notWeightedConvOfDistinctQMatrices (WeightedDiagram.weightGen QuantaleThree.mid)
    (WeightedDiagram.weightGen QuantaleThree.top) rfl

/-- FIRE 4 (a quantale-law fire): tensor distributes over join on the carrier, concretely
`mid (x) (bot (v) top) = (mid (x) bot) (v) (mid (x) top)`. -/
theorem fireTensorDistributesOverJoin :
    tensorQ QuantaleThree.mid (joinQ QuantaleThree.bot QuantaleThree.top)
      = joinQ (tensorQ QuantaleThree.mid QuantaleThree.bot) (tensorQ QuantaleThree.mid QuantaleThree.top) :=
  rfl

/-- FIRE 5 (the special Frobenius law decides true over the quantale): copy-then-merge and the identity
wire have equal quantale matrices, and are convertible. -/
theorem fireSpecialFrobeniusDecidesTrue :
    decideWeightedConvBool specialFrobeniusLeftSide specialFrobeniusRightSide = true
      ∧ WeightedConv specialFrobeniusLeftSide specialFrobeniusRightSide :=
  ⟨rfl, WeightedConv.fromSpecialFrobeniusRow⟩

end FX1Poly.Polygraph.Omega.QuantaleProp
