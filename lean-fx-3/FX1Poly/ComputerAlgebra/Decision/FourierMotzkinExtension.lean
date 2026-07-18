import FX1Poly.ComputerAlgebra.Decision.FourierMotzkinCompleteness

/-! # FX1Poly/ComputerAlgebra/Decision/FourierMotzkinExtension — the DISSAT-ARITH
    round-extension push: the wall REFUTED as stated, the inequality-guarded form
    PROVEN, and Farkas completeness INHABITED

Round 2 on the sibling wall `lfmRoundExtensionStatement`
(FourierMotzkinCompleteness.lean, owner
`fxDissatArith_hasFourierMotzkinCompleteness := false`).  Outcome, in three acts:

  1. **THE WALL AS STATED IS FALSE** (`lreRoundExtensionStatementRefuted`).  The
     statement quantifies over ARBITRARY certified rows — including rows whose
     relation is `isEqualTo`.  The elimination round buckets rows by the SIGN of
     the target coefficient only, so an equality row (both a lower AND an upper
     bound on the variable) lands in a single bucket and its opposite bound is
     forgotten.  Counterexample: `[x = 0, x >= 1]` — both rows sit in the
     positive bucket, the negative bucket is empty, the round output is the
     EMPTY list (satisfiable by anything), yet the input is unsatisfiable at
     every denominator.  Machine-checked below.
  2. **THE CORRECTED STATEMENT IS PROVEN** (`lreRoundExtensionHolds` inhabiting
     `lreRoundExtensionInequalityStatement`): the same extension property with
     the single extra hypothesis that every input row's relation is an
     inequality (`lfmRelationIsInequality`).  This is exactly the invariant the
     actual pipeline maintains — seed constraints are weighted sums (always
     inequalities by `lfmWeightedSumRelationIsInequality`) and rounds preserve
     inequality-ness — so nothing is lost for the cascade.
  3. **THE CASCADE CLOSES THE SIBLING WALL** (`lreFarkasCompletenessHolds`
     inhabits `lfkFarkasCompletenessStatement`, ascribed verbatim): fuel
     induction back through the driver, the ground+scan-clean base, the
     unit-provenance seed extraction, and the equality re-assembly transport
     from the expanded to the original system produce, for every system the
     finder scans clean, a satisfying scaled environment — contradicting
     rational infeasibility; on a scan hit the composition theorem hands over
     the checker-accepted certificate.

## Attack shape (per the sibling header's three documented failures)

This is documented shape 1 (direct structural back-substitution) with three
deviations that dissolve its recorded pain points:

  * **Midpoint witness, not endpoint**: with both buckets nonempty the new
    value for the eliminated variable is `t := cStar·LStar + aStar·UStar` at
    denominator `D' := D·(aStar·cStar + aStar·cStar)` — the MIDPOINT of the
    best scaled lower bound `LStar/(D·aStar)` and best scaled upper bound
    `UStar/(D·cStar)`.  The strict-tie bookkeeping that killed the endpoint
    route disappears: a strict row tying the weak optimum forces its cross
    combination to be STRICT, which in the succ-le integer encoding is a whole
    `+1` of headroom — enough to keep the midpoint strictly inside.  With one
    bucket empty the witness pads a whole denominator unit
    (`LStar + D·aStar` resp. `UStar − D·cStar`), again covering weak and
    strict rows uniformly.  Strictness is absorbed by the encoding; no
    lexicographic tie state.
  * **Unconditional decomposition kit**: `lreDotProductSplitAt` (dot = pivot
    entry · pivot coefficient + rest) and `lreDotProductUpdateAt` (dot after
    environment update = new value · pivot coefficient + rest) are structural
    equalities with NO length hypotheses — the padding/truncating semantics of
    the sibling files already make missing entries genuine zeros.  Everything
    else moves along cross-sum equality (`lfkIntEq`) congruence lemmas.
  * **Pairwise combo consumption**: the fold-selected best rows are compared
    only through the cross combinations the round itself emitted (via the
    bespoke membership predicate `lreRowIsAmong`), so no lcm/product
    recombination of heterogeneous denominators ever appears (the trap that
    relocated attack 2 into attack 1's mass).

## Supersession notes

  * `lfmRoundExtensionStatement` (sibling wall Prop): REFUTED here, byte-intact
    there.  The sibling owner flag
    `fxDissatArith_hasFourierMotzkinCompleteness := false` refers to that file
    and stays authoritative FOR THAT FILE; the corrected statement and the full
    completeness cascade live here under
    `fxDissatArith_hasRoundExtension := true` and
    `fxDissatArith_hasFourierMotzkinCompletenessProven := true`.
  * `lfkFarkasCompletenessStatement` (LinearFarkasCertificate.lean wall, owner
    `fxDissatArith_hasFarkasCompleteness := false` in that file, untouched):
    INHABITED here by `lreFarkasCompletenessHolds`.

## Zero-axiom discipline

Init only plus the two sibling imports.  Structural recursion throughout; no
`WellFounded.fix`.  No `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `funext`, `omega`, no `decide` on `Prop`, no catch-all match
arms, no `List.append`, no `Int`, no `Nat.sub/mod/div/min/max`.  Nat facts are
the siblings' probed-clean core plus hand-rolled additions (`lreNatLeAddLeft`,
positive-multiplier cancellation `lreNatMulLeCancelLeft` — never the banned
order corners).  Per-declaration gate in
`FX1PolyAudit/ComputerAlgebra/Decision/FourierMotzkinExtension.lean`. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace FX1Poly.ComputerAlgebra

/-! ## Nat kit additions — hand-rolled, probed-clean building blocks only -/

/-- `base <= addend + base` (structural on the addend; avoids `Nat.le_add_left`
so the probe surface stays inside the siblings' cleared core). -/
theorem lreNatLeAddLeft : ∀ (addendValue baseValue : Nat),
    Nat.le baseValue (addendValue + baseValue)
  | Nat.zero, baseValue => Nat.le_of_eq (Nat.zero_add baseValue).symm
  | Nat.succ addendPred, baseValue =>
      Nat.le_trans (lreNatLeAddLeft addendPred baseValue)
        (Nat.le_trans (Nat.le_succ (addendPred + baseValue))
          (Nat.le_of_eq (Nat.succ_add addendPred baseValue).symm))

/-- `base <= base + addend` (structural on the addend). -/
theorem lreNatLeAddRight : ∀ (baseValue addendValue : Nat),
    Nat.le baseValue (baseValue + addendValue)
  | _baseValue, Nat.zero => Nat.le_refl _
  | baseValue, Nat.succ addendPred =>
      Nat.le_trans (lreNatLeAddRight baseValue addendPred)
        (Nat.le_succ (baseValue + addendPred))

/-- Cancel a POSITIVE common left multiplier inside `le`: from
`(m+1)*u <= (m+1)*v` conclude `u <= v` (case on `ble u v`; the false branch
squeezes `(m+1)*(v+1) <= (m+1)*v` into the succ-le-self absurdity). -/
theorem lreNatMulLeCancelLeft (multiplierPred leftValue rightValue : Nat)
    (scaledBound : Nat.le (Nat.succ multiplierPred * leftValue)
      (Nat.succ multiplierPred * rightValue)) : Nat.le leftValue rightValue :=
  match lfmBoolCases (Nat.ble leftValue rightValue) with
  | Or.inl bleTrue => lfkNatLeOfBle leftValue rightValue bleTrue
  | Or.inr bleFalse =>
      let strictFlip : Nat.le (rightValue + 1) leftValue :=
        lfkNatLeOfBle (rightValue + 1) leftValue
          (lfmNatBleFalseFlipStrict leftValue rightValue bleFalse)
      let scaledFlip : Nat.le (Nat.succ multiplierPred * (rightValue + 1))
          (Nat.succ multiplierPred * rightValue) :=
        Nat.le_trans (lfkNatMulLeMulLeft (Nat.succ multiplierPred) strictFlip) scaledBound
      let expandedFlip : Nat.le
          (Nat.succ multiplierPred * rightValue + Nat.succ multiplierPred)
          (Nat.succ multiplierPred * rightValue + 0) :=
        lfkNatLeCongr
          ((congrArg (fun probe => Nat.succ multiplierPred * rightValue + probe)
              (Nat.mul_one (Nat.succ multiplierPred)).symm).trans
            (Nat.mul_add (Nat.succ multiplierPred) rightValue 1).symm)
          rfl scaledFlip
      let cancelled : Nat.le (Nat.succ multiplierPred) 0 :=
        lfmNatLeOfAddLeAddRight (Nat.succ multiplierPred * rightValue)
          (Nat.succ multiplierPred) 0
          (lfkNatLeCongr
            (Nat.add_comm (Nat.succ multiplierPred)
              (Nat.succ multiplierPred * rightValue))
            (Nat.add_comm 0 (Nat.succ multiplierPred * rightValue)) expandedFlip)
      nomatch cancelled

/-- Cancel a POSITIVE common left multiplier inside an equality. -/
theorem lreNatMulLeftCancelEq (multiplierPred leftValue rightValue : Nat)
    (scaledEq : Nat.succ multiplierPred * leftValue
      = Nat.succ multiplierPred * rightValue) : leftValue = rightValue :=
  lfmNatEqOfBleBle leftValue rightValue
    (lfkNatBleOfLe leftValue rightValue
      (lreNatMulLeCancelLeft multiplierPred leftValue rightValue (Nat.le_of_eq scaledEq)))
    (lfkNatBleOfLe rightValue leftValue
      (lreNatMulLeCancelLeft multiplierPred rightValue leftValue
        (Nat.le_of_eq scaledEq.symm)))

/-- A product of positives is positive (`ble`-form). -/
theorem lreNatPositiveMulPositive (leftValue rightValue : Nat)
    (leftPositive : Nat.ble 1 leftValue = true)
    (rightPositive : Nat.ble 1 rightValue = true) :
    Nat.ble 1 (leftValue * rightValue) = true :=
  lfkNatBleOfLe 1 (leftValue * rightValue)
    (Nat.le_trans (lfkNatLeOfBle 1 rightValue rightPositive)
      (lfkNatLeCongr (Nat.mul_one rightValue).symm (Nat.mul_comm leftValue rightValue)
        (lfkNatMulLeMulLeft rightValue (lfkNatLeOfBle 1 leftValue leftPositive))))

/-- A positive Nat has a successor shape (the existential the denominator
assembly destructures). -/
theorem lrePositiveSuccShape : ∀ (value : Nat), Nat.ble 1 value = true →
    ∃ (predecessorValue : Nat), value = predecessorValue + 1
  | Nat.zero, contradictoryWitness => Bool.noConfusion contradictoryWitness
  | Nat.succ predecessorValue, _positiveWitness => Exists.intro predecessorValue rfl

/-- A true conjunction with a false right conjunct forces the left to have been
the culprit — here the contrapositive form the scan-clean analysis needs: a
FALSE conjunction with a TRUE left conjunct has a false right conjunct. -/
theorem lreBoolAndFalseRight : ∀ (leftFlag rightFlag : Bool),
    (leftFlag && rightFlag) = false → leftFlag = true → rightFlag = false
  | true, false, _falseWitness, _leftWitness => rfl
  | true, true, contradictoryWitness, _leftWitness => Bool.noConfusion contradictoryWitness
  | false, true, _falseWitness, contradictoryWitness => Bool.noConfusion contradictoryWitness
  | false, false, _falseWitness, contradictoryWitness => Bool.noConfusion contradictoryWitness

/-- Split a `cond`-of-Option scan step that returned `none`: the test was false
and the tail also scanned clean. -/
theorem lreCondNoneSplit : ∀ (testFlag : Bool) (headProvenance : List Nat)
    (tailResult : Option (List Nat)),
    cond testFlag (Option.some headProvenance) tailResult = Option.none →
    And (testFlag = false) (tailResult = Option.none)
  | true, _headProvenance, _tailResult, condWitness => nomatch condWitness
  | false, _headProvenance, _tailResult, condWitness => And.intro rfl condWitness

/-! ## LfkInt kit — cross-sum equality congruence, order transports, movers -/

/-- Cross-sum equality is symmetric. -/
theorem lreIntEqSymm {leftValue rightValue : LfkInt}
    (eqWitness : lfkIntEq leftValue rightValue = true) :
    lfkIntEq rightValue leftValue = true :=
  lfkNatBeqOfEq (rightValue.positivePart + leftValue.negativePart)
    (leftValue.positivePart + rightValue.negativePart)
    (lfkNatEqOfBeq (leftValue.positivePart + rightValue.negativePart)
      (rightValue.positivePart + leftValue.negativePart) eqWitness).symm

/-- Cross-sum equality is transitive (add the two witnesses, cancel the shared
middle parts). -/
theorem lreIntEqTrans {firstValue secondValue thirdValue : LfkInt}
    (leftWitness : lfkIntEq firstValue secondValue = true)
    (rightWitness : lfkIntEq secondValue thirdValue = true) :
    lfkIntEq firstValue thirdValue = true :=
  let firstPos := firstValue.positivePart
  let firstNeg := firstValue.negativePart
  let secondPos := secondValue.positivePart
  let secondNeg := secondValue.negativePart
  let thirdPos := thirdValue.positivePart
  let thirdNeg := thirdValue.negativePart
  let leftEq : firstPos + secondNeg = secondPos + firstNeg :=
    lfkNatEqOfBeq _ _ leftWitness
  let rightEq : secondPos + thirdNeg = thirdPos + secondNeg :=
    lfkNatEqOfBeq _ _ rightWitness
  let targetToPair : (firstPos + thirdNeg) + (secondPos + secondNeg)
      = (firstPos + secondNeg) + (secondPos + thirdNeg) :=
    (lfkNatAddSwapMiddle firstPos thirdNeg secondPos secondNeg).trans
      ((congrArg (fun probe => (firstPos + secondPos) + probe)
          (Nat.add_comm thirdNeg secondNeg)).trans
        (lfkNatAddSwapMiddle firstPos secondNeg secondPos thirdNeg).symm)
  let pairRewritten : (firstPos + secondNeg) + (secondPos + thirdNeg)
      = (secondPos + firstNeg) + (thirdPos + secondNeg) :=
    lfkNatAddCongr leftEq rightEq
  let pairToResult : (secondPos + firstNeg) + (thirdPos + secondNeg)
      = (thirdPos + firstNeg) + (secondPos + secondNeg) :=
    (lfkNatAddSwapMiddle secondPos firstNeg thirdPos secondNeg).trans
      ((congrArg (fun probe => probe + (firstNeg + secondNeg))
          (Nat.add_comm secondPos thirdPos)).trans
        (lfkNatAddSwapMiddle thirdPos firstNeg secondPos secondNeg).symm)
  let summedEq : (firstPos + thirdNeg) + (secondPos + secondNeg)
      = (thirdPos + firstNeg) + (secondPos + secondNeg) :=
    targetToPair.trans (pairRewritten.trans pairToResult)
  lfkNatBeqOfEq _ _
    (lfkNatAddLeftCancel (secondPos + secondNeg) (firstPos + thirdNeg)
      (thirdPos + firstNeg)
      ((Nat.add_comm _ _).trans (summedEq.trans (Nat.add_comm _ _))))

/-- Three-term right swap `(x + y) + z = (x + z) + y` — the recurring shuffle of
the cross-sum transports. -/
theorem lreNatAddRightSwap (firstTerm secondTerm thirdTerm : Nat) :
    (firstTerm + secondTerm) + thirdTerm = (firstTerm + thirdTerm) + secondTerm :=
  (Nat.add_assoc firstTerm secondTerm thirdTerm).trans
    ((congrArg (fun probe => firstTerm + probe) (Nat.add_comm secondTerm thirdTerm)).trans
      (Nat.add_assoc firstTerm thirdTerm secondTerm).symm)

/-- Three-term left swap `x + (y + z) = y + (x + z)`. -/
theorem lreNatAddLeftSwap (firstTerm secondTerm thirdTerm : Nat) :
    firstTerm + (secondTerm + thirdTerm) = secondTerm + (firstTerm + thirdTerm) :=
  (Nat.add_assoc firstTerm secondTerm thirdTerm).symm.trans
    ((congrArg (fun probe => probe + thirdTerm) (Nat.add_comm firstTerm secondTerm)).trans
      (Nat.add_assoc secondTerm firstTerm thirdTerm))

/-- The Nat embedded as a nonnegative `LfkInt`. -/
def lreIntOfNat (value : Nat) : LfkInt := LfkInt.mk value 0

/-- The integer one — the succ-le strictness unit. -/
def lreIntOne : LfkInt := lreIntOfNat 1

/-- A positive Nat embeds as a cross-positive integer. -/
theorem lreIntOfNatIsPositive (value : Nat) (positiveWitness : Nat.ble 1 value = true) :
    lfkIntIsPositive (lreIntOfNat value) = true := positiveWitness

/-- Cross-sum order is transitive (add the side witnesses, cancel the middle). -/
theorem lreIntLeTrans {firstValue secondValue thirdValue : LfkInt}
    (leftBound : lfkIntLe firstValue secondValue = true)
    (rightBound : lfkIntLe secondValue thirdValue = true) :
    lfkIntLe firstValue thirdValue = true :=
  let firstPos := firstValue.positivePart
  let firstNeg := firstValue.negativePart
  let secondPos := secondValue.positivePart
  let secondNeg := secondValue.negativePart
  let thirdPos := thirdValue.positivePart
  let thirdNeg := thirdValue.negativePart
  let leftLe : Nat.le (firstPos + secondNeg) (secondPos + firstNeg) :=
    lfkNatLeOfBle _ _ leftBound
  let rightLe : Nat.le (secondPos + thirdNeg) (thirdPos + secondNeg) :=
    lfkNatLeOfBle _ _ rightBound
  let chained : Nat.le ((firstPos + secondNeg) + thirdNeg)
      ((thirdPos + secondNeg) + firstNeg) :=
    Nat.le_trans (Nat.add_le_add_right leftLe thirdNeg)
      (Nat.le_trans
        (Nat.le_of_eq (lreNatAddRightSwap secondPos firstNeg thirdNeg))
        (Nat.add_le_add_right rightLe firstNeg))
  lfkNatBleOfLe _ _
    (lfmNatLeOfAddLeAddRight secondNeg (firstPos + thirdNeg) (thirdPos + firstNeg)
      (lfkNatLeCongr
        (lreNatAddRightSwap firstPos thirdNeg secondNeg)
        (lreNatAddRightSwap thirdPos firstNeg secondNeg)
        chained))

/-- Strict order is weak order shifted by one: forward bridge. -/
theorem lreIntLtGivesLeShifted {lowerValue higherValue : LfkInt}
    (strictWitness : lfkIntLt lowerValue higherValue = true) :
    lfkIntLe (lfkIntAdd lowerValue lreIntOne) higherValue = true :=
  lfkNatBleOfLe _ _
    (lfkNatLeCongr
      (lfkNatAddOneShiftOut lowerValue.positivePart higherValue.negativePart)
      rfl
      (lfkNatLeOfBle _ _ strictWitness))

/-- Strict order is weak order shifted by one: backward bridge. -/
theorem lreIntLeShiftedGivesLt {lowerValue higherValue : LfkInt}
    (shiftedWitness : lfkIntLe (lfkIntAdd lowerValue lreIntOne) higherValue = true) :
    lfkIntLt lowerValue higherValue = true :=
  lfkNatBleOfLe _ _
    (lfkNatLeCongr
      (lfkNatAddOneShiftOut lowerValue.positivePart higherValue.negativePart).symm
      rfl
      (lfkNatLeOfBle _ _ shiftedWitness))

/-- Transport `<=` along a cross-sum equality of the LEFT endpoint. -/
theorem lreIntLeCongrLeft {leftValue leftRewritten rightValue : LfkInt}
    (leftEqWitness : lfkIntEq leftValue leftRewritten = true)
    (boundWitness : lfkIntLe leftValue rightValue = true) :
    lfkIntLe leftRewritten rightValue = true :=
  let oldPos := leftValue.positivePart
  let oldNeg := leftValue.negativePart
  let newPos := leftRewritten.positivePart
  let newNeg := leftRewritten.negativePart
  let rightPos := rightValue.positivePart
  let rightNeg := rightValue.negativePart
  let crossEq : oldPos + newNeg = newPos + oldNeg := lfkNatEqOfBeq _ _ leftEqWitness
  let paddedBound : Nat.le ((oldPos + rightNeg) + (newPos + newNeg))
      ((rightPos + oldNeg) + (newPos + newNeg)) :=
    lfkNatAddLeAdd (lfkNatLeOfBle _ _ boundWitness) (Nat.le_refl (newPos + newNeg))
  let leftShuffle : (newPos + rightNeg) + (oldPos + newNeg)
      = (oldPos + rightNeg) + (newPos + newNeg) :=
    (lfkNatAddSwapMiddle newPos rightNeg oldPos newNeg).trans
      ((congrArg (fun probe => probe + (rightNeg + newNeg)) (Nat.add_comm newPos oldPos)).trans
        (lfkNatAddSwapMiddle oldPos rightNeg newPos newNeg).symm)
  let rightShuffle : (rightPos + newNeg) + (oldPos + newNeg)
      = (rightPos + oldNeg) + (newPos + newNeg) :=
    (congrArg (fun probe => (rightPos + newNeg) + probe) crossEq).trans
      ((lfkNatAddSwapMiddle rightPos newNeg newPos oldNeg).trans
        ((congrArg (fun probe => (rightPos + newPos) + probe)
            (Nat.add_comm newNeg oldNeg)).trans
          (lfkNatAddSwapMiddle rightPos oldNeg newPos newNeg).symm))
  lfkNatBleOfLe _ _
    (lfmNatLeOfAddLeAddRight (oldPos + newNeg) (newPos + rightNeg) (rightPos + newNeg)
      (lfkNatLeCongr leftShuffle rightShuffle paddedBound))

/-- Transport `<=` along a cross-sum equality of the RIGHT endpoint. -/
theorem lreIntLeCongrRight {leftValue rightValue rightRewritten : LfkInt}
    (rightEqWitness : lfkIntEq rightValue rightRewritten = true)
    (boundWitness : lfkIntLe leftValue rightValue = true) :
    lfkIntLe leftValue rightRewritten = true :=
  let leftPos := leftValue.positivePart
  let leftNeg := leftValue.negativePart
  let oldPos := rightValue.positivePart
  let oldNeg := rightValue.negativePart
  let newPos := rightRewritten.positivePart
  let newNeg := rightRewritten.negativePart
  let crossEq : oldPos + newNeg = newPos + oldNeg := lfkNatEqOfBeq _ _ rightEqWitness
  let paddedBound : Nat.le ((leftPos + oldNeg) + (oldPos + newNeg))
      ((oldPos + leftNeg) + (oldPos + newNeg)) :=
    lfkNatAddLeAdd (lfkNatLeOfBle _ _ boundWitness) (Nat.le_refl (oldPos + newNeg))
  let leftShuffle : (leftPos + newNeg) + (oldPos + oldNeg)
      = (leftPos + oldNeg) + (oldPos + newNeg) :=
    (lfkNatAddSwapMiddle leftPos newNeg oldPos oldNeg).trans
      ((congrArg (fun probe => (leftPos + oldPos) + probe) (Nat.add_comm newNeg oldNeg)).trans
        (lfkNatAddSwapMiddle leftPos oldNeg oldPos newNeg).symm)
  let rightShuffle : (newPos + leftNeg) + (oldPos + oldNeg)
      = (oldPos + leftNeg) + (oldPos + newNeg) :=
    (lfkNatAddSwapMiddle newPos leftNeg oldPos oldNeg).trans
      ((congrArg (fun probe => probe + (leftNeg + oldNeg)) (Nat.add_comm newPos oldPos)).trans
        ((lfkNatAddSwapMiddle oldPos leftNeg newPos oldNeg).symm.trans
          (congrArg (fun probe => (oldPos + leftNeg) + probe)
            crossEq.symm)))
  lfkNatBleOfLe _ _
    (lfmNatLeOfAddLeAddRight (oldPos + oldNeg) (leftPos + newNeg) (newPos + leftNeg)
      (lfkNatLeCongr leftShuffle rightShuffle paddedBound))

/-- Transport `<` along a cross-sum equality of the LEFT endpoint (via the
one-shift bridges and the weak transport). -/
theorem lreIntLtCongrLeft {leftValue leftRewritten rightValue : LfkInt}
    (leftEqWitness : lfkIntEq leftValue leftRewritten = true)
    (strictWitness : lfkIntLt leftValue rightValue = true) :
    lfkIntLt leftRewritten rightValue = true :=
  lreIntLeShiftedGivesLt
    (lreIntLeCongrLeft
      (lfkIntAddEqEq leftEqWitness (lfkIntEqRefl lreIntOne))
      (lreIntLtGivesLeShifted strictWitness))

/-- Transport `<` along a cross-sum equality of the RIGHT endpoint. -/
theorem lreIntLtCongrRight {leftValue rightValue rightRewritten : LfkInt}
    (rightEqWitness : lfkIntEq rightValue rightRewritten = true)
    (strictWitness : lfkIntLt leftValue rightValue = true) :
    lfkIntLt leftValue rightRewritten = true :=
  lreIntLeShiftedGivesLt
    (lreIntLeCongrRight rightEqWitness (lreIntLtGivesLeShifted strictWitness))

/-- MOVER: a negated addend crosses `<=` from left to right. -/
theorem lreIntLeMoveNegAcross {leftBase rightBase movedValue : LfkInt}
    (boundWitness : lfkIntLe (lfkIntAdd leftBase (lfkIntNegate movedValue)) rightBase = true) :
    lfkIntLe leftBase (lfkIntAdd rightBase movedValue) = true :=
  lfkNatBleOfLe _ _
    (lfkNatLeCongr
      ((congrArg (fun probe => leftBase.positivePart + probe)
          (Nat.add_comm rightBase.negativePart movedValue.negativePart)).trans
        (Nat.add_assoc leftBase.positivePart movedValue.negativePart
          rightBase.negativePart).symm)
      ((Nat.add_assoc rightBase.positivePart movedValue.positivePart
          leftBase.negativePart).trans
        (congrArg (fun probe => rightBase.positivePart + probe)
          (Nat.add_comm movedValue.positivePart leftBase.negativePart)))
      (lfkNatLeOfBle _ _ boundWitness))

/-- MOVER, strict form. -/
theorem lreIntLtMoveNegAcross {leftBase rightBase movedValue : LfkInt}
    (strictWitness : lfkIntLt (lfkIntAdd leftBase (lfkIntNegate movedValue)) rightBase = true) :
    lfkIntLt leftBase (lfkIntAdd rightBase movedValue) = true :=
  let shuffledShift : lfkIntAdd (lfkIntAdd leftBase (lfkIntNegate movedValue)) lreIntOne
      = lfkIntAdd (lfkIntAdd leftBase lreIntOne) (lfkIntNegate movedValue) :=
    (lfkIntAddAssoc leftBase (lfkIntNegate movedValue) lreIntOne).trans
      ((congrArg (fun probe => lfkIntAdd leftBase probe)
          (lfkIntAddComm (lfkIntNegate movedValue) lreIntOne)).trans
        (lfkIntAddAssoc leftBase lreIntOne (lfkIntNegate movedValue)).symm)
  lreIntLeShiftedGivesLt
    (lreIntLeMoveNegAcross
      ((congrArg (fun probe => lfkIntLe probe rightBase) shuffledShift.symm).trans
        (lreIntLtGivesLeShifted strictWitness)))

/-- MOVER: split a two-addend `<=` into the cross-difference form
`X1 + X2 <= Y1 + Y2  ==>  X1 - Y1 <= Y2 - X2` (the combo-unfolding pivot). -/
theorem lreIntLeSplitAcross {firstLow secondLow firstHigh secondHigh : LfkInt}
    (boundWitness : lfkIntLe (lfkIntAdd firstLow secondLow)
      (lfkIntAdd firstHigh secondHigh) = true) :
    lfkIntLe (lfkIntAdd firstLow (lfkIntNegate firstHigh))
      (lfkIntAdd secondHigh (lfkIntNegate secondLow)) = true :=
  lfkNatBleOfLe _ _
    (lfkNatLeCongr
      ((congrArg (fun probe => (firstLow.positivePart + firstHigh.negativePart) + probe)
          (Nat.add_comm secondHigh.negativePart secondLow.positivePart)).trans
        (lfkNatAddSwapMiddle firstLow.positivePart firstHigh.negativePart
          secondLow.positivePart secondHigh.negativePart))
      ((congrArg (fun probe => probe + (firstLow.negativePart + firstHigh.positivePart))
          (Nat.add_comm secondHigh.positivePart secondLow.negativePart)).trans
        ((Nat.add_comm (secondLow.negativePart + secondHigh.positivePart)
            (firstLow.negativePart + firstHigh.positivePart)).trans
          ((lfkNatAddSwapMiddle firstLow.negativePart firstHigh.positivePart
              secondLow.negativePart secondHigh.positivePart).trans
            (Nat.add_comm (firstLow.negativePart + secondLow.negativePart)
              (firstHigh.positivePart + secondHigh.positivePart)))))
      (lfkNatLeOfBle _ _ boundWitness))

/-- MOVER, strict split. -/
theorem lreIntLtSplitAcross {firstLow secondLow firstHigh secondHigh : LfkInt}
    (strictWitness : lfkIntLt (lfkIntAdd firstLow secondLow)
      (lfkIntAdd firstHigh secondHigh) = true) :
    lfkIntLt (lfkIntAdd firstLow (lfkIntNegate firstHigh))
      (lfkIntAdd secondHigh (lfkIntNegate secondLow)) = true :=
  let shiftIntoFirst : lfkIntAdd (lfkIntAdd firstLow secondLow) lreIntOne
      = lfkIntAdd (lfkIntAdd firstLow lreIntOne) secondLow :=
    (lfkIntAddAssoc firstLow secondLow lreIntOne).trans
      ((congrArg (fun probe => lfkIntAdd firstLow probe)
          (lfkIntAddComm secondLow lreIntOne)).trans
        (lfkIntAddAssoc firstLow lreIntOne secondLow).symm)
  let shiftOutOfFirst : lfkIntAdd (lfkIntAdd firstLow lreIntOne) (lfkIntNegate firstHigh)
      = lfkIntAdd (lfkIntAdd firstLow (lfkIntNegate firstHigh)) lreIntOne :=
    (lfkIntAddAssoc firstLow lreIntOne (lfkIntNegate firstHigh)).trans
      ((congrArg (fun probe => lfkIntAdd firstLow probe)
          (lfkIntAddComm lreIntOne (lfkIntNegate firstHigh))).trans
        (lfkIntAddAssoc firstLow (lfkIntNegate firstHigh) lreIntOne).symm)
  lreIntLeShiftedGivesLt
    ((congrArg
        (fun probe => lfkIntLe probe
          (lfkIntAdd secondHigh (lfkIntNegate secondLow))) shiftOutOfFirst).symm.trans
      (lreIntLeSplitAcross
        ((congrArg
            (fun probe => lfkIntLe probe (lfkIntAdd firstHigh secondHigh))
            shiftIntoFirst.symm).trans
          (lreIntLtGivesLeShifted strictWitness))))

/-- MOVER: swap sides around a subtraction — from `A <= B - C` conclude
`C <= B - A` (stated additively with negations). -/
theorem lreIntLeSwapSides {leftValue restValue subtractedValue : LfkInt}
    (boundWitness : lfkIntLe leftValue
      (lfkIntAdd restValue (lfkIntNegate subtractedValue)) = true) :
    lfkIntLe subtractedValue
      (lfkIntAdd (lfkIntNegate leftValue) restValue) = true :=
  lfkNatBleOfLe _ _
    (lfkNatLeCongr
      ((Nat.add_comm subtractedValue.positivePart
          (leftValue.positivePart + restValue.negativePart)).trans
        (Nat.add_assoc leftValue.positivePart restValue.negativePart
          subtractedValue.positivePart))
      ((congrArg (fun probe => probe + subtractedValue.negativePart)
          (Nat.add_comm leftValue.negativePart restValue.positivePart)).trans
        (lreNatAddRightSwap restValue.positivePart leftValue.negativePart
          subtractedValue.negativePart))
      (lfkNatLeOfBle _ _ boundWitness))

/-- MOVER, strict swap. -/
theorem lreIntLtSwapSides {leftValue restValue subtractedValue : LfkInt}
    (strictWitness : lfkIntLt leftValue
      (lfkIntAdd restValue (lfkIntNegate subtractedValue)) = true) :
    lfkIntLt subtractedValue
      (lfkIntAdd (lfkIntNegate leftValue) restValue) = true :=
  let shiftedWeak : lfkIntLe subtractedValue
      (lfkIntAdd (lfkIntNegate (lfkIntAdd leftValue lreIntOne)) restValue) = true :=
    lreIntLeSwapSides (lreIntLtGivesLeShifted strictWitness)
  lfkNatBleOfLe _ _
    (lfkNatLeCongr
      ((Nat.add_assoc subtractedValue.positivePart
          (leftValue.positivePart + restValue.negativePart) 1).trans
        (congrArg (fun probe => subtractedValue.positivePart + probe)
          (lfkNatAddOneShiftOut leftValue.positivePart restValue.negativePart).symm))
      rfl
      (lfkNatLeOfBle _ _ shiftedWeak))

/-- Scaling by a POSITIVE Nat preserves strict order (the one-shift bridges plus
the whole-multiplier headroom `1 <= m+1`). -/
theorem lreIntScaleLtMono (multiplierPred : Nat) {lowerValue higherValue : LfkInt}
    (strictWitness : lfkIntLt lowerValue higherValue = true) :
    lfkIntLt (lfkIntScaleByNat (multiplierPred + 1) lowerValue)
      (lfkIntScaleByNat (multiplierPred + 1) higherValue) = true :=
  let scaledShifted : lfkIntLe
      (lfkIntScaleByNat (multiplierPred + 1) (lfkIntAdd lowerValue lreIntOne))
      (lfkIntScaleByNat (multiplierPred + 1) higherValue) = true :=
    lfkIntScaleLeMono (multiplierPred + 1) (lreIntLtGivesLeShifted strictWitness)
  let distributed : lfkIntLe
      (lfkIntAdd (lfkIntScaleByNat (multiplierPred + 1) lowerValue)
        (lfkIntScaleByNat (multiplierPred + 1) lreIntOne))
      (lfkIntScaleByNat (multiplierPred + 1) higherValue) = true :=
    (congrArg
        (fun probe => lfkIntLe probe (lfkIntScaleByNat (multiplierPred + 1) higherValue))
        (lfkIntScaleAddDistrib (multiplierPred + 1) lowerValue lreIntOne)).symm.trans
      scaledShifted
  let oneBelowScaledOne : lfkIntLe lreIntOne
      (lfkIntScaleByNat (multiplierPred + 1) lreIntOne) = true :=
    lfkNatBleOfLe _ _
      (lfkNatLeCongr rfl (Nat.mul_one (multiplierPred + 1))
        (Nat.succ_le_succ (Nat.zero_le multiplierPred)))
  lreIntLeShiftedGivesLt
    (lreIntLeTrans
      (lfkIntAddLeAdd (lfmIntLeRefl (lfkIntScaleByNat (multiplierPred + 1) lowerValue))
        oneBelowScaledOne)
      distributed)

/-- Cancel a POSITIVE common scale inside `<=`. -/
theorem lreIntLeCancelScale (multiplierPred : Nat) {leftValue rightValue : LfkInt}
    (scaledBound : lfkIntLe (lfkIntScaleByNat (multiplierPred + 1) leftValue)
      (lfkIntScaleByNat (multiplierPred + 1) rightValue) = true) :
    lfkIntLe leftValue rightValue = true :=
  lfkNatBleOfLe _ _
    (lreNatMulLeCancelLeft multiplierPred
      (leftValue.positivePart + rightValue.negativePart)
      (rightValue.positivePart + leftValue.negativePart)
      (lfkNatLeCongr
        (Nat.mul_add (multiplierPred + 1) leftValue.positivePart
          rightValue.negativePart)
        (Nat.mul_add (multiplierPred + 1) rightValue.positivePart
          leftValue.negativePart)
        (lfkNatLeOfBle _ _ scaledBound)))

/-- Multiplying FROM the zero integer gives the zero integer (structurally). -/
theorem lreIntMulZeroLeft (value : LfkInt) : lfkIntMul lfkIntZero value = lfkIntZero :=
  lfkIntMkCongr
    (lfkNatAddCongr (Nat.zero_mul value.positivePart) (Nat.zero_mul value.negativePart))
    (lfkNatAddCongr (Nat.zero_mul value.negativePart) (Nat.zero_mul value.positivePart))

/-- A value plus its own negation is cross-zero (right-negation orientation). -/
theorem lreIntAddNegateRightZero (value : LfkInt) :
    lfkIntIsZero (lfkIntAdd value (lfkIntNegate value)) = true :=
  lfkNatBeqOfEq (value.positivePart + value.negativePart)
    (value.negativePart + value.positivePart)
    (Nat.add_comm value.positivePart value.negativePart)

/-- Dropping a cross-zero LEFT addend is a cross-sum equality. -/
theorem lreIntEqDropZeroLeft {zeroishValue baseValue : LfkInt}
    (zeroWitness : lfkIntIsZero zeroishValue = true) :
    lfkIntEq (lfkIntAdd zeroishValue baseValue) baseValue = true :=
  lfkNatBeqOfEq ((zeroishValue.positivePart + baseValue.positivePart) + baseValue.negativePart)
    (baseValue.positivePart + (zeroishValue.negativePart + baseValue.negativePart))
    ((congrArg (fun probe => probe + baseValue.negativePart)
        (Nat.add_comm zeroishValue.positivePart baseValue.positivePart)).trans
      ((Nat.add_assoc baseValue.positivePart zeroishValue.positivePart
          baseValue.negativePart).trans
        (congrArg (fun probe => baseValue.positivePart + (probe + baseValue.negativePart))
          (lfkNatEqOfBeq zeroishValue.positivePart zeroishValue.negativePart zeroWitness))))

/-- Strictly exceed a value by adding a cross-positive amount to any weak upper
bound: `x <= y` and `0 < w` give `x < y + w`. -/
theorem lreIntLtOfLeAddPositive {lowerValue upperValue paddingValue : LfkInt}
    (positiveWitness : lfkIntIsPositive paddingValue = true)
    (boundWitness : lfkIntLe lowerValue upperValue = true) :
    lfkIntLt lowerValue (lfkIntAdd upperValue paddingValue) = true :=
  lfkNatBleOfLe _ _
    (lfkNatLeCongr
      ((congrArg (fun probe => probe + 1)
          (Nat.add_assoc lowerValue.positivePart upperValue.negativePart
            paddingValue.negativePart).symm).trans
        (Nat.add_assoc (lowerValue.positivePart + upperValue.negativePart)
          paddingValue.negativePart 1))
      (lreNatAddRightSwap upperValue.positivePart paddingValue.positivePart
        lowerValue.negativePart)
      (lfkNatAddLeAdd (lfkNatLeOfBle _ _ boundWitness) (lfkNatLeOfBle _ _ positiveWitness)))

/-- Fall strictly below a value by subtracting a cross-positive amount from any
weak lower bound: `x <= y` and `0 < w` give `x - w < y`. -/
theorem lreIntLtOfLeSubPositive {lowerValue upperValue paddingValue : LfkInt}
    (positiveWitness : lfkIntIsPositive paddingValue = true)
    (boundWitness : lfkIntLe lowerValue upperValue = true) :
    lfkIntLt (lfkIntAdd lowerValue (lfkIntNegate paddingValue)) upperValue = true :=
  lfkNatBleOfLe _ _
    (lfkNatLeCongr
      ((congrArg (fun probe => probe + 1)
          (lreNatAddRightSwap lowerValue.positivePart paddingValue.negativePart
            upperValue.negativePart)).trans
        (Nat.add_assoc (lowerValue.positivePart + upperValue.negativePart)
          paddingValue.negativePart 1))
      (Nat.add_assoc upperValue.positivePart lowerValue.negativePart
        paddingValue.positivePart).symm
      (lfkNatAddLeAdd (lfkNatLeOfBle _ _ boundWitness) (lfkNatLeOfBle _ _ positiveWitness)))

/-- Adding a cross-nonnegative value on the right never decreases. -/
theorem lreIntLeAddNonNegRight {baseValue paddingValue : LfkInt}
    (nonNegativeWitness : lfkIntIsNonNegative paddingValue = true) :
    lfkIntLe baseValue (lfkIntAdd baseValue paddingValue) = true :=
  lfkNatBleOfLe _ _
    (lfkNatLeCongr
      (Nat.add_assoc baseValue.positivePart baseValue.negativePart
        paddingValue.negativePart).symm
      (lreNatAddRightSwap baseValue.positivePart paddingValue.positivePart
        baseValue.negativePart)
      (Nat.add_le_add_left (lfkNatLeOfBle _ _ nonNegativeWitness)
        (baseValue.positivePart + baseValue.negativePart)))

/-- Left commutation for integer addition (structural). -/
theorem lreIntAddLeftCommute (outerValue middleValue innerValue : LfkInt) :
    lfkIntAdd outerValue (lfkIntAdd middleValue innerValue)
      = lfkIntAdd middleValue (lfkIntAdd outerValue innerValue) :=
  (lfkIntAddAssoc outerValue middleValue innerValue).symm.trans
    ((congrArg (fun probe => lfkIntAdd probe innerValue)
        (lfkIntAddComm outerValue middleValue)).trans
      (lfkIntAddAssoc middleValue outerValue innerValue))

/-- A cross-positive magnitude is at least one. -/
theorem lreIntPositiveMagnitudePositive (value : LfkInt)
    (positiveWitness : lfkIntIsPositive value = true) :
    Nat.ble 1 (lfmNatDelta value.positivePart value.negativePart) = true :=
  let magnitude := lfmNatDelta value.positivePart value.negativePart
  let recovery : value.negativePart + magnitude = value.positivePart :=
    lfmNatDeltaRecovers value.positivePart value.negativePart
      (lfmNatBleWeakenFromSucc value.negativePart value.positivePart positiveWitness)
  lfkNatBleOfLe 1 magnitude
    (lfmNatLeOfAddLeAddRight value.negativePart 1 magnitude
      (lfkNatLeCongr (Nat.add_comm 1 value.negativePart)
        (Nat.add_comm magnitude value.negativePart)
        (lfkNatLeCongr rfl recovery
          (lfkNatLeOfBle (value.negativePart + 1) value.positivePart positiveWitness))))

/-- Multiplying a witness by a CROSS-POSITIVE entry is, up to cross-sum
equality, scaling the witness by the entry's witnessed magnitude. -/
theorem lreIntMulPositiveEntryCrossEq (witnessValue entryValue : LfkInt)
    (positiveWitness : lfkIntIsPositive entryValue = true) :
    lfkIntEq (lfkIntMul witnessValue entryValue)
      (lfkIntScaleByNat (lfmNatDelta entryValue.positivePart entryValue.negativePart)
        witnessValue) = true :=
  let magnitude := lfmNatDelta entryValue.positivePart entryValue.negativePart
  let witnessPos := witnessValue.positivePart
  let witnessNeg := witnessValue.negativePart
  let entryPos := entryValue.positivePart
  let entryNeg := entryValue.negativePart
  let recovery : entryNeg + magnitude = entryPos :=
    lfmNatDeltaRecovers entryPos entryNeg
      (lfmNatBleWeakenFromSucc entryNeg entryPos positiveWitness)
  let sharedA := witnessPos * entryNeg
  let sharedB := witnessPos * magnitude
  let sharedC := witnessNeg * entryNeg
  let sharedD := magnitude * witnessNeg
  let leftExpand : (witnessPos * entryPos + witnessNeg * entryNeg) + magnitude * witnessNeg
      = ((sharedA + sharedB) + sharedC) + sharedD :=
    (congrArg (fun probe => (witnessPos * probe + sharedC) + sharedD) recovery.symm).trans
      (congrArg (fun probe => (probe + sharedC) + sharedD)
        (Nat.mul_add witnessPos entryNeg magnitude))
  let centerShuffle : ((sharedA + sharedB) + sharedC) + sharedD
      = sharedB + (sharedA + (sharedC + sharedD)) :=
    (congrArg (fun probe => probe + sharedD) (lreNatAddRightSwap sharedA sharedB sharedC)).trans
      ((lreNatAddRightSwap (sharedA + sharedC) sharedB sharedD).trans
        ((Nat.add_comm ((sharedA + sharedC) + sharedD) sharedB).trans
          (congrArg (fun probe => sharedB + probe)
            (Nat.add_assoc sharedA sharedC sharedD))))
  let rightCollapse : sharedB + (sharedA + (sharedC + sharedD))
      = magnitude * witnessPos + (witnessPos * entryNeg + witnessNeg * entryPos) :=
    (congrArg (fun probe => probe + (sharedA + (sharedC + sharedD)))
        (Nat.mul_comm witnessPos magnitude)).trans
      (congrArg (fun probe => magnitude * witnessPos + (sharedA + probe))
        (((congrArg (fun probe => sharedC + probe)
            (Nat.mul_comm magnitude witnessNeg)).trans
          (Nat.mul_add witnessNeg entryNeg magnitude).symm).trans
          (congrArg (fun probe => witnessNeg * probe) recovery)))
  lfkNatBeqOfEq _ _ (leftExpand.trans (centerShuffle.trans rightCollapse))

/-- Multiplying a witness by a CROSS-NEGATIVE entry is, up to cross-sum
equality, the NEGATED scaling of the witness by the entry's witnessed
magnitude. -/
theorem lreIntMulNegativeEntryCrossEq (witnessValue entryValue : LfkInt)
    (negativeWitness : lfkIntIsPositive (lfkIntNegate entryValue) = true) :
    lfkIntEq (lfkIntMul witnessValue entryValue)
      (lfkIntNegate
        (lfkIntScaleByNat (lfmNatDelta entryValue.negativePart entryValue.positivePart)
          witnessValue)) = true :=
  let magnitude := lfmNatDelta entryValue.negativePart entryValue.positivePart
  let witnessPos := witnessValue.positivePart
  let witnessNeg := witnessValue.negativePart
  let entryPos := entryValue.positivePart
  let entryNeg := entryValue.negativePart
  let recovery : entryPos + magnitude = entryNeg :=
    lfmNatDeltaRecovers entryNeg entryPos
      (lfmNatBleWeakenFromSucc entryPos entryNeg negativeWitness)
  let sharedP := witnessPos * entryPos
  let sharedQ := witnessNeg * entryPos
  let sharedR := witnessNeg * magnitude
  let sharedS := magnitude * witnessPos
  let leftExpand : (witnessPos * entryPos + witnessNeg * entryNeg) + magnitude * witnessPos
      = (sharedP + (sharedQ + sharedR)) + sharedS :=
    (congrArg (fun probe => (sharedP + witnessNeg * probe) + sharedS) recovery.symm).trans
      (congrArg (fun probe => (sharedP + probe) + sharedS)
        (Nat.mul_add witnessNeg entryPos magnitude))
  let normalized : (sharedP + (sharedQ + sharedR)) + sharedS
      = sharedP + (sharedQ + (sharedR + sharedS)) :=
    (Nat.add_assoc sharedP (sharedQ + sharedR) sharedS).trans
      (congrArg (fun probe => sharedP + probe) (Nat.add_assoc sharedQ sharedR sharedS))
  let rightExpand : magnitude * witnessNeg + (witnessPos * entryNeg + witnessNeg * entryPos)
      = sharedP + (sharedQ + (sharedR + sharedS)) :=
    ((congrArg (fun probe => magnitude * witnessNeg + (witnessPos * probe + sharedQ))
        recovery.symm).trans
      (congrArg (fun probe => magnitude * witnessNeg + (probe + sharedQ))
        (Nat.mul_add witnessPos entryPos magnitude))).trans
      ((congrArg (fun probe => probe + ((sharedP + witnessPos * magnitude) + sharedQ))
          (Nat.mul_comm magnitude witnessNeg)).trans
        ((Nat.add_comm sharedR ((sharedP + witnessPos * magnitude) + sharedQ)).trans
          ((congrArg (fun probe => probe + sharedR)
              ((congrArg (fun probe => probe + sharedQ)
                  (congrArg (fun probe => sharedP + probe)
                    (Nat.mul_comm witnessPos magnitude))).trans
                (lreNatAddRightSwap sharedP sharedS sharedQ))).trans
            ((Nat.add_assoc (sharedP + sharedQ) sharedS sharedR).trans
              ((congrArg (fun probe => (sharedP + sharedQ) + probe)
                  (Nat.add_comm sharedS sharedR)).trans
                ((Nat.add_assoc sharedP sharedQ (sharedR + sharedS)).trans
                  rfl))))))
  lfkNatBeqOfEq _ _ (leftExpand.trans (normalized.trans rightExpand.symm))

/-- The sign trichotomy every row falls into at the pivot position. -/
theorem lreIntSignTrichotomy (value : LfkInt) :
    Or (lfkIntIsZero value = true)
      (Or (lfkIntIsPositive value = true)
        (lfkIntIsPositive (lfkIntNegate value) = true)) :=
  match lfmBoolCases (lfkIntIsPositive value) with
  | Or.inl positiveTrue => Or.inr (Or.inl positiveTrue)
  | Or.inr positiveFalse =>
      match lfmBoolCases (lfkIntIsPositive (lfkIntNegate value)) with
      | Or.inl negativeTrue => Or.inr (Or.inr negativeTrue)
      | Or.inr negativeFalse =>
          Or.inl
            (lfkNatBeqOfEq value.positivePart value.negativePart
              (lfmNatEqOfBleBle value.positivePart value.negativePart
                (lfkNatBleOfLe _ _
                  (Nat.le_of_succ_le_succ
                    (lfkNatLeOfBle _ _
                      (lfmNatBleFalseFlipStrict (value.negativePart + 1)
                        value.positivePart positiveFalse))))
                (lfkNatBleOfLe _ _
                  (Nat.le_of_succ_le_succ
                    (lfkNatLeOfBle _ _
                      (lfmNatBleFalseFlipStrict (value.positivePart + 1)
                        value.negativePart negativeFalse))))))

/-! ## The environment-update / dot-product decomposition kit (Step-1 core) -/

/-- Replace the coefficient at one position by the genuine zero; vectors too
short to reach the position are unchanged (their entry already reads as zero). -/
def lreZeroCoefficientAt (positionIndex : Nat) (vector : List LfkInt) : List LfkInt :=
  match vector, positionIndex with
  | List.nil, _anyIndex => List.nil
  | _vectorHead :: vectorTail, Nat.zero => lfkIntZero :: vectorTail
  | vectorHead :: vectorTail, Nat.succ positionPred =>
      vectorHead :: lreZeroCoefficientAt positionPred vectorTail
termination_by structural vector

/-- Write a value at one environment position, zero-padding the environment as
needed to reach it (so the written entry is always live). -/
def lreUpdateEnvAt : Nat → LfkInt → List LfkInt → List LfkInt
  | Nat.zero, newValue, List.nil => newValue :: List.nil
  | Nat.zero, newValue, _envHead :: envTail => newValue :: envTail
  | Nat.succ positionPred, newValue, List.nil =>
      lfkIntZero :: lreUpdateEnvAt positionPred newValue List.nil
  | Nat.succ positionPred, newValue, envHead :: envTail =>
      envHead :: lreUpdateEnvAt positionPred newValue envTail

/-- Dotting from the empty environment is zero, whatever the coefficients. -/
theorem lreDotProductNilEnv : ∀ (coefficientVector : List LfkInt),
    lfkDotProduct List.nil coefficientVector = lfkIntZero
  | List.nil => rfl
  | _coefficientHead :: _coefficientTail => rfl

/-- THE SPLIT LEMMA: any dot product decomposes as (entry at the pivot) times
(coefficient at the pivot) plus the pivot-zeroed rest — structurally, with no
length hypotheses. -/
theorem lreDotProductSplitAt : ∀ (positionIndex : Nat) (env coefficientVector : List LfkInt),
    lfkDotProduct env coefficientVector
      = lfkIntAdd
          (lfkIntMul (lfmCoefficientAtIndex positionIndex env)
            (lfmCoefficientAtIndex positionIndex coefficientVector))
          (lfkDotProduct env (lreZeroCoefficientAt positionIndex coefficientVector))
  | _positionIndex, List.nil, List.nil => rfl
  | Nat.zero, List.nil, coefficientHead :: _coefficientTail =>
      (lreIntMulZeroLeft coefficientHead).symm
  | Nat.succ positionPred, List.nil, _coefficientHead :: coefficientTail =>
      (lreIntMulZeroLeft (lfmCoefficientAtIndex positionPred coefficientTail)).symm
  | _positionIndex, _envHead :: _envTail, List.nil => rfl
  | Nat.zero, envHead :: envTail, coefficientHead :: coefficientTail =>
      (congrArg (lfkIntAdd (lfkIntMul envHead coefficientHead))
        (lfkIntZeroAdd (lfkDotProduct envTail coefficientTail))).symm
  | Nat.succ positionPred, envHead :: envTail, coefficientHead :: coefficientTail =>
      (congrArg (lfkIntAdd (lfkIntMul envHead coefficientHead))
          (lreDotProductSplitAt positionPred envTail coefficientTail)).trans
        (lreIntAddLeftCommute (lfkIntMul envHead coefficientHead)
          (lfkIntMul (lfmCoefficientAtIndex positionPred envTail)
            (lfmCoefficientAtIndex positionPred coefficientTail))
          (lfkDotProduct envTail (lreZeroCoefficientAt positionPred coefficientTail)))

/-- THE MASTER DECOMPOSITION: dotting against an updated environment is the new
value times the pivot coefficient plus the pivot-zeroed rest against the OLD
environment — structural, unconditional. -/
theorem lreDotProductUpdateAt : ∀ (positionIndex : Nat)
    (env coefficientVector : List LfkInt) (newValue : LfkInt),
    lfkDotProduct (lreUpdateEnvAt positionIndex newValue env) coefficientVector
      = lfkIntAdd
          (lfkIntMul newValue (lfmCoefficientAtIndex positionIndex coefficientVector))
          (lfkDotProduct env (lreZeroCoefficientAt positionIndex coefficientVector))
  | Nat.zero, List.nil, List.nil, _newValue => rfl
  | Nat.zero, List.nil, coefficientHead :: coefficientTail, newValue =>
      congrArg (lfkIntAdd (lfkIntMul newValue coefficientHead))
        (lreDotProductNilEnv coefficientTail)
  | Nat.zero, _envHead :: _envTail, List.nil, _newValue => rfl
  | Nat.zero, _envHead :: envTail, coefficientHead :: coefficientTail, newValue =>
      (congrArg (lfkIntAdd (lfkIntMul newValue coefficientHead))
        (lfkIntZeroAdd (lfkDotProduct envTail coefficientTail))).symm
  | Nat.succ _positionPred, List.nil, List.nil, _newValue => rfl
  | Nat.succ positionPred, List.nil, coefficientHead :: coefficientTail, newValue =>
      (congrArg (lfkIntAdd (lfkIntMul lfkIntZero coefficientHead))
          ((lreDotProductUpdateAt positionPred List.nil coefficientTail newValue).trans
            (congrArg
              (lfkIntAdd (lfkIntMul newValue
                (lfmCoefficientAtIndex positionPred coefficientTail)))
              (lreDotProductNilEnv (lreZeroCoefficientAt positionPred coefficientTail))))).trans
        ((congrArg
            (fun probe => lfkIntAdd probe
              (lfkIntMul newValue (lfmCoefficientAtIndex positionPred coefficientTail)))
            (lreIntMulZeroLeft coefficientHead)).trans
          (lfkIntZeroAdd
            (lfkIntMul newValue (lfmCoefficientAtIndex positionPred coefficientTail))))
  | Nat.succ _positionPred, _envHead :: _envTail, List.nil, _newValue => rfl
  | Nat.succ positionPred, envHead :: envTail, coefficientHead :: coefficientTail, newValue =>
      (congrArg (lfkIntAdd (lfkIntMul envHead coefficientHead))
          (lreDotProductUpdateAt positionPred envTail coefficientTail newValue)).trans
        (lreIntAddLeftCommute (lfkIntMul envHead coefficientHead)
          (lfkIntMul newValue (lfmCoefficientAtIndex positionPred coefficientTail))
          (lfkDotProduct envTail (lreZeroCoefficientAt positionPred coefficientTail)))

/-- Entry step for the scaled-environment dot: multiplication from a scaled
entry is the scaled multiplication. -/
theorem lreIntMulScaleLeft (multiplier : Nat) (envValue coefficientValue : LfkInt) :
    lfkIntMul (lfkIntScaleByNat multiplier envValue) coefficientValue
      = lfkIntScaleByNat multiplier (lfkIntMul envValue coefficientValue) :=
  lfkIntMkCongr
    ((lfkNatAddCongr
        (lfkNatMulAssoc multiplier envValue.positivePart coefficientValue.positivePart)
        (lfkNatMulAssoc multiplier envValue.negativePart coefficientValue.negativePart)).trans
      (Nat.mul_add multiplier (envValue.positivePart * coefficientValue.positivePart)
        (envValue.negativePart * coefficientValue.negativePart)).symm)
    ((lfkNatAddCongr
        (lfkNatMulAssoc multiplier envValue.positivePart coefficientValue.negativePart)
        (lfkNatMulAssoc multiplier envValue.negativePart coefficientValue.positivePart)).trans
      (Nat.mul_add multiplier (envValue.positivePart * coefficientValue.negativePart)
        (envValue.negativePart * coefficientValue.positivePart)).symm)

/-- Dotting from a scaled environment scales the dot value (the environment-side
analog of the sibling's `lfkDotProductScaledVector`). -/
theorem lreDotProductScaledEnv : ∀ (multiplier : Nat) (env coefficientVector : List LfkInt),
    lfkDotProduct (lfkScaleCoefficientVector multiplier env) coefficientVector
      = lfkIntScaleByNat multiplier (lfkDotProduct env coefficientVector)
  | _multiplier, List.nil, List.nil => rfl
  | _multiplier, List.nil, _coefficientHead :: _coefficientTail => rfl
  | _multiplier, _envHead :: _envTail, List.nil => rfl
  | multiplier, envHead :: envTail, coefficientHead :: coefficientTail =>
      (lfkIntAddCongr (lreIntMulScaleLeft multiplier envHead coefficientHead)
          (lreDotProductScaledEnv multiplier envTail coefficientTail)).trans
        (lfkIntScaleAddDistrib multiplier (lfkIntMul envHead coefficientHead)
          (lfkDotProduct envTail coefficientTail)).symm

/-! ## Membership kit — a bespoke recursive `among` predicate (no `List.Mem`) -/

/-- Is the row one of the listed rows?  (Recursive `Or`-of-equalities Prop.) -/
def lreRowIsAmong (row : LfmCertifiedRow) : List LfmCertifiedRow → Prop
  | List.nil => False
  | rowHead :: rowTail => Or (row = rowHead) (lreRowIsAmong row rowTail)

/-- Is every listed row among the universe rows? -/
def lreAllRowsAmong : List LfmCertifiedRow → List LfmCertifiedRow → Prop
  | List.nil, _universeRows => True
  | rowHead :: rowTail, universeRows =>
      And (lreRowIsAmong rowHead universeRows) (lreAllRowsAmong rowTail universeRows)

/-- Membership transports along equality of the member. -/
theorem lreAmongOfEqMember : ∀ (rows : List LfmCertifiedRow) (leftRow rightRow : LfmCertifiedRow),
    leftRow = rightRow → lreRowIsAmong rightRow rows → lreRowIsAmong leftRow rows
  | List.nil, _leftRow, _rightRow, _memberEq, amongWitness => False.elim amongWitness
  | _rowHead :: rowTail, leftRow, rightRow, memberEq, amongWitness =>
      match amongWitness with
      | Or.inl headEq => Or.inl (memberEq.trans headEq)
      | Or.inr tailWitness =>
          Or.inr (lreAmongOfEqMember rowTail leftRow rightRow memberEq tailWitness)

/-- Widening the universe preserves `lreAllRowsAmong`. -/
theorem lreAllRowsAmongExtend :
    ∀ (rows : List LfmCertifiedRow) (extraRow : LfmCertifiedRow)
      (universeRows : List LfmCertifiedRow),
    lreAllRowsAmong rows universeRows → lreAllRowsAmong rows (extraRow :: universeRows)
  | List.nil, _extraRow, _universeRows, _amongWitness => True.intro
  | _rowHead :: rowTail, extraRow, universeRows, amongWitness =>
      And.intro (Or.inr amongWitness.left)
        (lreAllRowsAmongExtend rowTail extraRow universeRows amongWitness.right)

/-- Every list is all-among itself. -/
theorem lreAllRowsAmongSelf : ∀ (rows : List LfmCertifiedRow), lreAllRowsAmong rows rows
  | List.nil => True.intro
  | rowHead :: rowTail =>
      And.intro (Or.inl rfl)
        (lreAllRowsAmongExtend rowTail rowHead rowTail (lreAllRowsAmongSelf rowTail))

/-- A member of a list passing a Bool scan passes the test itself. -/
theorem lreTestPassesOfAmong (rowTest : LfmCertifiedRow → Bool) :
    ∀ (rows : List LfmCertifiedRow) (row : LfmCertifiedRow),
    lreRowIsAmong row rows → lfmAllRowsPass rowTest rows = true → rowTest row = true
  | List.nil, _row, amongWitness, _passWitness => False.elim amongWitness
  | rowHead :: rowTail, row, amongWitness, passWitness =>
      let destructured := lfkBoolAndDestruct (rowTest rowHead)
        (lfmAllRowsPass rowTest rowTail) passWitness
      match amongWitness with
      | Or.inl headEq => (congrArg rowTest headEq).trans destructured.left
      | Or.inr tailWitness =>
          lreTestPassesOfAmong rowTest rowTail row tailWitness destructured.right

/-- Membership in the kept branch of a true `cond`. -/
theorem lreAmongCondOfTrue (row : LfmCertifiedRow)
    (keptRows droppedRows : List LfmCertifiedRow) :
    ∀ (branchFlag : Bool), branchFlag = true → lreRowIsAmong row keptRows →
    lreRowIsAmong row (cond branchFlag keptRows droppedRows)
  | true, _flagWitness, amongWitness => amongWitness
  | false, contradictoryWitness, _amongWitness => Bool.noConfusion contradictoryWitness

/-- Membership in the dropped branch of a false `cond`. -/
theorem lreAmongCondOfFalse (row : LfmCertifiedRow)
    (keptRows droppedRows : List LfmCertifiedRow) :
    ∀ (branchFlag : Bool), branchFlag = false → lreRowIsAmong row droppedRows →
    lreRowIsAmong row (cond branchFlag keptRows droppedRows)
  | false, _flagWitness, amongWitness => amongWitness
  | true, contradictoryWitness, _amongWitness => Bool.noConfusion contradictoryWitness

/-- A member passing the filter test is among the filtered rows. -/
theorem lreAmongFilterOfPass (filterTest : LfmCertifiedRow → Bool) :
    ∀ (rows : List LfmCertifiedRow) (row : LfmCertifiedRow),
    lreRowIsAmong row rows → filterTest row = true →
    lreRowIsAmong row (lfmFilterRowsByTest filterTest rows)
  | List.nil, _row, amongWitness, _testWitness => False.elim amongWitness
  | rowHead :: rowTail, row, amongWitness, testWitness =>
      match amongWitness with
      | Or.inl headEq =>
          lreAmongCondOfTrue row (rowHead :: lfmFilterRowsByTest filterTest rowTail)
            (lfmFilterRowsByTest filterTest rowTail) (filterTest rowHead)
            ((congrArg filterTest headEq).symm.trans testWitness) (Or.inl headEq)
      | Or.inr tailWitness =>
          match lfmBoolCases (filterTest rowHead) with
          | Or.inl headTestTrue =>
              lreAmongCondOfTrue row (rowHead :: lfmFilterRowsByTest filterTest rowTail)
                (lfmFilterRowsByTest filterTest rowTail) (filterTest rowHead) headTestTrue
                (Or.inr (lreAmongFilterOfPass filterTest rowTail row tailWitness testWitness))
          | Or.inr headTestFalse =>
              lreAmongCondOfFalse row (rowHead :: lfmFilterRowsByTest filterTest rowTail)
                (lfmFilterRowsByTest filterTest rowTail) (filterTest rowHead) headTestFalse
                (lreAmongFilterOfPass filterTest rowTail row tailWitness testWitness)

/-- An empty filter output means every member fails the test. -/
theorem lreFilterNilAllFail (filterTest : LfmCertifiedRow → Bool) :
    ∀ (rows : List LfmCertifiedRow),
    lfmFilterRowsByTest filterTest rows = List.nil →
    ∀ (row : LfmCertifiedRow), lreRowIsAmong row rows → filterTest row = false
  | List.nil, _nilWitness, _row, amongWitness => False.elim amongWitness
  | rowHead :: rowTail, nilWitness, row, amongWitness =>
      match lfmBoolCases (filterTest rowHead) with
      | Or.inl headTestTrue =>
          nomatch
            (((congrArg
                (fun probe => cond probe (rowHead :: lfmFilterRowsByTest filterTest rowTail)
                  (lfmFilterRowsByTest filterTest rowTail)) headTestTrue).symm.trans
              nilWitness :
              rowHead :: lfmFilterRowsByTest filterTest rowTail = List.nil))
      | Or.inr headTestFalse =>
          let tailNil : lfmFilterRowsByTest filterTest rowTail = List.nil :=
            ((congrArg
                (fun probe => cond probe (rowHead :: lfmFilterRowsByTest filterTest rowTail)
                  (lfmFilterRowsByTest filterTest rowTail)) headTestFalse).symm.trans
              nilWitness)
          match amongWitness with
          | Or.inl headEq => (congrArg filterTest headEq).trans headTestFalse
          | Or.inr tailWitness =>
              lreFilterNilAllFail filterTest rowTail tailNil row tailWitness

/-- Membership propagates into the join, left side. -/
theorem lreAmongJoinLeft : ∀ (firstRows secondRows : List LfmCertifiedRow)
    (row : LfmCertifiedRow),
    lreRowIsAmong row firstRows → lreRowIsAmong row (lfmJoinRowLists firstRows secondRows)
  | List.nil, _secondRows, _row, amongWitness => False.elim amongWitness
  | _rowHead :: rowTail, secondRows, row, amongWitness =>
      match amongWitness with
      | Or.inl headEq => Or.inl headEq
      | Or.inr tailWitness => Or.inr (lreAmongJoinLeft rowTail secondRows row tailWitness)

/-- Membership propagates into the join, right side. -/
theorem lreAmongJoinRight : ∀ (firstRows secondRows : List LfmCertifiedRow)
    (row : LfmCertifiedRow),
    lreRowIsAmong row secondRows → lreRowIsAmong row (lfmJoinRowLists firstRows secondRows)
  | List.nil, _secondRows, _row, amongWitness => amongWitness
  | _rowHead :: rowTail, secondRows, row, amongWitness =>
      Or.inr (lreAmongJoinRight rowTail secondRows row amongWitness)

/-- The pair combination of a positive row with a listed negative row is among
the one-against-all combinations. -/
theorem lreAmongCombineOne (variableIndex : Nat) (positiveRow : LfmCertifiedRow) :
    ∀ (negativeRows : List LfmCertifiedRow) (negativeRow : LfmCertifiedRow),
    lreRowIsAmong negativeRow negativeRows →
    lreRowIsAmong (lfmCombineRowPair variableIndex positiveRow negativeRow)
      (lfmCombineOneAgainstAll variableIndex positiveRow negativeRows)
  | List.nil, _negativeRow, amongWitness => False.elim amongWitness
  | _negativeHead :: negativeTail, negativeRow, amongWitness =>
      match amongWitness with
      | Or.inl headEq =>
          Or.inl (congrArg (lfmCombineRowPair variableIndex positiveRow) headEq)
      | Or.inr tailWitness =>
          Or.inr (lreAmongCombineOne variableIndex positiveRow negativeTail negativeRow
            tailWitness)

/-- The pair combination of listed positive and negative rows is among the full
cross combination. -/
theorem lreAmongCrossCombine (variableIndex : Nat) :
    ∀ (positiveRows negativeRows : List LfmCertifiedRow)
      (positiveRow negativeRow : LfmCertifiedRow),
    lreRowIsAmong positiveRow positiveRows → lreRowIsAmong negativeRow negativeRows →
    lreRowIsAmong (lfmCombineRowPair variableIndex positiveRow negativeRow)
      (lfmCrossCombineAll variableIndex positiveRows negativeRows)
  | List.nil, _negativeRows, _positiveRow, _negativeRow, amongPositive, _amongNegative =>
      False.elim amongPositive
  | positiveHead :: positiveTail, negativeRows, positiveRow, negativeRow,
      amongPositive, amongNegative =>
      match amongPositive with
      | Or.inl headEq =>
          lreAmongJoinLeft
            (lfmCombineOneAgainstAll variableIndex positiveHead negativeRows)
            (lfmCrossCombineAll variableIndex positiveTail negativeRows)
            (lfmCombineRowPair variableIndex positiveRow negativeRow)
            (lreAmongOfEqMember
              (lfmCombineOneAgainstAll variableIndex positiveHead negativeRows)
              (lfmCombineRowPair variableIndex positiveRow negativeRow)
              (lfmCombineRowPair variableIndex positiveHead negativeRow)
              (congrArg (fun probe => lfmCombineRowPair variableIndex probe negativeRow)
                headEq)
              (lreAmongCombineOne variableIndex positiveHead negativeRows negativeRow
                amongNegative))
      | Or.inr tailWitness =>
          lreAmongJoinRight
            (lfmCombineOneAgainstAll variableIndex positiveHead negativeRows)
            (lfmCrossCombineAll variableIndex positiveTail negativeRows)
            (lfmCombineRowPair variableIndex positiveRow negativeRow)
            (lreAmongCrossCombine variableIndex positiveTail negativeRows positiveRow
              negativeRow tailWitness amongNegative)

/-! ## Scaled-row satisfaction plumbing -/

/-- Scale one constraint's bound (the per-row form of
`lfkScaleBoundsForDenominator`). -/
def lreScaleConstraintBound (denominator : Nat) (constraint : LfkConstraint) : LfkConstraint :=
  LfkConstraint.mk constraint.coefficients
    (lfkIntScaleByNat denominator constraint.bound) constraint.relation

/-- Satisfaction of the scaled row list extracts to any member row. -/
theorem lreRowSatisfiedOfAmong (denominator : Nat) (env : List LfkInt) :
    ∀ (rows : List LfmCertifiedRow) (row : LfmCertifiedRow),
    lreRowIsAmong row rows →
    lfkSatisfiesSystem env
      (lfkScaleBoundsForDenominator denominator (lfmConstraintsOfRows rows)) = true →
    lfkSatisfiesConstraint env (lreScaleConstraintBound denominator row.constraint) = true
  | List.nil, _row, amongWitness, _satWitness => False.elim amongWitness
  | rowHead :: rowTail, row, amongWitness, satWitness =>
      let destructured := lfkBoolAndDestruct
        (lfkSatisfiesConstraint env (lreScaleConstraintBound denominator rowHead.constraint))
        (lfkSatisfiesSystem env
          (lfkScaleBoundsForDenominator denominator (lfmConstraintsOfRows rowTail)))
        satWitness
      match amongWitness with
      | Or.inl headEq =>
          (congrArg
            (fun probe => lfkSatisfiesConstraint env
              (lreScaleConstraintBound denominator probe.constraint)) headEq).trans
            destructured.left
      | Or.inr tailWitness =>
          lreRowSatisfiedOfAmong denominator env rowTail row tailWitness destructured.right

/-- Satisfaction of a joined scaled row list splits into the two halves. -/
theorem lreJoinedRowsSatisfiedSplit (denominator : Nat) (env : List LfkInt) :
    ∀ (firstRows secondRows : List LfmCertifiedRow),
    lfkSatisfiesSystem env
      (lfkScaleBoundsForDenominator denominator
        (lfmConstraintsOfRows (lfmJoinRowLists firstRows secondRows))) = true →
    And
      (lfkSatisfiesSystem env
        (lfkScaleBoundsForDenominator denominator (lfmConstraintsOfRows firstRows)) = true)
      (lfkSatisfiesSystem env
        (lfkScaleBoundsForDenominator denominator (lfmConstraintsOfRows secondRows)) = true)
  | List.nil, _secondRows, satWitness => And.intro rfl satWitness
  | rowHead :: rowTail, secondRows, satWitness =>
      let destructured := lfkBoolAndDestruct
        (lfkSatisfiesConstraint env (lreScaleConstraintBound denominator rowHead.constraint))
        (lfkSatisfiesSystem env
          (lfkScaleBoundsForDenominator denominator
            (lfmConstraintsOfRows (lfmJoinRowLists rowTail secondRows))))
        satWitness
      let tailSplit := lreJoinedRowsSatisfiedSplit denominator env rowTail secondRows
        destructured.right
      And.intro (lfkBoolAndIntro _ _ destructured.left tailSplit.left) tailSplit.right

/-! ## Row endpoint data — rests, lower/upper numerators -/

/-- The pivot-free part of a row's dot value at the given environment. -/
def lreRowRestDotAt (variableIndex : Nat) (env : List LfkInt) (row : LfmCertifiedRow) : LfkInt :=
  lfkDotProduct env (lreZeroCoefficientAt variableIndex row.constraint.coefficients)

/-- The cleared LOWER-endpoint numerator of a positive row:
`denominator·bound − rest` (the rational bound is this over
`denominator·positiveMagnitude`). -/
def lreRowLowerNumeratorAt (variableIndex denominator : Nat) (env : List LfkInt)
    (row : LfmCertifiedRow) : LfkInt :=
  lfkIntAdd (lfkIntScaleByNat denominator row.constraint.bound)
    (lfkIntNegate (lreRowRestDotAt variableIndex env row))

/-- The cleared UPPER-endpoint numerator of a negative row:
`rest − denominator·bound` (the rational bound is this over
`denominator·negativeMagnitude`). -/
def lreRowUpperNumeratorAt (variableIndex denominator : Nat) (env : List LfkInt)
    (row : LfmCertifiedRow) : LfkInt :=
  lfkIntAdd (lreRowRestDotAt variableIndex env row)
    (lfkIntNegate (lfkIntScaleByNat denominator row.constraint.bound))

/-- Any satisfied constraint satisfies its weak-inequality reading. -/
theorem lreSatisfactionGivesWeakLe (env : List LfkInt) :
    ∀ (constraint : LfkConstraint), lfkSatisfiesConstraint env constraint = true →
    lfkIntLe constraint.bound (lfkDotProduct env constraint.coefficients) = true
  | LfkConstraint.mk _coefficientVector _boundValue LfkRelation.isGreaterOrEqual,
      satWitness => satWitness
  | LfkConstraint.mk _coefficientVector _boundValue LfkRelation.isStrictlyGreater,
      satWitness => lfkIntLeOfLt satWitness
  | LfkConstraint.mk _coefficientVector _boundValue LfkRelation.isEqualTo,
      satWitness => lfkIntLeOfEqFlip satWitness

/-- Scaling a strict relation by a positive multiplier keeps it strict. -/
theorem lreScaleRelationStrictOfPositive : ∀ (multiplier : Nat),
    Nat.ble 1 multiplier = true →
    lfkScaleRelation multiplier LfkRelation.isStrictlyGreater
      = LfkRelation.isStrictlyGreater
  | Nat.zero, contradictoryWitness => Bool.noConfusion contradictoryWitness
  | Nat.succ _multiplierPred, _positiveWitness => rfl

/-- A strict left operand makes the join strict. -/
theorem lreJoinStrictLeft : ∀ (rightRelation : LfkRelation),
    lfkJoinRelations LfkRelation.isStrictlyGreater rightRelation
      = LfkRelation.isStrictlyGreater
  | LfkRelation.isGreaterOrEqual => rfl
  | LfkRelation.isStrictlyGreater => rfl
  | LfkRelation.isEqualTo => rfl

/-- A strict right operand makes the join strict. -/
theorem lreJoinStrictRight : ∀ (leftRelation : LfkRelation),
    lfkJoinRelations leftRelation LfkRelation.isStrictlyGreater
      = LfkRelation.isStrictlyGreater
  | LfkRelation.isGreaterOrEqual => rfl
  | LfkRelation.isStrictlyGreater => rfl
  | LfkRelation.isEqualTo => rfl

/-! ## THE COMBO UNFOLD — a satisfied cross combination reads as the scaled
    endpoint inequality `cMag·lowerNum(P) <= aMag·upperNum(N)` -/

/-- The four structural/value forms every combo-unfolding shares: the combined
dot value collapses (cross-sum-equally) to the pivot-free rest sum, and the
scaled bound / scaled lower / scaled upper all decompose into matching
difference shapes. -/
theorem lreComboUnfoldForms (variableIndex denominator : Nat) (env : List LfkInt)
    (positiveRow negativeRow : LfmCertifiedRow)
    (positiveTest : lfmRowHasPositiveCoefficientAt variableIndex positiveRow = true)
    (negativeTest : lfmRowHasNegativeCoefficientAt variableIndex negativeRow = true) :
    And
      (lfkIntEq
        (lfkDotProduct env
          (lfmCombineRowPair variableIndex positiveRow negativeRow).constraint.coefficients)
        (lfkIntAdd
          (lfkIntScaleByNat (lfmNegativeMagnitudeAt variableIndex negativeRow)
            (lreRowRestDotAt variableIndex env positiveRow))
          (lfkIntScaleByNat (lfmPositiveMagnitudeAt variableIndex positiveRow)
            (lreRowRestDotAt variableIndex env negativeRow))) = true)
      (And
        (lfkIntScaleByNat denominator
            (lfmCombineRowPair variableIndex positiveRow negativeRow).constraint.bound
          = lfkIntAdd
              (lfkIntScaleByNat
                (denominator * lfmNegativeMagnitudeAt variableIndex negativeRow)
                positiveRow.constraint.bound)
              (lfkIntScaleByNat
                (denominator * lfmPositiveMagnitudeAt variableIndex positiveRow)
                negativeRow.constraint.bound))
        (And
          (lfkIntScaleByNat (lfmNegativeMagnitudeAt variableIndex negativeRow)
              (lreRowLowerNumeratorAt variableIndex denominator env positiveRow)
            = lfkIntAdd
                (lfkIntScaleByNat
                  (denominator * lfmNegativeMagnitudeAt variableIndex negativeRow)
                  positiveRow.constraint.bound)
                (lfkIntNegate
                  (lfkIntScaleByNat (lfmNegativeMagnitudeAt variableIndex negativeRow)
                    (lreRowRestDotAt variableIndex env positiveRow))))
          (lfkIntScaleByNat (lfmPositiveMagnitudeAt variableIndex positiveRow)
              (lreRowUpperNumeratorAt variableIndex denominator env negativeRow)
            = lfkIntAdd
                (lfkIntScaleByNat (lfmPositiveMagnitudeAt variableIndex positiveRow)
                  (lreRowRestDotAt variableIndex env negativeRow))
                (lfkIntNegate
                  (lfkIntScaleByNat
                    (denominator * lfmPositiveMagnitudeAt variableIndex positiveRow)
                    negativeRow.constraint.bound))))) :=
  let positiveMag := lfmPositiveMagnitudeAt variableIndex positiveRow
  let negativeMag := lfmNegativeMagnitudeAt variableIndex negativeRow
  let coefficientsP := positiveRow.constraint.coefficients
  let coefficientsN := negativeRow.constraint.coefficients
  let boundP := positiveRow.constraint.bound
  let boundN := negativeRow.constraint.bound
  let pivotEntry := lfmCoefficientAtIndex variableIndex env
  let pivotCoeffP := lfmCoefficientAtIndex variableIndex coefficientsP
  let pivotCoeffN := lfmCoefficientAtIndex variableIndex coefficientsN
  let restP := lreRowRestDotAt variableIndex env positiveRow
  let restN := lreRowRestDotAt variableIndex env negativeRow
  let restSum := lfkIntAdd (lfkIntScaleByNat negativeMag restP)
    (lfkIntScaleByNat positiveMag restN)
  let dotStructural : lfkDotProduct env
      (lfmCombineRowPair variableIndex positiveRow negativeRow).constraint.coefficients
      = lfkIntAdd
          (lfkIntScaleByNat negativeMag (lfkIntAdd (lfkIntMul pivotEntry pivotCoeffP) restP))
          (lfkIntScaleByNat positiveMag (lfkIntAdd (lfkIntMul pivotEntry pivotCoeffN) restN)) :=
    (lfkDotProductAddVectors env
        (lfkScaleCoefficientVector negativeMag coefficientsP)
        (lfkScaleCoefficientVector positiveMag coefficientsN)).trans
      ((lfkIntAddCongr (lfkDotProductScaledVector env negativeMag coefficientsP)
          (lfkDotProductScaledVector env positiveMag coefficientsN)).trans
        (lfkIntAddCongr
          (congrArg (lfkIntScaleByNat negativeMag)
            (lreDotProductSplitAt variableIndex env coefficientsP))
          (congrArg (lfkIntScaleByNat positiveMag)
            (lreDotProductSplitAt variableIndex env coefficientsN))))
  let valueEq : lfkIntEq
      (lfkIntAdd
        (lfkIntScaleByNat negativeMag (lfkIntAdd (lfkIntMul pivotEntry pivotCoeffP) restP))
        (lfkIntScaleByNat positiveMag (lfkIntAdd (lfkIntMul pivotEntry pivotCoeffN) restN)))
      (lfkIntAdd
        (lfkIntScaleByNat negativeMag
          (lfkIntAdd (lfkIntScaleByNat positiveMag pivotEntry) restP))
        (lfkIntScaleByNat positiveMag
          (lfkIntAdd (lfkIntNegate (lfkIntScaleByNat negativeMag pivotEntry)) restN)))
      = true :=
    lfkIntAddEqEq
      (lfkIntScaleEqMono negativeMag
        (lfkIntAddEqEq (lreIntMulPositiveEntryCrossEq pivotEntry pivotCoeffP positiveTest)
          (lfkIntEqRefl restP)))
      (lfkIntScaleEqMono positiveMag
        (lfkIntAddEqEq (lreIntMulNegativeEntryCrossEq pivotEntry pivotCoeffN negativeTest)
          (lfkIntEqRefl restN)))
  let middleStructural : lfkIntAdd
      (lfkIntScaleByNat negativeMag
        (lfkIntAdd (lfkIntScaleByNat positiveMag pivotEntry) restP))
      (lfkIntScaleByNat positiveMag
        (lfkIntAdd (lfkIntNegate (lfkIntScaleByNat negativeMag pivotEntry)) restN))
      = lfkIntAdd
          (lfkIntAdd (lfkIntScaleByNat (negativeMag * positiveMag) pivotEntry)
            (lfkIntNegate (lfkIntScaleByNat (positiveMag * negativeMag) pivotEntry)))
          restSum :=
    (lfkIntAddCongr
        ((lfkIntScaleAddDistrib negativeMag (lfkIntScaleByNat positiveMag pivotEntry)
            restP).trans
          (congrArg (fun probe => lfkIntAdd probe (lfkIntScaleByNat negativeMag restP))
            (lfmIntScaleCompose negativeMag positiveMag pivotEntry).symm))
        ((lfkIntScaleAddDistrib positiveMag
            (lfkIntNegate (lfkIntScaleByNat negativeMag pivotEntry)) restN).trans
          (congrArg (fun probe => lfkIntAdd probe (lfkIntScaleByNat positiveMag restN))
            (congrArg lfkIntNegate
              (lfmIntScaleCompose positiveMag negativeMag pivotEntry).symm)))).trans
      (lfkIntAddSwapMiddle (lfkIntScaleByNat (negativeMag * positiveMag) pivotEntry)
        (lfkIntScaleByNat negativeMag restP)
        (lfkIntNegate (lfkIntScaleByNat (positiveMag * negativeMag) pivotEntry))
        (lfkIntScaleByNat positiveMag restN))
  let headZero : lfkIntIsZero
      (lfkIntAdd (lfkIntScaleByNat (negativeMag * positiveMag) pivotEntry)
        (lfkIntNegate (lfkIntScaleByNat (positiveMag * negativeMag) pivotEntry))) = true :=
    (congrArg
        (fun probe => lfkIntIsZero
          (lfkIntAdd (lfkIntScaleByNat (negativeMag * positiveMag) pivotEntry)
            (lfkIntNegate (lfkIntScaleByNat probe pivotEntry))))
        (Nat.mul_comm positiveMag negativeMag)).trans
      (lreIntAddNegateRightZero (lfkIntScaleByNat (negativeMag * positiveMag) pivotEntry))
  let dotAtMiddle : lfkIntEq
      (lfkDotProduct env
        (lfmCombineRowPair variableIndex positiveRow negativeRow).constraint.coefficients)
      (lfkIntAdd
        (lfkIntAdd (lfkIntScaleByNat (negativeMag * positiveMag) pivotEntry)
          (lfkIntNegate (lfkIntScaleByNat (positiveMag * negativeMag) pivotEntry)))
        restSum) = true :=
    (congrArg
        (fun probe => lfkIntEq
          (lfkDotProduct env
            (lfmCombineRowPair variableIndex positiveRow negativeRow).constraint.coefficients)
          probe) middleStructural).symm.trans
      ((congrArg
          (fun probe => lfkIntEq probe
            (lfkIntAdd
              (lfkIntScaleByNat negativeMag
                (lfkIntAdd (lfkIntScaleByNat positiveMag pivotEntry) restP))
              (lfkIntScaleByNat positiveMag
                (lfkIntAdd (lfkIntNegate (lfkIntScaleByNat negativeMag pivotEntry))
                  restN)))) dotStructural).trans
        valueEq)
  And.intro
    (lreIntEqTrans dotAtMiddle (lreIntEqDropZeroLeft headZero))
    (And.intro
      ((lfkIntScaleAddDistrib denominator (lfkIntScaleByNat negativeMag boundP)
          (lfkIntScaleByNat positiveMag boundN)).trans
        (lfkIntAddCongr (lfmIntScaleCompose denominator negativeMag boundP).symm
          (lfmIntScaleCompose denominator positiveMag boundN).symm))
      (And.intro
        ((lfkIntScaleAddDistrib negativeMag (lfkIntScaleByNat denominator boundP)
            (lfkIntNegate restP)).trans
          (congrArg
            (fun probe => lfkIntAdd probe
              (lfkIntNegate (lfkIntScaleByNat negativeMag restP)))
            ((lfmIntScaleCompose negativeMag denominator boundP).symm.trans
              (congrArg (fun probe => lfkIntScaleByNat probe boundP)
                (Nat.mul_comm negativeMag denominator)))))
        ((lfkIntScaleAddDistrib positiveMag restN
            (lfkIntNegate (lfkIntScaleByNat denominator boundN))).trans
          (congrArg
            (fun probe => lfkIntAdd (lfkIntScaleByNat positiveMag restN) probe)
            (congrArg lfkIntNegate
              ((lfmIntScaleCompose positiveMag denominator boundN).symm.trans
                (congrArg (fun probe => lfkIntScaleByNat probe boundN)
                  (Nat.mul_comm positiveMag denominator))))))))

/-- WEAK COMBO BOUND: a satisfied scaled cross combination gives the weak scaled
endpoint inequality — no relation hypotheses at all (strict/equality
satisfaction weakens). -/
theorem lreComboSatisfactionGivesWeakBound (variableIndex denominator : Nat)
    (env : List LfkInt) (positiveRow negativeRow : LfmCertifiedRow)
    (positiveTest : lfmRowHasPositiveCoefficientAt variableIndex positiveRow = true)
    (negativeTest : lfmRowHasNegativeCoefficientAt variableIndex negativeRow = true)
    (comboSatisfied : lfkSatisfiesConstraint env
      (lreScaleConstraintBound denominator
        (lfmCombineRowPair variableIndex positiveRow negativeRow).constraint) = true) :
    lfkIntLe
      (lfkIntScaleByNat (lfmNegativeMagnitudeAt variableIndex negativeRow)
        (lreRowLowerNumeratorAt variableIndex denominator env positiveRow))
      (lfkIntScaleByNat (lfmPositiveMagnitudeAt variableIndex positiveRow)
        (lreRowUpperNumeratorAt variableIndex denominator env negativeRow)) = true :=
  let forms := lreComboUnfoldForms variableIndex denominator env positiveRow negativeRow
    positiveTest negativeTest
  let restSum := lfkIntAdd
    (lfkIntScaleByNat (lfmNegativeMagnitudeAt variableIndex negativeRow)
      (lreRowRestDotAt variableIndex env positiveRow))
    (lfkIntScaleByNat (lfmPositiveMagnitudeAt variableIndex positiveRow)
      (lreRowRestDotAt variableIndex env negativeRow))
  let weakAtDot : lfkIntLe
      (lfkIntScaleByNat denominator
        (lfmCombineRowPair variableIndex positiveRow negativeRow).constraint.bound)
      (lfkDotProduct env
        (lfmCombineRowPair variableIndex positiveRow negativeRow).constraint.coefficients)
      = true :=
    lreSatisfactionGivesWeakLe env
      (lreScaleConstraintBound denominator
        (lfmCombineRowPair variableIndex positiveRow negativeRow).constraint)
      comboSatisfied
  let weakAtRestSum : lfkIntLe
      (lfkIntScaleByNat denominator
        (lfmCombineRowPair variableIndex positiveRow negativeRow).constraint.bound)
      restSum = true :=
    lreIntLeCongrRight forms.left weakAtDot
  let weakSplitInput : lfkIntLe
      (lfkIntAdd
        (lfkIntScaleByNat
          (denominator * lfmNegativeMagnitudeAt variableIndex negativeRow)
          positiveRow.constraint.bound)
        (lfkIntScaleByNat
          (denominator * lfmPositiveMagnitudeAt variableIndex positiveRow)
          negativeRow.constraint.bound))
      restSum = true :=
    (congrArg (fun probe => lfkIntLe probe restSum) forms.right.left).symm.trans
      weakAtRestSum
  ((congrArg
      (fun probe => lfkIntLe probe
        (lfkIntScaleByNat (lfmPositiveMagnitudeAt variableIndex positiveRow)
          (lreRowUpperNumeratorAt variableIndex denominator env negativeRow)))
      forms.right.right.left).trans
    (congrArg
      (fun probe => lfkIntLe
        (lfkIntAdd
          (lfkIntScaleByNat
            (denominator * lfmNegativeMagnitudeAt variableIndex negativeRow)
            positiveRow.constraint.bound)
          (lfkIntNegate
            (lfkIntScaleByNat (lfmNegativeMagnitudeAt variableIndex negativeRow)
              (lreRowRestDotAt variableIndex env positiveRow))))
        probe)
      forms.right.right.right)).trans
    (lreIntLeSplitAcross weakSplitInput)

/-- STRICT COMBO BOUND: when either parent's relation is strict the combination
is strict, and the scaled endpoint inequality holds STRICTLY (the whole-`+1`
integer headroom the midpoint witness spends on ties). -/
theorem lreComboSatisfactionGivesStrictBound (variableIndex denominator : Nat)
    (env : List LfkInt) (positiveRow negativeRow : LfmCertifiedRow)
    (positiveTest : lfmRowHasPositiveCoefficientAt variableIndex positiveRow = true)
    (negativeTest : lfmRowHasNegativeCoefficientAt variableIndex negativeRow = true)
    (strictSource : Or (positiveRow.constraint.relation = LfkRelation.isStrictlyGreater)
      (negativeRow.constraint.relation = LfkRelation.isStrictlyGreater))
    (comboSatisfied : lfkSatisfiesConstraint env
      (lreScaleConstraintBound denominator
        (lfmCombineRowPair variableIndex positiveRow negativeRow).constraint) = true) :
    lfkIntLt
      (lfkIntScaleByNat (lfmNegativeMagnitudeAt variableIndex negativeRow)
        (lreRowLowerNumeratorAt variableIndex denominator env positiveRow))
      (lfkIntScaleByNat (lfmPositiveMagnitudeAt variableIndex positiveRow)
        (lreRowUpperNumeratorAt variableIndex denominator env negativeRow)) = true :=
  let forms := lreComboUnfoldForms variableIndex denominator env positiveRow negativeRow
    positiveTest negativeTest
  let positiveMagPositive : Nat.ble 1 (lfmPositiveMagnitudeAt variableIndex positiveRow)
      = true :=
    lreIntPositiveMagnitudePositive (lfmRowCoefficientAt variableIndex positiveRow)
      positiveTest
  let negativeMagPositive : Nat.ble 1 (lfmNegativeMagnitudeAt variableIndex negativeRow)
      = true :=
    lreIntPositiveMagnitudePositive
      (lfkIntNegate (lfmRowCoefficientAt variableIndex negativeRow)) negativeTest
  let comboRelationStrict :
      (lfmCombineRowPair variableIndex positiveRow negativeRow).constraint.relation
        = LfkRelation.isStrictlyGreater :=
    match strictSource with
    | Or.inl positiveStrict =>
        (congrArg
            (fun probe => lfkJoinRelations
              (lfkScaleRelation (lfmNegativeMagnitudeAt variableIndex negativeRow) probe)
              (lfkScaleRelation (lfmPositiveMagnitudeAt variableIndex positiveRow)
                negativeRow.constraint.relation))
            positiveStrict).trans
          ((congrArg
              (fun probe => lfkJoinRelations probe
                (lfkScaleRelation (lfmPositiveMagnitudeAt variableIndex positiveRow)
                  negativeRow.constraint.relation))
              (lreScaleRelationStrictOfPositive
                (lfmNegativeMagnitudeAt variableIndex negativeRow)
                negativeMagPositive)).trans
            (lreJoinStrictLeft
              (lfkScaleRelation (lfmPositiveMagnitudeAt variableIndex positiveRow)
                negativeRow.constraint.relation)))
    | Or.inr negativeStrict =>
        (congrArg
            (fun probe => lfkJoinRelations
              (lfkScaleRelation (lfmNegativeMagnitudeAt variableIndex negativeRow)
                positiveRow.constraint.relation)
              (lfkScaleRelation (lfmPositiveMagnitudeAt variableIndex positiveRow) probe))
            negativeStrict).trans
          ((congrArg
              (lfkJoinRelations
                (lfkScaleRelation (lfmNegativeMagnitudeAt variableIndex negativeRow)
                  positiveRow.constraint.relation))
              (lreScaleRelationStrictOfPositive
                (lfmPositiveMagnitudeAt variableIndex positiveRow)
                positiveMagPositive)).trans
            (lreJoinStrictRight
              (lfkScaleRelation (lfmNegativeMagnitudeAt variableIndex negativeRow)
                positiveRow.constraint.relation)))
  let restSum := lfkIntAdd
    (lfkIntScaleByNat (lfmNegativeMagnitudeAt variableIndex negativeRow)
      (lreRowRestDotAt variableIndex env positiveRow))
    (lfkIntScaleByNat (lfmPositiveMagnitudeAt variableIndex positiveRow)
      (lreRowRestDotAt variableIndex env negativeRow))
  let strictAtDot : lfkIntLt
      (lfkIntScaleByNat denominator
        (lfmCombineRowPair variableIndex positiveRow negativeRow).constraint.bound)
      (lfkDotProduct env
        (lfmCombineRowPair variableIndex positiveRow negativeRow).constraint.coefficients)
      = true :=
    (congrArg
        (fun probe => lfkSatisfiesConstraint env
          (LfkConstraint.mk
            (lfmCombineRowPair variableIndex positiveRow negativeRow).constraint.coefficients
            (lfkIntScaleByNat denominator
              (lfmCombineRowPair variableIndex positiveRow negativeRow).constraint.bound)
            probe))
        comboRelationStrict).symm.trans comboSatisfied
  let strictAtRestSum : lfkIntLt
      (lfkIntScaleByNat denominator
        (lfmCombineRowPair variableIndex positiveRow negativeRow).constraint.bound)
      restSum = true :=
    lreIntLtCongrRight forms.left strictAtDot
  let strictSplitInput : lfkIntLt
      (lfkIntAdd
        (lfkIntScaleByNat
          (denominator * lfmNegativeMagnitudeAt variableIndex negativeRow)
          positiveRow.constraint.bound)
        (lfkIntScaleByNat
          (denominator * lfmPositiveMagnitudeAt variableIndex positiveRow)
          negativeRow.constraint.bound))
      restSum = true :=
    (congrArg (fun probe => lfkIntLt probe restSum) forms.right.left).symm.trans
      strictAtRestSum
  ((congrArg
      (fun probe => lfkIntLt probe
        (lfkIntScaleByNat (lfmPositiveMagnitudeAt variableIndex positiveRow)
          (lreRowUpperNumeratorAt variableIndex denominator env negativeRow)))
      forms.right.right.left).trans
    (congrArg
      (fun probe => lfkIntLt
        (lfkIntAdd
          (lfkIntScaleByNat
            (denominator * lfmNegativeMagnitudeAt variableIndex negativeRow)
            positiveRow.constraint.bound)
          (lfkIntNegate
            (lfkIntScaleByNat (lfmNegativeMagnitudeAt variableIndex negativeRow)
              (lreRowRestDotAt variableIndex env positiveRow))))
        probe)
      forms.right.right.right)).trans
    (lreIntLtSplitAcross strictSplitInput)

/-! ## Endpoint arithmetic cores — midpoint and lone-bucket witnesses -/

/-- A failed `<=` flips to the reverse `<=` (totality of the cross-sum order). -/
theorem lreIntLeFalseFlip {leftValue rightValue : LfkInt}
    (falseWitness : lfkIntLe leftValue rightValue = false) :
    lfkIntLe rightValue leftValue = true :=
  lfmNatBleWeakenFromSucc (rightValue.positivePart + leftValue.negativePart)
    (leftValue.positivePart + rightValue.negativePart)
    (lfmNatBleFalseFlipStrict (leftValue.positivePart + rightValue.negativePart)
      (rightValue.positivePart + leftValue.negativePart) falseWitness)

/-- Structural transport for `<=`: rewrite both endpoints along plain
equalities (the Eq-side companion of the cross-sum congruence lemmas). -/
theorem lreIntLeTermTransport {leftTarget leftRewritten rightTarget rightRewritten : LfkInt}
    (leftEq : leftTarget = leftRewritten) (rightEq : rightTarget = rightRewritten)
    (boundWitness : lfkIntLe leftRewritten rightRewritten = true) :
    lfkIntLe leftTarget rightTarget = true :=
  ((congrArg (fun probe => lfkIntLe probe rightTarget) leftEq).trans
    (congrArg (fun probe => lfkIntLe leftRewritten probe) rightEq)).trans boundWitness

/-- Structural transport for `<`. -/
theorem lreIntLtTermTransport {leftTarget leftRewritten rightTarget rightRewritten : LfkInt}
    (leftEq : leftTarget = leftRewritten) (rightEq : rightTarget = rightRewritten)
    (strictWitness : lfkIntLt leftRewritten rightRewritten = true) :
    lfkIntLt leftTarget rightTarget = true :=
  ((congrArg (fun probe => lfkIntLt probe rightTarget) leftEq).trans
    (congrArg (fun probe => lfkIntLt leftRewritten probe) rightEq)).trans strictWitness

/-- THE GENERIC DOMINANCE TRANSITIVITY: two cross-multiplied endpoint
comparisons chain, cancelling the shared positive middle magnitude. -/
theorem lreIntScaledDominanceTrans (firstMag secondMag thirdMag : Nat)
    (firstValue secondValue thirdValue : LfkInt)
    (secondMagPositive : Nat.ble 1 secondMag = true)
    (firstBound : lfkIntLe (lfkIntScaleByNat firstMag secondValue)
      (lfkIntScaleByNat secondMag firstValue) = true)
    (secondBound : lfkIntLe (lfkIntScaleByNat secondMag thirdValue)
      (lfkIntScaleByNat thirdMag secondValue) = true) :
    lfkIntLe (lfkIntScaleByNat firstMag thirdValue)
      (lfkIntScaleByNat thirdMag firstValue) = true :=
  let liftedFirst : lfkIntLe (lfkIntScaleByNat (thirdMag * firstMag) secondValue)
      (lfkIntScaleByNat (thirdMag * secondMag) firstValue) = true :=
    lreIntLeTermTransport (lfmIntScaleCompose thirdMag firstMag secondValue)
      (lfmIntScaleCompose thirdMag secondMag firstValue)
      (lfkIntScaleLeMono thirdMag firstBound)
  let liftedSecond : lfkIntLe (lfkIntScaleByNat (firstMag * secondMag) thirdValue)
      (lfkIntScaleByNat (thirdMag * firstMag) secondValue) = true :=
    lreIntLeTermTransport (lfmIntScaleCompose firstMag secondMag thirdValue)
      ((congrArg (fun probe => lfkIntScaleByNat probe secondValue)
          (Nat.mul_comm thirdMag firstMag)).trans
        (lfmIntScaleCompose firstMag thirdMag secondValue))
      (lfkIntScaleLeMono firstMag secondBound)
  let reorderedChained : lfkIntLe
      (lfkIntScaleByNat secondMag (lfkIntScaleByNat firstMag thirdValue))
      (lfkIntScaleByNat secondMag (lfkIntScaleByNat thirdMag firstValue)) = true :=
    lreIntLeTermTransport
      ((lfmIntScaleCompose secondMag firstMag thirdValue).symm.trans
        (congrArg (fun probe => lfkIntScaleByNat probe thirdValue)
          (Nat.mul_comm secondMag firstMag)))
      ((lfmIntScaleCompose secondMag thirdMag firstValue).symm.trans
        (congrArg (fun probe => lfkIntScaleByNat probe firstValue)
          (Nat.mul_comm secondMag thirdMag)))
      (lreIntLeTrans liftedSecond liftedFirst)
  Exists.elim (lrePositiveSuccShape secondMag secondMagPositive)
    (fun magnitudePred shapeEq =>
      lreIntLeCancelScale magnitudePred
        ((congrArg
            (fun probe => lfkIntLe
              (lfkIntScaleByNat probe (lfkIntScaleByNat firstMag thirdValue))
              (lfkIntScaleByNat probe (lfkIntScaleByNat thirdMag firstValue)))
            shapeEq).symm.trans reorderedChained))

/-- MIDPOINT LOWER CORE (weak): with the doubled scale
`S := aStar·cStar + aStar·cStar` and the midpoint witness
`t := cStar·LStar + aStar·UStar`, lower dominance plus the weak combo bound
give `S·LP <= aP·t`. -/
theorem lreMidpointLowerWeakCore (targetMag lowerStarMag upperStarMag : Nat)
    (targetLower lowerStar upperStar : LfkInt)
    (dominanceFact : lfkIntLe (lfkIntScaleByNat lowerStarMag targetLower)
      (lfkIntScaleByNat targetMag lowerStar) = true)
    (comboFact : lfkIntLe (lfkIntScaleByNat upperStarMag targetLower)
      (lfkIntScaleByNat targetMag upperStar) = true) :
    lfkIntLe
      (lfkIntScaleByNat (lowerStarMag * upperStarMag + lowerStarMag * upperStarMag)
        targetLower)
      (lfkIntScaleByNat targetMag
        (lfkIntAdd (lfkIntScaleByNat upperStarMag lowerStar)
          (lfkIntScaleByNat lowerStarMag upperStar))) = true :=
  let liftedDominance : lfkIntLe
      (lfkIntScaleByNat (lowerStarMag * upperStarMag) targetLower)
      (lfkIntScaleByNat targetMag (lfkIntScaleByNat upperStarMag lowerStar)) = true :=
    lreIntLeTermTransport
      ((congrArg (fun probe => lfkIntScaleByNat probe targetLower)
          (Nat.mul_comm lowerStarMag upperStarMag)).trans
        (lfmIntScaleCompose upperStarMag lowerStarMag targetLower))
      ((lfmIntScaleCompose targetMag upperStarMag lowerStar).symm.trans
        ((congrArg (fun probe => lfkIntScaleByNat probe lowerStar)
            (Nat.mul_comm targetMag upperStarMag)).trans
          (lfmIntScaleCompose upperStarMag targetMag lowerStar)))
      (lfkIntScaleLeMono upperStarMag dominanceFact)
  let liftedCombo : lfkIntLe
      (lfkIntScaleByNat (lowerStarMag * upperStarMag) targetLower)
      (lfkIntScaleByNat targetMag (lfkIntScaleByNat lowerStarMag upperStar)) = true :=
    lreIntLeTermTransport (lfmIntScaleCompose lowerStarMag upperStarMag targetLower)
      ((lfmIntScaleCompose targetMag lowerStarMag upperStar).symm.trans
        ((congrArg (fun probe => lfkIntScaleByNat probe upperStar)
            (Nat.mul_comm targetMag lowerStarMag)).trans
          (lfmIntScaleCompose lowerStarMag targetMag upperStar)))
      (lfkIntScaleLeMono lowerStarMag comboFact)
  lreIntLeTermTransport
    (lfmIntScaleAddMultipliers (lowerStarMag * upperStarMag)
      (lowerStarMag * upperStarMag) targetLower)
    (lfkIntScaleAddDistrib targetMag (lfkIntScaleByNat upperStarMag lowerStar)
      (lfkIntScaleByNat lowerStarMag upperStar))
    (lfkIntAddLeAdd liftedDominance liftedCombo)

/-- MIDPOINT LOWER CORE (strict): a STRICT combo bound upgrades the midpoint
inequality to strict (the strict-parent whole-unit headroom). -/
theorem lreMidpointLowerStrictCore (targetMag lowerStarMag upperStarMag : Nat)
    (targetLower lowerStar upperStar : LfkInt)
    (lowerStarMagPositive : Nat.ble 1 lowerStarMag = true)
    (dominanceFact : lfkIntLe (lfkIntScaleByNat lowerStarMag targetLower)
      (lfkIntScaleByNat targetMag lowerStar) = true)
    (strictComboFact : lfkIntLt (lfkIntScaleByNat upperStarMag targetLower)
      (lfkIntScaleByNat targetMag upperStar) = true) :
    lfkIntLt
      (lfkIntScaleByNat (lowerStarMag * upperStarMag + lowerStarMag * upperStarMag)
        targetLower)
      (lfkIntScaleByNat targetMag
        (lfkIntAdd (lfkIntScaleByNat upperStarMag lowerStar)
          (lfkIntScaleByNat lowerStarMag upperStar))) = true :=
  let liftedDominance : lfkIntLe
      (lfkIntScaleByNat (lowerStarMag * upperStarMag) targetLower)
      (lfkIntScaleByNat targetMag (lfkIntScaleByNat upperStarMag lowerStar)) = true :=
    lreIntLeTermTransport
      ((congrArg (fun probe => lfkIntScaleByNat probe targetLower)
          (Nat.mul_comm lowerStarMag upperStarMag)).trans
        (lfmIntScaleCompose upperStarMag lowerStarMag targetLower))
      ((lfmIntScaleCompose targetMag upperStarMag lowerStar).symm.trans
        ((congrArg (fun probe => lfkIntScaleByNat probe lowerStar)
            (Nat.mul_comm targetMag upperStarMag)).trans
          (lfmIntScaleCompose upperStarMag targetMag lowerStar)))
      (lfkIntScaleLeMono upperStarMag dominanceFact)
  let liftedStrictCombo : lfkIntLt
      (lfkIntScaleByNat (lowerStarMag * upperStarMag) targetLower)
      (lfkIntScaleByNat targetMag (lfkIntScaleByNat lowerStarMag upperStar)) = true :=
    Exists.elim (lrePositiveSuccShape lowerStarMag lowerStarMagPositive)
      (fun magnitudePred shapeEq =>
        lreIntLtTermTransport (lfmIntScaleCompose lowerStarMag upperStarMag targetLower)
          ((lfmIntScaleCompose targetMag lowerStarMag upperStar).symm.trans
            ((congrArg (fun probe => lfkIntScaleByNat probe upperStar)
                (Nat.mul_comm targetMag lowerStarMag)).trans
              (lfmIntScaleCompose lowerStarMag targetMag upperStar)))
          ((congrArg
              (fun probe => lfkIntLt
                (lfkIntScaleByNat probe (lfkIntScaleByNat upperStarMag targetLower))
                (lfkIntScaleByNat probe (lfkIntScaleByNat targetMag upperStar)))
              shapeEq).trans
            (lreIntScaleLtMono magnitudePred strictComboFact)))
  lreIntLtTermTransport
    (lfmIntScaleAddMultipliers (lowerStarMag * upperStarMag)
      (lowerStarMag * upperStarMag) targetLower)
    (lfkIntScaleAddDistrib targetMag (lfkIntScaleByNat upperStarMag lowerStar)
      (lfkIntScaleByNat lowerStarMag upperStar))
    (lfkIntAddLeLt liftedDominance liftedStrictCombo)

/-- MIDPOINT UPPER CORE (weak): the mirrored inequality for negative rows —
combo bound through the best lower plus upper dominance give
`cN·t <= S·UN`. -/
theorem lreMidpointUpperWeakCore (targetMag lowerStarMag upperStarMag : Nat)
    (targetUpper lowerStar upperStar : LfkInt)
    (comboFact : lfkIntLe (lfkIntScaleByNat targetMag lowerStar)
      (lfkIntScaleByNat lowerStarMag targetUpper) = true)
    (dominanceFact : lfkIntLe (lfkIntScaleByNat targetMag upperStar)
      (lfkIntScaleByNat upperStarMag targetUpper) = true) :
    lfkIntLe
      (lfkIntScaleByNat targetMag
        (lfkIntAdd (lfkIntScaleByNat upperStarMag lowerStar)
          (lfkIntScaleByNat lowerStarMag upperStar)))
      (lfkIntScaleByNat (lowerStarMag * upperStarMag + lowerStarMag * upperStarMag)
        targetUpper) = true :=
  let liftedCombo : lfkIntLe
      (lfkIntScaleByNat targetMag (lfkIntScaleByNat upperStarMag lowerStar))
      (lfkIntScaleByNat (lowerStarMag * upperStarMag) targetUpper) = true :=
    lreIntLeTermTransport
      ((lfmIntScaleCompose targetMag upperStarMag lowerStar).symm.trans
        ((congrArg (fun probe => lfkIntScaleByNat probe lowerStar)
            (Nat.mul_comm targetMag upperStarMag)).trans
          (lfmIntScaleCompose upperStarMag targetMag lowerStar)))
      ((congrArg (fun probe => lfkIntScaleByNat probe targetUpper)
          (Nat.mul_comm lowerStarMag upperStarMag)).trans
        (lfmIntScaleCompose upperStarMag lowerStarMag targetUpper))
      (lfkIntScaleLeMono upperStarMag comboFact)
  let liftedDominance : lfkIntLe
      (lfkIntScaleByNat targetMag (lfkIntScaleByNat lowerStarMag upperStar))
      (lfkIntScaleByNat (lowerStarMag * upperStarMag) targetUpper) = true :=
    lreIntLeTermTransport
      ((lfmIntScaleCompose targetMag lowerStarMag upperStar).symm.trans
        ((congrArg (fun probe => lfkIntScaleByNat probe upperStar)
            (Nat.mul_comm targetMag lowerStarMag)).trans
          (lfmIntScaleCompose lowerStarMag targetMag upperStar)))
      (lfmIntScaleCompose lowerStarMag upperStarMag targetUpper)
      (lfkIntScaleLeMono lowerStarMag dominanceFact)
  lreIntLeTermTransport
    (lfkIntScaleAddDistrib targetMag (lfkIntScaleByNat upperStarMag lowerStar)
      (lfkIntScaleByNat lowerStarMag upperStar))
    (lfmIntScaleAddMultipliers (lowerStarMag * upperStarMag)
      (lowerStarMag * upperStarMag) targetUpper)
    (lfkIntAddLeAdd liftedCombo liftedDominance)

/-- MIDPOINT UPPER CORE (strict): a STRICT combo bound upgrades the mirrored
midpoint inequality to strict. -/
theorem lreMidpointUpperStrictCore (targetMag lowerStarMag upperStarMag : Nat)
    (targetUpper lowerStar upperStar : LfkInt)
    (upperStarMagPositive : Nat.ble 1 upperStarMag = true)
    (strictComboFact : lfkIntLt (lfkIntScaleByNat targetMag lowerStar)
      (lfkIntScaleByNat lowerStarMag targetUpper) = true)
    (dominanceFact : lfkIntLe (lfkIntScaleByNat targetMag upperStar)
      (lfkIntScaleByNat upperStarMag targetUpper) = true) :
    lfkIntLt
      (lfkIntScaleByNat targetMag
        (lfkIntAdd (lfkIntScaleByNat upperStarMag lowerStar)
          (lfkIntScaleByNat lowerStarMag upperStar)))
      (lfkIntScaleByNat (lowerStarMag * upperStarMag + lowerStarMag * upperStarMag)
        targetUpper) = true :=
  let liftedStrictCombo : lfkIntLt
      (lfkIntScaleByNat targetMag (lfkIntScaleByNat upperStarMag lowerStar))
      (lfkIntScaleByNat (lowerStarMag * upperStarMag) targetUpper) = true :=
    Exists.elim (lrePositiveSuccShape upperStarMag upperStarMagPositive)
      (fun magnitudePred shapeEq =>
        lreIntLtTermTransport
          ((lfmIntScaleCompose targetMag upperStarMag lowerStar).symm.trans
            ((congrArg (fun probe => lfkIntScaleByNat probe lowerStar)
                (Nat.mul_comm targetMag upperStarMag)).trans
              (lfmIntScaleCompose upperStarMag targetMag lowerStar)))
          ((congrArg (fun probe => lfkIntScaleByNat probe targetUpper)
              (Nat.mul_comm lowerStarMag upperStarMag)).trans
            (lfmIntScaleCompose upperStarMag lowerStarMag targetUpper))
          ((congrArg
              (fun probe => lfkIntLt
                (lfkIntScaleByNat probe (lfkIntScaleByNat targetMag lowerStar))
                (lfkIntScaleByNat probe (lfkIntScaleByNat lowerStarMag targetUpper)))
              shapeEq).trans
            (lreIntScaleLtMono magnitudePred strictComboFact)))
  let liftedDominance : lfkIntLe
      (lfkIntScaleByNat targetMag (lfkIntScaleByNat lowerStarMag upperStar))
      (lfkIntScaleByNat (lowerStarMag * upperStarMag) targetUpper) = true :=
    lreIntLeTermTransport
      ((lfmIntScaleCompose targetMag lowerStarMag upperStar).symm.trans
        ((congrArg (fun probe => lfkIntScaleByNat probe upperStar)
            (Nat.mul_comm targetMag lowerStarMag)).trans
          (lfmIntScaleCompose lowerStarMag targetMag upperStar)))
      (lfmIntScaleCompose lowerStarMag upperStarMag targetUpper)
      (lfkIntScaleLeMono lowerStarMag dominanceFact)
  lreIntLtTermTransport
    (lfkIntScaleAddDistrib targetMag (lfkIntScaleByNat upperStarMag lowerStar)
      (lfkIntScaleByNat lowerStarMag upperStar))
    (lfmIntScaleAddMultipliers (lowerStarMag * upperStarMag)
      (lowerStarMag * upperStarMag) targetUpper)
    (lfkIntAddLtLe liftedStrictCombo liftedDominance)

/-- LONE LOWER CORE: with no upper rows the witness pads a whole denominator
unit above the best lower bound — STRICTLY above every scaled lower bound, so
weak and strict rows are both covered. -/
theorem lreLoneLowerEndpointCore (targetMag bestMag padAmount : Nat)
    (targetLower bestLower : LfkInt)
    (targetMagPositive : Nat.ble 1 targetMag = true)
    (padPositive : Nat.ble 1 padAmount = true)
    (dominanceFact : lfkIntLe (lfkIntScaleByNat bestMag targetLower)
      (lfkIntScaleByNat targetMag bestLower) = true) :
    lfkIntLt (lfkIntScaleByNat bestMag targetLower)
      (lfkIntScaleByNat targetMag
        (lfkIntAdd bestLower (lreIntOfNat padAmount))) = true :=
  (congrArg
      (fun probe => lfkIntLt (lfkIntScaleByNat bestMag targetLower) probe)
      (lfkIntScaleAddDistrib targetMag bestLower (lreIntOfNat padAmount))).trans
    (lreIntLtOfLeAddPositive
      (lreIntOfNatIsPositive (targetMag * padAmount)
        (lreNatPositiveMulPositive targetMag padAmount targetMagPositive padPositive))
      dominanceFact)

/-- LONE UPPER CORE: with no lower rows the witness sits a whole denominator
unit below the best upper bound — STRICTLY below every scaled upper bound. -/
theorem lreLoneUpperEndpointCore (targetMag bestMag padAmount : Nat)
    (targetUpper bestUpper : LfkInt)
    (targetMagPositive : Nat.ble 1 targetMag = true)
    (padPositive : Nat.ble 1 padAmount = true)
    (dominanceFact : lfkIntLe (lfkIntScaleByNat targetMag bestUpper)
      (lfkIntScaleByNat bestMag targetUpper) = true) :
    lfkIntLt
      (lfkIntScaleByNat targetMag
        (lfkIntAdd bestUpper (lfkIntNegate (lreIntOfNat padAmount))))
      (lfkIntScaleByNat bestMag targetUpper) = true :=
  (congrArg
      (fun probe => lfkIntLt probe (lfkIntScaleByNat bestMag targetUpper))
      (lfkIntScaleAddDistrib targetMag bestUpper
        (lfkIntNegate (lreIntOfNat padAmount)))).trans
    (lreIntLtOfLeSubPositive
      (lreIntOfNatIsPositive (targetMag * padAmount)
        (lreNatPositiveMulPositive targetMag padAmount targetMagPositive padPositive))
      dominanceFact)

/-! ## The dominating-row selection fold (constructive max/min endpoint) -/

/-- Running-best fold: keep the current best while it survives the comparison,
otherwise adopt the candidate. -/
def lreSelectDominatingRow (shouldKeepCurrent : LfmCertifiedRow → LfmCertifiedRow → Bool) :
    LfmCertifiedRow → List LfmCertifiedRow → LfmCertifiedRow
  | currentBest, List.nil => currentBest
  | currentBest, candidateHead :: candidateTail =>
      lreSelectDominatingRow shouldKeepCurrent
        (cond (shouldKeepCurrent currentBest candidateHead) currentBest candidateHead)
        candidateTail

/-- THE FOLD INVARIANT: given reflexivity, comparison totality (flip), and
transitivity over test-passing rows, the selected row is among the seeded list
and dominates the seed and every candidate. -/
theorem lreSelectDominatingRowSound
    (shouldKeepCurrent : LfmCertifiedRow → LfmCertifiedRow → Bool)
    (rowTest : LfmCertifiedRow → Bool)
    (reflStep : ∀ (row : LfmCertifiedRow), shouldKeepCurrent row row = true)
    (flipStep : ∀ (leftRow rightRow : LfmCertifiedRow),
      shouldKeepCurrent leftRow rightRow = false →
      shouldKeepCurrent rightRow leftRow = true)
    (transStep : ∀ (firstRow secondRow thirdRow : LfmCertifiedRow),
      rowTest firstRow = true → rowTest secondRow = true → rowTest thirdRow = true →
      shouldKeepCurrent firstRow secondRow = true →
      shouldKeepCurrent secondRow thirdRow = true →
      shouldKeepCurrent firstRow thirdRow = true) :
    ∀ (candidates : List LfmCertifiedRow) (currentBest : LfmCertifiedRow),
    rowTest currentBest = true → lfmAllRowsPass rowTest candidates = true →
    And
      (lreRowIsAmong (lreSelectDominatingRow shouldKeepCurrent currentBest candidates)
        (currentBest :: candidates))
      (And
        (shouldKeepCurrent
          (lreSelectDominatingRow shouldKeepCurrent currentBest candidates)
          currentBest = true)
        (∀ (candidateRow : LfmCertifiedRow), lreRowIsAmong candidateRow candidates →
          shouldKeepCurrent
            (lreSelectDominatingRow shouldKeepCurrent currentBest candidates)
            candidateRow = true))
  | List.nil, currentBest, _testWitness, _passWitness =>
      And.intro (Or.inl rfl)
        (And.intro (reflStep currentBest)
          (fun _candidateRow amongWitness => False.elim amongWitness))
  | candidateHead :: candidateTail, currentBest, testWitness, passWitness =>
      let destructured := lfkBoolAndDestruct (rowTest candidateHead)
        (lfmAllRowsPass rowTest candidateTail) passWitness
      match lfmBoolCases (shouldKeepCurrent currentBest candidateHead) with
      | Or.inl keepTrue =>
          let nextEq : cond (shouldKeepCurrent currentBest candidateHead) currentBest
              candidateHead = currentBest :=
            congrArg (fun probe => cond probe currentBest candidateHead) keepTrue
          let nextTest : rowTest (cond (shouldKeepCurrent currentBest candidateHead)
              currentBest candidateHead) = true :=
            (congrArg rowTest nextEq).trans testWitness
          let recursed := lreSelectDominatingRowSound shouldKeepCurrent rowTest reflStep
            flipStep transStep candidateTail
            (cond (shouldKeepCurrent currentBest candidateHead) currentBest candidateHead)
            nextTest destructured.right
          let selectedRow := lreSelectDominatingRow shouldKeepCurrent
            (cond (shouldKeepCurrent currentBest candidateHead) currentBest candidateHead)
            candidateTail
          let selectedTest : rowTest selectedRow = true :=
            lreTestPassesOfAmong rowTest
              (cond (shouldKeepCurrent currentBest candidateHead) currentBest candidateHead
                :: candidateTail)
              selectedRow recursed.left
              (lfkBoolAndIntro _ _ nextTest destructured.right)
          let keepsCurrent : shouldKeepCurrent selectedRow currentBest = true :=
            (congrArg (shouldKeepCurrent selectedRow) nextEq).symm.trans
              recursed.right.left
          let keepsHead : shouldKeepCurrent selectedRow candidateHead = true :=
            transStep selectedRow currentBest candidateHead selectedTest testWitness
              destructured.left keepsCurrent keepTrue
          And.intro
            (match recursed.left with
             | Or.inl selectedEq => Or.inl (selectedEq.trans nextEq)
             | Or.inr amongTail => Or.inr (Or.inr amongTail))
            (And.intro keepsCurrent
              (fun candidateRow amongWitness =>
                match amongWitness with
                | Or.inl headEq =>
                    (congrArg (shouldKeepCurrent selectedRow) headEq).trans keepsHead
                | Or.inr tailWitness => recursed.right.right candidateRow tailWitness))
      | Or.inr keepFalse =>
          let nextEq : cond (shouldKeepCurrent currentBest candidateHead) currentBest
              candidateHead = candidateHead :=
            congrArg (fun probe => cond probe currentBest candidateHead) keepFalse
          let nextTest : rowTest (cond (shouldKeepCurrent currentBest candidateHead)
              currentBest candidateHead) = true :=
            (congrArg rowTest nextEq).trans destructured.left
          let recursed := lreSelectDominatingRowSound shouldKeepCurrent rowTest reflStep
            flipStep transStep candidateTail
            (cond (shouldKeepCurrent currentBest candidateHead) currentBest candidateHead)
            nextTest destructured.right
          let selectedRow := lreSelectDominatingRow shouldKeepCurrent
            (cond (shouldKeepCurrent currentBest candidateHead) currentBest candidateHead)
            candidateTail
          let selectedTest : rowTest selectedRow = true :=
            lreTestPassesOfAmong rowTest
              (cond (shouldKeepCurrent currentBest candidateHead) currentBest candidateHead
                :: candidateTail)
              selectedRow recursed.left
              (lfkBoolAndIntro _ _ nextTest destructured.right)
          let keepsHead : shouldKeepCurrent selectedRow candidateHead = true :=
            (congrArg (shouldKeepCurrent selectedRow) nextEq).symm.trans
              recursed.right.left
          let keepsCurrent : shouldKeepCurrent selectedRow currentBest = true :=
            transStep selectedRow candidateHead currentBest selectedTest
              destructured.left testWitness keepsHead
              (flipStep currentBest candidateHead keepFalse)
          And.intro
            (match recursed.left with
             | Or.inl selectedEq => Or.inr (Or.inl (selectedEq.trans nextEq))
             | Or.inr amongTail => Or.inr (Or.inr amongTail))
            (And.intro keepsCurrent
              (fun candidateRow amongWitness =>
                match amongWitness with
                | Or.inl headEq =>
                    (congrArg (shouldKeepCurrent selectedRow) headEq).trans keepsHead
                | Or.inr tailWitness => recursed.right.right candidateRow tailWitness))

/-- The lower-endpoint dominance comparison: does the left row's scaled lower
bound sit at or above the right row's? -/
def lreLowerDominates (variableIndex denominator : Nat) (env : List LfkInt)
    (leftRow rightRow : LfmCertifiedRow) : Bool :=
  lfkIntLe
    (lfkIntScaleByNat (lfmPositiveMagnitudeAt variableIndex leftRow)
      (lreRowLowerNumeratorAt variableIndex denominator env rightRow))
    (lfkIntScaleByNat (lfmPositiveMagnitudeAt variableIndex rightRow)
      (lreRowLowerNumeratorAt variableIndex denominator env leftRow))

/-- The upper-endpoint dominance comparison: does the left row's scaled upper
bound sit at or below the right row's? -/
def lreUpperDominates (variableIndex denominator : Nat) (env : List LfkInt)
    (leftRow rightRow : LfmCertifiedRow) : Bool :=
  lfkIntLe
    (lfkIntScaleByNat (lfmNegativeMagnitudeAt variableIndex rightRow)
      (lreRowUpperNumeratorAt variableIndex denominator env leftRow))
    (lfkIntScaleByNat (lfmNegativeMagnitudeAt variableIndex leftRow)
      (lreRowUpperNumeratorAt variableIndex denominator env rightRow))

/-- Lower dominance is transitive over the positive bucket (the generic
cancellation core instantiated). -/
theorem lreLowerDominatesTrans (variableIndex denominator : Nat) (env : List LfkInt)
    (firstRow secondRow thirdRow : LfmCertifiedRow)
    (_firstTest : lfmRowHasPositiveCoefficientAt variableIndex firstRow = true)
    (secondTest : lfmRowHasPositiveCoefficientAt variableIndex secondRow = true)
    (_thirdTest : lfmRowHasPositiveCoefficientAt variableIndex thirdRow = true)
    (firstDominates : lreLowerDominates variableIndex denominator env firstRow secondRow
      = true)
    (secondDominates : lreLowerDominates variableIndex denominator env secondRow thirdRow
      = true) :
    lreLowerDominates variableIndex denominator env firstRow thirdRow = true :=
  lreIntScaledDominanceTrans (lfmPositiveMagnitudeAt variableIndex firstRow)
    (lfmPositiveMagnitudeAt variableIndex secondRow)
    (lfmPositiveMagnitudeAt variableIndex thirdRow)
    (lreRowLowerNumeratorAt variableIndex denominator env firstRow)
    (lreRowLowerNumeratorAt variableIndex denominator env secondRow)
    (lreRowLowerNumeratorAt variableIndex denominator env thirdRow)
    (lreIntPositiveMagnitudePositive (lfmRowCoefficientAt variableIndex secondRow)
      secondTest)
    firstDominates secondDominates

/-- Upper dominance is transitive over the negative bucket. -/
theorem lreUpperDominatesTrans (variableIndex denominator : Nat) (env : List LfkInt)
    (firstRow secondRow thirdRow : LfmCertifiedRow)
    (_firstTest : lfmRowHasNegativeCoefficientAt variableIndex firstRow = true)
    (secondTest : lfmRowHasNegativeCoefficientAt variableIndex secondRow = true)
    (_thirdTest : lfmRowHasNegativeCoefficientAt variableIndex thirdRow = true)
    (firstDominates : lreUpperDominates variableIndex denominator env firstRow secondRow
      = true)
    (secondDominates : lreUpperDominates variableIndex denominator env secondRow thirdRow
      = true) :
    lreUpperDominates variableIndex denominator env firstRow thirdRow = true :=
  lreIntScaledDominanceTrans (lfmNegativeMagnitudeAt variableIndex thirdRow)
    (lfmNegativeMagnitudeAt variableIndex secondRow)
    (lfmNegativeMagnitudeAt variableIndex firstRow)
    (lreRowUpperNumeratorAt variableIndex denominator env thirdRow)
    (lreRowUpperNumeratorAt variableIndex denominator env secondRow)
    (lreRowUpperNumeratorAt variableIndex denominator env firstRow)
    (lreIntPositiveMagnitudePositive
      (lfkIntNegate (lfmRowCoefficientAt variableIndex secondRow)) secondTest)
    secondDominates firstDominates

/-! ## The per-row verification steps at the constructed witness -/

/-- The updated-and-scaled environment's dot value in canonical form:
new value times pivot coefficient plus the scaled pivot-free rest. -/
theorem lreUpdatedDotForm (variableIndex scaleFactor : Nat) (outputEnv : List LfkInt)
    (witnessValue : LfkInt) (coefficientVector : List LfkInt) :
    lfkDotProduct
      (lreUpdateEnvAt variableIndex witnessValue
        (lfkScaleCoefficientVector scaleFactor outputEnv))
      coefficientVector
      = lfkIntAdd
          (lfkIntMul witnessValue (lfmCoefficientAtIndex variableIndex coefficientVector))
          (lfkIntScaleByNat scaleFactor
            (lfkDotProduct outputEnv
              (lreZeroCoefficientAt variableIndex coefficientVector))) :=
  (lreDotProductUpdateAt variableIndex (lfkScaleCoefficientVector scaleFactor outputEnv)
      coefficientVector witnessValue).trans
    (congrArg
      (lfkIntAdd
        (lfkIntMul witnessValue (lfmCoefficientAtIndex variableIndex coefficientVector)))
      (lreDotProductScaledEnv scaleFactor outputEnv
        (lreZeroCoefficientAt variableIndex coefficientVector)))

/-- ZERO-ROW STEP: a pivot-free row transports from the output environment to
the updated scaled environment (the pivot contributions on both sides are
cross-zero, and scaling by the positive factor preserves the relation). -/
theorem lreZeroRowStep (variableIndex outputDenominator scaleFactor : Nat)
    (outputEnv : List LfkInt) (witnessValue : LfkInt)
    (coefficientVector : List LfkInt) (boundValue : LfkInt) :
    ∀ (relation : LfkRelation),
    Nat.ble 1 scaleFactor = true →
    lfkIntIsZero (lfmCoefficientAtIndex variableIndex coefficientVector) = true →
    lfmRelationIsInequality relation = true →
    lfkSatisfiesConstraint outputEnv
      (LfkConstraint.mk coefficientVector
        (lfkIntScaleByNat outputDenominator boundValue) relation) = true →
    lfkSatisfiesConstraint
      (lreUpdateEnvAt variableIndex witnessValue
        (lfkScaleCoefficientVector scaleFactor outputEnv))
      (LfkConstraint.mk coefficientVector
        (lfkIntScaleByNat (outputDenominator * scaleFactor) boundValue) relation) = true
  | LfkRelation.isGreaterOrEqual, _scalePositive, zeroTest, _inequalityWitness,
      rowSatisfied =>
      let restValue := lfkDotProduct outputEnv
        (lreZeroCoefficientAt variableIndex coefficientVector)
      let outDotCrossRest : lfkIntEq (lfkDotProduct outputEnv coefficientVector)
          restValue = true :=
        (congrArg (fun probe => lfkIntEq probe restValue)
            (lreDotProductSplitAt variableIndex outputEnv coefficientVector)).trans
          (lreIntEqDropZeroLeft
            (lfkIntMulZeroRight (lfmCoefficientAtIndex variableIndex outputEnv)
              (lfmCoefficientAtIndex variableIndex coefficientVector) zeroTest))
      let restBound : lfkIntLe (lfkIntScaleByNat outputDenominator boundValue)
          restValue = true :=
        lreIntLeCongrRight outDotCrossRest rowSatisfied
      let composedBound : lfkIntLe
          (lfkIntScaleByNat (outputDenominator * scaleFactor) boundValue)
          (lfkIntScaleByNat scaleFactor restValue) = true :=
        lreIntLeTermTransport
          ((congrArg (fun probe => lfkIntScaleByNat probe boundValue)
              (Nat.mul_comm outputDenominator scaleFactor)).trans
            (lfmIntScaleCompose scaleFactor outputDenominator boundValue))
          rfl
          (lfkIntScaleLeMono scaleFactor restBound)
      let newDotCrossRest : lfkIntEq
          (lfkDotProduct
            (lreUpdateEnvAt variableIndex witnessValue
              (lfkScaleCoefficientVector scaleFactor outputEnv))
            coefficientVector)
          (lfkIntScaleByNat scaleFactor restValue) = true :=
        (congrArg (fun probe => lfkIntEq probe (lfkIntScaleByNat scaleFactor restValue))
            (lreUpdatedDotForm variableIndex scaleFactor outputEnv witnessValue
              coefficientVector)).trans
          (lreIntEqDropZeroLeft
            (lfkIntMulZeroRight witnessValue
              (lfmCoefficientAtIndex variableIndex coefficientVector) zeroTest))
      lreIntLeCongrRight (lreIntEqSymm newDotCrossRest) composedBound
  | LfkRelation.isStrictlyGreater, scalePositive, zeroTest, _inequalityWitness,
      rowSatisfied =>
      let restValue := lfkDotProduct outputEnv
        (lreZeroCoefficientAt variableIndex coefficientVector)
      let outDotCrossRest : lfkIntEq (lfkDotProduct outputEnv coefficientVector)
          restValue = true :=
        (congrArg (fun probe => lfkIntEq probe restValue)
            (lreDotProductSplitAt variableIndex outputEnv coefficientVector)).trans
          (lreIntEqDropZeroLeft
            (lfkIntMulZeroRight (lfmCoefficientAtIndex variableIndex outputEnv)
              (lfmCoefficientAtIndex variableIndex coefficientVector) zeroTest))
      let restBound : lfkIntLt (lfkIntScaleByNat outputDenominator boundValue)
          restValue = true :=
        lreIntLtCongrRight outDotCrossRest rowSatisfied
      let composedBound : lfkIntLt
          (lfkIntScaleByNat (outputDenominator * scaleFactor) boundValue)
          (lfkIntScaleByNat scaleFactor restValue) = true :=
        Exists.elim (lrePositiveSuccShape scaleFactor scalePositive)
          (fun scalePred shapeEq =>
            lreIntLtTermTransport
              ((congrArg (fun probe => lfkIntScaleByNat probe boundValue)
                  (Nat.mul_comm outputDenominator scaleFactor)).trans
                (lfmIntScaleCompose scaleFactor outputDenominator boundValue))
              rfl
              ((congrArg
                  (fun probe => lfkIntLt
                    (lfkIntScaleByNat probe
                      (lfkIntScaleByNat outputDenominator boundValue))
                    (lfkIntScaleByNat probe restValue))
                  shapeEq).trans
                (lreIntScaleLtMono scalePred restBound)))
      let newDotCrossRest : lfkIntEq
          (lfkDotProduct
            (lreUpdateEnvAt variableIndex witnessValue
              (lfkScaleCoefficientVector scaleFactor outputEnv))
            coefficientVector)
          (lfkIntScaleByNat scaleFactor restValue) = true :=
        (congrArg (fun probe => lfkIntEq probe (lfkIntScaleByNat scaleFactor restValue))
            (lreUpdatedDotForm variableIndex scaleFactor outputEnv witnessValue
              coefficientVector)).trans
          (lreIntEqDropZeroLeft
            (lfkIntMulZeroRight witnessValue
              (lfmCoefficientAtIndex variableIndex coefficientVector) zeroTest))
      lreIntLtCongrRight (lreIntEqSymm newDotCrossRest) composedBound
  | LfkRelation.isEqualTo, _scalePositive, _zeroTest, contradictoryWitness,
      _rowSatisfied => Bool.noConfusion contradictoryWitness

/-- POSITIVE-ROW STEP: a row with cross-positive pivot coefficient is satisfied
at the witness whenever the scaled endpoint facts hold (weak always, strict
when the row is strict). -/
theorem lrePositiveRowStep (variableIndex outputDenominator scaleFactor : Nat)
    (outputEnv : List LfkInt) (witnessValue : LfkInt)
    (coefficientVector : List LfkInt) (boundValue : LfkInt) :
    ∀ (relation : LfkRelation),
    lfkIntIsPositive (lfmCoefficientAtIndex variableIndex coefficientVector) = true →
    lfmRelationIsInequality relation = true →
    (lfkIntLe
      (lfkIntScaleByNat scaleFactor
        (lfkIntAdd (lfkIntScaleByNat outputDenominator boundValue)
          (lfkIntNegate
            (lfkDotProduct outputEnv
              (lreZeroCoefficientAt variableIndex coefficientVector)))))
      (lfkIntScaleByNat
        (lfmNatDelta (lfmCoefficientAtIndex variableIndex coefficientVector).positivePart
          (lfmCoefficientAtIndex variableIndex coefficientVector).negativePart)
        witnessValue) = true) →
    (relation = LfkRelation.isStrictlyGreater →
      lfkIntLt
        (lfkIntScaleByNat scaleFactor
          (lfkIntAdd (lfkIntScaleByNat outputDenominator boundValue)
            (lfkIntNegate
              (lfkDotProduct outputEnv
                (lreZeroCoefficientAt variableIndex coefficientVector)))))
        (lfkIntScaleByNat
          (lfmNatDelta
            (lfmCoefficientAtIndex variableIndex coefficientVector).positivePart
            (lfmCoefficientAtIndex variableIndex coefficientVector).negativePart)
          witnessValue) = true) →
    lfkSatisfiesConstraint
      (lreUpdateEnvAt variableIndex witnessValue
        (lfkScaleCoefficientVector scaleFactor outputEnv))
      (LfkConstraint.mk coefficientVector
        (lfkIntScaleByNat (outputDenominator * scaleFactor) boundValue) relation) = true
  | LfkRelation.isGreaterOrEqual, positiveTest, _inequalityWitness, weakEndpointFact,
      _strictEndpointFact =>
      let restValue := lfkDotProduct outputEnv
        (lreZeroCoefficientAt variableIndex coefficientVector)
      let pivotMagnitude := lfmNatDelta
        (lfmCoefficientAtIndex variableIndex coefficientVector).positivePart
        (lfmCoefficientAtIndex variableIndex coefficientVector).negativePart
      let lowerFormEq : lfkIntScaleByNat scaleFactor
          (lfkIntAdd (lfkIntScaleByNat outputDenominator boundValue)
            (lfkIntNegate restValue))
          = lfkIntAdd
              (lfkIntScaleByNat (outputDenominator * scaleFactor) boundValue)
              (lfkIntNegate (lfkIntScaleByNat scaleFactor restValue)) :=
        (lfkIntScaleAddDistrib scaleFactor
            (lfkIntScaleByNat outputDenominator boundValue)
            (lfkIntNegate restValue)).trans
          (congrArg
            (fun probe => lfkIntAdd probe
              (lfkIntNegate (lfkIntScaleByNat scaleFactor restValue)))
            ((lfmIntScaleCompose scaleFactor outputDenominator boundValue).symm.trans
              (congrArg (fun probe => lfkIntScaleByNat probe boundValue)
                (Nat.mul_comm scaleFactor outputDenominator))))
      let movedAcross : lfkIntLe
          (lfkIntScaleByNat (outputDenominator * scaleFactor) boundValue)
          (lfkIntAdd (lfkIntScaleByNat pivotMagnitude witnessValue)
            (lfkIntScaleByNat scaleFactor restValue)) = true :=
        lreIntLeMoveNegAcross
          ((congrArg
              (fun probe => lfkIntLe probe
                (lfkIntScaleByNat pivotMagnitude witnessValue))
              lowerFormEq).symm.trans weakEndpointFact)
      let valueAtDot : lfkIntEq
          (lfkDotProduct
            (lreUpdateEnvAt variableIndex witnessValue
              (lfkScaleCoefficientVector scaleFactor outputEnv))
            coefficientVector)
          (lfkIntAdd (lfkIntScaleByNat pivotMagnitude witnessValue)
            (lfkIntScaleByNat scaleFactor restValue)) = true :=
        (congrArg
            (fun probe => lfkIntEq probe
              (lfkIntAdd (lfkIntScaleByNat pivotMagnitude witnessValue)
                (lfkIntScaleByNat scaleFactor restValue)))
            (lreUpdatedDotForm variableIndex scaleFactor outputEnv witnessValue
              coefficientVector)).trans
          (lfkIntAddEqEq
            (lreIntMulPositiveEntryCrossEq witnessValue
              (lfmCoefficientAtIndex variableIndex coefficientVector) positiveTest)
            (lfkIntEqRefl (lfkIntScaleByNat scaleFactor restValue)))
      lreIntLeCongrRight (lreIntEqSymm valueAtDot) movedAcross
  | LfkRelation.isStrictlyGreater, positiveTest, _inequalityWitness, _weakEndpointFact,
      strictEndpointFact =>
      let restValue := lfkDotProduct outputEnv
        (lreZeroCoefficientAt variableIndex coefficientVector)
      let pivotMagnitude := lfmNatDelta
        (lfmCoefficientAtIndex variableIndex coefficientVector).positivePart
        (lfmCoefficientAtIndex variableIndex coefficientVector).negativePart
      let lowerFormEq : lfkIntScaleByNat scaleFactor
          (lfkIntAdd (lfkIntScaleByNat outputDenominator boundValue)
            (lfkIntNegate restValue))
          = lfkIntAdd
              (lfkIntScaleByNat (outputDenominator * scaleFactor) boundValue)
              (lfkIntNegate (lfkIntScaleByNat scaleFactor restValue)) :=
        (lfkIntScaleAddDistrib scaleFactor
            (lfkIntScaleByNat outputDenominator boundValue)
            (lfkIntNegate restValue)).trans
          (congrArg
            (fun probe => lfkIntAdd probe
              (lfkIntNegate (lfkIntScaleByNat scaleFactor restValue)))
            ((lfmIntScaleCompose scaleFactor outputDenominator boundValue).symm.trans
              (congrArg (fun probe => lfkIntScaleByNat probe boundValue)
                (Nat.mul_comm scaleFactor outputDenominator))))
      let movedAcross : lfkIntLt
          (lfkIntScaleByNat (outputDenominator * scaleFactor) boundValue)
          (lfkIntAdd (lfkIntScaleByNat pivotMagnitude witnessValue)
            (lfkIntScaleByNat scaleFactor restValue)) = true :=
        lreIntLtMoveNegAcross
          ((congrArg
              (fun probe => lfkIntLt probe
                (lfkIntScaleByNat pivotMagnitude witnessValue))
              lowerFormEq).symm.trans (strictEndpointFact rfl))
      let valueAtDot : lfkIntEq
          (lfkDotProduct
            (lreUpdateEnvAt variableIndex witnessValue
              (lfkScaleCoefficientVector scaleFactor outputEnv))
            coefficientVector)
          (lfkIntAdd (lfkIntScaleByNat pivotMagnitude witnessValue)
            (lfkIntScaleByNat scaleFactor restValue)) = true :=
        (congrArg
            (fun probe => lfkIntEq probe
              (lfkIntAdd (lfkIntScaleByNat pivotMagnitude witnessValue)
                (lfkIntScaleByNat scaleFactor restValue)))
            (lreUpdatedDotForm variableIndex scaleFactor outputEnv witnessValue
              coefficientVector)).trans
          (lfkIntAddEqEq
            (lreIntMulPositiveEntryCrossEq witnessValue
              (lfmCoefficientAtIndex variableIndex coefficientVector) positiveTest)
            (lfkIntEqRefl (lfkIntScaleByNat scaleFactor restValue)))
      lreIntLtCongrRight (lreIntEqSymm valueAtDot) movedAcross
  | LfkRelation.isEqualTo, _positiveTest, contradictoryWitness, _weakEndpointFact,
      _strictEndpointFact => Bool.noConfusion contradictoryWitness

/-- NEGATIVE-ROW STEP: a row with cross-negative pivot coefficient is satisfied
at the witness whenever the scaled endpoint facts hold. -/
theorem lreNegativeRowStep (variableIndex outputDenominator scaleFactor : Nat)
    (outputEnv : List LfkInt) (witnessValue : LfkInt)
    (coefficientVector : List LfkInt) (boundValue : LfkInt) :
    ∀ (relation : LfkRelation),
    lfkIntIsPositive
      (lfkIntNegate (lfmCoefficientAtIndex variableIndex coefficientVector)) = true →
    lfmRelationIsInequality relation = true →
    (lfkIntLe
      (lfkIntScaleByNat
        (lfmNatDelta (lfmCoefficientAtIndex variableIndex coefficientVector).negativePart
          (lfmCoefficientAtIndex variableIndex coefficientVector).positivePart)
        witnessValue)
      (lfkIntScaleByNat scaleFactor
        (lfkIntAdd
          (lfkDotProduct outputEnv
            (lreZeroCoefficientAt variableIndex coefficientVector))
          (lfkIntNegate (lfkIntScaleByNat outputDenominator boundValue)))) = true) →
    (relation = LfkRelation.isStrictlyGreater →
      lfkIntLt
        (lfkIntScaleByNat
          (lfmNatDelta
            (lfmCoefficientAtIndex variableIndex coefficientVector).negativePart
            (lfmCoefficientAtIndex variableIndex coefficientVector).positivePart)
          witnessValue)
        (lfkIntScaleByNat scaleFactor
          (lfkIntAdd
            (lfkDotProduct outputEnv
              (lreZeroCoefficientAt variableIndex coefficientVector))
            (lfkIntNegate (lfkIntScaleByNat outputDenominator boundValue)))) = true) →
    lfkSatisfiesConstraint
      (lreUpdateEnvAt variableIndex witnessValue
        (lfkScaleCoefficientVector scaleFactor outputEnv))
      (LfkConstraint.mk coefficientVector
        (lfkIntScaleByNat (outputDenominator * scaleFactor) boundValue) relation) = true
  | LfkRelation.isGreaterOrEqual, negativeTest, _inequalityWitness, weakEndpointFact,
      _strictEndpointFact =>
      let restValue := lfkDotProduct outputEnv
        (lreZeroCoefficientAt variableIndex coefficientVector)
      let pivotMagnitude := lfmNatDelta
        (lfmCoefficientAtIndex variableIndex coefficientVector).negativePart
        (lfmCoefficientAtIndex variableIndex coefficientVector).positivePart
      let upperFormEq : lfkIntScaleByNat scaleFactor
          (lfkIntAdd restValue
            (lfkIntNegate (lfkIntScaleByNat outputDenominator boundValue)))
          = lfkIntAdd (lfkIntScaleByNat scaleFactor restValue)
              (lfkIntNegate
                (lfkIntScaleByNat (outputDenominator * scaleFactor) boundValue)) :=
        (lfkIntScaleAddDistrib scaleFactor restValue
            (lfkIntNegate (lfkIntScaleByNat outputDenominator boundValue))).trans
          (congrArg
            (fun probe => lfkIntAdd (lfkIntScaleByNat scaleFactor restValue) probe)
            (congrArg lfkIntNegate
              ((lfmIntScaleCompose scaleFactor outputDenominator boundValue).symm.trans
                (congrArg (fun probe => lfkIntScaleByNat probe boundValue)
                  (Nat.mul_comm scaleFactor outputDenominator)))))
      let swappedSides : lfkIntLe
          (lfkIntScaleByNat (outputDenominator * scaleFactor) boundValue)
          (lfkIntAdd (lfkIntNegate (lfkIntScaleByNat pivotMagnitude witnessValue))
            (lfkIntScaleByNat scaleFactor restValue)) = true :=
        lreIntLeSwapSides
          ((congrArg
              (fun probe => lfkIntLe (lfkIntScaleByNat pivotMagnitude witnessValue)
                probe)
              upperFormEq).symm.trans weakEndpointFact)
      let valueAtDot : lfkIntEq
          (lfkDotProduct
            (lreUpdateEnvAt variableIndex witnessValue
              (lfkScaleCoefficientVector scaleFactor outputEnv))
            coefficientVector)
          (lfkIntAdd (lfkIntNegate (lfkIntScaleByNat pivotMagnitude witnessValue))
            (lfkIntScaleByNat scaleFactor restValue)) = true :=
        (congrArg
            (fun probe => lfkIntEq probe
              (lfkIntAdd (lfkIntNegate (lfkIntScaleByNat pivotMagnitude witnessValue))
                (lfkIntScaleByNat scaleFactor restValue)))
            (lreUpdatedDotForm variableIndex scaleFactor outputEnv witnessValue
              coefficientVector)).trans
          (lfkIntAddEqEq
            (lreIntMulNegativeEntryCrossEq witnessValue
              (lfmCoefficientAtIndex variableIndex coefficientVector) negativeTest)
            (lfkIntEqRefl (lfkIntScaleByNat scaleFactor restValue)))
      lreIntLeCongrRight (lreIntEqSymm valueAtDot) swappedSides
  | LfkRelation.isStrictlyGreater, negativeTest, _inequalityWitness, _weakEndpointFact,
      strictEndpointFact =>
      let restValue := lfkDotProduct outputEnv
        (lreZeroCoefficientAt variableIndex coefficientVector)
      let pivotMagnitude := lfmNatDelta
        (lfmCoefficientAtIndex variableIndex coefficientVector).negativePart
        (lfmCoefficientAtIndex variableIndex coefficientVector).positivePart
      let upperFormEq : lfkIntScaleByNat scaleFactor
          (lfkIntAdd restValue
            (lfkIntNegate (lfkIntScaleByNat outputDenominator boundValue)))
          = lfkIntAdd (lfkIntScaleByNat scaleFactor restValue)
              (lfkIntNegate
                (lfkIntScaleByNat (outputDenominator * scaleFactor) boundValue)) :=
        (lfkIntScaleAddDistrib scaleFactor restValue
            (lfkIntNegate (lfkIntScaleByNat outputDenominator boundValue))).trans
          (congrArg
            (fun probe => lfkIntAdd (lfkIntScaleByNat scaleFactor restValue) probe)
            (congrArg lfkIntNegate
              ((lfmIntScaleCompose scaleFactor outputDenominator boundValue).symm.trans
                (congrArg (fun probe => lfkIntScaleByNat probe boundValue)
                  (Nat.mul_comm scaleFactor outputDenominator)))))
      let swappedSides : lfkIntLt
          (lfkIntScaleByNat (outputDenominator * scaleFactor) boundValue)
          (lfkIntAdd (lfkIntNegate (lfkIntScaleByNat pivotMagnitude witnessValue))
            (lfkIntScaleByNat scaleFactor restValue)) = true :=
        lreIntLtSwapSides
          ((congrArg
              (fun probe => lfkIntLt (lfkIntScaleByNat pivotMagnitude witnessValue)
                probe)
              upperFormEq).symm.trans (strictEndpointFact rfl))
      let valueAtDot : lfkIntEq
          (lfkDotProduct
            (lreUpdateEnvAt variableIndex witnessValue
              (lfkScaleCoefficientVector scaleFactor outputEnv))
            coefficientVector)
          (lfkIntAdd (lfkIntNegate (lfkIntScaleByNat pivotMagnitude witnessValue))
            (lfkIntScaleByNat scaleFactor restValue)) = true :=
        (congrArg
            (fun probe => lfkIntEq probe
              (lfkIntAdd (lfkIntNegate (lfkIntScaleByNat pivotMagnitude witnessValue))
                (lfkIntScaleByNat scaleFactor restValue)))
            (lreUpdatedDotForm variableIndex scaleFactor outputEnv witnessValue
              coefficientVector)).trans
          (lfkIntAddEqEq
            (lreIntMulNegativeEntryCrossEq witnessValue
              (lfmCoefficientAtIndex variableIndex coefficientVector) negativeTest)
            (lfkIntEqRefl (lfkIntScaleByNat scaleFactor restValue)))
      lreIntLtCongrRight (lreIntEqSymm valueAtDot) swappedSides
  | LfkRelation.isEqualTo, _negativeTest, contradictoryWitness, _weakEndpointFact,
      _strictEndpointFact => Bool.noConfusion contradictoryWitness

/-- Assemble per-row satisfaction into whole-list satisfaction. -/
theorem lreAssembleInputSatisfaction (inputDenominator : Nat) (inputEnv : List LfkInt)
    (universeRows : List LfmCertifiedRow)
    (rowStep : ∀ (row : LfmCertifiedRow), lreRowIsAmong row universeRows →
      lfkSatisfiesConstraint inputEnv
        (lreScaleConstraintBound inputDenominator row.constraint) = true) :
    ∀ (currentRows : List LfmCertifiedRow), lreAllRowsAmong currentRows universeRows →
    lfkSatisfiesSystem inputEnv
      (lfkScaleBoundsForDenominator inputDenominator
        (lfmConstraintsOfRows currentRows)) = true
  | List.nil, _allAmongWitness => rfl
  | rowHead :: rowTail, allAmongWitness =>
      lfkBoolAndIntro _ _ (rowStep rowHead allAmongWitness.left)
        (lreAssembleInputSatisfaction inputDenominator inputEnv universeRows rowStep
          rowTail allAmongWitness.right)

/-! ## THE CORRECTED ROUND-EXTENSION THEOREM -/

/-- THE ROUND EXTENSION for inequality rows: satisfying the elimination round's
output at a positive denominator extends to satisfying the round's input at a
rescaled denominator.  The witness is the cleared MIDPOINT of the fold-selected
best scaled lower and upper bounds (both buckets nonempty), the best bound
padded by a whole denominator unit (one bucket empty), or the output
environment verbatim (no pivot rows). -/
theorem lreRoundExtensionForInequalityRows (variableIndex : Nat)
    (rows : List LfmCertifiedRow)
    (inequalityWitness : lfmAllRowsPass
      (fun row => lfmRelationIsInequality row.constraint.relation) rows = true)
    (outputDenominatorPred : Nat) (outputEnv : List LfkInt)
    (outputSatisfied : lfkSatisfiesSystem outputEnv
      (lfkScaleBoundsForDenominator (outputDenominatorPred + 1)
        (lfmConstraintsOfRows (lfmEliminationRound variableIndex rows))) = true) :
    ∃ (inputDenominatorPred : Nat) (inputEnv : List LfkInt),
      lfkSatisfiesSystem inputEnv
        (lfkScaleBoundsForDenominator (inputDenominatorPred + 1)
          (lfmConstraintsOfRows rows)) = true :=
  let outputDenominator := outputDenominatorPred + 1
  let rowInequality : ∀ (row : LfmCertifiedRow), lreRowIsAmong row rows →
      lfmRelationIsInequality row.constraint.relation = true :=
    fun row amongWitness =>
      lreTestPassesOfAmong (fun probeRow => lfmRelationIsInequality
        probeRow.constraint.relation) rows row amongWitness inequalityWitness
  let zeroRowSatisfiedAtOutput : ∀ (row : LfmCertifiedRow), lreRowIsAmong row rows →
      lfmRowCoefficientIsZeroAt variableIndex row = true →
      lfkSatisfiesConstraint outputEnv
        (lreScaleConstraintBound outputDenominator row.constraint) = true :=
    fun row amongWitness zeroWitness =>
      lreRowSatisfiedOfAmong outputDenominator outputEnv
        (lfmEliminationRound variableIndex rows) row
        (lreAmongJoinLeft
          (lfmFilterRowsByTest (lfmRowCoefficientIsZeroAt variableIndex) rows)
          (lfmCrossCombineAll variableIndex
            (lfmFilterRowsByTest (lfmRowHasPositiveCoefficientAt variableIndex) rows)
            (lfmFilterRowsByTest (lfmRowHasNegativeCoefficientAt variableIndex) rows))
          row
          (lreAmongFilterOfPass (lfmRowCoefficientIsZeroAt variableIndex) rows row
            amongWitness zeroWitness))
        outputSatisfied
  let comboSatisfiedAt : ∀ (positiveRow negativeRow : LfmCertifiedRow),
      lreRowIsAmong positiveRow
        (lfmFilterRowsByTest (lfmRowHasPositiveCoefficientAt variableIndex) rows) →
      lreRowIsAmong negativeRow
        (lfmFilterRowsByTest (lfmRowHasNegativeCoefficientAt variableIndex) rows) →
      lfkSatisfiesConstraint outputEnv
        (lreScaleConstraintBound outputDenominator
          (lfmCombineRowPair variableIndex positiveRow negativeRow).constraint) = true :=
    fun positiveRow negativeRow positiveAmong negativeAmong =>
      lreRowSatisfiedOfAmong outputDenominator outputEnv
        (lfmEliminationRound variableIndex rows)
        (lfmCombineRowPair variableIndex positiveRow negativeRow)
        (lreAmongJoinRight
          (lfmFilterRowsByTest (lfmRowCoefficientIsZeroAt variableIndex) rows)
          (lfmCrossCombineAll variableIndex
            (lfmFilterRowsByTest (lfmRowHasPositiveCoefficientAt variableIndex) rows)
            (lfmFilterRowsByTest (lfmRowHasNegativeCoefficientAt variableIndex) rows))
          (lfmCombineRowPair variableIndex positiveRow negativeRow)
          (lreAmongCrossCombine variableIndex
            (lfmFilterRowsByTest (lfmRowHasPositiveCoefficientAt variableIndex) rows)
            (lfmFilterRowsByTest (lfmRowHasNegativeCoefficientAt variableIndex) rows)
            positiveRow negativeRow positiveAmong negativeAmong))
        outputSatisfied
  match hPositive : lfmFilterRowsByTest (lfmRowHasPositiveCoefficientAt variableIndex)
      rows,
    hNegative : lfmFilterRowsByTest (lfmRowHasNegativeCoefficientAt variableIndex)
      rows with
  | List.nil, List.nil =>
      Exists.intro outputDenominatorPred (Exists.intro outputEnv
        (lreAssembleInputSatisfaction outputDenominator outputEnv rows
          (fun row amongWitness =>
            match lreIntSignTrichotomy (lfmRowCoefficientAt variableIndex row) with
            | Or.inl zeroWitness => zeroRowSatisfiedAtOutput row amongWitness zeroWitness
            | Or.inr (Or.inl positiveWitness) =>
                Bool.noConfusion (positiveWitness.symm.trans
                  (lreFilterNilAllFail (lfmRowHasPositiveCoefficientAt variableIndex)
                    rows hPositive row amongWitness))
            | Or.inr (Or.inr negativeWitness) =>
                Bool.noConfusion (negativeWitness.symm.trans
                  (lreFilterNilAllFail (lfmRowHasNegativeCoefficientAt variableIndex)
                    rows hNegative row amongWitness)))
          rows (lreAllRowsAmongSelf rows)))
  | List.nil, negativeHead :: negativeTail =>
      let negativeBucketPass : lfmAllRowsPass
          (lfmRowHasNegativeCoefficientAt variableIndex)
          (negativeHead :: negativeTail) = true :=
        (congrArg (lfmAllRowsPass (lfmRowHasNegativeCoefficientAt variableIndex))
          hNegative).symm.trans
          (lfmFilterOutputsPassTest (lfmRowHasNegativeCoefficientAt variableIndex) rows)
      let negativeDestructured := lfkBoolAndDestruct
        (lfmRowHasNegativeCoefficientAt variableIndex negativeHead)
        (lfmAllRowsPass (lfmRowHasNegativeCoefficientAt variableIndex) negativeTail)
        negativeBucketPass
      let bestUpper := lreSelectDominatingRow
        (lreUpperDominates variableIndex outputDenominator outputEnv)
        negativeHead negativeTail
      let upperSound := lreSelectDominatingRowSound
        (lreUpperDominates variableIndex outputDenominator outputEnv)
        (lfmRowHasNegativeCoefficientAt variableIndex)
        (fun row => lfmIntLeRefl
          (lfkIntScaleByNat (lfmNegativeMagnitudeAt variableIndex row)
            (lreRowUpperNumeratorAt variableIndex outputDenominator outputEnv row)))
        (fun _leftRow _rightRow falseWitness => lreIntLeFalseFlip falseWitness)
        (fun firstRow secondRow thirdRow firstTest secondTest thirdTest
            firstDominates secondDominates =>
          lreUpperDominatesTrans variableIndex outputDenominator outputEnv firstRow
            secondRow thirdRow firstTest secondTest thirdTest firstDominates
            secondDominates)
        negativeTail negativeHead negativeDestructured.left negativeDestructured.right
      let bestUpperTest : lfmRowHasNegativeCoefficientAt variableIndex bestUpper
          = true :=
        lreTestPassesOfAmong (lfmRowHasNegativeCoefficientAt variableIndex)
          (negativeHead :: negativeTail) bestUpper upperSound.left negativeBucketPass
      let upperMag := lfmNegativeMagnitudeAt variableIndex bestUpper
      let upperMagPositive : Nat.ble 1 upperMag = true :=
        lreIntPositiveMagnitudePositive
          (lfkIntNegate (lfmRowCoefficientAt variableIndex bestUpper)) bestUpperTest
      let witnessValue := lfkIntAdd
        (lreRowUpperNumeratorAt variableIndex outputDenominator outputEnv bestUpper)
        (lfkIntNegate (lreIntOfNat (outputDenominator * upperMag)))
      let dominanceOverNegative : ∀ (row : LfmCertifiedRow),
          lreRowIsAmong row (negativeHead :: negativeTail) →
          lreUpperDominates variableIndex outputDenominator outputEnv bestUpper row
            = true :=
        fun row amongWitness =>
          match amongWitness with
          | Or.inl headEq =>
              (congrArg
                (lreUpperDominates variableIndex outputDenominator outputEnv bestUpper)
                headEq).trans upperSound.right.left
          | Or.inr tailWitness => upperSound.right.right row tailWitness
      let rowStep : ∀ (row : LfmCertifiedRow), lreRowIsAmong row rows →
          lfkSatisfiesConstraint
            (lreUpdateEnvAt variableIndex witnessValue
              (lfkScaleCoefficientVector upperMag outputEnv))
            (lreScaleConstraintBound (outputDenominator * upperMag) row.constraint)
            = true :=
        fun row amongWitness =>
          match lreIntSignTrichotomy (lfmRowCoefficientAt variableIndex row) with
          | Or.inl zeroWitness =>
              lreZeroRowStep variableIndex outputDenominator upperMag outputEnv
                witnessValue row.constraint.coefficients row.constraint.bound
                row.constraint.relation upperMagPositive zeroWitness
                (rowInequality row amongWitness)
                (zeroRowSatisfiedAtOutput row amongWitness zeroWitness)
          | Or.inr (Or.inl positiveWitness) =>
              Bool.noConfusion (positiveWitness.symm.trans
                (lreFilterNilAllFail (lfmRowHasPositiveCoefficientAt variableIndex)
                  rows hPositive row amongWitness))
          | Or.inr (Or.inr negativeWitness) =>
              let rowAmongBucketCons : lreRowIsAmong row (negativeHead :: negativeTail) :=
                Eq.mpr (congrArg (lreRowIsAmong row) hNegative).symm
                  (lreAmongFilterOfPass (lfmRowHasNegativeCoefficientAt variableIndex)
                    rows row amongWitness negativeWitness)
              let loneStrict := lreLoneUpperEndpointCore
                (lfmNegativeMagnitudeAt variableIndex row) upperMag
                (outputDenominator * upperMag)
                (lreRowUpperNumeratorAt variableIndex outputDenominator outputEnv row)
                (lreRowUpperNumeratorAt variableIndex outputDenominator outputEnv
                  bestUpper)
                (lreIntPositiveMagnitudePositive
                  (lfkIntNegate (lfmRowCoefficientAt variableIndex row))
                  negativeWitness)
                (lreNatPositiveMulPositive outputDenominator upperMag rfl
                  upperMagPositive)
                (dominanceOverNegative row rowAmongBucketCons)
              lreNegativeRowStep variableIndex outputDenominator upperMag outputEnv
                witnessValue row.constraint.coefficients row.constraint.bound
                row.constraint.relation negativeWitness (rowInequality row amongWitness)
                (lfkIntLeOfLt loneStrict) (fun _relationStrict => loneStrict)
      Exists.elim
        (lrePositiveSuccShape (outputDenominator * upperMag)
          (lreNatPositiveMulPositive outputDenominator upperMag rfl upperMagPositive))
        (fun inputDenominatorPred shapeEq =>
          Exists.intro inputDenominatorPred (Exists.intro
            (lreUpdateEnvAt variableIndex witnessValue
              (lfkScaleCoefficientVector upperMag outputEnv))
            ((congrArg
                (fun probe => lfkSatisfiesSystem
                  (lreUpdateEnvAt variableIndex witnessValue
                    (lfkScaleCoefficientVector upperMag outputEnv))
                  (lfkScaleBoundsForDenominator probe (lfmConstraintsOfRows rows)))
                shapeEq).symm.trans
              (lreAssembleInputSatisfaction (outputDenominator * upperMag)
                (lreUpdateEnvAt variableIndex witnessValue
                  (lfkScaleCoefficientVector upperMag outputEnv))
                rows rowStep rows (lreAllRowsAmongSelf rows)))))
  | positiveHead :: positiveTail, List.nil =>
      let positiveBucketPass : lfmAllRowsPass
          (lfmRowHasPositiveCoefficientAt variableIndex)
          (positiveHead :: positiveTail) = true :=
        (congrArg (lfmAllRowsPass (lfmRowHasPositiveCoefficientAt variableIndex))
          hPositive).symm.trans
          (lfmFilterOutputsPassTest (lfmRowHasPositiveCoefficientAt variableIndex) rows)
      let positiveDestructured := lfkBoolAndDestruct
        (lfmRowHasPositiveCoefficientAt variableIndex positiveHead)
        (lfmAllRowsPass (lfmRowHasPositiveCoefficientAt variableIndex) positiveTail)
        positiveBucketPass
      let bestLower := lreSelectDominatingRow
        (lreLowerDominates variableIndex outputDenominator outputEnv)
        positiveHead positiveTail
      let lowerSound := lreSelectDominatingRowSound
        (lreLowerDominates variableIndex outputDenominator outputEnv)
        (lfmRowHasPositiveCoefficientAt variableIndex)
        (fun row => lfmIntLeRefl
          (lfkIntScaleByNat (lfmPositiveMagnitudeAt variableIndex row)
            (lreRowLowerNumeratorAt variableIndex outputDenominator outputEnv row)))
        (fun _leftRow _rightRow falseWitness => lreIntLeFalseFlip falseWitness)
        (fun firstRow secondRow thirdRow firstTest secondTest thirdTest
            firstDominates secondDominates =>
          lreLowerDominatesTrans variableIndex outputDenominator outputEnv firstRow
            secondRow thirdRow firstTest secondTest thirdTest firstDominates
            secondDominates)
        positiveTail positiveHead positiveDestructured.left positiveDestructured.right
      let bestLowerTest : lfmRowHasPositiveCoefficientAt variableIndex bestLower
          = true :=
        lreTestPassesOfAmong (lfmRowHasPositiveCoefficientAt variableIndex)
          (positiveHead :: positiveTail) bestLower lowerSound.left positiveBucketPass
      let lowerMag := lfmPositiveMagnitudeAt variableIndex bestLower
      let lowerMagPositive : Nat.ble 1 lowerMag = true :=
        lreIntPositiveMagnitudePositive (lfmRowCoefficientAt variableIndex bestLower)
          bestLowerTest
      let witnessValue := lfkIntAdd
        (lreRowLowerNumeratorAt variableIndex outputDenominator outputEnv bestLower)
        (lreIntOfNat (outputDenominator * lowerMag))
      let dominanceOverPositive : ∀ (row : LfmCertifiedRow),
          lreRowIsAmong row (positiveHead :: positiveTail) →
          lreLowerDominates variableIndex outputDenominator outputEnv bestLower row
            = true :=
        fun row amongWitness =>
          match amongWitness with
          | Or.inl headEq =>
              (congrArg
                (lreLowerDominates variableIndex outputDenominator outputEnv bestLower)
                headEq).trans lowerSound.right.left
          | Or.inr tailWitness => lowerSound.right.right row tailWitness
      let rowStep : ∀ (row : LfmCertifiedRow), lreRowIsAmong row rows →
          lfkSatisfiesConstraint
            (lreUpdateEnvAt variableIndex witnessValue
              (lfkScaleCoefficientVector lowerMag outputEnv))
            (lreScaleConstraintBound (outputDenominator * lowerMag) row.constraint)
            = true :=
        fun row amongWitness =>
          match lreIntSignTrichotomy (lfmRowCoefficientAt variableIndex row) with
          | Or.inl zeroWitness =>
              lreZeroRowStep variableIndex outputDenominator lowerMag outputEnv
                witnessValue row.constraint.coefficients row.constraint.bound
                row.constraint.relation lowerMagPositive zeroWitness
                (rowInequality row amongWitness)
                (zeroRowSatisfiedAtOutput row amongWitness zeroWitness)
          | Or.inr (Or.inl positiveWitness) =>
              let rowAmongBucketCons : lreRowIsAmong row (positiveHead :: positiveTail) :=
                Eq.mpr (congrArg (lreRowIsAmong row) hPositive).symm
                  (lreAmongFilterOfPass (lfmRowHasPositiveCoefficientAt variableIndex)
                    rows row amongWitness positiveWitness)
              let loneStrict := lreLoneLowerEndpointCore
                (lfmPositiveMagnitudeAt variableIndex row) lowerMag
                (outputDenominator * lowerMag)
                (lreRowLowerNumeratorAt variableIndex outputDenominator outputEnv row)
                (lreRowLowerNumeratorAt variableIndex outputDenominator outputEnv
                  bestLower)
                (lreIntPositiveMagnitudePositive
                  (lfmRowCoefficientAt variableIndex row) positiveWitness)
                (lreNatPositiveMulPositive outputDenominator lowerMag rfl
                  lowerMagPositive)
                (dominanceOverPositive row rowAmongBucketCons)
              lrePositiveRowStep variableIndex outputDenominator lowerMag outputEnv
                witnessValue row.constraint.coefficients row.constraint.bound
                row.constraint.relation positiveWitness (rowInequality row amongWitness)
                (lfkIntLeOfLt loneStrict) (fun _relationStrict => loneStrict)
          | Or.inr (Or.inr negativeWitness) =>
              Bool.noConfusion (negativeWitness.symm.trans
                (lreFilterNilAllFail (lfmRowHasNegativeCoefficientAt variableIndex)
                  rows hNegative row amongWitness))
      Exists.elim
        (lrePositiveSuccShape (outputDenominator * lowerMag)
          (lreNatPositiveMulPositive outputDenominator lowerMag rfl lowerMagPositive))
        (fun inputDenominatorPred shapeEq =>
          Exists.intro inputDenominatorPred (Exists.intro
            (lreUpdateEnvAt variableIndex witnessValue
              (lfkScaleCoefficientVector lowerMag outputEnv))
            ((congrArg
                (fun probe => lfkSatisfiesSystem
                  (lreUpdateEnvAt variableIndex witnessValue
                    (lfkScaleCoefficientVector lowerMag outputEnv))
                  (lfkScaleBoundsForDenominator probe (lfmConstraintsOfRows rows)))
                shapeEq).symm.trans
              (lreAssembleInputSatisfaction (outputDenominator * lowerMag)
                (lreUpdateEnvAt variableIndex witnessValue
                  (lfkScaleCoefficientVector lowerMag outputEnv))
                rows rowStep rows (lreAllRowsAmongSelf rows)))))
  | positiveHead :: positiveTail, negativeHead :: negativeTail =>
      let positiveBucketPass : lfmAllRowsPass
          (lfmRowHasPositiveCoefficientAt variableIndex)
          (positiveHead :: positiveTail) = true :=
        (congrArg (lfmAllRowsPass (lfmRowHasPositiveCoefficientAt variableIndex))
          hPositive).symm.trans
          (lfmFilterOutputsPassTest (lfmRowHasPositiveCoefficientAt variableIndex) rows)
      let positiveDestructured := lfkBoolAndDestruct
        (lfmRowHasPositiveCoefficientAt variableIndex positiveHead)
        (lfmAllRowsPass (lfmRowHasPositiveCoefficientAt variableIndex) positiveTail)
        positiveBucketPass
      let negativeBucketPass : lfmAllRowsPass
          (lfmRowHasNegativeCoefficientAt variableIndex)
          (negativeHead :: negativeTail) = true :=
        (congrArg (lfmAllRowsPass (lfmRowHasNegativeCoefficientAt variableIndex))
          hNegative).symm.trans
          (lfmFilterOutputsPassTest (lfmRowHasNegativeCoefficientAt variableIndex) rows)
      let negativeDestructured := lfkBoolAndDestruct
        (lfmRowHasNegativeCoefficientAt variableIndex negativeHead)
        (lfmAllRowsPass (lfmRowHasNegativeCoefficientAt variableIndex) negativeTail)
        negativeBucketPass
      let bestLower := lreSelectDominatingRow
        (lreLowerDominates variableIndex outputDenominator outputEnv)
        positiveHead positiveTail
      let lowerSound := lreSelectDominatingRowSound
        (lreLowerDominates variableIndex outputDenominator outputEnv)
        (lfmRowHasPositiveCoefficientAt variableIndex)
        (fun row => lfmIntLeRefl
          (lfkIntScaleByNat (lfmPositiveMagnitudeAt variableIndex row)
            (lreRowLowerNumeratorAt variableIndex outputDenominator outputEnv row)))
        (fun _leftRow _rightRow falseWitness => lreIntLeFalseFlip falseWitness)
        (fun firstRow secondRow thirdRow firstTest secondTest thirdTest
            firstDominates secondDominates =>
          lreLowerDominatesTrans variableIndex outputDenominator outputEnv firstRow
            secondRow thirdRow firstTest secondTest thirdTest firstDominates
            secondDominates)
        positiveTail positiveHead positiveDestructured.left positiveDestructured.right
      let bestUpper := lreSelectDominatingRow
        (lreUpperDominates variableIndex outputDenominator outputEnv)
        negativeHead negativeTail
      let upperSound := lreSelectDominatingRowSound
        (lreUpperDominates variableIndex outputDenominator outputEnv)
        (lfmRowHasNegativeCoefficientAt variableIndex)
        (fun row => lfmIntLeRefl
          (lfkIntScaleByNat (lfmNegativeMagnitudeAt variableIndex row)
            (lreRowUpperNumeratorAt variableIndex outputDenominator outputEnv row)))
        (fun _leftRow _rightRow falseWitness => lreIntLeFalseFlip falseWitness)
        (fun firstRow secondRow thirdRow firstTest secondTest thirdTest
            firstDominates secondDominates =>
          lreUpperDominatesTrans variableIndex outputDenominator outputEnv firstRow
            secondRow thirdRow firstTest secondTest thirdTest firstDominates
            secondDominates)
        negativeTail negativeHead negativeDestructured.left negativeDestructured.right
      let bestLowerTest : lfmRowHasPositiveCoefficientAt variableIndex bestLower
          = true :=
        lreTestPassesOfAmong (lfmRowHasPositiveCoefficientAt variableIndex)
          (positiveHead :: positiveTail) bestLower lowerSound.left positiveBucketPass
      let bestUpperTest : lfmRowHasNegativeCoefficientAt variableIndex bestUpper
          = true :=
        lreTestPassesOfAmong (lfmRowHasNegativeCoefficientAt variableIndex)
          (negativeHead :: negativeTail) bestUpper upperSound.left negativeBucketPass
      let bestLowerAmongBucket : lreRowIsAmong bestLower
          (lfmFilterRowsByTest (lfmRowHasPositiveCoefficientAt variableIndex) rows) :=
        Eq.mpr (congrArg (lreRowIsAmong bestLower) hPositive) lowerSound.left
      let bestUpperAmongBucket : lreRowIsAmong bestUpper
          (lfmFilterRowsByTest (lfmRowHasNegativeCoefficientAt variableIndex) rows) :=
        Eq.mpr (congrArg (lreRowIsAmong bestUpper) hNegative) upperSound.left
      let lowerMag := lfmPositiveMagnitudeAt variableIndex bestLower
      let upperMag := lfmNegativeMagnitudeAt variableIndex bestUpper
      let lowerMagPositive : Nat.ble 1 lowerMag = true :=
        lreIntPositiveMagnitudePositive (lfmRowCoefficientAt variableIndex bestLower)
          bestLowerTest
      let upperMagPositive : Nat.ble 1 upperMag = true :=
        lreIntPositiveMagnitudePositive
          (lfkIntNegate (lfmRowCoefficientAt variableIndex bestUpper)) bestUpperTest
      let scaleFactor := lowerMag * upperMag + lowerMag * upperMag
      let scalePositive : Nat.ble 1 scaleFactor = true :=
        lfkNatBleOfLe 1 scaleFactor
          (Nat.le_trans
            (lfkNatLeOfBle 1 (lowerMag * upperMag)
              (lreNatPositiveMulPositive lowerMag upperMag lowerMagPositive
                upperMagPositive))
            (lreNatLeAddRight (lowerMag * upperMag) (lowerMag * upperMag)))
      let witnessValue := lfkIntAdd
        (lfkIntScaleByNat upperMag
          (lreRowLowerNumeratorAt variableIndex outputDenominator outputEnv bestLower))
        (lfkIntScaleByNat lowerMag
          (lreRowUpperNumeratorAt variableIndex outputDenominator outputEnv bestUpper))
      let dominanceOverPositive : ∀ (row : LfmCertifiedRow),
          lreRowIsAmong row (positiveHead :: positiveTail) →
          lreLowerDominates variableIndex outputDenominator outputEnv bestLower row
            = true :=
        fun row amongWitness =>
          match amongWitness with
          | Or.inl headEq =>
              (congrArg
                (lreLowerDominates variableIndex outputDenominator outputEnv bestLower)
                headEq).trans lowerSound.right.left
          | Or.inr tailWitness => lowerSound.right.right row tailWitness
      let dominanceOverNegative : ∀ (row : LfmCertifiedRow),
          lreRowIsAmong row (negativeHead :: negativeTail) →
          lreUpperDominates variableIndex outputDenominator outputEnv bestUpper row
            = true :=
        fun row amongWitness =>
          match amongWitness with
          | Or.inl headEq =>
              (congrArg
                (lreUpperDominates variableIndex outputDenominator outputEnv bestUpper)
                headEq).trans upperSound.right.left
          | Or.inr tailWitness => upperSound.right.right row tailWitness
      let rowStep : ∀ (row : LfmCertifiedRow), lreRowIsAmong row rows →
          lfkSatisfiesConstraint
            (lreUpdateEnvAt variableIndex witnessValue
              (lfkScaleCoefficientVector scaleFactor outputEnv))
            (lreScaleConstraintBound (outputDenominator * scaleFactor) row.constraint)
            = true :=
        fun row amongWitness =>
          match lreIntSignTrichotomy (lfmRowCoefficientAt variableIndex row) with
          | Or.inl zeroWitness =>
              lreZeroRowStep variableIndex outputDenominator scaleFactor outputEnv
                witnessValue row.constraint.coefficients row.constraint.bound
                row.constraint.relation scalePositive zeroWitness
                (rowInequality row amongWitness)
                (zeroRowSatisfiedAtOutput row amongWitness zeroWitness)
          | Or.inr (Or.inl positiveWitness) =>
              let rowAmongPositiveBucket : lreRowIsAmong row
                  (lfmFilterRowsByTest (lfmRowHasPositiveCoefficientAt variableIndex)
                    rows) :=
                lreAmongFilterOfPass (lfmRowHasPositiveCoefficientAt variableIndex)
                  rows row amongWitness positiveWitness
              let rowAmongBucketCons : lreRowIsAmong row (positiveHead :: positiveTail) :=
                Eq.mpr (congrArg (lreRowIsAmong row) hPositive).symm
                  rowAmongPositiveBucket
              let comboSat := comboSatisfiedAt row bestUpper rowAmongPositiveBucket
                bestUpperAmongBucket
              let dominance := dominanceOverPositive row rowAmongBucketCons
              lrePositiveRowStep variableIndex outputDenominator scaleFactor outputEnv
                witnessValue row.constraint.coefficients row.constraint.bound
                row.constraint.relation positiveWitness (rowInequality row amongWitness)
                (lreMidpointLowerWeakCore (lfmPositiveMagnitudeAt variableIndex row)
                  lowerMag upperMag
                  (lreRowLowerNumeratorAt variableIndex outputDenominator outputEnv row)
                  (lreRowLowerNumeratorAt variableIndex outputDenominator outputEnv
                    bestLower)
                  (lreRowUpperNumeratorAt variableIndex outputDenominator outputEnv
                    bestUpper)
                  dominance
                  (lreComboSatisfactionGivesWeakBound variableIndex outputDenominator
                    outputEnv row bestUpper positiveWitness bestUpperTest comboSat))
                (fun relationStrict =>
                  lreMidpointLowerStrictCore (lfmPositiveMagnitudeAt variableIndex row)
                    lowerMag upperMag
                    (lreRowLowerNumeratorAt variableIndex outputDenominator outputEnv
                      row)
                    (lreRowLowerNumeratorAt variableIndex outputDenominator outputEnv
                      bestLower)
                    (lreRowUpperNumeratorAt variableIndex outputDenominator outputEnv
                      bestUpper)
                    lowerMagPositive dominance
                    (lreComboSatisfactionGivesStrictBound variableIndex
                      outputDenominator outputEnv row bestUpper positiveWitness
                      bestUpperTest (Or.inl relationStrict) comboSat))
          | Or.inr (Or.inr negativeWitness) =>
              let rowAmongNegativeBucket : lreRowIsAmong row
                  (lfmFilterRowsByTest (lfmRowHasNegativeCoefficientAt variableIndex)
                    rows) :=
                lreAmongFilterOfPass (lfmRowHasNegativeCoefficientAt variableIndex)
                  rows row amongWitness negativeWitness
              let rowAmongBucketCons : lreRowIsAmong row (negativeHead :: negativeTail) :=
                Eq.mpr (congrArg (lreRowIsAmong row) hNegative).symm
                  rowAmongNegativeBucket
              let comboSat := comboSatisfiedAt bestLower row bestLowerAmongBucket
                rowAmongNegativeBucket
              let dominance := dominanceOverNegative row rowAmongBucketCons
              lreNegativeRowStep variableIndex outputDenominator scaleFactor outputEnv
                witnessValue row.constraint.coefficients row.constraint.bound
                row.constraint.relation negativeWitness (rowInequality row amongWitness)
                (lreMidpointUpperWeakCore (lfmNegativeMagnitudeAt variableIndex row)
                  lowerMag upperMag
                  (lreRowUpperNumeratorAt variableIndex outputDenominator outputEnv row)
                  (lreRowLowerNumeratorAt variableIndex outputDenominator outputEnv
                    bestLower)
                  (lreRowUpperNumeratorAt variableIndex outputDenominator outputEnv
                    bestUpper)
                  (lreComboSatisfactionGivesWeakBound variableIndex outputDenominator
                    outputEnv bestLower row bestLowerTest negativeWitness comboSat)
                  dominance)
                (fun relationStrict =>
                  lreMidpointUpperStrictCore (lfmNegativeMagnitudeAt variableIndex row)
                    lowerMag upperMag
                    (lreRowUpperNumeratorAt variableIndex outputDenominator outputEnv
                      row)
                    (lreRowLowerNumeratorAt variableIndex outputDenominator outputEnv
                      bestLower)
                    (lreRowUpperNumeratorAt variableIndex outputDenominator outputEnv
                      bestUpper)
                    upperMagPositive
                    (lreComboSatisfactionGivesStrictBound variableIndex
                      outputDenominator outputEnv bestLower row bestLowerTest
                      negativeWitness (Or.inr relationStrict) comboSat)
                    dominance)
      Exists.elim
        (lrePositiveSuccShape (outputDenominator * scaleFactor)
          (lreNatPositiveMulPositive outputDenominator scaleFactor rfl scalePositive))
        (fun inputDenominatorPred shapeEq =>
          Exists.intro inputDenominatorPred (Exists.intro
            (lreUpdateEnvAt variableIndex witnessValue
              (lfkScaleCoefficientVector scaleFactor outputEnv))
            ((congrArg
                (fun probe => lfkSatisfiesSystem
                  (lreUpdateEnvAt variableIndex witnessValue
                    (lfkScaleCoefficientVector scaleFactor outputEnv))
                  (lfkScaleBoundsForDenominator probe (lfmConstraintsOfRows rows)))
                shapeEq).symm.trans
              (lreAssembleInputSatisfaction (outputDenominator * scaleFactor)
                (lreUpdateEnvAt variableIndex witnessValue
                  (lfkScaleCoefficientVector scaleFactor outputEnv))
                rows rowStep rows (lreAllRowsAmongSelf rows)))))

/-! ## The corrected statement, its inhabitant, and THE REFUTATION of the
    original wall Prop -/

/-- THE CORRECTED WALL STATEMENT: `lfmRoundExtensionStatement` guarded by the
inequality-relations invariant the pipeline actually maintains.  This is the
form the completeness cascade needs — and, unlike the unguarded original
(REFUTED below), it is TRUE. -/
def lreRoundExtensionInequalityStatement : Prop :=
  ∀ (variableIndex : Nat) (rows : List LfmCertifiedRow),
    lfmAllRowsPass (fun row => lfmRelationIsInequality row.constraint.relation) rows
      = true →
    ∀ (outputDenominatorPred : Nat) (outputEnv : List LfkInt),
    lfkSatisfiesSystem outputEnv
      (lfkScaleBoundsForDenominator (outputDenominatorPred + 1)
        (lfmConstraintsOfRows (lfmEliminationRound variableIndex rows))) = true →
    ∃ (inputDenominatorPred : Nat) (inputEnv : List LfkInt),
      lfkSatisfiesSystem inputEnv
        (lfkScaleBoundsForDenominator (inputDenominatorPred + 1)
          (lfmConstraintsOfRows rows)) = true

/-- The corrected round-extension statement HOLDS. -/
theorem lreRoundExtensionHolds : lreRoundExtensionInequalityStatement :=
  fun variableIndex rows inequalityWitness outputDenominatorPred outputEnv
      outputSatisfied =>
    lreRoundExtensionForInequalityRows variableIndex rows inequalityWitness
      outputDenominatorPred outputEnv outputSatisfied

/-- Refutation fixture, row 1: the EQUALITY row `x = 0`. -/
def lreRefutationEqualityRow : LfmCertifiedRow :=
  LfmCertifiedRow.mk
    (LfkConstraint.mk (LfkInt.mk 1 0 :: List.nil) lfkIntZero LfkRelation.isEqualTo)
    (1 :: List.nil)

/-- Refutation fixture, row 2: the inequality row `x >= 1`. -/
def lreRefutationInequalityRow : LfmCertifiedRow :=
  LfmCertifiedRow.mk
    (LfkConstraint.mk (LfkInt.mk 1 0 :: List.nil) (LfkInt.mk 1 0)
      LfkRelation.isGreaterOrEqual)
    (0 :: 1 :: List.nil)

/-- The refutation rows: `[x = 0, x >= 1]` — unsatisfiable at every
denominator, yet BOTH rows land in the positive bucket (the round buckets by
coefficient SIGN only), the negative bucket is empty, and the round output is
the EMPTY system. -/
def lreRefutationRows : List LfmCertifiedRow :=
  lreRefutationEqualityRow :: lreRefutationInequalityRow :: List.nil

/-- Kernel pin: eliminating the only variable from the refutation rows yields
NO output rows — the equality's upper-bound half is forgotten. -/
theorem lreRefutationRoundOutputEmptyPin :
    lfmConstraintsOfRows (lfmEliminationRound 0 lreRefutationRows) = List.nil := rfl

/-- THE REFUTATION: `lfmRoundExtensionStatement` — the sibling wall Prop AS
STATED, quantifying over arbitrary certified rows — is FALSE.  Instantiated at
the refutation rows, its hypothesis holds by `rfl` (the round output is empty),
but its conclusion demands an environment with `x = 0` and `x >= d > 0`
simultaneously. -/
theorem lreRoundExtensionStatementRefuted
    (extensionClaim : lfmRoundExtensionStatement) : False :=
  Exists.elim (extensionClaim 0 lreRefutationRows 0 List.nil rfl)
    (fun inputDenominatorPred innerExists =>
      Exists.elim innerExists (fun inputEnv satisfactionWitness =>
        let dotValue := lfkDotProduct inputEnv (LfkInt.mk 1 0 :: List.nil)
        let destructuredOuter := lfkBoolAndDestruct
          (lfkSatisfiesConstraint inputEnv
            (lreScaleConstraintBound (inputDenominatorPred + 1)
              lreRefutationEqualityRow.constraint))
          (lfkSatisfiesSystem inputEnv
            (lfkScaleBoundsForDenominator (inputDenominatorPred + 1)
              (lfmConstraintsOfRows (lreRefutationInequalityRow :: List.nil))))
          satisfactionWitness
        let destructuredInner := lfkBoolAndDestruct
          (lfkSatisfiesConstraint inputEnv
            (lreScaleConstraintBound (inputDenominatorPred + 1)
              lreRefutationInequalityRow.constraint))
          (lfkSatisfiesSystem inputEnv
            (lfkScaleBoundsForDenominator (inputDenominatorPred + 1) List.nil))
          destructuredOuter.right
        let dotPartsEq : dotValue.positivePart = dotValue.negativePart :=
          (lfkNatEqOfBeq (dotValue.positivePart + 0) (0 + dotValue.negativePart)
            destructuredOuter.left).trans (Nat.zero_add dotValue.negativePart)
        let boundLe : Nat.le ((inputDenominatorPred + 1) * 1 + dotValue.negativePart)
            dotValue.positivePart :=
          lfkNatLeOfBle _ _ destructuredInner.left
        let squeezedLe : Nat.le ((inputDenominatorPred + 1) * 1 + dotValue.negativePart)
            dotValue.negativePart :=
          lfkNatLeCongr rfl dotPartsEq.symm boundLe
        let riseLe : Nat.le (dotValue.negativePart + 1)
            ((inputDenominatorPred + 1) * 1 + dotValue.negativePart) :=
          lfkNatLeCongr rfl
            ((congrArg (fun probe => probe + dotValue.negativePart)
                (Nat.mul_one (inputDenominatorPred + 1))).trans
              ((Nat.add_assoc inputDenominatorPred 1 dotValue.negativePart).trans
                (congrArg (fun probe => inputDenominatorPred + probe)
                  (Nat.add_comm 1 dotValue.negativePart))))
            (lreNatLeAddLeft inputDenominatorPred (dotValue.negativePart + 1))
        lfkNatSuccLeSelfFalse dotValue.negativePart (Nat.le_trans riseLe squeezedLe)))

/-! ## The cascade: rounds preserve inequality, driver backward induction,
    the scan-clean base, seed extraction, expansion re-assembly -/

/-- Scaling preserves the inequality reading of a relation. -/
theorem lreScaleRelationPreservesInequality : ∀ (multiplier : Nat)
    (relation : LfkRelation),
    lfmRelationIsInequality relation = true →
    lfmRelationIsInequality (lfkScaleRelation multiplier relation) = true
  | _multiplier, LfkRelation.isGreaterOrEqual, _inequalityWitness => rfl
  | Nat.zero, LfkRelation.isStrictlyGreater, _inequalityWitness => rfl
  | Nat.succ _multiplierPred, LfkRelation.isStrictlyGreater, _inequalityWitness => rfl
  | _multiplier, LfkRelation.isEqualTo, contradictoryWitness =>
      Bool.noConfusion contradictoryWitness

/-- The elimination round preserves the all-rows-inequality invariant. -/
theorem lreRoundPreservesInequality (variableIndex : Nat)
    (rows : List LfmCertifiedRow)
    (inequalityWitness : lfmAllRowsPass
      (fun row => lfmRelationIsInequality row.constraint.relation) rows = true) :
    lfmAllRowsPass (fun row => lfmRelationIsInequality row.constraint.relation)
      (lfmEliminationRound variableIndex rows) = true :=
  lfmRoundPreservesAllPass variableIndex
    (fun row => lfmRelationIsInequality row.constraint.relation)
    (fun positiveRow negativeRow _positiveInequality negativeInequality =>
      lfmJoinPreservesInequality
        (lfkScaleRelation (lfmNegativeMagnitudeAt variableIndex negativeRow)
          positiveRow.constraint.relation)
        (lfkScaleRelation (lfmPositiveMagnitudeAt variableIndex positiveRow)
          negativeRow.constraint.relation)
        (lreScaleRelationPreservesInequality
          (lfmPositiveMagnitudeAt variableIndex positiveRow)
          negativeRow.constraint.relation negativeInequality))
    rows inequalityWitness

/-- The driver preserves the all-rows-inequality invariant. -/
theorem lreDriverPreservesInequality : ∀ (fuel currentIndex : Nat)
    (rows : List LfmCertifiedRow),
    lfmAllRowsPass (fun row => lfmRelationIsInequality row.constraint.relation) rows
      = true →
    lfmAllRowsPass (fun row => lfmRelationIsInequality row.constraint.relation)
      (lfmEliminateFromIndex currentIndex fuel rows) = true
  | Nat.zero, _currentIndex, _rows, inequalityWitness => inequalityWitness
  | Nat.succ remainingFuel, currentIndex, rows, inequalityWitness =>
      lreDriverPreservesInequality remainingFuel (currentIndex + 1)
        (lfmEliminationRound currentIndex rows)
        (lreRoundPreservesInequality currentIndex rows inequalityWitness)

/-- BACKWARD DRIVER INDUCTION: a satisfiable driver output extends back to a
satisfiable driver input, one corrected round extension per unit of fuel. -/
theorem lreDriverBackwardExtension : ∀ (fuel currentIndex : Nat)
    (rows : List LfmCertifiedRow),
    lfmAllRowsPass (fun row => lfmRelationIsInequality row.constraint.relation) rows
      = true →
    (∃ (outputDenominatorPred : Nat) (outputEnv : List LfkInt),
      lfkSatisfiesSystem outputEnv
        (lfkScaleBoundsForDenominator (outputDenominatorPred + 1)
          (lfmConstraintsOfRows (lfmEliminateFromIndex currentIndex fuel rows)))
        = true) →
    ∃ (inputDenominatorPred : Nat) (inputEnv : List LfkInt),
      lfkSatisfiesSystem inputEnv
        (lfkScaleBoundsForDenominator (inputDenominatorPred + 1)
          (lfmConstraintsOfRows rows)) = true
  | Nat.zero, _currentIndex, _rows, _inequalityWitness, outputExists => outputExists
  | Nat.succ remainingFuel, currentIndex, rows, inequalityWitness, outputExists =>
      Exists.elim
        (lreDriverBackwardExtension remainingFuel (currentIndex + 1)
          (lfmEliminationRound currentIndex rows)
          (lreRoundPreservesInequality currentIndex rows inequalityWitness)
          outputExists)
        (fun roundDenominatorPred innerExists =>
          Exists.elim innerExists (fun roundEnv roundSatisfied =>
            lreRoundExtensionForInequalityRows currentIndex rows inequalityWitness
              roundDenominatorPred roundEnv roundSatisfied))

/-- A ground, non-contradictory inequality row is satisfied by the EMPTY
environment at denominator one. -/
theorem lreGroundRowSatisfiedByEmptyEnv (coefficientVector : List LfkInt)
    (boundValue : LfkInt) : ∀ (relation : LfkRelation),
    lfmRelationIsInequality relation = true →
    lfkBoundViolatesRelation relation boundValue = false →
    lfkSatisfiesConstraint List.nil
      (LfkConstraint.mk coefficientVector (lfkIntScaleByNat 1 boundValue) relation)
      = true
  | LfkRelation.isGreaterOrEqual, _inequalityWitness, notViolating =>
      (congrArg (fun probe => lfkIntLe (lfkIntScaleByNat 1 boundValue) probe)
          (lreDotProductNilEnv coefficientVector)).trans
        (lfkNatBleOfLe _ _
          (lfkNatLeCongr (lfmNatOneMul boundValue.positivePart)
            ((Nat.zero_add (1 * boundValue.negativePart)).trans
              (lfmNatOneMul boundValue.negativePart))
            (Nat.le_of_succ_le_succ
              (lfkNatLeOfBle _ _
                (lfmNatBleFalseFlipStrict (boundValue.negativePart + 1)
                  boundValue.positivePart notViolating)))))
  | LfkRelation.isStrictlyGreater, _inequalityWitness, notViolating =>
      (congrArg (fun probe => lfkIntLt (lfkIntScaleByNat 1 boundValue) probe)
          (lreDotProductNilEnv coefficientVector)).trans
        (lfkNatBleOfLe _ _
          (lfkNatLeCongr
            (congrArg (fun probe => probe + 1) (lfmNatOneMul boundValue.positivePart))
            ((Nat.zero_add (1 * boundValue.negativePart)).trans
              (lfmNatOneMul boundValue.negativePart))
            (lfkNatLeOfBle _ _
              (lfmNatBleFalseFlipStrict boundValue.negativePart
                boundValue.positivePart notViolating))))
  | LfkRelation.isEqualTo, contradictoryWitness, _notViolating =>
      Bool.noConfusion contradictoryWitness

/-- THE SCAN-CLEAN BASE: ground inequality rows surviving a clean contradiction
scan are satisfied by the empty environment at denominator one. -/
theorem lreGroundCleanRowsSatisfied : ∀ (rows : List LfmCertifiedRow),
    lfmAllRowsPass (fun row => lfkAllCoefficientsAreZero row.constraint.coefficients)
      rows = true →
    lfmAllRowsPass (fun row => lfmRelationIsInequality row.constraint.relation) rows
      = true →
    lfmScanForContradiction rows = Option.none →
    lfkSatisfiesSystem List.nil
      (lfkScaleBoundsForDenominator 1 (lfmConstraintsOfRows rows)) = true
  | List.nil, _groundWitness, _inequalityWitness, _scanWitness => rfl
  | rowHead :: rowTail, groundWitness, inequalityWitness, scanWitness =>
      let groundDestructured := lfkBoolAndDestruct
        (lfkAllCoefficientsAreZero rowHead.constraint.coefficients)
        (lfmAllRowsPass
          (fun row => lfkAllCoefficientsAreZero row.constraint.coefficients) rowTail)
        groundWitness
      let inequalityDestructured := lfkBoolAndDestruct
        (lfmRelationIsInequality rowHead.constraint.relation)
        (lfmAllRowsPass
          (fun row => lfmRelationIsInequality row.constraint.relation) rowTail)
        inequalityWitness
      let scanSplit := lreCondNoneSplit (lfkIsGroundContradiction rowHead.constraint)
        rowHead.provenance (lfmScanForContradiction rowTail) scanWitness
      lfkBoolAndIntro _ _
        (lreGroundRowSatisfiedByEmptyEnv rowHead.constraint.coefficients
          rowHead.constraint.bound rowHead.constraint.relation
          inequalityDestructured.left
          (lreBoolAndFalseRight
            (lfkAllCoefficientsAreZero rowHead.constraint.coefficients)
            (lfkBoundViolatesRelation rowHead.constraint.relation
              rowHead.constraint.bound)
            scanSplit.left groundDestructured.left))
        (lreGroundCleanRowsSatisfied rowTail groundDestructured.right
          inequalityDestructured.right scanSplit.right)

/-- Every seed row's relation is an inequality (seed constraints are weighted
sums). -/
theorem lreSeedRowsFromIndexInequality (fullExpandedSystem : List LfkConstraint) :
    ∀ (remainingRows : List LfkConstraint) (startIndex : Nat),
    lfmAllRowsPass (fun row => lfmRelationIsInequality row.constraint.relation)
      (lfmSeedRowsFromIndex fullExpandedSystem remainingRows startIndex) = true
  | List.nil, _startIndex => rfl
  | _remainingHead :: remainingTail, startIndex =>
      lfkBoolAndIntro _ _
        (lfmWeightedSumRelationIsInequality (lfmUnitProvenance startIndex)
          fullExpandedSystem)
        (lreSeedRowsFromIndexInequality fullExpandedSystem remainingTail
          (startIndex + 1))

/-- Are all constraint relations inequalities? -/
def lreAllConstraintsInequality : List LfkConstraint → Bool
  | List.nil => true
  | constraintHead :: constraintTail =>
      lfmRelationIsInequality constraintHead.relation
        && lreAllConstraintsInequality constraintTail

/-- Row-split systems carry only inequality relations. -/
theorem lreExpandSystemInequality : ∀ (system : List LfkConstraint),
    lreAllConstraintsInequality (lfkExpandSystem system) = true
  | List.nil => rfl
  | LfkConstraint.mk _coefficients _bound LfkRelation.isGreaterOrEqual :: systemTail =>
      lfkBoolAndIntro _ _ rfl (lreExpandSystemInequality systemTail)
  | LfkConstraint.mk _coefficients _bound LfkRelation.isStrictlyGreater :: systemTail =>
      lfkBoolAndIntro _ _ rfl (lreExpandSystemInequality systemTail)
  | LfkConstraint.mk _coefficients _bound LfkRelation.isEqualTo :: systemTail =>
      lfkBoolAndIntro _ _ rfl
        (lfkBoolAndIntro _ _ rfl (lreExpandSystemInequality systemTail))

/-- The constraint at a row index, defaulting to the trivial row beyond the
system's length. -/
def lreConstraintAtIndex (rowIndex : Nat) (system : List LfkConstraint) : LfkConstraint :=
  match system, rowIndex with
  | List.nil, _anyIndex => lfkTrivialConstraint
  | constraintHead :: _constraintTail, Nat.zero => constraintHead
  | _constraintHead :: constraintTail, Nat.succ indexPred =>
      lreConstraintAtIndex indexPred constraintTail
termination_by structural system

/-- The scaled trivial row is satisfied by every environment. -/
theorem lreScaledTrivialSatisfied (denominator : Nat) (env : List LfkInt) :
    lfkSatisfiesConstraint env
      (lreScaleConstraintBound denominator lfkTrivialConstraint) = true :=
  (congrArg (fun probe => lfkIntLe (lfkIntScaleByNat denominator lfkIntZero) probe)
    (lfkDotProductNilRight env)).trans rfl

/-- Scaling by zero yields a cross-zero value. -/
theorem lreIntScaleZeroIsZero (value : LfkInt) :
    lfkIntIsZero (lfkIntScaleByNat 0 value) = true :=
  lfkNatBeqOfEq (0 * value.positivePart) (0 * value.negativePart)
    ((Nat.zero_mul value.positivePart).trans (Nat.zero_mul value.negativePart).symm)

/-- The empty certificate weights every system to the trivial row. -/
theorem lreWeightedSumNilCertificate : ∀ (system : List LfkConstraint),
    lfkWeightedSum List.nil system = lfkTrivialConstraint
  | List.nil => rfl
  | _constraintHead :: _constraintTail => rfl

/-- ZERO-WEIGHT PEEL: satisfaction of a scaled weighted sum whose leading
weight is zero passes to the tail weighted sum (the zero-scaled head
contributes cross-zero to coefficients and bound, and the join keeps the
tail's relation strictness through `lreJoinStrictRight`). -/
theorem lreUnitSumZeroPeel (denominator : Nat) (env : List LfkInt)
    (headConstraint : LfkConstraint) (tailSystem : List LfkConstraint)
    (unitTail : List Nat)
    (sumSatisfied : lfkSatisfiesConstraint env
      (lreScaleConstraintBound denominator
        (lfkWeightedSum (0 :: unitTail) (headConstraint :: tailSystem))) = true) :
    lfkSatisfiesConstraint env
      (lreScaleConstraintBound denominator (lfkWeightedSum unitTail tailSystem))
      = true :=
  let tailSum := lfkWeightedSum unitTail tailSystem
  let boundDrop : lfkIntEq
      (lfkIntScaleByNat denominator (lfkIntAdd (lfkIntScaleByNat 0 headConstraint.bound)
        tailSum.bound))
      (lfkIntScaleByNat denominator tailSum.bound) = true :=
    (congrArg
        (fun probe => lfkIntEq probe (lfkIntScaleByNat denominator tailSum.bound))
        (lfkIntScaleAddDistrib denominator (lfkIntScaleByNat 0 headConstraint.bound)
          tailSum.bound)).trans
      (lreIntEqDropZeroLeft
        (lfmIntScalePreservesZero denominator
          (lreIntScaleZeroIsZero headConstraint.bound)))
  let dotDrop : lfkIntEq
      (lfkDotProduct env
        (lfkAddCoefficientVectors
          (lfkScaleCoefficientVector 0 headConstraint.coefficients)
          tailSum.coefficients))
      (lfkDotProduct env tailSum.coefficients) = true :=
    (congrArg
        (fun probe => lfkIntEq probe (lfkDotProduct env tailSum.coefficients))
        (lfkDotProductAddVectors env
          (lfkScaleCoefficientVector 0 headConstraint.coefficients)
          tailSum.coefficients)).trans
      (lreIntEqDropZeroLeft
        ((congrArg lfkIntIsZero
            (lfkDotProductScaledVector env 0 headConstraint.coefficients)).trans
          (lreIntScaleZeroIsZero (lfkDotProduct env headConstraint.coefficients))))
  match tailRelationShape : tailSum.relation,
      lfmWeightedSumRelationIsInequality unitTail tailSystem with
  | LfkRelation.isGreaterOrEqual, _tailInequality =>
      let weakSum : lfkIntLe
          (lfkIntScaleByNat denominator
            (lfkIntAdd (lfkIntScaleByNat 0 headConstraint.bound) tailSum.bound))
          (lfkDotProduct env
            (lfkAddCoefficientVectors
              (lfkScaleCoefficientVector 0 headConstraint.coefficients)
              tailSum.coefficients)) = true :=
        lreSatisfactionGivesWeakLe env
          (lreScaleConstraintBound denominator
            (lfkWeightedSum (0 :: unitTail) (headConstraint :: tailSystem)))
          sumSatisfied
      (congrArg
          (fun probe => lfkSatisfiesConstraint env
            (LfkConstraint.mk tailSum.coefficients
              (lfkIntScaleByNat denominator tailSum.bound) probe))
          tailRelationShape).trans
        (lreIntLeCongrRight dotDrop (lreIntLeCongrLeft boundDrop weakSum))
  | LfkRelation.isStrictlyGreater, _tailInequality =>
      let sumRelationStrict : (lfkWeightedSum (0 :: unitTail)
          (headConstraint :: tailSystem)).relation = LfkRelation.isStrictlyGreater :=
        (congrArg (lfkJoinRelations (lfkScaleRelation 0 headConstraint.relation))
            tailRelationShape).trans
          (lreJoinStrictRight (lfkScaleRelation 0 headConstraint.relation))
      let strictSum : lfkIntLt
          (lfkIntScaleByNat denominator
            (lfkIntAdd (lfkIntScaleByNat 0 headConstraint.bound) tailSum.bound))
          (lfkDotProduct env
            (lfkAddCoefficientVectors
              (lfkScaleCoefficientVector 0 headConstraint.coefficients)
              tailSum.coefficients)) = true :=
        (congrArg
            (fun probe => lfkSatisfiesConstraint env
              (LfkConstraint.mk
                (lfkAddCoefficientVectors
                  (lfkScaleCoefficientVector 0 headConstraint.coefficients)
                  tailSum.coefficients)
                (lfkIntScaleByNat denominator
                  (lfkIntAdd (lfkIntScaleByNat 0 headConstraint.bound) tailSum.bound))
                probe))
            sumRelationStrict).symm.trans sumSatisfied
      (congrArg
          (fun probe => lfkSatisfiesConstraint env
            (LfkConstraint.mk tailSum.coefficients
              (lfkIntScaleByNat denominator tailSum.bound) probe))
          tailRelationShape).trans
        (lreIntLtCongrRight dotDrop (lreIntLtCongrLeft boundDrop strictSum))
  | LfkRelation.isEqualTo, tailInequality => Bool.noConfusion tailInequality

/-- The scaled unit-one value reads as the value itself. -/
theorem lreIntScaleOneCrossEq (value : LfkInt) :
    lfkIntEq (lfkIntScaleByNat 1 value) value = true :=
  lfkNatBeqOfEq (1 * value.positivePart + value.negativePart)
    (value.positivePart + 1 * value.negativePart)
    (lfkNatAddCongr (lfmNatOneMul value.positivePart)
      (lfmNatOneMul value.negativePart).symm)

/-- HEAD SEED EXTRACT: satisfaction of the scaled weight-one head seed gives
satisfaction of the scaled head row itself. -/
theorem lreHeadSeedExtract (denominator : Nat) (env : List LfkInt)
    (coefficientVector : List LfkInt) (boundValue : LfkInt)
    (tailSystem : List LfkConstraint) : ∀ (relation : LfkRelation),
    lfmRelationIsInequality relation = true →
    lfkSatisfiesConstraint env
      (lreScaleConstraintBound denominator
        (lfkWeightedSum (lfmUnitProvenance 0)
          (LfkConstraint.mk coefficientVector boundValue relation :: tailSystem)))
      = true →
    lfkSatisfiesConstraint env
      (lreScaleConstraintBound denominator
        (LfkConstraint.mk coefficientVector boundValue relation)) = true
  | LfkRelation.isGreaterOrEqual, _inequalityWitness, sumSatisfied =>
      let sumCollapse : lfkWeightedSum (lfmUnitProvenance 0)
          (LfkConstraint.mk coefficientVector boundValue
            LfkRelation.isGreaterOrEqual :: tailSystem)
          = lfkScaleConstraint 1
              (LfkConstraint.mk coefficientVector boundValue
                LfkRelation.isGreaterOrEqual) :=
        (congrArg
            (lfkAddConstraints (lfkScaleConstraint 1
              (LfkConstraint.mk coefficientVector boundValue
                LfkRelation.isGreaterOrEqual)))
            (lreWeightedSumNilCertificate tailSystem)).trans
          (lfmAddConstraintsTrivialRight
            (lfkScaleConstraint 1
              (LfkConstraint.mk coefficientVector boundValue
                LfkRelation.isGreaterOrEqual)) rfl)
      let scaledSat : lfkIntLe
          (lfkIntScaleByNat denominator (lfkIntScaleByNat 1 boundValue))
          (lfkDotProduct env (lfkScaleCoefficientVector 1 coefficientVector)) = true :=
        (congrArg
            (fun probe => lfkSatisfiesConstraint env
              (lreScaleConstraintBound denominator probe)) sumCollapse).symm.trans
          sumSatisfied
      lreIntLeCongrRight
        ((congrArg
            (fun probe => lfkIntEq probe (lfkDotProduct env coefficientVector))
            (lfkDotProductScaledVector env 1 coefficientVector)).trans
          (lreIntScaleOneCrossEq (lfkDotProduct env coefficientVector)))
        (lreIntLeCongrLeft
          (lfkIntScaleEqMono denominator (lreIntScaleOneCrossEq boundValue))
          scaledSat)
  | LfkRelation.isStrictlyGreater, _inequalityWitness, sumSatisfied =>
      let sumCollapse : lfkWeightedSum (lfmUnitProvenance 0)
          (LfkConstraint.mk coefficientVector boundValue
            LfkRelation.isStrictlyGreater :: tailSystem)
          = lfkScaleConstraint 1
              (LfkConstraint.mk coefficientVector boundValue
                LfkRelation.isStrictlyGreater) :=
        (congrArg
            (lfkAddConstraints (lfkScaleConstraint 1
              (LfkConstraint.mk coefficientVector boundValue
                LfkRelation.isStrictlyGreater)))
            (lreWeightedSumNilCertificate tailSystem)).trans
          (lfmAddConstraintsTrivialRight
            (lfkScaleConstraint 1
              (LfkConstraint.mk coefficientVector boundValue
                LfkRelation.isStrictlyGreater)) rfl)
      let scaledSat : lfkIntLt
          (lfkIntScaleByNat denominator (lfkIntScaleByNat 1 boundValue))
          (lfkDotProduct env (lfkScaleCoefficientVector 1 coefficientVector)) = true :=
        (congrArg
            (fun probe => lfkSatisfiesConstraint env
              (lreScaleConstraintBound denominator probe)) sumCollapse).symm.trans
          sumSatisfied
      lreIntLtCongrRight
        ((congrArg
            (fun probe => lfkIntEq probe (lfkDotProduct env coefficientVector))
            (lfkDotProductScaledVector env 1 coefficientVector)).trans
          (lreIntScaleOneCrossEq (lfkDotProduct env coefficientVector)))
        (lreIntLtCongrLeft
          (lfkIntScaleEqMono denominator (lreIntScaleOneCrossEq boundValue))
          scaledSat)
  | LfkRelation.isEqualTo, contradictoryWitness, _sumSatisfied =>
      Bool.noConfusion contradictoryWitness

/-- UNIT EXTRACT: satisfaction of the scaled unit-provenance weighted sum gives
satisfaction of the scaled row it selects (trivial beyond the system). -/
theorem lreUnitSumSatGivesRowSat (denominator : Nat) (env : List LfkInt) :
    ∀ (system : List LfkConstraint) (rowIndex : Nat),
    lreAllConstraintsInequality system = true →
    lfkSatisfiesConstraint env
      (lreScaleConstraintBound denominator
        (lfkWeightedSum (lfmUnitProvenance rowIndex) system)) = true →
    lfkSatisfiesConstraint env
      (lreScaleConstraintBound denominator (lreConstraintAtIndex rowIndex system))
      = true
  | List.nil, _rowIndex, _systemInequality, _sumSatisfied =>
      lreScaledTrivialSatisfied denominator env
  | headConstraint :: tailSystem, Nat.zero, systemInequality, sumSatisfied =>
      lreHeadSeedExtract denominator env headConstraint.coefficients
        headConstraint.bound tailSystem headConstraint.relation
        (lfkBoolAndDestruct (lfmRelationIsInequality headConstraint.relation)
          (lreAllConstraintsInequality tailSystem) systemInequality).left
        sumSatisfied
  | headConstraint :: tailSystem, Nat.succ indexPred, systemInequality, sumSatisfied =>
      lreUnitSumSatGivesRowSat denominator env tailSystem indexPred
        (lfkBoolAndDestruct (lfmRelationIsInequality headConstraint.relation)
          (lreAllConstraintsInequality tailSystem) systemInequality).right
        (lreUnitSumZeroPeel denominator env headConstraint tailSystem
          (lfmUnitProvenance indexPred) sumSatisfied)

/-- SEEDS TO UNITS: satisfaction of the scaled seed list gives satisfaction of
every in-range scaled unit-provenance weighted sum. -/
theorem lreSeedsSatGivesUnitSat (fullSystem : List LfkConstraint) (denominator : Nat)
    (env : List LfkInt) :
    ∀ (remainingRows : List LfkConstraint) (startIndex : Nat),
    lfkSatisfiesSystem env
      (lfkScaleBoundsForDenominator denominator
        (lfmConstraintsOfRows
          (lfmSeedRowsFromIndex fullSystem remainingRows startIndex))) = true →
    ∀ (offsetIndex : Nat),
    Nat.ble (offsetIndex + 1) (List.length remainingRows) = true →
    lfkSatisfiesConstraint env
      (lreScaleConstraintBound denominator
        (lfkWeightedSum (lfmUnitProvenance (startIndex + offsetIndex)) fullSystem))
      = true
  | List.nil, _startIndex, _seedsSatisfied, _offsetIndex, boundWitness =>
      Bool.noConfusion boundWitness
  | _remainingHead :: remainingTail, startIndex, seedsSatisfied, Nat.zero,
      _boundWitness =>
      (lfkBoolAndDestruct
        (lfkSatisfiesConstraint env
          (lreScaleConstraintBound denominator
            (lfkWeightedSum (lfmUnitProvenance startIndex) fullSystem)))
        (lfkSatisfiesSystem env
          (lfkScaleBoundsForDenominator denominator
            (lfmConstraintsOfRows
              (lfmSeedRowsFromIndex fullSystem remainingTail (startIndex + 1)))))
        seedsSatisfied).left
  | _remainingHead :: remainingTail, startIndex, seedsSatisfied, Nat.succ offsetPred,
      boundWitness =>
      (congrArg
          (fun probe => lfkSatisfiesConstraint env
            (lreScaleConstraintBound denominator
              (lfkWeightedSum (lfmUnitProvenance probe) fullSystem)))
          (Nat.succ_add startIndex offsetPred)).symm.trans
        (lreSeedsSatGivesUnitSat fullSystem denominator env remainingTail
          (startIndex + 1)
          (lfkBoolAndDestruct
            (lfkSatisfiesConstraint env
              (lreScaleConstraintBound denominator
                (lfkWeightedSum (lfmUnitProvenance startIndex) fullSystem)))
            (lfkSatisfiesSystem env
              (lfkScaleBoundsForDenominator denominator
                (lfmConstraintsOfRows
                  (lfmSeedRowsFromIndex fullSystem remainingTail (startIndex + 1)))))
            seedsSatisfied).right
          offsetPred boundWitness)

/-- Beyond the system's length the indexed constraint is the trivial row. -/
theorem lreConstraintAtIndexBeyond : ∀ (system : List LfkConstraint) (rowIndex : Nat),
    Nat.ble (List.length system) rowIndex = true →
    lreConstraintAtIndex rowIndex system = lfkTrivialConstraint
  | List.nil, _rowIndex, _boundWitness => rfl
  | _headConstraint :: _tailSystem, Nat.zero, boundWitness =>
      Bool.noConfusion boundWitness
  | _headConstraint :: tailSystem, Nat.succ indexPred, boundWitness =>
      lreConstraintAtIndexBeyond tailSystem indexPred boundWitness

/-- Row-indexed satisfaction assembles into whole-system satisfaction. -/
theorem lreIndexedSatGivesSystemSat (denominator : Nat) (env : List LfkInt) :
    ∀ (system : List LfkConstraint),
    (∀ (rowIndex : Nat), lfkSatisfiesConstraint env
      (lreScaleConstraintBound denominator (lreConstraintAtIndex rowIndex system))
      = true) →
    lfkSatisfiesSystem env (lfkScaleBoundsForDenominator denominator system) = true
  | List.nil, _indexedSatisfied => rfl
  | _headConstraint :: tailSystem, indexedSatisfied =>
      lfkBoolAndIntro _ _ (indexedSatisfied 0)
        (lreIndexedSatGivesSystemSat denominator env tailSystem
          (fun rowIndex => indexedSatisfied (rowIndex + 1)))

/-- T1: satisfaction of the scaled SEED list gives satisfaction of the scaled
expanded system itself. -/
theorem lreSeedsSatGivesSystemSat (fullSystem : List LfkConstraint) (denominator : Nat)
    (env : List LfkInt)
    (systemInequality : lreAllConstraintsInequality fullSystem = true)
    (seedsSatisfied : lfkSatisfiesSystem env
      (lfkScaleBoundsForDenominator denominator
        (lfmConstraintsOfRows (lfmSeedRows fullSystem))) = true) :
    lfkSatisfiesSystem env (lfkScaleBoundsForDenominator denominator fullSystem)
      = true :=
  lreIndexedSatGivesSystemSat denominator env fullSystem
    (fun rowIndex =>
      match lfmBoolCases (Nat.ble (rowIndex + 1) (List.length fullSystem)) with
      | Or.inl withinWitness =>
          lreUnitSumSatGivesRowSat denominator env fullSystem rowIndex
            systemInequality
            ((congrArg
                (fun probe => lfkSatisfiesConstraint env
                  (lreScaleConstraintBound denominator
                    (lfkWeightedSum (lfmUnitProvenance probe) fullSystem)))
                (Nat.zero_add rowIndex)).symm.trans
              (lreSeedsSatGivesUnitSat fullSystem denominator env fullSystem 0
                seedsSatisfied rowIndex withinWitness))
      | Or.inr beyondWitness =>
          (congrArg
              (fun probe => lfkSatisfiesConstraint env
                (lreScaleConstraintBound denominator probe))
              (lreConstraintAtIndexBeyond fullSystem rowIndex
                (lfmNatBleFalseFlipStrict (rowIndex + 1) (List.length fullSystem)
                  beyondWitness))).trans
            (lreScaledTrivialSatisfied denominator env))

/-- T2: satisfaction of the scaled EXPANDED system re-assembles equalities and
gives satisfaction of the scaled original system. -/
theorem lreExpandedScaledSatGivesOriginalScaledSat (denominator : Nat)
    (env : List LfkInt) : ∀ (system : List LfkConstraint),
    lfkSatisfiesSystem env
      (lfkScaleBoundsForDenominator denominator (lfkExpandSystem system)) = true →
    lfkSatisfiesSystem env (lfkScaleBoundsForDenominator denominator system) = true
  | List.nil, _satisfiedWitness => rfl
  | LfkConstraint.mk headCoefficients headBound LfkRelation.isGreaterOrEqual
      :: systemTail, satisfiedWitness =>
      let destructured := lfkBoolAndDestruct
        (lfkSatisfiesConstraint env
          (lreScaleConstraintBound denominator
            (LfkConstraint.mk headCoefficients headBound
              LfkRelation.isGreaterOrEqual)))
        (lfkSatisfiesSystem env
          (lfkScaleBoundsForDenominator denominator (lfkExpandSystem systemTail)))
        satisfiedWitness
      lfkBoolAndIntro _ _ destructured.left
        (lreExpandedScaledSatGivesOriginalScaledSat denominator env systemTail
          destructured.right)
  | LfkConstraint.mk headCoefficients headBound LfkRelation.isStrictlyGreater
      :: systemTail, satisfiedWitness =>
      let destructured := lfkBoolAndDestruct
        (lfkSatisfiesConstraint env
          (lreScaleConstraintBound denominator
            (LfkConstraint.mk headCoefficients headBound
              LfkRelation.isStrictlyGreater)))
        (lfkSatisfiesSystem env
          (lfkScaleBoundsForDenominator denominator (lfkExpandSystem systemTail)))
        satisfiedWitness
      lfkBoolAndIntro _ _ destructured.left
        (lreExpandedScaledSatGivesOriginalScaledSat denominator env systemTail
          destructured.right)
  | LfkConstraint.mk headCoefficients headBound LfkRelation.isEqualTo
      :: systemTail, satisfiedWitness =>
      let scaledBound := lfkIntScaleByNat denominator headBound
      let dotValue := lfkDotProduct env headCoefficients
      let destructuredForward := lfkBoolAndDestruct
        (lfkSatisfiesConstraint env
          (lreScaleConstraintBound denominator
            (lfkForwardEqualityRow
              (LfkConstraint.mk headCoefficients headBound LfkRelation.isEqualTo))))
        (lfkSatisfiesSystem env
          (lfkScaleBoundsForDenominator denominator
            (lfkFlipEqualityRow
              (LfkConstraint.mk headCoefficients headBound LfkRelation.isEqualTo)
              :: lfkExpandSystem systemTail)))
        satisfiedWitness
      let destructuredFlip := lfkBoolAndDestruct
        (lfkSatisfiesConstraint env
          (lreScaleConstraintBound denominator
            (lfkFlipEqualityRow
              (LfkConstraint.mk headCoefficients headBound LfkRelation.isEqualTo))))
        (lfkSatisfiesSystem env
          (lfkScaleBoundsForDenominator denominator (lfkExpandSystem systemTail)))
        destructuredForward.right
      let flipTransported : lfkIntLe (lfkIntNegate scaledBound)
          (lfkIntNegate dotValue) = true :=
        (congrArg (fun probe => lfkIntLe (lfkIntNegate scaledBound) probe)
          (lfkDotProductNegatedVector env headCoefficients)).symm.trans
          destructuredFlip.left
      let reverseBound : Nat.le (dotValue.positivePart + scaledBound.negativePart)
          (scaledBound.positivePart + dotValue.negativePart) :=
        lfkNatLeCongr (Nat.add_comm dotValue.positivePart scaledBound.negativePart)
          (Nat.add_comm scaledBound.positivePart dotValue.negativePart)
          (lfkNatLeOfBle _ _ flipTransported)
      let equalitySatisfied : lfkIntEq dotValue scaledBound = true :=
        lfkNatBeqOfEq _ _
          (lfmNatEqOfBleBle (dotValue.positivePart + scaledBound.negativePart)
            (scaledBound.positivePart + dotValue.negativePart)
            (lfkNatBleOfLe _ _ reverseBound) destructuredForward.left)
      lfkBoolAndIntro _ _ equalitySatisfied
        (lreExpandedScaledSatGivesOriginalScaledSat denominator env systemTail
          destructuredFlip.right)

/-! ## THE COMPLETENESS INHABITANT — the sibling wall Prop, verbatim -/

/-- FARKAS COMPLETENESS HOLDS: every rationally infeasible system has an
accepted certificate — `lfkFarkasCompletenessStatement` (the
LinearFarkasCertificate wall Prop, ascribed verbatim) is INHABITED.  On a scan
hit the composition theorem hands over the checker-accepted certificate; on a
clean scan the ground base, the backward driver induction through the corrected
round extension, the unit-provenance seed extraction, and the equality
re-assembly produce a satisfying scaled environment, contradicting the
infeasibility hypothesis. -/
theorem lreFarkasCompletenessHolds : lfkFarkasCompletenessStatement :=
  fun system infeasibilityWitness =>
    match foundShape : lfmFindRefutationCertificate system with
    | Option.some certificate =>
        Exists.intro certificate
          (lfmFoundContradictionCertifies system certificate foundShape)
    | Option.none =>
        let expandedSystem := lfkExpandSystem system
        let eliminationFuel := lfmMaxCoefficientLength expandedSystem
        let seededRows := lfmSeedRows expandedSystem
        let seedsInequality : lfmAllRowsPass
            (fun row => lfmRelationIsInequality row.constraint.relation) seededRows
            = true :=
          lreSeedRowsFromIndexInequality expandedSystem expandedSystem 0
        let baseSatisfied : lfkSatisfiesSystem List.nil
            (lfkScaleBoundsForDenominator 1
              (lfmConstraintsOfRows
                (lfmEliminateFromIndex 0 eliminationFuel seededRows))) = true :=
          lreGroundCleanRowsSatisfied
            (lfmEliminateFromIndex 0 eliminationFuel seededRows)
            (lfmFinalRowsAreGround system)
            (lreDriverPreservesInequality eliminationFuel 0 seededRows
              seedsInequality)
            foundShape
        False.elim
          (Exists.elim
            (lreDriverBackwardExtension eliminationFuel 0 seededRows seedsInequality
              (Exists.intro 0 (Exists.intro List.nil baseSatisfied)))
            (fun witnessDenominatorPred innerExists =>
              Exists.elim innerExists (fun witnessEnv seedsSatisfied =>
                infeasibilityWitness witnessDenominatorPred witnessEnv
                  (lreExpandedScaledSatGivesOriginalScaledSat
                    (witnessDenominatorPred + 1) witnessEnv system
                    (lreSeedsSatGivesSystemSat expandedSystem
                      (witnessDenominatorPred + 1) witnessEnv
                      (lreExpandSystemInequality system) seedsSatisfied)))))

/-! ## The scaled-checker kit — accepted certificates refute the rational
    relaxation too (feeds the completeness fires) -/

/-- Row splitting commutes with bound scaling (negated bounds scale to negated
scaled bounds definitionally). -/
theorem lreExpandScaleBoundsCommute (denominator : Nat) :
    ∀ (system : List LfkConstraint),
    lfkExpandSystem (lfkScaleBoundsForDenominator denominator system)
      = lfkScaleBoundsForDenominator denominator (lfkExpandSystem system)
  | List.nil => rfl
  | LfkConstraint.mk _headCoefficients _headBound LfkRelation.isGreaterOrEqual
      :: systemTail =>
      congrArg
        (List.cons (LfkConstraint.mk _headCoefficients
          (lfkIntScaleByNat denominator _headBound) LfkRelation.isGreaterOrEqual))
        (lreExpandScaleBoundsCommute denominator systemTail)
  | LfkConstraint.mk _headCoefficients _headBound LfkRelation.isStrictlyGreater
      :: systemTail =>
      congrArg
        (List.cons (LfkConstraint.mk _headCoefficients
          (lfkIntScaleByNat denominator _headBound) LfkRelation.isStrictlyGreater))
        (lreExpandScaleBoundsCommute denominator systemTail)
  | LfkConstraint.mk _headCoefficients _headBound LfkRelation.isEqualTo
      :: systemTail =>
      congrArg
        (fun probe =>
          LfkConstraint.mk _headCoefficients
            (lfkIntScaleByNat denominator _headBound) LfkRelation.isGreaterOrEqual
          :: LfkConstraint.mk (lfkNegateCoefficientVector _headCoefficients)
            (lfkIntNegate (lfkIntScaleByNat denominator _headBound))
            LfkRelation.isGreaterOrEqual
          :: probe)
        (lreExpandScaleBoundsCommute denominator systemTail)

/-- Weighted sums commute with bound scaling. -/
theorem lreWeightedSumOfScaledBounds : ∀ (certificate : List Nat)
    (system : List LfkConstraint) (denominator : Nat),
    lfkWeightedSum certificate (lfkScaleBoundsForDenominator denominator system)
      = lreScaleConstraintBound denominator (lfkWeightedSum certificate system)
  | List.nil, List.nil, _denominator => rfl
  | List.nil, _constraintHead :: _constraintTail, _denominator => rfl
  | _multiplierHead :: _multiplierTail, List.nil, _denominator => rfl
  | multiplierHead :: multiplierTail, constraintHead :: constraintTail, denominator =>
      (congrArg
          (lfkAddConstraints
            (lfkScaleConstraint multiplierHead
              (lreScaleConstraintBound denominator constraintHead)))
          (lreWeightedSumOfScaledBounds multiplierTail constraintTail denominator)).trans
        (lfmConstraintMkCongr rfl
          ((congrArg
              (fun probe => lfkIntAdd probe
                (lfkIntScaleByNat denominator
                  (lfkWeightedSum multiplierTail constraintTail).bound))
              ((lfmIntScaleCompose multiplierHead denominator
                  constraintHead.bound).symm.trans
                ((congrArg (fun probe => lfkIntScaleByNat probe constraintHead.bound)
                    (Nat.mul_comm multiplierHead denominator)).trans
                  (lfmIntScaleCompose denominator multiplierHead
                    constraintHead.bound)))).trans
            (lfkIntScaleAddDistrib denominator
              (lfkIntScaleByNat multiplierHead constraintHead.bound)
              (lfkWeightedSum multiplierTail constraintTail).bound).symm)
          rfl)

/-- A ground contradiction stays a ground contradiction after scaling the bound
by a positive denominator. -/
theorem lreGroundContradictionScaledBound (denominatorPred : Nat)
    (constraint : LfkConstraint)
    (contradictionWitness : lfkIsGroundContradiction constraint = true) :
    lfkIsGroundContradiction
      (lreScaleConstraintBound (denominatorPred + 1) constraint) = true :=
  let destructured := lfkBoolAndDestruct
    (lfkAllCoefficientsAreZero constraint.coefficients)
    (lfkBoundViolatesRelation constraint.relation constraint.bound)
    contradictionWitness
  let violationScaled : lfkBoundViolatesRelation constraint.relation
      (lfkIntScaleByNat (denominatorPred + 1) constraint.bound) = true :=
    match constraint.relation, destructured.right with
    | LfkRelation.isGreaterOrEqual, positiveWitness =>
        lfkNatBleOfLe _ _
          (Nat.le_trans
            (Nat.add_le_add_left (Nat.succ_le_succ (Nat.zero_le denominatorPred))
              ((denominatorPred + 1) * constraint.bound.negativePart))
            (Nat.le_trans
              (Nat.le_of_eq
                ((congrArg
                    (fun probe => (denominatorPred + 1)
                      * constraint.bound.negativePart + probe)
                    (Nat.mul_one (denominatorPred + 1)).symm).trans
                  (Nat.mul_add (denominatorPred + 1) constraint.bound.negativePart
                    1).symm))
              (lfkNatMulLeMulLeft (denominatorPred + 1)
                (lfkNatLeOfBle _ _ positiveWitness))))
    | LfkRelation.isStrictlyGreater, nonNegativeWitness =>
        lfkNatBleOfLe _ _
          (lfkNatMulLeMulLeft (denominatorPred + 1)
            (lfkNatLeOfBle _ _ nonNegativeWitness))
    | LfkRelation.isEqualTo, nonZeroWitness =>
        match lfmBoolCases (lfkIntIsZero
          (lfkIntScaleByNat (denominatorPred + 1) constraint.bound)) with
        | Or.inr scaledNonZero => (congrArg Bool.not scaledNonZero).trans rfl
        | Or.inl scaledZero =>
            Bool.noConfusion
              ((lfkNatBeqOfEq constraint.bound.positivePart
                  constraint.bound.negativePart
                  (lreNatMulLeftCancelEq denominatorPred
                    constraint.bound.positivePart constraint.bound.negativePart
                    (lfkNatEqOfBeq _ _ scaledZero))).symm.trans
                (lfkBoolNotTrueImpliesFalse _ nonZeroWitness))
  lfkBoolAndIntro _ _ destructured.left violationScaled

/-- Accepted certificates stay accepted against the denominator-scaled system. -/
theorem lreCheckerAcceptsScaledBounds (denominatorPred : Nat)
    (certificate : List Nat) (system : List LfkConstraint)
    (checkWitness : lfkCheckRefutation certificate system = true) :
    lfkCheckRefutation certificate
      (lfkScaleBoundsForDenominator (denominatorPred + 1) system) = true :=
  (congrArg lfkIsGroundContradiction
      ((congrArg (lfkWeightedSum certificate)
          (lreExpandScaleBoundsCommute (denominatorPred + 1) system)).trans
        (lreWeightedSumOfScaledBounds certificate (lfkExpandSystem system)
          (denominatorPred + 1)))).trans
    (lreGroundContradictionScaledBound denominatorPred
      (lfkWeightedSum certificate (lfkExpandSystem system)) checkWitness)

/-- An accepted certificate witnesses RATIONAL infeasibility in the
denominator encoding — exactly the hypothesis shape of
`lfkFarkasCompletenessStatement`. -/
theorem lreScaledInfeasibilityOfAcceptedCertificate (certificate : List Nat)
    (system : List LfkConstraint)
    (checkWitness : lfkCheckRefutation certificate system = true) :
    ∀ (denominatorPred : Nat) (env : List LfkInt),
    lfkSatisfiesSystem env
      (lfkScaleBoundsForDenominator (denominatorPred + 1) system) = true → False :=
  fun denominatorPred env satisfactionWitness =>
    lfkRefutationSoundUnconditional certificate
      (lfkScaleBoundsForDenominator (denominatorPred + 1) system)
      (lreCheckerAcceptsScaledBounds denominatorPred certificate system checkWitness)
      env satisfactionWitness

/-! ## Markers -/

/-- DECIDED marker: the ROUND-EXTENSION push — the wall Prop
`lfmRoundExtensionStatement` REFUTED as stated
(`lreRoundExtensionStatementRefuted`: equality rows enter a single sign bucket
and their opposite bound is forgotten), the corrected inequality-guarded form
`lreRoundExtensionInequalityStatement` PROVEN (`lreRoundExtensionHolds`) with
the midpoint witness and the whole-unit strict headroom, and the full
environment-update/dot-decomposition + endpoint-selection kit shipped
zero-axiom.  Supersedes the sibling's round-extension wall CONTENT; the
sibling's owner flag `fxDissatArith_hasFourierMotzkinCompleteness := false`
stays byte-intact THERE as a historical record of that file's scope. -/
def fxDissatArith_hasRoundExtension : Bool := true

/-- REFUTATION marker: `lfmRoundExtensionStatement` as literally stated is
FALSE — machine-checked by `lreRoundExtensionStatementRefuted` on the
`[x = 0, x >= 1]` fixture. -/
def fxDissatArith_roundExtensionAsStatedRefuted : Bool := true

/-- THE CASCADE marker: `lfkFarkasCompletenessStatement` — the
LinearFarkasCertificate wall, verbatim — is INHABITED by
`lreFarkasCompletenessHolds`: every rationally infeasible system yields a
checker-accepted Farkas certificate through the Fourier–Motzkin finder.
Supersedes the CONTENT of the sibling walls
`fxDissatArith_hasFarkasCompleteness := false` (LinearFarkasCertificate.lean)
and `fxDissatArith_hasFourierMotzkinCompleteness := false`
(FourierMotzkinCompleteness.lean); both flags stay byte-intact in their files
per the no-edit discipline. -/
def fxDissatArith_hasFourierMotzkinCompletenessProven : Bool := true

/-! ## Smokes — the two-round backward extension fire, the refutation pins,
    the completeness fires (Bool outputs only; FALSE cases included) -/

/-- Extension fire fixture, lower row: `x + y >= 3`. -/
def lreSmokeLowerRow : LfmCertifiedRow :=
  LfmCertifiedRow.mk
    (LfkConstraint.mk (LfkInt.mk 1 0 :: LfkInt.mk 1 0 :: List.nil) (LfkInt.mk 3 0)
      LfkRelation.isGreaterOrEqual)
    (1 :: List.nil)

/-- Extension fire fixture, upper row: `-x + y >= 1`. -/
def lreSmokeUpperRow : LfmCertifiedRow :=
  LfmCertifiedRow.mk
    (LfkConstraint.mk (LfkInt.mk 0 1 :: LfkInt.mk 1 0 :: List.nil) (LfkInt.mk 1 0)
      LfkRelation.isGreaterOrEqual)
    (0 :: 1 :: List.nil)

/-- The satisfiable two-variable extension fixture (`x` bounded both ways). -/
def lreSmokeExtensionRows : List LfmCertifiedRow :=
  lreSmokeLowerRow :: lreSmokeUpperRow :: List.nil

/-- Kernel pin: round 0 (eliminate `x`) cross-combines the pair into
`0·x + 2y >= 4` (the `x`-column entry is the cross-zero `(1,1)`). -/
theorem lreSmokeRoundOneOutputPin :
    lfmConstraintsOfRows (lfmEliminationRound 0 lreSmokeExtensionRows)
      = LfkConstraint.mk (LfkInt.mk 1 1 :: LfkInt.mk 2 0 :: List.nil) (LfkInt.mk 4 0)
          LfkRelation.isGreaterOrEqual :: List.nil := rfl

/-- Kernel pin: round 1 (eliminate `y`) leaves NO rows (lower bounds only). -/
theorem lreSmokeRoundTwoOutputPin :
    lfmConstraintsOfRows
      (lfmEliminationRound 1 (lfmEliminationRound 0 lreSmokeExtensionRows))
      = List.nil := rfl

/-- Kernel pin, BACKWARD STAGE 1: the lone-lower-bucket witness `y = 3` at
denominator 2 (numerator 6 = best lower numerator `4` padded by one whole
denominator unit `D·aStar = 1·2`) satisfies the round-0 output. -/
theorem lreSmokeBackwardStageOnePin :
    lfkSatisfiesSystem (LfkInt.mk 0 0 :: LfkInt.mk 6 0 :: List.nil)
      (lfkScaleBoundsForDenominator 2
        (lfmConstraintsOfRows (lfmEliminationRound 0 lreSmokeExtensionRows)))
      = true := rfl

/-- Kernel pin, BACKWARD STAGE 2: the midpoint witness `x = 1` at denominator 4
(cleared numerator `(12,8) ~ 4` = `cStar·LStar + aStar·UStar` with
`LStar = (6,6) ~ 0`, `UStar = (6,2) ~ 4`, `aStar = cStar = 1` — the midpoint of
the interval `[0, 2]` seen at `y = 3`) together with the rescaled `y` entry
satisfies the ORIGINAL two rows — the concrete two-round extension witness,
constructed exactly as `lreRoundExtensionForInequalityRows` does. -/
theorem lreSmokeBackwardStageTwoPin :
    lfkSatisfiesSystem (LfkInt.mk 12 8 :: LfkInt.mk 12 0 :: List.nil)
      (lfkScaleBoundsForDenominator 4 (lfmConstraintsOfRows lreSmokeExtensionRows))
      = true := rfl

/-- Kernel pin (control): the extension fixture is satisfiable — the finder
scans clean on it. -/
theorem lreSmokeExtensionScanCleanPin :
    lfmScanFoundNothing (lfmConstraintsOfRows lreSmokeExtensionRows) = true := rfl

/-- Kernel pin: the refutation instance's HYPOTHESIS — the empty environment
satisfies the (empty) round output of the `[x = 0, x >= 1]` fixture at
denominator 1. -/
theorem lreRefutationHypothesisHoldsPin :
    lfkSatisfiesSystem List.nil
      (lfkScaleBoundsForDenominator 1
        (lfmConstraintsOfRows (lfmEliminationRound 0 lreRefutationRows))) = true := rfl

/-- Kernel pin (FALSE case): the refutation INPUT rejects the pinned-to-zero
environment at denominator 1 (`x = 0` holds but `x >= 1` fails). -/
theorem lreRefutationInputRejectsZeroPin :
    lfkSatisfiesSystem (LfkInt.mk 0 0 :: List.nil)
      (lfkScaleBoundsForDenominator 1 (lfmConstraintsOfRows lreRefutationRows))
      = false := rfl

/-- COMPLETENESS FIRE 1: the inhabitant applied to the sibling's classic
`x >= 1, -x >= 0` fixture — rational infeasibility supplied by the accepted
`[1, 1]` certificate through the scaled-checker kit — yields a checked
certificate end-to-end. -/
theorem lreSmokeCompletenessFiredOnContradictory :
    ∃ (certificate : List Nat),
      lfkCheckRefutation certificate lfkSmokeContradictorySystem = true :=
  lreFarkasCompletenessHolds lfkSmokeContradictorySystem
    (lreScaledInfeasibilityOfAcceptedCertificate (1 :: 1 :: List.nil)
      lfkSmokeContradictorySystem rfl)

/-- COMPLETENESS FIRE 2: the strictness fixture `x > 0, -x >= 0`. -/
theorem lreSmokeCompletenessFiredOnStrict :
    ∃ (certificate : List Nat),
      lfkCheckRefutation certificate lfkSmokeStrictSystem = true :=
  lreFarkasCompletenessHolds lfkSmokeStrictSystem
    (lreScaledInfeasibilityOfAcceptedCertificate (1 :: 1 :: List.nil)
      lfkSmokeStrictSystem rfl)

/-- COMPLETENESS FIRE 3: the two-variable chain `x >= 1, -x + y >= 1, -y >= -1`. -/
theorem lreSmokeCompletenessFiredOnTwoVariableChain :
    ∃ (certificate : List Nat),
      lfkCheckRefutation certificate lfmSmokeTwoVariableChainSystem = true :=
  lreFarkasCompletenessHolds lfmSmokeTwoVariableChainSystem
    (lreScaledInfeasibilityOfAcceptedCertificate (1 :: 1 :: 1 :: List.nil)
      lfmSmokeTwoVariableChainSystem rfl)

-- Round 0 of the extension fixture eliminates x into 2y >= 4. Expect: true
#eval Nat.beq (List.length
  (lfmConstraintsOfRows (lfmEliminationRound 0 lreSmokeExtensionRows))) 1
-- Round 1 then eliminates y into the empty system. Expect: true
#eval Nat.beq (List.length (lfmConstraintsOfRows
  (lfmEliminationRound 1 (lfmEliminationRound 0 lreSmokeExtensionRows)))) 0
-- Backward stage 1: y = 3 at denominator 2 satisfies the round-0 output. Expect: true
#eval lfkSatisfiesSystem (LfkInt.mk 0 0 :: LfkInt.mk 6 0 :: List.nil)
  (lfkScaleBoundsForDenominator 2
    (lfmConstraintsOfRows (lfmEliminationRound 0 lreSmokeExtensionRows)))
-- Backward stage 2: x = 1, y = 3 at denominator 4 satisfy the input. Expect: true
#eval lfkSatisfiesSystem (LfkInt.mk 12 8 :: LfkInt.mk 12 0 :: List.nil)
  (lfkScaleBoundsForDenominator 4 (lfmConstraintsOfRows lreSmokeExtensionRows))
-- Control: the extension fixture is satisfiable, the finder scans clean. Expect: true
#eval lfmScanFoundNothing (lfmConstraintsOfRows lreSmokeExtensionRows)
-- The refutation fixture's round output is EMPTY. Expect: true
#eval Nat.beq (List.length
  (lfmConstraintsOfRows (lfmEliminationRound 0 lreRefutationRows))) 0
-- FALSE case: the refutation input rejects x = 0 at denominator 1. Expect: false
#eval lfkSatisfiesSystem (LfkInt.mk 0 0 :: List.nil)
  (lfkScaleBoundsForDenominator 1 (lfmConstraintsOfRows lreRefutationRows))
-- Scaled-checker kit: [1,1] stays accepted at denominator 7. Expect: true
#eval lfkCheckRefutation (1 :: 1 :: List.nil)
  (lfkScaleBoundsForDenominator 7 lfkSmokeContradictorySystem)

end FX1Poly.ComputerAlgebra
