/-! # FX1Poly/ComputerAlgebra/Decision/LinearFarkasCertificate — the DISSAT-ARITH certificate route
    (integer linear-arithmetic refutation by Farkas certificates, Nat multipliers)

Half 1 of the DISSAT-ARITH lane: an unsatisfiability CERTIFICATE checker for systems of
integer linear constraints, after Besson's weakened Farkas lemma (Fast Reflexive
Arithmetic Tactics, TYPES'06, Lemma 2) and the Rocq micromega / SMT `la_generic`
checker split: an untrusted FINDER (not in scope here) emits a list of nonnegative
multipliers; the verified CHECKER scales each constraint by its multiplier, adds
everything up, and accepts exactly when the weighted sum is a GROUND contradiction
(all variable coefficients cancel and the residual numeric comparison is false).  The
headline theorem `lfkRefutationSound` lives entirely on the checker: an accepted
certificate refutes EVERY integer environment.

## The integer kit — (positivePart, negativePart) Nat pairs

`LfkInt` represents the integer `positivePart - negativePart`; the representation is
NEVER normalized (certificate arithmetic only ADDS and SCALES, and every comparison is
a cross-sum on Nat, e.g. `a <= b  :=  Nat.ble (a.pos + b.neg) (b.pos + a.neg)`).  This
keeps the whole file inside the kernel-clean Nat kit: no `Int`, no `Nat.sub`, no
normalization lemmas.  Strict order is the succ-le form (`... + 1 <= ...`).

## Constraints, dense vectors, truncating dot product

A constraint is `coefficients . env  REL  bound` with `REL` one of `>=`, `>`, `=`.
Coefficient vectors and environments are DENSE `List LfkInt` indexed by variable
0, 1, 2, ...; `lfkDotProduct` zips structurally and TRUNCATES at the shorter list
(absent entries read as zero).  Vector addition (`lfkAddCoefficientVectors`) PADS: when
one summand runs out the other's tail is kept verbatim, so the empty list is a genuine
zero vector and dot-product additivity holds with NO length hypotheses — the soundness
theorem is stated both unconditionally (`lfkRefutationSoundUnconditional`) and in the
commissioned length-guarded form (`lfkRefutationSound`).

## Equalities — row splitting (the SMT-checker convention)

A Nat multiplier cannot subtract, but refutations may need an equality with a NEGATIVE
weight.  Following the Alethe/cvc5 convention (and the brief's recommendation over
micromega's Equal-op partial checker), `lfkExpandSystem` replaces each `isEqualTo` row
by TWO `isGreaterOrEqual` rows — the row itself and its flip (coefficients and bound
negated, i.e. both (pos,neg) pairs swapped).  A certificate is a bare `List Nat`
aligned with the EXPANDED system: an equality row consumes two consecutive multiplier
slots (forward weight, then backward weight), so the signed weight lambda+ - lambda- is
expressed without ever writing a signed number.  A certificate shorter than the
expanded system leaves the remaining rows unused (multiplier zero); extra entries are
ignored — both are sound because the weighted-sum lemma quantifies over exactly the
rows that are incorporated.

## Strictness threading (the Motzkin corner)

`lfkScaleRelation` degrades a strict row scaled by 0 to `>=` (0·(t > b) would be the
FALSE ground row 0 > 0), and `lfkJoinRelations` makes strict absorb (`isEqualTo` is the
additive unit, per the micromega `OpAdd` table restricted to the expanded fragment).
Hence the weighted sum is strict exactly when some strict row carries a POSITIVE
multiplier, and the final numeric test matches the joined relation: a `>=` sum is
contradictory when its bound is strictly positive, a `>` sum already when the bound is
nonnegative, an `=` sum when the bound is nonzero (unreachable from the checker path —
the fold's base relation is `>=` — but kept total and proved sound).

## Soundness (the commissioned bar — DECIDED)

  * `lfkWeightedSumSatisfied` — any environment satisfying every row satisfies the
    weighted sum (induction along the fold; per step `lfkScalePreservesSatisfaction`
    and `lfkAddPreservesSatisfaction`, the latter a 9-case relation-join dispatch over
    the cross-sum monotonicity kit).
  * `lfkSatisfiesExpandedOfSatisfies` — satisfaction transports to the expanded system
    (an equality yields both derived inequalities; the flip side goes through
    `lfkDotProductNegatedVector`, which is definitional on (pos,neg) pairs).
  * `lfkGroundContradictionRefutes` — a satisfied ground-contradictory row is `False`
    (all-zero coefficients force a cross-zero dot value; the residual Nat comparison
    collapses to `x + 1 <= x`).
  * `lfkRefutationSound` / `lfkRefutationSoundUnconditional` — the composition:
    `lfkCheckRefutation certificate system = true` refutes every environment.

## The honest walls (owner-false, NOT attempted)

  * `lfkFarkasCompletenessStatement` — every RATIONALLY infeasible system (encoded
    integer-only: no scaled environment satisfies the denominator-scaled system) has an
    accepted certificate.  True classically (Farkas/Motzkin); constructively REACHABLE
    by Fourier–Motzkin elimination with certificate composition — fuel = variable
    count, eliminate one variable per round, each derived row carries its two-row
    provenance, compose multipliers back down the elimination tree.  This is a genuine
    future brick, NOT Dickson-walled (FM terminates structurally on the variable
    count).  Owner `fxDissatArith_hasFarkasCompleteness := false`.
  * `lfkPresburgerDecisionStatement` — full integer satisfiability decision (Cooper
    quantifier elimination; Farkas alone is incomplete over the integers — the
    canonical gap `2x = 1` is rationally feasible, hence certificate-free, yet has no
    integer solution).  A SEPARATE future brick.  Owner
    `fxDissatArith_hasPresburgerDecision := false`.

## Zero-axiom discipline

Init only, no repo imports.  Structural recursion throughout; no `WellFounded.fix`.
No `propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`, `funext`,
`omega`, no `decide` on `Prop`, no catch-all match arms.  Nat facts restricted to the
probed-clean core family (`Nat.add_comm/assoc`, `Nat.mul_add/mul_comm/zero_mul/
succ_mul/mul_one`, the plain `le` kit) plus hand-rolled `ble`/`beq` reflection,
left-cancellation, and mul-monotonicity; the four-term AC shuffle is the single
hand-proved `lfkNatAddSwapMiddle`.  All list helpers are bespoke, monomorphic,
cons-only — no `List.append`.  Per-declaration gate in
`FX1PolyAudit/ComputerAlgebra/Decision/LinearFarkasCertificate.lean`. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace FX1Poly.ComputerAlgebra

/-! ## Nat kit — hand-rolled ble/beq reflection and the AC/cancellation helpers -/

/-- `Nat.beq` is reflexive (structural induction; `beq (succ v) (succ v)` is
definitionally `beq v v`). -/
theorem lfkNatBeqRefl : ∀ (value : Nat), Nat.beq value value = true
  | Nat.zero => rfl
  | Nat.succ smallerValue => lfkNatBeqRefl smallerValue

/-- Propositional equality gives boolean equality. -/
theorem lfkNatBeqOfEq (leftValue rightValue : Nat) (valuesEq : leftValue = rightValue) :
    Nat.beq leftValue rightValue = true :=
  (congrArg (Nat.beq leftValue) valuesEq).symm.trans (lfkNatBeqRefl leftValue)

/-- Boolean equality gives propositional equality (double structural recursion). -/
theorem lfkNatEqOfBeq : ∀ (leftValue rightValue : Nat),
    Nat.beq leftValue rightValue = true → leftValue = rightValue
  | Nat.zero, Nat.zero, _trivialWitness => rfl
  | Nat.zero, Nat.succ _rightPred, contradictoryWitness => Bool.noConfusion contradictoryWitness
  | Nat.succ _leftPred, Nat.zero, contradictoryWitness => Bool.noConfusion contradictoryWitness
  | Nat.succ leftPred, Nat.succ rightPred, headWitness =>
      congrArg Nat.succ (lfkNatEqOfBeq leftPred rightPred headWitness)

/-- `Nat.ble` reflects into `Nat.le` (double structural recursion). -/
theorem lfkNatLeOfBle : ∀ (leftValue rightValue : Nat),
    Nat.ble leftValue rightValue = true → Nat.le leftValue rightValue
  | Nat.zero, rightValue, _trivialWitness => Nat.zero_le rightValue
  | Nat.succ _leftPred, Nat.zero, contradictoryWitness => Bool.noConfusion contradictoryWitness
  | Nat.succ leftPred, Nat.succ rightPred, tailWitness =>
      Nat.succ_le_succ (lfkNatLeOfBle leftPred rightPred tailWitness)

/-- `Nat.le` computes into `Nat.ble` (double structural recursion). -/
theorem lfkNatBleOfLe : ∀ (leftValue rightValue : Nat),
    Nat.le leftValue rightValue → Nat.ble leftValue rightValue = true
  | Nat.zero, Nat.zero, _trivialWitness => rfl
  | Nat.zero, Nat.succ _rightPred, _trivialWitness => rfl
  | Nat.succ _leftPred, Nat.zero, impossibleWitness => nomatch impossibleWitness
  | Nat.succ leftPred, Nat.succ rightPred, boundWitness =>
      lfkNatBleOfLe leftPred rightPred (Nat.le_of_succ_le_succ boundWitness)

/-- `value + 1 <= value` is absurd (the single contradiction shape every
ground-contradiction case is funneled into). -/
theorem lfkNatSuccLeSelfFalse : ∀ (value : Nat), Nat.le (value + 1) value → False
  | Nat.zero, impossibleWitness => nomatch impossibleWitness
  | Nat.succ smallerValue, boundWitness =>
      lfkNatSuccLeSelfFalse smallerValue (Nat.le_of_succ_le_succ boundWitness)

/-- Congruence for `+` in both operands at once. -/
theorem lfkNatAddCongr {leftValue leftRewritten rightValue rightRewritten : Nat}
    (leftEq : leftValue = leftRewritten) (rightEq : rightValue = rightRewritten) :
    leftValue + rightValue = leftRewritten + rightRewritten :=
  (congrArg (fun probe => probe + rightValue) leftEq).trans
    (congrArg (fun probe => leftRewritten + probe) rightEq)

/-- The four-term AC shuffle `(a + b) + (c + d) = (a + c) + (b + d)` — the ONLY
associativity/commutativity rearrangement the cross-sum kit ever needs. -/
theorem lfkNatAddSwapMiddle (firstTerm secondTerm thirdTerm fourthTerm : Nat) :
    (firstTerm + secondTerm) + (thirdTerm + fourthTerm)
      = (firstTerm + thirdTerm) + (secondTerm + fourthTerm) :=
  (Nat.add_assoc firstTerm secondTerm (thirdTerm + fourthTerm)).trans
    ((congrArg (fun probe => firstTerm + probe)
        (((Nat.add_assoc secondTerm thirdTerm fourthTerm).symm.trans
            (congrArg (fun probe => probe + fourthTerm) (Nat.add_comm secondTerm thirdTerm))).trans
          (Nat.add_assoc thirdTerm secondTerm fourthTerm))).trans
      (Nat.add_assoc firstTerm thirdTerm (secondTerm + fourthTerm)).symm)

/-- Move a `+ 1` out across a right addend: `(a + 1) + b = (a + b) + 1`. -/
theorem lfkNatAddOneShiftOut (leftTerm rightTerm : Nat) :
    (leftTerm + 1) + rightTerm = (leftTerm + rightTerm) + 1 :=
  (Nat.add_assoc leftTerm 1 rightTerm).trans
    ((congrArg (fun probe => leftTerm + probe) (Nat.add_comm 1 rightTerm)).trans
      (Nat.add_assoc leftTerm rightTerm 1).symm)

/-- Left cancellation for Nat addition (structural on the shared term; no
`Nat.sub`, no order lemmas). -/
theorem lfkNatAddLeftCancel : ∀ (sharedTerm leftValue rightValue : Nat),
    sharedTerm + leftValue = sharedTerm + rightValue → leftValue = rightValue
  | Nat.zero, leftValue, rightValue, sumEq =>
      ((Nat.zero_add leftValue).symm.trans sumEq).trans (Nat.zero_add rightValue)
  | Nat.succ sharedPred, leftValue, rightValue, sumEq =>
      lfkNatAddLeftCancel sharedPred leftValue rightValue
        (Nat.succ.inj (((Nat.succ_add sharedPred leftValue).symm.trans sumEq).trans
          (Nat.succ_add sharedPred rightValue)))

/-- Two-sided monotonicity of addition. -/
theorem lfkNatAddLeAdd {leftLow leftHigh rightLow rightHigh : Nat}
    (leftBound : Nat.le leftLow leftHigh) (rightBound : Nat.le rightLow rightHigh) :
    Nat.le (leftLow + rightLow) (leftHigh + rightHigh) :=
  Nat.le_trans (Nat.add_le_add_right leftBound rightLow) (Nat.add_le_add_left rightBound leftHigh)

/-- Transport a `le` fact across equalities of both endpoints (built purely from
`le_of_eq` and `le_trans`; no `Eq.mpr` motives). -/
theorem lfkNatLeCongr {leftValue leftRewritten rightValue rightRewritten : Nat}
    (leftEq : leftValue = leftRewritten) (rightEq : rightValue = rightRewritten)
    (rewrittenBound : Nat.le leftRewritten rightRewritten) : Nat.le leftValue rightValue :=
  Nat.le_trans (Nat.le_of_eq leftEq)
    (Nat.le_trans rewrittenBound (Nat.le_of_eq rightEq.symm))

/-- Left-factor monotonicity of multiplication, hand-rolled by structural induction on
the multiplier (`Nat.mul_le_mul_left` is deliberately avoided — the hand recursion
uses only probed-clean facts). -/
theorem lfkNatMulLeMulLeft : ∀ (multiplier : Nat) {leftValue rightValue : Nat},
    Nat.le leftValue rightValue → Nat.le (multiplier * leftValue) (multiplier * rightValue)
  | Nat.zero, leftValue, rightValue, _boundWitness =>
      lfkNatLeCongr (Nat.zero_mul leftValue) (Nat.zero_mul rightValue) (Nat.le_refl 0)
  | Nat.succ multiplierPred, leftValue, rightValue, boundWitness =>
      lfkNatLeCongr (Nat.succ_mul multiplierPred leftValue) (Nat.succ_mul multiplierPred rightValue)
        (lfkNatAddLeAdd (lfkNatMulLeMulLeft multiplierPred boundWitness) boundWitness)

/-- Hand-rolled multiplication associativity (structural on the third factor; the
library `Nat.mul_assoc` is banned by the leak ledger). -/
theorem lfkNatMulAssoc : ∀ (firstFactor secondFactor thirdFactor : Nat),
    (firstFactor * secondFactor) * thirdFactor = firstFactor * (secondFactor * thirdFactor)
  | _firstFactor, _secondFactor, Nat.zero => rfl
  | firstFactor, secondFactor, Nat.succ thirdPred =>
      (congrArg (fun probe => probe + firstFactor * secondFactor)
          (lfkNatMulAssoc firstFactor secondFactor thirdPred)).trans
        (Nat.mul_add firstFactor (secondFactor * thirdPred) secondFactor).symm

/-- Left commutation `a * (b * c) = b * (a * c)` (assoc + comm + assoc). -/
theorem lfkNatMulLeftCommute (outerFactor middleFactor innerFactor : Nat) :
    outerFactor * (middleFactor * innerFactor) = middleFactor * (outerFactor * innerFactor) :=
  (lfkNatMulAssoc outerFactor middleFactor innerFactor).symm.trans
    ((congrArg (fun probe => probe * innerFactor) (Nat.mul_comm outerFactor middleFactor)).trans
      (lfkNatMulAssoc middleFactor outerFactor innerFactor))

/-- `0 * a + 0 * b = 0` — the zero-multiplier collapse for scaled strict rows. -/
theorem lfkNatBothZeroMulSum (leftValue rightValue : Nat) :
    0 * leftValue + 0 * rightValue = 0 :=
  (lfkNatAddCongr (Nat.zero_mul leftValue) (Nat.zero_mul rightValue)).trans rfl

/-! ## Bool kit -/

/-- Split a true conjunction into its two true conjuncts (finite case bash). -/
theorem lfkBoolAndDestruct : ∀ (leftFlag rightFlag : Bool),
    (leftFlag && rightFlag) = true → And (leftFlag = true) (rightFlag = true)
  | true, true, _trivialWitness => And.intro rfl rfl
  | true, false, contradictoryWitness => Bool.noConfusion contradictoryWitness
  | false, true, contradictoryWitness => Bool.noConfusion contradictoryWitness
  | false, false, contradictoryWitness => Bool.noConfusion contradictoryWitness

/-- Assemble a true conjunction from two true conjuncts (finite case bash). -/
theorem lfkBoolAndIntro : ∀ (leftFlag rightFlag : Bool),
    leftFlag = true → rightFlag = true → (leftFlag && rightFlag) = true
  | true, true, _leftWitness, _rightWitness => rfl
  | true, false, _leftWitness, contradictoryWitness => Bool.noConfusion contradictoryWitness
  | false, true, contradictoryWitness, _rightWitness => Bool.noConfusion contradictoryWitness
  | false, false, contradictoryWitness, _rightWitness => Bool.noConfusion contradictoryWitness

/-- `Bool.not flag = true` forces `flag = false`. -/
theorem lfkBoolNotTrueImpliesFalse : ∀ (flag : Bool), Bool.not flag = true → flag = false
  | true, contradictoryWitness => Bool.noConfusion contradictoryWitness
  | false, _trivialWitness => rfl

/-! ## Stage 1 — the (positivePart, negativePart) integer kit -/

/-- An integer as an UNNORMALIZED pair of Nats denoting
`positivePart - negativePart`.  Certificates only add and scale, and every comparison
is a cross-sum, so no normalization is ever required. -/
structure LfkInt where
  positivePart : Nat
  negativePart : Nat

/-- The integer zero. -/
def lfkIntZero : LfkInt := LfkInt.mk 0 0

/-- Componentwise addition (represents integer addition). -/
def lfkIntAdd (leftValue rightValue : LfkInt) : LfkInt :=
  LfkInt.mk (leftValue.positivePart + rightValue.positivePart)
    (leftValue.negativePart + rightValue.negativePart)

/-- Sign-aware multiplication:
`(p1 - n1) * (p2 - n2) = (p1*p2 + n1*n2) - (p1*n2 + n1*p2)`. -/
def lfkIntMul (leftValue rightValue : LfkInt) : LfkInt :=
  LfkInt.mk (leftValue.positivePart * rightValue.positivePart
      + leftValue.negativePart * rightValue.negativePart)
    (leftValue.positivePart * rightValue.negativePart
      + leftValue.negativePart * rightValue.positivePart)

/-- Negation is the component swap. -/
def lfkIntNegate (value : LfkInt) : LfkInt :=
  LfkInt.mk value.negativePart value.positivePart

/-- Scaling by a Nat multiplier (the certificate action; both parts scale). -/
def lfkIntScaleByNat (multiplier : Nat) (value : LfkInt) : LfkInt :=
  LfkInt.mk (multiplier * value.positivePart) (multiplier * value.negativePart)

/-- `0 <= value`, i.e. `negativePart <= positivePart` (cross-sum with zero). -/
def lfkIntIsNonNegative (value : LfkInt) : Bool :=
  Nat.ble value.negativePart value.positivePart

/-- `0 < value`, in succ-le form. -/
def lfkIntIsPositive (value : LfkInt) : Bool :=
  Nat.ble (value.negativePart + 1) value.positivePart

/-- `value = 0`, i.e. the parts agree. -/
def lfkIntIsZero (value : LfkInt) : Bool :=
  Nat.beq value.positivePart value.negativePart

/-- Cross-sum boolean equality: `p1 - n1 = p2 - n2  iff  p1 + n2 = p2 + n1`. -/
def lfkIntEq (leftValue rightValue : LfkInt) : Bool :=
  Nat.beq (leftValue.positivePart + rightValue.negativePart)
    (rightValue.positivePart + leftValue.negativePart)

/-- Cross-sum boolean order: `p1 - n1 <= p2 - n2  iff  p1 + n2 <= p2 + n1`. -/
def lfkIntLe (leftValue rightValue : LfkInt) : Bool :=
  Nat.ble (leftValue.positivePart + rightValue.negativePart)
    (rightValue.positivePart + leftValue.negativePart)

/-- Cross-sum strict order in succ-le form. -/
def lfkIntLt (leftValue rightValue : LfkInt) : Bool :=
  Nat.ble (leftValue.positivePart + rightValue.negativePart + 1)
    (rightValue.positivePart + leftValue.negativePart)

/-- Structure congruence from the two field equations. -/
theorem lfkIntMkCongr {leftPositive rightPositive leftNegative rightNegative : Nat}
    (positiveEq : leftPositive = rightPositive) (negativeEq : leftNegative = rightNegative) :
    LfkInt.mk leftPositive leftNegative = LfkInt.mk rightPositive rightNegative :=
  (congrArg (fun probe => LfkInt.mk probe leftNegative) positiveEq).trans
    (congrArg (fun probe => LfkInt.mk rightPositive probe) negativeEq)

/-- Addition commutes (componentwise `Nat.add_comm`). -/
theorem lfkIntAddComm (leftValue rightValue : LfkInt) :
    lfkIntAdd leftValue rightValue = lfkIntAdd rightValue leftValue :=
  lfkIntMkCongr (Nat.add_comm leftValue.positivePart rightValue.positivePart)
    (Nat.add_comm leftValue.negativePart rightValue.negativePart)

/-- Addition associates (componentwise `Nat.add_assoc`). -/
theorem lfkIntAddAssoc (firstValue secondValue thirdValue : LfkInt) :
    lfkIntAdd (lfkIntAdd firstValue secondValue) thirdValue
      = lfkIntAdd firstValue (lfkIntAdd secondValue thirdValue) :=
  lfkIntMkCongr
    (Nat.add_assoc firstValue.positivePart secondValue.positivePart thirdValue.positivePart)
    (Nat.add_assoc firstValue.negativePart secondValue.negativePart thirdValue.negativePart)

/-- Zero is a left identity (right identity is definitional). -/
theorem lfkIntZeroAdd (value : LfkInt) : lfkIntAdd lfkIntZero value = value :=
  lfkIntMkCongr (Nat.zero_add value.positivePart) (Nat.zero_add value.negativePart)

/-- Zero is a right identity (definitional: `x + 0` reduces, then structure eta). -/
theorem lfkIntAddZero (value : LfkInt) : lfkIntAdd value lfkIntZero = value := rfl

/-- Cross-sum equality is reflexive. -/
theorem lfkIntEqRefl (value : LfkInt) : lfkIntEq value value = true :=
  lfkNatBeqRefl (value.positivePart + value.negativePart)

/-- Congruence for `lfkIntAdd` in both operands. -/
theorem lfkIntAddCongr {leftValue leftRewritten rightValue rightRewritten : LfkInt}
    (leftEq : leftValue = leftRewritten) (rightEq : rightValue = rightRewritten) :
    lfkIntAdd leftValue rightValue = lfkIntAdd leftRewritten rightRewritten :=
  (congrArg (fun probe => lfkIntAdd probe rightValue) leftEq).trans
    (congrArg (fun probe => lfkIntAdd leftRewritten probe) rightEq)

/-- The four-term shuffle lifted componentwise. -/
theorem lfkIntAddSwapMiddle (firstValue secondValue thirdValue fourthValue : LfkInt) :
    lfkIntAdd (lfkIntAdd firstValue secondValue) (lfkIntAdd thirdValue fourthValue)
      = lfkIntAdd (lfkIntAdd firstValue thirdValue) (lfkIntAdd secondValue fourthValue) :=
  lfkIntMkCongr
    (lfkNatAddSwapMiddle firstValue.positivePart secondValue.positivePart
      thirdValue.positivePart fourthValue.positivePart)
    (lfkNatAddSwapMiddle firstValue.negativePart secondValue.negativePart
      thirdValue.negativePart fourthValue.negativePart)

/-- Scaling distributes over addition (componentwise `Nat.mul_add`). -/
theorem lfkIntScaleAddDistrib (multiplier : Nat) (leftValue rightValue : LfkInt) :
    lfkIntScaleByNat multiplier (lfkIntAdd leftValue rightValue)
      = lfkIntAdd (lfkIntScaleByNat multiplier leftValue) (lfkIntScaleByNat multiplier rightValue) :=
  lfkIntMkCongr (Nat.mul_add multiplier leftValue.positivePart rightValue.positivePart)
    (Nat.mul_add multiplier leftValue.negativePart rightValue.negativePart)

/-- Multiplication distributes over addition on the right factor. -/
theorem lfkIntMulAddRight (envValue addLeft addRight : LfkInt) :
    lfkIntMul envValue (lfkIntAdd addLeft addRight)
      = lfkIntAdd (lfkIntMul envValue addLeft) (lfkIntMul envValue addRight) :=
  lfkIntMkCongr
    ((lfkNatAddCongr (Nat.mul_add envValue.positivePart addLeft.positivePart addRight.positivePart)
        (Nat.mul_add envValue.negativePart addLeft.negativePart addRight.negativePart)).trans
      (lfkNatAddSwapMiddle (envValue.positivePart * addLeft.positivePart)
        (envValue.positivePart * addRight.positivePart)
        (envValue.negativePart * addLeft.negativePart)
        (envValue.negativePart * addRight.negativePart)))
    ((lfkNatAddCongr (Nat.mul_add envValue.positivePart addLeft.negativePart addRight.negativePart)
        (Nat.mul_add envValue.negativePart addLeft.positivePart addRight.positivePart)).trans
      (lfkNatAddSwapMiddle (envValue.positivePart * addLeft.negativePart)
        (envValue.positivePart * addRight.negativePart)
        (envValue.negativePart * addLeft.positivePart)
        (envValue.negativePart * addRight.positivePart)))

/-- Multiplication commutes past a Nat scale on the right factor. -/
theorem lfkIntMulScaleRight (envValue : LfkInt) (multiplier : Nat) (coefficientValue : LfkInt) :
    lfkIntMul envValue (lfkIntScaleByNat multiplier coefficientValue)
      = lfkIntScaleByNat multiplier (lfkIntMul envValue coefficientValue) :=
  lfkIntMkCongr
    ((lfkNatAddCongr
        (lfkNatMulLeftCommute envValue.positivePart multiplier coefficientValue.positivePart)
        (lfkNatMulLeftCommute envValue.negativePart multiplier coefficientValue.negativePart)).trans
      (Nat.mul_add multiplier (envValue.positivePart * coefficientValue.positivePart)
        (envValue.negativePart * coefficientValue.negativePart)).symm)
    ((lfkNatAddCongr
        (lfkNatMulLeftCommute envValue.positivePart multiplier coefficientValue.negativePart)
        (lfkNatMulLeftCommute envValue.negativePart multiplier coefficientValue.positivePart)).trans
      (Nat.mul_add multiplier (envValue.positivePart * coefficientValue.negativePart)
        (envValue.negativePart * coefficientValue.positivePart)).symm)

/-! ## Order kit on `LfkInt` (Bool-valued, cross-sum reflection) -/

/-- Weaken strict to non-strict. -/
theorem lfkIntLeOfLt {lowerValue higherValue : LfkInt}
    (strictWitness : lfkIntLt lowerValue higherValue = true) :
    lfkIntLe lowerValue higherValue = true :=
  lfkNatBleOfLe (lowerValue.positivePart + higherValue.negativePart)
    (higherValue.positivePart + lowerValue.negativePart)
    (Nat.le_trans (Nat.le_succ (lowerValue.positivePart + higherValue.negativePart))
      (lfkNatLeOfBle (lowerValue.positivePart + higherValue.negativePart + 1)
        (higherValue.positivePart + lowerValue.negativePart) strictWitness))

/-- An equality witness in satisfaction orientation (`dot = bound`) yields the
`bound <= dot` inequality. -/
theorem lfkIntLeOfEqFlip {dotValue boundValue : LfkInt}
    (eqWitness : lfkIntEq dotValue boundValue = true) :
    lfkIntLe boundValue dotValue = true :=
  lfkNatBleOfLe (boundValue.positivePart + dotValue.negativePart)
    (dotValue.positivePart + boundValue.negativePart)
    (Nat.le_of_eq (lfkNatEqOfBeq (dotValue.positivePart + boundValue.negativePart)
      (boundValue.positivePart + dotValue.negativePart) eqWitness).symm)

/-- `<=` adds: the separating-conjunction shape of the Farkas sum. -/
theorem lfkIntAddLeAdd {leftLow leftHigh rightLow rightHigh : LfkInt}
    (leftBound : lfkIntLe leftLow leftHigh = true)
    (rightBound : lfkIntLe rightLow rightHigh = true) :
    lfkIntLe (lfkIntAdd leftLow rightLow) (lfkIntAdd leftHigh rightHigh) = true :=
  lfkNatBleOfLe ((leftLow.positivePart + rightLow.positivePart)
      + (leftHigh.negativePart + rightHigh.negativePart))
    ((leftHigh.positivePart + rightHigh.positivePart)
      + (leftLow.negativePart + rightLow.negativePart))
    (lfkNatLeCongr
      (lfkNatAddSwapMiddle leftLow.positivePart rightLow.positivePart
        leftHigh.negativePart rightHigh.negativePart)
      (lfkNatAddSwapMiddle leftHigh.positivePart rightHigh.positivePart
        leftLow.negativePart rightLow.negativePart)
      (lfkNatAddLeAdd
        (lfkNatLeOfBle (leftLow.positivePart + leftHigh.negativePart)
          (leftHigh.positivePart + leftLow.negativePart) leftBound)
        (lfkNatLeOfBle (rightLow.positivePart + rightHigh.negativePart)
          (rightHigh.positivePart + rightLow.negativePart) rightBound)))

/-- `<` on the left absorbs a `<=` on the right into a strict sum. -/
theorem lfkIntAddLtLe {leftLow leftHigh rightLow rightHigh : LfkInt}
    (leftStrict : lfkIntLt leftLow leftHigh = true)
    (rightBound : lfkIntLe rightLow rightHigh = true) :
    lfkIntLt (lfkIntAdd leftLow rightLow) (lfkIntAdd leftHigh rightHigh) = true :=
  lfkNatBleOfLe ((leftLow.positivePart + rightLow.positivePart)
      + (leftHigh.negativePart + rightHigh.negativePart) + 1)
    ((leftHigh.positivePart + rightHigh.positivePart)
      + (leftLow.negativePart + rightLow.negativePart))
    (lfkNatLeCongr
      ((congrArg (fun probe => probe + 1)
          (lfkNatAddSwapMiddle leftLow.positivePart rightLow.positivePart
            leftHigh.negativePart rightHigh.negativePart)).trans
        (lfkNatAddOneShiftOut (leftLow.positivePart + leftHigh.negativePart)
          (rightLow.positivePart + rightHigh.negativePart)).symm)
      (lfkNatAddSwapMiddle leftHigh.positivePart rightHigh.positivePart
        leftLow.negativePart rightLow.negativePart)
      (lfkNatAddLeAdd
        (lfkNatLeOfBle (leftLow.positivePart + leftHigh.negativePart + 1)
          (leftHigh.positivePart + leftLow.negativePart) leftStrict)
        (lfkNatLeOfBle (rightLow.positivePart + rightHigh.negativePart)
          (rightHigh.positivePart + rightLow.negativePart) rightBound)))

/-- `<=` on the left absorbs a `<` on the right into a strict sum. -/
theorem lfkIntAddLeLt {leftLow leftHigh rightLow rightHigh : LfkInt}
    (leftBound : lfkIntLe leftLow leftHigh = true)
    (rightStrict : lfkIntLt rightLow rightHigh = true) :
    lfkIntLt (lfkIntAdd leftLow rightLow) (lfkIntAdd leftHigh rightHigh) = true :=
  lfkNatBleOfLe ((leftLow.positivePart + rightLow.positivePart)
      + (leftHigh.negativePart + rightHigh.negativePart) + 1)
    ((leftHigh.positivePart + rightHigh.positivePart)
      + (leftLow.negativePart + rightLow.negativePart))
    (lfkNatLeCongr
      ((congrArg (fun probe => probe + 1)
          (lfkNatAddSwapMiddle leftLow.positivePart rightLow.positivePart
            leftHigh.negativePart rightHigh.negativePart)).trans
        (Nat.add_assoc (leftLow.positivePart + leftHigh.negativePart)
          (rightLow.positivePart + rightHigh.negativePart) 1))
      (lfkNatAddSwapMiddle leftHigh.positivePart rightHigh.positivePart
        leftLow.negativePart rightLow.negativePart)
      (lfkNatAddLeAdd
        (lfkNatLeOfBle (leftLow.positivePart + leftHigh.negativePart)
          (leftHigh.positivePart + leftLow.negativePart) leftBound)
        (lfkNatLeOfBle (rightLow.positivePart + rightHigh.negativePart + 1)
          (rightHigh.positivePart + rightLow.negativePart) rightStrict)))

/-- Two stricts add to a strict. -/
theorem lfkIntAddLtLt {leftLow leftHigh rightLow rightHigh : LfkInt}
    (leftStrict : lfkIntLt leftLow leftHigh = true)
    (rightStrict : lfkIntLt rightLow rightHigh = true) :
    lfkIntLt (lfkIntAdd leftLow rightLow) (lfkIntAdd leftHigh rightHigh) = true :=
  lfkIntAddLtLe leftStrict (lfkIntLeOfLt rightStrict)

/-- Two equalities add to an equality (satisfaction orientation `dot = bound`). -/
theorem lfkIntAddEqEq {dotLeft boundLeft dotRight boundRight : LfkInt}
    (leftEqWitness : lfkIntEq dotLeft boundLeft = true)
    (rightEqWitness : lfkIntEq dotRight boundRight = true) :
    lfkIntEq (lfkIntAdd dotLeft dotRight) (lfkIntAdd boundLeft boundRight) = true :=
  lfkNatBeqOfEq ((dotLeft.positivePart + dotRight.positivePart)
      + (boundLeft.negativePart + boundRight.negativePart))
    ((boundLeft.positivePart + boundRight.positivePart)
      + (dotLeft.negativePart + dotRight.negativePart))
    ((lfkNatAddSwapMiddle dotLeft.positivePart dotRight.positivePart
        boundLeft.negativePart boundRight.negativePart).trans
      ((lfkNatAddCongr
          (lfkNatEqOfBeq (dotLeft.positivePart + boundLeft.negativePart)
            (boundLeft.positivePart + dotLeft.negativePart) leftEqWitness)
          (lfkNatEqOfBeq (dotRight.positivePart + boundRight.negativePart)
            (boundRight.positivePart + dotRight.negativePart) rightEqWitness)).trans
        (lfkNatAddSwapMiddle boundLeft.positivePart dotLeft.negativePart
          boundRight.positivePart dotRight.negativePart)))

/-- Scaling by any Nat preserves `<=` (via hand-rolled mul-monotonicity). -/
theorem lfkIntScaleLeMono (multiplier : Nat) {lowerValue higherValue : LfkInt}
    (leWitness : lfkIntLe lowerValue higherValue = true) :
    lfkIntLe (lfkIntScaleByNat multiplier lowerValue)
      (lfkIntScaleByNat multiplier higherValue) = true :=
  lfkNatBleOfLe (multiplier * lowerValue.positivePart + multiplier * higherValue.negativePart)
    (multiplier * higherValue.positivePart + multiplier * lowerValue.negativePart)
    (lfkNatLeCongr
      (Nat.mul_add multiplier lowerValue.positivePart higherValue.negativePart).symm
      (Nat.mul_add multiplier higherValue.positivePart lowerValue.negativePart).symm
      (lfkNatMulLeMulLeft multiplier
        (lfkNatLeOfBle (lowerValue.positivePart + higherValue.negativePart)
          (higherValue.positivePart + lowerValue.negativePart) leWitness)))

/-- Scaling by any Nat preserves cross-sum equality. -/
theorem lfkIntScaleEqMono (multiplier : Nat) {dotValue boundValue : LfkInt}
    (eqWitness : lfkIntEq dotValue boundValue = true) :
    lfkIntEq (lfkIntScaleByNat multiplier dotValue)
      (lfkIntScaleByNat multiplier boundValue) = true :=
  lfkNatBeqOfEq (multiplier * dotValue.positivePart + multiplier * boundValue.negativePart)
    (multiplier * boundValue.positivePart + multiplier * dotValue.negativePart)
    ((Nat.mul_add multiplier dotValue.positivePart boundValue.negativePart).symm.trans
      ((congrArg (fun probe => multiplier * probe)
          (lfkNatEqOfBeq (dotValue.positivePart + boundValue.negativePart)
            (boundValue.positivePart + dotValue.negativePart) eqWitness)).trans
        (Nat.mul_add multiplier boundValue.positivePart dotValue.negativePart)))

/-- A zero coefficient annihilates under multiplication (cross-zero is preserved). -/
theorem lfkIntMulZeroRight (envValue coefficientValue : LfkInt)
    (coefficientZero : lfkIntIsZero coefficientValue = true) :
    lfkIntIsZero (lfkIntMul envValue coefficientValue) = true :=
  lfkNatBeqOfEq
    (envValue.positivePart * coefficientValue.positivePart
      + envValue.negativePart * coefficientValue.negativePart)
    (envValue.positivePart * coefficientValue.negativePart
      + envValue.negativePart * coefficientValue.positivePart)
    ((congrArg
        (fun probe => envValue.positivePart * probe
          + envValue.negativePart * coefficientValue.negativePart)
        (lfkNatEqOfBeq coefficientValue.positivePart coefficientValue.negativePart
          coefficientZero)).trans
      (congrArg
        (fun probe => envValue.positivePart * coefficientValue.negativePart
          + envValue.negativePart * probe)
        (lfkNatEqOfBeq coefficientValue.positivePart coefficientValue.negativePart
          coefficientZero).symm))

/-- Cross-zero is closed under addition. -/
theorem lfkIntAddZeroPreserving {leftValue rightValue : LfkInt}
    (leftZero : lfkIntIsZero leftValue = true) (rightZero : lfkIntIsZero rightValue = true) :
    lfkIntIsZero (lfkIntAdd leftValue rightValue) = true :=
  lfkNatBeqOfEq (leftValue.positivePart + rightValue.positivePart)
    (leftValue.negativePart + rightValue.negativePart)
    (lfkNatAddCongr
      (lfkNatEqOfBeq leftValue.positivePart leftValue.negativePart leftZero)
      (lfkNatEqOfBeq rightValue.positivePart rightValue.negativePart rightZero))

/-! ## Stage 2 — dense coefficient vectors, the truncating dot product -/

/-- A linear term: DENSE coefficient vector, entry `i` multiplies variable `i`.
Vectors shorter than the environment read as zero-extended. -/
abbrev LfkLinearTerm : Type := List LfkInt

/-- PADDING vector addition: when one summand ends, the other's tail is kept.  This
makes `List.nil` a genuine zero vector, so dot-product additivity below needs no
length hypotheses.  Cons-only — no `List.append`. -/
def lfkAddCoefficientVectors : List LfkInt → List LfkInt → List LfkInt
  | List.nil, List.nil => List.nil
  | List.nil, rightHead :: rightTail => rightHead :: rightTail
  | leftHead :: leftTail, List.nil => leftHead :: leftTail
  | leftHead :: leftTail, rightHead :: rightTail =>
      lfkIntAdd leftHead rightHead :: lfkAddCoefficientVectors leftTail rightTail

/-- Scale every coefficient by the Nat multiplier. -/
def lfkScaleCoefficientVector (multiplier : Nat) : List LfkInt → List LfkInt
  | List.nil => List.nil
  | vectorHead :: vectorTail =>
      lfkIntScaleByNat multiplier vectorHead :: lfkScaleCoefficientVector multiplier vectorTail

/-- Negate every coefficient (component swap, entrywise). -/
def lfkNegateCoefficientVector : List LfkInt → List LfkInt
  | List.nil => List.nil
  | vectorHead :: vectorTail =>
      lfkIntNegate vectorHead :: lfkNegateCoefficientVector vectorTail

/-- Structural dot product; TRUNCATES at the shorter list (missing entries are
semantically zero). -/
def lfkDotProduct : List LfkInt → List LfkInt → LfkInt
  | List.nil, List.nil => lfkIntZero
  | List.nil, _coefficientHead :: _coefficientTail => lfkIntZero
  | _envHead :: _envTail, List.nil => lfkIntZero
  | envHead :: envTail, coefficientHead :: coefficientTail =>
      lfkIntAdd (lfkIntMul envHead coefficientHead) (lfkDotProduct envTail coefficientTail)

/-- Dotting against the empty vector is zero, whatever the environment. -/
theorem lfkDotProductNilRight : ∀ (env : List LfkInt),
    lfkDotProduct env List.nil = lfkIntZero
  | List.nil => rfl
  | _envHead :: _envTail => rfl

/-- THE additivity law: padding addition of vectors is addition of dot values —
unconditional, no length hypotheses (padding + truncation agree on the zero
extension). -/
theorem lfkDotProductAddVectors : ∀ (env leftVector rightVector : List LfkInt),
    lfkDotProduct env (lfkAddCoefficientVectors leftVector rightVector)
      = lfkIntAdd (lfkDotProduct env leftVector) (lfkDotProduct env rightVector)
  | List.nil, List.nil, List.nil => rfl
  | List.nil, List.nil, _rightHead :: _rightTail => rfl
  | List.nil, _leftHead :: _leftTail, List.nil => rfl
  | List.nil, _leftHead :: _leftTail, _rightHead :: _rightTail => rfl
  | _envHead :: _envTail, List.nil, List.nil => rfl
  | envHead :: envTail, List.nil, rightHead :: rightTail =>
      (lfkIntZeroAdd (lfkDotProduct (envHead :: envTail) (rightHead :: rightTail))).symm
  | _envHead :: _envTail, _leftHead :: _leftTail, List.nil => rfl
  | envHead :: envTail, leftHead :: leftTail, rightHead :: rightTail =>
      (lfkIntAddCongr (lfkIntMulAddRight envHead leftHead rightHead)
          (lfkDotProductAddVectors envTail leftTail rightTail)).trans
        (lfkIntAddSwapMiddle (lfkIntMul envHead leftHead) (lfkIntMul envHead rightHead)
          (lfkDotProduct envTail leftTail) (lfkDotProduct envTail rightTail))

/-- Dotting a scaled vector scales the dot value. -/
theorem lfkDotProductScaledVector : ∀ (env : List LfkInt) (multiplier : Nat)
    (coefficientVector : List LfkInt),
    lfkDotProduct env (lfkScaleCoefficientVector multiplier coefficientVector)
      = lfkIntScaleByNat multiplier (lfkDotProduct env coefficientVector)
  | List.nil, _multiplier, List.nil => rfl
  | List.nil, _multiplier, _coefficientHead :: _coefficientTail => rfl
  | _envHead :: _envTail, _multiplier, List.nil => rfl
  | envHead :: envTail, multiplier, coefficientHead :: coefficientTail =>
      (lfkIntAddCongr (lfkIntMulScaleRight envHead multiplier coefficientHead)
          (lfkDotProductScaledVector envTail multiplier coefficientTail)).trans
        (lfkIntScaleAddDistrib multiplier (lfkIntMul envHead coefficientHead)
          (lfkDotProduct envTail coefficientTail)).symm

/-- Dotting a negated vector negates the dot value (the entrywise steps are
definitional on (pos,neg) pairs). -/
theorem lfkDotProductNegatedVector : ∀ (env coefficientVector : List LfkInt),
    lfkDotProduct env (lfkNegateCoefficientVector coefficientVector)
      = lfkIntNegate (lfkDotProduct env coefficientVector)
  | List.nil, List.nil => rfl
  | List.nil, _coefficientHead :: _coefficientTail => rfl
  | _envHead :: _envTail, List.nil => rfl
  | envHead :: envTail, coefficientHead :: coefficientTail =>
      congrArg (lfkIntAdd (lfkIntMul envHead (lfkIntNegate coefficientHead)))
        (lfkDotProductNegatedVector envTail coefficientTail)

/-- All coefficients are (cross-)zero. -/
def lfkAllCoefficientsAreZero : List LfkInt → Bool
  | List.nil => true
  | vectorHead :: vectorTail => lfkIntIsZero vectorHead && lfkAllCoefficientsAreZero vectorTail

/-- A cross-zero coefficient vector dots to a cross-zero value against ANY
environment (truncation only drops zero contributions). -/
theorem lfkDotProductZeroCoefficients : ∀ (env coefficientVector : List LfkInt),
    lfkAllCoefficientsAreZero coefficientVector = true →
    lfkIntIsZero (lfkDotProduct env coefficientVector) = true
  | List.nil, List.nil, _trivialWitness => rfl
  | List.nil, _coefficientHead :: _coefficientTail, _allZeroWitness => rfl
  | _envHead :: _envTail, List.nil, _trivialWitness => rfl
  | envHead :: envTail, coefficientHead :: coefficientTail, allZeroWitness =>
      let destructured := lfkBoolAndDestruct (lfkIntIsZero coefficientHead)
        (lfkAllCoefficientsAreZero coefficientTail) allZeroWitness
      lfkIntAddZeroPreserving
        (lfkIntMulZeroRight envHead coefficientHead destructured.left)
        (lfkDotProductZeroCoefficients envTail coefficientTail destructured.right)

/-! ## Stage 2 — constraints and satisfaction -/

/-- Constraint relations: `coefficients . env  REL  bound`. -/
inductive LfkRelation where
  | isGreaterOrEqual : LfkRelation
  | isStrictlyGreater : LfkRelation
  | isEqualTo : LfkRelation

/-- One linear constraint over the dense variable space. -/
structure LfkConstraint where
  coefficients : LfkLinearTerm
  bound : LfkInt
  relation : LfkRelation

/-- Does the environment satisfy the constraint? -/
def lfkSatisfiesConstraint (env : List LfkInt) (constraint : LfkConstraint) : Bool :=
  match constraint.relation with
  | LfkRelation.isGreaterOrEqual =>
      lfkIntLe constraint.bound (lfkDotProduct env constraint.coefficients)
  | LfkRelation.isStrictlyGreater =>
      lfkIntLt constraint.bound (lfkDotProduct env constraint.coefficients)
  | LfkRelation.isEqualTo =>
      lfkIntEq (lfkDotProduct env constraint.coefficients) constraint.bound

/-- Does the environment satisfy every constraint of the system? -/
def lfkSatisfiesSystem (env : List LfkInt) : List LfkConstraint → Bool
  | List.nil => true
  | constraintHead :: constraintTail =>
      lfkSatisfiesConstraint env constraintHead && lfkSatisfiesSystem env constraintTail

/-- The commissioned well-formedness guard: every row's coefficient vector has exactly
the environment's length (the padding/truncating semantics make the soundness theorem
true even without it — see `lfkRefutationSoundUnconditional`). -/
def lfkEnvMatchesLength (env : List LfkInt) : List LfkConstraint → Bool
  | List.nil => true
  | constraintHead :: constraintTail =>
      Nat.beq (List.length constraintHead.coefficients) (List.length env)
        && lfkEnvMatchesLength env constraintTail

/-! ## Stage 3 — row splitting for equalities, the weighted sum, THE CHECKER -/

/-- The forward `>=` row of an equality (same coefficients and bound). -/
def lfkForwardEqualityRow (constraint : LfkConstraint) : LfkConstraint :=
  LfkConstraint.mk constraint.coefficients constraint.bound LfkRelation.isGreaterOrEqual

/-- The flipped `>=` row of an equality: coefficients and bound negated (both are
plain component swaps). -/
def lfkFlipEqualityRow (constraint : LfkConstraint) : LfkConstraint :=
  LfkConstraint.mk (lfkNegateCoefficientVector constraint.coefficients)
    (lfkIntNegate constraint.bound) LfkRelation.isGreaterOrEqual

/-- Row-split every equality into its forward and flipped `>=` rows; inequality rows
pass through.  Certificates align with THIS list — an equality consumes two
consecutive multiplier slots. -/
def lfkExpandSystem : List LfkConstraint → List LfkConstraint
  | List.nil => List.nil
  | constraintHead :: constraintTail =>
      match constraintHead.relation with
      | LfkRelation.isGreaterOrEqual => constraintHead :: lfkExpandSystem constraintTail
      | LfkRelation.isStrictlyGreater => constraintHead :: lfkExpandSystem constraintTail
      | LfkRelation.isEqualTo =>
          lfkForwardEqualityRow constraintHead :: lfkFlipEqualityRow constraintHead
            :: lfkExpandSystem constraintTail

/-- Scaling a relation by a multiplier: zero DEGRADES strictness (`0·(t > b)` would be
the false row `0 > 0`); equalities and non-strict rows are stable. -/
def lfkScaleRelation (multiplier : Nat) : LfkRelation → LfkRelation
  | LfkRelation.isGreaterOrEqual => LfkRelation.isGreaterOrEqual
  | LfkRelation.isEqualTo => LfkRelation.isEqualTo
  | LfkRelation.isStrictlyGreater =>
      match multiplier with
      | Nat.zero => LfkRelation.isGreaterOrEqual
      | Nat.succ _multiplierPred => LfkRelation.isStrictlyGreater

/-- Joining relations under addition: equality is the additive unit, strict absorbs
(the micromega `OpAdd` table, total on this fragment). -/
def lfkJoinRelations : LfkRelation → LfkRelation → LfkRelation
  | LfkRelation.isEqualTo, LfkRelation.isEqualTo => LfkRelation.isEqualTo
  | LfkRelation.isEqualTo, LfkRelation.isGreaterOrEqual => LfkRelation.isGreaterOrEqual
  | LfkRelation.isEqualTo, LfkRelation.isStrictlyGreater => LfkRelation.isStrictlyGreater
  | LfkRelation.isGreaterOrEqual, LfkRelation.isEqualTo => LfkRelation.isGreaterOrEqual
  | LfkRelation.isGreaterOrEqual, LfkRelation.isGreaterOrEqual => LfkRelation.isGreaterOrEqual
  | LfkRelation.isGreaterOrEqual, LfkRelation.isStrictlyGreater => LfkRelation.isStrictlyGreater
  | LfkRelation.isStrictlyGreater, LfkRelation.isEqualTo => LfkRelation.isStrictlyGreater
  | LfkRelation.isStrictlyGreater, LfkRelation.isGreaterOrEqual => LfkRelation.isStrictlyGreater
  | LfkRelation.isStrictlyGreater, LfkRelation.isStrictlyGreater => LfkRelation.isStrictlyGreater

/-- Scale a whole constraint by a Nat multiplier. -/
def lfkScaleConstraint (multiplier : Nat) (constraint : LfkConstraint) : LfkConstraint :=
  LfkConstraint.mk (lfkScaleCoefficientVector multiplier constraint.coefficients)
    (lfkIntScaleByNat multiplier constraint.bound)
    (lfkScaleRelation multiplier constraint.relation)

/-- Add two constraints (padding vector addition, bound addition, relation join). -/
def lfkAddConstraints (leftConstraint rightConstraint : LfkConstraint) : LfkConstraint :=
  LfkConstraint.mk
    (lfkAddCoefficientVectors leftConstraint.coefficients rightConstraint.coefficients)
    (lfkIntAdd leftConstraint.bound rightConstraint.bound)
    (lfkJoinRelations leftConstraint.relation rightConstraint.relation)

/-- The vacuous row `0 >= 0` — the fold's base, satisfied by everything. -/
def lfkTrivialConstraint : LfkConstraint :=
  LfkConstraint.mk List.nil lfkIntZero LfkRelation.isGreaterOrEqual

/-- The trivial row is satisfied by every environment. -/
theorem lfkTrivialSatisfied (env : List LfkInt) :
    lfkSatisfiesConstraint env lfkTrivialConstraint = true :=
  (congrArg (fun probe => lfkIntLe lfkIntZero probe) (lfkDotProductNilRight env)).trans rfl

/-- The Farkas weighted sum: scale each row by its multiplier and add.  A shorter
certificate leaves trailing rows unused; a longer one has its tail ignored. -/
def lfkWeightedSum : List Nat → List LfkConstraint → LfkConstraint
  | List.nil, List.nil => lfkTrivialConstraint
  | List.nil, _constraintHead :: _constraintTail => lfkTrivialConstraint
  | _multiplierHead :: _multiplierTail, List.nil => lfkTrivialConstraint
  | multiplierHead :: multiplierTail, constraintHead :: constraintTail =>
      lfkAddConstraints (lfkScaleConstraint multiplierHead constraintHead)
        (lfkWeightedSum multiplierTail constraintTail)

/-- Does the bound refute the (all-coefficients-zero) summed row?  `>=`: bound must be
strictly positive; `>`: nonnegative suffices; `=`: nonzero (unreachable from the
checker's fold, whose base relation is `>=`, but kept total and proved sound). -/
def lfkBoundViolatesRelation : LfkRelation → LfkInt → Bool
  | LfkRelation.isGreaterOrEqual, boundValue => lfkIntIsPositive boundValue
  | LfkRelation.isStrictlyGreater, boundValue => lfkIntIsNonNegative boundValue
  | LfkRelation.isEqualTo, boundValue => Bool.not (lfkIntIsZero boundValue)

/-- Is the constraint a GROUND contradiction — all coefficients cross-zero and the
residual numeric comparison false? -/
def lfkIsGroundContradiction (constraint : LfkConstraint) : Bool :=
  lfkAllCoefficientsAreZero constraint.coefficients
    && lfkBoundViolatesRelation constraint.relation constraint.bound

/-- THE CHECKER: accept the certificate iff the weighted sum over the row-split
system is a ground contradiction.  O(rows · variables) Nat arithmetic, no search. -/
def lfkCheckRefutation (certificate : List Nat) (system : List LfkConstraint) : Bool :=
  lfkIsGroundContradiction (lfkWeightedSum certificate (lfkExpandSystem system))

/-! ## Stage 4 — soundness -/

/-- Scaling preserves satisfaction: exactly for equalities, monotonely for `>=`, and
for strict rows via the positive-multiplier case (zero degrades to the vacuous
`0 >= 0`, which is where the `+ 1 <= multiplier` headroom is spent). -/
theorem lfkScalePreservesSatisfaction (env : List LfkInt) :
    ∀ (multiplier : Nat) (constraint : LfkConstraint),
      lfkSatisfiesConstraint env constraint = true →
      lfkSatisfiesConstraint env (lfkScaleConstraint multiplier constraint) = true
  | multiplier, LfkConstraint.mk coefficientVector boundValue LfkRelation.isGreaterOrEqual,
      satWitness =>
      (congrArg (fun probe => lfkIntLe (lfkIntScaleByNat multiplier boundValue) probe)
          (lfkDotProductScaledVector env multiplier coefficientVector)).trans
        (lfkIntScaleLeMono multiplier satWitness)
  | multiplier, LfkConstraint.mk coefficientVector boundValue LfkRelation.isEqualTo,
      satWitness =>
      (congrArg (fun probe => lfkIntEq probe (lfkIntScaleByNat multiplier boundValue))
          (lfkDotProductScaledVector env multiplier coefficientVector)).trans
        (lfkIntScaleEqMono multiplier satWitness)
  | Nat.zero, LfkConstraint.mk coefficientVector boundValue LfkRelation.isStrictlyGreater,
      _satWitness =>
      (congrArg (fun probe => lfkIntLe (lfkIntScaleByNat 0 boundValue) probe)
          (lfkDotProductScaledVector env 0 coefficientVector)).trans
        (lfkNatBleOfLe
          (0 * boundValue.positivePart
            + 0 * (lfkDotProduct env coefficientVector).negativePart)
          (0 * (lfkDotProduct env coefficientVector).positivePart
            + 0 * boundValue.negativePart)
          (Nat.le_of_eq
            ((lfkNatBothZeroMulSum boundValue.positivePart
                (lfkDotProduct env coefficientVector).negativePart).trans
              (lfkNatBothZeroMulSum (lfkDotProduct env coefficientVector).positivePart
                boundValue.negativePart).symm)))
  | Nat.succ multiplierPred,
      LfkConstraint.mk coefficientVector boundValue LfkRelation.isStrictlyGreater, satWitness =>
      (congrArg
          (fun probe => lfkIntLt (lfkIntScaleByNat (Nat.succ multiplierPred) boundValue) probe)
          (lfkDotProductScaledVector env (Nat.succ multiplierPred) coefficientVector)).trans
        (lfkNatBleOfLe
          (Nat.succ multiplierPred * boundValue.positivePart
            + Nat.succ multiplierPred * (lfkDotProduct env coefficientVector).negativePart + 1)
          (Nat.succ multiplierPred * (lfkDotProduct env coefficientVector).positivePart
            + Nat.succ multiplierPred * boundValue.negativePart)
          (lfkNatLeCongr
            (congrArg (fun probe => probe + 1)
              (Nat.mul_add (Nat.succ multiplierPred) boundValue.positivePart
                (lfkDotProduct env coefficientVector).negativePart).symm)
            (Nat.mul_add (Nat.succ multiplierPred)
              (lfkDotProduct env coefficientVector).positivePart boundValue.negativePart).symm
            (Nat.le_trans
              (Nat.add_le_add_left (Nat.succ_le_succ (Nat.zero_le multiplierPred))
                (Nat.succ multiplierPred
                  * (boundValue.positivePart
                      + (lfkDotProduct env coefficientVector).negativePart)))
              (lfkNatMulLeMulLeft (Nat.succ multiplierPred)
                (lfkNatLeOfBle
                  (boundValue.positivePart
                    + (lfkDotProduct env coefficientVector).negativePart + 1)
                  ((lfkDotProduct env coefficientVector).positivePart
                    + boundValue.negativePart)
                  satWitness)))))

/-- Adding two satisfied constraints yields a satisfied sum (dot additivity + the
9-case relation-join dispatch). -/
theorem lfkAddPreservesSatisfaction (env : List LfkInt) :
    ∀ (leftConstraint rightConstraint : LfkConstraint),
      lfkSatisfiesConstraint env leftConstraint = true →
      lfkSatisfiesConstraint env rightConstraint = true →
      lfkSatisfiesConstraint env (lfkAddConstraints leftConstraint rightConstraint) = true
  | LfkConstraint.mk leftCoefficients leftBound LfkRelation.isGreaterOrEqual,
      LfkConstraint.mk rightCoefficients rightBound LfkRelation.isGreaterOrEqual,
      leftWitness, rightWitness =>
      (congrArg (fun probe => lfkIntLe (lfkIntAdd leftBound rightBound) probe)
          (lfkDotProductAddVectors env leftCoefficients rightCoefficients)).trans
        (lfkIntAddLeAdd leftWitness rightWitness)
  | LfkConstraint.mk leftCoefficients leftBound LfkRelation.isGreaterOrEqual,
      LfkConstraint.mk rightCoefficients rightBound LfkRelation.isStrictlyGreater,
      leftWitness, rightWitness =>
      (congrArg (fun probe => lfkIntLt (lfkIntAdd leftBound rightBound) probe)
          (lfkDotProductAddVectors env leftCoefficients rightCoefficients)).trans
        (lfkIntAddLeLt leftWitness rightWitness)
  | LfkConstraint.mk leftCoefficients leftBound LfkRelation.isGreaterOrEqual,
      LfkConstraint.mk rightCoefficients rightBound LfkRelation.isEqualTo,
      leftWitness, rightWitness =>
      (congrArg (fun probe => lfkIntLe (lfkIntAdd leftBound rightBound) probe)
          (lfkDotProductAddVectors env leftCoefficients rightCoefficients)).trans
        (lfkIntAddLeAdd leftWitness (lfkIntLeOfEqFlip rightWitness))
  | LfkConstraint.mk leftCoefficients leftBound LfkRelation.isStrictlyGreater,
      LfkConstraint.mk rightCoefficients rightBound LfkRelation.isGreaterOrEqual,
      leftWitness, rightWitness =>
      (congrArg (fun probe => lfkIntLt (lfkIntAdd leftBound rightBound) probe)
          (lfkDotProductAddVectors env leftCoefficients rightCoefficients)).trans
        (lfkIntAddLtLe leftWitness rightWitness)
  | LfkConstraint.mk leftCoefficients leftBound LfkRelation.isStrictlyGreater,
      LfkConstraint.mk rightCoefficients rightBound LfkRelation.isStrictlyGreater,
      leftWitness, rightWitness =>
      (congrArg (fun probe => lfkIntLt (lfkIntAdd leftBound rightBound) probe)
          (lfkDotProductAddVectors env leftCoefficients rightCoefficients)).trans
        (lfkIntAddLtLt leftWitness rightWitness)
  | LfkConstraint.mk leftCoefficients leftBound LfkRelation.isStrictlyGreater,
      LfkConstraint.mk rightCoefficients rightBound LfkRelation.isEqualTo,
      leftWitness, rightWitness =>
      (congrArg (fun probe => lfkIntLt (lfkIntAdd leftBound rightBound) probe)
          (lfkDotProductAddVectors env leftCoefficients rightCoefficients)).trans
        (lfkIntAddLtLe leftWitness (lfkIntLeOfEqFlip rightWitness))
  | LfkConstraint.mk leftCoefficients leftBound LfkRelation.isEqualTo,
      LfkConstraint.mk rightCoefficients rightBound LfkRelation.isGreaterOrEqual,
      leftWitness, rightWitness =>
      (congrArg (fun probe => lfkIntLe (lfkIntAdd leftBound rightBound) probe)
          (lfkDotProductAddVectors env leftCoefficients rightCoefficients)).trans
        (lfkIntAddLeAdd (lfkIntLeOfEqFlip leftWitness) rightWitness)
  | LfkConstraint.mk leftCoefficients leftBound LfkRelation.isEqualTo,
      LfkConstraint.mk rightCoefficients rightBound LfkRelation.isStrictlyGreater,
      leftWitness, rightWitness =>
      (congrArg (fun probe => lfkIntLt (lfkIntAdd leftBound rightBound) probe)
          (lfkDotProductAddVectors env leftCoefficients rightCoefficients)).trans
        (lfkIntAddLeLt (lfkIntLeOfEqFlip leftWitness) rightWitness)
  | LfkConstraint.mk leftCoefficients leftBound LfkRelation.isEqualTo,
      LfkConstraint.mk rightCoefficients rightBound LfkRelation.isEqualTo,
      leftWitness, rightWitness =>
      (congrArg (fun probe => lfkIntEq probe (lfkIntAdd leftBound rightBound))
          (lfkDotProductAddVectors env leftCoefficients rightCoefficients)).trans
        (lfkIntAddEqEq leftWitness rightWitness)

/-- THE WEIGHTED-SUM LEMMA: an environment satisfying every row satisfies the
weighted sum, whatever the certificate. -/
theorem lfkWeightedSumSatisfied : ∀ (certificate : List Nat) (system : List LfkConstraint)
    (env : List LfkInt),
    lfkSatisfiesSystem env system = true →
    lfkSatisfiesConstraint env (lfkWeightedSum certificate system) = true
  | List.nil, List.nil, env, _systemWitness => lfkTrivialSatisfied env
  | List.nil, _constraintHead :: _constraintTail, env, _systemWitness => lfkTrivialSatisfied env
  | _multiplierHead :: _multiplierTail, List.nil, env, _systemWitness => lfkTrivialSatisfied env
  | multiplierHead :: multiplierTail, constraintHead :: constraintTail, env, systemWitness =>
      let destructured := lfkBoolAndDestruct (lfkSatisfiesConstraint env constraintHead)
        (lfkSatisfiesSystem env constraintTail) systemWitness
      lfkAddPreservesSatisfaction env (lfkScaleConstraint multiplierHead constraintHead)
        (lfkWeightedSum multiplierTail constraintTail)
        (lfkScalePreservesSatisfaction env multiplierHead constraintHead destructured.left)
        (lfkWeightedSumSatisfied multiplierTail constraintTail env destructured.right)

/-- Satisfaction transports to the row-split system: an equality yields both its
forward and flipped inequalities. -/
theorem lfkSatisfiesExpandedOfSatisfies (env : List LfkInt) :
    ∀ (system : List LfkConstraint),
      lfkSatisfiesSystem env system = true →
      lfkSatisfiesSystem env (lfkExpandSystem system) = true
  | List.nil, _systemWitness => rfl
  | LfkConstraint.mk headCoefficients headBound LfkRelation.isGreaterOrEqual :: systemTail,
      systemWitness =>
      let destructured := lfkBoolAndDestruct
        (lfkSatisfiesConstraint env
          (LfkConstraint.mk headCoefficients headBound LfkRelation.isGreaterOrEqual))
        (lfkSatisfiesSystem env systemTail) systemWitness
      lfkBoolAndIntro _ _ destructured.left
        (lfkSatisfiesExpandedOfSatisfies env systemTail destructured.right)
  | LfkConstraint.mk headCoefficients headBound LfkRelation.isStrictlyGreater :: systemTail,
      systemWitness =>
      let destructured := lfkBoolAndDestruct
        (lfkSatisfiesConstraint env
          (LfkConstraint.mk headCoefficients headBound LfkRelation.isStrictlyGreater))
        (lfkSatisfiesSystem env systemTail) systemWitness
      lfkBoolAndIntro _ _ destructured.left
        (lfkSatisfiesExpandedOfSatisfies env systemTail destructured.right)
  | LfkConstraint.mk headCoefficients headBound LfkRelation.isEqualTo :: systemTail,
      systemWitness =>
      let destructured := lfkBoolAndDestruct
        (lfkSatisfiesConstraint env
          (LfkConstraint.mk headCoefficients headBound LfkRelation.isEqualTo))
        (lfkSatisfiesSystem env systemTail) systemWitness
      lfkBoolAndIntro _ _ (lfkIntLeOfEqFlip destructured.left)
        (lfkBoolAndIntro _ _
          ((congrArg (fun probe => lfkIntLe (lfkIntNegate headBound) probe)
              (lfkDotProductNegatedVector env headCoefficients)).trans
            (lfkNatBleOfLe
              (headBound.negativePart + (lfkDotProduct env headCoefficients).positivePart)
              ((lfkDotProduct env headCoefficients).negativePart + headBound.positivePart)
              (Nat.le_of_eq
                ((Nat.add_comm headBound.negativePart
                    (lfkDotProduct env headCoefficients).positivePart).trans
                  ((lfkNatEqOfBeq
                      ((lfkDotProduct env headCoefficients).positivePart
                        + headBound.negativePart)
                      (headBound.positivePart
                        + (lfkDotProduct env headCoefficients).negativePart)
                      destructured.left).trans
                    (Nat.add_comm headBound.positivePart
                      (lfkDotProduct env headCoefficients).negativePart))))))
          (lfkSatisfiesExpandedOfSatisfies env systemTail destructured.right))

/-- A satisfied ground contradiction is absurd: the cross-zero dot value squeezes the
residual comparison into `x + 1 <= x`. -/
theorem lfkGroundContradictionRefutes (env : List LfkInt) :
    ∀ (constraint : LfkConstraint),
      lfkIsGroundContradiction constraint = true →
      lfkSatisfiesConstraint env constraint = true → False
  | LfkConstraint.mk coefficientVector boundValue LfkRelation.isGreaterOrEqual,
      contradictionWitness, satWitness =>
      let destructured := lfkBoolAndDestruct (lfkAllCoefficientsAreZero coefficientVector)
        (lfkIntIsPositive boundValue) contradictionWitness
      let dotValue := lfkDotProduct env coefficientVector
      let dotPartsEq : dotValue.positivePart = dotValue.negativePart :=
        lfkNatEqOfBeq dotValue.positivePart dotValue.negativePart
          (lfkDotProductZeroCoefficients env coefficientVector destructured.left)
      let positiveWitness : Nat.le (boundValue.negativePart + 1) boundValue.positivePart :=
        lfkNatLeOfBle (boundValue.negativePart + 1) boundValue.positivePart destructured.right
      let satisfiedLe : Nat.le (boundValue.positivePart + dotValue.negativePart)
          (dotValue.positivePart + boundValue.negativePart) :=
        lfkNatLeOfBle (boundValue.positivePart + dotValue.negativePart)
          (dotValue.positivePart + boundValue.negativePart) satWitness
      lfkNatSuccLeSelfFalse (boundValue.negativePart + dotValue.negativePart)
        (Nat.le_trans
          (Nat.le_of_eq (lfkNatAddOneShiftOut boundValue.negativePart dotValue.negativePart).symm)
          (Nat.le_trans
            (Nat.le_trans (Nat.add_le_add_right positiveWitness dotValue.negativePart)
              satisfiedLe)
            (Nat.le_of_eq
              ((congrArg (fun probe => probe + boundValue.negativePart) dotPartsEq).trans
                (Nat.add_comm dotValue.negativePart boundValue.negativePart)))))
  | LfkConstraint.mk coefficientVector boundValue LfkRelation.isStrictlyGreater,
      contradictionWitness, satWitness =>
      let destructured := lfkBoolAndDestruct (lfkAllCoefficientsAreZero coefficientVector)
        (lfkIntIsNonNegative boundValue) contradictionWitness
      let dotValue := lfkDotProduct env coefficientVector
      let dotPartsEq : dotValue.positivePart = dotValue.negativePart :=
        lfkNatEqOfBeq dotValue.positivePart dotValue.negativePart
          (lfkDotProductZeroCoefficients env coefficientVector destructured.left)
      let nonNegativeWitness : Nat.le boundValue.negativePart boundValue.positivePart :=
        lfkNatLeOfBle boundValue.negativePart boundValue.positivePart destructured.right
      let satisfiedLt : Nat.le (boundValue.positivePart + dotValue.negativePart + 1)
          (dotValue.positivePart + boundValue.negativePart) :=
        lfkNatLeOfBle (boundValue.positivePart + dotValue.negativePart + 1)
          (dotValue.positivePart + boundValue.negativePart) satWitness
      lfkNatSuccLeSelfFalse (boundValue.negativePart + dotValue.negativePart)
        (Nat.le_trans
          (Nat.succ_le_succ (Nat.add_le_add_right nonNegativeWitness dotValue.negativePart))
          (Nat.le_trans satisfiedLt
            (Nat.le_of_eq
              ((congrArg (fun probe => probe + boundValue.negativePart) dotPartsEq).trans
                (Nat.add_comm dotValue.negativePart boundValue.negativePart)))))
  | LfkConstraint.mk coefficientVector boundValue LfkRelation.isEqualTo,
      contradictionWitness, satWitness =>
      let destructured := lfkBoolAndDestruct (lfkAllCoefficientsAreZero coefficientVector)
        (Bool.not (lfkIntIsZero boundValue)) contradictionWitness
      let dotValue := lfkDotProduct env coefficientVector
      let dotPartsEq : dotValue.positivePart = dotValue.negativePart :=
        lfkNatEqOfBeq dotValue.positivePart dotValue.negativePart
          (lfkDotProductZeroCoefficients env coefficientVector destructured.left)
      let satisfiedEq : dotValue.positivePart + boundValue.negativePart
          = boundValue.positivePart + dotValue.negativePart :=
        lfkNatEqOfBeq (dotValue.positivePart + boundValue.negativePart)
          (boundValue.positivePart + dotValue.negativePart) satWitness
      let boundPartsEq : boundValue.negativePart = boundValue.positivePart :=
        lfkNatAddLeftCancel dotValue.negativePart boundValue.negativePart boundValue.positivePart
          ((Nat.add_comm dotValue.negativePart boundValue.negativePart).trans
            (((Nat.add_comm boundValue.negativePart dotValue.negativePart).trans
                ((congrArg (fun probe => probe + boundValue.negativePart) dotPartsEq.symm).trans
                  satisfiedEq)).trans
              (Nat.add_comm boundValue.positivePart dotValue.negativePart)))
      Bool.noConfusion
        ((lfkBoolNotTrueImpliesFalse (lfkIntIsZero boundValue) destructured.right).symm.trans
          (lfkNatBeqOfEq boundValue.positivePart boundValue.negativePart boundPartsEq.symm))

/-- HEADLINE (unconditional form): an accepted certificate refutes EVERY environment —
no length hypothesis needed, thanks to the padding/truncating vector semantics. -/
theorem lfkRefutationSoundUnconditional (certificate : List Nat) (system : List LfkConstraint)
    (checkWitness : lfkCheckRefutation certificate system = true) (env : List LfkInt)
    (systemWitness : lfkSatisfiesSystem env system = true) : False :=
  lfkGroundContradictionRefutes env (lfkWeightedSum certificate (lfkExpandSystem system))
    checkWitness
    (lfkWeightedSumSatisfied certificate (lfkExpandSystem system) env
      (lfkSatisfiesExpandedOfSatisfies env system systemWitness))

/-- HEADLINE (commissioned form): accepted certificate + length-matching environment
+ satisfaction is absurd. -/
theorem lfkRefutationSound (certificate : List Nat) (system : List LfkConstraint)
    (checkWitness : lfkCheckRefutation certificate system = true) :
    ∀ (env : List LfkInt), lfkEnvMatchesLength env system = true →
      lfkSatisfiesSystem env system = true → False :=
  fun env _lengthWitness systemWitness =>
    lfkRefutationSoundUnconditional certificate system checkWitness env systemWitness

/-! ## Stage 5 — the honest walls (owner-false Props) -/

/-- Scale every BOUND by the denominator, leaving coefficients alone: the integer
environment `env` satisfies the scaled system exactly when the rational vector
`env / denominator` satisfies the original (all three relations are preserved under
multiplication by a positive integer). -/
def lfkScaleBoundsForDenominator (denominator : Nat) : List LfkConstraint → List LfkConstraint
  | List.nil => List.nil
  | constraintHead :: constraintTail =>
      LfkConstraint.mk constraintHead.coefficients
          (lfkIntScaleByNat denominator constraintHead.bound) constraintHead.relation
        :: lfkScaleBoundsForDenominator denominator constraintTail

/-- COMPLETENESS WALL (owner-false, NOT proven here): every RATIONALLY infeasible
system has an accepted Farkas certificate.  Rational infeasibility is encoded
integer-only: no positive denominator `d` admits an integer environment for the
`d`-scaled-bounds system (`env` then denotes the rational point `env / d`).  True
classically (Farkas/Motzkin transposition); constructively REACHABLE — the route is
Fourier–Motzkin elimination with certificate composition, fuel = number of variables,
one variable eliminated per round, each derived row remembering its two parent rows so
the final ground contradiction unwinds into multipliers for the original rows.  This
is a genuine future brick, NOT Dickson-walled: FM recursion is structural on the
variable count.  Owner: `fxDissatArith_hasFarkasCompleteness := false`. -/
def lfkFarkasCompletenessStatement : Prop :=
  ∀ (system : List LfkConstraint),
    (∀ (denominatorPred : Nat) (env : List LfkInt),
        lfkSatisfiesSystem env
          (lfkScaleBoundsForDenominator (denominatorPred + 1) system) = true → False) →
    ∃ (certificate : List Nat), lfkCheckRefutation certificate system = true

/-- PRESBURGER WALL (owner-false, NOT attempted): full decidability of integer
satisfiability for these systems (Cooper / Omega-test quantifier elimination).  Farkas
certificates alone CANNOT close this: `2x = 1` is integer-unsatisfiable but rationally
feasible, hence certificate-free — the standard escape hatches are cutting planes /
bound tightening (`INT_TIGHT_UB/LB`) on top of the summing engine.  A SEPARATE future
brick.  Owner: `fxDissatArith_hasPresburgerDecision := false`. -/
def lfkPresburgerDecisionStatement : Prop :=
  ∀ (system : List LfkConstraint),
    Or (∃ (env : List LfkInt), lfkSatisfiesSystem env system = true)
      (∀ (env : List LfkInt), lfkSatisfiesSystem env system = true → False)

/-- DECIDED marker: the Farkas-certificate refutation engine (integer kit, dense
constraint semantics, row-split checker, and the soundness chain through
`lfkRefutationSound`) is fully proven, zero-axiom, finder-free. -/
def fxDissatArith_hasFarkasCertificate : Bool := true

/-- Owner flag for `lfkFarkasCompletenessStatement` — NOT proven (future FM brick). -/
def fxDissatArith_hasFarkasCompleteness : Bool := false

/-- Owner flag for `lfkPresburgerDecisionStatement` — NOT proven (future Cooper
brick). -/
def fxDissatArith_hasPresburgerDecision : Bool := false

/-! ## Smokes (Bool outputs only; FALSE cases included; kernel-checked `rfl` pins) -/

/-- Smoke fixture: `x >= 1` and `-x >= 0` — rationally infeasible. -/
def lfkSmokeContradictorySystem : List LfkConstraint :=
  [LfkConstraint.mk [LfkInt.mk 1 0] (LfkInt.mk 1 0) LfkRelation.isGreaterOrEqual,
   LfkConstraint.mk [LfkInt.mk 0 1] lfkIntZero LfkRelation.isGreaterOrEqual]

/-- Smoke fixture: `x >= 0`, `y >= 0`, `x + y >= -5` — satisfiable (e.g. by 0, 0). -/
def lfkSmokeSatisfiableTriple : List LfkConstraint :=
  [LfkConstraint.mk [LfkInt.mk 1 0, lfkIntZero] lfkIntZero LfkRelation.isGreaterOrEqual,
   LfkConstraint.mk [lfkIntZero, LfkInt.mk 1 0] lfkIntZero LfkRelation.isGreaterOrEqual,
   LfkConstraint.mk [LfkInt.mk 1 0, LfkInt.mk 1 0] (LfkInt.mk 0 5)
     LfkRelation.isGreaterOrEqual]

/-- Smoke fixture: `x > 0` and `-x >= 0` — the contradiction lives in strictness. -/
def lfkSmokeStrictSystem : List LfkConstraint :=
  [LfkConstraint.mk [LfkInt.mk 1 0] lfkIntZero LfkRelation.isStrictlyGreater,
   LfkConstraint.mk [LfkInt.mk 0 1] lfkIntZero LfkRelation.isGreaterOrEqual]

/-- Smoke fixture: `x = 3` and `-x >= -2` (i.e. `x <= 2`).  In the EXPANDED view the
equality occupies certificate slots 0 (forward `x >= 3`) and 1 (flipped `-x >= -3`);
slot 2 is the inequality. -/
def lfkSmokeEqualitySystem : List LfkConstraint :=
  [LfkConstraint.mk [LfkInt.mk 1 0] (LfkInt.mk 3 0) LfkRelation.isEqualTo,
   LfkConstraint.mk [LfkInt.mk 0 1] (LfkInt.mk 0 2) LfkRelation.isGreaterOrEqual]

/-- Smoke fixture: `x >= 1`, `y >= 2` — satisfiable. -/
def lfkSmokeSatisfiablePair : List LfkConstraint :=
  [LfkConstraint.mk [LfkInt.mk 1 0, lfkIntZero] (LfkInt.mk 1 0) LfkRelation.isGreaterOrEqual,
   LfkConstraint.mk [lfkIntZero, LfkInt.mk 1 0] (LfkInt.mk 2 0) LfkRelation.isGreaterOrEqual]

/-- Smoke fixture: the witnessing environment `(x, y) = (1, 2)`. -/
def lfkSmokeSatisfyingEnv : List LfkInt := [LfkInt.mk 1 0, LfkInt.mk 2 0]

/-- Kernel pin: multipliers `[1, 1]` refute `x >= 1, -x >= 0`. -/
theorem lfkSmokeContradictoryPin :
    lfkCheckRefutation [1, 1] lfkSmokeContradictorySystem = true := rfl

/-- Kernel pin (FALSE case): the bogus certificate `[1, 0]` is REJECTED. -/
theorem lfkSmokeBogusCertificatePin :
    lfkCheckRefutation [1, 0] lfkSmokeContradictorySystem = false := rfl

/-- Kernel pin (FALSE case): no multiplier choice `[1, 1, 1]` refutes the satisfiable
triple — coefficients do not cancel. -/
theorem lfkSmokeSatisfiableTriplePin :
    lfkCheckRefutation [1, 1, 1] lfkSmokeSatisfiableTriple = false := rfl

/-- Kernel pin: strictness threads — `x > 0, -x >= 0` is refuted with a ZERO residual
bound (the joined relation is strict, so nonnegativity of the bound suffices). -/
theorem lfkSmokeStrictPin :
    lfkCheckRefutation [1, 1] lfkSmokeStrictSystem = true := rfl

/-- Kernel pin: the equality route — forward slot weighted 1, flipped slot 0,
inequality slot 1. -/
theorem lfkSmokeEqualityPin :
    lfkCheckRefutation [1, 0, 1] lfkSmokeEqualitySystem = true := rfl

/-- Kernel pin (FALSE case): the empty system admits no refutation. -/
theorem lfkSmokeEmptyPin :
    lfkCheckRefutation List.nil List.nil = false := rfl

/-- Kernel pin: the satisfiable pair really is satisfied by `(1, 2)`. -/
theorem lfkSmokeSatisfyingEnvPin :
    lfkSatisfiesSystem lfkSmokeSatisfyingEnv lfkSmokeSatisfiablePair = true := rfl

-- Refutation of x >= 1, -x >= 0 by [1,1]. Expect: true
#eval lfkCheckRefutation [1, 1] lfkSmokeContradictorySystem
-- FALSE case: bogus certificate [1,0] rejected. Expect: false
#eval lfkCheckRefutation [1, 0] lfkSmokeContradictorySystem
-- FALSE case: satisfiable triple not refutable by [1,1,1]. Expect: false
#eval lfkCheckRefutation [1, 1, 1] lfkSmokeSatisfiableTriple
-- Strictness threads through the join. Expect: true
#eval lfkCheckRefutation [1, 1] lfkSmokeStrictSystem
-- Equality via two expanded slots. Expect: true
#eval lfkCheckRefutation [1, 0, 1] lfkSmokeEqualitySystem
-- FALSE case: empty system, empty certificate. Expect: false
#eval lfkCheckRefutation List.nil List.nil
-- Satisfiable sanity: (1,2) satisfies x >= 1, y >= 2. Expect: true
#eval lfkSatisfiesSystem lfkSmokeSatisfyingEnv lfkSmokeSatisfiablePair

end FX1Poly.ComputerAlgebra
