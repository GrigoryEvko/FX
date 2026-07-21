import FX1Poly.ComputerAlgebra.Decision.LinearFarkasCertificate

/-! # Fourier–Motzkin elimination with certificate composition

A verified FINDER built on the verified CHECKER of `LinearFarkasCertificate`:
Fourier–Motzkin elimination over the row-split system in which every derived row
carries its Nat-multiplier provenance over the original expanded rows, so that a
ground contradiction discovered by elimination hands the checker an
already-composed refutation certificate.  The literature offers verified FM finders
that produce no certificates (Nipkow's AFP `LinearQuantifierElim`) and verified
linear-arithmetic checkers whose finder is left unverified (Besson's micromega) or
whose completeness is only meta-level (HOL Light's `REAL_LINEAR_PROVER`); a verified
finder that emits a checker-accepted certificate is the combination pursued here.

## The certificate-threading engine

A certified row (`LfmCertifiedRow`) is a constraint together with a provenance
vector; the invariant `lfmRowMatchesProvenance` states that the constraint IS the
provenance-weighted sum of the expanded system.  Seeds take unit provenances
(`lfmUnitProvenance`), so their invariant is definitional.  One elimination round
(`lfmEliminationRound`) buckets rows by the sign of the target coefficient
(cross-sum tests; rows too short fall in the zero bucket, where the coefficient
reads as the genuine zero), passes zero rows through untouched, and cross-combines
each positive row with each negative row, scaling by the opposite coefficient
magnitudes.  Magnitudes are extracted with `lfmNatDelta`, a hand-rolled structural
difference with the recovery spec `small + delta = big`, never `Nat.sub`.

The invariant threads through combination by the bilinearity theorems, proved as
structural equalities of `LfkConstraint` (coefficients, bound, and relation):

  * `lfmWeightedSumOfScaledCertificate` — weighting by a certificate scaled by a
    multiplier equals scaling the weighted sum by that multiplier;
  * `lfmWeightedSumOfAddedCertificates` — weighting by a sum of certificates equals
    adding the two weighted sums

over the padding Nat-vector algebra `lfmProvenanceAdd` and `lfmProvenanceScale`.  The
relation components hold because `lfkScaleRelation` distributes over the join and
over multiplier addition and multiplication (finite case analysis, `rfl` except one
`Nat.zero_mul` transport).  Trivial-row absorption `add trivial X = X` needs
`X.relation` to be an inequality, supplied by `lfmWeightedSumRelationIsInequality`:
the weighted-sum fold's relation is always an inequality, its base being `>=`.

## What is proven

  * `lfmFoundContradictionCertifies` — the composition theorem: whenever the driver
    (`lfmFindRefutationCertificate`: seed, eliminate every variable, scan for a
    ground-contradictory row) returns a certificate, `lfkCheckRefutation` accepts it
    against the original system.  Finder output needs no post-hoc reconstruction.
  * `lfmFoundCertificateRefutes` — composed with the checker's soundness: a found
    certificate refutes every integer environment.
  * `lfmRoundPreservesSatisfaction` and `lfmEliminateFromIndexPreservesSatisfaction`
    — forward preservation: any environment satisfying the input rows satisfies every
    derived row, so elimination never invents constraints.
  * `lfmRoundEliminatesTargetVariable` — every output row of a round has cross-zero
    coefficient at the eliminated position (scaled-opposite-entries cancellation
    through the witnessed deltas).
  * `lfmFinalRowsAreGround` — the grounding theorem: after `lfmMaxCoefficientLength`
    rounds every surviving row is variable-free, so the final scan is a genuine
    ground-row scan.  Rounds establish zero at the target index, preserve zero at
    previously eliminated indices, preserve the length bound, and entries beyond the
    length bound read as zero.
  * `lfmOnePairExtensionCore` — the backward-direction step: the pure-arithmetic
    interval-nonemptiness core for one positive/negative pair with weak relations,
    where the scaled witness `v = cN·(boundP − restP)` satisfies both parents'
    `(aP·cN)`-scaled rows whenever the combined row is satisfied.  This is the
    algebra the inequality-guarded extension iterates.
  * End-of-file smokes: the checker module's unsat fixtures (plain, strict,
    equality) and a two-variable chain run finder → checker with the composed
    certificates accepted (kernel `rfl` pins and `#eval`s); satisfiable systems and a
    relaxed chain scan clean.

## The uninhabited round-extension Prop

`lfmRoundExtensionStatement` is the backward/extension claim: if some integer
environment satisfies a round's OUTPUT at a positive denominator (in the checker's
`lfkScaleBoundsForDenominator` encoding of a rational point), then some integer
environment satisfies the round's INPUT at a positive denominator, over arbitrary
certified rows.  This file states the Prop but leaves it uninhabited, so
completeness (`lfkFarkasCompletenessStatement`) is not proven here
(`fxDissatArith_hasFourierMotzkinCompleteness = false`).

As stated (unguarded) the Prop is too strong.  It is refuted in
`FourierMotzkinExtension` on the fixture `[x = 0, x >= 1]`: an equality row is at
once a lower and an upper bound on the pivot, so it lands in a single sign bucket
and its opposite half is dropped, letting a round emit an empty (satisfiable) system
from an unsatisfiable input.  Under the extra hypothesis that every input row is an
inequality (`lfmRelationIsInequality`) the extension holds, and because the pipeline
maintains that invariant — seeds are weighted sums, every round preserves
inequality-ness — `FourierMotzkinExtension` recovers Farkas completeness from the
guarded form.  The one-pair interval algebra it iterates is `lfmOnePairExtensionCore`,
proven below.

## Zero-axiom discipline

Init only plus the checker import.  Structural recursion throughout (the driver's
fuel is the max coefficient length); no `WellFounded.fix`.  No `propext`,
`Quot.sound`, `Classical.choice`, `sorry`, `native_decide`, `funext`, `omega`, no
`decide` on `Prop`, no catch-all match arms, no `List.append`, no `Int`, no
`Nat.sub/mod/div/min/max` (witnessed `lfmNatDelta` differences instead; the
two-branch maximum is the hand-rolled `lfmNatGreater` over `cond`).  Nat facts are
restricted to the checker's probed-clean core; new AC identities are hand-proved
(`lfmNatAddMulDistrib`).  The per-declaration zero-axiom gate lives in the
`FX1PolyAudit` twin. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace FX1Poly.ComputerAlgebra

/-! ## Nat kit extensions — right distributivity, witnessed differences, ble flips -/

/-- Right distributivity `(a + b) * c = a * c + b * c`, hand-rolled from the
probed-clean `Nat.mul_comm`/`Nat.mul_add` (the library `Nat.add_mul` is banned by
the leak ledger). -/
theorem lfmNatAddMulDistrib (leftAddend rightAddend factor : Nat) :
    (leftAddend + rightAddend) * factor = leftAddend * factor + rightAddend * factor :=
  (Nat.mul_comm (leftAddend + rightAddend) factor).trans
    ((Nat.mul_add factor leftAddend rightAddend).trans
      (lfkNatAddCongr (Nat.mul_comm factor leftAddend) (Nat.mul_comm factor rightAddend)))

/-- One is a left identity for multiplication (via `Nat.succ_mul` + `Nat.zero_mul`;
`Nat.one_mul` itself is avoided, matching the sibling's restricted core). -/
theorem lfmNatOneMul (value : Nat) : 1 * value = value :=
  (Nat.succ_mul 0 value).trans
    ((congrArg (fun probe => probe + value) (Nat.zero_mul value)).trans (Nat.zero_add value))

/-- Helper for the witnessed difference, recursing STRUCTURALLY ON THE SUBTRAHEND
(first argument) so that `lfmNatDeltaFromSmall 0 big` reduces for abstract `big`. -/
def lfmNatDeltaFromSmall : Nat → Nat → Nat
  | Nat.zero, bigValue => bigValue
  | Nat.succ _smallPred, Nat.zero => Nat.zero
  | Nat.succ smallPred, Nat.succ bigPred => lfmNatDeltaFromSmall smallPred bigPred

/-- The witnessed difference: `lfmNatDelta big small` is `big - small` computed by
double structural recursion — NEVER `Nat.sub`, and used only through the recovery
spec below. -/
def lfmNatDelta (bigValue smallValue : Nat) : Nat :=
  lfmNatDeltaFromSmall smallValue bigValue

/-- THE recovery spec: when `small <= big`, adding the witnessed difference back
recovers `big`. -/
theorem lfmNatDeltaRecovers : ∀ (bigValue smallValue : Nat),
    Nat.ble smallValue bigValue = true →
    smallValue + lfmNatDelta bigValue smallValue = bigValue
  | bigValue, Nat.zero, _trivialWitness => Nat.zero_add bigValue
  | Nat.zero, Nat.succ _smallPred, contradictoryWitness => Bool.noConfusion contradictoryWitness
  | Nat.succ bigPred, Nat.succ smallPred, tailWitness =>
      (Nat.succ_add smallPred (lfmNatDelta bigPred smallPred)).trans
        (congrArg Nat.succ (lfmNatDeltaRecovers bigPred smallPred tailWitness))

/-- Weaken a strict cross-sum comparison (`small + 1 <= big`) to its weak form. -/
theorem lfmNatBleWeakenFromSucc (smallValue bigValue : Nat)
    (strictWitness : Nat.ble (smallValue + 1) bigValue = true) :
    Nat.ble smallValue bigValue = true :=
  lfkNatBleOfLe smallValue bigValue
    (Nat.le_trans (Nat.le_succ smallValue)
      (lfkNatLeOfBle (smallValue + 1) bigValue strictWitness))

/-- A failed `ble` flips into the strict reverse comparison (double structural
recursion — no order-lemma imports). -/
theorem lfmNatBleFalseFlipStrict : ∀ (leftValue rightValue : Nat),
    Nat.ble leftValue rightValue = false → Nat.ble (rightValue + 1) leftValue = true
  | Nat.zero, _rightValue, contradictoryWitness => Bool.noConfusion contradictoryWitness
  | Nat.succ _leftPred, Nat.zero, _falseWitness => rfl
  | Nat.succ leftPred, Nat.succ rightPred, falseWitness =>
      lfmNatBleFalseFlipStrict leftPred rightPred falseWitness

/-- Two opposite `ble`s force equality (double structural recursion). -/
theorem lfmNatEqOfBleBle : ∀ (leftValue rightValue : Nat),
    Nat.ble leftValue rightValue = true → Nat.ble rightValue leftValue = true →
    leftValue = rightValue
  | Nat.zero, Nat.zero, _forwardWitness, _backwardWitness => rfl
  | Nat.zero, Nat.succ _rightPred, _forwardWitness, backwardWitness =>
      Bool.noConfusion backwardWitness
  | Nat.succ _leftPred, Nat.zero, forwardWitness, _backwardWitness =>
      Bool.noConfusion forwardWitness
  | Nat.succ leftPred, Nat.succ rightPred, forwardWitness, backwardWitness =>
      congrArg Nat.succ (lfmNatEqOfBleBle leftPred rightPred forwardWitness backwardWitness)

/-- Right cancellation of addition inside `le` (structural on the shared addend;
`Nat.le_of_add_le_add_left` is on the confirmed-dirty list, so hand-rolled). -/
theorem lfmNatLeOfAddLeAddRight : ∀ (sharedAddend leftValue rightValue : Nat),
    Nat.le (leftValue + sharedAddend) (rightValue + sharedAddend) →
    Nat.le leftValue rightValue
  | Nat.zero, _leftValue, _rightValue, boundWitness => boundWitness
  | Nat.succ sharedPred, leftValue, rightValue, boundWitness =>
      lfmNatLeOfAddLeAddRight sharedPred leftValue rightValue
        (Nat.le_of_succ_le_succ boundWitness)

/-- Every Bool is `true` or `false` — the case-split hub for `cond`-based
definitions (avoids match-equation binders entirely). -/
theorem lfmBoolCases : ∀ (flag : Bool), Or (flag = true) (flag = false)
  | true => Or.inl rfl
  | false => Or.inr rfl

/-- `cond` distributes over `Nat.succ` in both branches. -/
theorem lfmCondSucc : ∀ (branchFlag : Bool) (trueValue falseValue : Nat),
    cond branchFlag (Nat.succ trueValue) (Nat.succ falseValue)
      = Nat.succ (cond branchFlag trueValue falseValue)
  | true, _trueValue, _falseValue => rfl
  | false, _trueValue, _falseValue => rfl

/-! ## The two-branch maximum (`Nat.max` is banned; this is `cond` over `ble`) -/

/-- The larger of two Nats. -/
def lfmNatGreater (leftValue rightValue : Nat) : Nat :=
  cond (Nat.ble leftValue rightValue) rightValue leftValue

/-- `lfmNatGreater` commutes with double `succ`. -/
theorem lfmNatGreaterSucc (leftValue rightValue : Nat) :
    lfmNatGreater (Nat.succ leftValue) (Nat.succ rightValue)
      = Nat.succ (lfmNatGreater leftValue rightValue) :=
  lfmCondSucc (Nat.ble leftValue rightValue) rightValue leftValue

/-- The left operand is below the greater. -/
theorem lfmNatLeGreaterLeft (leftValue rightValue : Nat) :
    Nat.le leftValue (lfmNatGreater leftValue rightValue) :=
  match lfmBoolCases (Nat.ble leftValue rightValue) with
  | Or.inl bleTrue =>
      Nat.le_trans (lfkNatLeOfBle leftValue rightValue bleTrue)
        (Nat.le_of_eq
          ((congrArg (fun probe => cond probe rightValue leftValue) bleTrue).symm))
  | Or.inr bleFalse =>
      Nat.le_of_eq ((congrArg (fun probe => cond probe rightValue leftValue) bleFalse).symm)

/-- The right operand is below the greater. -/
theorem lfmNatLeGreaterRight (leftValue rightValue : Nat) :
    Nat.le rightValue (lfmNatGreater leftValue rightValue) :=
  match lfmBoolCases (Nat.ble leftValue rightValue) with
  | Or.inl bleTrue =>
      Nat.le_of_eq ((congrArg (fun probe => cond probe rightValue leftValue) bleTrue).symm)
  | Or.inr bleFalse =>
      Nat.le_trans
        (Nat.le_trans (Nat.le_succ rightValue)
          (lfkNatLeOfBle (rightValue + 1) leftValue
            (lfmNatBleFalseFlipStrict leftValue rightValue bleFalse)))
        (Nat.le_of_eq ((congrArg (fun probe => cond probe rightValue leftValue) bleFalse).symm))

/-- The greater is below any common upper bound. -/
theorem lfmNatGreaterLeOfBoth (leftValue rightValue boundValue : Nat)
    (leftBound : Nat.le leftValue boundValue) (rightBound : Nat.le rightValue boundValue) :
    Nat.le (lfmNatGreater leftValue rightValue) boundValue :=
  match lfmBoolCases (Nat.ble leftValue rightValue) with
  | Or.inl bleTrue =>
      Nat.le_trans
        (Nat.le_of_eq (congrArg (fun probe => cond probe rightValue leftValue) bleTrue))
        rightBound
  | Or.inr bleFalse =>
      Nat.le_trans
        (Nat.le_of_eq (congrArg (fun probe => cond probe rightValue leftValue) bleFalse))
        leftBound

/-! ## LfkInt kit extensions — scale composition, multiplier distribution, zeros -/

/-- Scaling composes with multiplier multiplication (componentwise
`lfkNatMulAssoc`). -/
theorem lfmIntScaleCompose (outerMultiplier innerMultiplier : Nat) (value : LfkInt) :
    lfkIntScaleByNat (outerMultiplier * innerMultiplier) value
      = lfkIntScaleByNat outerMultiplier (lfkIntScaleByNat innerMultiplier value) :=
  lfkIntMkCongr (lfkNatMulAssoc outerMultiplier innerMultiplier value.positivePart)
    (lfkNatMulAssoc outerMultiplier innerMultiplier value.negativePart)

/-- Scaling distributes over multiplier addition (componentwise
`lfmNatAddMulDistrib`). -/
theorem lfmIntScaleAddMultipliers (leftMultiplier rightMultiplier : Nat) (value : LfkInt) :
    lfkIntScaleByNat (leftMultiplier + rightMultiplier) value
      = lfkIntAdd (lfkIntScaleByNat leftMultiplier value)
          (lfkIntScaleByNat rightMultiplier value) :=
  lfkIntMkCongr (lfmNatAddMulDistrib leftMultiplier rightMultiplier value.positivePart)
    (lfmNatAddMulDistrib leftMultiplier rightMultiplier value.negativePart)

/-- Scaling preserves cross-zero. -/
theorem lfmIntScalePreservesZero (multiplier : Nat) {value : LfkInt}
    (zeroWitness : lfkIntIsZero value = true) :
    lfkIntIsZero (lfkIntScaleByNat multiplier value) = true :=
  lfkNatBeqOfEq (multiplier * value.positivePart) (multiplier * value.negativePart)
    (congrArg (fun probe => multiplier * probe)
      (lfkNatEqOfBeq value.positivePart value.negativePart zeroWitness))

/-- A value plus its negation is cross-zero. -/
theorem lfmIntAddNegateSelfZero (value : LfkInt) :
    lfkIntIsZero (lfkIntAdd (lfkIntNegate value) value) = true :=
  lfkNatBeqOfEq (value.negativePart + value.positivePart)
    (value.positivePart + value.negativePart)
    (Nat.add_comm value.negativePart value.positivePart)

/-- Cross-sum order is reflexive. -/
theorem lfmIntLeRefl (value : LfkInt) : lfkIntLe value value = true :=
  lfkNatBleOfLe (value.positivePart + value.negativePart)
    (value.positivePart + value.negativePart)
    (Nat.le_refl (value.positivePart + value.negativePart))

/-- Adding a cross-zero part on the right does not decrease a value. -/
theorem lfmIntLeSelfPlusZero (value zeroPart : LfkInt)
    (zeroWitness : lfkIntIsZero zeroPart = true) :
    lfkIntLe value (lfkIntAdd value zeroPart) = true :=
  lfkNatBleOfLe (value.positivePart + (value.negativePart + zeroPart.negativePart))
    ((value.positivePart + zeroPart.positivePart) + value.negativePart)
    (Nat.le_of_eq
      ((Nat.add_assoc value.positivePart value.negativePart zeroPart.negativePart).symm.trans
        ((congrArg (fun probe => value.positivePart + value.negativePart + probe)
            (lfkNatEqOfBeq zeroPart.positivePart zeroPart.negativePart zeroWitness).symm).trans
          ((Nat.add_assoc value.positivePart value.negativePart zeroPart.positivePart).trans
            ((congrArg (fun probe => value.positivePart + probe)
                (Nat.add_comm value.negativePart zeroPart.positivePart)).trans
              (Nat.add_assoc value.positivePart zeroPart.positivePart
                value.negativePart).symm)))))

/-- Dropping a cross-zero addend from the right of an upper bound. -/
theorem lfmIntLePlusZeroDrop (leftValue rightValue zeroPart : LfkInt)
    (zeroWitness : lfkIntIsZero zeroPart = true)
    (boundWitness : lfkIntLe leftValue (lfkIntAdd rightValue zeroPart) = true) :
    lfkIntLe leftValue rightValue = true :=
  lfkNatBleOfLe (leftValue.positivePart + rightValue.negativePart)
    (rightValue.positivePart + leftValue.negativePart)
    (lfmNatLeOfAddLeAddRight zeroPart.negativePart
      (leftValue.positivePart + rightValue.negativePart)
      (rightValue.positivePart + leftValue.negativePart)
      (lfkNatLeCongr
        (Nat.add_assoc leftValue.positivePart rightValue.negativePart zeroPart.negativePart)
        ((congrArg (fun probe => rightValue.positivePart + leftValue.negativePart + probe)
            (lfkNatEqOfBeq zeroPart.positivePart zeroPart.negativePart zeroWitness).symm).trans
          ((Nat.add_assoc rightValue.positivePart leftValue.negativePart
              zeroPart.positivePart).trans
            ((congrArg (fun probe => rightValue.positivePart + probe)
                (Nat.add_comm leftValue.negativePart zeroPart.positivePart)).trans
              (Nat.add_assoc rightValue.positivePart zeroPart.positivePart
                leftValue.negativePart).symm)))
        (lfkNatLeOfBle
          (leftValue.positivePart + (rightValue.negativePart + zeroPart.negativePart))
          ((rightValue.positivePart + zeroPart.positivePart) + leftValue.negativePart)
          boundWitness)))

/-! ## Coefficient-vector kit extensions -/

/-- Congruence for cons on coefficient vectors. -/
theorem lfmConsCongr {headValue headRewritten : LfkInt}
    {tailValue tailRewritten : List LfkInt}
    (headEq : headValue = headRewritten) (tailEq : tailValue = tailRewritten) :
    headValue :: tailValue = headRewritten :: tailRewritten :=
  (congrArg (fun probe => probe :: tailValue) headEq).trans
    (congrArg (fun probe => headRewritten :: probe) tailEq)

/-- The empty vector is a left identity for padding addition. -/
theorem lfmVectorAddNilLeft : ∀ (vector : List LfkInt),
    lfkAddCoefficientVectors List.nil vector = vector
  | List.nil => rfl
  | _vectorHead :: _vectorTail => rfl

/-- The empty vector is a right identity for padding addition. -/
theorem lfmVectorAddNilRight : ∀ (vector : List LfkInt),
    lfkAddCoefficientVectors vector List.nil = vector
  | List.nil => rfl
  | _vectorHead :: _vectorTail => rfl

/-- Padding addition commutes. -/
theorem lfmVectorAddComm : ∀ (leftVector rightVector : List LfkInt),
    lfkAddCoefficientVectors leftVector rightVector
      = lfkAddCoefficientVectors rightVector leftVector
  | List.nil, List.nil => rfl
  | List.nil, _rightHead :: _rightTail => rfl
  | _leftHead :: _leftTail, List.nil => rfl
  | leftHead :: leftTail, rightHead :: rightTail =>
      lfmConsCongr (lfkIntAddComm leftHead rightHead) (lfmVectorAddComm leftTail rightTail)

/-- Padding addition associates. -/
theorem lfmVectorAddAssoc : ∀ (firstVector secondVector thirdVector : List LfkInt),
    lfkAddCoefficientVectors (lfkAddCoefficientVectors firstVector secondVector) thirdVector
      = lfkAddCoefficientVectors firstVector (lfkAddCoefficientVectors secondVector thirdVector)
  | List.nil, List.nil, List.nil => rfl
  | List.nil, List.nil, _thirdHead :: _thirdTail => rfl
  | List.nil, _secondHead :: _secondTail, List.nil => rfl
  | List.nil, _secondHead :: _secondTail, _thirdHead :: _thirdTail => rfl
  | _firstHead :: _firstTail, List.nil, List.nil => rfl
  | _firstHead :: _firstTail, List.nil, _thirdHead :: _thirdTail => rfl
  | _firstHead :: _firstTail, _secondHead :: _secondTail, List.nil => rfl
  | firstHead :: firstTail, secondHead :: secondTail, thirdHead :: thirdTail =>
      lfmConsCongr (lfkIntAddAssoc firstHead secondHead thirdHead)
        (lfmVectorAddAssoc firstTail secondTail thirdTail)

/-- Scaling distributes over padding addition. -/
theorem lfmScaleVectorAddDistrib : ∀ (multiplier : Nat) (leftVector rightVector : List LfkInt),
    lfkScaleCoefficientVector multiplier (lfkAddCoefficientVectors leftVector rightVector)
      = lfkAddCoefficientVectors (lfkScaleCoefficientVector multiplier leftVector)
          (lfkScaleCoefficientVector multiplier rightVector)
  | _multiplier, List.nil, List.nil => rfl
  | _multiplier, List.nil, _rightHead :: _rightTail => rfl
  | _multiplier, _leftHead :: _leftTail, List.nil => rfl
  | multiplier, leftHead :: leftTail, rightHead :: rightTail =>
      lfmConsCongr (lfkIntScaleAddDistrib multiplier leftHead rightHead)
        (lfmScaleVectorAddDistrib multiplier leftTail rightTail)

/-- Vector scaling composes with multiplier multiplication. -/
theorem lfmScaleVectorCompose : ∀ (outerMultiplier innerMultiplier : Nat)
    (vector : List LfkInt),
    lfkScaleCoefficientVector (outerMultiplier * innerMultiplier) vector
      = lfkScaleCoefficientVector outerMultiplier
          (lfkScaleCoefficientVector innerMultiplier vector)
  | _outerMultiplier, _innerMultiplier, List.nil => rfl
  | outerMultiplier, innerMultiplier, vectorHead :: vectorTail =>
      lfmConsCongr (lfmIntScaleCompose outerMultiplier innerMultiplier vectorHead)
        (lfmScaleVectorCompose outerMultiplier innerMultiplier vectorTail)

/-- Vector scaling distributes over multiplier addition. -/
theorem lfmScaleVectorAddMultipliers : ∀ (leftMultiplier rightMultiplier : Nat)
    (vector : List LfkInt),
    lfkScaleCoefficientVector (leftMultiplier + rightMultiplier) vector
      = lfkAddCoefficientVectors (lfkScaleCoefficientVector leftMultiplier vector)
          (lfkScaleCoefficientVector rightMultiplier vector)
  | _leftMultiplier, _rightMultiplier, List.nil => rfl
  | leftMultiplier, rightMultiplier, vectorHead :: vectorTail =>
      lfmConsCongr (lfmIntScaleAddMultipliers leftMultiplier rightMultiplier vectorHead)
        (lfmScaleVectorAddMultipliers leftMultiplier rightMultiplier vectorTail)

/-- Scaling preserves vector length. -/
theorem lfmLengthOfScaledVector : ∀ (multiplier : Nat) (vector : List LfkInt),
    List.length (lfkScaleCoefficientVector multiplier vector) = List.length vector
  | _multiplier, List.nil => rfl
  | multiplier, _vectorHead :: vectorTail =>
      congrArg (fun probe => probe + 1) (lfmLengthOfScaledVector multiplier vectorTail)

/-- Padding addition takes the greater length. -/
theorem lfmLengthOfAddedVectors : ∀ (leftVector rightVector : List LfkInt),
    List.length (lfkAddCoefficientVectors leftVector rightVector)
      = lfmNatGreater (List.length leftVector) (List.length rightVector)
  | List.nil, List.nil => rfl
  | List.nil, _rightHead :: _rightTail => rfl
  | _leftHead :: _leftTail, List.nil => rfl
  | _leftHead :: leftTail, _rightHead :: rightTail =>
      (congrArg (fun probe => probe + 1) (lfmLengthOfAddedVectors leftTail rightTail)).trans
        (lfmNatGreaterSucc (List.length leftTail) (List.length rightTail)).symm

/-! ## Relation kit — the join is a bounded semilattice, scaling distributes -/

/-- Is the relation an inequality (`>=` or `>`)?  The weighted-sum fold never
produces `isEqualTo` (its base is the trivial `>=` row), which is exactly what the
trivial-row absorption lemmas need. -/
def lfmRelationIsInequality : LfkRelation → Bool
  | LfkRelation.isGreaterOrEqual => true
  | LfkRelation.isStrictlyGreater => true
  | LfkRelation.isEqualTo => false

/-- The join commutes. -/
theorem lfmJoinRelationsComm : ∀ (leftRelation rightRelation : LfkRelation),
    lfkJoinRelations leftRelation rightRelation = lfkJoinRelations rightRelation leftRelation
  | LfkRelation.isGreaterOrEqual, LfkRelation.isGreaterOrEqual => rfl
  | LfkRelation.isGreaterOrEqual, LfkRelation.isStrictlyGreater => rfl
  | LfkRelation.isGreaterOrEqual, LfkRelation.isEqualTo => rfl
  | LfkRelation.isStrictlyGreater, LfkRelation.isGreaterOrEqual => rfl
  | LfkRelation.isStrictlyGreater, LfkRelation.isStrictlyGreater => rfl
  | LfkRelation.isStrictlyGreater, LfkRelation.isEqualTo => rfl
  | LfkRelation.isEqualTo, LfkRelation.isGreaterOrEqual => rfl
  | LfkRelation.isEqualTo, LfkRelation.isStrictlyGreater => rfl
  | LfkRelation.isEqualTo, LfkRelation.isEqualTo => rfl

/-- The join associates (27-arm bash, all definitional). -/
theorem lfmJoinRelationsAssoc : ∀ (firstRelation secondRelation thirdRelation : LfkRelation),
    lfkJoinRelations (lfkJoinRelations firstRelation secondRelation) thirdRelation
      = lfkJoinRelations firstRelation (lfkJoinRelations secondRelation thirdRelation)
  | LfkRelation.isGreaterOrEqual, LfkRelation.isGreaterOrEqual,
      LfkRelation.isGreaterOrEqual => rfl
  | LfkRelation.isGreaterOrEqual, LfkRelation.isGreaterOrEqual,
      LfkRelation.isStrictlyGreater => rfl
  | LfkRelation.isGreaterOrEqual, LfkRelation.isGreaterOrEqual, LfkRelation.isEqualTo => rfl
  | LfkRelation.isGreaterOrEqual, LfkRelation.isStrictlyGreater,
      LfkRelation.isGreaterOrEqual => rfl
  | LfkRelation.isGreaterOrEqual, LfkRelation.isStrictlyGreater,
      LfkRelation.isStrictlyGreater => rfl
  | LfkRelation.isGreaterOrEqual, LfkRelation.isStrictlyGreater, LfkRelation.isEqualTo => rfl
  | LfkRelation.isGreaterOrEqual, LfkRelation.isEqualTo, LfkRelation.isGreaterOrEqual => rfl
  | LfkRelation.isGreaterOrEqual, LfkRelation.isEqualTo, LfkRelation.isStrictlyGreater => rfl
  | LfkRelation.isGreaterOrEqual, LfkRelation.isEqualTo, LfkRelation.isEqualTo => rfl
  | LfkRelation.isStrictlyGreater, LfkRelation.isGreaterOrEqual,
      LfkRelation.isGreaterOrEqual => rfl
  | LfkRelation.isStrictlyGreater, LfkRelation.isGreaterOrEqual,
      LfkRelation.isStrictlyGreater => rfl
  | LfkRelation.isStrictlyGreater, LfkRelation.isGreaterOrEqual, LfkRelation.isEqualTo => rfl
  | LfkRelation.isStrictlyGreater, LfkRelation.isStrictlyGreater,
      LfkRelation.isGreaterOrEqual => rfl
  | LfkRelation.isStrictlyGreater, LfkRelation.isStrictlyGreater,
      LfkRelation.isStrictlyGreater => rfl
  | LfkRelation.isStrictlyGreater, LfkRelation.isStrictlyGreater, LfkRelation.isEqualTo => rfl
  | LfkRelation.isStrictlyGreater, LfkRelation.isEqualTo, LfkRelation.isGreaterOrEqual => rfl
  | LfkRelation.isStrictlyGreater, LfkRelation.isEqualTo, LfkRelation.isStrictlyGreater => rfl
  | LfkRelation.isStrictlyGreater, LfkRelation.isEqualTo, LfkRelation.isEqualTo => rfl
  | LfkRelation.isEqualTo, LfkRelation.isGreaterOrEqual, LfkRelation.isGreaterOrEqual => rfl
  | LfkRelation.isEqualTo, LfkRelation.isGreaterOrEqual, LfkRelation.isStrictlyGreater => rfl
  | LfkRelation.isEqualTo, LfkRelation.isGreaterOrEqual, LfkRelation.isEqualTo => rfl
  | LfkRelation.isEqualTo, LfkRelation.isStrictlyGreater, LfkRelation.isGreaterOrEqual => rfl
  | LfkRelation.isEqualTo, LfkRelation.isStrictlyGreater, LfkRelation.isStrictlyGreater => rfl
  | LfkRelation.isEqualTo, LfkRelation.isStrictlyGreater, LfkRelation.isEqualTo => rfl
  | LfkRelation.isEqualTo, LfkRelation.isEqualTo, LfkRelation.isGreaterOrEqual => rfl
  | LfkRelation.isEqualTo, LfkRelation.isEqualTo, LfkRelation.isStrictlyGreater => rfl
  | LfkRelation.isEqualTo, LfkRelation.isEqualTo, LfkRelation.isEqualTo => rfl

/-- Joining with an inequality on the right yields an inequality. -/
theorem lfmJoinPreservesInequality : ∀ (leftRelation rightRelation : LfkRelation),
    lfmRelationIsInequality rightRelation = true →
    lfmRelationIsInequality (lfkJoinRelations leftRelation rightRelation) = true
  | LfkRelation.isGreaterOrEqual, LfkRelation.isGreaterOrEqual, _rightWitness => rfl
  | LfkRelation.isGreaterOrEqual, LfkRelation.isStrictlyGreater, _rightWitness => rfl
  | LfkRelation.isGreaterOrEqual, LfkRelation.isEqualTo, contradictoryWitness =>
      Bool.noConfusion contradictoryWitness
  | LfkRelation.isStrictlyGreater, LfkRelation.isGreaterOrEqual, _rightWitness => rfl
  | LfkRelation.isStrictlyGreater, LfkRelation.isStrictlyGreater, _rightWitness => rfl
  | LfkRelation.isStrictlyGreater, LfkRelation.isEqualTo, contradictoryWitness =>
      Bool.noConfusion contradictoryWitness
  | LfkRelation.isEqualTo, LfkRelation.isGreaterOrEqual, _rightWitness => rfl
  | LfkRelation.isEqualTo, LfkRelation.isStrictlyGreater, _rightWitness => rfl
  | LfkRelation.isEqualTo, LfkRelation.isEqualTo, contradictoryWitness =>
      Bool.noConfusion contradictoryWitness

/-- Scaling distributes over the join (zero degrades strictness coherently on both
sides — 14-arm bash, all definitional). -/
theorem lfmScaleRelationOfJoin : ∀ (multiplier : Nat)
    (leftRelation rightRelation : LfkRelation),
    lfkScaleRelation multiplier (lfkJoinRelations leftRelation rightRelation)
      = lfkJoinRelations (lfkScaleRelation multiplier leftRelation)
          (lfkScaleRelation multiplier rightRelation)
  | _multiplier, LfkRelation.isGreaterOrEqual, LfkRelation.isGreaterOrEqual => rfl
  | _multiplier, LfkRelation.isGreaterOrEqual, LfkRelation.isEqualTo => rfl
  | _multiplier, LfkRelation.isEqualTo, LfkRelation.isGreaterOrEqual => rfl
  | _multiplier, LfkRelation.isEqualTo, LfkRelation.isEqualTo => rfl
  | Nat.zero, LfkRelation.isGreaterOrEqual, LfkRelation.isStrictlyGreater => rfl
  | Nat.succ _multiplierPred, LfkRelation.isGreaterOrEqual, LfkRelation.isStrictlyGreater => rfl
  | Nat.zero, LfkRelation.isEqualTo, LfkRelation.isStrictlyGreater => rfl
  | Nat.succ _multiplierPred, LfkRelation.isEqualTo, LfkRelation.isStrictlyGreater => rfl
  | Nat.zero, LfkRelation.isStrictlyGreater, LfkRelation.isGreaterOrEqual => rfl
  | Nat.succ _multiplierPred, LfkRelation.isStrictlyGreater, LfkRelation.isGreaterOrEqual => rfl
  | Nat.zero, LfkRelation.isStrictlyGreater, LfkRelation.isEqualTo => rfl
  | Nat.succ _multiplierPred, LfkRelation.isStrictlyGreater, LfkRelation.isEqualTo => rfl
  | Nat.zero, LfkRelation.isStrictlyGreater, LfkRelation.isStrictlyGreater => rfl
  | Nat.succ _multiplierPred, LfkRelation.isStrictlyGreater, LfkRelation.isStrictlyGreater => rfl

/-- Relation scaling composes with multiplier multiplication (the one non-`rfl`
arm transports along `Nat.zero_mul`). -/
theorem lfmScaleRelationCompose : ∀ (outerMultiplier innerMultiplier : Nat)
    (relation : LfkRelation),
    lfkScaleRelation (outerMultiplier * innerMultiplier) relation
      = lfkScaleRelation outerMultiplier (lfkScaleRelation innerMultiplier relation)
  | _outerMultiplier, _innerMultiplier, LfkRelation.isGreaterOrEqual => rfl
  | _outerMultiplier, _innerMultiplier, LfkRelation.isEqualTo => rfl
  | Nat.zero, Nat.zero, LfkRelation.isStrictlyGreater => rfl
  | Nat.zero, Nat.succ innerPred, LfkRelation.isStrictlyGreater =>
      congrArg (fun probe => lfkScaleRelation probe LfkRelation.isStrictlyGreater)
        (Nat.zero_mul (Nat.succ innerPred))
  | Nat.succ _outerPred, Nat.zero, LfkRelation.isStrictlyGreater => rfl
  | Nat.succ _outerPred, Nat.succ _innerPred, LfkRelation.isStrictlyGreater => rfl

/-- Relation scaling distributes over multiplier addition (probed: every arm
definitional — the sum's zero/succ shape mirrors the disjunction of the parts). -/
theorem lfmScaleRelationOfAddMultipliers : ∀ (leftMultiplier rightMultiplier : Nat)
    (relation : LfkRelation),
    lfkScaleRelation (leftMultiplier + rightMultiplier) relation
      = lfkJoinRelations (lfkScaleRelation leftMultiplier relation)
          (lfkScaleRelation rightMultiplier relation)
  | _leftMultiplier, _rightMultiplier, LfkRelation.isGreaterOrEqual => rfl
  | _leftMultiplier, _rightMultiplier, LfkRelation.isEqualTo => rfl
  | Nat.zero, Nat.zero, LfkRelation.isStrictlyGreater => rfl
  | Nat.zero, Nat.succ _rightPred, LfkRelation.isStrictlyGreater => rfl
  | Nat.succ _leftPred, Nat.zero, LfkRelation.isStrictlyGreater => rfl
  | Nat.succ _leftPred, Nat.succ _rightPred, LfkRelation.isStrictlyGreater => rfl

/-! ## Constraint kit — the add/scale algebra at the constraint level -/

/-- Structure congruence for constraints from the three field equations. -/
theorem lfmConstraintMkCongr {leftCoefficients rightCoefficients : List LfkInt}
    {leftBound rightBound : LfkInt} {leftRelation rightRelation : LfkRelation}
    (coefficientsEq : leftCoefficients = rightCoefficients)
    (boundEq : leftBound = rightBound) (relationEq : leftRelation = rightRelation) :
    LfkConstraint.mk leftCoefficients leftBound leftRelation
      = LfkConstraint.mk rightCoefficients rightBound rightRelation :=
  ((congrArg (fun probe => LfkConstraint.mk probe leftBound leftRelation)
      coefficientsEq).trans
    (congrArg (fun probe => LfkConstraint.mk rightCoefficients probe leftRelation)
      boundEq)).trans
    (congrArg (fun probe => LfkConstraint.mk rightCoefficients rightBound probe) relationEq)

/-- Congruence for constraint addition in both operands. -/
theorem lfmAddConstraintsCongr {leftValue leftRewritten rightValue rightRewritten : LfkConstraint}
    (leftEq : leftValue = leftRewritten) (rightEq : rightValue = rightRewritten) :
    lfkAddConstraints leftValue rightValue = lfkAddConstraints leftRewritten rightRewritten :=
  (congrArg (fun probe => lfkAddConstraints probe rightValue) leftEq).trans
    (congrArg (fun probe => lfkAddConstraints leftRewritten probe) rightEq)

/-- Constraint scaling distributes over constraint addition. -/
theorem lfmScaleConstraintAddDistrib (multiplier : Nat)
    (leftConstraint rightConstraint : LfkConstraint) :
    lfkScaleConstraint multiplier (lfkAddConstraints leftConstraint rightConstraint)
      = lfkAddConstraints (lfkScaleConstraint multiplier leftConstraint)
          (lfkScaleConstraint multiplier rightConstraint) :=
  lfmConstraintMkCongr
    (lfmScaleVectorAddDistrib multiplier leftConstraint.coefficients
      rightConstraint.coefficients)
    (lfkIntScaleAddDistrib multiplier leftConstraint.bound rightConstraint.bound)
    (lfmScaleRelationOfJoin multiplier leftConstraint.relation rightConstraint.relation)

/-- Constraint scaling composes with multiplier multiplication. -/
theorem lfmScaleConstraintCompose (outerMultiplier innerMultiplier : Nat)
    (constraint : LfkConstraint) :
    lfkScaleConstraint (outerMultiplier * innerMultiplier) constraint
      = lfkScaleConstraint outerMultiplier (lfkScaleConstraint innerMultiplier constraint) :=
  lfmConstraintMkCongr
    (lfmScaleVectorCompose outerMultiplier innerMultiplier constraint.coefficients)
    (lfmIntScaleCompose outerMultiplier innerMultiplier constraint.bound)
    (lfmScaleRelationCompose outerMultiplier innerMultiplier constraint.relation)

/-- Constraint scaling distributes over multiplier addition. -/
theorem lfmScaleConstraintAddMultipliers (leftMultiplier rightMultiplier : Nat)
    (constraint : LfkConstraint) :
    lfkScaleConstraint (leftMultiplier + rightMultiplier) constraint
      = lfkAddConstraints (lfkScaleConstraint leftMultiplier constraint)
          (lfkScaleConstraint rightMultiplier constraint) :=
  lfmConstraintMkCongr
    (lfmScaleVectorAddMultipliers leftMultiplier rightMultiplier constraint.coefficients)
    (lfmIntScaleAddMultipliers leftMultiplier rightMultiplier constraint.bound)
    (lfmScaleRelationOfAddMultipliers leftMultiplier rightMultiplier constraint.relation)

/-- Constraint addition commutes. -/
theorem lfmAddConstraintsComm (leftConstraint rightConstraint : LfkConstraint) :
    lfkAddConstraints leftConstraint rightConstraint
      = lfkAddConstraints rightConstraint leftConstraint :=
  lfmConstraintMkCongr
    (lfmVectorAddComm leftConstraint.coefficients rightConstraint.coefficients)
    (lfkIntAddComm leftConstraint.bound rightConstraint.bound)
    (lfmJoinRelationsComm leftConstraint.relation rightConstraint.relation)

/-- Constraint addition associates. -/
theorem lfmAddConstraintsAssoc (firstConstraint secondConstraint thirdConstraint : LfkConstraint) :
    lfkAddConstraints (lfkAddConstraints firstConstraint secondConstraint) thirdConstraint
      = lfkAddConstraints firstConstraint
          (lfkAddConstraints secondConstraint thirdConstraint) :=
  lfmConstraintMkCongr
    (lfmVectorAddAssoc firstConstraint.coefficients secondConstraint.coefficients
      thirdConstraint.coefficients)
    (lfkIntAddAssoc firstConstraint.bound secondConstraint.bound thirdConstraint.bound)
    (lfmJoinRelationsAssoc firstConstraint.relation secondConstraint.relation
      thirdConstraint.relation)

/-- The four-term shuffle at the constraint level (mirrors `lfkNatAddSwapMiddle`). -/
theorem lfmAddConstraintsSwapMiddle
    (firstConstraint secondConstraint thirdConstraint fourthConstraint : LfkConstraint) :
    lfkAddConstraints (lfkAddConstraints firstConstraint secondConstraint)
        (lfkAddConstraints thirdConstraint fourthConstraint)
      = lfkAddConstraints (lfkAddConstraints firstConstraint thirdConstraint)
          (lfkAddConstraints secondConstraint fourthConstraint) :=
  (lfmAddConstraintsAssoc firstConstraint secondConstraint
      (lfkAddConstraints thirdConstraint fourthConstraint)).trans
    ((congrArg (fun probe => lfkAddConstraints firstConstraint probe)
        (((lfmAddConstraintsAssoc secondConstraint thirdConstraint fourthConstraint).symm.trans
            (congrArg (fun probe => lfkAddConstraints probe fourthConstraint)
              (lfmAddConstraintsComm secondConstraint thirdConstraint))).trans
          (lfmAddConstraintsAssoc thirdConstraint secondConstraint fourthConstraint))).trans
      (lfmAddConstraintsAssoc firstConstraint thirdConstraint
        (lfkAddConstraints secondConstraint fourthConstraint)).symm)

/-- The trivial row is a left identity for constraint addition on inequality rows. -/
theorem lfmAddConstraintsTrivialLeft : ∀ (constraint : LfkConstraint),
    lfmRelationIsInequality constraint.relation = true →
    lfkAddConstraints lfkTrivialConstraint constraint = constraint
  | LfkConstraint.mk coefficientVector boundValue LfkRelation.isGreaterOrEqual,
      _inequalityWitness =>
      lfmConstraintMkCongr (lfmVectorAddNilLeft coefficientVector)
        (lfkIntZeroAdd boundValue) rfl
  | LfkConstraint.mk coefficientVector boundValue LfkRelation.isStrictlyGreater,
      _inequalityWitness =>
      lfmConstraintMkCongr (lfmVectorAddNilLeft coefficientVector)
        (lfkIntZeroAdd boundValue) rfl
  | LfkConstraint.mk _coefficientVector _boundValue LfkRelation.isEqualTo,
      contradictoryWitness => Bool.noConfusion contradictoryWitness

/-- The trivial row is a right identity for constraint addition on inequality rows. -/
theorem lfmAddConstraintsTrivialRight : ∀ (constraint : LfkConstraint),
    lfmRelationIsInequality constraint.relation = true →
    lfkAddConstraints constraint lfkTrivialConstraint = constraint
  | LfkConstraint.mk coefficientVector boundValue LfkRelation.isGreaterOrEqual,
      _inequalityWitness =>
      lfmConstraintMkCongr (lfmVectorAddNilRight coefficientVector)
        (lfkIntAddZero boundValue) rfl
  | LfkConstraint.mk coefficientVector boundValue LfkRelation.isStrictlyGreater,
      _inequalityWitness =>
      lfmConstraintMkCongr (lfmVectorAddNilRight coefficientVector)
        (lfkIntAddZero boundValue) rfl
  | LfkConstraint.mk _coefficientVector _boundValue LfkRelation.isEqualTo,
      contradictoryWitness => Bool.noConfusion contradictoryWitness

/-! ## Provenance vectors — the Nat multiplier algebra -/

/-- Padding addition of provenance vectors (cons-only, mirrors
`lfkAddCoefficientVectors`). -/
def lfmProvenanceAdd : List Nat → List Nat → List Nat
  | List.nil, List.nil => List.nil
  | List.nil, rightHead :: rightTail => rightHead :: rightTail
  | leftHead :: leftTail, List.nil => leftHead :: leftTail
  | leftHead :: leftTail, rightHead :: rightTail =>
      (leftHead + rightHead) :: lfmProvenanceAdd leftTail rightTail

/-- Scale every provenance weight. -/
def lfmProvenanceScale (multiplier : Nat) : List Nat → List Nat
  | List.nil => List.nil
  | weightHead :: weightTail => multiplier * weightHead :: lfmProvenanceScale multiplier weightTail

/-- The unit provenance: weight 1 at the given row index, 0 before it. -/
def lfmUnitProvenance : Nat → List Nat
  | Nat.zero => 1 :: List.nil
  | Nat.succ indexPred => 0 :: lfmUnitProvenance indexPred

/-! ## THE BILINEARITY THEOREMS — weighted sums are linear in the certificate -/

/-- The weighted-sum fold never produces an equality relation (its base is the
trivial `>=` row and the join preserves inequalities from the right). -/
theorem lfmWeightedSumRelationIsInequality : ∀ (certificate : List Nat)
    (system : List LfkConstraint),
    lfmRelationIsInequality (lfkWeightedSum certificate system).relation = true
  | List.nil, List.nil => rfl
  | List.nil, _constraintHead :: _constraintTail => rfl
  | _multiplierHead :: _multiplierTail, List.nil => rfl
  | multiplierHead :: multiplierTail, constraintHead :: constraintTail =>
      lfmJoinPreservesInequality
        (lfkScaleRelation multiplierHead constraintHead.relation)
        (lfkWeightedSum multiplierTail constraintTail).relation
        (lfmWeightedSumRelationIsInequality multiplierTail constraintTail)

/-- BILINEARITY, scale side: weighting by a scaled certificate is scaling the
weighted sum — a STRUCTURAL equality of constraints. -/
theorem lfmWeightedSumOfScaledCertificate : ∀ (multiplier : Nat) (certificate : List Nat)
    (system : List LfkConstraint),
    lfkWeightedSum (lfmProvenanceScale multiplier certificate) system
      = lfkScaleConstraint multiplier (lfkWeightedSum certificate system)
  | _multiplier, List.nil, List.nil => rfl
  | _multiplier, List.nil, _constraintHead :: _constraintTail => rfl
  | _multiplier, _weightHead :: _weightTail, List.nil => rfl
  | multiplier, weightHead :: weightTail, constraintHead :: constraintTail =>
      (lfmAddConstraintsCongr
          (lfmScaleConstraintCompose multiplier weightHead constraintHead)
          (lfmWeightedSumOfScaledCertificate multiplier weightTail constraintTail)).trans
        (lfmScaleConstraintAddDistrib multiplier
          (lfkScaleConstraint weightHead constraintHead)
          (lfkWeightedSum weightTail constraintTail)).symm

/-- BILINEARITY, add side: weighting by a certificate sum is adding the weighted
sums — a STRUCTURAL equality of constraints. -/
theorem lfmWeightedSumOfAddedCertificates : ∀ (leftCertificate rightCertificate : List Nat)
    (system : List LfkConstraint),
    lfkWeightedSum (lfmProvenanceAdd leftCertificate rightCertificate) system
      = lfkAddConstraints (lfkWeightedSum leftCertificate system)
          (lfkWeightedSum rightCertificate system)
  | List.nil, List.nil, List.nil => rfl
  | List.nil, List.nil, _constraintHead :: _constraintTail => rfl
  | List.nil, _rightHead :: _rightTail, List.nil => rfl
  | List.nil, rightHead :: rightTail, constraintHead :: constraintTail =>
      (lfmAddConstraintsTrivialLeft
          (lfkWeightedSum (rightHead :: rightTail) (constraintHead :: constraintTail))
          (lfmWeightedSumRelationIsInequality (rightHead :: rightTail)
            (constraintHead :: constraintTail))).symm
  | _leftHead :: _leftTail, List.nil, List.nil => rfl
  | leftHead :: leftTail, List.nil, constraintHead :: constraintTail =>
      (lfmAddConstraintsTrivialRight
          (lfkWeightedSum (leftHead :: leftTail) (constraintHead :: constraintTail))
          (lfmWeightedSumRelationIsInequality (leftHead :: leftTail)
            (constraintHead :: constraintTail))).symm
  | _leftHead :: _leftTail, _rightHead :: _rightTail, List.nil => rfl
  | leftHead :: leftTail, rightHead :: rightTail, constraintHead :: constraintTail =>
      (lfmAddConstraintsCongr
          (lfmScaleConstraintAddMultipliers leftHead rightHead constraintHead)
          (lfmWeightedSumOfAddedCertificates leftTail rightTail constraintTail)).trans
        (lfmAddConstraintsSwapMiddle
          (lfkScaleConstraint leftHead constraintHead)
          (lfkScaleConstraint rightHead constraintHead)
          (lfkWeightedSum leftTail constraintTail)
          (lfkWeightedSum rightTail constraintTail))

/-- The longest coefficient vector across the system — the driver's fuel: after
this many elimination rounds every coefficient position has been processed. -/
def lfmMaxCoefficientLength : List LfkConstraint → Nat
  | List.nil => 0
  | constraintHead :: constraintTail =>
      lfmNatGreater (List.length constraintHead.coefficients)
        (lfmMaxCoefficientLength constraintTail)

/-- The weighted sum's coefficient vector never exceeds the longest row of the
system. -/
theorem lfmWeightedSumLengthBounded : ∀ (certificate : List Nat)
    (system : List LfkConstraint),
    Nat.ble (List.length (lfkWeightedSum certificate system).coefficients)
      (lfmMaxCoefficientLength system) = true
  | List.nil, List.nil => rfl
  | List.nil, _constraintHead :: _constraintTail => rfl
  | _multiplierHead :: _multiplierTail, List.nil => rfl
  | multiplierHead :: multiplierTail, constraintHead :: constraintTail =>
      lfkNatBleOfLe _ _
        (lfkNatLeCongr
          ((lfmLengthOfAddedVectors
              (lfkScaleCoefficientVector multiplierHead constraintHead.coefficients)
              (lfkWeightedSum multiplierTail constraintTail).coefficients).trans
            (congrArg
              (fun probe => lfmNatGreater probe
                (List.length (lfkWeightedSum multiplierTail constraintTail).coefficients))
              (lfmLengthOfScaledVector multiplierHead constraintHead.coefficients)))
          rfl
          (lfmNatGreaterLeOfBoth (List.length constraintHead.coefficients)
            (List.length (lfkWeightedSum multiplierTail constraintTail).coefficients)
            (lfmNatGreater (List.length constraintHead.coefficients)
              (lfmMaxCoefficientLength constraintTail))
            (lfmNatLeGreaterLeft (List.length constraintHead.coefficients)
              (lfmMaxCoefficientLength constraintTail))
            (Nat.le_trans
              (lfkNatLeOfBle _ _ (lfmWeightedSumLengthBounded multiplierTail constraintTail))
              (lfmNatLeGreaterRight (List.length constraintHead.coefficients)
                (lfmMaxCoefficientLength constraintTail)))))

/-! ## Coefficient extraction — dense vectors read as zero beyond their length -/

/-- The coefficient at a variable position; positions beyond the vector read as
the genuine zero (matching the truncating dot-product semantics).  The match
scrutinizes the VECTOR first so `lfmCoefficientAtIndex idx List.nil` reduces for
abstract `idx`. -/
def lfmCoefficientAtIndex (positionIndex : Nat) (vector : List LfkInt) : LfkInt :=
  match vector, positionIndex with
  | List.nil, _anyIndex => lfkIntZero
  | vectorHead :: _vectorTail, Nat.zero => vectorHead
  | _vectorHead :: vectorTail, Nat.succ positionPred =>
      lfmCoefficientAtIndex positionPred vectorTail
termination_by structural vector

/-- Extraction commutes with padding addition. -/
theorem lfmCoefficientAtOfAddedVectors : ∀ (positionIndex : Nat)
    (leftVector rightVector : List LfkInt),
    lfmCoefficientAtIndex positionIndex (lfkAddCoefficientVectors leftVector rightVector)
      = lfkIntAdd (lfmCoefficientAtIndex positionIndex leftVector)
          (lfmCoefficientAtIndex positionIndex rightVector)
  | _positionIndex, List.nil, List.nil => rfl
  | positionIndex, List.nil, rightHead :: rightTail =>
      (lfkIntZeroAdd (lfmCoefficientAtIndex positionIndex (rightHead :: rightTail))).symm
  | _positionIndex, _leftHead :: _leftTail, List.nil => rfl
  | Nat.zero, _leftHead :: _leftTail, _rightHead :: _rightTail => rfl
  | Nat.succ positionPred, _leftHead :: leftTail, _rightHead :: rightTail =>
      lfmCoefficientAtOfAddedVectors positionPred leftTail rightTail

/-- Extraction commutes with scaling. -/
theorem lfmCoefficientAtOfScaledVector : ∀ (positionIndex multiplier : Nat)
    (vector : List LfkInt),
    lfmCoefficientAtIndex positionIndex (lfkScaleCoefficientVector multiplier vector)
      = lfkIntScaleByNat multiplier (lfmCoefficientAtIndex positionIndex vector)
  | _positionIndex, _multiplier, List.nil => rfl
  | Nat.zero, _multiplier, _vectorHead :: _vectorTail => rfl
  | Nat.succ positionPred, multiplier, _vectorHead :: vectorTail =>
      lfmCoefficientAtOfScaledVector positionPred multiplier vectorTail

/-- Positions at or beyond the vector length read as zero. -/
theorem lfmCoefficientBeyondLengthIsZero : ∀ (positionIndex : Nat) (vector : List LfkInt),
    Nat.ble (List.length vector) positionIndex = true →
    lfmCoefficientAtIndex positionIndex vector = lfkIntZero
  | _positionIndex, List.nil, _boundWitness => rfl
  | Nat.zero, _vectorHead :: _vectorTail, contradictoryWitness =>
      Bool.noConfusion contradictoryWitness
  | Nat.succ positionPred, _vectorHead :: vectorTail, boundWitness =>
      lfmCoefficientBeyondLengthIsZero positionPred vectorTail boundWitness

/-- If every extracted entry is cross-zero then the whole-vector Bool scan agrees. -/
theorem lfmAllCoefficientsZeroOfEntriesZero : ∀ (vector : List LfkInt),
    (∀ (positionIndex : Nat),
        lfkIntIsZero (lfmCoefficientAtIndex positionIndex vector) = true) →
    lfkAllCoefficientsAreZero vector = true
  | List.nil, _entriesWitness => rfl
  | _vectorHead :: vectorTail, entriesWitness =>
      lfkBoolAndIntro _ _ (entriesWitness 0)
        (lfmAllCoefficientsZeroOfEntriesZero vectorTail
          (fun positionIndex => entriesWitness (positionIndex + 1)))

/-! ## The cancellation core — scaled opposite entries cross to zero -/

/-- THE CANCELLATION LEMMA: a cross-positive entry scaled by the opposite entry's
witnessed negative magnitude, plus the cross-negative entry scaled by the positive
magnitude, is cross-zero.  Only the WEAK cross comparisons are needed — the
witnessed deltas do the bookkeeping that `natAbs`/`Nat.sub` would have done. -/
theorem lfmScaledOppositeEntriesCancel (positiveEntry negativeEntry : LfkInt)
    (positiveWeakWitness :
      Nat.ble positiveEntry.negativePart positiveEntry.positivePart = true)
    (negativeWeakWitness :
      Nat.ble negativeEntry.positivePart negativeEntry.negativePart = true) :
    lfkIntIsZero (lfkIntAdd
      (lfkIntScaleByNat
        (lfmNatDelta negativeEntry.negativePart negativeEntry.positivePart) positiveEntry)
      (lfkIntScaleByNat
        (lfmNatDelta positiveEntry.positivePart positiveEntry.negativePart) negativeEntry))
      = true :=
  let positiveMagnitude := lfmNatDelta positiveEntry.positivePart positiveEntry.negativePart
  let negativeMagnitude := lfmNatDelta negativeEntry.negativePart negativeEntry.positivePart
  lfkNatBeqOfEq
    (negativeMagnitude * positiveEntry.positivePart
      + positiveMagnitude * negativeEntry.positivePart)
    (negativeMagnitude * positiveEntry.negativePart
      + positiveMagnitude * negativeEntry.negativePart)
    ((congrArg (fun probe => probe + positiveMagnitude * negativeEntry.positivePart)
        ((congrArg (fun probe => negativeMagnitude * probe)
            (lfmNatDeltaRecovers positiveEntry.positivePart positiveEntry.negativePart
              positiveWeakWitness).symm).trans
          (Nat.mul_add negativeMagnitude positiveEntry.negativePart positiveMagnitude))).trans
      ((Nat.add_assoc (negativeMagnitude * positiveEntry.negativePart)
          (negativeMagnitude * positiveMagnitude)
          (positiveMagnitude * negativeEntry.positivePart)).trans
        ((congrArg (fun probe => negativeMagnitude * positiveEntry.negativePart + probe)
            ((Nat.add_comm (negativeMagnitude * positiveMagnitude)
                (positiveMagnitude * negativeEntry.positivePart)).trans
              (congrArg
                (fun probe => positiveMagnitude * negativeEntry.positivePart + probe)
                (Nat.mul_comm negativeMagnitude positiveMagnitude)))).trans
          ((congrArg (fun probe => negativeMagnitude * positiveEntry.negativePart + probe)
              (Nat.mul_add positiveMagnitude negativeEntry.positivePart
                negativeMagnitude).symm).trans
            (congrArg (fun probe => negativeMagnitude * positiveEntry.negativePart
                + positiveMagnitude * probe)
              (lfmNatDeltaRecovers negativeEntry.negativePart negativeEntry.positivePart
                negativeWeakWitness))))))

/-! ## Certified rows: a constraint plus its provenance -/

/-- A certified row: the constraint TOGETHER with the Nat multipliers that derive
it from the expanded original system.  The invariant `lfmRowMatchesProvenance`
travels as a separate Prop, established definitionally at the seeds and preserved
through combination by the bilinearity theorems. -/
structure LfmCertifiedRow where
  constraint : LfkConstraint
  provenance : List Nat

/-- THE EXACTNESS INVARIANT: the row's constraint IS the provenance-weighted sum
of the expanded system. -/
def lfmRowMatchesProvenance (expandedSystem : List LfkConstraint)
    (row : LfmCertifiedRow) : Prop :=
  row.constraint = lfkWeightedSum row.provenance expandedSystem

/-- The row's coefficient at a variable position. -/
def lfmRowCoefficientAt (variableIndex : Nat) (row : LfmCertifiedRow) : LfkInt :=
  lfmCoefficientAtIndex variableIndex row.constraint.coefficients

/-- Does the row have a cross-positive coefficient at the position? -/
def lfmRowHasPositiveCoefficientAt (variableIndex : Nat) (row : LfmCertifiedRow) : Bool :=
  lfkIntIsPositive (lfmRowCoefficientAt variableIndex row)

/-- Does the row have a cross-negative coefficient at the position? -/
def lfmRowHasNegativeCoefficientAt (variableIndex : Nat) (row : LfmCertifiedRow) : Bool :=
  lfkIntIsPositive (lfkIntNegate (lfmRowCoefficientAt variableIndex row))

/-- Is the row's coefficient at the position cross-zero? -/
def lfmRowCoefficientIsZeroAt (variableIndex : Nat) (row : LfmCertifiedRow) : Bool :=
  lfkIntIsZero (lfmRowCoefficientAt variableIndex row)

/-- Is the row's coefficient vector within the length bound? -/
def lfmRowCoefficientLengthIsWithin (lengthBound : Nat) (row : LfmCertifiedRow) : Bool :=
  Nat.ble (List.length row.constraint.coefficients) lengthBound

/-- Bool fold: does every row pass the test? -/
def lfmAllRowsPass (rowTest : LfmCertifiedRow → Bool) : List LfmCertifiedRow → Bool
  | List.nil => true
  | rowHead :: rowTail => rowTest rowHead && lfmAllRowsPass rowTest rowTail

/-- Prop fold: does every row satisfy the property? -/
def lfmAllRowsHold (rowProperty : LfmCertifiedRow → Prop) : List LfmCertifiedRow → Prop
  | List.nil => True
  | rowHead :: rowTail => And (rowProperty rowHead) (lfmAllRowsHold rowProperty rowTail)

/-- Cons-only concatenation of row lists (bespoke, monomorphic — no
`List.append`). -/
def lfmJoinRowLists : List LfmCertifiedRow → List LfmCertifiedRow → List LfmCertifiedRow
  | List.nil, secondRows => secondRows
  | rowHead :: rowTail, secondRows => rowHead :: lfmJoinRowLists rowTail secondRows

/-- Joining preserves a Bool row test. -/
theorem lfmJoinPreservesAllPass (rowTest : LfmCertifiedRow → Bool) :
    ∀ (firstRows secondRows : List LfmCertifiedRow),
    lfmAllRowsPass rowTest firstRows = true → lfmAllRowsPass rowTest secondRows = true →
    lfmAllRowsPass rowTest (lfmJoinRowLists firstRows secondRows) = true
  | List.nil, _secondRows, _firstWitness, secondWitness => secondWitness
  | rowHead :: rowTail, secondRows, firstWitness, secondWitness =>
      let destructured := lfkBoolAndDestruct (rowTest rowHead)
        (lfmAllRowsPass rowTest rowTail) firstWitness
      lfkBoolAndIntro _ _ destructured.left
        (lfmJoinPreservesAllPass rowTest rowTail secondRows destructured.right secondWitness)

/-- Joining preserves a Prop row property. -/
theorem lfmJoinPreservesAllHold (rowProperty : LfmCertifiedRow → Prop) :
    ∀ (firstRows secondRows : List LfmCertifiedRow),
    lfmAllRowsHold rowProperty firstRows → lfmAllRowsHold rowProperty secondRows →
    lfmAllRowsHold rowProperty (lfmJoinRowLists firstRows secondRows)
  | List.nil, _secondRows, _firstWitness, secondWitness => secondWitness
  | _rowHead :: rowTail, secondRows, firstWitness, secondWitness =>
      And.intro firstWitness.left
        (lfmJoinPreservesAllHold rowProperty rowTail secondRows firstWitness.right
          secondWitness)

/-- Filter rows by a Bool test (cond-based, cons-only). -/
def lfmFilterRowsByTest (rowTest : LfmCertifiedRow → Bool) :
    List LfmCertifiedRow → List LfmCertifiedRow
  | List.nil => List.nil
  | rowHead :: rowTail =>
      cond (rowTest rowHead) (rowHead :: lfmFilterRowsByTest rowTest rowTail)
        (lfmFilterRowsByTest rowTest rowTail)

/-- A `cond` of two row lists passes a test if both branches do. -/
theorem lfmCondRowListAllPass (rowTest : LfmCertifiedRow → Bool) :
    ∀ (branchFlag : Bool) (keptRows droppedRows : List LfmCertifiedRow),
    lfmAllRowsPass rowTest keptRows = true → lfmAllRowsPass rowTest droppedRows = true →
    lfmAllRowsPass rowTest (cond branchFlag keptRows droppedRows) = true
  | true, _keptRows, _droppedRows, keptWitness, _droppedWitness => keptWitness
  | false, _keptRows, _droppedRows, _keptWitness, droppedWitness => droppedWitness

/-- A `cond` of two row lists holds a property if both branches do. -/
theorem lfmCondRowListAllHold (rowProperty : LfmCertifiedRow → Prop) :
    ∀ (branchFlag : Bool) (keptRows droppedRows : List LfmCertifiedRow),
    lfmAllRowsHold rowProperty keptRows → lfmAllRowsHold rowProperty droppedRows →
    lfmAllRowsHold rowProperty (cond branchFlag keptRows droppedRows)
  | true, _keptRows, _droppedRows, keptWitness, _droppedWitness => keptWitness
  | false, _keptRows, _droppedRows, _keptWitness, droppedWitness => droppedWitness

/-- Filtering preserves any Bool row test the input rows pass. -/
theorem lfmFilterPreservesAllPass (filterTest propertyTest : LfmCertifiedRow → Bool) :
    ∀ (rows : List LfmCertifiedRow), lfmAllRowsPass propertyTest rows = true →
    lfmAllRowsPass propertyTest (lfmFilterRowsByTest filterTest rows) = true
  | List.nil, _rowsWitness => rfl
  | rowHead :: rowTail, rowsWitness =>
      let destructured := lfkBoolAndDestruct (propertyTest rowHead)
        (lfmAllRowsPass propertyTest rowTail) rowsWitness
      lfmCondRowListAllPass propertyTest (filterTest rowHead)
        (rowHead :: lfmFilterRowsByTest filterTest rowTail)
        (lfmFilterRowsByTest filterTest rowTail)
        (lfkBoolAndIntro _ _ destructured.left
          (lfmFilterPreservesAllPass filterTest propertyTest rowTail destructured.right))
        (lfmFilterPreservesAllPass filterTest propertyTest rowTail destructured.right)

/-- Filtering preserves any Prop row property the input rows hold. -/
theorem lfmFilterPreservesAllHold (filterTest : LfmCertifiedRow → Bool)
    (rowProperty : LfmCertifiedRow → Prop) :
    ∀ (rows : List LfmCertifiedRow), lfmAllRowsHold rowProperty rows →
    lfmAllRowsHold rowProperty (lfmFilterRowsByTest filterTest rows)
  | List.nil, _rowsWitness => True.intro
  | rowHead :: rowTail, rowsWitness =>
      lfmCondRowListAllHold rowProperty (filterTest rowHead)
        (rowHead :: lfmFilterRowsByTest filterTest rowTail)
        (lfmFilterRowsByTest filterTest rowTail)
        (And.intro rowsWitness.left
          (lfmFilterPreservesAllHold filterTest rowProperty rowTail rowsWitness.right))
        (lfmFilterPreservesAllHold filterTest rowProperty rowTail rowsWitness.right)

/-- Every row surviving the filter passes the filter's own test. -/
theorem lfmFilterOutputsPassTest (filterTest : LfmCertifiedRow → Bool) :
    ∀ (rows : List LfmCertifiedRow),
    lfmAllRowsPass filterTest (lfmFilterRowsByTest filterTest rows) = true
  | List.nil => rfl
  | rowHead :: rowTail =>
      match lfmBoolCases (filterTest rowHead) with
      | Or.inl testTrue =>
          (congrArg (lfmAllRowsPass filterTest)
              (congrArg
                (fun probe => cond probe (rowHead :: lfmFilterRowsByTest filterTest rowTail)
                  (lfmFilterRowsByTest filterTest rowTail)) testTrue)).trans
            (lfkBoolAndIntro _ _ testTrue (lfmFilterOutputsPassTest filterTest rowTail))
      | Or.inr testFalse =>
          (congrArg (lfmAllRowsPass filterTest)
              (congrArg
                (fun probe => cond probe (rowHead :: lfmFilterRowsByTest filterTest rowTail)
                  (lfmFilterRowsByTest filterTest rowTail)) testFalse)).trans
            (lfmFilterOutputsPassTest filterTest rowTail)

/-! ## One elimination round with certificate composition -/

/-- The positive-row scaling magnitude: the witnessed excess of the coefficient's
positive part (for a cross-positive entry, its integer value). -/
def lfmPositiveMagnitudeAt (variableIndex : Nat) (row : LfmCertifiedRow) : Nat :=
  lfmNatDelta (lfmRowCoefficientAt variableIndex row).positivePart
    (lfmRowCoefficientAt variableIndex row).negativePart

/-- The negative-row scaling magnitude: the witnessed excess of the coefficient's
negative part (for a cross-negative entry, its absolute integer value). -/
def lfmNegativeMagnitudeAt (variableIndex : Nat) (row : LfmCertifiedRow) : Nat :=
  lfmNatDelta (lfmRowCoefficientAt variableIndex row).negativePart
    (lfmRowCoefficientAt variableIndex row).positivePart

/-- Cross-combine a positive row with a negative row: scale the positive row by
the negative coefficient's magnitude and vice versa, add constraints AND
provenances.  The target coefficients cancel; the provenance algebra mirrors the
constraint algebra exactly. -/
def lfmCombineRowPair (variableIndex : Nat)
    (positiveRow negativeRow : LfmCertifiedRow) : LfmCertifiedRow :=
  LfmCertifiedRow.mk
    (lfkAddConstraints
      (lfkScaleConstraint (lfmNegativeMagnitudeAt variableIndex negativeRow)
        positiveRow.constraint)
      (lfkScaleConstraint (lfmPositiveMagnitudeAt variableIndex positiveRow)
        negativeRow.constraint))
    (lfmProvenanceAdd
      (lfmProvenanceScale (lfmNegativeMagnitudeAt variableIndex negativeRow)
        positiveRow.provenance)
      (lfmProvenanceScale (lfmPositiveMagnitudeAt variableIndex positiveRow)
        negativeRow.provenance))

/-- Combination preserves provenance exactness: the constraint-level add and scale
are exactly the provenance-level add and scale, by the bilinearity theorems. -/
theorem lfmCombineRowPairExact (expandedSystem : List LfkConstraint) (variableIndex : Nat)
    (positiveRow negativeRow : LfmCertifiedRow)
    (positiveExact : lfmRowMatchesProvenance expandedSystem positiveRow)
    (negativeExact : lfmRowMatchesProvenance expandedSystem negativeRow) :
    lfmRowMatchesProvenance expandedSystem
      (lfmCombineRowPair variableIndex positiveRow negativeRow) :=
  (lfmAddConstraintsCongr
      (congrArg
        (lfkScaleConstraint (lfmNegativeMagnitudeAt variableIndex negativeRow))
        positiveExact)
      (congrArg
        (lfkScaleConstraint (lfmPositiveMagnitudeAt variableIndex positiveRow))
        negativeExact)).trans
    ((lfmAddConstraintsCongr
        (lfmWeightedSumOfScaledCertificate
          (lfmNegativeMagnitudeAt variableIndex negativeRow)
          positiveRow.provenance expandedSystem).symm
        (lfmWeightedSumOfScaledCertificate
          (lfmPositiveMagnitudeAt variableIndex positiveRow)
          negativeRow.provenance expandedSystem).symm).trans
      (lfmWeightedSumOfAddedCertificates
        (lfmProvenanceScale (lfmNegativeMagnitudeAt variableIndex negativeRow)
          positiveRow.provenance)
        (lfmProvenanceScale (lfmPositiveMagnitudeAt variableIndex positiveRow)
          negativeRow.provenance) expandedSystem).symm)

/-- Combination preserves satisfaction, from the checker's scale and add
preservation lemmas. -/
theorem lfmCombineRowPairSatisfied (env : List LfkInt) (variableIndex : Nat)
    (positiveRow negativeRow : LfmCertifiedRow)
    (positiveSat : lfkSatisfiesConstraint env positiveRow.constraint = true)
    (negativeSat : lfkSatisfiesConstraint env negativeRow.constraint = true) :
    lfkSatisfiesConstraint env
      (lfmCombineRowPair variableIndex positiveRow negativeRow).constraint = true :=
  lfkAddPreservesSatisfaction env
    (lfkScaleConstraint (lfmNegativeMagnitudeAt variableIndex negativeRow)
      positiveRow.constraint)
    (lfkScaleConstraint (lfmPositiveMagnitudeAt variableIndex positiveRow)
      negativeRow.constraint)
    (lfkScalePreservesSatisfaction env (lfmNegativeMagnitudeAt variableIndex negativeRow)
      positiveRow.constraint positiveSat)
    (lfkScalePreservesSatisfaction env (lfmPositiveMagnitudeAt variableIndex positiveRow)
      negativeRow.constraint negativeSat)

/-- The combined row's coefficient at the eliminated position is cross-zero (the
cancellation lemma through the entry-extraction homomorphisms). -/
theorem lfmCombineRowPairZeroAtTarget (variableIndex : Nat)
    (positiveRow negativeRow : LfmCertifiedRow)
    (positiveTest : lfmRowHasPositiveCoefficientAt variableIndex positiveRow = true)
    (negativeTest : lfmRowHasNegativeCoefficientAt variableIndex negativeRow = true) :
    lfmRowCoefficientIsZeroAt variableIndex
      (lfmCombineRowPair variableIndex positiveRow negativeRow) = true :=
  (congrArg lfkIntIsZero
      ((lfmCoefficientAtOfAddedVectors variableIndex
          (lfkScaleCoefficientVector (lfmNegativeMagnitudeAt variableIndex negativeRow)
            positiveRow.constraint.coefficients)
          (lfkScaleCoefficientVector (lfmPositiveMagnitudeAt variableIndex positiveRow)
            negativeRow.constraint.coefficients)).trans
        (lfkIntAddCongr
          (lfmCoefficientAtOfScaledVector variableIndex
            (lfmNegativeMagnitudeAt variableIndex negativeRow)
            positiveRow.constraint.coefficients)
          (lfmCoefficientAtOfScaledVector variableIndex
            (lfmPositiveMagnitudeAt variableIndex positiveRow)
            negativeRow.constraint.coefficients)))).trans
    (lfmScaledOppositeEntriesCancel
      (lfmRowCoefficientAt variableIndex positiveRow)
      (lfmRowCoefficientAt variableIndex negativeRow)
      (lfmNatBleWeakenFromSucc
        (lfmRowCoefficientAt variableIndex positiveRow).negativePart
        (lfmRowCoefficientAt variableIndex positiveRow).positivePart positiveTest)
      (lfmNatBleWeakenFromSucc
        (lfmRowCoefficientAt variableIndex negativeRow).positivePart
        (lfmRowCoefficientAt variableIndex negativeRow).negativePart negativeTest))

/-- Combination preserves cross-zero coefficients at every other position. -/
theorem lfmCombineRowPairPreservesZeroAt (otherIndex variableIndex : Nat)
    (positiveRow negativeRow : LfmCertifiedRow)
    (positiveZero : lfmRowCoefficientIsZeroAt otherIndex positiveRow = true)
    (negativeZero : lfmRowCoefficientIsZeroAt otherIndex negativeRow = true) :
    lfmRowCoefficientIsZeroAt otherIndex
      (lfmCombineRowPair variableIndex positiveRow negativeRow) = true :=
  (congrArg lfkIntIsZero
      ((lfmCoefficientAtOfAddedVectors otherIndex
          (lfkScaleCoefficientVector (lfmNegativeMagnitudeAt variableIndex negativeRow)
            positiveRow.constraint.coefficients)
          (lfkScaleCoefficientVector (lfmPositiveMagnitudeAt variableIndex positiveRow)
            negativeRow.constraint.coefficients)).trans
        (lfkIntAddCongr
          (lfmCoefficientAtOfScaledVector otherIndex
            (lfmNegativeMagnitudeAt variableIndex negativeRow)
            positiveRow.constraint.coefficients)
          (lfmCoefficientAtOfScaledVector otherIndex
            (lfmPositiveMagnitudeAt variableIndex positiveRow)
            negativeRow.constraint.coefficients)))).trans
    (lfkIntAddZeroPreserving
      (lfmIntScalePreservesZero (lfmNegativeMagnitudeAt variableIndex negativeRow)
        positiveZero)
      (lfmIntScalePreservesZero (lfmPositiveMagnitudeAt variableIndex positiveRow)
        negativeZero))

/-- Combination keeps coefficient vectors within any common length bound. -/
theorem lfmCombineRowPairLengthWithin (lengthBound variableIndex : Nat)
    (positiveRow negativeRow : LfmCertifiedRow)
    (positiveWithin : lfmRowCoefficientLengthIsWithin lengthBound positiveRow = true)
    (negativeWithin : lfmRowCoefficientLengthIsWithin lengthBound negativeRow = true) :
    lfmRowCoefficientLengthIsWithin lengthBound
      (lfmCombineRowPair variableIndex positiveRow negativeRow) = true :=
  lfkNatBleOfLe _ _
    (lfkNatLeCongr
      ((lfmLengthOfAddedVectors
          (lfkScaleCoefficientVector (lfmNegativeMagnitudeAt variableIndex negativeRow)
            positiveRow.constraint.coefficients)
          (lfkScaleCoefficientVector (lfmPositiveMagnitudeAt variableIndex positiveRow)
            negativeRow.constraint.coefficients)).trans
        ((congrArg
            (fun probe => lfmNatGreater probe
              (List.length (lfkScaleCoefficientVector
                (lfmPositiveMagnitudeAt variableIndex positiveRow)
                negativeRow.constraint.coefficients)))
            (lfmLengthOfScaledVector (lfmNegativeMagnitudeAt variableIndex negativeRow)
              positiveRow.constraint.coefficients)).trans
          (congrArg
            (fun probe => lfmNatGreater (List.length positiveRow.constraint.coefficients)
              probe)
            (lfmLengthOfScaledVector (lfmPositiveMagnitudeAt variableIndex positiveRow)
              negativeRow.constraint.coefficients))))
      rfl
      (lfmNatGreaterLeOfBoth (List.length positiveRow.constraint.coefficients)
        (List.length negativeRow.constraint.coefficients) lengthBound
        (lfkNatLeOfBle _ _ positiveWithin)
        (lfkNatLeOfBle _ _ negativeWithin)))

/-- Combine one positive row against every negative row. -/
def lfmCombineOneAgainstAll (variableIndex : Nat) (positiveRow : LfmCertifiedRow) :
    List LfmCertifiedRow → List LfmCertifiedRow
  | List.nil => List.nil
  | negativeHead :: negativeTail =>
      lfmCombineRowPair variableIndex positiveRow negativeHead
        :: lfmCombineOneAgainstAll variableIndex positiveRow negativeTail

/-- Combine every positive row against every negative row. -/
def lfmCrossCombineAll (variableIndex : Nat) :
    List LfmCertifiedRow → List LfmCertifiedRow → List LfmCertifiedRow
  | List.nil, _negativeRows => List.nil
  | positiveHead :: positiveTail, negativeRows =>
      lfmJoinRowLists (lfmCombineOneAgainstAll variableIndex positiveHead negativeRows)
        (lfmCrossCombineAll variableIndex positiveTail negativeRows)

/-- Bool-test transport through `lfmCombineOneAgainstAll`, generic in the pair
step. -/
theorem lfmCombineOneAllPass (variableIndex : Nat)
    (targetTest positiveTest negativeTest : LfmCertifiedRow → Bool)
    (pairStep : ∀ (positiveRow negativeRow : LfmCertifiedRow),
      positiveTest positiveRow = true → negativeTest negativeRow = true →
      targetTest (lfmCombineRowPair variableIndex positiveRow negativeRow) = true)
    (positiveRow : LfmCertifiedRow) (positivePass : positiveTest positiveRow = true) :
    ∀ (negativeRows : List LfmCertifiedRow),
    lfmAllRowsPass negativeTest negativeRows = true →
    lfmAllRowsPass targetTest
      (lfmCombineOneAgainstAll variableIndex positiveRow negativeRows) = true
  | List.nil, _negativeWitness => rfl
  | negativeHead :: negativeTail, negativeWitness =>
      let destructured := lfkBoolAndDestruct (negativeTest negativeHead)
        (lfmAllRowsPass negativeTest negativeTail) negativeWitness
      lfkBoolAndIntro _ _
        (pairStep positiveRow negativeHead positivePass destructured.left)
        (lfmCombineOneAllPass variableIndex targetTest positiveTest negativeTest pairStep
          positiveRow positivePass negativeTail destructured.right)

/-- Bool-test transport through the full cross product. -/
theorem lfmCrossCombineAllPass (variableIndex : Nat)
    (targetTest positiveTest negativeTest : LfmCertifiedRow → Bool)
    (pairStep : ∀ (positiveRow negativeRow : LfmCertifiedRow),
      positiveTest positiveRow = true → negativeTest negativeRow = true →
      targetTest (lfmCombineRowPair variableIndex positiveRow negativeRow) = true) :
    ∀ (positiveRows : List LfmCertifiedRow),
    lfmAllRowsPass positiveTest positiveRows = true →
    ∀ (negativeRows : List LfmCertifiedRow),
    lfmAllRowsPass negativeTest negativeRows = true →
    lfmAllRowsPass targetTest
      (lfmCrossCombineAll variableIndex positiveRows negativeRows) = true
  | List.nil, _positiveWitness, _negativeRows, _negativeWitness => rfl
  | positiveHead :: positiveTail, positiveWitness, negativeRows, negativeWitness =>
      let destructured := lfkBoolAndDestruct (positiveTest positiveHead)
        (lfmAllRowsPass positiveTest positiveTail) positiveWitness
      lfmJoinPreservesAllPass targetTest _ _
        (lfmCombineOneAllPass variableIndex targetTest positiveTest negativeTest pairStep
          positiveHead destructured.left negativeRows negativeWitness)
        (lfmCrossCombineAllPass variableIndex targetTest positiveTest negativeTest pairStep
          positiveTail destructured.right negativeRows negativeWitness)

/-- Prop-property transport through `lfmCombineOneAgainstAll`. -/
theorem lfmCombineOneAllHold (variableIndex : Nat)
    (targetProperty positiveProperty negativeProperty : LfmCertifiedRow → Prop)
    (pairStep : ∀ (positiveRow negativeRow : LfmCertifiedRow),
      positiveProperty positiveRow → negativeProperty negativeRow →
      targetProperty (lfmCombineRowPair variableIndex positiveRow negativeRow))
    (positiveRow : LfmCertifiedRow) (positiveHolds : positiveProperty positiveRow) :
    ∀ (negativeRows : List LfmCertifiedRow),
    lfmAllRowsHold negativeProperty negativeRows →
    lfmAllRowsHold targetProperty
      (lfmCombineOneAgainstAll variableIndex positiveRow negativeRows)
  | List.nil, _negativeWitness => True.intro
  | _negativeHead :: negativeTail, negativeWitness =>
      And.intro (pairStep positiveRow _ positiveHolds negativeWitness.left)
        (lfmCombineOneAllHold variableIndex targetProperty positiveProperty
          negativeProperty pairStep positiveRow positiveHolds negativeTail
          negativeWitness.right)

/-- Prop-property transport through the full cross product. -/
theorem lfmCrossCombineAllHold (variableIndex : Nat)
    (targetProperty positiveProperty negativeProperty : LfmCertifiedRow → Prop)
    (pairStep : ∀ (positiveRow negativeRow : LfmCertifiedRow),
      positiveProperty positiveRow → negativeProperty negativeRow →
      targetProperty (lfmCombineRowPair variableIndex positiveRow negativeRow)) :
    ∀ (positiveRows : List LfmCertifiedRow),
    lfmAllRowsHold positiveProperty positiveRows →
    ∀ (negativeRows : List LfmCertifiedRow),
    lfmAllRowsHold negativeProperty negativeRows →
    lfmAllRowsHold targetProperty
      (lfmCrossCombineAll variableIndex positiveRows negativeRows)
  | List.nil, _positiveWitness, _negativeRows, _negativeWitness => True.intro
  | _positiveHead :: positiveTail, positiveWitness, negativeRows, negativeWitness =>
      lfmJoinPreservesAllHold targetProperty _ _
        (lfmCombineOneAllHold variableIndex targetProperty positiveProperty
          negativeProperty pairStep _ positiveWitness.left negativeRows negativeWitness)
        (lfmCrossCombineAllHold variableIndex targetProperty positiveProperty
          negativeProperty pairStep positiveTail positiveWitness.right negativeRows
          negativeWitness)

/-- ONE ELIMINATION ROUND: pass through the rows with cross-zero coefficient at
the target position, cross-combine the positive bucket against the negative
bucket.  Certificate provenance composes inside `lfmCombineRowPair`. -/
def lfmEliminationRound (variableIndex : Nat) (rows : List LfmCertifiedRow) :
    List LfmCertifiedRow :=
  lfmJoinRowLists
    (lfmFilterRowsByTest (lfmRowCoefficientIsZeroAt variableIndex) rows)
    (lfmCrossCombineAll variableIndex
      (lfmFilterRowsByTest (lfmRowHasPositiveCoefficientAt variableIndex) rows)
      (lfmFilterRowsByTest (lfmRowHasNegativeCoefficientAt variableIndex) rows))

/-- Generic Bool-test preservation through a round (pair step supplied). -/
theorem lfmRoundPreservesAllPass (variableIndex : Nat)
    (propertyTest : LfmCertifiedRow → Bool)
    (pairStep : ∀ (positiveRow negativeRow : LfmCertifiedRow),
      propertyTest positiveRow = true → propertyTest negativeRow = true →
      propertyTest (lfmCombineRowPair variableIndex positiveRow negativeRow) = true)
    (rows : List LfmCertifiedRow)
    (rowsWitness : lfmAllRowsPass propertyTest rows = true) :
    lfmAllRowsPass propertyTest (lfmEliminationRound variableIndex rows) = true :=
  lfmJoinPreservesAllPass propertyTest _ _
    (lfmFilterPreservesAllPass (lfmRowCoefficientIsZeroAt variableIndex) propertyTest
      rows rowsWitness)
    (lfmCrossCombineAllPass variableIndex propertyTest propertyTest propertyTest pairStep
      (lfmFilterRowsByTest (lfmRowHasPositiveCoefficientAt variableIndex) rows)
      (lfmFilterPreservesAllPass (lfmRowHasPositiveCoefficientAt variableIndex)
        propertyTest rows rowsWitness)
      (lfmFilterRowsByTest (lfmRowHasNegativeCoefficientAt variableIndex) rows)
      (lfmFilterPreservesAllPass (lfmRowHasNegativeCoefficientAt variableIndex)
        propertyTest rows rowsWitness))

/-- Generic Prop-property preservation through a round. -/
theorem lfmRoundPreservesAllHold (variableIndex : Nat)
    (rowProperty : LfmCertifiedRow → Prop)
    (pairStep : ∀ (positiveRow negativeRow : LfmCertifiedRow),
      rowProperty positiveRow → rowProperty negativeRow →
      rowProperty (lfmCombineRowPair variableIndex positiveRow negativeRow))
    (rows : List LfmCertifiedRow) (rowsWitness : lfmAllRowsHold rowProperty rows) :
    lfmAllRowsHold rowProperty (lfmEliminationRound variableIndex rows) :=
  lfmJoinPreservesAllHold rowProperty _ _
    (lfmFilterPreservesAllHold (lfmRowCoefficientIsZeroAt variableIndex) rowProperty
      rows rowsWitness)
    (lfmCrossCombineAllHold variableIndex rowProperty rowProperty rowProperty pairStep
      (lfmFilterRowsByTest (lfmRowHasPositiveCoefficientAt variableIndex) rows)
      (lfmFilterPreservesAllHold (lfmRowHasPositiveCoefficientAt variableIndex)
        rowProperty rows rowsWitness)
      (lfmFilterRowsByTest (lfmRowHasNegativeCoefficientAt variableIndex) rows)
      (lfmFilterPreservesAllHold (lfmRowHasNegativeCoefficientAt variableIndex)
        rowProperty rows rowsWitness))

/-- The round preserves provenance exactness. -/
theorem lfmRoundPreservesExactness (expandedSystem : List LfkConstraint)
    (variableIndex : Nat) (rows : List LfmCertifiedRow)
    (rowsWitness : lfmAllRowsHold (lfmRowMatchesProvenance expandedSystem) rows) :
    lfmAllRowsHold (lfmRowMatchesProvenance expandedSystem)
      (lfmEliminationRound variableIndex rows) :=
  lfmRoundPreservesAllHold variableIndex (lfmRowMatchesProvenance expandedSystem)
    (fun positiveRow negativeRow positiveExact negativeExact =>
      lfmCombineRowPairExact expandedSystem variableIndex positiveRow negativeRow
        positiveExact negativeExact)
    rows rowsWitness

/-- At round level: satisfaction is preserved forward. -/
theorem lfmRoundPreservesSatisfaction (env : List LfkInt) (variableIndex : Nat)
    (rows : List LfmCertifiedRow)
    (rowsWitness : lfmAllRowsPass
      (fun row => lfkSatisfiesConstraint env row.constraint) rows = true) :
    lfmAllRowsPass (fun row => lfkSatisfiesConstraint env row.constraint)
      (lfmEliminationRound variableIndex rows) = true :=
  lfmRoundPreservesAllPass variableIndex
    (fun row => lfkSatisfiesConstraint env row.constraint)
    (fun positiveRow negativeRow positiveSat negativeSat =>
      lfmCombineRowPairSatisfied env variableIndex positiveRow negativeRow
        positiveSat negativeSat)
    rows rowsWitness

/-- At round level: every output row has cross-zero coefficient at the eliminated
position, unconditionally (zero bucket by its filter test, cross combinations by
cancellation). -/
theorem lfmRoundEliminatesTargetVariable (variableIndex : Nat)
    (rows : List LfmCertifiedRow) :
    lfmAllRowsPass (lfmRowCoefficientIsZeroAt variableIndex)
      (lfmEliminationRound variableIndex rows) = true :=
  lfmJoinPreservesAllPass (lfmRowCoefficientIsZeroAt variableIndex) _ _
    (lfmFilterOutputsPassTest (lfmRowCoefficientIsZeroAt variableIndex) rows)
    (lfmCrossCombineAllPass variableIndex (lfmRowCoefficientIsZeroAt variableIndex)
      (lfmRowHasPositiveCoefficientAt variableIndex)
      (lfmRowHasNegativeCoefficientAt variableIndex)
      (fun positiveRow negativeRow positiveTest negativeTest =>
        lfmCombineRowPairZeroAtTarget variableIndex positiveRow negativeRow
          positiveTest negativeTest)
      (lfmFilterRowsByTest (lfmRowHasPositiveCoefficientAt variableIndex) rows)
      (lfmFilterOutputsPassTest (lfmRowHasPositiveCoefficientAt variableIndex) rows)
      (lfmFilterRowsByTest (lfmRowHasNegativeCoefficientAt variableIndex) rows)
      (lfmFilterOutputsPassTest (lfmRowHasNegativeCoefficientAt variableIndex) rows))

/-- The round preserves cross-zero coefficients at every position. -/
theorem lfmRoundPreservesZeroCoefficientAt (otherIndex variableIndex : Nat)
    (rows : List LfmCertifiedRow)
    (rowsWitness : lfmAllRowsPass (lfmRowCoefficientIsZeroAt otherIndex) rows = true) :
    lfmAllRowsPass (lfmRowCoefficientIsZeroAt otherIndex)
      (lfmEliminationRound variableIndex rows) = true :=
  lfmRoundPreservesAllPass variableIndex (lfmRowCoefficientIsZeroAt otherIndex)
    (fun positiveRow negativeRow positiveZero negativeZero =>
      lfmCombineRowPairPreservesZeroAt otherIndex variableIndex positiveRow negativeRow
        positiveZero negativeZero)
    rows rowsWitness

/-- The round preserves the coefficient-length bound. -/
theorem lfmRoundPreservesLengthWithin (lengthBound variableIndex : Nat)
    (rows : List LfmCertifiedRow)
    (rowsWitness : lfmAllRowsPass (lfmRowCoefficientLengthIsWithin lengthBound) rows
      = true) :
    lfmAllRowsPass (lfmRowCoefficientLengthIsWithin lengthBound)
      (lfmEliminationRound variableIndex rows) = true :=
  lfmRoundPreservesAllPass variableIndex (lfmRowCoefficientLengthIsWithin lengthBound)
    (fun positiveRow negativeRow positiveWithin negativeWithin =>
      lfmCombineRowPairLengthWithin lengthBound variableIndex positiveRow negativeRow
        positiveWithin negativeWithin)
    rows rowsWitness

/-! ## Seeds, the driver, the ground scan, the composition theorem -/

/-- Seed rows: row `i` of the expanded system becomes the certified row whose
constraint is the unit-provenance weighted sum — exactness is DEFINITIONAL. -/
def lfmSeedRowsFromIndex (fullExpandedSystem : List LfkConstraint) :
    List LfkConstraint → Nat → List LfmCertifiedRow
  | List.nil, _startIndex => List.nil
  | _remainingHead :: remainingTail, startIndex =>
      LfmCertifiedRow.mk
          (lfkWeightedSum (lfmUnitProvenance startIndex) fullExpandedSystem)
          (lfmUnitProvenance startIndex)
        :: lfmSeedRowsFromIndex fullExpandedSystem remainingTail (startIndex + 1)

/-- The seed rows of an expanded system (one per row, unit provenances). -/
def lfmSeedRows (expandedSystem : List LfkConstraint) : List LfmCertifiedRow :=
  lfmSeedRowsFromIndex expandedSystem expandedSystem 0

/-- Every seed row is provenance-exact (definitionally). -/
theorem lfmSeedRowsFromIndexExact (fullExpandedSystem : List LfkConstraint) :
    ∀ (remainingRows : List LfkConstraint) (startIndex : Nat),
    lfmAllRowsHold (lfmRowMatchesProvenance fullExpandedSystem)
      (lfmSeedRowsFromIndex fullExpandedSystem remainingRows startIndex)
  | List.nil, _startIndex => True.intro
  | _remainingHead :: remainingTail, startIndex =>
      And.intro rfl
        (lfmSeedRowsFromIndexExact fullExpandedSystem remainingTail (startIndex + 1))

/-- Every seed row is satisfied by any environment satisfying the expanded
system (the sibling's weighted-sum satisfaction lemma, per unit provenance). -/
theorem lfmSeedRowsFromIndexSatisfied (fullExpandedSystem : List LfkConstraint)
    (env : List LfkInt)
    (systemWitness : lfkSatisfiesSystem env fullExpandedSystem = true) :
    ∀ (remainingRows : List LfkConstraint) (startIndex : Nat),
    lfmAllRowsPass (fun row => lfkSatisfiesConstraint env row.constraint)
      (lfmSeedRowsFromIndex fullExpandedSystem remainingRows startIndex) = true
  | List.nil, _startIndex => rfl
  | _remainingHead :: remainingTail, startIndex =>
      lfkBoolAndIntro _ _
        (lfkWeightedSumSatisfied (lfmUnitProvenance startIndex) fullExpandedSystem env
          systemWitness)
        (lfmSeedRowsFromIndexSatisfied fullExpandedSystem env systemWitness
          remainingTail (startIndex + 1))

/-- Every seed row's coefficient vector is within the system's max length. -/
theorem lfmSeedRowsFromIndexLengthBounded (fullExpandedSystem : List LfkConstraint) :
    ∀ (remainingRows : List LfkConstraint) (startIndex : Nat),
    lfmAllRowsPass
      (lfmRowCoefficientLengthIsWithin (lfmMaxCoefficientLength fullExpandedSystem))
      (lfmSeedRowsFromIndex fullExpandedSystem remainingRows startIndex) = true
  | List.nil, _startIndex => rfl
  | _remainingHead :: remainingTail, startIndex =>
      lfkBoolAndIntro _ _
        (lfmWeightedSumLengthBounded (lfmUnitProvenance startIndex) fullExpandedSystem)
        (lfmSeedRowsFromIndexLengthBounded fullExpandedSystem remainingTail
          (startIndex + 1))

/-- THE DRIVER LOOP: eliminate variables `currentIndex, currentIndex+1, ...` for
`fuel` rounds (structural recursion on the fuel — no `WellFounded.fix`). -/
def lfmEliminateFromIndex : Nat → Nat → List LfmCertifiedRow → List LfmCertifiedRow
  | _currentIndex, Nat.zero, rows => rows
  | currentIndex, Nat.succ remainingFuel, rows =>
      lfmEliminateFromIndex (currentIndex + 1) remainingFuel
        (lfmEliminationRound currentIndex rows)

/-- The driver preserves provenance exactness. -/
theorem lfmEliminateFromIndexPreservesExactness (expandedSystem : List LfkConstraint) :
    ∀ (fuel currentIndex : Nat) (rows : List LfmCertifiedRow),
    lfmAllRowsHold (lfmRowMatchesProvenance expandedSystem) rows →
    lfmAllRowsHold (lfmRowMatchesProvenance expandedSystem)
      (lfmEliminateFromIndex currentIndex fuel rows)
  | Nat.zero, _currentIndex, _rows, rowsWitness => rowsWitness
  | Nat.succ remainingFuel, currentIndex, rows, rowsWitness =>
      lfmEliminateFromIndexPreservesExactness expandedSystem remainingFuel
        (currentIndex + 1) (lfmEliminationRound currentIndex rows)
        (lfmRoundPreservesExactness expandedSystem currentIndex rows rowsWitness)

/-- The driver preserves satisfaction (forward direction, whole pipeline). -/
theorem lfmEliminateFromIndexPreservesSatisfaction (env : List LfkInt) :
    ∀ (fuel currentIndex : Nat) (rows : List LfmCertifiedRow),
    lfmAllRowsPass (fun row => lfkSatisfiesConstraint env row.constraint) rows = true →
    lfmAllRowsPass (fun row => lfkSatisfiesConstraint env row.constraint)
      (lfmEliminateFromIndex currentIndex fuel rows) = true
  | Nat.zero, _currentIndex, _rows, rowsWitness => rowsWitness
  | Nat.succ remainingFuel, currentIndex, rows, rowsWitness =>
      lfmEliminateFromIndexPreservesSatisfaction env remainingFuel (currentIndex + 1)
        (lfmEliminationRound currentIndex rows)
        (lfmRoundPreservesSatisfaction env currentIndex rows rowsWitness)

/-- The driver preserves the coefficient-length bound. -/
theorem lfmEliminateFromIndexPreservesLengthWithin (lengthBound : Nat) :
    ∀ (fuel currentIndex : Nat) (rows : List LfmCertifiedRow),
    lfmAllRowsPass (lfmRowCoefficientLengthIsWithin lengthBound) rows = true →
    lfmAllRowsPass (lfmRowCoefficientLengthIsWithin lengthBound)
      (lfmEliminateFromIndex currentIndex fuel rows) = true
  | Nat.zero, _currentIndex, _rows, rowsWitness => rowsWitness
  | Nat.succ remainingFuel, currentIndex, rows, rowsWitness =>
      lfmEliminateFromIndexPreservesLengthWithin lengthBound remainingFuel
        (currentIndex + 1) (lfmEliminationRound currentIndex rows)
        (lfmRoundPreservesLengthWithin lengthBound currentIndex rows rowsWitness)

/-- THE ZERO-COVERAGE INVARIANT: if the input rows are cross-zero at every
position below `currentIndex`, the driver's output is cross-zero at every
position below `currentIndex + fuel` (each round establishes its target and
preserves the others). -/
theorem lfmEliminateFromIndexZeroCoverage :
    ∀ (fuel currentIndex : Nat) (rows : List LfmCertifiedRow),
    (∀ (earlierIndex : Nat), Nat.ble (earlierIndex + 1) currentIndex = true →
        lfmAllRowsPass (lfmRowCoefficientIsZeroAt earlierIndex) rows = true) →
    ∀ (coveredIndex : Nat),
    Nat.ble (coveredIndex + 1) (currentIndex + fuel) = true →
    lfmAllRowsPass (lfmRowCoefficientIsZeroAt coveredIndex)
      (lfmEliminateFromIndex currentIndex fuel rows) = true
  | Nat.zero, _currentIndex, _rows, coverageWitness, coveredIndex, coveredWitness =>
      coverageWitness coveredIndex coveredWitness
  | Nat.succ remainingFuel, currentIndex, rows, coverageWitness, coveredIndex,
      coveredWitness =>
      lfmEliminateFromIndexZeroCoverage remainingFuel (currentIndex + 1)
        (lfmEliminationRound currentIndex rows)
        (fun earlierIndex earlierWitness =>
          match lfmBoolCases (Nat.ble (earlierIndex + 1) currentIndex) with
          | Or.inl strictlyBelow =>
              lfmRoundPreservesZeroCoefficientAt earlierIndex currentIndex rows
                (coverageWitness earlierIndex strictlyBelow)
          | Or.inr notBelow =>
              (congrArg
                  (fun probe => lfmAllRowsPass (lfmRowCoefficientIsZeroAt probe)
                    (lfmEliminationRound currentIndex rows))
                  (lfmNatEqOfBleBle earlierIndex currentIndex
                    (lfkNatBleOfLe earlierIndex currentIndex
                      (Nat.le_of_succ_le_succ
                        (lfkNatLeOfBle (earlierIndex + 1) (currentIndex + 1)
                          earlierWitness)))
                    (lfkNatBleOfLe currentIndex earlierIndex
                      (Nat.le_of_succ_le_succ
                        (lfkNatLeOfBle (currentIndex + 1) (earlierIndex + 1)
                          (lfmNatBleFalseFlipStrict (earlierIndex + 1) currentIndex
                            notBelow)))))).trans
                (lfmRoundEliminatesTargetVariable currentIndex rows))
        coveredIndex
        ((congrArg (Nat.ble (coveredIndex + 1))
            (Nat.succ_add currentIndex remainingFuel)).trans coveredWitness)

/-- Positions at or beyond the bound are cross-zero when the length is within the
bound; positions below are covered by hypothesis — so ALL entries are cross-zero. -/
theorem lfmRowGroundOfBoundedZeros (lengthBound : Nat) (coefficientVector : List LfkInt)
    (lengthWitness : Nat.ble (List.length coefficientVector) lengthBound = true)
    (zerosWitness : ∀ (coveredIndex : Nat),
      Nat.ble (coveredIndex + 1) lengthBound = true →
      lfkIntIsZero (lfmCoefficientAtIndex coveredIndex coefficientVector) = true) :
    lfkAllCoefficientsAreZero coefficientVector = true :=
  lfmAllCoefficientsZeroOfEntriesZero coefficientVector
    (fun positionIndex =>
      match lfmBoolCases (Nat.ble (positionIndex + 1) lengthBound) with
      | Or.inl withinWitness => zerosWitness positionIndex withinWitness
      | Or.inr beyondWitness =>
          (congrArg lfkIntIsZero
              (lfmCoefficientBeyondLengthIsZero positionIndex coefficientVector
                (lfkNatBleOfLe (List.length coefficientVector) positionIndex
                  (Nat.le_trans (lfkNatLeOfBle _ _ lengthWitness)
                    (Nat.le_of_succ_le_succ
                      (lfkNatLeOfBle (lengthBound + 1) (positionIndex + 1)
                        (lfmNatBleFalseFlipStrict (positionIndex + 1) lengthBound
                          beyondWitness))))))).trans
            (lfkNatBeqRefl 0))

/-- Rows-level assembly: length bound + per-position zero coverage give the
ground-row Bool scan on every row. -/
theorem lfmRowsGroundOfBoundedAndCovered (lengthBound : Nat) :
    ∀ (rows : List LfmCertifiedRow),
    lfmAllRowsPass (lfmRowCoefficientLengthIsWithin lengthBound) rows = true →
    (∀ (coveredIndex : Nat), Nat.ble (coveredIndex + 1) lengthBound = true →
        lfmAllRowsPass (lfmRowCoefficientIsZeroAt coveredIndex) rows = true) →
    lfmAllRowsPass (fun row => lfkAllCoefficientsAreZero row.constraint.coefficients)
      rows = true
  | List.nil, _lengthWitness, _zerosWitness => rfl
  | rowHead :: rowTail, lengthWitness, zerosWitness =>
      let destructuredLength := lfkBoolAndDestruct
        (lfmRowCoefficientLengthIsWithin lengthBound rowHead)
        (lfmAllRowsPass (lfmRowCoefficientLengthIsWithin lengthBound) rowTail)
        lengthWitness
      lfkBoolAndIntro _ _
        (lfmRowGroundOfBoundedZeros lengthBound rowHead.constraint.coefficients
          destructuredLength.left
          (fun coveredIndex coveredWitness =>
            (lfkBoolAndDestruct (lfmRowCoefficientIsZeroAt coveredIndex rowHead)
              (lfmAllRowsPass (lfmRowCoefficientIsZeroAt coveredIndex) rowTail)
              (zerosWitness coveredIndex coveredWitness)).left))
        (lfmRowsGroundOfBoundedAndCovered lengthBound rowTail destructuredLength.right
          (fun coveredIndex coveredWitness =>
            (lfkBoolAndDestruct (lfmRowCoefficientIsZeroAt coveredIndex rowHead)
              (lfmAllRowsPass (lfmRowCoefficientIsZeroAt coveredIndex) rowTail)
              (zerosWitness coveredIndex coveredWitness)).right))

/-- THE GROUND SCAN: return the provenance of the first ground-contradictory row. -/
def lfmScanForContradiction : List LfmCertifiedRow → Option (List Nat)
  | List.nil => Option.none
  | rowHead :: rowTail =>
      cond (lfkIsGroundContradiction rowHead.constraint)
        (Option.some rowHead.provenance) (lfmScanForContradiction rowTail)

/-- Split a successful `cond`-of-Option scan step into its two possible shapes. -/
theorem lfmCondSomeSplit : ∀ (testFlag : Bool) (headProvenance : List Nat)
    (tailResult : Option (List Nat)) (certificate : List Nat),
    cond testFlag (Option.some headProvenance) tailResult = Option.some certificate →
    Or (And (testFlag = true) (headProvenance = certificate))
      (And (testFlag = false) (tailResult = Option.some certificate))
  | true, _headProvenance, _tailResult, _certificate, condWitness =>
      Or.inl (And.intro rfl (Option.some.inj condWitness))
  | false, _headProvenance, _tailResult, _certificate, condWitness =>
      Or.inr (And.intro rfl condWitness)

/-- A scan hit on provenance-exact rows IS an accepted ground contradiction of
the weighted sum — the certificate needs no reconstruction. -/
theorem lfmScanHitCertifies (expandedSystem : List LfkConstraint) :
    ∀ (rows : List LfmCertifiedRow) (certificate : List Nat),
    lfmAllRowsHold (lfmRowMatchesProvenance expandedSystem) rows →
    lfmScanForContradiction rows = Option.some certificate →
    lfkIsGroundContradiction (lfkWeightedSum certificate expandedSystem) = true
  | List.nil, _certificate, _exactWitness, scanWitness => nomatch scanWitness
  | rowHead :: rowTail, certificate, exactWitness, scanWitness =>
      match lfmCondSomeSplit (lfkIsGroundContradiction rowHead.constraint)
        rowHead.provenance (lfmScanForContradiction rowTail) certificate scanWitness with
      | Or.inl (And.intro groundEq provenanceEq) =>
          ((congrArg
              (fun probe => lfkIsGroundContradiction
                (lfkWeightedSum probe expandedSystem)) provenanceEq.symm).trans
            ((congrArg lfkIsGroundContradiction exactWitness.left.symm).trans groundEq))
      | Or.inr (And.intro _testFalse tailScanWitness) =>
          lfmScanHitCertifies expandedSystem rowTail certificate exactWitness.right
            tailScanWitness

/-- THE FINDER: seed the expanded system, eliminate one variable per round for
max-coefficient-length rounds, scan the (provably ground) survivors. -/
def lfmFindRefutationCertificate (system : List LfkConstraint) : Option (List Nat) :=
  lfmScanForContradiction
    (lfmEliminateFromIndex 0 (lfmMaxCoefficientLength (lfkExpandSystem system))
      (lfmSeedRows (lfkExpandSystem system)))

/-- THE COMPOSITION THEOREM: whatever certificate the finder returns, the
sibling's checker ACCEPTS it against the original system. -/
theorem lfmFoundContradictionCertifies (system : List LfkConstraint)
    (certificate : List Nat)
    (foundWitness : lfmFindRefutationCertificate system = Option.some certificate) :
    lfkCheckRefutation certificate system = true :=
  lfmScanHitCertifies (lfkExpandSystem system)
    (lfmEliminateFromIndex 0 (lfmMaxCoefficientLength (lfkExpandSystem system))
      (lfmSeedRows (lfkExpandSystem system)))
    certificate
    (lfmEliminateFromIndexPreservesExactness (lfkExpandSystem system)
      (lfmMaxCoefficientLength (lfkExpandSystem system)) 0
      (lfmSeedRows (lfkExpandSystem system))
      (lfmSeedRowsFromIndexExact (lfkExpandSystem system) (lfkExpandSystem system) 0))
    foundWitness

/-- Composition with the sibling's soundness: a found certificate refutes EVERY
integer environment. -/
theorem lfmFoundCertificateRefutes (system : List LfkConstraint) (certificate : List Nat)
    (foundWitness : lfmFindRefutationCertificate system = Option.some certificate)
    (env : List LfkInt) (satisfactionWitness : lfkSatisfiesSystem env system = true) :
    False :=
  lfkRefutationSoundUnconditional certificate system
    (lfmFoundContradictionCertifies system certificate foundWitness) env
    satisfactionWitness

/-- THE GROUNDING THEOREM: after the full driver run every surviving row is
variable-free — the scan is a genuine ground-row scan.  (Positions below the
fuel are eliminated by rounds; positions at or beyond it are outside every
row's length bound.) -/
theorem lfmFinalRowsAreGround (system : List LfkConstraint) :
    lfmAllRowsPass (fun row => lfkAllCoefficientsAreZero row.constraint.coefficients)
      (lfmEliminateFromIndex 0 (lfmMaxCoefficientLength (lfkExpandSystem system))
        (lfmSeedRows (lfkExpandSystem system))) = true :=
  lfmRowsGroundOfBoundedAndCovered (lfmMaxCoefficientLength (lfkExpandSystem system))
    (lfmEliminateFromIndex 0 (lfmMaxCoefficientLength (lfkExpandSystem system))
      (lfmSeedRows (lfkExpandSystem system)))
    (lfmEliminateFromIndexPreservesLengthWithin
      (lfmMaxCoefficientLength (lfkExpandSystem system))
      (lfmMaxCoefficientLength (lfkExpandSystem system)) 0
      (lfmSeedRows (lfkExpandSystem system))
      (lfmSeedRowsFromIndexLengthBounded (lfkExpandSystem system)
        (lfkExpandSystem system) 0))
    (fun coveredIndex coveredWitness =>
      lfmEliminateFromIndexZeroCoverage
        (lfmMaxCoefficientLength (lfkExpandSystem system)) 0
        (lfmSeedRows (lfkExpandSystem system))
        (fun _earlierIndex contradictoryWitness => Bool.noConfusion contradictoryWitness)
        coveredIndex
        ((congrArg (Nat.ble (coveredIndex + 1))
            (Nat.zero_add (lfmMaxCoefficientLength (lfkExpandSystem system)))).trans
          coveredWitness))

/-! ## The backward direction: the one-pair step and the round-extension Prop -/

/-- The extension witness for one positive/negative pair: the rational lower bound
`(positiveBound - positiveRest) / positiveMagnitude` cleared to the common scale
`positiveMagnitude * negativeMagnitude` — i.e.
`negativeMagnitude * (positiveBound - positiveRest)`. -/
def lfmExtensionWitnessValue (negativeMagnitude : Nat)
    (positiveBound positiveRest : LfkInt) : LfkInt :=
  lfkIntScaleByNat negativeMagnitude (lfkIntAdd positiveBound (lfkIntNegate positiveRest))

/-- The one-pair extension core (weak relations): reading the positive row as
`aP*x + positiveRest >= positiveBound` and the negative row as
`-cN*x + negativeRest >= negativeBound`, if their Fourier-Motzkin combination
`cN*positiveBound + aP*negativeBound <= cN*positiveRest + aP*negativeRest` holds,
then the witness `v := cN*(positiveBound - positiveRest)` satisfies BOTH rows
after clearing denominators by `m := aP*cN`:

  * positive row (scaled by `m`): `aP*v + m*positiveRest >= m*positiveBound`
    (with equality — `v` sits exactly on the lower endpoint);
  * negative row (scaled by `m`): `cN*v + m*negativeBound <= m*negativeRest`.

This is the interval-nonemptiness algebra that the inequality-guarded round
extension iterates over the max-lower or min-upper endpoints; strict variants add a
factor of 2 and one unit of headroom from the strict combination. -/
theorem lfmOnePairExtensionCore (positiveMagnitude negativeMagnitude : Nat)
    (positiveRest positiveBound negativeRest negativeBound : LfkInt)
    (comboWitness : lfkIntLe
      (lfkIntAdd (lfkIntScaleByNat negativeMagnitude positiveBound)
        (lfkIntScaleByNat positiveMagnitude negativeBound))
      (lfkIntAdd (lfkIntScaleByNat negativeMagnitude positiveRest)
        (lfkIntScaleByNat positiveMagnitude negativeRest)) = true) :
    And
      (lfkIntLe
        (lfkIntScaleByNat (positiveMagnitude * negativeMagnitude) positiveBound)
        (lfkIntAdd
          (lfkIntScaleByNat positiveMagnitude
            (lfmExtensionWitnessValue negativeMagnitude positiveBound positiveRest))
          (lfkIntScaleByNat (positiveMagnitude * negativeMagnitude) positiveRest)) = true)
      (lfkIntLe
        (lfkIntAdd
          (lfkIntScaleByNat negativeMagnitude
            (lfmExtensionWitnessValue negativeMagnitude positiveBound positiveRest))
          (lfkIntScaleByNat (positiveMagnitude * negativeMagnitude) negativeBound))
        (lfkIntScaleByNat (positiveMagnitude * negativeMagnitude) negativeRest) = true) :=
  let commonScale := positiveMagnitude * negativeMagnitude
  let boundGap := lfkIntAdd positiveBound (lfkIntNegate positiveRest)
  let positiveClaim : lfkIntLe
      (lfkIntScaleByNat (positiveMagnitude * negativeMagnitude) positiveBound)
      (lfkIntAdd
        (lfkIntScaleByNat positiveMagnitude
          (lfmExtensionWitnessValue negativeMagnitude positiveBound positiveRest))
        (lfkIntScaleByNat (positiveMagnitude * negativeMagnitude) positiveRest)) = true :=
    Eq.trans
      (congrArg
        (fun probe => lfkIntLe (lfkIntScaleByNat commonScale positiveBound) probe)
        (Eq.trans
          (congrArg
            (fun probe => lfkIntAdd probe (lfkIntScaleByNat commonScale positiveRest))
            (Eq.trans
              (lfmIntScaleCompose positiveMagnitude negativeMagnitude boundGap).symm
              (lfkIntScaleAddDistrib commonScale positiveBound
                (lfkIntNegate positiveRest))))
          (lfkIntAddAssoc (lfkIntScaleByNat commonScale positiveBound)
            (lfkIntScaleByNat commonScale (lfkIntNegate positiveRest))
            (lfkIntScaleByNat commonScale positiveRest))))
      (lfmIntLeSelfPlusZero (lfkIntScaleByNat commonScale positiveBound)
        (lfkIntAdd (lfkIntScaleByNat commonScale (lfkIntNegate positiveRest))
          (lfkIntScaleByNat commonScale positiveRest))
        (Eq.trans
          (congrArg lfkIntIsZero
            (lfkIntScaleAddDistrib commonScale (lfkIntNegate positiveRest)
              positiveRest).symm)
          (lfmIntScalePreservesZero commonScale
            (lfmIntAddNegateSelfZero positiveRest))))
  let squaredScale := negativeMagnitude * negativeMagnitude
  let liftedBoundTerm := lfkIntScaleByNat squaredScale positiveBound
  let liftedNegatedRest := lfkIntScaleByNat squaredScale (lfkIntNegate positiveRest)
  let liftedRest := lfkIntScaleByNat squaredScale positiveRest
  let scaledNegativeBound := lfkIntScaleByNat commonScale negativeBound
  let scaledNegativeRest := lfkIntScaleByNat commonScale negativeRest
  let comboScaled : lfkIntLe
      (lfkIntScaleByNat negativeMagnitude
        (lfkIntAdd (lfkIntScaleByNat negativeMagnitude positiveBound)
          (lfkIntScaleByNat positiveMagnitude negativeBound)))
      (lfkIntScaleByNat negativeMagnitude
        (lfkIntAdd (lfkIntScaleByNat negativeMagnitude positiveRest)
          (lfkIntScaleByNat positiveMagnitude negativeRest))) = true :=
    lfkIntScaleLeMono negativeMagnitude comboWitness
  let lowerSplit : lfkIntScaleByNat negativeMagnitude
      (lfkIntAdd (lfkIntScaleByNat negativeMagnitude positiveBound)
        (lfkIntScaleByNat positiveMagnitude negativeBound))
      = lfkIntAdd liftedBoundTerm scaledNegativeBound :=
    (lfkIntScaleAddDistrib negativeMagnitude
        (lfkIntScaleByNat negativeMagnitude positiveBound)
        (lfkIntScaleByNat positiveMagnitude negativeBound)).trans
      (lfkIntAddCongr
        (lfmIntScaleCompose negativeMagnitude negativeMagnitude positiveBound).symm
        ((lfmIntScaleCompose negativeMagnitude positiveMagnitude negativeBound).symm.trans
          (congrArg (fun probe => lfkIntScaleByNat probe negativeBound)
            (Nat.mul_comm negativeMagnitude positiveMagnitude))))
  let upperSplit : lfkIntScaleByNat negativeMagnitude
      (lfkIntAdd (lfkIntScaleByNat negativeMagnitude positiveRest)
        (lfkIntScaleByNat positiveMagnitude negativeRest))
      = lfkIntAdd liftedRest scaledNegativeRest :=
    (lfkIntScaleAddDistrib negativeMagnitude
        (lfkIntScaleByNat negativeMagnitude positiveRest)
        (lfkIntScaleByNat positiveMagnitude negativeRest)).trans
      (lfkIntAddCongr
        (lfmIntScaleCompose negativeMagnitude negativeMagnitude positiveRest).symm
        ((lfmIntScaleCompose negativeMagnitude positiveMagnitude negativeRest).symm.trans
          (congrArg (fun probe => lfkIntScaleByNat probe negativeRest)
            (Nat.mul_comm negativeMagnitude positiveMagnitude))))
  let comboRewritten : lfkIntLe (lfkIntAdd liftedBoundTerm scaledNegativeBound)
      (lfkIntAdd liftedRest scaledNegativeRest) = true :=
    ((congrArg (fun probe => lfkIntLe probe (lfkIntAdd liftedRest scaledNegativeRest))
        lowerSplit.symm).trans
      (congrArg
        (fun probe => lfkIntLe
          (lfkIntScaleByNat negativeMagnitude
            (lfkIntAdd (lfkIntScaleByNat negativeMagnitude positiveBound)
              (lfkIntScaleByNat positiveMagnitude negativeBound))) probe)
        upperSplit.symm)).trans
      comboScaled
  let paddedCombo : lfkIntLe
      (lfkIntAdd (lfkIntAdd liftedBoundTerm scaledNegativeBound) liftedNegatedRest)
      (lfkIntAdd (lfkIntAdd liftedRest scaledNegativeRest) liftedNegatedRest) = true :=
    lfkIntAddLeAdd comboRewritten (lfmIntLeRefl liftedNegatedRest)
  let leftShuffle : lfkIntAdd (lfkIntAdd liftedBoundTerm scaledNegativeBound) liftedNegatedRest
      = lfkIntAdd (lfkIntAdd liftedBoundTerm liftedNegatedRest) scaledNegativeBound :=
    (lfkIntAddAssoc liftedBoundTerm scaledNegativeBound liftedNegatedRest).trans
      ((congrArg (fun probe => lfkIntAdd liftedBoundTerm probe)
          (lfkIntAddComm scaledNegativeBound liftedNegatedRest)).trans
        (lfkIntAddAssoc liftedBoundTerm liftedNegatedRest scaledNegativeBound).symm)
  let rightShuffle : lfkIntAdd (lfkIntAdd liftedRest scaledNegativeRest) liftedNegatedRest
      = lfkIntAdd scaledNegativeRest (lfkIntAdd liftedNegatedRest liftedRest) :=
    ((congrArg (fun probe => lfkIntAdd probe liftedNegatedRest)
        (lfkIntAddComm liftedRest scaledNegativeRest)).trans
      (lfkIntAddAssoc scaledNegativeRest liftedRest liftedNegatedRest)).trans
      (congrArg (fun probe => lfkIntAdd scaledNegativeRest probe)
        (lfkIntAddComm liftedRest liftedNegatedRest))
  let zeroTail : lfkIntIsZero (lfkIntAdd liftedNegatedRest liftedRest) = true :=
    (congrArg lfkIntIsZero
        (lfkIntScaleAddDistrib squaredScale (lfkIntNegate positiveRest)
          positiveRest).symm).trans
      (lfmIntScalePreservesZero squaredScale (lfmIntAddNegateSelfZero positiveRest))
  let shuffledCombo : lfkIntLe
      (lfkIntAdd (lfkIntAdd liftedBoundTerm liftedNegatedRest) scaledNegativeBound)
      (lfkIntAdd scaledNegativeRest (lfkIntAdd liftedNegatedRest liftedRest)) = true :=
    (congrArg
        (fun probe => lfkIntLe
          (lfkIntAdd (lfkIntAdd liftedBoundTerm liftedNegatedRest) scaledNegativeBound)
          probe)
        rightShuffle).symm.trans
      ((congrArg
          (fun probe => lfkIntLe probe
            (lfkIntAdd (lfkIntAdd liftedRest scaledNegativeRest) liftedNegatedRest))
          leftShuffle.symm).trans
        paddedCombo)
  let droppedZero : lfkIntLe
      (lfkIntAdd (lfkIntAdd liftedBoundTerm liftedNegatedRest) scaledNegativeBound)
      scaledNegativeRest = true :=
    lfmIntLePlusZeroDrop
      (lfkIntAdd (lfkIntAdd liftedBoundTerm liftedNegatedRest) scaledNegativeBound)
      scaledNegativeRest (lfkIntAdd liftedNegatedRest liftedRest) zeroTail shuffledCombo
  let witnessSplit : lfkIntScaleByNat negativeMagnitude
      (lfmExtensionWitnessValue negativeMagnitude positiveBound positiveRest)
      = lfkIntAdd liftedBoundTerm liftedNegatedRest :=
    (lfmIntScaleCompose negativeMagnitude negativeMagnitude boundGap).symm.trans
      (lfkIntScaleAddDistrib squaredScale positiveBound (lfkIntNegate positiveRest))
  let negativeClaim : lfkIntLe
      (lfkIntAdd
        (lfkIntScaleByNat negativeMagnitude
          (lfmExtensionWitnessValue negativeMagnitude positiveBound positiveRest))
        (lfkIntScaleByNat (positiveMagnitude * negativeMagnitude) negativeBound))
      (lfkIntScaleByNat (positiveMagnitude * negativeMagnitude) negativeRest) = true :=
    (congrArg
        (fun probe => lfkIntLe (lfkIntAdd probe scaledNegativeBound) scaledNegativeRest)
        witnessSplit).trans
      droppedZero
  And.intro positiveClaim negativeClaim

/-! ## The round-extension Prop (stated, uninhabited here) -/

/-- Extract the bare constraints of a certified-row list (cons-only). -/
def lfmConstraintsOfRows : List LfmCertifiedRow → List LfkConstraint
  | List.nil => List.nil
  | rowHead :: rowTail => rowHead.constraint :: lfmConstraintsOfRows rowTail

/-- The round-extension Prop: if some integer environment satisfies the ROUND
OUTPUT at a positive denominator (the checker's `lfkScaleBoundsForDenominator`
encoding of a rational point), then some integer environment satisfies the ROUND
INPUT at a positive denominator, over arbitrary certified rows.  This is the
backward direction of Fourier–Motzkin equisatisfiability, whose constructive
witness is the cleared max-lower or min-upper endpoint in the weak case and the
midpoint in the strict case; `lfmOnePairExtensionCore` above is the one-pair
algebra it iterates.  The Prop is stated but not inhabited here.

As written it is unguarded and too strong: `FourierMotzkinExtension` refutes it on
`[x = 0, x >= 1]`, where an equality row occupies a single sign bucket and its
opposite half is dropped.  Restricting to inequality input rows makes it hold, and
that guarded form yields `lfkFarkasCompletenessStatement` downstream together with
the grounding theorem `lfmFinalRowsAreGround`.  This file records
`fxDissatArith_hasFourierMotzkinCompleteness = false`. -/
def lfmRoundExtensionStatement : Prop :=
  ∀ (variableIndex : Nat) (rows : List LfmCertifiedRow)
    (outputDenominatorPred : Nat) (outputEnv : List LfkInt),
    lfkSatisfiesSystem outputEnv
      (lfkScaleBoundsForDenominator (outputDenominatorPred + 1)
        (lfmConstraintsOfRows (lfmEliminationRound variableIndex rows))) = true →
    ∃ (inputDenominatorPred : Nat) (inputEnv : List LfkInt),
      lfkSatisfiesSystem inputEnv
        (lfkScaleBoundsForDenominator (inputDenominatorPred + 1)
          (lfmConstraintsOfRows rows)) = true

/-- The certificate-composition pipeline is fully proven, zero-axiom: certified
rows with unit-provenance seeds, the elimination round with provenance threading
(bilinearity), the fuel driver, the grounding theorem, and the composition theorem
`lfmFoundContradictionCertifies` (finder output is checker-accepted verbatim). -/
def fxDissatArith_hasFmCertificateComposition : Bool := true

/-- Completeness (`lfkFarkasCompletenessStatement`) is not proven within this file:
the round-extension Prop `lfmRoundExtensionStatement` is stated but uninhabited
here.  Its inequality-guarded form is inhabited, and completeness obtained, in
`FourierMotzkinExtension`. -/
def fxDissatArith_hasFourierMotzkinCompleteness : Bool := false

/-! ## Smokes — finder → checker fires and clean scans (Bool `rfl` pins and `#eval`s) -/

/-- Run the finder and hand whatever certificate it returns to the sibling's
checker; `false` when the finder returns nothing. -/
def lfmCheckFoundCertificate (system : List LfkConstraint) : Bool :=
  match lfmFindRefutationCertificate system with
  | Option.none => false
  | Option.some certificate => lfkCheckRefutation certificate system

/-- Did the finder come back empty-handed? -/
def lfmScanFoundNothing (system : List LfkConstraint) : Bool :=
  match lfmFindRefutationCertificate system with
  | Option.none => true
  | Option.some _certificate => false

/-- Smoke fixture: the two-variable chain `x >= 1`, `-x + y >= 1`, `-y >= -1` —
infeasible (the first two force `y >= 2`, the third caps `y <= 1`). -/
def lfmSmokeTwoVariableChainSystem : List LfkConstraint :=
  [LfkConstraint.mk [LfkInt.mk 1 0] (LfkInt.mk 1 0) LfkRelation.isGreaterOrEqual,
   LfkConstraint.mk [LfkInt.mk 0 1, LfkInt.mk 1 0] (LfkInt.mk 1 0)
     LfkRelation.isGreaterOrEqual,
   LfkConstraint.mk [lfkIntZero, LfkInt.mk 0 1] (LfkInt.mk 0 1)
     LfkRelation.isGreaterOrEqual]

/-- Smoke fixture (FALSE case): the chain relaxed to `-y >= -3` — satisfiable
by `(x, y) = (1, 2)`. -/
def lfmSmokeRelaxedChainSystem : List LfkConstraint :=
  [LfkConstraint.mk [LfkInt.mk 1 0] (LfkInt.mk 1 0) LfkRelation.isGreaterOrEqual,
   LfkConstraint.mk [LfkInt.mk 0 1, LfkInt.mk 1 0] (LfkInt.mk 1 0)
     LfkRelation.isGreaterOrEqual,
   LfkConstraint.mk [lfkIntZero, LfkInt.mk 0 1] (LfkInt.mk 0 3)
     LfkRelation.isGreaterOrEqual]

/-- Smoke fixture: the environment `(1, 2)` witnessing the relaxed chain. -/
def lfmSmokeRelaxedChainEnv : List LfkInt := [LfkInt.mk 1 0, LfkInt.mk 2 0]

/-- Kernel pin: the finder's certificate for the sibling's `x >= 1, -x >= 0`
fixture CHECKS end-to-end (finder → checker). -/
theorem lfmSmokeSiblingContradictoryFiredPin :
    lfmCheckFoundCertificate lfkSmokeContradictorySystem = true := rfl

/-- Kernel pin: the finder composes exactly the sibling's own `[1, 1]`. -/
theorem lfmSmokeSiblingContradictoryCertificatePin :
    lfmFindRefutationCertificate lfkSmokeContradictorySystem
      = Option.some [1, 1] := rfl

/-- Kernel pin: the strictness fixture `x > 0, -x >= 0` fires end-to-end. -/
theorem lfmSmokeSiblingStrictFiredPin :
    lfmCheckFoundCertificate lfkSmokeStrictSystem = true := rfl

/-- Kernel pin: on the equality fixture `x = 3, -x >= -2` the finder composes
the two-slot expanded certificate `[1, 0, 1]` itself (forward slot weighted,
flipped slot unused, inequality slot weighted). -/
theorem lfmSmokeSiblingEqualityCertificatePin :
    lfmFindRefutationCertificate lfkSmokeEqualitySystem
      = Option.some [1, 0, 1] := rfl

/-- Kernel pin: the equality fixture fires end-to-end. -/
theorem lfmSmokeSiblingEqualityFiredPin :
    lfmCheckFoundCertificate lfkSmokeEqualitySystem = true := rfl

/-- Kernel pin: the two-variable chain is refuted with the composed
`[1, 1, 1]` (two elimination rounds, provenance added across the cross pair). -/
theorem lfmSmokeTwoVariableChainCertificatePin :
    lfmFindRefutationCertificate lfmSmokeTwoVariableChainSystem
      = Option.some [1, 1, 1] := rfl

/-- Kernel pin: the chain's found certificate CHECKS against the original. -/
theorem lfmSmokeTwoVariableChainFiredPin :
    lfmCheckFoundCertificate lfmSmokeTwoVariableChainSystem = true := rfl

/-- Kernel pin (FALSE case): the sibling's satisfiable triple scans clean —
the eliminator returns NO certificate. -/
theorem lfmSmokeSatisfiableTripleCleanPin :
    lfmScanFoundNothing lfkSmokeSatisfiableTriple = true := rfl

/-- Kernel pin (FALSE case): the sibling's satisfiable pair scans clean. -/
theorem lfmSmokeSatisfiablePairCleanPin :
    lfmScanFoundNothing lfkSmokeSatisfiablePair = true := rfl

/-- Kernel pin (FALSE case): the relaxed chain scans clean. -/
theorem lfmSmokeRelaxedChainCleanPin :
    lfmScanFoundNothing lfmSmokeRelaxedChainSystem = true := rfl

/-- Kernel pin: the relaxed chain really is satisfied by `(1, 2)`. -/
theorem lfmSmokeRelaxedChainEnvPin :
    lfkSatisfiesSystem lfmSmokeRelaxedChainEnv lfmSmokeRelaxedChainSystem = true := rfl

/-- Kernel fire of the one-pair extension core on the concrete pair
`2x + 1 >= 5` (i.e. `x >= 2`) and `-3x + 10 >= 1` (i.e. `x <= 3`): the combo
hypothesis is discharged by `rfl` and both scaled-parent conclusions hold for
the witness `v = 3 * (5 - 1) = 12` — the cleared lower endpoint `x = 2` at the
common scale `2 * 3 = 6`. -/
theorem lfmSmokeOnePairCoreFired :
    And
      (lfkIntLe (lfkIntScaleByNat (2 * 3) (LfkInt.mk 5 0))
        (lfkIntAdd
          (lfkIntScaleByNat 2
            (lfmExtensionWitnessValue 3 (LfkInt.mk 5 0) (LfkInt.mk 1 0)))
          (lfkIntScaleByNat (2 * 3) (LfkInt.mk 1 0))) = true)
      (lfkIntLe
        (lfkIntAdd
          (lfkIntScaleByNat 3
            (lfmExtensionWitnessValue 3 (LfkInt.mk 5 0) (LfkInt.mk 1 0)))
          (lfkIntScaleByNat (2 * 3) (LfkInt.mk 1 0)))
        (lfkIntScaleByNat (2 * 3) (LfkInt.mk 10 0)) = true) :=
  lfmOnePairExtensionCore 2 3 (LfkInt.mk 1 0) (LfkInt.mk 5 0) (LfkInt.mk 10 0)
    (LfkInt.mk 1 0) rfl

-- End-to-end: finder certificate for x >= 1, -x >= 0 CHECKS. Expect: true
#eval lfmCheckFoundCertificate lfkSmokeContradictorySystem
-- The composed certificate itself. Expect: some [1, 1]
#eval lfmFindRefutationCertificate lfkSmokeContradictorySystem
-- Strictness fixture end-to-end. Expect: true
#eval lfmCheckFoundCertificate lfkSmokeStrictSystem
-- Equality fixture: the finder composes the two-slot route. Expect: some [1, 0, 1]
#eval lfmFindRefutationCertificate lfkSmokeEqualitySystem
-- Two-variable chain end-to-end. Expect: true
#eval lfmCheckFoundCertificate lfmSmokeTwoVariableChainSystem
-- Its composed certificate. Expect: some [1, 1, 1]
#eval lfmFindRefutationCertificate lfmSmokeTwoVariableChainSystem
-- FALSE case: satisfiable triple — the eliminator finds nothing. Expect: true
#eval lfmScanFoundNothing lfkSmokeSatisfiableTriple
-- FALSE case: satisfiable pair — finder output. Expect: none
#eval lfmFindRefutationCertificate lfkSmokeSatisfiablePair
-- FALSE case: relaxed chain scans clean. Expect: true
#eval lfmScanFoundNothing lfmSmokeRelaxedChainSystem
-- Satisfiable sanity: (1, 2) satisfies the relaxed chain. Expect: true
#eval lfkSatisfiesSystem lfmSmokeRelaxedChainEnv lfmSmokeRelaxedChainSystem

end FX1Poly.ComputerAlgebra
