import FX1Poly.ComputerAlgebra.Decision.FourierMotzkinExtension

/-! # FX1Poly/ComputerAlgebra/Decision/PresburgerCooper — the LAST ARITH WALL:
    Cooper quantifier elimination over the lane's pair integers, zero-axiom

The DISSAT-ARITH lane's Presburger wall
(`lfkPresburgerDecisionStatement`, LinearFarkasCertificate.lean, owner
`fxDissatArith_hasPresburgerDecision := false`) demands full decidability of
integer satisfiability for linear-constraint systems.  Farkas/Fourier–Motzkin
certificates CANNOT close it: `2x = 1` is rationally feasible (hence
certificate-free) yet integer-unsatisfiable.  The fix, after Cooper 1972 as
mechanized by Chaieb–Nipkow (LPAR'05) and Norrish (TPHOLs'03), is quantifier
elimination with DIVISIBILITY atoms.  This brick delivers the full pipeline:

  * **(A) Syntax + semantics** — reflected Presburger formulas over `LfkInt`
    pair integers: linear terms `PcqTerm` (dense coefficient vector reusing
    `lfkDotProduct` + explicit constant), strict-inequality atoms in the
    lane's succ-le encoding, divisibility `(mp+1) | t` with a structurally
    positive literal modulus, negated divisibility kept as an atom (the
    Chaieb–Nipkow NNF invariant), conjunction/disjunction/negation/exists in
    de Bruijn discipline (`pcqInterp`); an executable ground evaluator
    (`pcqQfEval`) with TWO-SIDED soundness against the Prop semantics.
  * **(B) Normalization with certificates** — negation normal form
    (`pcqNnfOfQf`, equivalence both directions, negation surviving only on
    divisibility), and unitarization of the bound variable: the global scale
    is the PRODUCT of the per-atom pivot-coefficient magnitudes (any common
    multiple works — no gcd/lcm, hence no division walls), the per-atom
    factor is recovered by the counting divider against the witnessed
    divides-the-product certificate, and the whole U-step is recorded as ONE
    added `L | x` atom (`pcqSeparate`, equivalence both directions per
    Chaieb–Nipkow fact (2)/(3)).
  * **(C) THE ELIMINATION STEP** (`pcqCooperElimination`) — for a unitary
    matrix `m` with pivot `x`:
      `(∃ x, holds x m)  ↔  (⋁_{j=1..δ} holds j (minusInf m))
                            ∨ (⋁_{b ∈ B} ⋁_{j=1..δ} holds (b + j) m)`
    BOTH directions over the Prop semantics, `δ := pcqDelta m` the product of
    all divisibility moduli.  The proof follows the brief's skeleton
    constructively: shift-invariance of `minusInf` by `δ`-multiples
    (periodicity, Chaieb–Nipkow (7)), agreement of `m` with `minusInf m`
    below a computed threshold ((6)), the descent lemma ((9)) with the
    lower-bound window extraction, iterated descent below the threshold, and
    the counting-divider window reduction into `[1..δ]`.  Every case split is
    on a computed Bool (`pcqMatrixEval`, `pcqWindowTest`) — no classical
    choice anywhere.
  * **(D) THE FULL DECISION** — `pcqEliminate` recurses inside-out
    (structural on the formula; the exists case runs
    NNF → separate → `pcqCooperStep`), producing a quantifier-free
    equivalent; `pcqDecide` evaluates it in the empty environment.
    Soundness and completeness are two-sided
    (`pcqDecideTrueSound` / `pcqDecideFalseComplete`).  The lane wall
    statement `lfkPresburgerDecisionStatement` is then confronted VERBATIM
    and INHABITED (`pcqPresburgerDecisionHolds`): each constraint row
    translates atom-for-atom (`>=`/`>`/`=` via the succ-le encoding, the SAME
    `lfkDotProduct`), the system closes under `n := pcqSystemVarCount`
    inner existentials (`pcqFexN`), and truncation/padding semantics make
    satisfaction depend only on the first `n` variables.

Fires (kernel-decided, tiny deltas) live in the sibling
`PresburgerCooperFires.lean`: the `2x = 1` integrality gap decides FALSE
(the lane's signature separator), `∃x (3 | x ∧ x > 5)` decides TRUE, a
two-quantifier instance, and negative controls.

## Zero-axiom discipline

Init only plus the three sibling imports (`LinearFarkasCertificate`,
`FourierMotzkinCompleteness`, `FourierMotzkinExtension` — reusing their
probed-clean Nat/LfkInt/dot-product kits).  Structural recursion throughout
(the counting divider recurses on the dividend; formula recursions are
structural); no `WellFounded.fix`.  No `propext`, `Quot.sound`,
`Classical.choice`, `sorry`, `native_decide`, `funext`, `omega`, no `decide`
on `Prop`, no catch-all match arms, no `List.append`, no `Int`, no
`Nat.sub/mod/div/min/max` (counting divider + `lfmNatDelta` witnessed
differences instead).  Per-declaration gate in
`FX1PolyAudit/ComputerAlgebra/Decision/PresburgerCooper.lean`. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace FX1Poly.ComputerAlgebra

/-! ## Stage 0a — Nat kit additions (counting divider, cancellation, shapes) -/

/-- Structural predecessor (total; `0 ↦ 0`). -/
def pcqNatPred : Nat → Nat
  | Nat.zero => Nat.zero
  | Nat.succ predecessorValue => predecessorValue

/-- On positives the predecessor undoes the successor. -/
theorem pcqNatPredSucc : ∀ (value : Nat), Nat.ble 1 value = true →
    pcqNatPred value + 1 = value
  | Nat.zero, contradictoryWitness => Bool.noConfusion contradictoryWitness
  | Nat.succ _predecessorValue, _positiveWitness => rfl

/-- A left addend of a zero sum is zero. -/
theorem pcqNatSumZeroLeft : ∀ (leftValue rightValue : Nat),
    leftValue + rightValue = 0 → leftValue = 0
  | _leftValue, Nat.zero, sumEq => sumEq
  | _leftValue, Nat.succ _rightPred, sumEq => Nat.noConfusion sumEq

/-- Right cancellation for Nat addition (via commutation and the sibling left
cancellation). -/
theorem pcqNatAddRightCancel (sharedTerm leftValue rightValue : Nat)
    (sumEq : leftValue + sharedTerm = rightValue + sharedTerm) :
    leftValue = rightValue :=
  lfkNatAddLeftCancel sharedTerm leftValue rightValue
    ((Nat.add_comm sharedTerm leftValue).trans
      (sumEq.trans (Nat.add_comm rightValue sharedTerm)))

/-- Left cancellation of addition inside `le` (structural on the shared
addend; the library corner is on the banned list). -/
theorem pcqNatLeCancelAddLeft : ∀ (sharedTerm leftValue rightValue : Nat),
    Nat.le (sharedTerm + leftValue) (sharedTerm + rightValue) →
    Nat.le leftValue rightValue
  | Nat.zero, leftValue, rightValue, boundWitness =>
      lfkNatLeCongr (Nat.zero_add leftValue).symm (Nat.zero_add rightValue).symm boundWitness
  | Nat.succ sharedPred, leftValue, rightValue, boundWitness =>
      pcqNatLeCancelAddLeft sharedPred leftValue rightValue
        (Nat.le_of_succ_le_succ
          (lfkNatLeCongr (Nat.succ_add sharedPred leftValue).symm
            (Nat.succ_add sharedPred rightValue).symm boundWitness))

/-- `le` plus disequality tightens to a strict (succ-le) bound (double
structural recursion; `Nat.beq` on successors reduces definitionally). -/
theorem pcqNatSuccLeOfLeNe : ∀ (smallValue bigValue : Nat),
    Nat.le smallValue bigValue → Nat.beq smallValue bigValue = false →
    Nat.le (smallValue + 1) bigValue
  | Nat.zero, Nat.zero, _boundWitness, neWitness => Bool.noConfusion neWitness
  | Nat.zero, Nat.succ bigPred, _boundWitness, _neWitness =>
      Nat.succ_le_succ (Nat.zero_le bigPred)
  | Nat.succ _smallPred, Nat.zero, boundWitness, _neWitness => nomatch boundWitness
  | Nat.succ smallPred, Nat.succ bigPred, boundWitness, neWitness =>
      Nat.succ_le_succ
        (pcqNatSuccLeOfLeNe smallPred bigPred (Nat.le_of_succ_le_succ boundWitness) neWitness)

/-- `le` into a successor bound plus disequality with that bound drops to the
predecessor bound. -/
theorem pcqNatLeOfLeSuccNe : ∀ (smallValue bigPred : Nat),
    Nat.le smallValue (bigPred + 1) → Nat.beq smallValue (bigPred + 1) = false →
    Nat.le smallValue bigPred
  | Nat.zero, bigPred, _boundWitness, _neWitness => Nat.zero_le bigPred
  | Nat.succ smallPred, bigPred, boundWitness, neWitness =>
      pcqNatSuccLeOfLeNe smallPred bigPred (Nat.le_of_succ_le_succ boundWitness) neWitness

/-- A positive multiple dominates the multiplier: `n <= n * (dp + 1)`. -/
theorem pcqNatLeMulPositive (baseValue deltaPred : Nat) :
    Nat.le baseValue (baseValue * (deltaPred + 1)) :=
  lfkNatLeCongr (Nat.mul_one baseValue).symm rfl
    (lfkNatMulLeMulLeft baseValue (Nat.succ_le_succ (Nat.zero_le deltaPred)))

/-- A nonzero Nat has a successor shape (Bool-equality form). -/
theorem pcqNatNonZeroShape : ∀ (value : Nat), Nat.beq value 0 = false →
    ∃ (predecessorValue : Nat), value = predecessorValue + 1
  | Nat.zero, contradictoryWitness => Bool.noConfusion contradictoryWitness
  | Nat.succ predecessorValue, _nonZeroWitness => Exists.intro predecessorValue rfl

/-! ## Stage 0b — THE COUNTING DIVIDER (structural on the dividend; no
`Nat.mod`/`Nat.div`/`Nat.sub`; certificates by plain induction) -/

/-- Remainder of `value` modulo `modulusPred + 1`, computed by counting: each
increment either wraps to zero (when the running remainder hits the top) or
steps up. -/
def pcqNatModCounting (modulusPred : Nat) : Nat → Nat
  | Nat.zero => Nat.zero
  | Nat.succ smallerValue =>
      let previousRemainder := pcqNatModCounting modulusPred smallerValue
      cond (Nat.beq previousRemainder modulusPred) Nat.zero (previousRemainder + 1)

/-- Quotient of `value` by `modulusPred + 1`, counting wraps of the running
remainder. -/
def pcqNatDivCounting (modulusPred : Nat) : Nat → Nat
  | Nat.zero => Nat.zero
  | Nat.succ smallerValue =>
      let previousRemainder := pcqNatModCounting modulusPred smallerValue
      cond (Nat.beq previousRemainder modulusPred)
        (pcqNatDivCounting modulusPred smallerValue + 1)
        (pcqNatDivCounting modulusPred smallerValue)

/-- The counting remainder never exceeds `modulusPred`. -/
theorem pcqNatModCountingBound : ∀ (modulusPred value : Nat),
    Nat.le (pcqNatModCounting modulusPred value) modulusPred
  | modulusPred, Nat.zero => Nat.zero_le modulusPred
  | modulusPred, Nat.succ smallerValue =>
      match lfmBoolCases (Nat.beq (pcqNatModCounting modulusPred smallerValue) modulusPred) with
      | Or.inl wrapTrue =>
          lfkNatLeCongr
            (congrArg (fun probe => cond probe Nat.zero
              (pcqNatModCounting modulusPred smallerValue + 1)) wrapTrue)
            rfl (Nat.zero_le modulusPred)
      | Or.inr wrapFalse =>
          lfkNatLeCongr
            (congrArg (fun probe => cond probe Nat.zero
              (pcqNatModCounting modulusPred smallerValue + 1)) wrapFalse)
            rfl
            (pcqNatSuccLeOfLeNe (pcqNatModCounting modulusPred smallerValue) modulusPred
              (pcqNatModCountingBound modulusPred smallerValue) wrapFalse)

/-- THE RECOVERY SPEC: modulus times counting quotient plus counting
remainder recovers the dividend. -/
theorem pcqNatDivModRecovers : ∀ (modulusPred value : Nat),
    (modulusPred + 1) * pcqNatDivCounting modulusPred value
      + pcqNatModCounting modulusPred value = value
  | _modulusPred, Nat.zero => rfl
  | modulusPred, Nat.succ smallerValue =>
      match lfmBoolCases (Nat.beq (pcqNatModCounting modulusPred smallerValue) modulusPred) with
      | Or.inl wrapTrue =>
          let smallerQuotient := pcqNatDivCounting modulusPred smallerValue
          let smallerRemainder := pcqNatModCounting modulusPred smallerValue
          let remainderTop : smallerRemainder = modulusPred :=
            lfkNatEqOfBeq smallerRemainder modulusPred wrapTrue
          let headStep : (modulusPred + 1) * pcqNatDivCounting modulusPred (Nat.succ smallerValue)
              + pcqNatModCounting modulusPred (Nat.succ smallerValue)
              = (modulusPred + 1) * (smallerQuotient + 1) + Nat.zero :=
            lfkNatAddCongr
              (congrArg (fun probe => (modulusPred + 1)
                * cond probe (smallerQuotient + 1) smallerQuotient) wrapTrue)
              (congrArg (fun probe => cond probe Nat.zero (smallerRemainder + 1)) wrapTrue)
          let expandStep : (modulusPred + 1) * (smallerQuotient + 1)
              = (modulusPred + 1) * smallerQuotient + (modulusPred + 1) :=
            (Nat.mul_add (modulusPred + 1) smallerQuotient 1).trans
              (congrArg (fun probe => (modulusPred + 1) * smallerQuotient + probe)
                (Nat.mul_one (modulusPred + 1)))
          let regroupStep : (modulusPred + 1) * smallerQuotient + (modulusPred + 1)
              = ((modulusPred + 1) * smallerQuotient + modulusPred) + 1 :=
            (Nat.add_assoc ((modulusPred + 1) * smallerQuotient) modulusPred 1).symm
          let recoverStep : ((modulusPred + 1) * smallerQuotient + modulusPred) + 1
              = smallerValue + 1 :=
            congrArg (fun probe => probe + 1)
              ((congrArg (fun probe => (modulusPred + 1) * smallerQuotient + probe)
                  remainderTop.symm).trans
                (pcqNatDivModRecovers modulusPred smallerValue))
          headStep.trans (expandStep.trans (regroupStep.trans recoverStep))
      | Or.inr wrapFalse =>
          let smallerQuotient := pcqNatDivCounting modulusPred smallerValue
          let smallerRemainder := pcqNatModCounting modulusPred smallerValue
          let headStep : (modulusPred + 1) * pcqNatDivCounting modulusPred (Nat.succ smallerValue)
              + pcqNatModCounting modulusPred (Nat.succ smallerValue)
              = (modulusPred + 1) * smallerQuotient + (smallerRemainder + 1) :=
            lfkNatAddCongr
              (congrArg (fun probe => (modulusPred + 1)
                * cond probe (smallerQuotient + 1) smallerQuotient) wrapFalse)
              (congrArg (fun probe => cond probe Nat.zero (smallerRemainder + 1)) wrapFalse)
          headStep.trans
            ((Nat.add_assoc ((modulusPred + 1) * smallerQuotient) smallerRemainder 1).symm.trans
              (congrArg (fun probe => probe + 1) (pcqNatDivModRecovers modulusPred smallerValue)))

/-- UNIQUE REMAINDER ZERO: a below-modulus value that completes a multiple to
another multiple must vanish (double structural recursion on the two
quotients). -/
theorem pcqNatUniqueRemainderZero : ∀ (modulusPred remainderValue innerQuotient
      outerQuotient : Nat),
    remainderValue + (modulusPred + 1) * innerQuotient = (modulusPred + 1) * outerQuotient →
    Nat.le remainderValue modulusPred → remainderValue = 0
  | _modulusPred, _remainderValue, Nat.zero, Nat.zero, mixedEq, _boundWitness => mixedEq
  | modulusPred, remainderValue, Nat.zero, Nat.succ outerPred, mixedEq, boundWitness =>
      let modulusBelow : Nat.le (modulusPred + 1) remainderValue :=
        lfkNatLeCongr rfl mixedEq
          (lreNatLeAddLeft ((modulusPred + 1) * outerPred) (modulusPred + 1))
      False.elim
        (lfkNatSuccLeSelfFalse modulusPred (Nat.le_trans modulusBelow boundWitness))
  | _modulusPred, remainderValue, Nat.succ _innerPred, Nat.zero, mixedEq, _boundWitness =>
      pcqNatSumZeroLeft remainderValue _ mixedEq
  | modulusPred, remainderValue, Nat.succ innerPred, Nat.succ outerPred, mixedEq,
      boundWitness =>
      pcqNatUniqueRemainderZero modulusPred remainderValue innerPred outerPred
        (pcqNatAddRightCancel (modulusPred + 1)
          (remainderValue + (modulusPred + 1) * innerPred)
          ((modulusPred + 1) * outerPred)
          ((Nat.add_assoc remainderValue ((modulusPred + 1) * innerPred)
              (modulusPred + 1)).trans mixedEq))
        boundWitness

/-! ## Stage 0c — Nat divisibility (witnessed multiples of the product) -/

/-- `divisor` divides `target` — the multiplicative witness Prop. -/
def pcqNatDividesProp (divisor target : Nat) : Prop :=
  ∃ (cofactor : Nat), divisor * cofactor = target

/-- Divisibility extends along a right factor. -/
theorem pcqNatDividesMulRight (divisor target extraFactor : Nat)
    (dividesWitness : pcqNatDividesProp divisor target) :
    pcqNatDividesProp divisor (target * extraFactor) :=
  match dividesWitness with
  | Exists.intro cofactor cofactorEq =>
      Exists.intro (cofactor * extraFactor)
        ((lfkNatMulAssoc divisor cofactor extraFactor).symm.trans
          (congrArg (fun probe => probe * extraFactor) cofactorEq))

/-- Divisibility extends along a left factor. -/
theorem pcqNatDividesMulLeft (divisor target extraFactor : Nat)
    (dividesWitness : pcqNatDividesProp divisor target) :
    pcqNatDividesProp divisor (extraFactor * target) :=
  match pcqNatDividesMulRight divisor target extraFactor dividesWitness with
  | Exists.intro cofactor cofactorEq =>
      Exists.intro cofactor (cofactorEq.trans (Nat.mul_comm target extraFactor))

/-- Every Nat divides itself. -/
theorem pcqNatDividesSelf (divisor : Nat) : pcqNatDividesProp divisor divisor :=
  Exists.intro 1 (Nat.mul_one divisor)

/-- EXACT COUNTING QUOTIENT: when the divisor is positive and divides the
target, the counting quotient recovers the exact cofactor
(`quotient * divisor = target`). -/
theorem pcqNatCountingQuotientExact (divisorPred target : Nat)
    (dividesWitness : pcqNatDividesProp (divisorPred + 1) target) :
    pcqNatDivCounting divisorPred target * (divisorPred + 1) = target :=
  match dividesWitness with
  | Exists.intro cofactor cofactorEq =>
      let remainderZero : pcqNatModCounting divisorPred target = 0 :=
        pcqNatUniqueRemainderZero divisorPred (pcqNatModCounting divisorPred target)
          (pcqNatDivCounting divisorPred target) cofactor
          (((Nat.add_comm (pcqNatModCounting divisorPred target)
              ((divisorPred + 1) * pcqNatDivCounting divisorPred target)).trans
            (pcqNatDivModRecovers divisorPred target)).trans cofactorEq.symm)
          (pcqNatModCountingBound divisorPred target)
      (Nat.mul_comm (pcqNatDivCounting divisorPred target) (divisorPred + 1)).trans
        (((congrArg
            (fun probe => (divisorPred + 1) * pcqNatDivCounting divisorPred target + probe)
            remainderZero).symm).trans
          (pcqNatDivModRecovers divisorPred target))

/-! ## Stage 0d — Bool kit additions -/

/-- Destruct a true disjunction. -/
theorem pcqBoolOrDestructTrue : ∀ (leftFlag rightFlag : Bool),
    (leftFlag || rightFlag) = true → Or (leftFlag = true) (rightFlag = true)
  | true, true, _trivialWitness => Or.inl rfl
  | true, false, _trivialWitness => Or.inl rfl
  | false, true, _trivialWitness => Or.inr rfl
  | false, false, contradictoryWitness => Bool.noConfusion contradictoryWitness

/-- Destruct a false disjunction. -/
theorem pcqBoolOrDestructFalse : ∀ (leftFlag rightFlag : Bool),
    (leftFlag || rightFlag) = false → And (leftFlag = false) (rightFlag = false)
  | true, true, contradictoryWitness => Bool.noConfusion contradictoryWitness
  | true, false, contradictoryWitness => Bool.noConfusion contradictoryWitness
  | false, true, contradictoryWitness => Bool.noConfusion contradictoryWitness
  | false, false, _trivialWitness => And.intro rfl rfl

/-- Assemble a true disjunction from the left. -/
theorem pcqBoolOrIntroLeft : ∀ (leftFlag rightFlag : Bool),
    leftFlag = true → (leftFlag || rightFlag) = true
  | true, true, _trivialWitness => rfl
  | true, false, _trivialWitness => rfl
  | false, _rightFlag, contradictoryWitness => Bool.noConfusion contradictoryWitness

/-- Assemble a true disjunction from the right. -/
theorem pcqBoolOrIntroRight : ∀ (leftFlag rightFlag : Bool),
    rightFlag = true → (leftFlag || rightFlag) = true
  | true, true, _trivialWitness => rfl
  | false, true, _trivialWitness => rfl
  | true, false, contradictoryWitness => Bool.noConfusion contradictoryWitness
  | false, false, contradictoryWitness => Bool.noConfusion contradictoryWitness

/-- Destruct a false conjunction. -/
theorem pcqBoolAndDestructFalse : ∀ (leftFlag rightFlag : Bool),
    (leftFlag && rightFlag) = false → Or (leftFlag = false) (rightFlag = false)
  | true, true, contradictoryWitness => Bool.noConfusion contradictoryWitness
  | true, false, _trivialWitness => Or.inr rfl
  | false, true, _trivialWitness => Or.inl rfl
  | false, false, _trivialWitness => Or.inl rfl

/-- A false negation forces a true flag. -/
theorem pcqBoolNotFalseImpliesTrue : ∀ (flag : Bool), Bool.not flag = false → flag = true
  | true, _trivialWitness => rfl
  | false, contradictoryWitness => Bool.noConfusion contradictoryWitness

/-- Assemble a true negation. -/
theorem pcqBoolNotTrueOfFalse : ∀ (flag : Bool), flag = false → Bool.not flag = true
  | false, _trivialWitness => rfl
  | true, contradictoryWitness => Bool.noConfusion contradictoryWitness

/-! ## Stage 0e — LfkInt kit additions (order corners, cross-eq congruence) -/

/-- Strict order plus reverse weak order is absurd. -/
theorem pcqIntLtLeAbsurd {lowerValue higherValue : LfkInt}
    (strictWitness : lfkIntLt lowerValue higherValue = true)
    (reverseWitness : lfkIntLe higherValue lowerValue = true) : False :=
  lfkNatSuccLeSelfFalse (lowerValue.positivePart + higherValue.negativePart)
    (Nat.le_trans
      (lfkNatLeOfBle (lowerValue.positivePart + higherValue.negativePart + 1)
        (higherValue.positivePart + lowerValue.negativePart) strictWitness)
      (lfkNatLeOfBle (higherValue.positivePart + lowerValue.negativePart)
        (lowerValue.positivePart + higherValue.negativePart) reverseWitness))

/-- A failed strict comparison flips to the reverse weak comparison. -/
theorem pcqIntLtFalseGivesLe {leftValue rightValue : LfkInt}
    (falseWitness : lfkIntLt leftValue rightValue = false) :
    lfkIntLe rightValue leftValue = true :=
  lfkNatBleOfLe (rightValue.positivePart + leftValue.negativePart)
    (leftValue.positivePart + rightValue.negativePart)
    (Nat.le_of_succ_le_succ
      (lfkNatLeOfBle (rightValue.positivePart + leftValue.negativePart + 1)
        (leftValue.positivePart + rightValue.negativePart + 1)
        (lfmNatBleFalseFlipStrict (leftValue.positivePart + rightValue.negativePart + 1)
          (rightValue.positivePart + leftValue.negativePart) falseWitness)))

/-- Weak order is strict order against the successor: forward bridge. -/
theorem pcqIntLtSuccOfLe {leftValue rightValue : LfkInt}
    (boundWitness : lfkIntLe leftValue rightValue = true) :
    lfkIntLt leftValue (lfkIntAdd rightValue lreIntOne) = true :=
  lfkNatBleOfLe (leftValue.positivePart + (rightValue.negativePart + 0) + 1)
    (rightValue.positivePart + 1 + leftValue.negativePart)
    (lfkNatLeCongr rfl
      (lfkNatAddOneShiftOut rightValue.positivePart leftValue.negativePart)
      (Nat.succ_le_succ (lfkNatLeOfBle _ _ boundWitness)))

/-- Weak order is strict order against the successor: backward bridge. -/
theorem pcqIntLeOfLtSucc {leftValue rightValue : LfkInt}
    (strictWitness : lfkIntLt leftValue (lfkIntAdd rightValue lreIntOne) = true) :
    lfkIntLe leftValue rightValue = true :=
  lfkNatBleOfLe (leftValue.positivePart + rightValue.negativePart)
    (rightValue.positivePart + leftValue.negativePart)
    (Nat.le_of_succ_le_succ
      (lfkNatLeCongr rfl
        (lfkNatAddOneShiftOut rightValue.positivePart leftValue.negativePart).symm
        (lfkNatLeOfBle (leftValue.positivePart + (rightValue.negativePart + 0) + 1)
          (rightValue.positivePart + 1 + leftValue.negativePart) strictWitness)))

/-- Chain a strict below a weak bound. -/
theorem pcqIntLtOfLtLe {firstValue secondValue thirdValue : LfkInt}
    (strictWitness : lfkIntLt firstValue secondValue = true)
    (weakWitness : lfkIntLe secondValue thirdValue = true) :
    lfkIntLt firstValue thirdValue = true :=
  lreIntLeShiftedGivesLt
    (lreIntLeTrans (lreIntLtGivesLeShifted strictWitness) weakWitness)

/-- Chain a weak below a strict bound. -/
theorem pcqIntLtOfLeLt {firstValue secondValue thirdValue : LfkInt}
    (weakWitness : lfkIntLe firstValue secondValue = true)
    (strictWitness : lfkIntLt secondValue thirdValue = true) :
    lfkIntLt firstValue thirdValue = true :=
  lreIntLeShiftedGivesLt
    (lreIntLeTrans
      (lfkIntAddLeAdd weakWitness (lfmIntLeRefl lreIntOne))
      (lreIntLtGivesLeShifted strictWitness))

/-- Cross-sum equality is a congruence for negation. -/
theorem pcqIntEqNegateCongr {leftValue rightValue : LfkInt}
    (eqWitness : lfkIntEq leftValue rightValue = true) :
    lfkIntEq (lfkIntNegate leftValue) (lfkIntNegate rightValue) = true :=
  lfkNatBeqOfEq (leftValue.negativePart + rightValue.positivePart)
    (rightValue.negativePart + leftValue.positivePart)
    ((Nat.add_comm leftValue.negativePart rightValue.positivePart).trans
      ((lfkNatEqOfBeq (leftValue.positivePart + rightValue.negativePart)
        (rightValue.positivePart + leftValue.negativePart) eqWitness).symm.trans
        (Nat.add_comm leftValue.positivePart rightValue.negativePart)))

/-- Cross-sum equality is a congruence for multiplication on the right
factor (`mul_add` expansion against the shared witness pair). -/
theorem pcqIntMulCrossEqRight (witnessValue : LfkInt) {leftFactor rightFactor : LfkInt}
    (eqWitness : lfkIntEq leftFactor rightFactor = true) :
    lfkIntEq (lfkIntMul witnessValue leftFactor) (lfkIntMul witnessValue rightFactor) = true :=
  let crossEq : leftFactor.positivePart + rightFactor.negativePart
      = rightFactor.positivePart + leftFactor.negativePart :=
    lfkNatEqOfBeq _ _ eqWitness
  let crossEqFlipped : leftFactor.negativePart + rightFactor.positivePart
      = rightFactor.negativePart + leftFactor.positivePart :=
    (Nat.add_comm leftFactor.negativePart rightFactor.positivePart).trans
      (crossEq.symm.trans (Nat.add_comm leftFactor.positivePart rightFactor.negativePart))
  lfkNatBeqOfEq _ _
    ((lfkNatAddSwapMiddle (witnessValue.positivePart * leftFactor.positivePart)
        (witnessValue.negativePart * leftFactor.negativePart)
        (witnessValue.positivePart * rightFactor.negativePart)
        (witnessValue.negativePart * rightFactor.positivePart)).trans
      ((lfkNatAddCongr
          ((Nat.mul_add witnessValue.positivePart leftFactor.positivePart
            rightFactor.negativePart).symm.trans
            ((congrArg (fun probe => witnessValue.positivePart * probe) crossEq).trans
              (Nat.mul_add witnessValue.positivePart rightFactor.positivePart
                leftFactor.negativePart)))
          ((Nat.mul_add witnessValue.negativePart leftFactor.negativePart
            rightFactor.positivePart).symm.trans
            ((congrArg (fun probe => witnessValue.negativePart * probe) crossEqFlipped).trans
              (Nat.mul_add witnessValue.negativePart rightFactor.negativePart
                leftFactor.positivePart)))).trans
        (lfkNatAddSwapMiddle (witnessValue.positivePart * rightFactor.positivePart)
          (witnessValue.positivePart * leftFactor.negativePart)
          (witnessValue.negativePart * rightFactor.negativePart)
          (witnessValue.negativePart * leftFactor.positivePart))))

/-- Right swap for pair-integer addition (plain equality). -/
theorem pcqIntAddRightSwap (firstValue secondValue thirdValue : LfkInt) :
    lfkIntAdd (lfkIntAdd firstValue secondValue) thirdValue
      = lfkIntAdd (lfkIntAdd firstValue thirdValue) secondValue :=
  (lfkIntAddAssoc firstValue secondValue thirdValue).trans
    ((congrArg (fun probe => lfkIntAdd firstValue probe)
        (lfkIntAddComm secondValue thirdValue)).trans
      (lfkIntAddAssoc firstValue thirdValue secondValue).symm)

/-- Dropping a cross-zero RIGHT addend is a cross-sum equality. -/
theorem pcqIntEqDropZeroRight {baseValue zeroishValue : LfkInt}
    (zeroWitness : lfkIntIsZero zeroishValue = true) :
    lfkIntEq (lfkIntAdd baseValue zeroishValue) baseValue = true :=
  lfkNatBeqOfEq ((baseValue.positivePart + zeroishValue.positivePart) + baseValue.negativePart)
    (baseValue.positivePart + (baseValue.negativePart + zeroishValue.negativePart))
    ((Nat.add_assoc baseValue.positivePart zeroishValue.positivePart
        baseValue.negativePart).trans
      ((congrArg (fun probe => baseValue.positivePart + probe)
          (Nat.add_comm zeroishValue.positivePart baseValue.negativePart)).trans
        (congrArg (fun probe => baseValue.positivePart + (baseValue.negativePart + probe))
          (lfkNatEqOfBeq zeroishValue.positivePart zeroishValue.negativePart zeroWitness))))

/-- The two-branch minimum over the cross-sum order. -/
def pcqIntLesser (leftValue rightValue : LfkInt) : LfkInt :=
  cond (lfkIntLe leftValue rightValue) leftValue rightValue

/-- The minimum sits below its left argument. -/
theorem pcqIntLesserLeLeft (leftValue rightValue : LfkInt) :
    lfkIntLe (pcqIntLesser leftValue rightValue) leftValue = true :=
  match compareCases : lfkIntLe leftValue rightValue with
  | true =>
      (congrArg (fun probe => lfkIntLe (cond probe leftValue rightValue) leftValue)
        compareCases).trans (lfmIntLeRefl leftValue)
  | false =>
      (congrArg (fun probe => lfkIntLe (cond probe leftValue rightValue) leftValue)
        compareCases).trans (lreIntLeFalseFlip compareCases)

/-- The minimum sits below its right argument. -/
theorem pcqIntLesserLeRight (leftValue rightValue : LfkInt) :
    lfkIntLe (pcqIntLesser leftValue rightValue) rightValue = true :=
  match compareCases : lfkIntLe leftValue rightValue with
  | true =>
      (congrArg (fun probe => lfkIntLe (cond probe leftValue rightValue) rightValue)
        compareCases).trans compareCases
  | false =>
      (congrArg (fun probe => lfkIntLe (cond probe leftValue rightValue) rightValue)
        compareCases).trans (lfmIntLeRefl rightValue)

/-! ## Stage A1 — divisibility over pair integers: Prop, decomposition, DECIDER -/

/-- `modulus` divides the pair integer `value`: a multiplicative witness up to
cross-sum equality (unnormalized pairs never demand syntactic equality). -/
def pcqDividesProp (modulus : Nat) (value : LfkInt) : Prop :=
  ∃ (quotient : LfkInt), lfkIntEq (lfkIntScaleByNat modulus quotient) value = true

/-- Divisibility transports along cross-sum equality. -/
theorem pcqDividesCrossEq {modulus : Nat} {leftValue rightValue : LfkInt}
    (eqWitness : lfkIntEq leftValue rightValue = true)
    (dividesWitness : pcqDividesProp modulus leftValue) :
    pcqDividesProp modulus rightValue :=
  match dividesWitness with
  | Exists.intro quotient quotientEq =>
      Exists.intro quotient (lreIntEqTrans quotientEq eqWitness)

/-- The canonical remainder of a pair integer modulo `modulusPred + 1`,
computed by counting on `positivePart + modulusPred * negativePart` (the
congruence `-1 ≡ modulusPred` eliminates subtraction). -/
def pcqIntRemainder (modulusPred : Nat) (value : LfkInt) : Nat :=
  pcqNatModCounting modulusPred (value.positivePart + modulusPred * value.negativePart)

/-- The quotient companion of `pcqIntRemainder`. -/
def pcqIntQuotientPart (modulusPred : Nat) (value : LfkInt) : Nat :=
  pcqNatDivCounting modulusPred (value.positivePart + modulusPred * value.negativePart)

/-- THE DECOMPOSITION: every pair integer is, up to cross-sum equality, the
modulus times a quotient pair plus its canonical remainder. -/
theorem pcqIntRemainderDecomposition (modulusPred : Nat) (value : LfkInt) :
    lfkIntEq value
      (lfkIntAdd
        (lfkIntScaleByNat (modulusPred + 1)
          (LfkInt.mk (pcqIntQuotientPart modulusPred value) value.negativePart))
        (lreIntOfNat (pcqIntRemainder modulusPred value))) = true :=
  let quotientValue := pcqIntQuotientPart modulusPred value
  let remainderValue := pcqIntRemainder modulusPred value
  let recovery : (modulusPred + 1) * quotientValue + remainderValue
      = value.positivePart + modulusPred * value.negativePart :=
    pcqNatDivModRecovers modulusPred
      (value.positivePart + modulusPred * value.negativePart)
  lfkNatBeqOfEq
    (value.positivePart + ((modulusPred + 1) * value.negativePart + 0))
    (((modulusPred + 1) * quotientValue + remainderValue) + value.negativePart)
    ((congrArg (fun probe => value.positivePart + probe)
        (Nat.succ_mul modulusPred value.negativePart)).trans
      ((Nat.add_assoc value.positivePart (modulusPred * value.negativePart)
          value.negativePart).symm.trans
        (congrArg (fun probe => probe + value.negativePart) recovery.symm)))

/-- THE DECIDER: divisibility of a pair integer by `modulusPred + 1` is the
vanishing of the canonical remainder. -/
def pcqDvdDecide (modulusPred : Nat) (value : LfkInt) : Bool :=
  Nat.beq (pcqIntRemainder modulusPred value) 0

/-- Decider soundness: an accepted value is genuinely divisible. -/
theorem pcqDvdDecideSound (modulusPred : Nat) (value : LfkInt)
    (decideWitness : pcqDvdDecide modulusPred value = true) :
    pcqDividesProp (modulusPred + 1) value :=
  let quotientPair := LfkInt.mk (pcqIntQuotientPart modulusPred value) value.negativePart
  let remainderZero : pcqIntRemainder modulusPred value = 0 :=
    lfkNatEqOfBeq (pcqIntRemainder modulusPred value) 0 decideWitness
  let collapsedDecomposition : lfkIntEq value
      (lfkIntAdd (lfkIntScaleByNat (modulusPred + 1) quotientPair) (lreIntOfNat 0)) = true :=
    (congrArg (fun probe => lfkIntEq value
        (lfkIntAdd (lfkIntScaleByNat (modulusPred + 1) quotientPair)
          (lreIntOfNat probe))) remainderZero).symm.trans
      (pcqIntRemainderDecomposition modulusPred value)
  Exists.intro quotientPair (lreIntEqSymm collapsedDecomposition)

/-- Decider completeness: a rejected value admits no quotient (unique
remainder against the counting certificate). -/
theorem pcqDvdDecideComplete (modulusPred : Nat) (value : LfkInt)
    (decideWitness : pcqDvdDecide modulusPred value = false)
    (dividesWitness : pcqDividesProp (modulusPred + 1) value) : False :=
  match dividesWitness with
  | Exists.intro witnessQuotient witnessEq =>
      let quotientValue := pcqIntQuotientPart modulusPred value
      let remainderValue := pcqIntRemainder modulusPred value
      let chainedEq : lfkIntEq (lfkIntScaleByNat (modulusPred + 1) witnessQuotient)
          (lfkIntAdd
            (lfkIntScaleByNat (modulusPred + 1)
              (LfkInt.mk quotientValue value.negativePart))
            (lreIntOfNat remainderValue)) = true :=
        lreIntEqTrans witnessEq (pcqIntRemainderDecomposition modulusPred value)
      let crossEquation : (modulusPred + 1) * witnessQuotient.positivePart
          + ((modulusPred + 1) * value.negativePart + 0)
          = ((modulusPred + 1) * quotientValue + remainderValue)
            + (modulusPred + 1) * witnessQuotient.negativePart :=
        lfkNatEqOfBeq _ _ chainedEq
      let leftCollapsed : (modulusPred + 1) * witnessQuotient.positivePart
          + ((modulusPred + 1) * value.negativePart + 0)
          = (modulusPred + 1) * (witnessQuotient.positivePart + value.negativePart) :=
        (Nat.mul_add (modulusPred + 1) witnessQuotient.positivePart
          value.negativePart).symm
      let rightCollapsed : ((modulusPred + 1) * quotientValue + remainderValue)
          + (modulusPred + 1) * witnessQuotient.negativePart
          = remainderValue
            + (modulusPred + 1) * (quotientValue + witnessQuotient.negativePart) :=
        (congrArg (fun probe => probe + (modulusPred + 1) * witnessQuotient.negativePart)
            (Nat.add_comm ((modulusPred + 1) * quotientValue) remainderValue)).trans
          ((Nat.add_assoc remainderValue ((modulusPred + 1) * quotientValue)
              ((modulusPred + 1) * witnessQuotient.negativePart)).trans
            (congrArg (fun probe => remainderValue + probe)
              (Nat.mul_add (modulusPred + 1) quotientValue
                witnessQuotient.negativePart).symm))
      let remainderIsZero : remainderValue = 0 :=
        pcqNatUniqueRemainderZero modulusPred remainderValue
          (quotientValue + witnessQuotient.negativePart)
          (witnessQuotient.positivePart + value.negativePart)
          ((leftCollapsed.symm.trans crossEquation).trans rightCollapsed).symm
          (pcqNatModCountingBound modulusPred
            (value.positivePart + modulusPred * value.negativePart))
      match pcqNatNonZeroShape remainderValue decideWitness with
      | Exists.intro _remainderPred remainderShape =>
          Nat.noConfusion (remainderShape.symm.trans remainderIsZero)

/-- Constructive double-negation elimination for divisibility (via the
decider). -/
theorem pcqDividesDoubleNegElim (modulusPred : Nat) (value : LfkInt)
    (doubleNegWitness : (pcqDividesProp (modulusPred + 1) value → False) → False) :
    pcqDividesProp (modulusPred + 1) value :=
  match lfmBoolCases (pcqDvdDecide modulusPred value) with
  | Or.inl decideTrue => pcqDvdDecideSound modulusPred value decideTrue
  | Or.inr decideFalse =>
      False.elim (doubleNegWitness
        (fun dividesWitness =>
          pcqDvdDecideComplete modulusPred value decideFalse dividesWitness))

/-- Cancel `(value + shift) + (- shift)` down to `value` (cross-sum form). -/
theorem pcqIntAddCancelRight (baseValue shiftValue : LfkInt) :
    lfkIntEq (lfkIntAdd (lfkIntAdd baseValue shiftValue) (lfkIntNegate shiftValue))
      baseValue = true :=
  (congrArg (fun probe => lfkIntEq probe baseValue)
      (lfkIntAddAssoc baseValue shiftValue (lfkIntNegate shiftValue))).trans
    (pcqIntEqDropZeroRight (lreIntAddNegateRightZero shiftValue))

/-- Divisibility absorbs an added scaled multiple of the modulus. -/
theorem pcqDividesAddScaled (modulus cofactor : Nat) (value shiftValue : LfkInt)
    (dividesWitness : pcqDividesProp modulus value) :
    pcqDividesProp modulus
      (lfkIntAdd value (lfkIntScaleByNat (modulus * cofactor) shiftValue)) :=
  match dividesWitness with
  | Exists.intro quotient quotientEq =>
      Exists.intro (lfkIntAdd quotient (lfkIntScaleByNat cofactor shiftValue))
        ((congrArg
            (fun probe => lfkIntEq probe
              (lfkIntAdd value (lfkIntScaleByNat (modulus * cofactor) shiftValue)))
            ((lfkIntScaleAddDistrib modulus quotient
                (lfkIntScaleByNat cofactor shiftValue)).trans
              (congrArg (fun probe => lfkIntAdd (lfkIntScaleByNat modulus quotient) probe)
                (lfmIntScaleCompose modulus cofactor shiftValue).symm))).trans
          (lfkIntAddEqEq quotientEq
            (lfkIntEqRefl (lfkIntScaleByNat (modulus * cofactor) shiftValue))))

/-- Divisibility drops an added scaled multiple of the modulus. -/
theorem pcqDividesDropScaled (modulus cofactor : Nat) (value shiftValue : LfkInt)
    (dividesWitness : pcqDividesProp modulus
      (lfkIntAdd value (lfkIntScaleByNat (modulus * cofactor) shiftValue))) :
    pcqDividesProp modulus value :=
  pcqDividesCrossEq
    (pcqIntAddCancelRight value (lfkIntScaleByNat (modulus * cofactor) shiftValue))
    (pcqDividesAddScaled modulus cofactor
      (lfkIntAdd value (lfkIntScaleByNat (modulus * cofactor) shiftValue))
      (lfkIntNegate shiftValue) dividesWitness)

/-! ## Stage A2 — linear terms (dense coefficient vector + constant) -/

/-- A linear term: dense coefficient vector (entry `i` multiplies de Bruijn
variable `i`, truncation/padding semantics from the sibling dot product) plus
an explicit constant. -/
structure PcqTerm where
  coefficients : List LfkInt
  constantPart : LfkInt

/-- Evaluate a term against an environment. -/
def pcqTermEval (env : List LfkInt) (term : PcqTerm) : LfkInt :=
  lfkIntAdd (lfkDotProduct env term.coefficients) term.constantPart

/-- Pointwise term addition. -/
def pcqTermAdd (leftTerm rightTerm : PcqTerm) : PcqTerm :=
  PcqTerm.mk (lfkAddCoefficientVectors leftTerm.coefficients rightTerm.coefficients)
    (lfkIntAdd leftTerm.constantPart rightTerm.constantPart)

/-- Pointwise term negation. -/
def pcqTermNegate (term : PcqTerm) : PcqTerm :=
  PcqTerm.mk (lfkNegateCoefficientVector term.coefficients)
    (lfkIntNegate term.constantPart)

/-- Scale a term by a Nat multiplier. -/
def pcqTermScaleByNat (multiplier : Nat) (term : PcqTerm) : PcqTerm :=
  PcqTerm.mk (lfkScaleCoefficientVector multiplier term.coefficients)
    (lfkIntScaleByNat multiplier term.constantPart)

/-- The constant term. -/
def pcqConstTerm (value : LfkInt) : PcqTerm := PcqTerm.mk List.nil value

/-- Add one to a term's constant. -/
def pcqTermPlusOne (term : PcqTerm) : PcqTerm :=
  PcqTerm.mk term.coefficients (lfkIntAdd term.constantPart lreIntOne)

/-- Evaluation is additive. -/
theorem pcqTermEvalAdd (env : List LfkInt) (leftTerm rightTerm : PcqTerm) :
    pcqTermEval env (pcqTermAdd leftTerm rightTerm)
      = lfkIntAdd (pcqTermEval env leftTerm) (pcqTermEval env rightTerm) :=
  (congrArg (fun probe => lfkIntAdd probe
      (lfkIntAdd leftTerm.constantPart rightTerm.constantPart))
    (lfkDotProductAddVectors env leftTerm.coefficients rightTerm.coefficients)).trans
    (lfkIntAddSwapMiddle (lfkDotProduct env leftTerm.coefficients)
      (lfkDotProduct env rightTerm.coefficients)
      leftTerm.constantPart rightTerm.constantPart)

/-- Evaluation commutes with negation. -/
theorem pcqTermEvalNegate (env : List LfkInt) (term : PcqTerm) :
    pcqTermEval env (pcqTermNegate term) = lfkIntNegate (pcqTermEval env term) :=
  congrArg (fun probe => lfkIntAdd probe (lfkIntNegate term.constantPart))
    (lfkDotProductNegatedVector env term.coefficients)

/-- Evaluation commutes with Nat scaling. -/
theorem pcqTermEvalScale (env : List LfkInt) (multiplier : Nat) (term : PcqTerm) :
    pcqTermEval env (pcqTermScaleByNat multiplier term)
      = lfkIntScaleByNat multiplier (pcqTermEval env term) :=
  (congrArg (fun probe => lfkIntAdd probe (lfkIntScaleByNat multiplier term.constantPart))
    (lfkDotProductScaledVector env multiplier term.coefficients)).trans
    (lfkIntScaleAddDistrib multiplier (lfkDotProduct env term.coefficients)
      term.constantPart).symm

/-- Constant terms evaluate to their constant. -/
theorem pcqConstTermEval (env : List LfkInt) (value : LfkInt) :
    pcqTermEval env (pcqConstTerm value) = value :=
  (congrArg (fun probe => lfkIntAdd probe value) (lfkDotProductNilRight env)).trans
    (lfkIntZeroAdd value)

/-- The plus-one term evaluates to the successor. -/
theorem pcqTermPlusOneEval (env : List LfkInt) (term : PcqTerm) :
    pcqTermEval env (pcqTermPlusOne term) = lfkIntAdd (pcqTermEval env term) lreIntOne :=
  (lfkIntAddAssoc (lfkDotProduct env term.coefficients) term.constantPart lreIntOne).symm

/-- The pivot coefficient of a term under a binder (entry 0; absent reads
zero). -/
def pcqTermHeadCoeff (term : PcqTerm) : LfkInt :=
  match term.coefficients with
  | List.nil => lfkIntZero
  | headCoefficient :: _tailCoefficients => headCoefficient

/-- The term with the pivot coefficient stripped (de Bruijn decrement). -/
def pcqTermTail (term : PcqTerm) : PcqTerm :=
  PcqTerm.mk
    (match term.coefficients with
     | List.nil => List.nil
     | _headCoefficient :: tailCoefficients => tailCoefficients)
    term.constantPart

/-- THE CONS SPLIT: evaluation under a binder is pivot times head coefficient
plus the tail term's evaluation. -/
theorem pcqTermEvalConsSplit (pivotValue : LfkInt) (env : List LfkInt) :
    ∀ (term : PcqTerm),
    pcqTermEval (pivotValue :: env) term
      = lfkIntAdd (lfkIntMul pivotValue (pcqTermHeadCoeff term))
          (pcqTermEval env (pcqTermTail term))
  | PcqTerm.mk List.nil constantValue =>
      ((congrArg (fun probe => lfkIntAdd lfkIntZero (lfkIntAdd probe constantValue))
          (lfkDotProductNilRight env)).trans
        (lfkIntZeroAdd (lfkIntAdd lfkIntZero constantValue))).symm
  | PcqTerm.mk (headCoefficient :: tailCoefficients) constantValue =>
      lfkIntAddAssoc (lfkIntMul pivotValue headCoefficient)
        (lfkDotProduct env tailCoefficients) constantValue

/-! ## Stage A3 — reflected formulas: surface (with exists) and QF layers -/

/-- Surface Presburger formulas (de Bruijn binders; strict inequality in the
succ-le encoding; structurally positive divisibility moduli; negated
divisibility native per the NNF invariant). -/
inductive PcqFormula where
  | flt (leftTerm rightTerm : PcqTerm) : PcqFormula
  | fdvd (modulusPred : Nat) (target : PcqTerm) : PcqFormula
  | fndvd (modulusPred : Nat) (target : PcqTerm) : PcqFormula
  | fconj (leftBranch rightBranch : PcqFormula) : PcqFormula
  | fdisj (leftBranch rightBranch : PcqFormula) : PcqFormula
  | fneg (body : PcqFormula) : PcqFormula
  | fexists (body : PcqFormula) : PcqFormula

/-- The Prop semantics over integer environments (variable `i` reads entry `i`,
missing entries read zero through the truncating dot product). -/
def pcqInterp : List LfkInt → PcqFormula → Prop
  | env, PcqFormula.flt leftTerm rightTerm =>
      lfkIntLt (pcqTermEval env leftTerm) (pcqTermEval env rightTerm) = true
  | env, PcqFormula.fdvd modulusPred target =>
      pcqDividesProp (modulusPred + 1) (pcqTermEval env target)
  | env, PcqFormula.fndvd modulusPred target =>
      pcqDividesProp (modulusPred + 1) (pcqTermEval env target) → False
  | env, PcqFormula.fconj leftBranch rightBranch =>
      And (pcqInterp env leftBranch) (pcqInterp env rightBranch)
  | env, PcqFormula.fdisj leftBranch rightBranch =>
      Or (pcqInterp env leftBranch) (pcqInterp env rightBranch)
  | env, PcqFormula.fneg body => pcqInterp env body → False
  | env, PcqFormula.fexists body =>
      ∃ (boundValue : LfkInt), pcqInterp (boundValue :: env) body

/-- Quantifier-free formulas (the elimination output layer). -/
inductive PcqQfFormula where
  | qlt (leftTerm rightTerm : PcqTerm) : PcqQfFormula
  | qdvd (modulusPred : Nat) (target : PcqTerm) : PcqQfFormula
  | qndvd (modulusPred : Nat) (target : PcqTerm) : PcqQfFormula
  | qconj (leftBranch rightBranch : PcqQfFormula) : PcqQfFormula
  | qdisj (leftBranch rightBranch : PcqQfFormula) : PcqQfFormula
  | qneg (body : PcqQfFormula) : PcqQfFormula

/-- Prop semantics of the QF layer. -/
def pcqQfHolds (env : List LfkInt) : PcqQfFormula → Prop
  | PcqQfFormula.qlt leftTerm rightTerm =>
      lfkIntLt (pcqTermEval env leftTerm) (pcqTermEval env rightTerm) = true
  | PcqQfFormula.qdvd modulusPred target =>
      pcqDividesProp (modulusPred + 1) (pcqTermEval env target)
  | PcqQfFormula.qndvd modulusPred target =>
      pcqDividesProp (modulusPred + 1) (pcqTermEval env target) → False
  | PcqQfFormula.qconj leftBranch rightBranch =>
      And (pcqQfHolds env leftBranch) (pcqQfHolds env rightBranch)
  | PcqQfFormula.qdisj leftBranch rightBranch =>
      Or (pcqQfHolds env leftBranch) (pcqQfHolds env rightBranch)
  | PcqQfFormula.qneg body => pcqQfHolds env body → False

/-- THE EXECUTABLE EVALUATOR on the QF layer (total; divisibility via the
counting decider). -/
def pcqQfEval (env : List LfkInt) : PcqQfFormula → Bool
  | PcqQfFormula.qlt leftTerm rightTerm =>
      lfkIntLt (pcqTermEval env leftTerm) (pcqTermEval env rightTerm)
  | PcqQfFormula.qdvd modulusPred target =>
      pcqDvdDecide modulusPred (pcqTermEval env target)
  | PcqQfFormula.qndvd modulusPred target =>
      Bool.not (pcqDvdDecide modulusPred (pcqTermEval env target))
  | PcqQfFormula.qconj leftBranch rightBranch =>
      pcqQfEval env leftBranch && pcqQfEval env rightBranch
  | PcqQfFormula.qdisj leftBranch rightBranch =>
      pcqQfEval env leftBranch || pcqQfEval env rightBranch
  | PcqQfFormula.qneg body => Bool.not (pcqQfEval env body)

mutual

/-- Evaluator soundness: `true` means the Prop semantics holds. -/
theorem pcqQfEvalTrueSound (env : List LfkInt) : ∀ (formula : PcqQfFormula),
    pcqQfEval env formula = true → pcqQfHolds env formula
  | PcqQfFormula.qlt _leftTerm _rightTerm, evalWitness => evalWitness
  | PcqQfFormula.qdvd modulusPred target, evalWitness =>
      pcqDvdDecideSound modulusPred (pcqTermEval env target) evalWitness
  | PcqQfFormula.qndvd modulusPred target, evalWitness =>
      fun dividesWitness =>
        pcqDvdDecideComplete modulusPred (pcqTermEval env target)
          (lfkBoolNotTrueImpliesFalse (pcqDvdDecide modulusPred (pcqTermEval env target))
            evalWitness)
          dividesWitness
  | PcqQfFormula.qconj leftBranch rightBranch, evalWitness =>
      let destructured := lfkBoolAndDestruct (pcqQfEval env leftBranch)
        (pcqQfEval env rightBranch) evalWitness
      And.intro (pcqQfEvalTrueSound env leftBranch destructured.left)
        (pcqQfEvalTrueSound env rightBranch destructured.right)
  | PcqQfFormula.qdisj leftBranch rightBranch, evalWitness =>
      match pcqBoolOrDestructTrue (pcqQfEval env leftBranch)
        (pcqQfEval env rightBranch) evalWitness with
      | Or.inl leftTrue => Or.inl (pcqQfEvalTrueSound env leftBranch leftTrue)
      | Or.inr rightTrue => Or.inr (pcqQfEvalTrueSound env rightBranch rightTrue)
  | PcqQfFormula.qneg body, evalWitness =>
      fun bodyHolds =>
        pcqQfEvalFalseComplete env body
          (lfkBoolNotTrueImpliesFalse (pcqQfEval env body) evalWitness) bodyHolds

/-- Evaluator completeness: `false` refutes the Prop semantics. -/
theorem pcqQfEvalFalseComplete (env : List LfkInt) : ∀ (formula : PcqQfFormula),
    pcqQfEval env formula = false → pcqQfHolds env formula → False
  | PcqQfFormula.qlt _leftTerm _rightTerm, evalWitness, holdsWitness =>
      Bool.noConfusion (evalWitness.symm.trans holdsWitness)
  | PcqQfFormula.qdvd modulusPred target, evalWitness, holdsWitness =>
      pcqDvdDecideComplete modulusPred (pcqTermEval env target) evalWitness holdsWitness
  | PcqQfFormula.qndvd modulusPred target, evalWitness, holdsWitness =>
      holdsWitness
        (pcqDvdDecideSound modulusPred (pcqTermEval env target)
          (pcqBoolNotFalseImpliesTrue (pcqDvdDecide modulusPred (pcqTermEval env target))
            evalWitness))
  | PcqQfFormula.qconj leftBranch rightBranch, evalWitness, holdsWitness =>
      (match pcqBoolAndDestructFalse (pcqQfEval env leftBranch)
        (pcqQfEval env rightBranch) evalWitness with
      | Or.inl leftFalse =>
          pcqQfEvalFalseComplete env leftBranch leftFalse holdsWitness.left
      | Or.inr rightFalse =>
          pcqQfEvalFalseComplete env rightBranch rightFalse holdsWitness.right)
  | PcqQfFormula.qdisj leftBranch rightBranch, evalWitness, holdsWitness =>
      let destructured := pcqBoolOrDestructFalse (pcqQfEval env leftBranch)
        (pcqQfEval env rightBranch) evalWitness
      (match holdsWitness with
      | Or.inl leftHolds =>
          pcqQfEvalFalseComplete env leftBranch destructured.left leftHolds
      | Or.inr rightHolds =>
          pcqQfEvalFalseComplete env rightBranch destructured.right rightHolds)
  | PcqQfFormula.qneg body, evalWitness, holdsWitness =>
      holdsWitness
        (pcqQfEvalTrueSound env body
          (pcqBoolNotFalseImpliesTrue (pcqQfEval env body) evalWitness))

end

/-- Constructive excluded middle for the QF layer (via the evaluator). -/
theorem pcqQfHoldsOrNot (env : List LfkInt) (formula : PcqQfFormula) :
    Or (pcqQfHolds env formula) (pcqQfHolds env formula → False) :=
  match lfmBoolCases (pcqQfEval env formula) with
  | Or.inl evalTrue => Or.inl (pcqQfEvalTrueSound env formula evalTrue)
  | Or.inr evalFalse => Or.inr (pcqQfEvalFalseComplete env formula evalFalse)

/-- Lift a plain equality of pair integers to a cross-sum equality. -/
theorem pcqIntEqOfEq {leftValue rightValue : LfkInt} (plainEq : leftValue = rightValue) :
    lfkIntEq leftValue rightValue = true :=
  plainEq ▸ lfkIntEqRefl leftValue

/-! ## Stage C0 — the unitary matrix layer (one distinguished pivot variable;
matrix terms live over the OUTER environment) -/

/-- A unitary Cooper matrix: every pivot occurrence has coefficient exactly
`+1` (`mupper`/`mlower`/`mdvd`/`mndvd`); pivot-free residue keeps its own atom
forms; `mtrue`/`mfalse` absorb the minus-infinity substitution. -/
inductive PcqMatrix where
  | mtrue : PcqMatrix
  | mfalse : PcqMatrix
  | mupper (bound : PcqTerm) : PcqMatrix
  | mlower (bound : PcqTerm) : PcqMatrix
  | mdvd (modulusPred : Nat) (offset : PcqTerm) : PcqMatrix
  | mndvd (modulusPred : Nat) (offset : PcqTerm) : PcqMatrix
  | mfreelt (leftTerm rightTerm : PcqTerm) : PcqMatrix
  | mfreedvd (modulusPred : Nat) (target : PcqTerm) : PcqMatrix
  | mfreendvd (modulusPred : Nat) (target : PcqTerm) : PcqMatrix
  | mconj (leftBranch rightBranch : PcqMatrix) : PcqMatrix
  | mdisj (leftBranch rightBranch : PcqMatrix) : PcqMatrix

/-- Prop semantics of a matrix at a pivot value. -/
def pcqMatrixHolds (env : List LfkInt) (pivotValue : LfkInt) : PcqMatrix → Prop
  | PcqMatrix.mtrue => True
  | PcqMatrix.mfalse => False
  | PcqMatrix.mupper bound => lfkIntLt pivotValue (pcqTermEval env bound) = true
  | PcqMatrix.mlower bound => lfkIntLt (pcqTermEval env bound) pivotValue = true
  | PcqMatrix.mdvd modulusPred offset =>
      pcqDividesProp (modulusPred + 1) (lfkIntAdd pivotValue (pcqTermEval env offset))
  | PcqMatrix.mndvd modulusPred offset =>
      pcqDividesProp (modulusPred + 1) (lfkIntAdd pivotValue (pcqTermEval env offset)) → False
  | PcqMatrix.mfreelt leftTerm rightTerm =>
      lfkIntLt (pcqTermEval env leftTerm) (pcqTermEval env rightTerm) = true
  | PcqMatrix.mfreedvd modulusPred target =>
      pcqDividesProp (modulusPred + 1) (pcqTermEval env target)
  | PcqMatrix.mfreendvd modulusPred target =>
      pcqDividesProp (modulusPred + 1) (pcqTermEval env target) → False
  | PcqMatrix.mconj leftBranch rightBranch =>
      And (pcqMatrixHolds env pivotValue leftBranch) (pcqMatrixHolds env pivotValue rightBranch)
  | PcqMatrix.mdisj leftBranch rightBranch =>
      Or (pcqMatrixHolds env pivotValue leftBranch) (pcqMatrixHolds env pivotValue rightBranch)

/-- Executable matrix evaluator (the constructive case-split engine). -/
def pcqMatrixEval (env : List LfkInt) (pivotValue : LfkInt) : PcqMatrix → Bool
  | PcqMatrix.mtrue => true
  | PcqMatrix.mfalse => false
  | PcqMatrix.mupper bound => lfkIntLt pivotValue (pcqTermEval env bound)
  | PcqMatrix.mlower bound => lfkIntLt (pcqTermEval env bound) pivotValue
  | PcqMatrix.mdvd modulusPred offset =>
      pcqDvdDecide modulusPred (lfkIntAdd pivotValue (pcqTermEval env offset))
  | PcqMatrix.mndvd modulusPred offset =>
      Bool.not (pcqDvdDecide modulusPred (lfkIntAdd pivotValue (pcqTermEval env offset)))
  | PcqMatrix.mfreelt leftTerm rightTerm =>
      lfkIntLt (pcqTermEval env leftTerm) (pcqTermEval env rightTerm)
  | PcqMatrix.mfreedvd modulusPred target => pcqDvdDecide modulusPred (pcqTermEval env target)
  | PcqMatrix.mfreendvd modulusPred target =>
      Bool.not (pcqDvdDecide modulusPred (pcqTermEval env target))
  | PcqMatrix.mconj leftBranch rightBranch =>
      pcqMatrixEval env pivotValue leftBranch && pcqMatrixEval env pivotValue rightBranch
  | PcqMatrix.mdisj leftBranch rightBranch =>
      pcqMatrixEval env pivotValue leftBranch || pcqMatrixEval env pivotValue rightBranch

/-- Matrix evaluator soundness. -/
theorem pcqMatrixEvalTrueSound (env : List LfkInt) (pivotValue : LfkInt) :
    ∀ (matrix : PcqMatrix), pcqMatrixEval env pivotValue matrix = true →
    pcqMatrixHolds env pivotValue matrix
  | PcqMatrix.mtrue, _evalWitness => True.intro
  | PcqMatrix.mfalse, evalWitness => Bool.noConfusion evalWitness
  | PcqMatrix.mupper _bound, evalWitness => evalWitness
  | PcqMatrix.mlower _bound, evalWitness => evalWitness
  | PcqMatrix.mdvd modulusPred offset, evalWitness =>
      pcqDvdDecideSound modulusPred (lfkIntAdd pivotValue (pcqTermEval env offset)) evalWitness
  | PcqMatrix.mndvd modulusPred offset, evalWitness =>
      fun dividesWitness =>
        pcqDvdDecideComplete modulusPred (lfkIntAdd pivotValue (pcqTermEval env offset))
          (lfkBoolNotTrueImpliesFalse _ evalWitness) dividesWitness
  | PcqMatrix.mfreelt _leftTerm _rightTerm, evalWitness => evalWitness
  | PcqMatrix.mfreedvd modulusPred target, evalWitness =>
      pcqDvdDecideSound modulusPred (pcqTermEval env target) evalWitness
  | PcqMatrix.mfreendvd modulusPred target, evalWitness =>
      fun dividesWitness =>
        pcqDvdDecideComplete modulusPred (pcqTermEval env target)
          (lfkBoolNotTrueImpliesFalse _ evalWitness) dividesWitness
  | PcqMatrix.mconj leftBranch rightBranch, evalWitness =>
      let destructured := lfkBoolAndDestruct (pcqMatrixEval env pivotValue leftBranch)
        (pcqMatrixEval env pivotValue rightBranch) evalWitness
      And.intro (pcqMatrixEvalTrueSound env pivotValue leftBranch destructured.left)
        (pcqMatrixEvalTrueSound env pivotValue rightBranch destructured.right)
  | PcqMatrix.mdisj leftBranch rightBranch, evalWitness =>
      match pcqBoolOrDestructTrue (pcqMatrixEval env pivotValue leftBranch)
        (pcqMatrixEval env pivotValue rightBranch) evalWitness with
      | Or.inl leftTrue => Or.inl (pcqMatrixEvalTrueSound env pivotValue leftBranch leftTrue)
      | Or.inr rightTrue => Or.inr (pcqMatrixEvalTrueSound env pivotValue rightBranch rightTrue)

/-- Matrix evaluator completeness. -/
theorem pcqMatrixEvalFalseComplete (env : List LfkInt) (pivotValue : LfkInt) :
    ∀ (matrix : PcqMatrix), pcqMatrixEval env pivotValue matrix = false →
    pcqMatrixHolds env pivotValue matrix → False
  | PcqMatrix.mtrue, evalWitness, _holdsWitness => Bool.noConfusion evalWitness
  | PcqMatrix.mfalse, _evalWitness, holdsWitness => holdsWitness
  | PcqMatrix.mupper _bound, evalWitness, holdsWitness =>
      Bool.noConfusion (evalWitness.symm.trans holdsWitness)
  | PcqMatrix.mlower _bound, evalWitness, holdsWitness =>
      Bool.noConfusion (evalWitness.symm.trans holdsWitness)
  | PcqMatrix.mdvd modulusPred offset, evalWitness, holdsWitness =>
      pcqDvdDecideComplete modulusPred (lfkIntAdd pivotValue (pcqTermEval env offset))
        evalWitness holdsWitness
  | PcqMatrix.mndvd modulusPred offset, evalWitness, holdsWitness =>
      holdsWitness
        (pcqDvdDecideSound modulusPred (lfkIntAdd pivotValue (pcqTermEval env offset))
          (pcqBoolNotFalseImpliesTrue _ evalWitness))
  | PcqMatrix.mfreelt _leftTerm _rightTerm, evalWitness, holdsWitness =>
      Bool.noConfusion (evalWitness.symm.trans holdsWitness)
  | PcqMatrix.mfreedvd modulusPred target, evalWitness, holdsWitness =>
      pcqDvdDecideComplete modulusPred (pcqTermEval env target) evalWitness holdsWitness
  | PcqMatrix.mfreendvd modulusPred target, evalWitness, holdsWitness =>
      holdsWitness
        (pcqDvdDecideSound modulusPred (pcqTermEval env target)
          (pcqBoolNotFalseImpliesTrue _ evalWitness))
  | PcqMatrix.mconj leftBranch rightBranch, evalWitness, holdsWitness =>
      (match pcqBoolAndDestructFalse (pcqMatrixEval env pivotValue leftBranch)
        (pcqMatrixEval env pivotValue rightBranch) evalWitness with
      | Or.inl leftFalse =>
          pcqMatrixEvalFalseComplete env pivotValue leftBranch leftFalse holdsWitness.left
      | Or.inr rightFalse =>
          pcqMatrixEvalFalseComplete env pivotValue rightBranch rightFalse holdsWitness.right)
  | PcqMatrix.mdisj leftBranch rightBranch, evalWitness, holdsWitness =>
      let destructured := pcqBoolOrDestructFalse (pcqMatrixEval env pivotValue leftBranch)
        (pcqMatrixEval env pivotValue rightBranch) evalWitness
      (match holdsWitness with
      | Or.inl leftHolds =>
          pcqMatrixEvalFalseComplete env pivotValue leftBranch destructured.left leftHolds
      | Or.inr rightHolds =>
          pcqMatrixEvalFalseComplete env pivotValue rightBranch destructured.right rightHolds)

/-- Holding matrices evaluate to `true` (evaluator totality closes the
constructive loop). -/
theorem pcqMatrixEvalOfHolds (env : List LfkInt) (pivotValue : LfkInt) (matrix : PcqMatrix)
    (holdsWitness : pcqMatrixHolds env pivotValue matrix) :
    pcqMatrixEval env pivotValue matrix = true :=
  match lfmBoolCases (pcqMatrixEval env pivotValue matrix) with
  | Or.inl evalTrue => evalTrue
  | Or.inr evalFalse =>
      False.elim (pcqMatrixEvalFalseComplete env pivotValue matrix evalFalse holdsWitness)

/-- Matrix satisfaction transports along cross-sum equality of the pivot. -/
theorem pcqMatrixHoldsCrossEq (env : List LfkInt) {oldPivot newPivot : LfkInt}
    (pivotEq : lfkIntEq oldPivot newPivot = true) :
    ∀ (matrix : PcqMatrix), pcqMatrixHolds env oldPivot matrix →
    pcqMatrixHolds env newPivot matrix
  | PcqMatrix.mtrue, _holdsWitness => True.intro
  | PcqMatrix.mfalse, holdsWitness => holdsWitness
  | PcqMatrix.mupper _bound, holdsWitness => lreIntLtCongrLeft pivotEq holdsWitness
  | PcqMatrix.mlower _bound, holdsWitness => lreIntLtCongrRight pivotEq holdsWitness
  | PcqMatrix.mdvd _modulusPred offset, holdsWitness =>
      pcqDividesCrossEq
        (lfkIntAddEqEq pivotEq (lfkIntEqRefl (pcqTermEval env offset))) holdsWitness
  | PcqMatrix.mndvd _modulusPred offset, holdsWitness =>
      fun dividesWitness =>
        holdsWitness
          (pcqDividesCrossEq
            (lfkIntAddEqEq (lreIntEqSymm pivotEq) (lfkIntEqRefl (pcqTermEval env offset)))
            dividesWitness)
  | PcqMatrix.mfreelt _leftTerm _rightTerm, holdsWitness => holdsWitness
  | PcqMatrix.mfreedvd _modulusPred _target, holdsWitness => holdsWitness
  | PcqMatrix.mfreendvd _modulusPred _target, holdsWitness => holdsWitness
  | PcqMatrix.mconj leftBranch rightBranch, holdsWitness =>
      And.intro (pcqMatrixHoldsCrossEq env pivotEq leftBranch holdsWitness.left)
        (pcqMatrixHoldsCrossEq env pivotEq rightBranch holdsWitness.right)
  | PcqMatrix.mdisj leftBranch rightBranch, holdsWitness =>
      (match holdsWitness with
      | Or.inl leftHolds =>
          Or.inl (pcqMatrixHoldsCrossEq env pivotEq leftBranch leftHolds)
      | Or.inr rightHolds =>
          Or.inr (pcqMatrixHoldsCrossEq env pivotEq rightBranch rightHolds))

/-! ## Stage C1 — minus-infinity form, delta, lower-bound set -/

/-- The minus-infinity form: upper bounds hold, lower bounds fail, everything
else (in particular divisibility) is untouched. -/
def pcqMinusInf : PcqMatrix → PcqMatrix
  | PcqMatrix.mtrue => PcqMatrix.mtrue
  | PcqMatrix.mfalse => PcqMatrix.mfalse
  | PcqMatrix.mupper _bound => PcqMatrix.mtrue
  | PcqMatrix.mlower _bound => PcqMatrix.mfalse
  | PcqMatrix.mdvd modulusPred offset => PcqMatrix.mdvd modulusPred offset
  | PcqMatrix.mndvd modulusPred offset => PcqMatrix.mndvd modulusPred offset
  | PcqMatrix.mfreelt leftTerm rightTerm => PcqMatrix.mfreelt leftTerm rightTerm
  | PcqMatrix.mfreedvd modulusPred target => PcqMatrix.mfreedvd modulusPred target
  | PcqMatrix.mfreendvd modulusPred target => PcqMatrix.mfreendvd modulusPred target
  | PcqMatrix.mconj leftBranch rightBranch =>
      PcqMatrix.mconj (pcqMinusInf leftBranch) (pcqMinusInf rightBranch)
  | PcqMatrix.mdisj leftBranch rightBranch =>
      PcqMatrix.mdisj (pcqMinusInf leftBranch) (pcqMinusInf rightBranch)

/-- The period: the PRODUCT of all pivot divisibility moduli (any common
multiple works — no lcm needed). -/
def pcqDelta : PcqMatrix → Nat
  | PcqMatrix.mtrue => 1
  | PcqMatrix.mfalse => 1
  | PcqMatrix.mupper _bound => 1
  | PcqMatrix.mlower _bound => 1
  | PcqMatrix.mdvd modulusPred _offset => modulusPred + 1
  | PcqMatrix.mndvd modulusPred _offset => modulusPred + 1
  | PcqMatrix.mfreelt _leftTerm _rightTerm => 1
  | PcqMatrix.mfreedvd _modulusPred _target => 1
  | PcqMatrix.mfreendvd _modulusPred _target => 1
  | PcqMatrix.mconj leftBranch rightBranch => pcqDelta leftBranch * pcqDelta rightBranch
  | PcqMatrix.mdisj leftBranch rightBranch => pcqDelta leftBranch * pcqDelta rightBranch

/-- Delta is positive. -/
theorem pcqDeltaPositive : ∀ (matrix : PcqMatrix), Nat.ble 1 (pcqDelta matrix) = true
  | PcqMatrix.mtrue => rfl
  | PcqMatrix.mfalse => rfl
  | PcqMatrix.mupper _bound => rfl
  | PcqMatrix.mlower _bound => rfl
  | PcqMatrix.mdvd modulusPred _offset =>
      lfkNatBleOfLe 1 (modulusPred + 1) (Nat.succ_le_succ (Nat.zero_le modulusPred))
  | PcqMatrix.mndvd modulusPred _offset =>
      lfkNatBleOfLe 1 (modulusPred + 1) (Nat.succ_le_succ (Nat.zero_le modulusPred))
  | PcqMatrix.mfreelt _leftTerm _rightTerm => rfl
  | PcqMatrix.mfreedvd _modulusPred _target => rfl
  | PcqMatrix.mfreendvd _modulusPred _target => rfl
  | PcqMatrix.mconj leftBranch rightBranch =>
      lreNatPositiveMulPositive (pcqDelta leftBranch) (pcqDelta rightBranch)
        (pcqDeltaPositive leftBranch) (pcqDeltaPositive rightBranch)
  | PcqMatrix.mdisj leftBranch rightBranch =>
      lreNatPositiveMulPositive (pcqDelta leftBranch) (pcqDelta rightBranch)
        (pcqDeltaPositive leftBranch) (pcqDeltaPositive rightBranch)

/-- Cons-only concatenation of term lists. -/
def pcqTermListConcat : List PcqTerm → List PcqTerm → List PcqTerm
  | List.nil, secondList => secondList
  | headTerm :: tailTerms, secondList => headTerm :: pcqTermListConcat tailTerms secondList

/-- The B-set: evaluated lower-bound terms are the only descent boundaries
(the atom normal form has no equalities — they arrive as inequality pairs). -/
def pcqLowerBounds : PcqMatrix → List PcqTerm
  | PcqMatrix.mtrue => List.nil
  | PcqMatrix.mfalse => List.nil
  | PcqMatrix.mupper _bound => List.nil
  | PcqMatrix.mlower bound => bound :: List.nil
  | PcqMatrix.mdvd _modulusPred _offset => List.nil
  | PcqMatrix.mndvd _modulusPred _offset => List.nil
  | PcqMatrix.mfreelt _leftTerm _rightTerm => List.nil
  | PcqMatrix.mfreedvd _modulusPred _target => List.nil
  | PcqMatrix.mfreendvd _modulusPred _target => List.nil
  | PcqMatrix.mconj leftBranch rightBranch =>
      pcqTermListConcat (pcqLowerBounds leftBranch) (pcqLowerBounds rightBranch)
  | PcqMatrix.mdisj leftBranch rightBranch =>
      pcqTermListConcat (pcqLowerBounds leftBranch) (pcqLowerBounds rightBranch)

/-- Every pivot divisibility modulus divides the target (structure-mirroring
Prop). -/
def pcqAllModuliDivide : PcqMatrix → Nat → Prop
  | PcqMatrix.mtrue, _target => True
  | PcqMatrix.mfalse, _target => True
  | PcqMatrix.mupper _bound, _target => True
  | PcqMatrix.mlower _bound, _target => True
  | PcqMatrix.mdvd modulusPred _offset, target => pcqNatDividesProp (modulusPred + 1) target
  | PcqMatrix.mndvd modulusPred _offset, target => pcqNatDividesProp (modulusPred + 1) target
  | PcqMatrix.mfreelt _leftTerm _rightTerm, _target => True
  | PcqMatrix.mfreedvd _modulusPred _target, _target' => True
  | PcqMatrix.mfreendvd _modulusPred _target, _target' => True
  | PcqMatrix.mconj leftBranch rightBranch, target =>
      And (pcqAllModuliDivide leftBranch target) (pcqAllModuliDivide rightBranch target)
  | PcqMatrix.mdisj leftBranch rightBranch, target =>
      And (pcqAllModuliDivide leftBranch target) (pcqAllModuliDivide rightBranch target)

/-- Modulus division is stable under enlarging the target by a right factor. -/
theorem pcqAllModuliDivideMulRight : ∀ (matrix : PcqMatrix) (target extraFactor : Nat),
    pcqAllModuliDivide matrix target → pcqAllModuliDivide matrix (target * extraFactor)
  | PcqMatrix.mtrue, _target, _extraFactor, _divideWitness => True.intro
  | PcqMatrix.mfalse, _target, _extraFactor, _divideWitness => True.intro
  | PcqMatrix.mupper _bound, _target, _extraFactor, _divideWitness => True.intro
  | PcqMatrix.mlower _bound, _target, _extraFactor, _divideWitness => True.intro
  | PcqMatrix.mdvd modulusPred _offset, target, extraFactor, divideWitness =>
      pcqNatDividesMulRight (modulusPred + 1) target extraFactor divideWitness
  | PcqMatrix.mndvd modulusPred _offset, target, extraFactor, divideWitness =>
      pcqNatDividesMulRight (modulusPred + 1) target extraFactor divideWitness
  | PcqMatrix.mfreelt _leftTerm _rightTerm, _target, _extraFactor, _divideWitness => True.intro
  | PcqMatrix.mfreedvd _modulusPred _target, _target', _extraFactor, _divideWitness => True.intro
  | PcqMatrix.mfreendvd _modulusPred _target, _target', _extraFactor, _divideWitness =>
      True.intro
  | PcqMatrix.mconj leftBranch rightBranch, target, extraFactor, divideWitness =>
      And.intro
        (pcqAllModuliDivideMulRight leftBranch target extraFactor divideWitness.left)
        (pcqAllModuliDivideMulRight rightBranch target extraFactor divideWitness.right)
  | PcqMatrix.mdisj leftBranch rightBranch, target, extraFactor, divideWitness =>
      And.intro
        (pcqAllModuliDivideMulRight leftBranch target extraFactor divideWitness.left)
        (pcqAllModuliDivideMulRight rightBranch target extraFactor divideWitness.right)

/-- Modulus division is stable under enlarging the target by a left factor. -/
theorem pcqAllModuliDivideMulLeft : ∀ (matrix : PcqMatrix) (target extraFactor : Nat),
    pcqAllModuliDivide matrix target → pcqAllModuliDivide matrix (extraFactor * target)
  | matrix, target, extraFactor, divideWitness =>
      (Nat.mul_comm target extraFactor) ▸
        pcqAllModuliDivideMulRight matrix target extraFactor divideWitness

/-- THE DELTA CERTIFICATE: every modulus divides the product delta. -/
theorem pcqModuliDivideDelta : ∀ (matrix : PcqMatrix),
    pcqAllModuliDivide matrix (pcqDelta matrix)
  | PcqMatrix.mtrue => True.intro
  | PcqMatrix.mfalse => True.intro
  | PcqMatrix.mupper _bound => True.intro
  | PcqMatrix.mlower _bound => True.intro
  | PcqMatrix.mdvd modulusPred _offset => pcqNatDividesSelf (modulusPred + 1)
  | PcqMatrix.mndvd modulusPred _offset => pcqNatDividesSelf (modulusPred + 1)
  | PcqMatrix.mfreelt _leftTerm _rightTerm => True.intro
  | PcqMatrix.mfreedvd _modulusPred _target => True.intro
  | PcqMatrix.mfreendvd _modulusPred _target => True.intro
  | PcqMatrix.mconj leftBranch rightBranch =>
      And.intro
        (pcqAllModuliDivideMulRight leftBranch (pcqDelta leftBranch)
          (pcqDelta rightBranch) (pcqModuliDivideDelta leftBranch))
        (pcqAllModuliDivideMulLeft rightBranch (pcqDelta rightBranch)
          (pcqDelta leftBranch) (pcqModuliDivideDelta rightBranch))
  | PcqMatrix.mdisj leftBranch rightBranch =>
      And.intro
        (pcqAllModuliDivideMulRight leftBranch (pcqDelta leftBranch)
          (pcqDelta rightBranch) (pcqModuliDivideDelta leftBranch))
        (pcqAllModuliDivideMulLeft rightBranch (pcqDelta rightBranch)
          (pcqDelta leftBranch) (pcqModuliDivideDelta rightBranch))

/-! ## Stage C2 — finite disjunction kits (recursive Props mirroring the
output formula's disjunction structure) -/

/-- Some index in `[1..bound]` satisfies the property. -/
def pcqAnyUpTo (property : Nat → Prop) : Nat → Prop
  | Nat.zero => False
  | Nat.succ boundPred => Or (pcqAnyUpTo property boundPred) (property (boundPred + 1))

/-- Inject a concrete witness index into the range disjunction. -/
theorem pcqAnyUpToOfWitness (property : Nat → Prop) : ∀ (bound witnessIndex : Nat),
    Nat.ble 1 witnessIndex = true → Nat.ble witnessIndex bound = true →
    property witnessIndex → pcqAnyUpTo property bound
  | Nat.zero, witnessIndex, positiveWitness, boundWitness, _propertyWitness =>
      nomatch Nat.le_trans (lfkNatLeOfBle 1 witnessIndex positiveWitness)
        (lfkNatLeOfBle witnessIndex 0 boundWitness)
  | Nat.succ boundPred, witnessIndex, positiveWitness, boundWitness, propertyWitness =>
      match lfmBoolCases (Nat.beq witnessIndex (boundPred + 1)) with
      | Or.inl topHit =>
          Or.inr (lfkNatEqOfBeq witnessIndex (boundPred + 1) topHit ▸ propertyWitness)
      | Or.inr topMiss =>
          Or.inl (pcqAnyUpToOfWitness property boundPred witnessIndex positiveWitness
            (lfkNatBleOfLe witnessIndex boundPred
              (pcqNatLeOfLeSuccNe witnessIndex boundPred
                (lfkNatLeOfBle witnessIndex (boundPred + 1) boundWitness) topMiss))
            propertyWitness)

/-- Extract a concrete witness index from the range disjunction. -/
theorem pcqAnyUpToElim (property : Nat → Prop) : ∀ (bound : Nat),
    pcqAnyUpTo property bound →
    ∃ (witnessIndex : Nat), And (Nat.ble 1 witnessIndex = true)
      (And (Nat.ble witnessIndex bound = true) (property witnessIndex))
  | Nat.zero, anyWitness => False.elim anyWitness
  | Nat.succ boundPred, anyWitness =>
      (match anyWitness with
      | Or.inl tailAny =>
          (match pcqAnyUpToElim property boundPred tailAny with
          | Exists.intro witnessIndex bundle =>
              Exists.intro witnessIndex
                (And.intro bundle.left
                  (And.intro
                    (lfkNatBleOfLe witnessIndex (boundPred + 1)
                      (Nat.le_trans
                        (lfkNatLeOfBle witnessIndex boundPred bundle.right.left)
                        (Nat.le_succ boundPred)))
                    bundle.right.right)))
      | Or.inr topHolds =>
          Exists.intro (boundPred + 1)
            (And.intro (lfkNatBleOfLe 1 (boundPred + 1)
                (Nat.succ_le_succ (Nat.zero_le boundPred)))
              (And.intro (lfkNatBleOfLe (boundPred + 1) (boundPred + 1)
                  (Nat.le_refl (boundPred + 1)))
                topHolds)))

/-- Map a pointwise implication across the range disjunction. -/
theorem pcqAnyUpToMap (sourceProperty targetProperty : Nat → Prop)
    (pointwiseMap : ∀ (index : Nat), sourceProperty index → targetProperty index) :
    ∀ (bound : Nat), pcqAnyUpTo sourceProperty bound → pcqAnyUpTo targetProperty bound
  | Nat.zero, anyWitness => False.elim anyWitness
  | Nat.succ boundPred, anyWitness =>
      (match anyWitness with
      | Or.inl tailAny =>
          Or.inl (pcqAnyUpToMap sourceProperty targetProperty pointwiseMap boundPred tailAny)
      | Or.inr topHolds => Or.inr (pointwiseMap (boundPred + 1) topHolds))

/-- Some term in the list satisfies the property. -/
def pcqAnyTerm (property : PcqTerm → Prop) : List PcqTerm → Prop
  | List.nil => False
  | headTerm :: tailTerms => Or (property headTerm) (pcqAnyTerm property tailTerms)

/-- Map a pointwise implication across the term disjunction. -/
theorem pcqAnyTermMap (sourceProperty targetProperty : PcqTerm → Prop)
    (pointwiseMap : ∀ (term : PcqTerm), sourceProperty term → targetProperty term) :
    ∀ (termList : List PcqTerm), pcqAnyTerm sourceProperty termList →
    pcqAnyTerm targetProperty termList
  | List.nil, anyWitness => False.elim anyWitness
  | headTerm :: tailTerms, anyWitness =>
      (match anyWitness with
      | Or.inl headHolds => Or.inl (pointwiseMap headTerm headHolds)
      | Or.inr tailAny =>
          Or.inr (pcqAnyTermMap sourceProperty targetProperty pointwiseMap tailTerms tailAny))

/-- Inject the left list into a concatenation's disjunction. -/
theorem pcqAnyTermConcatLeft (property : PcqTerm → Prop) :
    ∀ (firstList secondList : List PcqTerm), pcqAnyTerm property firstList →
    pcqAnyTerm property (pcqTermListConcat firstList secondList)
  | List.nil, _secondList, anyWitness => False.elim anyWitness
  | _headTerm :: tailTerms, secondList, anyWitness =>
      (match anyWitness with
      | Or.inl headHolds => Or.inl headHolds
      | Or.inr tailAny =>
          Or.inr (pcqAnyTermConcatLeft property tailTerms secondList tailAny))

/-- Inject the right list into a concatenation's disjunction. -/
theorem pcqAnyTermConcatRight (property : PcqTerm → Prop) :
    ∀ (firstList secondList : List PcqTerm), pcqAnyTerm property secondList →
    pcqAnyTerm property (pcqTermListConcat firstList secondList)
  | List.nil, _secondList, anyWitness => anyWitness
  | _headTerm :: tailTerms, secondList, anyWitness =>
      Or.inr (pcqAnyTermConcatRight property tailTerms secondList anyWitness)

/-! ## Stage C3 — periodicity: the minus-infinity form is invariant under
delta-multiple shifts of the pivot (Chaieb–Nipkow fact (7), pair-shift form) -/

/-- Shift invariance of the minus-infinity form: only divisibility atoms
mention the pivot, and each modulus divides the shift multiplier. -/
theorem pcqMinusInfShift (env : List LfkInt) (deltaValue : Nat) (shiftValue : LfkInt) :
    ∀ (matrix : PcqMatrix) (pivotValue : LfkInt),
    pcqAllModuliDivide matrix deltaValue →
    pcqMatrixHolds env pivotValue (pcqMinusInf matrix) →
    pcqMatrixHolds env (lfkIntAdd pivotValue (lfkIntScaleByNat deltaValue shiftValue))
      (pcqMinusInf matrix)
  | PcqMatrix.mtrue, _pivotValue, _divideWitness, _holdsWitness => True.intro
  | PcqMatrix.mfalse, _pivotValue, _divideWitness, holdsWitness => holdsWitness
  | PcqMatrix.mupper _bound, _pivotValue, _divideWitness, _holdsWitness => True.intro
  | PcqMatrix.mlower _bound, _pivotValue, _divideWitness, holdsWitness => False.elim holdsWitness
  | PcqMatrix.mdvd modulusPred offset, pivotValue, divideWitness, holdsWitness =>
      (match divideWitness with
      | Exists.intro cofactor cofactorEq =>
          let offsetValue := pcqTermEval env offset
          let planEq : lfkIntAdd (lfkIntAdd pivotValue offsetValue)
              (lfkIntScaleByNat ((modulusPred + 1) * cofactor) shiftValue)
              = lfkIntAdd (lfkIntAdd pivotValue (lfkIntScaleByNat deltaValue shiftValue))
                  offsetValue :=
            (congrArg (fun probe => lfkIntAdd (lfkIntAdd pivotValue offsetValue) probe)
                (congrArg (fun probe => lfkIntScaleByNat probe shiftValue) cofactorEq)).trans
              (pcqIntAddRightSwap pivotValue offsetValue
                (lfkIntScaleByNat deltaValue shiftValue))
          pcqDividesCrossEq (pcqIntEqOfEq planEq)
            (pcqDividesAddScaled (modulusPred + 1) cofactor
              (lfkIntAdd pivotValue offsetValue) shiftValue holdsWitness))
  | PcqMatrix.mndvd modulusPred offset, pivotValue, divideWitness, holdsWitness =>
      (match divideWitness with
      | Exists.intro cofactor cofactorEq =>
          let offsetValue := pcqTermEval env offset
          let planEq : lfkIntAdd (lfkIntAdd pivotValue offsetValue)
              (lfkIntScaleByNat ((modulusPred + 1) * cofactor) shiftValue)
              = lfkIntAdd (lfkIntAdd pivotValue (lfkIntScaleByNat deltaValue shiftValue))
                  offsetValue :=
            (congrArg (fun probe => lfkIntAdd (lfkIntAdd pivotValue offsetValue) probe)
                (congrArg (fun probe => lfkIntScaleByNat probe shiftValue) cofactorEq)).trans
              (pcqIntAddRightSwap pivotValue offsetValue
                (lfkIntScaleByNat deltaValue shiftValue))
          fun shiftedWitness =>
            holdsWitness
              (pcqDividesDropScaled (modulusPred + 1) cofactor
                (lfkIntAdd pivotValue offsetValue) shiftValue
                (pcqDividesCrossEq (pcqIntEqOfEq planEq.symm) shiftedWitness)))
  | PcqMatrix.mfreelt _leftTerm _rightTerm, _pivotValue, _divideWitness, holdsWitness =>
      holdsWitness
  | PcqMatrix.mfreedvd _modulusPred _target, _pivotValue, _divideWitness, holdsWitness =>
      holdsWitness
  | PcqMatrix.mfreendvd _modulusPred _target, _pivotValue, _divideWitness, holdsWitness =>
      holdsWitness
  | PcqMatrix.mconj leftBranch rightBranch, pivotValue, divideWitness, holdsWitness =>
      And.intro
        (pcqMinusInfShift env deltaValue shiftValue leftBranch pivotValue
          divideWitness.left holdsWitness.left)
        (pcqMinusInfShift env deltaValue shiftValue rightBranch pivotValue
          divideWitness.right holdsWitness.right)
  | PcqMatrix.mdisj leftBranch rightBranch, pivotValue, divideWitness, holdsWitness =>
      (match holdsWitness with
      | Or.inl leftHolds =>
          Or.inl (pcqMinusInfShift env deltaValue shiftValue leftBranch pivotValue
            divideWitness.left leftHolds)
      | Or.inr rightHolds =>
          Or.inr (pcqMinusInfShift env deltaValue shiftValue rightBranch pivotValue
            divideWitness.right rightHolds))

/-! ## Stage C4 — agreement below a computed threshold (Chaieb–Nipkow (6)) -/

/-- The low threshold: below it, every bound atom agrees with its
minus-infinity substitution. -/
def pcqLowThreshold (env : List LfkInt) : PcqMatrix → LfkInt
  | PcqMatrix.mtrue => lfkIntZero
  | PcqMatrix.mfalse => lfkIntZero
  | PcqMatrix.mupper bound => pcqTermEval env bound
  | PcqMatrix.mlower bound => lfkIntAdd (pcqTermEval env bound) lreIntOne
  | PcqMatrix.mdvd _modulusPred _offset => lfkIntZero
  | PcqMatrix.mndvd _modulusPred _offset => lfkIntZero
  | PcqMatrix.mfreelt _leftTerm _rightTerm => lfkIntZero
  | PcqMatrix.mfreedvd _modulusPred _target => lfkIntZero
  | PcqMatrix.mfreendvd _modulusPred _target => lfkIntZero
  | PcqMatrix.mconj leftBranch rightBranch =>
      pcqIntLesser (pcqLowThreshold env leftBranch) (pcqLowThreshold env rightBranch)
  | PcqMatrix.mdisj leftBranch rightBranch =>
      pcqIntLesser (pcqLowThreshold env leftBranch) (pcqLowThreshold env rightBranch)

/-- Below the threshold the matrix and its minus-infinity form agree. -/
theorem pcqMinusInfAgreesBelow (env : List LfkInt) :
    ∀ (matrix : PcqMatrix) (pivotValue : LfkInt),
    lfkIntLt pivotValue (pcqLowThreshold env matrix) = true →
    Iff (pcqMatrixHolds env pivotValue matrix)
      (pcqMatrixHolds env pivotValue (pcqMinusInf matrix))
  | PcqMatrix.mtrue, _pivotValue, _belowWitness => Iff.rfl
  | PcqMatrix.mfalse, _pivotValue, _belowWitness => Iff.rfl
  | PcqMatrix.mupper _bound, _pivotValue, belowWitness =>
      Iff.intro (fun _holdsWitness => True.intro) (fun _trivialWitness => belowWitness)
  | PcqMatrix.mlower _bound, _pivotValue, belowWitness =>
      Iff.intro
        (fun holdsWitness =>
          pcqIntLtLeAbsurd holdsWitness (pcqIntLeOfLtSucc belowWitness))
        (fun falseWitness => False.elim falseWitness)
  | PcqMatrix.mdvd _modulusPred _offset, _pivotValue, _belowWitness => Iff.rfl
  | PcqMatrix.mndvd _modulusPred _offset, _pivotValue, _belowWitness => Iff.rfl
  | PcqMatrix.mfreelt _leftTerm _rightTerm, _pivotValue, _belowWitness => Iff.rfl
  | PcqMatrix.mfreedvd _modulusPred _target, _pivotValue, _belowWitness => Iff.rfl
  | PcqMatrix.mfreendvd _modulusPred _target, _pivotValue, _belowWitness => Iff.rfl
  | PcqMatrix.mconj leftBranch rightBranch, pivotValue, belowWitness =>
      let leftIff := pcqMinusInfAgreesBelow env leftBranch pivotValue
        (pcqIntLtOfLtLe belowWitness
          (pcqIntLesserLeLeft (pcqLowThreshold env leftBranch)
            (pcqLowThreshold env rightBranch)))
      let rightIff := pcqMinusInfAgreesBelow env rightBranch pivotValue
        (pcqIntLtOfLtLe belowWitness
          (pcqIntLesserLeRight (pcqLowThreshold env leftBranch)
            (pcqLowThreshold env rightBranch)))
      Iff.intro
        (fun holdsWitness =>
          And.intro (leftIff.mp holdsWitness.left) (rightIff.mp holdsWitness.right))
        (fun holdsWitness =>
          And.intro (leftIff.mpr holdsWitness.left) (rightIff.mpr holdsWitness.right))
  | PcqMatrix.mdisj leftBranch rightBranch, pivotValue, belowWitness =>
      let leftIff := pcqMinusInfAgreesBelow env leftBranch pivotValue
        (pcqIntLtOfLtLe belowWitness
          (pcqIntLesserLeLeft (pcqLowThreshold env leftBranch)
            (pcqLowThreshold env rightBranch)))
      let rightIff := pcqMinusInfAgreesBelow env rightBranch pivotValue
        (pcqIntLtOfLtLe belowWitness
          (pcqIntLesserLeRight (pcqLowThreshold env leftBranch)
            (pcqLowThreshold env rightBranch)))
      Iff.intro
        (fun holdsWitness =>
          match holdsWitness with
          | Or.inl leftHolds => Or.inl (leftIff.mp leftHolds)
          | Or.inr rightHolds => Or.inr (rightIff.mp rightHolds))
        (fun holdsWitness =>
          match holdsWitness with
          | Or.inl leftHolds => Or.inl (leftIff.mpr leftHolds)
          | Or.inr rightHolds => Or.inr (rightIff.mpr rightHolds))

/-! ## Stage C5 — the descent lemma (Chaieb–Nipkow (9)): descend by delta or
land in a lower-bound window -/

/-- One descent step: either the matrix still holds at `pivot - delta`, or
the pivot sits in some window `(b, b + delta]` of a lower bound `b`. -/
theorem pcqDescentWindow (env : List LfkInt) (deltaValue : Nat)
    (deltaPositive : Nat.ble 1 deltaValue = true) :
    ∀ (matrix : PcqMatrix) (pivotValue : LfkInt),
    pcqAllModuliDivide matrix deltaValue →
    pcqMatrixHolds env pivotValue matrix →
    Or
      (pcqMatrixHolds env
        (lfkIntAdd pivotValue (lfkIntNegate (lreIntOfNat deltaValue))) matrix)
      (pcqAnyTerm
        (fun boundTerm => pcqAnyUpTo
          (fun windowIndex => lfkIntEq pivotValue
            (lfkIntAdd (pcqTermEval env boundTerm) (lreIntOfNat windowIndex)) = true)
          deltaValue)
        (pcqLowerBounds matrix))
  | PcqMatrix.mtrue, _pivotValue, _divideWitness, _holdsWitness => Or.inl True.intro
  | PcqMatrix.mfalse, _pivotValue, _divideWitness, holdsWitness => False.elim holdsWitness
  | PcqMatrix.mupper _bound, _pivotValue, _divideWitness, holdsWitness =>
      Or.inl
        (lreIntLtOfLeSubPositive
          (lreIntOfNatIsPositive deltaValue deltaPositive)
          (lfkIntLeOfLt holdsWitness))
  | PcqMatrix.mlower bound, pivotValue, _divideWitness, holdsWitness =>
      (match lfmBoolCases (lfkIntLt (pcqTermEval env bound)
          (lfkIntAdd pivotValue (lfkIntNegate (lreIntOfNat deltaValue)))) with
      | Or.inl descendedStrict => Or.inl descendedStrict
      | Or.inr descendedFalse =>
          let boundValue := pcqTermEval env bound
          let bigLower := boundValue.positivePart + pivotValue.negativePart
          let bigUpper := pivotValue.positivePart + boundValue.negativePart
          let strictNat : Nat.le (bigLower + 1) bigUpper :=
            lfkNatLeOfBle (bigLower + 1) bigUpper holdsWitness
          let weakNat : Nat.le bigUpper (bigLower + deltaValue) :=
            lfkNatLeCongr rfl
              (Nat.add_assoc boundValue.positivePart pivotValue.negativePart deltaValue)
              (lfkNatLeOfBle _ _ (pcqIntLtFalseGivesLe descendedFalse))
          let windowIndex := lfmNatDelta bigUpper bigLower
          let recovery : bigLower + windowIndex = bigUpper :=
            lfmNatDeltaRecovers bigUpper bigLower
              (lfkNatBleOfLe bigLower bigUpper
                (Nat.le_trans (Nat.le_succ bigLower) strictNat))
          let indexPositive : Nat.le 1 windowIndex :=
            pcqNatLeCancelAddLeft bigLower 1 windowIndex
              (lfkNatLeCongr rfl recovery strictNat)
          let indexBounded : Nat.le windowIndex deltaValue :=
            pcqNatLeCancelAddLeft bigLower windowIndex deltaValue
              (lfkNatLeCongr recovery rfl weakNat)
          let windowCrossEq : lfkIntEq pivotValue
              (lfkIntAdd boundValue (lreIntOfNat windowIndex)) = true :=
            lfkNatBeqOfEq _ _
              ((lreNatAddRightSwap boundValue.positivePart windowIndex
                  pivotValue.negativePart).trans recovery).symm
          Or.inr
            (Or.inl
              (pcqAnyUpToOfWitness _ deltaValue windowIndex
                (lfkNatBleOfLe 1 windowIndex indexPositive)
                (lfkNatBleOfLe windowIndex deltaValue indexBounded)
                windowCrossEq)))
  | PcqMatrix.mdvd modulusPred offset, pivotValue, divideWitness, holdsWitness =>
      (match divideWitness with
      | Exists.intro cofactor cofactorEq =>
          let offsetValue := pcqTermEval env offset
          let scalePieceEq : lfkIntScaleByNat ((modulusPred + 1) * cofactor)
              (lfkIntNegate lreIntOne) = lfkIntNegate (lreIntOfNat deltaValue) :=
            (congrArg (fun probe => lfkIntScaleByNat probe (lfkIntNegate lreIntOne))
                cofactorEq).trans
              (lfkIntMkCongr rfl (Nat.mul_one deltaValue))
          let planEq : lfkIntAdd (lfkIntAdd pivotValue offsetValue)
              (lfkIntScaleByNat ((modulusPred + 1) * cofactor) (lfkIntNegate lreIntOne))
              = lfkIntAdd
                  (lfkIntAdd pivotValue (lfkIntNegate (lreIntOfNat deltaValue)))
                  offsetValue :=
            (congrArg (fun probe => lfkIntAdd (lfkIntAdd pivotValue offsetValue) probe)
                scalePieceEq).trans
              (pcqIntAddRightSwap pivotValue offsetValue
                (lfkIntNegate (lreIntOfNat deltaValue)))
          Or.inl
            (pcqDividesCrossEq (pcqIntEqOfEq planEq)
              (pcqDividesAddScaled (modulusPred + 1) cofactor
                (lfkIntAdd pivotValue offsetValue) (lfkIntNegate lreIntOne) holdsWitness)))
  | PcqMatrix.mndvd modulusPred offset, pivotValue, divideWitness, holdsWitness =>
      (match divideWitness with
      | Exists.intro cofactor cofactorEq =>
          let offsetValue := pcqTermEval env offset
          let scalePieceEq : lfkIntScaleByNat ((modulusPred + 1) * cofactor)
              (lfkIntNegate lreIntOne) = lfkIntNegate (lreIntOfNat deltaValue) :=
            (congrArg (fun probe => lfkIntScaleByNat probe (lfkIntNegate lreIntOne))
                cofactorEq).trans
              (lfkIntMkCongr rfl (Nat.mul_one deltaValue))
          let planEq : lfkIntAdd (lfkIntAdd pivotValue offsetValue)
              (lfkIntScaleByNat ((modulusPred + 1) * cofactor) (lfkIntNegate lreIntOne))
              = lfkIntAdd
                  (lfkIntAdd pivotValue (lfkIntNegate (lreIntOfNat deltaValue)))
                  offsetValue :=
            (congrArg (fun probe => lfkIntAdd (lfkIntAdd pivotValue offsetValue) probe)
                scalePieceEq).trans
              (pcqIntAddRightSwap pivotValue offsetValue
                (lfkIntNegate (lreIntOfNat deltaValue)))
          Or.inl
            (fun descendedWitness =>
              holdsWitness
                (pcqDividesDropScaled (modulusPred + 1) cofactor
                  (lfkIntAdd pivotValue offsetValue) (lfkIntNegate lreIntOne)
                  (pcqDividesCrossEq (pcqIntEqOfEq planEq.symm) descendedWitness))))
  | PcqMatrix.mfreelt _leftTerm _rightTerm, _pivotValue, _divideWitness, holdsWitness =>
      Or.inl holdsWitness
  | PcqMatrix.mfreedvd _modulusPred _target, _pivotValue, _divideWitness, holdsWitness =>
      Or.inl holdsWitness
  | PcqMatrix.mfreendvd _modulusPred _target, _pivotValue, _divideWitness, holdsWitness =>
      Or.inl holdsWitness
  | PcqMatrix.mconj leftBranch rightBranch, pivotValue, divideWitness, holdsWitness =>
      (match pcqDescentWindow env deltaValue deltaPositive leftBranch pivotValue
          divideWitness.left holdsWitness.left with
      | Or.inr leftWindow =>
          Or.inr (pcqAnyTermConcatLeft _ (pcqLowerBounds leftBranch)
            (pcqLowerBounds rightBranch) leftWindow)
      | Or.inl leftDescends =>
          (match pcqDescentWindow env deltaValue deltaPositive rightBranch pivotValue
              divideWitness.right holdsWitness.right with
          | Or.inr rightWindow =>
              Or.inr (pcqAnyTermConcatRight _ (pcqLowerBounds leftBranch)
                (pcqLowerBounds rightBranch) rightWindow)
          | Or.inl rightDescends => Or.inl (And.intro leftDescends rightDescends)))
  | PcqMatrix.mdisj leftBranch rightBranch, pivotValue, divideWitness, holdsWitness =>
      (match holdsWitness with
      | Or.inl leftHolds =>
          (match pcqDescentWindow env deltaValue deltaPositive leftBranch pivotValue
              divideWitness.left leftHolds with
          | Or.inl leftDescends => Or.inl (Or.inl leftDescends)
          | Or.inr leftWindow =>
              Or.inr (pcqAnyTermConcatLeft _ (pcqLowerBounds leftBranch)
                (pcqLowerBounds rightBranch) leftWindow))
      | Or.inr rightHolds =>
          (match pcqDescentWindow env deltaValue deltaPositive rightBranch pivotValue
              divideWitness.right rightHolds with
          | Or.inl rightDescends => Or.inl (Or.inr rightDescends)
          | Or.inr rightWindow =>
              Or.inr (pcqAnyTermConcatRight _ (pcqLowerBounds leftBranch)
                (pcqLowerBounds rightBranch) rightWindow)))

/-! ## Stage C6 — the executable window test and its reflections -/

/-- Boolean range disjunction. -/
def pcqAnyUpToBool (test : Nat → Bool) : Nat → Bool
  | Nat.zero => false
  | Nat.succ boundPred => pcqAnyUpToBool test boundPred || test (boundPred + 1)

/-- Boolean term-list disjunction. -/
def pcqAnyTermBool (test : PcqTerm → Bool) : List PcqTerm → Bool
  | List.nil => false
  | headTerm :: tailTerms => test headTerm || pcqAnyTermBool test tailTerms

/-- A range disjunction with pointwise Bool support computes to `true`. -/
theorem pcqAnyUpToBoolOfProp (test : Nat → Bool) (property : Nat → Prop)
    (pointwise : ∀ (index : Nat), property index → test index = true) :
    ∀ (bound : Nat), pcqAnyUpTo property bound → pcqAnyUpToBool test bound = true
  | Nat.zero, anyWitness => False.elim anyWitness
  | Nat.succ boundPred, anyWitness =>
      (match anyWitness with
      | Or.inl tailAny =>
          pcqBoolOrIntroLeft (pcqAnyUpToBool test boundPred) (test (boundPred + 1))
            (pcqAnyUpToBoolOfProp test property pointwise boundPred tailAny)
      | Or.inr topHolds =>
          pcqBoolOrIntroRight (pcqAnyUpToBool test boundPred) (test (boundPred + 1))
            (pointwise (boundPred + 1) topHolds))

/-- A true Boolean range disjunction reflects into the Prop disjunction. -/
theorem pcqAnyUpToBoolTrueElim (test : Nat → Bool) : ∀ (bound : Nat),
    pcqAnyUpToBool test bound = true →
    pcqAnyUpTo (fun index => test index = true) bound
  | Nat.zero, boolWitness => Bool.noConfusion boolWitness
  | Nat.succ boundPred, boolWitness =>
      (match pcqBoolOrDestructTrue (pcqAnyUpToBool test boundPred)
        (test (boundPred + 1)) boolWitness with
      | Or.inl tailTrue => Or.inl (pcqAnyUpToBoolTrueElim test boundPred tailTrue)
      | Or.inr topTrue => Or.inr topTrue)

/-- A term disjunction with pointwise Bool support computes to `true`. -/
theorem pcqAnyTermBoolOfProp (test : PcqTerm → Bool) (property : PcqTerm → Prop)
    (pointwise : ∀ (term : PcqTerm), property term → test term = true) :
    ∀ (termList : List PcqTerm), pcqAnyTerm property termList →
    pcqAnyTermBool test termList = true
  | List.nil, anyWitness => False.elim anyWitness
  | headTerm :: tailTerms, anyWitness =>
      (match anyWitness with
      | Or.inl headHolds =>
          pcqBoolOrIntroLeft (test headTerm) (pcqAnyTermBool test tailTerms)
            (pointwise headTerm headHolds)
      | Or.inr tailAny =>
          pcqBoolOrIntroRight (test headTerm) (pcqAnyTermBool test tailTerms)
            (pcqAnyTermBoolOfProp test property pointwise tailTerms tailAny))

/-- A true Boolean term disjunction reflects into the Prop disjunction. -/
theorem pcqAnyTermBoolTrueElim (test : PcqTerm → Bool) : ∀ (termList : List PcqTerm),
    pcqAnyTermBool test termList = true →
    pcqAnyTerm (fun term => test term = true) termList
  | List.nil, boolWitness => Bool.noConfusion boolWitness
  | headTerm :: tailTerms, boolWitness =>
      (match pcqBoolOrDestructTrue (test headTerm)
        (pcqAnyTermBool test tailTerms) boolWitness with
      | Or.inl headTrue => Or.inl headTrue
      | Or.inr tailTrue => Or.inr (pcqAnyTermBoolTrueElim test tailTerms tailTrue))

/-- THE WINDOW TEST: does some `b + j` (lower bound `b`, `j` in `[1..delta]`)
satisfy the matrix? -/
def pcqWindowTest (env : List LfkInt) (matrix : PcqMatrix) : Bool :=
  pcqAnyTermBool
    (fun boundTerm => pcqAnyUpToBool
      (fun windowIndex => pcqMatrixEval env
        (lfkIntAdd (pcqTermEval env boundTerm) (lreIntOfNat windowIndex)) matrix)
      (pcqDelta matrix))
    (pcqLowerBounds matrix)

/-! ## Stage C7 — iterated descent and the reach-below construction -/

/-- One descent step under a failed window test. -/
theorem pcqDescentStep (env : List LfkInt) (matrix : PcqMatrix)
    (noWindow : pcqWindowTest env matrix = false) (pivotValue : LfkInt)
    (holdsWitness : pcqMatrixHolds env pivotValue matrix) :
    pcqMatrixHolds env
      (lfkIntAdd pivotValue (lfkIntNegate (lreIntOfNat (pcqDelta matrix)))) matrix :=
  match pcqDescentWindow env (pcqDelta matrix) (pcqDeltaPositive matrix) matrix pivotValue
    (pcqModuliDivideDelta matrix) holdsWitness with
  | Or.inl descended => descended
  | Or.inr windowProp =>
      let windowTrue : pcqWindowTest env matrix = true :=
        pcqAnyTermBoolOfProp _ _
          (fun boundTerm innerAny =>
            pcqAnyUpToBoolOfProp _ _
              (fun windowIndex pivotCrossEq =>
                pcqMatrixEvalOfHolds env
                  (lfkIntAdd (pcqTermEval env boundTerm) (lreIntOfNat windowIndex)) matrix
                  (pcqMatrixHoldsCrossEq env pivotCrossEq matrix holdsWitness))
              (pcqDelta matrix) innerAny)
          (pcqLowerBounds matrix) windowProp
      False.elim (Bool.noConfusion (noWindow.symm.trans windowTrue))

/-- Iterated descent: under a failed window test the matrix holds at every
`pivot - stepCount * delta`. -/
theorem pcqDescentMany (env : List LfkInt) (matrix : PcqMatrix)
    (noWindow : pcqWindowTest env matrix = false) (pivotValue : LfkInt)
    (holdsWitness : pcqMatrixHolds env pivotValue matrix) :
    ∀ (stepCount : Nat),
    pcqMatrixHolds env
      (lfkIntAdd pivotValue (lfkIntScaleByNat (pcqDelta matrix) (LfkInt.mk 0 stepCount)))
      matrix
  | Nat.zero => holdsWitness
  | Nat.succ stepPred =>
      let previousPoint := lfkIntAdd pivotValue
        (lfkIntScaleByNat (pcqDelta matrix) (LfkInt.mk 0 stepPred))
      let steppedHolds : pcqMatrixHolds env
          (lfkIntAdd previousPoint (lfkIntNegate (lreIntOfNat (pcqDelta matrix)))) matrix :=
        pcqDescentStep env matrix noWindow previousPoint
          (pcqDescentMany env matrix noWindow pivotValue holdsWitness stepPred)
      let planEq : lfkIntAdd previousPoint (lfkIntNegate (lreIntOfNat (pcqDelta matrix)))
          = lfkIntAdd pivotValue
              (lfkIntScaleByNat (pcqDelta matrix) (LfkInt.mk 0 (stepPred + 1))) :=
        lfkIntMkCongr rfl
          (Nat.add_assoc pivotValue.negativePart
            (pcqDelta matrix * stepPred) (pcqDelta matrix))
      pcqMatrixHoldsCrossEq env (pcqIntEqOfEq planEq) matrix steppedHolds

/-- A positive multiplier dominates: `base <= delta * base`. -/
theorem pcqNatLeMulOfPositive (baseValue deltaValue : Nat)
    (deltaPositive : Nat.ble 1 deltaValue = true) :
    Nat.le baseValue (deltaValue * baseValue) :=
  lfkNatLeCongr (Nat.mul_one baseValue).symm (Nat.mul_comm deltaValue baseValue)
    (lfkNatMulLeMulLeft baseValue (lfkNatLeOfBle 1 deltaValue deltaPositive))

/-- Reach strictly below any threshold by subtracting enough delta steps. -/
theorem pcqReachBelowThreshold (deltaValue : Nat)
    (deltaPositive : Nat.ble 1 deltaValue = true)
    (startValue thresholdValue : LfkInt) :
    ∃ (stepCount : Nat),
      lfkIntLt
        (lfkIntAdd startValue (lfkIntScaleByNat deltaValue (LfkInt.mk 0 stepCount)))
        thresholdValue = true :=
  let stepCount := (startValue.positivePart + thresholdValue.negativePart) + 1
  Exists.intro stepCount
    (lfkNatBleOfLe _ _
      (Nat.le_trans (pcqNatLeMulOfPositive stepCount deltaValue deltaPositive)
        (lfkNatLeCongr rfl
          (Nat.add_assoc thresholdValue.positivePart startValue.negativePart
            (deltaValue * stepCount)).symm
          (lreNatLeAddLeft (thresholdValue.positivePart + startValue.negativePart)
            (deltaValue * stepCount)))))

/-! ## Stage C8 — window reduction: shift any point into `[1..delta]` modulo
delta (the counting-divider congruence) -/

/-- Reduce any pair integer into the window `[1..delta]` by a delta-multiple
shift. -/
theorem pcqWindowReduce : ∀ (deltaValue : Nat), Nat.ble 1 deltaValue = true →
    ∀ (targetValue : LfkInt),
    ∃ (windowIndex : Nat), ∃ (shiftPair : LfkInt),
      And (Nat.ble 1 windowIndex = true)
        (And (Nat.ble windowIndex deltaValue = true)
          (lfkIntEq (lfkIntAdd targetValue (lfkIntScaleByNat deltaValue shiftPair))
            (lreIntOfNat windowIndex) = true))
  | Nat.zero, contradictoryWitness, _targetValue => Bool.noConfusion contradictoryWitness
  | Nat.succ deltaPred, _positiveWitness, targetValue =>
      let remainderValue := pcqIntRemainder deltaPred targetValue
      let quotientPair := LfkInt.mk (pcqIntQuotientPart deltaPred targetValue)
        targetValue.negativePart
      let scaledQuotient := lfkIntScaleByNat (deltaPred + 1) quotientPair
      let decomposition : lfkIntEq targetValue
          (lfkIntAdd scaledQuotient (lreIntOfNat remainderValue)) = true :=
        pcqIntRemainderDecomposition deltaPred targetValue
      match lfmBoolCases (Nat.beq remainderValue 0) with
      | Or.inl remainderZeroBeq =>
          let remainderZero : remainderValue = 0 :=
            lfkNatEqOfBeq remainderValue 0 remainderZeroBeq
          let collapsedDecomposition : lfkIntEq targetValue scaledQuotient = true :=
            (congrArg (fun probe => lfkIntEq targetValue
                (lfkIntAdd scaledQuotient (lreIntOfNat probe))) remainderZero).symm.trans
              decomposition
          let shiftPair := lfkIntAdd lreIntOne (lfkIntNegate quotientPair)
          let distributeEq : lfkIntAdd targetValue
              (lfkIntScaleByNat (deltaPred + 1) shiftPair)
              = lfkIntAdd targetValue
                  (lfkIntAdd (lfkIntScaleByNat (deltaPred + 1) lreIntOne)
                    (lfkIntNegate scaledQuotient)) :=
            congrArg (fun probe => lfkIntAdd targetValue probe)
              (lfkIntScaleAddDistrib (deltaPred + 1) lreIntOne (lfkIntNegate quotientPair))
          let substituteEq : lfkIntEq
              (lfkIntAdd targetValue
                (lfkIntAdd (lfkIntScaleByNat (deltaPred + 1) lreIntOne)
                  (lfkIntNegate scaledQuotient)))
              (lfkIntAdd scaledQuotient
                (lfkIntAdd (lfkIntScaleByNat (deltaPred + 1) lreIntOne)
                  (lfkIntNegate scaledQuotient))) = true :=
            lfkIntAddEqEq collapsedDecomposition
              (lfkIntEqRefl (lfkIntAdd (lfkIntScaleByNat (deltaPred + 1) lreIntOne)
                (lfkIntNegate scaledQuotient)))
          let commuteEq : lfkIntAdd scaledQuotient
              (lfkIntAdd (lfkIntScaleByNat (deltaPred + 1) lreIntOne)
                (lfkIntNegate scaledQuotient))
              = lfkIntAdd (lfkIntScaleByNat (deltaPred + 1) lreIntOne)
                  (lfkIntAdd scaledQuotient (lfkIntNegate scaledQuotient)) :=
            lreIntAddLeftCommute scaledQuotient
              (lfkIntScaleByNat (deltaPred + 1) lreIntOne) (lfkIntNegate scaledQuotient)
          let dropEq : lfkIntEq
              (lfkIntAdd (lfkIntScaleByNat (deltaPred + 1) lreIntOne)
                (lfkIntAdd scaledQuotient (lfkIntNegate scaledQuotient)))
              (lfkIntScaleByNat (deltaPred + 1) lreIntOne) = true :=
            pcqIntEqDropZeroRight (lreIntAddNegateRightZero scaledQuotient)
          let unitEq : lfkIntScaleByNat (deltaPred + 1) lreIntOne
              = lreIntOfNat (deltaPred + 1) :=
            lfkIntMkCongr (Nat.mul_one (deltaPred + 1)) rfl
          Exists.intro (deltaPred + 1)
            (Exists.intro shiftPair
              (And.intro (lfkNatBleOfLe 1 (deltaPred + 1)
                  (Nat.succ_le_succ (Nat.zero_le deltaPred)))
                (And.intro
                  (lfkNatBleOfLe (deltaPred + 1) (deltaPred + 1) (Nat.le_refl (deltaPred + 1)))
                  (lreIntEqTrans (pcqIntEqOfEq distributeEq)
                    (lreIntEqTrans substituteEq
                      (lreIntEqTrans (pcqIntEqOfEq commuteEq)
                        (lreIntEqTrans dropEq (pcqIntEqOfEq unitEq))))))))
      | Or.inr remainderNonZero =>
          let shiftPair := lfkIntNegate quotientPair
          let substituteEq : lfkIntEq
              (lfkIntAdd targetValue (lfkIntNegate scaledQuotient))
              (lfkIntAdd (lfkIntAdd scaledQuotient (lreIntOfNat remainderValue))
                (lfkIntNegate scaledQuotient)) = true :=
            lfkIntAddEqEq decomposition (lfkIntEqRefl (lfkIntNegate scaledQuotient))
          let cancelEq : lfkIntEq
              (lfkIntAdd (lfkIntAdd scaledQuotient (lreIntOfNat remainderValue))
                (lfkIntNegate scaledQuotient))
              (lreIntOfNat remainderValue) = true :=
            (congrArg (fun probe => lfkIntEq
                (lfkIntAdd probe (lfkIntNegate scaledQuotient))
                (lreIntOfNat remainderValue))
              (lfkIntAddComm scaledQuotient (lreIntOfNat remainderValue))).trans
              (pcqIntAddCancelRight (lreIntOfNat remainderValue) scaledQuotient)
          (match pcqNatNonZeroShape remainderValue remainderNonZero with
          | Exists.intro remainderPred remainderShape =>
              Exists.intro remainderValue
                (Exists.intro shiftPair
                  (And.intro
                    (lfkNatBleOfLe 1 remainderValue
                      (lfkNatLeCongr rfl remainderShape
                        (Nat.succ_le_succ (Nat.zero_le remainderPred))))
                    (And.intro
                      (lfkNatBleOfLe remainderValue (deltaPred + 1)
                        (Nat.le_trans
                          (pcqNatModCountingBound deltaPred
                            (targetValue.positivePart
                              + deltaPred * targetValue.negativePart))
                          (Nat.le_succ deltaPred)))
                      (lreIntEqTrans substituteEq cancelEq)))))

/-! ## Stage C9 — THE COOPER ELIMINATION THEOREM (both directions) -/

/-- Forward: a witness yields the minus-infinity branch or the window
branch. -/
theorem pcqCooperForward (env : List LfkInt) (matrix : PcqMatrix)
    (existsWitness : ∃ (pivotValue : LfkInt), pcqMatrixHolds env pivotValue matrix) :
    Or
      (pcqAnyUpTo (fun windowIndex =>
          pcqMatrixHolds env (lreIntOfNat windowIndex) (pcqMinusInf matrix))
        (pcqDelta matrix))
      (pcqAnyTerm (fun boundTerm => pcqAnyUpTo (fun windowIndex =>
            pcqMatrixHolds env
              (lfkIntAdd (pcqTermEval env boundTerm) (lreIntOfNat windowIndex)) matrix)
          (pcqDelta matrix))
        (pcqLowerBounds matrix)) :=
  match existsWitness with
  | Exists.intro pivotValue holdsWitness =>
      (match lfmBoolCases (pcqWindowTest env matrix) with
      | Or.inl windowTrue =>
          Or.inr
            (pcqAnyTermMap _ _
              (fun boundTerm outerBoolTrue =>
                pcqAnyUpToMap _ _
                  (fun windowIndex evalTrue =>
                    pcqMatrixEvalTrueSound env
                      (lfkIntAdd (pcqTermEval env boundTerm) (lreIntOfNat windowIndex))
                      matrix evalTrue)
                  (pcqDelta matrix)
                  (pcqAnyUpToBoolTrueElim _ (pcqDelta matrix) outerBoolTrue))
              (pcqLowerBounds matrix)
              (pcqAnyTermBoolTrueElim _ (pcqLowerBounds matrix) windowTrue))
      | Or.inr windowFalse =>
          (match pcqReachBelowThreshold (pcqDelta matrix) (pcqDeltaPositive matrix)
            pivotValue (pcqLowThreshold env matrix) with
          | Exists.intro stepCount belowLt =>
              let descendedPoint := lfkIntAdd pivotValue
                (lfkIntScaleByNat (pcqDelta matrix) (LfkInt.mk 0 stepCount))
              let minusInfHolds : pcqMatrixHolds env descendedPoint (pcqMinusInf matrix) :=
                (pcqMinusInfAgreesBelow env matrix descendedPoint belowLt).mp
                  (pcqDescentMany env matrix windowFalse pivotValue holdsWitness stepCount)
              (match pcqWindowReduce (pcqDelta matrix) (pcqDeltaPositive matrix)
                descendedPoint with
              | Exists.intro windowIndex (Exists.intro shiftPair bundle) =>
                  Or.inl
                    (pcqAnyUpToOfWitness _ (pcqDelta matrix) windowIndex
                      bundle.left bundle.right.left
                      (pcqMatrixHoldsCrossEq env bundle.right.right (pcqMinusInf matrix)
                        (pcqMinusInfShift env (pcqDelta matrix) shiftPair matrix
                          descendedPoint (pcqModuliDivideDelta matrix) minusInfHolds))))))

/-- Backward, minus-infinity branch: descend the window witness below the
threshold and transfer back to the matrix. -/
theorem pcqCooperBackwardMinusInf (env : List LfkInt) (matrix : PcqMatrix)
    (branchWitness : pcqAnyUpTo (fun windowIndex =>
        pcqMatrixHolds env (lreIntOfNat windowIndex) (pcqMinusInf matrix))
      (pcqDelta matrix)) :
    ∃ (pivotValue : LfkInt), pcqMatrixHolds env pivotValue matrix :=
  match pcqAnyUpToElim _ (pcqDelta matrix) branchWitness with
  | Exists.intro windowIndex bundle =>
      (match pcqReachBelowThreshold (pcqDelta matrix) (pcqDeltaPositive matrix)
        (lreIntOfNat windowIndex) (pcqLowThreshold env matrix) with
      | Exists.intro stepCount belowLt =>
          let descendedPoint := lfkIntAdd (lreIntOfNat windowIndex)
            (lfkIntScaleByNat (pcqDelta matrix) (LfkInt.mk 0 stepCount))
          Exists.intro descendedPoint
            ((pcqMinusInfAgreesBelow env matrix descendedPoint belowLt).mpr
              (pcqMinusInfShift env (pcqDelta matrix) (LfkInt.mk 0 stepCount) matrix
                (lreIntOfNat windowIndex) (pcqModuliDivideDelta matrix)
                bundle.right.right)))

/-- Backward, window branch: `b + j` is a direct witness. -/
theorem pcqCooperBackwardWindow (env : List LfkInt) (matrix : PcqMatrix) :
    ∀ (termList : List PcqTerm),
    pcqAnyTerm (fun boundTerm => pcqAnyUpTo (fun windowIndex =>
        pcqMatrixHolds env
          (lfkIntAdd (pcqTermEval env boundTerm) (lreIntOfNat windowIndex)) matrix)
      (pcqDelta matrix)) termList →
    ∃ (pivotValue : LfkInt), pcqMatrixHolds env pivotValue matrix
  | List.nil, anyWitness => False.elim anyWitness
  | headTerm :: tailTerms, anyWitness =>
      (match anyWitness with
      | Or.inl innerAny =>
          (match pcqAnyUpToElim _ (pcqDelta matrix) innerAny with
          | Exists.intro windowIndex bundle =>
              Exists.intro
                (lfkIntAdd (pcqTermEval env headTerm) (lreIntOfNat windowIndex))
                bundle.right.right)
      | Or.inr tailAny => pcqCooperBackwardWindow env matrix tailTerms tailAny)

/-- THE COOPER ELIMINATION THEOREM: existence of a pivot is EXACTLY the
minus-infinity disjunction or the boundary-window disjunction, both over
`[1..delta]` (Chaieb–Nipkow fact (10), proven constructively). -/
theorem pcqCooperElimination (env : List LfkInt) (matrix : PcqMatrix) :
    Iff (∃ (pivotValue : LfkInt), pcqMatrixHolds env pivotValue matrix)
      (Or
        (pcqAnyUpTo (fun windowIndex =>
            pcqMatrixHolds env (lreIntOfNat windowIndex) (pcqMinusInf matrix))
          (pcqDelta matrix))
        (pcqAnyTerm (fun boundTerm => pcqAnyUpTo (fun windowIndex =>
              pcqMatrixHolds env
                (lfkIntAdd (pcqTermEval env boundTerm) (lreIntOfNat windowIndex)) matrix)
            (pcqDelta matrix))
          (pcqLowerBounds matrix))) :=
  Iff.intro
    (fun existsWitness => pcqCooperForward env matrix existsWitness)
    (fun branchWitness =>
      match branchWitness with
      | Or.inl minusInfBranch => pcqCooperBackwardMinusInf env matrix minusInfBranch
      | Or.inr windowBranch =>
          pcqCooperBackwardWindow env matrix (pcqLowerBounds matrix) windowBranch)

/-! ## Stage B1 — negation normal form (negation survives only on
divisibility; inequality negation flips through the succ-le encoding) -/

/-- NNF formulas: no negation connective; negated divisibility is an atom. -/
inductive PcqNnfFormula where
  | nlt (leftTerm rightTerm : PcqTerm) : PcqNnfFormula
  | ndvd (modulusPred : Nat) (target : PcqTerm) : PcqNnfFormula
  | nndvd (modulusPred : Nat) (target : PcqTerm) : PcqNnfFormula
  | nconj (leftBranch rightBranch : PcqNnfFormula) : PcqNnfFormula
  | ndisj (leftBranch rightBranch : PcqNnfFormula) : PcqNnfFormula

/-- Prop semantics of the NNF layer. -/
def pcqNnfHolds (env : List LfkInt) : PcqNnfFormula → Prop
  | PcqNnfFormula.nlt leftTerm rightTerm =>
      lfkIntLt (pcqTermEval env leftTerm) (pcqTermEval env rightTerm) = true
  | PcqNnfFormula.ndvd modulusPred target =>
      pcqDividesProp (modulusPred + 1) (pcqTermEval env target)
  | PcqNnfFormula.nndvd modulusPred target =>
      pcqDividesProp (modulusPred + 1) (pcqTermEval env target) → False
  | PcqNnfFormula.nconj leftBranch rightBranch =>
      And (pcqNnfHolds env leftBranch) (pcqNnfHolds env rightBranch)
  | PcqNnfFormula.ndisj leftBranch rightBranch =>
      Or (pcqNnfHolds env leftBranch) (pcqNnfHolds env rightBranch)

/-- Polarity-directed NNF of a QF formula. -/
def pcqNnfOfQf : PcqQfFormula → Bool → PcqNnfFormula
  | PcqQfFormula.qlt leftTerm rightTerm, true => PcqNnfFormula.nlt leftTerm rightTerm
  | PcqQfFormula.qlt leftTerm rightTerm, false =>
      PcqNnfFormula.nlt rightTerm (pcqTermPlusOne leftTerm)
  | PcqQfFormula.qdvd modulusPred target, true => PcqNnfFormula.ndvd modulusPred target
  | PcqQfFormula.qdvd modulusPred target, false => PcqNnfFormula.nndvd modulusPred target
  | PcqQfFormula.qndvd modulusPred target, true => PcqNnfFormula.nndvd modulusPred target
  | PcqQfFormula.qndvd modulusPred target, false => PcqNnfFormula.ndvd modulusPred target
  | PcqQfFormula.qconj leftBranch rightBranch, true =>
      PcqNnfFormula.nconj (pcqNnfOfQf leftBranch true) (pcqNnfOfQf rightBranch true)
  | PcqQfFormula.qconj leftBranch rightBranch, false =>
      PcqNnfFormula.ndisj (pcqNnfOfQf leftBranch false) (pcqNnfOfQf rightBranch false)
  | PcqQfFormula.qdisj leftBranch rightBranch, true =>
      PcqNnfFormula.ndisj (pcqNnfOfQf leftBranch true) (pcqNnfOfQf rightBranch true)
  | PcqQfFormula.qdisj leftBranch rightBranch, false =>
      PcqNnfFormula.nconj (pcqNnfOfQf leftBranch false) (pcqNnfOfQf rightBranch false)
  | PcqQfFormula.qneg body, true => pcqNnfOfQf body false
  | PcqQfFormula.qneg body, false => pcqNnfOfQf body true

/-- NNF EQUIVALENCE, both polarities and both directions (Chaieb–Nipkow
NNF invariant; the negative inequality polarity flips through succ-le, the
divisibility double negation eliminates through the decider). -/
theorem pcqNnfOfQfSound (env : List LfkInt) : ∀ (formula : PcqQfFormula),
    And
      (Iff (pcqNnfHolds env (pcqNnfOfQf formula true)) (pcqQfHolds env formula))
      (Iff (pcqNnfHolds env (pcqNnfOfQf formula false)) (pcqQfHolds env formula → False))
  | PcqQfFormula.qlt leftTerm rightTerm =>
      And.intro Iff.rfl
        (Iff.intro
          (fun negatedHolds holdsWitness =>
            pcqIntLtLeAbsurd holdsWitness
              (pcqIntLeOfLtSucc
                ((congrArg
                    (fun probe => lfkIntLt (pcqTermEval env rightTerm) probe)
                    (pcqTermPlusOneEval env leftTerm)).symm.trans negatedHolds)))
          (fun refutation =>
            (congrArg (fun probe => lfkIntLt (pcqTermEval env rightTerm) probe)
              (pcqTermPlusOneEval env leftTerm)).trans
              (pcqIntLtSuccOfLe
                (pcqIntLtFalseGivesLe
                  (match lfmBoolCases (lfkIntLt (pcqTermEval env leftTerm)
                    (pcqTermEval env rightTerm)) with
                  | Or.inl holdsWitness => False.elim (refutation holdsWitness)
                  | Or.inr failsWitness => failsWitness)))))
  | PcqQfFormula.qdvd _modulusPred _target => And.intro Iff.rfl Iff.rfl
  | PcqQfFormula.qndvd modulusPred target =>
      And.intro Iff.rfl
        (Iff.intro
          (fun dividesWitness refutation => refutation dividesWitness)
          (fun doubleNegation =>
            pcqDividesDoubleNegElim modulusPred (pcqTermEval env target) doubleNegation))
  | PcqQfFormula.qconj leftBranch rightBranch =>
      let leftBundle := pcqNnfOfQfSound env leftBranch
      let rightBundle := pcqNnfOfQfSound env rightBranch
      And.intro
        (Iff.intro
          (fun holdsWitness =>
            And.intro (leftBundle.left.mp holdsWitness.left)
              (rightBundle.left.mp holdsWitness.right))
          (fun holdsWitness =>
            And.intro (leftBundle.left.mpr holdsWitness.left)
              (rightBundle.left.mpr holdsWitness.right)))
        (Iff.intro
          (fun negatedHolds bothHold =>
            match negatedHolds with
            | Or.inl leftNegated => leftBundle.right.mp leftNegated bothHold.left
            | Or.inr rightNegated => rightBundle.right.mp rightNegated bothHold.right)
          (fun refutation =>
            match pcqQfHoldsOrNot env leftBranch with
            | Or.inl leftHolds =>
                Or.inr (rightBundle.right.mpr
                  (fun rightHolds => refutation (And.intro leftHolds rightHolds)))
            | Or.inr leftFails => Or.inl (leftBundle.right.mpr leftFails)))
  | PcqQfFormula.qdisj leftBranch rightBranch =>
      let leftBundle := pcqNnfOfQfSound env leftBranch
      let rightBundle := pcqNnfOfQfSound env rightBranch
      And.intro
        (Iff.intro
          (fun holdsWitness =>
            match holdsWitness with
            | Or.inl leftHolds => Or.inl (leftBundle.left.mp leftHolds)
            | Or.inr rightHolds => Or.inr (rightBundle.left.mp rightHolds))
          (fun holdsWitness =>
            match holdsWitness with
            | Or.inl leftHolds => Or.inl (leftBundle.left.mpr leftHolds)
            | Or.inr rightHolds => Or.inr (rightBundle.left.mpr rightHolds)))
        (Iff.intro
          (fun negatedHolds eitherHolds =>
            match eitherHolds with
            | Or.inl leftHolds => leftBundle.right.mp negatedHolds.left leftHolds
            | Or.inr rightHolds => rightBundle.right.mp negatedHolds.right rightHolds)
          (fun refutation =>
            And.intro
              (leftBundle.right.mpr (fun leftHolds => refutation (Or.inl leftHolds)))
              (rightBundle.right.mpr (fun rightHolds => refutation (Or.inr rightHolds)))))
  | PcqQfFormula.qneg body =>
      let bodyBundle := pcqNnfOfQfSound env body
      And.intro bodyBundle.right
        (Iff.intro
          (fun positiveHolds doubleNegation => doubleNegation (bodyBundle.left.mp positiveHolds))
          (fun doubleNegation =>
            bodyBundle.left.mpr
              (match pcqQfHoldsOrNot env body with
              | Or.inl bodyHolds => bodyHolds
              | Or.inr bodyFails => False.elim (doubleNegation bodyFails))))

/-! ## Stage B2 — order and scale corners for the unitarization step -/

/-- Strict-order cancellation of a positive Nat multiplier (succ-le form). -/
theorem pcqNatMulLtCancelLeft (multiplierPred leftValue rightValue : Nat)
    (scaledStrict : Nat.le (Nat.succ multiplierPred * leftValue + 1)
      (Nat.succ multiplierPred * rightValue)) : Nat.le (leftValue + 1) rightValue :=
  match lfmBoolCases (Nat.ble (leftValue + 1) rightValue) with
  | Or.inl bleTrue => lfkNatLeOfBle (leftValue + 1) rightValue bleTrue
  | Or.inr bleFalse =>
      let reverseWeak : Nat.le rightValue leftValue :=
        Nat.le_of_succ_le_succ
          (lfkNatLeOfBle (rightValue + 1) (leftValue + 1)
            (lfmNatBleFalseFlipStrict (leftValue + 1) rightValue bleFalse))
      let scaledReverse : Nat.le (Nat.succ multiplierPred * rightValue)
          (Nat.succ multiplierPred * leftValue) :=
        lfkNatMulLeMulLeft (Nat.succ multiplierPred) reverseWeak
      False.elim
        (lfkNatSuccLeSelfFalse (Nat.succ multiplierPred * leftValue)
          (Nat.le_trans scaledStrict scaledReverse))

/-- Cancel a positive scale inside a strict pair comparison. -/
theorem pcqIntLtCancelScale (multiplierPred : Nat) {leftValue rightValue : LfkInt}
    (scaledStrict : lfkIntLt (lfkIntScaleByNat (multiplierPred + 1) leftValue)
      (lfkIntScaleByNat (multiplierPred + 1) rightValue) = true) :
    lfkIntLt leftValue rightValue = true :=
  lfkNatBleOfLe _ _
    (pcqNatMulLtCancelLeft multiplierPred
      (leftValue.positivePart + rightValue.negativePart)
      (rightValue.positivePart + leftValue.negativePart)
      (lfkNatLeCongr
        (congrArg (fun probe => probe + 1)
          (Nat.mul_add (multiplierPred + 1) leftValue.positivePart
            rightValue.negativePart))
        (Nat.mul_add (multiplierPred + 1) rightValue.positivePart leftValue.negativePart)
        (lfkNatLeOfBle _ _ scaledStrict)))

/-- Cancel a positive scale inside a cross-sum equality. -/
theorem pcqIntEqCancelScale (multiplierPred : Nat) {leftValue rightValue : LfkInt}
    (scaledEq : lfkIntEq (lfkIntScaleByNat (multiplierPred + 1) leftValue)
      (lfkIntScaleByNat (multiplierPred + 1) rightValue) = true) :
    lfkIntEq leftValue rightValue = true :=
  lfkNatBeqOfEq _ _
    (lreNatMulLeftCancelEq multiplierPred
      (leftValue.positivePart + rightValue.negativePart)
      (rightValue.positivePart + leftValue.negativePart)
      ((Nat.mul_add (multiplierPred + 1) leftValue.positivePart
          rightValue.negativePart).trans
        ((lfkNatEqOfBeq _ _ scaledEq).trans
          (Nat.mul_add (multiplierPred + 1) rightValue.positivePart
            leftValue.negativePart).symm)))

/-- Flip a strict comparison across negation on the left:
`-A < B` gives `-B < A`. -/
theorem pcqIntLtNegFlip {leftValue rightValue : LfkInt}
    (strictWitness : lfkIntLt (lfkIntNegate leftValue) rightValue = true) :
    lfkIntLt (lfkIntNegate rightValue) leftValue = true :=
  lfkNatBleOfLe _ _
    (lfkNatLeCongr
      (congrArg (fun probe => probe + 1)
        (Nat.add_comm rightValue.negativePart leftValue.negativePart))
      (Nat.add_comm leftValue.positivePart rightValue.positivePart)
      (lfkNatLeOfBle _ _ strictWitness))

/-- Strict order is invariant under adding a shared LEFT addend. -/
theorem pcqIntLtAddLeft (sharedValue : LfkInt) {leftValue rightValue : LfkInt}
    (strictWitness : lfkIntLt leftValue rightValue = true) :
    lfkIntLt (lfkIntAdd sharedValue leftValue) (lfkIntAdd sharedValue rightValue) = true :=
  lfkNatBleOfLe
    (sharedValue.positivePart + leftValue.positivePart
      + (sharedValue.negativePart + rightValue.negativePart) + 1)
    (sharedValue.positivePart + rightValue.positivePart
      + (sharedValue.negativePart + leftValue.negativePart))
    (lfkNatLeCongr
      ((congrArg (fun probe => probe + 1)
          (lfkNatAddSwapMiddle sharedValue.positivePart leftValue.positivePart
            sharedValue.negativePart rightValue.negativePart)).trans
        (Nat.add_assoc (sharedValue.positivePart + sharedValue.negativePart)
          (leftValue.positivePart + rightValue.negativePart) 1))
      (lfkNatAddSwapMiddle sharedValue.positivePart rightValue.positivePart
        sharedValue.negativePart leftValue.negativePart)
      (Nat.add_le_add_left (lfkNatLeOfBle _ _ strictWitness)
        (sharedValue.positivePart + sharedValue.negativePart)))

/-- Strict order cancels a shared LEFT addend. -/
theorem pcqIntLtCancelAddLeft (sharedValue : LfkInt) {leftValue rightValue : LfkInt}
    (paddedStrict : lfkIntLt (lfkIntAdd sharedValue leftValue)
      (lfkIntAdd sharedValue rightValue) = true) :
    lfkIntLt leftValue rightValue = true :=
  lfkNatBleOfLe (leftValue.positivePart + rightValue.negativePart + 1)
    (rightValue.positivePart + leftValue.negativePart)
    (pcqNatLeCancelAddLeft (sharedValue.positivePart + sharedValue.negativePart)
      (leftValue.positivePart + rightValue.negativePart + 1)
      (rightValue.positivePart + leftValue.negativePart)
      (lfkNatLeCongr
        ((Nat.add_assoc (sharedValue.positivePart + sharedValue.negativePart)
            (leftValue.positivePart + rightValue.negativePart) 1).symm.trans
          (congrArg (fun probe => probe + 1)
            (lfkNatAddSwapMiddle sharedValue.positivePart leftValue.positivePart
              sharedValue.negativePart rightValue.negativePart).symm))
        (lfkNatAddSwapMiddle sharedValue.positivePart rightValue.positivePart
          sharedValue.negativePart leftValue.negativePart).symm
        (lfkNatLeOfBle _ _ paddedStrict)))

/-- Turn the difference form back into the sum form (two further
`lreIntLtSplitAcross` applications cycle around; double negation is
definitional on pairs). -/
theorem pcqIntLtDiffGivesSum {firstLow secondLow firstHigh secondHigh : LfkInt}
    (diffWitness : lfkIntLt (lfkIntAdd firstLow (lfkIntNegate firstHigh))
      (lfkIntAdd secondHigh (lfkIntNegate secondLow)) = true) :
    lfkIntLt (lfkIntAdd firstLow secondLow) (lfkIntAdd firstHigh secondHigh) = true :=
  lreIntLtSplitAcross (lreIntLtSplitAcross diffWitness)

/-- A cross-zero difference is a cross-sum equality of the endpoints. -/
theorem pcqIntEqOfAddNegZero {leftValue rightValue : LfkInt}
    (zeroWitness : lfkIntIsZero (lfkIntAdd leftValue (lfkIntNegate rightValue)) = true) :
    lfkIntEq leftValue rightValue = true :=
  lfkNatBeqOfEq _ _
    ((lfkNatEqOfBeq _ _ zeroWitness).trans
      (Nat.add_comm leftValue.negativePart rightValue.positivePart))

/-- Divisibility scales up: `d | v` gives `(m*d) | (m·v)`. -/
theorem pcqDividesScaleUp (scaleFactor modulus : Nat) (value : LfkInt)
    (dividesWitness : pcqDividesProp modulus value) :
    pcqDividesProp (scaleFactor * modulus) (lfkIntScaleByNat scaleFactor value) :=
  match dividesWitness with
  | Exists.intro quotient quotientEq =>
      Exists.intro quotient
        ((congrArg (fun probe => lfkIntEq probe (lfkIntScaleByNat scaleFactor value))
            (lfmIntScaleCompose scaleFactor modulus quotient)).trans
          (lfkIntScaleEqMono scaleFactor quotientEq))

/-- Divisibility scales down: `((mp+1)*d) | ((mp+1)·v)` gives `d | v`. -/
theorem pcqDividesScaleDown (scaleFactorPred modulus : Nat) (value : LfkInt)
    (dividesWitness : pcqDividesProp ((scaleFactorPred + 1) * modulus)
      (lfkIntScaleByNat (scaleFactorPred + 1) value)) :
    pcqDividesProp modulus value :=
  match dividesWitness with
  | Exists.intro quotient quotientEq =>
      Exists.intro quotient
        (pcqIntEqCancelScale scaleFactorPred
          ((congrArg
              (fun probe => lfkIntEq probe
                (lfkIntScaleByNat (scaleFactorPred + 1) value))
              (lfmIntScaleCompose (scaleFactorPred + 1) modulus quotient)).symm.trans
            quotientEq))

/-- Divisibility is invariant under negation. -/
theorem pcqDividesNegate (modulus : Nat) (value : LfkInt)
    (dividesWitness : pcqDividesProp modulus value) :
    pcqDividesProp modulus (lfkIntNegate value) :=
  match dividesWitness with
  | Exists.intro quotient quotientEq =>
      Exists.intro (lfkIntNegate quotient) (pcqIntEqNegateCongr quotientEq)

/-! ## Stage B3 — pair-integer sign analysis (the witnessed magnitude and the
three-way view: cross-zero / positive `ofNat` / negative `negate ofNat`) -/

/-- Propositional-equality transport for the LEFT side of an `Iff`
(`Eq.mp`/`Eq.mpr` only — no axioms). -/
theorem pcqIffCongrLeft {leftProp rewrittenProp rightProp : Prop}
    (leftEq : leftProp = rewrittenProp) (baseIff : Iff rewrittenProp rightProp) :
    Iff leftProp rightProp :=
  Iff.intro (fun leftHolds => baseIff.mp (Eq.mp leftEq leftHolds))
    (fun rightHolds => Eq.mpr leftEq (baseIff.mpr rightHolds))

/-- Propositional-equality transport for the RIGHT side of an `Iff`. -/
theorem pcqIffCongrRight {leftProp rightProp rewrittenProp : Prop}
    (rightEq : rightProp = rewrittenProp) (baseIff : Iff leftProp rewrittenProp) :
    Iff leftProp rightProp :=
  Iff.intro (fun leftHolds => Eq.mpr rightEq (baseIff.mp leftHolds))
    (fun rightHolds => baseIff.mpr (Eq.mp rightEq rightHolds))

/-- An `Iff` out of a propositional equality. -/
theorem pcqIffOfEq {leftProp rightProp : Prop} (propEq : leftProp = rightProp) :
    Iff leftProp rightProp :=
  Iff.intro (fun leftHolds => Eq.mp propEq leftHolds)
    (fun rightHolds => Eq.mpr propEq rightHolds)

/-- The Nat magnitude of a pair integer: the witnessed difference in whichever
direction is nonnegative. -/
def pcqIntMagnitude (value : LfkInt) : Nat :=
  cond (Nat.ble value.negativePart value.positivePart)
    (lfmNatDelta value.positivePart value.negativePart)
    (lfmNatDelta value.negativePart value.positivePart)

/-- A vanishing magnitude forces a cross-zero pair. -/
theorem pcqIntZeroOfMagnitudeZero (value : LfkInt)
    (magnitudeZero : Nat.beq (pcqIntMagnitude value) 0 = true) :
    lfkIntIsZero value = true :=
  match orderCase : Nat.ble value.negativePart value.positivePart with
  | true =>
      let branchZero : Nat.beq (lfmNatDelta value.positivePart value.negativePart) 0 = true :=
        (congrArg
          (fun probe => Nat.beq
            (cond probe (lfmNatDelta value.positivePart value.negativePart)
              (lfmNatDelta value.negativePart value.positivePart)) 0)
          orderCase).symm.trans magnitudeZero
      let recoveredEq : value.negativePart + 0 = value.positivePart :=
        (congrArg (fun probe => value.negativePart + probe)
          (lfkNatEqOfBeq (lfmNatDelta value.positivePart value.negativePart) 0
            branchZero)).symm.trans
          (lfmNatDeltaRecovers value.positivePart value.negativePart orderCase)
      lfkNatBeqOfEq value.positivePart value.negativePart (recoveredEq : value.negativePart = value.positivePart).symm
  | false =>
      let branchZero : Nat.beq (lfmNatDelta value.negativePart value.positivePart) 0 = true :=
        (congrArg
          (fun probe => Nat.beq
            (cond probe (lfmNatDelta value.positivePart value.negativePart)
              (lfmNatDelta value.negativePart value.positivePart)) 0)
          orderCase).symm.trans magnitudeZero
      let flippedOrder : Nat.ble value.positivePart value.negativePart = true :=
        lfmNatBleWeakenFromSucc value.positivePart value.negativePart
          (lfmNatBleFalseFlipStrict value.negativePart value.positivePart orderCase)
      let recoveredEq : value.positivePart + 0 = value.negativePart :=
        (congrArg (fun probe => value.positivePart + probe)
          (lfkNatEqOfBeq (lfmNatDelta value.negativePart value.positivePart) 0
            branchZero)).symm.trans
          (lfmNatDeltaRecovers value.negativePart value.positivePart flippedOrder)
      lfkNatBeqOfEq value.positivePart value.negativePart
        (recoveredEq : value.positivePart = value.negativePart)

/-- A cross-nonnegative pair is cross-equal to its magnitude embedded as a
nonnegative integer. -/
theorem pcqIntEqOfNatMagnitude (value : LfkInt)
    (orderCase : Nat.ble value.negativePart value.positivePart = true) :
    lfkIntEq value (lreIntOfNat (pcqIntMagnitude value)) = true :=
  let magnitudeEq : pcqIntMagnitude value = lfmNatDelta value.positivePart value.negativePart :=
    congrArg
      (fun probe => cond probe (lfmNatDelta value.positivePart value.negativePart)
        (lfmNatDelta value.negativePart value.positivePart))
      orderCase
  lfkNatBeqOfEq (value.positivePart + 0) (pcqIntMagnitude value + value.negativePart)
    ((((lfmNatDeltaRecovers value.positivePart value.negativePart orderCase).symm.trans
        (Nat.add_comm value.negativePart
          (lfmNatDelta value.positivePart value.negativePart))).trans
      (congrArg (fun probe => probe + value.negativePart) magnitudeEq.symm)
      : value.positivePart + 0 = pcqIntMagnitude value + value.negativePart))

/-- A cross-negative pair is cross-equal to the negation of its embedded
magnitude. -/
theorem pcqIntEqNegOfNatMagnitude (value : LfkInt)
    (orderCase : Nat.ble value.negativePart value.positivePart = false) :
    lfkIntEq value (lfkIntNegate (lreIntOfNat (pcqIntMagnitude value))) = true :=
  let magnitudeEq : pcqIntMagnitude value = lfmNatDelta value.negativePart value.positivePart :=
    congrArg
      (fun probe => cond probe (lfmNatDelta value.positivePart value.negativePart)
        (lfmNatDelta value.negativePart value.positivePart))
      orderCase
  let flippedOrder : Nat.ble value.positivePart value.negativePart = true :=
    lfmNatBleWeakenFromSucc value.positivePart value.negativePart
      (lfmNatBleFalseFlipStrict value.negativePart value.positivePart orderCase)
  lfkNatBeqOfEq (value.positivePart + pcqIntMagnitude value) (0 + value.negativePart)
    (((congrArg (fun probe => value.positivePart + probe) magnitudeEq).trans
        (lfmNatDeltaRecovers value.negativePart value.positivePart flippedOrder)).trans
      (Nat.zero_add value.negativePart).symm)

/-- The magnitude clamped to one on cross-zero pairs — the per-atom factor of
the global unitarization scale. -/
def pcqMagnitudeOrOne (value : LfkInt) : Nat :=
  cond (Nat.beq (pcqIntMagnitude value) 0) 1 (pcqIntMagnitude value)

/-- The clamped magnitude is positive. -/
theorem pcqMagnitudeOrOnePositive (value : LfkInt) :
    Nat.ble 1 (pcqMagnitudeOrOne value) = true :=
  match zeroCase : Nat.beq (pcqIntMagnitude value) 0 with
  | true =>
      (congrArg (fun probe => Nat.ble 1 (cond probe 1 (pcqIntMagnitude value)))
        zeroCase : Nat.ble 1 (pcqMagnitudeOrOne value) = true)
  | false =>
      match pcqNatNonZeroShape (pcqIntMagnitude value) zeroCase with
      | Exists.intro magnitudePred shapeEq =>
          (((congrArg (fun probe => Nat.ble 1 (cond probe 1 (pcqIntMagnitude value)))
              zeroCase).trans
            ((congrArg (fun probe => Nat.ble 1 probe) shapeEq).trans
              (lfkNatBleOfLe 1 (magnitudePred + 1)
                (Nat.succ_le_succ (Nat.zero_le magnitudePred)))))
            : Nat.ble 1 (pcqMagnitudeOrOne value) = true)

/-- On non-cross-zero pairs the clamp is the identity. -/
theorem pcqMagnitudeOrOneEqMagnitude (value : LfkInt)
    (nonZeroCase : Nat.beq (pcqIntMagnitude value) 0 = false) :
    pcqMagnitudeOrOne value = pcqIntMagnitude value :=
  congrArg (fun probe => cond probe 1 (pcqIntMagnitude value)) nonZeroCase

/-- A cofactor recovering a positive product is itself positive (successor
shape). -/
theorem pcqNatCofactorShape : ∀ (cofactor magnitudePred target : Nat),
    cofactor * (magnitudePred + 1) = target → Nat.ble 1 target = true →
    ∃ (cofactorPred : Nat), cofactor = cofactorPred + 1
  | Nat.zero, magnitudePred, _target, recoverEq, targetPositive =>
      Bool.noConfusion
        (((congrArg (fun probe => Nat.ble 1 probe)
            (recoverEq.symm.trans (Nat.zero_mul (magnitudePred + 1)))).trans rfl).symm.trans
          targetPositive)
  | Nat.succ cofactorPred, _magnitudePred, _target, _recoverEq, _targetPositive =>
      Exists.intro cofactorPred rfl

/-- Multiplying an `ofNat` on the right is Nat scaling. -/
theorem pcqIntMulOfNatRight (value : LfkInt) (count : Nat) :
    lfkIntMul value (lreIntOfNat count) = lfkIntScaleByNat count value :=
  lfkIntMkCongr
    ((Nat.mul_comm value.positivePart count :
        value.positivePart * count + value.negativePart * 0 = count * value.positivePart))
    (((Nat.zero_add (value.negativePart * count)).trans
        (Nat.mul_comm value.negativePart count) :
      value.positivePart * 0 + value.negativePart * count = count * value.negativePart))

/-- A component-equal pair is cross-equal to the literal zero. -/
theorem pcqIntEqZeroOfIsZero {value : LfkInt} (zeroWitness : lfkIntIsZero value = true) :
    lfkIntEq value lfkIntZero = true :=
  lfkNatBeqOfEq (value.positivePart + 0) (0 + value.negativePart)
    (((lfkNatEqOfBeq value.positivePart value.negativePart zeroWitness).trans
        (Nat.zero_add value.negativePart).symm :
      value.positivePart + 0 = 0 + value.negativePart))

/-! ## Stage B4 — the global unitarization scale (product of clamped pivot
magnitudes) and its divisibility certificate -/

/-- The pivot-difference coefficient of a strict-inequality atom under the
binder: head coefficient of the left side minus head coefficient of the
right side. -/
def pcqNnfLtPivot (leftTerm rightTerm : PcqTerm) : LfkInt :=
  lfkIntAdd (pcqTermHeadCoeff leftTerm) (lfkIntNegate (pcqTermHeadCoeff rightTerm))

/-- The global unitarization scale: the PRODUCT over all atoms of the clamped
pivot-coefficient magnitude (any common multiple works — no gcd/lcm needed). -/
def pcqNnfScale : PcqNnfFormula → Nat
  | PcqNnfFormula.nlt leftTerm rightTerm =>
      pcqMagnitudeOrOne (pcqNnfLtPivot leftTerm rightTerm)
  | PcqNnfFormula.ndvd _modulusPred target => pcqMagnitudeOrOne (pcqTermHeadCoeff target)
  | PcqNnfFormula.nndvd _modulusPred target => pcqMagnitudeOrOne (pcqTermHeadCoeff target)
  | PcqNnfFormula.nconj leftBranch rightBranch =>
      pcqNnfScale leftBranch * pcqNnfScale rightBranch
  | PcqNnfFormula.ndisj leftBranch rightBranch =>
      pcqNnfScale leftBranch * pcqNnfScale rightBranch

/-- The global scale is positive. -/
theorem pcqNnfScalePositive : ∀ (formula : PcqNnfFormula),
    Nat.ble 1 (pcqNnfScale formula) = true
  | PcqNnfFormula.nlt leftTerm rightTerm =>
      pcqMagnitudeOrOnePositive (pcqNnfLtPivot leftTerm rightTerm)
  | PcqNnfFormula.ndvd _modulusPred target =>
      pcqMagnitudeOrOnePositive (pcqTermHeadCoeff target)
  | PcqNnfFormula.nndvd _modulusPred target =>
      pcqMagnitudeOrOnePositive (pcqTermHeadCoeff target)
  | PcqNnfFormula.nconj leftBranch rightBranch =>
      lreNatPositiveMulPositive (pcqNnfScale leftBranch) (pcqNnfScale rightBranch)
        (pcqNnfScalePositive leftBranch) (pcqNnfScalePositive rightBranch)
  | PcqNnfFormula.ndisj leftBranch rightBranch =>
      lreNatPositiveMulPositive (pcqNnfScale leftBranch) (pcqNnfScale rightBranch)
        (pcqNnfScalePositive leftBranch) (pcqNnfScalePositive rightBranch)

/-- Every atom's clamped pivot magnitude divides the target (structure-mirroring
Prop, the analogue of `pcqAllModuliDivide`). -/
def pcqNnfCoeffsDivide : PcqNnfFormula → Nat → Prop
  | PcqNnfFormula.nlt leftTerm rightTerm, target =>
      pcqNatDividesProp (pcqMagnitudeOrOne (pcqNnfLtPivot leftTerm rightTerm)) target
  | PcqNnfFormula.ndvd _modulusPred divTarget, target =>
      pcqNatDividesProp (pcqMagnitudeOrOne (pcqTermHeadCoeff divTarget)) target
  | PcqNnfFormula.nndvd _modulusPred divTarget, target =>
      pcqNatDividesProp (pcqMagnitudeOrOne (pcqTermHeadCoeff divTarget)) target
  | PcqNnfFormula.nconj leftBranch rightBranch, target =>
      And (pcqNnfCoeffsDivide leftBranch target) (pcqNnfCoeffsDivide rightBranch target)
  | PcqNnfFormula.ndisj leftBranch rightBranch, target =>
      And (pcqNnfCoeffsDivide leftBranch target) (pcqNnfCoeffsDivide rightBranch target)

/-- Coefficient division is stable under enlarging the target by a right
factor. -/
theorem pcqNnfCoeffsDivideMulRight : ∀ (formula : PcqNnfFormula) (target extraFactor : Nat),
    pcqNnfCoeffsDivide formula target → pcqNnfCoeffsDivide formula (target * extraFactor)
  | PcqNnfFormula.nlt leftTerm rightTerm, target, extraFactor, divideWitness =>
      pcqNatDividesMulRight (pcqMagnitudeOrOne (pcqNnfLtPivot leftTerm rightTerm))
        target extraFactor divideWitness
  | PcqNnfFormula.ndvd _modulusPred divTarget, target, extraFactor, divideWitness =>
      pcqNatDividesMulRight (pcqMagnitudeOrOne (pcqTermHeadCoeff divTarget))
        target extraFactor divideWitness
  | PcqNnfFormula.nndvd _modulusPred divTarget, target, extraFactor, divideWitness =>
      pcqNatDividesMulRight (pcqMagnitudeOrOne (pcqTermHeadCoeff divTarget))
        target extraFactor divideWitness
  | PcqNnfFormula.nconj leftBranch rightBranch, target, extraFactor, divideWitness =>
      And.intro
        (pcqNnfCoeffsDivideMulRight leftBranch target extraFactor divideWitness.left)
        (pcqNnfCoeffsDivideMulRight rightBranch target extraFactor divideWitness.right)
  | PcqNnfFormula.ndisj leftBranch rightBranch, target, extraFactor, divideWitness =>
      And.intro
        (pcqNnfCoeffsDivideMulRight leftBranch target extraFactor divideWitness.left)
        (pcqNnfCoeffsDivideMulRight rightBranch target extraFactor divideWitness.right)

/-- Coefficient division is stable under enlarging the target by a left
factor. -/
theorem pcqNnfCoeffsDivideMulLeft (formula : PcqNnfFormula) (target extraFactor : Nat)
    (divideWitness : pcqNnfCoeffsDivide formula target) :
    pcqNnfCoeffsDivide formula (extraFactor * target) :=
  (Nat.mul_comm target extraFactor) ▸
    pcqNnfCoeffsDivideMulRight formula target extraFactor divideWitness

/-- THE SCALE CERTIFICATE: every atom's clamped pivot magnitude divides the
global product scale. -/
theorem pcqNnfCoeffsDivideScale : ∀ (formula : PcqNnfFormula),
    pcqNnfCoeffsDivide formula (pcqNnfScale formula)
  | PcqNnfFormula.nlt leftTerm rightTerm =>
      pcqNatDividesSelf (pcqMagnitudeOrOne (pcqNnfLtPivot leftTerm rightTerm))
  | PcqNnfFormula.ndvd _modulusPred divTarget =>
      pcqNatDividesSelf (pcqMagnitudeOrOne (pcqTermHeadCoeff divTarget))
  | PcqNnfFormula.nndvd _modulusPred divTarget =>
      pcqNatDividesSelf (pcqMagnitudeOrOne (pcqTermHeadCoeff divTarget))
  | PcqNnfFormula.nconj leftBranch rightBranch =>
      And.intro
        (pcqNnfCoeffsDivideMulRight leftBranch (pcqNnfScale leftBranch)
          (pcqNnfScale rightBranch) (pcqNnfCoeffsDivideScale leftBranch))
        (pcqNnfCoeffsDivideMulLeft rightBranch (pcqNnfScale rightBranch)
          (pcqNnfScale leftBranch) (pcqNnfCoeffsDivideScale rightBranch))
  | PcqNnfFormula.ndisj leftBranch rightBranch =>
      And.intro
        (pcqNnfCoeffsDivideMulRight leftBranch (pcqNnfScale leftBranch)
          (pcqNnfScale rightBranch) (pcqNnfCoeffsDivideScale leftBranch))
        (pcqNnfCoeffsDivideMulLeft rightBranch (pcqNnfScale rightBranch)
          (pcqNnfScale leftBranch) (pcqNnfCoeffsDivideScale rightBranch))

/-! ## Stage B5 — the unit matrix builder (every pivot occurrence scaled to
coefficient exactly +1; pivot-free atoms drop to free atoms) -/

/-- Rewriting matrix satisfaction of a `cond` by a true condition flag. -/
theorem pcqMatrixHoldsCondEqTrue (env : List LfkInt) (pivotValue : LfkInt)
    {conditionFlag : Bool} (trueBranch falseBranch : PcqMatrix)
    (flagEq : conditionFlag = true) :
    pcqMatrixHolds env pivotValue (cond conditionFlag trueBranch falseBranch)
      = pcqMatrixHolds env pivotValue trueBranch :=
  congrArg (fun probe => pcqMatrixHolds env pivotValue (cond probe trueBranch falseBranch))
    flagEq

/-- Rewriting matrix satisfaction of a `cond` by a false condition flag. -/
theorem pcqMatrixHoldsCondEqFalse (env : List LfkInt) (pivotValue : LfkInt)
    {conditionFlag : Bool} (trueBranch falseBranch : PcqMatrix)
    (flagEq : conditionFlag = false) :
    pcqMatrixHolds env pivotValue (cond conditionFlag trueBranch falseBranch)
      = pcqMatrixHolds env pivotValue falseBranch :=
  congrArg (fun probe => pcqMatrixHolds env pivotValue (cond probe trueBranch falseBranch))
    flagEq

/-- Unitarize one strict-inequality atom (difference form `d*x < r`): a
cross-zero pivot difference keeps a free comparison against zero; a positive
one becomes an upper bound, a negative one a lower bound, each residue scaled
by the counting cofactor `scale / |d|`. -/
def pcqUnitLtAtom (scaleValue : Nat) (pivotCoeff : LfkInt) (residualTerm : PcqTerm) :
    PcqMatrix :=
  let cofactor := pcqNatDivCounting (pcqNatPred (pcqIntMagnitude pivotCoeff)) scaleValue
  cond (Nat.beq (pcqIntMagnitude pivotCoeff) 0)
    (PcqMatrix.mfreelt (pcqConstTerm lfkIntZero) residualTerm)
    (cond (Nat.ble pivotCoeff.negativePart pivotCoeff.positivePart)
      (PcqMatrix.mupper (pcqTermScaleByNat cofactor residualTerm))
      (PcqMatrix.mlower (pcqTermScaleByNat cofactor (pcqTermNegate residualTerm))))

/-- Unitarize one divisibility atom `(mp+1) | c*x + u`: cross-zero pivot
coefficient keeps a free atom; otherwise the modulus and the offset scale by
the counting cofactor, the offset negated on a negative pivot coefficient. -/
def pcqUnitDvdAtom (scaleValue modulusPred : Nat) (pivotCoeff : LfkInt)
    (tailTerm : PcqTerm) : PcqMatrix :=
  let cofactor := pcqNatDivCounting (pcqNatPred (pcqIntMagnitude pivotCoeff)) scaleValue
  cond (Nat.beq (pcqIntMagnitude pivotCoeff) 0)
    (PcqMatrix.mfreedvd modulusPred tailTerm)
    (cond (Nat.ble pivotCoeff.negativePart pivotCoeff.positivePart)
      (PcqMatrix.mdvd (pcqNatPred (cofactor * (modulusPred + 1)))
        (pcqTermScaleByNat cofactor tailTerm))
      (PcqMatrix.mdvd (pcqNatPred (cofactor * (modulusPred + 1)))
        (pcqTermScaleByNat cofactor (pcqTermNegate tailTerm))))

/-- Unitarize one negated-divisibility atom (same shape as `pcqUnitDvdAtom`
with the negated constructors). -/
def pcqUnitNdvdAtom (scaleValue modulusPred : Nat) (pivotCoeff : LfkInt)
    (tailTerm : PcqTerm) : PcqMatrix :=
  let cofactor := pcqNatDivCounting (pcqNatPred (pcqIntMagnitude pivotCoeff)) scaleValue
  cond (Nat.beq (pcqIntMagnitude pivotCoeff) 0)
    (PcqMatrix.mfreendvd modulusPred tailTerm)
    (cond (Nat.ble pivotCoeff.negativePart pivotCoeff.positivePart)
      (PcqMatrix.mndvd (pcqNatPred (cofactor * (modulusPred + 1)))
        (pcqTermScaleByNat cofactor tailTerm))
      (PcqMatrix.mndvd (pcqNatPred (cofactor * (modulusPred + 1)))
        (pcqTermScaleByNat cofactor (pcqTermNegate tailTerm))))

/-- THE STRICT-INEQUALITY UNITARIZATION EQUIVALENCE: under the binder, the
atom `eval t1 < eval t2` holds at pivot `x` exactly when the unitarized atom
holds at pivot `scale*x` (difference form, then the three-way sign split,
scaling both sides by the counting cofactor `scale / |d|`). -/
theorem pcqUnitLtAtomEquiv (env : List LfkInt) (scaleValue : Nat)
    (scalePositive : Nat.ble 1 scaleValue = true) (leftTerm rightTerm : PcqTerm)
    (pivotValue : LfkInt)
    (divideWitness : pcqNatDividesProp
      (pcqMagnitudeOrOne (pcqNnfLtPivot leftTerm rightTerm)) scaleValue) :
    Iff
      (lfkIntLt (pcqTermEval (pivotValue :: env) leftTerm)
        (pcqTermEval (pivotValue :: env) rightTerm) = true)
      (pcqMatrixHolds env (lfkIntScaleByNat scaleValue pivotValue)
        (pcqUnitLtAtom scaleValue (pcqNnfLtPivot leftTerm rightTerm)
          (pcqTermAdd (pcqTermTail rightTerm) (pcqTermNegate (pcqTermTail leftTerm))))) :=
  let pivotCoeff := pcqNnfLtPivot leftTerm rightTerm
  let residualTerm := pcqTermAdd (pcqTermTail rightTerm) (pcqTermNegate (pcqTermTail leftTerm))
  let headLeft := pcqTermHeadCoeff leftTerm
  let headRight := pcqTermHeadCoeff rightTerm
  let tailLeftValue := pcqTermEval env (pcqTermTail leftTerm)
  let tailRightValue := pcqTermEval env (pcqTermTail rightTerm)
  let residualValue := lfkIntAdd tailRightValue (lfkIntNegate tailLeftValue)
  let scaledPivot := lfkIntScaleByNat scaleValue pivotValue
  let residualEvalEq : pcqTermEval env residualTerm = residualValue :=
    (pcqTermEvalAdd env (pcqTermTail rightTerm) (pcqTermNegate (pcqTermTail leftTerm))).trans
      (congrArg (fun probe => lfkIntAdd tailRightValue probe)
        (pcqTermEvalNegate env (pcqTermTail leftTerm)))
  let splitEq : (lfkIntLt (pcqTermEval (pivotValue :: env) leftTerm)
        (pcqTermEval (pivotValue :: env) rightTerm) = true)
      = (lfkIntLt (lfkIntAdd (lfkIntMul pivotValue headLeft) tailLeftValue)
          (lfkIntAdd (lfkIntMul pivotValue headRight) tailRightValue) = true) :=
    congrArg (fun probe => probe = true)
      ((congrArg
          (fun probe => lfkIntLt probe (pcqTermEval (pivotValue :: env) rightTerm))
          (pcqTermEvalConsSplit pivotValue env leftTerm)).trans
        (congrArg
          (fun probe => lfkIntLt
            (lfkIntAdd (lfkIntMul pivotValue headLeft) tailLeftValue) probe)
          (pcqTermEvalConsSplit pivotValue env rightTerm)))
  let diffIff : Iff
      (lfkIntLt (lfkIntAdd (lfkIntMul pivotValue headLeft) tailLeftValue)
        (lfkIntAdd (lfkIntMul pivotValue headRight) tailRightValue) = true)
      (lfkIntLt (lfkIntMul pivotValue pivotCoeff) residualValue = true) :=
    Iff.intro
      (fun sumWitness =>
        Eq.mpr
          (congrArg (fun probe => lfkIntLt probe residualValue = true)
            (lfkIntMulAddRight pivotValue headLeft (lfkIntNegate headRight)))
          (lreIntLtSplitAcross sumWitness))
      (fun diffWitness =>
        pcqIntLtDiffGivesSum
          (Eq.mp
            (congrArg (fun probe => lfkIntLt probe residualValue = true)
              (lfkIntMulAddRight pivotValue headLeft (lfkIntNegate headRight)))
            diffWitness))
  pcqIffCongrLeft splitEq
    (match magnitudeCase : Nat.beq (pcqIntMagnitude pivotCoeff) 0 with
     | true =>
        let zeroWitness : lfkIntIsZero pivotCoeff = true :=
          pcqIntZeroOfMagnitudeZero pivotCoeff magnitudeCase
        let pivotZeroEq : lfkIntEq (lfkIntMul pivotValue pivotCoeff) lfkIntZero = true :=
          pcqIntEqZeroOfIsZero (lfkIntMulZeroRight pivotValue pivotCoeff zeroWitness)
        let zeroPivotIff : Iff
            (lfkIntLt (lfkIntMul pivotValue pivotCoeff) residualValue = true)
            (lfkIntLt lfkIntZero residualValue = true) :=
          Iff.intro
            (fun strictWitness => lreIntLtCongrLeft pivotZeroEq strictWitness)
            (fun strictWitness =>
              lreIntLtCongrLeft (lreIntEqSymm pivotZeroEq) strictWitness)
        let targetEq : pcqMatrixHolds env scaledPivot
              (PcqMatrix.mfreelt (pcqConstTerm lfkIntZero) residualTerm)
            = (lfkIntLt lfkIntZero residualValue = true) :=
          (congrArg
            (fun probe => lfkIntLt probe (pcqTermEval env residualTerm) = true)
            (pcqConstTermEval env lfkIntZero)).trans
            (congrArg (fun probe => lfkIntLt lfkIntZero probe = true) residualEvalEq)
        pcqIffCongrRight
          (pcqMatrixHoldsCondEqTrue env scaledPivot _ _ magnitudeCase)
          (diffIff.trans (zeroPivotIff.trans (pcqIffOfEq targetEq).symm))
     | false =>
        match pcqNatNonZeroShape (pcqIntMagnitude pivotCoeff) magnitudeCase with
        | Exists.intro magnitudePred magnitudeShape =>
            let divideMagnitude : pcqNatDividesProp (magnitudePred + 1) scaleValue :=
              Eq.mp
                (congrArg (fun probe => pcqNatDividesProp probe scaleValue)
                  ((pcqMagnitudeOrOneEqMagnitude pivotCoeff magnitudeCase).trans
                    magnitudeShape))
                divideWitness
            let builderCofactor :=
              pcqNatDivCounting (pcqNatPred (pcqIntMagnitude pivotCoeff)) scaleValue
            let builderCofactorEq : builderCofactor
                = pcqNatDivCounting magnitudePred scaleValue :=
              congrArg (fun probe => pcqNatDivCounting probe scaleValue)
                (congrArg pcqNatPred magnitudeShape)
            let exactRecovery : pcqNatDivCounting magnitudePred scaleValue
                * (magnitudePred + 1) = scaleValue :=
              pcqNatCountingQuotientExact magnitudePred scaleValue divideMagnitude
            match pcqNatCofactorShape (pcqNatDivCounting magnitudePred scaleValue)
              magnitudePred scaleValue exactRecovery scalePositive with
            | Exists.intro cofactorPred cofactorShape =>
                let cofactorRewrite : builderCofactor = cofactorPred + 1 :=
                  builderCofactorEq.trans cofactorShape
                let mulRecovery : (cofactorPred + 1) * pcqIntMagnitude pivotCoeff
                    = scaleValue :=
                  ((congrArg (fun probe => probe * pcqIntMagnitude pivotCoeff)
                      cofactorShape).symm).trans
                    ((congrArg
                        (fun probe => pcqNatDivCounting magnitudePred scaleValue * probe)
                        magnitudeShape).trans exactRecovery)
                let scaledOfNatEq : lfkIntScaleByNat (cofactorPred + 1)
                      (lfkIntMul pivotValue (lreIntOfNat (pcqIntMagnitude pivotCoeff)))
                    = scaledPivot :=
                  (lfkIntMulScaleRight pivotValue (cofactorPred + 1)
                      (lreIntOfNat (pcqIntMagnitude pivotCoeff))).symm.trans
                    ((congrArg (fun probe => lfkIntMul pivotValue (lreIntOfNat probe))
                        mulRecovery).trans
                      (pcqIntMulOfNatRight pivotValue scaleValue))
                match signCase : Nat.ble pivotCoeff.negativePart pivotCoeff.positivePart with
                | true =>
                    let coeffEq : lfkIntEq pivotCoeff
                        (lreIntOfNat (pcqIntMagnitude pivotCoeff)) = true :=
                      pcqIntEqOfNatMagnitude pivotCoeff signCase
                    let pivotMulIff : Iff
                        (lfkIntLt (lfkIntMul pivotValue pivotCoeff) residualValue = true)
                        (lfkIntLt (lfkIntMul pivotValue
                            (lreIntOfNat (pcqIntMagnitude pivotCoeff)))
                          residualValue = true) :=
                      Iff.intro
                        (fun strictWitness =>
                          lreIntLtCongrLeft (pcqIntMulCrossEqRight pivotValue coeffEq)
                            strictWitness)
                        (fun strictWitness =>
                          lreIntLtCongrLeft
                            (lreIntEqSymm (pcqIntMulCrossEqRight pivotValue coeffEq))
                            strictWitness)
                    let scaledIff : Iff
                        (lfkIntLt (lfkIntMul pivotValue
                            (lreIntOfNat (pcqIntMagnitude pivotCoeff)))
                          residualValue = true)
                        (lfkIntLt scaledPivot
                          (lfkIntScaleByNat (cofactorPred + 1) residualValue) = true) :=
                      Iff.intro
                        (fun strictWitness =>
                          Eq.mp
                            (congrArg
                              (fun probe => lfkIntLt probe
                                (lfkIntScaleByNat (cofactorPred + 1) residualValue) = true)
                              scaledOfNatEq)
                            (lreIntScaleLtMono cofactorPred strictWitness))
                        (fun strictWitness =>
                          pcqIntLtCancelScale cofactorPred
                            (Eq.mpr
                              (congrArg
                                (fun probe => lfkIntLt probe
                                  (lfkIntScaleByNat (cofactorPred + 1) residualValue)
                                    = true)
                                scaledOfNatEq)
                              strictWitness))
                    let targetEq : pcqMatrixHolds env scaledPivot
                          (PcqMatrix.mupper (pcqTermScaleByNat builderCofactor residualTerm))
                        = (lfkIntLt scaledPivot
                            (lfkIntScaleByNat (cofactorPred + 1) residualValue) = true) :=
                      congrArg (fun probe => lfkIntLt scaledPivot probe = true)
                        ((pcqTermEvalScale env builderCofactor residualTerm).trans
                          ((congrArg
                              (fun probe => lfkIntScaleByNat builderCofactor probe)
                              residualEvalEq).trans
                            (congrArg
                              (fun probe => lfkIntScaleByNat probe residualValue)
                              cofactorRewrite)))
                    pcqIffCongrRight
                      ((pcqMatrixHoldsCondEqFalse env scaledPivot _ _ magnitudeCase).trans
                        (pcqMatrixHoldsCondEqTrue env scaledPivot _ _ signCase))
                      (diffIff.trans (pivotMulIff.trans
                        (scaledIff.trans (pcqIffOfEq targetEq).symm)))
                | false =>
                    let coeffEq : lfkIntEq pivotCoeff
                        (lfkIntNegate (lreIntOfNat (pcqIntMagnitude pivotCoeff))) = true :=
                      pcqIntEqNegOfNatMagnitude pivotCoeff signCase
                    let negFlipIff : Iff
                        (lfkIntLt (lfkIntMul pivotValue pivotCoeff) residualValue = true)
                        (lfkIntLt (lfkIntNegate residualValue)
                          (lfkIntMul pivotValue
                            (lreIntOfNat (pcqIntMagnitude pivotCoeff))) = true) :=
                      Iff.intro
                        (fun strictWitness =>
                          pcqIntLtNegFlip
                            (leftValue := lfkIntMul pivotValue
                              (lreIntOfNat (pcqIntMagnitude pivotCoeff)))
                            (rightValue := residualValue)
                            (lreIntLtCongrLeft (pcqIntMulCrossEqRight pivotValue coeffEq)
                              strictWitness))
                        (fun strictWitness =>
                          lreIntLtCongrLeft
                            (lreIntEqSymm (pcqIntMulCrossEqRight pivotValue coeffEq))
                            (pcqIntLtNegFlip
                              (leftValue := residualValue)
                              (rightValue := lfkIntMul pivotValue
                                (lreIntOfNat (pcqIntMagnitude pivotCoeff)))
                              strictWitness))
                    let scaledIff : Iff
                        (lfkIntLt (lfkIntNegate residualValue)
                          (lfkIntMul pivotValue
                            (lreIntOfNat (pcqIntMagnitude pivotCoeff))) = true)
                        (lfkIntLt (lfkIntScaleByNat (cofactorPred + 1)
                            (lfkIntNegate residualValue)) scaledPivot = true) :=
                      Iff.intro
                        (fun strictWitness =>
                          Eq.mp
                            (congrArg
                              (fun probe => lfkIntLt
                                (lfkIntScaleByNat (cofactorPred + 1)
                                  (lfkIntNegate residualValue)) probe = true)
                              scaledOfNatEq)
                            (lreIntScaleLtMono cofactorPred strictWitness))
                        (fun strictWitness =>
                          pcqIntLtCancelScale cofactorPred
                            (Eq.mpr
                              (congrArg
                                (fun probe => lfkIntLt
                                  (lfkIntScaleByNat (cofactorPred + 1)
                                    (lfkIntNegate residualValue)) probe = true)
                                scaledOfNatEq)
                              strictWitness))
                    let targetEq : pcqMatrixHolds env scaledPivot
                          (PcqMatrix.mlower
                            (pcqTermScaleByNat builderCofactor (pcqTermNegate residualTerm)))
                        = (lfkIntLt (lfkIntScaleByNat (cofactorPred + 1)
                            (lfkIntNegate residualValue)) scaledPivot = true) :=
                      congrArg (fun probe => lfkIntLt probe scaledPivot = true)
                        ((pcqTermEvalScale env builderCofactor
                            (pcqTermNegate residualTerm)).trans
                          ((congrArg
                              (fun probe => lfkIntScaleByNat builderCofactor probe)
                              ((pcqTermEvalNegate env residualTerm).trans
                                (congrArg lfkIntNegate residualEvalEq))).trans
                            (congrArg
                              (fun probe => lfkIntScaleByNat probe
                                (lfkIntNegate residualValue))
                              cofactorRewrite)))
                    pcqIffCongrRight
                      ((pcqMatrixHoldsCondEqFalse env scaledPivot _ _ magnitudeCase).trans
                        (pcqMatrixHoldsCondEqFalse env scaledPivot _ _ signCase))
                      (diffIff.trans (negFlipIff.trans
                        (scaledIff.trans (pcqIffOfEq targetEq).symm))))

/-- THE DIVISIBILITY UNITARIZATION EQUIVALENCE: `(mp+1) | c*x + u` at pivot
`x` is the unitarized divisibility at pivot `scale*x` (modulus and offset
scaled by the counting cofactor; negative coefficients route through the
negation invariance of divisibility). -/
theorem pcqUnitDvdAtomEquiv (env : List LfkInt) (scaleValue : Nat)
    (scalePositive : Nat.ble 1 scaleValue = true) (modulusPred : Nat) (target : PcqTerm)
    (pivotValue : LfkInt)
    (divideWitness : pcqNatDividesProp (pcqMagnitudeOrOne (pcqTermHeadCoeff target))
      scaleValue) :
    Iff
      (pcqDividesProp (modulusPred + 1) (pcqTermEval (pivotValue :: env) target))
      (pcqMatrixHolds env (lfkIntScaleByNat scaleValue pivotValue)
        (pcqUnitDvdAtom scaleValue modulusPred (pcqTermHeadCoeff target)
          (pcqTermTail target))) :=
  let pivotCoeff := pcqTermHeadCoeff target
  let tailValue := pcqTermEval env (pcqTermTail target)
  let combinedValue := lfkIntAdd (lfkIntMul pivotValue pivotCoeff) tailValue
  let scaledPivot := lfkIntScaleByNat scaleValue pivotValue
  let splitEq : (pcqDividesProp (modulusPred + 1) (pcqTermEval (pivotValue :: env) target))
      = pcqDividesProp (modulusPred + 1) combinedValue :=
    congrArg (fun probe => pcqDividesProp (modulusPred + 1) probe)
      (pcqTermEvalConsSplit pivotValue env target)
  pcqIffCongrLeft splitEq
    (match magnitudeCase : Nat.beq (pcqIntMagnitude pivotCoeff) 0 with
     | true =>
        let zeroWitness : lfkIntIsZero pivotCoeff = true :=
          pcqIntZeroOfMagnitudeZero pivotCoeff magnitudeCase
        let dropEq : lfkIntEq combinedValue tailValue = true :=
          lreIntEqTrans
            (pcqIntEqOfEq (lfkIntAddComm (lfkIntMul pivotValue pivotCoeff) tailValue))
            (pcqIntEqDropZeroRight (lfkIntMulZeroRight pivotValue pivotCoeff zeroWitness))
        pcqIffCongrRight
          (pcqMatrixHoldsCondEqTrue env scaledPivot _ _ magnitudeCase)
          (Iff.intro
            (fun dividesWitness' => pcqDividesCrossEq dropEq dividesWitness')
            (fun dividesWitness' =>
              pcqDividesCrossEq (lreIntEqSymm dropEq) dividesWitness'))
     | false =>
        match pcqNatNonZeroShape (pcqIntMagnitude pivotCoeff) magnitudeCase with
        | Exists.intro magnitudePred magnitudeShape =>
            let divideMagnitude : pcqNatDividesProp (magnitudePred + 1) scaleValue :=
              Eq.mp
                (congrArg (fun probe => pcqNatDividesProp probe scaleValue)
                  ((pcqMagnitudeOrOneEqMagnitude pivotCoeff magnitudeCase).trans
                    magnitudeShape))
                divideWitness
            let builderCofactor :=
              pcqNatDivCounting (pcqNatPred (pcqIntMagnitude pivotCoeff)) scaleValue
            let builderCofactorEq : builderCofactor
                = pcqNatDivCounting magnitudePred scaleValue :=
              congrArg (fun probe => pcqNatDivCounting probe scaleValue)
                (congrArg pcqNatPred magnitudeShape)
            let exactRecovery : pcqNatDivCounting magnitudePred scaleValue
                * (magnitudePred + 1) = scaleValue :=
              pcqNatCountingQuotientExact magnitudePred scaleValue divideMagnitude
            match pcqNatCofactorShape (pcqNatDivCounting magnitudePred scaleValue)
              magnitudePred scaleValue exactRecovery scalePositive with
            | Exists.intro cofactorPred cofactorShape =>
                let cofactorRewrite : builderCofactor = cofactorPred + 1 :=
                  builderCofactorEq.trans cofactorShape
                let mulRecovery : (cofactorPred + 1) * pcqIntMagnitude pivotCoeff
                    = scaleValue :=
                  ((congrArg (fun probe => probe * pcqIntMagnitude pivotCoeff)
                      cofactorShape).symm).trans
                    ((congrArg
                        (fun probe => pcqNatDivCounting magnitudePred scaleValue * probe)
                        magnitudeShape).trans exactRecovery)
                let scaledOfNatEq : lfkIntScaleByNat (cofactorPred + 1)
                      (lfkIntMul pivotValue (lreIntOfNat (pcqIntMagnitude pivotCoeff)))
                    = scaledPivot :=
                  (lfkIntMulScaleRight pivotValue (cofactorPred + 1)
                      (lreIntOfNat (pcqIntMagnitude pivotCoeff))).symm.trans
                    ((congrArg (fun probe => lfkIntMul pivotValue (lreIntOfNat probe))
                        mulRecovery).trans
                      (pcqIntMulOfNatRight pivotValue scaleValue))
                let modulusRecover : pcqNatPred ((cofactorPred + 1) * (modulusPred + 1)) + 1
                    = (cofactorPred + 1) * (modulusPred + 1) :=
                  pcqNatPredSucc ((cofactorPred + 1) * (modulusPred + 1))
                    (lreNatPositiveMulPositive (cofactorPred + 1) (modulusPred + 1)
                      (lfkNatBleOfLe 1 (cofactorPred + 1)
                        (Nat.succ_le_succ (Nat.zero_le cofactorPred)))
                      (lfkNatBleOfLe 1 (modulusPred + 1)
                        (Nat.succ_le_succ (Nat.zero_le modulusPred))))
                let modulusEqChain : pcqNatPred (builderCofactor * (modulusPred + 1)) + 1
                    = (cofactorPred + 1) * (modulusPred + 1) :=
                  (congrArg
                      (fun probe => pcqNatPred (probe * (modulusPred + 1)) + 1)
                      cofactorRewrite).trans modulusRecover
                match signCase : Nat.ble pivotCoeff.negativePart pivotCoeff.positivePart with
                | true =>
                    let coeffEq : lfkIntEq pivotCoeff
                        (lreIntOfNat (pcqIntMagnitude pivotCoeff)) = true :=
                      pcqIntEqOfNatMagnitude pivotCoeff signCase
                    let scaledCombinedEq : lfkIntEq
                        (lfkIntScaleByNat (cofactorPred + 1) combinedValue)
                        (lfkIntAdd scaledPivot
                          (lfkIntScaleByNat (cofactorPred + 1) tailValue)) = true :=
                      lreIntEqTrans
                        (pcqIntEqOfEq (lfkIntScaleAddDistrib (cofactorPred + 1)
                          (lfkIntMul pivotValue pivotCoeff) tailValue))
                        (lfkIntAddEqEq
                          (lreIntEqTrans
                            (lfkIntScaleEqMono (cofactorPred + 1)
                              (pcqIntMulCrossEqRight pivotValue coeffEq))
                            (pcqIntEqOfEq scaledOfNatEq))
                          (lfkIntEqRefl (lfkIntScaleByNat (cofactorPred + 1) tailValue)))
                    let middleIff : Iff (pcqDividesProp (modulusPred + 1) combinedValue)
                        (pcqDividesProp ((cofactorPred + 1) * (modulusPred + 1))
                          (lfkIntAdd scaledPivot
                            (lfkIntScaleByNat (cofactorPred + 1) tailValue))) :=
                      Iff.intro
                        (fun dividesWitness' =>
                          pcqDividesCrossEq scaledCombinedEq
                            (pcqDividesScaleUp (cofactorPred + 1) (modulusPred + 1)
                              combinedValue dividesWitness'))
                        (fun dividesWitness' =>
                          pcqDividesScaleDown cofactorPred (modulusPred + 1) combinedValue
                            (pcqDividesCrossEq (lreIntEqSymm scaledCombinedEq)
                              dividesWitness'))
                    let targetEq : pcqMatrixHolds env scaledPivot
                          (PcqMatrix.mdvd (pcqNatPred (builderCofactor * (modulusPred + 1)))
                            (pcqTermScaleByNat builderCofactor (pcqTermTail target)))
                        = pcqDividesProp ((cofactorPred + 1) * (modulusPred + 1))
                            (lfkIntAdd scaledPivot
                              (lfkIntScaleByNat (cofactorPred + 1) tailValue)) :=
                      (congrArg
                          (fun probe =>
                            pcqDividesProp
                              (pcqNatPred (builderCofactor * (modulusPred + 1)) + 1)
                              (lfkIntAdd scaledPivot probe))
                          ((pcqTermEvalScale env builderCofactor (pcqTermTail target)).trans
                            (congrArg (fun probe => lfkIntScaleByNat probe tailValue)
                              cofactorRewrite))).trans
                        (congrArg
                          (fun probe => pcqDividesProp probe
                            (lfkIntAdd scaledPivot
                              (lfkIntScaleByNat (cofactorPred + 1) tailValue)))
                          modulusEqChain)
                    pcqIffCongrRight
                      ((pcqMatrixHoldsCondEqFalse env scaledPivot _ _ magnitudeCase).trans
                        (pcqMatrixHoldsCondEqTrue env scaledPivot _ _ signCase))
                      (middleIff.trans (pcqIffOfEq targetEq).symm)
                | false =>
                    let negCoeffEq : lfkIntEq (lfkIntNegate pivotCoeff)
                        (lreIntOfNat (pcqIntMagnitude pivotCoeff)) = true :=
                      (pcqIntEqNegateCongr
                        (pcqIntEqNegOfNatMagnitude pivotCoeff signCase))
                    let scaledNegCombinedEq : lfkIntEq
                        (lfkIntScaleByNat (cofactorPred + 1) (lfkIntNegate combinedValue))
                        (lfkIntAdd scaledPivot
                          (lfkIntScaleByNat (cofactorPred + 1)
                            (lfkIntNegate tailValue))) = true :=
                      lreIntEqTrans
                        (pcqIntEqOfEq (lfkIntScaleAddDistrib (cofactorPred + 1)
                          (lfkIntMul pivotValue (lfkIntNegate pivotCoeff))
                          (lfkIntNegate tailValue)))
                        (lfkIntAddEqEq
                          (lreIntEqTrans
                            (lfkIntScaleEqMono (cofactorPred + 1)
                              (pcqIntMulCrossEqRight pivotValue negCoeffEq))
                            (pcqIntEqOfEq scaledOfNatEq))
                          (lfkIntEqRefl (lfkIntScaleByNat (cofactorPred + 1)
                            (lfkIntNegate tailValue))))
                    let middleIff : Iff (pcqDividesProp (modulusPred + 1) combinedValue)
                        (pcqDividesProp ((cofactorPred + 1) * (modulusPred + 1))
                          (lfkIntAdd scaledPivot
                            (lfkIntScaleByNat (cofactorPred + 1)
                              (lfkIntNegate tailValue)))) :=
                      Iff.intro
                        (fun dividesWitness' =>
                          pcqDividesCrossEq scaledNegCombinedEq
                            (pcqDividesScaleUp (cofactorPred + 1) (modulusPred + 1)
                              (lfkIntNegate combinedValue)
                              (pcqDividesNegate (modulusPred + 1) combinedValue
                                dividesWitness')))
                        (fun dividesWitness' =>
                          pcqDividesNegate (modulusPred + 1) (lfkIntNegate combinedValue)
                            (pcqDividesScaleDown cofactorPred (modulusPred + 1)
                              (lfkIntNegate combinedValue)
                              (pcqDividesCrossEq (lreIntEqSymm scaledNegCombinedEq)
                                dividesWitness')))
                    let targetEq : pcqMatrixHolds env scaledPivot
                          (PcqMatrix.mdvd (pcqNatPred (builderCofactor * (modulusPred + 1)))
                            (pcqTermScaleByNat builderCofactor
                              (pcqTermNegate (pcqTermTail target))))
                        = pcqDividesProp ((cofactorPred + 1) * (modulusPred + 1))
                            (lfkIntAdd scaledPivot
                              (lfkIntScaleByNat (cofactorPred + 1)
                                (lfkIntNegate tailValue))) :=
                      (congrArg
                          (fun probe =>
                            pcqDividesProp
                              (pcqNatPred (builderCofactor * (modulusPred + 1)) + 1)
                              (lfkIntAdd scaledPivot probe))
                          ((pcqTermEvalScale env builderCofactor
                              (pcqTermNegate (pcqTermTail target))).trans
                            ((congrArg
                                (fun probe => lfkIntScaleByNat builderCofactor probe)
                                (pcqTermEvalNegate env (pcqTermTail target))).trans
                              (congrArg
                                (fun probe => lfkIntScaleByNat probe
                                  (lfkIntNegate tailValue))
                                cofactorRewrite)))).trans
                        (congrArg
                          (fun probe => pcqDividesProp probe
                            (lfkIntAdd scaledPivot
                              (lfkIntScaleByNat (cofactorPred + 1)
                                (lfkIntNegate tailValue))))
                          modulusEqChain)
                    pcqIffCongrRight
                      ((pcqMatrixHoldsCondEqFalse env scaledPivot _ _ magnitudeCase).trans
                        (pcqMatrixHoldsCondEqFalse env scaledPivot _ _ signCase))
                      (middleIff.trans (pcqIffOfEq targetEq).symm))

/-- The negated-divisibility builder mirrors the divisibility builder: its
satisfaction is exactly the negation of the latter's, case by case. -/
theorem pcqUnitNdvdMirror (env : List LfkInt) (pivotValue : LfkInt)
    (scaleValue modulusPred : Nat) (pivotCoeff : LfkInt) (tailTerm : PcqTerm) :
    Iff
      (pcqMatrixHolds env pivotValue
        (pcqUnitNdvdAtom scaleValue modulusPred pivotCoeff tailTerm))
      (pcqMatrixHolds env pivotValue
        (pcqUnitDvdAtom scaleValue modulusPred pivotCoeff tailTerm) → False) :=
  match magnitudeCase : Nat.beq (pcqIntMagnitude pivotCoeff) 0 with
  | true =>
      pcqIffCongrLeft (pcqMatrixHoldsCondEqTrue env pivotValue _ _ magnitudeCase)
        (pcqIffCongrRight
          (congrArg (fun probe => probe → False)
            (pcqMatrixHoldsCondEqTrue env pivotValue _ _ magnitudeCase))
          Iff.rfl)
  | false =>
      match signCase : Nat.ble pivotCoeff.negativePart pivotCoeff.positivePart with
      | true =>
          pcqIffCongrLeft
            ((pcqMatrixHoldsCondEqFalse env pivotValue _ _ magnitudeCase).trans
              (pcqMatrixHoldsCondEqTrue env pivotValue _ _ signCase))
            (pcqIffCongrRight
              (congrArg (fun probe => probe → False)
                ((pcqMatrixHoldsCondEqFalse env pivotValue _ _ magnitudeCase).trans
                  (pcqMatrixHoldsCondEqTrue env pivotValue _ _ signCase)))
              Iff.rfl)
      | false =>
          pcqIffCongrLeft
            ((pcqMatrixHoldsCondEqFalse env pivotValue _ _ magnitudeCase).trans
              (pcqMatrixHoldsCondEqFalse env pivotValue _ _ signCase))
            (pcqIffCongrRight
              (congrArg (fun probe => probe → False)
                ((pcqMatrixHoldsCondEqFalse env pivotValue _ _ magnitudeCase).trans
                  (pcqMatrixHoldsCondEqFalse env pivotValue _ _ signCase)))
              Iff.rfl)

/-- THE NEGATED-DIVISIBILITY UNITARIZATION EQUIVALENCE (negation wrap of the
divisibility equivalence through the mirror). -/
theorem pcqUnitNdvdAtomEquiv (env : List LfkInt) (scaleValue : Nat)
    (scalePositive : Nat.ble 1 scaleValue = true) (modulusPred : Nat) (target : PcqTerm)
    (pivotValue : LfkInt)
    (divideWitness : pcqNatDividesProp (pcqMagnitudeOrOne (pcqTermHeadCoeff target))
      scaleValue) :
    Iff
      (pcqDividesProp (modulusPred + 1) (pcqTermEval (pivotValue :: env) target) → False)
      (pcqMatrixHolds env (lfkIntScaleByNat scaleValue pivotValue)
        (pcqUnitNdvdAtom scaleValue modulusPred (pcqTermHeadCoeff target)
          (pcqTermTail target))) :=
  let coreIff := pcqUnitDvdAtomEquiv env scaleValue scalePositive modulusPred target
    pivotValue divideWitness
  let mirrorIff := pcqUnitNdvdMirror env (lfkIntScaleByNat scaleValue pivotValue)
    scaleValue modulusPred (pcqTermHeadCoeff target) (pcqTermTail target)
  Iff.intro
    (fun negWitness =>
      mirrorIff.mpr (fun dvdHolds => negWitness (coreIff.mpr dvdHolds)))
    (fun ndvdHolds dividesWitness' =>
      (mirrorIff.mp ndvdHolds) (coreIff.mp dividesWitness'))

/-- The unit matrix of an NNF formula: every atom unitarized at the shared
global scale. -/
def pcqUnitMatrix (scaleValue : Nat) : PcqNnfFormula → PcqMatrix
  | PcqNnfFormula.nlt leftTerm rightTerm =>
      pcqUnitLtAtom scaleValue (pcqNnfLtPivot leftTerm rightTerm)
        (pcqTermAdd (pcqTermTail rightTerm) (pcqTermNegate (pcqTermTail leftTerm)))
  | PcqNnfFormula.ndvd modulusPred target =>
      pcqUnitDvdAtom scaleValue modulusPred (pcqTermHeadCoeff target) (pcqTermTail target)
  | PcqNnfFormula.nndvd modulusPred target =>
      pcqUnitNdvdAtom scaleValue modulusPred (pcqTermHeadCoeff target) (pcqTermTail target)
  | PcqNnfFormula.nconj leftBranch rightBranch =>
      PcqMatrix.mconj (pcqUnitMatrix scaleValue leftBranch)
        (pcqUnitMatrix scaleValue rightBranch)
  | PcqNnfFormula.ndisj leftBranch rightBranch =>
      PcqMatrix.mdisj (pcqUnitMatrix scaleValue leftBranch)
        (pcqUnitMatrix scaleValue rightBranch)

/-- THE UNIT-MATRIX EQUIVALENCE (Chaieb–Nipkow fact (3), product-scale form):
the NNF formula holds at pivot `x` under the binder exactly when its unit
matrix holds at pivot `scale*x` over the stripped environment. -/
theorem pcqUnitMatrixEquiv (env : List LfkInt) (scaleValue : Nat)
    (scalePositive : Nat.ble 1 scaleValue = true) :
    ∀ (formula : PcqNnfFormula), pcqNnfCoeffsDivide formula scaleValue →
    ∀ (pivotValue : LfkInt),
    Iff (pcqNnfHolds (pivotValue :: env) formula)
      (pcqMatrixHolds env (lfkIntScaleByNat scaleValue pivotValue)
        (pcqUnitMatrix scaleValue formula))
  | PcqNnfFormula.nlt leftTerm rightTerm, divideWitness, pivotValue =>
      pcqUnitLtAtomEquiv env scaleValue scalePositive leftTerm rightTerm pivotValue
        divideWitness
  | PcqNnfFormula.ndvd modulusPred target, divideWitness, pivotValue =>
      pcqUnitDvdAtomEquiv env scaleValue scalePositive modulusPred target pivotValue
        divideWitness
  | PcqNnfFormula.nndvd modulusPred target, divideWitness, pivotValue =>
      pcqUnitNdvdAtomEquiv env scaleValue scalePositive modulusPred target pivotValue
        divideWitness
  | PcqNnfFormula.nconj leftBranch rightBranch, divideWitness, pivotValue =>
      let leftIff := pcqUnitMatrixEquiv env scaleValue scalePositive leftBranch
        divideWitness.left pivotValue
      let rightIff := pcqUnitMatrixEquiv env scaleValue scalePositive rightBranch
        divideWitness.right pivotValue
      Iff.intro
        (fun bothHold => And.intro (leftIff.mp bothHold.left) (rightIff.mp bothHold.right))
        (fun bothHold => And.intro (leftIff.mpr bothHold.left) (rightIff.mpr bothHold.right))
  | PcqNnfFormula.ndisj leftBranch rightBranch, divideWitness, pivotValue =>
      let leftIff := pcqUnitMatrixEquiv env scaleValue scalePositive leftBranch
        divideWitness.left pivotValue
      let rightIff := pcqUnitMatrixEquiv env scaleValue scalePositive rightBranch
        divideWitness.right pivotValue
      Iff.intro
        (fun eitherHolds =>
          match eitherHolds with
          | Or.inl leftHolds => Or.inl (leftIff.mp leftHolds)
          | Or.inr rightHolds => Or.inr (rightIff.mp rightHolds))
        (fun eitherHolds =>
          match eitherHolds with
          | Or.inl leftHolds => Or.inl (leftIff.mpr leftHolds)
          | Or.inr rightHolds => Or.inr (rightIff.mpr rightHolds))

/-! ## Stage B6 — the separated matrix: the U-step recorded as ONE added
`scale | pivot` divisibility atom (Chaieb–Nipkow fact (2)) -/

/-- The separated (fully unitary) matrix: the unit matrix conjoined with the
single recording atom `scale | pivot + 0`. -/
def pcqSeparate (formula : PcqNnfFormula) : PcqMatrix :=
  PcqMatrix.mconj (pcqUnitMatrix (pcqNnfScale formula) formula)
    (PcqMatrix.mdvd (pcqNatPred (pcqNnfScale formula)) (pcqConstTerm lfkIntZero))

/-- THE SEPARATION EQUIVALENCE (Chaieb–Nipkow fact (2)/(3) combined):
`∃ x. phi(x)` exactly when the separated matrix has a satisfying unit pivot. -/
theorem pcqSeparateEquiv (env : List LfkInt) (formula : PcqNnfFormula) :
    Iff (∃ (pivotValue : LfkInt), pcqNnfHolds (pivotValue :: env) formula)
      (∃ (unitPivot : LfkInt), pcqMatrixHolds env unitPivot (pcqSeparate formula)) :=
  let scaleValue := pcqNnfScale formula
  let scaleRecover : pcqNatPred scaleValue + 1 = scaleValue :=
    pcqNatPredSucc scaleValue (pcqNnfScalePositive formula)
  Iff.intro
    (fun existsWitness =>
      match existsWitness with
      | Exists.intro pivotValue holdsWitness =>
          let unitPivot := lfkIntScaleByNat scaleValue pivotValue
          let valueEq : lfkIntAdd unitPivot (pcqTermEval env (pcqConstTerm lfkIntZero))
              = unitPivot :=
            congrArg (fun probe => lfkIntAdd unitPivot probe)
              (pcqConstTermEval env lfkIntZero)
          Exists.intro unitPivot
            (And.intro
              ((pcqUnitMatrixEquiv env scaleValue (pcqNnfScalePositive formula) formula
                (pcqNnfCoeffsDivideScale formula) pivotValue).mp holdsWitness)
              (Eq.mpr
                (congrArg (fun probe => pcqDividesProp (pcqNatPred scaleValue + 1) probe)
                  valueEq)
                (Eq.mpr
                  (congrArg (fun probe => pcqDividesProp probe unitPivot) scaleRecover)
                  (Exists.intro pivotValue (lfkIntEqRefl unitPivot))))))
    (fun existsWitness =>
      match existsWitness with
      | Exists.intro unitPivot holdsWitness =>
          let valueEq : lfkIntAdd unitPivot (pcqTermEval env (pcqConstTerm lfkIntZero))
              = unitPivot :=
            congrArg (fun probe => lfkIntAdd unitPivot probe)
              (pcqConstTermEval env lfkIntZero)
          let dividesUnit : pcqDividesProp scaleValue unitPivot :=
            Eq.mp (congrArg (fun probe => pcqDividesProp probe unitPivot) scaleRecover)
              (Eq.mp
                (congrArg (fun probe => pcqDividesProp (pcqNatPred scaleValue + 1) probe)
                  valueEq)
                holdsWitness.right)
          match dividesUnit with
          | Exists.intro quotientPivot quotientEq =>
              Exists.intro quotientPivot
                ((pcqUnitMatrixEquiv env scaleValue (pcqNnfScalePositive formula) formula
                  (pcqNnfCoeffsDivideScale formula) quotientPivot).mpr
                  (pcqMatrixHoldsCrossEq env (lreIntEqSymm quotientEq)
                    (pcqUnitMatrix scaleValue formula) holdsWitness.left)))

/-! ## Stage D1 — quantifier-free emission of a matrix at a pivot term -/

/-- The trivially-true quantifier-free formula (`0 < 1`). -/
def pcqQfTrueFormula : PcqQfFormula :=
  PcqQfFormula.qlt (pcqConstTerm lfkIntZero) (pcqConstTerm lreIntOne)

/-- The trivially-false quantifier-free formula (`1 < 0`). -/
def pcqQfFalseFormula : PcqQfFormula :=
  PcqQfFormula.qlt (pcqConstTerm lreIntOne) (pcqConstTerm lfkIntZero)

/-- The true formula holds in every environment. -/
theorem pcqQfTrueFormulaHolds (env : List LfkInt) : pcqQfHolds env pcqQfTrueFormula :=
  Eq.mpr
    (congrArg (fun probe => probe = true)
      ((congrArg (fun probe => lfkIntLt probe (pcqTermEval env (pcqConstTerm lreIntOne)))
          (pcqConstTermEval env lfkIntZero)).trans
        (congrArg (fun probe => lfkIntLt lfkIntZero probe)
          (pcqConstTermEval env lreIntOne))))
    rfl

/-- The false formula holds in no environment. -/
theorem pcqQfFalseFormulaAbsurd (env : List LfkInt)
    (holdsWitness : pcqQfHolds env pcqQfFalseFormula) : False :=
  Bool.noConfusion
    (Eq.mp
      (congrArg (fun probe => probe = true)
        ((congrArg (fun probe => lfkIntLt probe (pcqTermEval env (pcqConstTerm lfkIntZero)))
            (pcqConstTermEval env lreIntOne)).trans
          (congrArg (fun probe => lfkIntLt lreIntOne probe)
            (pcqConstTermEval env lfkIntZero))))
      holdsWitness)

/-- Substitute a pivot term into a matrix, producing a quantifier-free
formula over the outer environment. -/
def pcqQfOfMatrixAt : PcqMatrix → PcqTerm → PcqQfFormula
  | PcqMatrix.mtrue, _pivotTerm => pcqQfTrueFormula
  | PcqMatrix.mfalse, _pivotTerm => pcqQfFalseFormula
  | PcqMatrix.mupper bound, pivotTerm => PcqQfFormula.qlt pivotTerm bound
  | PcqMatrix.mlower bound, pivotTerm => PcqQfFormula.qlt bound pivotTerm
  | PcqMatrix.mdvd modulusPred offset, pivotTerm =>
      PcqQfFormula.qdvd modulusPred (pcqTermAdd pivotTerm offset)
  | PcqMatrix.mndvd modulusPred offset, pivotTerm =>
      PcqQfFormula.qndvd modulusPred (pcqTermAdd pivotTerm offset)
  | PcqMatrix.mfreelt leftTerm rightTerm, _pivotTerm =>
      PcqQfFormula.qlt leftTerm rightTerm
  | PcqMatrix.mfreedvd modulusPred target, _pivotTerm =>
      PcqQfFormula.qdvd modulusPred target
  | PcqMatrix.mfreendvd modulusPred target, _pivotTerm =>
      PcqQfFormula.qndvd modulusPred target
  | PcqMatrix.mconj leftBranch rightBranch, pivotTerm =>
      PcqQfFormula.qconj (pcqQfOfMatrixAt leftBranch pivotTerm)
        (pcqQfOfMatrixAt rightBranch pivotTerm)
  | PcqMatrix.mdisj leftBranch rightBranch, pivotTerm =>
      PcqQfFormula.qdisj (pcqQfOfMatrixAt leftBranch pivotTerm)
        (pcqQfOfMatrixAt rightBranch pivotTerm)

/-- THE SUBSTITUTION LEMMA: the emitted formula holds exactly when the matrix
holds at the pivot term's value. -/
theorem pcqQfOfMatrixAtHolds (env : List LfkInt) (pivotTerm : PcqTerm) :
    ∀ (matrix : PcqMatrix),
    Iff (pcqQfHolds env (pcqQfOfMatrixAt matrix pivotTerm))
      (pcqMatrixHolds env (pcqTermEval env pivotTerm) matrix)
  | PcqMatrix.mtrue =>
      Iff.intro (fun _holdsWitness => True.intro)
        (fun _trivialWitness => pcqQfTrueFormulaHolds env)
  | PcqMatrix.mfalse =>
      Iff.intro (fun holdsWitness => pcqQfFalseFormulaAbsurd env holdsWitness)
        (fun falseWitness => False.elim falseWitness)
  | PcqMatrix.mupper _bound => Iff.rfl
  | PcqMatrix.mlower _bound => Iff.rfl
  | PcqMatrix.mdvd modulusPred offset =>
      pcqIffOfEq
        (congrArg (fun probe => pcqDividesProp (modulusPred + 1) probe)
          (pcqTermEvalAdd env pivotTerm offset))
  | PcqMatrix.mndvd modulusPred offset =>
      pcqIffOfEq
        (congrArg (fun probe => pcqDividesProp (modulusPred + 1) probe → False)
          (pcqTermEvalAdd env pivotTerm offset))
  | PcqMatrix.mfreelt _leftTerm _rightTerm => Iff.rfl
  | PcqMatrix.mfreedvd _modulusPred _target => Iff.rfl
  | PcqMatrix.mfreendvd _modulusPred _target => Iff.rfl
  | PcqMatrix.mconj leftBranch rightBranch =>
      let leftIff := pcqQfOfMatrixAtHolds env pivotTerm leftBranch
      let rightIff := pcqQfOfMatrixAtHolds env pivotTerm rightBranch
      Iff.intro
        (fun bothHold => And.intro (leftIff.mp bothHold.left) (rightIff.mp bothHold.right))
        (fun bothHold =>
          And.intro (leftIff.mpr bothHold.left) (rightIff.mpr bothHold.right))
  | PcqMatrix.mdisj leftBranch rightBranch =>
      let leftIff := pcqQfOfMatrixAtHolds env pivotTerm leftBranch
      let rightIff := pcqQfOfMatrixAtHolds env pivotTerm rightBranch
      Iff.intro
        (fun eitherHolds =>
          match eitherHolds with
          | Or.inl leftHolds => Or.inl (leftIff.mp leftHolds)
          | Or.inr rightHolds => Or.inr (rightIff.mp rightHolds))
        (fun eitherHolds =>
          match eitherHolds with
          | Or.inl leftHolds => Or.inl (leftIff.mpr leftHolds)
          | Or.inr rightHolds => Or.inr (rightIff.mpr rightHolds))

/-! ## Stage D2 — quantifier-free finite disjunction builders and their
reflections into the recursive `pcqAnyUpTo` / `pcqAnyTerm` Props -/

/-- The disjunction of `builder j` over `j` in `[1..bound]`. -/
def pcqQfOrUpTo (builder : Nat → PcqQfFormula) : Nat → PcqQfFormula
  | Nat.zero => pcqQfFalseFormula
  | Nat.succ boundPred =>
      PcqQfFormula.qdisj (pcqQfOrUpTo builder boundPred) (builder (boundPred + 1))

/-- Range-disjunction reflection. -/
theorem pcqQfOrUpToHolds (env : List LfkInt) (builder : Nat → PcqQfFormula) :
    ∀ (bound : Nat),
    Iff (pcqQfHolds env (pcqQfOrUpTo builder bound))
      (pcqAnyUpTo (fun windowIndex => pcqQfHolds env (builder windowIndex)) bound)
  | Nat.zero =>
      Iff.intro (fun holdsWitness => pcqQfFalseFormulaAbsurd env holdsWitness)
        (fun falseWitness => False.elim falseWitness)
  | Nat.succ boundPred =>
      let tailIff := pcqQfOrUpToHolds env builder boundPred
      Iff.intro
        (fun eitherHolds =>
          match eitherHolds with
          | Or.inl tailHolds => Or.inl (tailIff.mp tailHolds)
          | Or.inr headHolds => Or.inr headHolds)
        (fun eitherHolds =>
          match eitherHolds with
          | Or.inl tailAny => Or.inl (tailIff.mpr tailAny)
          | Or.inr headHolds => Or.inr headHolds)

/-- The disjunction of `builder b` over the terms of a list. -/
def pcqQfOrOverTerms (builder : PcqTerm → PcqQfFormula) : List PcqTerm → PcqQfFormula
  | List.nil => pcqQfFalseFormula
  | headTerm :: tailTerms =>
      PcqQfFormula.qdisj (builder headTerm) (pcqQfOrOverTerms builder tailTerms)

/-- Term-list-disjunction reflection. -/
theorem pcqQfOrOverTermsHolds (env : List LfkInt) (builder : PcqTerm → PcqQfFormula) :
    ∀ (termList : List PcqTerm),
    Iff (pcqQfHolds env (pcqQfOrOverTerms builder termList))
      (pcqAnyTerm (fun boundTerm => pcqQfHolds env (builder boundTerm)) termList)
  | List.nil =>
      Iff.intro (fun holdsWitness => pcqQfFalseFormulaAbsurd env holdsWitness)
        (fun falseWitness => False.elim falseWitness)
  | _headTerm :: tailTerms =>
      let tailIff := pcqQfOrOverTermsHolds env builder tailTerms
      Iff.intro
        (fun eitherHolds =>
          match eitherHolds with
          | Or.inl headHolds => Or.inl headHolds
          | Or.inr tailHolds => Or.inr (tailIff.mp tailHolds))
        (fun eitherHolds =>
          match eitherHolds with
          | Or.inl headHolds => Or.inl headHolds
          | Or.inr tailAny => Or.inr (tailIff.mpr tailAny))

/-! ## Stage D3 — THE COOPER STEP as a quantifier-free formula -/

/-- One full Cooper elimination round on an NNF body: separate, then emit the
minus-infinity disjunction and the boundary-window disjunction over
`[1..delta]`. -/
def pcqCooperStep (formula : PcqNnfFormula) : PcqQfFormula :=
  let separatedMatrix := pcqSeparate formula
  PcqQfFormula.qdisj
    (pcqQfOrUpTo
      (fun windowIndex => pcqQfOfMatrixAt (pcqMinusInf separatedMatrix)
        (pcqConstTerm (lreIntOfNat windowIndex)))
      (pcqDelta separatedMatrix))
    (pcqQfOrOverTerms
      (fun boundTerm => pcqQfOrUpTo
        (fun windowIndex => pcqQfOfMatrixAt separatedMatrix
          (pcqTermAdd boundTerm (pcqConstTerm (lreIntOfNat windowIndex))))
        (pcqDelta separatedMatrix))
      (pcqLowerBounds separatedMatrix))

/-- THE COOPER STEP EQUIVALENCE: the emitted quantifier-free formula holds
exactly when some pivot satisfies the NNF body — the composition of the
separation equivalence, the Cooper elimination theorem, and the emission
reflections. -/
theorem pcqCooperStepEquiv (env : List LfkInt) (formula : PcqNnfFormula) :
    Iff (pcqQfHolds env (pcqCooperStep formula))
      (∃ (pivotValue : LfkInt), pcqNnfHolds (pivotValue :: env) formula) :=
  let separatedMatrix := pcqSeparate formula
  let deltaValue := pcqDelta separatedMatrix
  let minusInfPointIff : ∀ (windowIndex : Nat),
      Iff (pcqQfHolds env (pcqQfOfMatrixAt (pcqMinusInf separatedMatrix)
          (pcqConstTerm (lreIntOfNat windowIndex))))
        (pcqMatrixHolds env (lreIntOfNat windowIndex) (pcqMinusInf separatedMatrix)) :=
    fun windowIndex =>
      pcqIffCongrRight
        ((congrArg (fun probe => pcqMatrixHolds env probe (pcqMinusInf separatedMatrix))
            (pcqConstTermEval env (lreIntOfNat windowIndex))).symm)
        (pcqQfOfMatrixAtHolds env (pcqConstTerm (lreIntOfNat windowIndex))
          (pcqMinusInf separatedMatrix))
  let windowPointIff : ∀ (boundTerm : PcqTerm) (windowIndex : Nat),
      Iff (pcqQfHolds env (pcqQfOfMatrixAt separatedMatrix
          (pcqTermAdd boundTerm (pcqConstTerm (lreIntOfNat windowIndex)))))
        (pcqMatrixHolds env
          (lfkIntAdd (pcqTermEval env boundTerm) (lreIntOfNat windowIndex))
          separatedMatrix) :=
    fun boundTerm windowIndex =>
      pcqIffCongrRight
        ((congrArg (fun probe => pcqMatrixHolds env probe separatedMatrix)
            ((pcqTermEvalAdd env boundTerm (pcqConstTerm (lreIntOfNat windowIndex))).trans
              (congrArg (fun probe => lfkIntAdd (pcqTermEval env boundTerm) probe)
                (pcqConstTermEval env (lreIntOfNat windowIndex))))).symm)
        (pcqQfOfMatrixAtHolds env
          (pcqTermAdd boundTerm (pcqConstTerm (lreIntOfNat windowIndex))) separatedMatrix)
  let minusInfBranchIff : Iff
      (pcqQfHolds env (pcqQfOrUpTo (fun windowIndex =>
        pcqQfOfMatrixAt (pcqMinusInf separatedMatrix)
          (pcqConstTerm (lreIntOfNat windowIndex))) deltaValue))
      (pcqAnyUpTo (fun windowIndex =>
        pcqMatrixHolds env (lreIntOfNat windowIndex) (pcqMinusInf separatedMatrix))
        deltaValue) :=
    Iff.intro
      (fun qfAny =>
        pcqAnyUpToMap _ _
          (fun windowIndex pointWitness => (minusInfPointIff windowIndex).mp pointWitness)
          deltaValue
          ((pcqQfOrUpToHolds env _ deltaValue).mp qfAny))
      (fun propAny =>
        (pcqQfOrUpToHolds env _ deltaValue).mpr
          (pcqAnyUpToMap _ _
            (fun windowIndex pointWitness =>
              (minusInfPointIff windowIndex).mpr pointWitness)
            deltaValue propAny))
  let windowBranchIff : Iff
      (pcqQfHolds env (pcqQfOrOverTerms (fun boundTerm =>
        pcqQfOrUpTo (fun windowIndex => pcqQfOfMatrixAt separatedMatrix
          (pcqTermAdd boundTerm (pcqConstTerm (lreIntOfNat windowIndex)))) deltaValue)
        (pcqLowerBounds separatedMatrix)))
      (pcqAnyTerm (fun boundTerm => pcqAnyUpTo (fun windowIndex =>
          pcqMatrixHolds env
            (lfkIntAdd (pcqTermEval env boundTerm) (lreIntOfNat windowIndex))
            separatedMatrix) deltaValue)
        (pcqLowerBounds separatedMatrix)) :=
    Iff.intro
      (fun qfAny =>
        pcqAnyTermMap _ _
          (fun boundTerm innerQf =>
            pcqAnyUpToMap _ _
              (fun windowIndex pointWitness =>
                (windowPointIff boundTerm windowIndex).mp pointWitness)
              deltaValue
              ((pcqQfOrUpToHolds env _ deltaValue).mp innerQf))
          (pcqLowerBounds separatedMatrix)
          ((pcqQfOrOverTermsHolds env _ (pcqLowerBounds separatedMatrix)).mp qfAny))
      (fun propAny =>
        (pcqQfOrOverTermsHolds env _ (pcqLowerBounds separatedMatrix)).mpr
          (pcqAnyTermMap _ _
            (fun boundTerm innerAny =>
              (pcqQfOrUpToHolds env _ deltaValue).mpr
                (pcqAnyUpToMap _ _
                  (fun windowIndex pointWitness =>
                    (windowPointIff boundTerm windowIndex).mpr pointWitness)
                  deltaValue innerAny))
            (pcqLowerBounds separatedMatrix) propAny))
  Iff.intro
    (fun stepHolds =>
      (pcqSeparateEquiv env formula).mpr
        ((pcqCooperElimination env separatedMatrix).mpr
          (match stepHolds with
           | Or.inl minusInfQf => Or.inl (minusInfBranchIff.mp minusInfQf)
           | Or.inr windowQf => Or.inr (windowBranchIff.mp windowQf))))
    (fun existsWitness =>
      match (pcqCooperElimination env separatedMatrix).mp
        ((pcqSeparateEquiv env formula).mp existsWitness) with
      | Or.inl minusInfProp => Or.inl (minusInfBranchIff.mpr minusInfProp)
      | Or.inr windowProp => Or.inr (windowBranchIff.mpr windowProp))

/-! ## Stage D4 — THE FULL ELIMINATION AND DECISION -/

/-- Eliminate all quantifiers, inside-out: the `fexists` case runs
NNF -> separate -> Cooper step on the recursively eliminated body. -/
def pcqEliminate : PcqFormula → PcqQfFormula
  | PcqFormula.flt leftTerm rightTerm => PcqQfFormula.qlt leftTerm rightTerm
  | PcqFormula.fdvd modulusPred target => PcqQfFormula.qdvd modulusPred target
  | PcqFormula.fndvd modulusPred target => PcqQfFormula.qndvd modulusPred target
  | PcqFormula.fconj leftBranch rightBranch =>
      PcqQfFormula.qconj (pcqEliminate leftBranch) (pcqEliminate rightBranch)
  | PcqFormula.fdisj leftBranch rightBranch =>
      PcqQfFormula.qdisj (pcqEliminate leftBranch) (pcqEliminate rightBranch)
  | PcqFormula.fneg body => PcqQfFormula.qneg (pcqEliminate body)
  | PcqFormula.fexists body => pcqCooperStep (pcqNnfOfQf (pcqEliminate body) true)

/-- THE ELIMINATION EQUIVALENCE: the quantifier-free result holds exactly when
the surface formula holds — over EVERY environment (the binder case
instantiates the inner equivalence at the extended environment). -/
theorem pcqEliminateEquiv : ∀ (formula : PcqFormula) (env : List LfkInt),
    Iff (pcqQfHolds env (pcqEliminate formula)) (pcqInterp env formula)
  | PcqFormula.flt _leftTerm _rightTerm, _env => Iff.rfl
  | PcqFormula.fdvd _modulusPred _target, _env => Iff.rfl
  | PcqFormula.fndvd _modulusPred _target, _env => Iff.rfl
  | PcqFormula.fconj leftBranch rightBranch, env =>
      let leftIff := pcqEliminateEquiv leftBranch env
      let rightIff := pcqEliminateEquiv rightBranch env
      Iff.intro
        (fun bothHold => And.intro (leftIff.mp bothHold.left) (rightIff.mp bothHold.right))
        (fun bothHold =>
          And.intro (leftIff.mpr bothHold.left) (rightIff.mpr bothHold.right))
  | PcqFormula.fdisj leftBranch rightBranch, env =>
      let leftIff := pcqEliminateEquiv leftBranch env
      let rightIff := pcqEliminateEquiv rightBranch env
      Iff.intro
        (fun eitherHolds =>
          match eitherHolds with
          | Or.inl leftHolds => Or.inl (leftIff.mp leftHolds)
          | Or.inr rightHolds => Or.inr (rightIff.mp rightHolds))
        (fun eitherHolds =>
          match eitherHolds with
          | Or.inl leftHolds => Or.inl (leftIff.mpr leftHolds)
          | Or.inr rightHolds => Or.inr (rightIff.mpr rightHolds))
  | PcqFormula.fneg body, env =>
      let bodyIff := pcqEliminateEquiv body env
      Iff.intro
        (fun negWitness interpWitness => negWitness (bodyIff.mpr interpWitness))
        (fun negWitness qfWitness => negWitness (bodyIff.mp qfWitness))
  | PcqFormula.fexists body, env =>
      let stepIff := pcqCooperStepEquiv env (pcqNnfOfQf (pcqEliminate body) true)
      Iff.intro
        (fun stepHolds =>
          match stepIff.mp stepHolds with
          | Exists.intro pivotValue nnfWitness =>
              Exists.intro pivotValue
                ((pcqEliminateEquiv body (pivotValue :: env)).mp
                  ((pcqNnfOfQfSound (pivotValue :: env) (pcqEliminate body)).left.mp
                    nnfWitness)))
        (fun existsWitness =>
          match existsWitness with
          | Exists.intro pivotValue interpWitness =>
              stepIff.mpr
                (Exists.intro pivotValue
                  ((pcqNnfOfQfSound (pivotValue :: env) (pcqEliminate body)).left.mpr
                    ((pcqEliminateEquiv body (pivotValue :: env)).mpr interpWitness))))

/-- THE DECISION PROCEDURE: eliminate every quantifier, then evaluate the
quantifier-free result in the empty environment. -/
def pcqDecide (formula : PcqFormula) : Bool :=
  pcqQfEval List.nil (pcqEliminate formula)

/-- Decision soundness: `true` means the formula holds (empty environment). -/
theorem pcqDecideTrueSound (formula : PcqFormula)
    (decideWitness : pcqDecide formula = true) : pcqInterp List.nil formula :=
  (pcqEliminateEquiv formula List.nil).mp
    (pcqQfEvalTrueSound List.nil (pcqEliminate formula) decideWitness)

/-- Decision completeness: `false` refutes the formula (empty environment). -/
theorem pcqDecideFalseComplete (formula : PcqFormula)
    (decideWitness : pcqDecide formula = false)
    (interpWitness : pcqInterp List.nil formula) : False :=
  pcqQfEvalFalseComplete List.nil (pcqEliminate formula) decideWitness
    ((pcqEliminateEquiv formula List.nil).mpr interpWitness)

/-! ## Stage D5 — THE LANE WALL CONFRONTED: `lfkPresburgerDecisionStatement`
inhabited VERBATIM.  Each constraint row translates atom-for-atom through the
succ-le encoding; the system closes under `pcqSystemVarCount` existentials;
truncation/padding makes satisfaction depend only on the bound prefix. -/

/-- Cross-sum equality yields both weak cross-sum orders. -/
theorem pcqIntLeLeOfEq {leftValue rightValue : LfkInt}
    (eqWitness : lfkIntEq leftValue rightValue = true) :
    And (lfkIntLe leftValue rightValue = true) (lfkIntLe rightValue leftValue = true) :=
  let crossEq : leftValue.positivePart + rightValue.negativePart
      = rightValue.positivePart + leftValue.negativePart :=
    lfkNatEqOfBeq (leftValue.positivePart + rightValue.negativePart)
      (rightValue.positivePart + leftValue.negativePart) eqWitness
  And.intro
    (lfkNatBleOfLe (leftValue.positivePart + rightValue.negativePart)
      (rightValue.positivePart + leftValue.negativePart) (Nat.le_of_eq crossEq))
    (lfkNatBleOfLe (rightValue.positivePart + leftValue.negativePart)
      (leftValue.positivePart + rightValue.negativePart) (Nat.le_of_eq crossEq.symm))

/-- Both weak cross-sum orders yield cross-sum equality (antisymmetry). -/
theorem pcqIntEqOfLeLe {leftValue rightValue : LfkInt}
    (forwardLe : lfkIntLe leftValue rightValue = true)
    (backwardLe : lfkIntLe rightValue leftValue = true) :
    lfkIntEq leftValue rightValue = true :=
  lfkNatBeqOfEq (leftValue.positivePart + rightValue.negativePart)
    (rightValue.positivePart + leftValue.negativePart)
    (lfmNatEqOfBleBle (leftValue.positivePart + rightValue.negativePart)
      (rightValue.positivePart + leftValue.negativePart) forwardLe backwardLe)

/-- Translate one constraint row: `>=` through the succ-le bridge, `>`
directly, `=` as the two-sided succ-le conjunction. -/
def pcqConstraintFormula (constraint : LfkConstraint) : PcqFormula :=
  match constraint.relation with
  | LfkRelation.isGreaterOrEqual =>
      PcqFormula.flt (pcqConstTerm constraint.bound)
        (PcqTerm.mk constraint.coefficients lreIntOne)
  | LfkRelation.isStrictlyGreater =>
      PcqFormula.flt (pcqConstTerm constraint.bound)
        (PcqTerm.mk constraint.coefficients lfkIntZero)
  | LfkRelation.isEqualTo =>
      PcqFormula.fconj
        (PcqFormula.flt (pcqConstTerm constraint.bound)
          (PcqTerm.mk constraint.coefficients lreIntOne))
        (PcqFormula.flt (PcqTerm.mk constraint.coefficients lfkIntZero)
          (pcqConstTerm (lfkIntAdd constraint.bound lreIntOne)))

/-- ROW EQUIVALENCE: the translated row holds exactly when the constraint is
satisfied — same environment, same dot product. -/
theorem pcqConstraintFormulaSound (env : List LfkInt) :
    ∀ (constraint : LfkConstraint),
    Iff (pcqInterp env (pcqConstraintFormula constraint))
      (lfkSatisfiesConstraint env constraint = true)
  | LfkConstraint.mk coefficientVector boundValue LfkRelation.isGreaterOrEqual =>
      Iff.intro
        (fun interpWitness =>
          pcqIntLeOfLtSucc
            (Eq.mp
              (congrArg
                (fun probe => lfkIntLt probe
                  (lfkIntAdd (lfkDotProduct env coefficientVector) lreIntOne) = true)
                (pcqConstTermEval env boundValue))
              interpWitness))
        (fun satisfiesWitness =>
          Eq.mpr
            (congrArg
              (fun probe => lfkIntLt probe
                (lfkIntAdd (lfkDotProduct env coefficientVector) lreIntOne) = true)
              (pcqConstTermEval env boundValue))
            (pcqIntLtSuccOfLe satisfiesWitness))
  | LfkConstraint.mk coefficientVector boundValue LfkRelation.isStrictlyGreater =>
      pcqIffOfEq
        (congrArg
          (fun probe => lfkIntLt probe (lfkDotProduct env coefficientVector) = true)
          (pcqConstTermEval env boundValue))
  | LfkConstraint.mk coefficientVector boundValue LfkRelation.isEqualTo =>
      let dotValue := lfkDotProduct env coefficientVector
      let firstRewrite : (lfkIntLt (pcqTermEval env (pcqConstTerm boundValue))
            (lfkIntAdd dotValue lreIntOne) = true)
          = (lfkIntLt boundValue (lfkIntAdd dotValue lreIntOne) = true) :=
        congrArg (fun probe => lfkIntLt probe (lfkIntAdd dotValue lreIntOne) = true)
          (pcqConstTermEval env boundValue)
      let secondRewrite : (lfkIntLt dotValue
            (pcqTermEval env (pcqConstTerm (lfkIntAdd boundValue lreIntOne))) = true)
          = (lfkIntLt dotValue (lfkIntAdd boundValue lreIntOne) = true) :=
        congrArg (fun probe => lfkIntLt dotValue probe = true)
          (pcqConstTermEval env (lfkIntAdd boundValue lreIntOne))
      Iff.intro
        (fun interpWitness =>
          pcqIntEqOfLeLe
            (pcqIntLeOfLtSucc (Eq.mp secondRewrite interpWitness.right))
            (pcqIntLeOfLtSucc (Eq.mp firstRewrite interpWitness.left)))
        (fun satisfiesWitness =>
          let bothLe := pcqIntLeLeOfEq satisfiesWitness
          And.intro
            (Eq.mpr firstRewrite (pcqIntLtSuccOfLe bothLe.right))
            (Eq.mpr secondRewrite (pcqIntLtSuccOfLe bothLe.left)))

/-- Translate a whole system as a conjunction (empty system reads true). -/
def pcqSystemFormula : List LfkConstraint → PcqFormula
  | List.nil => PcqFormula.flt (pcqConstTerm lfkIntZero) (pcqConstTerm lreIntOne)
  | constraintHead :: constraintTail =>
      PcqFormula.fconj (pcqConstraintFormula constraintHead)
        (pcqSystemFormula constraintTail)

/-- SYSTEM EQUIVALENCE: the translated system holds exactly when every row is
satisfied. -/
theorem pcqSystemFormulaSound (env : List LfkInt) : ∀ (system : List LfkConstraint),
    Iff (pcqInterp env (pcqSystemFormula system)) (lfkSatisfiesSystem env system = true)
  | List.nil =>
      Iff.intro (fun _interpWitness => rfl)
        (fun _satisfiesWitness => pcqQfTrueFormulaHolds env)
  | constraintHead :: constraintTail =>
      let headIff := pcqConstraintFormulaSound env constraintHead
      let tailIff := pcqSystemFormulaSound env constraintTail
      Iff.intro
        (fun interpWitness =>
          lfkBoolAndIntro (lfkSatisfiesConstraint env constraintHead)
            (lfkSatisfiesSystem env constraintTail)
            (headIff.mp interpWitness.left) (tailIff.mp interpWitness.right))
        (fun satisfiesWitness =>
          let destructured := lfkBoolAndDestruct (lfkSatisfiesConstraint env constraintHead)
            (lfkSatisfiesSystem env constraintTail) satisfiesWitness
          And.intro (headIff.mpr destructured.left) (tailIff.mpr destructured.right))

/-- Cons-only environment length. -/
def pcqEnvLen : List LfkInt → Nat
  | List.nil => 0
  | _entryHead :: entryTail => pcqEnvLen entryTail + 1

/-- Cons-only environment concatenation. -/
def pcqEnvConcat : List LfkInt → List LfkInt → List LfkInt
  | List.nil, secondList => secondList
  | entryHead :: entryTail, secondList => entryHead :: pcqEnvConcat entryTail secondList

/-- Concatenating the empty tail is the identity. -/
theorem pcqEnvConcatNil : ∀ (entries : List LfkInt),
    pcqEnvConcat entries List.nil = entries
  | List.nil => rfl
  | entryHead :: entryTail =>
      congrArg (fun probe => entryHead :: probe) (pcqEnvConcatNil entryTail)

/-- Truncate or zero-pad an environment to exactly `count` entries. -/
def pcqEnvTruncPad : Nat → List LfkInt → List LfkInt
  | Nat.zero, _env => List.nil
  | Nat.succ countPred, List.nil => lfkIntZero :: pcqEnvTruncPad countPred List.nil
  | Nat.succ countPred, entryHead :: entryTail =>
      entryHead :: pcqEnvTruncPad countPred entryTail

/-- The truncated-padded environment has exactly the requested length. -/
theorem pcqEnvTruncPadLen : ∀ (count : Nat) (env : List LfkInt),
    Nat.beq (pcqEnvLen (pcqEnvTruncPad count env)) count = true
  | Nat.zero, _env => rfl
  | Nat.succ countPred, List.nil => pcqEnvTruncPadLen countPred List.nil
  | Nat.succ countPred, _entryHead :: entryTail => pcqEnvTruncPadLen countPred entryTail

/-- Multiplying the literal zero pair on the left annihilates. -/
theorem pcqIntZeroMulLeft (value : LfkInt) : lfkIntMul lfkIntZero value = lfkIntZero :=
  lfkIntMkCongr (lfkNatBothZeroMulSum value.positivePart value.negativePart)
    (lfkNatBothZeroMulSum value.negativePart value.positivePart)

/-- Dotting against the empty environment is zero. -/
theorem pcqDotNilLeft : ∀ (coefficientVector : List LfkInt),
    lfkDotProduct List.nil coefficientVector = lfkIntZero
  | List.nil => rfl
  | _coefficientHead :: _coefficientTail => rfl

/-- THE PREFIX LEMMA: when the coefficient vector fits within the truncation
count, the truncated-padded environment dots identically (padded zeros
contribute nothing; truncation beyond the vector is invisible). -/
theorem pcqDotTruncPad : ∀ (count : Nat) (env coefficientVector : List LfkInt),
    Nat.ble (pcqEnvLen coefficientVector) count = true →
    lfkDotProduct (pcqEnvTruncPad count env) coefficientVector
      = lfkDotProduct env coefficientVector
  | count, env, List.nil, _fitWitness =>
      (lfkDotProductNilRight (pcqEnvTruncPad count env)).trans
        (lfkDotProductNilRight env).symm
  | Nat.zero, _env, _coefficientHead :: _coefficientTail, fitWitness =>
      Bool.noConfusion fitWitness
  | Nat.succ countPred, List.nil, coefficientHead :: coefficientTail, fitWitness =>
      ((congrArg
          (fun probe => lfkIntAdd probe
            (lfkDotProduct (pcqEnvTruncPad countPred List.nil) coefficientTail))
          (pcqIntZeroMulLeft coefficientHead)).trans
        ((lfkIntZeroAdd
            (lfkDotProduct (pcqEnvTruncPad countPred List.nil) coefficientTail)).trans
          ((pcqDotTruncPad countPred List.nil coefficientTail fitWitness).trans
            (pcqDotNilLeft coefficientTail))))
  | Nat.succ countPred, entryHead :: entryTail, coefficientHead :: coefficientTail,
      fitWitness =>
      congrArg (fun probe => lfkIntAdd (lfkIntMul entryHead coefficientHead) probe)
        (pcqDotTruncPad countPred entryTail coefficientTail fitWitness)

/-- Every row's coefficient vector fits within the count. -/
def pcqRowsFitWithin (count : Nat) : List LfkConstraint → Bool
  | List.nil => true
  | constraintHead :: constraintTail =>
      Nat.ble (pcqEnvLen constraintHead.coefficients) count
        && pcqRowsFitWithin count constraintTail

/-- The total coefficient length of a system — the existential closure count. -/
def pcqSystemVarCount : List LfkConstraint → Nat
  | List.nil => 0
  | constraintHead :: constraintTail =>
      pcqEnvLen constraintHead.coefficients + pcqSystemVarCount constraintTail

/-- Fitting is monotone in the count. -/
theorem pcqRowsFitMono : ∀ (system : List LfkConstraint) (smallCount bigCount : Nat),
    Nat.le smallCount bigCount → pcqRowsFitWithin smallCount system = true →
    pcqRowsFitWithin bigCount system = true
  | List.nil, _smallCount, _bigCount, _boundWitness, _fitWitness => rfl
  | constraintHead :: constraintTail, smallCount, bigCount, boundWitness, fitWitness =>
      let destructured := lfkBoolAndDestruct
        (Nat.ble (pcqEnvLen constraintHead.coefficients) smallCount)
        (pcqRowsFitWithin smallCount constraintTail) fitWitness
      lfkBoolAndIntro (Nat.ble (pcqEnvLen constraintHead.coefficients) bigCount)
        (pcqRowsFitWithin bigCount constraintTail)
        (lfkNatBleOfLe (pcqEnvLen constraintHead.coefficients) bigCount
          (Nat.le_trans
            (lfkNatLeOfBle (pcqEnvLen constraintHead.coefficients) smallCount
              destructured.left)
            boundWitness))
        (pcqRowsFitMono constraintTail smallCount bigCount boundWitness
          destructured.right)

/-- Every system fits within its own total coefficient length. -/
theorem pcqRowsFitVarCount : ∀ (system : List LfkConstraint),
    pcqRowsFitWithin (pcqSystemVarCount system) system = true
  | List.nil => rfl
  | constraintHead :: constraintTail =>
      lfkBoolAndIntro
        (Nat.ble (pcqEnvLen constraintHead.coefficients)
          (pcqEnvLen constraintHead.coefficients + pcqSystemVarCount constraintTail))
        (pcqRowsFitWithin
          (pcqEnvLen constraintHead.coefficients + pcqSystemVarCount constraintTail)
          constraintTail)
        (lfkNatBleOfLe (pcqEnvLen constraintHead.coefficients)
          (pcqEnvLen constraintHead.coefficients + pcqSystemVarCount constraintTail)
          (lfkNatLeCongr rfl
            (Nat.add_comm (pcqEnvLen constraintHead.coefficients)
              (pcqSystemVarCount constraintTail))
            (lreNatLeAddLeft (pcqSystemVarCount constraintTail)
              (pcqEnvLen constraintHead.coefficients))))
        (pcqRowsFitMono constraintTail (pcqSystemVarCount constraintTail)
          (pcqEnvLen constraintHead.coefficients + pcqSystemVarCount constraintTail)
          (lreNatLeAddLeft (pcqEnvLen constraintHead.coefficients)
            (pcqSystemVarCount constraintTail))
          (pcqRowsFitVarCount constraintTail))

/-- Row satisfaction sees only the truncated-padded prefix. -/
theorem pcqSatisfiesConstraintTruncPad (count : Nat) (env : List LfkInt) :
    ∀ (constraint : LfkConstraint),
    Nat.ble (pcqEnvLen constraint.coefficients) count = true →
    lfkSatisfiesConstraint (pcqEnvTruncPad count env) constraint
      = lfkSatisfiesConstraint env constraint
  | LfkConstraint.mk coefficientVector boundValue LfkRelation.isGreaterOrEqual,
      fitWitness =>
      congrArg (fun probe => lfkIntLe boundValue probe)
        (pcqDotTruncPad count env coefficientVector fitWitness)
  | LfkConstraint.mk coefficientVector boundValue LfkRelation.isStrictlyGreater,
      fitWitness =>
      congrArg (fun probe => lfkIntLt boundValue probe)
        (pcqDotTruncPad count env coefficientVector fitWitness)
  | LfkConstraint.mk coefficientVector boundValue LfkRelation.isEqualTo, fitWitness =>
      congrArg (fun probe => lfkIntEq probe boundValue)
        (pcqDotTruncPad count env coefficientVector fitWitness)

/-- System satisfaction sees only the truncated-padded prefix. -/
theorem pcqSatisfiesSystemTruncPad (count : Nat) (env : List LfkInt) :
    ∀ (system : List LfkConstraint), pcqRowsFitWithin count system = true →
    lfkSatisfiesSystem (pcqEnvTruncPad count env) system
      = lfkSatisfiesSystem env system
  | List.nil, _fitWitness => rfl
  | constraintHead :: constraintTail, fitWitness =>
      let destructured := lfkBoolAndDestruct
        (Nat.ble (pcqEnvLen constraintHead.coefficients) count)
        (pcqRowsFitWithin count constraintTail) fitWitness
      (congrArg
          (fun probe => probe
            && lfkSatisfiesSystem (pcqEnvTruncPad count env) constraintTail)
          (pcqSatisfiesConstraintTruncPad count env constraintHead
            destructured.left)).trans
        (congrArg (fun probe => lfkSatisfiesConstraint env constraintHead && probe)
          (pcqSatisfiesSystemTruncPad count env constraintTail destructured.right))

/-- Close a formula under `count` existentials (innermost binder first). -/
def pcqFexN : Nat → PcqFormula → PcqFormula
  | Nat.zero, formula => formula
  | Nat.succ countPred, formula => pcqFexN countPred (PcqFormula.fexists formula)

/-- Introduce the existential closure from an explicit witness prefix. -/
theorem pcqFexNIntro : ∀ (count : Nat) (witnessList tailEnv : List LfkInt)
    (formula : PcqFormula),
    Nat.beq (pcqEnvLen witnessList) count = true →
    pcqInterp (pcqEnvConcat witnessList tailEnv) formula →
    pcqInterp tailEnv (pcqFexN count formula)
  | Nat.zero, List.nil, _tailEnv, _formula, _lengthWitness, interpWitness => interpWitness
  | Nat.zero, _entryHead :: _entryTail, _tailEnv, _formula, lengthWitness,
      _interpWitness => Bool.noConfusion lengthWitness
  | Nat.succ _countPred, List.nil, _tailEnv, _formula, lengthWitness, _interpWitness =>
      Bool.noConfusion lengthWitness
  | Nat.succ countPred, entryHead :: entryTail, tailEnv, formula, lengthWitness,
      interpWitness =>
      pcqFexNIntro countPred entryTail tailEnv (PcqFormula.fexists formula) lengthWitness
        (Exists.intro entryHead interpWitness)

/-- Eliminate the existential closure into an explicit witness prefix. -/
theorem pcqFexNElim : ∀ (count : Nat) (tailEnv : List LfkInt) (formula : PcqFormula),
    pcqInterp tailEnv (pcqFexN count formula) →
    ∃ (witnessList : List LfkInt), pcqInterp (pcqEnvConcat witnessList tailEnv) formula
  | Nat.zero, _tailEnv, _formula, interpWitness => Exists.intro List.nil interpWitness
  | Nat.succ countPred, tailEnv, formula, interpWitness =>
      match pcqFexNElim countPred tailEnv (PcqFormula.fexists formula) interpWitness with
      | Exists.intro witnessList innerWitness =>
          match innerWitness with
          | Exists.intro headValue bodyWitness =>
              Exists.intro (headValue :: witnessList) bodyWitness

/-- THE LANE WALL, INHABITED VERBATIM: every integer linear-constraint system
either has a satisfying environment or refutes them all — decided by Cooper
elimination on the translated, existentially closed formula.  This is the
statement owned false by `fxDissatArith_hasPresburgerDecision` in
`LinearFarkasCertificate.lean`; the flag itself lives in that frozen file, so
the DECIDED marker here is `pcqHasPresburgerDecision`. -/
theorem pcqPresburgerDecisionHolds : lfkPresburgerDecisionStatement :=
  fun system =>
    match decideCase : pcqDecide (pcqFexN (pcqSystemVarCount system)
      (pcqSystemFormula system)) with
    | true =>
        (match pcqFexNElim (pcqSystemVarCount system) List.nil (pcqSystemFormula system)
          (pcqDecideTrueSound
            (pcqFexN (pcqSystemVarCount system) (pcqSystemFormula system)) decideCase) with
        | Exists.intro witnessList interpWitness =>
            Or.inl
              (Exists.intro (pcqEnvConcat witnessList List.nil)
                ((pcqSystemFormulaSound (pcqEnvConcat witnessList List.nil) system).mp
                  interpWitness)))
    | false =>
        Or.inr
          (fun env satisfiesWitness =>
            pcqDecideFalseComplete
              (pcqFexN (pcqSystemVarCount system) (pcqSystemFormula system)) decideCase
              (pcqFexNIntro (pcqSystemVarCount system)
                (pcqEnvTruncPad (pcqSystemVarCount system) env) List.nil
                (pcqSystemFormula system)
                (pcqEnvTruncPadLen (pcqSystemVarCount system) env)
                ((pcqSystemFormulaSound
                    (pcqEnvConcat (pcqEnvTruncPad (pcqSystemVarCount system) env) List.nil)
                    system).mpr
                  (((congrArg (fun probe => lfkSatisfiesSystem probe system)
                      (pcqEnvConcatNil
                        (pcqEnvTruncPad (pcqSystemVarCount system) env))).trans
                    (pcqSatisfiesSystemTruncPad (pcqSystemVarCount system) env system
                      (pcqRowsFitVarCount system))).trans
                    satisfiesWitness))))

/-- CONTENT MARKER (DECIDED): the full Cooper pipeline — syntax/semantics,
two-sided ground evaluation, NNF, product-scale unitarization, the two-sided
elimination theorem, the inside-out eliminator, the closed-formula decision,
and the verbatim inhabitation of `lfkPresburgerDecisionStatement`
(`pcqPresburgerDecisionHolds`) — is fully proven, zero-axiom.  The stale
owner flag `fxDissatArith_hasPresburgerDecision := false` lives in the frozen
`LinearFarkasCertificate.lean` and is SUPERSEDED by this marker. -/
def pcqHasPresburgerDecision : Bool := true

end FX1Poly.ComputerAlgebra
