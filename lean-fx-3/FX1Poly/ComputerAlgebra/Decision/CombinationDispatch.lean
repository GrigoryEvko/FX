import FX1Poly.ComputerAlgebra.Decision.GroundCongruenceClosure
import FX1Poly.ComputerAlgebra.Decision.LinearFarkasCertificate
import FX1Poly.ComputerAlgebra.Decision.FourierMotzkinCompleteness

/-! # Certificate-level Nelson–Oppen combination of the ground-congruence and Farkas engines

The sound certificate-combination core for the two decision engines, following the
Besson–Cornilleau–Pichardie proof-system reading of Nelson–Oppen (theory-specific certificates plus
explicit shared-variable equalities, each independently checkable) and the SMTCoq/Alethe convention
that theory combination lives in the certificate rather than in a verified combination algorithm.

  * The purified problem (`NocProblem`) — an E-part (ground equations over `GccTerm`), an A-part
    (`LfkConstraint` rows), and a shared interface mapping arithmetic variable indices to ground
    terms (`List (Nat × GccTerm)`). Purification itself — walking a mixed term bottom-up, replacing
    alien subterms by fresh shared variables — is syntactic preprocessing outside kernel scope; its
    equisatisfiability is stated as `nocPurificationStatement` over a faithful mixed AST
    (`NocMixedTerm`: uninterpreted application + linear arithmetic in one grammar).
  * Joint models (`nocIsJointModel`) — an integer environment for the A-part plus the
    functional-consistency bridge (`nocFunctionalConsistencyHolds`): shared variables whose terms
    are `GccDeriv`-provably equal carry cross-sum-equal values. The bridge is not an ad-hoc
    assumption: `nocModelAgreementGivesConsistency` derives it from a genuine two-theory model
    (`NocMixedModel` — a symbol valuation plus a congruent binary application operator) by induction
    over `GccDeriv` (`nocDerivPreservedByModel`).
  * The combination certificate (`NocCertificate`) — derived shared-variable equalities plus Farkas
    multipliers. The checker (`nocCheckCombination`) gcc-checks every derived equality (`gccDecide`
    on the looked-up terms) and runs the sibling Farkas checker on the A-part augmented with one
    `x_i - x_j = 0` row per derived equality (difference vectors built as padding sums of unit
    vectors — no subtraction, no min/max). An empty derived list degenerates to a pure A-side
    refutation; ground congruence alone never refutes, since the E-language here has no disequations.
  * Soundness (`nocCombinationSound`) — an accepted certificate refutes every joint model: each
    checked equality yields `GccDeriv` by the gcc engine's decision soundness, the bridge turns it
    into satisfaction of the augmented row (`nocDerivedRowSatisfiedOfEnvEq`), and
    `lfkRefutationSoundUnconditional` kills the environment. `nocCombinationSoundForMixedSemantics`
    restates the headline against the two-theory model semantics.
  * The end-to-end finder (`nocFindRefutation`) — one round of E→A equality propagation (enumerate
    shared pairs, keep exactly those the checker accepts) followed by the sibling Fourier–Motzkin
    finder on the augmented system; `nocFinderSound` proves every found certificate is
    checker-accepted (composing `lfmFoundContradictionCertifies`), and `nocFinderRefutesJointModels`
    closes the loop through soundness.

Two capabilities are walled. `nocPurificationStatement` asserts a purifier from the mixed AST to
`NocProblem` preserving and reflecting satisfiability; the missing legs are fresh-variable
allocation with hash-consing (one variable per distinct alien subterm, which is exactly functional
consistency), the definitional-extension argument (forward direction), and a term-model construction
extending a joint environment to a congruent `applyValue` (Nelson–Oppen's total model extension) for
the reflection direction (`fxDissatCombine_hasPurificationEquivalence`). As a bare existential the
statement carries no constructive force; the missing artifact is the purifier itself.
`nocCombinationCompletenessStatement` — every jointly-unsatisfiable problem has an accepted
certificate — is false over the integers as stated: the A-side alone inherits the Farkas gap
(`2x = 1` is integer-unsat, rationally feasible, certificate-free). Over the rationals it needs
(i) equality-interpolation completeness of the E-engine (single equalities suffice only for convex
theories, and ℤ-LIA is not convex: `1 <= x <= 2` entails `x = 1 ∨ x = 2` with neither disjunct
entailed, so the non-convex case needs case-split trees over equality disjunctions), (ii) Farkas
completeness over the rationals (the sibling's owner-false Fourier–Motzkin backward direction), and
(iii) model amalgamation (stable infiniteness / cardinality agreement, a semantic condition no
certificate checker inspects) (`fxDissatCombine_hasCombinationCompleteness`).

Init only; imports only the two engine files and the Fourier–Motzkin finder. Structural recursion
throughout; no `WellFounded.fix`, no `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `funext`, `omega`, no `decide` on `Prop`, no wildcard constructor arms. Nat facts
are restricted to the probed-clean kit used by the engines (`Nat.add_comm`, `Nat.zero_add`,
`Nat.mul_one`, `Nat.zero_mul`, `Nat.beq`) plus the sibling helpers (`lfkNatAddSwapMiddle`,
`lfkNatAddLeftCancel`, beq/ble reflection). All list helpers are bespoke, monomorphic, cons-only.
Per-declaration gate in the twin. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace FX1Poly.ComputerAlgebra

/-! ## Cross-sum equality kit on `LfkInt` (symmetry, transitivity, unit laws)

The sibling supplies reflexivity (`lfkIntEqRefl`); the combination additionally needs the
equivalence-relation half and the two unit-multiplication laws that make dot products against unit
vectors read off environment values. -/

/-- Cross-sum equality is symmetric. -/
theorem nocIntEqSymm {leftValue rightValue : LfkInt}
    (eqWitness : lfkIntEq leftValue rightValue = true) :
    lfkIntEq rightValue leftValue = true :=
  lfkNatBeqOfEq (rightValue.positivePart + leftValue.negativePart)
    (leftValue.positivePart + rightValue.negativePart)
    (lfkNatEqOfBeq (leftValue.positivePart + rightValue.negativePart)
      (rightValue.positivePart + leftValue.negativePart) eqWitness).symm

/-- Cross-sum transitivity at the Nat level: two cross equalities compose after
cancelling the middle value's `positivePart + negativePart` (the sibling's
left-cancellation, no subtraction). -/
theorem nocNatCrossSumTrans (firstPositive firstNegative secondPositive secondNegative
    thirdPositive thirdNegative : Nat)
    (leftCross : firstPositive + secondNegative = secondPositive + firstNegative)
    (rightCross : secondPositive + thirdNegative = thirdPositive + secondNegative) :
    firstPositive + thirdNegative = thirdPositive + firstNegative :=
  lfkNatAddLeftCancel (secondPositive + secondNegative)
    (firstPositive + thirdNegative) (thirdPositive + firstNegative)
    ((lfkNatAddSwapMiddle secondPositive secondNegative firstPositive thirdNegative).trans
      (((congrArg (fun probe => probe + (secondNegative + thirdNegative))
            (Nat.add_comm secondPositive firstPositive)).trans
          ((lfkNatAddSwapMiddle firstPositive secondPositive secondNegative
              thirdNegative).trans
            ((lfkNatAddCongr leftCross rightCross).trans
              ((lfkNatAddSwapMiddle secondPositive firstNegative thirdPositive
                  secondNegative).trans
                (congrArg (fun probe => (secondPositive + thirdPositive) + probe)
                  (Nat.add_comm firstNegative secondNegative)))))).trans
        (lfkNatAddSwapMiddle secondPositive secondNegative thirdPositive
          firstNegative).symm))

/-- Cross-sum equality is transitive. -/
theorem nocIntEqTrans {firstValue secondValue thirdValue : LfkInt}
    (leftEqWitness : lfkIntEq firstValue secondValue = true)
    (rightEqWitness : lfkIntEq secondValue thirdValue = true) :
    lfkIntEq firstValue thirdValue = true :=
  lfkNatBeqOfEq (firstValue.positivePart + thirdValue.negativePart)
    (thirdValue.positivePart + firstValue.negativePart)
    (nocNatCrossSumTrans firstValue.positivePart firstValue.negativePart
      secondValue.positivePart secondValue.negativePart
      thirdValue.positivePart thirdValue.negativePart
      (lfkNatEqOfBeq (firstValue.positivePart + secondValue.negativePart)
        (secondValue.positivePart + firstValue.negativePart) leftEqWitness)
      (lfkNatEqOfBeq (secondValue.positivePart + thirdValue.negativePart)
        (thirdValue.positivePart + secondValue.negativePart) rightEqWitness))

/-- Zero annihilates on the left of the sign-aware multiplication. -/
theorem nocIntZeroMul (weight : LfkInt) : lfkIntMul lfkIntZero weight = lfkIntZero :=
  lfkIntMkCongr
    (lfkNatAddCongr (Nat.zero_mul weight.positivePart) (Nat.zero_mul weight.negativePart))
    (lfkNatAddCongr (Nat.zero_mul weight.negativePart) (Nat.zero_mul weight.positivePart))

/-- The coefficient `+1` (as an unnormalized pair). -/
def nocPositiveUnit : LfkInt := LfkInt.mk 1 0

/-- The coefficient `-1` (as an unnormalized pair). -/
def nocNegativeUnit : LfkInt := LfkInt.mk 0 1

/-- Multiplying by the coefficient `+1` on the right is the identity. -/
theorem nocIntMulPositiveUnit (value : LfkInt) : lfkIntMul value nocPositiveUnit = value :=
  lfkIntMkCongr (Nat.mul_one value.positivePart)
    ((Nat.zero_add (value.negativePart * 1)).trans (Nat.mul_one value.negativePart))

/-- Multiplying by the coefficient `-1` on the right is negation (component swap). -/
theorem nocIntMulNegativeUnit (value : LfkInt) :
    lfkIntMul value nocNegativeUnit = lfkIntNegate value :=
  lfkIntMkCongr
    ((Nat.zero_add (value.negativePart * 1)).trans (Nat.mul_one value.negativePart))
    (Nat.mul_one value.positivePart)

/-- A value minus a cross-sum-equal value is cross-sum zero — the satisfaction core of
every derived-equality row. -/
theorem nocIntAddNegateEqZero {leftValue rightValue : LfkInt}
    (eqWitness : lfkIntEq leftValue rightValue = true) :
    lfkIntEq (lfkIntAdd leftValue (lfkIntNegate rightValue)) lfkIntZero = true :=
  lfkNatBeqOfEq
    ((leftValue.positivePart + rightValue.negativePart) + 0)
    (0 + (leftValue.negativePart + rightValue.positivePart))
    ((lfkNatEqOfBeq (leftValue.positivePart + rightValue.negativePart)
        (rightValue.positivePart + leftValue.negativePart) eqWitness).trans
      ((Nat.add_comm rightValue.positivePart leftValue.negativePart).trans
        (Nat.zero_add (leftValue.negativePart + rightValue.positivePart)).symm))

/-! ## The purified problem and the shared interface -/

/-- A purified two-theory problem: ground equations for the congruence engine, linear
rows for the Farkas engine, and the shared interface — arithmetic variable `i` denotes
the ground term paired with `i`.  Purification (alien-subterm extraction producing this
shape from a mixed conjunction) is out of kernel scope: see `nocPurificationStatement`. -/
structure NocProblem where
  equationalPart : List (GccTerm × GccTerm)
  arithmeticPart : List LfkConstraint
  sharedInterface : List (Nat × GccTerm)

/-- First-match lookup of a shared variable's denoted term. -/
def nocSharedLookup : List (Nat × GccTerm) → Nat → Option GccTerm
  | List.nil, _queryIndex => Option.none
  | interfaceEntry :: remainingEntries, queryIndex =>
      cond (Nat.beq queryIndex interfaceEntry.fst) (Option.some interfaceEntry.snd)
        (nocSharedLookup remainingEntries queryIndex)

/-- The value of variable `variableIndex` in a dense environment; absent entries read as
zero, matching the sibling's truncating dot-product semantics. -/
def nocEnvValueAt : List LfkInt → Nat → LfkInt
  | List.nil, _variableIndex => lfkIntZero
  | envHead :: _envTail, 0 => envHead
  | _envHead :: envTail, Nat.succ previousIndex => nocEnvValueAt envTail previousIndex

/-- The dense unit vector: `position` zeros followed by the given weight. -/
def nocUnitCoefficientVector : Nat → LfkInt → List LfkInt
  | 0, weight => [weight]
  | Nat.succ previousPosition, weight =>
      lfkIntZero :: nocUnitCoefficientVector previousPosition weight

/-- The difference vector `x_first - x_second` as a PADDING SUM of two unit vectors —
no subtraction, no ordering of the two indices needed. -/
def nocDifferenceVector (firstIndex secondIndex : Nat) : List LfkInt :=
  lfkAddCoefficientVectors (nocUnitCoefficientVector firstIndex nocPositiveUnit)
    (nocUnitCoefficientVector secondIndex nocNegativeUnit)

/-- The derived-equality row `x_first - x_second = 0`.  Stated as an EQUALITY row: the
sibling checker row-splits it internally, so one derived equality consumes two
consecutive Farkas-multiplier slots of the expanded system. -/
def nocDerivedEqualityConstraint (firstIndex secondIndex : Nat) : LfkConstraint :=
  LfkConstraint.mk (nocDifferenceVector firstIndex secondIndex) lfkIntZero
    LfkRelation.isEqualTo

/-! ## Joint-model semantics and its two-theory grounding -/

/-- THE FUNCTIONAL-CONSISTENCY BRIDGE: shared variables whose denoted terms are
`GccDeriv`-provably equal carry cross-sum-equal environment values.  This is the exact
semantic content of sharing a variable between the two theories; it is DERIVED from any
genuine two-theory model by `nocModelAgreementGivesConsistency`. -/
def nocFunctionalConsistencyHolds (problem : NocProblem) (env : List LfkInt) : Prop :=
  ∀ (leftIndex rightIndex : Nat) (leftTerm rightTerm : GccTerm),
    nocSharedLookup problem.sharedInterface leftIndex = Option.some leftTerm →
    nocSharedLookup problem.sharedInterface rightIndex = Option.some rightTerm →
    GccDeriv problem.equationalPart leftTerm rightTerm →
    lfkIntEq (nocEnvValueAt env leftIndex) (nocEnvValueAt env rightIndex) = true

/-- A joint model: the environment satisfies the A-part and respects the bridge.  (The
E-part is a pure equation list — no disequations — so it is never refutable alone; joint
unsatisfiability always manifests through the augmented A-side.) -/
def nocIsJointModel (problem : NocProblem) (env : List LfkInt) : Prop :=
  And (lfkSatisfiesSystem env problem.arithmeticPart = true)
    (nocFunctionalConsistencyHolds problem env)

/-- A two-theory model: a valuation of uninterpreted symbols plus an interpretation of
the (curried binary) application operator over the shared integer carrier. -/
structure NocMixedModel where
  symbolValue : Nat → LfkInt
  applyValue : LfkInt → LfkInt → LfkInt

/-- Evaluate a ground congruence term in a two-theory model. -/
def nocGroundTermValue (model : NocMixedModel) : GccTerm → LfkInt
  | GccTerm.symbol name => model.symbolValue name
  | GccTerm.apply function argument =>
      model.applyValue (nocGroundTermValue model function)
        (nocGroundTermValue model argument)

/-- The model's application operator is a genuine function of INTEGER VALUES: it
respects cross-sum equality in both arguments (the unnormalized-pair carrier makes this
a side condition rather than a freebie). -/
def nocModelRespectsIntEq (model : NocMixedModel) : Prop :=
  ∀ (leftFunction rightFunction leftArgument rightArgument : LfkInt),
    lfkIntEq leftFunction rightFunction = true →
    lfkIntEq leftArgument rightArgument = true →
    lfkIntEq (model.applyValue leftFunction leftArgument)
      (model.applyValue rightFunction rightArgument) = true

/-- The model satisfies every listed ground equation. -/
def nocModelSatisfiesEquations (model : NocMixedModel)
    (equations : List (GccTerm × GccTerm)) : Prop :=
  ∀ (equationIndex : Nat) (leftTerm rightTerm : GccTerm),
    gccListGetPair equations equationIndex = Option.some (leftTerm, rightTerm) →
    lfkIntEq (nocGroundTermValue model leftTerm) (nocGroundTermValue model rightTerm) = true

/-- E-SOUNDNESS IN THE TWO-THEORY MODEL: every `GccDeriv`-derivable equation holds under
evaluation (induction over the derivation; congruence is exactly the respect
condition). -/
theorem nocDerivPreservedByModel (model : NocMixedModel)
    (respectWitness : nocModelRespectsIntEq model)
    (equations : List (GccTerm × GccTerm))
    (equationsWitness : nocModelSatisfiesEquations model equations) :
    ∀ (sourceTerm targetTerm : GccTerm), GccDeriv equations sourceTerm targetTerm →
      lfkIntEq (nocGroundTermValue model sourceTerm)
        (nocGroundTermValue model targetTerm) = true := by
  intro sourceTerm targetTerm derivation
  induction derivation with
  | byEquation equationIndex leftTerm rightTerm lookupWitness =>
      exact equationsWitness equationIndex leftTerm rightTerm lookupWitness
  | byRefl term => exact lfkIntEqRefl (nocGroundTermValue model term)
  | bySymm leftTerm rightTerm _forwardDeriv forwardValueEq =>
      exact nocIntEqSymm forwardValueEq
  | byTrans leftTerm middleTerm rightTerm _leftDeriv _rightDeriv leftValueEq rightValueEq =>
      exact nocIntEqTrans leftValueEq rightValueEq
  | byCongruence leftFunction rightFunction leftArgument rightArgument _functionDeriv
      _argumentDeriv functionValueEq argumentValueEq =>
      exact respectWitness (nocGroundTermValue model leftFunction)
        (nocGroundTermValue model rightFunction) (nocGroundTermValue model leftArgument)
        (nocGroundTermValue model rightArgument) functionValueEq argumentValueEq

/-- The environment agrees with the model across the shared interface: each shared
variable's value is the value of its denoted term. -/
def nocEnvAgreesWithModel (model : NocMixedModel) (sharedInterface : List (Nat × GccTerm))
    (env : List LfkInt) : Prop :=
  ∀ (sharedIndex : Nat) (denotedTerm : GccTerm),
    nocSharedLookup sharedInterface sharedIndex = Option.some denotedTerm →
    lfkIntEq (nocEnvValueAt env sharedIndex) (nocGroundTermValue model denotedTerm) = true

/-- THE BRIDGE IS DERIVED, NOT ASSUMED: any environment agreeing with a respecting
two-theory model of the E-part satisfies functional consistency. -/
theorem nocModelAgreementGivesConsistency (problem : NocProblem) (model : NocMixedModel)
    (env : List LfkInt) (respectWitness : nocModelRespectsIntEq model)
    (equationsWitness : nocModelSatisfiesEquations model problem.equationalPart)
    (agreementWitness : nocEnvAgreesWithModel model problem.sharedInterface env) :
    nocFunctionalConsistencyHolds problem env :=
  fun leftIndex rightIndex leftTerm rightTerm leftLookup rightLookup derivation =>
    nocIntEqTrans (agreementWitness leftIndex leftTerm leftLookup)
      (nocIntEqTrans
        (nocDerivPreservedByModel model respectWitness problem.equationalPart
          equationsWitness leftTerm rightTerm derivation)
        (nocIntEqSymm (agreementWitness rightIndex rightTerm rightLookup)))

/-! ## The combination certificate and the checker -/

/-- The combination certificate: derived shared-variable equalities (each claiming its
two indices denote gcc-provably-equal terms) plus Farkas multipliers for the augmented
A-side, aligned with the sibling's EXPANDED row list (each derived equality row consumes
two consecutive slots). -/
structure NocCertificate where
  derivedEqualities : List (Nat × Nat)
  farkasMultipliers : List Nat

/-- Decide a claimed equality once both lookups are on the table: both indices must
resolve and the congruence engine must prove the terms equal. -/
def nocDecideOptionPairEquality (equations : List (GccTerm × GccTerm)) :
    Option GccTerm → Option GccTerm → Bool
  | Option.some leftTerm, Option.some rightTerm => gccDecide equations leftTerm rightTerm
  | Option.some _leftTerm, Option.none => false
  | Option.none, Option.some _rightTerm => false
  | Option.none, Option.none => false

/-- Check one derived equality against the shared interface. -/
def nocCheckDerivedEquality (equations : List (GccTerm × GccTerm))
    (sharedInterface : List (Nat × GccTerm)) (indexPair : Nat × Nat) : Bool :=
  nocDecideOptionPairEquality equations
    (nocSharedLookup sharedInterface indexPair.fst)
    (nocSharedLookup sharedInterface indexPair.snd)

/-- Check every derived equality. -/
def nocCheckAllDerivedEqualities (equations : List (GccTerm × GccTerm))
    (sharedInterface : List (Nat × GccTerm)) : List (Nat × Nat) → Bool
  | List.nil => true
  | indexPair :: remainingPairs =>
      nocCheckDerivedEquality equations sharedInterface indexPair
        && nocCheckAllDerivedEqualities equations sharedInterface remainingPairs

/-- Augment the A-part with one equality row per derived pair (cons-only). -/
def nocAugmentSystem : List (Nat × Nat) → List LfkConstraint → List LfkConstraint
  | List.nil, arithmeticPart => arithmeticPart
  | indexPair :: remainingPairs, arithmeticPart =>
      nocDerivedEqualityConstraint indexPair.fst indexPair.snd
        :: nocAugmentSystem remainingPairs arithmeticPart

/-- THE COMBINATION CHECKER: every derived equality gcc-checks AND the Farkas
certificate refutes the augmented A-side.  O(pairs · congruence) + O(rows · variables),
no search. -/
def nocCheckCombination (problem : NocProblem) (certificate : NocCertificate) : Bool :=
  nocCheckAllDerivedEqualities problem.equationalPart problem.sharedInterface
      certificate.derivedEqualities
    && lfkCheckRefutation certificate.farkasMultipliers
      (nocAugmentSystem certificate.derivedEqualities problem.arithmeticPart)

/-! ## Soundness of the combination -/

/-- Dotting a unit vector reads off the environment value (scaled by the weight);
truncation and zero-extension agree beyond the environment's length. -/
theorem nocDotUnitVector : ∀ (env : List LfkInt) (position : Nat) (weight : LfkInt),
    lfkDotProduct env (nocUnitCoefficientVector position weight)
      = lfkIntMul (nocEnvValueAt env position) weight
  | List.nil, 0, weight => (nocIntZeroMul weight).symm
  | List.nil, Nat.succ _previousPosition, weight => (nocIntZeroMul weight).symm
  | envHead :: envTail, 0, weight =>
      (congrArg (fun probe => lfkIntAdd (lfkIntMul envHead weight) probe)
          (lfkDotProductNilRight envTail)).trans
        (lfkIntAddZero (lfkIntMul envHead weight))
  | _envHead :: envTail, Nat.succ previousPosition, weight =>
      (lfkIntZeroAdd
          (lfkDotProduct envTail (nocUnitCoefficientVector previousPosition weight))).trans
        (nocDotUnitVector envTail previousPosition weight)

/-- Dotting a difference vector yields `value(first) - value(second)`. -/
theorem nocDotDifferenceVector (env : List LfkInt) (firstIndex secondIndex : Nat) :
    lfkDotProduct env (nocDifferenceVector firstIndex secondIndex)
      = lfkIntAdd (nocEnvValueAt env firstIndex)
          (lfkIntNegate (nocEnvValueAt env secondIndex)) :=
  (lfkDotProductAddVectors env (nocUnitCoefficientVector firstIndex nocPositiveUnit)
      (nocUnitCoefficientVector secondIndex nocNegativeUnit)).trans
    (lfkIntAddCongr
      ((nocDotUnitVector env firstIndex nocPositiveUnit).trans
        (nocIntMulPositiveUnit (nocEnvValueAt env firstIndex)))
      ((nocDotUnitVector env secondIndex nocNegativeUnit).trans
        (nocIntMulNegativeUnit (nocEnvValueAt env secondIndex))))

/-- Cross-sum-equal shared values satisfy the derived-equality row. -/
theorem nocDerivedRowSatisfiedOfEnvEq (env : List LfkInt) (firstIndex secondIndex : Nat)
    (envEqWitness : lfkIntEq (nocEnvValueAt env firstIndex)
      (nocEnvValueAt env secondIndex) = true) :
    lfkSatisfiesConstraint env (nocDerivedEqualityConstraint firstIndex secondIndex)
      = true :=
  (congrArg (fun probe => lfkIntEq probe lfkIntZero)
      (nocDotDifferenceVector env firstIndex secondIndex)).trans
    (nocIntAddNegateEqZero envEqWitness)

/-- A checked derived equality forces cross-sum-equal environment values in every
bridge-respecting environment: invert the lookups, extract the `gccDecide` verdict,
convert it to `GccDeriv` by the engine's decision soundness, and fire the bridge. -/
theorem nocCheckedEqualityGivesEnvEq (problem : NocProblem) (env : List LfkInt)
    (consistencyWitness : nocFunctionalConsistencyHolds problem env)
    (indexPair : Nat × Nat)
    (checkWitness : nocCheckDerivedEquality problem.equationalPart
      problem.sharedInterface indexPair = true) :
    lfkIntEq (nocEnvValueAt env indexPair.fst) (nocEnvValueAt env indexPair.snd)
      = true := by
  have decisionWitness : nocDecideOptionPairEquality problem.equationalPart
      (nocSharedLookup problem.sharedInterface indexPair.fst)
      (nocSharedLookup problem.sharedInterface indexPair.snd) = true := checkWitness
  cases hLeftLookup : nocSharedLookup problem.sharedInterface indexPair.fst with
  | none =>
      rw [hLeftLookup] at decisionWitness
      cases hRightLookup : nocSharedLookup problem.sharedInterface indexPair.snd with
      | none =>
          rw [hRightLookup] at decisionWitness
          exact Bool.noConfusion decisionWitness
      | some rightTerm =>
          rw [hRightLookup] at decisionWitness
          exact Bool.noConfusion decisionWitness
  | some leftTerm =>
      rw [hLeftLookup] at decisionWitness
      cases hRightLookup : nocSharedLookup problem.sharedInterface indexPair.snd with
      | none =>
          rw [hRightLookup] at decisionWitness
          exact Bool.noConfusion decisionWitness
      | some rightTerm =>
          rw [hRightLookup] at decisionWitness
          exact consistencyWitness indexPair.fst indexPair.snd leftTerm rightTerm
            hLeftLookup hRightLookup
            (gccDecideImpliesDeriv problem.equationalPart leftTerm rightTerm
              decisionWitness)

/-- A bridge-respecting environment satisfying the A-part satisfies the WHOLE augmented
system, provided every derived equality gcc-checks. -/
theorem nocAugmentedSystemSatisfied (problem : NocProblem) (env : List LfkInt)
    (consistencyWitness : nocFunctionalConsistencyHolds problem env)
    (arithmeticWitness : lfkSatisfiesSystem env problem.arithmeticPart = true) :
    ∀ (derivedEqualities : List (Nat × Nat)),
      nocCheckAllDerivedEqualities problem.equationalPart problem.sharedInterface
        derivedEqualities = true →
      lfkSatisfiesSystem env (nocAugmentSystem derivedEqualities problem.arithmeticPart)
        = true
  | List.nil, _allCheckWitness => arithmeticWitness
  | indexPair :: remainingPairs, allCheckWitness =>
      have destructured := lfkBoolAndDestruct
        (nocCheckDerivedEquality problem.equationalPart problem.sharedInterface indexPair)
        (nocCheckAllDerivedEqualities problem.equationalPart problem.sharedInterface
          remainingPairs)
        allCheckWitness
      lfkBoolAndIntro
        (lfkSatisfiesConstraint env
          (nocDerivedEqualityConstraint indexPair.fst indexPair.snd))
        (lfkSatisfiesSystem env (nocAugmentSystem remainingPairs problem.arithmeticPart))
        (nocDerivedRowSatisfiedOfEnvEq env indexPair.fst indexPair.snd
          (nocCheckedEqualityGivesEnvEq problem env consistencyWitness indexPair
            destructured.left))
        (nocAugmentedSystemSatisfied problem env consistencyWitness arithmeticWitness
          remainingPairs destructured.right)

/-- **THE HEADLINE — dispatch soundness**: an accepted combination certificate refutes
EVERY joint model.  Decomposition: (a) each derived equality is `GccDeriv`-derivable
(gcc decision soundness), (b) the bridge turns derivability into satisfaction of the
augmented rows, (c) the sibling's unconditional Farkas soundness kills the environment.
Nothing new is trusted: the two engine soundness theorems compose. -/
theorem nocCombinationSound (problem : NocProblem) (certificate : NocCertificate)
    (acceptedWitness : nocCheckCombination problem certificate = true) :
    ∀ (env : List LfkInt), nocIsJointModel problem env → False :=
  fun env jointModelWitness =>
    have destructured := lfkBoolAndDestruct
      (nocCheckAllDerivedEqualities problem.equationalPart problem.sharedInterface
        certificate.derivedEqualities)
      (lfkCheckRefutation certificate.farkasMultipliers
        (nocAugmentSystem certificate.derivedEqualities problem.arithmeticPart))
      acceptedWitness
    lfkRefutationSoundUnconditional certificate.farkasMultipliers
      (nocAugmentSystem certificate.derivedEqualities problem.arithmeticPart)
      destructured.right env
      (nocAugmentedSystemSatisfied problem env jointModelWitness.right
        jointModelWitness.left certificate.derivedEqualities destructured.left)

/-- The headline against genuine two-theory semantics: no respecting model of the
E-part can agree with an environment satisfying the A-part once a combination
certificate is accepted. -/
theorem nocCombinationSoundForMixedSemantics (problem : NocProblem)
    (certificate : NocCertificate)
    (acceptedWitness : nocCheckCombination problem certificate = true)
    (model : NocMixedModel) (env : List LfkInt)
    (respectWitness : nocModelRespectsIntEq model)
    (equationsWitness : nocModelSatisfiesEquations model problem.equationalPart)
    (agreementWitness : nocEnvAgreesWithModel model problem.sharedInterface env)
    (arithmeticWitness : lfkSatisfiesSystem env problem.arithmeticPart = true) : False :=
  nocCombinationSound problem certificate acceptedWitness env
    (And.intro arithmeticWitness
      (nocModelAgreementGivesConsistency problem model env respectWitness
        equationsWitness agreementWitness))

/-! ## The end-to-end finder (one-round E→A propagation + Fourier–Motzkin) -/

/-- Cons-only append for index-pair lists. -/
def nocIndexPairListAppend : List (Nat × Nat) → List (Nat × Nat) → List (Nat × Nat)
  | List.nil, rightList => rightList
  | headPair :: remainingPairs, rightList =>
      headPair :: nocIndexPairListAppend remainingPairs rightList

/-- Collect, for one anchor variable, every later shared variable whose claimed equality
the checker itself accepts (filtering BY the checker makes finder-soundness
definitional). -/
def nocCollectProvablePairs (equations : List (GccTerm × GccTerm))
    (sharedInterface : List (Nat × GccTerm)) (anchorIndex : Nat) :
    List (Nat × GccTerm) → List (Nat × Nat)
  | List.nil => List.nil
  | laterEntry :: remainingEntries =>
      cond (nocCheckDerivedEquality equations sharedInterface (anchorIndex, laterEntry.fst))
        ((anchorIndex, laterEntry.fst)
          :: nocCollectProvablePairs equations sharedInterface anchorIndex
            remainingEntries)
        (nocCollectProvablePairs equations sharedInterface anchorIndex remainingEntries)

/-- One-round E→A propagation over every suffix of the interface: each entry anchors
against all later entries — every unordered shared pair is tested exactly once. -/
def nocPropagateOverSuffix (equations : List (GccTerm × GccTerm))
    (sharedInterface : List (Nat × GccTerm)) : List (Nat × GccTerm) → List (Nat × Nat)
  | List.nil => List.nil
  | anchorEntry :: remainingEntries =>
      nocIndexPairListAppend
        (nocCollectProvablePairs equations sharedInterface anchorEntry.fst
          remainingEntries)
        (nocPropagateOverSuffix equations sharedInterface remainingEntries)

/-- The propagated equalities of a problem. -/
def nocPropagateEqualities (problem : NocProblem) : List (Nat × Nat) :=
  nocPropagateOverSuffix problem.equationalPart problem.sharedInterface
    problem.sharedInterface

/-- Assemble the combination certificate from the propagated equalities and the
Fourier–Motzkin finder's verdict. -/
def nocAssembleCertificate (propagatedEqualities : List (Nat × Nat)) :
    Option (List Nat) → Option NocCertificate
  | Option.some farkasMultipliers =>
      Option.some (NocCertificate.mk propagatedEqualities farkasMultipliers)
  | Option.none => Option.none

/-- THE END-TO-END FINDER: propagate shared equalities, augment the A-side, run the
sibling Fourier–Motzkin finder, package the certificate. -/
def nocFindRefutation (problem : NocProblem) : Option NocCertificate :=
  nocAssembleCertificate (nocPropagateEqualities problem)
    (lfmFindRefutationCertificate
      (nocAugmentSystem (nocPropagateEqualities problem) problem.arithmeticPart))

/-- All-check distributes over the bespoke append. -/
theorem nocCheckAllAppend (equations : List (GccTerm × GccTerm))
    (sharedInterface : List (Nat × GccTerm)) :
    ∀ (leftList rightList : List (Nat × Nat)),
      nocCheckAllDerivedEqualities equations sharedInterface leftList = true →
      nocCheckAllDerivedEqualities equations sharedInterface rightList = true →
      nocCheckAllDerivedEqualities equations sharedInterface
        (nocIndexPairListAppend leftList rightList) = true
  | List.nil, _rightList, _leftWitness, rightWitness => rightWitness
  | headPair :: remainingPairs, rightList, leftWitness, rightWitness =>
      have destructured := lfkBoolAndDestruct
        (nocCheckDerivedEquality equations sharedInterface headPair)
        (nocCheckAllDerivedEqualities equations sharedInterface remainingPairs)
        leftWitness
      lfkBoolAndIntro
        (nocCheckDerivedEquality equations sharedInterface headPair)
        (nocCheckAllDerivedEqualities equations sharedInterface
          (nocIndexPairListAppend remainingPairs rightList))
        destructured.left
        (nocCheckAllAppend equations sharedInterface remainingPairs rightList
          destructured.right rightWitness)

/-- Every collected pair checks — the collector filters by the checker predicate. -/
theorem nocCollectedPairsAllCheck (equations : List (GccTerm × GccTerm))
    (sharedInterface : List (Nat × GccTerm)) (anchorIndex : Nat) :
    ∀ (interfaceEntries : List (Nat × GccTerm)),
      nocCheckAllDerivedEqualities equations sharedInterface
        (nocCollectProvablePairs equations sharedInterface anchorIndex interfaceEntries)
        = true
  | List.nil => rfl
  | laterEntry :: remainingEntries => by
      cases hCheck : nocCheckDerivedEquality equations sharedInterface
          (anchorIndex, laterEntry.fst) with
      | true =>
          have hUnfold : nocCollectProvablePairs equations sharedInterface anchorIndex
              (laterEntry :: remainingEntries)
              = (anchorIndex, laterEntry.fst)
                :: nocCollectProvablePairs equations sharedInterface anchorIndex
                  remainingEntries := by
            simp only [nocCollectProvablePairs]
            rw [hCheck]
            rfl
          rw [hUnfold]
          exact lfkBoolAndIntro
            (nocCheckDerivedEquality equations sharedInterface
              (anchorIndex, laterEntry.fst))
            (nocCheckAllDerivedEqualities equations sharedInterface
              (nocCollectProvablePairs equations sharedInterface anchorIndex
                remainingEntries))
            hCheck
            (nocCollectedPairsAllCheck equations sharedInterface anchorIndex
              remainingEntries)
      | false =>
          have hUnfold : nocCollectProvablePairs equations sharedInterface anchorIndex
              (laterEntry :: remainingEntries)
              = nocCollectProvablePairs equations sharedInterface anchorIndex
                remainingEntries := by
            simp only [nocCollectProvablePairs]
            rw [hCheck]
            rfl
          rw [hUnfold]
          exact nocCollectedPairsAllCheck equations sharedInterface anchorIndex
            remainingEntries

/-- Every propagated pair checks (suffix induction over the interface). -/
theorem nocPropagateOverSuffixAllCheck (equations : List (GccTerm × GccTerm))
    (sharedInterface : List (Nat × GccTerm)) :
    ∀ (suffixEntries : List (Nat × GccTerm)),
      nocCheckAllDerivedEqualities equations sharedInterface
        (nocPropagateOverSuffix equations sharedInterface suffixEntries) = true
  | List.nil => rfl
  | anchorEntry :: remainingEntries =>
      nocCheckAllAppend equations sharedInterface
        (nocCollectProvablePairs equations sharedInterface anchorEntry.fst
          remainingEntries)
        (nocPropagateOverSuffix equations sharedInterface remainingEntries)
        (nocCollectedPairsAllCheck equations sharedInterface anchorEntry.fst
          remainingEntries)
        (nocPropagateOverSuffixAllCheck equations sharedInterface remainingEntries)

/-- The propagated equalities of any problem all check. -/
theorem nocPropagatedAllCheck (problem : NocProblem) :
    nocCheckAllDerivedEqualities problem.equationalPart problem.sharedInterface
      (nocPropagateEqualities problem) = true :=
  nocPropagateOverSuffixAllCheck problem.equationalPart problem.sharedInterface
    problem.sharedInterface

/-- Invert certificate assembly: a produced certificate carries exactly the propagated
equalities and a Fourier–Motzkin hit. -/
theorem nocAssembleCertificateInversion :
    ∀ (propagatedEqualities : List (Nat × Nat)) (finderResult : Option (List Nat))
      (certificate : NocCertificate),
      nocAssembleCertificate propagatedEqualities finderResult
        = Option.some certificate →
      And (certificate.derivedEqualities = propagatedEqualities)
        (finderResult = Option.some certificate.farkasMultipliers)
  | _propagatedEqualities, Option.none, _certificate, assembledWitness =>
      nomatch assembledWitness
  | propagatedEqualities, Option.some farkasMultipliers, certificate,
      assembledWitness => by
      injection assembledWitness with certificateEq
      rw [← certificateEq]
      exact And.intro rfl rfl

/-- **FINDER SOUNDNESS**: whatever certificate the end-to-end finder returns, the
combination checker accepts it (propagation filters by the checker; the Fourier–Motzkin
composition theorem covers the Farkas half). -/
theorem nocFinderSound (problem : NocProblem) (certificate : NocCertificate)
    (foundWitness : nocFindRefutation problem = Option.some certificate) :
    nocCheckCombination problem certificate = true := by
  have inverted := nocAssembleCertificateInversion (nocPropagateEqualities problem)
    (lfmFindRefutationCertificate
      (nocAugmentSystem (nocPropagateEqualities problem) problem.arithmeticPart))
    certificate foundWitness
  have equalitiesChecked : nocCheckAllDerivedEqualities problem.equationalPart
      problem.sharedInterface certificate.derivedEqualities = true := by
    rw [inverted.left]
    exact nocPropagatedAllCheck problem
  have farkasAccepted : lfkCheckRefutation certificate.farkasMultipliers
      (nocAugmentSystem certificate.derivedEqualities problem.arithmeticPart) = true := by
    rw [inverted.left]
    exact lfmFoundContradictionCertifies
      (nocAugmentSystem (nocPropagateEqualities problem) problem.arithmeticPart)
      certificate.farkasMultipliers inverted.right
  exact lfkBoolAndIntro
    (nocCheckAllDerivedEqualities problem.equationalPart problem.sharedInterface
      certificate.derivedEqualities)
    (lfkCheckRefutation certificate.farkasMultipliers
      (nocAugmentSystem certificate.derivedEqualities problem.arithmeticPart))
    equalitiesChecked farkasAccepted

/-- End-to-end: a finder hit refutes every joint model. -/
theorem nocFinderRefutesJointModels (problem : NocProblem) (certificate : NocCertificate)
    (foundWitness : nocFindRefutation problem = Option.some certificate)
    (env : List LfkInt) (jointModelWitness : nocIsJointModel problem env) : False :=
  nocCombinationSound problem certificate
    (nocFinderSound problem certificate foundWitness) env jointModelWitness

/-! ## The walls (owner-false Props) -/

/-- A genuinely MIXED term: uninterpreted symbols and application interleaved with
linear-arithmetic constructors.  This is the pre-purification language; the purifier
would extract alien subterms into fresh shared variables. -/
inductive NocMixedTerm : Type where
  | symbol (name : Nat) : NocMixedTerm
  | apply (function argument : NocMixedTerm) : NocMixedTerm
  | literal (value : LfkInt) : NocMixedTerm
  | addition (leftOperand rightOperand : NocMixedTerm) : NocMixedTerm
  | scaling (weight : LfkInt) (operand : NocMixedTerm) : NocMixedTerm

/-- Evaluate a mixed term in a two-theory model. -/
def nocMixedTermDenotation (model : NocMixedModel) : NocMixedTerm → LfkInt
  | NocMixedTerm.symbol name => model.symbolValue name
  | NocMixedTerm.apply function argument =>
      model.applyValue (nocMixedTermDenotation model function)
        (nocMixedTermDenotation model argument)
  | NocMixedTerm.literal value => value
  | NocMixedTerm.addition leftOperand rightOperand =>
      lfkIntAdd (nocMixedTermDenotation model leftOperand)
        (nocMixedTermDenotation model rightOperand)
  | NocMixedTerm.scaling weight operand =>
      lfkIntMul weight (nocMixedTermDenotation model operand)

/-- A mixed atom: a relation between two mixed terms (equalities subsume the E-language,
inequalities subsume the A-language). -/
structure NocMixedAtom where
  leftTerm : NocMixedTerm
  rightTerm : NocMixedTerm
  relation : LfkRelation

/-- Does the model satisfy one mixed atom (relations read `left REL right`, matching the
sibling's satisfaction orientation)? -/
def nocMixedAtomHolds (model : NocMixedModel) (atom : NocMixedAtom) : Bool :=
  match atom.relation with
  | LfkRelation.isGreaterOrEqual =>
      lfkIntLe (nocMixedTermDenotation model atom.rightTerm)
        (nocMixedTermDenotation model atom.leftTerm)
  | LfkRelation.isStrictlyGreater =>
      lfkIntLt (nocMixedTermDenotation model atom.rightTerm)
        (nocMixedTermDenotation model atom.leftTerm)
  | LfkRelation.isEqualTo =>
      lfkIntEq (nocMixedTermDenotation model atom.leftTerm)
        (nocMixedTermDenotation model atom.rightTerm)

/-- Does the model satisfy every mixed atom? -/
def nocMixedAtomsHold (model : NocMixedModel) : List NocMixedAtom → Bool
  | List.nil => true
  | atomHead :: atomTail =>
      nocMixedAtomHolds model atomHead && nocMixedAtomsHold model atomTail

/-- Purification equivalence, not proven here: some purifier maps every mixed conjunction to a
`NocProblem` whose joint satisfiability matches mixed satisfiability under respecting two-theory
models. The missing content is the concrete syntactic purifier with its two lemmas. Forward:
alien-subterm extraction with one fresh shared variable per distinct alien subterm (hash-consing,
the source of functional consistency) is a definitional extension, so a mixed model extends to a
joint environment. Backward: a joint environment must be extended to a congruent `applyValue` on the
whole carrier — Nelson–Oppen's total model extension / term-model construction. As a bare
existential the statement carries no constructive force; the missing artifact is the purifier itself
(`fxDissatCombine_hasPurificationEquivalence`). -/
def nocPurificationStatement : Prop :=
  ∃ (purify : List NocMixedAtom → NocProblem),
    ∀ (mixedAtoms : List NocMixedAtom),
      Iff
        (∃ (model : NocMixedModel),
          And (nocModelRespectsIntEq model) (nocMixedAtomsHold model mixedAtoms = true))
        (∃ (env : List LfkInt), nocIsJointModel (purify mixedAtoms) env)

/-- Combination completeness, not proven here and false over the integers as stated: every
jointly-unsatisfiable problem would have an accepted certificate. The integer counterexample is
inherited from the A-side alone — the problem with empty E-part and A-part `{2x = 1}` has no joint
model yet no Farkas certificate (rationally feasible). The reachable target is the rational
relaxation, which still needs: (i) equality-interpolation completeness of the E-side (every shared
equality entailed by the joint system is `GccDeriv`-derivable; single equalities suffice only for
convex theories, and ℤ-LIA is not convex, since `1 <= x <= 2` entails `x = 1 ∨ x = 2` with neither
disjunct entailed, so the non-convex case needs case-split trees over equality disjunctions);
(ii) Farkas completeness over the rationals (the sibling's owner-false Fourier–Motzkin backward
direction); (iii) model amalgamation (gluing an E-model and an A-model agreeing on the arrangement
needs stable infiniteness / cardinality agreement, a semantic condition no certificate checker
inspects) (`fxDissatCombine_hasCombinationCompleteness`). -/
def nocCombinationCompletenessStatement : Prop :=
  ∀ (problem : NocProblem),
    (∀ (env : List LfkInt), nocIsJointModel problem env → False) →
    ∃ (certificate : NocCertificate), nocCheckCombination problem certificate = true

/-- The certificate-level combination dispatch: checker, joint-model semantics, two-theory grounding
of the bridge, and the soundness chain through `nocCombinationSound` /
`nocCombinationSoundForMixedSemantics`. -/
def fxDissatCombine_hasDispatchSoundness : Bool := true

/-- The end-to-end finder (one-round propagation + Fourier–Motzkin), with `nocFinderSound` /
`nocFinderRefutesJointModels`. -/
def fxDissatCombine_hasEndToEndFinder : Bool := true

/-- Owner flag for `nocPurificationStatement`, not proven. -/
def fxDissatCombine_hasPurificationEquivalence : Bool := false

/-- Owner flag for `nocCombinationCompletenessStatement`, not proven and false over ℤ as stated
(see the wall docstring for the three missing rational-side legs). -/
def fxDissatCombine_hasCombinationCompleteness : Bool := false

/-! ## Smoke tests (Bool outputs, false cases included, kernel-checked `rfl` pins)

Symbols: `0 = a`, `1 = b`, `3 = f`. Shared variables: `x0 ↦ a`, `x1 ↦ b`. -/

/-- Smoke term `a`. -/
def nocSmokeTermA : GccTerm := GccTerm.symbol 0

/-- Smoke term `b`. -/
def nocSmokeTermB : GccTerm := GccTerm.symbol 1

/-- Smoke term `f(a)`. -/
def nocSmokeTermFofA : GccTerm := GccTerm.apply (GccTerm.symbol 3) (GccTerm.symbol 0)

/-- Smoke E-part: `f(a) = b` and `f(a) = a` — forces `a = b` through symmetry and
transitivity (a genuine congruence-engine call, not a literal equation). -/
def nocSmokeEquations : List (GccTerm × GccTerm) :=
  [(nocSmokeTermFofA, nocSmokeTermB), (nocSmokeTermFofA, nocSmokeTermA)]

/-- Smoke shared interface: `x0 ↦ a`, `x1 ↦ b`. -/
def nocSmokeSharedInterface : List (Nat × GccTerm) :=
  [(0, nocSmokeTermA), (1, nocSmokeTermB)]

/-- Smoke A-part: `x0 - x1 >= 1` — alone satisfiable, jointly contradictory with the
propagated `x0 = x1`. -/
def nocSmokeArithmeticPart : List LfkConstraint :=
  [LfkConstraint.mk [LfkInt.mk 1 0, LfkInt.mk 0 1] (LfkInt.mk 1 0)
    LfkRelation.isGreaterOrEqual]

/-- The jointly-unsatisfiable smoke problem. -/
def nocSmokeProblem : NocProblem :=
  NocProblem.mk nocSmokeEquations nocSmokeArithmeticPart nocSmokeSharedInterface

/-- The hand certificate: derive `x0 = x1`; over the EXPANDED augmented system (forward
equality row, flipped equality row, then the A-row) weight the flipped row and the
A-row once each — coefficients cancel, residual bound `1 > 0`. -/
def nocSmokeCertificate : NocCertificate := NocCertificate.mk [(0, 1)] [0, 1, 1]

/-- Same A-part and interface but an EMPTY E-part: `a = b` is no longer derivable, so
the same certificate must be REJECTED at the equality check. -/
def nocSmokeNoEquationsProblem : NocProblem :=
  NocProblem.mk List.nil nocSmokeArithmeticPart nocSmokeSharedInterface

/-- Satisfiable variant: A-part `x0 - x1 >= 0` is consistent with `x0 = x1`. -/
def nocSmokeSatisfiableArithmetic : List LfkConstraint :=
  [LfkConstraint.mk [LfkInt.mk 1 0, LfkInt.mk 0 1] lfkIntZero
    LfkRelation.isGreaterOrEqual]

/-- The jointly-satisfiable smoke problem. -/
def nocSmokeSatisfiableProblem : NocProblem :=
  NocProblem.mk nocSmokeEquations nocSmokeSatisfiableArithmetic nocSmokeSharedInterface

/-- The witnessing environment `x0 = x1 = 7` for the satisfiable problem. -/
def nocSmokeSatisfyingEnv : List LfkInt := [LfkInt.mk 7 0, LfkInt.mk 7 0]

/-- Pure-A degenerate dispatch: empty E-part, empty interface, the sibling's
contradictory system `x >= 1, -x >= 0` — the combination checker with NO derived
equalities is exactly the sibling checker. -/
def nocSmokePureArithmeticProblem : NocProblem :=
  NocProblem.mk List.nil lfkSmokeContradictorySystem List.nil

/-- Certificate for the pure-A dispatch: no equalities, sibling multipliers. -/
def nocSmokePureArithmeticCertificate : NocCertificate :=
  NocCertificate.mk List.nil [1, 1]

/-- Kernel pin: the combination certificate is ACCEPTED on the joint contradiction. -/
theorem nocSmokeAcceptedPin :
    nocCheckCombination nocSmokeProblem nocSmokeCertificate = true := rfl

/-- Kernel pin (FALSE case): without the E-equations the claimed equality is
unprovable — the SAME certificate is rejected. -/
theorem nocSmokeUnprovableEqualityPin :
    nocCheckCombination nocSmokeNoEquationsProblem nocSmokeCertificate = false := rfl

/-- Kernel pin (FALSE case): correct equality, bogus multipliers — the Farkas half
rejects. -/
theorem nocSmokeBogusMultipliersPin :
    nocCheckCombination nocSmokeProblem (NocCertificate.mk [(0, 1)] [0, 0, 0])
      = false := rfl

/-- Kernel pin: the pure-A degenerate dispatch is accepted (Layer-0 shape). -/
theorem nocSmokePureArithmeticPin :
    nocCheckCombination nocSmokePureArithmeticProblem nocSmokePureArithmeticCertificate
      = true := rfl

/-- Kernel pin (FALSE case): the empty problem admits no refutation. -/
theorem nocSmokeEmptyPin :
    nocCheckCombination (NocProblem.mk List.nil List.nil List.nil)
      (NocCertificate.mk List.nil List.nil) = false := rfl

/-- Kernel pin: the finder CLOSES the jointly-unsatisfiable smoke end-to-end. -/
theorem nocSmokeFinderHitPin :
    (nocFindRefutation nocSmokeProblem).isSome = true := rfl

/-- Kernel pin (FALSE case): on the jointly-satisfiable variant the finder returns
nothing. -/
theorem nocSmokeFinderMissPin :
    (nocFindRefutation nocSmokeSatisfiableProblem).isSome = false := rfl

/-- Any shared variable the satisfiable smoke interface resolves carries the value 7 in
the witnessing environment (concrete two-entry lookup inversion). -/
theorem nocSmokeLookupForcesSeven (queryIndex : Nat) (foundTerm : GccTerm)
    (lookupWitness : nocSharedLookup nocSmokeSharedInterface queryIndex
      = Option.some foundTerm) :
    nocEnvValueAt nocSmokeSatisfyingEnv queryIndex = LfkInt.mk 7 0 := by
  cases hBeqZero : Nat.beq queryIndex 0 with
  | true =>
      rw [lfkNatEqOfBeq queryIndex 0 hBeqZero]
      rfl
  | false =>
      cases hBeqOne : Nat.beq queryIndex 1 with
      | true =>
          rw [lfkNatEqOfBeq queryIndex 1 hBeqOne]
          rfl
      | false =>
          have lookupMissed : nocSharedLookup nocSmokeSharedInterface queryIndex
              = Option.none := by
            show cond (Nat.beq queryIndex 0) (Option.some nocSmokeTermA)
              (cond (Nat.beq queryIndex 1) (Option.some nocSmokeTermB) Option.none)
              = Option.none
            rw [hBeqZero, hBeqOne]
            rfl
          rw [lookupMissed] at lookupWitness
          exact Bool.noConfusion (congrArg Option.isSome lookupWitness)

/-- GENUINENESS PIN: the satisfiable smoke problem really HAS a joint model — the
environment `(7, 7)` satisfies the A-part and the bridge (all resolvable shared
variables carry the same value). -/
theorem nocSmokeSatisfiableJointModelPin :
    nocIsJointModel nocSmokeSatisfiableProblem nocSmokeSatisfyingEnv :=
  And.intro rfl
    (fun leftIndex rightIndex leftTerm rightTerm leftLookup rightLookup _derivation => by
      rw [nocSmokeLookupForcesSeven leftIndex leftTerm leftLookup,
        nocSmokeLookupForcesSeven rightIndex rightTerm rightLookup]
      exact lfkIntEqRefl (LfkInt.mk 7 0))

/-- UNIVERSAL FALSE-CASE CAPSTONE: no combination certificate WHATSOEVER is accepted on
the satisfiable smoke problem — soundness plus the exhibited joint model. -/
theorem nocSmokeSatisfiableHasNoCertificate (certificate : NocCertificate)
    (acceptedWitness : nocCheckCombination nocSmokeSatisfiableProblem certificate
      = true) : False :=
  nocCombinationSound nocSmokeSatisfiableProblem certificate acceptedWitness
    nocSmokeSatisfyingEnv nocSmokeSatisfiableJointModelPin

-- Joint contradiction accepted (E forces x0 = x1, A demands x0 >= x1 + 1). Expect: true
#eval nocCheckCombination nocSmokeProblem nocSmokeCertificate
-- FALSE case: empty E-part, the equality claim is rejected. Expect: false
#eval nocCheckCombination nocSmokeNoEquationsProblem nocSmokeCertificate
-- FALSE case: bogus multipliers rejected by the Farkas half. Expect: false
#eval nocCheckCombination nocSmokeProblem (NocCertificate.mk [(0, 1)] [0, 0, 0])
-- Pure-A degenerate dispatch (no derived equalities). Expect: true
#eval nocCheckCombination nocSmokePureArithmeticProblem nocSmokePureArithmeticCertificate
-- FALSE case: empty problem, empty certificate. Expect: false
#eval nocCheckCombination (NocProblem.mk List.nil List.nil List.nil)
  (NocCertificate.mk List.nil List.nil)
-- The end-to-end finder closes the joint contradiction. Expect: true
#eval (nocFindRefutation nocSmokeProblem).isSome
-- The found certificate is checker-accepted (nocFinderSound made executable). Expect: true
#eval match nocFindRefutation nocSmokeProblem with
  | Option.some foundCertificate => nocCheckCombination nocSmokeProblem foundCertificate
  | Option.none => false
-- FALSE case: the finder finds nothing on the jointly-satisfiable variant. Expect: false
#eval (nocFindRefutation nocSmokeSatisfiableProblem).isSome
-- Sanity: (7, 7) satisfies the satisfiable A-part. Expect: true
#eval lfkSatisfiesSystem nocSmokeSatisfyingEnv nocSmokeSatisfiableArithmetic

end FX1Poly.ComputerAlgebra
