import FX1Poly.ComputerAlgebra.Number.NormalizedRational

/-! # ComputerAlgebra/Probability/FiniteSupportDistribution — exact
finite-support ℚ-probability distributions (MEAS-1)

A concrete, decidable, zero-axiom probability-mass-function layer built
directly on the canonical-NF ℚ carrier `QnfRat` (NUM-Q-7): a finite list of
`(outcome : Nat, mass : QnfRat)` pairs.  Because masses live on the canonical
carrier, byte-equality IS rational equality (`qnfBeqIffEq`), so distribution
equality up to reordering / duplicate-merge is DECIDABLE by structural `Bool`
comparison of normalized supports.

## What lands (finite, decidable core — DECIDED)

  * `FpDist` — the carrier (`support : List (Nat × QnfRat)`).
  * `fpdMassSum` — the total mass (cons-only `qnfAdd` fold) with the
    append-splits-sum law `fpdMassSumCat` (mirrors the shipped `ihcSumCat`).
  * `fpdIsWellFormed` — every mass nonnegative (numerator-sign read) AND total
    mass `= qnfOne`, a pure `Bool`.
  * `fpdDirac` — a point mass, well-formed by `qnfAddZeroRight qnfOne`.
  * `fpdNormalise` — merge equal outcomes (`qnfAdd` colliding masses), drop
    zero masses, keep sorted by outcome; MASS-SUM-PRESERVING
    (`fpdNormaliseMassSum`).
  * `fpdMap` (pushforward along `Nat → Nat`), `fpdConvex` (weighted mix),
    `fpdProduct` (independent product on a pairing of outcomes),
    `fpdExpectation`, `fpdCondition` (filter + renormalise) — each with its
    mass-sum-preservation theorem (`fpd*PreservesMassOne`), the honest
    "well-formedness preservation = total stays one" content.
  * `fpdDistEq` — structural `qnfBeq` comparison of normalized supports, with
    soundness `fpdDistEqSound` and the genuine equivalence `FpConv`
    (`fpdConvSound` + the refutation half `fpdConvComplete`).
  * Expectation linearity (`fpdExpectationLinear`) and
    `fpdDiracExpectation`, both riding the `QnfRat` distributivity suite.

## The walls (WALLED, `false` markers)

  * `fpdHasCountableSupport := false` — countably-infinite / continuous
    distributions need a convergent series in the completion of ℚ (Bishop
    `RegularReal` L1 integration); no finite `List` support represents a
    geometric tail.
  * `fpdHasGiryMonadLaws := false` — the categorical Giry-monad multiplication
    laws + de Finetti exchangeability are the deep extension; this is the same
    walled node as the copy-discard Markov PROP's `cdwHasMarkovCompleteness`
    (row-stochastic-channel reconstruction).

## Zero-axiom

Structural recursion on `List` / `Nat` (never `WellFounded.fix`), full-enum
constructor matches (no wildcard arms over a split scrutinee), `QnfRat` kernel
arithmetic + its `qnfBeqIffEq` byte-equality, `congrArg`/`Eq.trans` and `calc`
chains.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`,
`native_decide`, `omega`, `funext`, `decide`-on-`Prop`.  Per-declaration gated
in `FX1PolyAudit/ComputerAlgebra/Probability/FiniteSupportDistribution.lean`. -/

namespace FX1Poly.ComputerAlgebra

/-! ## Two `QnfRat` scalar lemmas the fold needs -/

/-- `factor * 0 = 0` on the canonical carrier — derived from left
distributivity and additive cancellation (no dedicated multiplicative-zero law
ships in the `QnfRat` suite). -/
theorem qnfMulZeroRight (factor : QnfRat) : qnfMul factor qnfZero = qnfZero := by
  have hself : qnfMul factor qnfZero
      = qnfAdd (qnfMul factor qnfZero) (qnfMul factor qnfZero) := by
    have hdist := qnfMulLeftDistrib factor qnfZero qnfZero
    rw [qnfAddZeroRight qnfZero] at hdist
    exact hdist
  calc qnfMul factor qnfZero
      = qnfAdd (qnfMul factor qnfZero) qnfZero := (qnfAddZeroRight _).symm
    _ = qnfAdd (qnfMul factor qnfZero)
          (qnfAdd (qnfMul factor qnfZero) (qnfNeg (qnfMul factor qnfZero))) := by
            rw [qnfAddNegRight]
    _ = qnfAdd (qnfAdd (qnfMul factor qnfZero) (qnfMul factor qnfZero))
          (qnfNeg (qnfMul factor qnfZero)) := (qnfAddAssoc _ _ _).symm
    _ = qnfAdd (qnfMul factor qnfZero) (qnfNeg (qnfMul factor qnfZero)) := by
          rw [← hself]
    _ = qnfZero := qnfAddNegRight _

/-- `0 * factor = 0` — commute and reuse. -/
theorem qnfMulZeroLeft (factor : QnfRat) : qnfMul qnfZero factor = qnfZero :=
  (qnfMulComm qnfZero factor).trans (qnfMulZeroRight factor)

/-- The middle-four exchange for addition — `(p + q) + (r + s) =
(p + r) + (q + s)` — from commutativity and associativity. -/
theorem qnfAddMiddleFour (firstMass secondMass thirdMass fourthMass : QnfRat) :
    qnfAdd (qnfAdd firstMass secondMass) (qnfAdd thirdMass fourthMass) =
      qnfAdd (qnfAdd firstMass thirdMass) (qnfAdd secondMass fourthMass) := by
  rw [qnfAddAssoc firstMass secondMass (qnfAdd thirdMass fourthMass),
    ← qnfAddAssoc secondMass thirdMass fourthMass,
    qnfAddComm secondMass thirdMass,
    qnfAddAssoc thirdMass secondMass fourthMass,
    ← qnfAddAssoc firstMass thirdMass (qnfAdd secondMass fourthMass)]

/-- The three-factor left-swap — `first * (second * third) =
second * (first * third)` — from commutativity and associativity. -/
theorem qnfMulLeftSwap (firstMass secondMass thirdMass : QnfRat) :
    qnfMul firstMass (qnfMul secondMass thirdMass) =
      qnfMul secondMass (qnfMul firstMass thirdMass) := by
  rw [← qnfMulAssoc firstMass secondMass thirdMass,
    qnfMulComm firstMass secondMass,
    qnfMulAssoc secondMass firstMass thirdMass]

/-! ## T1 — the carrier, the mass sum, well-formedness, dirac -/

/-- A finite-support ℚ-probability distribution: outcomes are `Nat`, masses
are canonical rationals.  Well-formedness (`fpdIsWellFormed`) is a separate
predicate, not baked into the carrier, so intermediate (unnormalized) supports
are representable. -/
structure FpDist where
  support : List (Nat × QnfRat)

/-- Total mass — a cons-only `qnfAdd` fold over the mass column. -/
def fpdMassSum : List (Nat × QnfRat) → QnfRat
  | [] => qnfZero
  | (_outcome, mass) :: rest => qnfAdd mass (fpdMassSum rest)

/-- Cons-only concatenation of two supports (own list op — avoids the
propext-leak-prone `List.append` lemmas). -/
def fpdCat : List (Nat × QnfRat) → List (Nat × QnfRat) → List (Nat × QnfRat)
  | [], rightSupport => rightSupport
  | entry :: leftRest, rightSupport => entry :: fpdCat leftRest rightSupport

/-- **Append splits the sum** — the mass-column analogue of the shipped
`ihcSumCat`: total over a concatenation is the sum of totals. -/
theorem fpdMassSumCat : (leftSupport rightSupport : List (Nat × QnfRat)) →
    fpdMassSum (fpdCat leftSupport rightSupport) =
      qnfAdd (fpdMassSum leftSupport) (fpdMassSum rightSupport)
  | [], rightSupport => (qnfAddZeroLeft (fpdMassSum rightSupport)).symm
  | (_outcome, mass) :: leftRest, rightSupport => by
      show qnfAdd mass (fpdMassSum (fpdCat leftRest rightSupport))
        = qnfAdd (qnfAdd mass (fpdMassSum leftRest)) (fpdMassSum rightSupport)
      rw [fpdMassSumCat leftRest rightSupport,
        qnfAddAssoc mass (fpdMassSum leftRest) (fpdMassSum rightSupport)]

/-- A single mass is nonnegative — reads on the numerator sign (the
denominator is structurally positive). -/
def fpdMassIsNonNeg (mass : QnfRat) : Bool :=
  match mass.reducedPair.numerator with
  | .ofNat _ => true
  | .negSucc _ => false

/-- Every mass in a support is nonnegative. -/
def fpdAllMassesNonNeg : List (Nat × QnfRat) → Bool
  | [] => true
  | (_outcome, mass) :: rest => fpdMassIsNonNeg mass && fpdAllMassesNonNeg rest

/-- **Well-formedness**: all masses nonnegative AND total mass is exactly one.
Both conjuncts are `Bool`, so this is fully decidable by kernel computation. -/
def fpdIsWellFormed (mu : FpDist) : Bool :=
  fpdAllMassesNonNeg mu.support && qnfBeq (fpdMassSum mu.support) qnfOne

/-- A point mass at `outcome` — all probability on one atom. -/
def fpdDirac (outcome : Nat) : FpDist :=
  { support := [(outcome, qnfOne)] }

/-- The dirac total mass is one. -/
theorem fpdDiracMassSumOne (outcome : Nat) :
    fpdMassSum (fpdDirac outcome).support = qnfOne :=
  qnfAddZeroRight qnfOne

/-- A dirac point mass is well-formed — masses nonneg and total one both
reduce in the kernel (the outcome is irrelevant to either). -/
theorem fpdDiracIsWellFormed (outcome : Nat) :
    fpdIsWellFormed (fpdDirac outcome) = true := rfl

/-! ## T1 — normalisation (merge duplicates, drop zeros, sort by outcome) -/

/-- Insert one `(outcome, mass)` into a support kept sorted by outcome, merging
(`qnfAdd`) into an existing entry with the same outcome. -/
def fpdInsert (outcome : Nat) (mass : QnfRat) :
    List (Nat × QnfRat) → List (Nat × QnfRat)
  | [] => [(outcome, mass)]
  | (headOutcome, headMass) :: rest =>
      match Nat.beq outcome headOutcome with
      | true => (headOutcome, qnfAdd mass headMass) :: rest
      | false =>
          match Nat.ble outcome headOutcome with
          | true => (outcome, mass) :: (headOutcome, headMass) :: rest
          | false => (headOutcome, headMass) :: fpdInsert outcome mass rest

/-- Insertion preserves the total mass: it contributes exactly `mass`. -/
theorem fpdInsertMassSum (outcome : Nat) (mass : QnfRat) :
    (support : List (Nat × QnfRat)) →
      fpdMassSum (fpdInsert outcome mass support) =
        qnfAdd mass (fpdMassSum support)
  | [] => rfl
  | (headOutcome, headMass) :: rest => by
      show fpdMassSum
          (match Nat.beq outcome headOutcome with
            | true => (headOutcome, qnfAdd mass headMass) :: rest
            | false =>
                match Nat.ble outcome headOutcome with
                | true => (outcome, mass) :: (headOutcome, headMass) :: rest
                | false =>
                    (headOutcome, headMass) :: fpdInsert outcome mass rest)
        = qnfAdd mass (qnfAdd headMass (fpdMassSum rest))
      match Nat.beq outcome headOutcome with
      | true =>
          show qnfAdd (qnfAdd mass headMass) (fpdMassSum rest)
            = qnfAdd mass (qnfAdd headMass (fpdMassSum rest))
          rw [qnfAddAssoc mass headMass (fpdMassSum rest)]
      | false =>
          match Nat.ble outcome headOutcome with
          | true => rfl
          | false =>
              show qnfAdd headMass (fpdMassSum (fpdInsert outcome mass rest))
                = qnfAdd mass (qnfAdd headMass (fpdMassSum rest))
              rw [fpdInsertMassSum outcome mass rest,
                ← qnfAddAssoc headMass mass (fpdMassSum rest),
                qnfAddComm headMass mass,
                qnfAddAssoc mass headMass (fpdMassSum rest)]

/-- Merge every entry of a support into a sorted, duplicate-free-by-outcome
form. -/
def fpdMergeAll : List (Nat × QnfRat) → List (Nat × QnfRat)
  | [] => []
  | (outcome, mass) :: rest => fpdInsert outcome mass (fpdMergeAll rest)

/-- Merging preserves the total mass. -/
theorem fpdMergeAllMassSum : (support : List (Nat × QnfRat)) →
    fpdMassSum (fpdMergeAll support) = fpdMassSum support
  | [] => rfl
  | (outcome, mass) :: rest => by
      show fpdMassSum (fpdInsert outcome mass (fpdMergeAll rest))
        = qnfAdd mass (fpdMassSum rest)
      rw [fpdInsertMassSum outcome mass (fpdMergeAll rest),
        fpdMergeAllMassSum rest]

/-- Drop entries with zero mass. -/
def fpdDropZeros : List (Nat × QnfRat) → List (Nat × QnfRat)
  | [] => []
  | (outcome, mass) :: rest =>
      match qnfBeq mass qnfZero with
      | true => fpdDropZeros rest
      | false => (outcome, mass) :: fpdDropZeros rest

/-- Dropping zero masses preserves the total mass. -/
theorem fpdDropZerosMassSum : (support : List (Nat × QnfRat)) →
    fpdMassSum (fpdDropZeros support) = fpdMassSum support
  | [] => rfl
  | (outcome, mass) :: rest => by
      show fpdMassSum
          (match qnfBeq mass qnfZero with
            | true => fpdDropZeros rest
            | false => (outcome, mass) :: fpdDropZeros rest)
        = qnfAdd mass (fpdMassSum rest)
      match hbeq : qnfBeq mass qnfZero with
      | true =>
          have hzero : mass = qnfZero := (qnfBeqIffEq mass qnfZero).mp hbeq
          show fpdMassSum (fpdDropZeros rest) = qnfAdd mass (fpdMassSum rest)
          rw [fpdDropZerosMassSum rest, hzero, qnfAddZeroLeft (fpdMassSum rest)]
      | false =>
          show qnfAdd mass (fpdMassSum (fpdDropZeros rest))
            = qnfAdd mass (fpdMassSum rest)
          rw [fpdDropZerosMassSum rest]

/-- **Normalise**: merge equal outcomes, drop zero masses, keep sorted. -/
def fpdNormalise (mu : FpDist) : FpDist :=
  { support := fpdDropZeros (fpdMergeAll mu.support) }

/-- Normalisation preserves the total mass — the composition of the merge and
drop-zero preservations. -/
theorem fpdNormaliseMassSum (mu : FpDist) :
    fpdMassSum (fpdNormalise mu).support = fpdMassSum mu.support :=
  (fpdDropZerosMassSum (fpdMergeAll mu.support)).trans
    (fpdMergeAllMassSum mu.support)

/-! ## T2 — the operations and their mass-sum preservation -/

/-- Relabel outcomes along `relabel`, leaving masses untouched. -/
def fpdRelabel (relabel : Nat → Nat) :
    List (Nat × QnfRat) → List (Nat × QnfRat)
  | [] => []
  | (outcome, mass) :: rest => (relabel outcome, mass) :: fpdRelabel relabel rest

/-- Relabelling preserves the total mass (masses are unchanged). -/
theorem fpdRelabelMassSum (relabel : Nat → Nat) :
    (support : List (Nat × QnfRat)) →
      fpdMassSum (fpdRelabel relabel support) = fpdMassSum support
  | [] => rfl
  | (outcome, mass) :: rest => by
      show qnfAdd mass (fpdMassSum (fpdRelabel relabel rest))
        = qnfAdd mass (fpdMassSum rest)
      rw [fpdRelabelMassSum relabel rest]

/-- **Pushforward** along `relabel` — relabel outcomes, then merge collisions
and re-sort. -/
def fpdMap (relabel : Nat → Nat) (mu : FpDist) : FpDist :=
  fpdNormalise { support := fpdRelabel relabel mu.support }

/-- The pushforward preserves total mass one. -/
theorem fpdMapPreservesMassOne (relabel : Nat → Nat) (mu : FpDist)
    (hMassOne : fpdMassSum mu.support = qnfOne) :
    fpdMassSum (fpdMap relabel mu).support = qnfOne :=
  (fpdNormaliseMassSum { support := fpdRelabel relabel mu.support }).trans
    ((fpdRelabelMassSum relabel mu.support).trans hMassOne)

/-- Scale every mass by `factor`. -/
def fpdScale (factor : QnfRat) :
    List (Nat × QnfRat) → List (Nat × QnfRat)
  | [] => []
  | (outcome, mass) :: rest => (outcome, qnfMul factor mass) :: fpdScale factor rest

/-- Scaling multiplies the total by `factor`. -/
theorem fpdScaleMassSum (factor : QnfRat) :
    (support : List (Nat × QnfRat)) →
      fpdMassSum (fpdScale factor support) = qnfMul factor (fpdMassSum support)
  | [] => (qnfMulZeroRight factor).symm
  | (outcome, mass) :: rest => by
      show qnfAdd (qnfMul factor mass) (fpdMassSum (fpdScale factor rest))
        = qnfMul factor (qnfAdd mass (fpdMassSum rest))
      rw [fpdScaleMassSum factor rest,
        qnfMulLeftDistrib factor mass (fpdMassSum rest)]

/-- `weight + (1 - weight) = 1` on the canonical carrier. -/
theorem qnfAddWeightComplement (weight : QnfRat) :
    qnfAdd weight (qnfSub qnfOne weight) = qnfOne := by
  rw [qnfSubEqAddNeg qnfOne weight, ← qnfAddAssoc weight qnfOne (qnfNeg weight),
    qnfAddComm weight qnfOne, qnfAddAssoc qnfOne weight (qnfNeg weight),
    qnfAddNegRight weight, qnfAddZeroRight qnfOne]

/-- **Convex mixture**: `weight`-scaled `mu` plus `(1 - weight)`-scaled `nu`,
merged and re-sorted. -/
def fpdConvex (weight : QnfRat) (mu nu : FpDist) : FpDist :=
  fpdNormalise
    { support :=
        fpdCat (fpdScale weight mu.support)
          (fpdScale (qnfSub qnfOne weight) nu.support) }

/-- The convex mixture preserves total mass one. -/
theorem fpdConvexPreservesMassOne (weight : QnfRat) (mu nu : FpDist)
    (hMuOne : fpdMassSum mu.support = qnfOne)
    (hNuOne : fpdMassSum nu.support = qnfOne) :
    fpdMassSum (fpdConvex weight mu nu).support = qnfOne := by
  rw [fpdConvex,
    fpdNormaliseMassSum
      { support :=
          fpdCat (fpdScale weight mu.support)
            (fpdScale (qnfSub qnfOne weight) nu.support) },
    fpdMassSumCat (fpdScale weight mu.support)
      (fpdScale (qnfSub qnfOne weight) nu.support),
    fpdScaleMassSum weight mu.support,
    fpdScaleMassSum (qnfSub qnfOne weight) nu.support,
    hMuOne, hNuOne, qnfMulOneRight weight,
    qnfMulOneRight (qnfSub qnfOne weight), qnfAddWeightComplement weight]

/-- A total pairing of outcomes: `2^left · (2·right + 1)`.  Distinct on small
inputs (no halving, so no `Nat.div` propext leak); a full injectivity proof is
not needed for the mass-sum laws (any pairing works). -/
def fpdPairNat (leftOutcome rightOutcome : Nat) : Nat :=
  Nat.pow 2 leftOutcome * (2 * rightOutcome + 1)

/-- One row of the product grid: fix a left `(outcome, mass)` and pair it with
every right entry, multiplying masses. -/
def fpdProductRow (leftOutcome : Nat) (leftMass : QnfRat) :
    List (Nat × QnfRat) → List (Nat × QnfRat)
  | [] => []
  | (rightOutcome, rightMass) :: rest =>
      (fpdPairNat leftOutcome rightOutcome, qnfMul leftMass rightMass)
        :: fpdProductRow leftOutcome leftMass rest

/-- A product row's total is `leftMass · (total of the right support)`. -/
theorem fpdProductRowMassSum (leftOutcome : Nat) (leftMass : QnfRat) :
    (rightSupport : List (Nat × QnfRat)) →
      fpdMassSum (fpdProductRow leftOutcome leftMass rightSupport) =
        qnfMul leftMass (fpdMassSum rightSupport)
  | [] => (qnfMulZeroRight leftMass).symm
  | (rightOutcome, rightMass) :: rest => by
      show qnfAdd (qnfMul leftMass rightMass)
          (fpdMassSum (fpdProductRow leftOutcome leftMass rest))
        = qnfMul leftMass (qnfAdd rightMass (fpdMassSum rest))
      rw [fpdProductRowMassSum leftOutcome leftMass rest,
        qnfMulLeftDistrib leftMass rightMass (fpdMassSum rest)]

/-- The full product support: every left entry crossed with every right
entry. -/
def fpdProductSupport :
    List (Nat × QnfRat) → List (Nat × QnfRat) → List (Nat × QnfRat)
  | [], _rightSupport => []
  | (leftOutcome, leftMass) :: leftRest, rightSupport =>
      fpdCat (fpdProductRow leftOutcome leftMass rightSupport)
        (fpdProductSupport leftRest rightSupport)

/-- The product total is the product of totals. -/
theorem fpdProductSupportMassSum :
    (leftSupport rightSupport : List (Nat × QnfRat)) →
      fpdMassSum (fpdProductSupport leftSupport rightSupport) =
        qnfMul (fpdMassSum leftSupport) (fpdMassSum rightSupport)
  | [], rightSupport => (qnfMulZeroLeft (fpdMassSum rightSupport)).symm
  | (leftOutcome, leftMass) :: leftRest, rightSupport => by
      show fpdMassSum
          (fpdCat (fpdProductRow leftOutcome leftMass rightSupport)
            (fpdProductSupport leftRest rightSupport))
        = qnfMul (qnfAdd leftMass (fpdMassSum leftRest))
            (fpdMassSum rightSupport)
      rw [fpdMassSumCat (fpdProductRow leftOutcome leftMass rightSupport)
          (fpdProductSupport leftRest rightSupport),
        fpdProductRowMassSum leftOutcome leftMass rightSupport,
        fpdProductSupportMassSum leftRest rightSupport,
        qnfMulRightDistrib leftMass (fpdMassSum leftRest)
          (fpdMassSum rightSupport)]

/-- **Independent product** of two distributions on the paired outcome space. -/
def fpdProduct (mu nu : FpDist) : FpDist :=
  fpdNormalise { support := fpdProductSupport mu.support nu.support }

/-- The independent product preserves total mass one. -/
theorem fpdProductPreservesMassOne (mu nu : FpDist)
    (hMuOne : fpdMassSum mu.support = qnfOne)
    (hNuOne : fpdMassSum nu.support = qnfOne) :
    fpdMassSum (fpdProduct mu nu).support = qnfOne := by
  rw [fpdProduct,
    fpdNormaliseMassSum { support := fpdProductSupport mu.support nu.support },
    fpdProductSupportMassSum mu.support nu.support, hMuOne, hNuOne,
    qnfMulOneRight qnfOne]

/-- Keep only outcomes satisfying `predicate`. -/
def fpdFilter (predicate : Nat → Bool) :
    List (Nat × QnfRat) → List (Nat × QnfRat)
  | [] => []
  | (outcome, mass) :: rest =>
      match predicate outcome with
      | true => (outcome, mass) :: fpdFilter predicate rest
      | false => fpdFilter predicate rest

/-- **Condition** on `predicate`: keep matching outcomes, then renormalise by
the inverse of the kept mass. -/
def fpdCondition (predicate : Nat → Bool) (mu : FpDist) : FpDist :=
  fpdNormalise
    { support :=
        fpdScale (qnfInv (fpdMassSum (fpdFilter predicate mu.support)))
          (fpdFilter predicate mu.support) }

/-- Conditioning on a predicate with nonzero kept mass yields total mass one
(the field-inverse cancels). -/
theorem fpdConditionPreservesMassOne (predicate : Nat → Bool) (mu : FpDist)
    (hKeptNonzero : fpdMassSum (fpdFilter predicate mu.support) ≠ qnfZero) :
    fpdMassSum (fpdCondition predicate mu).support = qnfOne := by
  rw [fpdCondition,
    fpdNormaliseMassSum
      { support :=
          fpdScale (qnfInv (fpdMassSum (fpdFilter predicate mu.support)))
            (fpdFilter predicate mu.support) },
    fpdScaleMassSum (qnfInv (fpdMassSum (fpdFilter predicate mu.support)))
      (fpdFilter predicate mu.support),
    qnfInvMulCancels hKeptNonzero]

/-! ## T3 — expectation, its linearity, dirac expectation -/

/-- Expectation of a payoff over a support — `Σ mass · payoff outcome`. -/
def fpdExpectationList (payoff : Nat → QnfRat) :
    List (Nat × QnfRat) → QnfRat
  | [] => qnfZero
  | (outcome, mass) :: rest =>
      qnfAdd (qnfMul mass (payoff outcome)) (fpdExpectationList payoff rest)

/-- Expectation of a payoff over a distribution. -/
def fpdExpectation (payoff : Nat → QnfRat) (mu : FpDist) : QnfRat :=
  fpdExpectationList payoff mu.support

/-- **Dirac expectation**: `E_{δ a}[payoff] = payoff a`. -/
theorem fpdDiracExpectation (payoff : Nat → QnfRat) (outcome : Nat) :
    fpdExpectation payoff (fpdDirac outcome) = payoff outcome := by
  show qnfAdd (qnfMul qnfOne (payoff outcome)) qnfZero = payoff outcome
  rw [qnfAddZeroRight (qnfMul qnfOne (payoff outcome)),
    qnfMulOneLeft (payoff outcome)]

/-- Expectation is additive in the payoff. -/
theorem fpdExpectationAddPayoff (firstPayoff secondPayoff : Nat → QnfRat) :
    (support : List (Nat × QnfRat)) →
      fpdExpectationList
          (fun outcome => qnfAdd (firstPayoff outcome) (secondPayoff outcome))
          support =
        qnfAdd (fpdExpectationList firstPayoff support)
          (fpdExpectationList secondPayoff support)
  | [] => (qnfAddZeroRight qnfZero).symm
  | (outcome, mass) :: rest => by
      show qnfAdd (qnfMul mass (qnfAdd (firstPayoff outcome) (secondPayoff outcome)))
          (fpdExpectationList
            (fun inner => qnfAdd (firstPayoff inner) (secondPayoff inner)) rest)
        = qnfAdd (qnfAdd (qnfMul mass (firstPayoff outcome))
              (fpdExpectationList firstPayoff rest))
            (qnfAdd (qnfMul mass (secondPayoff outcome))
              (fpdExpectationList secondPayoff rest))
      rw [fpdExpectationAddPayoff firstPayoff secondPayoff rest,
        qnfMulLeftDistrib mass (firstPayoff outcome) (secondPayoff outcome),
        qnfAddMiddleFour (qnfMul mass (firstPayoff outcome))
          (qnfMul mass (secondPayoff outcome))
          (fpdExpectationList firstPayoff rest)
          (fpdExpectationList secondPayoff rest)]

/-- Expectation is homogeneous in the payoff. -/
theorem fpdExpectationScalePayoff (scalar : QnfRat) (payoff : Nat → QnfRat) :
    (support : List (Nat × QnfRat)) →
      fpdExpectationList (fun outcome => qnfMul scalar (payoff outcome)) support =
        qnfMul scalar (fpdExpectationList payoff support)
  | [] => (qnfMulZeroRight scalar).symm
  | (outcome, mass) :: rest => by
      show qnfAdd (qnfMul mass (qnfMul scalar (payoff outcome)))
          (fpdExpectationList (fun inner => qnfMul scalar (payoff inner)) rest)
        = qnfMul scalar (qnfAdd (qnfMul mass (payoff outcome))
            (fpdExpectationList payoff rest))
      rw [fpdExpectationScalePayoff scalar payoff rest,
        qnfMulLeftDistrib scalar (qnfMul mass (payoff outcome))
          (fpdExpectationList payoff rest),
        qnfMulLeftSwap mass scalar (payoff outcome)]

/-- **Expectation linearity**: `E[a·f + b·g] = a·E[f] + b·E[g]` on a fixed
distribution. -/
theorem fpdExpectationLinear (firstScalar secondScalar : QnfRat)
    (firstPayoff secondPayoff : Nat → QnfRat) (mu : FpDist) :
    fpdExpectation
        (fun outcome =>
          qnfAdd (qnfMul firstScalar (firstPayoff outcome))
            (qnfMul secondScalar (secondPayoff outcome)))
        mu =
      qnfAdd (qnfMul firstScalar (fpdExpectation firstPayoff mu))
        (qnfMul secondScalar (fpdExpectation secondPayoff mu)) := by
  show fpdExpectationList
      (fun outcome =>
        qnfAdd (qnfMul firstScalar (firstPayoff outcome))
          (qnfMul secondScalar (secondPayoff outcome)))
      mu.support
    = qnfAdd (qnfMul firstScalar (fpdExpectationList firstPayoff mu.support))
        (qnfMul secondScalar (fpdExpectationList secondPayoff mu.support))
  rw [fpdExpectationAddPayoff (fun outcome => qnfMul firstScalar (firstPayoff outcome))
      (fun outcome => qnfMul secondScalar (secondPayoff outcome)) mu.support,
    fpdExpectationScalePayoff firstScalar firstPayoff mu.support,
    fpdExpectationScalePayoff secondScalar secondPayoff mu.support]

/-! ## T3 — the equality decision and the congruence -/

/-- Structural `Bool` equality of two supports — outcomes by `Nat.beq`, masses
by `qnfBeq` (which IS rational equality on the canonical carrier). -/
def fpdSupportBeq :
    List (Nat × QnfRat) → List (Nat × QnfRat) → Bool
  | [], [] => true
  | [], _entry :: _rest => false
  | _entry :: _rest, [] => false
  | (leftOutcome, leftMass) :: leftRest, (rightOutcome, rightMass) :: rightRest =>
      Nat.beq leftOutcome rightOutcome && qnfBeq leftMass rightMass
        && fpdSupportBeq leftRest rightRest

/-- Support comparison is reflexive. -/
theorem fpdSupportBeqRefl : (support : List (Nat × QnfRat)) →
    fpdSupportBeq support support = true
  | [] => rfl
  | (outcome, mass) :: rest => by
      show (Nat.beq outcome outcome && qnfBeq mass mass
          && fpdSupportBeq rest rest) = true
      rw [qnfNatBeqSelfIsTrue outcome, qnfBeqSelfIsTrue mass,
        fpdSupportBeqRefl rest]
      rfl

/-- Support comparison is sound: `true` forces list equality. -/
theorem fpdSupportBeqSound : (leftSupport rightSupport : List (Nat × QnfRat)) →
    fpdSupportBeq leftSupport rightSupport = true → leftSupport = rightSupport
  | [], [], _ => rfl
  | [], _entry :: _rest, isBeqTrue => Bool.noConfusion isBeqTrue
  | _entry :: _rest, [], isBeqTrue => Bool.noConfusion isBeqTrue
  | (leftOutcome, leftMass) :: leftRest,
      (rightOutcome, rightMass) :: rightRest, isBeqTrue => by
      have hOutcome : leftOutcome = rightOutcome :=
        qnfNatEqOfBeqIsTrue
          (qnfBoolAndTrueGivesLeft (qnfBoolAndTrueGivesLeft isBeqTrue))
      have hMass : leftMass = rightMass :=
        (qnfBeqIffEq leftMass rightMass).mp
          (qnfBoolAndTrueGivesRight (qnfBoolAndTrueGivesLeft isBeqTrue))
      have hRest : leftRest = rightRest :=
        fpdSupportBeqSound leftRest rightRest
          (qnfBoolAndTrueGivesRight isBeqTrue)
      rw [hOutcome, hMass, hRest]

/-- **Distribution equality decision**: `qnfBeq`-compare the two normalised
supports. -/
def fpdDistEq (mu nu : FpDist) : Bool :=
  fpdSupportBeq (fpdNormalise mu).support (fpdNormalise nu).support

/-- `FpDist` equality follows from support equality (one `congrArg`). -/
theorem fpdEqOfSupportEq {mu nu : FpDist} (supportsEqual : mu.support = nu.support) :
    mu = nu :=
  Eq.rec
    (motive := fun targetSupport _ => mu = FpDist.mk targetSupport)
    rfl supportsEqual

/-- **Decision soundness**: `fpdDistEq` true forces the normalised
distributions equal. -/
theorem fpdDistEqSound {mu nu : FpDist} (isEqTrue : fpdDistEq mu nu = true) :
    fpdNormalise mu = fpdNormalise nu :=
  fpdEqOfSupportEq
    (fpdSupportBeqSound (fpdNormalise mu).support (fpdNormalise nu).support
      isEqTrue)

/-- **The distribution congruence**: two distributions are conv-equal exactly
when they share a normal form.  This is a genuine equivalence relation (it IS
`Eq` on normal forms) and it is precisely what `fpdDistEq` decides. -/
def FpConv (mu nu : FpDist) : Prop :=
  fpdNormalise mu = fpdNormalise nu

/-- `FpConv` is reflexive. -/
theorem fpConvRefl (mu : FpDist) : FpConv mu mu := rfl

/-- `FpConv` is symmetric. -/
theorem fpConvSymm {mu nu : FpDist} (areConv : FpConv mu nu) : FpConv nu mu :=
  areConv.symm

/-- `FpConv` is transitive. -/
theorem fpConvTrans {mu nu rho : FpDist}
    (firstConv : FpConv mu nu) (secondConv : FpConv nu rho) : FpConv mu rho :=
  firstConv.trans secondConv

/-- **Congruence soundness**: conv-equal distributions decide EQUAL. -/
theorem fpdConvSound {mu nu : FpDist} (areConv : FpConv mu nu) :
    fpdDistEq mu nu = true := by
  show fpdSupportBeq (fpdNormalise mu).support (fpdNormalise nu).support = true
  rw [areConv]
  exact fpdSupportBeqRefl (fpdNormalise nu).support

/-- **The refutation half**: distributions that decide EQUAL are conv-equal —
so `fpdDistEq` is EXACTLY `FpConv`, never over- or under-identifying. -/
theorem fpdConvComplete {mu nu : FpDist} (isEqTrue : fpdDistEq mu nu = true) :
    FpConv mu nu :=
  fpdDistEqSound isEqTrue

/-- The decision is EXACTLY the congruence. -/
theorem fpdDistEqIffConv (mu nu : FpDist) :
    fpdDistEq mu nu = true ↔ FpConv mu nu :=
  ⟨fpdConvComplete, fpdConvSound⟩

/-! ## T4 — the walls

The finite, decidable core above is complete and zero-axiom.  Two extensions
are genuinely out of reach on the QnfRat + finite-`List` substrate. -/

/-- WALLED — countably-infinite / continuous support.  A finite `List`
support cannot carry a geometric (or worse) tail: representing `P(n) = 2^{-n}`
needs the total `Σ 2^{-n} = 1` as a CONVERGENT SERIES in the completion of ℚ,
i.e. Bishop-real (`RegularReal`) L1 integration — a limit object no finite mass
list denotes.

Burned attack A (truncate-and-cap): keep the first `k` atoms and dump the tail
mass on one atom.  This changes the distribution (the capped atom's mass is
wrong for every finite `k`), so it is not the geometric law — it only ever
APPROXIMATES, and `fpdDistEq` correctly reports the approximants unequal.  No
finite `k` is the fixed point.

Burned attack B (symbolic tail entry): add a distinguished "tail" outcome whose
mass is a closed form `qnfSub qnfOne (partial sum)`.  This is a two-atom
regrouping, NOT the infinite distribution: expectation of an unbounded payoff
(`payoff n = qnfOfInt n`) over the true tail DIVERGES in ℚ, while the symbolic
entry gives a finite wrong answer.  The obstruction is exactly the missing
Bishop-L1 limit; `fpdExpectation` is a finite `qnfAdd` fold with no completion. -/
def fpdHasCountableSupport : Bool := false

/-- WALLED — the categorical Giry-monad laws + de Finetti exchangeability.
The finite join (a distribution-of-distributions flattened by
`fpdConvex`-style weighting) computes, but the MONAD LAWS (left/right unit and
associativity of the Kleisli composition at the Markov-category level) and
exchangeability are the deep structure.  This is the SAME walled node as the
copy-discard Markov PROP's `cdwHasMarkovCompleteness := false`
(`FreeCopyDiscard.lean`): reconstructing a row-stochastic channel from its
matrix.

Burned attack A (join as a `List`-of-`FpDist` weighted fold): defining
`join : FpDist-of-FpDist → FpDist` is easy, but the associativity law
`join ∘ map join = join ∘ join` is an equality of NORMAL FORMS over an
arbitrary pairing of outcomes; `fpdPairNat` is not associative-compatible
(`pair (pair a b) c ≠ pair a (pair b c)` as `Nat`s), so the two sides land on
different supports and `fpdDistEq` reports them unequal — the law fails at the
outcome-encoding layer, not the mass layer.

Burned attack B (de Finetti via a finite exchangeable prior): a finite mixture
of i.i.d. distributions is exchangeable, but the THEOREM (every exchangeable
sequence is such a mixture) quantifies over an infinite sequence and a mixing
MEASURE on the simplex — a continuous object walled by
`fpdHasCountableSupport` above.  The finite substrate proves the easy direction
(mixtures are exchangeable) and cannot state the converse. -/
def fpdHasGiryMonadLaws : Bool := false

/-! ## T5 — kernel `rfl` fires

Small (2–3 outcome) closed distributions; the whole normalise / arithmetic /
comparison pipeline reduces in the kernel. -/

set_option maxRecDepth 4096

/-- A fair coin as a convex `1/2`-mix of two diracs — total mass one, so it is
well-formed by kernel computation. -/
def fpdFairCoin : FpDist :=
  fpdConvex (qnfNormalize { numerator := 1, denominatorPredecessor := 1 })
    (fpdDirac 0) (fpdDirac 1)

/-- Fire: the fair coin is well-formed (masses nonneg, total one). -/
theorem fpdFireFairCoinWellFormed : fpdIsWellFormed fpdFairCoin = true := rfl

/-- Fire: the fair coin's total mass is exactly one. -/
theorem fpdFireFairCoinMassOne : fpdMassSum fpdFairCoin.support = qnfOne := rfl

/-- Fire: expectation of `payoff n = n/1` over the fair coin is `1/2` — the
mean of `{0, 1}`. -/
theorem fpdFireFairCoinExpectation :
    fpdExpectation (fun outcome => qnfOfInt (Int.ofNat outcome)) fpdFairCoin =
      qnfNormalize { numerator := 1, denominatorPredecessor := 1 } := rfl

/-- Fire: two distributions equal up to reordering AND duplicate-merge decide
EQUAL — `[(1,1/3),(0,1/3),(0,1/3)]` and `[(0,2/3),(1,1/3)]` share a normal
form. -/
theorem fpdFireReorderMergeEqual :
    fpdDistEq
        { support :=
            [(1, qnfNormalize { numerator := 1, denominatorPredecessor := 2 }),
             (0, qnfNormalize { numerator := 1, denominatorPredecessor := 2 }),
             (0, qnfNormalize { numerator := 1, denominatorPredecessor := 2 })] }
        { support :=
            [(0, qnfNormalize { numerator := 2, denominatorPredecessor := 2 }),
             (1, qnfNormalize { numerator := 1, denominatorPredecessor := 2 })] }
      = true := rfl

/-- Fire: a genuinely different distribution decides NOT equal — swapping the
masses of outcomes `0` and `1`. -/
theorem fpdFireDifferentNotEqual :
    fpdDistEq
        { support :=
            [(0, qnfNormalize { numerator := 2, denominatorPredecessor := 2 }),
             (1, qnfNormalize { numerator := 1, denominatorPredecessor := 2 })] }
        { support :=
            [(0, qnfNormalize { numerator := 1, denominatorPredecessor := 2 }),
             (1, qnfNormalize { numerator := 2, denominatorPredecessor := 2 })] }
      = false := rfl

/-- Fire: the product of two 2-point distributions has four outcomes with
product masses — `mu = {0,1}` each mass `1/2`, `nu = {0:1/3, 1:2/3}`; the four
product masses are `1/2·1/3 = 1/6`, `1/2·2/3 = 1/3`, `1/2·1/3 = 1/6`,
`1/2·2/3 = 1/3`, at the distinct paired outcomes `fpdPairNat` gives (1, 2, 3,
6), sorted. -/
theorem fpdFireProductFourOutcomes :
    (fpdProduct
        { support :=
            [(0, qnfNormalize { numerator := 1, denominatorPredecessor := 1 }),
             (1, qnfNormalize { numerator := 1, denominatorPredecessor := 1 })] }
        { support :=
            [(0, qnfNormalize { numerator := 1, denominatorPredecessor := 2 }),
             (1, qnfNormalize { numerator := 2, denominatorPredecessor := 2 })] }).support
      = [(1, qnfNormalize { numerator := 1, denominatorPredecessor := 5 }),
         (2, qnfNormalize { numerator := 1, denominatorPredecessor := 5 }),
         (3, qnfNormalize { numerator := 1, denominatorPredecessor := 2 }),
         (6, qnfNormalize { numerator := 1, denominatorPredecessor := 2 })] := rfl

/-- Fire: the product's total mass is one (independence preserves
normalisation) — `(1/2+1/2)·(1/3+2/3) = 1`. -/
theorem fpdFireProductMassOne :
    fpdMassSum
        (fpdProduct
          { support :=
              [(0, qnfNormalize { numerator := 1, denominatorPredecessor := 1 }),
               (1, qnfNormalize { numerator := 1, denominatorPredecessor := 1 })] }
          { support :=
              [(0, qnfNormalize { numerator := 1, denominatorPredecessor := 2 }),
               (1, qnfNormalize { numerator := 2, denominatorPredecessor := 2 })] }).support
      = qnfOne := rfl

/-! ## T6 — content markers -/

/-- DECIDED: the finite ℚ-pmf layer has a mass-sum-preserving normalisation and
each operation (`fpdMap` / `fpdConvex` / `fpdProduct` / `fpdCondition`) carries
total mass one (`fpd*PreservesMassOne`), all zero-axiom on the QnfRat kit. -/
def fpdHasMassPreservation : Bool := true

/-- DECIDED: distribution equality up to reordering / duplicate-merge is
decidable (`fpdDistEq`) and is EXACTLY the normal-form congruence
(`fpdDistEqIffConv`), with expectation linearity (`fpdExpectationLinear`) and
dirac expectation (`fpdDiracExpectation`). -/
def fpdHasDecidableEquality : Bool := true

end FX1Poly.ComputerAlgebra
