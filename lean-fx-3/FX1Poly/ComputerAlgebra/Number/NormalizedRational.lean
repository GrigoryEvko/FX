import FX1Poly.ComputerAlgebra.Number.RationalDistance

/-! # NormalizedRational — the canonical-NF ℚ carrier (NUM-Q-7)

The setoid layer (`RationalPair`) already ships the whole ℚ corpus: the
cross-multiplication setoid, exact field operations, the gcd normal form
`normalize` with its coprimality certificate, and THE UNIQUENESS theorem
`eqOfReducedOfDenotesSame` (reduced pairs denoting the same rational are
EQUAL).  What a structural-equality consumer (the Gröbner ideal-membership
checker's coefficient comparison, a hash key, a decision-procedure table)
still lacks is a CARRIER on which plain `Eq` — and a plain structural
`Bool` comparison — IS rational equality.

This module packages exactly that:

  * `QnfRat` — a `RationalPair` bundled with its reducedness certificate.
    Lean's definitional proof irrelevance plus structure eta make equality
    of the bundle equality of the pair (`qnfEqOfPairEq`), so byte equality
    on the carrier coincides with rational equality
    (`qnfEqIffPairsDenoteSame`).
  * `qnfNormalize` — raw pair to canonical carrier; THE HEADLINE
    `qnfNormalizeUnique`: cross-multiplication-equal raw pairs normalize to
    the SAME `QnfRat` (plain `Eq`), with converse and fixed-point/round-trip
    laws.
  * Ring operations as raw-op-then-normalize (`qnfAdd`/`qnfMul`/`qnfSub`;
    `qnfNeg` and `qnfInv` stay canonical WITHOUT renormalizing — negation
    keeps the magnitude, inversion swaps a coprime pair), with EVERY law in
    plain `Eq`: transported through `qnfNormalizeUnique` from the setoid
    laws, never re-proved.
  * The field witness `qnfMulInvCancels` on `value ≠ qnfZero` — on this
    carrier nonzeroness IS a plain disequality.
  * Structural Boolean equality `qnfBeq` with `qnfBeqIffEq` and a manual
    `DecidableEq` (`qnfDecEq`) — the Gröbner-Q successor compares
    coefficients by `==` and rewrites by `=` with zero setoid plumbing.
  * Kernel-`rfl` fires pinning normalization, sign handling, the zero
    collapse, arithmetic, and inverse cancellation on closed values.

Route note for the Gröbner-Q successor: instantiate the polynomial
coefficient type at `QnfRat`, use `qnfBeq`/`qnfDecEq` for the coefficient
scan (structural, no setoid), `qnfAdd`/`qnfMul`/`qnfNeg` for arithmetic, and
discharge the coefficient-field obligations with the `qnf*` laws below; the
zero-coefficient test is `qnfBeq · qnfZero` = numerator-is-zero by
`qnfEqZeroOfNumeratorZero`.

## Zero-axiom

Structure eta + definitional proof irrelevance (`qnfEqOfPairEq` is one
explicit-motive `Eq.rec`, no match compiler), `congrArg`/`Eq.trans` chains,
full-enum constructor matches.  No `axiom`, `sorry`, `propext`,
`Quot.sound`, `Classical`, `native_decide`, `omega`, no `WellFounded.fix`.
Per-declaration gated in
`FX1PolyAudit/ComputerAlgebra/Number/NormalizedRational.lean`. -/

namespace FX1Poly.ComputerAlgebra

open RationalPair

/-! ## The canonical carrier (T1) -/

/-- A rational in canonical normal form: a `RationalPair` (numerator
`Int`, structurally positive denominator `denominatorPredecessor + 1`)
carrying its reducedness certificate.  The certificate is a `Prop` field —
definitionally irrelevant — so equality of `QnfRat` values IS equality of
the underlying pairs, and the zero case is forced to `0/1` by reducedness
(`gcd 0 d = d = 1`): no separate sign-flag normalization is needed, the
`Int` numerator already has a unique zero. -/
structure QnfRat where
  reducedPair : RationalPair
  hasReducedShape : RationalPair.IsReduced reducedPair

/-- Read the canonical representative back as a raw pair. -/
def qnfToRawPair (value : QnfRat) : RationalPair :=
  value.reducedPair

/-- **Bundle equality from pair equality** — one explicit-motive `Eq.rec`;
the base case closes by structure eta plus definitional proof irrelevance
(no match compiler, no `Subtype` plumbing). -/
theorem qnfEqOfPairEq {leftValue rightValue : QnfRat}
    (pairsEqual : leftValue.reducedPair = rightValue.reducedPair) :
    leftValue = rightValue :=
  Eq.rec
    (motive := fun targetPair _ =>
      ∀ targetShape : RationalPair.IsReduced targetPair,
        leftValue = QnfRat.mk targetPair targetShape)
    (fun _ => rfl)
    pairsEqual
    rightValue.hasReducedShape

/-- Pair equality from componentwise equality — two `congrArg` steps over
the constructor, closed by structure eta (the shape of
`eqOfReducedOfDenotesSame`'s final step). -/
theorem qnfPairEqOfComponentsEq {leftPair rightPair : RationalPair}
    (numeratorsEqual : leftPair.numerator = rightPair.numerator)
    (predecessorsEqual :
      leftPair.denominatorPredecessor = rightPair.denominatorPredecessor) :
    leftPair = rightPair :=
  (congrArg
      (fun numerator =>
        RationalPair.mk numerator leftPair.denominatorPredecessor)
      numeratorsEqual).trans
    (congrArg (RationalPair.mk rightPair.numerator) predecessorsEqual)

/-- Canonical carriers whose pairs denote the same rational are EQUAL —
the setoid-level uniqueness theorem lands as plain `Eq` here. -/
theorem qnfEqOfPairsDenoteSame {leftValue rightValue : QnfRat}
    (pairsDenoteSame :
      DenotesSameAs leftValue.reducedPair rightValue.reducedPair) :
    leftValue = rightValue :=
  qnfEqOfPairEq
    (eqOfReducedOfDenotesSame leftValue.hasReducedShape
      rightValue.hasReducedShape pairsDenoteSame)

/-- Equal canonical carriers have setoid-equal pairs — transport
reflexivity along the equality with an explicit motive. -/
theorem qnfPairsDenoteSameOfEq {leftValue rightValue : QnfRat}
    (areEqual : leftValue = rightValue) :
    DenotesSameAs leftValue.reducedPair rightValue.reducedPair :=
  Eq.rec
    (motive := fun targetValue _ =>
      DenotesSameAs leftValue.reducedPair targetValue.reducedPair)
    (denotesSameAsRefl leftValue.reducedPair)
    areEqual

/-- **Byte equality IS rational equality** on the canonical carrier — the
T1 acceptance bar, packaged. -/
theorem qnfEqIffPairsDenoteSame (leftValue rightValue : QnfRat) :
    leftValue = rightValue ↔
      DenotesSameAs leftValue.reducedPair rightValue.reducedPair :=
  ⟨qnfPairsDenoteSameOfEq, qnfEqOfPairsDenoteSame⟩

/-! ## Normalization and THE HEADLINE (T2) -/

/-- Normalize a raw pair onto the canonical carrier — the shipped gcd
normal form (`RationalPair.normalize`, counting Euclid on structural fuel)
bundled with its coprimality certificate. -/
def qnfNormalize (rawValue : RationalPair) : QnfRat :=
  { reducedPair := normalize rawValue
    hasReducedShape := normalizeIsCoprime rawValue }

/-- **THE HEADLINE — normalization uniqueness**: raw pairs that are
cross-multiplication equal normalize to the SAME canonical carrier, as
plain `Eq`.  This is what turns every setoid law into a structural-equality
law downstream. -/
theorem qnfNormalizeUnique {leftRaw rightRaw : RationalPair}
    (denotesSame : DenotesSameAs leftRaw rightRaw) :
    qnfNormalize leftRaw = qnfNormalize rightRaw :=
  qnfEqOfPairEq (normalizeEqOfDenotesSameAs denotesSame)

/-- The converse: equal normal forms denote the same rational. -/
theorem qnfDenotesSameOfNormalizeEq {leftRaw rightRaw : RationalPair}
    (normalsEqual : qnfNormalize leftRaw = qnfNormalize rightRaw) :
    DenotesSameAs leftRaw rightRaw :=
  denotesSameAsOfNormalizeEq (congrArg QnfRat.reducedPair normalsEqual)

/-- The characterization: the decidable cross-multiplication setoid IS
equality of canonical carriers. -/
theorem qnfNormalizeEqIffDenotesSame (leftRaw rightRaw : RationalPair) :
    DenotesSameAs leftRaw rightRaw ↔
      qnfNormalize leftRaw = qnfNormalize rightRaw :=
  ⟨qnfNormalizeUnique, qnfDenotesSameOfNormalizeEq⟩

/-- **Round-trip / fixed point**: reading the pair back out of a canonical
carrier and normalizing returns the same carrier — already-canonical
values are fixed points of `qnfNormalize`. -/
theorem qnfNormalizeFixesCanonical (value : QnfRat) :
    qnfNormalize (qnfToRawPair value) = value :=
  qnfEqOfPairEq (normalizeOfReducedIsSelf value.hasReducedShape)

/-! ## Constants and the ℤ embedding -/

/-- The canonical zero: `0/1` — reducedness is `gcd 0 1 = 1`, kernel
computation. -/
def qnfZero : QnfRat :=
  { reducedPair := zeroRational, hasReducedShape := rfl }

/-- The canonical one: `1/1` — reducedness is `gcd 1 1 = 1`, kernel
computation. -/
def qnfOne : QnfRat :=
  { reducedPair := oneRational, hasReducedShape := rfl }

/-- Every integer pair `value/1` is reduced — the gcd divides `1`, and a
left factor of one is one. -/
theorem qnfIntPairIsReduced (value : Int) :
    RationalPair.IsReduced (rationalOfInt value) :=
  match natGcdDividesRight value.natAbs 1 with
  | ⟨_, oneEquation⟩ => natLeftFactorOfProductEqOne oneEquation.symm

/-- The canonical ℤ embedding: `value/1`, no normalization pass needed. -/
def qnfOfInt (value : Int) : QnfRat :=
  { reducedPair := rationalOfInt value
    hasReducedShape := qnfIntPairIsReduced value }

/-- Nontriviality: the canonical zero and one are distinct — their
numerators disagree at the second constructor layer. -/
theorem qnfZeroNeOne : qnfZero ≠ qnfOne :=
  fun areEqual =>
    Int.noConfusion
      (congrArg (fun value => value.reducedPair.numerator) areEqual)
      (fun magnitudesEqual => Nat.noConfusion magnitudesEqual)

/-! ## Ring operations (T3): raw op, then normalize

Negation and inversion are the two operations that stay canonical WITHOUT
a normalization pass — negation preserves the numerator magnitude, and
inversion swaps an already-coprime pair — so they are defined directly and
their closure is a transported coprimality certificate, not a gcd run. -/

/-- Canonical addition: exact raw addition, then normalize. -/
def qnfAdd (leftValue rightValue : QnfRat) : QnfRat :=
  qnfNormalize (addExact leftValue.reducedPair rightValue.reducedPair)

/-- Canonical multiplication: exact raw multiplication, then normalize. -/
def qnfMul (leftValue rightValue : QnfRat) : QnfRat :=
  qnfNormalize (mulExact leftValue.reducedPair rightValue.reducedPair)

/-- Canonical subtraction: exact raw subtraction, then normalize. -/
def qnfSub (leftValue rightValue : QnfRat) : QnfRat :=
  qnfNormalize (subExact leftValue.reducedPair rightValue.reducedPair)

/-- Negation preserves the magnitude — all three `Int.neg` arms are
definitional. -/
theorem qnfIntNegPreservesNatAbs :
    ∀ value : Int, (-value).natAbs = value.natAbs
  | .ofNat 0 => rfl
  | .ofNat (_ + 1) => rfl
  | .negSucc _ => rfl

/-- Negation keeps the reduced shape — transport the coprimality along the
magnitude-preservation equation. -/
theorem qnfNegExactKeepsReducedShape {rawValue : RationalPair}
    (hasReducedShape : RationalPair.IsReduced rawValue) :
    RationalPair.IsReduced (negExact rawValue) :=
  (congrArg (natGcd · (rawValue.denominatorPredecessor + 1))
      (qnfIntNegPreservesNatAbs rawValue.numerator)).trans
    hasReducedShape

/-- Canonical negation — no normalization pass. -/
def qnfNeg (value : QnfRat) : QnfRat :=
  { reducedPair := negExact value.reducedPair
    hasReducedShape := qnfNegExactKeepsReducedShape value.hasReducedShape }

/-- Subtraction IS addition of the negation — definitional on both layers. -/
theorem qnfSubEqAddNeg (leftValue rightValue : QnfRat) :
    qnfSub leftValue rightValue = qnfAdd leftValue (qnfNeg rightValue) :=
  rfl

/-! ## The ring laws in plain `Eq` — transported, never re-proved

Every law is ONE application of `qnfNormalizeUnique` to a setoid-law chain;
where an operand is itself a normalized result, the congruence lemmas strip
the inner `normalize` through `normalizeDenotesSame`, and identity laws
close through the canonical fixed point. -/

/-- Addition is commutative. -/
theorem qnfAddComm (leftValue rightValue : QnfRat) :
    qnfAdd leftValue rightValue = qnfAdd rightValue leftValue :=
  qnfNormalizeUnique
    (addExactComm leftValue.reducedPair rightValue.reducedPair)

/-- Addition is associative — strip the inner normal forms on both sides
around the setoid associativity. -/
theorem qnfAddAssoc (firstValue middleValue lastValue : QnfRat) :
    qnfAdd (qnfAdd firstValue middleValue) lastValue =
      qnfAdd firstValue (qnfAdd middleValue lastValue) :=
  qnfNormalizeUnique
    (denotesSameAsTrans
      (addExactCongrLeft lastValue.reducedPair
        (normalizeDenotesSame
          (addExact firstValue.reducedPair middleValue.reducedPair)))
      (denotesSameAsTrans
        (addExactAssoc firstValue.reducedPair middleValue.reducedPair
          lastValue.reducedPair)
        (addExactCongrRight firstValue.reducedPair
          (denotesSameAsSymm
            (normalizeDenotesSame
              (addExact middleValue.reducedPair lastValue.reducedPair))))))

/-- Zero is a right additive identity. -/
theorem qnfAddZeroRight (value : QnfRat) : qnfAdd value qnfZero = value :=
  (qnfNormalizeUnique (addExactZeroRight value.reducedPair)).trans
    (qnfNormalizeFixesCanonical value)

/-- Zero is a left additive identity. -/
theorem qnfAddZeroLeft (value : QnfRat) : qnfAdd qnfZero value = value :=
  (qnfNormalizeUnique (addExactZeroLeft value.reducedPair)).trans
    (qnfNormalizeFixesCanonical value)

/-- Negation is a right additive inverse. -/
theorem qnfAddNegRight (value : QnfRat) :
    qnfAdd value (qnfNeg value) = qnfZero :=
  (qnfNormalizeUnique (addExactNegRight value.reducedPair)).trans
    (qnfNormalizeFixesCanonical qnfZero)

/-- Negation is a left additive inverse — commute and reuse. -/
theorem qnfAddNegLeft (value : QnfRat) :
    qnfAdd (qnfNeg value) value = qnfZero :=
  (qnfAddComm (qnfNeg value) value).trans (qnfAddNegRight value)

/-- Multiplication is commutative. -/
theorem qnfMulComm (leftValue rightValue : QnfRat) :
    qnfMul leftValue rightValue = qnfMul rightValue leftValue :=
  qnfNormalizeUnique
    (mulExactComm leftValue.reducedPair rightValue.reducedPair)

/-- Multiplication is associative — strip the inner normal forms on both
sides around the setoid associativity. -/
theorem qnfMulAssoc (firstValue middleValue lastValue : QnfRat) :
    qnfMul (qnfMul firstValue middleValue) lastValue =
      qnfMul firstValue (qnfMul middleValue lastValue) :=
  qnfNormalizeUnique
    (denotesSameAsTrans
      (mulExactCongrLeft lastValue.reducedPair
        (normalizeDenotesSame
          (mulExact firstValue.reducedPair middleValue.reducedPair)))
      (denotesSameAsTrans
        (mulExactAssoc firstValue.reducedPair middleValue.reducedPair
          lastValue.reducedPair)
        (mulExactCongrRight firstValue.reducedPair
          (denotesSameAsSymm
            (normalizeDenotesSame
              (mulExact middleValue.reducedPair lastValue.reducedPair))))))

/-- One is a right multiplicative identity. -/
theorem qnfMulOneRight (value : QnfRat) : qnfMul value qnfOne = value :=
  (qnfNormalizeUnique (mulExactOneRight value.reducedPair)).trans
    (qnfNormalizeFixesCanonical value)

/-- One is a left multiplicative identity. -/
theorem qnfMulOneLeft (value : QnfRat) : qnfMul qnfOne value = value :=
  (qnfNormalizeUnique (mulExactOneLeft value.reducedPair)).trans
    (qnfNormalizeFixesCanonical value)

/-- Multiplication distributes over addition on the left. -/
theorem qnfMulLeftDistrib (factor leftSummand rightSummand : QnfRat) :
    qnfMul factor (qnfAdd leftSummand rightSummand) =
      qnfAdd (qnfMul factor leftSummand) (qnfMul factor rightSummand) :=
  qnfNormalizeUnique
    (denotesSameAsTrans
      (mulExactCongrRight factor.reducedPair
        (normalizeDenotesSame
          (addExact leftSummand.reducedPair rightSummand.reducedPair)))
      (denotesSameAsTrans
        (mulExactLeftDistrib factor.reducedPair leftSummand.reducedPair
          rightSummand.reducedPair)
        (addExactRespectsDenotesSameAs
          (denotesSameAsSymm
            (normalizeDenotesSame
              (mulExact factor.reducedPair leftSummand.reducedPair)))
          (denotesSameAsSymm
            (normalizeDenotesSame
              (mulExact factor.reducedPair rightSummand.reducedPair))))))

/-- Multiplication distributes over addition on the right. -/
theorem qnfMulRightDistrib (leftSummand rightSummand factor : QnfRat) :
    qnfMul (qnfAdd leftSummand rightSummand) factor =
      qnfAdd (qnfMul leftSummand factor) (qnfMul rightSummand factor) :=
  qnfNormalizeUnique
    (denotesSameAsTrans
      (mulExactCongrLeft factor.reducedPair
        (normalizeDenotesSame
          (addExact leftSummand.reducedPair rightSummand.reducedPair)))
      (denotesSameAsTrans
        (mulExactRightDistrib factor.reducedPair leftSummand.reducedPair
          rightSummand.reducedPair)
        (addExactRespectsDenotesSameAs
          (denotesSameAsSymm
            (normalizeDenotesSame
              (mulExact leftSummand.reducedPair factor.reducedPair)))
          (denotesSameAsSymm
            (normalizeDenotesSame
              (mulExact rightSummand.reducedPair factor.reducedPair))))))

/-! ## The inverse and the field witness (T4a)

On the canonical carrier apartness collapses to a plain disequality: a
reduced pair with zero numerator IS `0/1` (its reducedness forces the
denominator to one), so `value ≠ qnfZero` reads directly on the numerator. -/

/-- A reduced pair with zero numerator IS the zero pair — reducedness
collapses the denominator: `gcd 0 (d+1) = d+1 = 1`.  No `Int` constructor
split needed. -/
theorem qnfReducedWithZeroNumeratorIsZeroRational {rawValue : RationalPair}
    (hasReducedShape : RationalPair.IsReduced rawValue)
    (numeratorIsZero : rawValue.numerator = 0) :
    rawValue = zeroRational :=
  qnfPairEqOfComponentsEq numeratorIsZero
    (Nat.succ.inj
      ((congrArg
          (fun (numerator : Int) =>
            natGcd numerator.natAbs (rawValue.denominatorPredecessor + 1))
          numeratorIsZero).symm.trans
        hasReducedShape))

/-- A canonical carrier with zero numerator IS the canonical zero. -/
theorem qnfEqZeroOfNumeratorZero {value : QnfRat}
    (numeratorIsZero : value.reducedPair.numerator = 0) : value = qnfZero :=
  qnfEqOfPairEq
    (qnfReducedWithZeroNumeratorIsZeroRational value.hasReducedShape
      numeratorIsZero)

/-- Nonzero carriers have nonzero numerators — the contrapositive of the
zero collapse. -/
theorem qnfNumeratorNonzeroOfNeZero {value : QnfRat}
    (isNonzero : value ≠ qnfZero) : value.reducedPair.numerator ≠ 0 :=
  fun numeratorIsZero => isNonzero (qnfEqZeroOfNumeratorZero numeratorIsZero)

/-- A nonzero numerator makes the pair apart from zero — the bridge into
the setoid-level field law: a denotes-zero equation collapses the numerator
through the unit denominator. -/
theorem qnfIsApartFromZeroOfNumeratorNonzero {rawValue : RationalPair}
    (isNumeratorNonzero : rawValue.numerator ≠ 0) :
    IsApartFromZero rawValue :=
  fun denotesZero =>
    isNumeratorNonzero
      ((intMulOne rawValue.numerator).symm.trans
        (denotesZero.trans (intZeroMul (denominatorInt rawValue))))

/-- Inversion keeps the reduced shape — the inverse of a coprime pair swaps
the pair, and the gcd is commutative; the zero arm returns the (reduced)
zero pair. -/
theorem qnfInvExactKeepsReducedShape : ∀ {rawValue : RationalPair},
    RationalPair.IsReduced rawValue →
      RationalPair.IsReduced (invExact rawValue)
  | ⟨.ofNat 0, _⟩, _ => rfl
  | ⟨.ofNat (magnitudePredecessor + 1), denominatorPredecessor⟩,
      hasReducedShape =>
      (natGcdComm (denominatorPredecessor + 1)
          (magnitudePredecessor + 1)).trans
        hasReducedShape
  | ⟨.negSucc magnitudePredecessor, denominatorPredecessor⟩,
      hasReducedShape =>
      (natGcdComm (denominatorPredecessor + 1)
          (magnitudePredecessor + 1)).trans
        hasReducedShape

/-- Canonical inversion — swap the coprime pair, sign to the numerator; no
normalization pass.  Total, with the canonical zero as junk at zero. -/
def qnfInv (value : QnfRat) : QnfRat :=
  { reducedPair := invExact value.reducedPair
    hasReducedShape := qnfInvExactKeepsReducedShape value.hasReducedShape }

/-- **The field witness**: a nonzero canonical rational times its inverse
IS one, in plain `Eq`. -/
theorem qnfMulInvCancels {value : QnfRat} (isNonzero : value ≠ qnfZero) :
    qnfMul value (qnfInv value) = qnfOne :=
  (qnfNormalizeUnique
      (mulExactInvRight
        (qnfIsApartFromZeroOfNumeratorNonzero
          (qnfNumeratorNonzeroOfNeZero isNonzero)))).trans
    (qnfNormalizeFixesCanonical qnfOne)

/-- The field witness, left orientation — commute and reuse. -/
theorem qnfInvMulCancels {value : QnfRat} (isNonzero : value ≠ qnfZero) :
    qnfMul (qnfInv value) value = qnfOne :=
  (qnfMulComm (qnfInv value) value).trans (qnfMulInvCancels isNonzero)

/-! ## Structural Boolean equality and decidable equality (T4b)

Hand-rolled, self-contained: the `Bool` comparison is componentwise
`Nat.beq` (through a per-constructor `Int` comparator), and the equivalence
with `Eq` rides the carrier's byte-equality property.  Derived `BEq` /
`DecidableEq` instances are avoided (match-compiler leak risk); the
instances below wrap the manual definitions. -/

/-- `Nat.beq` is reflexively true — structural induction, both step arms
definitional. -/
theorem qnfNatBeqSelfIsTrue : ∀ value : Nat, Nat.beq value value = true
  | 0 => rfl
  | valuePredecessor + 1 => qnfNatBeqSelfIsTrue valuePredecessor

/-- `Nat.beq` at `true` gives equality — full-enum structural induction. -/
theorem qnfNatEqOfBeqIsTrue : ∀ {leftValue rightValue : Nat},
    Nat.beq leftValue rightValue = true → leftValue = rightValue
  | 0, 0, _ => rfl
  | 0, _ + 1, isBeqTrue => Bool.noConfusion isBeqTrue
  | _ + 1, 0, isBeqTrue => Bool.noConfusion isBeqTrue
  | _ + 1, _ + 1, isBeqTrue =>
      congrArg Nat.succ (qnfNatEqOfBeqIsTrue isBeqTrue)

/-- Structural `Int` comparison — sign constructors first, magnitudes by
`Nat.beq`. -/
def qnfIntBeq : Int → Int → Bool
  | .ofNat leftMagnitude, .ofNat rightMagnitude =>
      Nat.beq leftMagnitude rightMagnitude
  | .ofNat _, .negSucc _ => false
  | .negSucc _, .ofNat _ => false
  | .negSucc leftPredecessor, .negSucc rightPredecessor =>
      Nat.beq leftPredecessor rightPredecessor

/-- `qnfIntBeq` is reflexively true. -/
theorem qnfIntBeqSelfIsTrue : ∀ value : Int, qnfIntBeq value value = true
  | .ofNat magnitude => qnfNatBeqSelfIsTrue magnitude
  | .negSucc predecessor => qnfNatBeqSelfIsTrue predecessor

/-- `qnfIntBeq` at `true` gives equality — mixed-sign arms refute on the
`Bool`, same-sign arms lift the `Nat` equality through the constructor. -/
theorem qnfIntEqOfBeqIsTrue : ∀ {leftValue rightValue : Int},
    qnfIntBeq leftValue rightValue = true → leftValue = rightValue
  | .ofNat _, .ofNat _, isBeqTrue =>
      congrArg Int.ofNat (qnfNatEqOfBeqIsTrue isBeqTrue)
  | .ofNat _, .negSucc _, isBeqTrue => Bool.noConfusion isBeqTrue
  | .negSucc _, .ofNat _, isBeqTrue => Bool.noConfusion isBeqTrue
  | .negSucc _, .negSucc _, isBeqTrue =>
      congrArg Int.negSucc (qnfNatEqOfBeqIsTrue isBeqTrue)

/-- A true conjunction has a true left conjunct — `false && _` is
definitionally `false`. -/
theorem qnfBoolAndTrueGivesLeft : ∀ {leftFlag rightFlag : Bool},
    (leftFlag && rightFlag) = true → leftFlag = true
  | true, _, _ => rfl
  | false, _, isConjunctionTrue => Bool.noConfusion isConjunctionTrue

/-- A true conjunction has a true right conjunct — `true && b` is
definitionally `b`. -/
theorem qnfBoolAndTrueGivesRight : ∀ {leftFlag rightFlag : Bool},
    (leftFlag && rightFlag) = true → rightFlag = true
  | true, _, isConjunctionTrue => isConjunctionTrue
  | false, _, isConjunctionTrue => Bool.noConfusion isConjunctionTrue

/-- **Structural Boolean equality** on the canonical carrier — numerator
comparator AND denominator comparator, nothing else.  Because the carrier
is canonical, this IS rational equality (`qnfBeqIffEq`). -/
def qnfBeq (leftValue rightValue : QnfRat) : Bool :=
  qnfIntBeq leftValue.reducedPair.numerator
      rightValue.reducedPair.numerator &&
    Nat.beq leftValue.reducedPair.denominatorPredecessor
      rightValue.reducedPair.denominatorPredecessor

/-- `qnfBeq` is reflexively true — both component comparators are. -/
theorem qnfBeqSelfIsTrue (value : QnfRat) : qnfBeq value value = true :=
  (congrArg
      (fun leftFlag =>
        leftFlag &&
          Nat.beq value.reducedPair.denominatorPredecessor
            value.reducedPair.denominatorPredecessor)
      (qnfIntBeqSelfIsTrue value.reducedPair.numerator)).trans
    (qnfNatBeqSelfIsTrue value.reducedPair.denominatorPredecessor)

/-- **Structural `==` IS rational `=`** on the canonical carrier — the
Gröbner coefficient scan's acceptance bar. -/
theorem qnfBeqIffEq (leftValue rightValue : QnfRat) :
    qnfBeq leftValue rightValue = true ↔ leftValue = rightValue :=
  Iff.intro
    (fun isBeqTrue =>
      qnfEqOfPairEq
        (qnfPairEqOfComponentsEq
          (qnfIntEqOfBeqIsTrue (qnfBoolAndTrueGivesLeft isBeqTrue))
          (qnfNatEqOfBeqIsTrue (qnfBoolAndTrueGivesRight isBeqTrue))))
    (fun areEqual =>
      Eq.rec
        (motive := fun targetValue _ => qnfBeq leftValue targetValue = true)
        (qnfBeqSelfIsTrue leftValue)
        areEqual)

/-- Manual decidable equality — componentwise `Int.decEq` / `Nat.decEq`
(both clean), refutations by projection congruence. -/
def qnfDecEq (leftValue rightValue : QnfRat) :
    Decidable (leftValue = rightValue) :=
  match Int.decEq leftValue.reducedPair.numerator
      rightValue.reducedPair.numerator with
  | .isFalse numeratorsDiffer =>
      .isFalse
        (fun areEqual =>
          numeratorsDiffer
            (congrArg (fun value => value.reducedPair.numerator) areEqual))
  | .isTrue numeratorsEqual =>
      match Nat.decEq leftValue.reducedPair.denominatorPredecessor
          rightValue.reducedPair.denominatorPredecessor with
      | .isFalse predecessorsDiffer =>
          .isFalse
            (fun areEqual =>
              predecessorsDiffer
                (congrArg
                  (fun value => value.reducedPair.denominatorPredecessor)
                  areEqual))
      | .isTrue predecessorsEqual =>
          .isTrue
            (qnfEqOfPairEq
              (qnfPairEqOfComponentsEq numeratorsEqual predecessorsEqual))

/-- The `==` instance — structural comparison. -/
instance instBEqQnfRat : BEq QnfRat := ⟨qnfBeq⟩

/-- The decidable-equality instance — manual, not derived. -/
instance instDecidableEqQnfRat : DecidableEq QnfRat := qnfDecEq

/-! ## Kernel `rfl` fires (T5)

Closed-value pins: the whole normalize/arithmetic pipeline — counting
divider, structural-fuel gcd, magnitude quotient — reduces inside the
kernel, so every pin is a bare `rfl`.  The counting divider recurses once
per dividend unit, so the `30/30` inverse pin needs the raised recursion
depth. -/

set_option maxRecDepth 8192

/-- Fire: `2/4` and `1/2` normalize to the SAME carrier. -/
theorem qnfFireNormalizeTwoFourths :
    qnfNormalize { numerator := 2, denominatorPredecessor := 3 } =
      qnfNormalize { numerator := 1, denominatorPredecessor := 1 } :=
  rfl

/-- Fire: the canonical pair of `2/4` is literally `1/2`. -/
theorem qnfFireNormalizeTwoFourthsPair :
    (qnfNormalize { numerator := 2, denominatorPredecessor := 3 }).reducedPair =
      { numerator := 1, denominatorPredecessor := 1 } :=
  rfl

/-- Fire (sign handling): `-2/4` normalizes to `-1/2` — the denominator is
structurally positive on this carrier, so the raw-pair sign always lives in
the numerator; this pin exercises the negative magnitude-quotient path. -/
theorem qnfFireNormalizeNegative :
    (qnfNormalize { numerator := -2, denominatorPredecessor := 3 }).reducedPair =
      { numerator := -1, denominatorPredecessor := 1 } :=
  rfl

/-- Fire (zero sign collapse): `0/7` normalizes to the canonical zero. -/
theorem qnfFireZeroCollapse :
    qnfNormalize { numerator := 0, denominatorPredecessor := 6 } = qnfZero :=
  rfl

/-- Fire: `1/2 + 1/3 = 5/6`. -/
theorem qnfFireAddHalfThird :
    qnfAdd (qnfNormalize { numerator := 1, denominatorPredecessor := 1 })
        (qnfNormalize { numerator := 1, denominatorPredecessor := 2 }) =
      qnfNormalize { numerator := 5, denominatorPredecessor := 5 } :=
  rfl

/-- Fire: `1/2 - 1/3 = 1/6`. -/
theorem qnfFireSubHalfThird :
    qnfSub (qnfNormalize { numerator := 1, denominatorPredecessor := 1 })
        (qnfNormalize { numerator := 1, denominatorPredecessor := 2 }) =
      qnfNormalize { numerator := 1, denominatorPredecessor := 5 } :=
  rfl

/-- Fire: `(1/2) * (2/3) = 1/3` — the product `2/6` renormalizes. -/
theorem qnfFireMulHalfTwoThirds :
    qnfMul (qnfNormalize { numerator := 1, denominatorPredecessor := 1 })
        (qnfNormalize { numerator := 2, denominatorPredecessor := 2 }) =
      qnfNormalize { numerator := 1, denominatorPredecessor := 2 } :=
  rfl

/-- Fire: `(5/6) * (5/6)⁻¹ = 1` — the inverse swap plus the `30/30`
collapse. -/
theorem qnfFireInvCancel :
    qnfMul (qnfNormalize { numerator := 5, denominatorPredecessor := 5 })
        (qnfInv (qnfNormalize { numerator := 5, denominatorPredecessor := 5 })) =
      qnfOne :=
  rfl

/-- Fire: the structural comparator agrees on a computed sum. -/
theorem qnfFireBeqComputes :
    qnfBeq
        (qnfAdd (qnfNormalize { numerator := 1, denominatorPredecessor := 1 })
          (qnfNormalize { numerator := 1, denominatorPredecessor := 2 }))
        (qnfNormalize { numerator := 5, denominatorPredecessor := 5 }) =
      true :=
  rfl

/-! ## Content markers (T6) -/

/-- DECIDED: the ℚ carrier has a computable canonical normal form with
kernel-checked uniqueness (`qnfNormalizeUnique` /
`qnfNormalizeEqIffDenotesSame`) and byte-equality-is-rational-equality
(`qnfEqIffPairsDenoteSame`, `qnfBeqIffEq`). -/
def qnfHasCanonicalNormalForm : Bool := true

/-- DECIDED: the canonical carrier satisfies the full field-law suite in
plain `Eq` — commutative-group addition (`qnfAddComm`/`qnfAddAssoc`/
`qnfAddZeroRight`/`qnfAddNegRight`), commutative-monoid multiplication
(`qnfMulComm`/`qnfMulAssoc`/`qnfMulOneRight`), two-sided distributivity
(`qnfMulLeftDistrib`/`qnfMulRightDistrib`), nontriviality (`qnfZeroNeOne`),
and inverse cancellation on nonzero (`qnfMulInvCancels`). -/
def qnfHasFieldLaws : Bool := true

end FX1Poly.ComputerAlgebra
