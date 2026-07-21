import FX1Poly.ComputerAlgebra.Number.NatModularReduction

/-! # Bit-level operations as certified `Z/2^n` arithmetic

Little-endian bit vectors (`List Bool`, head = LSB) with ripple-carry addition, shift-add
multiplication, two's-complement negation, and the pointwise Boolean layer — every operation
certified against `Nat` semantics modulo `2^n` through the propext-clean counting-divider kit
(`natRemainder`, `NatModularReduction`). The closest mechanized prior art is Lean core's
`Init.Data.BitVec.Bitblast` (index-recursive, `%`-based carry) and Isabelle's
`Word_Lib/Reversed_Bit_Lists` (the same LSB-first list representation); the exact-sum carry invariant
below is the ACL2/Coquet induction form, structural on the lists, subtraction-free.

  * Value — `bvaToNat` (Horner, base 2) with the fresh structural power `bvaPow2` (doubling
    recursion) and the width bound `bvaToNatIsBounded`.
  * The adder — `bvaAddWithCarryOut` (simultaneous structural recursion, same length by contract,
    junk arms dead under the length hypothesis) and the carry invariant
    `bvaAddWithCarryOutInvariant`: `toNat sum + 2^n * carryOut = toNat u + toNat v + carryIn`, exact,
    no subtraction, no `%`. The truncating `bvaAdd` then satisfies
    `bvaAddCorrect : toNat (bvaAdd u v) = natRemainder (toNat u + toNat v) 2^n` by remainder
    uniqueness.
  * The multiplier — `bvaMulAux` (structural on the multiplier bits, the multiplicand doubled
    through the width-preserving truncating shift `bvaShiftLeftTrunc = take n (false :: u)`),
    certified by the split lemma `bvaSplitEquation`
    (`toNat (take k w) + 2^k * toNat (drop k w) = toNat w`) and the remainder push lemmas:
    `bvaMulCorrect : toNat (bvaMul u v) = natRemainder (toNat u * toNat v) 2^n`.
  * Negation, subtraction-free — `bvaComplementIdentity` (`toNat u + toNat (bvaNot u) + 1 = 2^n`) and
    `bvaNegCancels : natRemainder (toNat u + toNat (bvaNeg u)) 2^n = 0`.
  * Bitwise layer — `bvaXor`/`bvaAnd`/`bvaOr` via `bvaZipWith`; disjoint-support addition
    (`bvaDisjointAddIsXor`, `bvaDisjointXorToNat`), `bvaXorSelfIsZeroes`, `bvaAndSelfIsIdentity`.
  * Ground decision — the variable-free expression language `BvaExpr`
    (constants + add/mul/neg/xor/and/or/not) with `bvaEval`, the Bool well-formedness check
    `bvaExprIsWellFormedAtWidth`, and the decision `bvaDecideGroundEq = bvaBeq (bvaEval e1)
    (bvaEval e2)` proved equivalent to `Nat`-level value equality (`bvaDecideGroundEqIffToNatEq`)
    through `bvaToNatInjectiveOfSameLength` (parity + double-cancellation).
  * Marker `fxDissatBv_hasArithmeticBridge := true`.

Same-length pairs are managed by `Prop` hypotheses (`List.length u = List.length v`) rather than a
Bool gate — the theorems compose directly and the junk arms are killed by `Nat.noConfusion`. Widths
are never padded: every intermediate list has the multiplicand's length by construction.

`Init` plus the repo-internal `NatModularReduction` kit only. Structural recursion throughout (no
`WellFounded.fix`, no fuel). No `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `funext`, `omega`, no `decide` on `Prop` goals, no wildcard match arms over
inductive scrutinees (all matches fully enumerated), no `Nat.sub`/`Nat.mod`/`Nat.div`, no Init order
corpus (the hand-rolled `natLe*` kit from `NatEuclideanDivision` throughout), and no `simp` (the AC
`simp only` set is propext-dirty) — every additive shuffle is an explicit `congrArg`/`trans`
telescope. Per-declaration gate in the twin. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace FX1Poly.ComputerAlgebra

/-! ## Bool kit (hand-rolled, propext-free) -/

/-- Left conjunct extraction for Bool `&&`. -/
theorem bvaAndElimLeft : ∀ (leftFlag rightFlag : Bool),
    (leftFlag && rightFlag) = true → leftFlag = true
  | true, _rightFlag, _ => rfl
  | false, _rightFlag, hAnd => Bool.noConfusion hAnd

/-- Right conjunct extraction for Bool `&&`. -/
theorem bvaAndElimRight : ∀ (leftFlag rightFlag : Bool),
    (leftFlag && rightFlag) = true → rightFlag = true
  | true, _rightFlag, hAnd => hAnd
  | false, _rightFlag, hAnd => Bool.noConfusion hAnd

/-- Conjunction introduction for Bool `&&`. -/
theorem bvaAndIntro : ∀ (leftFlag rightFlag : Bool),
    leftFlag = true → rightFlag = true → (leftFlag && rightFlag) = true
  | true, _rightFlag, _, hRight => hRight
  | false, _rightFlag, hLeft, _ => Bool.noConfusion hLeft

/-! ## The value map and the structural power -/

/-- One bit as a `Nat` (`cond`, no `if`). -/
def bvaBoolToNat (bit : Bool) : Nat :=
  cond bit 1 0

/-- Little-endian Horner value: head is the least significant bit. -/
def bvaToNat : List Bool → Nat
  | [] => 0
  | bit :: rest => bvaBoolToNat bit + 2 * bvaToNat rest

/-- Fresh structural power of two by doubling — `bvaPow2 (n+1) = bvaPow2 n +
bvaPow2 n` is DEFINITIONAL, which is exactly the shape the cons-step
inductions need (no Init `Nat.pow` corpus anywhere). -/
def bvaPow2 : Nat → Nat
  | 0 => 1
  | exponent + 1 => bvaPow2 exponent + bvaPow2 exponent

/-- Powers of two are positive — `Nat.le` constructors plus the imported
transitivity, no Init order lemmas. -/
theorem bvaPow2IsPositive : ∀ (exponent : Nat), 0 < bvaPow2 exponent
  | 0 => Nat.le.refl
  | exponent + 1 =>
      natLeTrans (bvaPow2IsPositive exponent) (Nat.le.intro rfl)

/-- Doubling as self-addition (the clean `2 * v = v + v` bridge). -/
theorem bvaTwoMulIsAddSelf (value : Nat) : 2 * value = value + value :=
  (Nat.mul_comm 2 value).trans
    ((Nat.mul_succ value 1).trans (congrArg (· + value) (Nat.mul_one value)))

/-! ## Additive shuffle telescopes (the hand-rolled AC steps)

The AC `simp only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]` set is propext-dirty, so the
three shuffle shapes the inductions need are proved once as explicit telescopes. -/

/-- Riffle: `(a + b) + (c + d) = (a + c) + (b + d)`. -/
theorem bvaAddRiffle (firstTerm secondTerm thirdTerm fourthTerm : Nat) :
    (firstTerm + secondTerm) + (thirdTerm + fourthTerm)
      = (firstTerm + thirdTerm) + (secondTerm + fourthTerm) :=
  (Nat.add_assoc firstTerm secondTerm (thirdTerm + fourthTerm)).trans
    ((congrArg (firstTerm + ·)
        ((Nat.add_assoc secondTerm thirdTerm fourthTerm).symm.trans
          ((congrArg (· + fourthTerm) (Nat.add_comm secondTerm thirdTerm)).trans
            (Nat.add_assoc thirdTerm secondTerm fourthTerm)))).trans
      (Nat.add_assoc firstTerm thirdTerm (secondTerm + fourthTerm)).symm)

/-- Swap the middle addend past the tail: `(f + b) + t = (f + t) + b`. -/
theorem bvaAddSwapRight (frontTerm backTerm tailTerm : Nat) :
    (frontTerm + backTerm) + tailTerm = (frontTerm + tailTerm) + backTerm :=
  (Nat.add_assoc frontTerm backTerm tailTerm).trans
    ((congrArg (frontTerm + ·) (Nat.add_comm backTerm tailTerm)).trans
      (Nat.add_assoc frontTerm tailTerm backTerm).symm)

/-- Pull a factor `2` out through the left slot:
`a * (2 * b) = 2 * (a * b)` — rides the hand-proved `natMulAssoc`. -/
theorem bvaMulTwoSwap (leftFactor rightFactor : Nat) :
    leftFactor * (2 * rightFactor) = 2 * (leftFactor * rightFactor) :=
  (natMulAssoc leftFactor 2 rightFactor).symm.trans
    ((congrArg (· * rightFactor) (Nat.mul_comm leftFactor 2)).trans
      (natMulAssoc 2 leftFactor rightFactor))

/-! ## The width bound -/

/-- The cons step of every width bound: a bit plus a doubled in-bound tail
stays below the doubled power. -/
theorem bvaConsValueBound : ∀ (bit : Bool) (tailValue powerValue : Nat),
    tailValue < powerValue →
    bvaBoolToNat bit + 2 * tailValue < powerValue + powerValue
  | false, tailValue, powerValue, isBounded =>
      natLeOfEqLeft
        ((congrArg (· + 1)
            ((Nat.zero_add (2 * tailValue)).trans (bvaTwoMulIsAddSelf tailValue))).trans
          (Nat.add_assoc tailValue tailValue 1))
        (natLeTrans
          (natAddLeAddRight (natLeOfLt isBounded) (tailValue + 1))
          (natAddLeAddLeft isBounded powerValue))
  | true, tailValue, powerValue, isBounded =>
      natLeOfEqLeft
        ((congrArg (fun doubledValue => (1 + doubledValue) + 1)
            (bvaTwoMulIsAddSelf tailValue)).trans
          ((congrArg (· + 1) (Nat.add_comm 1 (tailValue + tailValue))).trans
            ((congrArg (· + 1) (Nat.add_assoc tailValue tailValue 1)).trans
              (Nat.succ_add tailValue (tailValue + 1)).symm)))
        (natLeTrans
          (natAddLeAddRight isBounded (tailValue + 1))
          (natAddLeAddLeft isBounded powerValue))

/-- **Width bound**: an `n`-bit vector's value stays below `2^n`. -/
theorem bvaToNatIsBounded : ∀ (bits : List Bool),
    bvaToNat bits < bvaPow2 (List.length bits)
  | [] => Nat.le.refl
  | bit :: rest =>
      bvaConsValueBound bit (bvaToNat rest) (bvaPow2 (List.length rest))
        (bvaToNatIsBounded rest)

/-! ## The full adder -/

/-- Exclusive or on bits, fully enumerated. -/
def bvaBitXor : Bool → Bool → Bool
  | true, true => false
  | true, false => true
  | false, true => true
  | false, false => false

/-- Full-adder sum bit. -/
def bvaFullAdderSum (firstBit secondBit carryBit : Bool) : Bool :=
  bvaBitXor firstBit (bvaBitXor secondBit carryBit)

/-- Full-adder carry bit (majority). -/
def bvaFullAdderCarry (firstBit secondBit carryBit : Bool) : Bool :=
  (firstBit && secondBit) || (carryBit && (firstBit || secondBit))

/-- The full-adder bit equation `sum + 2·carry = a + b + cin` — eight closed
cases, each by kernel computation. -/
theorem bvaFullAdderBitEquation : ∀ (firstBit secondBit carryBit : Bool),
    bvaBoolToNat (bvaFullAdderSum firstBit secondBit carryBit)
        + 2 * bvaBoolToNat (bvaFullAdderCarry firstBit secondBit carryBit)
      = bvaBoolToNat firstBit + bvaBoolToNat secondBit + bvaBoolToNat carryBit
  | true, true, true => rfl
  | true, true, false => rfl
  | true, false, true => rfl
  | true, false, false => rfl
  | false, true, true => rfl
  | false, true, false => rfl
  | false, false, true => rfl
  | false, false, false => rfl

/-! ## The ripple-carry adder -/

/-- Ripple-carry addition with carry-in, returning `(sumBits, carryOut)`.
Simultaneous structural recursion; the mixed-length junk arms return
`([], carry)` and are dead under the same-length contract. -/
def bvaAddWithCarryOut : List Bool → List Bool → Bool → List Bool × Bool
  | [], [], carryBit => ([], carryBit)
  | [], _secondBit :: _secondRest, carryBit => ([], carryBit)
  | _firstBit :: _firstRest, [], carryBit => ([], carryBit)
  | firstBit :: firstRest, secondBit :: secondRest, carryBit =>
      (bvaFullAdderSum firstBit secondBit carryBit ::
        (bvaAddWithCarryOut firstRest secondRest
          (bvaFullAdderCarry firstBit secondBit carryBit)).fst,
       (bvaAddWithCarryOut firstRest secondRest
         (bvaFullAdderCarry firstBit secondBit carryBit)).snd)

/-- The sum vector keeps the first operand's length. -/
theorem bvaAddWithCarryOutLength : ∀ (firstBits secondBits : List Bool) (carryBit : Bool),
    List.length firstBits = List.length secondBits →
    List.length (bvaAddWithCarryOut firstBits secondBits carryBit).fst
      = List.length firstBits
  | [], [], _, _ => rfl
  | [], _secondBit :: _secondRest, _, lengthsAgree => Nat.noConfusion lengthsAgree
  | _firstBit :: _firstRest, [], _, lengthsAgree => Nat.noConfusion lengthsAgree
  | firstBit :: firstRest, secondBit :: secondRest, carryBit, lengthsAgree =>
      congrArg (· + 1)
        (bvaAddWithCarryOutLength firstRest secondRest
          (bvaFullAdderCarry firstBit secondBit carryBit)
          (Nat.succ.inj lengthsAgree))

/-- The pure-`Nat` arithmetic content of one adder cons step: chain the tail
invariant and the bit equation through the additive telescopes. -/
theorem bvaAdderStepArithmetic
    {headSumValue headCarryValue headFirstValue headSecondValue carryInValue
      tailSumValue tailCarryValue tailFirstValue tailSecondValue powerValue : Nat}
    (hBit : headSumValue + 2 * headCarryValue
      = headFirstValue + headSecondValue + carryInValue)
    (hTail : tailSumValue + powerValue * tailCarryValue
      = tailFirstValue + tailSecondValue + headCarryValue) :
    (headSumValue + 2 * tailSumValue) + (powerValue + powerValue) * tailCarryValue
      = (headFirstValue + 2 * tailFirstValue)
          + (headSecondValue + 2 * tailSecondValue) + carryInValue :=
  calc (headSumValue + 2 * tailSumValue) + (powerValue + powerValue) * tailCarryValue
      = (headSumValue + 2 * tailSumValue)
          + (powerValue * tailCarryValue + powerValue * tailCarryValue) :=
        congrArg ((headSumValue + 2 * tailSumValue) + ·)
          (natRightDistrib powerValue powerValue tailCarryValue)
    _ = (headSumValue + 2 * tailSumValue) + 2 * (powerValue * tailCarryValue) :=
        congrArg ((headSumValue + 2 * tailSumValue) + ·)
          (bvaTwoMulIsAddSelf (powerValue * tailCarryValue)).symm
    _ = headSumValue + (2 * tailSumValue + 2 * (powerValue * tailCarryValue)) :=
        Nat.add_assoc headSumValue (2 * tailSumValue) (2 * (powerValue * tailCarryValue))
    _ = headSumValue + 2 * (tailSumValue + powerValue * tailCarryValue) :=
        congrArg (headSumValue + ·)
          (Nat.left_distrib 2 tailSumValue (powerValue * tailCarryValue)).symm
    _ = headSumValue + 2 * (tailFirstValue + tailSecondValue + headCarryValue) :=
        congrArg (fun combinedValue => headSumValue + 2 * combinedValue) hTail
    _ = headSumValue
          + (2 * (tailFirstValue + tailSecondValue) + 2 * headCarryValue) :=
        congrArg (headSumValue + ·)
          (Nat.left_distrib 2 (tailFirstValue + tailSecondValue) headCarryValue)
    _ = headSumValue
          + (2 * headCarryValue + 2 * (tailFirstValue + tailSecondValue)) :=
        congrArg (headSumValue + ·)
          (Nat.add_comm (2 * (tailFirstValue + tailSecondValue)) (2 * headCarryValue))
    _ = (headSumValue + 2 * headCarryValue)
          + 2 * (tailFirstValue + tailSecondValue) :=
        (Nat.add_assoc headSumValue (2 * headCarryValue)
          (2 * (tailFirstValue + tailSecondValue))).symm
    _ = (headFirstValue + headSecondValue + carryInValue)
          + 2 * (tailFirstValue + tailSecondValue) :=
        congrArg (· + 2 * (tailFirstValue + tailSecondValue)) hBit
    _ = (headFirstValue + headSecondValue + carryInValue)
          + (2 * tailFirstValue + 2 * tailSecondValue) :=
        congrArg ((headFirstValue + headSecondValue + carryInValue) + ·)
          (Nat.left_distrib 2 tailFirstValue tailSecondValue)
    _ = ((headFirstValue + headSecondValue)
          + (2 * tailFirstValue + 2 * tailSecondValue)) + carryInValue :=
        bvaAddSwapRight (headFirstValue + headSecondValue) carryInValue
          (2 * tailFirstValue + 2 * tailSecondValue)
    _ = ((headFirstValue + 2 * tailFirstValue)
          + (headSecondValue + 2 * tailSecondValue)) + carryInValue :=
        congrArg (· + carryInValue)
          (bvaAddRiffle headFirstValue headSecondValue
            (2 * tailFirstValue) (2 * tailSecondValue))

/-- The carry invariant, exact and subtraction-free: for same-length operands,
`toNat sum + 2^n · carryOut = toNat u + toNat v + carryIn`. -/
theorem bvaAddWithCarryOutInvariant : ∀ (firstBits secondBits : List Bool) (carryBit : Bool),
    List.length firstBits = List.length secondBits →
    bvaToNat (bvaAddWithCarryOut firstBits secondBits carryBit).fst
        + bvaPow2 (List.length firstBits)
            * bvaBoolToNat (bvaAddWithCarryOut firstBits secondBits carryBit).snd
      = bvaToNat firstBits + bvaToNat secondBits + bvaBoolToNat carryBit
  | [], [], carryBit, _ =>
      ((Nat.zero_add (1 * bvaBoolToNat carryBit)).trans
        (Nat.one_mul (bvaBoolToNat carryBit))).trans
        (Nat.zero_add (bvaBoolToNat carryBit)).symm
  | [], _secondBit :: _secondRest, _, lengthsAgree => Nat.noConfusion lengthsAgree
  | _firstBit :: _firstRest, [], _, lengthsAgree => Nat.noConfusion lengthsAgree
  | firstBit :: firstRest, secondBit :: secondRest, carryBit, lengthsAgree =>
      bvaAdderStepArithmetic
        (bvaFullAdderBitEquation firstBit secondBit carryBit)
        (bvaAddWithCarryOutInvariant firstRest secondRest
          (bvaFullAdderCarry firstBit secondBit carryBit)
          (Nat.succ.inj lengthsAgree))

/-- Truncating modular addition (carry-out dropped). -/
def bvaAdd (firstBits secondBits : List Bool) : List Bool :=
  (bvaAddWithCarryOut firstBits secondBits false).fst

/-- `bvaAdd` keeps the first operand's length. -/
theorem bvaAddLength (firstBits secondBits : List Bool)
    (lengthsAgree : List.length firstBits = List.length secondBits) :
    List.length (bvaAdd firstBits secondBits) = List.length firstBits :=
  bvaAddWithCarryOutLength firstBits secondBits false lengthsAgree

/-- **Adder correctness**: truncating addition IS addition modulo `2^n` —
remainder uniqueness applied to the carry invariant and the width bound. -/
theorem bvaAddCorrect (firstBits secondBits : List Bool)
    (lengthsAgree : List.length firstBits = List.length secondBits) :
    bvaToNat (bvaAdd firstBits secondBits)
      = natRemainder (bvaToNat firstBits + bvaToNat secondBits)
          (bvaPow2 (List.length firstBits)) :=
  have sumInvariant :
      bvaToNat (bvaAdd firstBits secondBits)
          + bvaPow2 (List.length firstBits)
              * bvaBoolToNat (bvaAddWithCarryOut firstBits secondBits false).snd
        = bvaToNat firstBits + bvaToNat secondBits :=
    bvaAddWithCarryOutInvariant firstBits secondBits false lengthsAgree
  have decomposition :
      bvaToNat firstBits + bvaToNat secondBits
        = bvaPow2 (List.length firstBits)
              * bvaBoolToNat (bvaAddWithCarryOut firstBits secondBits false).snd
            + bvaToNat (bvaAdd firstBits secondBits) :=
    sumInvariant.symm.trans
      (Nat.add_comm (bvaToNat (bvaAdd firstBits secondBits))
        (bvaPow2 (List.length firstBits)
          * bvaBoolToNat (bvaAddWithCarryOut firstBits secondBits false).snd))
  have sumBound :
      bvaToNat (bvaAdd firstBits secondBits) < bvaPow2 (List.length firstBits) :=
    natLeOfEqRight (bvaToNatIsBounded (bvaAdd firstBits secondBits))
      (congrArg bvaPow2 (bvaAddLength firstBits secondBits lengthsAgree))
  (natRemainderUnique sumBound decomposition).symm

/-! ## Zero and one vectors -/

/-- The all-`false` vector of a given width. -/
def bvaZeroes : Nat → List Bool
  | 0 => []
  | width + 1 => false :: bvaZeroes width

/-- The zero vector has value `0`. -/
theorem bvaZeroesToNat : ∀ (width : Nat), bvaToNat (bvaZeroes width) = 0
  | 0 => rfl
  | width + 1 =>
      congrArg (fun tailValue => 0 + 2 * tailValue) (bvaZeroesToNat width)

/-- The zero vector has the requested width. -/
theorem bvaZeroesLength : ∀ (width : Nat), List.length (bvaZeroes width) = width
  | 0 => rfl
  | width + 1 => congrArg (· + 1) (bvaZeroesLength width)

/-- The unit vector (`1` at the LSB) of a given width — empty at width `0`. -/
def bvaOneVector : Nat → List Bool
  | 0 => []
  | width + 1 => true :: bvaZeroes width

/-- The unit vector has the requested width. -/
theorem bvaOneVectorLength : ∀ (width : Nat),
    List.length (bvaOneVector width) = width
  | 0 => rfl
  | width + 1 => congrArg (· + 1) (bvaZeroesLength width)

/-- At any positive width the unit vector has value `1`. -/
theorem bvaOneVectorToNatSucc (width : Nat) :
    bvaToNat (bvaOneVector (width + 1)) = 1 :=
  congrArg (fun tailValue => 1 + 2 * tailValue) (bvaZeroesToNat width)

/-! ## Take, drop, and the truncating shift -/

/-- Structural prefix (fresh, cons-only — no `List.take` corpus). -/
def bvaTake : Nat → List Bool → List Bool
  | 0, [] => []
  | 0, _bit :: _rest => []
  | _count + 1, [] => []
  | count + 1, bit :: rest => bit :: bvaTake count rest

/-- Structural suffix (fresh, cons-only — no `List.drop` corpus). -/
def bvaDrop : Nat → List Bool → List Bool
  | 0, [] => []
  | 0, bit :: rest => bit :: rest
  | _count + 1, [] => []
  | count + 1, _bit :: rest => bvaDrop count rest

/-- An in-range prefix has exactly the requested length. -/
theorem bvaTakeLengthOfLe : ∀ (count : Nat) (bits : List Bool),
    count ≤ List.length bits → List.length (bvaTake count bits) = count
  | 0, [], _ => rfl
  | 0, _bit :: _rest, _ => rfl
  | _count + 1, [], isWithinLength => nomatch isWithinLength
  | count + 1, _bit :: rest, isWithinLength =>
      congrArg (· + 1)
        (bvaTakeLengthOfLe count rest (natLeOfSuccLeSucc isWithinLength))

/-- The pure-`Nat` content of one split cons step. -/
theorem bvaSplitStepArithmetic
    {headValue takeValue dropValue restValue powerValue : Nat}
    (hSplit : takeValue + powerValue * dropValue = restValue) :
    (headValue + 2 * takeValue) + (powerValue + powerValue) * dropValue
      = headValue + 2 * restValue :=
  calc (headValue + 2 * takeValue) + (powerValue + powerValue) * dropValue
      = (headValue + 2 * takeValue)
          + (powerValue * dropValue + powerValue * dropValue) :=
        congrArg ((headValue + 2 * takeValue) + ·)
          (natRightDistrib powerValue powerValue dropValue)
    _ = (headValue + 2 * takeValue) + 2 * (powerValue * dropValue) :=
        congrArg ((headValue + 2 * takeValue) + ·)
          (bvaTwoMulIsAddSelf (powerValue * dropValue)).symm
    _ = headValue + (2 * takeValue + 2 * (powerValue * dropValue)) :=
        Nat.add_assoc headValue (2 * takeValue) (2 * (powerValue * dropValue))
    _ = headValue + 2 * (takeValue + powerValue * dropValue) :=
        congrArg (headValue + ·)
          (Nat.left_distrib 2 takeValue (powerValue * dropValue)).symm
    _ = headValue + 2 * restValue :=
        congrArg (fun combinedValue => headValue + 2 * combinedValue) hSplit

/-- **The split lemma** — unconditional and subtraction-free:
`toNat (take k w) + 2^k · toNat (drop k w) = toNat w`. -/
theorem bvaSplitEquation : ∀ (count : Nat) (bits : List Bool),
    bvaToNat (bvaTake count bits)
        + bvaPow2 count * bvaToNat (bvaDrop count bits)
      = bvaToNat bits
  | 0, [] => rfl
  | 0, bit :: rest =>
      (Nat.zero_add (1 * bvaToNat (bit :: rest))).trans
        (Nat.one_mul (bvaToNat (bit :: rest)))
  | _count + 1, [] => rfl
  | count + 1, _bit :: rest =>
      bvaSplitStepArithmetic (bvaSplitEquation count rest)

/-- A `k`-prefix value stays below `2^k` (whatever the source list). -/
theorem bvaTakeToNatIsBounded : ∀ (count : Nat) (bits : List Bool),
    bvaToNat (bvaTake count bits) < bvaPow2 count
  | 0, [] => Nat.le.refl
  | 0, _bit :: _rest => Nat.le.refl
  | count + 1, [] => bvaPow2IsPositive (count + 1)
  | count + 1, bit :: rest =>
      bvaConsValueBound bit (bvaToNat (bvaTake count rest)) (bvaPow2 count)
        (bvaTakeToNatIsBounded count rest)

/-- Width-preserving truncating shift-left: prepend a `false` LSB, drop the
top bit — implemented as a prefix so every proof stays cons-only. -/
def bvaShiftLeftTrunc (bits : List Bool) : List Bool :=
  bvaTake (List.length bits) (false :: bits)

/-- The truncating shift preserves the width. -/
theorem bvaShiftLeftTruncLength (bits : List Bool) :
    List.length (bvaShiftLeftTrunc bits) = List.length bits :=
  bvaTakeLengthOfLe (List.length bits) (false :: bits) (Nat.le.step Nat.le.refl)

/-- **The truncating-shift lemma**: shifting IS doubling modulo `2^n` —
remainder uniqueness over the split lemma and the prefix bound. -/
theorem bvaShiftLeftTruncToNat (bits : List Bool) :
    bvaToNat (bvaShiftLeftTrunc bits)
      = natRemainder (2 * bvaToNat bits) (bvaPow2 (List.length bits)) :=
  have splitShifted :
      bvaToNat (bvaShiftLeftTrunc bits)
          + bvaPow2 (List.length bits)
              * bvaToNat (bvaDrop (List.length bits) (false :: bits))
        = bvaToNat (false :: bits) :=
    bvaSplitEquation (List.length bits) (false :: bits)
  have consValue : bvaToNat (false :: bits) = 2 * bvaToNat bits :=
    Nat.zero_add (2 * bvaToNat bits)
  have decomposition :
      2 * bvaToNat bits
        = bvaPow2 (List.length bits)
              * bvaToNat (bvaDrop (List.length bits) (false :: bits))
            + bvaToNat (bvaShiftLeftTrunc bits) :=
    (consValue.symm.trans splitShifted.symm).trans
      (Nat.add_comm (bvaToNat (bvaShiftLeftTrunc bits))
        (bvaPow2 (List.length bits)
          * bvaToNat (bvaDrop (List.length bits) (false :: bits))))
  (natRemainderUnique
    (bvaTakeToNatIsBounded (List.length bits) (false :: bits))
    decomposition).symm

/-! ## The shift-add multiplier -/

/-- Shift-add multiplication, structural on the multiplier bits (first
argument); the multiplicand is doubled by the truncating shift each step, so
every intermediate keeps the multiplicand's width by construction. -/
def bvaMulAux : List Bool → List Bool → List Bool
  | [], multiplicandBits => bvaZeroes (List.length multiplicandBits)
  | multiplierBit :: multiplierRest, multiplicandBits =>
      bvaAdd
        (cond multiplierBit multiplicandBits
          (bvaZeroes (List.length multiplicandBits)))
        (bvaMulAux multiplierRest (bvaShiftLeftTrunc multiplicandBits))

/-- The product keeps the multiplicand's width. -/
theorem bvaMulAuxLength : ∀ (multiplierBits multiplicandBits : List Bool),
    List.length (bvaMulAux multiplierBits multiplicandBits)
      = List.length multiplicandBits
  | [], multiplicandBits => bvaZeroesLength (List.length multiplicandBits)
  | multiplierBit :: multiplierRest, multiplicandBits => by
      have recLength := bvaMulAuxLength multiplierRest (bvaShiftLeftTrunc multiplicandBits)
      have partialLengthEq :
          List.length (cond multiplierBit multiplicandBits
              (bvaZeroes (List.length multiplicandBits)))
            = List.length multiplicandBits := by
        cases multiplierBit with
        | true => exact rfl
        | false => exact bvaZeroesLength (List.length multiplicandBits)
      have argsLengthsAgree :
          List.length (cond multiplierBit multiplicandBits
              (bvaZeroes (List.length multiplicandBits)))
            = List.length (bvaMulAux multiplierRest (bvaShiftLeftTrunc multiplicandBits)) :=
        partialLengthEq.trans
          (recLength.trans (bvaShiftLeftTruncLength multiplicandBits)).symm
      exact (bvaAddLength
          (cond multiplierBit multiplicandBits
            (bvaZeroes (List.length multiplicandBits)))
          (bvaMulAux multiplierRest (bvaShiftLeftTrunc multiplicandBits))
          argsLengthsAgree).trans partialLengthEq

/-- **Multiplier correctness** (auxiliary orientation): the shift-add product
IS multiplication modulo `2^(multiplicand width)` — whatever the multiplier's
length, since every processed bit contributes modulo the fixed modulus. -/
theorem bvaMulAuxCorrect : ∀ (multiplierBits multiplicandBits : List Bool),
    bvaToNat (bvaMulAux multiplierBits multiplicandBits)
      = natRemainder (bvaToNat multiplicandBits * bvaToNat multiplierBits)
          (bvaPow2 (List.length multiplicandBits))
  | [], multiplicandBits =>
      (bvaZeroesToNat (List.length multiplicandBits)).trans
        (natRemainderOfLt (bvaPow2IsPositive (List.length multiplicandBits))).symm
  | multiplierBit :: multiplierRest, multiplicandBits => by
      have shiftLengthEq : List.length (bvaShiftLeftTrunc multiplicandBits)
          = List.length multiplicandBits :=
        bvaShiftLeftTruncLength multiplicandBits
      have recCorrect := bvaMulAuxCorrect multiplierRest (bvaShiftLeftTrunc multiplicandBits)
      have shiftedFactored :
          bvaToNat (bvaMulAux multiplierRest (bvaShiftLeftTrunc multiplicandBits))
            = natRemainder (2 * (bvaToNat multiplicandBits * bvaToNat multiplierRest))
                (bvaPow2 (List.length multiplicandBits)) :=
        calc bvaToNat (bvaMulAux multiplierRest (bvaShiftLeftTrunc multiplicandBits))
            = natRemainder
                (bvaToNat (bvaShiftLeftTrunc multiplicandBits) * bvaToNat multiplierRest)
                (bvaPow2 (List.length (bvaShiftLeftTrunc multiplicandBits))) := recCorrect
          _ = natRemainder
                (bvaToNat (bvaShiftLeftTrunc multiplicandBits) * bvaToNat multiplierRest)
                (bvaPow2 (List.length multiplicandBits)) :=
              congrArg
                (natRemainder
                  (bvaToNat (bvaShiftLeftTrunc multiplicandBits) * bvaToNat multiplierRest))
                (congrArg bvaPow2 shiftLengthEq)
          _ = natRemainder
                (natRemainder (2 * bvaToNat multiplicandBits)
                    (bvaPow2 (List.length multiplicandBits)) * bvaToNat multiplierRest)
                (bvaPow2 (List.length multiplicandBits)) :=
              congrArg
                (fun shiftValue => natRemainder (shiftValue * bvaToNat multiplierRest)
                  (bvaPow2 (List.length multiplicandBits)))
                (bvaShiftLeftTruncToNat multiplicandBits)
          _ = natRemainder (2 * bvaToNat multiplicandBits * bvaToNat multiplierRest)
                (bvaPow2 (List.length multiplicandBits)) :=
              natRemainderMulPush (2 * bvaToNat multiplicandBits) (bvaToNat multiplierRest)
                (bvaPow2 (List.length multiplicandBits))
                (bvaPow2IsPositive (List.length multiplicandBits))
          _ = natRemainder (2 * (bvaToNat multiplicandBits * bvaToNat multiplierRest))
                (bvaPow2 (List.length multiplicandBits)) :=
              congrArg
                (fun productValue => natRemainder productValue
                  (bvaPow2 (List.length multiplicandBits)))
                (natMulAssoc 2 (bvaToNat multiplicandBits) (bvaToNat multiplierRest))
      have mulAuxLengthEq :
          List.length (bvaMulAux multiplierRest (bvaShiftLeftTrunc multiplicandBits))
            = List.length multiplicandBits :=
        (bvaMulAuxLength multiplierRest (bvaShiftLeftTrunc multiplicandBits)).trans
          shiftLengthEq
      cases multiplierBit with
      | true =>
          have argsLengthsAgree :
              List.length multiplicandBits
                = List.length (bvaMulAux multiplierRest (bvaShiftLeftTrunc multiplicandBits)) :=
            mulAuxLengthEq.symm
          have distributed :
              bvaToNat multiplicandBits * (1 + 2 * bvaToNat multiplierRest)
                = bvaToNat multiplicandBits
                    + 2 * (bvaToNat multiplicandBits * bvaToNat multiplierRest) :=
            (Nat.left_distrib (bvaToNat multiplicandBits) 1
                (2 * bvaToNat multiplierRest)).trans
              ((congrArg
                  (fun headValue => headValue
                    + bvaToNat multiplicandBits * (2 * bvaToNat multiplierRest))
                  (Nat.mul_one (bvaToNat multiplicandBits))).trans
                (congrArg (fun tailValue => bvaToNat multiplicandBits + tailValue)
                  (bvaMulTwoSwap (bvaToNat multiplicandBits) (bvaToNat multiplierRest))))
          calc bvaToNat (bvaAdd multiplicandBits
                  (bvaMulAux multiplierRest (bvaShiftLeftTrunc multiplicandBits)))
              = natRemainder
                  (bvaToNat multiplicandBits
                    + bvaToNat (bvaMulAux multiplierRest (bvaShiftLeftTrunc multiplicandBits)))
                  (bvaPow2 (List.length multiplicandBits)) :=
                bvaAddCorrect multiplicandBits
                  (bvaMulAux multiplierRest (bvaShiftLeftTrunc multiplicandBits))
                  argsLengthsAgree
            _ = natRemainder
                  (bvaToNat multiplicandBits
                    + natRemainder (2 * (bvaToNat multiplicandBits * bvaToNat multiplierRest))
                        (bvaPow2 (List.length multiplicandBits)))
                  (bvaPow2 (List.length multiplicandBits)) :=
                congrArg
                  (fun tailValue => natRemainder (bvaToNat multiplicandBits + tailValue)
                    (bvaPow2 (List.length multiplicandBits)))
                  shiftedFactored
            _ = natRemainder
                  (natRemainder (2 * (bvaToNat multiplicandBits * bvaToNat multiplierRest))
                      (bvaPow2 (List.length multiplicandBits))
                    + bvaToNat multiplicandBits)
                  (bvaPow2 (List.length multiplicandBits)) :=
                congrArg
                  (fun sumValue => natRemainder sumValue
                    (bvaPow2 (List.length multiplicandBits)))
                  (Nat.add_comm (bvaToNat multiplicandBits)
                    (natRemainder (2 * (bvaToNat multiplicandBits * bvaToNat multiplierRest))
                      (bvaPow2 (List.length multiplicandBits))))
            _ = natRemainder
                  (2 * (bvaToNat multiplicandBits * bvaToNat multiplierRest)
                    + bvaToNat multiplicandBits)
                  (bvaPow2 (List.length multiplicandBits)) :=
                natRemainderAddPush
                  (2 * (bvaToNat multiplicandBits * bvaToNat multiplierRest))
                  (bvaToNat multiplicandBits)
                  (bvaPow2 (List.length multiplicandBits))
                  (bvaPow2IsPositive (List.length multiplicandBits))
            _ = natRemainder
                  (bvaToNat multiplicandBits
                    + 2 * (bvaToNat multiplicandBits * bvaToNat multiplierRest))
                  (bvaPow2 (List.length multiplicandBits)) :=
                congrArg
                  (fun sumValue => natRemainder sumValue
                    (bvaPow2 (List.length multiplicandBits)))
                  (Nat.add_comm
                    (2 * (bvaToNat multiplicandBits * bvaToNat multiplierRest))
                    (bvaToNat multiplicandBits))
            _ = natRemainder
                  (bvaToNat multiplicandBits * (1 + 2 * bvaToNat multiplierRest))
                  (bvaPow2 (List.length multiplicandBits)) :=
                congrArg
                  (fun productValue => natRemainder productValue
                    (bvaPow2 (List.length multiplicandBits)))
                  distributed.symm
      | false =>
          have argsLengthsAgree :
              List.length (bvaZeroes (List.length multiplicandBits))
                = List.length (bvaMulAux multiplierRest (bvaShiftLeftTrunc multiplicandBits)) :=
            (bvaZeroesLength (List.length multiplicandBits)).trans mulAuxLengthEq.symm
          have shiftedBound :
              bvaToNat (bvaMulAux multiplierRest (bvaShiftLeftTrunc multiplicandBits))
                < bvaPow2 (List.length multiplicandBits) :=
            natLeOfEqRight
              (bvaToNatIsBounded
                (bvaMulAux multiplierRest (bvaShiftLeftTrunc multiplicandBits)))
              (congrArg bvaPow2 mulAuxLengthEq)
          have productFolded :
              bvaToNat multiplicandBits * (0 + 2 * bvaToNat multiplierRest)
                = 2 * (bvaToNat multiplicandBits * bvaToNat multiplierRest) :=
            (congrArg (fun factorValue => bvaToNat multiplicandBits * factorValue)
                (Nat.zero_add (2 * bvaToNat multiplierRest))).trans
              (bvaMulTwoSwap (bvaToNat multiplicandBits) (bvaToNat multiplierRest))
          calc bvaToNat (bvaAdd (bvaZeroes (List.length multiplicandBits))
                  (bvaMulAux multiplierRest (bvaShiftLeftTrunc multiplicandBits)))
              = natRemainder
                  (bvaToNat (bvaZeroes (List.length multiplicandBits))
                    + bvaToNat (bvaMulAux multiplierRest (bvaShiftLeftTrunc multiplicandBits)))
                  (bvaPow2 (List.length (bvaZeroes (List.length multiplicandBits)))) :=
                bvaAddCorrect (bvaZeroes (List.length multiplicandBits))
                  (bvaMulAux multiplierRest (bvaShiftLeftTrunc multiplicandBits))
                  argsLengthsAgree
            _ = natRemainder
                  (0 + bvaToNat (bvaMulAux multiplierRest (bvaShiftLeftTrunc multiplicandBits)))
                  (bvaPow2 (List.length (bvaZeroes (List.length multiplicandBits)))) :=
                congrArg
                  (fun zeroValue => natRemainder
                    (zeroValue
                      + bvaToNat (bvaMulAux multiplierRest (bvaShiftLeftTrunc multiplicandBits)))
                    (bvaPow2 (List.length (bvaZeroes (List.length multiplicandBits)))))
                  (bvaZeroesToNat (List.length multiplicandBits))
            _ = natRemainder
                  (bvaToNat (bvaMulAux multiplierRest (bvaShiftLeftTrunc multiplicandBits)))
                  (bvaPow2 (List.length (bvaZeroes (List.length multiplicandBits)))) :=
                congrArg
                  (fun sumValue => natRemainder sumValue
                    (bvaPow2 (List.length (bvaZeroes (List.length multiplicandBits)))))
                  (Nat.zero_add
                    (bvaToNat (bvaMulAux multiplierRest (bvaShiftLeftTrunc multiplicandBits))))
            _ = natRemainder
                  (bvaToNat (bvaMulAux multiplierRest (bvaShiftLeftTrunc multiplicandBits)))
                  (bvaPow2 (List.length multiplicandBits)) :=
                congrArg
                  (natRemainder
                    (bvaToNat (bvaMulAux multiplierRest (bvaShiftLeftTrunc multiplicandBits))))
                  (congrArg bvaPow2 (bvaZeroesLength (List.length multiplicandBits)))
            _ = bvaToNat (bvaMulAux multiplierRest (bvaShiftLeftTrunc multiplicandBits)) :=
                natRemainderOfLt shiftedBound
            _ = natRemainder (2 * (bvaToNat multiplicandBits * bvaToNat multiplierRest))
                  (bvaPow2 (List.length multiplicandBits)) :=
                shiftedFactored
            _ = natRemainder
                  (bvaToNat multiplicandBits * (0 + 2 * bvaToNat multiplierRest))
                  (bvaPow2 (List.length multiplicandBits)) :=
                congrArg
                  (fun productValue => natRemainder productValue
                    (bvaPow2 (List.length multiplicandBits)))
                  productFolded.symm

/-- Truncating modular multiplication at the FIRST operand's width. -/
def bvaMul (firstBits secondBits : List Bool) : List Bool :=
  bvaMulAux secondBits firstBits

/-- `bvaMul` keeps the first operand's length. -/
theorem bvaMulLength (firstBits secondBits : List Bool) :
    List.length (bvaMul firstBits secondBits) = List.length firstBits :=
  bvaMulAuxLength secondBits firstBits

/-- **Multiplier correctness**: shift-add multiplication IS multiplication
modulo `2^n` at the first operand's width — unconditional in the second
operand's length. -/
theorem bvaMulCorrect (firstBits secondBits : List Bool) :
    bvaToNat (bvaMul firstBits secondBits)
      = natRemainder (bvaToNat firstBits * bvaToNat secondBits)
          (bvaPow2 (List.length firstBits)) :=
  bvaMulAuxCorrect secondBits firstBits

/-! ## Complement and two's-complement negation (subtraction-free) -/

/-- Pointwise complement. -/
def bvaNot : List Bool → List Bool
  | [] => []
  | bit :: rest => (!bit) :: bvaNot rest

/-- Complement preserves the width. -/
theorem bvaNotLength : ∀ (bits : List Bool),
    List.length (bvaNot bits) = List.length bits
  | [] => rfl
  | _bit :: rest => congrArg (· + 1) (bvaNotLength rest)

/-- A bit plus its complement is `1`. -/
theorem bvaBitComplementEquation : ∀ (bit : Bool),
    bvaBoolToNat bit + bvaBoolToNat (!bit) = 1
  | true => rfl
  | false => rfl

/-- The pure-`Nat` content of one complement cons step. -/
theorem bvaComplementStepArithmetic
    {headValue headComplementValue tailValue tailComplementValue powerValue : Nat}
    (hBit : headValue + headComplementValue = 1)
    (hTail : tailValue + tailComplementValue + 1 = powerValue) :
    (headValue + 2 * tailValue) + (headComplementValue + 2 * tailComplementValue) + 1
      = powerValue + powerValue :=
  calc (headValue + 2 * tailValue) + (headComplementValue + 2 * tailComplementValue) + 1
      = ((headValue + headComplementValue)
          + (2 * tailValue + 2 * tailComplementValue)) + 1 :=
        congrArg (· + 1)
          (bvaAddRiffle headValue (2 * tailValue) headComplementValue
            (2 * tailComplementValue))
    _ = (1 + (2 * tailValue + 2 * tailComplementValue)) + 1 :=
        congrArg
          (fun headPairValue =>
            (headPairValue + (2 * tailValue + 2 * tailComplementValue)) + 1)
          hBit
    _ = ((2 * tailValue + 2 * tailComplementValue) + 1) + 1 :=
        congrArg (· + 1) (Nat.add_comm 1 (2 * tailValue + 2 * tailComplementValue))
    _ = (2 * (tailValue + tailComplementValue) + 1) + 1 :=
        congrArg (fun doubledValue => (doubledValue + 1) + 1)
          (Nat.left_distrib 2 tailValue tailComplementValue).symm
    _ = 2 * ((tailValue + tailComplementValue) + 1) :=
        (Nat.left_distrib 2 (tailValue + tailComplementValue) 1).symm
    _ = 2 * powerValue := congrArg (2 * ·) hTail
    _ = powerValue + powerValue := bvaTwoMulIsAddSelf powerValue

/-- **The complement identity**, stated WITHOUT subtraction:
`toNat u + toNat (bvaNot u) + 1 = 2^n`. -/
theorem bvaComplementIdentity : ∀ (bits : List Bool),
    bvaToNat bits + bvaToNat (bvaNot bits) + 1 = bvaPow2 (List.length bits)
  | [] => rfl
  | bit :: rest =>
      bvaComplementStepArithmetic (bvaBitComplementEquation bit)
        (bvaComplementIdentity rest)

/-- Two's-complement negation: complement, then add one (truncating). -/
def bvaNeg (bits : List Bool) : List Bool :=
  bvaAdd (bvaNot bits) (bvaOneVector (List.length bits))

/-- Negation preserves the width. -/
theorem bvaNegLength (bits : List Bool) :
    List.length (bvaNeg bits) = List.length bits :=
  (bvaAddLength (bvaNot bits) (bvaOneVector (List.length bits))
      ((bvaNotLength bits).trans (bvaOneVectorLength (List.length bits)).symm)).trans
    (bvaNotLength bits)

/-- **Negation cancels**: `u + bvaNeg u ≡ 0 (mod 2^n)` — the complement
identity chained through the adder correctness and the remainder kit. -/
theorem bvaNegCancels : ∀ (bits : List Bool),
    natRemainder (bvaToNat bits + bvaToNat (bvaNeg bits))
      (bvaPow2 (List.length bits)) = 0
  | [] => rfl
  | bit :: rest => by
      have notLengthEq : List.length (bvaNot (bit :: rest)) = List.length (bit :: rest) :=
        bvaNotLength (bit :: rest)
      have argsLengthsAgree :
          List.length (bvaNot (bit :: rest))
            = List.length (bvaOneVector (List.length (bit :: rest))) :=
        notLengthEq.trans (bvaOneVectorLength (List.length (bit :: rest))).symm
      have negValueEq :
          bvaToNat (bvaNeg (bit :: rest))
            = natRemainder (bvaToNat (bvaNot (bit :: rest)) + 1)
                (bvaPow2 (List.length (bit :: rest))) :=
        calc bvaToNat (bvaNeg (bit :: rest))
            = natRemainder
                (bvaToNat (bvaNot (bit :: rest))
                  + bvaToNat (bvaOneVector (List.length (bit :: rest))))
                (bvaPow2 (List.length (bvaNot (bit :: rest)))) :=
              bvaAddCorrect (bvaNot (bit :: rest))
                (bvaOneVector (List.length (bit :: rest))) argsLengthsAgree
          _ = natRemainder (bvaToNat (bvaNot (bit :: rest)) + 1)
                (bvaPow2 (List.length (bvaNot (bit :: rest)))) :=
              congrArg
                (fun oneValue => natRemainder (bvaToNat (bvaNot (bit :: rest)) + oneValue)
                  (bvaPow2 (List.length (bvaNot (bit :: rest)))))
                (bvaOneVectorToNatSucc (List.length rest))
          _ = natRemainder (bvaToNat (bvaNot (bit :: rest)) + 1)
                (bvaPow2 (List.length (bit :: rest))) :=
              congrArg (natRemainder (bvaToNat (bvaNot (bit :: rest)) + 1))
                (congrArg bvaPow2 notLengthEq)
      calc natRemainder (bvaToNat (bit :: rest) + bvaToNat (bvaNeg (bit :: rest)))
              (bvaPow2 (List.length (bit :: rest)))
          = natRemainder
              (bvaToNat (bit :: rest)
                + natRemainder (bvaToNat (bvaNot (bit :: rest)) + 1)
                    (bvaPow2 (List.length (bit :: rest))))
              (bvaPow2 (List.length (bit :: rest))) :=
            congrArg
              (fun negValue => natRemainder (bvaToNat (bit :: rest) + negValue)
                (bvaPow2 (List.length (bit :: rest))))
              negValueEq
        _ = natRemainder
              (natRemainder (bvaToNat (bvaNot (bit :: rest)) + 1)
                  (bvaPow2 (List.length (bit :: rest)))
                + bvaToNat (bit :: rest))
              (bvaPow2 (List.length (bit :: rest))) :=
            congrArg
              (fun sumValue => natRemainder sumValue
                (bvaPow2 (List.length (bit :: rest))))
              (Nat.add_comm (bvaToNat (bit :: rest))
                (natRemainder (bvaToNat (bvaNot (bit :: rest)) + 1)
                  (bvaPow2 (List.length (bit :: rest)))))
        _ = natRemainder
              ((bvaToNat (bvaNot (bit :: rest)) + 1) + bvaToNat (bit :: rest))
              (bvaPow2 (List.length (bit :: rest))) :=
            natRemainderAddPush (bvaToNat (bvaNot (bit :: rest)) + 1)
              (bvaToNat (bit :: rest)) (bvaPow2 (List.length (bit :: rest)))
              (bvaPow2IsPositive (List.length (bit :: rest)))
        _ = natRemainder
              (bvaToNat (bit :: rest) + bvaToNat (bvaNot (bit :: rest)) + 1)
              (bvaPow2 (List.length (bit :: rest))) :=
            congrArg
              (fun sumValue => natRemainder sumValue
                (bvaPow2 (List.length (bit :: rest))))
              ((Nat.add_comm (bvaToNat (bvaNot (bit :: rest)) + 1)
                  (bvaToNat (bit :: rest))).trans
                (Nat.add_assoc (bvaToNat (bit :: rest))
                  (bvaToNat (bvaNot (bit :: rest))) 1).symm)
        _ = natRemainder (bvaPow2 (List.length (bit :: rest)))
              (bvaPow2 (List.length (bit :: rest))) :=
            congrArg
              (fun totalValue => natRemainder totalValue
                (bvaPow2 (List.length (bit :: rest))))
              (bvaComplementIdentity (bit :: rest))
        _ = 0 := natRemainderSelf (bvaPow2IsPositive (List.length (bit :: rest)))

/-! ## The pointwise Boolean layer -/

/-- Pointwise combination of same-length vectors (junk arms return `[]`,
dead under the length contract). -/
def bvaZipWith (combine : Bool → Bool → Bool) : List Bool → List Bool → List Bool
  | [], [] => []
  | [], _secondBit :: _secondRest => []
  | _firstBit :: _firstRest, [] => []
  | firstBit :: firstRest, secondBit :: secondRest =>
      combine firstBit secondBit :: bvaZipWith combine firstRest secondRest

/-- Pointwise combination preserves the (shared) width. -/
theorem bvaZipWithLength (combine : Bool → Bool → Bool) :
    ∀ (firstBits secondBits : List Bool),
      List.length firstBits = List.length secondBits →
      List.length (bvaZipWith combine firstBits secondBits) = List.length firstBits
  | [], [], _ => rfl
  | [], _secondBit :: _secondRest, lengthsAgree => Nat.noConfusion lengthsAgree
  | _firstBit :: _firstRest, [], lengthsAgree => Nat.noConfusion lengthsAgree
  | _firstBit :: firstRest, _secondBit :: secondRest, lengthsAgree =>
      congrArg (· + 1)
        (bvaZipWithLength combine firstRest secondRest (Nat.succ.inj lengthsAgree))

/-- Bitwise exclusive or. -/
def bvaXor (firstBits secondBits : List Bool) : List Bool :=
  bvaZipWith bvaBitXor firstBits secondBits

/-- Bitwise conjunction. -/
def bvaAnd (firstBits secondBits : List Bool) : List Bool :=
  bvaZipWith (fun leftBit rightBit => leftBit && rightBit) firstBits secondBits

/-- Bitwise disjunction. -/
def bvaOr (firstBits secondBits : List Bool) : List Bool :=
  bvaZipWith (fun leftBit rightBit => leftBit || rightBit) firstBits secondBits

/-- Boolean-ring nilpotence: `x XOR x = 0`. -/
theorem bvaXorSelfIsZeroes : ∀ (bits : List Bool),
    bvaXor bits bits = bvaZeroes (List.length bits)
  | [] => rfl
  | bit :: rest => by
      cases bit with
      | true => exact congrArg (fun tailBits => false :: tailBits) (bvaXorSelfIsZeroes rest)
      | false => exact congrArg (fun tailBits => false :: tailBits) (bvaXorSelfIsZeroes rest)

/-- Boolean-ring idempotence: `x AND x = x`. -/
theorem bvaAndSelfIsIdentity : ∀ (bits : List Bool),
    bvaAnd bits bits = bits
  | [] => rfl
  | bit :: rest => by
      cases bit with
      | true => exact congrArg (fun tailBits => true :: tailBits) (bvaAndSelfIsIdentity rest)
      | false => exact congrArg (fun tailBits => false :: tailBits) (bvaAndSelfIsIdentity rest)

/-- Does every bit read `false`? -/
def bvaIsAllFalse : List Bool → Bool
  | [] => true
  | true :: _rest => false
  | false :: rest => bvaIsAllFalse rest

/-- **Disjoint-support addition is XOR** — with no common `true` bit the carry
chain stays dead: the full adder output pair IS `(u XOR v, false)`. -/
theorem bvaDisjointAddIsXor : ∀ (firstBits secondBits : List Bool),
    List.length firstBits = List.length secondBits →
    bvaIsAllFalse (bvaAnd firstBits secondBits) = true →
    bvaAddWithCarryOut firstBits secondBits false = (bvaXor firstBits secondBits, false)
  | [], [], _, _ => rfl
  | [], secondBit :: secondRest, lengthsAgree, _ => Nat.noConfusion lengthsAgree
  | firstBit :: firstRest, [], lengthsAgree, _ => Nat.noConfusion lengthsAgree
  | firstBit :: firstRest, secondBit :: secondRest, lengthsAgree, hDisjoint => by
      have tailLengthsAgree : List.length firstRest = List.length secondRest :=
        Nat.succ.inj lengthsAgree
      cases firstBit with
      | true =>
          cases secondBit with
          | true => exact Bool.noConfusion hDisjoint
          | false =>
              exact congrArg (fun tailPair => (true :: tailPair.fst, tailPair.snd))
                (bvaDisjointAddIsXor firstRest secondRest tailLengthsAgree hDisjoint)
      | false =>
          cases secondBit with
          | true =>
              exact congrArg (fun tailPair => (true :: tailPair.fst, tailPair.snd))
                (bvaDisjointAddIsXor firstRest secondRest tailLengthsAgree hDisjoint)
          | false =>
              exact congrArg (fun tailPair => (false :: tailPair.fst, tailPair.snd))
                (bvaDisjointAddIsXor firstRest secondRest tailLengthsAgree hDisjoint)

/-- Disjoint-support corollary on the truncating adder: `bvaAdd u v = bvaXor u v`. -/
theorem bvaDisjointAddEqXor (firstBits secondBits : List Bool)
    (lengthsAgree : List.length firstBits = List.length secondBits)
    (hDisjoint : bvaIsAllFalse (bvaAnd firstBits secondBits) = true) :
    bvaAdd firstBits secondBits = bvaXor firstBits secondBits :=
  congrArg Prod.fst (bvaDisjointAddIsXor firstBits secondBits lengthsAgree hDisjoint)

/-- Disjoint-support corollary on values: `toNat (u XOR v) = toNat u + toNat v`
EXACTLY (no truncation — the carry out is dead). -/
theorem bvaDisjointXorToNat (firstBits secondBits : List Bool)
    (lengthsAgree : List.length firstBits = List.length secondBits)
    (hDisjoint : bvaIsAllFalse (bvaAnd firstBits secondBits) = true) :
    bvaToNat (bvaXor firstBits secondBits) = bvaToNat firstBits + bvaToNat secondBits :=
  ((congrArg
      (fun (resultPair : List Bool × Bool) => bvaToNat resultPair.fst
        + bvaPow2 (List.length firstBits) * bvaBoolToNat resultPair.snd)
      (bvaDisjointAddIsXor firstBits secondBits lengthsAgree hDisjoint)).symm).trans
    (bvaAddWithCarryOutInvariant firstBits secondBits false lengthsAgree)

/-! ## Structural equality -/

/-- Structural equality on bits. -/
def bvaBitBeq : Bool → Bool → Bool
  | true, secondBit => secondBit
  | false, secondBit => !secondBit

/-- Reflexivity of `bvaBitBeq`. -/
theorem bvaBitBeqRefl : ∀ (bit : Bool), bvaBitBeq bit bit = true
  | true => rfl
  | false => rfl

/-- Soundness of `bvaBitBeq`. -/
theorem bvaBitBeqEq : ∀ (firstBit secondBit : Bool),
    bvaBitBeq firstBit secondBit = true → firstBit = secondBit
  | true, true, _ => rfl
  | true, false, hBeq => Bool.noConfusion hBeq
  | false, true, hBeq => Bool.noConfusion hBeq
  | false, false, _ => rfl

/-- Structural equality on bit vectors. -/
def bvaBeq : List Bool → List Bool → Bool
  | [], [] => true
  | [], _secondBit :: _secondRest => false
  | _firstBit :: _firstRest, [] => false
  | firstBit :: firstRest, secondBit :: secondRest =>
      bvaBitBeq firstBit secondBit && bvaBeq firstRest secondRest

/-- Reflexivity of `bvaBeq`. -/
theorem bvaBeqRefl : ∀ (bits : List Bool), bvaBeq bits bits = true
  | [] => rfl
  | bit :: rest =>
      bvaAndIntro (bvaBitBeq bit bit) (bvaBeq rest rest)
        (bvaBitBeqRefl bit) (bvaBeqRefl rest)

/-- Soundness of `bvaBeq`: beq-true vectors are equal. -/
theorem bvaBeqEq : ∀ (firstBits secondBits : List Bool),
    bvaBeq firstBits secondBits = true → firstBits = secondBits
  | [], [], _ => rfl
  | [], _secondBit :: _secondRest, hBeq => Bool.noConfusion hBeq
  | _firstBit :: _firstRest, [], hBeq => Bool.noConfusion hBeq
  | firstBit :: firstRest, secondBit :: secondRest, hBeq =>
      have headEq : firstBit = secondBit :=
        bvaBitBeqEq firstBit secondBit
          (bvaAndElimLeft (bvaBitBeq firstBit secondBit)
            (bvaBeq firstRest secondRest) hBeq)
      have tailEq : firstRest = secondRest :=
        bvaBeqEq firstRest secondRest
          (bvaAndElimRight (bvaBitBeq firstBit secondBit)
            (bvaBeq firstRest secondRest) hBeq)
      (congrArg (· :: firstRest) headEq).trans
        (congrArg (secondBit :: ·) tailEq)

/-! ## Value injectivity at fixed width -/

/-- Doubling is injective — structural double descent, `noConfusion` on the
mixed arms (both sides reduce to constructor-headed forms). -/
theorem bvaNatDoubleInjective : ∀ {firstValue secondValue : Nat},
    2 * firstValue = 2 * secondValue → firstValue = secondValue
  | 0, 0, _ => rfl
  | 0, _secondValue + 1, hEq => Nat.noConfusion hEq
  | _firstValue + 1, 0, hEq => Nat.noConfusion hEq
  | firstValue + 1, secondValue + 1, hEq =>
      congrArg (fun predecessorValue => predecessorValue + 1)
        (bvaNatDoubleInjective
          (firstValue := firstValue) (secondValue := secondValue)
          (Nat.succ.inj (Nat.succ.inj hEq)))

/-- Doubles are even. -/
theorem bvaEvenDouble : ∀ (value : Nat), natIsEven (2 * value) = true
  | 0 => rfl
  | value + 1 => bvaEvenDouble value

/-- Successors of doubles are odd. -/
theorem bvaOddDouble : ∀ (value : Nat), natIsEven (2 * value + 1) = false
  | 0 => rfl
  | value + 1 => bvaOddDouble value

/-- The cons-value split: equal Horner values force equal heads (parity) and
equal doubled tails (cancellation). -/
theorem bvaConsValueSplit : ∀ (firstBit secondBit : Bool)
    (firstTailValue secondTailValue : Nat),
    bvaBoolToNat firstBit + 2 * firstTailValue
        = bvaBoolToNat secondBit + 2 * secondTailValue →
    firstBit = secondBit ∧ firstTailValue = secondTailValue
  | true, true, _firstTailValue, _secondTailValue, hEq =>
      ⟨rfl, bvaNatDoubleInjective (natAddLeftCancel hEq)⟩
  | false, false, _firstTailValue, _secondTailValue, hEq =>
      ⟨rfl, bvaNatDoubleInjective (natAddLeftCancel hEq)⟩
  | true, false, firstTailValue, secondTailValue, hEq =>
      have parityEq : natIsEven (2 * firstTailValue + 1) = natIsEven (2 * secondTailValue) :=
        congrArg natIsEven
          ((Nat.add_comm (2 * firstTailValue) 1).trans
            (hEq.trans (Nat.zero_add (2 * secondTailValue))))
      Bool.noConfusion
        ((bvaOddDouble firstTailValue).symm.trans
          (parityEq.trans (bvaEvenDouble secondTailValue)))
  | false, true, firstTailValue, secondTailValue, hEq =>
      have parityEq : natIsEven (2 * secondTailValue + 1) = natIsEven (2 * firstTailValue) :=
        congrArg natIsEven
          ((Nat.add_comm (2 * secondTailValue) 1).trans
            (hEq.symm.trans (Nat.zero_add (2 * firstTailValue))))
      Bool.noConfusion
        ((bvaOddDouble secondTailValue).symm.trans
          (parityEq.trans (bvaEvenDouble firstTailValue)))

/-- **Value injectivity at fixed width**: same length + same value forces
structural equality. -/
theorem bvaToNatInjectiveOfSameLength : ∀ (firstBits secondBits : List Bool),
    List.length firstBits = List.length secondBits →
    bvaToNat firstBits = bvaToNat secondBits → firstBits = secondBits
  | [], [], _, _ => rfl
  | [], _secondBit :: _secondRest, lengthsAgree, _ => Nat.noConfusion lengthsAgree
  | _firstBit :: _firstRest, [], lengthsAgree, _ => Nat.noConfusion lengthsAgree
  | firstBit :: firstRest, secondBit :: secondRest, lengthsAgree, valuesAgree =>
      have headTailSplit :=
        bvaConsValueSplit firstBit secondBit (bvaToNat firstRest)
          (bvaToNat secondRest) valuesAgree
      have tailEq : firstRest = secondRest :=
        bvaToNatInjectiveOfSameLength firstRest secondRest
          (Nat.succ.inj lengthsAgree) headTailSplit.2
      (congrArg (· :: firstRest) headTailSplit.1).trans
        (congrArg (secondBit :: ·) tailEq)

/-! ## The ground expression language and its decision -/

/-- Variable-free bit-vector expressions over a fixed width: constants plus
the certified arithmetic and Boolean operations. -/
inductive BvaExpr : Type where
  | constant (bits : List Bool) : BvaExpr
  | add (leftOperand rightOperand : BvaExpr) : BvaExpr
  | mul (leftOperand rightOperand : BvaExpr) : BvaExpr
  | neg (operand : BvaExpr) : BvaExpr
  | xor (leftOperand rightOperand : BvaExpr) : BvaExpr
  | and (leftOperand rightOperand : BvaExpr) : BvaExpr
  | or (leftOperand rightOperand : BvaExpr) : BvaExpr
  | not (operand : BvaExpr) : BvaExpr

/-- Ground evaluation to a bit vector. -/
def bvaEval : BvaExpr → List Bool
  | .constant bits => bits
  | .add leftOperand rightOperand => bvaAdd (bvaEval leftOperand) (bvaEval rightOperand)
  | .mul leftOperand rightOperand => bvaMul (bvaEval leftOperand) (bvaEval rightOperand)
  | .neg operand => bvaNeg (bvaEval operand)
  | .xor leftOperand rightOperand => bvaXor (bvaEval leftOperand) (bvaEval rightOperand)
  | .and leftOperand rightOperand => bvaAnd (bvaEval leftOperand) (bvaEval rightOperand)
  | .or leftOperand rightOperand => bvaOr (bvaEval leftOperand) (bvaEval rightOperand)
  | .not operand => bvaNot (bvaEval operand)

/-- Well-formedness at a width: every constant leaf has exactly that width. -/
def bvaExprIsWellFormedAtWidth (width : Nat) : BvaExpr → Bool
  | .constant bits => Nat.beq (List.length bits) width
  | .add leftOperand rightOperand =>
      bvaExprIsWellFormedAtWidth width leftOperand
        && bvaExprIsWellFormedAtWidth width rightOperand
  | .mul leftOperand rightOperand =>
      bvaExprIsWellFormedAtWidth width leftOperand
        && bvaExprIsWellFormedAtWidth width rightOperand
  | .neg operand => bvaExprIsWellFormedAtWidth width operand
  | .xor leftOperand rightOperand =>
      bvaExprIsWellFormedAtWidth width leftOperand
        && bvaExprIsWellFormedAtWidth width rightOperand
  | .and leftOperand rightOperand =>
      bvaExprIsWellFormedAtWidth width leftOperand
        && bvaExprIsWellFormedAtWidth width rightOperand
  | .or leftOperand rightOperand =>
      bvaExprIsWellFormedAtWidth width leftOperand
        && bvaExprIsWellFormedAtWidth width rightOperand
  | .not operand => bvaExprIsWellFormedAtWidth width operand

/-- A well-formed expression evaluates to a vector of exactly the declared
width — every operation preserves it. -/
theorem bvaEvalLengthOfWellFormed (width : Nat) : ∀ (expr : BvaExpr),
    bvaExprIsWellFormedAtWidth width expr = true →
    List.length (bvaEval expr) = width
  | .constant _bits, hWellFormed => Nat.eq_of_beq_eq_true hWellFormed
  | .add leftOperand rightOperand, hWellFormed =>
      have leftLength := bvaEvalLengthOfWellFormed width leftOperand
        (bvaAndElimLeft (bvaExprIsWellFormedAtWidth width leftOperand)
          (bvaExprIsWellFormedAtWidth width rightOperand) hWellFormed)
      have rightLength := bvaEvalLengthOfWellFormed width rightOperand
        (bvaAndElimRight (bvaExprIsWellFormedAtWidth width leftOperand)
          (bvaExprIsWellFormedAtWidth width rightOperand) hWellFormed)
      (bvaAddLength (bvaEval leftOperand) (bvaEval rightOperand)
        (leftLength.trans rightLength.symm)).trans leftLength
  | .mul leftOperand rightOperand, hWellFormed =>
      have leftLength := bvaEvalLengthOfWellFormed width leftOperand
        (bvaAndElimLeft (bvaExprIsWellFormedAtWidth width leftOperand)
          (bvaExprIsWellFormedAtWidth width rightOperand) hWellFormed)
      (bvaMulLength (bvaEval leftOperand) (bvaEval rightOperand)).trans leftLength
  | .neg operand, hWellFormed =>
      (bvaNegLength (bvaEval operand)).trans
        (bvaEvalLengthOfWellFormed width operand hWellFormed)
  | .xor leftOperand rightOperand, hWellFormed =>
      have leftLength := bvaEvalLengthOfWellFormed width leftOperand
        (bvaAndElimLeft (bvaExprIsWellFormedAtWidth width leftOperand)
          (bvaExprIsWellFormedAtWidth width rightOperand) hWellFormed)
      have rightLength := bvaEvalLengthOfWellFormed width rightOperand
        (bvaAndElimRight (bvaExprIsWellFormedAtWidth width leftOperand)
          (bvaExprIsWellFormedAtWidth width rightOperand) hWellFormed)
      (bvaZipWithLength bvaBitXor (bvaEval leftOperand) (bvaEval rightOperand)
        (leftLength.trans rightLength.symm)).trans leftLength
  | .and leftOperand rightOperand, hWellFormed =>
      have leftLength := bvaEvalLengthOfWellFormed width leftOperand
        (bvaAndElimLeft (bvaExprIsWellFormedAtWidth width leftOperand)
          (bvaExprIsWellFormedAtWidth width rightOperand) hWellFormed)
      have rightLength := bvaEvalLengthOfWellFormed width rightOperand
        (bvaAndElimRight (bvaExprIsWellFormedAtWidth width leftOperand)
          (bvaExprIsWellFormedAtWidth width rightOperand) hWellFormed)
      (bvaZipWithLength (fun leftBit rightBit => leftBit && rightBit)
        (bvaEval leftOperand) (bvaEval rightOperand)
        (leftLength.trans rightLength.symm)).trans leftLength
  | .or leftOperand rightOperand, hWellFormed =>
      have leftLength := bvaEvalLengthOfWellFormed width leftOperand
        (bvaAndElimLeft (bvaExprIsWellFormedAtWidth width leftOperand)
          (bvaExprIsWellFormedAtWidth width rightOperand) hWellFormed)
      have rightLength := bvaEvalLengthOfWellFormed width rightOperand
        (bvaAndElimRight (bvaExprIsWellFormedAtWidth width leftOperand)
          (bvaExprIsWellFormedAtWidth width rightOperand) hWellFormed)
      (bvaZipWithLength (fun leftBit rightBit => leftBit || rightBit)
        (bvaEval leftOperand) (bvaEval rightOperand)
        (leftLength.trans rightLength.symm)).trans leftLength
  | .not operand, hWellFormed =>
      (bvaNotLength (bvaEval operand)).trans
        (bvaEvalLengthOfWellFormed width operand hWellFormed)

/-- The ground decision: structural equality of the evaluated vectors. -/
def bvaDecideGroundEq (leftExpr rightExpr : BvaExpr) : Bool :=
  bvaBeq (bvaEval leftExpr) (bvaEval rightExpr)

/-- **Decision correctness**: for well-formed same-width ground expressions,
the Bool decision answers `true` EXACTLY when the `Nat` values agree —
soundness by beq-soundness, completeness by value injectivity at fixed
width. -/
theorem bvaDecideGroundEqIffToNatEq (width : Nat) (leftExpr rightExpr : BvaExpr)
    (hLeftWellFormed : bvaExprIsWellFormedAtWidth width leftExpr = true)
    (hRightWellFormed : bvaExprIsWellFormedAtWidth width rightExpr = true) :
    bvaDecideGroundEq leftExpr rightExpr = true
      ↔ bvaToNat (bvaEval leftExpr) = bvaToNat (bvaEval rightExpr) :=
  Iff.intro
    (fun hDecide =>
      congrArg bvaToNat (bvaBeqEq (bvaEval leftExpr) (bvaEval rightExpr) hDecide))
    (fun hValuesAgree =>
      have lengthsAgree : List.length (bvaEval leftExpr) = List.length (bvaEval rightExpr) :=
        (bvaEvalLengthOfWellFormed width leftExpr hLeftWellFormed).trans
          (bvaEvalLengthOfWellFormed width rightExpr hRightWellFormed).symm
      have vectorsAgree : bvaEval leftExpr = bvaEval rightExpr :=
        bvaToNatInjectiveOfSameLength (bvaEval leftExpr) (bvaEval rightExpr)
          lengthsAgree hValuesAgree
      (congrArg (bvaBeq · (bvaEval rightExpr)) vectorsAgree).trans
        (bvaBeqRefl (bvaEval rightExpr)))

/-- Bit-level ripple-carry / shift-add / two's-complement operations as certified `Z/2^n`
arithmetic, with a sound-and-complete ground equality decision. -/
def fxDissatBv_hasArithmeticBridge : Bool := true

/-! ## Smoke tests (width 8; values printed through `bvaToNat`)

The 8-bit sample vectors, little-endian:
`200 = [f,f,f,t,f,f,t,t]`, `100 = [f,f,t,f,f,t,t,f]`, `44 = [f,f,t,t,f,t,f,f]`,
`45 = [t,f,t,t,f,t,f,f]`, `16 = [f,f,f,f,t,f,f,f]`, `3 = [t,t,f,f,f,f,f,f]`,
`5 = [t,f,t,f,f,f,f,f]`, `15 = [t,t,t,t,f,f,f,f]`, `1 = [t,f,f,f,f,f,f,f]`,
`255 = [t,t,t,t,t,t,t,t]`. -/

-- Overflow wraps: 200 + 100 = 300 ≡ 44 (mod 256).  Expected: 44
#eval bvaToNat (bvaAdd
  [false, false, false, true, false, false, true, true]
  [false, false, true, false, false, true, true, false])

-- 16 * 16 = 256 ≡ 0 (mod 256).  Expected: 0
#eval bvaToNat (bvaMul
  [false, false, false, false, true, false, false, false]
  [false, false, false, false, true, false, false, false])

-- 3 * 5 = 15 (no wrap).  Expected: 15
#eval bvaToNat (bvaMul
  [true, true, false, false, false, false, false, false]
  [true, false, true, false, false, false, false, false])

-- neg 1 = 255 (all ones).  Expected: 255
#eval bvaToNat (bvaNeg [true, false, false, false, false, false, false, false])

-- 200 XOR 200 = 0.  Expected: 0
#eval bvaToNat (bvaXor
  [false, false, false, true, false, false, true, true]
  [false, false, false, true, false, false, true, true])

-- Decision, TRUE case: 200 + 100 == 44 at width 8.  Expected: true
#eval bvaDecideGroundEq
  (BvaExpr.add
    (BvaExpr.constant [false, false, false, true, false, false, true, true])
    (BvaExpr.constant [false, false, true, false, false, true, true, false]))
  (BvaExpr.constant [false, false, true, true, false, true, false, false])

-- Decision, FALSE case: 200 + 100 == 45 at width 8.  Expected: false
#eval bvaDecideGroundEq
  (BvaExpr.add
    (BvaExpr.constant [false, false, false, true, false, false, true, true])
    (BvaExpr.constant [false, false, true, false, false, true, true, false]))
  (BvaExpr.constant [true, false, true, true, false, true, false, false])

-- Decision, TRUE case: 3 * 5 == 15.  Expected: true
#eval bvaDecideGroundEq
  (BvaExpr.mul
    (BvaExpr.constant [true, true, false, false, false, false, false, false])
    (BvaExpr.constant [true, false, true, false, false, false, false, false]))
  (BvaExpr.constant [true, true, true, true, false, false, false, false])

-- Decision, FALSE case: 3 * 5 == 16.  Expected: false
#eval bvaDecideGroundEq
  (BvaExpr.mul
    (BvaExpr.constant [true, true, false, false, false, false, false, false])
    (BvaExpr.constant [true, false, true, false, false, false, false, false]))
  (BvaExpr.constant [false, false, false, false, true, false, false, false])

-- Decision, TRUE case: neg 1 == 255.  Expected: true
#eval bvaDecideGroundEq
  (BvaExpr.neg (BvaExpr.constant [true, false, false, false, false, false, false, false]))
  (BvaExpr.constant [true, true, true, true, true, true, true, true])

end FX1Poly.ComputerAlgebra
