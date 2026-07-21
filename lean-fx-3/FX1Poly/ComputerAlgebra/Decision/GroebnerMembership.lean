/-! # FX1Poly/ComputerAlgebra/Decision/GroebnerMembership — the Gröbner
    ideal-membership certificate route (checkable cofactor certificates, F2 coefficients)

Ideal membership dissolves WITHOUT termination: the positive certificate for
`target ∈ ⟨g1..gk⟩` is a cofactor list `q1..qk` with
`target = q1*g1 + ... + qk*gk` as polynomials, and CHECKING a certificate is pure
polynomial arithmetic — no search, no Dickson, no confluence.  This is the
Grégoire–Pottier / nsatz reflection split (Coq `nsatz`; Lean `linear_combination` /
`polyrith`): an untrusted FINDER emits the certificate, a verified CHECKER validates it,
and the soundness theorem lives entirely on the checker.

## Coefficient choice — F2

Coefficients are **F2 = Bool** (xor/and) rather than ℚ.  A ℚ coefficient via the
`RationalPair` kit is a cross-multiplication setoid (`DenotesSameAs`, no canonical normal
form), so structural beq on sorted coefficient-carrying lists would be
equality-up-to-setoid everywhere — every AC lemma, canonicity, and the checker's final
beq would need setoid transport.  F2 keeps every theorem meaningful and makes the
representation CANONICAL: a nonzero F2 coefficient is 1, so a polynomial IS a
strictly-descending sorted list of exponent vectors, addition is the symmetric-difference
merge (collision = xor 1 1 = 0 = drop), negation is the identity (-1 = 1), and every
leading coefficient is a unit — division is always exact, and the nsatz scalar `c` and
Rabinowitsch exponent `r` both degenerate to 1.

## The layers

  * **Exponent vectors** (`GrbExp`) — strictly-ascending-by-variable lists of
    `GrbVarPower` (variable index, positive exponent); `grbExpMul` merges by inserting
    with exponent ADDITION on shared variables (`grbExpInsert`).
  * **Monomial order** (`grbMonoLess`) — graded lex: hand-rolled total degree
    (`grbExpDegree`, compared by hand-rolled `grbNatLess`) first, then lex
    (`grbExpLexLess`, smaller variable index = more significant).  Irreflexivity,
    asymmetry, transitivity, and totality-against-beq are all hand-proved — no library
    order lemmas.
  * **Polynomials** (`GrbPoly`) — strictly-descending sorted monomial lists.  `grbAdd`
    is an insert-fold with collision-drop (`grbMonoInsert`), `grbMul` distributes
    `grbScaleByMonomial` over `grbAdd`, `grbNeg` is the identity, `grbScale` is the
    Bool scalar action.  `grbAdd left right` is sorted whenever `right` is
    (`grbAddKeepsSorted`), which makes `grbMul` and `grbSumOfProducts` UNCONDITIONALLY
    sorted — no well-formedness threading through the finder.
  * **The workhorse** — `grbPolyExtensionality`: sorted polynomials with pointwise-equal
    F2 coefficient functions (`grbCoeff`, the xor-parity scan — a homomorphism from
    ARBITRARY lists, sorted or not) are byte-equal lists.  Every AC/cancellation
    identity (`grbAddAssoc`, `grbAddSwapLeft`, `grbAddCrossCancel`,
    `grbAddSelfIsZero`, ...) is one extensionality fire over a Bool xor case-bash.
  * **THE CHECKER** — `grbCheckCertificate gens cofs target` = structural beq of
    `grbSumOfProducts cofs gens` against `target`.  Membership is the SEMANTIC
    inductive `GrbInIdeal` (zero in; generators in; closed under `grbAdd`; closed under
    `grbMul` by ANY polynomial), and the headline `grbCertificateSound` says: checker
    accepts ⟹ `GrbInIdeal gens target`.  The ring-equality shape is
    `grbDifferenceInIdealByCertificate` (certificate for `p + (-q)` puts the difference
    in the ideal) with the semantic pin `grbRingEqualityByCertificate`: at every common
    zero of the generators, `p` and `q` evaluate equal (via the evaluation homomorphism
    `grbEvalPoly` and `grbInIdealVanishesOnCommonZero` — genuine Nullstellensatz-easy
    direction, no completeness claim).
  * **THE FINDER** (untrusted-but-verified-on-success) — `grbReduceStep` top-reduces the
    leading monomial by the first generator whose leading monomial divides it
    (`grbFindReducer`, exact F2 division via `grbExpQuotient`), accumulating the
    quotient monomial into the matching cofactor; `grbReduce` is fuel-bounded
    (structural on a `Nat` fuel — no `WellFounded.fix`).  THE INVARIANT
    (`grbReduceInvariant`): at every fuel level,
    `remainder + Σ cofᵢ·genᵢ = poly + Σ cof⁰ᵢ·genᵢ` as sorted lists — so fuel exhaustion
    still leaves a checkable partial certificate.  `grbFinderSound`: remainder `[]` ⟹
    the returned cofactors pass `grbCheckCertificate`.  No termination claim anywhere.
    One-round S-polynomial enrichment is out of scope.

## The honest wall

The full NON-membership decision (`grbNonMembershipDecisionStatement`, owner
`fxDissatGrob_hasNonMembershipDecision := false`) needs two missing legs: Buchberger
termination — Dickson's lemma, certified IMPOSSIBLE zero-axiom in this repo
(`fxNet4_dicksonWall` in `FX1Poly/ComputerAlgebra/Order/AlmostFull.lean`: the
AF-product route forces `WellFounded.fix`) — and Newman-style confluence of the
completed basis (reduce-to-nonzero refutes membership only over a confluent basis).
Neither is attempted.  The certificate route (`fxDissatGrob_hasCertificateRoute :=
true`) is fully DECIDED.

## Zero-axiom discipline

Init only, no repo imports needed after the F2 fallback.  Structural recursion
throughout (fuel for the finder).  No `propext`, `Quot.sound`, `Classical.choice`,
`sorry`, `native_decide`, `funext`, `omega`, no `decide` on `Prop`, no catch-all match
arms over split scrutinees.  Nat arithmetic restricted to the safe kit
(`Nat.beq` + hand-rolled `grbNatLess`/`grbNatMinus`); Bool dispatch in definitions uses
`cond`; all list helpers are bespoke, monomorphic, cons-only (no `List.append`).
Per-declaration gate in `FX1PolyAudit/ComputerAlgebra/Decision/GroebnerMembership.lean`. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace FX1Poly.ComputerAlgebra

/-! ## Bool kit (hand-rolled xor, and-lemmas; all by finite case-bash) -/

/-- F2 addition: Boolean exclusive or.  `grbBoolXor false b = b` is definitional. -/
def grbBoolXor : Bool → Bool → Bool
  | false, rightBit => rightBit
  | true, false => true
  | true, true => false

/-- `xor b false = b`. -/
theorem grbBoolXorFalseRight : (bit : Bool) → grbBoolXor bit false = bit
  | false => rfl
  | true => rfl

/-- `xor b b = false` — characteristic two. -/
theorem grbBoolXorSelfIsFalse : (bit : Bool) → grbBoolXor bit bit = false
  | false => rfl
  | true => rfl

/-- Associativity of xor. -/
theorem grbBoolXorAssoc : (first second third : Bool) →
    grbBoolXor (grbBoolXor first second) third = grbBoolXor first (grbBoolXor second third)
  | false, _, _ => rfl
  | true, false, _ => rfl
  | true, true, false => rfl
  | true, true, true => rfl

/-- Left-swap for xor: `a ^ (b ^ c) = b ^ (a ^ c)`. -/
theorem grbBoolXorSwapLeft : (first second third : Bool) →
    grbBoolXor first (grbBoolXor second third) = grbBoolXor second (grbBoolXor first third)
  | false, false, _ => rfl
  | false, true, _ => rfl
  | true, false, _ => rfl
  | true, true, false => rfl
  | true, true, true => rfl

/-- Left self-cancellation: `a ^ (a ^ b) = b`. -/
theorem grbBoolXorLeftSelfCancel : (shared bit : Bool) →
    grbBoolXor shared (grbBoolXor shared bit) = bit
  | false, _ => rfl
  | true, false => rfl
  | true, true => rfl

/-- Cross cancellation: `(s ^ p) ^ (s ^ r) = p ^ r`. -/
theorem grbBoolXorCrossCancel : (shared first second : Bool) →
    grbBoolXor (grbBoolXor shared first) (grbBoolXor shared second) = grbBoolXor first second
  | false, _, _ => rfl
  | true, false, false => rfl
  | true, false, true => rfl
  | true, true, false => rfl
  | true, true, true => rfl

/-- Xor is left-injective. -/
theorem grbBoolXorLeftInjective : (shared first second : Bool) →
    grbBoolXor shared first = grbBoolXor shared second → first = second
  | false, _, _, hEqual => hEqual
  | true, false, false, _ => rfl
  | true, false, true, hEqual => Bool.noConfusion hEqual
  | true, true, false, hEqual => Bool.noConfusion hEqual
  | true, true, true, _ => rfl

/-- A vanishing xor forces equality. -/
theorem grbBoolXorEqFalseImpliesEq : (first second : Bool) →
    grbBoolXor first second = false → first = second
  | false, false, _ => rfl
  | false, true, hVanishes => Bool.noConfusion hVanishes
  | true, false, hVanishes => Bool.noConfusion hVanishes
  | true, true, _ => rfl

/-- Right-factoring: `(a && c) ^ (b && c) = (a ^ b) && c`. -/
theorem grbBoolXorAndRightFactor : (first second factor : Bool) →
    grbBoolXor (first && factor) (second && factor) = (grbBoolXor first second && factor)
  | false, false, _ => rfl
  | false, true, _ => rfl
  | true, false, false => rfl
  | true, false, true => rfl
  | true, true, false => rfl
  | true, true, true => rfl

/-- Left-distribution of `&&` over xor: `(x && u) ^ (x && v) = x && (u ^ v)`. -/
theorem grbBoolAndDistribXor : (factor first second : Bool) →
    grbBoolXor (factor && first) (factor && second) = (factor && grbBoolXor first second)
  | false, _, _ => rfl
  | true, _, _ => rfl

/-- Left-swap for `&&`. -/
theorem grbBoolAndSwapLeft : (first second third : Bool) →
    (first && (second && third)) = (second && (first && third))
  | false, false, _ => rfl
  | false, true, _ => rfl
  | true, _, _ => rfl

/-- Associativity of `&&`. -/
theorem grbBoolAndAssoc : (first second third : Bool) →
    ((first && second) && third) = (first && (second && third))
  | false, _, _ => rfl
  | true, _, _ => rfl

/-- `a && true = a`. -/
theorem grbBoolAndTrueRight : (bit : Bool) → (bit && true) = bit
  | false => rfl
  | true => rfl

/-- `a && false = false`. -/
theorem grbBoolAndFalseRight : (bit : Bool) → (bit && false) = false
  | false => rfl
  | true => rfl

/-- Conjunction elimination for Bool `&&`. -/
theorem grbBoolAndElim : (leftFlag rightFlag : Bool) → (leftFlag && rightFlag) = true →
    leftFlag = true ∧ rightFlag = true
  | true, true, _ => ⟨rfl, rfl⟩
  | true, false, hBoth => Bool.noConfusion hBoth
  | false, true, hBoth => Bool.noConfusion hBoth
  | false, false, hBoth => Bool.noConfusion hBoth

/-- If a conjunction is false and its left half is true, its right half is false. -/
theorem grbBoolAndTrueLeftFalse {leftFlag rightFlag : Bool}
    (hBoth : (leftFlag && rightFlag) = false) (hLeft : leftFlag = true) : rightFlag = false := by
  subst hLeft
  exact hBoth

/-! ## Nat kit (Nat.beq facts + a hand-rolled strict order; no library order lemmas) -/

/-- Reflexivity of `Nat.beq`. -/
theorem grbNatBeqRefl : (value : Nat) → Nat.beq value value = true
  | 0 => rfl
  | Nat.succ predecessor => grbNatBeqRefl predecessor

/-- `Nat.beq` sound: beq-true numbers are equal. -/
theorem grbNatBeqEq : (leftValue rightValue : Nat) → Nat.beq leftValue rightValue = true →
    leftValue = rightValue
  | 0, 0, _ => rfl
  | 0, Nat.succ _, hBeq => Bool.noConfusion hBeq
  | Nat.succ _, 0, hBeq => Bool.noConfusion hBeq
  | Nat.succ leftPredecessor, Nat.succ rightPredecessor, hBeq =>
      congrArg Nat.succ (grbNatBeqEq leftPredecessor rightPredecessor hBeq)

/-- Beq-false is symmetric. -/
theorem grbNatBeqSymmFalse : (leftValue rightValue : Nat) →
    Nat.beq leftValue rightValue = false → Nat.beq rightValue leftValue = false
  | 0, 0, hBeq => hBeq
  | 0, Nat.succ _, _ => rfl
  | Nat.succ _, 0, _ => rfl
  | Nat.succ leftPredecessor, Nat.succ rightPredecessor, hBeq =>
      grbNatBeqSymmFalse leftPredecessor rightPredecessor hBeq

/-- Hand-rolled strict less-than on `Nat` (structural; no `Nat.blt`/`Nat.ble` lemmas). -/
def grbNatLess : Nat → Nat → Bool
  | 0, 0 => false
  | Nat.succ _, 0 => false
  | 0, Nat.succ _ => true
  | Nat.succ leftPredecessor, Nat.succ rightPredecessor =>
      grbNatLess leftPredecessor rightPredecessor

/-- Irreflexivity of `grbNatLess`. -/
theorem grbNatLessIrrefl : (value : Nat) → grbNatLess value value = false
  | 0 => rfl
  | Nat.succ predecessor => grbNatLessIrrefl predecessor

/-- Asymmetry of `grbNatLess`. -/
theorem grbNatLessAsym : (leftValue rightValue : Nat) →
    grbNatLess leftValue rightValue = true → grbNatLess rightValue leftValue = false
  | 0, 0, hLess => Bool.noConfusion hLess
  | Nat.succ _, 0, hLess => Bool.noConfusion hLess
  | 0, Nat.succ _, _ => rfl
  | Nat.succ leftPredecessor, Nat.succ rightPredecessor, hLess =>
      grbNatLessAsym leftPredecessor rightPredecessor hLess

/-- Transitivity of `grbNatLess`. -/
theorem grbNatLessTrans : (first second third : Nat) →
    grbNatLess first second = true → grbNatLess second third = true →
    grbNatLess first third = true
  | 0, 0, _, hFirst, _ => Bool.noConfusion hFirst
  | Nat.succ _, 0, _, hFirst, _ => Bool.noConfusion hFirst
  | 0, Nat.succ _, 0, _, hSecond => Bool.noConfusion hSecond
  | Nat.succ _, Nat.succ _, 0, _, hSecond => Bool.noConfusion hSecond
  | 0, Nat.succ _, Nat.succ _, _, _ => rfl
  | Nat.succ firstPredecessor, Nat.succ secondPredecessor, Nat.succ thirdPredecessor,
      hFirst, hSecond =>
      grbNatLessTrans firstPredecessor secondPredecessor thirdPredecessor hFirst hSecond

/-- Totality: beq-distinct numbers compare strictly one way or the other. -/
theorem grbNatLessTotal : (leftValue rightValue : Nat) →
    Nat.beq leftValue rightValue = false →
    grbNatLess leftValue rightValue = true ∨ grbNatLess rightValue leftValue = true
  | 0, 0, hBeq => Bool.noConfusion hBeq
  | 0, Nat.succ _, _ => Or.inl rfl
  | Nat.succ _, 0, _ => Or.inr rfl
  | Nat.succ leftPredecessor, Nat.succ rightPredecessor, hBeq =>
      grbNatLessTotal leftPredecessor rightPredecessor hBeq

/-- Non-strict comparison assembled from beq and the strict order (finder-side only). -/
def grbNatLessOrEq (leftValue rightValue : Nat) : Bool :=
  cond (Nat.beq leftValue rightValue) true (grbNatLess leftValue rightValue)

/-- Hand-rolled truncated subtraction (finder-side computation only; no lemmas needed —
the reduce invariant never relies on quotient correctness). -/
def grbNatMinus : Nat → Nat → Nat
  | 0, 0 => 0
  | Nat.succ leftPredecessor, 0 => Nat.succ leftPredecessor
  | 0, Nat.succ _ => 0
  | Nat.succ leftPredecessor, Nat.succ rightPredecessor =>
      grbNatMinus leftPredecessor rightPredecessor

/-! ## Exponent vectors: variable powers, beq, degree, merge-with-addition -/

/-- One variable power inside an exponent vector: `variableIndex ^ exponent`. -/
structure GrbVarPower where
  variableIndex : Nat
  exponent : Nat

/-- Structural Boolean equality on variable powers. -/
def grbVarPowerBeq (left right : GrbVarPower) : Bool :=
  Nat.beq left.variableIndex right.variableIndex && Nat.beq left.exponent right.exponent

/-- Reflexivity of `grbVarPowerBeq`. -/
theorem grbVarPowerBeqRefl (varPower : GrbVarPower) : grbVarPowerBeq varPower varPower = true := by
  show (Nat.beq varPower.variableIndex varPower.variableIndex &&
    Nat.beq varPower.exponent varPower.exponent) = true
  rw [grbNatBeqRefl varPower.variableIndex, grbNatBeqRefl varPower.exponent]
  rfl

/-- `grbVarPowerBeq` sound: beq-true variable powers are equal. -/
theorem grbVarPowerBeqEq : (left right : GrbVarPower) → grbVarPowerBeq left right = true →
    left = right
  | GrbVarPower.mk leftVariable leftExponent, GrbVarPower.mk rightVariable rightExponent,
      hBeq => by
      have hSplit := grbBoolAndElim _ _ hBeq
      rw [grbNatBeqEq leftVariable rightVariable hSplit.left,
        grbNatBeqEq leftExponent rightExponent hSplit.right]

/-- An exponent vector: variable powers sorted strictly ascending by variable index,
all exponents positive (canonical form maintained computationally by `grbExpInsert`). -/
abbrev GrbExp := List GrbVarPower

/-- Structural Boolean equality on exponent vectors. -/
def grbExpBeq : GrbExp → GrbExp → Bool
  | [], [] => true
  | [], _ :: _ => false
  | _ :: _, [] => false
  | leftHead :: leftRest, rightHead :: rightRest =>
      grbVarPowerBeq leftHead rightHead && grbExpBeq leftRest rightRest

/-- Reflexivity of `grbExpBeq`. -/
theorem grbExpBeqRefl : (exp : GrbExp) → grbExpBeq exp exp = true
  | [] => rfl
  | head :: rest => by
      show (grbVarPowerBeq head head && grbExpBeq rest rest) = true
      rw [grbVarPowerBeqRefl head, grbExpBeqRefl rest]
      rfl

/-- `grbExpBeq` sound: beq-true exponent vectors are equal. -/
theorem grbExpBeqEq : (left right : GrbExp) → grbExpBeq left right = true → left = right
  | [], [], _ => rfl
  | [], _ :: _, hBeq => Bool.noConfusion hBeq
  | _ :: _, [], hBeq => Bool.noConfusion hBeq
  | leftHead :: leftRest, rightHead :: rightRest, hBeq => by
      have hSplit := grbBoolAndElim _ _ hBeq
      rw [grbVarPowerBeqEq leftHead rightHead hSplit.left,
        grbExpBeqEq leftRest rightRest hSplit.right]

/-- Total degree of an exponent vector (hand-rolled exponent sum). -/
def grbExpDegree : GrbExp → Nat
  | [] => 0
  | varPower :: rest => varPower.exponent + grbExpDegree rest

/-- Insert a variable power into an exponent vector, ADDING exponents on a shared
variable — the multiset-union step of monomial multiplication. -/
def grbExpInsert (varPower : GrbVarPower) : GrbExp → GrbExp
  | [] => [varPower]
  | head :: rest =>
      cond (Nat.beq varPower.variableIndex head.variableIndex)
        ({ variableIndex := head.variableIndex,
           exponent := varPower.exponent + head.exponent } :: rest)
        (cond (grbNatLess varPower.variableIndex head.variableIndex)
          (varPower :: head :: rest)
          (head :: grbExpInsert varPower rest))

/-- `grbExpInsert` branch: shared variable — exponents add. -/
theorem grbExpInsertOnSharedVariable (varPower head : GrbVarPower) (rest : GrbExp)
    (hShared : Nat.beq varPower.variableIndex head.variableIndex = true) :
    grbExpInsert varPower (head :: rest) =
      { variableIndex := head.variableIndex,
        exponent := varPower.exponent + head.exponent } :: rest := by
  show cond (Nat.beq varPower.variableIndex head.variableIndex)
      ({ variableIndex := head.variableIndex,
         exponent := varPower.exponent + head.exponent } :: rest)
      (cond (grbNatLess varPower.variableIndex head.variableIndex)
        (varPower :: head :: rest)
        (head :: grbExpInsert varPower rest)) =
    { variableIndex := head.variableIndex,
      exponent := varPower.exponent + head.exponent } :: rest
  rw [hShared]
  rfl

/-- `grbExpInsert` branch: earlier variable — prepend. -/
theorem grbExpInsertOnEarlierVariable (varPower head : GrbVarPower) (rest : GrbExp)
    (hDistinct : Nat.beq varPower.variableIndex head.variableIndex = false)
    (hEarlier : grbNatLess varPower.variableIndex head.variableIndex = true) :
    grbExpInsert varPower (head :: rest) = varPower :: head :: rest := by
  show cond (Nat.beq varPower.variableIndex head.variableIndex)
      ({ variableIndex := head.variableIndex,
         exponent := varPower.exponent + head.exponent } :: rest)
      (cond (grbNatLess varPower.variableIndex head.variableIndex)
        (varPower :: head :: rest)
        (head :: grbExpInsert varPower rest)) = varPower :: head :: rest
  rw [hDistinct, hEarlier]
  rfl

/-- `grbExpInsert` branch: later variable — descend. -/
theorem grbExpInsertOnLaterVariable (varPower head : GrbVarPower) (rest : GrbExp)
    (hDistinct : Nat.beq varPower.variableIndex head.variableIndex = false)
    (hNotEarlier : grbNatLess varPower.variableIndex head.variableIndex = false) :
    grbExpInsert varPower (head :: rest) = head :: grbExpInsert varPower rest := by
  show cond (Nat.beq varPower.variableIndex head.variableIndex)
      ({ variableIndex := head.variableIndex,
         exponent := varPower.exponent + head.exponent } :: rest)
      (cond (grbNatLess varPower.variableIndex head.variableIndex)
        (varPower :: head :: rest)
        (head :: grbExpInsert varPower rest)) = head :: grbExpInsert varPower rest
  rw [hDistinct, hNotEarlier]
  rfl

/-- Monomial multiplication: merge the left exponent vector into the right, adding
exponents on shared variables. -/
def grbExpMul : GrbExp → GrbExp → GrbExp
  | [], right => right
  | varPower :: rest, right => grbExpInsert varPower (grbExpMul rest right)

/-! ## The monomial order: lex tail under a graded head

`grbExpLexLess` is strict lex with the SMALLER variable index more significant
(a positive exponent on an earlier variable beats any later content); `grbMonoLess`
compares hand-rolled total degrees first, then lex.  All four order laws are
hand-proved by structural case-bash on the sorted vectors. -/

/-- Strict lex order on exponent vectors (earlier variable index = more significant). -/
def grbExpLexLess : GrbExp → GrbExp → Bool
  | [], [] => false
  | [], _ :: _ => true
  | _ :: _, [] => false
  | GrbVarPower.mk leftVariable leftExponent :: leftRest,
      GrbVarPower.mk rightVariable rightExponent :: rightRest =>
      cond (Nat.beq leftVariable rightVariable)
        (cond (Nat.beq leftExponent rightExponent)
          (grbExpLexLess leftRest rightRest)
          (grbNatLess leftExponent rightExponent))
        (grbNatLess rightVariable leftVariable)

/-- Irreflexivity of the lex order. -/
theorem grbExpLexLessIrrefl : (exp : GrbExp) → grbExpLexLess exp exp = false
  | [] => rfl
  | GrbVarPower.mk headVariable headExponent :: rest => by
      show cond (Nat.beq headVariable headVariable)
          (cond (Nat.beq headExponent headExponent)
            (grbExpLexLess rest rest)
            (grbNatLess headExponent headExponent))
          (grbNatLess headVariable headVariable) = false
      rw [grbNatBeqRefl headVariable, grbNatBeqRefl headExponent]
      exact grbExpLexLessIrrefl rest

/-- Asymmetry of the lex order. -/
theorem grbExpLexLessAsym : (left right : GrbExp) → grbExpLexLess left right = true →
    grbExpLexLess right left = false
  | [], [], hLess => Bool.noConfusion hLess
  | [], _ :: _, _ => rfl
  | _ :: _, [], hLess => Bool.noConfusion hLess
  | GrbVarPower.mk leftVariable leftExponent :: leftRest,
      GrbVarPower.mk rightVariable rightExponent :: rightRest, hLess => by
      have hFull : cond (Nat.beq leftVariable rightVariable)
          (cond (Nat.beq leftExponent rightExponent)
            (grbExpLexLess leftRest rightRest)
            (grbNatLess leftExponent rightExponent))
          (grbNatLess rightVariable leftVariable) = true := hLess
      show cond (Nat.beq rightVariable leftVariable)
          (cond (Nat.beq rightExponent leftExponent)
            (grbExpLexLess rightRest leftRest)
            (grbNatLess rightExponent leftExponent))
          (grbNatLess leftVariable rightVariable) = false
      cases hVariable : Nat.beq leftVariable rightVariable with
      | true =>
          rw [hVariable] at hFull
          have variableEq := grbNatBeqEq leftVariable rightVariable hVariable
          rw [← variableEq, grbNatBeqRefl leftVariable]
          cases hExponent : Nat.beq leftExponent rightExponent with
          | true =>
              rw [hExponent] at hFull
              have exponentEq := grbNatBeqEq leftExponent rightExponent hExponent
              rw [← exponentEq, grbNatBeqRefl leftExponent]
              exact grbExpLexLessAsym leftRest rightRest hFull
          | false =>
              rw [hExponent] at hFull
              rw [grbNatBeqSymmFalse leftExponent rightExponent hExponent]
              exact grbNatLessAsym leftExponent rightExponent hFull
      | false =>
          rw [hVariable] at hFull
          rw [grbNatBeqSymmFalse leftVariable rightVariable hVariable]
          exact grbNatLessAsym rightVariable leftVariable hFull

/-- Transitivity of the lex order. -/
theorem grbExpLexLessTrans : (first second third : GrbExp) →
    grbExpLexLess first second = true → grbExpLexLess second third = true →
    grbExpLexLess first third = true
  | [], [], _, hFirst, _ => Bool.noConfusion hFirst
  | [], _ :: _, [], _, hSecond => Bool.noConfusion hSecond
  | [], _ :: _, _ :: _, _, _ => rfl
  | _ :: _, [], _, hFirst, _ => Bool.noConfusion hFirst
  | _ :: _, _ :: _, [], _, hSecond => Bool.noConfusion hSecond
  | GrbVarPower.mk firstVariable firstExponent :: firstRest,
      GrbVarPower.mk secondVariable secondExponent :: secondRest,
      GrbVarPower.mk thirdVariable thirdExponent :: thirdRest, hFirst, hSecond => by
      have hFull1 : cond (Nat.beq firstVariable secondVariable)
          (cond (Nat.beq firstExponent secondExponent)
            (grbExpLexLess firstRest secondRest)
            (grbNatLess firstExponent secondExponent))
          (grbNatLess secondVariable firstVariable) = true := hFirst
      have hFull2 : cond (Nat.beq secondVariable thirdVariable)
          (cond (Nat.beq secondExponent thirdExponent)
            (grbExpLexLess secondRest thirdRest)
            (grbNatLess secondExponent thirdExponent))
          (grbNatLess thirdVariable secondVariable) = true := hSecond
      show cond (Nat.beq firstVariable thirdVariable)
          (cond (Nat.beq firstExponent thirdExponent)
            (grbExpLexLess firstRest thirdRest)
            (grbNatLess firstExponent thirdExponent))
          (grbNatLess thirdVariable firstVariable) = true
      cases hVariable1 : Nat.beq firstVariable secondVariable with
      | true =>
          rw [hVariable1] at hFull1
          have variableEq1 := grbNatBeqEq firstVariable secondVariable hVariable1
          cases hVariable2 : Nat.beq secondVariable thirdVariable with
          | true =>
              rw [hVariable2] at hFull2
              have variableEq2 := grbNatBeqEq secondVariable thirdVariable hVariable2
              have hVariable13 : Nat.beq firstVariable thirdVariable = true := by
                rw [variableEq1, variableEq2]
                exact grbNatBeqRefl thirdVariable
              rw [hVariable13]
              cases hExponent1 : Nat.beq firstExponent secondExponent with
              | true =>
                  rw [hExponent1] at hFull1
                  have exponentEq1 := grbNatBeqEq firstExponent secondExponent hExponent1
                  cases hExponent2 : Nat.beq secondExponent thirdExponent with
                  | true =>
                      rw [hExponent2] at hFull2
                      have exponentEq2 := grbNatBeqEq secondExponent thirdExponent hExponent2
                      have hExponent13 : Nat.beq firstExponent thirdExponent = true := by
                        rw [exponentEq1, exponentEq2]
                        exact grbNatBeqRefl thirdExponent
                      rw [hExponent13]
                      exact grbExpLexLessTrans firstRest secondRest thirdRest hFull1 hFull2
                  | false =>
                      rw [hExponent2] at hFull2
                      have hExponent13 : Nat.beq firstExponent thirdExponent = false := by
                        rw [exponentEq1]
                        exact hExponent2
                      rw [hExponent13, exponentEq1]
                      exact hFull2
              | false =>
                  rw [hExponent1] at hFull1
                  cases hExponent2 : Nat.beq secondExponent thirdExponent with
                  | true =>
                      have exponentEq2 := grbNatBeqEq secondExponent thirdExponent hExponent2
                      have hExponent13 : Nat.beq firstExponent thirdExponent = false := by
                        rw [← exponentEq2]
                        exact hExponent1
                      rw [hExponent13, ← exponentEq2]
                      exact hFull1
                  | false =>
                      rw [hExponent2] at hFull2
                      have lessThrough :=
                        grbNatLessTrans firstExponent secondExponent thirdExponent hFull1 hFull2
                      have hExponent13 : Nat.beq firstExponent thirdExponent = false := by
                        cases hExponent13c : Nat.beq firstExponent thirdExponent with
                        | false => rfl
                        | true =>
                            have exponentEq13 :=
                              grbNatBeqEq firstExponent thirdExponent hExponent13c
                            rw [← exponentEq13] at hFull2
                            exact Bool.noConfusion
                              ((grbNatLessAsym firstExponent secondExponent hFull1).symm.trans
                                hFull2)
                      rw [hExponent13]
                      exact lessThrough
          | false =>
              rw [hVariable2] at hFull2
              have hVariable13 : Nat.beq firstVariable thirdVariable = false := by
                rw [variableEq1]
                exact hVariable2
              rw [hVariable13, variableEq1]
              exact hFull2
      | false =>
          rw [hVariable1] at hFull1
          cases hVariable2 : Nat.beq secondVariable thirdVariable with
          | true =>
              have variableEq2 := grbNatBeqEq secondVariable thirdVariable hVariable2
              have hVariable13 : Nat.beq firstVariable thirdVariable = false := by
                rw [← variableEq2]
                exact hVariable1
              rw [hVariable13, ← variableEq2]
              exact hFull1
          | false =>
              rw [hVariable2] at hFull2
              have lessThrough :=
                grbNatLessTrans thirdVariable secondVariable firstVariable hFull2 hFull1
              have hVariable13 : Nat.beq firstVariable thirdVariable = false := by
                cases hVariable13c : Nat.beq firstVariable thirdVariable with
                | false => rfl
                | true =>
                    have variableEq13 := grbNatBeqEq firstVariable thirdVariable hVariable13c
                    rw [variableEq13] at hFull1
                    exact Bool.noConfusion
                      ((grbNatLessAsym thirdVariable secondVariable hFull2).symm.trans hFull1)
              rw [hVariable13]
              exact lessThrough

/-- Totality: beq-distinct exponent vectors compare strictly one way or the other. -/
theorem grbExpLexLessTotal : (left right : GrbExp) → grbExpBeq left right = false →
    grbExpLexLess left right = true ∨ grbExpLexLess right left = true
  | [], [], hBeq => Bool.noConfusion hBeq
  | [], _ :: _, _ => Or.inl rfl
  | _ :: _, [], _ => Or.inr rfl
  | GrbVarPower.mk leftVariable leftExponent :: leftRest,
      GrbVarPower.mk rightVariable rightExponent :: rightRest, hBeq => by
      cases hVariable : Nat.beq leftVariable rightVariable with
      | false =>
          cases grbNatLessTotal leftVariable rightVariable hVariable with
          | inl lessLeftRight =>
              apply Or.inr
              show cond (Nat.beq rightVariable leftVariable)
                  (cond (Nat.beq rightExponent leftExponent)
                    (grbExpLexLess rightRest leftRest)
                    (grbNatLess rightExponent leftExponent))
                  (grbNatLess leftVariable rightVariable) = true
              rw [grbNatBeqSymmFalse leftVariable rightVariable hVariable]
              exact lessLeftRight
          | inr lessRightLeft =>
              apply Or.inl
              show cond (Nat.beq leftVariable rightVariable)
                  (cond (Nat.beq leftExponent rightExponent)
                    (grbExpLexLess leftRest rightRest)
                    (grbNatLess leftExponent rightExponent))
                  (grbNatLess rightVariable leftVariable) = true
              rw [hVariable]
              exact lessRightLeft
      | true =>
          have variableEq := grbNatBeqEq leftVariable rightVariable hVariable
          cases hExponent : Nat.beq leftExponent rightExponent with
          | false =>
              cases grbNatLessTotal leftExponent rightExponent hExponent with
              | inl lessLeftRight =>
                  apply Or.inl
                  show cond (Nat.beq leftVariable rightVariable)
                      (cond (Nat.beq leftExponent rightExponent)
                        (grbExpLexLess leftRest rightRest)
                        (grbNatLess leftExponent rightExponent))
                      (grbNatLess rightVariable leftVariable) = true
                  rw [hVariable, hExponent]
                  exact lessLeftRight
              | inr lessRightLeft =>
                  apply Or.inr
                  show cond (Nat.beq rightVariable leftVariable)
                      (cond (Nat.beq rightExponent leftExponent)
                        (grbExpLexLess rightRest leftRest)
                        (grbNatLess rightExponent leftExponent))
                      (grbNatLess leftVariable rightVariable) = true
                  rw [← variableEq, grbNatBeqRefl leftVariable,
                    grbNatBeqSymmFalse leftExponent rightExponent hExponent]
                  exact lessRightLeft
          | true =>
              have exponentEq := grbNatBeqEq leftExponent rightExponent hExponent
              have varPowTrue : grbVarPowerBeq (GrbVarPower.mk leftVariable leftExponent)
                  (GrbVarPower.mk rightVariable rightExponent) = true := by
                show (Nat.beq leftVariable rightVariable && Nat.beq leftExponent rightExponent) =
                  true
                rw [hVariable, hExponent]
                rfl
              have tailBeqFalse : grbExpBeq leftRest rightRest = false := by
                have hCons : (grbVarPowerBeq (GrbVarPower.mk leftVariable leftExponent)
                    (GrbVarPower.mk rightVariable rightExponent) &&
                    grbExpBeq leftRest rightRest) = false := hBeq
                exact grbBoolAndTrueLeftFalse hCons varPowTrue
              cases grbExpLexLessTotal leftRest rightRest tailBeqFalse with
              | inl tailLess =>
                  apply Or.inl
                  show cond (Nat.beq leftVariable rightVariable)
                      (cond (Nat.beq leftExponent rightExponent)
                        (grbExpLexLess leftRest rightRest)
                        (grbNatLess leftExponent rightExponent))
                      (grbNatLess rightVariable leftVariable) = true
                  rw [hVariable, hExponent]
                  exact tailLess
              | inr tailLess =>
                  apply Or.inr
                  show cond (Nat.beq rightVariable leftVariable)
                      (cond (Nat.beq rightExponent leftExponent)
                        (grbExpLexLess rightRest leftRest)
                        (grbNatLess rightExponent leftExponent))
                      (grbNatLess leftVariable rightVariable) = true
                  rw [← variableEq, grbNatBeqRefl leftVariable, ← exponentEq,
                    grbNatBeqRefl leftExponent]
                  exact tailLess

/-- The graded-lex monomial order: total degree first, then lex. -/
def grbMonoLess (left right : GrbExp) : Bool :=
  cond (Nat.beq (grbExpDegree left) (grbExpDegree right))
    (grbExpLexLess left right)
    (grbNatLess (grbExpDegree left) (grbExpDegree right))

/-- Irreflexivity of the monomial order. -/
theorem grbMonoLessIrrefl (exp : GrbExp) : grbMonoLess exp exp = false := by
  show cond (Nat.beq (grbExpDegree exp) (grbExpDegree exp))
      (grbExpLexLess exp exp)
      (grbNatLess (grbExpDegree exp) (grbExpDegree exp)) = false
  rw [grbNatBeqRefl (grbExpDegree exp)]
  exact grbExpLexLessIrrefl exp

/-- Asymmetry of the monomial order. -/
theorem grbMonoLessAsym (left right : GrbExp) (hLess : grbMonoLess left right = true) :
    grbMonoLess right left = false := by
  have hFull : cond (Nat.beq (grbExpDegree left) (grbExpDegree right))
      (grbExpLexLess left right)
      (grbNatLess (grbExpDegree left) (grbExpDegree right)) = true := hLess
  show cond (Nat.beq (grbExpDegree right) (grbExpDegree left))
      (grbExpLexLess right left)
      (grbNatLess (grbExpDegree right) (grbExpDegree left)) = false
  cases hDegree : Nat.beq (grbExpDegree left) (grbExpDegree right) with
  | true =>
      rw [hDegree] at hFull
      have degreeEq := grbNatBeqEq (grbExpDegree left) (grbExpDegree right) hDegree
      rw [← degreeEq, grbNatBeqRefl (grbExpDegree left)]
      exact grbExpLexLessAsym left right hFull
  | false =>
      rw [hDegree] at hFull
      rw [grbNatBeqSymmFalse (grbExpDegree left) (grbExpDegree right) hDegree]
      exact grbNatLessAsym (grbExpDegree left) (grbExpDegree right) hFull

/-- Transitivity of the monomial order. -/
theorem grbMonoLessTrans (first second third : GrbExp)
    (hFirst : grbMonoLess first second = true) (hSecond : grbMonoLess second third = true) :
    grbMonoLess first third = true := by
  have hFull1 : cond (Nat.beq (grbExpDegree first) (grbExpDegree second))
      (grbExpLexLess first second)
      (grbNatLess (grbExpDegree first) (grbExpDegree second)) = true := hFirst
  have hFull2 : cond (Nat.beq (grbExpDegree second) (grbExpDegree third))
      (grbExpLexLess second third)
      (grbNatLess (grbExpDegree second) (grbExpDegree third)) = true := hSecond
  show cond (Nat.beq (grbExpDegree first) (grbExpDegree third))
      (grbExpLexLess first third)
      (grbNatLess (grbExpDegree first) (grbExpDegree third)) = true
  cases hDegree1 : Nat.beq (grbExpDegree first) (grbExpDegree second) with
  | true =>
      rw [hDegree1] at hFull1
      have degreeEq1 := grbNatBeqEq (grbExpDegree first) (grbExpDegree second) hDegree1
      cases hDegree2 : Nat.beq (grbExpDegree second) (grbExpDegree third) with
      | true =>
          rw [hDegree2] at hFull2
          have degreeEq2 := grbNatBeqEq (grbExpDegree second) (grbExpDegree third) hDegree2
          have hDegree13 : Nat.beq (grbExpDegree first) (grbExpDegree third) = true := by
            rw [degreeEq1, degreeEq2]
            exact grbNatBeqRefl (grbExpDegree third)
          rw [hDegree13]
          exact grbExpLexLessTrans first second third hFull1 hFull2
      | false =>
          rw [hDegree2] at hFull2
          have hDegree13 : Nat.beq (grbExpDegree first) (grbExpDegree third) = false := by
            rw [degreeEq1]
            exact hDegree2
          rw [hDegree13, degreeEq1]
          exact hFull2
  | false =>
      rw [hDegree1] at hFull1
      cases hDegree2 : Nat.beq (grbExpDegree second) (grbExpDegree third) with
      | true =>
          have degreeEq2 := grbNatBeqEq (grbExpDegree second) (grbExpDegree third) hDegree2
          have hDegree13 : Nat.beq (grbExpDegree first) (grbExpDegree third) = false := by
            rw [← degreeEq2]
            exact hDegree1
          rw [hDegree13, ← degreeEq2]
          exact hFull1
      | false =>
          rw [hDegree2] at hFull2
          have lessThrough := grbNatLessTrans (grbExpDegree first) (grbExpDegree second)
            (grbExpDegree third) hFull1 hFull2
          have hDegree13 : Nat.beq (grbExpDegree first) (grbExpDegree third) = false := by
            cases hDegree13c : Nat.beq (grbExpDegree first) (grbExpDegree third) with
            | false => rfl
            | true =>
                have degreeEq13 :=
                  grbNatBeqEq (grbExpDegree first) (grbExpDegree third) hDegree13c
                rw [← degreeEq13] at hFull2
                exact Bool.noConfusion
                  ((grbNatLessAsym (grbExpDegree first) (grbExpDegree second)
                    hFull1).symm.trans hFull2)
          rw [hDegree13]
          exact lessThrough

/-- Totality: beq-distinct monomials compare strictly one way or the other. -/
theorem grbMonoLessTotal (left right : GrbExp) (hBeq : grbExpBeq left right = false) :
    grbMonoLess left right = true ∨ grbMonoLess right left = true := by
  cases hDegree : Nat.beq (grbExpDegree left) (grbExpDegree right) with
  | true =>
      have degreeEq := grbNatBeqEq (grbExpDegree left) (grbExpDegree right) hDegree
      cases grbExpLexLessTotal left right hBeq with
      | inl lexLeftRight =>
          apply Or.inl
          show cond (Nat.beq (grbExpDegree left) (grbExpDegree right))
              (grbExpLexLess left right)
              (grbNatLess (grbExpDegree left) (grbExpDegree right)) = true
          rw [hDegree]
          exact lexLeftRight
      | inr lexRightLeft =>
          apply Or.inr
          show cond (Nat.beq (grbExpDegree right) (grbExpDegree left))
              (grbExpLexLess right left)
              (grbNatLess (grbExpDegree right) (grbExpDegree left)) = true
          rw [← degreeEq, grbNatBeqRefl (grbExpDegree left)]
          exact lexRightLeft
  | false =>
      cases grbNatLessTotal (grbExpDegree left) (grbExpDegree right) hDegree with
      | inl lessLeftRight =>
          apply Or.inl
          show cond (Nat.beq (grbExpDegree left) (grbExpDegree right))
              (grbExpLexLess left right)
              (grbNatLess (grbExpDegree left) (grbExpDegree right)) = true
          rw [hDegree]
          exact lessLeftRight
      | inr lessRightLeft =>
          apply Or.inr
          show cond (Nat.beq (grbExpDegree right) (grbExpDegree left))
              (grbExpLexLess right left)
              (grbNatLess (grbExpDegree right) (grbExpDegree left)) = true
          rw [grbNatBeqSymmFalse (grbExpDegree left) (grbExpDegree right) hDegree]
          exact lessRightLeft

/-! ## Polynomials over F2: sorted monomial lists, insert-fold arithmetic -/

/-- An F2 polynomial: monomials (exponent vectors) sorted strictly descending under
`grbMonoLess`; the coefficient of every stored monomial is 1, absent monomials have
coefficient 0 — the pair `(Exp, Coeff)` of the general design collapses. -/
abbrev GrbPoly := List GrbExp

/-- Structural Boolean equality on polynomials. -/
def grbPolyBeq : GrbPoly → GrbPoly → Bool
  | [], [] => true
  | [], _ :: _ => false
  | _ :: _, [] => false
  | leftHead :: leftRest, rightHead :: rightRest =>
      grbExpBeq leftHead rightHead && grbPolyBeq leftRest rightRest

/-- Reflexivity of `grbPolyBeq`. -/
theorem grbPolyBeqRefl : (poly : GrbPoly) → grbPolyBeq poly poly = true
  | [] => rfl
  | head :: rest => by
      show (grbExpBeq head head && grbPolyBeq rest rest) = true
      rw [grbExpBeqRefl head, grbPolyBeqRefl rest]
      rfl

/-- `grbPolyBeq` sound: beq-true polynomials are equal. -/
theorem grbPolyBeqEq : (left right : GrbPoly) → grbPolyBeq left right = true → left = right
  | [], [], _ => rfl
  | [], _ :: _, hBeq => Bool.noConfusion hBeq
  | _ :: _, [], hBeq => Bool.noConfusion hBeq
  | leftHead :: leftRest, rightHead :: rightRest, hBeq => by
      have hSplit := grbBoolAndElim _ _ hBeq
      rw [grbExpBeqEq leftHead rightHead hSplit.left,
        grbPolyBeqEq leftRest rightRest hSplit.right]

/-- The zero polynomial. -/
def grbZero : GrbPoly := []

/-- The constant-one polynomial (single monomial with empty exponent vector). -/
def grbOnePoly : GrbPoly := [[]]

/-- The degree-one polynomial in a single variable. -/
def grbVariablePoly (index : Nat) : GrbPoly :=
  [[{ variableIndex := index, exponent := 1 }]]

/-- Insert a monomial into a polynomial: collision is xor 1 1 = 0, so the pair DROPS
(characteristic two); otherwise place by the descending monomial order. -/
def grbMonoInsert (mono : GrbExp) : GrbPoly → GrbPoly
  | [] => [mono]
  | head :: rest =>
      cond (grbExpBeq mono head) rest
        (cond (grbMonoLess head mono)
          (mono :: head :: rest)
          (head :: grbMonoInsert mono rest))

/-- `grbMonoInsert` branch: collision — the pair cancels. -/
theorem grbMonoInsertOnCollision (mono head : GrbExp) (rest : GrbPoly)
    (hSame : grbExpBeq mono head = true) : grbMonoInsert mono (head :: rest) = rest := by
  show cond (grbExpBeq mono head) rest
      (cond (grbMonoLess head mono)
        (mono :: head :: rest)
        (head :: grbMonoInsert mono rest)) = rest
  rw [hSame]
  rfl

/-- `grbMonoInsert` branch: the inserted monomial dominates the head — prepend. -/
theorem grbMonoInsertOnGreater (mono head : GrbExp) (rest : GrbPoly)
    (hDistinct : grbExpBeq mono head = false) (hHeadLess : grbMonoLess head mono = true) :
    grbMonoInsert mono (head :: rest) = mono :: head :: rest := by
  show cond (grbExpBeq mono head) rest
      (cond (grbMonoLess head mono)
        (mono :: head :: rest)
        (head :: grbMonoInsert mono rest)) = mono :: head :: rest
  rw [hDistinct, hHeadLess]
  rfl

/-- `grbMonoInsert` branch: the head dominates — descend. -/
theorem grbMonoInsertOnSmaller (mono head : GrbExp) (rest : GrbPoly)
    (hDistinct : grbExpBeq mono head = false) (hNotGreater : grbMonoLess head mono = false) :
    grbMonoInsert mono (head :: rest) = head :: grbMonoInsert mono rest := by
  show cond (grbExpBeq mono head) rest
      (cond (grbMonoLess head mono)
        (mono :: head :: rest)
        (head :: grbMonoInsert mono rest)) = head :: grbMonoInsert mono rest
  rw [hDistinct, hNotGreater]
  rfl

/-- Polynomial addition over F2: insert-fold the left list into the right (symmetric
difference of monomial sets).  `grbAdd [] right = right` is definitional, and the
result is sorted whenever `right` is — for ANY left operand. -/
def grbAdd : GrbPoly → GrbPoly → GrbPoly
  | [], right => right
  | mono :: rest, right => grbMonoInsert mono (grbAdd rest right)

/-- F2 negation is the identity: `-1 = 1`. -/
def grbNeg (poly : GrbPoly) : GrbPoly := poly

/-- Scalar action of the F2 coefficient field. -/
def grbScale (scalar : Bool) (poly : GrbPoly) : GrbPoly := cond scalar poly []

/-- Multiply every monomial of a polynomial by a fixed monomial (F2 coefficient 1·1). -/
def grbScaleByMonomial (mono : GrbExp) : GrbPoly → GrbPoly
  | [] => []
  | head :: rest => grbExpMul mono head :: grbScaleByMonomial mono rest

/-- Polynomial multiplication: distribute `grbScaleByMonomial` over `grbAdd`. -/
def grbMul : GrbPoly → GrbPoly → GrbPoly
  | [], [] => []
  | [], _ :: _ => []
  | mono :: rest, right => grbAdd (grbScaleByMonomial mono right) (grbMul rest right)

/-- `grbMul [] right = []` for every right operand. -/
theorem grbMulNilLeft : (right : GrbPoly) → grbMul [] right = []
  | [] => rfl
  | _ :: _ => rfl

/-- Sum of pairwise products `Σ cofᵢ·genᵢ` (mismatched lengths truncate to zero). -/
def grbSumOfProducts : List GrbPoly → List GrbPoly → GrbPoly
  | [], [] => []
  | [], _ :: _ => []
  | _ :: _, [] => []
  | cofactor :: cofactorRest, gen :: genRest =>
      grbAdd (grbMul cofactor gen) (grbSumOfProducts cofactorRest genRest)

/-! ## Sortedness: the strict-descending invariant -/

/-- Strictly-descending sortedness of a monomial list under `grbMonoLess`. -/
inductive GrbPolySorted : GrbPoly → Prop where
  | nilIsSorted : GrbPolySorted []
  | singleIsSorted (mono : GrbExp) : GrbPolySorted [mono]
  | consIsSorted (first second : GrbExp) (rest : GrbPoly)
      (isDescending : grbMonoLess second first = true)
      (tailIsSorted : GrbPolySorted (second :: rest)) :
      GrbPolySorted (first :: second :: rest)

/-- The tail of a sorted list is sorted. -/
theorem grbSortedTail (head : GrbExp) (rest : GrbPoly)
    (hSorted : GrbPolySorted (head :: rest)) : GrbPolySorted rest := by
  cases hSorted with
  | singleIsSorted _ => exact GrbPolySorted.nilIsSorted
  | consIsSorted _ _ _ _ tailIsSorted => exact tailIsSorted

/-- Dropping the second element of a sorted list keeps it sorted (via transitivity). -/
theorem grbSortedSkip (first second : GrbExp) (rest : GrbPoly)
    (hSorted : GrbPolySorted (first :: second :: rest)) : GrbPolySorted (first :: rest) := by
  cases hSorted with
  | consIsSorted _ _ _ isDescending tailIsSorted =>
      cases tailIsSorted with
      | singleIsSorted _ => exact GrbPolySorted.singleIsSorted first
      | consIsSorted _ _ _ isDescendingTail tailTailIsSorted =>
          exact GrbPolySorted.consIsSorted _ _ _
            (grbMonoLessTrans _ _ _ isDescendingTail isDescending) tailTailIsSorted

/-- Inserting a monomial strictly below a dominating head keeps the list sorted. -/
theorem grbMonoInsertUnderHead : (rest : GrbPoly) → (head mono : GrbExp) →
    grbMonoLess mono head = true → GrbPolySorted (head :: rest) →
    GrbPolySorted (head :: grbMonoInsert mono rest)
  | [], head, mono, hMonoLessHead, _ =>
      GrbPolySorted.consIsSorted head mono [] hMonoLessHead (GrbPolySorted.singleIsSorted mono)
  | second :: rest2, head, mono, hMonoLessHead, hSortedAll => by
      cases hSortedAll with
      | consIsSorted _ _ _ hSecondLessHead hTailSorted =>
          cases hBeq : grbExpBeq mono second with
          | true =>
              rw [grbMonoInsertOnCollision mono second rest2 hBeq]
              exact grbSortedSkip head second rest2
                (GrbPolySorted.consIsSorted _ _ _ hSecondLessHead hTailSorted)
          | false =>
              cases hLess : grbMonoLess second mono with
              | true =>
                  rw [grbMonoInsertOnGreater mono second rest2 hBeq hLess]
                  exact GrbPolySorted.consIsSorted _ _ _ hMonoLessHead
                    (GrbPolySorted.consIsSorted _ _ _ hLess hTailSorted)
              | false =>
                  have hMonoLessSecond : grbMonoLess mono second = true := by
                    cases grbMonoLessTotal mono second hBeq with
                    | inl hForward => exact hForward
                    | inr hBackward => exact Bool.noConfusion (hLess.symm.trans hBackward)
                  rw [grbMonoInsertOnSmaller mono second rest2 hBeq hLess]
                  exact GrbPolySorted.consIsSorted _ _ _ hSecondLessHead
                    (grbMonoInsertUnderHead rest2 second mono hMonoLessSecond hTailSorted)

/-- `grbMonoInsert` preserves sortedness. -/
theorem grbMonoInsertKeepsSorted (mono : GrbExp) : (poly : GrbPoly) →
    GrbPolySorted poly → GrbPolySorted (grbMonoInsert mono poly)
  | [], _ => GrbPolySorted.singleIsSorted mono
  | head :: rest, hSorted => by
      cases hBeq : grbExpBeq mono head with
      | true =>
          rw [grbMonoInsertOnCollision mono head rest hBeq]
          exact grbSortedTail head rest hSorted
      | false =>
          cases hLess : grbMonoLess head mono with
          | true =>
              rw [grbMonoInsertOnGreater mono head rest hBeq hLess]
              exact GrbPolySorted.consIsSorted _ _ _ hLess hSorted
          | false =>
              have hMonoLessHead : grbMonoLess mono head = true := by
                cases grbMonoLessTotal mono head hBeq with
                | inl hForward => exact hForward
                | inr hBackward => exact Bool.noConfusion (hLess.symm.trans hBackward)
              rw [grbMonoInsertOnSmaller mono head rest hBeq hLess]
              exact grbMonoInsertUnderHead rest head mono hMonoLessHead hSorted

/-- `grbAdd left right` is sorted whenever `right` is — for ANY left operand. -/
theorem grbAddKeepsSorted : (left right : GrbPoly) → GrbPolySorted right →
    GrbPolySorted (grbAdd left right)
  | [], _, hRightSorted => hRightSorted
  | mono :: rest, right, hRightSorted =>
      grbMonoInsertKeepsSorted mono (grbAdd rest right)
        (grbAddKeepsSorted rest right hRightSorted)

/-- `grbMul` output is unconditionally sorted. -/
theorem grbMulIsSorted : (left right : GrbPoly) → GrbPolySorted (grbMul left right)
  | [], [] => GrbPolySorted.nilIsSorted
  | [], _ :: _ => GrbPolySorted.nilIsSorted
  | mono :: rest, right =>
      grbAddKeepsSorted (grbScaleByMonomial mono right) (grbMul rest right)
        (grbMulIsSorted rest right)

/-- `grbSumOfProducts` output is unconditionally sorted. -/
theorem grbSumOfProductsIsSorted : (cofactors generators : List GrbPoly) →
    GrbPolySorted (grbSumOfProducts cofactors generators)
  | [], [] => GrbPolySorted.nilIsSorted
  | [], _ :: _ => GrbPolySorted.nilIsSorted
  | _ :: _, [] => GrbPolySorted.nilIsSorted
  | cofactor :: cofactorRest, gen :: genRest =>
      grbAddKeepsSorted (grbMul cofactor gen) (grbSumOfProducts cofactorRest genRest)
        (grbSumOfProductsIsSorted cofactorRest genRest)

/-! ## The F2 coefficient scan and sorted-list extensionality

`grbCoeff` is the xor-parity coefficient function — a homomorphism from ARBITRARY
monomial lists; on sorted lists it is the exact coefficient, and two sorted lists with
pointwise-equal coefficient functions are byte-equal (`grbPolyExtensionality`).  Every
AC identity downstream is one extensionality fire over a Bool case-bash. -/

/-- F2 coefficient of a monomial in a polynomial (xor-parity scan). -/
def grbCoeff : GrbPoly → GrbExp → Bool
  | [], _ => false
  | mono :: rest, exp => grbBoolXor (grbExpBeq exp mono) (grbCoeff rest exp)

/-- Coefficient scan through an insertion. -/
theorem grbCoeffMonoInsert : (poly : GrbPoly) → (mono exp : GrbExp) →
    grbCoeff (grbMonoInsert mono poly) exp = grbBoolXor (grbExpBeq exp mono) (grbCoeff poly exp)
  | [], _, _ => rfl
  | head :: rest, mono, exp => by
      cases hBeq : grbExpBeq mono head with
      | true =>
          have monoEq := grbExpBeqEq mono head hBeq
          rw [grbMonoInsertOnCollision mono head rest hBeq, monoEq]
          show grbCoeff rest exp =
            grbBoolXor (grbExpBeq exp head) (grbBoolXor (grbExpBeq exp head) (grbCoeff rest exp))
          exact (grbBoolXorLeftSelfCancel (grbExpBeq exp head) (grbCoeff rest exp)).symm
      | false =>
          cases hLess : grbMonoLess head mono with
          | true =>
              rw [grbMonoInsertOnGreater mono head rest hBeq hLess]
              rfl
          | false =>
              rw [grbMonoInsertOnSmaller mono head rest hBeq hLess]
              show grbBoolXor (grbExpBeq exp head) (grbCoeff (grbMonoInsert mono rest) exp) =
                grbBoolXor (grbExpBeq exp mono)
                  (grbBoolXor (grbExpBeq exp head) (grbCoeff rest exp))
              rw [grbCoeffMonoInsert rest mono exp]
              exact grbBoolXorSwapLeft (grbExpBeq exp head) (grbExpBeq exp mono)
                (grbCoeff rest exp)

/-- The coefficient scan is an F2 homomorphism through `grbAdd` — on ARBITRARY lists. -/
theorem grbCoeffAdd : (left right : GrbPoly) → (exp : GrbExp) →
    grbCoeff (grbAdd left right) exp = grbBoolXor (grbCoeff left exp) (grbCoeff right exp)
  | [], _, _ => rfl
  | mono :: rest, right, exp => by
      show grbCoeff (grbMonoInsert mono (grbAdd rest right)) exp = _
      rw [grbCoeffMonoInsert (grbAdd rest right) mono exp, grbCoeffAdd rest right exp]
      exact (grbBoolXorAssoc (grbExpBeq exp mono) (grbCoeff rest exp) (grbCoeff right exp)).symm

/-- In a sorted list, everything below the head misses the head's coefficient. -/
theorem grbCoeffFalseUnderHead : (tail : GrbPoly) → (exp : GrbExp) →
    GrbPolySorted (exp :: tail) → grbCoeff tail exp = false
  | [], _, _ => rfl
  | head :: rest, exp, hSortedAll => by
      cases hSortedAll with
      | consIsSorted _ _ _ hHeadLess hTailSorted =>
          show grbBoolXor (grbExpBeq exp head) (grbCoeff rest exp) = false
          cases hBeq : grbExpBeq exp head with
          | true =>
              have expEq := grbExpBeqEq exp head hBeq
              rw [expEq] at hHeadLess
              rw [grbMonoLessIrrefl head] at hHeadLess
              exact Bool.noConfusion hHeadLess
          | false =>
              exact grbCoeffFalseUnderHead rest exp
                (grbSortedSkip exp head rest
                  (GrbPolySorted.consIsSorted exp head rest hHeadLess hTailSorted))

/-- A monomial with coefficient 1 in the sorted tail sits strictly below the head. -/
theorem grbCoeffTrueImpliesLessThanHead : (tail : GrbPoly) → (head exp : GrbExp) →
    GrbPolySorted (head :: tail) → grbCoeff tail exp = true → grbMonoLess exp head = true
  | [], _, _, _, hCoeff => Bool.noConfusion hCoeff
  | second :: rest, head, exp, hSortedAll, hCoeff => by
      cases hSortedAll with
      | consIsSorted _ _ _ hSecondLess hTailSorted =>
          have hCoeffFull : grbBoolXor (grbExpBeq exp second) (grbCoeff rest exp) = true :=
            hCoeff
          cases hBeq : grbExpBeq exp second with
          | true =>
              have expEq := grbExpBeqEq exp second hBeq
              rw [expEq]
              exact hSecondLess
          | false =>
              rw [hBeq] at hCoeffFull
              exact grbMonoLessTrans exp second head
                (grbCoeffTrueImpliesLessThanHead rest second exp hTailSorted hCoeffFull)
                hSecondLess

/-- **Sorted-list extensionality**: sorted polynomials with pointwise-equal F2
coefficient functions are byte-equal lists.  The canonical-form keystone. -/
theorem grbPolyExtensionality : (left right : GrbPoly) → GrbPolySorted left →
    GrbPolySorted right → ((exp : GrbExp) → grbCoeff left exp = grbCoeff right exp) →
    left = right
  | [], [], _, _, _ => rfl
  | [], headRight :: restRight, _, hRightSorted, hPointwise => by
      exfalso
      have hCoeffAtHead : grbCoeff (headRight :: restRight) headRight = true := by
        show grbBoolXor (grbExpBeq headRight headRight) (grbCoeff restRight headRight) = true
        rw [grbExpBeqRefl headRight,
          grbCoeffFalseUnderHead restRight headRight hRightSorted]
        rfl
      exact Bool.noConfusion ((hPointwise headRight).trans hCoeffAtHead)
  | headLeft :: restLeft, [], hLeftSorted, _, hPointwise => by
      exfalso
      have hCoeffAtHead : grbCoeff (headLeft :: restLeft) headLeft = true := by
        show grbBoolXor (grbExpBeq headLeft headLeft) (grbCoeff restLeft headLeft) = true
        rw [grbExpBeqRefl headLeft, grbCoeffFalseUnderHead restLeft headLeft hLeftSorted]
        rfl
      exact Bool.noConfusion ((hPointwise headLeft).symm.trans hCoeffAtHead)
  | headLeft :: restLeft, headRight :: restRight, hLeftSorted, hRightSorted, hPointwise => by
      cases hHeads : grbExpBeq headLeft headRight with
      | true =>
          have headsEqual := grbExpBeqEq headLeft headRight hHeads
          subst headsEqual
          have tailsAgree : (exp : GrbExp) → grbCoeff restLeft exp = grbCoeff restRight exp := by
            intro exp
            have hPointAt : grbBoolXor (grbExpBeq exp headLeft) (grbCoeff restLeft exp) =
                grbBoolXor (grbExpBeq exp headLeft) (grbCoeff restRight exp) := hPointwise exp
            exact grbBoolXorLeftInjective (grbExpBeq exp headLeft) (grbCoeff restLeft exp)
              (grbCoeff restRight exp) hPointAt
          exact congrArg (List.cons headLeft)
            (grbPolyExtensionality restLeft restRight
              (grbSortedTail headLeft restLeft hLeftSorted)
              (grbSortedTail headLeft restRight hRightSorted) tailsAgree)
      | false =>
          exfalso
          have hCoeffLeftAtLeftHead : grbCoeff (headLeft :: restLeft) headLeft = true := by
            show grbBoolXor (grbExpBeq headLeft headLeft) (grbCoeff restLeft headLeft) = true
            rw [grbExpBeqRefl headLeft,
              grbCoeffFalseUnderHead restLeft headLeft hLeftSorted]
            rfl
          have hCoeffRightAtLeftHead : grbCoeff restRight headLeft = true := by
            have hPointAt : grbBoolXor (grbExpBeq headLeft headRight)
                (grbCoeff restRight headLeft) = true :=
              (hPointwise headLeft).symm.trans hCoeffLeftAtLeftHead
            rw [hHeads] at hPointAt
            exact hPointAt
          have hLeftLessRight := grbCoeffTrueImpliesLessThanHead restRight headRight headLeft
            hRightSorted hCoeffRightAtLeftHead
          have hCoeffRightAtRightHead : grbCoeff (headRight :: restRight) headRight = true := by
            show grbBoolXor (grbExpBeq headRight headRight) (grbCoeff restRight headRight) = true
            rw [grbExpBeqRefl headRight,
              grbCoeffFalseUnderHead restRight headRight hRightSorted]
            rfl
          have hHeadsSym : grbExpBeq headRight headLeft = false := by
            cases hBackward : grbExpBeq headRight headLeft with
            | false => rfl
            | true =>
                have backwardEq := grbExpBeqEq headRight headLeft hBackward
                rw [backwardEq] at hHeads
                rw [grbExpBeqRefl headLeft] at hHeads
                exact Bool.noConfusion hHeads
          have hCoeffLeftAtRightHead : grbCoeff restLeft headRight = true := by
            have hPointAt : grbBoolXor (grbExpBeq headRight headLeft)
                (grbCoeff restLeft headRight) = true :=
              (hPointwise headRight).trans hCoeffRightAtRightHead
            rw [hHeadsSym] at hPointAt
            exact hPointAt
          have hRightLessLeft := grbCoeffTrueImpliesLessThanHead restLeft headLeft headRight
            hLeftSorted hCoeffLeftAtRightHead
          exact Bool.noConfusion
            ((grbMonoLessAsym headLeft headRight hLeftLessRight).symm.trans hRightLessLeft)

/-! ## The AC family the checker and finder consume — all one-fire extensionality -/

/-- `grbAdd poly [] = poly` on sorted input. -/
theorem grbAddNilRightIsIdentity (poly : GrbPoly) (hSorted : GrbPolySorted poly) :
    grbAdd poly [] = poly :=
  grbPolyExtensionality (grbAdd poly []) poly
    (grbAddKeepsSorted poly [] GrbPolySorted.nilIsSorted) hSorted
    (fun exp => by
      rw [grbCoeffAdd poly [] exp]
      exact grbBoolXorFalseRight (grbCoeff poly exp))

/-- Associativity of `grbAdd` (third operand sorted suffices). -/
theorem grbAddAssoc (first second third : GrbPoly) (hThirdSorted : GrbPolySorted third) :
    grbAdd (grbAdd first second) third = grbAdd first (grbAdd second third) :=
  grbPolyExtensionality (grbAdd (grbAdd first second) third)
    (grbAdd first (grbAdd second third))
    (grbAddKeepsSorted (grbAdd first second) third hThirdSorted)
    (grbAddKeepsSorted first (grbAdd second third)
      (grbAddKeepsSorted second third hThirdSorted))
    (fun exp => by
      rw [grbCoeffAdd (grbAdd first second) third exp, grbCoeffAdd first second exp,
        grbCoeffAdd first (grbAdd second third) exp, grbCoeffAdd second third exp]
      exact grbBoolXorAssoc (grbCoeff first exp) (grbCoeff second exp) (grbCoeff third exp))

/-- Left-swap for `grbAdd` (innermost operand sorted suffices). -/
theorem grbAddSwapLeft (first second rest : GrbPoly) (hRestSorted : GrbPolySorted rest) :
    grbAdd first (grbAdd second rest) = grbAdd second (grbAdd first rest) :=
  grbPolyExtensionality (grbAdd first (grbAdd second rest))
    (grbAdd second (grbAdd first rest))
    (grbAddKeepsSorted first (grbAdd second rest) (grbAddKeepsSorted second rest hRestSorted))
    (grbAddKeepsSorted second (grbAdd first rest) (grbAddKeepsSorted first rest hRestSorted))
    (fun exp => by
      rw [grbCoeffAdd first (grbAdd second rest) exp, grbCoeffAdd second rest exp,
        grbCoeffAdd second (grbAdd first rest) exp, grbCoeffAdd first rest exp]
      exact grbBoolXorSwapLeft (grbCoeff first exp) (grbCoeff second exp) (grbCoeff rest exp))

/-- Cross-cancellation: `(s + p) + (s + r) = p + r` — the reduce-step engine. -/
theorem grbAddCrossCancel (shared first rest : GrbPoly) (hRestSorted : GrbPolySorted rest) :
    grbAdd (grbAdd shared first) (grbAdd shared rest) = grbAdd first rest :=
  grbPolyExtensionality (grbAdd (grbAdd shared first) (grbAdd shared rest))
    (grbAdd first rest)
    (grbAddKeepsSorted (grbAdd shared first) (grbAdd shared rest)
      (grbAddKeepsSorted shared rest hRestSorted))
    (grbAddKeepsSorted first rest hRestSorted)
    (fun exp => by
      rw [grbCoeffAdd (grbAdd shared first) (grbAdd shared rest) exp,
        grbCoeffAdd shared first exp, grbCoeffAdd shared rest exp,
        grbCoeffAdd first rest exp]
      exact grbBoolXorCrossCancel (grbCoeff shared exp) (grbCoeff first exp)
        (grbCoeff rest exp))

/-- Left self-cancellation: `s + (s + r) = r` — the collision engine. -/
theorem grbAddSelfCancelLeft (shared rest : GrbPoly) (hRestSorted : GrbPolySorted rest) :
    grbAdd shared (grbAdd shared rest) = rest :=
  grbPolyExtensionality (grbAdd shared (grbAdd shared rest)) rest
    (grbAddKeepsSorted shared (grbAdd shared rest) (grbAddKeepsSorted shared rest hRestSorted))
    hRestSorted
    (fun exp => by
      rw [grbCoeffAdd shared (grbAdd shared rest) exp, grbCoeffAdd shared rest exp]
      exact grbBoolXorLeftSelfCancel (grbCoeff shared exp) (grbCoeff rest exp))

/-- Characteristic two at the list level: `p + p = 0` on sorted input. -/
theorem grbAddSelfIsZero (poly : GrbPoly) (hSorted : GrbPolySorted poly) :
    grbAdd poly poly = [] :=
  grbPolyExtensionality (grbAdd poly poly) []
    (grbAddKeepsSorted poly poly hSorted) GrbPolySorted.nilIsSorted
    (fun exp => by
      rw [grbCoeffAdd poly poly exp]
      exact grbBoolXorSelfIsFalse (grbCoeff poly exp))

/-- Multiplication distributes over a monomial insertion — the cofactor-update law. -/
theorem grbMulMonoInsert : (cofactor : GrbPoly) → (mono : GrbExp) → (gen : GrbPoly) →
    grbMul (grbMonoInsert mono cofactor) gen =
      grbAdd (grbScaleByMonomial mono gen) (grbMul cofactor gen)
  | [], _, _ => rfl
  | head :: rest, mono, gen => by
      cases hBeq : grbExpBeq mono head with
      | true =>
          have monoEq := grbExpBeqEq mono head hBeq
          rw [grbMonoInsertOnCollision mono head rest hBeq, monoEq]
          exact (grbAddSelfCancelLeft (grbScaleByMonomial head gen) (grbMul rest gen)
            (grbMulIsSorted rest gen)).symm
      | false =>
          cases hLess : grbMonoLess head mono with
          | true =>
              rw [grbMonoInsertOnGreater mono head rest hBeq hLess]
              rfl
          | false =>
              rw [grbMonoInsertOnSmaller mono head rest hBeq hLess]
              show grbAdd (grbScaleByMonomial head gen) (grbMul (grbMonoInsert mono rest) gen) =
                grbAdd (grbScaleByMonomial mono gen)
                  (grbAdd (grbScaleByMonomial head gen) (grbMul rest gen))
              rw [grbMulMonoInsert rest mono gen]
              exact grbAddSwapLeft (grbScaleByMonomial head gen) (grbScaleByMonomial mono gen)
                (grbMul rest gen) (grbMulIsSorted rest gen)

/-! ## THE CHECKER: semantic ideal membership + certificate soundness -/

/-- Bespoke list membership for generator lists. -/
inductive GrbMember : GrbPoly → List GrbPoly → Prop where
  | atHead (element : GrbPoly) (rest : List GrbPoly) : GrbMember element (element :: rest)
  | inTail (element head : GrbPoly) (rest : List GrbPoly)
      (isInRest : GrbMember element rest) : GrbMember element (head :: rest)

/-- **Semantic ideal membership**: the inductive closure of the generator list under
zero, addition, and scaling by ANY polynomial. -/
inductive GrbInIdeal (generators : List GrbPoly) : GrbPoly → Prop where
  | byZeroPolynomial : GrbInIdeal generators []
  | byGenerator (gen : GrbPoly) (isGenerator : GrbMember gen generators) :
      GrbInIdeal generators gen
  | byAddition (left right : GrbPoly) (leftInIdeal : GrbInIdeal generators left)
      (rightInIdeal : GrbInIdeal generators right) : GrbInIdeal generators (grbAdd left right)
  | byPolynomialScale (multiplier member : GrbPoly)
      (memberInIdeal : GrbInIdeal generators member) :
      GrbInIdeal generators (grbMul multiplier member)

/-- **THE CHECKER**: a certificate (cofactor list aligned with the generators) checks
when `Σ cofᵢ·genᵢ` is byte-equal to the target.  Pure polynomial arithmetic — no
search, no termination. -/
def grbCheckCertificate (generators cofactors : List GrbPoly) (target : GrbPoly) : Bool :=
  grbPolyBeq (grbSumOfProducts cofactors generators) target

/-- Every pairwise-product sum over a sublist of the generators is in the ideal. -/
theorem grbSumOfProductsInIdeal : (cofactors selected : List GrbPoly) →
    (generators : List GrbPoly) →
    ((gen : GrbPoly) → GrbMember gen selected → GrbMember gen generators) →
    GrbInIdeal generators (grbSumOfProducts cofactors selected)
  | [], [], _, _ => GrbInIdeal.byZeroPolynomial
  | [], _ :: _, _, _ => GrbInIdeal.byZeroPolynomial
  | _ :: _, [], _, _ => GrbInIdeal.byZeroPolynomial
  | cofactor :: cofactorRest, gen :: genRest, generators, hSubset =>
      GrbInIdeal.byAddition _ _
        (GrbInIdeal.byPolynomialScale cofactor gen
          (GrbInIdeal.byGenerator gen (hSubset gen (GrbMember.atHead gen genRest))))
        (grbSumOfProductsInIdeal cofactorRest genRest generators
          (fun element isMember => hSubset element (GrbMember.inTail element gen genRest isMember)))

/-- **THE SOUNDNESS THEOREM**: an accepted certificate puts the target in the ideal. -/
theorem grbCertificateSound (generators cofactors : List GrbPoly) (target : GrbPoly)
    (hCheckPasses : grbCheckCertificate generators cofactors target = true) :
    GrbInIdeal generators target :=
  grbPolyBeqEq (grbSumOfProducts cofactors generators) target hCheckPasses ▸
    grbSumOfProductsInIdeal cofactors generators generators (fun _ isMember => isMember)

/-- The ring-equality dissolution shape: a certificate for the difference `p + (-q)`
puts the difference in the ideal (over F2 the difference IS `grbAdd p q`). -/
theorem grbDifferenceInIdealByCertificate (generators cofactors : List GrbPoly)
    (leftPoly rightPoly : GrbPoly)
    (hCheckPasses : grbCheckCertificate generators cofactors
      (grbAdd leftPoly (grbNeg rightPoly)) = true) :
    GrbInIdeal generators (grbAdd leftPoly (grbNeg rightPoly)) :=
  grbCertificateSound generators cofactors (grbAdd leftPoly (grbNeg rightPoly)) hCheckPasses

/-! ## Evaluation semantics: the homomorphism that grounds `GrbInIdeal` -/

/-- Boolean power (`b ^ e` with `b ^ 0 = 1`). -/
def grbBoolPow (base : Bool) : Nat → Bool
  | 0 => true
  | Nat.succ exponent => base && grbBoolPow base exponent

/-- Power homomorphism: `b ^ (m + n) = b ^ m && b ^ n`. -/
theorem grbBoolPowAdd : (base : Bool) → (left right : Nat) →
    grbBoolPow base (left + right) = (grbBoolPow base left && grbBoolPow base right)
  | base, left, 0 => by
      show grbBoolPow base left = (grbBoolPow base left && true)
      exact (grbBoolAndTrueRight (grbBoolPow base left)).symm
  | base, left, Nat.succ right => by
      show (base && grbBoolPow base (left + right)) =
        (grbBoolPow base left && (base && grbBoolPow base right))
      rw [grbBoolPowAdd base left right]
      exact grbBoolAndSwapLeft base (grbBoolPow base left) (grbBoolPow base right)

/-- Evaluate a monomial at an F2 point. -/
def grbEvalMonomial (point : Nat → Bool) : GrbExp → Bool
  | [] => true
  | varPower :: rest =>
      grbBoolPow (point varPower.variableIndex) varPower.exponent && grbEvalMonomial point rest

/-- Evaluate a polynomial at an F2 point (xor over its monomials). -/
def grbEvalPoly (point : Nat → Bool) : GrbPoly → Bool
  | [] => false
  | mono :: rest => grbBoolXor (grbEvalMonomial point mono) (grbEvalPoly point rest)

/-- Evaluation through `grbExpInsert`. -/
theorem grbEvalMonomialInsert : (exp : GrbExp) → (varPower : GrbVarPower) →
    (point : Nat → Bool) →
    grbEvalMonomial point (grbExpInsert varPower exp) =
      (grbBoolPow (point varPower.variableIndex) varPower.exponent && grbEvalMonomial point exp)
  | [], _, _ => rfl
  | head :: rest, varPower, point => by
      cases hVariable : Nat.beq varPower.variableIndex head.variableIndex with
      | true =>
          have variableEq := grbNatBeqEq varPower.variableIndex head.variableIndex hVariable
          rw [grbExpInsertOnSharedVariable varPower head rest hVariable]
          show (grbBoolPow (point head.variableIndex) (varPower.exponent + head.exponent) &&
            grbEvalMonomial point rest) = _
          rw [grbBoolPowAdd (point head.variableIndex) varPower.exponent head.exponent,
            variableEq]
          exact grbBoolAndAssoc (grbBoolPow (point head.variableIndex) varPower.exponent)
            (grbBoolPow (point head.variableIndex) head.exponent) (grbEvalMonomial point rest)
      | false =>
          cases hEarlier : grbNatLess varPower.variableIndex head.variableIndex with
          | true =>
              rw [grbExpInsertOnEarlierVariable varPower head rest hVariable hEarlier]
              rfl
          | false =>
              rw [grbExpInsertOnLaterVariable varPower head rest hVariable hEarlier]
              show (grbBoolPow (point head.variableIndex) head.exponent &&
                grbEvalMonomial point (grbExpInsert varPower rest)) = _
              rw [grbEvalMonomialInsert rest varPower point]
              exact grbBoolAndSwapLeft (grbBoolPow (point head.variableIndex) head.exponent)
                (grbBoolPow (point varPower.variableIndex) varPower.exponent)
                (grbEvalMonomial point rest)

/-- Evaluation is multiplicative through `grbExpMul`. -/
theorem grbEvalMonomialMul : (left right : GrbExp) → (point : Nat → Bool) →
    grbEvalMonomial point (grbExpMul left right) =
      (grbEvalMonomial point left && grbEvalMonomial point right)
  | [], _, _ => rfl
  | varPower :: rest, right, point => by
      show grbEvalMonomial point (grbExpInsert varPower (grbExpMul rest right)) = _
      rw [grbEvalMonomialInsert (grbExpMul rest right) varPower point,
        grbEvalMonomialMul rest right point]
      exact (grbBoolAndAssoc (grbBoolPow (point varPower.variableIndex) varPower.exponent)
        (grbEvalMonomial point rest) (grbEvalMonomial point right)).symm

/-- Evaluation through `grbScaleByMonomial`. -/
theorem grbEvalScaleByMonomial : (gen : GrbPoly) → (mono : GrbExp) → (point : Nat → Bool) →
    grbEvalPoly point (grbScaleByMonomial mono gen) =
      (grbEvalMonomial point mono && grbEvalPoly point gen)
  | [], mono, point => by
      show false = (grbEvalMonomial point mono && false)
      exact (grbBoolAndFalseRight (grbEvalMonomial point mono)).symm
  | head :: rest, mono, point => by
      show grbBoolXor (grbEvalMonomial point (grbExpMul mono head))
        (grbEvalPoly point (grbScaleByMonomial mono rest)) = _
      rw [grbEvalMonomialMul mono head point, grbEvalScaleByMonomial rest mono point]
      exact grbBoolAndDistribXor (grbEvalMonomial point mono) (grbEvalMonomial point head)
        (grbEvalPoly point rest)

/-- Evaluation through `grbMonoInsert`. -/
theorem grbEvalPolyMonoInsert : (poly : GrbPoly) → (mono : GrbExp) → (point : Nat → Bool) →
    grbEvalPoly point (grbMonoInsert mono poly) =
      grbBoolXor (grbEvalMonomial point mono) (grbEvalPoly point poly)
  | [], _, _ => rfl
  | head :: rest, mono, point => by
      cases hBeq : grbExpBeq mono head with
      | true =>
          have monoEq := grbExpBeqEq mono head hBeq
          rw [grbMonoInsertOnCollision mono head rest hBeq, monoEq]
          show grbEvalPoly point rest =
            grbBoolXor (grbEvalMonomial point head)
              (grbBoolXor (grbEvalMonomial point head) (grbEvalPoly point rest))
          exact (grbBoolXorLeftSelfCancel (grbEvalMonomial point head)
            (grbEvalPoly point rest)).symm
      | false =>
          cases hLess : grbMonoLess head mono with
          | true =>
              rw [grbMonoInsertOnGreater mono head rest hBeq hLess]
              rfl
          | false =>
              rw [grbMonoInsertOnSmaller mono head rest hBeq hLess]
              show grbBoolXor (grbEvalMonomial point head)
                (grbEvalPoly point (grbMonoInsert mono rest)) = _
              rw [grbEvalPolyMonoInsert rest mono point]
              exact grbBoolXorSwapLeft (grbEvalMonomial point head)
                (grbEvalMonomial point mono) (grbEvalPoly point rest)

/-- Evaluation is additive through `grbAdd`. -/
theorem grbEvalPolyAdd : (left right : GrbPoly) → (point : Nat → Bool) →
    grbEvalPoly point (grbAdd left right) =
      grbBoolXor (grbEvalPoly point left) (grbEvalPoly point right)
  | [], _, _ => rfl
  | mono :: rest, right, point => by
      show grbEvalPoly point (grbMonoInsert mono (grbAdd rest right)) = _
      rw [grbEvalPolyMonoInsert (grbAdd rest right) mono point,
        grbEvalPolyAdd rest right point]
      exact (grbBoolXorAssoc (grbEvalMonomial point mono) (grbEvalPoly point rest)
        (grbEvalPoly point right)).symm

/-- Evaluation is multiplicative through `grbMul`. -/
theorem grbEvalPolyMul : (left right : GrbPoly) → (point : Nat → Bool) →
    grbEvalPoly point (grbMul left right) =
      (grbEvalPoly point left && grbEvalPoly point right)
  | [], right, point => by
      rw [grbMulNilLeft right]
      rfl
  | mono :: rest, right, point => by
      show grbEvalPoly point (grbAdd (grbScaleByMonomial mono right) (grbMul rest right)) = _
      rw [grbEvalPolyAdd (grbScaleByMonomial mono right) (grbMul rest right) point,
        grbEvalScaleByMonomial right mono point, grbEvalPolyMul rest right point]
      exact grbBoolXorAndRightFactor (grbEvalMonomial point mono) (grbEvalPoly point rest)
        (grbEvalPoly point right)

/-- Evaluation through `grbNeg` (the identity over F2). -/
theorem grbEvalPolyNeg (poly : GrbPoly) (point : Nat → Bool) :
    grbEvalPoly point (grbNeg poly) = grbEvalPoly point poly := rfl

/-- **Semantic grounding**: ideal members vanish at every common zero of the
generators (the easy Nullstellensatz direction — no completeness claim). -/
theorem grbInIdealVanishesOnCommonZero (generators : List GrbPoly) (target : GrbPoly)
    (point : Nat → Bool) (hInIdeal : GrbInIdeal generators target)
    (hGeneratorsVanish : (gen : GrbPoly) → GrbMember gen generators →
      grbEvalPoly point gen = false) :
    grbEvalPoly point target = false := by
  induction hInIdeal with
  | byZeroPolynomial => rfl
  | byGenerator gen isGenerator => exact hGeneratorsVanish gen isGenerator
  | byAddition left right _ _ leftVanishes rightVanishes =>
      rw [grbEvalPolyAdd left right point, leftVanishes, rightVanishes]
      rfl
  | byPolynomialScale multiplier member _ memberVanishes =>
      rw [grbEvalPolyMul multiplier member point, memberVanishes]
      exact grbBoolAndFalseRight (grbEvalPoly point multiplier)

/-- **Ring-equality pin**: an accepted difference certificate makes the two sides
evaluate equal at every common zero of the generators. -/
theorem grbRingEqualityByCertificate (generators cofactors : List GrbPoly)
    (leftPoly rightPoly : GrbPoly) (point : Nat → Bool)
    (hCheckPasses : grbCheckCertificate generators cofactors
      (grbAdd leftPoly (grbNeg rightPoly)) = true)
    (hGeneratorsVanish : (gen : GrbPoly) → GrbMember gen generators →
      grbEvalPoly point gen = false) :
    grbEvalPoly point leftPoly = grbEvalPoly point rightPoly := by
  have hVanishes := grbInIdealVanishesOnCommonZero generators
    (grbAdd leftPoly (grbNeg rightPoly)) point
    (grbCertificateSound generators cofactors (grbAdd leftPoly (grbNeg rightPoly)) hCheckPasses)
    hGeneratorsVanish
  rw [grbEvalPolyAdd leftPoly (grbNeg rightPoly) point] at hVanishes
  exact grbBoolXorEqFalseImpliesEq (grbEvalPoly point leftPoly)
    (grbEvalPoly point (grbNeg rightPoly)) hVanishes

/-! ## THE FINDER: fuel-bounded top-reduction with cofactor accumulation

Untrusted-but-verified-on-success: the invariant holds at EVERY fuel level, so even a
fuel-exhausted run leaves a checkable partial certificate; a run reaching remainder
`[]` yields cofactors the checker accepts (`grbFinderSound`).  Divisibility/quotient
correctness is never needed by any theorem — it only affects finder PROGRESS,
witnessed by the `#eval` smokes. -/

/-- Exponent of a variable inside an exponent vector (0 when absent). -/
def grbExpLookup : GrbExp → Nat → Nat
  | [], _ => 0
  | varPower :: rest, targetVariable =>
      cond (Nat.beq varPower.variableIndex targetVariable)
        varPower.exponent
        (grbExpLookup rest targetVariable)

/-- Does the divisor monomial divide the target monomial (per-variable exponent bound)? -/
def grbExpDivides : GrbExp → GrbExp → Bool
  | [], _ => true
  | varPower :: rest, target =>
      grbNatLessOrEq varPower.exponent (grbExpLookup target varPower.variableIndex) &&
        grbExpDivides rest target

/-- Monomial quotient (per-variable truncated exponent difference, dropping zeros). -/
def grbExpQuotient : GrbExp → GrbExp → GrbExp
  | [], _ => []
  | varPower :: rest, divisor =>
      cond (grbNatLess 0
          (grbNatMinus varPower.exponent (grbExpLookup divisor varPower.variableIndex)))
        ({ variableIndex := varPower.variableIndex,
           exponent :=
             grbNatMinus varPower.exponent (grbExpLookup divisor varPower.variableIndex) } ::
          grbExpQuotient rest divisor)
        (grbExpQuotient rest divisor)

/-- A reducer choice: which generator fires, with what quotient monomial. -/
structure GrbReducerChoice where
  cofactorIndex : Nat
  quotientExponent : GrbExp
  reducerBody : GrbPoly

/-- Shift a reducer choice one generator to the right. -/
def grbBumpReducerIndex : Option GrbReducerChoice → Option GrbReducerChoice
  | none => none
  | some found => some { found with cofactorIndex := Nat.succ found.cofactorIndex }

/-- Scan the generators for the first whose leading monomial divides the lead exponent
(zero generators are skipped — they have no leading monomial). -/
def grbFindReducer : List GrbPoly → GrbExp → Option GrbReducerChoice
  | [], _ => none
  | [] :: rest, leadExponent => grbBumpReducerIndex (grbFindReducer rest leadExponent)
  | (genLead :: genRest) :: rest, leadExponent =>
      cond (grbExpDivides genLead leadExponent)
        (some { cofactorIndex := 0,
                quotientExponent := grbExpQuotient leadExponent genLead,
                reducerBody := genLead :: genRest })
        (grbBumpReducerIndex (grbFindReducer rest leadExponent))

/-- Positional generator lookup. -/
def grbGeneratorAt : List GrbPoly → Nat → Option GrbPoly
  | [], 0 => none
  | [], Nat.succ _ => none
  | gen :: _, 0 => some gen
  | _ :: rest, Nat.succ index => grbGeneratorAt rest index

/-- A found reducer really is the generator at its index. -/
theorem grbFindReducerPointsAtGenerator : (generators : List GrbPoly) →
    (leadExponent : GrbExp) → (choice : GrbReducerChoice) →
    grbFindReducer generators leadExponent = some choice →
    grbGeneratorAt generators choice.cofactorIndex = some choice.reducerBody
  | [], _, choice, hFind => by
      have hImpossible : (none : Option GrbReducerChoice) = some choice := hFind
      exact nomatch hImpossible
  | [] :: rest, leadExponent, choice, hFind => by
      have hFindFull : grbBumpReducerIndex (grbFindReducer rest leadExponent) = some choice :=
        hFind
      cases hInner : grbFindReducer rest leadExponent with
      | none =>
          rw [hInner] at hFindFull
          have hImpossible : (none : Option GrbReducerChoice) = some choice := hFindFull
          exact nomatch hImpossible
      | some inner =>
          rw [hInner] at hFindFull
          have choiceEq := Option.some.inj hFindFull
          rw [← choiceEq]
          exact grbFindReducerPointsAtGenerator rest leadExponent inner hInner
  | (genLead :: genRest) :: rest, leadExponent, choice, hFind => by
      have hFindFull : cond (grbExpDivides genLead leadExponent)
          (some { cofactorIndex := 0,
                  quotientExponent := grbExpQuotient leadExponent genLead,
                  reducerBody := genLead :: genRest })
          (grbBumpReducerIndex (grbFindReducer rest leadExponent)) = some choice := hFind
      cases hDivides : grbExpDivides genLead leadExponent with
      | true =>
          rw [hDivides] at hFindFull
          have choiceEq := Option.some.inj hFindFull
          rw [← choiceEq]
          rfl
      | false =>
          rw [hDivides] at hFindFull
          cases hInner : grbFindReducer rest leadExponent with
          | none =>
              rw [hInner] at hFindFull
              have hImpossible : (none : Option GrbReducerChoice) = some choice := hFindFull
              exact nomatch hImpossible
          | some inner =>
              rw [hInner] at hFindFull
              have choiceEq := Option.some.inj hFindFull
              rw [← choiceEq]
              exact grbFindReducerPointsAtGenerator rest leadExponent inner hInner

/-- Length agreement between a cofactor list and the generator list. -/
def grbHasSameLength : List GrbPoly → List GrbPoly → Bool
  | [], [] => true
  | [], _ :: _ => false
  | _ :: _, [] => false
  | _ :: leftRest, _ :: rightRest => grbHasSameLength leftRest rightRest

/-- Insert a monomial into the cofactor at the given index. -/
def grbUpdateCofactors : Nat → GrbExp → List GrbPoly → List GrbPoly
  | 0, _, [] => []
  | 0, mono, cofactor :: rest => grbMonoInsert mono cofactor :: rest
  | Nat.succ _, _, [] => []
  | Nat.succ index, mono, cofactor :: rest => cofactor :: grbUpdateCofactors index mono rest

/-- Cofactor update preserves length agreement. -/
theorem grbUpdateCofactorsKeepLength : (cofactors generators : List GrbPoly) →
    (index : Nat) → (mono : GrbExp) → grbHasSameLength cofactors generators = true →
    grbHasSameLength (grbUpdateCofactors index mono cofactors) generators = true
  | [], _, 0, _, hLengths => hLengths
  | [], _, Nat.succ _, _, hLengths => hLengths
  | _ :: _, [], 0, _, hLengths => Bool.noConfusion hLengths
  | _ :: _, [], Nat.succ _, _, hLengths => Bool.noConfusion hLengths
  | _ :: _, _ :: _, 0, _, hLengths => hLengths
  | _ :: cofactorRest, _ :: genRest, Nat.succ index, mono, hLengths =>
      grbUpdateCofactorsKeepLength cofactorRest genRest index mono hLengths

/-- Updating cofactor `i` by monomial `m` shifts the product sum by `m·genᵢ`. -/
theorem grbSumUpdateCofactors : (cofactors generators : List GrbPoly) → (index : Nat) →
    (mono : GrbExp) → (gen : GrbPoly) → grbHasSameLength cofactors generators = true →
    grbGeneratorAt generators index = some gen →
    grbSumOfProducts (grbUpdateCofactors index mono cofactors) generators =
      grbAdd (grbScaleByMonomial mono gen) (grbSumOfProducts cofactors generators)
  | [], [], 0, _, gen, _, hGeneratorHit => by
      have hImpossible : (none : Option GrbPoly) = some gen := hGeneratorHit
      exact nomatch hImpossible
  | [], [], Nat.succ _, _, gen, _, hGeneratorHit => by
      have hImpossible : (none : Option GrbPoly) = some gen := hGeneratorHit
      exact nomatch hImpossible
  | [], _ :: _, _, _, _, hLengths, _ => Bool.noConfusion hLengths
  | _ :: _, [], _, _, _, hLengths, _ => Bool.noConfusion hLengths
  | cofactor :: cofactorRest, genHead :: genRest, 0, mono, gen, _, hGeneratorHit => by
      have genEq : genHead = gen := Option.some.inj hGeneratorHit
      subst genEq
      show grbAdd (grbMul (grbMonoInsert mono cofactor) genHead)
        (grbSumOfProducts cofactorRest genRest) = _
      rw [grbMulMonoInsert cofactor mono genHead]
      exact grbAddAssoc (grbScaleByMonomial mono genHead) (grbMul cofactor genHead)
        (grbSumOfProducts cofactorRest genRest) (grbSumOfProductsIsSorted cofactorRest genRest)
  | cofactor :: cofactorRest, genHead :: genRest, Nat.succ index, mono, gen, hLengths,
      hGeneratorHit => by
      show grbAdd (grbMul cofactor genHead)
        (grbSumOfProducts (grbUpdateCofactors index mono cofactorRest) genRest) = _
      rw [grbSumUpdateCofactors cofactorRest genRest index mono gen hLengths hGeneratorHit]
      exact grbAddSwapLeft (grbMul cofactor genHead) (grbScaleByMonomial mono gen)
        (grbSumOfProducts cofactorRest genRest) (grbSumOfProductsIsSorted cofactorRest genRest)

/-- The reduce result: the working remainder and the accumulated cofactors. -/
structure GrbReduceResult where
  remainderPoly : GrbPoly
  cofactorPolys : List GrbPoly

/-- Package a fired reducer choice into the next reduce state. -/
def grbApplyReducerChoice (leadExponent : GrbExp) (restPoly : GrbPoly)
    (cofactors : List GrbPoly) : Option GrbReducerChoice → Option GrbReduceResult
  | none => none
  | some choice =>
      some { remainderPoly :=
               grbAdd (grbScaleByMonomial choice.quotientExponent choice.reducerBody)
                 (leadExponent :: restPoly),
             cofactorPolys :=
               grbUpdateCofactors choice.cofactorIndex choice.quotientExponent cofactors }

/-- **One top-reduction step**: subtract (= xor in) `m·genᵢ` where `m` is the exact F2
quotient of the leading monomial by `lm(genᵢ)`, and record `m` in cofactor `i`.
Returns `none` when the polynomial is zero or no generator's lead divides. -/
def grbReduceStep (generators : List GrbPoly) (poly : GrbPoly)
    (cofactors : List GrbPoly) : Option GrbReduceResult :=
  match poly with
  | [] => none
  | leadExponent :: restPoly =>
      grbApplyReducerChoice leadExponent restPoly cofactors
        (grbFindReducer generators leadExponent)

/-- **The fuel-bounded finder loop** (structural on fuel — no `WellFounded.fix`). -/
def grbReduce : Nat → List GrbPoly → GrbPoly → List GrbPoly → GrbReduceResult
  | 0, _, poly, cofactors => { remainderPoly := poly, cofactorPolys := cofactors }
  | Nat.succ fuel, generators, poly, cofactors =>
      match grbReduceStep generators poly cofactors with
      | none => { remainderPoly := poly, cofactorPolys := cofactors }
      | some stepResult =>
          grbReduce fuel generators stepResult.remainderPoly stepResult.cofactorPolys

/-- A fired step preserves lengths and the running certificate sum. -/
theorem grbReduceStepPreservesSum (generators : List GrbPoly) (poly : GrbPoly)
    (cofactors : List GrbPoly) (next : GrbReduceResult)
    (hLengths : grbHasSameLength cofactors generators = true)
    (hStepFires : grbReduceStep generators poly cofactors = some next) :
    grbHasSameLength next.cofactorPolys generators = true ∧
      grbAdd next.remainderPoly (grbSumOfProducts next.cofactorPolys generators) =
        grbAdd poly (grbSumOfProducts cofactors generators) := by
  cases poly with
  | nil =>
      have hImpossible : (none : Option GrbReduceResult) = some next := hStepFires
      exact nomatch hImpossible
  | cons leadExponent restPoly =>
      have hStepFull : grbApplyReducerChoice leadExponent restPoly cofactors
          (grbFindReducer generators leadExponent) = some next := hStepFires
      cases hFind : grbFindReducer generators leadExponent with
      | none =>
          rw [hFind] at hStepFull
          have hImpossible : (none : Option GrbReduceResult) = some next := hStepFull
          exact nomatch hImpossible
      | some choice =>
          rw [hFind] at hStepFull
          have nextEq := Option.some.inj hStepFull
          rw [← nextEq]
          constructor
          · exact grbUpdateCofactorsKeepLength cofactors generators choice.cofactorIndex
              choice.quotientExponent hLengths
          · show grbAdd
                (grbAdd (grbScaleByMonomial choice.quotientExponent choice.reducerBody)
                  (leadExponent :: restPoly))
                (grbSumOfProducts
                  (grbUpdateCofactors choice.cofactorIndex choice.quotientExponent cofactors)
                  generators) =
              grbAdd (leadExponent :: restPoly) (grbSumOfProducts cofactors generators)
            rw [grbSumUpdateCofactors cofactors generators choice.cofactorIndex
              choice.quotientExponent choice.reducerBody hLengths
              (grbFindReducerPointsAtGenerator generators leadExponent choice hFind)]
            exact grbAddCrossCancel
              (grbScaleByMonomial choice.quotientExponent choice.reducerBody)
              (leadExponent :: restPoly) (grbSumOfProducts cofactors generators)
              (grbSumOfProductsIsSorted cofactors generators)

/-- Reduce unfolding: a stuck step returns the state unchanged. -/
theorem grbReduceOnStuckStep (fuel : Nat) (generators : List GrbPoly) (poly : GrbPoly)
    (cofactors : List GrbPoly)
    (hStepStuck : grbReduceStep generators poly cofactors = none) :
    grbReduce (Nat.succ fuel) generators poly cofactors =
      { remainderPoly := poly, cofactorPolys := cofactors } := by
  show (match grbReduceStep generators poly cofactors with
    | none => ({ remainderPoly := poly, cofactorPolys := cofactors } : GrbReduceResult)
    | some stepResult =>
        grbReduce fuel generators stepResult.remainderPoly stepResult.cofactorPolys) =
    { remainderPoly := poly, cofactorPolys := cofactors }
  rw [hStepStuck]

/-- Reduce unfolding: a fired step recurses on the stepped state. -/
theorem grbReduceOnFiringStep (fuel : Nat) (generators : List GrbPoly) (poly : GrbPoly)
    (cofactors : List GrbPoly) (next : GrbReduceResult)
    (hStepFires : grbReduceStep generators poly cofactors = some next) :
    grbReduce (Nat.succ fuel) generators poly cofactors =
      grbReduce fuel generators next.remainderPoly next.cofactorPolys := by
  show (match grbReduceStep generators poly cofactors with
    | none => ({ remainderPoly := poly, cofactorPolys := cofactors } : GrbReduceResult)
    | some stepResult =>
        grbReduce fuel generators stepResult.remainderPoly stepResult.cofactorPolys) =
    grbReduce fuel generators next.remainderPoly next.cofactorPolys
  rw [hStepFires]

/-- **THE INVARIANT**: at every fuel level, `remainder + Σ cofᵢ·genᵢ` equals the input
`poly + Σ cof⁰ᵢ·genᵢ` as sorted lists — fuel exhaustion still leaves a checkable
partial certificate. -/
theorem grbReduceInvariant : (fuel : Nat) → (generators : List GrbPoly) → (poly : GrbPoly) →
    (cofactors : List GrbPoly) → grbHasSameLength cofactors generators = true →
    grbHasSameLength (grbReduce fuel generators poly cofactors).cofactorPolys generators =
        true ∧
      grbAdd (grbReduce fuel generators poly cofactors).remainderPoly
          (grbSumOfProducts (grbReduce fuel generators poly cofactors).cofactorPolys
            generators) =
        grbAdd poly (grbSumOfProducts cofactors generators)
  | 0, _, _, _, hLengths => ⟨hLengths, rfl⟩
  | Nat.succ fuel, generators, poly, cofactors, hLengths => by
      cases hStep : grbReduceStep generators poly cofactors with
      | none =>
          rw [grbReduceOnStuckStep fuel generators poly cofactors hStep]
          exact ⟨hLengths, rfl⟩
      | some next =>
          rw [grbReduceOnFiringStep fuel generators poly cofactors next hStep]
          have hStepFacts := grbReduceStepPreservesSum generators poly cofactors next
            hLengths hStep
          have hRecursiveFacts := grbReduceInvariant fuel generators next.remainderPoly
            next.cofactorPolys hStepFacts.left
          exact ⟨hRecursiveFacts.left, hRecursiveFacts.right.trans hStepFacts.right⟩

/-- The all-zero cofactor seed aligned with the generator list. -/
def grbZeroCofactorsFor : List GrbPoly → List GrbPoly
  | [] => []
  | _ :: rest => [] :: grbZeroCofactorsFor rest

/-- The zero seed agrees in length with the generators. -/
theorem grbZeroCofactorsMatchLength : (generators : List GrbPoly) →
    grbHasSameLength (grbZeroCofactorsFor generators) generators = true
  | [] => rfl
  | _ :: rest => grbZeroCofactorsMatchLength rest

/-- The zero seed's product sum is the zero polynomial. -/
theorem grbSumOfZeroCofactorsIsNil : (generators : List GrbPoly) →
    grbSumOfProducts (grbZeroCofactorsFor generators) generators = []
  | [] => rfl
  | gen :: rest => by
      show grbAdd (grbMul [] gen) (grbSumOfProducts (grbZeroCofactorsFor rest) rest) = []
      rw [grbMulNilLeft gen]
      show grbSumOfProducts (grbZeroCofactorsFor rest) rest = []
      exact grbSumOfZeroCofactorsIsNil rest

/-- **FINDER SOUNDNESS**: a run from the zero seed that reaches remainder `[]` yields
cofactors the checker accepts — finder success always produces a valid certificate. -/
theorem grbFinderSound (fuel : Nat) (generators : List GrbPoly) (target : GrbPoly)
    (hTargetSorted : GrbPolySorted target)
    (hRemainderVanishes :
      (grbReduce fuel generators target (grbZeroCofactorsFor generators)).remainderPoly = []) :
    grbCheckCertificate generators
      (grbReduce fuel generators target (grbZeroCofactorsFor generators)).cofactorPolys
      target = true := by
  have hInvariant := grbReduceInvariant fuel generators target (grbZeroCofactorsFor generators)
    (grbZeroCofactorsMatchLength generators)
  have hSumEquation := hInvariant.right
  rw [hRemainderVanishes, grbSumOfZeroCofactorsIsNil generators,
    grbAddNilRightIsIdentity target hTargetSorted] at hSumEquation
  have hSumIsTarget : grbSumOfProducts
      (grbReduce fuel generators target (grbZeroCofactorsFor generators)).cofactorPolys
      generators = target := hSumEquation
  show grbPolyBeq (grbSumOfProducts
    (grbReduce fuel generators target (grbZeroCofactorsFor generators)).cofactorPolys
    generators) target = true
  rw [hSumIsTarget]
  exact grbPolyBeqRefl target

/-! ## The honest wall: non-membership needs the two missing legs -/

/-- **THE WALL — the full non-membership decision.**  Deciding `GrbInIdeal` outright
(membership OR refutation, for every generator list and target) is the classical
Gröbner-basis decision: reduce the target to a normal form over a COMPLETED basis and
read non-membership off a nonzero remainder.  That route needs (1) Buchberger
termination = Dickson's lemma — certified a zero-axiom IMPOSSIBILITY in this repo
(`fxNet4_dicksonWall := false` in `FX1Poly/ComputerAlgebra/Order/AlmostFull.lean`: the
almost-full PRODUCT theorem forces `WellFounded.fix`) — and (2) Newman-style confluence
of the completed rewrite system, so that ONE nonzero normal form refutes ALL reduction
orders.  Neither leg is attempted here; the statement is recorded as the owner target. -/
def grbNonMembershipDecisionStatement : Prop :=
  (generators : List GrbPoly) → (target : GrbPoly) →
    GrbInIdeal generators target ∨ (GrbInIdeal generators target → False)

/-- Owner flag for `grbNonMembershipDecisionStatement` — NOT proven, walled at
Dickson (`fxNet4_dicksonWall`) + Newman confluence. -/
def fxDissatGrob_hasNonMembershipDecision : Bool := false

/-- DECIDED marker for the certificate route: the sorted-list F2
polynomial substrate, the AC lemma family by sorted-list extensionality, the
certificate checker with `grbCertificateSound`, and the fuel-bounded finder with
`grbReduceInvariant` + `grbFinderSound`. -/
def fxDissatGrob_hasCertificateRoute : Bool := true

/-! ## Smokes (Bool outputs only; FALSE cases included) -/

/-- Smoke fixture: `x + y` over F2 (variables 0 and 1). -/
def grbSmokeXPlusY : GrbPoly := grbAdd (grbVariablePoly 0) (grbVariablePoly 1)

/-- Smoke fixture: `(x + y)^2 = x^2 + y^2` over F2. -/
def grbSmokeSquareOfXPlusY : GrbPoly := grbMul grbSmokeXPlusY grbSmokeXPlusY

/-- Smoke fixture: `x·y`. -/
def grbSmokeXTimesY : GrbPoly := grbMul (grbVariablePoly 0) (grbVariablePoly 1)

/-- Smoke fixture: `x^2 + x·y` — the two-generator target. -/
def grbSmokeTwoGenTarget : GrbPoly :=
  grbAdd (grbMul (grbVariablePoly 0) (grbVariablePoly 0)) grbSmokeXTimesY

-- (x+y)^2 ∈ ⟨x+y⟩: hand certificate (cofactor x+y) checks. Expect: true
#eval grbCheckCertificate [grbSmokeXPlusY] [grbSmokeXPlusY] grbSmokeSquareOfXPlusY
-- (x+y)^2 ∈ ⟨x+y⟩: the finder reaches remainder []. Expect: true
#eval grbPolyBeq (grbReduce 8 [grbSmokeXPlusY] grbSmokeSquareOfXPlusY
  (grbZeroCofactorsFor [grbSmokeXPlusY])).remainderPoly []
-- (x+y)^2 ∈ ⟨x+y⟩: the finder's own certificate checks. Expect: true
#eval grbCheckCertificate [grbSmokeXPlusY] (grbReduce 8 [grbSmokeXPlusY]
  grbSmokeSquareOfXPlusY (grbZeroCofactorsFor [grbSmokeXPlusY])).cofactorPolys
  grbSmokeSquareOfXPlusY
-- FALSE case: x against ⟨x·y⟩ — the finder gets stuck (remainder ≠ []). Expect: false
#eval grbPolyBeq (grbReduce 8 [grbSmokeXTimesY] (grbVariablePoly 0)
  (grbZeroCofactorsFor [grbSmokeXTimesY])).remainderPoly []
-- FALSE case: the bogus certificate 1·(x·y) for x is REJECTED. Expect: false
#eval grbCheckCertificate [grbSmokeXTimesY] [grbOnePoly] (grbVariablePoly 0)
-- Ring-equality pin: p - p over the EMPTY generator list (empty certificate). Expect: true
#eval grbCheckCertificate [] [] (grbAdd grbSmokeSquareOfXPlusY (grbNeg grbSmokeSquareOfXPlusY))
-- Two generators: x^2 + xy ∈ ⟨x, y⟩ with cofactors (x+y, 0). Expect: true
#eval grbCheckCertificate [grbVariablePoly 0, grbVariablePoly 1]
  [grbSmokeXPlusY, grbZero] grbSmokeTwoGenTarget
-- FALSE case: perturbed cofactors (y, 0) for the same target are REJECTED. Expect: false
#eval grbCheckCertificate [grbVariablePoly 0, grbVariablePoly 1]
  [grbVariablePoly 1, grbZero] grbSmokeTwoGenTarget
-- Two generators, finder route: remainder []. Expect: true
#eval grbPolyBeq (grbReduce 8 [grbVariablePoly 0, grbVariablePoly 1] grbSmokeTwoGenTarget
  (grbZeroCofactorsFor [grbVariablePoly 0, grbVariablePoly 1])).remainderPoly []
-- Two generators, finder route: the found certificate checks. Expect: true
#eval grbCheckCertificate [grbVariablePoly 0, grbVariablePoly 1]
  (grbReduce 8 [grbVariablePoly 0, grbVariablePoly 1] grbSmokeTwoGenTarget
    (grbZeroCofactorsFor [grbVariablePoly 0, grbVariablePoly 1])).cofactorPolys
  grbSmokeTwoGenTarget

end FX1Poly.ComputerAlgebra
