import FX1Poly.ComputerAlgebra.Decision.GroebnerRationalMembership

/-! # FX1Poly/ComputerAlgebra/Decision/GroebnerRationalEvaluation — the ℚ evaluation
    layer grounding the ideal-membership decision semantically

The ℚ Gröbner certificate brick (`GroebnerRationalMembership.lean`, prefix `grq`)
decides ideal membership by checkable cofactor certificates — the semantic inductive
`GrqInIdeal`, the structural checker `grqCheckCertificate`, the soundness
`grqCertificateSound`.  This module supplies its evaluation-homomorphism layer: the
common-zero grounding of `GroebnerMembership.lean`'s `grbEvalPoly`, over the canonical
rational carrier `QnfRat` instead of the Bool field.

## Coefficient field: QnfRat vs Bool

The Bool monomial evaluation multiplies Booleans (`&&`, unit `true`) at a total point
`Nat → Bool`; here the coefficient field is `QnfRat`, so `&&` becomes `qnfMul`, the
monomial unit `true` becomes `qnfOne`, the polynomial fold `grbBoolXor` becomes
`qnfAdd`, and the polynomial zero `false` becomes `qnfZero`.  Every place the Bool
proof closed by `rfl` on a Bool identity (`true && b = b`, `b && true = b`,
`b && false = false`) now discharges the corresponding `qnf` law
(`qnfMulOneLeft` / `qnfMulOneRight` / `grqQnfMulZeroRight`).  The exponent-vector
substrate (`GrbExp`, `grbExpInsert`, `grbExpMul`, the order lemmas) is reused from the
Bool brick by import, untouched.

## Environment convention

The Bool evaluation runs at a TOTAL point `Nat → Bool`, so no variable is ever
"missing".  Here the environment is a `List QnfRat` indexed by variable number, and
a variable index past the end of the list evaluates at `qnfZero`
(`greEnvLookup` returns `qnfZero` out of bounds) — the same convention a dense
coordinate vector induces, and the one the fires exercise (e.g. `[qnfOfInt 3]` binds
variable `0` to `3` and leaves every other variable at `0`).

## Layers

  * **`qnfPow` and the power homomorphism** — `qnfPow base exponent` structural on the
    exponent, with `qnfPowAdd` (`x^(m+n) = x^m · x^n`), `qnfPowOne`, `qnfOnePow`,
    `qnfMulPow` (`(x·y)^n = x^n · y^n`), telescoped from `qnfMulAssoc`/`qnfMulComm`
    through the two reusable rearrangers `qnfMulSwapLeft`/`qnfMulExchange`.
  * **Monomial evaluation** — `greEvalVarPower`/`greEvalExp` with the
    exponent-multiplication homomorphism `greEvalExpMul` (eval of `grbExpMul` is the
    product of evals — where `qnfPowAdd` fires, through `greEvalExpInsert`).
  * **Polynomial evaluation** — `greEvalPoly` (sum over terms) with the ring
    homomorphisms `greEvalAdd` (through the insert-fold `grqAdd`), `greEvalMul`,
    `greEvalScaleTerm`, and `greEvalSumOfProducts`.
  * **The grounding** — `greCommonZeroOfIdealMember`: a member of the ideal of a
    generator list vanishes at every common zero of the generators (the easy
    Nullstellensatz direction — no completeness claim), by induction on `GrqInIdeal`
    through the polynomial homomorphisms.

## Zero-axiom discipline

Init + the two imported bricks only.  Structural recursion throughout.  No `propext`,
`Quot.sound`, `Classical.choice`, `sorry`, `native_decide`, `funext`, `omega`, no
`WellFounded.fix`, no `decide` on `Prop`, no catch-all arms over split scrutinees.
All coefficient reasoning is plain `Eq` over `QnfRat` composed from the `qnf` law kit
and the `grqQnf*` telescopes.  Per-declaration gate in
`FX1PolyAudit/ComputerAlgebra/Decision/GroebnerRationalEvaluation.lean`. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace FX1Poly.ComputerAlgebra

/-! ## Canonical power and its homomorphisms -/

/-- Canonical power (`base ^ exponent` with `base ^ 0 = qnfOne`), structural on the
exponent. -/
def qnfPow (base : QnfRat) : Nat → QnfRat
  | 0 => qnfOne
  | Nat.succ exponent => qnfMul base (qnfPow base exponent)

/-- `base ^ 0 = qnfOne`. -/
theorem qnfPowZero (base : QnfRat) : qnfPow base 0 = qnfOne := rfl

/-- `base ^ (exponent + 1) = base · base ^ exponent`. -/
theorem qnfPowSucc (base : QnfRat) (exponent : Nat) :
    qnfPow base (Nat.succ exponent) = qnfMul base (qnfPow base exponent) := rfl

/-- Left-swap for canonical multiplication: `a · (b · c) = b · (a · c)`. -/
theorem qnfMulSwapLeft (firstFactor secondFactor thirdFactor : QnfRat) :
    qnfMul firstFactor (qnfMul secondFactor thirdFactor) =
      qnfMul secondFactor (qnfMul firstFactor thirdFactor) :=
  ((qnfMulAssoc firstFactor secondFactor thirdFactor).symm.trans
      (congrArg (fun value => qnfMul value thirdFactor)
        (qnfMulComm firstFactor secondFactor))).trans
    (qnfMulAssoc secondFactor firstFactor thirdFactor)

/-- **The power homomorphism**: `base ^ (left + right) =
base ^ left · base ^ right`, by induction on `right` and `qnfMulAssoc`. -/
theorem qnfPowAdd : (base : QnfRat) → (left right : Nat) →
    qnfPow base (left + right) = qnfMul (qnfPow base left) (qnfPow base right)
  | base, left, 0 => by
      show qnfPow base left = qnfMul (qnfPow base left) qnfOne
      exact (qnfMulOneRight (qnfPow base left)).symm
  | base, left, Nat.succ right => by
      show qnfMul base (qnfPow base (left + right)) =
        qnfMul (qnfPow base left) (qnfMul base (qnfPow base right))
      rw [qnfPowAdd base left right]
      exact qnfMulSwapLeft base (qnfPow base left) (qnfPow base right)

/-- `base ^ 1 = base`. -/
theorem qnfPowOne (base : QnfRat) : qnfPow base 1 = base :=
  qnfMulOneRight base

/-- `qnfOne ^ exponent = qnfOne`. -/
theorem qnfOnePow : (exponent : Nat) → qnfPow qnfOne exponent = qnfOne
  | 0 => rfl
  | Nat.succ exponent => by
      show qnfMul qnfOne (qnfPow qnfOne exponent) = qnfOne
      rw [qnfOnePow exponent]
      exact qnfMulOneLeft qnfOne

/-- The four-factor exchange: `(a · b) · (c · d) = (a · c) · (b · d)`. -/
theorem qnfMulExchange (firstFactor secondFactor thirdFactor fourthFactor : QnfRat) :
    qnfMul (qnfMul firstFactor secondFactor) (qnfMul thirdFactor fourthFactor) =
      qnfMul (qnfMul firstFactor thirdFactor) (qnfMul secondFactor fourthFactor) :=
  ((qnfMulAssoc firstFactor secondFactor (qnfMul thirdFactor fourthFactor)).trans
      (congrArg (qnfMul firstFactor)
        (qnfMulSwapLeft secondFactor thirdFactor fourthFactor))).trans
    (qnfMulAssoc firstFactor thirdFactor (qnfMul secondFactor fourthFactor)).symm

/-- The product power homomorphism: `(base · other) ^ exponent =
base ^ exponent · other ^ exponent`. -/
theorem qnfMulPow : (base other : QnfRat) → (exponent : Nat) →
    qnfPow (qnfMul base other) exponent =
      qnfMul (qnfPow base exponent) (qnfPow other exponent)
  | base, other, 0 => (qnfMulOneRight qnfOne).symm
  | base, other, Nat.succ exponent => by
      show qnfMul (qnfMul base other) (qnfPow (qnfMul base other) exponent) =
        qnfMul (qnfMul base (qnfPow base exponent)) (qnfMul other (qnfPow other exponent))
      rw [qnfMulPow base other exponent]
      exact qnfMulExchange base other (qnfPow base exponent) (qnfPow other exponent)

/-! ## Monomial evaluation over a `List QnfRat` environment -/

/-- Look up a variable's value in the environment; a variable index past the end of
the list evaluates at `qnfZero` (the documented missing-variable convention). -/
def greEnvLookup : List QnfRat → Nat → QnfRat
  | [], _ => qnfZero
  | value :: _, 0 => value
  | _ :: rest, Nat.succ index => greEnvLookup rest index

/-- Evaluate one variable power `variableIndex ^ exponent` at the environment. -/
def greEvalVarPower (env : List QnfRat) (varPower : GrbVarPower) : QnfRat :=
  qnfPow (greEnvLookup env varPower.variableIndex) varPower.exponent

/-- Evaluate a monomial (exponent vector) at the environment — the product of its
variable-power evaluations, empty monomial at `qnfOne`. -/
def greEvalExp (env : List QnfRat) : GrbExp → QnfRat
  | [] => qnfOne
  | varPower :: rest => qnfMul (greEvalVarPower env varPower) (greEvalExp env rest)

/-- Evaluation through `grbExpInsert` — the shared-variable branch is exactly where
`qnfPowAdd` fires. -/
theorem greEvalExpInsert : (exp : GrbExp) → (varPower : GrbVarPower) →
    (env : List QnfRat) →
    greEvalExp env (grbExpInsert varPower exp) =
      qnfMul (greEvalVarPower env varPower) (greEvalExp env exp)
  | [], _, _ => rfl
  | head :: rest, varPower, env => by
      cases hVariable : Nat.beq varPower.variableIndex head.variableIndex with
      | true =>
          have variableEq := grbNatBeqEq varPower.variableIndex head.variableIndex hVariable
          rw [grbExpInsertOnSharedVariable varPower head rest hVariable]
          show qnfMul (qnfPow (greEnvLookup env head.variableIndex)
              (varPower.exponent + head.exponent)) (greEvalExp env rest) =
            qnfMul (qnfPow (greEnvLookup env varPower.variableIndex) varPower.exponent)
              (qnfMul (qnfPow (greEnvLookup env head.variableIndex) head.exponent)
                (greEvalExp env rest))
          rw [qnfPowAdd (greEnvLookup env head.variableIndex) varPower.exponent head.exponent,
            variableEq]
          exact qnfMulAssoc (qnfPow (greEnvLookup env head.variableIndex) varPower.exponent)
            (qnfPow (greEnvLookup env head.variableIndex) head.exponent) (greEvalExp env rest)
      | false =>
          cases hEarlier : grbNatLess varPower.variableIndex head.variableIndex with
          | true =>
              rw [grbExpInsertOnEarlierVariable varPower head rest hVariable hEarlier]
              rfl
          | false =>
              rw [grbExpInsertOnLaterVariable varPower head rest hVariable hEarlier]
              show qnfMul (greEvalVarPower env head)
                  (greEvalExp env (grbExpInsert varPower rest)) = _
              rw [greEvalExpInsert rest varPower env]
              exact qnfMulSwapLeft (greEvalVarPower env head) (greEvalVarPower env varPower)
                (greEvalExp env rest)

/-- **The exponent-multiplication homomorphism**: evaluation is multiplicative
through `grbExpMul`. -/
theorem greEvalExpMul : (left right : GrbExp) → (env : List QnfRat) →
    greEvalExp env (grbExpMul left right) =
      qnfMul (greEvalExp env left) (greEvalExp env right)
  | [], right, env => (qnfMulOneLeft (greEvalExp env right)).symm
  | varPower :: rest, right, env => by
      show greEvalExp env (grbExpInsert varPower (grbExpMul rest right)) = _
      rw [greEvalExpInsert (grbExpMul rest right) varPower env,
        greEvalExpMul rest right env]
      exact (qnfMulAssoc (greEvalVarPower env varPower)
        (greEvalExp env rest) (greEvalExp env right)).symm

/-! ## Polynomial evaluation and the ring homomorphisms -/

/-- Evaluate a rational polynomial at the environment — the `qnfAdd` sum over its
terms, each term contributing `coefficient · (monomial evaluation)`. -/
def greEvalPoly (env : List QnfRat) : GrqPoly → QnfRat
  | [] => qnfZero
  | term :: rest =>
      qnfAdd (qnfMul term.coefficient (greEvalExp env term.exponentVector))
        (greEvalPoly env rest)

/-- Evaluation through the four-way canonical `grqTermInsert` — the workhorse: on the
collision branch the coefficient sum splits by `qnfMulRightDistrib`, on the
zero-coefficient branch it annihilates. -/
theorem greEvalPolyTermInsert : (poly : GrqPoly) → (coefficient : QnfRat) →
    (exponent : GrbExp) → (env : List QnfRat) →
    greEvalPoly env (grqTermInsert coefficient exponent poly) =
      qnfAdd (qnfMul coefficient (greEvalExp env exponent)) (greEvalPoly env poly)
  | [], coefficient, exponent, env => by
      cases hZero : qnfBeq coefficient qnfZero with
      | true =>
          rw [grqTermInsertNilOnZeroCoefficient coefficient exponent hZero,
            (qnfBeqIffEq coefficient qnfZero).mp hZero]
          show qnfZero = qnfAdd (qnfMul qnfZero (greEvalExp env exponent)) qnfZero
          rw [grqQnfMulZeroLeft (greEvalExp env exponent)]
          exact (qnfAddZeroRight qnfZero).symm
      | false =>
          rw [grqTermInsertNilOnNonzeroCoefficient coefficient exponent hZero]
          rfl
  | head :: rest, coefficient, exponent, env => by
      cases hZero : qnfBeq coefficient qnfZero with
      | true =>
          rw [grqTermInsertOnZeroCoefficient coefficient exponent head rest hZero,
            (qnfBeqIffEq coefficient qnfZero).mp hZero,
            grqQnfMulZeroLeft (greEvalExp env exponent)]
          exact (qnfAddZeroLeft (greEvalPoly env (head :: rest))).symm
      | false =>
          cases hShared : grbExpBeq exponent head.exponentVector with
          | true =>
              have expEq := grbExpBeqEq exponent head.exponentVector hShared
              cases hSum : qnfBeq (qnfAdd coefficient head.coefficient) qnfZero with
              | true =>
                  rw [grqTermInsertOnCollisionCancel coefficient exponent head rest
                    hZero hShared hSum, expEq]
                  show greEvalPoly env rest =
                    qnfAdd (qnfMul coefficient (greEvalExp env head.exponentVector))
                      (qnfAdd (qnfMul head.coefficient (greEvalExp env head.exponentVector))
                        (greEvalPoly env rest))
                  have sumZero := (qnfBeqIffEq (qnfAdd coefficient head.coefficient) qnfZero).mp hSum
                  rw [(qnfAddAssoc (qnfMul coefficient (greEvalExp env head.exponentVector))
                        (qnfMul head.coefficient (greEvalExp env head.exponentVector))
                        (greEvalPoly env rest)).symm,
                    (qnfMulRightDistrib coefficient head.coefficient
                      (greEvalExp env head.exponentVector)).symm,
                    sumZero, grqQnfMulZeroLeft (greEvalExp env head.exponentVector),
                    qnfAddZeroLeft (greEvalPoly env rest)]
              | false =>
                  rw [grqTermInsertOnCollisionMerge coefficient exponent head rest
                    hZero hShared hSum, expEq]
                  show qnfAdd (qnfMul (qnfAdd coefficient head.coefficient)
                      (greEvalExp env head.exponentVector)) (greEvalPoly env rest) =
                    qnfAdd (qnfMul coefficient (greEvalExp env head.exponentVector))
                      (qnfAdd (qnfMul head.coefficient (greEvalExp env head.exponentVector))
                        (greEvalPoly env rest))
                  rw [qnfMulRightDistrib coefficient head.coefficient
                    (greEvalExp env head.exponentVector)]
                  exact qnfAddAssoc (qnfMul coefficient (greEvalExp env head.exponentVector))
                    (qnfMul head.coefficient (greEvalExp env head.exponentVector))
                    (greEvalPoly env rest)
          | false =>
              cases hLess : grbMonoLess head.exponentVector exponent with
              | true =>
                  rw [grqTermInsertOnGreater coefficient exponent head rest hZero hShared hLess]
                  rfl
              | false =>
                  rw [grqTermInsertOnSmaller coefficient exponent head rest hZero hShared hLess]
                  show qnfAdd (qnfMul head.coefficient (greEvalExp env head.exponentVector))
                      (greEvalPoly env (grqTermInsert coefficient exponent rest)) = _
                  rw [greEvalPolyTermInsert rest coefficient exponent env]
                  exact grqQnfAddSwapLeft
                    (qnfMul head.coefficient (greEvalExp env head.exponentVector))
                    (qnfMul coefficient (greEvalExp env exponent)) (greEvalPoly env rest)

/-- **Additive homomorphism**: evaluation of the insert-fold `grqAdd` is the `qnfAdd`
of the evaluations. -/
theorem greEvalAdd : (leftPoly rightPoly : GrqPoly) → (env : List QnfRat) →
    greEvalPoly env (grqAdd leftPoly rightPoly) =
      qnfAdd (greEvalPoly env leftPoly) (greEvalPoly env rightPoly)
  | [], rightPoly, env => (qnfAddZeroLeft (greEvalPoly env rightPoly)).symm
  | term :: rest, rightPoly, env => by
      show greEvalPoly env (grqTermInsert term.coefficient term.exponentVector
        (grqAdd rest rightPoly)) = _
      rw [greEvalPolyTermInsert (grqAdd rest rightPoly) term.coefficient
        term.exponentVector env, greEvalAdd rest rightPoly env]
      exact (qnfAddAssoc (qnfMul term.coefficient (greEvalExp env term.exponentVector))
        (greEvalPoly env rest) (greEvalPoly env rightPoly)).symm

/-- Evaluation of a single-term scaling `scalar · monomial · gen` scales the whole
evaluation by `scalar · (monomial evaluation)`. -/
theorem greEvalScaleTerm : (gen : GrqPoly) → (scalar : QnfRat) → (monomial : GrbExp) →
    (env : List QnfRat) →
    greEvalPoly env (grqScaleTerm scalar monomial gen) =
      qnfMul (qnfMul scalar (greEvalExp env monomial)) (greEvalPoly env gen)
  | [], scalar, monomial, env =>
      (grqQnfMulZeroRight (qnfMul scalar (greEvalExp env monomial))).symm
  | term :: rest, scalar, monomial, env => by
      show qnfAdd (qnfMul (qnfMul scalar term.coefficient)
          (greEvalExp env (grbExpMul monomial term.exponentVector)))
          (greEvalPoly env (grqScaleTerm scalar monomial rest)) =
        qnfMul (qnfMul scalar (greEvalExp env monomial))
          (qnfAdd (qnfMul term.coefficient (greEvalExp env term.exponentVector))
            (greEvalPoly env rest))
      rw [greEvalExpMul monomial term.exponentVector env,
        greEvalScaleTerm rest scalar monomial env,
        qnfMulLeftDistrib (qnfMul scalar (greEvalExp env monomial))
          (qnfMul term.coefficient (greEvalExp env term.exponentVector))
          (greEvalPoly env rest)]
      exact congrArg (fun value => qnfAdd value
          (qnfMul (qnfMul scalar (greEvalExp env monomial)) (greEvalPoly env rest)))
        (qnfMulExchange scalar term.coefficient (greEvalExp env monomial)
          (greEvalExp env term.exponentVector))

/-- **Multiplicative homomorphism**: evaluation of `grqMul` is the `qnfMul` of the
evaluations. -/
theorem greEvalMul : (leftPoly rightPoly : GrqPoly) → (env : List QnfRat) →
    greEvalPoly env (grqMul leftPoly rightPoly) =
      qnfMul (greEvalPoly env leftPoly) (greEvalPoly env rightPoly)
  | [], right, env => by
      rw [grqMulNilLeft right]
      exact (grqQnfMulZeroLeft (greEvalPoly env right)).symm
  | term :: rest, right, env => by
      show greEvalPoly env (grqAdd (grqScaleTerm term.coefficient term.exponentVector right)
        (grqMul rest right)) = _
      rw [greEvalAdd (grqScaleTerm term.coefficient term.exponentVector right)
          (grqMul rest right) env,
        greEvalScaleTerm right term.coefficient term.exponentVector env,
        greEvalMul rest right env]
      exact (qnfMulRightDistrib (qnfMul term.coefficient (greEvalExp env term.exponentVector))
        (greEvalPoly env rest) (greEvalPoly env right)).symm

/-- The pairwise dot product of two polynomial lists under evaluation — the semantic
target of `grqSumOfProducts`. -/
def greEvalDotProduct (env : List QnfRat) : List GrqPoly → List GrqPoly → QnfRat
  | [], [] => qnfZero
  | [], _ :: _ => qnfZero
  | _ :: _, [] => qnfZero
  | cofactor :: cofactorRest, gen :: genRest =>
      qnfAdd (qnfMul (greEvalPoly env cofactor) (greEvalPoly env gen))
        (greEvalDotProduct env cofactorRest genRest)

/-- **Sum-of-products homomorphism**: evaluation of `grqSumOfProducts` is the
evaluated dot product `Σ (eval cofᵢ)·(eval genᵢ)`. -/
theorem greEvalSumOfProducts : (cofactors generators : List GrqPoly) →
    (env : List QnfRat) →
    greEvalPoly env (grqSumOfProducts cofactors generators) =
      greEvalDotProduct env cofactors generators
  | [], [], _ => rfl
  | [], _ :: _, _ => rfl
  | _ :: _, [], _ => rfl
  | cofactor :: cofactorRest, gen :: genRest, env => by
      show greEvalPoly env (grqAdd (grqMul cofactor gen)
          (grqSumOfProducts cofactorRest genRest)) =
        qnfAdd (qnfMul (greEvalPoly env cofactor) (greEvalPoly env gen))
          (greEvalDotProduct env cofactorRest genRest)
      rw [greEvalAdd (grqMul cofactor gen) (grqSumOfProducts cofactorRest genRest) env,
        greEvalMul cofactor gen env, greEvalSumOfProducts cofactorRest genRest env]

/-! ## The common-zero grounding of ideal membership -/

/-- **The grounding** (the easy Nullstellensatz direction): every member of the ideal
generated by a list vanishes at every common zero of the generators.  By induction on
`GrqInIdeal` through the polynomial homomorphisms — no completeness claim (non-membership
stays out of scope at the F2 wall `grbNonMembershipDecisionStatement`). -/
theorem greCommonZeroOfIdealMember (generators : List GrqPoly) (target : GrqPoly)
    (env : List QnfRat) (hInIdeal : GrqInIdeal generators target)
    (hGeneratorsVanish : (gen : GrqPoly) → GrqMember gen generators →
      greEvalPoly env gen = qnfZero) :
    greEvalPoly env target = qnfZero := by
  induction hInIdeal with
  | byZeroPolynomial => rfl
  | byGenerator gen isGenerator => exact hGeneratorsVanish gen isGenerator
  | byAddition leftPoly rightPoly _ _ leftVanishes rightVanishes =>
      rw [greEvalAdd leftPoly rightPoly env, leftVanishes, rightVanishes]
      exact qnfAddZeroLeft qnfZero
  | byPolynomialScale multiplier member _ memberVanishes =>
      rw [greEvalMul multiplier member env, memberVanishes]
      exact grqQnfMulZeroRight (greEvalPoly env multiplier)

/-! ## Fires -/

set_option maxRecDepth 8192

/-- Fire: `qnfPow` computes `2 ^ 3 = 8` on canonical rationals. -/
theorem greFirePowTwoCubed : qnfPow (qnfOfInt 2) 3 = qnfOfInt 8 := rfl

/-- Fire: `qnfPow` computes `(1/2) ^ 2 = 1/4` on canonical rationals. -/
theorem greFirePowOneHalfSquared :
    qnfPow (qnfNormalize { numerator := 1, denominatorPredecessor := 1 }) 2 =
      qnfNormalize { numerator := 1, denominatorPredecessor := 3 } := rfl

/-- Fire: `x^2 - 1` evaluated at `x = 3` is `8` (single-variable environment `[3]`). -/
theorem greFireXSquaredMinusOneAtThree :
    greEvalPoly [qnfOfInt 3] grqFireXSquaredMinusOne = qnfOfInt 8 := rfl

/-- Fire: `x - 1` evaluated at `x = 1` vanishes — the generator zero for the grounding
fire below. -/
theorem greFireXMinusOneVanishesAtOne :
    greEvalPoly [qnfOne] grqFireXMinusOne = qnfZero := rfl

/-- Every generator in the singleton list `[x - 1]` vanishes at the environment `[1]`
— the common-zero hypothesis the grounding fire feeds to `greCommonZeroOfIdealMember`. -/
theorem greFireSingletonGeneratorVanishes : (gen : GrqPoly) →
    GrqMember gen [grqFireXMinusOne] → greEvalPoly [qnfOne] gen = qnfZero
  | _, GrqMember.atHead _ _ => greFireXMinusOneVanishesAtOne
  | _, GrqMember.inTail _ _ _ isInRest => nomatch isInRest

/-- **Fire — the certificate route consuming T4**: `x^2 - 1 ∈ ⟨x - 1⟩` (accepted
certificate, hand cofactor `x + 1`), and the environment `[1]` zeroes the single
generator `x - 1`, hence — by `greCommonZeroOfIdealMember` — zeroes the member
`x^2 - 1`.  No direct evaluation of `x^2 - 1`; the vanishing is deduced from ideal
membership and the generator's zero. -/
theorem greFireXSquaredMinusOneVanishesAtOne :
    greEvalPoly [qnfOne] grqFireXSquaredMinusOne = qnfZero :=
  greCommonZeroOfIdealMember [grqFireXMinusOne] grqFireXSquaredMinusOne [qnfOne]
    (grqCertificateSound [grqFireXMinusOne] [grqFireXPlusOne] grqFireXSquaredMinusOne
      grqFireCheckerAcceptsSquareCertificate)
    greFireSingletonGeneratorVanishes

/-- Fire: two-variable evaluation — `x·y - 1` at `x = 2, y = 3` is `5`. -/
theorem greFireTwoVariableEval :
    greEvalPoly [qnfOfInt 2, qnfOfInt 3] grqFireXTimesYMinusOne = qnfOfInt 5 := rfl

/-! ## Content markers -/

/-- DECIDED: the ℚ evaluation-homomorphism layer — `qnfPow` with the power
homomorphism `qnfPowAdd` and `qnfMulPow`, monomial evaluation
`greEvalExp` with the exponent-multiplication homomorphism `greEvalExpMul`, and the
polynomial ring homomorphisms `greEvalAdd`/`greEvalMul`/`greEvalScaleTerm`/
`greEvalSumOfProducts`. -/
def greHasEvaluationHomomorphism : Bool := true

/-- DECIDED: the semantic grounding of the ℚ ideal-membership decision —
`greCommonZeroOfIdealMember`: a member of the ideal vanishes at every common zero of
the generators (the easy Nullstellensatz direction), so an accepted `grqCheckCertificate`
now carries semantic content, not merely `GrqInIdeal` membership.  Non-membership /
completeness stays out of scope at the F2 wall `fxDissatGrob_hasNonMembershipDecision`. -/
def greHasCommonZeroGrounding : Bool := true

end FX1Poly.ComputerAlgebra
