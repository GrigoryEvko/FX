/-! # FX1Poly/ComputerAlgebra/Decision/TwoSatDecision — 2-SAT decided via implication-path duality

The SCC-free Aspvall–Plass–Tarjan route, certificate-first, zero-axiom.

A 2-SAT clause `(a ∨ b)` contributes the two implication edges `¬a → b` and `¬b → a`
(`twoSatClauseHasEdge`), making the edge set definitionally skew-symmetric.  Reachability
is CERTIFICATE-BEARING throughout: a path is a plain node list checked by
`twoSatIsPathFrom`, and the fuel-bounded closure `twoSatComputeReach` stores, for every
visited literal, the path that discovered it.

Pillars:

  * **Skew duality** (`twoSatPathDual`): a checked path `a ⇝ b` dualizes constructively to
    a checked path `¬b ⇝ ¬a`, by clause-scan case analysis lifted along an accumulator
    recursion (`twoSatDualPathAux`).
  * **Semantic force** (`twoSatPathForces`): under any assignment satisfying every clause,
    truth propagates along every checked edge and path.  Hence two path certificates
    `x ⇝ ¬x` and `¬x ⇝ x` refute satisfiability outright
    (`twoSatContradictionPathsSound`).
  * **Fuel adequacy is PROVEN, not assumed** (`twoSatIterateStabilizes`): the expansion
    step only appends fresh literals drawn from the finite clause universe, the visited
    list stays duplicate-free, and the hand-rolled pigeonhole
    (`twoSatNodupSubsetLengthLe` over the structural Boolean order `twoSatNatLe`) forces a
    fixpoint within `|universe| + 1` rounds.  At the fixpoint the visited set is
    edge-closed, so computed NON-membership genuinely refutes reachability
    (`twoSatClosedRefutesPath` — the linchpin), giving both directions of the bridge
    `twoSatComputedReachesSound` / `twoSatComputedReachesComplete`.
  * **The static assignment rule is FALSE on ties** — for `{(¬x ∨ ¬y)}` neither literal
    reaches its negation, yet "set `l` true iff `¬(l ⇝ ¬l)`" falsifies the clause.  The
    SAT half therefore follows Even–Itai–Shamir: `twoSatAugmentLoop` walks the variables
    and adds one DECISION unit clause `(l ∨ l)` (edge `¬l → l`) per variable, choosing the
    side `l` whose forward reach `l ⇝ ¬l` is absent in the CURRENT augmented system.  The
    augmentation-decomposition lemma (`twoSatUnitAugmentDecompose` — paths through the new
    edge factor through `¬l` and `l` in the old system) shows each decision preserves the
    no-mutual-reach invariant (`twoSatDecisionPreservesNoMutual`), so ties are eliminated
    and the reach-based assignment (`twoSatSelectTrueVariables`) becomes total and
    consistent.

The decision procedure `twoSatDecide` returns either `isUnsatisfiable` with a variable and
BOTH path certificates (checkable by `twoSatIsPathFrom`), or `isSatisfiable` with the list
of true variables (checkable by `twoSatSatisfies`).  Commissioned theorems, both landed:

  1. `twoSatDecideUnsatSound` — an UNSAT verdict refutes every assignment (via the pure
     certificate theorem `twoSatContradictionPathsSound`).
  2. `twoSatDecideSatSound` — a SAT verdict's assignment satisfies every clause: a
     falsified clause `(a ∨ b)` would force `a ⇝ ¬a` and `b ⇝ ¬b` in the augmented
     system (`twoSatValLemma`, using the per-variable decision edge for the negative
     sign), and chaining through the clause's own edges builds a mutual-reach pair,
     contradicting the preserved invariant (`twoSatClauseSatisfiedPointwise`).

Marker: `fxDissatIsland_hasTwoSatDecision := true`.

## Zero-axiom discipline

Init only.  Structural recursion and full constructor enumeration everywhere; no `omega`,
no `decide` on `Prop`, no `Nat.sub`/`Nat.le_*`/`Nat.ble_*`/`List.append` library surface —
the order (`twoSatNatLe`), equality tests (`twoSatNatBeq`, `twoSatBoolBeq`,
`twoSatLiteralBeq`), and list appends (`twoSatAppendLiterals`, `twoSatAppendEntries`) are
purpose-built with hand-proven laws.  Per-declaration gate in
`FX1PolyAudit/ComputerAlgebra/Decision/TwoSatDecision.lean`. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace FX1Poly.ComputerAlgebra

/-! ## Boolean kit — structural case bashes, no library lemmas -/

/-- Left conjunct of a true conjunction. -/
theorem twoSatAndLeft : (leftFlag rightFlag : Bool) → (leftFlag && rightFlag) = true → leftFlag = true
  | true, true, _ => rfl
  | true, false, hBoth => Bool.noConfusion hBoth
  | false, true, hBoth => Bool.noConfusion hBoth
  | false, false, hBoth => Bool.noConfusion hBoth

/-- Right conjunct of a true conjunction. -/
theorem twoSatAndRight : (leftFlag rightFlag : Bool) → (leftFlag && rightFlag) = true → rightFlag = true
  | true, true, _ => rfl
  | true, false, hBoth => Bool.noConfusion hBoth
  | false, true, _ => rfl
  | false, false, hBoth => Bool.noConfusion hBoth

/-- Introduce a true conjunction from both conjuncts. -/
theorem twoSatAndIntro : (leftFlag rightFlag : Bool) → leftFlag = true → rightFlag = true →
    (leftFlag && rightFlag) = true
  | true, true, _, _ => rfl
  | true, false, _, hRight => Bool.noConfusion hRight
  | false, true, hLeft, _ => Bool.noConfusion hLeft
  | false, false, hLeft, _ => Bool.noConfusion hLeft

/-- Case split on a true disjunction. -/
theorem twoSatOrCases : (leftFlag rightFlag : Bool) → (leftFlag || rightFlag) = true →
    leftFlag = true ∨ rightFlag = true
  | true, true, _ => Or.inl rfl
  | true, false, _ => Or.inl rfl
  | false, true, _ => Or.inr rfl
  | false, false, hEither => Bool.noConfusion hEither

/-- Introduce a true disjunction from the left. -/
theorem twoSatOrIntroLeft : (leftFlag rightFlag : Bool) → leftFlag = true →
    (leftFlag || rightFlag) = true
  | true, true, _ => rfl
  | true, false, _ => rfl
  | false, true, hLeft => Bool.noConfusion hLeft
  | false, false, hLeft => Bool.noConfusion hLeft

/-- Introduce a true disjunction from the right. -/
theorem twoSatOrIntroRight : (leftFlag rightFlag : Bool) → rightFlag = true →
    (leftFlag || rightFlag) = true
  | true, true, _ => rfl
  | true, false, hRight => Bool.noConfusion hRight
  | false, true, _ => rfl
  | false, false, hRight => Bool.noConfusion hRight

/-- A false disjunction has both disjuncts false. -/
theorem twoSatOrFalseSplit : (leftFlag rightFlag : Bool) → (leftFlag || rightFlag) = false →
    leftFlag = false ∧ rightFlag = false
  | false, false, _ => And.intro rfl rfl
  | false, true, hEither => Bool.noConfusion hEither
  | true, false, hEither => Bool.noConfusion hEither
  | true, true, hEither => Bool.noConfusion hEither

/-- A flag whose negation is true is false. -/
theorem twoSatNotEqTrue : (flag : Bool) → Bool.not flag = true → flag = false
  | false, _ => rfl
  | true, hNot => Bool.noConfusion hNot

/-- A flag whose negation is false is true. -/
theorem twoSatNotEqFalse : (flag : Bool) → Bool.not flag = false → flag = true
  | true, _ => rfl
  | false, hNot => Bool.noConfusion hNot

/-! ## Structural `Nat` equality -/

/-- Structural Boolean equality on `Nat` (avoids `Nat.beq` library lemmas). -/
def twoSatNatBeq : Nat → Nat → Bool
  | Nat.zero, Nat.zero => true
  | Nat.zero, Nat.succ _ => false
  | Nat.succ _, Nat.zero => false
  | Nat.succ leftPred, Nat.succ rightPred => twoSatNatBeq leftPred rightPred

/-- `twoSatNatBeq` is reflexive. -/
theorem twoSatNatBeqRefl : (value : Nat) → twoSatNatBeq value value = true
  | Nat.zero => rfl
  | Nat.succ valuePred => twoSatNatBeqRefl valuePred

/-- `twoSatNatBeq` decides equality (soundness direction). -/
theorem twoSatNatBeqImpliesEq : (left right : Nat) → twoSatNatBeq left right = true → left = right
  | Nat.zero, Nat.zero, _ => rfl
  | Nat.zero, Nat.succ _, hBeq => Bool.noConfusion hBeq
  | Nat.succ _, Nat.zero, hBeq => Bool.noConfusion hBeq
  | Nat.succ leftPred, Nat.succ rightPred, hBeq =>
      congrArg Nat.succ (twoSatNatBeqImpliesEq leftPred rightPred hBeq)

/-! ## Structural `Nat` order — the pigeonhole substrate -/

/-- Structural Boolean `≤` on `Nat` (avoids every `Nat.le`/`Nat.ble` library lemma). -/
def twoSatNatLe : Nat → Nat → Bool
  | Nat.zero, Nat.zero => true
  | Nat.zero, Nat.succ _ => true
  | Nat.succ _, Nat.zero => false
  | Nat.succ leftPred, Nat.succ rightPred => twoSatNatLe leftPred rightPred

/-- Zero is below everything. -/
theorem twoSatNatLeZeroLeft : (value : Nat) → twoSatNatLe Nat.zero value = true
  | Nat.zero => rfl
  | Nat.succ _ => rfl

/-- Transitivity of `twoSatNatLe`. -/
theorem twoSatNatLeTrans : (first second third : Nat) →
    twoSatNatLe first second = true → twoSatNatLe second third = true →
    twoSatNatLe first third = true
  | Nat.zero, Nat.zero, Nat.zero, _, _ => rfl
  | Nat.zero, Nat.zero, Nat.succ _, _, _ => rfl
  | Nat.zero, Nat.succ _, Nat.zero, _, _ => rfl
  | Nat.zero, Nat.succ _, Nat.succ _, _, _ => rfl
  | Nat.succ _, Nat.zero, Nat.zero, hFirstSecond, _ => Bool.noConfusion hFirstSecond
  | Nat.succ _, Nat.zero, Nat.succ _, hFirstSecond, _ => Bool.noConfusion hFirstSecond
  | Nat.succ _, Nat.succ _, Nat.zero, _, hSecondThird => Bool.noConfusion hSecondThird
  | Nat.succ firstPred, Nat.succ secondPred, Nat.succ thirdPred, hFirstSecond, hSecondThird =>
      twoSatNatLeTrans firstPred secondPred thirdPred hFirstSecond hSecondThird

/-- `succ n ≤ n` never holds. -/
theorem twoSatNatLeSuccSelfFalse : (value : Nat) → twoSatNatLe (Nat.succ value) value = false
  | Nat.zero => rfl
  | Nat.succ valuePred => twoSatNatLeSuccSelfFalse valuePred

/-- The pigeonhole clash: `succ bound ≤ other` and `other ≤ bound` are jointly absurd. -/
theorem twoSatNatLeSuccAbsurd (bound other : Nat)
    (hUpper : twoSatNatLe (Nat.succ bound) other = true)
    (hLower : twoSatNatLe other bound = true) : False :=
  Bool.noConfusion
    ((twoSatNatLeSuccSelfFalse bound).symm.trans
      (twoSatNatLeTrans (Nat.succ bound) other bound hUpper hLower))

/-- Hand-rolled `succ_add` (structural on the right addend). -/
theorem twoSatSuccAdd (left : Nat) : (right : Nat) → Nat.succ left + right = Nat.succ (left + right)
  | Nat.zero => rfl
  | Nat.succ rightPred => congrArg Nat.succ (twoSatSuccAdd left rightPred)

/-- Every number is below itself plus anything. -/
theorem twoSatNatLeAddRight : (base extra : Nat) → twoSatNatLe base (base + extra) = true
  | Nat.zero, extra => twoSatNatLeZeroLeft (Nat.zero + extra)
  | Nat.succ basePred, extra => by
      rw [twoSatSuccAdd basePred extra]
      exact twoSatNatLeAddRight basePred extra

/-- Adding a common left summand preserves the order. -/
theorem twoSatNatLeAddLeftMono : (shift left right : Nat) → twoSatNatLe left right = true →
    twoSatNatLe (shift + left) (shift + right) = true
  | Nat.zero, left, right, hBase => by
      rw [Nat.zero_add, Nat.zero_add]
      exact hBase
  | Nat.succ shiftPred, left, right, hBase => by
      rw [twoSatSuccAdd shiftPred left, twoSatSuccAdd shiftPred right]
      exact twoSatNatLeAddLeftMono shiftPred left right hBase

/-! ## `Nat` list membership and duplicate-free insertion -/

/-- Membership of a `Nat` in a list, via `twoSatNatBeq`. -/
def twoSatNatMember (needle : Nat) : List Nat → Bool
  | [] => false
  | head :: tail => twoSatNatBeq needle head || twoSatNatMember needle tail

/-- Insert a variable index unless already present. -/
def twoSatInsertVariable (candidate : Nat) (variables : List Nat) : List Nat :=
  match twoSatNatMember candidate variables with
  | true => variables
  | false => candidate :: variables

/-- The inserted variable is a member of the insertion result. -/
theorem twoSatInsertMemberSelf (candidate : Nat) (variables : List Nat) :
    twoSatNatMember candidate (twoSatInsertVariable candidate variables) = true := by
  cases hMember : twoSatNatMember candidate variables with
  | true =>
      simp only [twoSatInsertVariable]
      rw [hMember]
      exact hMember
  | false =>
      simp only [twoSatInsertVariable, hMember]
      exact twoSatOrIntroLeft (twoSatNatBeq candidate candidate) (twoSatNatMember candidate variables)
        (twoSatNatBeqRefl candidate)

/-- Insertion preserves existing membership. -/
theorem twoSatInsertMemberMono (candidate other : Nat) (variables : List Nat)
    (hMember : twoSatNatMember other variables = true) :
    twoSatNatMember other (twoSatInsertVariable candidate variables) = true := by
  cases hCandidate : twoSatNatMember candidate variables with
  | true =>
      simp only [twoSatInsertVariable, hCandidate]
      exact hMember
  | false =>
      simp only [twoSatInsertVariable, hCandidate]
      exact twoSatOrIntroRight (twoSatNatBeq other candidate) (twoSatNatMember other variables) hMember

/-- Membership after insertion came from the candidate or from the original list. -/
theorem twoSatInsertMemberCases (candidate other : Nat) (variables : List Nat)
    (hMember : twoSatNatMember other (twoSatInsertVariable candidate variables) = true) :
    twoSatNatBeq other candidate = true ∨ twoSatNatMember other variables = true := by
  cases hCandidate : twoSatNatMember candidate variables with
  | true =>
      rw [twoSatInsertVariable, hCandidate] at hMember
      exact Or.inr hMember
  | false =>
      rw [twoSatInsertVariable, hCandidate] at hMember
      exact twoSatOrCases (twoSatNatBeq other candidate) (twoSatNatMember other variables) hMember

/-! ## Literals -/

/-- A 2-SAT literal: a variable index with a sign. -/
structure TwoSatLiteral where
  variableIndex : Nat
  isPositive : Bool

/-- Negation flips the sign. -/
def twoSatNegate (literal : TwoSatLiteral) : TwoSatLiteral :=
  TwoSatLiteral.mk literal.variableIndex (Bool.not literal.isPositive)

/-- The positive literal of a variable. -/
def twoSatPositiveLiteral (variableIndex : Nat) : TwoSatLiteral :=
  TwoSatLiteral.mk variableIndex true

/-- The negative literal of a variable. -/
def twoSatNegativeLiteral (variableIndex : Nat) : TwoSatLiteral :=
  TwoSatLiteral.mk variableIndex false

/-- Structural Boolean equality on `Bool` (avoids `BEq` instances). -/
def twoSatBoolBeq : Bool → Bool → Bool
  | false, false => true
  | false, true => false
  | true, false => false
  | true, true => true

/-- `twoSatBoolBeq` is reflexive. -/
theorem twoSatBoolBeqRefl : (flag : Bool) → twoSatBoolBeq flag flag = true
  | false => rfl
  | true => rfl

/-- `twoSatBoolBeq` decides equality. -/
theorem twoSatBoolBeqImpliesEq : (left right : Bool) → twoSatBoolBeq left right = true → left = right
  | false, false, _ => rfl
  | false, true, hBeq => Bool.noConfusion hBeq
  | true, false, hBeq => Bool.noConfusion hBeq
  | true, true, _ => rfl

/-- Boolean equality of literals. -/
def twoSatLiteralBeq (left right : TwoSatLiteral) : Bool :=
  twoSatNatBeq left.variableIndex right.variableIndex &&
    twoSatBoolBeq left.isPositive right.isPositive

/-- `twoSatLiteralBeq` is reflexive. -/
theorem twoSatLiteralBeqRefl (literal : TwoSatLiteral) : twoSatLiteralBeq literal literal = true :=
  twoSatAndIntro (twoSatNatBeq literal.variableIndex literal.variableIndex)
    (twoSatBoolBeq literal.isPositive literal.isPositive)
    (twoSatNatBeqRefl literal.variableIndex) (twoSatBoolBeqRefl literal.isPositive)

/-- `twoSatLiteralBeq` decides equality. -/
theorem twoSatLiteralBeqImpliesEq (left right : TwoSatLiteral)
    (hBeq : twoSatLiteralBeq left right = true) : left = right := by
  cases left with
  | mk leftIndex leftSign =>
      cases right with
      | mk rightIndex rightSign =>
          have hIndex : leftIndex = rightIndex :=
            twoSatNatBeqImpliesEq leftIndex rightIndex
              (twoSatAndLeft (twoSatNatBeq leftIndex rightIndex) (twoSatBoolBeq leftSign rightSign) hBeq)
          have hSign : leftSign = rightSign :=
            twoSatBoolBeqImpliesEq leftSign rightSign
              (twoSatAndRight (twoSatNatBeq leftIndex rightIndex) (twoSatBoolBeq leftSign rightSign) hBeq)
          rw [hIndex, hSign]

/-- A failed literal comparison fails in the reverse orientation too. -/
theorem twoSatLiteralBeqFalseSymm (left right : TwoSatLiteral)
    (hFalse : twoSatLiteralBeq left right = false) : twoSatLiteralBeq right left = false := by
  cases hOpposite : twoSatLiteralBeq right left with
  | false => rfl
  | true =>
      have hEq : right = left := twoSatLiteralBeqImpliesEq right left hOpposite
      rw [hEq, twoSatLiteralBeqRefl left] at hFalse
      exact Bool.noConfusion hFalse

/-- Negation is an involution. -/
theorem twoSatNegateInvolution : (literal : TwoSatLiteral) →
    twoSatNegate (twoSatNegate literal) = literal
  | TwoSatLiteral.mk _index true => rfl
  | TwoSatLiteral.mk _index false => rfl

/-- No literal equals its own negation. -/
theorem twoSatLiteralBeqNegateSelf : (literal : TwoSatLiteral) →
    twoSatLiteralBeq literal (twoSatNegate literal) = false
  | TwoSatLiteral.mk index true => by
      show (twoSatNatBeq index index && twoSatBoolBeq true false) = false
      rw [twoSatNatBeqRefl index]
      exact rfl
  | TwoSatLiteral.mk index false => by
      show (twoSatNatBeq index index && twoSatBoolBeq false true) = false
      rw [twoSatNatBeqRefl index]
      exact rfl

/-! ## Literal lists: membership, append, removal, duplicate freedom, subsets -/

/-- Membership of a literal in a list. -/
def twoSatLiteralMember (needle : TwoSatLiteral) : List TwoSatLiteral → Bool
  | [] => false
  | head :: tail => twoSatLiteralBeq needle head || twoSatLiteralMember needle tail

/-- Cons-only append of literal lists (`List.append` is banned). -/
def twoSatAppendLiterals : List TwoSatLiteral → List TwoSatLiteral → List TwoSatLiteral
  | [], second => second
  | head :: tail, second => head :: twoSatAppendLiterals tail second

/-- Appending the empty list on the right is the identity. -/
theorem twoSatAppendLiteralsNil : (list : List TwoSatLiteral) →
    twoSatAppendLiterals list [] = list
  | [] => rfl
  | head :: tail => congrArg (List.cons head) (twoSatAppendLiteralsNil tail)

/-- Membership in an append is the disjunction of the memberships. -/
theorem twoSatMemberAppendEq (probe : TwoSatLiteral) :
    (first second : List TwoSatLiteral) →
    twoSatLiteralMember probe (twoSatAppendLiterals first second) =
      (twoSatLiteralMember probe first || twoSatLiteralMember probe second)
  | [], second => rfl
  | head :: tail, second => by
      show (twoSatLiteralBeq probe head || twoSatLiteralMember probe (twoSatAppendLiterals tail second)) =
        ((twoSatLiteralBeq probe head || twoSatLiteralMember probe tail) || twoSatLiteralMember probe second)
      rw [twoSatMemberAppendEq probe tail second]
      cases hHead : twoSatLiteralBeq probe head with
      | true => rfl
      | false => rfl

/-- Length of an append is the sum of the lengths. -/
theorem twoSatAppendLiteralsLength : (first second : List TwoSatLiteral) →
    (twoSatAppendLiterals first second).length = first.length + second.length
  | [], second => (Nat.zero_add second.length).symm
  | head :: tail, second => by
      show Nat.succ ((twoSatAppendLiterals tail second).length) = Nat.succ tail.length + second.length
      rw [twoSatSuccAdd tail.length second.length]
      exact congrArg Nat.succ (twoSatAppendLiteralsLength tail second)

/-- Remove the first occurrence of a literal. -/
def twoSatRemoveFirstLiteral (target : TwoSatLiteral) : List TwoSatLiteral → List TwoSatLiteral
  | [] => []
  | head :: tail =>
      match twoSatLiteralBeq target head with
      | true => tail
      | false => head :: twoSatRemoveFirstLiteral target tail

/-- Removing a present literal shortens the list by exactly one. -/
theorem twoSatRemoveFirstLength (target : TwoSatLiteral) :
    (haystack : List TwoSatLiteral) →
    twoSatLiteralMember target haystack = true →
    haystack.length = Nat.succ (twoSatRemoveFirstLiteral target haystack).length
  | [], hMember => Bool.noConfusion hMember
  | head :: tail, hMember => by
      cases hBeq : twoSatLiteralBeq target head with
      | true =>
          simp only [twoSatRemoveFirstLiteral, hBeq]
          exact rfl
      | false =>
          simp only [twoSatRemoveFirstLiteral, hBeq]
          have hTail : twoSatLiteralMember target tail = true := by
            cases twoSatOrCases (twoSatLiteralBeq target head) (twoSatLiteralMember target tail) hMember with
            | inl hHead => rw [hBeq] at hHead; exact Bool.noConfusion hHead
            | inr hRest => exact hRest
          show Nat.succ tail.length = Nat.succ (Nat.succ (twoSatRemoveFirstLiteral target tail).length)
          exact congrArg Nat.succ (twoSatRemoveFirstLength target tail hTail)

/-- Membership of a DIFFERENT literal survives removal. -/
theorem twoSatMemberRemoveFirst (target needle : TwoSatLiteral) :
    (haystack : List TwoSatLiteral) →
    twoSatLiteralMember needle haystack = true →
    twoSatLiteralBeq needle target = false →
    twoSatLiteralMember needle (twoSatRemoveFirstLiteral target haystack) = true
  | [], hMember, _ => Bool.noConfusion hMember
  | head :: tail, hMember, hDistinct => by
      cases hBeq : twoSatLiteralBeq target head with
      | true =>
          simp only [twoSatRemoveFirstLiteral, hBeq]
          cases twoSatOrCases (twoSatLiteralBeq needle head) (twoSatLiteralMember needle tail) hMember with
          | inl hHead =>
              have hHeadEq : head = target := (twoSatLiteralBeqImpliesEq target head hBeq).symm
              rw [hHeadEq] at hHead
              rw [hHead] at hDistinct
              exact Bool.noConfusion hDistinct
          | inr hRest => exact hRest
      | false =>
          simp only [twoSatRemoveFirstLiteral, hBeq]
          cases hNeedleHead : twoSatLiteralBeq needle head with
          | true =>
              exact twoSatOrIntroLeft (twoSatLiteralBeq needle head)
                (twoSatLiteralMember needle (twoSatRemoveFirstLiteral target tail))
                hNeedleHead
          | false =>
              have hRest : twoSatLiteralMember needle tail = true := by
                cases twoSatOrCases (twoSatLiteralBeq needle head) (twoSatLiteralMember needle tail) hMember with
                | inl hHead => rw [hNeedleHead] at hHead; exact Bool.noConfusion hHead
                | inr hTail => exact hTail
              exact twoSatOrIntroRight (twoSatLiteralBeq needle head)
                (twoSatLiteralMember needle (twoSatRemoveFirstLiteral target tail))
                (twoSatMemberRemoveFirst target needle tail hRest hDistinct)

/-- Duplicate-freedom of a literal list. -/
def twoSatLiteralsNodup : List TwoSatLiteral → Bool
  | [] => true
  | head :: tail => Bool.not (twoSatLiteralMember head tail) && twoSatLiteralsNodup tail

/-- Every element of `candidates` is a member of `universeList`. -/
def twoSatAllMembersOf (universeList : List TwoSatLiteral) : List TwoSatLiteral → Bool
  | [] => true
  | head :: tail => twoSatLiteralMember head universeList && twoSatAllMembersOf universeList tail

/-- Subset lists survive extension of the ambient list. -/
theorem twoSatAllMembersWeakenCons (extra : TwoSatLiteral) (universeList : List TwoSatLiteral) :
    (candidates : List TwoSatLiteral) →
    twoSatAllMembersOf universeList candidates = true →
    twoSatAllMembersOf (extra :: universeList) candidates = true
  | [], _ => rfl
  | head :: tail, hAll =>
      twoSatAndIntro (twoSatLiteralMember head (extra :: universeList))
        (twoSatAllMembersOf (extra :: universeList) tail)
        (twoSatOrIntroRight (twoSatLiteralBeq head extra) (twoSatLiteralMember head universeList)
          (twoSatAndLeft (twoSatLiteralMember head universeList) (twoSatAllMembersOf universeList tail) hAll))
        (twoSatAllMembersWeakenCons extra universeList tail
          (twoSatAndRight (twoSatLiteralMember head universeList) (twoSatAllMembersOf universeList tail) hAll))

/-- Every list is a subset of itself. -/
theorem twoSatAllMembersSelf : (list : List TwoSatLiteral) → twoSatAllMembersOf list list = true
  | [] => rfl
  | head :: tail =>
      twoSatAndIntro (twoSatLiteralMember head (head :: tail)) (twoSatAllMembersOf (head :: tail) tail)
        (twoSatOrIntroLeft (twoSatLiteralBeq head head) (twoSatLiteralMember head tail)
          (twoSatLiteralBeqRefl head))
        (twoSatAllMembersWeakenCons head tail tail (twoSatAllMembersSelf tail))

/-- Concatenating two subsets yields a subset. -/
theorem twoSatAllMembersAppendCompose (universeList : List TwoSatLiteral) :
    (first second : List TwoSatLiteral) →
    twoSatAllMembersOf universeList first = true →
    twoSatAllMembersOf universeList second = true →
    twoSatAllMembersOf universeList (twoSatAppendLiterals first second) = true
  | [], _, _, hSecond => hSecond
  | head :: tail, second, hFirst, hSecond =>
      twoSatAndIntro (twoSatLiteralMember head universeList)
        (twoSatAllMembersOf universeList (twoSatAppendLiterals tail second))
        (twoSatAndLeft (twoSatLiteralMember head universeList) (twoSatAllMembersOf universeList tail) hFirst)
        (twoSatAllMembersAppendCompose universeList tail second
          (twoSatAndRight (twoSatLiteralMember head universeList) (twoSatAllMembersOf universeList tail) hFirst)
          hSecond)

/-- A subset avoiding a removed element is a subset of the removal result. -/
theorem twoSatAllMembersRemove (universeList : List TwoSatLiteral) (target : TwoSatLiteral) :
    (candidates : List TwoSatLiteral) →
    twoSatAllMembersOf universeList candidates = true →
    twoSatLiteralMember target candidates = false →
    twoSatAllMembersOf (twoSatRemoveFirstLiteral target universeList) candidates = true
  | [], _, _ => rfl
  | head :: tail, hAll, hAvoid => by
      have hHeadDistinct : twoSatLiteralBeq head target = false :=
        twoSatLiteralBeqFalseSymm target head
          (twoSatOrFalseSplit (twoSatLiteralBeq target head) (twoSatLiteralMember target tail) hAvoid).left
      have hTailAvoid : twoSatLiteralMember target tail = false :=
        (twoSatOrFalseSplit (twoSatLiteralBeq target head) (twoSatLiteralMember target tail) hAvoid).right
      exact twoSatAndIntro (twoSatLiteralMember head (twoSatRemoveFirstLiteral target universeList))
        (twoSatAllMembersOf (twoSatRemoveFirstLiteral target universeList) tail)
        (twoSatMemberRemoveFirst target head universeList
          (twoSatAndLeft (twoSatLiteralMember head universeList) (twoSatAllMembersOf universeList tail) hAll)
          hHeadDistinct)
        (twoSatAllMembersRemove universeList target tail
          (twoSatAndRight (twoSatLiteralMember head universeList) (twoSatAllMembersOf universeList tail) hAll)
          hTailAvoid)

/-- **Pigeonhole cardinality bound**: a duplicate-free subset is no longer than its
ambient list. -/
theorem twoSatNodupSubsetLengthLe :
    (candidates universeList : List TwoSatLiteral) →
    twoSatLiteralsNodup candidates = true →
    twoSatAllMembersOf universeList candidates = true →
    twoSatNatLe candidates.length universeList.length = true
  | [], universeList, _, _ => twoSatNatLeZeroLeft universeList.length
  | head :: tail, universeList, hNodup, hSubset => by
      have hHeadMember : twoSatLiteralMember head universeList = true :=
        twoSatAndLeft (twoSatLiteralMember head universeList) (twoSatAllMembersOf universeList tail) hSubset
      have hTailSubset : twoSatAllMembersOf universeList tail = true :=
        twoSatAndRight (twoSatLiteralMember head universeList) (twoSatAllMembersOf universeList tail) hSubset
      have hHeadFresh : twoSatLiteralMember head tail = false :=
        twoSatNotEqTrue (twoSatLiteralMember head tail)
          (twoSatAndLeft (Bool.not (twoSatLiteralMember head tail)) (twoSatLiteralsNodup tail) hNodup)
      have hTailNodup : twoSatLiteralsNodup tail = true :=
        twoSatAndRight (Bool.not (twoSatLiteralMember head tail)) (twoSatLiteralsNodup tail) hNodup
      have hRecursive : twoSatNatLe tail.length (twoSatRemoveFirstLiteral head universeList).length = true :=
        twoSatNodupSubsetLengthLe tail (twoSatRemoveFirstLiteral head universeList) hTailNodup
          (twoSatAllMembersRemove universeList head tail hTailSubset hHeadFresh)
      rw [twoSatRemoveFirstLength head universeList hHeadMember]
      exact hRecursive

/-- Splicing a fresh element between two lists preserves duplicate-freedom. -/
theorem twoSatNodupInsertMiddle (candidate : TwoSatLiteral) :
    (first second : List TwoSatLiteral) →
    twoSatLiteralsNodup (twoSatAppendLiterals first second) = true →
    twoSatLiteralMember candidate first = false →
    twoSatLiteralMember candidate second = false →
    twoSatLiteralsNodup (twoSatAppendLiterals first (candidate :: second)) = true
  | [], second, hNodup, _, hFreshSecond => by
      show (Bool.not (twoSatLiteralMember candidate second) && twoSatLiteralsNodup second) = true
      rw [hFreshSecond]
      exact hNodup
  | head :: tail, second, hNodup, hFreshFirst, hFreshSecond => by
      have hHeadOld : twoSatLiteralMember head (twoSatAppendLiterals tail second) = false :=
        twoSatNotEqTrue (twoSatLiteralMember head (twoSatAppendLiterals tail second))
          (twoSatAndLeft (Bool.not (twoSatLiteralMember head (twoSatAppendLiterals tail second)))
            (twoSatLiteralsNodup (twoSatAppendLiterals tail second)) hNodup)
      have hTailNodup : twoSatLiteralsNodup (twoSatAppendLiterals tail second) = true :=
        twoSatAndRight (Bool.not (twoSatLiteralMember head (twoSatAppendLiterals tail second)))
          (twoSatLiteralsNodup (twoSatAppendLiterals tail second)) hNodup
      have hOldSplit : (twoSatLiteralMember head tail || twoSatLiteralMember head second) = false := by
        rw [← twoSatMemberAppendEq head tail second]
        exact hHeadOld
      have hCandidateHead : twoSatLiteralBeq head candidate = false :=
        twoSatLiteralBeqFalseSymm candidate head
          (twoSatOrFalseSplit (twoSatLiteralBeq candidate head) (twoSatLiteralMember candidate tail)
            hFreshFirst).left
      have hCandidateTail : twoSatLiteralMember candidate tail = false :=
        (twoSatOrFalseSplit (twoSatLiteralBeq candidate head) (twoSatLiteralMember candidate tail)
          hFreshFirst).right
      have hHeadNew : twoSatLiteralMember head (twoSatAppendLiterals tail (candidate :: second)) = false := by
        rw [twoSatMemberAppendEq head tail (candidate :: second)]
        show (twoSatLiteralMember head tail ||
          (twoSatLiteralBeq head candidate || twoSatLiteralMember head second)) = false
        rw [(twoSatOrFalseSplit (twoSatLiteralMember head tail) (twoSatLiteralMember head second) hOldSplit).left,
          hCandidateHead,
          (twoSatOrFalseSplit (twoSatLiteralMember head tail) (twoSatLiteralMember head second) hOldSplit).right]
        exact rfl
      show (Bool.not (twoSatLiteralMember head (twoSatAppendLiterals tail (candidate :: second))) &&
        twoSatLiteralsNodup (twoSatAppendLiterals tail (candidate :: second))) = true
      rw [hHeadNew]
      exact twoSatNodupInsertMiddle candidate tail second hTailNodup hCandidateTail hFreshSecond

/-! ## Clauses, implication edges, the literal universe, the variable census -/

/-- A 2-SAT clause: the disjunction of two literals. -/
structure TwoSatClause where
  firstLiteral : TwoSatLiteral
  secondLiteral : TwoSatLiteral

/-- Boolean equality of clauses. -/
def twoSatClauseBeq (left right : TwoSatClause) : Bool :=
  twoSatLiteralBeq left.firstLiteral right.firstLiteral &&
    twoSatLiteralBeq left.secondLiteral right.secondLiteral

/-- `twoSatClauseBeq` is reflexive. -/
theorem twoSatClauseBeqRefl (clause : TwoSatClause) : twoSatClauseBeq clause clause = true :=
  twoSatAndIntro (twoSatLiteralBeq clause.firstLiteral clause.firstLiteral)
    (twoSatLiteralBeq clause.secondLiteral clause.secondLiteral)
    (twoSatLiteralBeqRefl clause.firstLiteral) (twoSatLiteralBeqRefl clause.secondLiteral)

/-- `twoSatClauseBeq` decides equality. -/
theorem twoSatClauseBeqImpliesEq (left right : TwoSatClause)
    (hBeq : twoSatClauseBeq left right = true) : left = right := by
  cases left with
  | mk leftFirst leftSecond =>
      cases right with
      | mk rightFirst rightSecond =>
          have hFirst : leftFirst = rightFirst :=
            twoSatLiteralBeqImpliesEq leftFirst rightFirst
              (twoSatAndLeft (twoSatLiteralBeq leftFirst rightFirst)
                (twoSatLiteralBeq leftSecond rightSecond) hBeq)
          have hSecond : leftSecond = rightSecond :=
            twoSatLiteralBeqImpliesEq leftSecond rightSecond
              (twoSatAndRight (twoSatLiteralBeq leftFirst rightFirst)
                (twoSatLiteralBeq leftSecond rightSecond) hBeq)
          rw [hFirst, hSecond]

/-- Membership of a clause in a system. -/
def twoSatClauseMember (needle : TwoSatClause) : List TwoSatClause → Bool
  | [] => false
  | head :: tail => twoSatClauseBeq needle head || twoSatClauseMember needle tail

/-- The two implication edges of a clause `(a ∨ b)`: `¬a → b` and `¬b → a`. -/
def twoSatClauseHasEdge (clause : TwoSatClause) (source target : TwoSatLiteral) : Bool :=
  (twoSatLiteralBeq source (twoSatNegate clause.firstLiteral) &&
     twoSatLiteralBeq target clause.secondLiteral) ||
  (twoSatLiteralBeq source (twoSatNegate clause.secondLiteral) &&
     twoSatLiteralBeq target clause.firstLiteral)

/-- Edge membership over a whole system: some clause contributes the edge. -/
def twoSatHasEdge (system : List TwoSatClause) (source target : TwoSatLiteral) : Bool :=
  match system with
  | [] => false
  | clause :: rest => twoSatClauseHasEdge clause source target || twoSatHasEdge rest source target

/-- Decompose a clause edge into its two orientations, with the endpoints resolved. -/
theorem twoSatClauseHasEdgeCases (clause : TwoSatClause) (source target : TwoSatLiteral)
    (hEdge : twoSatClauseHasEdge clause source target = true) :
    (source = twoSatNegate clause.firstLiteral ∧ target = clause.secondLiteral) ∨
    (source = twoSatNegate clause.secondLiteral ∧ target = clause.firstLiteral) := by
  cases twoSatOrCases
      (twoSatLiteralBeq source (twoSatNegate clause.firstLiteral) &&
        twoSatLiteralBeq target clause.secondLiteral)
      (twoSatLiteralBeq source (twoSatNegate clause.secondLiteral) &&
        twoSatLiteralBeq target clause.firstLiteral) hEdge with
  | inl hFirst =>
      exact Or.inl (And.intro
        (twoSatLiteralBeqImpliesEq source (twoSatNegate clause.firstLiteral)
          (twoSatAndLeft (twoSatLiteralBeq source (twoSatNegate clause.firstLiteral))
            (twoSatLiteralBeq target clause.secondLiteral) hFirst))
        (twoSatLiteralBeqImpliesEq target clause.secondLiteral
          (twoSatAndRight (twoSatLiteralBeq source (twoSatNegate clause.firstLiteral))
            (twoSatLiteralBeq target clause.secondLiteral) hFirst)))
  | inr hSecond =>
      exact Or.inr (And.intro
        (twoSatLiteralBeqImpliesEq source (twoSatNegate clause.secondLiteral)
          (twoSatAndLeft (twoSatLiteralBeq source (twoSatNegate clause.secondLiteral))
            (twoSatLiteralBeq target clause.firstLiteral) hSecond))
        (twoSatLiteralBeqImpliesEq target clause.firstLiteral
          (twoSatAndRight (twoSatLiteralBeq source (twoSatNegate clause.secondLiteral))
            (twoSatLiteralBeq target clause.firstLiteral) hSecond)))

/-- **Skew duality, clause level**: each clause edge dualizes to its contrapositive. -/
theorem twoSatClauseHasEdgeDual (clause : TwoSatClause) (source target : TwoSatLiteral)
    (hEdge : twoSatClauseHasEdge clause source target = true) :
    twoSatClauseHasEdge clause (twoSatNegate target) (twoSatNegate source) = true := by
  cases twoSatClauseHasEdgeCases clause source target hEdge with
  | inl hFirstOrientation =>
      apply twoSatOrIntroRight
      apply twoSatAndIntro
      · rw [hFirstOrientation.right]
        exact twoSatLiteralBeqRefl (twoSatNegate clause.secondLiteral)
      · rw [hFirstOrientation.left, twoSatNegateInvolution clause.firstLiteral]
        exact twoSatLiteralBeqRefl clause.firstLiteral
  | inr hSecondOrientation =>
      apply twoSatOrIntroLeft
      apply twoSatAndIntro
      · rw [hSecondOrientation.right]
        exact twoSatLiteralBeqRefl (twoSatNegate clause.firstLiteral)
      · rw [hSecondOrientation.left, twoSatNegateInvolution clause.secondLiteral]
        exact twoSatLiteralBeqRefl clause.secondLiteral

/-- **Skew duality, system level.** -/
theorem twoSatHasEdgeDual : (system : List TwoSatClause) → (source target : TwoSatLiteral) →
    twoSatHasEdge system source target = true →
    twoSatHasEdge system (twoSatNegate target) (twoSatNegate source) = true
  | [], _, _, hEdge => Bool.noConfusion hEdge
  | clause :: rest, source, target, hEdge => by
      cases twoSatOrCases (twoSatClauseHasEdge clause source target)
          (twoSatHasEdge rest source target) hEdge with
      | inl hClause =>
          exact twoSatOrIntroLeft
            (twoSatClauseHasEdge clause (twoSatNegate target) (twoSatNegate source))
            (twoSatHasEdge rest (twoSatNegate target) (twoSatNegate source))
            (twoSatClauseHasEdgeDual clause source target hClause)
      | inr hRest =>
          exact twoSatOrIntroRight
            (twoSatClauseHasEdge clause (twoSatNegate target) (twoSatNegate source))
            (twoSatHasEdge rest (twoSatNegate target) (twoSatNegate source))
            (twoSatHasEdgeDual rest source target hRest)

/-- A member clause's edges are system edges. -/
theorem twoSatHasEdgeOfClauseMember : (system : List TwoSatClause) → (clause : TwoSatClause) →
    (source target : TwoSatLiteral) →
    twoSatClauseMember clause system = true →
    twoSatClauseHasEdge clause source target = true →
    twoSatHasEdge system source target = true
  | [], _, _, _, hMember, _ => Bool.noConfusion hMember
  | head :: rest, clause, source, target, hMember, hEdge => by
      cases twoSatOrCases (twoSatClauseBeq clause head) (twoSatClauseMember clause rest) hMember with
      | inl hBeq =>
          have hHeadEq : clause = head := twoSatClauseBeqImpliesEq clause head hBeq
          rw [← hHeadEq]
          exact twoSatOrIntroLeft (twoSatClauseHasEdge clause source target)
            (twoSatHasEdge rest source target) hEdge
      | inr hRest =>
          exact twoSatOrIntroRight (twoSatClauseHasEdge head source target)
            (twoSatHasEdge rest source target)
            (twoSatHasEdgeOfClauseMember rest clause source target hRest hEdge)

/-- A system edge comes from some member clause. -/
theorem twoSatHasEdgeExistsClause : (system : List TwoSatClause) → (source target : TwoSatLiteral) →
    twoSatHasEdge system source target = true →
    ∃ clause, twoSatClauseMember clause system = true ∧ twoSatClauseHasEdge clause source target = true
  | [], _, _, hEdge => Bool.noConfusion hEdge
  | head :: rest, source, target, hEdge => by
      cases twoSatOrCases (twoSatClauseHasEdge head source target)
          (twoSatHasEdge rest source target) hEdge with
      | inl hHead =>
          exact Exists.intro head (And.intro
            (twoSatOrIntroLeft (twoSatClauseBeq head head) (twoSatClauseMember head rest)
              (twoSatClauseBeqRefl head))
            hHead)
      | inr hRest =>
          cases twoSatHasEdgeExistsClause rest source target hRest with
          | intro clause hClause =>
              exact Exists.intro clause (And.intro
                (twoSatOrIntroRight (twoSatClauseBeq clause head) (twoSatClauseMember clause rest)
                  hClause.left)
                hClause.right)

/-- The literal universe of a system: both signs of both literals of every clause. -/
def twoSatUniverse : List TwoSatClause → List TwoSatLiteral
  | [] => []
  | clause :: rest =>
      clause.firstLiteral :: twoSatNegate clause.firstLiteral ::
      clause.secondLiteral :: twoSatNegate clause.secondLiteral :: twoSatUniverse rest

/-- Edge targets live in the literal universe. -/
theorem twoSatEdgeTargetInUniverse : (system : List TwoSatClause) → (source target : TwoSatLiteral) →
    twoSatHasEdge system source target = true →
    twoSatLiteralMember target (twoSatUniverse system) = true
  | [], _, _, hEdge => Bool.noConfusion hEdge
  | clause :: rest, source, target, hEdge => by
      cases twoSatOrCases (twoSatClauseHasEdge clause source target)
          (twoSatHasEdge rest source target) hEdge with
      | inl hClause =>
          cases twoSatClauseHasEdgeCases clause source target hClause with
          | inl hFirstOrientation =>
              apply twoSatOrIntroRight
              apply twoSatOrIntroRight
              apply twoSatOrIntroLeft
              rw [hFirstOrientation.right]
              exact twoSatLiteralBeqRefl clause.secondLiteral
          | inr hSecondOrientation =>
              apply twoSatOrIntroLeft
              rw [hSecondOrientation.right]
              exact twoSatLiteralBeqRefl clause.firstLiteral
      | inr hRest =>
          apply twoSatOrIntroRight
          apply twoSatOrIntroRight
          apply twoSatOrIntroRight
          apply twoSatOrIntroRight
          exact twoSatEdgeTargetInUniverse rest source target hRest

/-- The variable census of a system (duplicate-free by construction). -/
def twoSatCollectVariables : List TwoSatClause → List Nat
  | [] => []
  | clause :: rest =>
      twoSatInsertVariable clause.firstLiteral.variableIndex
        (twoSatInsertVariable clause.secondLiteral.variableIndex (twoSatCollectVariables rest))

/-- Census membership is monotone under system extension. -/
theorem twoSatCollectVarsConsMono (clause : TwoSatClause) (system : List TwoSatClause)
    (variableIndex : Nat)
    (hMember : twoSatNatMember variableIndex (twoSatCollectVariables system) = true) :
    twoSatNatMember variableIndex (twoSatCollectVariables (clause :: system)) = true :=
  twoSatInsertMemberMono clause.firstLiteral.variableIndex variableIndex
    (twoSatInsertVariable clause.secondLiteral.variableIndex (twoSatCollectVariables system))
    (twoSatInsertMemberMono clause.secondLiteral.variableIndex variableIndex
      (twoSatCollectVariables system) hMember)

/-- Both variables of a member clause are in the census. -/
theorem twoSatClauseVarsCollected : (system : List TwoSatClause) → (clause : TwoSatClause) →
    twoSatClauseMember clause system = true →
    twoSatNatMember clause.firstLiteral.variableIndex (twoSatCollectVariables system) = true ∧
    twoSatNatMember clause.secondLiteral.variableIndex (twoSatCollectVariables system) = true
  | [], _, hMember => Bool.noConfusion hMember
  | head :: rest, clause, hMember => by
      cases twoSatOrCases (twoSatClauseBeq clause head) (twoSatClauseMember clause rest) hMember with
      | inl hBeq =>
          rw [twoSatClauseBeqImpliesEq clause head hBeq]
          exact And.intro
            (twoSatInsertMemberSelf head.firstLiteral.variableIndex
              (twoSatInsertVariable head.secondLiteral.variableIndex (twoSatCollectVariables rest)))
            (twoSatInsertMemberMono head.firstLiteral.variableIndex head.secondLiteral.variableIndex
              (twoSatInsertVariable head.secondLiteral.variableIndex (twoSatCollectVariables rest))
              (twoSatInsertMemberSelf head.secondLiteral.variableIndex (twoSatCollectVariables rest)))
      | inr hRest =>
          have hRecursive := twoSatClauseVarsCollected rest clause hRest
          exact And.intro
            (twoSatCollectVarsConsMono head rest clause.firstLiteral.variableIndex hRecursive.left)
            (twoSatCollectVarsConsMono head rest clause.secondLiteral.variableIndex hRecursive.right)

/-- Edge sources have censused variables (edge sources are negated clause literals). -/
theorem twoSatEdgeSourceVarCollected : (system : List TwoSatClause) → (source target : TwoSatLiteral) →
    twoSatHasEdge system source target = true →
    twoSatNatMember source.variableIndex (twoSatCollectVariables system) = true
  | [], _, _, hEdge => Bool.noConfusion hEdge
  | clause :: rest, source, target, hEdge => by
      cases twoSatOrCases (twoSatClauseHasEdge clause source target)
          (twoSatHasEdge rest source target) hEdge with
      | inl hClause =>
          cases twoSatClauseHasEdgeCases clause source target hClause with
          | inl hFirstOrientation =>
              rw [hFirstOrientation.left]
              exact twoSatInsertMemberSelf clause.firstLiteral.variableIndex
                (twoSatInsertVariable clause.secondLiteral.variableIndex (twoSatCollectVariables rest))
          | inr hSecondOrientation =>
              rw [hSecondOrientation.left]
              exact twoSatInsertMemberMono clause.firstLiteral.variableIndex
                clause.secondLiteral.variableIndex
                (twoSatInsertVariable clause.secondLiteral.variableIndex (twoSatCollectVariables rest))
                (twoSatInsertMemberSelf clause.secondLiteral.variableIndex (twoSatCollectVariables rest))
      | inr hRest =>
          exact twoSatCollectVarsConsMono clause rest source.variableIndex
            (twoSatEdgeSourceVarCollected rest source target hRest)

/-- A literal with a matching variable index is a member of the sign pair
`candidate :: ¬candidate :: rest`, whichever its sign. -/
theorem twoSatSignPairMember (candidate : TwoSatLiteral) (variableIndex : Nat) (sign : Bool)
    (hVar : variableIndex = candidate.variableIndex) (rest : List TwoSatLiteral) :
    twoSatLiteralMember (TwoSatLiteral.mk variableIndex sign)
      (candidate :: twoSatNegate candidate :: rest) = true := by
  cases candidate with
  | mk candidateVar candidateSign =>
      subst hVar
      cases sign with
      | true =>
          cases candidateSign with
          | true =>
              exact twoSatOrIntroLeft
                (twoSatLiteralBeq (TwoSatLiteral.mk variableIndex true) (TwoSatLiteral.mk variableIndex true))
                (twoSatLiteralMember (TwoSatLiteral.mk variableIndex true)
                  (twoSatNegate (TwoSatLiteral.mk variableIndex true) :: rest))
                (twoSatLiteralBeqRefl (TwoSatLiteral.mk variableIndex true))
          | false =>
              exact twoSatOrIntroRight
                (twoSatLiteralBeq (TwoSatLiteral.mk variableIndex true) (TwoSatLiteral.mk variableIndex false))
                (twoSatLiteralMember (TwoSatLiteral.mk variableIndex true)
                  (twoSatNegate (TwoSatLiteral.mk variableIndex false) :: rest))
                (twoSatOrIntroLeft
                  (twoSatLiteralBeq (TwoSatLiteral.mk variableIndex true)
                    (twoSatNegate (TwoSatLiteral.mk variableIndex false)))
                  (twoSatLiteralMember (TwoSatLiteral.mk variableIndex true) rest)
                  (twoSatLiteralBeqRefl (TwoSatLiteral.mk variableIndex true)))
      | false =>
          cases candidateSign with
          | true =>
              exact twoSatOrIntroRight
                (twoSatLiteralBeq (TwoSatLiteral.mk variableIndex false) (TwoSatLiteral.mk variableIndex true))
                (twoSatLiteralMember (TwoSatLiteral.mk variableIndex false)
                  (twoSatNegate (TwoSatLiteral.mk variableIndex true) :: rest))
                (twoSatOrIntroLeft
                  (twoSatLiteralBeq (TwoSatLiteral.mk variableIndex false)
                    (twoSatNegate (TwoSatLiteral.mk variableIndex true)))
                  (twoSatLiteralMember (TwoSatLiteral.mk variableIndex false) rest)
                  (twoSatLiteralBeqRefl (TwoSatLiteral.mk variableIndex false)))
          | false =>
              exact twoSatOrIntroLeft
                (twoSatLiteralBeq (TwoSatLiteral.mk variableIndex false) (TwoSatLiteral.mk variableIndex false))
                (twoSatLiteralMember (TwoSatLiteral.mk variableIndex false)
                  (twoSatNegate (TwoSatLiteral.mk variableIndex false) :: rest))
                (twoSatLiteralBeqRefl (TwoSatLiteral.mk variableIndex false))

/-- Both signs of every censused variable live in the literal universe. -/
theorem twoSatVarInUniverse : (system : List TwoSatClause) → (variableIndex : Nat) → (sign : Bool) →
    twoSatNatMember variableIndex (twoSatCollectVariables system) = true →
    twoSatLiteralMember (TwoSatLiteral.mk variableIndex sign) (twoSatUniverse system) = true
  | [], _, _, hMember => Bool.noConfusion hMember
  | clause :: rest, variableIndex, sign, hMember => by
      cases twoSatInsertMemberCases clause.firstLiteral.variableIndex variableIndex
          (twoSatInsertVariable clause.secondLiteral.variableIndex (twoSatCollectVariables rest))
          hMember with
      | inl hFirstVar =>
          exact twoSatSignPairMember clause.firstLiteral variableIndex sign
            (twoSatNatBeqImpliesEq variableIndex clause.firstLiteral.variableIndex hFirstVar)
            (clause.secondLiteral :: twoSatNegate clause.secondLiteral :: twoSatUniverse rest)
      | inr hInner =>
          cases twoSatInsertMemberCases clause.secondLiteral.variableIndex variableIndex
              (twoSatCollectVariables rest) hInner with
          | inl hSecondVar =>
              exact twoSatOrIntroRight
                (twoSatLiteralBeq (TwoSatLiteral.mk variableIndex sign) clause.firstLiteral)
                (twoSatLiteralMember (TwoSatLiteral.mk variableIndex sign)
                  (twoSatNegate clause.firstLiteral :: clause.secondLiteral ::
                   twoSatNegate clause.secondLiteral :: twoSatUniverse rest))
                (twoSatOrIntroRight
                  (twoSatLiteralBeq (TwoSatLiteral.mk variableIndex sign) (twoSatNegate clause.firstLiteral))
                  (twoSatLiteralMember (TwoSatLiteral.mk variableIndex sign)
                    (clause.secondLiteral :: twoSatNegate clause.secondLiteral :: twoSatUniverse rest))
                  (twoSatSignPairMember clause.secondLiteral variableIndex sign
                    (twoSatNatBeqImpliesEq variableIndex clause.secondLiteral.variableIndex hSecondVar)
                    (twoSatUniverse rest)))
          | inr hRest =>
              exact twoSatOrIntroRight
                (twoSatLiteralBeq (TwoSatLiteral.mk variableIndex sign) clause.firstLiteral)
                (twoSatLiteralMember (TwoSatLiteral.mk variableIndex sign)
                  (twoSatNegate clause.firstLiteral :: clause.secondLiteral ::
                   twoSatNegate clause.secondLiteral :: twoSatUniverse rest))
                (twoSatOrIntroRight
                  (twoSatLiteralBeq (TwoSatLiteral.mk variableIndex sign) (twoSatNegate clause.firstLiteral))
                  (twoSatLiteralMember (TwoSatLiteral.mk variableIndex sign)
                    (clause.secondLiteral :: twoSatNegate clause.secondLiteral :: twoSatUniverse rest))
                  (twoSatOrIntroRight
                    (twoSatLiteralBeq (TwoSatLiteral.mk variableIndex sign) clause.secondLiteral)
                    (twoSatLiteralMember (TwoSatLiteral.mk variableIndex sign)
                      (twoSatNegate clause.secondLiteral :: twoSatUniverse rest))
                    (twoSatOrIntroRight
                      (twoSatLiteralBeq (TwoSatLiteral.mk variableIndex sign)
                        (twoSatNegate clause.secondLiteral))
                      (twoSatLiteralMember (TwoSatLiteral.mk variableIndex sign) (twoSatUniverse rest))
                      (twoSatVarInUniverse rest variableIndex sign hRest))))

/-! ## Path certificates -/

/-- Path checker: `path` lists the successive nodes after `source`; consecutive hops must
be edges and the walk ends (via literal equality) at `target`.  The empty path checks
`source = target`. -/
def twoSatIsPathFrom (system : List TwoSatClause) :
    TwoSatLiteral → List TwoSatLiteral → TwoSatLiteral → Bool
  | source, [], target => twoSatLiteralBeq source target
  | source, nextNode :: restPath, target =>
      twoSatHasEdge system source nextNode && twoSatIsPathFrom system nextNode restPath target

/-- Checked paths compose along the cons-only append. -/
theorem twoSatPathAppend (system : List TwoSatClause) :
    (firstPath : List TwoSatLiteral) → (source middle target : TwoSatLiteral) →
    (secondPath : List TwoSatLiteral) →
    twoSatIsPathFrom system source firstPath middle = true →
    twoSatIsPathFrom system middle secondPath target = true →
    twoSatIsPathFrom system source (twoSatAppendLiterals firstPath secondPath) target = true
  | [], source, middle, _target, _secondPath, hFirst, hSecond => by
      rw [twoSatLiteralBeqImpliesEq source middle hFirst]
      exact hSecond
  | nextNode :: restPath, source, middle, target, secondPath, hFirst, hSecond =>
      twoSatAndIntro (twoSatHasEdge system source nextNode)
        (twoSatIsPathFrom system nextNode (twoSatAppendLiterals restPath secondPath) target)
        (twoSatAndLeft (twoSatHasEdge system source nextNode)
          (twoSatIsPathFrom system nextNode restPath middle) hFirst)
        (twoSatPathAppend system restPath nextNode middle target secondPath
          (twoSatAndRight (twoSatHasEdge system source nextNode)
            (twoSatIsPathFrom system nextNode restPath middle) hFirst)
          hSecond)

/-- Semantic reachability: SOME checked path exists. -/
def TwoSatReaches (system : List TwoSatClause) (source target : TwoSatLiteral) : Prop :=
  ∃ pathWitness, twoSatIsPathFrom system source pathWitness target = true

/-- Reflexivity of reachability: the empty path. -/
theorem twoSatReachesRefl (system : List TwoSatClause) (node : TwoSatLiteral) :
    TwoSatReaches system node node :=
  Exists.intro [] (twoSatLiteralBeqRefl node)

/-- A single edge reaches. -/
theorem twoSatReachesOfEdge (system : List TwoSatClause) (source target : TwoSatLiteral)
    (hEdge : twoSatHasEdge system source target = true) : TwoSatReaches system source target :=
  Exists.intro [target]
    (twoSatAndIntro (twoSatHasEdge system source target) (twoSatLiteralBeq target target)
      hEdge (twoSatLiteralBeqRefl target))

/-- Transitivity of reachability, by path append. -/
theorem twoSatReachesTrans (system : List TwoSatClause) (source middle target : TwoSatLiteral)
    (hFirst : TwoSatReaches system source middle) (hSecond : TwoSatReaches system middle target) :
    TwoSatReaches system source target := by
  cases hFirst with
  | intro firstPath hFirstPath =>
      cases hSecond with
      | intro secondPath hSecondPath =>
          exact Exists.intro (twoSatAppendLiterals firstPath secondPath)
            (twoSatPathAppend system firstPath source middle target secondPath hFirstPath hSecondPath)

/-! ## Skew duality at the path level -/

/-- Accumulator for the dual path: negations of the traversed prefix, reversed. -/
def twoSatDualPathAux : TwoSatLiteral → List TwoSatLiteral → List TwoSatLiteral → List TwoSatLiteral
  | _source, [], accumulated => accumulated
  | source, nextNode :: restPath, accumulated =>
      twoSatDualPathAux nextNode restPath (twoSatNegate source :: accumulated)

/-- Dual-path accumulator invariant: a forward path prefix plus a checked accumulator
suffix from `¬source` assemble into a checked dual path from `¬target`. -/
theorem twoSatDualPathAuxSound (system : List TwoSatClause) :
    (path : List TwoSatLiteral) → (source target finalTarget : TwoSatLiteral) →
    (accumulated : List TwoSatLiteral) →
    twoSatIsPathFrom system source path target = true →
    twoSatIsPathFrom system (twoSatNegate source) accumulated finalTarget = true →
    twoSatIsPathFrom system (twoSatNegate target) (twoSatDualPathAux source path accumulated)
      finalTarget = true
  | [], source, target, _finalTarget, _accumulated, hPath, hAccumulated => by
      rw [← twoSatLiteralBeqImpliesEq source target hPath]
      exact hAccumulated
  | nextNode :: restPath, source, target, finalTarget, accumulated, hPath, hAccumulated =>
      twoSatDualPathAuxSound system restPath nextNode target finalTarget
        (twoSatNegate source :: accumulated)
        (twoSatAndRight (twoSatHasEdge system source nextNode)
          (twoSatIsPathFrom system nextNode restPath target) hPath)
        (twoSatAndIntro (twoSatHasEdge system (twoSatNegate nextNode) (twoSatNegate source))
          (twoSatIsPathFrom system (twoSatNegate source) accumulated finalTarget)
          (twoSatHasEdgeDual system source nextNode
            (twoSatAndLeft (twoSatHasEdge system source nextNode)
              (twoSatIsPathFrom system nextNode restPath target) hPath))
          hAccumulated)

/-- **Skew duality, path level**: a checked path `source ⇝ target` dualizes to a checked
path `¬target ⇝ ¬source`. -/
theorem twoSatPathDual (system : List TwoSatClause) (source target : TwoSatLiteral)
    (path : List TwoSatLiteral)
    (hPath : twoSatIsPathFrom system source path target = true) :
    twoSatIsPathFrom system (twoSatNegate target) (twoSatDualPathAux source path [])
      (twoSatNegate source) = true :=
  twoSatDualPathAuxSound system path source target (twoSatNegate source) [] hPath
    (twoSatLiteralBeqRefl (twoSatNegate source))

/-- Reachability dualizes. -/
theorem twoSatReachesDual (system : List TwoSatClause) (source target : TwoSatLiteral)
    (hReaches : TwoSatReaches system source target) :
    TwoSatReaches system (twoSatNegate target) (twoSatNegate source) := by
  cases hReaches with
  | intro pathWitness hPath =>
      exact Exists.intro (twoSatDualPathAux source pathWitness [])
        (twoSatPathDual system source target pathWitness hPath)

/-- Clause membership persists under system extension. -/
theorem twoSatClauseMemberConsMono (extraClause : TwoSatClause) (system : List TwoSatClause)
    (clause : TwoSatClause) (hMember : twoSatClauseMember clause system = true) :
    twoSatClauseMember clause (extraClause :: system) = true :=
  twoSatOrIntroRight (twoSatClauseBeq clause extraClause) (twoSatClauseMember clause system) hMember

/-! ## Semantics: assignments, evaluation, force -/

/-- Evaluate a literal under an assignment. -/
def twoSatEvalLiteral (assignment : Nat → Bool) (literal : TwoSatLiteral) : Bool :=
  match literal.isPositive with
  | true => assignment literal.variableIndex
  | false => Bool.not (assignment literal.variableIndex)

/-- Evaluating a negation negates the evaluation. -/
theorem twoSatEvalNegate (assignment : Nat → Bool) : (literal : TwoSatLiteral) →
    twoSatEvalLiteral assignment (twoSatNegate literal) =
      Bool.not (twoSatEvalLiteral assignment literal)
  | TwoSatLiteral.mk _index true => rfl
  | TwoSatLiteral.mk index false => by
      show assignment index = Bool.not (Bool.not (assignment index))
      cases hValue : assignment index with
      | true => rfl
      | false => rfl

/-- Evaluate a clause (disjunction of its two literals). -/
def twoSatEvalClause (assignment : Nat → Bool) (clause : TwoSatClause) : Bool :=
  twoSatEvalLiteral assignment clause.firstLiteral ||
    twoSatEvalLiteral assignment clause.secondLiteral

/-- Evaluate a whole system (conjunction of clauses). -/
def twoSatSatisfies (assignment : Nat → Bool) : List TwoSatClause → Bool
  | [] => true
  | clause :: rest => twoSatEvalClause assignment clause && twoSatSatisfies assignment rest

/-- A satisfying assignment satisfies every member clause. -/
theorem twoSatSatisfiesClauseMember (assignment : Nat → Bool) :
    (system : List TwoSatClause) → (clause : TwoSatClause) →
    twoSatSatisfies assignment system = true →
    twoSatClauseMember clause system = true →
    twoSatEvalClause assignment clause = true
  | [], _clause, _hSat, hMember => Bool.noConfusion hMember
  | head :: rest, clause, hSat, hMember => by
      cases twoSatOrCases (twoSatClauseBeq clause head) (twoSatClauseMember clause rest) hMember with
      | inl hBeq =>
          rw [twoSatClauseBeqImpliesEq clause head hBeq]
          exact twoSatAndLeft (twoSatEvalClause assignment head) (twoSatSatisfies assignment rest) hSat
      | inr hRest =>
          exact twoSatSatisfiesClauseMember assignment rest clause
            (twoSatAndRight (twoSatEvalClause assignment head) (twoSatSatisfies assignment rest) hSat)
            hRest

/-- **Edge force**: under a satisfying assignment, a true edge source forces a true target. -/
theorem twoSatEdgeForces (system : List TwoSatClause) (assignment : Nat → Bool)
    (source target : TwoSatLiteral)
    (hSat : twoSatSatisfies assignment system = true)
    (hEdge : twoSatHasEdge system source target = true)
    (hSource : twoSatEvalLiteral assignment source = true) :
    twoSatEvalLiteral assignment target = true := by
  cases twoSatHasEdgeExistsClause system source target hEdge with
  | intro clause hClause =>
      have hClauseTrue : twoSatEvalClause assignment clause = true :=
        twoSatSatisfiesClauseMember assignment system clause hSat hClause.left
      cases twoSatClauseHasEdgeCases clause source target hClause.right with
      | inl hFirstOrientation =>
          have hFirstFalse : twoSatEvalLiteral assignment clause.firstLiteral = false := by
            have hNegTrue : twoSatEvalLiteral assignment (twoSatNegate clause.firstLiteral) = true := by
              rw [← hFirstOrientation.left]
              exact hSource
            rw [twoSatEvalNegate assignment clause.firstLiteral] at hNegTrue
            exact twoSatNotEqTrue (twoSatEvalLiteral assignment clause.firstLiteral) hNegTrue
          rw [hFirstOrientation.right]
          cases twoSatOrCases (twoSatEvalLiteral assignment clause.firstLiteral)
              (twoSatEvalLiteral assignment clause.secondLiteral) hClauseTrue with
          | inl hFirstTrue =>
              rw [hFirstFalse] at hFirstTrue
              exact Bool.noConfusion hFirstTrue
          | inr hSecondTrue => exact hSecondTrue
      | inr hSecondOrientation =>
          have hSecondFalse : twoSatEvalLiteral assignment clause.secondLiteral = false := by
            have hNegTrue : twoSatEvalLiteral assignment (twoSatNegate clause.secondLiteral) = true := by
              rw [← hSecondOrientation.left]
              exact hSource
            rw [twoSatEvalNegate assignment clause.secondLiteral] at hNegTrue
            exact twoSatNotEqTrue (twoSatEvalLiteral assignment clause.secondLiteral) hNegTrue
          rw [hSecondOrientation.right]
          cases twoSatOrCases (twoSatEvalLiteral assignment clause.firstLiteral)
              (twoSatEvalLiteral assignment clause.secondLiteral) hClauseTrue with
          | inl hFirstTrue => exact hFirstTrue
          | inr hSecondTrue =>
              rw [hSecondFalse] at hSecondTrue
              exact Bool.noConfusion hSecondTrue

/-- **Path force**: truth propagates along a checked path. -/
theorem twoSatPathForces (system : List TwoSatClause) (assignment : Nat → Bool)
    (hSat : twoSatSatisfies assignment system = true) :
    (path : List TwoSatLiteral) → (source target : TwoSatLiteral) →
    twoSatIsPathFrom system source path target = true →
    twoSatEvalLiteral assignment source = true →
    twoSatEvalLiteral assignment target = true
  | [], source, target, hPath, hSource => by
      rw [← twoSatLiteralBeqImpliesEq source target hPath]
      exact hSource
  | nextNode :: restPath, source, target, hPath, hSource =>
      twoSatPathForces system assignment hSat restPath nextNode target
        (twoSatAndRight (twoSatHasEdge system source nextNode)
          (twoSatIsPathFrom system nextNode restPath target) hPath)
        (twoSatEdgeForces system assignment source nextNode hSat
          (twoSatAndLeft (twoSatHasEdge system source nextNode)
            (twoSatIsPathFrom system nextNode restPath target) hPath)
          hSource)

/-- **Certificate refutation**: two checked paths `base ⇝ ¬base` and `¬base ⇝ base`
refute every satisfying assignment. -/
theorem twoSatContradictionPathsSound (system : List TwoSatClause) (assignment : Nat → Bool)
    (baseLiteral : TwoSatLiteral) (forwardPath backwardPath : List TwoSatLiteral)
    (hForward : twoSatIsPathFrom system baseLiteral forwardPath (twoSatNegate baseLiteral) = true)
    (hBackward : twoSatIsPathFrom system (twoSatNegate baseLiteral) backwardPath baseLiteral = true)
    (hSat : twoSatSatisfies assignment system = true) : False := by
  cases hValue : twoSatEvalLiteral assignment baseLiteral with
  | true =>
      have hNegTrue : twoSatEvalLiteral assignment (twoSatNegate baseLiteral) = true :=
        twoSatPathForces system assignment hSat forwardPath baseLiteral (twoSatNegate baseLiteral)
          hForward hValue
      rw [twoSatEvalNegate assignment baseLiteral, hValue] at hNegTrue
      exact Bool.noConfusion hNegTrue
  | false =>
      have hNegTrue : twoSatEvalLiteral assignment (twoSatNegate baseLiteral) = true := by
        rw [twoSatEvalNegate assignment baseLiteral, hValue]
        exact rfl
      have hBaseTrue : twoSatEvalLiteral assignment baseLiteral = true :=
        twoSatPathForces system assignment hSat backwardPath (twoSatNegate baseLiteral) baseLiteral
          hBackward hNegTrue
      rw [hValue] at hBaseTrue
      exact Bool.noConfusion hBaseTrue

/-! ## Certificate-bearing reachability closure -/

/-- A closure entry: a reached literal together with the path that discovered it. -/
structure TwoSatReachEntry where
  reachedLiteral : TwoSatLiteral
  pathWitness : List TwoSatLiteral

/-- The literals of an entry list. -/
def twoSatEntryLiterals : List TwoSatReachEntry → List TwoSatLiteral
  | [] => []
  | entry :: rest => entry.reachedLiteral :: twoSatEntryLiterals rest

/-- Cons-only append of entry lists. -/
def twoSatAppendEntries : List TwoSatReachEntry → List TwoSatReachEntry → List TwoSatReachEntry
  | [], second => second
  | entry :: rest, second => entry :: twoSatAppendEntries rest second

/-- Appending the empty entry list is the identity. -/
theorem twoSatAppendEntriesNil : (entries : List TwoSatReachEntry) →
    twoSatAppendEntries entries [] = entries
  | [] => rfl
  | entry :: rest => congrArg (List.cons entry) (twoSatAppendEntriesNil rest)

/-- Entry literals commute with append. -/
theorem twoSatEntryLiteralsAppend : (first second : List TwoSatReachEntry) →
    twoSatEntryLiterals (twoSatAppendEntries first second) =
      twoSatAppendLiterals (twoSatEntryLiterals first) (twoSatEntryLiterals second)
  | [], _second => rfl
  | entry :: rest, second =>
      congrArg (List.cons entry.reachedLiteral) (twoSatEntryLiteralsAppend rest second)

/-- Find the entry of a literal. -/
def twoSatFindEntry (needle : TwoSatLiteral) : List TwoSatReachEntry → Option TwoSatReachEntry
  | [] => Option.none
  | entry :: rest =>
      match twoSatLiteralBeq needle entry.reachedLiteral with
      | true => Option.some entry
      | false => twoSatFindEntry needle rest

/-- Find a visited entry with an edge into the candidate. -/
def twoSatFindEdgeParent (system : List TwoSatClause) (candidate : TwoSatLiteral) :
    List TwoSatReachEntry → Option TwoSatReachEntry
  | [] => Option.none
  | entry :: rest =>
      match twoSatHasEdge system entry.reachedLiteral candidate with
      | true => Option.some entry
      | false => twoSatFindEdgeParent system candidate rest

/-- All entries carry checked paths from the source. -/
def twoSatAllEntriesValid (system : List TwoSatClause) (source : TwoSatLiteral) :
    List TwoSatReachEntry → Bool
  | [] => true
  | entry :: rest =>
      twoSatIsPathFrom system source entry.pathWitness entry.reachedLiteral &&
      twoSatAllEntriesValid system source rest

/-- Consider one universe candidate: prepend it to the newcomers when it is fresh and some
visited entry has an edge into it (extending that entry's path witness). -/
def twoSatConsiderCandidate (system : List TwoSatClause) (visited : List TwoSatReachEntry)
    (candidate : TwoSatLiteral) (accumulated : List TwoSatReachEntry) : List TwoSatReachEntry :=
  match twoSatLiteralMember candidate (twoSatEntryLiterals visited) ||
        twoSatLiteralMember candidate (twoSatEntryLiterals accumulated) with
  | true => accumulated
  | false =>
      match twoSatFindEdgeParent system candidate visited with
      | Option.none => accumulated
      | Option.some parentEntry =>
          TwoSatReachEntry.mk candidate
            (twoSatAppendLiterals parentEntry.pathWitness [candidate]) :: accumulated

/-- One expansion sweep over the pending universe, accumulating fresh newcomers. -/
def twoSatCollectNewcomers (system : List TwoSatClause) (visited : List TwoSatReachEntry) :
    List TwoSatLiteral → List TwoSatReachEntry → List TwoSatReachEntry
  | [], accumulated => accumulated
  | candidate :: remainingUniverse, accumulated =>
      twoSatCollectNewcomers system visited remainingUniverse
        (twoSatConsiderCandidate system visited candidate accumulated)

/-- One closure round: append the sweep's newcomers to the visited list. -/
def twoSatExpandStep (system : List TwoSatClause) (literalUniverse : List TwoSatLiteral)
    (visited : List TwoSatReachEntry) : List TwoSatReachEntry :=
  twoSatAppendEntries visited (twoSatCollectNewcomers system visited literalUniverse [])

/-- Fuel-bounded iteration of closure rounds. -/
def twoSatIterateExpansion (system : List TwoSatClause) (literalUniverse : List TwoSatLiteral) :
    Nat → List TwoSatReachEntry → List TwoSatReachEntry
  | Nat.zero, visited => visited
  | Nat.succ remainingFuel, visited =>
      twoSatIterateExpansion system literalUniverse remainingFuel
        (twoSatExpandStep system literalUniverse visited)

/-- The certificate-bearing reach closure of a source literal. -/
def twoSatComputeReach (system : List TwoSatClause) (source : TwoSatLiteral) :
    List TwoSatReachEntry :=
  twoSatIterateExpansion system (twoSatUniverse system)
    (Nat.succ (twoSatUniverse system).length) [TwoSatReachEntry.mk source []]

/-- Computed reachability: membership in the closure's literals. -/
def twoSatComputedReaches (system : List TwoSatClause) (source target : TwoSatLiteral) : Bool :=
  twoSatLiteralMember target (twoSatEntryLiterals (twoSatComputeReach system source))

/-- The consider step preserves accumulated membership. -/
theorem twoSatConsiderExtends (system : List TwoSatClause) (visited : List TwoSatReachEntry)
    (candidate : TwoSatLiteral) (accumulated : List TwoSatReachEntry) (probe : TwoSatLiteral)
    (hMember : twoSatLiteralMember probe (twoSatEntryLiterals accumulated) = true) :
    twoSatLiteralMember probe
      (twoSatEntryLiterals (twoSatConsiderCandidate system visited candidate accumulated)) = true := by
  cases hSkip : (twoSatLiteralMember candidate (twoSatEntryLiterals visited) ||
      twoSatLiteralMember candidate (twoSatEntryLiterals accumulated)) with
  | true =>
      simp only [twoSatConsiderCandidate, hSkip]
      exact hMember
  | false =>
      cases hParent : twoSatFindEdgeParent system candidate visited with
      | none =>
          simp only [twoSatConsiderCandidate, hSkip, hParent]
          exact hMember
      | some parentEntry =>
          simp only [twoSatConsiderCandidate, hSkip, hParent]
          exact twoSatOrIntroRight (twoSatLiteralBeq probe candidate)
            (twoSatLiteralMember probe (twoSatEntryLiterals accumulated)) hMember

/-- The sweep preserves accumulated membership. -/
theorem twoSatCollectExtends (system : List TwoSatClause) (visited : List TwoSatReachEntry) :
    (pending : List TwoSatLiteral) → (accumulated : List TwoSatReachEntry) →
    (probe : TwoSatLiteral) →
    twoSatLiteralMember probe (twoSatEntryLiterals accumulated) = true →
    twoSatLiteralMember probe
      (twoSatEntryLiterals (twoSatCollectNewcomers system visited pending accumulated)) = true
  | [], _accumulated, _probe, hMember => hMember
  | candidate :: remainingUniverse, accumulated, probe, hMember =>
      twoSatCollectExtends system visited remainingUniverse
        (twoSatConsiderCandidate system visited candidate accumulated) probe
        (twoSatConsiderExtends system visited candidate accumulated probe hMember)

/-- If a sweep returns NO newcomers, every fresh pending candidate has no edge from the
visited set — the visited set is edge-closed over the pending list. -/
theorem twoSatCollectEmptyClosed (system : List TwoSatClause) (visited : List TwoSatReachEntry) :
    (pending : List TwoSatLiteral) → (accumulated : List TwoSatReachEntry) →
    twoSatCollectNewcomers system visited pending accumulated = [] →
    (candidate : TwoSatLiteral) →
    twoSatLiteralMember candidate pending = true →
    twoSatLiteralMember candidate (twoSatEntryLiterals visited) = false →
    twoSatFindEdgeParent system candidate visited = Option.none
  | [], _accumulated, _hCollect, _candidate, hPending, _hFresh => Bool.noConfusion hPending
  | probeHead :: pendingRest, accumulated, hCollect, candidate, hPending, hFresh => by
      cases twoSatOrCases (twoSatLiteralBeq candidate probeHead)
          (twoSatLiteralMember candidate pendingRest) hPending with
      | inl hBeqHead =>
          have hCandidateEq : candidate = probeHead :=
            twoSatLiteralBeqImpliesEq candidate probeHead hBeqHead
          subst hCandidateEq
          cases hParent : twoSatFindEdgeParent system candidate visited with
          | none => rfl
          | some parentEntry =>
              cases hAccMember : twoSatLiteralMember candidate (twoSatEntryLiterals accumulated) with
              | true =>
                  have hSkip : (twoSatLiteralMember candidate (twoSatEntryLiterals visited) ||
                      twoSatLiteralMember candidate (twoSatEntryLiterals accumulated)) = true :=
                    twoSatOrIntroRight (twoSatLiteralMember candidate (twoSatEntryLiterals visited))
                      (twoSatLiteralMember candidate (twoSatEntryLiterals accumulated)) hAccMember
                  have hStay : twoSatCollectNewcomers system visited pendingRest accumulated = [] := by
                    simp only [twoSatCollectNewcomers, twoSatConsiderCandidate, hSkip] at hCollect
                    exact hCollect
                  have hExtend := twoSatCollectExtends system visited pendingRest accumulated
                    candidate hAccMember
                  rw [hStay] at hExtend
                  exact Bool.noConfusion hExtend
              | false =>
                  have hSkip : (twoSatLiteralMember candidate (twoSatEntryLiterals visited) ||
                      twoSatLiteralMember candidate (twoSatEntryLiterals accumulated)) = false := by
                    rw [hFresh, hAccMember]
                    exact rfl
                  have hStay : twoSatCollectNewcomers system visited pendingRest
                      (TwoSatReachEntry.mk candidate
                        (twoSatAppendLiterals parentEntry.pathWitness [candidate]) :: accumulated) = [] := by
                    simp only [twoSatCollectNewcomers, twoSatConsiderCandidate, hSkip, hParent] at hCollect
                    exact hCollect
                  have hSelf : twoSatLiteralMember candidate (twoSatEntryLiterals
                      (TwoSatReachEntry.mk candidate
                        (twoSatAppendLiterals parentEntry.pathWitness [candidate]) :: accumulated)) = true :=
                    twoSatOrIntroLeft (twoSatLiteralBeq candidate candidate)
                      (twoSatLiteralMember candidate (twoSatEntryLiterals accumulated))
                      (twoSatLiteralBeqRefl candidate)
                  have hExtend := twoSatCollectExtends system visited pendingRest
                      (TwoSatReachEntry.mk candidate
                        (twoSatAppendLiterals parentEntry.pathWitness [candidate]) :: accumulated)
                      candidate hSelf
                  rw [hStay] at hExtend
                  exact Bool.noConfusion hExtend
      | inr hPendingRest =>
          have hStep : twoSatCollectNewcomers system visited pendingRest
              (twoSatConsiderCandidate system visited probeHead accumulated) = [] := by
            simp only [twoSatCollectNewcomers] at hCollect
            exact hCollect
          exact twoSatCollectEmptyClosed system visited pendingRest
            (twoSatConsiderCandidate system visited probeHead accumulated) hStep candidate
            hPendingRest hFresh

/-- A visited entry with an edge into the candidate makes the parent search succeed. -/
theorem twoSatFindEdgeParentNoneAbsurd (system : List TwoSatClause) (candidate : TwoSatLiteral) :
    (visited : List TwoSatReachEntry) → (sourceLit : TwoSatLiteral) →
    twoSatLiteralMember sourceLit (twoSatEntryLiterals visited) = true →
    twoSatHasEdge system sourceLit candidate = true →
    twoSatFindEdgeParent system candidate visited = Option.none → False
  | [], _sourceLit, hMember, _hEdge, _hNone => Bool.noConfusion hMember
  | entry :: rest, sourceLit, hMember, hEdge, hNone => by
      cases hEdgeHead : twoSatHasEdge system entry.reachedLiteral candidate with
      | true =>
          simp only [twoSatFindEdgeParent, hEdgeHead] at hNone
          exact nomatch hNone
      | false =>
          have hRestNone : twoSatFindEdgeParent system candidate rest = Option.none := by
            simp only [twoSatFindEdgeParent, hEdgeHead] at hNone
            exact hNone
          cases twoSatOrCases (twoSatLiteralBeq sourceLit entry.reachedLiteral)
              (twoSatLiteralMember sourceLit (twoSatEntryLiterals rest)) hMember with
          | inl hHeadBeq =>
              rw [twoSatLiteralBeqImpliesEq sourceLit entry.reachedLiteral hHeadBeq] at hEdge
              rw [hEdge] at hEdgeHead
              exact Bool.noConfusion hEdgeHead
          | inr hRestMember =>
              exact twoSatFindEdgeParentNoneAbsurd system candidate rest sourceLit hRestMember
                hEdge hRestNone

/-- A successful parent search returns a visited entry with a checked path and an edge. -/
theorem twoSatFindEdgeParentSound (system : List TwoSatClause) (candidate source : TwoSatLiteral) :
    (visited : List TwoSatReachEntry) → (parentEntry : TwoSatReachEntry) →
    twoSatFindEdgeParent system candidate visited = Option.some parentEntry →
    twoSatAllEntriesValid system source visited = true →
    twoSatIsPathFrom system source parentEntry.pathWitness parentEntry.reachedLiteral = true ∧
    twoSatHasEdge system parentEntry.reachedLiteral candidate = true
  | [], _parentEntry, hFind, _hValid => nomatch hFind
  | entry :: rest, parentEntry, hFind, hValid => by
      cases hEdgeHead : twoSatHasEdge system entry.reachedLiteral candidate with
      | true =>
          have hSome : Option.some entry = Option.some parentEntry := by
            simp only [twoSatFindEdgeParent, hEdgeHead] at hFind
            exact hFind
          have hEntryEq : entry = parentEntry := by
            injection hSome
          rw [← hEntryEq]
          exact And.intro
            (twoSatAndLeft (twoSatIsPathFrom system source entry.pathWitness entry.reachedLiteral)
              (twoSatAllEntriesValid system source rest) hValid)
            hEdgeHead
      | false =>
          have hRestFind : twoSatFindEdgeParent system candidate rest = Option.some parentEntry := by
            simp only [twoSatFindEdgeParent, hEdgeHead] at hFind
            exact hFind
          exact twoSatFindEdgeParentSound system candidate source rest parentEntry hRestFind
            (twoSatAndRight (twoSatIsPathFrom system source entry.pathWitness entry.reachedLiteral)
              (twoSatAllEntriesValid system source rest) hValid)

/-- **The linchpin**: an edge-closed visited set containing the source captures every
checked path endpoint — computed non-membership refutes genuine reachability. -/
theorem twoSatClosedRefutesPath (system : List TwoSatClause) (visited : List TwoSatReachEntry)
    (hClosed : ∀ candidate : TwoSatLiteral,
      twoSatLiteralMember candidate (twoSatUniverse system) = true →
      twoSatLiteralMember candidate (twoSatEntryLiterals visited) = false →
      twoSatFindEdgeParent system candidate visited = Option.none) :
    (path : List TwoSatLiteral) → (source target : TwoSatLiteral) →
    twoSatLiteralMember source (twoSatEntryLiterals visited) = true →
    twoSatIsPathFrom system source path target = true →
    twoSatLiteralMember target (twoSatEntryLiterals visited) = true
  | [], source, target, hSource, hPath => by
      rw [← twoSatLiteralBeqImpliesEq source target hPath]
      exact hSource
  | nextNode :: restPath, source, target, hSource, hPath => by
      have hEdge : twoSatHasEdge system source nextNode = true :=
        twoSatAndLeft (twoSatHasEdge system source nextNode)
          (twoSatIsPathFrom system nextNode restPath target) hPath
      cases hNextVisited : twoSatLiteralMember nextNode (twoSatEntryLiterals visited) with
      | true =>
          exact twoSatClosedRefutesPath system visited hClosed restPath nextNode target hNextVisited
            (twoSatAndRight (twoSatHasEdge system source nextNode)
              (twoSatIsPathFrom system nextNode restPath target) hPath)
      | false =>
          exact False.elim (twoSatFindEdgeParentNoneAbsurd system nextNode visited source
            hSource hEdge
            (hClosed nextNode (twoSatEdgeTargetInUniverse system source nextNode hEdge) hNextVisited))

/-- Membership in the closure literals means the entry search succeeds. -/
theorem twoSatFindEntryOfMemberAbsurd (needle : TwoSatLiteral) :
    (entries : List TwoSatReachEntry) →
    twoSatLiteralMember needle (twoSatEntryLiterals entries) = true →
    twoSatFindEntry needle entries = Option.none → False
  | [], hMember, _hNone => Bool.noConfusion hMember
  | entry :: rest, hMember, hNone => by
      cases hBeq : twoSatLiteralBeq needle entry.reachedLiteral with
      | true =>
          simp only [twoSatFindEntry, hBeq] at hNone
          exact nomatch hNone
      | false =>
          have hRestNone : twoSatFindEntry needle rest = Option.none := by
            simp only [twoSatFindEntry, hBeq] at hNone
            exact hNone
          have hRestMember : twoSatLiteralMember needle (twoSatEntryLiterals rest) = true := by
            cases twoSatOrCases (twoSatLiteralBeq needle entry.reachedLiteral)
                (twoSatLiteralMember needle (twoSatEntryLiterals rest)) hMember with
            | inl hHit =>
                rw [hBeq] at hHit
                exact Bool.noConfusion hHit
            | inr hTail => exact hTail
          exact twoSatFindEntryOfMemberAbsurd needle rest hRestMember hRestNone

/-- A found entry carries a checked path to the needle. -/
theorem twoSatFindEntrySound (system : List TwoSatClause) (source needle : TwoSatLiteral) :
    (entries : List TwoSatReachEntry) → (found : TwoSatReachEntry) →
    twoSatFindEntry needle entries = Option.some found →
    twoSatAllEntriesValid system source entries = true →
    twoSatIsPathFrom system source found.pathWitness needle = true
  | [], _found, hFind, _hValid => nomatch hFind
  | entry :: rest, found, hFind, hValid => by
      cases hBeq : twoSatLiteralBeq needle entry.reachedLiteral with
      | true =>
          have hSome : Option.some entry = Option.some found := by
            simp only [twoSatFindEntry, hBeq] at hFind
            exact hFind
          have hEntryEq : entry = found := by
            injection hSome
          rw [twoSatLiteralBeqImpliesEq needle entry.reachedLiteral hBeq, ← hEntryEq]
          exact twoSatAndLeft (twoSatIsPathFrom system source entry.pathWitness entry.reachedLiteral)
            (twoSatAllEntriesValid system source rest) hValid
      | false =>
          have hRestFind : twoSatFindEntry needle rest = Option.some found := by
            simp only [twoSatFindEntry, hBeq] at hFind
            exact hFind
          exact twoSatFindEntrySound system source needle rest found hRestFind
            (twoSatAndRight (twoSatIsPathFrom system source entry.pathWitness entry.reachedLiteral)
              (twoSatAllEntriesValid system source rest) hValid)

/-- The sweep preserves duplicate-freedom of the visited-plus-accumulated literals. -/
theorem twoSatCollectNodup (system : List TwoSatClause) (visited : List TwoSatReachEntry) :
    (pending : List TwoSatLiteral) → (accumulated : List TwoSatReachEntry) →
    twoSatLiteralsNodup (twoSatAppendLiterals (twoSatEntryLiterals visited)
      (twoSatEntryLiterals accumulated)) = true →
    twoSatLiteralsNodup (twoSatAppendLiterals (twoSatEntryLiterals visited)
      (twoSatEntryLiterals (twoSatCollectNewcomers system visited pending accumulated))) = true
  | [], _accumulated, hNodup => hNodup
  | candidate :: remainingUniverse, accumulated, hNodup => by
      apply twoSatCollectNodup system visited remainingUniverse
        (twoSatConsiderCandidate system visited candidate accumulated)
      cases hSkip : (twoSatLiteralMember candidate (twoSatEntryLiterals visited) ||
          twoSatLiteralMember candidate (twoSatEntryLiterals accumulated)) with
      | true =>
          simp only [twoSatConsiderCandidate, hSkip]
          exact hNodup
      | false =>
          cases hParent : twoSatFindEdgeParent system candidate visited with
          | none =>
              simp only [twoSatConsiderCandidate, hSkip, hParent]
              exact hNodup
          | some parentEntry =>
              simp only [twoSatConsiderCandidate, hSkip, hParent]
              exact twoSatNodupInsertMiddle candidate (twoSatEntryLiterals visited)
                (twoSatEntryLiterals accumulated) hNodup
                (twoSatOrFalseSplit (twoSatLiteralMember candidate (twoSatEntryLiterals visited))
                  (twoSatLiteralMember candidate (twoSatEntryLiterals accumulated)) hSkip).left
                (twoSatOrFalseSplit (twoSatLiteralMember candidate (twoSatEntryLiterals visited))
                  (twoSatLiteralMember candidate (twoSatEntryLiterals accumulated)) hSkip).right

/-- The sweep's output literals stay inside the ambient universe. -/
theorem twoSatCollectSubset (system : List TwoSatClause) (visited : List TwoSatReachEntry)
    (universeList : List TwoSatLiteral) :
    (pending : List TwoSatLiteral) → (accumulated : List TwoSatReachEntry) →
    twoSatAllMembersOf universeList pending = true →
    twoSatAllMembersOf universeList (twoSatEntryLiterals accumulated) = true →
    twoSatAllMembersOf universeList
      (twoSatEntryLiterals (twoSatCollectNewcomers system visited pending accumulated)) = true
  | [], _accumulated, _hPending, hAccumulated => hAccumulated
  | candidate :: remainingUniverse, accumulated, hPending, hAccumulated => by
      apply twoSatCollectSubset system visited universeList remainingUniverse
        (twoSatConsiderCandidate system visited candidate accumulated)
        (twoSatAndRight (twoSatLiteralMember candidate universeList)
          (twoSatAllMembersOf universeList remainingUniverse) hPending)
      cases hSkip : (twoSatLiteralMember candidate (twoSatEntryLiterals visited) ||
          twoSatLiteralMember candidate (twoSatEntryLiterals accumulated)) with
      | true =>
          simp only [twoSatConsiderCandidate, hSkip]
          exact hAccumulated
      | false =>
          cases hParent : twoSatFindEdgeParent system candidate visited with
          | none =>
              simp only [twoSatConsiderCandidate, hSkip, hParent]
              exact hAccumulated
          | some parentEntry =>
              simp only [twoSatConsiderCandidate, hSkip, hParent]
              exact twoSatAndIntro (twoSatLiteralMember candidate universeList)
                (twoSatAllMembersOf universeList (twoSatEntryLiterals accumulated))
                (twoSatAndLeft (twoSatLiteralMember candidate universeList)
                  (twoSatAllMembersOf universeList remainingUniverse) hPending)
                hAccumulated

/-- The sweep only appends entries with checked paths. -/
theorem twoSatCollectAllValid (system : List TwoSatClause) (source : TwoSatLiteral)
    (visited : List TwoSatReachEntry) :
    (pending : List TwoSatLiteral) → (accumulated : List TwoSatReachEntry) →
    twoSatAllEntriesValid system source visited = true →
    twoSatAllEntriesValid system source accumulated = true →
    twoSatAllEntriesValid system source
      (twoSatCollectNewcomers system visited pending accumulated) = true
  | [], _accumulated, _hVisited, hAccumulated => hAccumulated
  | candidate :: remainingUniverse, accumulated, hVisited, hAccumulated => by
      apply twoSatCollectAllValid system source visited remainingUniverse
        (twoSatConsiderCandidate system visited candidate accumulated) hVisited
      cases hSkip : (twoSatLiteralMember candidate (twoSatEntryLiterals visited) ||
          twoSatLiteralMember candidate (twoSatEntryLiterals accumulated)) with
      | true =>
          simp only [twoSatConsiderCandidate, hSkip]
          exact hAccumulated
      | false =>
          cases hParent : twoSatFindEdgeParent system candidate visited with
          | none =>
              simp only [twoSatConsiderCandidate, hSkip, hParent]
              exact hAccumulated
          | some parentEntry =>
              simp only [twoSatConsiderCandidate, hSkip, hParent]
              have hParentFacts := twoSatFindEdgeParentSound system candidate source visited
                parentEntry hParent hVisited
              exact twoSatAndIntro
                (twoSatIsPathFrom system source
                  (twoSatAppendLiterals parentEntry.pathWitness [candidate]) candidate)
                (twoSatAllEntriesValid system source accumulated)
                (twoSatPathAppend system parentEntry.pathWitness source parentEntry.reachedLiteral
                  candidate [candidate] hParentFacts.left
                  (twoSatAndIntro (twoSatHasEdge system parentEntry.reachedLiteral candidate)
                    (twoSatLiteralBeq candidate candidate) hParentFacts.right
                    (twoSatLiteralBeqRefl candidate)))
                hAccumulated

/-- Validity survives entry-list append. -/
theorem twoSatAllEntriesValidAppend (system : List TwoSatClause) (source : TwoSatLiteral) :
    (first second : List TwoSatReachEntry) →
    twoSatAllEntriesValid system source first = true →
    twoSatAllEntriesValid system source second = true →
    twoSatAllEntriesValid system source (twoSatAppendEntries first second) = true
  | [], _second, _hFirst, hSecond => hSecond
  | entry :: rest, second, hFirst, hSecond =>
      twoSatAndIntro (twoSatIsPathFrom system source entry.pathWitness entry.reachedLiteral)
        (twoSatAllEntriesValid system source (twoSatAppendEntries rest second))
        (twoSatAndLeft (twoSatIsPathFrom system source entry.pathWitness entry.reachedLiteral)
          (twoSatAllEntriesValid system source rest) hFirst)
        (twoSatAllEntriesValidAppend system source rest second
          (twoSatAndRight (twoSatIsPathFrom system source entry.pathWitness entry.reachedLiteral)
            (twoSatAllEntriesValid system source rest) hFirst)
          hSecond)

/-- The closure round preserves duplicate-freedom. -/
theorem twoSatStepNodup (system : List TwoSatClause) (literalUniverse : List TwoSatLiteral)
    (visited : List TwoSatReachEntry)
    (hNodup : twoSatLiteralsNodup (twoSatEntryLiterals visited) = true) :
    twoSatLiteralsNodup (twoSatEntryLiterals (twoSatExpandStep system literalUniverse visited)) = true := by
  have hBase : twoSatLiteralsNodup (twoSatAppendLiterals (twoSatEntryLiterals visited) []) = true := by
    rw [twoSatAppendLiteralsNil (twoSatEntryLiterals visited)]
    exact hNodup
  have hCollect := twoSatCollectNodup system visited literalUniverse [] hBase
  show twoSatLiteralsNodup (twoSatEntryLiterals (twoSatAppendEntries visited
    (twoSatCollectNewcomers system visited literalUniverse []))) = true
  rw [twoSatEntryLiteralsAppend visited (twoSatCollectNewcomers system visited literalUniverse [])]
  exact hCollect

/-- The closure round stays inside the universe. -/
theorem twoSatStepSubset (system : List TwoSatClause) (literalUniverse : List TwoSatLiteral)
    (visited : List TwoSatReachEntry)
    (hSubset : twoSatAllMembersOf literalUniverse (twoSatEntryLiterals visited) = true) :
    twoSatAllMembersOf literalUniverse
      (twoSatEntryLiterals (twoSatExpandStep system literalUniverse visited)) = true := by
  have hCollect := twoSatCollectSubset system visited literalUniverse literalUniverse []
    (twoSatAllMembersSelf literalUniverse) rfl
  show twoSatAllMembersOf literalUniverse (twoSatEntryLiterals (twoSatAppendEntries visited
    (twoSatCollectNewcomers system visited literalUniverse []))) = true
  rw [twoSatEntryLiteralsAppend visited (twoSatCollectNewcomers system visited literalUniverse [])]
  exact twoSatAllMembersAppendCompose literalUniverse (twoSatEntryLiterals visited)
    (twoSatEntryLiterals (twoSatCollectNewcomers system visited literalUniverse [])) hSubset hCollect

/-- The closure round preserves entry validity. -/
theorem twoSatStepAllValid (system : List TwoSatClause) (literalUniverse : List TwoSatLiteral)
    (source : TwoSatLiteral) (visited : List TwoSatReachEntry)
    (hValid : twoSatAllEntriesValid system source visited = true) :
    twoSatAllEntriesValid system source (twoSatExpandStep system literalUniverse visited) = true := by
  have hCollect := twoSatCollectAllValid system source visited literalUniverse [] hValid rfl
  show twoSatAllEntriesValid system source (twoSatAppendEntries visited
    (twoSatCollectNewcomers system visited literalUniverse [])) = true
  exact twoSatAllEntriesValidAppend system source visited
    (twoSatCollectNewcomers system visited literalUniverse []) hValid hCollect

/-- The closure round preserves membership. -/
theorem twoSatStepMemberMono (system : List TwoSatClause) (literalUniverse : List TwoSatLiteral)
    (visited : List TwoSatReachEntry) (probe : TwoSatLiteral)
    (hMember : twoSatLiteralMember probe (twoSatEntryLiterals visited) = true) :
    twoSatLiteralMember probe
      (twoSatEntryLiterals (twoSatExpandStep system literalUniverse visited)) = true := by
  show twoSatLiteralMember probe (twoSatEntryLiterals (twoSatAppendEntries visited
    (twoSatCollectNewcomers system visited literalUniverse []))) = true
  rw [twoSatEntryLiteralsAppend visited (twoSatCollectNewcomers system visited literalUniverse []),
    twoSatMemberAppendEq probe (twoSatEntryLiterals visited)
      (twoSatEntryLiterals (twoSatCollectNewcomers system visited literalUniverse []))]
  exact twoSatOrIntroLeft (twoSatLiteralMember probe (twoSatEntryLiterals visited))
    (twoSatLiteralMember probe
      (twoSatEntryLiterals (twoSatCollectNewcomers system visited literalUniverse []))) hMember

/-- Iteration preserves entry validity. -/
theorem twoSatIterateAllValid (system : List TwoSatClause) (literalUniverse : List TwoSatLiteral)
    (source : TwoSatLiteral) :
    (fuel : Nat) → (visited : List TwoSatReachEntry) →
    twoSatAllEntriesValid system source visited = true →
    twoSatAllEntriesValid system source
      (twoSatIterateExpansion system literalUniverse fuel visited) = true
  | Nat.zero, _visited, hValid => hValid
  | Nat.succ remainingFuel, visited, hValid =>
      twoSatIterateAllValid system literalUniverse source remainingFuel
        (twoSatExpandStep system literalUniverse visited)
        (twoSatStepAllValid system literalUniverse source visited hValid)

/-- Iteration preserves membership. -/
theorem twoSatIterateMemberMono (system : List TwoSatClause) (literalUniverse : List TwoSatLiteral)
    (probe : TwoSatLiteral) :
    (fuel : Nat) → (visited : List TwoSatReachEntry) →
    twoSatLiteralMember probe (twoSatEntryLiterals visited) = true →
    twoSatLiteralMember probe
      (twoSatEntryLiterals (twoSatIterateExpansion system literalUniverse fuel visited)) = true
  | Nat.zero, _visited, hMember => hMember
  | Nat.succ remainingFuel, visited, hMember =>
      twoSatIterateMemberMono system literalUniverse probe remainingFuel
        (twoSatExpandStep system literalUniverse visited)
        (twoSatStepMemberMono system literalUniverse visited probe hMember)

/-- A stable visited set is a fixpoint of the iteration. -/
theorem twoSatStableIterateIdentity (system : List TwoSatClause)
    (literalUniverse : List TwoSatLiteral) :
    (fuel : Nat) → (visited : List TwoSatReachEntry) →
    twoSatCollectNewcomers system visited literalUniverse [] = [] →
    twoSatIterateExpansion system literalUniverse fuel visited = visited
  | Nat.zero, _visited, _hStable => rfl
  | Nat.succ remainingFuel, visited, hStable => by
      have hStepIdentity : twoSatExpandStep system literalUniverse visited = visited := by
        show twoSatAppendEntries visited
          (twoSatCollectNewcomers system visited literalUniverse []) = visited
        rw [hStable]
        exact twoSatAppendEntriesNil visited
      show twoSatIterateExpansion system literalUniverse remainingFuel
        (twoSatExpandStep system literalUniverse visited) = visited
      rw [hStepIdentity]
      exact twoSatStableIterateIdentity system literalUniverse remainingFuel visited hStable

/-- **Fuel adequacy**: with `|universe| + 1` rounds the closure stabilizes — each unstable
round strictly grows the duplicate-free visited set inside the finite universe, so the
hand-rolled pigeonhole caps the number of unstable rounds. -/
theorem twoSatIterateStabilizes (system : List TwoSatClause)
    (literalUniverse : List TwoSatLiteral) :
    (fuel : Nat) → (visited : List TwoSatReachEntry) →
    twoSatLiteralsNodup (twoSatEntryLiterals visited) = true →
    twoSatAllMembersOf literalUniverse (twoSatEntryLiterals visited) = true →
    twoSatNatLe (Nat.succ literalUniverse.length)
      (fuel + (twoSatEntryLiterals visited).length) = true →
    twoSatCollectNewcomers system (twoSatIterateExpansion system literalUniverse fuel visited)
      literalUniverse [] = []
  | Nat.zero, visited, hNodup, hSubset, hFuel => by
      rw [Nat.zero_add] at hFuel
      exact False.elim (twoSatNatLeSuccAbsurd literalUniverse.length
        (twoSatEntryLiterals visited).length hFuel
        (twoSatNodupSubsetLengthLe (twoSatEntryLiterals visited) literalUniverse hNodup hSubset))
  | Nat.succ remainingFuel, visited, hNodup, hSubset, hFuel => by
      cases hNewcomers : twoSatCollectNewcomers system visited literalUniverse [] with
      | nil =>
          rw [twoSatStableIterateIdentity system literalUniverse (Nat.succ remainingFuel)
            visited hNewcomers]
          exact hNewcomers
      | cons newcomerHead newcomerTail =>
          have hStepEq : twoSatExpandStep system literalUniverse visited =
              twoSatAppendEntries visited (newcomerHead :: newcomerTail) := by
            show twoSatAppendEntries visited
              (twoSatCollectNewcomers system visited literalUniverse []) =
              twoSatAppendEntries visited (newcomerHead :: newcomerTail)
            rw [hNewcomers]
          have hLenEq : (twoSatEntryLiterals (twoSatExpandStep system literalUniverse visited)).length =
              (twoSatEntryLiterals visited).length +
                Nat.succ (twoSatEntryLiterals newcomerTail).length := by
            rw [hStepEq, twoSatEntryLiteralsAppend visited (newcomerHead :: newcomerTail)]
            exact twoSatAppendLiteralsLength (twoSatEntryLiterals visited)
              (newcomerHead.reachedLiteral :: twoSatEntryLiterals newcomerTail)
          have hGrow : twoSatNatLe (Nat.succ (twoSatEntryLiterals visited).length)
              ((twoSatEntryLiterals (twoSatExpandStep system literalUniverse visited)).length) = true := by
            rw [hLenEq]
            exact twoSatNatLeAddRight (twoSatEntryLiterals visited).length
              (twoSatEntryLiterals newcomerTail).length
          have hFuelNext : twoSatNatLe (Nat.succ literalUniverse.length)
              (remainingFuel +
                (twoSatEntryLiterals (twoSatExpandStep system literalUniverse visited)).length) = true := by
            rw [twoSatSuccAdd remainingFuel (twoSatEntryLiterals visited).length] at hFuel
            exact twoSatNatLeTrans (Nat.succ literalUniverse.length)
              (remainingFuel + Nat.succ (twoSatEntryLiterals visited).length)
              (remainingFuel +
                (twoSatEntryLiterals (twoSatExpandStep system literalUniverse visited)).length)
              hFuel
              (twoSatNatLeAddLeftMono remainingFuel
                (Nat.succ (twoSatEntryLiterals visited).length)
                ((twoSatEntryLiterals (twoSatExpandStep system literalUniverse visited)).length)
                hGrow)
          exact twoSatIterateStabilizes system literalUniverse remainingFuel
            (twoSatExpandStep system literalUniverse visited)
            (twoSatStepNodup system literalUniverse visited hNodup)
            (twoSatStepSubset system literalUniverse visited hSubset)
            hFuelNext

/-- The reach closure is stable: its sweep returns no newcomers. -/
theorem twoSatComputeReachStable (system : List TwoSatClause) (source : TwoSatLiteral)
    (hSourceInUniverse : twoSatLiteralMember source (twoSatUniverse system) = true) :
    twoSatCollectNewcomers system (twoSatComputeReach system source)
      (twoSatUniverse system) [] = [] := by
  have hInitNodup : twoSatLiteralsNodup (twoSatEntryLiterals [TwoSatReachEntry.mk source []]) = true := rfl
  have hInitSubset : twoSatAllMembersOf (twoSatUniverse system)
      (twoSatEntryLiterals [TwoSatReachEntry.mk source []]) = true := by
    show (twoSatLiteralMember source (twoSatUniverse system) &&
      twoSatAllMembersOf (twoSatUniverse system) []) = true
    rw [hSourceInUniverse]
    exact rfl
  have hInitFuel : twoSatNatLe (Nat.succ (twoSatUniverse system).length)
      (Nat.succ (twoSatUniverse system).length +
        (twoSatEntryLiterals [TwoSatReachEntry.mk source []]).length) = true :=
    twoSatNatLeAddRight (Nat.succ (twoSatUniverse system).length)
      ((twoSatEntryLiterals [TwoSatReachEntry.mk source []]).length)
  exact twoSatIterateStabilizes system (twoSatUniverse system)
    (Nat.succ (twoSatUniverse system).length) [TwoSatReachEntry.mk source []]
    hInitNodup hInitSubset hInitFuel

/-- Every fresh universe literal has no edge from the stable closure. -/
theorem twoSatComputeReachClosed (system : List TwoSatClause) (source : TwoSatLiteral)
    (hSourceInUniverse : twoSatLiteralMember source (twoSatUniverse system) = true)
    (candidate : TwoSatLiteral)
    (hCandidateUniverse : twoSatLiteralMember candidate (twoSatUniverse system) = true)
    (hFresh : twoSatLiteralMember candidate
      (twoSatEntryLiterals (twoSatComputeReach system source)) = false) :
    twoSatFindEdgeParent system candidate (twoSatComputeReach system source) = Option.none :=
  twoSatCollectEmptyClosed system (twoSatComputeReach system source) (twoSatUniverse system) []
    (twoSatComputeReachStable system source hSourceInUniverse) candidate hCandidateUniverse hFresh

/-- The closure contains its source. -/
theorem twoSatComputeReachContainsSource (system : List TwoSatClause) (source : TwoSatLiteral) :
    twoSatLiteralMember source (twoSatEntryLiterals (twoSatComputeReach system source)) = true :=
  twoSatIterateMemberMono system (twoSatUniverse system) source
    (Nat.succ (twoSatUniverse system).length) [TwoSatReachEntry.mk source []]
    (twoSatOrIntroLeft (twoSatLiteralBeq source source)
      (twoSatLiteralMember source (twoSatEntryLiterals ([] : List TwoSatReachEntry)))
      (twoSatLiteralBeqRefl source))

/-- All closure entries carry checked paths. -/
theorem twoSatComputeReachAllValid (system : List TwoSatClause) (source : TwoSatLiteral) :
    twoSatAllEntriesValid system source (twoSatComputeReach system source) = true :=
  twoSatIterateAllValid system (twoSatUniverse system) source
    (Nat.succ (twoSatUniverse system).length) [TwoSatReachEntry.mk source []]
    (twoSatAndIntro (twoSatIsPathFrom system source [] source)
      (twoSatAllEntriesValid system source []) (twoSatLiteralBeqRefl source) rfl)

/-- **Soundness of computed reachability**: a computed hit yields a checked path. -/
theorem twoSatComputedReachesSound (system : List TwoSatClause) (source target : TwoSatLiteral)
    (hComputed : twoSatComputedReaches system source target = true) :
    TwoSatReaches system source target := by
  cases hFind : twoSatFindEntry target (twoSatComputeReach system source) with
  | none =>
      exact False.elim (twoSatFindEntryOfMemberAbsurd target (twoSatComputeReach system source)
        hComputed hFind)
  | some found =>
      exact Exists.intro found.pathWitness
        (twoSatFindEntrySound system source target (twoSatComputeReach system source) found hFind
          (twoSatComputeReachAllValid system source))

/-- **Completeness of computed reachability** (for sources inside the universe). -/
theorem twoSatComputedReachesComplete (system : List TwoSatClause) (source target : TwoSatLiteral)
    (hSourceInUniverse : twoSatLiteralMember source (twoSatUniverse system) = true)
    (hReaches : TwoSatReaches system source target) :
    twoSatComputedReaches system source target = true := by
  cases hReaches with
  | intro pathWitness hPath =>
      exact twoSatClosedRefutesPath system (twoSatComputeReach system source)
        (fun candidate hCandidateUniverse hFresh =>
          twoSatComputeReachClosed system source hSourceInUniverse candidate
            hCandidateUniverse hFresh)
        pathWitness source target
        (twoSatComputeReachContainsSource system source)
        hPath

/-- A literal genuinely reaching its negation has a censused variable (the first hop's
source is a negated clause literal). -/
theorem twoSatReachesSelfNegVarCollected (system : List TwoSatClause) (probe : TwoSatLiteral)
    (hReaches : TwoSatReaches system probe (twoSatNegate probe)) :
    twoSatNatMember probe.variableIndex (twoSatCollectVariables system) = true := by
  cases hReaches with
  | intro pathWitness hPath =>
      cases pathWitness with
      | nil =>
          have hBeq : twoSatLiteralBeq probe (twoSatNegate probe) = true := hPath
          exact Bool.noConfusion ((twoSatLiteralBeqNegateSelf probe).symm.trans hBeq)
      | cons nextNode restPath =>
          exact twoSatEdgeSourceVarCollected system probe nextNode
            (twoSatAndLeft (twoSatHasEdge system probe nextNode)
              (twoSatIsPathFrom system nextNode restPath (twoSatNegate probe)) hPath)

/-! ## The decision procedure -/

/-- An UNSAT witness: a variable with checked paths both ways between its two signs. -/
structure TwoSatContradictionWitness where
  contradictionVariable : Nat
  forwardPath : List TwoSatLiteral
  backwardPath : List TwoSatLiteral

/-- Search both reach closures of a variable for the two-way contradiction pair. -/
def twoSatFindContradictionPaths (system : List TwoSatClause) (variableIndex : Nat) :
    Option TwoSatContradictionWitness :=
  match twoSatFindEntry (twoSatNegativeLiteral variableIndex)
          (twoSatComputeReach system (twoSatPositiveLiteral variableIndex)),
        twoSatFindEntry (twoSatPositiveLiteral variableIndex)
          (twoSatComputeReach system (twoSatNegativeLiteral variableIndex)) with
  | Option.some forwardEntry, Option.some backwardEntry =>
      Option.some (TwoSatContradictionWitness.mk variableIndex
        forwardEntry.pathWitness backwardEntry.pathWitness)
  | Option.some _forwardEntry, Option.none => Option.none
  | Option.none, Option.some _backwardEntry => Option.none
  | Option.none, Option.none => Option.none

/-- Scan the variable census for a two-way variable. -/
def twoSatScanForTwoWay (system : List TwoSatClause) : List Nat → Option TwoSatContradictionWitness
  | [] => Option.none
  | variableIndex :: remainingVariables =>
      match twoSatFindContradictionPaths system variableIndex with
      | Option.some witness => Option.some witness
      | Option.none => twoSatScanForTwoWay system remainingVariables

/-- The decision unit clause `(l ∨ l)`, contributing exactly the edge `¬l → l`. -/
def twoSatUnitClauseFor (literal : TwoSatLiteral) : TwoSatClause :=
  TwoSatClause.mk literal literal

/-- Even–Itai–Shamir tie elimination: walk the variables, adding the decision unit clause
of the side whose forward reach is absent in the CURRENT augmented system. -/
def twoSatAugmentLoop : List Nat → List TwoSatClause → List TwoSatClause
  | [], currentSystem => currentSystem
  | variableIndex :: remainingVariables, currentSystem =>
      match twoSatComputedReaches currentSystem (twoSatPositiveLiteral variableIndex)
          (twoSatNegativeLiteral variableIndex) with
      | true =>
          twoSatAugmentLoop remainingVariables
            (twoSatUnitClauseFor (twoSatNegativeLiteral variableIndex) :: currentSystem)
      | false =>
          twoSatAugmentLoop remainingVariables
            (twoSatUnitClauseFor (twoSatPositiveLiteral variableIndex) :: currentSystem)

/-- The fully decision-augmented system. -/
def twoSatAugmentedSystem (system : List TwoSatClause) : List TwoSatClause :=
  twoSatAugmentLoop (twoSatCollectVariables system) system

/-- The selected true variables: those whose positive literal does NOT reach its negation
in the augmented system. -/
def twoSatSelectTrueVariables (augmentedSystem : List TwoSatClause) : List Nat → List Nat
  | [] => []
  | variableIndex :: remainingVariables =>
      match twoSatComputedReaches augmentedSystem (twoSatPositiveLiteral variableIndex)
          (twoSatNegativeLiteral variableIndex) with
      | true => twoSatSelectTrueVariables augmentedSystem remainingVariables
      | false => variableIndex :: twoSatSelectTrueVariables augmentedSystem remainingVariables

/-- The assignment induced by a true-variable list. -/
def twoSatEnvOfTrueList (trueVariables : List Nat) : Nat → Bool :=
  fun variableIndex => twoSatNatMember variableIndex trueVariables

/-- The verdict of the 2-SAT decision procedure. -/
inductive TwoSatVerdict where
  | isUnsatisfiable (contradictionVariable : Nat)
      (forwardPath : List TwoSatLiteral) (backwardPath : List TwoSatLiteral) : TwoSatVerdict
  | isSatisfiable (trueVariables : List Nat) : TwoSatVerdict

/-- **The 2-SAT decision procedure**: UNSAT with two path certificates, or SAT with the
selected true-variable list. -/
def twoSatDecide (system : List TwoSatClause) : TwoSatVerdict :=
  match twoSatScanForTwoWay system (twoSatCollectVariables system) with
  | Option.some witness =>
      TwoSatVerdict.isUnsatisfiable witness.contradictionVariable
        witness.forwardPath witness.backwardPath
  | Option.none =>
      TwoSatVerdict.isSatisfiable
        (twoSatSelectTrueVariables (twoSatAugmentedSystem system)
          (twoSatCollectVariables system))

/-! ## Theorem 1 — UNSAT soundness -/

/-- A produced contradiction witness names its variable. -/
theorem twoSatFindContradictionPathsVariable (system : List TwoSatClause) (variableIndex : Nat)
    (witness : TwoSatContradictionWitness)
    (hFind : twoSatFindContradictionPaths system variableIndex = Option.some witness) :
    witness.contradictionVariable = variableIndex := by
  cases hForwardFind : twoSatFindEntry (twoSatNegativeLiteral variableIndex)
      (twoSatComputeReach system (twoSatPositiveLiteral variableIndex)) with
  | none =>
      cases hBackwardFind : twoSatFindEntry (twoSatPositiveLiteral variableIndex)
          (twoSatComputeReach system (twoSatNegativeLiteral variableIndex)) with
      | none =>
          simp only [twoSatFindContradictionPaths, hForwardFind, hBackwardFind] at hFind
          exact nomatch hFind
      | some backwardEntry =>
          simp only [twoSatFindContradictionPaths, hForwardFind, hBackwardFind] at hFind
          exact nomatch hFind
  | some forwardEntry =>
      cases hBackwardFind : twoSatFindEntry (twoSatPositiveLiteral variableIndex)
          (twoSatComputeReach system (twoSatNegativeLiteral variableIndex)) with
      | none =>
          simp only [twoSatFindContradictionPaths, hForwardFind, hBackwardFind] at hFind
          exact nomatch hFind
      | some backwardEntry =>
          simp only [twoSatFindContradictionPaths, hForwardFind, hBackwardFind] at hFind
          have hWitnessEq : TwoSatContradictionWitness.mk variableIndex forwardEntry.pathWitness
              backwardEntry.pathWitness = witness := by
            injection hFind
          subst hWitnessEq
          exact rfl

/-- A produced contradiction witness carries CHECKED paths for its variable. -/
theorem twoSatFindContradictionPathsSound (system : List TwoSatClause) (variableIndex : Nat)
    (witness : TwoSatContradictionWitness)
    (hFind : twoSatFindContradictionPaths system variableIndex = Option.some witness) :
    twoSatIsPathFrom system (twoSatPositiveLiteral variableIndex) witness.forwardPath
      (twoSatNegativeLiteral variableIndex) = true ∧
    twoSatIsPathFrom system (twoSatNegativeLiteral variableIndex) witness.backwardPath
      (twoSatPositiveLiteral variableIndex) = true := by
  cases hForwardFind : twoSatFindEntry (twoSatNegativeLiteral variableIndex)
      (twoSatComputeReach system (twoSatPositiveLiteral variableIndex)) with
  | none =>
      cases hBackwardFind : twoSatFindEntry (twoSatPositiveLiteral variableIndex)
          (twoSatComputeReach system (twoSatNegativeLiteral variableIndex)) with
      | none =>
          simp only [twoSatFindContradictionPaths, hForwardFind, hBackwardFind] at hFind
          exact nomatch hFind
      | some backwardEntry =>
          simp only [twoSatFindContradictionPaths, hForwardFind, hBackwardFind] at hFind
          exact nomatch hFind
  | some forwardEntry =>
      cases hBackwardFind : twoSatFindEntry (twoSatPositiveLiteral variableIndex)
          (twoSatComputeReach system (twoSatNegativeLiteral variableIndex)) with
      | none =>
          simp only [twoSatFindContradictionPaths, hForwardFind, hBackwardFind] at hFind
          exact nomatch hFind
      | some backwardEntry =>
          simp only [twoSatFindContradictionPaths, hForwardFind, hBackwardFind] at hFind
          have hWitnessEq : TwoSatContradictionWitness.mk variableIndex forwardEntry.pathWitness
              backwardEntry.pathWitness = witness := by
            injection hFind
          subst hWitnessEq
          exact And.intro
            (twoSatFindEntrySound system (twoSatPositiveLiteral variableIndex)
              (twoSatNegativeLiteral variableIndex)
              (twoSatComputeReach system (twoSatPositiveLiteral variableIndex)) forwardEntry
              hForwardFind
              (twoSatComputeReachAllValid system (twoSatPositiveLiteral variableIndex)))
            (twoSatFindEntrySound system (twoSatNegativeLiteral variableIndex)
              (twoSatPositiveLiteral variableIndex)
              (twoSatComputeReach system (twoSatNegativeLiteral variableIndex)) backwardEntry
              hBackwardFind
              (twoSatComputeReachAllValid system (twoSatNegativeLiteral variableIndex)))

/-- A successful scan yields checked paths at the witness's variable. -/
theorem twoSatScanForTwoWaySound (system : List TwoSatClause) :
    (variables : List Nat) → (witness : TwoSatContradictionWitness) →
    twoSatScanForTwoWay system variables = Option.some witness →
    twoSatIsPathFrom system (twoSatPositiveLiteral witness.contradictionVariable)
      witness.forwardPath (twoSatNegativeLiteral witness.contradictionVariable) = true ∧
    twoSatIsPathFrom system (twoSatNegativeLiteral witness.contradictionVariable)
      witness.backwardPath (twoSatPositiveLiteral witness.contradictionVariable) = true
  | [], _witness, hScan => nomatch hScan
  | variableIndex :: remainingVariables, witness, hScan => by
      cases hFind : twoSatFindContradictionPaths system variableIndex with
      | some foundWitness =>
          have hWitnessEq : foundWitness = witness := by
            have hSome : Option.some foundWitness = Option.some witness := by
              simp only [twoSatScanForTwoWay, hFind] at hScan
              exact hScan
            injection hSome
          rw [← hWitnessEq,
            twoSatFindContradictionPathsVariable system variableIndex foundWitness hFind]
          exact twoSatFindContradictionPathsSound system variableIndex foundWitness hFind
      | none =>
          have hRest : twoSatScanForTwoWay system remainingVariables = Option.some witness := by
            simp only [twoSatScanForTwoWay, hFind] at hScan
            exact hScan
          exact twoSatScanForTwoWaySound system remainingVariables witness hRest

/-- **Theorem 1 — UNSAT soundness**: an unsatisfiable verdict refutes every assignment. -/
theorem twoSatDecideUnsatSound (system : List TwoSatClause) (contradictionVariable : Nat)
    (forwardPath backwardPath : List TwoSatLiteral) (assignment : Nat → Bool)
    (hDecide : twoSatDecide system =
      TwoSatVerdict.isUnsatisfiable contradictionVariable forwardPath backwardPath)
    (hSat : twoSatSatisfies assignment system = true) : False := by
  cases hScan : twoSatScanForTwoWay system (twoSatCollectVariables system) with
  | none =>
      simp only [twoSatDecide, hScan] at hDecide
      exact nomatch hDecide
  | some witness =>
      have hCerts := twoSatScanForTwoWaySound system (twoSatCollectVariables system) witness hScan
      exact twoSatContradictionPathsSound system assignment
        (twoSatPositiveLiteral witness.contradictionVariable) witness.forwardPath
        witness.backwardPath hCerts.left hCerts.right hSat

/-! ## Theorem 2 — SAT soundness (the APT hard half) -/

/-- A failed scan fails at every censused variable. -/
theorem twoSatScanForTwoWayNoneAt (system : List TwoSatClause) :
    (variables : List Nat) → (variableIndex : Nat) →
    twoSatScanForTwoWay system variables = Option.none →
    twoSatNatMember variableIndex variables = true →
    twoSatFindContradictionPaths system variableIndex = Option.none
  | [], _variableIndex, _hScan, hMember => Bool.noConfusion hMember
  | headVariable :: remainingVariables, variableIndex, hScan, hMember => by
      cases hFind : twoSatFindContradictionPaths system headVariable with
      | some foundWitness =>
          simp only [twoSatScanForTwoWay, hFind] at hScan
          exact nomatch hScan
      | none =>
          have hRest : twoSatScanForTwoWay system remainingVariables = Option.none := by
            simp only [twoSatScanForTwoWay, hFind] at hScan
            exact hScan
          cases twoSatOrCases (twoSatNatBeq variableIndex headVariable)
              (twoSatNatMember variableIndex remainingVariables) hMember with
          | inl hBeq =>
              rw [twoSatNatBeqImpliesEq variableIndex headVariable hBeq]
              exact hFind
          | inr hRestMember =>
              exact twoSatScanForTwoWayNoneAt system remainingVariables variableIndex hRest
                hRestMember

/-- Both genuine reaches at a censused variable force a contradiction witness. -/
theorem twoSatFindContradictionPathsNoneRefutes (system : List TwoSatClause) (variableIndex : Nat)
    (hVarCollected : twoSatNatMember variableIndex (twoSatCollectVariables system) = true)
    (hContraNone : twoSatFindContradictionPaths system variableIndex = Option.none)
    (hForward : TwoSatReaches system (twoSatPositiveLiteral variableIndex)
      (twoSatNegativeLiteral variableIndex))
    (hBackward : TwoSatReaches system (twoSatNegativeLiteral variableIndex)
      (twoSatPositiveLiteral variableIndex)) : False := by
  have hForwardComputed : twoSatComputedReaches system (twoSatPositiveLiteral variableIndex)
      (twoSatNegativeLiteral variableIndex) = true :=
    twoSatComputedReachesComplete system (twoSatPositiveLiteral variableIndex)
      (twoSatNegativeLiteral variableIndex)
      (twoSatVarInUniverse system variableIndex true hVarCollected) hForward
  have hBackwardComputed : twoSatComputedReaches system (twoSatNegativeLiteral variableIndex)
      (twoSatPositiveLiteral variableIndex) = true :=
    twoSatComputedReachesComplete system (twoSatNegativeLiteral variableIndex)
      (twoSatPositiveLiteral variableIndex)
      (twoSatVarInUniverse system variableIndex false hVarCollected) hBackward
  cases hForwardFind : twoSatFindEntry (twoSatNegativeLiteral variableIndex)
      (twoSatComputeReach system (twoSatPositiveLiteral variableIndex)) with
  | none =>
      exact twoSatFindEntryOfMemberAbsurd (twoSatNegativeLiteral variableIndex)
        (twoSatComputeReach system (twoSatPositiveLiteral variableIndex)) hForwardComputed
        hForwardFind
  | some forwardEntry =>
      cases hBackwardFind : twoSatFindEntry (twoSatPositiveLiteral variableIndex)
          (twoSatComputeReach system (twoSatNegativeLiteral variableIndex)) with
      | none =>
          exact twoSatFindEntryOfMemberAbsurd (twoSatPositiveLiteral variableIndex)
            (twoSatComputeReach system (twoSatNegativeLiteral variableIndex)) hBackwardComputed
            hBackwardFind
      | some backwardEntry =>
          simp only [twoSatFindContradictionPaths, hForwardFind, hBackwardFind] at hContraNone
          exact nomatch hContraNone

/-- The no-mutual-reach invariant: no literal reaches its negation both ways. -/
def TwoSatHasNoMutualPair (system : List TwoSatClause) : Prop :=
  ∀ probe : TwoSatLiteral,
    TwoSatReaches system probe (twoSatNegate probe) →
    TwoSatReaches system (twoSatNegate probe) probe → False

/-- A failed scan certifies the no-mutual-reach invariant. -/
theorem twoSatScanNoneNoMutual (system : List TwoSatClause)
    (hScanNone : twoSatScanForTwoWay system (twoSatCollectVariables system) = Option.none) :
    TwoSatHasNoMutualPair system := by
  intro probe hForward hBackward
  cases probe with
  | mk variableIndex sign =>
      have hVarCollected : twoSatNatMember variableIndex (twoSatCollectVariables system) = true :=
        twoSatReachesSelfNegVarCollected system (TwoSatLiteral.mk variableIndex sign) hForward
      have hContraNone := twoSatScanForTwoWayNoneAt system (twoSatCollectVariables system)
        variableIndex hScanNone hVarCollected
      cases sign with
      | true =>
          exact twoSatFindContradictionPathsNoneRefutes system variableIndex hVarCollected
            hContraNone hForward hBackward
      | false =>
          exact twoSatFindContradictionPathsNoneRefutes system variableIndex hVarCollected
            hContraNone hBackward hForward

/-- **Augmentation decomposition**: a path through the decision-augmented system either
lives in the old system, or factors through `¬chosen` and `chosen` in the old system. -/
theorem twoSatUnitAugmentDecompose (system : List TwoSatClause) (chosen : TwoSatLiteral) :
    (path : List TwoSatLiteral) → (source target : TwoSatLiteral) →
    twoSatIsPathFrom (twoSatUnitClauseFor chosen :: system) source path target = true →
    TwoSatReaches system source target ∨
      (TwoSatReaches system source (twoSatNegate chosen) ∧ TwoSatReaches system chosen target)
  | [], _source, _target, hPath => Or.inl (Exists.intro [] hPath)
  | nextNode :: restPath, source, target, hPath => by
      have hEdge : twoSatHasEdge (twoSatUnitClauseFor chosen :: system) source nextNode = true :=
        twoSatAndLeft (twoSatHasEdge (twoSatUnitClauseFor chosen :: system) source nextNode)
          (twoSatIsPathFrom (twoSatUnitClauseFor chosen :: system) nextNode restPath target) hPath
      have hRest : twoSatIsPathFrom (twoSatUnitClauseFor chosen :: system) nextNode restPath
          target = true :=
        twoSatAndRight (twoSatHasEdge (twoSatUnitClauseFor chosen :: system) source nextNode)
          (twoSatIsPathFrom (twoSatUnitClauseFor chosen :: system) nextNode restPath target) hPath
      have hRecursive := twoSatUnitAugmentDecompose system chosen restPath nextNode target hRest
      cases twoSatOrCases (twoSatClauseHasEdge (twoSatUnitClauseFor chosen) source nextNode)
          (twoSatHasEdge system source nextNode) hEdge with
      | inl hUnitEdge =>
          have hEndpoints : source = twoSatNegate chosen ∧ nextNode = chosen := by
            cases twoSatClauseHasEdgeCases (twoSatUnitClauseFor chosen) source nextNode
                hUnitEdge with
            | inl hOrientation => exact hOrientation
            | inr hOrientation => exact hOrientation
          cases hRecursive with
          | inl hDirect =>
              refine Or.inr (And.intro ?_ ?_)
              · rw [hEndpoints.left]
                exact twoSatReachesRefl system (twoSatNegate chosen)
              · rw [← hEndpoints.right]
                exact hDirect
          | inr hFactored =>
              refine Or.inr (And.intro ?_ ?_)
              · rw [hEndpoints.left]
                exact twoSatReachesRefl system (twoSatNegate chosen)
              · exact hFactored.right
      | inr hSystemEdge =>
          cases hRecursive with
          | inl hDirect =>
              exact Or.inl (twoSatReachesTrans system source nextNode target
                (twoSatReachesOfEdge system source nextNode hSystemEdge) hDirect)
          | inr hFactored =>
              exact Or.inr (And.intro
                (twoSatReachesTrans system source nextNode (twoSatNegate chosen)
                  (twoSatReachesOfEdge system source nextNode hSystemEdge) hFactored.left)
                hFactored.right)

/-- **Decision preservation**: adding the unit clause of a safe chosen literal preserves
the no-mutual-reach invariant. -/
theorem twoSatDecisionPreservesNoMutual (system : List TwoSatClause) (chosen : TwoSatLiteral)
    (hNoMutual : TwoSatHasNoMutualPair system)
    (hChosenSafe : TwoSatReaches system chosen (twoSatNegate chosen) → False) :
    TwoSatHasNoMutualPair (twoSatUnitClauseFor chosen :: system) := by
  intro probe hForward hBackward
  cases hForward with
  | intro forwardPath hForwardPath =>
      cases hBackward with
      | intro backwardPath hBackwardPath =>
          cases twoSatUnitAugmentDecompose system chosen forwardPath probe (twoSatNegate probe)
              hForwardPath with
          | inl hForwardOld =>
              cases twoSatUnitAugmentDecompose system chosen backwardPath (twoSatNegate probe)
                  probe hBackwardPath with
              | inl hBackwardOld => exact hNoMutual probe hForwardOld hBackwardOld
              | inr hBackwardFactored =>
                  exact hChosenSafe (twoSatReachesTrans system chosen probe (twoSatNegate chosen)
                    hBackwardFactored.right
                    (twoSatReachesTrans system probe (twoSatNegate probe) (twoSatNegate chosen)
                      hForwardOld hBackwardFactored.left))
          | inr hForwardFactored =>
              cases twoSatUnitAugmentDecompose system chosen backwardPath (twoSatNegate probe)
                  probe hBackwardPath with
              | inl hBackwardOld =>
                  exact hChosenSafe (twoSatReachesTrans system chosen (twoSatNegate probe)
                    (twoSatNegate chosen) hForwardFactored.right
                    (twoSatReachesTrans system (twoSatNegate probe) probe (twoSatNegate chosen)
                      hBackwardOld hForwardFactored.left))
              | inr hBackwardFactored =>
                  exact hChosenSafe (twoSatReachesTrans system chosen probe (twoSatNegate chosen)
                    hBackwardFactored.right hForwardFactored.left)

/-- The augment loop preserves the no-mutual-reach invariant at every decision. -/
theorem twoSatAugmentLoopPreservesNoMutual :
    (pendingVariables : List Nat) → (system : List TwoSatClause) →
    TwoSatHasNoMutualPair system →
    TwoSatHasNoMutualPair (twoSatAugmentLoop pendingVariables system)
  | [], _system, hNoMutual => hNoMutual
  | variableIndex :: remainingVariables, system, hNoMutual => by
      cases hReach : twoSatComputedReaches system (twoSatPositiveLiteral variableIndex)
          (twoSatNegativeLiteral variableIndex) with
      | true =>
          have hChosenSafe : TwoSatReaches system (twoSatNegativeLiteral variableIndex)
              (twoSatNegate (twoSatNegativeLiteral variableIndex)) → False := by
            intro hSem
            exact hNoMutual (twoSatPositiveLiteral variableIndex)
              (twoSatComputedReachesSound system (twoSatPositiveLiteral variableIndex)
                (twoSatNegativeLiteral variableIndex) hReach)
              hSem
          simp only [twoSatAugmentLoop]
          rw [hReach]
          exact twoSatAugmentLoopPreservesNoMutual remainingVariables
            (twoSatUnitClauseFor (twoSatNegativeLiteral variableIndex) :: system)
            (twoSatDecisionPreservesNoMutual system (twoSatNegativeLiteral variableIndex)
              hNoMutual hChosenSafe)
      | false =>
          have hChosenSafe : TwoSatReaches system (twoSatPositiveLiteral variableIndex)
              (twoSatNegate (twoSatPositiveLiteral variableIndex)) → False := by
            intro hSem
            cases hVarMember : twoSatNatMember variableIndex (twoSatCollectVariables system) with
            | true =>
                have hComputed := twoSatComputedReachesComplete system
                  (twoSatPositiveLiteral variableIndex) (twoSatNegativeLiteral variableIndex)
                  (twoSatVarInUniverse system variableIndex true hVarMember) hSem
                exact Bool.noConfusion (hReach.symm.trans hComputed)
            | false =>
                have hCollected : twoSatNatMember variableIndex
                    (twoSatCollectVariables system) = true :=
                  twoSatReachesSelfNegVarCollected system
                    (twoSatPositiveLiteral variableIndex) hSem
                exact Bool.noConfusion (hVarMember.symm.trans hCollected)
          simp only [twoSatAugmentLoop]
          rw [hReach]
          exact twoSatAugmentLoopPreservesNoMutual remainingVariables
            (twoSatUnitClauseFor (twoSatPositiveLiteral variableIndex) :: system)
            (twoSatDecisionPreservesNoMutual system (twoSatPositiveLiteral variableIndex)
              hNoMutual hChosenSafe)

/-- Clause membership persists through the augment loop. -/
theorem twoSatClauseMemberAugmentMono :
    (pendingVariables : List Nat) → (system : List TwoSatClause) → (clause : TwoSatClause) →
    twoSatClauseMember clause system = true →
    twoSatClauseMember clause (twoSatAugmentLoop pendingVariables system) = true
  | [], _system, _clause, hMember => hMember
  | variableIndex :: remainingVariables, system, clause, hMember => by
      cases hReach : twoSatComputedReaches system (twoSatPositiveLiteral variableIndex)
          (twoSatNegativeLiteral variableIndex) with
      | true =>
          simp only [twoSatAugmentLoop]
          rw [hReach]
          exact twoSatClauseMemberAugmentMono remainingVariables
            (twoSatUnitClauseFor (twoSatNegativeLiteral variableIndex) :: system) clause
            (twoSatClauseMemberConsMono
              (twoSatUnitClauseFor (twoSatNegativeLiteral variableIndex)) system clause hMember)
      | false =>
          simp only [twoSatAugmentLoop]
          rw [hReach]
          exact twoSatClauseMemberAugmentMono remainingVariables
            (twoSatUnitClauseFor (twoSatPositiveLiteral variableIndex) :: system) clause
            (twoSatClauseMemberConsMono
              (twoSatUnitClauseFor (twoSatPositiveLiteral variableIndex)) system clause hMember)

/-- Census membership persists through the augment loop. -/
theorem twoSatCollectVarsAugmentMono :
    (pendingVariables : List Nat) → (system : List TwoSatClause) → (variableIndex : Nat) →
    twoSatNatMember variableIndex (twoSatCollectVariables system) = true →
    twoSatNatMember variableIndex
      (twoSatCollectVariables (twoSatAugmentLoop pendingVariables system)) = true
  | [], _system, _variableIndex, hMember => hMember
  | headVariable :: remainingVariables, system, variableIndex, hMember => by
      cases hReach : twoSatComputedReaches system (twoSatPositiveLiteral headVariable)
          (twoSatNegativeLiteral headVariable) with
      | true =>
          simp only [twoSatAugmentLoop]
          rw [hReach]
          exact twoSatCollectVarsAugmentMono remainingVariables
            (twoSatUnitClauseFor (twoSatNegativeLiteral headVariable) :: system) variableIndex
            (twoSatCollectVarsConsMono
              (twoSatUnitClauseFor (twoSatNegativeLiteral headVariable)) system variableIndex
              hMember)
      | false =>
          simp only [twoSatAugmentLoop]
          rw [hReach]
          exact twoSatCollectVarsAugmentMono remainingVariables
            (twoSatUnitClauseFor (twoSatPositiveLiteral headVariable) :: system) variableIndex
            (twoSatCollectVarsConsMono
              (twoSatUnitClauseFor (twoSatPositiveLiteral headVariable)) system variableIndex
              hMember)

/-- Every pending variable receives a decision unit clause in the augment loop. -/
theorem twoSatAugmentLoopDecides :
    (pendingVariables : List Nat) → (system : List TwoSatClause) → (variableIndex : Nat) →
    twoSatNatMember variableIndex pendingVariables = true →
    twoSatClauseMember (twoSatUnitClauseFor (twoSatPositiveLiteral variableIndex))
      (twoSatAugmentLoop pendingVariables system) = true ∨
    twoSatClauseMember (twoSatUnitClauseFor (twoSatNegativeLiteral variableIndex))
      (twoSatAugmentLoop pendingVariables system) = true
  | [], _system, _variableIndex, hMember => Bool.noConfusion hMember
  | headVariable :: remainingVariables, system, variableIndex, hMember => by
      cases twoSatOrCases (twoSatNatBeq variableIndex headVariable)
          (twoSatNatMember variableIndex remainingVariables) hMember with
      | inl hBeq =>
          have hVarEq : variableIndex = headVariable :=
            twoSatNatBeqImpliesEq variableIndex headVariable hBeq
          subst hVarEq
          cases hReach : twoSatComputedReaches system (twoSatPositiveLiteral variableIndex)
              (twoSatNegativeLiteral variableIndex) with
          | true =>
              apply Or.inr
              simp only [twoSatAugmentLoop]
              rw [hReach]
              exact twoSatClauseMemberAugmentMono remainingVariables
                (twoSatUnitClauseFor (twoSatNegativeLiteral variableIndex) :: system)
                (twoSatUnitClauseFor (twoSatNegativeLiteral variableIndex))
                (twoSatOrIntroLeft
                  (twoSatClauseBeq (twoSatUnitClauseFor (twoSatNegativeLiteral variableIndex))
                    (twoSatUnitClauseFor (twoSatNegativeLiteral variableIndex)))
                  (twoSatClauseMember
                    (twoSatUnitClauseFor (twoSatNegativeLiteral variableIndex)) system)
                  (twoSatClauseBeqRefl (twoSatUnitClauseFor (twoSatNegativeLiteral variableIndex))))
          | false =>
              apply Or.inl
              simp only [twoSatAugmentLoop]
              rw [hReach]
              exact twoSatClauseMemberAugmentMono remainingVariables
                (twoSatUnitClauseFor (twoSatPositiveLiteral variableIndex) :: system)
                (twoSatUnitClauseFor (twoSatPositiveLiteral variableIndex))
                (twoSatOrIntroLeft
                  (twoSatClauseBeq (twoSatUnitClauseFor (twoSatPositiveLiteral variableIndex))
                    (twoSatUnitClauseFor (twoSatPositiveLiteral variableIndex)))
                  (twoSatClauseMember
                    (twoSatUnitClauseFor (twoSatPositiveLiteral variableIndex)) system)
                  (twoSatClauseBeqRefl (twoSatUnitClauseFor (twoSatPositiveLiteral variableIndex))))
      | inr hRestMember =>
          cases hReach : twoSatComputedReaches system (twoSatPositiveLiteral headVariable)
              (twoSatNegativeLiteral headVariable) with
          | true =>
              simp only [twoSatAugmentLoop]
              rw [hReach]
              exact twoSatAugmentLoopDecides remainingVariables
                (twoSatUnitClauseFor (twoSatNegativeLiteral headVariable) :: system)
                variableIndex hRestMember
          | false =>
              simp only [twoSatAugmentLoop]
              rw [hReach]
              exact twoSatAugmentLoopDecides remainingVariables
                (twoSatUnitClauseFor (twoSatPositiveLiteral headVariable) :: system)
                variableIndex hRestMember

/-- Selected variables have no computed forward reach. -/
theorem twoSatSelectMemberSound (augmentedSystem : List TwoSatClause) :
    (variables : List Nat) → (variableIndex : Nat) →
    twoSatNatMember variableIndex (twoSatSelectTrueVariables augmentedSystem variables) = true →
    twoSatComputedReaches augmentedSystem (twoSatPositiveLiteral variableIndex)
      (twoSatNegativeLiteral variableIndex) = false
  | [], _variableIndex, hMember => Bool.noConfusion hMember
  | headVariable :: remainingVariables, variableIndex, hMember => by
      cases hReach : twoSatComputedReaches augmentedSystem (twoSatPositiveLiteral headVariable)
          (twoSatNegativeLiteral headVariable) with
      | true =>
          have hRest : twoSatNatMember variableIndex
              (twoSatSelectTrueVariables augmentedSystem remainingVariables) = true := by
            simp only [twoSatSelectTrueVariables, hReach] at hMember
            exact hMember
          exact twoSatSelectMemberSound augmentedSystem remainingVariables variableIndex hRest
      | false =>
          have hConsMember : twoSatNatMember variableIndex
              (headVariable :: twoSatSelectTrueVariables augmentedSystem remainingVariables) =
              true := by
            simp only [twoSatSelectTrueVariables, hReach] at hMember
            exact hMember
          cases twoSatOrCases (twoSatNatBeq variableIndex headVariable)
              (twoSatNatMember variableIndex
                (twoSatSelectTrueVariables augmentedSystem remainingVariables)) hConsMember with
          | inl hBeq =>
              rw [twoSatNatBeqImpliesEq variableIndex headVariable hBeq]
              exact hReach
          | inr hRest =>
              exact twoSatSelectMemberSound augmentedSystem remainingVariables variableIndex hRest

/-- Censused variables without computed forward reach are selected. -/
theorem twoSatSelectMemberComplete (augmentedSystem : List TwoSatClause) :
    (variables : List Nat) → (variableIndex : Nat) →
    twoSatNatMember variableIndex variables = true →
    twoSatComputedReaches augmentedSystem (twoSatPositiveLiteral variableIndex)
      (twoSatNegativeLiteral variableIndex) = false →
    twoSatNatMember variableIndex (twoSatSelectTrueVariables augmentedSystem variables) = true
  | [], _variableIndex, hMember, _hReachFalse => Bool.noConfusion hMember
  | headVariable :: remainingVariables, variableIndex, hMember, hReachFalse => by
      cases twoSatOrCases (twoSatNatBeq variableIndex headVariable)
          (twoSatNatMember variableIndex remainingVariables) hMember with
      | inl hBeq =>
          have hVarEq : variableIndex = headVariable :=
            twoSatNatBeqImpliesEq variableIndex headVariable hBeq
          subst hVarEq
          simp only [twoSatSelectTrueVariables, hReachFalse]
          exact twoSatOrIntroLeft (twoSatNatBeq variableIndex variableIndex)
            (twoSatNatMember variableIndex
              (twoSatSelectTrueVariables augmentedSystem remainingVariables))
            (twoSatNatBeqRefl variableIndex)
      | inr hRestMember =>
          cases hReach : twoSatComputedReaches augmentedSystem
              (twoSatPositiveLiteral headVariable) (twoSatNegativeLiteral headVariable) with
          | true =>
              simp only [twoSatSelectTrueVariables, hReach]
              exact twoSatSelectMemberComplete augmentedSystem remainingVariables variableIndex
                hRestMember hReachFalse
          | false =>
              simp only [twoSatSelectTrueVariables, hReach]
              exact twoSatOrIntroRight (twoSatNatBeq variableIndex headVariable)
                (twoSatNatMember variableIndex
                  (twoSatSelectTrueVariables augmentedSystem remainingVariables))
                (twoSatSelectMemberComplete augmentedSystem remainingVariables variableIndex
                  hRestMember hReachFalse)

/-- The unit clause `(l ∨ l)` contributes exactly the decision edge `¬l → l`. -/
theorem twoSatUnitClauseEdge (literal : TwoSatLiteral) :
    twoSatClauseHasEdge (twoSatUnitClauseFor literal) (twoSatNegate literal) literal = true :=
  twoSatOrIntroLeft
    (twoSatLiteralBeq (twoSatNegate literal)
        (twoSatNegate (twoSatUnitClauseFor literal).firstLiteral) &&
      twoSatLiteralBeq literal (twoSatUnitClauseFor literal).secondLiteral)
    (twoSatLiteralBeq (twoSatNegate literal)
        (twoSatNegate (twoSatUnitClauseFor literal).secondLiteral) &&
      twoSatLiteralBeq literal (twoSatUnitClauseFor literal).firstLiteral)
    (twoSatAndIntro
      (twoSatLiteralBeq (twoSatNegate literal)
        (twoSatNegate (twoSatUnitClauseFor literal).firstLiteral))
      (twoSatLiteralBeq literal (twoSatUnitClauseFor literal).secondLiteral)
      (twoSatLiteralBeqRefl (twoSatNegate literal))
      (twoSatLiteralBeqRefl literal))

/-- **The reach-forcing valuation lemma**: on the augmented system, a censused literal
evaluated FALSE by the selected assignment genuinely reaches its negation. -/
theorem twoSatValLemma (system : List TwoSatClause) (literal : TwoSatLiteral)
    (hVarCollected : twoSatNatMember literal.variableIndex (twoSatCollectVariables system) = true)
    (hEval : twoSatEvalLiteral
      (twoSatEnvOfTrueList (twoSatSelectTrueVariables (twoSatAugmentedSystem system)
        (twoSatCollectVariables system)))
      literal = false) :
    TwoSatReaches (twoSatAugmentedSystem system) literal (twoSatNegate literal) := by
  cases literal with
  | mk variableIndex sign =>
      cases sign with
      | true =>
          have hMemberFalse : twoSatNatMember variableIndex
              (twoSatSelectTrueVariables (twoSatAugmentedSystem system)
                (twoSatCollectVariables system)) = false := hEval
          cases hReach : twoSatComputedReaches (twoSatAugmentedSystem system)
              (twoSatPositiveLiteral variableIndex) (twoSatNegativeLiteral variableIndex) with
          | true =>
              exact twoSatComputedReachesSound (twoSatAugmentedSystem system)
                (twoSatPositiveLiteral variableIndex) (twoSatNegativeLiteral variableIndex)
                hReach
          | false =>
              have hSelected := twoSatSelectMemberComplete (twoSatAugmentedSystem system)
                (twoSatCollectVariables system) variableIndex hVarCollected hReach
              exact Bool.noConfusion (hMemberFalse.symm.trans hSelected)
      | false =>
          have hMemberTrue : twoSatNatMember variableIndex
              (twoSatSelectTrueVariables (twoSatAugmentedSystem system)
                (twoSatCollectVariables system)) = true :=
            twoSatNotEqFalse (twoSatNatMember variableIndex
              (twoSatSelectTrueVariables (twoSatAugmentedSystem system)
                (twoSatCollectVariables system))) hEval
          have hReachFalse : twoSatComputedReaches (twoSatAugmentedSystem system)
              (twoSatPositiveLiteral variableIndex) (twoSatNegativeLiteral variableIndex) =
              false :=
            twoSatSelectMemberSound (twoSatAugmentedSystem system)
              (twoSatCollectVariables system) variableIndex hMemberTrue
          cases twoSatAugmentLoopDecides (twoSatCollectVariables system) system variableIndex
              hVarCollected with
          | inl hPositiveDecision =>
              exact twoSatReachesOfEdge (twoSatAugmentedSystem system)
                (twoSatNegativeLiteral variableIndex) (twoSatPositiveLiteral variableIndex)
                (twoSatHasEdgeOfClauseMember (twoSatAugmentedSystem system)
                  (twoSatUnitClauseFor (twoSatPositiveLiteral variableIndex))
                  (twoSatNegativeLiteral variableIndex) (twoSatPositiveLiteral variableIndex)
                  hPositiveDecision
                  (twoSatUnitClauseEdge (twoSatPositiveLiteral variableIndex)))
          | inr hNegativeDecision =>
              have hSemantic : TwoSatReaches (twoSatAugmentedSystem system)
                  (twoSatPositiveLiteral variableIndex) (twoSatNegativeLiteral variableIndex) :=
                twoSatReachesOfEdge (twoSatAugmentedSystem system)
                  (twoSatPositiveLiteral variableIndex) (twoSatNegativeLiteral variableIndex)
                  (twoSatHasEdgeOfClauseMember (twoSatAugmentedSystem system)
                    (twoSatUnitClauseFor (twoSatNegativeLiteral variableIndex))
                    (twoSatPositiveLiteral variableIndex) (twoSatNegativeLiteral variableIndex)
                    hNegativeDecision
                    (twoSatUnitClauseEdge (twoSatNegativeLiteral variableIndex)))
              have hComputed := twoSatComputedReachesComplete (twoSatAugmentedSystem system)
                (twoSatPositiveLiteral variableIndex) (twoSatNegativeLiteral variableIndex)
                (twoSatVarInUniverse (twoSatAugmentedSystem system) variableIndex true
                  (twoSatCollectVarsAugmentMono (twoSatCollectVariables system) system
                    variableIndex hVarCollected))
                hSemantic
              exact Bool.noConfusion (hReachFalse.symm.trans hComputed)

/-- **Pointwise clause satisfaction** under the selected assignment, given a failed scan:
a falsified clause would assemble a mutual-reach pair in the augmented system. -/
theorem twoSatClauseSatisfiedPointwise (system : List TwoSatClause) (clause : TwoSatClause)
    (hScanNone : twoSatScanForTwoWay system (twoSatCollectVariables system) = Option.none)
    (hClauseMember : twoSatClauseMember clause system = true) :
    twoSatEvalClause (twoSatEnvOfTrueList (twoSatSelectTrueVariables
      (twoSatAugmentedSystem system) (twoSatCollectVariables system))) clause = true := by
  cases hEval : twoSatEvalClause (twoSatEnvOfTrueList (twoSatSelectTrueVariables
      (twoSatAugmentedSystem system) (twoSatCollectVariables system))) clause with
  | true => rfl
  | false =>
      have hSplit := twoSatOrFalseSplit
        (twoSatEvalLiteral (twoSatEnvOfTrueList (twoSatSelectTrueVariables
          (twoSatAugmentedSystem system) (twoSatCollectVariables system))) clause.firstLiteral)
        (twoSatEvalLiteral (twoSatEnvOfTrueList (twoSatSelectTrueVariables
          (twoSatAugmentedSystem system) (twoSatCollectVariables system))) clause.secondLiteral)
        hEval
      have hVars := twoSatClauseVarsCollected system clause hClauseMember
      have hReachFirst : TwoSatReaches (twoSatAugmentedSystem system) clause.firstLiteral
          (twoSatNegate clause.firstLiteral) :=
        twoSatValLemma system clause.firstLiteral hVars.left hSplit.left
      have hReachSecond : TwoSatReaches (twoSatAugmentedSystem system) clause.secondLiteral
          (twoSatNegate clause.secondLiteral) :=
        twoSatValLemma system clause.secondLiteral hVars.right hSplit.right
      have hClauseInAug : twoSatClauseMember clause (twoSatAugmentedSystem system) = true :=
        twoSatClauseMemberAugmentMono (twoSatCollectVariables system) system clause hClauseMember
      have hEdgeFirst : twoSatHasEdge (twoSatAugmentedSystem system)
          (twoSatNegate clause.firstLiteral) clause.secondLiteral = true :=
        twoSatHasEdgeOfClauseMember (twoSatAugmentedSystem system) clause
          (twoSatNegate clause.firstLiteral) clause.secondLiteral hClauseInAug
          (twoSatOrIntroLeft
            (twoSatLiteralBeq (twoSatNegate clause.firstLiteral)
                (twoSatNegate clause.firstLiteral) &&
              twoSatLiteralBeq clause.secondLiteral clause.secondLiteral)
            (twoSatLiteralBeq (twoSatNegate clause.firstLiteral)
                (twoSatNegate clause.secondLiteral) &&
              twoSatLiteralBeq clause.secondLiteral clause.firstLiteral)
            (twoSatAndIntro
              (twoSatLiteralBeq (twoSatNegate clause.firstLiteral)
                (twoSatNegate clause.firstLiteral))
              (twoSatLiteralBeq clause.secondLiteral clause.secondLiteral)
              (twoSatLiteralBeqRefl (twoSatNegate clause.firstLiteral))
              (twoSatLiteralBeqRefl clause.secondLiteral)))
      have hEdgeSecond : twoSatHasEdge (twoSatAugmentedSystem system)
          (twoSatNegate clause.secondLiteral) clause.firstLiteral = true :=
        twoSatHasEdgeOfClauseMember (twoSatAugmentedSystem system) clause
          (twoSatNegate clause.secondLiteral) clause.firstLiteral hClauseInAug
          (twoSatOrIntroRight
            (twoSatLiteralBeq (twoSatNegate clause.secondLiteral)
                (twoSatNegate clause.firstLiteral) &&
              twoSatLiteralBeq clause.firstLiteral clause.secondLiteral)
            (twoSatLiteralBeq (twoSatNegate clause.secondLiteral)
                (twoSatNegate clause.secondLiteral) &&
              twoSatLiteralBeq clause.firstLiteral clause.firstLiteral)
            (twoSatAndIntro
              (twoSatLiteralBeq (twoSatNegate clause.secondLiteral)
                (twoSatNegate clause.secondLiteral))
              (twoSatLiteralBeq clause.firstLiteral clause.firstLiteral)
              (twoSatLiteralBeqRefl (twoSatNegate clause.secondLiteral))
              (twoSatLiteralBeqRefl clause.firstLiteral)))
      have hBackward : TwoSatReaches (twoSatAugmentedSystem system)
          (twoSatNegate clause.firstLiteral) clause.firstLiteral :=
        twoSatReachesTrans (twoSatAugmentedSystem system) (twoSatNegate clause.firstLiteral)
          clause.secondLiteral clause.firstLiteral
          (twoSatReachesOfEdge (twoSatAugmentedSystem system) (twoSatNegate clause.firstLiteral)
            clause.secondLiteral hEdgeFirst)
          (twoSatReachesTrans (twoSatAugmentedSystem system) clause.secondLiteral
            (twoSatNegate clause.secondLiteral) clause.firstLiteral
            hReachSecond
            (twoSatReachesOfEdge (twoSatAugmentedSystem system)
              (twoSatNegate clause.secondLiteral) clause.firstLiteral hEdgeSecond))
      have hNoMutualAug : TwoSatHasNoMutualPair (twoSatAugmentedSystem system) :=
        twoSatAugmentLoopPreservesNoMutual (twoSatCollectVariables system) system
          (twoSatScanNoneNoMutual system hScanNone)
      exact False.elim (hNoMutualAug clause.firstLiteral hReachFirst hBackward)

/-- Pointwise clause truth gives whole-system satisfaction. -/
theorem twoSatSatisfiesOfPointwise (assignment : Nat → Bool) :
    (system : List TwoSatClause) →
    (∀ clause : TwoSatClause, twoSatClauseMember clause system = true →
      twoSatEvalClause assignment clause = true) →
    twoSatSatisfies assignment system = true
  | [], _hPointwise => rfl
  | clause :: rest, hPointwise =>
      twoSatAndIntro (twoSatEvalClause assignment clause) (twoSatSatisfies assignment rest)
        (hPointwise clause (twoSatOrIntroLeft (twoSatClauseBeq clause clause)
          (twoSatClauseMember clause rest) (twoSatClauseBeqRefl clause)))
        (twoSatSatisfiesOfPointwise assignment rest
          (fun innerClause hInnerMember => hPointwise innerClause
            (twoSatOrIntroRight (twoSatClauseBeq innerClause clause)
              (twoSatClauseMember innerClause rest) hInnerMember)))

/-- **Theorem 2 — SAT soundness (the APT hard half)**: a satisfiable verdict's assignment
satisfies every clause. -/
theorem twoSatDecideSatSound (system : List TwoSatClause) (trueVariables : List Nat)
    (hDecide : twoSatDecide system = TwoSatVerdict.isSatisfiable trueVariables) :
    twoSatSatisfies (twoSatEnvOfTrueList trueVariables) system = true := by
  cases hScan : twoSatScanForTwoWay system (twoSatCollectVariables system) with
  | some witness =>
      simp only [twoSatDecide, hScan] at hDecide
      exact nomatch hDecide
  | none =>
      have hVars : twoSatSelectTrueVariables (twoSatAugmentedSystem system)
          (twoSatCollectVariables system) = trueVariables := by
        simp only [twoSatDecide, hScan] at hDecide
        injection hDecide
      rw [← hVars]
      exact twoSatSatisfiesOfPointwise (twoSatEnvOfTrueList (twoSatSelectTrueVariables
          (twoSatAugmentedSystem system) (twoSatCollectVariables system))) system
        (fun clause hMember => twoSatClauseSatisfiedPointwise system clause hScan hMember)

/-! ## Verdict inspection, genuineness smokes, marker -/

/-- Is the verdict satisfiable? -/
def twoSatVerdictIsSatisfiable : TwoSatVerdict → Bool
  | TwoSatVerdict.isUnsatisfiable _contradictionVariable _forwardPath _backwardPath => false
  | TwoSatVerdict.isSatisfiable _trueVariables => true

/-- The verdict's true-variable list (empty for UNSAT verdicts). -/
def twoSatVerdictTrueVariables : TwoSatVerdict → List Nat
  | TwoSatVerdict.isUnsatisfiable _contradictionVariable _forwardPath _backwardPath => []
  | TwoSatVerdict.isSatisfiable trueVariables => trueVariables

/-- Check a verdict against a system: SAT verdicts by evaluating the assignment, UNSAT
verdicts by checking BOTH path certificates. -/
def twoSatVerdictWitnessChecks (system : List TwoSatClause) : TwoSatVerdict → Bool
  | TwoSatVerdict.isUnsatisfiable contradictionVariable forwardPath backwardPath =>
      twoSatIsPathFrom system (twoSatPositiveLiteral contradictionVariable) forwardPath
        (twoSatNegativeLiteral contradictionVariable) &&
      twoSatIsPathFrom system (twoSatNegativeLiteral contradictionVariable) backwardPath
        (twoSatPositiveLiteral contradictionVariable)
  | TwoSatVerdict.isSatisfiable trueVariables =>
      twoSatSatisfies (twoSatEnvOfTrueList trueVariables) system

/-- Satisfiable smoke system: `(x0)`, `x0 → x1`, `x1 → x2` (as clauses). -/
def twoSatSmokeChainSystem : List TwoSatClause :=
  [TwoSatClause.mk (TwoSatLiteral.mk 0 true) (TwoSatLiteral.mk 0 true),
   TwoSatClause.mk (TwoSatLiteral.mk 0 false) (TwoSatLiteral.mk 1 true),
   TwoSatClause.mk (TwoSatLiteral.mk 1 false) (TwoSatLiteral.mk 2 true)]

/-- The classic four-clause contradiction on two variables (UNSAT). -/
def twoSatSmokeContradictionSystem : List TwoSatClause :=
  [TwoSatClause.mk (TwoSatLiteral.mk 0 true) (TwoSatLiteral.mk 1 true),
   TwoSatClause.mk (TwoSatLiteral.mk 0 true) (TwoSatLiteral.mk 1 false),
   TwoSatClause.mk (TwoSatLiteral.mk 0 false) (TwoSatLiteral.mk 1 true),
   TwoSatClause.mk (TwoSatLiteral.mk 0 false) (TwoSatLiteral.mk 1 false)]

-- genuineness smokes
#eval twoSatVerdictIsSatisfiable (twoSatDecide twoSatSmokeChainSystem)
-- expected: true
#eval twoSatVerdictTrueVariables (twoSatDecide twoSatSmokeChainSystem)
-- expected: [0, 1, 2]
#eval twoSatVerdictWitnessChecks twoSatSmokeChainSystem (twoSatDecide twoSatSmokeChainSystem)
-- expected: true (the SAT assignment satisfies every clause)
#eval twoSatVerdictIsSatisfiable (twoSatDecide twoSatSmokeContradictionSystem)
-- expected: false
#eval twoSatVerdictWitnessChecks twoSatSmokeContradictionSystem
  (twoSatDecide twoSatSmokeContradictionSystem)
-- expected: true (BOTH contradiction path certificates check)
#eval twoSatVerdictWitnessChecks twoSatSmokeContradictionSystem
  (twoSatDecide twoSatSmokeChainSystem)
-- expected: false (FALSE case — chain verdict does not witness the contradiction system)
#eval twoSatIsPathFrom twoSatSmokeChainSystem (TwoSatLiteral.mk 0 true)
  [TwoSatLiteral.mk 1 true, TwoSatLiteral.mk 2 true] (TwoSatLiteral.mk 2 true)
-- expected: true (x0 → x1 → x2)
#eval twoSatIsPathFrom twoSatSmokeChainSystem (TwoSatLiteral.mk 0 true)
  [TwoSatLiteral.mk 2 true] (TwoSatLiteral.mk 2 true)
-- expected: false (FALSE case — no direct edge x0 → x2)
#eval twoSatIsPathFrom twoSatSmokeChainSystem (TwoSatLiteral.mk 2 false)
  (twoSatDualPathAux (TwoSatLiteral.mk 0 true)
    [TwoSatLiteral.mk 1 true, TwoSatLiteral.mk 2 true] [])
  (TwoSatLiteral.mk 0 false)
-- expected: true (skew duality: ¬x2 → ¬x1 → ¬x0)
#eval twoSatSatisfies (twoSatEnvOfTrueList []) twoSatSmokeChainSystem
-- expected: false (FALSE case — the all-false assignment violates the unit clause)
#eval twoSatVerdictIsSatisfiable (twoSatDecide [])
-- expected: true (the empty system is satisfiable)
#eval twoSatVerdictWitnessChecks [] (twoSatDecide [])
-- expected: true

/-- DECIDED marker: the 2-SAT decision procedure ships with BOTH commissioned theorems —
`twoSatDecideUnsatSound` (certificate refutation of every assignment) and
`twoSatDecideSatSound` (the APT/Even–Itai–Shamir SAT half), zero-axiom. -/
def fxDissatIsland_hasTwoSatDecision : Bool := true

end FX1Poly.ComputerAlgebra
