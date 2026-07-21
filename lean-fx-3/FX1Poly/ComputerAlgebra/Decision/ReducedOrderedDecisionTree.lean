/-! # FX1Poly/ComputerAlgebra/Decision/ReducedOrderedDecisionTree — the ROBDD half of
    Boolean-equivalence decision (reduced ordered binary decision TREES: canonicity +
    formula-equivalence decision)

Boolean-formula equivalence is decided by compilation to **reduced ordered binary decision
trees** — the tree form of Bryant's ROBDDs (Bryant IEEE TC 1986; Andersen's lecture-note
"canonicity lemma"), where sharing is dropped, so Bryant's up-to-isomorphism uniqueness
collapses to plain structural equality.  The closest mechanized prior art is Nipkow's AFP
`Boolean_Expression_Checkers` (tree form, but no order and no canonicity theorem); the
canonicity statement below has no direct mechanized precedent.

  * **Trees** — `RobddTree`: Boolean leaves and `branch variableIndex lowChild highChild`
    nodes (low = the false-cofactor).  Ordering is Boolean-valued: `robddAllVarsAbove bound`
    (every branch variable strictly exceeds `bound`) threaded through `robddIsOrdered`;
    reducedness `robddIsReduced` bans beq-equal siblings.  `robddIsCanonical` = both.
  * **Independence** — `robddEvalUpdateIndependent`: a tree whose variables all exceed `v`
    ignores a single-point env update at `v`.  Cofactor extraction (`robddCofactorLow` /
    `robddCofactorHigh`) reads one branch under the corresponding update.
  * ★ **CANONICITY** — `robddCanonicalUnique`: two canonical trees computing the same
    function pointwise are structurally EQUAL.  The proof is a nested structural induction
    (outer on the first tree, inner on the second) — no fuel, no size measure: the
    leaf-vs-branch and larger-root-vs-smaller-root cases both close by applying the INNER
    induction hypothesis to the whole first tree against each child of the second, forcing
    beq-equal siblings against reducedness; the smaller-root case collapses the first
    tree's own siblings through independence of the other side (Andersen's argument).
  * **Builder** — `robddBuildOver` runs Shannon expansion over an explicit strictly
    ascending support list, restricting the formula (`robddRestrict`) at each head and
    collapsing equal children via `robddMkBranch` — canonical by construction
    (`robddBuildOverCanonical`), evaluation-correct over any covering list
    (`robddBuildOverEval`).  Support lists come from `robddSupportInto` (sorted dedup
    insertion, `robddSortedInsert`).

## The decision

`robddDecideEquiv formulaA formulaB` = structural beq of the two trees built over the
MERGED support (the merge is needed only for evaluation coverage — canonicity itself is
support-agnostic since vacuous tests collapse).  DECIDED, fully:

  * the packaged biconditional `robddEquivIffDecide` (pointwise-equivalence ↔ beq-true),
  * canonicity `robddCanonicalUnique` powering the completeness direction,
  * the `Decidable` instance `robddFormulaEquivDecidable` (Bool case split on the decision
    bit — no `propext`, no `decide`),
  * marker `fxDissatBool_hasRobddDecision := true`.

The Pi-over-envs equivalence is only ever PROVEN pointwise and USED by application — no
`funext` anywhere.

## Zero-axiom discipline

Init only.  Structural recursion throughout (no `WellFounded.fix`).  No `propext`,
`Quot.sound`, `Classical.choice`, `sorry`, `native_decide`, `funext`, `omega`, no `decide`
on `Prop` goals, no wildcard match arms over inductive scrutinees.  Bool dispatch in
definitions uses `cond`, never `if`; all comparisons are hand-rolled (`robddNatLess`,
`robddBoolBeq`, `robddTreeBeq`) with their kits proved by structural induction.  The
formula constructor for variables is `variableRef` (`variable` is a Lean keyword).
Per-declaration gate in `FX1PolyAudit/ComputerAlgebra/Decision/ReducedOrderedDecisionTree.lean`. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace FX1Poly.ComputerAlgebra

/-! ## Bool kit (hand-rolled, propext-free) -/

/-- Conjunction elimination for Bool `&&`. -/
theorem robddBoolAndElim : (leftFlag rightFlag : Bool) → (leftFlag && rightFlag) = true →
    leftFlag = true ∧ rightFlag = true
  | true, _, hAnd => ⟨rfl, hAnd⟩
  | false, _, hAnd => Bool.noConfusion hAnd

/-- Conjunction introduction for Bool `&&`. -/
theorem robddBoolAndIntro : (leftFlag rightFlag : Bool) → leftFlag = true → rightFlag = true →
    (leftFlag && rightFlag) = true
  | true, _, _, hRight => hRight
  | false, _, hLeft, _ => Bool.noConfusion hLeft

/-- Disjunction elimination for Bool `||`. -/
theorem robddBoolOrElim : (leftFlag rightFlag : Bool) → (leftFlag || rightFlag) = true →
    leftFlag = true ∨ rightFlag = true
  | true, _, _ => Or.inl rfl
  | false, _, hOr => Or.inr hOr

/-- Left disjunction introduction for Bool `||`. -/
theorem robddBoolOrIntroLeft : (leftFlag rightFlag : Bool) → leftFlag = true →
    (leftFlag || rightFlag) = true
  | true, _, _ => rfl
  | false, _, hLeft => Bool.noConfusion hLeft

/-- Right disjunction introduction for Bool `||`. -/
theorem robddBoolOrIntroRight : (leftFlag rightFlag : Bool) → rightFlag = true →
    (leftFlag || rightFlag) = true
  | true, _, _ => rfl
  | false, _, hRight => hRight

/-- A true negation forces the flag false. -/
theorem robddBoolNotElim : (flag : Bool) → (!flag) = true → flag = false
  | true, hNot => Bool.noConfusion hNot
  | false, _ => rfl

/-- `cond` with identical branches is that branch. -/
theorem robddBoolCondSame : (selector chosenValue : Bool) →
    cond selector chosenValue chosenValue = chosenValue
  | true, _ => rfl
  | false, _ => rfl

/-- Structural Boolean equality on `Bool`. -/
def robddBoolBeq : Bool → Bool → Bool
  | true, secondFlag => secondFlag
  | false, secondFlag => !secondFlag

/-- Reflexivity of `robddBoolBeq`. -/
theorem robddBoolBeqRefl : (flag : Bool) → robddBoolBeq flag flag = true
  | true => rfl
  | false => rfl

/-- `robddBoolBeq` sound: beq-true Booleans are equal. -/
theorem robddBoolBeqEq : (firstFlag secondFlag : Bool) →
    robddBoolBeq firstFlag secondFlag = true → firstFlag = secondFlag
  | true, true, _ => rfl
  | true, false, hBeq => Bool.noConfusion hBeq
  | false, true, hBeq => Bool.noConfusion hBeq
  | false, false, _ => rfl

/-- Exclusive or on `Bool`, hand-rolled. -/
def robddBoolXor : Bool → Bool → Bool
  | true, secondFlag => !secondFlag
  | false, secondFlag => secondFlag

/-! ## Nat kit (hand-rolled, propext-free) -/

/-- Reflexivity of `Nat.beq`. -/
theorem robddNatBeqRefl : (value : Nat) → Nat.beq value value = true
  | 0 => rfl
  | Nat.succ predecessor => robddNatBeqRefl predecessor

/-- `Nat.beq` sound: beq-true numbers are equal. -/
theorem robddNatBeqEq : (leftValue rightValue : Nat) → Nat.beq leftValue rightValue = true →
    leftValue = rightValue
  | 0, 0, _ => rfl
  | 0, Nat.succ _, hBeq => Bool.noConfusion hBeq
  | Nat.succ _, 0, hBeq => Bool.noConfusion hBeq
  | Nat.succ leftPredecessor, Nat.succ rightPredecessor, hBeq =>
      congrArg Nat.succ (robddNatBeqEq leftPredecessor rightPredecessor hBeq)

/-- Strict less-than on `Nat`, by double structural recursion. -/
def robddNatLess : Nat → Nat → Bool
  | 0, 0 => false
  | 0, Nat.succ _ => true
  | Nat.succ _, 0 => false
  | Nat.succ firstPredecessor, Nat.succ secondPredecessor =>
      robddNatLess firstPredecessor secondPredecessor

/-- A strictly larger number is beq-distinct from the smaller one. -/
theorem robddNatLessImpliesBeqFalse : (lowerValue upperValue : Nat) →
    robddNatLess lowerValue upperValue = true → Nat.beq upperValue lowerValue = false
  | 0, 0, hLess => Bool.noConfusion hLess
  | 0, Nat.succ _, _ => rfl
  | Nat.succ _, 0, hLess => Bool.noConfusion hLess
  | Nat.succ lowerPredecessor, Nat.succ upperPredecessor, hLess =>
      robddNatLessImpliesBeqFalse lowerPredecessor upperPredecessor hLess

/-- Transitivity of `robddNatLess`. -/
theorem robddNatLessTrans : (lowerValue middleValue upperValue : Nat) →
    robddNatLess lowerValue middleValue = true → robddNatLess middleValue upperValue = true →
    robddNatLess lowerValue upperValue = true
  | 0, 0, _, hFirst, _ => Bool.noConfusion hFirst
  | 0, Nat.succ _, 0, _, hSecond => Bool.noConfusion hSecond
  | 0, Nat.succ _, Nat.succ _, _, _ => rfl
  | Nat.succ _, 0, _, hFirst, _ => Bool.noConfusion hFirst
  | Nat.succ _, Nat.succ _, 0, _, hSecond => Bool.noConfusion hSecond
  | Nat.succ lowerPredecessor, Nat.succ middlePredecessor, Nat.succ upperPredecessor,
    hFirst, hSecond =>
      robddNatLessTrans lowerPredecessor middlePredecessor upperPredecessor hFirst hSecond

/-- Trichotomy: any two naturals are related by less, beq, or greater. -/
theorem robddNatTrichotomy : (firstValue secondValue : Nat) →
    robddNatLess firstValue secondValue = true ∨
      (Nat.beq firstValue secondValue = true ∨ robddNatLess secondValue firstValue = true)
  | 0, 0 => Or.inr (Or.inl rfl)
  | 0, Nat.succ _ => Or.inl rfl
  | Nat.succ _, 0 => Or.inr (Or.inr rfl)
  | Nat.succ firstPredecessor, Nat.succ secondPredecessor =>
      match robddNatTrichotomy firstPredecessor secondPredecessor with
      | Or.inl hLess => Or.inl hLess
      | Or.inr (Or.inl hBeq) => Or.inr (Or.inl hBeq)
      | Or.inr (Or.inr hGreater) => Or.inr (Or.inr hGreater)

/-! ## Environments: total valuations with single-point update -/

/-- Single-point environment update: `targetVariable` now reads `newValue`. -/
def robddEnvUpdate (env : Nat → Bool) (targetVariable : Nat) (newValue : Bool) : Nat → Bool :=
  fun queriedVariable => cond (Nat.beq queriedVariable targetVariable) newValue (env queriedVariable)

/-- Reading the updated environment at the target yields the new value. -/
theorem robddEnvUpdateAtTarget (env : Nat → Bool) (targetVariable : Nat) (newValue : Bool) :
    robddEnvUpdate env targetVariable newValue targetVariable = newValue := by
  show cond (Nat.beq targetVariable targetVariable) newValue (env targetVariable) = newValue
  rw [robddNatBeqRefl targetVariable]
  rfl

/-- Reading the updated environment away from the target is unchanged. -/
theorem robddEnvUpdateAway (env : Nat → Bool) (targetVariable : Nat) (newValue : Bool)
    (queriedVariable : Nat) (hDiffers : Nat.beq queriedVariable targetVariable = false) :
    robddEnvUpdate env targetVariable newValue queriedVariable = env queriedVariable := by
  show cond (Nat.beq queriedVariable targetVariable) newValue (env queriedVariable)
      = env queriedVariable
  rw [hDiffers]
  rfl

/-! ## Decision trees -/

/-- Binary decision trees: Boolean leaves, or a test on a variable with a false-branch
(`lowChild`) and a true-branch (`highChild`). -/
inductive RobddTree : Type where
  | leaf (storedValue : Bool) : RobddTree
  | branch (variableIndex : Nat) (lowChild highChild : RobddTree) : RobddTree

/-- Structural Boolean equality on decision trees. -/
def robddTreeBeq : RobddTree → RobddTree → Bool
  | RobddTree.leaf firstValue, RobddTree.leaf secondValue => robddBoolBeq firstValue secondValue
  | RobddTree.leaf _, RobddTree.branch _ _ _ => false
  | RobddTree.branch _ _ _, RobddTree.leaf _ => false
  | RobddTree.branch firstVariable firstLow firstHigh,
    RobddTree.branch secondVariable secondLow secondHigh =>
      Nat.beq firstVariable secondVariable &&
        (robddTreeBeq firstLow secondLow && robddTreeBeq firstHigh secondHigh)

/-- Reflexivity of `robddTreeBeq`. -/
theorem robddTreeBeqRefl : (tree : RobddTree) → robddTreeBeq tree tree = true
  | RobddTree.leaf storedValue => robddBoolBeqRefl storedValue
  | RobddTree.branch variableIndex lowChild highChild => by
      show (Nat.beq variableIndex variableIndex &&
          (robddTreeBeq lowChild lowChild && robddTreeBeq highChild highChild)) = true
      rw [robddNatBeqRefl variableIndex, robddTreeBeqRefl lowChild, robddTreeBeqRefl highChild]
      rfl

/-- `robddTreeBeq` sound: beq-true trees are equal. -/
theorem robddTreeBeqEq : (firstTree secondTree : RobddTree) →
    robddTreeBeq firstTree secondTree = true → firstTree = secondTree
  | RobddTree.leaf firstValue, RobddTree.leaf secondValue, hBeq =>
      congrArg RobddTree.leaf (robddBoolBeqEq firstValue secondValue hBeq)
  | RobddTree.leaf _, RobddTree.branch _ _ _, hBeq => Bool.noConfusion hBeq
  | RobddTree.branch _ _ _, RobddTree.leaf _, hBeq => Bool.noConfusion hBeq
  | RobddTree.branch firstVariable firstLow firstHigh,
    RobddTree.branch secondVariable secondLow secondHigh, hBeq => by
      have hTyped : (Nat.beq firstVariable secondVariable &&
          (robddTreeBeq firstLow secondLow && robddTreeBeq firstHigh secondHigh)) = true := hBeq
      have hSplit := robddBoolAndElim _ _ hTyped
      have hChildren := robddBoolAndElim _ _ hSplit.right
      rw [robddNatBeqEq firstVariable secondVariable hSplit.left,
          robddTreeBeqEq firstLow secondLow hChildren.left,
          robddTreeBeqEq firstHigh secondHigh hChildren.right]

/-- Tree evaluation under a total environment: a branch reads its variable and follows
the true-branch (`highChild`) or false-branch (`lowChild`). -/
def robddEval (env : Nat → Bool) : RobddTree → Bool
  | RobddTree.leaf storedValue => storedValue
  | RobddTree.branch variableIndex lowChild highChild =>
      cond (env variableIndex) (robddEval env highChild) (robddEval env lowChild)

/-! ## Invariants: ordering and reducedness -/

/-- Does every branch variable of the tree strictly exceed `bound`? -/
def robddAllVarsAbove (bound : Nat) : RobddTree → Bool
  | RobddTree.leaf _ => true
  | RobddTree.branch variableIndex lowChild highChild =>
      robddNatLess bound variableIndex &&
        (robddAllVarsAbove bound lowChild && robddAllVarsAbove bound highChild)

/-- Is the tree ordered: below each branch, both children test only strictly larger
variables (and are recursively ordered)? -/
def robddIsOrdered : RobddTree → Bool
  | RobddTree.leaf _ => true
  | RobddTree.branch variableIndex lowChild highChild =>
      robddAllVarsAbove variableIndex lowChild &&
        (robddAllVarsAbove variableIndex highChild &&
        (robddIsOrdered lowChild && robddIsOrdered highChild))

/-- Is the tree reduced: no branch has beq-equal children (no redundant tests)? -/
def robddIsReduced : RobddTree → Bool
  | RobddTree.leaf _ => true
  | RobddTree.branch _ lowChild highChild =>
      (!robddTreeBeq lowChild highChild) &&
        (robddIsReduced lowChild && robddIsReduced highChild)

/-- Is the tree canonical: ordered and reduced? -/
def robddIsCanonical (tree : RobddTree) : Bool :=
  robddIsOrdered tree && robddIsReduced tree

/-- Lowering the strict bound preserves `robddAllVarsAbove`. -/
theorem robddAllVarsAboveWeaken (lowerBound upperBound : Nat)
    (hBoundLess : robddNatLess lowerBound upperBound = true) : (tree : RobddTree) →
    robddAllVarsAbove upperBound tree = true → robddAllVarsAbove lowerBound tree = true
  | RobddTree.leaf _, _ => rfl
  | RobddTree.branch variableIndex lowChild highChild, hAbove => by
      have hTyped : (robddNatLess upperBound variableIndex &&
          (robddAllVarsAbove upperBound lowChild && robddAllVarsAbove upperBound highChild))
          = true := hAbove
      have hSplit := robddBoolAndElim _ _ hTyped
      have hChildren := robddBoolAndElim _ _ hSplit.right
      exact robddBoolAndIntro _ _
        (robddNatLessTrans lowerBound upperBound variableIndex hBoundLess hSplit.left)
        (robddBoolAndIntro _ _
          (robddAllVarsAboveWeaken lowerBound upperBound hBoundLess lowChild hChildren.left)
          (robddAllVarsAboveWeaken lowerBound upperBound hBoundLess highChild hChildren.right))

/-! ## Independence and cofactor extraction -/

/-- **Independence**: a tree whose branch variables all strictly exceed `targetVariable`
evaluates identically under a single-point update at `targetVariable`. -/
theorem robddEvalUpdateIndependent (targetVariable : Nat) (newValue : Bool) :
    (tree : RobddTree) → robddAllVarsAbove targetVariable tree = true → (env : Nat → Bool) →
    robddEval (robddEnvUpdate env targetVariable newValue) tree = robddEval env tree
  | RobddTree.leaf _, _, _ => rfl
  | RobddTree.branch variableIndex lowChild highChild, hAbove, env => by
      have hTyped : (robddNatLess targetVariable variableIndex &&
          (robddAllVarsAbove targetVariable lowChild &&
            robddAllVarsAbove targetVariable highChild)) = true := hAbove
      have hSplit := robddBoolAndElim _ _ hTyped
      have hChildren := robddBoolAndElim _ _ hSplit.right
      have hBeqFalse : Nat.beq variableIndex targetVariable = false :=
        robddNatLessImpliesBeqFalse targetVariable variableIndex hSplit.left
      show cond (cond (Nat.beq variableIndex targetVariable) newValue (env variableIndex))
            (robddEval (robddEnvUpdate env targetVariable newValue) highChild)
            (robddEval (robddEnvUpdate env targetVariable newValue) lowChild)
          = cond (env variableIndex) (robddEval env highChild) (robddEval env lowChild)
      rw [hBeqFalse,
          robddEvalUpdateIndependent targetVariable newValue lowChild hChildren.left env,
          robddEvalUpdateIndependent targetVariable newValue highChild hChildren.right env]
      rfl

/-- **Low cofactor**: under the false-update at the root variable, a branch evaluates to
its low child (which must not retest the root variable). -/
theorem robddCofactorLow (rootVariable : Nat) (lowChild highChild : RobddTree)
    (hAboveLow : robddAllVarsAbove rootVariable lowChild = true) (env : Nat → Bool) :
    robddEval (robddEnvUpdate env rootVariable false)
        (RobddTree.branch rootVariable lowChild highChild)
      = robddEval env lowChild := by
  show cond (cond (Nat.beq rootVariable rootVariable) false (env rootVariable))
        (robddEval (robddEnvUpdate env rootVariable false) highChild)
        (robddEval (robddEnvUpdate env rootVariable false) lowChild)
      = robddEval env lowChild
  rw [robddNatBeqRefl rootVariable]
  exact robddEvalUpdateIndependent rootVariable false lowChild hAboveLow env

/-- **High cofactor**: under the true-update at the root variable, a branch evaluates to
its high child (which must not retest the root variable). -/
theorem robddCofactorHigh (rootVariable : Nat) (lowChild highChild : RobddTree)
    (hAboveHigh : robddAllVarsAbove rootVariable highChild = true) (env : Nat → Bool) :
    robddEval (robddEnvUpdate env rootVariable true)
        (RobddTree.branch rootVariable lowChild highChild)
      = robddEval env highChild := by
  show cond (cond (Nat.beq rootVariable rootVariable) true (env rootVariable))
        (robddEval (robddEnvUpdate env rootVariable true) highChild)
        (robddEval (robddEnvUpdate env rootVariable true) lowChild)
      = robddEval env highChild
  rw [robddNatBeqRefl rootVariable]
  exact robddEvalUpdateIndependent rootVariable true highChild hAboveHigh env

/-! ## Canonicity -/

/-- Unpacking a canonical branch: both children sit strictly above the root variable, both
are canonical, and the children are beq-distinct. -/
theorem robddCanonicalBranchParts (variableIndex : Nat) (lowChild highChild : RobddTree)
    (hCanonical : robddIsCanonical (RobddTree.branch variableIndex lowChild highChild) = true) :
    robddAllVarsAbove variableIndex lowChild = true ∧
    (robddAllVarsAbove variableIndex highChild = true ∧
    (robddIsCanonical lowChild = true ∧
    (robddIsCanonical highChild = true ∧
    robddTreeBeq lowChild highChild = false))) := by
  have hPair : (robddIsOrdered (RobddTree.branch variableIndex lowChild highChild) &&
      robddIsReduced (RobddTree.branch variableIndex lowChild highChild)) = true := hCanonical
  have hSplit := robddBoolAndElim _ _ hPair
  have hOrderedTyped : (robddAllVarsAbove variableIndex lowChild &&
      (robddAllVarsAbove variableIndex highChild &&
      (robddIsOrdered lowChild && robddIsOrdered highChild))) = true := hSplit.left
  have hReducedTyped : ((!robddTreeBeq lowChild highChild) &&
      (robddIsReduced lowChild && robddIsReduced highChild)) = true := hSplit.right
  have hOrderedSplit := robddBoolAndElim _ _ hOrderedTyped
  have hOrderedRest := robddBoolAndElim _ _ hOrderedSplit.right
  have hOrderedChildren := robddBoolAndElim _ _ hOrderedRest.right
  have hReducedSplit := robddBoolAndElim _ _ hReducedTyped
  have hReducedChildren := robddBoolAndElim _ _ hReducedSplit.right
  exact ⟨hOrderedSplit.left, hOrderedRest.left,
    robddBoolAndIntro _ _ hOrderedChildren.left hReducedChildren.left,
    robddBoolAndIntro _ _ hOrderedChildren.right hReducedChildren.right,
    robddBoolNotElim _ hReducedSplit.left⟩

/-- Equal children refute a beq-distinctness witness (the reducedness contradiction). -/
theorem robddReducednessAbsurd (lowChild highChild : RobddTree) (hEqual : lowChild = highChild)
    (hBeqFalse : robddTreeBeq lowChild highChild = false) : False := by
  rw [hEqual] at hBeqFalse
  exact Bool.noConfusion ((robddTreeBeqRefl highChild).symm.trans hBeqFalse)

/-- ★ **CANONICITY**: canonical (ordered + reduced) decision trees computing the same
Boolean function pointwise are structurally equal.  Nested structural induction — outer on
the first tree, inner on the second; the cross cases (leaf vs branch, larger root vs
smaller root) apply the inner induction hypothesis to the WHOLE first tree against each
child of the second, forcing beq-equal siblings against reducedness. -/
theorem robddCanonicalUnique : (firstTree secondTree : RobddTree) →
    robddIsCanonical firstTree = true → robddIsCanonical secondTree = true →
    ((env : Nat → Bool) → robddEval env firstTree = robddEval env secondTree) →
    firstTree = secondTree := by
  intro firstTree
  induction firstTree with
  | leaf firstValue =>
    intro secondTree
    induction secondTree with
    | leaf secondValue =>
      intro _ _ hPointwise
      exact congrArg RobddTree.leaf (hPointwise (fun _ => false))
    | branch secondVariable secondLow secondHigh ihSecondLow ihSecondHigh =>
      intro hCanonFirst hCanonSecond hPointwise
      have hSecondParts :=
        robddCanonicalBranchParts secondVariable secondLow secondHigh hCanonSecond
      have hFirstLow : (env : Nat → Bool) →
          robddEval env (RobddTree.leaf firstValue) = robddEval env secondLow := fun env =>
        Eq.trans (hPointwise (robddEnvUpdate env secondVariable false))
          (robddCofactorLow secondVariable secondLow secondHigh hSecondParts.left env)
      have hFirstHigh : (env : Nat → Bool) →
          robddEval env (RobddTree.leaf firstValue) = robddEval env secondHigh := fun env =>
        Eq.trans (hPointwise (robddEnvUpdate env secondVariable true))
          (robddCofactorHigh secondVariable secondLow secondHigh hSecondParts.right.left env)
      have hEqualLow : RobddTree.leaf firstValue = secondLow :=
        ihSecondLow hCanonFirst hSecondParts.right.right.left hFirstLow
      have hEqualHigh : RobddTree.leaf firstValue = secondHigh :=
        ihSecondHigh hCanonFirst hSecondParts.right.right.right.left hFirstHigh
      exact False.elim (robddReducednessAbsurd secondLow secondHigh
        (hEqualLow.symm.trans hEqualHigh) hSecondParts.right.right.right.right)
  | branch firstVariable firstLow firstHigh ihFirstLow ihFirstHigh =>
    intro secondTree
    induction secondTree with
    | leaf secondValue =>
      intro hCanonFirst hCanonSecond hPointwise
      have hFirstParts :=
        robddCanonicalBranchParts firstVariable firstLow firstHigh hCanonFirst
      have hLowConst : (env : Nat → Bool) →
          robddEval env firstLow = robddEval env (RobddTree.leaf secondValue) := fun env =>
        Eq.trans
          (Eq.symm (robddCofactorLow firstVariable firstLow firstHigh hFirstParts.left env))
          (hPointwise (robddEnvUpdate env firstVariable false))
      have hHighConst : (env : Nat → Bool) →
          robddEval env firstHigh = robddEval env (RobddTree.leaf secondValue) := fun env =>
        Eq.trans
          (Eq.symm (robddCofactorHigh firstVariable firstLow firstHigh
            hFirstParts.right.left env))
          (hPointwise (robddEnvUpdate env firstVariable true))
      have hEqualLow : firstLow = RobddTree.leaf secondValue :=
        ihFirstLow (RobddTree.leaf secondValue) hFirstParts.right.right.left
          hCanonSecond hLowConst
      have hEqualHigh : firstHigh = RobddTree.leaf secondValue :=
        ihFirstHigh (RobddTree.leaf secondValue) hFirstParts.right.right.right.left
          hCanonSecond hHighConst
      exact False.elim (robddReducednessAbsurd firstLow firstHigh
        (hEqualLow.trans hEqualHigh.symm) hFirstParts.right.right.right.right)
    | branch secondVariable secondLow secondHigh ihSecondLow ihSecondHigh =>
      intro hCanonFirst hCanonSecond hPointwise
      have hFirstParts :=
        robddCanonicalBranchParts firstVariable firstLow firstHigh hCanonFirst
      have hSecondParts :=
        robddCanonicalBranchParts secondVariable secondLow secondHigh hCanonSecond
      cases robddNatTrichotomy firstVariable secondVariable with
      | inl hFirstSmaller =>
        have hSecondAbove : robddAllVarsAbove firstVariable
            (RobddTree.branch secondVariable secondLow secondHigh) = true :=
          robddBoolAndIntro _ _ hFirstSmaller (robddBoolAndIntro _ _
            (robddAllVarsAboveWeaken firstVariable secondVariable hFirstSmaller
              secondLow hSecondParts.left)
            (robddAllVarsAboveWeaken firstVariable secondVariable hFirstSmaller
              secondHigh hSecondParts.right.left))
        have hLowHighAgree : (env : Nat → Bool) →
            robddEval env firstLow = robddEval env firstHigh := fun env =>
          Eq.trans
            (Eq.symm (robddCofactorLow firstVariable firstLow firstHigh hFirstParts.left env))
          (Eq.trans (hPointwise (robddEnvUpdate env firstVariable false))
          (Eq.trans (robddEvalUpdateIndependent firstVariable false
              (RobddTree.branch secondVariable secondLow secondHigh) hSecondAbove env)
          (Eq.trans (Eq.symm (robddEvalUpdateIndependent firstVariable true
              (RobddTree.branch secondVariable secondLow secondHigh) hSecondAbove env))
          (Eq.trans (Eq.symm (hPointwise (robddEnvUpdate env firstVariable true)))
            (robddCofactorHigh firstVariable firstLow firstHigh
              hFirstParts.right.left env)))))
        have hCollapse : firstLow = firstHigh :=
          ihFirstLow firstHigh hFirstParts.right.right.left
            hFirstParts.right.right.right.left hLowHighAgree
        exact False.elim (robddReducednessAbsurd firstLow firstHigh hCollapse
          hFirstParts.right.right.right.right)
      | inr hRemaining =>
        cases hRemaining with
        | inl hRootsBeq =>
          have hRootsEqual : firstVariable = secondVariable :=
            robddNatBeqEq firstVariable secondVariable hRootsBeq
          subst hRootsEqual
          have hLowAgree : (env : Nat → Bool) →
              robddEval env firstLow = robddEval env secondLow := fun env =>
            Eq.trans
              (Eq.symm (robddCofactorLow firstVariable firstLow firstHigh
                hFirstParts.left env))
            (Eq.trans (hPointwise (robddEnvUpdate env firstVariable false))
              (robddCofactorLow firstVariable secondLow secondHigh hSecondParts.left env))
          have hHighAgree : (env : Nat → Bool) →
              robddEval env firstHigh = robddEval env secondHigh := fun env =>
            Eq.trans
              (Eq.symm (robddCofactorHigh firstVariable firstLow firstHigh
                hFirstParts.right.left env))
            (Eq.trans (hPointwise (robddEnvUpdate env firstVariable true))
              (robddCofactorHigh firstVariable secondLow secondHigh
                hSecondParts.right.left env))
          have hEqualLow : firstLow = secondLow :=
            ihFirstLow secondLow hFirstParts.right.right.left
              hSecondParts.right.right.left hLowAgree
          have hEqualHigh : firstHigh = secondHigh :=
            ihFirstHigh secondHigh hFirstParts.right.right.right.left
              hSecondParts.right.right.right.left hHighAgree
          rw [hEqualLow, hEqualHigh]
        | inr hSecondSmaller =>
          have hFirstAbove : robddAllVarsAbove secondVariable
              (RobddTree.branch firstVariable firstLow firstHigh) = true :=
            robddBoolAndIntro _ _ hSecondSmaller (robddBoolAndIntro _ _
              (robddAllVarsAboveWeaken secondVariable firstVariable hSecondSmaller
                firstLow hFirstParts.left)
              (robddAllVarsAboveWeaken secondVariable firstVariable hSecondSmaller
                firstHigh hFirstParts.right.left))
          have hFirstIsLow : (env : Nat → Bool) →
              robddEval env (RobddTree.branch firstVariable firstLow firstHigh)
                = robddEval env secondLow := fun env =>
            Eq.trans (Eq.symm (robddEvalUpdateIndependent secondVariable false
                (RobddTree.branch firstVariable firstLow firstHigh) hFirstAbove env))
            (Eq.trans (hPointwise (robddEnvUpdate env secondVariable false))
              (robddCofactorLow secondVariable secondLow secondHigh hSecondParts.left env))
          have hFirstIsHigh : (env : Nat → Bool) →
              robddEval env (RobddTree.branch firstVariable firstLow firstHigh)
                = robddEval env secondHigh := fun env =>
            Eq.trans (Eq.symm (robddEvalUpdateIndependent secondVariable true
                (RobddTree.branch firstVariable firstLow firstHigh) hFirstAbove env))
            (Eq.trans (hPointwise (robddEnvUpdate env secondVariable true))
              (robddCofactorHigh secondVariable secondLow secondHigh
                hSecondParts.right.left env))
          have hEqualLow : RobddTree.branch firstVariable firstLow firstHigh = secondLow :=
            ihSecondLow hCanonFirst hSecondParts.right.right.left hFirstIsLow
          have hEqualHigh : RobddTree.branch firstVariable firstLow firstHigh = secondHigh :=
            ihSecondHigh hCanonFirst hSecondParts.right.right.right.left hFirstIsHigh
          exact False.elim (robddReducednessAbsurd secondLow secondHigh
            (hEqualLow.symm.trans hEqualHigh) hSecondParts.right.right.right.right)

/-! ## Formulas -/

/-- Boolean formulas over Nat-indexed variables.  The variable constructor is
`variableRef` because `variable` is a Lean keyword. -/
inductive RobddFormula : Type where
  | falseConst : RobddFormula
  | trueConst : RobddFormula
  | variableRef (index : Nat) : RobddFormula
  | negation (operand : RobddFormula) : RobddFormula
  | conjunction (leftOperand rightOperand : RobddFormula) : RobddFormula
  | disjunction (leftOperand rightOperand : RobddFormula) : RobddFormula
  | exclusiveOr (leftOperand rightOperand : RobddFormula) : RobddFormula

/-- Formula evaluation under a total environment. -/
def robddFormulaEval (env : Nat → Bool) : RobddFormula → Bool
  | RobddFormula.falseConst => false
  | RobddFormula.trueConst => true
  | RobddFormula.variableRef index => env index
  | RobddFormula.negation operand => !robddFormulaEval env operand
  | RobddFormula.conjunction leftOperand rightOperand =>
      robddFormulaEval env leftOperand && robddFormulaEval env rightOperand
  | RobddFormula.disjunction leftOperand rightOperand =>
      robddFormulaEval env leftOperand || robddFormulaEval env rightOperand
  | RobddFormula.exclusiveOr leftOperand rightOperand =>
      robddBoolXor (robddFormulaEval env leftOperand) (robddFormulaEval env rightOperand)

/-- Substituting a constant for one variable, structurally. -/
def robddRestrict (targetVariable : Nat) (newValue : Bool) : RobddFormula → RobddFormula
  | RobddFormula.falseConst => RobddFormula.falseConst
  | RobddFormula.trueConst => RobddFormula.trueConst
  | RobddFormula.variableRef index =>
      cond (Nat.beq index targetVariable)
        (cond newValue RobddFormula.trueConst RobddFormula.falseConst)
        (RobddFormula.variableRef index)
  | RobddFormula.negation operand =>
      RobddFormula.negation (robddRestrict targetVariable newValue operand)
  | RobddFormula.conjunction leftOperand rightOperand =>
      RobddFormula.conjunction (robddRestrict targetVariable newValue leftOperand)
        (robddRestrict targetVariable newValue rightOperand)
  | RobddFormula.disjunction leftOperand rightOperand =>
      RobddFormula.disjunction (robddRestrict targetVariable newValue leftOperand)
        (robddRestrict targetVariable newValue rightOperand)
  | RobddFormula.exclusiveOr leftOperand rightOperand =>
      RobddFormula.exclusiveOr (robddRestrict targetVariable newValue leftOperand)
        (robddRestrict targetVariable newValue rightOperand)

/-- Restriction agrees with evaluation under the single-point update. -/
theorem robddRestrictEval (targetVariable : Nat) (newValue : Bool) :
    (formula : RobddFormula) → (env : Nat → Bool) →
    robddFormulaEval env (robddRestrict targetVariable newValue formula)
      = robddFormulaEval (robddEnvUpdate env targetVariable newValue) formula
  | RobddFormula.falseConst, _ => rfl
  | RobddFormula.trueConst, _ => rfl
  | RobddFormula.variableRef index, env => by
      show robddFormulaEval env
          (cond (Nat.beq index targetVariable)
            (cond newValue RobddFormula.trueConst RobddFormula.falseConst)
            (RobddFormula.variableRef index))
          = cond (Nat.beq index targetVariable) newValue (env index)
      cases hBeq : Nat.beq index targetVariable with
      | true =>
          cases newValue with
          | true => rfl
          | false => rfl
      | false => rfl
  | RobddFormula.negation operand, env => by
      show (!robddFormulaEval env (robddRestrict targetVariable newValue operand))
          = (!robddFormulaEval (robddEnvUpdate env targetVariable newValue) operand)
      rw [robddRestrictEval targetVariable newValue operand env]
  | RobddFormula.conjunction leftOperand rightOperand, env => by
      show (robddFormulaEval env (robddRestrict targetVariable newValue leftOperand) &&
          robddFormulaEval env (robddRestrict targetVariable newValue rightOperand))
          = (robddFormulaEval (robddEnvUpdate env targetVariable newValue) leftOperand &&
            robddFormulaEval (robddEnvUpdate env targetVariable newValue) rightOperand)
      rw [robddRestrictEval targetVariable newValue leftOperand env,
          robddRestrictEval targetVariable newValue rightOperand env]
  | RobddFormula.disjunction leftOperand rightOperand, env => by
      show (robddFormulaEval env (robddRestrict targetVariable newValue leftOperand) ||
          robddFormulaEval env (robddRestrict targetVariable newValue rightOperand))
          = (robddFormulaEval (robddEnvUpdate env targetVariable newValue) leftOperand ||
            robddFormulaEval (robddEnvUpdate env targetVariable newValue) rightOperand)
      rw [robddRestrictEval targetVariable newValue leftOperand env,
          robddRestrictEval targetVariable newValue rightOperand env]
  | RobddFormula.exclusiveOr leftOperand rightOperand, env => by
      show robddBoolXor (robddFormulaEval env (robddRestrict targetVariable newValue leftOperand))
          (robddFormulaEval env (robddRestrict targetVariable newValue rightOperand))
          = robddBoolXor
            (robddFormulaEval (robddEnvUpdate env targetVariable newValue) leftOperand)
            (robddFormulaEval (robddEnvUpdate env targetVariable newValue) rightOperand)
      rw [robddRestrictEval targetVariable newValue leftOperand env,
          robddRestrictEval targetVariable newValue rightOperand env]

/-- Formula evaluation only depends on the environment pointwise. -/
theorem robddFormulaEvalCongr (envFirst envSecond : Nat → Bool)
    (hAgree : (queriedVariable : Nat) → envFirst queriedVariable = envSecond queriedVariable) :
    (formula : RobddFormula) →
    robddFormulaEval envFirst formula = robddFormulaEval envSecond formula
  | RobddFormula.falseConst => rfl
  | RobddFormula.trueConst => rfl
  | RobddFormula.variableRef index => hAgree index
  | RobddFormula.negation operand =>
      congrArg Bool.not (robddFormulaEvalCongr envFirst envSecond hAgree operand)
  | RobddFormula.conjunction leftOperand rightOperand => by
      show (robddFormulaEval envFirst leftOperand && robddFormulaEval envFirst rightOperand)
          = (robddFormulaEval envSecond leftOperand && robddFormulaEval envSecond rightOperand)
      rw [robddFormulaEvalCongr envFirst envSecond hAgree leftOperand,
          robddFormulaEvalCongr envFirst envSecond hAgree rightOperand]
  | RobddFormula.disjunction leftOperand rightOperand => by
      show (robddFormulaEval envFirst leftOperand || robddFormulaEval envFirst rightOperand)
          = (robddFormulaEval envSecond leftOperand || robddFormulaEval envSecond rightOperand)
      rw [robddFormulaEvalCongr envFirst envSecond hAgree leftOperand,
          robddFormulaEvalCongr envFirst envSecond hAgree rightOperand]
  | RobddFormula.exclusiveOr leftOperand rightOperand => by
      show robddBoolXor (robddFormulaEval envFirst leftOperand)
            (robddFormulaEval envFirst rightOperand)
          = robddBoolXor (robddFormulaEval envSecond leftOperand)
            (robddFormulaEval envSecond rightOperand)
      rw [robddFormulaEvalCongr envFirst envSecond hAgree leftOperand,
          robddFormulaEvalCongr envFirst envSecond hAgree rightOperand]

/-- **Shannon expansion**: dispatching on the current value of a variable between the two
single-point restrictions recovers the formula's value. -/
theorem robddShannonExpansion (targetVariable : Nat) (formula : RobddFormula)
    (env : Nat → Bool) :
    cond (env targetVariable)
      (robddFormulaEval (robddEnvUpdate env targetVariable true) formula)
      (robddFormulaEval (robddEnvUpdate env targetVariable false) formula)
    = robddFormulaEval env formula := by
  cases hCurrent : env targetVariable with
  | true =>
      have hAgree : (queriedVariable : Nat) →
          robddEnvUpdate env targetVariable true queriedVariable = env queriedVariable := by
        intro queriedVariable
        show cond (Nat.beq queriedVariable targetVariable) true (env queriedVariable)
            = env queriedVariable
        cases hBeq : Nat.beq queriedVariable targetVariable with
        | true =>
            have hSame : queriedVariable = targetVariable :=
              robddNatBeqEq queriedVariable targetVariable hBeq
            rw [hSame, hCurrent]
            rfl
        | false => rfl
      exact robddFormulaEvalCongr (robddEnvUpdate env targetVariable true) env hAgree formula
  | false =>
      have hAgree : (queriedVariable : Nat) →
          robddEnvUpdate env targetVariable false queriedVariable = env queriedVariable := by
        intro queriedVariable
        show cond (Nat.beq queriedVariable targetVariable) false (env queriedVariable)
            = env queriedVariable
        cases hBeq : Nat.beq queriedVariable targetVariable with
        | true =>
            have hSame : queriedVariable = targetVariable :=
              robddNatBeqEq queriedVariable targetVariable hBeq
            rw [hSame, hCurrent]
            rfl
        | false => rfl
      exact robddFormulaEvalCongr (robddEnvUpdate env targetVariable false) env hAgree formula

/-! ## Support lists: sorted dedup insertion, membership, coverage -/

/-- List membership by `Nat.beq`. -/
def robddListContains (queriedVariable : Nat) : List Nat → Bool
  | List.nil => false
  | List.cons headVariable restVariables =>
      Nat.beq queriedVariable headVariable || robddListContains queriedVariable restVariables

/-- Is every list member strictly above `bound`? -/
def robddListAllAbove (bound : Nat) : List Nat → Bool
  | List.nil => true
  | List.cons headVariable restVariables =>
      robddNatLess bound headVariable && robddListAllAbove bound restVariables

/-- Is the list strictly ascending (hereditarily: each head bounds its whole tail)? -/
def robddListSortedStrict : List Nat → Bool
  | List.nil => true
  | List.cons headVariable restVariables =>
      robddListAllAbove headVariable restVariables && robddListSortedStrict restVariables

/-- Dedup sorted insertion into a strictly ascending list. -/
def robddSortedInsert (newVariable : Nat) : List Nat → List Nat
  | List.nil => List.cons newVariable List.nil
  | List.cons headVariable restVariables =>
      cond (robddNatLess newVariable headVariable)
        (List.cons newVariable (List.cons headVariable restVariables))
        (cond (Nat.beq newVariable headVariable)
          (List.cons headVariable restVariables)
          (List.cons headVariable (robddSortedInsert newVariable restVariables)))

/-- Lowering the strict bound preserves `robddListAllAbove`. -/
theorem robddListAllAboveWeaken (lowerBound upperBound : Nat)
    (hBoundLess : robddNatLess lowerBound upperBound = true) : (variableList : List Nat) →
    robddListAllAbove upperBound variableList = true →
    robddListAllAbove lowerBound variableList = true
  | List.nil, _ => rfl
  | List.cons headVariable restVariables, hAllAbove => by
      have hTyped : (robddNatLess upperBound headVariable &&
          robddListAllAbove upperBound restVariables) = true := hAllAbove
      have hSplit := robddBoolAndElim _ _ hTyped
      exact robddBoolAndIntro _ _
        (robddNatLessTrans lowerBound upperBound headVariable hBoundLess hSplit.left)
        (robddListAllAboveWeaken lowerBound upperBound hBoundLess restVariables hSplit.right)

/-- Inserting a member above the bound preserves `robddListAllAbove`. -/
theorem robddListAllAboveInsert (bound newVariable : Nat)
    (hNewAbove : robddNatLess bound newVariable = true) : (variableList : List Nat) →
    robddListAllAbove bound variableList = true →
    robddListAllAbove bound (robddSortedInsert newVariable variableList) = true
  | List.nil, _ => robddBoolAndIntro _ _ hNewAbove rfl
  | List.cons headVariable restVariables, hAllAbove => by
      have hTyped : (robddNatLess bound headVariable &&
          robddListAllAbove bound restVariables) = true := hAllAbove
      have hSplit := robddBoolAndElim _ _ hTyped
      show robddListAllAbove bound
          (cond (robddNatLess newVariable headVariable)
            (List.cons newVariable (List.cons headVariable restVariables))
            (cond (Nat.beq newVariable headVariable)
              (List.cons headVariable restVariables)
              (List.cons headVariable (robddSortedInsert newVariable restVariables)))) = true
      cases hLessHead : robddNatLess newVariable headVariable with
      | true => exact robddBoolAndIntro _ _ hNewAbove hAllAbove
      | false =>
          cases hBeqHead : Nat.beq newVariable headVariable with
          | true => exact hAllAbove
          | false =>
              exact robddBoolAndIntro _ _ hSplit.left
                (robddListAllAboveInsert bound newVariable hNewAbove
                  restVariables hSplit.right)

/-- Sorted insertion preserves strict ascending order. -/
theorem robddSortedInsertPreserves (newVariable : Nat) : (variableList : List Nat) →
    robddListSortedStrict variableList = true →
    robddListSortedStrict (robddSortedInsert newVariable variableList) = true
  | List.nil, _ => rfl
  | List.cons headVariable restVariables, hSorted => by
      have hTyped : (robddListAllAbove headVariable restVariables &&
          robddListSortedStrict restVariables) = true := hSorted
      have hSplit := robddBoolAndElim _ _ hTyped
      show robddListSortedStrict
          (cond (robddNatLess newVariable headVariable)
            (List.cons newVariable (List.cons headVariable restVariables))
            (cond (Nat.beq newVariable headVariable)
              (List.cons headVariable restVariables)
              (List.cons headVariable (robddSortedInsert newVariable restVariables)))) = true
      cases hLessHead : robddNatLess newVariable headVariable with
      | true =>
          exact robddBoolAndIntro _ _
            (robddBoolAndIntro _ _ hLessHead
              (robddListAllAboveWeaken newVariable headVariable hLessHead
                restVariables hSplit.left))
            hSorted
      | false =>
          cases hBeqHead : Nat.beq newVariable headVariable with
          | true => exact hSorted
          | false =>
              have hHeadLessNew : robddNatLess headVariable newVariable = true := by
                cases robddNatTrichotomy newVariable headVariable with
                | inl hLess => exact Bool.noConfusion (hLessHead.symm.trans hLess)
                | inr hRest =>
                    cases hRest with
                    | inl hBeq => exact Bool.noConfusion (hBeqHead.symm.trans hBeq)
                    | inr hGreater => exact hGreater
              exact robddBoolAndIntro _ _
                (robddListAllAboveInsert headVariable newVariable hHeadLessNew
                  restVariables hSplit.left)
                (robddSortedInsertPreserves newVariable restVariables hSplit.right)

/-- Insertion makes the inserted variable a member. -/
theorem robddContainsInsertSelf (newVariable : Nat) : (variableList : List Nat) →
    robddListContains newVariable (robddSortedInsert newVariable variableList) = true
  | List.nil => robddBoolOrIntroLeft _ _ (robddNatBeqRefl newVariable)
  | List.cons headVariable restVariables => by
      show robddListContains newVariable
          (cond (robddNatLess newVariable headVariable)
            (List.cons newVariable (List.cons headVariable restVariables))
            (cond (Nat.beq newVariable headVariable)
              (List.cons headVariable restVariables)
              (List.cons headVariable (robddSortedInsert newVariable restVariables)))) = true
      cases hLessHead : robddNatLess newVariable headVariable with
      | true => exact robddBoolOrIntroLeft _ _ (robddNatBeqRefl newVariable)
      | false =>
          cases hBeqHead : Nat.beq newVariable headVariable with
          | true => exact robddBoolOrIntroLeft _ _ hBeqHead
          | false =>
              exact robddBoolOrIntroRight _ _
                (robddContainsInsertSelf newVariable restVariables)

/-- Insertion keeps every existing member. -/
theorem robddContainsInsertMono (queriedVariable newVariable : Nat) :
    (variableList : List Nat) →
    robddListContains queriedVariable variableList = true →
    robddListContains queriedVariable (robddSortedInsert newVariable variableList) = true
  | List.nil, hContains => Bool.noConfusion hContains
  | List.cons headVariable restVariables, hContains => by
      have hTyped : (Nat.beq queriedVariable headVariable ||
          robddListContains queriedVariable restVariables) = true := hContains
      show robddListContains queriedVariable
          (cond (robddNatLess newVariable headVariable)
            (List.cons newVariable (List.cons headVariable restVariables))
            (cond (Nat.beq newVariable headVariable)
              (List.cons headVariable restVariables)
              (List.cons headVariable (robddSortedInsert newVariable restVariables)))) = true
      cases hLessHead : robddNatLess newVariable headVariable with
      | true => exact robddBoolOrIntroRight _ _ hContains
      | false =>
          cases hBeqHead : Nat.beq newVariable headVariable with
          | true => exact hContains
          | false =>
              cases robddBoolOrElim _ _ hTyped with
              | inl hAtHead => exact robddBoolOrIntroLeft _ _ hAtHead
              | inr hInRest =>
                  exact robddBoolOrIntroRight _ _
                    (robddContainsInsertMono queriedVariable newVariable
                      restVariables hInRest)

/-- Sorted-dedup accumulation of a formula's support. -/
def robddSupportInto : RobddFormula → List Nat → List Nat
  | RobddFormula.falseConst, accumulator => accumulator
  | RobddFormula.trueConst, accumulator => accumulator
  | RobddFormula.variableRef index, accumulator => robddSortedInsert index accumulator
  | RobddFormula.negation operand, accumulator => robddSupportInto operand accumulator
  | RobddFormula.conjunction leftOperand rightOperand, accumulator =>
      robddSupportInto rightOperand (robddSupportInto leftOperand accumulator)
  | RobddFormula.disjunction leftOperand rightOperand, accumulator =>
      robddSupportInto rightOperand (robddSupportInto leftOperand accumulator)
  | RobddFormula.exclusiveOr leftOperand rightOperand, accumulator =>
      robddSupportInto rightOperand (robddSupportInto leftOperand accumulator)

/-- Support accumulation keeps every accumulator member. -/
theorem robddContainsSupportMono (queriedVariable : Nat) : (formula : RobddFormula) →
    (accumulator : List Nat) →
    robddListContains queriedVariable accumulator = true →
    robddListContains queriedVariable (robddSupportInto formula accumulator) = true
  | RobddFormula.falseConst, _, hContains => hContains
  | RobddFormula.trueConst, _, hContains => hContains
  | RobddFormula.variableRef index, accumulator, hContains =>
      robddContainsInsertMono queriedVariable index accumulator hContains
  | RobddFormula.negation operand, accumulator, hContains =>
      robddContainsSupportMono queriedVariable operand accumulator hContains
  | RobddFormula.conjunction leftOperand rightOperand, accumulator, hContains =>
      robddContainsSupportMono queriedVariable rightOperand
        (robddSupportInto leftOperand accumulator)
        (robddContainsSupportMono queriedVariable leftOperand accumulator hContains)
  | RobddFormula.disjunction leftOperand rightOperand, accumulator, hContains =>
      robddContainsSupportMono queriedVariable rightOperand
        (robddSupportInto leftOperand accumulator)
        (robddContainsSupportMono queriedVariable leftOperand accumulator hContains)
  | RobddFormula.exclusiveOr leftOperand rightOperand, accumulator, hContains =>
      robddContainsSupportMono queriedVariable rightOperand
        (robddSupportInto leftOperand accumulator)
        (robddContainsSupportMono queriedVariable leftOperand accumulator hContains)

/-- Support accumulation preserves strict ascending order. -/
theorem robddSupportIntoSorted : (formula : RobddFormula) → (accumulator : List Nat) →
    robddListSortedStrict accumulator = true →
    robddListSortedStrict (robddSupportInto formula accumulator) = true
  | RobddFormula.falseConst, _, hSorted => hSorted
  | RobddFormula.trueConst, _, hSorted => hSorted
  | RobddFormula.variableRef index, accumulator, hSorted =>
      robddSortedInsertPreserves index accumulator hSorted
  | RobddFormula.negation operand, accumulator, hSorted =>
      robddSupportIntoSorted operand accumulator hSorted
  | RobddFormula.conjunction leftOperand rightOperand, accumulator, hSorted =>
      robddSupportIntoSorted rightOperand (robddSupportInto leftOperand accumulator)
        (robddSupportIntoSorted leftOperand accumulator hSorted)
  | RobddFormula.disjunction leftOperand rightOperand, accumulator, hSorted =>
      robddSupportIntoSorted rightOperand (robddSupportInto leftOperand accumulator)
        (robddSupportIntoSorted leftOperand accumulator hSorted)
  | RobddFormula.exclusiveOr leftOperand rightOperand, accumulator, hSorted =>
      robddSupportIntoSorted rightOperand (robddSupportInto leftOperand accumulator)
        (robddSupportIntoSorted leftOperand accumulator hSorted)

/-- Does the list contain every variable the formula mentions? -/
def robddFormulaVarsCovered (variableList : List Nat) : RobddFormula → Bool
  | RobddFormula.falseConst => true
  | RobddFormula.trueConst => true
  | RobddFormula.variableRef index => robddListContains index variableList
  | RobddFormula.negation operand => robddFormulaVarsCovered variableList operand
  | RobddFormula.conjunction leftOperand rightOperand =>
      robddFormulaVarsCovered variableList leftOperand &&
        robddFormulaVarsCovered variableList rightOperand
  | RobddFormula.disjunction leftOperand rightOperand =>
      robddFormulaVarsCovered variableList leftOperand &&
        robddFormulaVarsCovered variableList rightOperand
  | RobddFormula.exclusiveOr leftOperand rightOperand =>
      robddFormulaVarsCovered variableList leftOperand &&
        robddFormulaVarsCovered variableList rightOperand

/-- Coverage is monotone along list inclusion (stated via membership implication). -/
theorem robddCoveredMono (smallList largeList : List Nat)
    (hSubset : (queriedVariable : Nat) →
      robddListContains queriedVariable smallList = true →
      robddListContains queriedVariable largeList = true) :
    (formula : RobddFormula) →
    robddFormulaVarsCovered smallList formula = true →
    robddFormulaVarsCovered largeList formula = true
  | RobddFormula.falseConst, _ => rfl
  | RobddFormula.trueConst, _ => rfl
  | RobddFormula.variableRef index, hCovered => hSubset index hCovered
  | RobddFormula.negation operand, hCovered =>
      robddCoveredMono smallList largeList hSubset operand hCovered
  | RobddFormula.conjunction leftOperand rightOperand, hCovered => by
      have hTyped : (robddFormulaVarsCovered smallList leftOperand &&
          robddFormulaVarsCovered smallList rightOperand) = true := hCovered
      have hSplit := robddBoolAndElim _ _ hTyped
      exact robddBoolAndIntro _ _
        (robddCoveredMono smallList largeList hSubset leftOperand hSplit.left)
        (robddCoveredMono smallList largeList hSubset rightOperand hSplit.right)
  | RobddFormula.disjunction leftOperand rightOperand, hCovered => by
      have hTyped : (robddFormulaVarsCovered smallList leftOperand &&
          robddFormulaVarsCovered smallList rightOperand) = true := hCovered
      have hSplit := robddBoolAndElim _ _ hTyped
      exact robddBoolAndIntro _ _
        (robddCoveredMono smallList largeList hSubset leftOperand hSplit.left)
        (robddCoveredMono smallList largeList hSubset rightOperand hSplit.right)
  | RobddFormula.exclusiveOr leftOperand rightOperand, hCovered => by
      have hTyped : (robddFormulaVarsCovered smallList leftOperand &&
          robddFormulaVarsCovered smallList rightOperand) = true := hCovered
      have hSplit := robddBoolAndElim _ _ hTyped
      exact robddBoolAndIntro _ _
        (robddCoveredMono smallList largeList hSubset leftOperand hSplit.left)
        (robddCoveredMono smallList largeList hSubset rightOperand hSplit.right)

/-- Accumulating a formula's support covers that formula. -/
theorem robddSupportIntoCovers : (formula : RobddFormula) → (accumulator : List Nat) →
    robddFormulaVarsCovered (robddSupportInto formula accumulator) formula = true
  | RobddFormula.falseConst, _ => rfl
  | RobddFormula.trueConst, _ => rfl
  | RobddFormula.variableRef index, accumulator => robddContainsInsertSelf index accumulator
  | RobddFormula.negation operand, accumulator => robddSupportIntoCovers operand accumulator
  | RobddFormula.conjunction leftOperand rightOperand, accumulator => by
      exact robddBoolAndIntro _ _
        (robddCoveredMono (robddSupportInto leftOperand accumulator)
          (robddSupportInto rightOperand (robddSupportInto leftOperand accumulator))
          (fun queriedVariable hMember => robddContainsSupportMono queriedVariable
            rightOperand (robddSupportInto leftOperand accumulator) hMember)
          leftOperand (robddSupportIntoCovers leftOperand accumulator))
        (robddSupportIntoCovers rightOperand (robddSupportInto leftOperand accumulator))
  | RobddFormula.disjunction leftOperand rightOperand, accumulator => by
      exact robddBoolAndIntro _ _
        (robddCoveredMono (robddSupportInto leftOperand accumulator)
          (robddSupportInto rightOperand (robddSupportInto leftOperand accumulator))
          (fun queriedVariable hMember => robddContainsSupportMono queriedVariable
            rightOperand (robddSupportInto leftOperand accumulator) hMember)
          leftOperand (robddSupportIntoCovers leftOperand accumulator))
        (robddSupportIntoCovers rightOperand (robddSupportInto leftOperand accumulator))
  | RobddFormula.exclusiveOr leftOperand rightOperand, accumulator => by
      exact robddBoolAndIntro _ _
        (robddCoveredMono (robddSupportInto leftOperand accumulator)
          (robddSupportInto rightOperand (robddSupportInto leftOperand accumulator))
          (fun queriedVariable hMember => robddContainsSupportMono queriedVariable
            rightOperand (robddSupportInto leftOperand accumulator) hMember)
          leftOperand (robddSupportIntoCovers leftOperand accumulator))
        (robddSupportIntoCovers rightOperand (robddSupportInto leftOperand accumulator))

/-- Restriction at the head keeps the formula covered by the tail list. -/
theorem robddRestrictCovered (targetVariable : Nat) (newValue : Bool)
    (restVariables : List Nat) : (formula : RobddFormula) →
    robddFormulaVarsCovered (List.cons targetVariable restVariables) formula = true →
    robddFormulaVarsCovered restVariables
      (robddRestrict targetVariable newValue formula) = true
  | RobddFormula.falseConst, _ => rfl
  | RobddFormula.trueConst, _ => rfl
  | RobddFormula.variableRef index, hCovered => by
      have hTyped : (Nat.beq index targetVariable ||
          robddListContains index restVariables) = true := hCovered
      show robddFormulaVarsCovered restVariables
          (cond (Nat.beq index targetVariable)
            (cond newValue RobddFormula.trueConst RobddFormula.falseConst)
            (RobddFormula.variableRef index)) = true
      cases hBeq : Nat.beq index targetVariable with
      | true =>
          cases newValue with
          | true => rfl
          | false => rfl
      | false =>
          rw [hBeq] at hTyped
          exact hTyped
  | RobddFormula.negation operand, hCovered =>
      robddRestrictCovered targetVariable newValue restVariables operand hCovered
  | RobddFormula.conjunction leftOperand rightOperand, hCovered => by
      have hTyped : (robddFormulaVarsCovered (List.cons targetVariable restVariables)
          leftOperand &&
          robddFormulaVarsCovered (List.cons targetVariable restVariables) rightOperand)
          = true := hCovered
      have hSplit := robddBoolAndElim _ _ hTyped
      exact robddBoolAndIntro _ _
        (robddRestrictCovered targetVariable newValue restVariables leftOperand hSplit.left)
        (robddRestrictCovered targetVariable newValue restVariables rightOperand hSplit.right)
  | RobddFormula.disjunction leftOperand rightOperand, hCovered => by
      have hTyped : (robddFormulaVarsCovered (List.cons targetVariable restVariables)
          leftOperand &&
          robddFormulaVarsCovered (List.cons targetVariable restVariables) rightOperand)
          = true := hCovered
      have hSplit := robddBoolAndElim _ _ hTyped
      exact robddBoolAndIntro _ _
        (robddRestrictCovered targetVariable newValue restVariables leftOperand hSplit.left)
        (robddRestrictCovered targetVariable newValue restVariables rightOperand hSplit.right)
  | RobddFormula.exclusiveOr leftOperand rightOperand, hCovered => by
      have hTyped : (robddFormulaVarsCovered (List.cons targetVariable restVariables)
          leftOperand &&
          robddFormulaVarsCovered (List.cons targetVariable restVariables) rightOperand)
          = true := hCovered
      have hSplit := robddBoolAndElim _ _ hTyped
      exact robddBoolAndIntro _ _
        (robddRestrictCovered targetVariable newValue restVariables leftOperand hSplit.left)
        (robddRestrictCovered targetVariable newValue restVariables rightOperand hSplit.right)

/-- A formula covered by the empty list evaluates identically under any two
environments. -/
theorem robddCoveredNilConst : (formula : RobddFormula) →
    robddFormulaVarsCovered List.nil formula = true →
    (envFirst envSecond : Nat → Bool) →
    robddFormulaEval envFirst formula = robddFormulaEval envSecond formula
  | RobddFormula.falseConst, _, _, _ => rfl
  | RobddFormula.trueConst, _, _, _ => rfl
  | RobddFormula.variableRef _, hCovered, _, _ => Bool.noConfusion hCovered
  | RobddFormula.negation operand, hCovered, envFirst, envSecond =>
      congrArg Bool.not (robddCoveredNilConst operand hCovered envFirst envSecond)
  | RobddFormula.conjunction leftOperand rightOperand, hCovered, envFirst, envSecond => by
      have hTyped : (robddFormulaVarsCovered List.nil leftOperand &&
          robddFormulaVarsCovered List.nil rightOperand) = true := hCovered
      have hSplit := robddBoolAndElim _ _ hTyped
      show (robddFormulaEval envFirst leftOperand && robddFormulaEval envFirst rightOperand)
          = (robddFormulaEval envSecond leftOperand && robddFormulaEval envSecond rightOperand)
      rw [robddCoveredNilConst leftOperand hSplit.left envFirst envSecond,
          robddCoveredNilConst rightOperand hSplit.right envFirst envSecond]
  | RobddFormula.disjunction leftOperand rightOperand, hCovered, envFirst, envSecond => by
      have hTyped : (robddFormulaVarsCovered List.nil leftOperand &&
          robddFormulaVarsCovered List.nil rightOperand) = true := hCovered
      have hSplit := robddBoolAndElim _ _ hTyped
      show (robddFormulaEval envFirst leftOperand || robddFormulaEval envFirst rightOperand)
          = (robddFormulaEval envSecond leftOperand || robddFormulaEval envSecond rightOperand)
      rw [robddCoveredNilConst leftOperand hSplit.left envFirst envSecond,
          robddCoveredNilConst rightOperand hSplit.right envFirst envSecond]
  | RobddFormula.exclusiveOr leftOperand rightOperand, hCovered, envFirst, envSecond => by
      have hTyped : (robddFormulaVarsCovered List.nil leftOperand &&
          robddFormulaVarsCovered List.nil rightOperand) = true := hCovered
      have hSplit := robddBoolAndElim _ _ hTyped
      show robddBoolXor (robddFormulaEval envFirst leftOperand)
            (robddFormulaEval envFirst rightOperand)
          = robddBoolXor (robddFormulaEval envSecond leftOperand)
            (robddFormulaEval envSecond rightOperand)
      rw [robddCoveredNilConst leftOperand hSplit.left envFirst envSecond,
          robddCoveredNilConst rightOperand hSplit.right envFirst envSecond]

/-! ## The builder: Shannon expansion over an explicit support list -/

/-- Smart branch constructor: collapse when both children are beq-equal. -/
def robddMkBranch (variableIndex : Nat) (lowChild highChild : RobddTree) : RobddTree :=
  cond (robddTreeBeq lowChild highChild) lowChild
    (RobddTree.branch variableIndex lowChild highChild)

/-- `robddMkBranch` evaluates like a genuine branch (collapse is semantically silent). -/
theorem robddMkBranchEval (variableIndex : Nat) (lowChild highChild : RobddTree)
    (env : Nat → Bool) :
    robddEval env (robddMkBranch variableIndex lowChild highChild)
      = cond (env variableIndex) (robddEval env highChild) (robddEval env lowChild) := by
  show robddEval env (cond (robddTreeBeq lowChild highChild) lowChild
      (RobddTree.branch variableIndex lowChild highChild))
      = cond (env variableIndex) (robddEval env highChild) (robddEval env lowChild)
  cases hBeq : robddTreeBeq lowChild highChild with
  | true =>
      have hChildrenEqual : lowChild = highChild := robddTreeBeqEq lowChild highChild hBeq
      rw [hChildrenEqual]
      exact Eq.symm (robddBoolCondSame (env variableIndex) (robddEval env highChild))
  | false => rfl

/-- `robddMkBranch` stays above any bound its inputs respect. -/
theorem robddMkBranchAllVarsAbove (bound variableIndex : Nat) (lowChild highChild : RobddTree)
    (hVarAbove : robddNatLess bound variableIndex = true)
    (hLowAbove : robddAllVarsAbove bound lowChild = true)
    (hHighAbove : robddAllVarsAbove bound highChild = true) :
    robddAllVarsAbove bound (robddMkBranch variableIndex lowChild highChild) = true := by
  show robddAllVarsAbove bound (cond (robddTreeBeq lowChild highChild) lowChild
      (RobddTree.branch variableIndex lowChild highChild)) = true
  cases hBeq : robddTreeBeq lowChild highChild with
  | true => exact hLowAbove
  | false =>
      exact robddBoolAndIntro _ _ hVarAbove (robddBoolAndIntro _ _ hLowAbove hHighAbove)

/-- `robddMkBranch` is ordered when its children are ordered and above the root. -/
theorem robddMkBranchOrdered (variableIndex : Nat) (lowChild highChild : RobddTree)
    (hLowAbove : robddAllVarsAbove variableIndex lowChild = true)
    (hHighAbove : robddAllVarsAbove variableIndex highChild = true)
    (hLowOrdered : robddIsOrdered lowChild = true)
    (hHighOrdered : robddIsOrdered highChild = true) :
    robddIsOrdered (robddMkBranch variableIndex lowChild highChild) = true := by
  show robddIsOrdered (cond (robddTreeBeq lowChild highChild) lowChild
      (RobddTree.branch variableIndex lowChild highChild)) = true
  cases hBeq : robddTreeBeq lowChild highChild with
  | true => exact hLowOrdered
  | false =>
      exact robddBoolAndIntro _ _ hLowAbove (robddBoolAndIntro _ _ hHighAbove
        (robddBoolAndIntro _ _ hLowOrdered hHighOrdered))

/-- `robddMkBranch` is reduced when its children are — collapse kills equal siblings. -/
theorem robddMkBranchReduced (variableIndex : Nat) (lowChild highChild : RobddTree)
    (hLowReduced : robddIsReduced lowChild = true)
    (hHighReduced : robddIsReduced highChild = true) :
    robddIsReduced (robddMkBranch variableIndex lowChild highChild) = true := by
  show robddIsReduced (cond (robddTreeBeq lowChild highChild) lowChild
      (RobddTree.branch variableIndex lowChild highChild)) = true
  cases hBeq : robddTreeBeq lowChild highChild with
  | true => exact hLowReduced
  | false =>
      have hNotBeq : (!robddTreeBeq lowChild highChild) = true := by
        rw [hBeq]
        rfl
      exact robddBoolAndIntro _ _ hNotBeq
        (robddBoolAndIntro _ _ hLowReduced hHighReduced)

/-- Shannon-expansion builder over an explicit variable list: at each head, restrict the
formula both ways and combine with the smart constructor; on the empty list, evaluate the
(now closed, if the list covered the formula) formula under the all-false environment. -/
def robddBuildOver : List Nat → RobddFormula → RobddTree
  | List.nil, formula => RobddTree.leaf (robddFormulaEval (fun _ => false) formula)
  | List.cons headVariable restVariables, formula =>
      robddMkBranch headVariable
        (robddBuildOver restVariables (robddRestrict headVariable false formula))
        (robddBuildOver restVariables (robddRestrict headVariable true formula))

/-- Built trees test only variables strictly above any bound bounding the list. -/
theorem robddBuildOverAllVarsAbove (bound : Nat) : (variableList : List Nat) →
    (formula : RobddFormula) → robddListAllAbove bound variableList = true →
    robddAllVarsAbove bound (robddBuildOver variableList formula) = true
  | List.nil, _, _ => rfl
  | List.cons headVariable restVariables, formula, hAllAbove => by
      have hTyped : (robddNatLess bound headVariable &&
          robddListAllAbove bound restVariables) = true := hAllAbove
      have hSplit := robddBoolAndElim _ _ hTyped
      exact robddMkBranchAllVarsAbove bound headVariable
        (robddBuildOver restVariables (robddRestrict headVariable false formula))
        (robddBuildOver restVariables (robddRestrict headVariable true formula))
        hSplit.left
        (robddBuildOverAllVarsAbove bound restVariables
          (robddRestrict headVariable false formula) hSplit.right)
        (robddBuildOverAllVarsAbove bound restVariables
          (robddRestrict headVariable true formula) hSplit.right)

/-- Built trees are ordered whenever the variable list is strictly ascending. -/
theorem robddBuildOverOrdered : (variableList : List Nat) → (formula : RobddFormula) →
    robddListSortedStrict variableList = true →
    robddIsOrdered (robddBuildOver variableList formula) = true
  | List.nil, _, _ => rfl
  | List.cons headVariable restVariables, formula, hSorted => by
      have hTyped : (robddListAllAbove headVariable restVariables &&
          robddListSortedStrict restVariables) = true := hSorted
      have hSplit := robddBoolAndElim _ _ hTyped
      exact robddMkBranchOrdered headVariable
        (robddBuildOver restVariables (robddRestrict headVariable false formula))
        (robddBuildOver restVariables (robddRestrict headVariable true formula))
        (robddBuildOverAllVarsAbove headVariable restVariables
          (robddRestrict headVariable false formula) hSplit.left)
        (robddBuildOverAllVarsAbove headVariable restVariables
          (robddRestrict headVariable true formula) hSplit.left)
        (robddBuildOverOrdered restVariables
          (robddRestrict headVariable false formula) hSplit.right)
        (robddBuildOverOrdered restVariables
          (robddRestrict headVariable true formula) hSplit.right)

/-- Built trees are reduced unconditionally — the smart constructor collapses. -/
theorem robddBuildOverReduced : (variableList : List Nat) → (formula : RobddFormula) →
    robddIsReduced (robddBuildOver variableList formula) = true
  | List.nil, _ => rfl
  | List.cons headVariable restVariables, formula =>
      robddMkBranchReduced headVariable
        (robddBuildOver restVariables (robddRestrict headVariable false formula))
        (robddBuildOver restVariables (robddRestrict headVariable true formula))
        (robddBuildOverReduced restVariables (robddRestrict headVariable false formula))
        (robddBuildOverReduced restVariables (robddRestrict headVariable true formula))

/-- Built trees are canonical whenever the variable list is strictly ascending. -/
theorem robddBuildOverCanonical (variableList : List Nat) (formula : RobddFormula)
    (hSorted : robddListSortedStrict variableList = true) :
    robddIsCanonical (robddBuildOver variableList formula) = true :=
  robddBoolAndIntro _ _ (robddBuildOverOrdered variableList formula hSorted)
    (robddBuildOverReduced variableList formula)

/-- **Evaluation correctness**: over any covering variable list, the built tree computes
the formula, pointwise in the environment. -/
theorem robddBuildOverEval : (variableList : List Nat) → (formula : RobddFormula) →
    robddFormulaVarsCovered variableList formula = true → (env : Nat → Bool) →
    robddEval env (robddBuildOver variableList formula) = robddFormulaEval env formula
  | List.nil, formula, hCovered, env =>
      robddCoveredNilConst formula hCovered (fun _ => false) env
  | List.cons headVariable restVariables, formula, hCovered, env => by
      have hLowEval : robddEval env
          (robddBuildOver restVariables (robddRestrict headVariable false formula))
          = robddFormulaEval (robddEnvUpdate env headVariable false) formula :=
        Eq.trans
          (robddBuildOverEval restVariables (robddRestrict headVariable false formula)
            (robddRestrictCovered headVariable false restVariables formula hCovered) env)
          (robddRestrictEval headVariable false formula env)
      have hHighEval : robddEval env
          (robddBuildOver restVariables (robddRestrict headVariable true formula))
          = robddFormulaEval (robddEnvUpdate env headVariable true) formula :=
        Eq.trans
          (robddBuildOverEval restVariables (robddRestrict headVariable true formula)
            (robddRestrictCovered headVariable true restVariables formula hCovered) env)
          (robddRestrictEval headVariable true formula env)
      have hCondEqual : cond (env headVariable)
            (robddEval env
              (robddBuildOver restVariables (robddRestrict headVariable true formula)))
            (robddEval env
              (robddBuildOver restVariables (robddRestrict headVariable false formula)))
          = cond (env headVariable)
            (robddFormulaEval (robddEnvUpdate env headVariable true) formula)
            (robddFormulaEval (robddEnvUpdate env headVariable false) formula) := by
        rw [hLowEval, hHighEval]
      exact Eq.trans
        (robddMkBranchEval headVariable
          (robddBuildOver restVariables (robddRestrict headVariable false formula))
          (robddBuildOver restVariables (robddRestrict headVariable true formula)) env)
        (Eq.trans hCondEqual (robddShannonExpansion headVariable formula env))

/-! ## The decision -/

/-- Merged support of a formula pair (needed only for evaluation coverage of both). -/
def robddMergedSupport (formulaA formulaB : RobddFormula) : List Nat :=
  robddSupportInto formulaB (robddSupportInto formulaA List.nil)

/-- The merged support is strictly ascending. -/
theorem robddMergedSupportSorted (formulaA formulaB : RobddFormula) :
    robddListSortedStrict (robddMergedSupport formulaA formulaB) = true :=
  robddSupportIntoSorted formulaB (robddSupportInto formulaA List.nil)
    (robddSupportIntoSorted formulaA List.nil rfl)

/-- The merged support covers the left formula. -/
theorem robddMergedSupportCoversLeft (formulaA formulaB : RobddFormula) :
    robddFormulaVarsCovered (robddMergedSupport formulaA formulaB) formulaA = true :=
  robddCoveredMono (robddSupportInto formulaA List.nil)
    (robddMergedSupport formulaA formulaB)
    (fun queriedVariable hMember => robddContainsSupportMono queriedVariable formulaB
      (robddSupportInto formulaA List.nil) hMember)
    formulaA (robddSupportIntoCovers formulaA List.nil)

/-- The merged support covers the right formula. -/
theorem robddMergedSupportCoversRight (formulaA formulaB : RobddFormula) :
    robddFormulaVarsCovered (robddMergedSupport formulaA formulaB) formulaB = true :=
  robddSupportIntoCovers formulaB (robddSupportInto formulaA List.nil)

/-- **The decision procedure**: build both trees over the merged support, compare
structurally. -/
def robddDecideEquiv (formulaA formulaB : RobddFormula) : Bool :=
  robddTreeBeq
    (robddBuildOver (robddMergedSupport formulaA formulaB) formulaA)
    (robddBuildOver (robddMergedSupport formulaA formulaB) formulaB)

/-- **The biconditional**: pointwise formula equivalence iff the decision bit is `true`.
Forward = canonicity of the two built trees; backward = beq soundness plus evaluation
correctness both ways.  No `funext`: the Pi over environments is proven pointwise and
used by application only. -/
theorem robddEquivIffDecide (formulaA formulaB : RobddFormula) :
    ((env : Nat → Bool) → robddFormulaEval env formulaA = robddFormulaEval env formulaB) ↔
      robddDecideEquiv formulaA formulaB = true := by
  constructor
  · intro hEquiv
    have hTreesEqual : robddBuildOver (robddMergedSupport formulaA formulaB) formulaA
        = robddBuildOver (robddMergedSupport formulaA formulaB) formulaB :=
      robddCanonicalUnique
        (robddBuildOver (robddMergedSupport formulaA formulaB) formulaA)
        (robddBuildOver (robddMergedSupport formulaA formulaB) formulaB)
        (robddBuildOverCanonical (robddMergedSupport formulaA formulaB) formulaA
          (robddMergedSupportSorted formulaA formulaB))
        (robddBuildOverCanonical (robddMergedSupport formulaA formulaB) formulaB
          (robddMergedSupportSorted formulaA formulaB))
        (fun env => Eq.trans
          (robddBuildOverEval (robddMergedSupport formulaA formulaB) formulaA
            (robddMergedSupportCoversLeft formulaA formulaB) env)
          (Eq.trans (hEquiv env)
            (Eq.symm (robddBuildOverEval (robddMergedSupport formulaA formulaB) formulaB
              (robddMergedSupportCoversRight formulaA formulaB) env))))
    show robddTreeBeq
        (robddBuildOver (robddMergedSupport formulaA formulaB) formulaA)
        (robddBuildOver (robddMergedSupport formulaA formulaB) formulaB) = true
    rw [hTreesEqual]
    exact robddTreeBeqRefl (robddBuildOver (robddMergedSupport formulaA formulaB) formulaB)
  · intro hDecide env
    have hTreesEqual : robddBuildOver (robddMergedSupport formulaA formulaB) formulaA
        = robddBuildOver (robddMergedSupport formulaA formulaB) formulaB :=
      robddTreeBeqEq _ _ hDecide
    exact Eq.trans
      (Eq.symm (robddBuildOverEval (robddMergedSupport formulaA formulaB) formulaA
        (robddMergedSupportCoversLeft formulaA formulaB) env))
      (Eq.trans (congrArg (robddEval env) hTreesEqual)
        (robddBuildOverEval (robddMergedSupport formulaA formulaB) formulaB
          (robddMergedSupportCoversRight formulaA formulaB) env))

/-- Pointwise Boolean-formula equivalence is decidable — by computation, no classical
axioms. -/
instance robddFormulaEquivDecidable (formulaA formulaB : RobddFormula) :
    Decidable ((env : Nat → Bool) →
      robddFormulaEval env formulaA = robddFormulaEval env formulaB) :=
  match hDecide : robddDecideEquiv formulaA formulaB with
  | true => isTrue ((robddEquivIffDecide formulaA formulaB).mpr hDecide)
  | false => isFalse (fun hEquiv => Bool.noConfusion
      (hDecide.symm.trans ((robddEquivIffDecide formulaA formulaB).mp hEquiv)))

/-- Marker: the ROBDD half of canonical Boolean-equivalence decision is DECIDED —
canonicity + biconditional + `Decidable` instance. -/
def fxDissatBool_hasRobddDecision : Bool := true

/-! ## Smoke tests (genuineness pins, false cases included)

Variables: `0 = x`, `1 = y`. -/

/- `(x ∧ y) ∨ (x ∧ ¬y) ≡ x` — expect `true`. -/
#eval robddDecideEquiv
  (RobddFormula.disjunction
    (RobddFormula.conjunction (RobddFormula.variableRef 0) (RobddFormula.variableRef 1))
    (RobddFormula.conjunction (RobddFormula.variableRef 0)
      (RobddFormula.negation (RobddFormula.variableRef 1))))
  (RobddFormula.variableRef 0)

/- `x ⊕ y ≡ (x ∨ y) ∧ ¬(x ∧ y)` — expect `true`. -/
#eval robddDecideEquiv
  (RobddFormula.exclusiveOr (RobddFormula.variableRef 0) (RobddFormula.variableRef 1))
  (RobddFormula.conjunction
    (RobddFormula.disjunction (RobddFormula.variableRef 0) (RobddFormula.variableRef 1))
    (RobddFormula.negation
      (RobddFormula.conjunction (RobddFormula.variableRef 0) (RobddFormula.variableRef 1))))

/- `x ≢ y` — expect `false`. -/
#eval robddDecideEquiv (RobddFormula.variableRef 0) (RobddFormula.variableRef 1)

/- `x ∧ ¬x ≡ false` — expect `true`. -/
#eval robddDecideEquiv
  (RobddFormula.conjunction (RobddFormula.variableRef 0)
    (RobddFormula.negation (RobddFormula.variableRef 0)))
  RobddFormula.falseConst

/- `x ∨ ¬x ≡ true` — expect `true`. -/
#eval robddDecideEquiv
  (RobddFormula.disjunction (RobddFormula.variableRef 0)
    (RobddFormula.negation (RobddFormula.variableRef 0)))
  RobddFormula.trueConst

/- `x ≢ ¬x` — expect `false`. -/
#eval robddDecideEquiv (RobddFormula.variableRef 0)
  (RobddFormula.negation (RobddFormula.variableRef 0))

/- De Morgan: `¬(x ∧ y) ≡ ¬x ∨ ¬y` — expect `true`. -/
#eval robddDecideEquiv
  (RobddFormula.negation
    (RobddFormula.conjunction (RobddFormula.variableRef 0) (RobddFormula.variableRef 1)))
  (RobddFormula.disjunction
    (RobddFormula.negation (RobddFormula.variableRef 0))
    (RobddFormula.negation (RobddFormula.variableRef 1)))

/- Structural pin: the tree built for `x ⊕ y` is the genuine two-level branch
`branch 0 (branch 1 (leaf false) (leaf true)) (branch 1 (leaf true) (leaf false))` —
expect `true`. -/
#eval robddTreeBeq
  (robddBuildOver
    (robddMergedSupport
      (RobddFormula.exclusiveOr (RobddFormula.variableRef 0) (RobddFormula.variableRef 1))
      (RobddFormula.exclusiveOr (RobddFormula.variableRef 0) (RobddFormula.variableRef 1)))
    (RobddFormula.exclusiveOr (RobddFormula.variableRef 0) (RobddFormula.variableRef 1)))
  (RobddTree.branch 0
    (RobddTree.branch 1 (RobddTree.leaf false) (RobddTree.leaf true))
    (RobddTree.branch 1 (RobddTree.leaf true) (RobddTree.leaf false)))

/- Structural pin, negative: that same tree is NOT the collapsed constant — expect
`false`. -/
#eval robddTreeBeq
  (robddBuildOver
    (robddMergedSupport
      (RobddFormula.exclusiveOr (RobddFormula.variableRef 0) (RobddFormula.variableRef 1))
      (RobddFormula.exclusiveOr (RobddFormula.variableRef 0) (RobddFormula.variableRef 1)))
    (RobddFormula.exclusiveOr (RobddFormula.variableRef 0) (RobddFormula.variableRef 1)))
  (RobddTree.leaf false)

end FX1Poly.ComputerAlgebra
