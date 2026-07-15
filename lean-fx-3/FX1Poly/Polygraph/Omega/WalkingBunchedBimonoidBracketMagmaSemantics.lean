import FX1Poly.Polygraph.Omega.WalkingBunchedBimonoidStarUnitalRestatement

/-! # Polygraph/Omega/WalkingBunchedBimonoidBracketMagmaSemantics — the BRACKET-MAGMA semantics: the free
commutative unital magma sees the association order the matrices (plain AND affine) cannot (WP-PROP r31, #2033)

★★ **THE THIRD INVARIANT.**  The plain `Mat(N)` semantics is blind to swallowed units (r30 decided that hole);
the r30 affine-offset semantics is blind to ASSOCIATION ORDERS: `(mu |> a) ; mu` and `(a <| mu) ; mu` share the
plain matrix `[[1,1,1]]` AND the augmented matrix `[[1,0,0,0],[0,1,1,1]]`.  This file builds the semantics that
separates them: 2-cells evaluate to FUNCTIONS on lists of BRACKET TREES — elements of the free commutative
unital magma in canonical form (`pairNode` children ordered by a total structural comparator, units absorbed by
the smart constructor `bunchedBimonoidBracketMul`).  The multiplication `mu_a` multiplies in the magma, the
comultiplication duplicates, the swap swaps, the (co)units insert/discard the magma unit — so EVERY row of the
unital star scope holds pointwise (commutativity via the canonical ordering; the unit rows via unit absorption)
while `(x * y) * z` and `x * (y * z)` remain DISTINCT canonical trees.

The absorber is composability-GATED exactly like the r30 affine absorber (the strict rows are false on junk
instances): the target relation carries (i) the r30 Clean-gate equivalence — its per-row proofs REUSED from the
shipped `bunchedBimonoidAugGated*` lemmas by projection, (ii) ungated declared-boundary-width agreement, and
(iii) the pointwise evaluation agreement on Clean cells at declared-source-width argument lists.

The sibling `WalkingBunchedBimonoidStarAssocLawRefutation` fires this invariant to DECIDE the unital star.

Raw Lean 4 + Init; STRUCTURAL only; ASCII-only.  Per-declaration `#assert_no_axioms` AND independent
`#print axioms` gated in the audit twin. -/

namespace FX1Poly.Polygraph.Omega

set_option maxHeartbeats 4000000

/-! # =========================================================================================
    # A — THE BRACKET-TREE CARRIER: the free commutative unital magma in canonical form
    # =========================================================================================
-/

/-- ★ **A bracket tree** — an element of the free commutative unital magma on countably many variables:
the unit, a variable leaf, or an unordered pair (kept canonical: smaller child first under the structural
comparator; the smart constructor `bunchedBimonoidBracketMul` maintains canonicity and absorbs units). -/
inductive BunchedBimonoidBracketTree where
  /-- The magma unit (the value of `eta_a`). -/
  | unitLeaf
  /-- A variable (one input strand). -/
  | varLeaf (variableIndex : Nat)
  /-- A product node — the two factors, canonically ordered. -/
  | pairNode (leftFactor rightFactor : BunchedBimonoidBracketTree)

/-- Structural `Nat` comparison (hand-rolled; propext-clean). -/
def bunchedBimonoidBracketNatCompare : Nat → Nat → Ordering
  | 0, 0 => .eq
  | 0, _ + 1 => .lt
  | _ + 1, 0 => .gt
  | leftPred + 1, rightPred + 1 => bunchedBimonoidBracketNatCompare leftPred rightPred

/-- The order flip. -/
def bunchedBimonoidBracketOrderingFlip : Ordering → Ordering
  | .lt => .gt
  | .eq => .eq
  | .gt => .lt

/-- ★ The **total structural comparator** on bracket trees: `unitLeaf < varLeaf _ < pairNode _ _`, variables
by index, pairs lexicographically. -/
def bunchedBimonoidBracketTreeCompare :
    BunchedBimonoidBracketTree → BunchedBimonoidBracketTree → Ordering
  | .unitLeaf, .unitLeaf => .eq
  | .unitLeaf, .varLeaf _ => .lt
  | .unitLeaf, .pairNode _ _ => .lt
  | .varLeaf _, .unitLeaf => .gt
  | .varLeaf leftIndex, .varLeaf rightIndex => bunchedBimonoidBracketNatCompare leftIndex rightIndex
  | .varLeaf _, .pairNode _ _ => .lt
  | .pairNode _ _, .unitLeaf => .gt
  | .pairNode _ _, .varLeaf _ => .gt
  | .pairNode leftLeft leftRight, .pairNode rightLeft rightRight =>
      match bunchedBimonoidBracketTreeCompare leftLeft rightLeft with
      | .lt => .lt
      | .gt => .gt
      | .eq => bunchedBimonoidBracketTreeCompare leftRight rightRight

/-- `Nat` comparison antisymmetry: swapping the arguments flips the ordering. -/
theorem bunchedBimonoidBracketNatCompareFlip : (leftValue rightValue : Nat) →
    bunchedBimonoidBracketNatCompare rightValue leftValue
      = bunchedBimonoidBracketOrderingFlip (bunchedBimonoidBracketNatCompare leftValue rightValue)
  | 0, 0 => rfl
  | 0, _ + 1 => rfl
  | _ + 1, 0 => rfl
  | leftPred + 1, rightPred + 1 => bunchedBimonoidBracketNatCompareFlip leftPred rightPred

/-- `Nat` comparison reflects equality. -/
theorem bunchedBimonoidBracketNatCompareEqExtract : (leftValue rightValue : Nat) →
    bunchedBimonoidBracketNatCompare leftValue rightValue = .eq → leftValue = rightValue
  | 0, 0, _ => rfl
  | 0, _ + 1, absurdEq => Ordering.noConfusion absurdEq
  | _ + 1, 0, absurdEq => Ordering.noConfusion absurdEq
  | leftPred + 1, rightPred + 1, headEq =>
      congrArg Nat.succ (bunchedBimonoidBracketNatCompareEqExtract leftPred rightPred headEq)

/-- ★ Tree comparison antisymmetry: swapping the arguments flips the ordering. -/
theorem bunchedBimonoidBracketTreeCompareFlip : (leftTree rightTree : BunchedBimonoidBracketTree) →
    bunchedBimonoidBracketTreeCompare rightTree leftTree
      = bunchedBimonoidBracketOrderingFlip (bunchedBimonoidBracketTreeCompare leftTree rightTree)
  | .unitLeaf, .unitLeaf => rfl
  | .unitLeaf, .varLeaf _ => rfl
  | .unitLeaf, .pairNode _ _ => rfl
  | .varLeaf _, .unitLeaf => rfl
  | .varLeaf leftIndex, .varLeaf rightIndex =>
      bunchedBimonoidBracketNatCompareFlip leftIndex rightIndex
  | .varLeaf _, .pairNode _ _ => rfl
  | .pairNode _ _, .unitLeaf => rfl
  | .pairNode _ _, .varLeaf _ => rfl
  | .pairNode leftLeft leftRight, .pairNode rightLeft rightRight => by
      have headFlip := bunchedBimonoidBracketTreeCompareFlip leftLeft rightLeft
      have tailFlip := bunchedBimonoidBracketTreeCompareFlip leftRight rightRight
      show (match bunchedBimonoidBracketTreeCompare rightLeft leftLeft with
          | .lt => Ordering.lt
          | .gt => Ordering.gt
          | .eq => bunchedBimonoidBracketTreeCompare rightRight leftRight)
        = bunchedBimonoidBracketOrderingFlip
            (match bunchedBimonoidBracketTreeCompare leftLeft rightLeft with
              | .lt => Ordering.lt
              | .gt => Ordering.gt
              | .eq => bunchedBimonoidBracketTreeCompare leftRight rightRight)
      rw [headFlip]
      match bunchedBimonoidBracketTreeCompare leftLeft rightLeft with
      | .lt => rfl
      | .gt => rfl
      | .eq => exact tailFlip

/-- ★ Tree comparison reflects equality. -/
theorem bunchedBimonoidBracketTreeCompareEqExtract : (leftTree rightTree : BunchedBimonoidBracketTree) →
    bunchedBimonoidBracketTreeCompare leftTree rightTree = .eq → leftTree = rightTree
  | .unitLeaf, .unitLeaf, _ => rfl
  | .unitLeaf, .varLeaf _, absurdEq => Ordering.noConfusion absurdEq
  | .unitLeaf, .pairNode _ _, absurdEq => Ordering.noConfusion absurdEq
  | .varLeaf _, .unitLeaf, absurdEq => Ordering.noConfusion absurdEq
  | .varLeaf leftIndex, .varLeaf rightIndex, indexEq =>
      congrArg BunchedBimonoidBracketTree.varLeaf
        (bunchedBimonoidBracketNatCompareEqExtract leftIndex rightIndex indexEq)
  | .varLeaf _, .pairNode _ _, absurdEq => Ordering.noConfusion absurdEq
  | .pairNode _ _, .unitLeaf, absurdEq => Ordering.noConfusion absurdEq
  | .pairNode _ _, .varLeaf _, absurdEq => Ordering.noConfusion absurdEq
  | .pairNode leftLeft leftRight, .pairNode rightLeft rightRight, pairEq => by
      match headOrder : bunchedBimonoidBracketTreeCompare leftLeft rightLeft with
      | .lt =>
          have reduced : Ordering.lt = Ordering.eq := by
            have shaped : (match bunchedBimonoidBracketTreeCompare leftLeft rightLeft with
                | .lt => Ordering.lt
                | .gt => Ordering.gt
                | .eq => bunchedBimonoidBracketTreeCompare leftRight rightRight) = .eq := pairEq
            rw [headOrder] at shaped
            exact shaped
          exact Ordering.noConfusion reduced
      | .gt =>
          have reduced : Ordering.gt = Ordering.eq := by
            have shaped : (match bunchedBimonoidBracketTreeCompare leftLeft rightLeft with
                | .lt => Ordering.lt
                | .gt => Ordering.gt
                | .eq => bunchedBimonoidBracketTreeCompare leftRight rightRight) = .eq := pairEq
            rw [headOrder] at shaped
            exact shaped
          exact Ordering.noConfusion reduced
      | .eq =>
          have tailEq : bunchedBimonoidBracketTreeCompare leftRight rightRight = .eq := by
            have shaped : (match bunchedBimonoidBracketTreeCompare leftLeft rightLeft with
                | .lt => Ordering.lt
                | .gt => Ordering.gt
                | .eq => bunchedBimonoidBracketTreeCompare leftRight rightRight) = .eq := pairEq
            rw [headOrder] at shaped
            exact shaped
          have headTreeEq := bunchedBimonoidBracketTreeCompareEqExtract leftLeft rightLeft headOrder
          have tailTreeEq := bunchedBimonoidBracketTreeCompareEqExtract leftRight rightRight tailEq
          rw [headTreeEq, tailTreeEq]

/-- The canonically ordered pair — smaller child first. -/
def bunchedBimonoidBracketOrderedPair
    (leftTree rightTree : BunchedBimonoidBracketTree) : BunchedBimonoidBracketTree :=
  match bunchedBimonoidBracketTreeCompare leftTree rightTree with
  | .gt => .pairNode rightTree leftTree
  | .lt => .pairNode leftTree rightTree
  | .eq => .pairNode leftTree rightTree

/-- ★ **The canonical magma multiplication** — units absorbed, children canonically ordered.  Commutative
(`bunchedBimonoidBracketMulComm`), unital, NOT associative: exactly the free commutative unital magma. -/
def bunchedBimonoidBracketMul :
    BunchedBimonoidBracketTree → BunchedBimonoidBracketTree → BunchedBimonoidBracketTree
  | .unitLeaf, rightTree => rightTree
  | .varLeaf leftIndex, .unitLeaf => .varLeaf leftIndex
  | .pairNode leftLeft leftRight, .unitLeaf => .pairNode leftLeft leftRight
  | .varLeaf leftIndex, .varLeaf rightIndex =>
      bunchedBimonoidBracketOrderedPair (.varLeaf leftIndex) (.varLeaf rightIndex)
  | .varLeaf leftIndex, .pairNode rightLeft rightRight =>
      bunchedBimonoidBracketOrderedPair (.varLeaf leftIndex) (.pairNode rightLeft rightRight)
  | .pairNode leftLeft leftRight, .varLeaf rightIndex =>
      bunchedBimonoidBracketOrderedPair (.pairNode leftLeft leftRight) (.varLeaf rightIndex)
  | .pairNode leftLeft leftRight, .pairNode rightLeft rightRight =>
      bunchedBimonoidBracketOrderedPair (.pairNode leftLeft leftRight) (.pairNode rightLeft rightRight)

/-- The unit is a right unit for the canonical multiplication. -/
theorem bunchedBimonoidBracketMulUnitRight : (tree : BunchedBimonoidBracketTree) →
    bunchedBimonoidBracketMul tree .unitLeaf = tree
  | .unitLeaf => rfl
  | .varLeaf _ => rfl
  | .pairNode _ _ => rfl

/-- The ordered pair is symmetric in its arguments. -/
theorem bunchedBimonoidBracketOrderedPairComm (leftTree rightTree : BunchedBimonoidBracketTree) :
    bunchedBimonoidBracketOrderedPair leftTree rightTree
      = bunchedBimonoidBracketOrderedPair rightTree leftTree := by
  unfold bunchedBimonoidBracketOrderedPair
  rw [bunchedBimonoidBracketTreeCompareFlip leftTree rightTree]
  cases compareOrder : bunchedBimonoidBracketTreeCompare leftTree rightTree with
  | lt => rfl
  | gt => rfl
  | eq =>
      rw [bunchedBimonoidBracketTreeCompareEqExtract leftTree rightTree compareOrder]
      rfl

/-- ★ **The canonical multiplication is COMMUTATIVE** — and (deliberately) NOT associative. -/
theorem bunchedBimonoidBracketMulComm : (leftTree rightTree : BunchedBimonoidBracketTree) →
    bunchedBimonoidBracketMul leftTree rightTree = bunchedBimonoidBracketMul rightTree leftTree
  | .unitLeaf, .unitLeaf => rfl
  | .unitLeaf, .varLeaf _ => rfl
  | .unitLeaf, .pairNode _ _ => rfl
  | .varLeaf _, .unitLeaf => rfl
  | .pairNode _ _, .unitLeaf => rfl
  | .varLeaf leftIndex, .varLeaf rightIndex =>
      bunchedBimonoidBracketOrderedPairComm (.varLeaf leftIndex) (.varLeaf rightIndex)
  | .varLeaf leftIndex, .pairNode rightLeft rightRight =>
      bunchedBimonoidBracketOrderedPairComm (.varLeaf leftIndex) (.pairNode rightLeft rightRight)
  | .pairNode leftLeft leftRight, .varLeaf rightIndex =>
      bunchedBimonoidBracketOrderedPairComm (.pairNode leftLeft leftRight) (.varLeaf rightIndex)
  | .pairNode leftLeft leftRight, .pairNode rightLeft rightRight =>
      bunchedBimonoidBracketOrderedPairComm (.pairNode leftLeft leftRight)
        (.pairNode rightLeft rightRight)

/-! # =========================================================================================
    # B — THE MONOMORPHIC LIST KIT (hand-rolled; Init's `append` lemmas leak propext)
    # =========================================================================================
-/

/-- Positional read with unit default (the padding element is the magma unit). -/
def bunchedBimonoidBracketGet : List BunchedBimonoidBracketTree → Nat → BunchedBimonoidBracketTree
  | [], _ => .unitLeaf
  | headTree :: _, 0 => headTree
  | _ :: tailTrees, index + 1 => bunchedBimonoidBracketGet tailTrees index

/-- Truncate-or-pad to an exact length (pad with the magma unit) — the generator arity normalizer (the
bracket analogue of the r30 `bunchedBimonoidAugTruncPad`). -/
def bunchedBimonoidBracketTruncPad :
    Nat → List BunchedBimonoidBracketTree → List BunchedBimonoidBracketTree
  | 0, _ => []
  | padCount + 1, [] => .unitLeaf :: bunchedBimonoidBracketTruncPad padCount []
  | keepCount + 1, headTree :: tailTrees => headTree :: bunchedBimonoidBracketTruncPad keepCount tailTrees

/-- TruncPad output length is exactly the requested length. -/
theorem bunchedBimonoidBracketTruncPadLength :
    (targetLength : Nat) → (trees : List BunchedBimonoidBracketTree) →
      (bunchedBimonoidBracketTruncPad targetLength trees).length = targetLength
  | 0, _ => rfl
  | padCount + 1, [] => congrArg Nat.succ (bunchedBimonoidBracketTruncPadLength padCount [])
  | keepCount + 1, _ :: tailTrees =>
      congrArg Nat.succ (bunchedBimonoidBracketTruncPadLength keepCount tailTrees)

/-- `Nat` boolean equality reflects propositional equality (`==` on `Nat` is `decide`; axiom-free). -/
theorem bunchedBimonoidBracketNatEqOfBeq (leftValue rightValue : Nat)
    (beqTrue : (leftValue == rightValue) = true) : leftValue = rightValue :=
  of_decide_eq_true beqTrue

/-- A zero-length tree list is nil. -/
theorem bunchedBimonoidBracketNilOfLengthZero :
    (trees : List BunchedBimonoidBracketTree) → trees.length = 0 → trees = []
  | [], _ => rfl
  | _ :: _, absurdLength => Nat.noConfusion absurdLength

/-- Append with nil on the right (monomorphic; Init's `List.append_nil` leaks propext). -/
theorem bunchedBimonoidBracketAppendNil : (trees : List BunchedBimonoidBracketTree) →
    trees ++ [] = trees
  | [] => rfl
  | headTree :: tailTrees =>
      congrArg (headTree :: ·) (bunchedBimonoidBracketAppendNil tailTrees)

/-- Append associativity (monomorphic; Init's `List.append_assoc` leaks propext). -/
theorem bunchedBimonoidBracketAppendAssoc :
    (firstTrees secondTrees thirdTrees : List BunchedBimonoidBracketTree) →
      (firstTrees ++ secondTrees) ++ thirdTrees = firstTrees ++ (secondTrees ++ thirdTrees)
  | [], _, _ => rfl
  | headTree :: tailTrees, secondTrees, thirdTrees =>
      congrArg (headTree :: ·) (bunchedBimonoidBracketAppendAssoc tailTrees secondTrees thirdTrees)

/-- Take-then-drop recovers the list. -/
theorem bunchedBimonoidBracketTakeAppendDrop :
    (count : Nat) → (trees : List BunchedBimonoidBracketTree) →
      trees.take count ++ trees.drop count = trees
  | 0, _ => rfl
  | _ + 1, [] => rfl
  | count + 1, headTree :: tailTrees =>
      congrArg (headTree :: ·) (bunchedBimonoidBracketTakeAppendDrop count tailTrees)

/-- Taking exactly the length of the left append factor recovers it. -/
theorem bunchedBimonoidBracketTakeAppendLeft :
    (leftTrees rightTrees : List BunchedBimonoidBracketTree) →
      (leftTrees ++ rightTrees).take leftTrees.length = leftTrees
  | [], _ => rfl
  | headTree :: tailTrees, rightTrees =>
      congrArg (headTree :: ·) (bunchedBimonoidBracketTakeAppendLeft tailTrees rightTrees)

/-- Dropping exactly the length of the left append factor leaves the right factor. -/
theorem bunchedBimonoidBracketDropAppendLeft :
    (leftTrees rightTrees : List BunchedBimonoidBracketTree) →
      (leftTrees ++ rightTrees).drop leftTrees.length = rightTrees
  | [], _ => rfl
  | _ :: tailTrees, rightTrees => bunchedBimonoidBracketDropAppendLeft tailTrees rightTrees

/-- Take of nil is nil at every count. -/
theorem bunchedBimonoidBracketTakeNil : (count : Nat) →
    (([] : List BunchedBimonoidBracketTree).take count) = []
  | 0 => rfl
  | _ + 1 => rfl

/-- Drop of nil is nil at every count. -/
theorem bunchedBimonoidBracketDropNil : (count : Nat) →
    (([] : List BunchedBimonoidBracketTree).drop count) = []
  | 0 => rfl
  | _ + 1 => rfl

/-- Length of an append is the sum of lengths. -/
theorem bunchedBimonoidBracketLengthAppend :
    (leftTrees rightTrees : List BunchedBimonoidBracketTree) →
      (leftTrees ++ rightTrees).length = leftTrees.length + rightTrees.length
  | [], rightTrees => (Nat.zero_add rightTrees.length).symm
  | headTree :: tailTrees, rightTrees => by
      show (tailTrees ++ rightTrees).length + 1 = (tailTrees.length + 1) + rightTrees.length
      rw [bunchedBimonoidBracketLengthAppend tailTrees rightTrees, Nat.succ_add]

/-- Take at the first summand of an exact-sum length yields exactly that many elements. -/
theorem bunchedBimonoidBracketTakeLengthAdd :
    (count extra : Nat) → (trees : List BunchedBimonoidBracketTree) →
      trees.length = count + extra → (trees.take count).length = count
  | 0, _, _, _ => rfl
  | count + 1, extra, [], absurdLength => by
      rw [Nat.succ_add] at absurdLength
      exact Nat.noConfusion absurdLength
  | count + 1, extra, headTree :: tailTrees, sumLength => by
      rw [Nat.succ_add] at sumLength
      exact congrArg Nat.succ
        (bunchedBimonoidBracketTakeLengthAdd count extra tailTrees (Nat.succ.inj sumLength))

/-- Drop at the first summand of an exact-sum length leaves exactly the second summand. -/
theorem bunchedBimonoidBracketDropLengthAdd :
    (count extra : Nat) → (trees : List BunchedBimonoidBracketTree) →
      trees.length = count + extra → (trees.drop count).length = extra
  | 0, extra, trees, sumLength => by
      rw [Nat.zero_add] at sumLength
      exact sumLength
  | count + 1, extra, [], absurdLength => by
      rw [Nat.succ_add] at absurdLength
      exact Nat.noConfusion absurdLength
  | count + 1, extra, _ :: tailTrees, sumLength => by
      rw [Nat.succ_add] at sumLength
      exact bunchedBimonoidBracketDropLengthAdd count extra tailTrees (Nat.succ.inj sumLength)

/-- Take at a sum splits into take-then-take-of-drop. -/
theorem bunchedBimonoidBracketTakeAddSplit :
    (firstCount secondCount : Nat) → (trees : List BunchedBimonoidBracketTree) →
      trees.take (firstCount + secondCount)
        = trees.take firstCount ++ (trees.drop firstCount).take secondCount
  | 0, secondCount, trees => by rw [Nat.zero_add]; rfl
  | firstCount + 1, secondCount, [] => by
      rw [Nat.succ_add]
      show ([] : List BunchedBimonoidBracketTree) = [] ++ ([] : List BunchedBimonoidBracketTree).take secondCount
      rw [bunchedBimonoidBracketTakeNil secondCount]
      rfl
  | firstCount + 1, secondCount, headTree :: tailTrees => by
      rw [Nat.succ_add]
      exact congrArg (headTree :: ·)
        (bunchedBimonoidBracketTakeAddSplit firstCount secondCount tailTrees)

/-- Drop at a sum is drop-then-drop. -/
theorem bunchedBimonoidBracketDropAddSplit :
    (firstCount secondCount : Nat) → (trees : List BunchedBimonoidBracketTree) →
      trees.drop (firstCount + secondCount) = (trees.drop firstCount).drop secondCount
  | 0, secondCount, trees => by rw [Nat.zero_add]; rfl
  | firstCount + 1, secondCount, [] => by
      rw [Nat.succ_add]
      exact (bunchedBimonoidBracketDropNil secondCount).symm
  | firstCount + 1, secondCount, _ :: tailTrees => by
      rw [Nat.succ_add]
      exact bunchedBimonoidBracketDropAddSplit firstCount secondCount tailTrees

/-! # =========================================================================================
    # C — THE BRACKET EVALUATION (the six-arm structural fold)
    # =========================================================================================
-/

/-- The bracket carrier: functions on bracket-tree lists at dimension 2, trivial elsewhere (widths are read
off the shipped `bunchedBimonoidAugWordWidth` directly from the syntax, so dimension 1 carries no data). -/
def BunchedBimonoidBracketCarrier : Nat → Type
  | 0 => Unit
  | 1 => Unit
  | 2 => List BunchedBimonoidBracketTree → List BunchedBimonoidBracketTree
  | _ + 3 => Unit

/-- The declared width of a cell at any dimension — the augmented word width at dimension 1, zero elsewhere
(constant `Nat` motive; propext-clean). -/
def bunchedBimonoidBracketWordWidthAt :
    {dim : Nat} → CellExpr bunchedBimonoidOmegaComputad dim → Nat
  | 1, word => bunchedBimonoidAugWordWidth word
  | 0, _ => 0
  | _ + 2, _ => 0

/-- ★ The **raw generator behaviors** — the walking-bunched-bimonoid operations on bracket-tree lists:
multiply (canonically), duplicate, swap, insert the unit, discard.  The colour labels (junk at label-dim 1)
act as the identity. -/
def bunchedBimonoidBracketGenRaw :
    BunchedBIGenLabel → List BunchedBimonoidBracketTree → List BunchedBimonoidBracketTree
  | .addMult, args =>
      [bunchedBimonoidBracketMul (bunchedBimonoidBracketGet args 0) (bunchedBimonoidBracketGet args 1)]
  | .multMult, args =>
      [bunchedBimonoidBracketMul (bunchedBimonoidBracketGet args 0) (bunchedBimonoidBracketGet args 1)]
  | .addUnit, _ => [.unitLeaf]
  | .multUnit, _ => [.unitLeaf]
  | .addComult, args => [bunchedBimonoidBracketGet args 0, bunchedBimonoidBracketGet args 0]
  | .addCounit, _ => []
  | .addSwap, args => [bunchedBimonoidBracketGet args 1, bunchedBimonoidBracketGet args 0]
  | .additiveColour, args => args
  | .multColour, args => args

/-- Generator evaluation: the declared-target-width-normalized raw behavior at label-dim 1. -/
def bunchedBimonoidBracketGenEval : (labelDim : Nat) → BunchedBIGenLabel → Nat →
    BunchedBimonoidBracketCarrier (labelDim + 1)
  | 0, _, _ => ()
  | 1, label, targetWidth =>
      fun args => bunchedBimonoidBracketTruncPad targetWidth (bunchedBimonoidBracketGenRaw label args)
  | _ + 2, _, _ => ()

/-- Identity evaluation: the identity function at dim 1 -> 2. -/
def bunchedBimonoidBracketIdEval : (d : Nat) → BunchedBimonoidBracketCarrier (d + 1)
  | 0 => ()
  | 1 => fun args => args
  | _ + 2 => ()

/-- Vertical composition: function composition (diagrammatic order) at dimension 2. -/
def bunchedBimonoidBracketVcompEval : (d : Nat) →
    BunchedBimonoidBracketCarrier (d + 1) → BunchedBimonoidBracketCarrier (d + 1) →
      BunchedBimonoidBracketCarrier (d + 1)
  | 0, _, _ => ()
  | 1, leftFun, rightFun => fun args => rightFun (leftFun args)
  | _ + 2, _, _ => ()

/-- Left whisker: pass the whisker-width prefix, evaluate on the rest. -/
def bunchedBimonoidBracketWhiskerLeftEval : (d : Nat) → Nat →
    BunchedBimonoidBracketCarrier (d + 2) → BunchedBimonoidBracketCarrier (d + 2)
  | 0, whiskerWidth, cellFun =>
      fun args => args.take whiskerWidth ++ cellFun (args.drop whiskerWidth)
  | _ + 1, _, _ => ()

/-- Right whisker: evaluate on the declared-source-width prefix, pass the rest. -/
def bunchedBimonoidBracketWhiskerRightEval : (d : Nat) →
    BunchedBimonoidBracketCarrier (d + 2) → Nat → BunchedBimonoidBracketCarrier (d + 2)
  | 0, cellFun, splitWidth =>
      fun args => cellFun (args.take splitWidth) ++ args.drop splitWidth
  | _ + 1, _, _ => ()

/-- ★★ **The bracket evaluation** — the six-arm structural fold into the bracket carrier: 2-cells become
functions on bracket-tree lists; whisker splits and generator arities are driven by the DECLARED boundary
widths (`bunchedBimonoidAugWordWidth` on the syntax), mirroring the r30 affine truncation discipline. -/
def bunchedBimonoidBracketEval : {dim : Nat} → CellExpr bunchedBimonoidOmegaComputad dim →
    BunchedBimonoidBracketCarrier dim
  | _, .ofMode _ => ()
  | _, .gen (dim := labelDim) label _ target =>
      bunchedBimonoidBracketGenEval labelDim label (bunchedBimonoidBracketWordWidthAt target)
  | _, .id (dim := d) _ => bunchedBimonoidBracketIdEval d
  | _, .vcomp (dim := d) leftCell rightCell =>
      bunchedBimonoidBracketVcompEval d (bunchedBimonoidBracketEval leftCell)
        (bunchedBimonoidBracketEval rightCell)
  | _, .whiskerLeft (dim := d) whiskerCell cell =>
      bunchedBimonoidBracketWhiskerLeftEval d (bunchedBimonoidBracketWordWidthAt whiskerCell)
        (bunchedBimonoidBracketEval cell)
  | _, .whiskerRight (dim := d) cell _whiskerCell =>
      bunchedBimonoidBracketWhiskerRightEval d (bunchedBimonoidBracketEval cell)
        (bunchedBimonoidBracketWordWidthAt (boundarySource cell))

/-! ## Truth probes — the bracket semantics separates the association orders -/

/-- `(mu |> a) ; mu` — multiply the FIRST two strands, then multiply: the left association `(x*y)*z`. -/
def bunchedBimonoidLeftAssocCell : CellExpr bunchedBimonoidOmegaComputad 2 :=
  CellExpr.vcomp (CellExpr.whiskerRight bunchedBimonoidAddMuGen bunchedBimonoidAdditiveGen)
    bunchedBimonoidAddMuGen

/-- `(a <| mu) ; mu` — multiply the LAST two strands, then multiply: the right association `x*(y*z)`. -/
def bunchedBimonoidRightAssocCell : CellExpr bunchedBimonoidOmegaComputad 2 :=
  CellExpr.vcomp (CellExpr.whiskerLeft bunchedBimonoidAdditiveGen bunchedBimonoidAddMuGen)
    bunchedBimonoidAddMuGen

/-- The three-variable argument list `[x0, x1, x2]`. -/
def bunchedBimonoidBracketThreeVars : List BunchedBimonoidBracketTree :=
  [.varLeaf 0, .varLeaf 1, .varLeaf 2]

/-- ★★ **The left association evaluates to `(x0 * x1) * x2`** — the canonical tree
`pairNode (varLeaf 2) (pairNode (varLeaf 0) (varLeaf 1))` (the leaf sorts before the node). -/
theorem bunchedBimonoidLeftAssocBracketValue :
    bunchedBimonoidBracketEval bunchedBimonoidLeftAssocCell bunchedBimonoidBracketThreeVars
      = [.pairNode (.varLeaf 2) (.pairNode (.varLeaf 0) (.varLeaf 1))] := rfl

/-- ★★ **The right association evaluates to `x0 * (x1 * x2)`** — the canonical tree
`pairNode (varLeaf 0) (pairNode (varLeaf 1) (varLeaf 2))`.  DIFFERENT from the left association: the bracket
semantics sees the association order. -/
theorem bunchedBimonoidRightAssocBracketValue :
    bunchedBimonoidBracketEval bunchedBimonoidRightAssocCell bunchedBimonoidBracketThreeVars
      = [.pairNode (.varLeaf 0) (.pairNode (.varLeaf 1) (.varLeaf 2))] := rfl

/-! # =========================================================================================
    # D — THE SHAPE INVARIANT: Clean cells at declared-source-width inputs produce
    #     declared-target-width outputs
    # =========================================================================================
-/

/-- The shape statement, dimension-matched (contentful exactly at dimension 2). -/
def bunchedBimonoidBracketShapeStatement :
    {dim : Nat} → CellExpr bunchedBimonoidOmegaComputad dim → Prop
  | 2, cell => bunchedBimonoidAugCleanCell cell = true →
      ∀ (args : List BunchedBimonoidBracketTree),
        args.length = bunchedBimonoidAugWordWidth (boundarySource cell) →
        (bunchedBimonoidBracketEval cell args).length
          = bunchedBimonoidAugWordWidth (boundaryTarget cell)
  | 0, _ => True
  | 1, _ => True
  | _ + 3, _ => True

/-- ★ **THE SHAPE INVARIANT** — on Clean cells, declared-source-width inputs produce declared-target-width
outputs (the bracket analogue of the r30 declared-boundary-dims invariant; the composability gate supplies
the vcomp interface agreement). -/
theorem bunchedBimonoidBracketShape :
    ∀ {dim : Nat} (cell : CellExpr bunchedBimonoidOmegaComputad dim),
      bunchedBimonoidBracketShapeStatement cell
  | _, .ofMode _ => True.intro
  | _, .gen (dim := labelDim) label _ target => by
      match labelDim with
      | 0 => exact True.intro
      | 1 =>
          intro _ args _
          exact bunchedBimonoidBracketTruncPadLength (bunchedBimonoidAugWordWidth target)
            (bunchedBimonoidBracketGenRaw label args)
      | _ + 2 => exact True.intro
  | _, .id (dim := innerDim) word => by
      match innerDim with
      | 0 => exact True.intro
      | 1 =>
          intro _ args lengthPin
          exact lengthPin
      | _ + 2 => exact True.intro
  | _, .vcomp (dim := innerDim) leftCell rightCell => by
      match innerDim with
      | 0 => exact True.intro
      | _ + 2 => exact True.intro
      | 1 =>
          intro cleanBoth args lengthPin
          have cleanSplit := bunchedBimonoidAugAndSplit cleanBoth
          have cleanTail := bunchedBimonoidAugAndSplit cleanSplit.2
          have interfaceBeq : ((bunchedBimonoidEvalAugCell leftCell).rows
              == (bunchedBimonoidEvalAugCell rightCell).cols) = true := cleanTail.2
          have interfaceNat : (bunchedBimonoidEvalAugCell leftCell).rows
              = (bunchedBimonoidEvalAugCell rightCell).cols :=
            bunchedBimonoidBracketNatEqOfBeq _ _ interfaceBeq
          have interfaceWidth : bunchedBimonoidAugWordWidth (boundaryTarget leftCell)
              = bunchedBimonoidAugWordWidth (boundarySource rightCell) := by
            have rowsForm := bunchedBimonoidAugRowsEq leftCell
            have colsForm := bunchedBimonoidAugColsEq rightCell
            rw [rowsForm, colsForm] at interfaceNat
            exact Nat.succ.inj interfaceNat
          have leftLength := bunchedBimonoidBracketShape leftCell cleanSplit.1 args lengthPin
          have rightLength := bunchedBimonoidBracketShape rightCell cleanTail.1
            (bunchedBimonoidBracketEval leftCell args) (leftLength.trans interfaceWidth)
          exact rightLength
  | _, .whiskerLeft (dim := innerDim) whiskerCell cell => by
      match innerDim with
      | _ + 1 => exact True.intro
      | 0 =>
          intro cleanBoth args lengthPin
          have cleanSplit := bunchedBimonoidAugAndSplit cleanBoth
          have pinAsAdd : args.length
              = bunchedBimonoidAugWordWidth whiskerCell
                + bunchedBimonoidAugWordWidth (boundarySource cell) := lengthPin
          show (args.take (bunchedBimonoidAugWordWidth whiskerCell)
              ++ bunchedBimonoidBracketEval cell
                  (args.drop (bunchedBimonoidAugWordWidth whiskerCell))).length
            = bunchedBimonoidAugWordWidth whiskerCell
                + bunchedBimonoidAugWordWidth (boundaryTarget cell)
          rw [bunchedBimonoidBracketLengthAppend]
          rw [bunchedBimonoidBracketTakeLengthAdd (bunchedBimonoidAugWordWidth whiskerCell)
            (bunchedBimonoidAugWordWidth (boundarySource cell)) args pinAsAdd]
          rw [bunchedBimonoidBracketShape cell cleanSplit.2
            (args.drop (bunchedBimonoidAugWordWidth whiskerCell))
            (bunchedBimonoidBracketDropLengthAdd (bunchedBimonoidAugWordWidth whiskerCell)
              (bunchedBimonoidAugWordWidth (boundarySource cell)) args pinAsAdd)]
  | _, .whiskerRight (dim := innerDim) cell whiskerCell => by
      match innerDim with
      | _ + 1 => exact True.intro
      | 0 =>
          intro cleanBoth args lengthPin
          have cleanSplit := bunchedBimonoidAugAndSplit cleanBoth
          have pinAsAdd : args.length
              = bunchedBimonoidAugWordWidth (boundarySource cell)
                + bunchedBimonoidAugWordWidth whiskerCell := lengthPin
          show (bunchedBimonoidBracketEval cell
                (args.take (bunchedBimonoidAugWordWidth (boundarySource cell)))
              ++ args.drop (bunchedBimonoidAugWordWidth (boundarySource cell))).length
            = bunchedBimonoidAugWordWidth (boundaryTarget cell)
                + bunchedBimonoidAugWordWidth whiskerCell
          rw [bunchedBimonoidBracketLengthAppend]
          rw [bunchedBimonoidBracketShape cell cleanSplit.1
            (args.take (bunchedBimonoidAugWordWidth (boundarySource cell)))
            (bunchedBimonoidBracketTakeLengthAdd
              (bunchedBimonoidAugWordWidth (boundarySource cell))
              (bunchedBimonoidAugWordWidth whiskerCell) args pinAsAdd)]
          rw [bunchedBimonoidBracketDropLengthAdd
            (bunchedBimonoidAugWordWidth (boundarySource cell))
            (bunchedBimonoidAugWordWidth whiskerCell) args pinAsAdd]

/-! # =========================================================================================
    # E — THE COMPOSABILITY-GATED BRACKET RELATION
    # =========================================================================================
-/

/-- Take at an exact left-factor length (packaged for rewriting). -/
theorem bunchedBimonoidBracketTakeAppendOfLength (count : Nat)
    (leftTrees rightTrees : List BunchedBimonoidBracketTree)
    (lengthEq : leftTrees.length = count) :
    (leftTrees ++ rightTrees).take count = leftTrees := by
  subst lengthEq
  exact bunchedBimonoidBracketTakeAppendLeft leftTrees rightTrees

/-- Drop at an exact left-factor length (packaged for rewriting). -/
theorem bunchedBimonoidBracketDropAppendOfLength (count : Nat)
    (leftTrees rightTrees : List BunchedBimonoidBracketTree)
    (lengthEq : leftTrees.length = count) :
    (leftTrees ++ rightTrees).drop count = rightTrees := by
  subst lengthEq
  exact bunchedBimonoidBracketDropAppendLeft leftTrees rightTrees

/-- The composability bit of a Clean vertical composite, decoded to declared-width agreement. -/
theorem bunchedBimonoidBracketCleanVcompSplit
    {leftCell rightCell : CellExpr bunchedBimonoidOmegaComputad 2}
    (cleanBoth : bunchedBimonoidAugCleanCell (CellExpr.vcomp leftCell rightCell) = true) :
    bunchedBimonoidAugCleanCell leftCell = true
      ∧ bunchedBimonoidAugCleanCell rightCell = true
      ∧ bunchedBimonoidAugWordWidth (boundaryTarget leftCell)
          = bunchedBimonoidAugWordWidth (boundarySource rightCell) := by
  have cleanSplit := bunchedBimonoidAugAndSplit cleanBoth
  have cleanTail := bunchedBimonoidAugAndSplit cleanSplit.2
  have interfaceNat : (bunchedBimonoidEvalAugCell leftCell).rows
      = (bunchedBimonoidEvalAugCell rightCell).cols :=
    bunchedBimonoidBracketNatEqOfBeq _ _ cleanTail.2
  refine ⟨cleanSplit.1, cleanTail.1, ?_⟩
  rw [bunchedBimonoidAugRowsEq leftCell, bunchedBimonoidAugColsEq rightCell] at interfaceNat
  exact Nat.succ.inj interfaceNat

/-- Rebuild a Clean vertical composite from its pieces. -/
theorem bunchedBimonoidBracketCleanVcompJoin
    {leftCell rightCell : CellExpr bunchedBimonoidOmegaComputad 2}
    (cleanLeft : bunchedBimonoidAugCleanCell leftCell = true)
    (cleanRight : bunchedBimonoidAugCleanCell rightCell = true)
    (interfaceWidth : bunchedBimonoidAugWordWidth (boundaryTarget leftCell)
      = bunchedBimonoidAugWordWidth (boundarySource rightCell)) :
    bunchedBimonoidAugCleanCell (CellExpr.vcomp leftCell rightCell) = true := by
  refine bunchedBimonoidAugAndJoin cleanLeft (bunchedBimonoidAugAndJoin cleanRight ?_)
  show ((bunchedBimonoidEvalAugCell leftCell).rows
      == (bunchedBimonoidEvalAugCell rightCell).cols) = true
  rw [bunchedBimonoidAugRowsEq leftCell, bunchedBimonoidAugColsEq rightCell, interfaceWidth]
  exact show decide (bunchedBimonoidAugWordWidth (boundarySource rightCell) + 1
      = bunchedBimonoidAugWordWidth (boundarySource rightCell) + 1) = true
    from decide_eq_true rfl

/-- ★ The **dimension-matched bracket agreement**: declared boundary-width agreement (ungated) plus pointwise
bracket-evaluation agreement on Clean cells at declared-source-width inputs — contentful at dimension 2,
declared-width equality at dimension 1, trivial elsewhere. -/
def bunchedBimonoidBracketAgree : {dim : Nat} → CellExpr bunchedBimonoidOmegaComputad dim →
    CellExpr bunchedBimonoidOmegaComputad dim → Prop
  | 0, _, _ => True
  | 1, wordAlpha, wordBeta =>
      bunchedBimonoidAugWordWidth wordAlpha = bunchedBimonoidAugWordWidth wordBeta
  | 2, cellAlpha, cellBeta =>
      (bunchedBimonoidAugWordWidth (boundarySource cellAlpha)
          = bunchedBimonoidAugWordWidth (boundarySource cellBeta))
        ∧ (bunchedBimonoidAugWordWidth (boundaryTarget cellAlpha)
            = bunchedBimonoidAugWordWidth (boundaryTarget cellBeta))
        ∧ (bunchedBimonoidAugCleanCell cellAlpha = true →
            bunchedBimonoidAugCleanCell cellBeta = true →
            ∀ (args : List BunchedBimonoidBracketTree),
              args.length = bunchedBimonoidAugWordWidth (boundarySource cellAlpha) →
              bunchedBimonoidBracketEval cellAlpha args = bunchedBimonoidBracketEval cellBeta args)
  | _ + 3, _, _ => True

/-- ★★ **The gated bracket relation** — the r30 Clean-gate equivalence plus the bracket agreement.  The
target relation the UNITAL scope's saturated congruence folds into. -/
def bunchedBimonoidBracketGatedEq : CellRelOver bunchedBimonoidOmegaComputad :=
  fun {_dim} cellAlpha cellBeta =>
    (bunchedBimonoidAugCleanGate cellAlpha = true ↔ bunchedBimonoidAugCleanGate cellBeta = true)
      ∧ bunchedBimonoidBracketAgree cellAlpha cellBeta

/-- Agreement is reflexive. -/
theorem bunchedBimonoidBracketAgreeRefl :
    ∀ {dim : Nat} (cell : CellExpr bunchedBimonoidOmegaComputad dim),
      bunchedBimonoidBracketAgree cell cell
  | 0, _ => True.intro
  | 1, _ => rfl
  | 2, _ => ⟨rfl, rfl, fun _ _ _ _ => rfl⟩
  | _ + 3, _ => True.intro

/-- Agreement is symmetric. -/
theorem bunchedBimonoidBracketAgreeSymm :
    {dim : Nat} → {cellAlpha cellBeta : CellExpr bunchedBimonoidOmegaComputad dim} →
      bunchedBimonoidBracketAgree cellAlpha cellBeta → bunchedBimonoidBracketAgree cellBeta cellAlpha
  | 0, _, _, _ => True.intro
  | 1, _, _, widthEq => widthEq.symm
  | 2, _, _, ⟨sourceEq, targetEq, gatedPointwise⟩ =>
      ⟨sourceEq.symm, targetEq.symm, fun cleanBeta cleanAlpha args lengthPin =>
        (gatedPointwise cleanAlpha cleanBeta args (lengthPin.trans sourceEq.symm)).symm⟩
  | _ + 3, _, _, _ => True.intro

/-- Agreement is transitive (given transport of Cleanliness to the middle cell). -/
theorem bunchedBimonoidBracketAgreeTrans :
    {dim : Nat} → {cellAlpha cellBeta cellGamma : CellExpr bunchedBimonoidOmegaComputad dim} →
      (bunchedBimonoidAugCleanGate cellAlpha = true → bunchedBimonoidAugCleanGate cellBeta = true) →
      bunchedBimonoidBracketAgree cellAlpha cellBeta → bunchedBimonoidBracketAgree cellBeta cellGamma →
      bunchedBimonoidBracketAgree cellAlpha cellGamma
  | 0, _, _, _, _, _, _ => True.intro
  | 1, _, _, _, _, widthLeft, widthRight => widthLeft.trans widthRight
  | 2, _, _, _, cleanMiddleOf, ⟨sourceLeft, targetLeft, pointwiseLeft⟩,
      ⟨sourceRight, targetRight, pointwiseRight⟩ =>
      ⟨sourceLeft.trans sourceRight, targetLeft.trans targetRight,
        fun cleanAlpha cleanGamma args lengthPin =>
          (pointwiseLeft cleanAlpha (cleanMiddleOf cleanAlpha) args lengthPin).trans
            (pointwiseRight (cleanMiddleOf cleanAlpha) cleanGamma args
              (lengthPin.trans sourceLeft))⟩
  | _ + 3, _, _, _, _, _, _ => True.intro

/-- Clean-gate transport into the LEFT factor of a vertical composite (dimension 2). -/
theorem bunchedBimonoidBracketCleanVcompIffLeft
    {cellAlpha cellAlpha' cellBeta : CellExpr bunchedBimonoidOmegaComputad 2}
    (cleanIff : bunchedBimonoidAugCleanCell cellAlpha = true
      ↔ bunchedBimonoidAugCleanCell cellAlpha' = true)
    (targetEq : bunchedBimonoidAugWordWidth (boundaryTarget cellAlpha)
      = bunchedBimonoidAugWordWidth (boundaryTarget cellAlpha')) :
    bunchedBimonoidAugCleanCell (CellExpr.vcomp cellAlpha cellBeta) = true
      ↔ bunchedBimonoidAugCleanCell (CellExpr.vcomp cellAlpha' cellBeta) = true := by
  constructor
  · intro cleanLeft
    have parts := bunchedBimonoidBracketCleanVcompSplit cleanLeft
    exact bunchedBimonoidBracketCleanVcompJoin (cleanIff.mp parts.1) parts.2.1
      (targetEq.symm.trans parts.2.2)
  · intro cleanRight
    have parts := bunchedBimonoidBracketCleanVcompSplit cleanRight
    exact bunchedBimonoidBracketCleanVcompJoin (cleanIff.mpr parts.1) parts.2.1
      (targetEq.trans parts.2.2)

/-- Clean-gate transport into the RIGHT factor of a vertical composite (dimension 2). -/
theorem bunchedBimonoidBracketCleanVcompIffRight
    {cellAlpha cellBeta cellBeta' : CellExpr bunchedBimonoidOmegaComputad 2}
    (cleanIff : bunchedBimonoidAugCleanCell cellBeta = true
      ↔ bunchedBimonoidAugCleanCell cellBeta' = true)
    (sourceEq : bunchedBimonoidAugWordWidth (boundarySource cellBeta)
      = bunchedBimonoidAugWordWidth (boundarySource cellBeta')) :
    bunchedBimonoidAugCleanCell (CellExpr.vcomp cellAlpha cellBeta) = true
      ↔ bunchedBimonoidAugCleanCell (CellExpr.vcomp cellAlpha cellBeta') = true := by
  constructor
  · intro cleanLeft
    have parts := bunchedBimonoidBracketCleanVcompSplit cleanLeft
    exact bunchedBimonoidBracketCleanVcompJoin parts.1 (cleanIff.mp parts.2.1)
      (parts.2.2.trans sourceEq)
  · intro cleanRight
    have parts := bunchedBimonoidBracketCleanVcompSplit cleanRight
    exact bunchedBimonoidBracketCleanVcompJoin parts.1 (cleanIff.mpr parts.2.1)
      (parts.2.2.trans sourceEq.symm)

/-! ## The eleven strict rows, gated-absorbed by the bracket semantics -/

/-- vcompAssoc is bracket-absorbed. -/
theorem bunchedBimonoidBracketGatedVcompAssoc {dim : Nat}
    (cellA cellB cellC : CellExpr bunchedBimonoidOmegaComputad (dim + 1)) :
    bunchedBimonoidBracketGatedEq
      (CellExpr.vcomp (CellExpr.vcomp cellA cellB) cellC)
      (CellExpr.vcomp cellA (CellExpr.vcomp cellB cellC)) := by
  refine ⟨(bunchedBimonoidAugGatedVcompAssoc cellA cellB cellC).1, ?_⟩
  match dim with
  | 0 =>
      exact Nat.add_assoc (bunchedBimonoidAugWordWidth cellA)
        (bunchedBimonoidAugWordWidth cellB) (bunchedBimonoidAugWordWidth cellC)
  | 1 => exact ⟨rfl, rfl, fun _ _ _ _ => rfl⟩
  | _ + 2 => exact True.intro

/-- vcompUnitLeft is bracket-absorbed. -/
theorem bunchedBimonoidBracketGatedVcompUnitLeft {dim : Nat}
    (cellA : CellExpr bunchedBimonoidOmegaComputad (dim + 1)) :
    bunchedBimonoidBracketGatedEq
      (CellExpr.vcomp (CellExpr.id (boundarySource cellA)) cellA) cellA := by
  refine ⟨(bunchedBimonoidAugGatedVcompUnitLeft cellA).1, ?_⟩
  match dim with
  | 0 => exact Nat.zero_add (bunchedBimonoidAugWordWidth cellA)
  | 1 => exact ⟨rfl, rfl, fun _ _ _ _ => rfl⟩
  | _ + 2 => exact True.intro

/-- vcompUnitRight is bracket-absorbed. -/
theorem bunchedBimonoidBracketGatedVcompUnitRight {dim : Nat}
    (cellA : CellExpr bunchedBimonoidOmegaComputad (dim + 1)) :
    bunchedBimonoidBracketGatedEq
      (CellExpr.vcomp cellA (CellExpr.id (boundaryTarget cellA))) cellA := by
  refine ⟨(bunchedBimonoidAugGatedVcompUnitRight cellA).1, ?_⟩
  match dim with
  | 0 => rfl
  | 1 => exact ⟨rfl, rfl, fun _ _ _ _ => rfl⟩
  | _ + 2 => exact True.intro

/-- whiskerLeftUnit is bracket-absorbed. -/
theorem bunchedBimonoidBracketGatedWhiskerLeftUnit {dim : Nat}
    (whiskeringCell innerCell : CellExpr bunchedBimonoidOmegaComputad (dim + 1)) :
    bunchedBimonoidBracketGatedEq
      (CellExpr.whiskerLeft whiskeringCell (CellExpr.id innerCell))
      (CellExpr.id (CellExpr.vcomp whiskeringCell innerCell)) := by
  refine ⟨(bunchedBimonoidAugGatedWhiskerLeftUnit whiskeringCell innerCell).1, ?_⟩
  match dim with
  | 0 =>
      refine ⟨rfl, rfl, fun _ _ args _ => ?_⟩
      exact bunchedBimonoidBracketTakeAppendDrop (bunchedBimonoidAugWordWidth whiskeringCell) args
  | _ + 1 => exact True.intro

/-- whiskerRightUnit is bracket-absorbed. -/
theorem bunchedBimonoidBracketGatedWhiskerRightUnit {dim : Nat}
    (innerCell whiskeringCell : CellExpr bunchedBimonoidOmegaComputad (dim + 1)) :
    bunchedBimonoidBracketGatedEq
      (CellExpr.whiskerRight (CellExpr.id innerCell) whiskeringCell)
      (CellExpr.id (CellExpr.vcomp innerCell whiskeringCell)) := by
  refine ⟨(bunchedBimonoidAugGatedWhiskerRightUnit innerCell whiskeringCell).1, ?_⟩
  match dim with
  | 0 =>
      refine ⟨rfl, rfl, fun _ _ args _ => ?_⟩
      exact bunchedBimonoidBracketTakeAppendDrop (bunchedBimonoidAugWordWidth innerCell) args
  | _ + 1 => exact True.intro

/-- whiskerLeftFunctorial is bracket-absorbed. -/
theorem bunchedBimonoidBracketGatedWhiskerLeftFunctorial {dim : Nat}
    (whiskeringCell : CellExpr bunchedBimonoidOmegaComputad (dim + 1))
    (cellBeta cellGamma : CellExpr bunchedBimonoidOmegaComputad (dim + 2)) :
    bunchedBimonoidBracketGatedEq
      (CellExpr.whiskerLeft whiskeringCell (CellExpr.vcomp cellBeta cellGamma))
      (CellExpr.vcomp (CellExpr.whiskerLeft whiskeringCell cellBeta)
        (CellExpr.whiskerLeft whiskeringCell cellGamma)) := by
  refine ⟨(bunchedBimonoidAugGatedWhiskerLeftFunctorial whiskeringCell cellBeta cellGamma).1, ?_⟩
  match dim with
  | 0 =>
      refine ⟨rfl, rfl, fun _ _ args lengthPin => ?_⟩
      have pinAsAdd : args.length
          = bunchedBimonoidAugWordWidth whiskeringCell
            + bunchedBimonoidAugWordWidth (boundarySource cellBeta) := lengthPin
      have takeLen : (args.take (bunchedBimonoidAugWordWidth whiskeringCell)).length
          = bunchedBimonoidAugWordWidth whiskeringCell :=
        bunchedBimonoidBracketTakeLengthAdd _ _ args pinAsAdd
      show args.take (bunchedBimonoidAugWordWidth whiskeringCell)
          ++ bunchedBimonoidBracketEval cellGamma
              (bunchedBimonoidBracketEval cellBeta
                (args.drop (bunchedBimonoidAugWordWidth whiskeringCell)))
        = ((args.take (bunchedBimonoidAugWordWidth whiskeringCell)
              ++ bunchedBimonoidBracketEval cellBeta
                  (args.drop (bunchedBimonoidAugWordWidth whiskeringCell))).take
                (bunchedBimonoidAugWordWidth whiskeringCell))
            ++ bunchedBimonoidBracketEval cellGamma
              ((args.take (bunchedBimonoidAugWordWidth whiskeringCell)
                  ++ bunchedBimonoidBracketEval cellBeta
                      (args.drop (bunchedBimonoidAugWordWidth whiskeringCell))).drop
                    (bunchedBimonoidAugWordWidth whiskeringCell))
      rw [bunchedBimonoidBracketTakeAppendOfLength _ _ _ takeLen,
        bunchedBimonoidBracketDropAppendOfLength _ _ _ takeLen]
  | _ + 1 => exact True.intro

/-- whiskerRightFunctorial is bracket-absorbed (GATED — the interface agreement and the shape invariant
carry the split). -/
theorem bunchedBimonoidBracketGatedWhiskerRightFunctorial {dim : Nat}
    (cellAlpha cellBeta : CellExpr bunchedBimonoidOmegaComputad (dim + 2))
    (whiskeringCell : CellExpr bunchedBimonoidOmegaComputad (dim + 1)) :
    bunchedBimonoidBracketGatedEq
      (CellExpr.whiskerRight (CellExpr.vcomp cellAlpha cellBeta) whiskeringCell)
      (CellExpr.vcomp (CellExpr.whiskerRight cellAlpha whiskeringCell)
        (CellExpr.whiskerRight cellBeta whiskeringCell)) := by
  refine ⟨(bunchedBimonoidAugGatedWhiskerRightFunctorial cellAlpha cellBeta whiskeringCell).1, ?_⟩
  match dim with
  | 0 =>
      refine ⟨rfl, rfl, fun cleanLeft _ args lengthPin => ?_⟩
      have cleanParts := bunchedBimonoidAugAndSplit cleanLeft
      have vcompParts := bunchedBimonoidBracketCleanVcompSplit cleanParts.1
      have pinAsAdd : args.length
          = bunchedBimonoidAugWordWidth (boundarySource cellAlpha)
            + bunchedBimonoidAugWordWidth whiskeringCell := lengthPin
      have takeLen : (args.take (bunchedBimonoidAugWordWidth (boundarySource cellAlpha))).length
          = bunchedBimonoidAugWordWidth (boundarySource cellAlpha) :=
        bunchedBimonoidBracketTakeLengthAdd _ _ args pinAsAdd
      have shapeAlpha : (bunchedBimonoidBracketEval cellAlpha
            (args.take (bunchedBimonoidAugWordWidth (boundarySource cellAlpha)))).length
          = bunchedBimonoidAugWordWidth (boundarySource cellBeta) :=
        (bunchedBimonoidBracketShape cellAlpha vcompParts.1 _ takeLen).trans vcompParts.2.2
      show bunchedBimonoidBracketEval cellBeta
            (bunchedBimonoidBracketEval cellAlpha
              (args.take (bunchedBimonoidAugWordWidth (boundarySource cellAlpha))))
          ++ args.drop (bunchedBimonoidAugWordWidth (boundarySource cellAlpha))
        = bunchedBimonoidBracketEval cellBeta
            ((bunchedBimonoidBracketEval cellAlpha
                (args.take (bunchedBimonoidAugWordWidth (boundarySource cellAlpha)))
              ++ args.drop (bunchedBimonoidAugWordWidth (boundarySource cellAlpha))).take
                (bunchedBimonoidAugWordWidth (boundarySource cellBeta)))
          ++ ((bunchedBimonoidBracketEval cellAlpha
                (args.take (bunchedBimonoidAugWordWidth (boundarySource cellAlpha)))
              ++ args.drop (bunchedBimonoidAugWordWidth (boundarySource cellAlpha))).drop
                (bunchedBimonoidAugWordWidth (boundarySource cellBeta)))
      rw [bunchedBimonoidBracketTakeAppendOfLength _ _ _ shapeAlpha,
        bunchedBimonoidBracketDropAppendOfLength _ _ _ shapeAlpha]
  | _ + 1 => exact True.intro

/-- The Godement interchange is bracket-absorbed (GATED — the shape invariant routes the whisker splits). -/
theorem bunchedBimonoidBracketGatedInterchange {dim : Nat}
    (cellAlpha cellBeta : CellExpr bunchedBimonoidOmegaComputad (dim + 2)) :
    bunchedBimonoidBracketGatedEq
      (CellExpr.vcomp (CellExpr.whiskerRight cellAlpha (boundarySource cellBeta))
        (CellExpr.whiskerLeft (boundaryTarget cellAlpha) cellBeta))
      (CellExpr.vcomp (CellExpr.whiskerLeft (boundarySource cellAlpha) cellBeta)
        (CellExpr.whiskerRight cellAlpha (boundaryTarget cellBeta))) := by
  refine ⟨(bunchedBimonoidAugGatedInterchange cellAlpha cellBeta).1, ?_⟩
  match dim with
  | 0 =>
      refine ⟨rfl, rfl, fun cleanLeft _ args lengthPin => ?_⟩
      have cleanParts := bunchedBimonoidBracketCleanVcompSplit cleanLeft
      have alphaClean := (bunchedBimonoidAugAndSplit cleanParts.1).1
      have pinAsAdd : args.length
          = bunchedBimonoidAugWordWidth (boundarySource cellAlpha)
            + bunchedBimonoidAugWordWidth (boundarySource cellBeta) := lengthPin
      have takeLen : (args.take (bunchedBimonoidAugWordWidth (boundarySource cellAlpha))).length
          = bunchedBimonoidAugWordWidth (boundarySource cellAlpha) :=
        bunchedBimonoidBracketTakeLengthAdd _ _ args pinAsAdd
      have shapeAlpha : (bunchedBimonoidBracketEval cellAlpha
            (args.take (bunchedBimonoidAugWordWidth (boundarySource cellAlpha)))).length
          = bunchedBimonoidAugWordWidth (boundaryTarget cellAlpha) :=
        bunchedBimonoidBracketShape cellAlpha alphaClean _ takeLen
      show ((bunchedBimonoidBracketEval cellAlpha
              (args.take (bunchedBimonoidAugWordWidth (boundarySource cellAlpha)))
            ++ args.drop (bunchedBimonoidAugWordWidth (boundarySource cellAlpha))).take
              (bunchedBimonoidAugWordWidth (boundaryTarget cellAlpha)))
          ++ bunchedBimonoidBracketEval cellBeta
            ((bunchedBimonoidBracketEval cellAlpha
                (args.take (bunchedBimonoidAugWordWidth (boundarySource cellAlpha)))
              ++ args.drop (bunchedBimonoidAugWordWidth (boundarySource cellAlpha))).drop
                (bunchedBimonoidAugWordWidth (boundaryTarget cellAlpha)))
        = bunchedBimonoidBracketEval cellAlpha
            ((args.take (bunchedBimonoidAugWordWidth (boundarySource cellAlpha))
              ++ bunchedBimonoidBracketEval cellBeta
                  (args.drop (bunchedBimonoidAugWordWidth (boundarySource cellAlpha)))).take
                (bunchedBimonoidAugWordWidth (boundarySource cellAlpha)))
          ++ ((args.take (bunchedBimonoidAugWordWidth (boundarySource cellAlpha))
              ++ bunchedBimonoidBracketEval cellBeta
                  (args.drop (bunchedBimonoidAugWordWidth (boundarySource cellAlpha)))).drop
                (bunchedBimonoidAugWordWidth (boundarySource cellAlpha)))
      rw [bunchedBimonoidBracketTakeAppendOfLength _ _ _ shapeAlpha,
        bunchedBimonoidBracketDropAppendOfLength _ _ _ shapeAlpha,
        bunchedBimonoidBracketTakeAppendOfLength _ _ _ takeLen,
        bunchedBimonoidBracketDropAppendOfLength _ _ _ takeLen]
  | _ + 1 => exact True.intro

/-- whiskerAssocLeft is bracket-absorbed. -/
theorem bunchedBimonoidBracketGatedWhiskerAssocLeft {dim : Nat}
    (whiskP whiskQ : CellExpr bunchedBimonoidOmegaComputad (dim + 1))
    (innerCell : CellExpr bunchedBimonoidOmegaComputad (dim + 2)) :
    bunchedBimonoidBracketGatedEq
      (CellExpr.whiskerLeft (CellExpr.vcomp whiskP whiskQ) innerCell)
      (CellExpr.whiskerLeft whiskP (CellExpr.whiskerLeft whiskQ innerCell)) := by
  refine ⟨(bunchedBimonoidAugGatedWhiskerAssocLeft whiskP whiskQ innerCell).1, ?_⟩
  match dim with
  | 0 =>
      refine ⟨Nat.add_assoc (bunchedBimonoidAugWordWidth whiskP)
          (bunchedBimonoidAugWordWidth whiskQ)
          (bunchedBimonoidAugWordWidth (boundarySource innerCell)),
        Nat.add_assoc (bunchedBimonoidAugWordWidth whiskP)
          (bunchedBimonoidAugWordWidth whiskQ)
          (bunchedBimonoidAugWordWidth (boundaryTarget innerCell)),
        fun _ _ args _ => ?_⟩
      show args.take (bunchedBimonoidAugWordWidth whiskP + bunchedBimonoidAugWordWidth whiskQ)
          ++ bunchedBimonoidBracketEval innerCell
            (args.drop (bunchedBimonoidAugWordWidth whiskP + bunchedBimonoidAugWordWidth whiskQ))
        = args.take (bunchedBimonoidAugWordWidth whiskP)
          ++ ((args.drop (bunchedBimonoidAugWordWidth whiskP)).take
                (bunchedBimonoidAugWordWidth whiskQ)
              ++ bunchedBimonoidBracketEval innerCell
                ((args.drop (bunchedBimonoidAugWordWidth whiskP)).drop
                  (bunchedBimonoidAugWordWidth whiskQ)))
      rw [bunchedBimonoidBracketTakeAddSplit, bunchedBimonoidBracketDropAddSplit,
        bunchedBimonoidBracketAppendAssoc]
  | _ + 1 => exact True.intro

/-- whiskerAssocRight is bracket-absorbed. -/
theorem bunchedBimonoidBracketGatedWhiskerAssocRight {dim : Nat}
    (innerCell : CellExpr bunchedBimonoidOmegaComputad (dim + 2))
    (whiskP whiskQ : CellExpr bunchedBimonoidOmegaComputad (dim + 1)) :
    bunchedBimonoidBracketGatedEq
      (CellExpr.whiskerRight innerCell (CellExpr.vcomp whiskP whiskQ))
      (CellExpr.whiskerRight (CellExpr.whiskerRight innerCell whiskP) whiskQ) := by
  refine ⟨(bunchedBimonoidAugGatedWhiskerAssocRight innerCell whiskP whiskQ).1, ?_⟩
  match dim with
  | 0 =>
      refine ⟨(Nat.add_assoc (bunchedBimonoidAugWordWidth (boundarySource innerCell))
          (bunchedBimonoidAugWordWidth whiskP) (bunchedBimonoidAugWordWidth whiskQ)).symm,
        (Nat.add_assoc (bunchedBimonoidAugWordWidth (boundaryTarget innerCell))
          (bunchedBimonoidAugWordWidth whiskP) (bunchedBimonoidAugWordWidth whiskQ)).symm,
        fun _ _ args lengthPin => ?_⟩
      have pinAsAdd : args.length
          = bunchedBimonoidAugWordWidth (boundarySource innerCell)
            + (bunchedBimonoidAugWordWidth whiskP + bunchedBimonoidAugWordWidth whiskQ) :=
        lengthPin
      have takeLen : (args.take (bunchedBimonoidAugWordWidth (boundarySource innerCell))).length
          = bunchedBimonoidAugWordWidth (boundarySource innerCell) :=
        bunchedBimonoidBracketTakeLengthAdd _ _ args pinAsAdd
      show (bunchedBimonoidBracketEval innerCell
            (args.take (bunchedBimonoidAugWordWidth (boundarySource innerCell))))
          ++ (args.drop (bunchedBimonoidAugWordWidth (boundarySource innerCell)))
        = ((bunchedBimonoidBracketEval innerCell
              ((args.take (bunchedBimonoidAugWordWidth (boundarySource innerCell)
                  + bunchedBimonoidAugWordWidth whiskP)).take
                (bunchedBimonoidAugWordWidth (boundarySource innerCell))))
            ++ ((args.take (bunchedBimonoidAugWordWidth (boundarySource innerCell)
                  + bunchedBimonoidAugWordWidth whiskP)).drop
                (bunchedBimonoidAugWordWidth (boundarySource innerCell))))
          ++ (args.drop (bunchedBimonoidAugWordWidth (boundarySource innerCell)
              + bunchedBimonoidAugWordWidth whiskP))
      rw [bunchedBimonoidBracketTakeAddSplit
          (bunchedBimonoidAugWordWidth (boundarySource innerCell))
          (bunchedBimonoidAugWordWidth whiskP) args]
      rw [bunchedBimonoidBracketTakeAppendOfLength _ _ _ takeLen,
        bunchedBimonoidBracketDropAppendOfLength _ _ _ takeLen]
      rw [bunchedBimonoidBracketDropAddSplit
          (bunchedBimonoidAugWordWidth (boundarySource innerCell))
          (bunchedBimonoidAugWordWidth whiskP) args]
      rw [bunchedBimonoidBracketAppendAssoc]
      rw [bunchedBimonoidBracketTakeAppendDrop (bunchedBimonoidAugWordWidth whiskP)
        (args.drop (bunchedBimonoidAugWordWidth (boundarySource innerCell)))]
  | _ + 1 => exact True.intro

/-- whiskerLeftRightCommute is bracket-absorbed. -/
theorem bunchedBimonoidBracketGatedWhiskerLeftRightCommute {dim : Nat}
    (whiskP : CellExpr bunchedBimonoidOmegaComputad (dim + 1))
    (innerCell : CellExpr bunchedBimonoidOmegaComputad (dim + 2))
    (whiskQ : CellExpr bunchedBimonoidOmegaComputad (dim + 1)) :
    bunchedBimonoidBracketGatedEq
      (CellExpr.whiskerRight (CellExpr.whiskerLeft whiskP innerCell) whiskQ)
      (CellExpr.whiskerLeft whiskP (CellExpr.whiskerRight innerCell whiskQ)) := by
  refine ⟨(bunchedBimonoidAugGatedWhiskerLeftRightCommute whiskP innerCell whiskQ).1, ?_⟩
  match dim with
  | 0 =>
      refine ⟨Nat.add_assoc (bunchedBimonoidAugWordWidth whiskP)
          (bunchedBimonoidAugWordWidth (boundarySource innerCell))
          (bunchedBimonoidAugWordWidth whiskQ),
        Nat.add_assoc (bunchedBimonoidAugWordWidth whiskP)
          (bunchedBimonoidAugWordWidth (boundaryTarget innerCell))
          (bunchedBimonoidAugWordWidth whiskQ),
        fun _ _ args lengthPin => ?_⟩
      have pinAsAdd : args.length
          = (bunchedBimonoidAugWordWidth whiskP
              + bunchedBimonoidAugWordWidth (boundarySource innerCell))
            + bunchedBimonoidAugWordWidth whiskQ := lengthPin
      have takeLenP : (args.take (bunchedBimonoidAugWordWidth whiskP)).length
          = bunchedBimonoidAugWordWidth whiskP := by
        refine bunchedBimonoidBracketTakeLengthAdd (bunchedBimonoidAugWordWidth whiskP)
          (bunchedBimonoidAugWordWidth (boundarySource innerCell)
            + bunchedBimonoidAugWordWidth whiskQ) args ?_
        rw [← Nat.add_assoc]
        exact pinAsAdd
      show bunchedBimonoidBracketEval (CellExpr.whiskerLeft whiskP innerCell)
            (args.take (bunchedBimonoidAugWordWidth whiskP
              + bunchedBimonoidAugWordWidth (boundarySource innerCell)))
          ++ args.drop (bunchedBimonoidAugWordWidth whiskP
              + bunchedBimonoidAugWordWidth (boundarySource innerCell))
        = args.take (bunchedBimonoidAugWordWidth whiskP)
          ++ (bunchedBimonoidBracketEval innerCell
                ((args.drop (bunchedBimonoidAugWordWidth whiskP)).take
                  (bunchedBimonoidAugWordWidth (boundarySource innerCell)))
              ++ (args.drop (bunchedBimonoidAugWordWidth whiskP)).drop
                  (bunchedBimonoidAugWordWidth (boundarySource innerCell)))
      show (args.take (bunchedBimonoidAugWordWidth whiskP
              + bunchedBimonoidAugWordWidth (boundarySource innerCell))).take
            (bunchedBimonoidAugWordWidth whiskP)
          ++ bunchedBimonoidBracketEval innerCell
            ((args.take (bunchedBimonoidAugWordWidth whiskP
                + bunchedBimonoidAugWordWidth (boundarySource innerCell))).drop
              (bunchedBimonoidAugWordWidth whiskP))
          ++ args.drop (bunchedBimonoidAugWordWidth whiskP
              + bunchedBimonoidAugWordWidth (boundarySource innerCell))
        = args.take (bunchedBimonoidAugWordWidth whiskP)
          ++ (bunchedBimonoidBracketEval innerCell
                ((args.drop (bunchedBimonoidAugWordWidth whiskP)).take
                  (bunchedBimonoidAugWordWidth (boundarySource innerCell)))
              ++ (args.drop (bunchedBimonoidAugWordWidth whiskP)).drop
                  (bunchedBimonoidAugWordWidth (boundarySource innerCell)))
      rw [bunchedBimonoidBracketTakeAddSplit (bunchedBimonoidAugWordWidth whiskP)
          (bunchedBimonoidAugWordWidth (boundarySource innerCell)) args]
      rw [bunchedBimonoidBracketTakeAppendOfLength _ _ _ takeLenP,
        bunchedBimonoidBracketDropAppendOfLength _ _ _ takeLenP]
      rw [bunchedBimonoidBracketDropAddSplit (bunchedBimonoidAugWordWidth whiskP)
          (bunchedBimonoidAugWordWidth (boundarySource innerCell)) args]
      rw [bunchedBimonoidBracketAppendAssoc]
  | _ + 1 => exact True.intro

/-! # =========================================================================================
    # F — THE CONGRUENCE TRANSPORTS (the eleven closure fields, dimension-matched)
    # =========================================================================================
-/

/-- Left-factor vcomp congruence transport. -/
theorem bunchedBimonoidBracketGatedVcompCongrLeft :
    (dim : Nat) → (cellAlpha cellAlpha' cellBeta : CellExpr bunchedBimonoidOmegaComputad (dim + 1)) →
      bunchedBimonoidBracketGatedEq cellAlpha cellAlpha' →
      bunchedBimonoidBracketGatedEq (CellExpr.vcomp cellAlpha cellBeta)
        (CellExpr.vcomp cellAlpha' cellBeta)
  | 0, _, _, wordBeta, ⟨_, widthEq⟩ =>
      ⟨Iff.intro (fun _ => rfl) (fun _ => rfl),
        congrArg (fun width => Nat.add width (bunchedBimonoidAugWordWidth wordBeta)) widthEq⟩
  | 1, _, _, cellBeta, ⟨cleanIff, sourceEq, targetEq, gatedPointwise⟩ =>
      ⟨bunchedBimonoidBracketCleanVcompIffLeft cleanIff targetEq,
        sourceEq, rfl,
        fun cleanLeft cleanRight args lengthPin =>
          congrArg (bunchedBimonoidBracketEval cellBeta)
            (gatedPointwise (bunchedBimonoidBracketCleanVcompSplit cleanLeft).1
              (bunchedBimonoidBracketCleanVcompSplit cleanRight).1 args lengthPin)⟩
  | _ + 2, _, _, _, _ => ⟨Iff.intro (fun _ => rfl) (fun _ => rfl), True.intro⟩

/-- Right-factor vcomp congruence transport. -/
theorem bunchedBimonoidBracketGatedVcompCongrRight :
    (dim : Nat) → (cellAlpha cellBeta cellBeta' : CellExpr bunchedBimonoidOmegaComputad (dim + 1)) →
      bunchedBimonoidBracketGatedEq cellBeta cellBeta' →
      bunchedBimonoidBracketGatedEq (CellExpr.vcomp cellAlpha cellBeta)
        (CellExpr.vcomp cellAlpha cellBeta')
  | 0, wordAlpha, _, _, ⟨_, widthEq⟩ =>
      ⟨Iff.intro (fun _ => rfl) (fun _ => rfl),
        congrArg (fun width => Nat.add (bunchedBimonoidAugWordWidth wordAlpha) width) widthEq⟩
  | 1, cellAlpha, _, _, ⟨cleanIff, sourceEq, targetEq, gatedPointwise⟩ =>
      ⟨bunchedBimonoidBracketCleanVcompIffRight cleanIff sourceEq,
        rfl, targetEq,
        fun cleanLeft cleanRight args lengthPin => by
          have leftParts := bunchedBimonoidBracketCleanVcompSplit cleanLeft
          have rightParts := bunchedBimonoidBracketCleanVcompSplit cleanRight
          have middleLength : (bunchedBimonoidBracketEval cellAlpha args).length
              = bunchedBimonoidAugWordWidth (boundarySource _) :=
            (bunchedBimonoidBracketShape cellAlpha leftParts.1 args lengthPin).trans
              leftParts.2.2
          exact gatedPointwise leftParts.2.1 rightParts.2.1
            (bunchedBimonoidBracketEval cellAlpha args) middleLength⟩
  | _ + 2, _, _, _, _ => ⟨Iff.intro (fun _ => rfl) (fun _ => rfl), True.intro⟩

/-- Whiskered-cell left-whisker congruence transport. -/
theorem bunchedBimonoidBracketGatedWhiskerLeftCongr :
    (dim : Nat) → (whiskeringCell : CellExpr bunchedBimonoidOmegaComputad (dim + 1)) →
      (cellBeta cellBeta' : CellExpr bunchedBimonoidOmegaComputad (dim + 2)) →
      bunchedBimonoidBracketGatedEq cellBeta cellBeta' →
      bunchedBimonoidBracketGatedEq (CellExpr.whiskerLeft whiskeringCell cellBeta)
        (CellExpr.whiskerLeft whiskeringCell cellBeta')
  | 0, whiskeringCell, cellBeta, _, ⟨cleanIff, sourceEq, targetEq, gatedPointwise⟩ =>
      ⟨Iff.intro
          (fun cleanLeft => bunchedBimonoidAugAndJoin
            (bunchedBimonoidAugCleanOneCell whiskeringCell)
            (cleanIff.mp (bunchedBimonoidAugAndSplit cleanLeft).2))
          (fun cleanRight => bunchedBimonoidAugAndJoin
            (bunchedBimonoidAugCleanOneCell whiskeringCell)
            (cleanIff.mpr (bunchedBimonoidAugAndSplit cleanRight).2)),
        congrArg (fun width => Nat.add (bunchedBimonoidAugWordWidth whiskeringCell) width) sourceEq,
        congrArg (fun width => Nat.add (bunchedBimonoidAugWordWidth whiskeringCell) width) targetEq,
        fun cleanLeft cleanRight args lengthPin => by
          have pinAsAdd : args.length
              = bunchedBimonoidAugWordWidth whiskeringCell
                + bunchedBimonoidAugWordWidth (boundarySource cellBeta) := lengthPin
          exact congrArg (args.take (bunchedBimonoidAugWordWidth whiskeringCell) ++ ·)
            (gatedPointwise (bunchedBimonoidAugAndSplit cleanLeft).2
              (bunchedBimonoidAugAndSplit cleanRight).2
              (args.drop (bunchedBimonoidAugWordWidth whiskeringCell))
              (bunchedBimonoidBracketDropLengthAdd _ _ args pinAsAdd))⟩
  | _ + 1, _, _, _, _ => ⟨Iff.intro (fun _ => rfl) (fun _ => rfl), True.intro⟩

/-- Whiskered-cell right-whisker congruence transport. -/
theorem bunchedBimonoidBracketGatedWhiskerRightCongr :
    (dim : Nat) → (cellAlpha cellAlpha' : CellExpr bunchedBimonoidOmegaComputad (dim + 2)) →
      (whiskeringCell : CellExpr bunchedBimonoidOmegaComputad (dim + 1)) →
      bunchedBimonoidBracketGatedEq cellAlpha cellAlpha' →
      bunchedBimonoidBracketGatedEq (CellExpr.whiskerRight cellAlpha whiskeringCell)
        (CellExpr.whiskerRight cellAlpha' whiskeringCell)
  | 0, cellAlpha, cellAlpha', whiskeringCell, ⟨cleanIff, sourceEq, targetEq, gatedPointwise⟩ =>
      ⟨Iff.intro
          (fun cleanLeft => bunchedBimonoidAugAndJoin
            (cleanIff.mp (bunchedBimonoidAugAndSplit cleanLeft).1)
            (bunchedBimonoidAugCleanOneCell whiskeringCell))
          (fun cleanRight => bunchedBimonoidAugAndJoin
            (cleanIff.mpr (bunchedBimonoidAugAndSplit cleanRight).1)
            (bunchedBimonoidAugCleanOneCell whiskeringCell)),
        congrArg (fun width => Nat.add width (bunchedBimonoidAugWordWidth whiskeringCell)) sourceEq,
        congrArg (fun width => Nat.add width (bunchedBimonoidAugWordWidth whiskeringCell)) targetEq,
        fun cleanLeft cleanRight args lengthPin => by
          show bunchedBimonoidBracketEval cellAlpha
                (args.take (bunchedBimonoidAugWordWidth (boundarySource cellAlpha)))
              ++ args.drop (bunchedBimonoidAugWordWidth (boundarySource cellAlpha))
            = bunchedBimonoidBracketEval cellAlpha'
                (args.take (bunchedBimonoidAugWordWidth (boundarySource cellAlpha')))
              ++ args.drop (bunchedBimonoidAugWordWidth (boundarySource cellAlpha'))
          rw [← sourceEq]
          exact congrArg
            (· ++ args.drop (bunchedBimonoidAugWordWidth (boundarySource cellAlpha)))
            (gatedPointwise (bunchedBimonoidAugAndSplit cleanLeft).1
              (bunchedBimonoidAugAndSplit cleanRight).1
              (args.take (bunchedBimonoidAugWordWidth (boundarySource cellAlpha)))
              (bunchedBimonoidBracketTakeLengthAdd _ _ args lengthPin))⟩
  | _ + 1, _, _, _, _ => ⟨Iff.intro (fun _ => rfl) (fun _ => rfl), True.intro⟩

/-- Identity dimension-bump congruence transport. -/
theorem bunchedBimonoidBracketGatedIdCongr :
    (dim : Nat) → (cellAlpha cellBeta : CellExpr bunchedBimonoidOmegaComputad dim) →
      bunchedBimonoidBracketGatedEq cellAlpha cellBeta →
      bunchedBimonoidBracketGatedEq (CellExpr.id cellAlpha) (CellExpr.id cellBeta)
  | 0, _, _, _ => ⟨Iff.intro (fun _ => rfl) (fun _ => rfl), rfl⟩
  | 1, wordAlpha, wordBeta, ⟨_, widthEq⟩ =>
      ⟨Iff.intro (fun _ => bunchedBimonoidAugCleanOneCell wordBeta)
          (fun _ => bunchedBimonoidAugCleanOneCell wordAlpha),
        widthEq, widthEq, fun _ _ _ _ => rfl⟩
  | _ + 2, _, _, _ => ⟨Iff.intro (fun _ => rfl) (fun _ => rfl), True.intro⟩

/-- Whiskering-word left congruence transport (the whisker word varies). -/
theorem bunchedBimonoidBracketGatedWhiskerLeftWhiskerCongr :
    (dim : Nat) → (whiskerAlpha whiskerAlpha' : CellExpr bunchedBimonoidOmegaComputad (dim + 1)) →
      (innerCell : CellExpr bunchedBimonoidOmegaComputad (dim + 2)) →
      bunchedBimonoidBracketGatedEq whiskerAlpha whiskerAlpha' →
      bunchedBimonoidBracketGatedEq (CellExpr.whiskerLeft whiskerAlpha innerCell)
        (CellExpr.whiskerLeft whiskerAlpha' innerCell)
  | 0, whiskerAlpha, whiskerAlpha', innerCell, ⟨_, widthEq⟩ =>
      ⟨Iff.intro
          (fun cleanLeft => bunchedBimonoidAugAndJoin
            (bunchedBimonoidAugCleanOneCell whiskerAlpha')
            (bunchedBimonoidAugAndSplit cleanLeft).2)
          (fun cleanRight => bunchedBimonoidAugAndJoin
            (bunchedBimonoidAugCleanOneCell whiskerAlpha)
            (bunchedBimonoidAugAndSplit cleanRight).2),
        congrArg (fun width => Nat.add width
          (bunchedBimonoidAugWordWidth (boundarySource innerCell))) widthEq,
        congrArg (fun width => Nat.add width
          (bunchedBimonoidAugWordWidth (boundaryTarget innerCell))) widthEq,
        fun _ _ args _ => by
          show args.take (bunchedBimonoidAugWordWidth whiskerAlpha)
              ++ bunchedBimonoidBracketEval innerCell
                  (args.drop (bunchedBimonoidAugWordWidth whiskerAlpha))
            = args.take (bunchedBimonoidAugWordWidth whiskerAlpha')
              ++ bunchedBimonoidBracketEval innerCell
                  (args.drop (bunchedBimonoidAugWordWidth whiskerAlpha'))
          rw [widthEq]⟩
  | _ + 1, _, _, _, _ => ⟨Iff.intro (fun _ => rfl) (fun _ => rfl), True.intro⟩

/-- Whiskering-word right congruence transport (the whisker word varies; the split is source-driven, so the
evaluation is untouched). -/
theorem bunchedBimonoidBracketGatedWhiskerRightWhiskerCongr :
    (dim : Nat) → (innerCell : CellExpr bunchedBimonoidOmegaComputad (dim + 2)) →
      (whiskerAlpha whiskerAlpha' : CellExpr bunchedBimonoidOmegaComputad (dim + 1)) →
      bunchedBimonoidBracketGatedEq whiskerAlpha whiskerAlpha' →
      bunchedBimonoidBracketGatedEq (CellExpr.whiskerRight innerCell whiskerAlpha)
        (CellExpr.whiskerRight innerCell whiskerAlpha')
  | 0, innerCell, whiskerAlpha, whiskerAlpha', ⟨_, widthEq⟩ =>
      ⟨Iff.intro
          (fun cleanLeft => bunchedBimonoidAugAndJoin
            (bunchedBimonoidAugAndSplit cleanLeft).1
            (bunchedBimonoidAugCleanOneCell whiskerAlpha'))
          (fun cleanRight => bunchedBimonoidAugAndJoin
            (bunchedBimonoidAugAndSplit cleanRight).1
            (bunchedBimonoidAugCleanOneCell whiskerAlpha)),
        congrArg (fun width => Nat.add
          (bunchedBimonoidAugWordWidth (boundarySource innerCell)) width) widthEq,
        congrArg (fun width => Nat.add
          (bunchedBimonoidAugWordWidth (boundaryTarget innerCell)) width) widthEq,
        fun _ _ _ _ => rfl⟩
  | _ + 1, _, _, _, _ => ⟨Iff.intro (fun _ => rfl) (fun _ => rfl), True.intro⟩

/-! # =========================================================================================
    # G — THE GATED ABSORBER over the FULL UNITAL SCOPE + THE FOLD
    # =========================================================================================
-/

/-- ★★★ **THE BRACKET SEMANTICS GATED-ABSORBS THE FULL UNITAL STAR SCOPE** — every strict omega-law row
(composability-gated, the Clean-equivalences REUSED from the shipped r30 affine absorber by projection),
all 15 sound rows, the 3 hexagon rows, AND the four r30 (co)unit rows hold pointwise in the free commutative
unital magma; the eleven congruence fields transport.  The invariant that finally sees association orders
folds through EVERY unital-scope derivation. -/
def bunchedBimonoidBracketGatedAbsorbsUnitalScope :
    IsSaturatedCongruenceWithId bunchedBimonoidOmegaComputad
      bunchedBimonoidUnitalStarCongruenceScope bunchedBimonoidBracketGatedEq where
  ofRelation := by
    intro dim cellAlpha cellBeta row
    match row with
    | Or.inl (Or.inl strictRow) =>
        match strictRow with
        | .vcompAssoc cellA cellB cellC =>
            exact bunchedBimonoidBracketGatedVcompAssoc cellA cellB cellC
        | .vcompUnitLeft cellA => exact bunchedBimonoidBracketGatedVcompUnitLeft cellA
        | .vcompUnitRight cellA => exact bunchedBimonoidBracketGatedVcompUnitRight cellA
        | .whiskerLeftUnit whiskeringCell innerCell =>
            exact bunchedBimonoidBracketGatedWhiskerLeftUnit whiskeringCell innerCell
        | .whiskerRightUnit innerCell whiskeringCell =>
            exact bunchedBimonoidBracketGatedWhiskerRightUnit innerCell whiskeringCell
        | .whiskerLeftFunctorial whiskeringCell cellBetaInner cellGamma =>
            exact bunchedBimonoidBracketGatedWhiskerLeftFunctorial whiskeringCell cellBetaInner
              cellGamma
        | .whiskerRightFunctorial cellAlphaInner cellBetaInner whiskeringCell =>
            exact bunchedBimonoidBracketGatedWhiskerRightFunctorial cellAlphaInner cellBetaInner
              whiskeringCell
        | .interchange cellAlphaInner cellBetaInner =>
            exact bunchedBimonoidBracketGatedInterchange cellAlphaInner cellBetaInner
        | .whiskerAssocLeft whiskP whiskQ innerCell =>
            exact bunchedBimonoidBracketGatedWhiskerAssocLeft whiskP whiskQ innerCell
        | .whiskerAssocRight innerCell whiskP whiskQ =>
            exact bunchedBimonoidBracketGatedWhiskerAssocRight innerCell whiskP whiskQ
        | .whiskerLeftRightCommute whiskP innerCell whiskQ =>
            exact bunchedBimonoidBracketGatedWhiskerLeftRightCommute whiskP innerCell whiskQ
    | Or.inl (Or.inr (Or.inl soundRow)) =>
        match soundRow with
        | .multMonadPentagon =>
            exact ⟨Iff.intro (fun _ => by decide) (fun _ => by decide), rfl, rfl,
              fun _ _ args =>
                match args with
                | [] => fun lengthPin => Nat.noConfusion lengthPin
                | [_] => fun lengthPin => Nat.noConfusion (Nat.succ.inj lengthPin)
                | [_, _] => fun lengthPin =>
                    Nat.noConfusion (Nat.succ.inj (Nat.succ.inj lengthPin))
                | [_, _, _] => fun lengthPin =>
                    Nat.noConfusion (Nat.succ.inj (Nat.succ.inj (Nat.succ.inj lengthPin)))
                | _ :: _ :: _ :: _ :: rest => fun lengthPin => by
                    have restNil := bunchedBimonoidBracketNilOfLengthZero rest
                      (Nat.succ.inj (Nat.succ.inj (Nat.succ.inj (Nat.succ.inj lengthPin))))
                    subst restNil
                    rfl⟩
        | .multMonadRootUnitAssoc =>
            exact ⟨Iff.intro (fun _ => by decide) (fun _ => by decide), rfl, rfl,
              fun _ _ args =>
                match args with
                | [] => fun lengthPin => Nat.noConfusion lengthPin
                | [_] => fun lengthPin => Nat.noConfusion (Nat.succ.inj lengthPin)
                | _ :: _ :: rest => fun lengthPin => by
                    have restNil := bunchedBimonoidBracketNilOfLengthZero rest
                      (Nat.succ.inj (Nat.succ.inj lengthPin))
                    subst restNil
                    rfl⟩
        | .addMonadPentagon =>
            exact ⟨Iff.intro (fun _ => by decide) (fun _ => by decide), rfl, rfl,
              fun _ _ args =>
                match args with
                | [] => fun lengthPin => Nat.noConfusion lengthPin
                | [_] => fun lengthPin => Nat.noConfusion (Nat.succ.inj lengthPin)
                | [_, _] => fun lengthPin =>
                    Nat.noConfusion (Nat.succ.inj (Nat.succ.inj lengthPin))
                | [_, _, _] => fun lengthPin =>
                    Nat.noConfusion (Nat.succ.inj (Nat.succ.inj (Nat.succ.inj lengthPin)))
                | _ :: _ :: _ :: _ :: rest => fun lengthPin => by
                    have restNil := bunchedBimonoidBracketNilOfLengthZero rest
                      (Nat.succ.inj (Nat.succ.inj (Nat.succ.inj (Nat.succ.inj lengthPin))))
                    subst restNil
                    rfl⟩
        | .addMonadRootUnitAssoc =>
            exact ⟨Iff.intro (fun _ => by decide) (fun _ => by decide), rfl, rfl,
              fun _ _ args =>
                match args with
                | [] => fun lengthPin => Nat.noConfusion lengthPin
                | [_] => fun lengthPin => Nat.noConfusion (Nat.succ.inj lengthPin)
                | _ :: _ :: rest => fun lengthPin => by
                    have restNil := bunchedBimonoidBracketNilOfLengthZero rest
                      (Nat.succ.inj (Nat.succ.inj lengthPin))
                    subst restNil
                    rfl⟩
        | .comonoidCopentagon =>
            exact ⟨Iff.intro (fun _ => by decide) (fun _ => by decide), rfl, rfl,
              fun _ _ args =>
                match args with
                | [] => fun lengthPin => Nat.noConfusion lengthPin
                | [_] => fun lengthPin => Nat.noConfusion (Nat.succ.inj lengthPin)
                | _ :: _ :: rest => fun lengthPin => by
                    have restNil := bunchedBimonoidBracketNilOfLengthZero rest
                      (Nat.succ.inj (Nat.succ.inj lengthPin))
                    subst restNil
                    rfl⟩
        | .comonoidRootCounitCoassoc =>
            exact ⟨Iff.intro (fun _ => by decide) (fun _ => by decide), rfl, rfl,
              fun _ _ args =>
                match args with
                | [] => fun lengthPin => Nat.noConfusion lengthPin
                | [_] => fun lengthPin => Nat.noConfusion (Nat.succ.inj lengthPin)
                | _ :: _ :: rest => fun lengthPin => by
                    have restNil := bunchedBimonoidBracketNilOfLengthZero rest
                      (Nat.succ.inj (Nat.succ.inj lengthPin))
                    subst restNil
                    rfl⟩
        | .bialgebraProduct =>
            exact ⟨Iff.intro (fun _ => by decide) (fun _ => by decide), rfl, rfl,
              fun _ _ args =>
                match args with
                | [] => fun lengthPin => Nat.noConfusion lengthPin
                | [_] => fun lengthPin => Nat.noConfusion (Nat.succ.inj lengthPin)
                | _ :: _ :: rest => fun lengthPin => by
                    have restNil := bunchedBimonoidBracketNilOfLengthZero rest
                      (Nat.succ.inj (Nat.succ.inj lengthPin))
                    subst restNil
                    rfl⟩
        | .bialgebraCounit =>
            exact ⟨Iff.intro (fun _ => by decide) (fun _ => by decide), rfl, rfl,
              fun _ _ args =>
                match args with
                | [] => fun lengthPin => Nat.noConfusion lengthPin
                | [_] => fun lengthPin => Nat.noConfusion (Nat.succ.inj lengthPin)
                | _ :: _ :: rest => fun lengthPin => by
                    have restNil := bunchedBimonoidBracketNilOfLengthZero rest
                      (Nat.succ.inj (Nat.succ.inj lengthPin))
                    subst restNil
                    rfl⟩
        | .bialgebraUnit =>
            exact ⟨Iff.intro (fun _ => by decide) (fun _ => by decide), rfl, rfl,
              fun _ _ args =>
                match args with
                | [] => fun _ => rfl
                | _ :: _ => fun lengthPin => Nat.noConfusion lengthPin⟩
        | .bialgebraBone =>
            exact ⟨Iff.intro (fun _ => by decide) (fun _ => by decide), rfl, rfl,
              fun _ _ args =>
                match args with
                | [] => fun _ => rfl
                | _ :: _ => fun lengthPin => Nat.noConfusion lengthPin⟩
        | .commutativity =>
            exact ⟨Iff.intro (fun _ => by decide) (fun _ => by decide), rfl, rfl,
              fun _ _ args =>
                match args with
                | [] => fun lengthPin => Nat.noConfusion lengthPin
                | [_] => fun lengthPin => Nat.noConfusion (Nat.succ.inj lengthPin)
                | firstTree :: secondTree :: rest => fun lengthPin => by
                    have restNil := bunchedBimonoidBracketNilOfLengthZero rest
                      (Nat.succ.inj (Nat.succ.inj lengthPin))
                    subst restNil
                    show [bunchedBimonoidBracketMul secondTree firstTree]
                      = [bunchedBimonoidBracketMul firstTree secondTree]
                    rw [bunchedBimonoidBracketMulComm secondTree firstTree]⟩
        | .cocommutativity =>
            exact ⟨Iff.intro (fun _ => by decide) (fun _ => by decide), rfl, rfl,
              fun _ _ args =>
                match args with
                | [] => fun lengthPin => Nat.noConfusion lengthPin
                | _ :: rest => fun lengthPin => by
                    have restNil := bunchedBimonoidBracketNilOfLengthZero rest
                      (Nat.succ.inj lengthPin)
                    subst restNil
                    rfl⟩
        | .sigmaInvolution =>
            exact ⟨Iff.intro (fun _ => by decide) (fun _ => by decide), rfl, rfl,
              fun _ _ args =>
                match args with
                | [] => fun lengthPin => Nat.noConfusion lengthPin
                | [_] => fun lengthPin => Nat.noConfusion (Nat.succ.inj lengthPin)
                | _ :: _ :: rest => fun lengthPin => by
                    have restNil := bunchedBimonoidBracketNilOfLengthZero rest
                      (Nat.succ.inj (Nat.succ.inj lengthPin))
                    subst restNil
                    rfl⟩
        | .sigmaEtaNaturality =>
            exact ⟨Iff.intro (fun _ => by decide) (fun _ => by decide), rfl, rfl,
              fun _ _ args =>
                match args with
                | [] => fun lengthPin => Nat.noConfusion lengthPin
                | _ :: rest => fun lengthPin => by
                    have restNil := bunchedBimonoidBracketNilOfLengthZero rest
                      (Nat.succ.inj lengthPin)
                    subst restNil
                    rfl⟩
        | .sigmaEpsNaturality =>
            exact ⟨Iff.intro (fun _ => by decide) (fun _ => by decide), rfl, rfl,
              fun _ _ args =>
                match args with
                | [] => fun lengthPin => Nat.noConfusion lengthPin
                | [_] => fun lengthPin => Nat.noConfusion (Nat.succ.inj lengthPin)
                | _ :: _ :: rest => fun lengthPin => by
                    have restNil := bunchedBimonoidBracketNilOfLengthZero rest
                      (Nat.succ.inj (Nat.succ.inj lengthPin))
                    subst restNil
                    rfl⟩
    | Or.inl (Or.inr (Or.inr hexRow)) =>
        match hexRow with
        | .yangBaxter =>
            exact ⟨Iff.intro (fun _ => by decide) (fun _ => by decide), rfl, rfl,
              fun _ _ args =>
                match args with
                | [] => fun lengthPin => Nat.noConfusion lengthPin
                | [_] => fun lengthPin => Nat.noConfusion (Nat.succ.inj lengthPin)
                | [_, _] => fun lengthPin =>
                    Nat.noConfusion (Nat.succ.inj (Nat.succ.inj lengthPin))
                | _ :: _ :: _ :: rest => fun lengthPin => by
                    have restNil := bunchedBimonoidBracketNilOfLengthZero rest
                      (Nat.succ.inj (Nat.succ.inj (Nat.succ.inj lengthPin)))
                    subst restNil
                    rfl⟩
        | .muNaturality =>
            exact ⟨Iff.intro (fun _ => by decide) (fun _ => by decide), rfl, rfl,
              fun _ _ args =>
                match args with
                | [] => fun lengthPin => Nat.noConfusion lengthPin
                | [_] => fun lengthPin => Nat.noConfusion (Nat.succ.inj lengthPin)
                | [_, _] => fun lengthPin =>
                    Nat.noConfusion (Nat.succ.inj (Nat.succ.inj lengthPin))
                | _ :: _ :: _ :: rest => fun lengthPin => by
                    have restNil := bunchedBimonoidBracketNilOfLengthZero rest
                      (Nat.succ.inj (Nat.succ.inj (Nat.succ.inj lengthPin)))
                    subst restNil
                    rfl⟩
        | .deltaNaturality =>
            exact ⟨Iff.intro (fun _ => by decide) (fun _ => by decide), rfl, rfl,
              fun _ _ args =>
                match args with
                | [] => fun lengthPin => Nat.noConfusion lengthPin
                | [_] => fun lengthPin => Nat.noConfusion (Nat.succ.inj lengthPin)
                | _ :: _ :: rest => fun lengthPin => by
                    have restNil := bunchedBimonoidBracketNilOfLengthZero rest
                      (Nat.succ.inj (Nat.succ.inj lengthPin))
                    subst restNil
                    rfl⟩
    | Or.inr unitRow =>
        match unitRow with
        | .rightUnit =>
            exact ⟨Iff.intro (fun _ => by decide) (fun _ => by decide), rfl, rfl,
              fun _ _ args =>
                match args with
                | [] => fun lengthPin => Nat.noConfusion lengthPin
                | strandTree :: rest => fun lengthPin => by
                    have restNil := bunchedBimonoidBracketNilOfLengthZero rest
                      (Nat.succ.inj lengthPin)
                    subst restNil
                    show [bunchedBimonoidBracketMul strandTree .unitLeaf] = [strandTree]
                    rw [bunchedBimonoidBracketMulUnitRight strandTree]⟩
        | .leftUnit =>
            exact ⟨Iff.intro (fun _ => by decide) (fun _ => by decide), rfl, rfl,
              fun _ _ args =>
                match args with
                | [] => fun lengthPin => Nat.noConfusion lengthPin
                | _ :: rest => fun lengthPin => by
                    have restNil := bunchedBimonoidBracketNilOfLengthZero rest
                      (Nat.succ.inj lengthPin)
                    subst restNil
                    rfl⟩
        | .rightCounit =>
            exact ⟨Iff.intro (fun _ => by decide) (fun _ => by decide), rfl, rfl,
              fun _ _ args =>
                match args with
                | [] => fun lengthPin => Nat.noConfusion lengthPin
                | _ :: rest => fun lengthPin => by
                    have restNil := bunchedBimonoidBracketNilOfLengthZero rest
                      (Nat.succ.inj lengthPin)
                    subst restNil
                    rfl⟩
        | .leftCounit =>
            exact ⟨Iff.intro (fun _ => by decide) (fun _ => by decide), rfl, rfl,
              fun _ _ args =>
                match args with
                | [] => fun lengthPin => Nat.noConfusion lengthPin
                | _ :: rest => fun lengthPin => by
                    have restNil := bunchedBimonoidBracketNilOfLengthZero rest
                      (Nat.succ.inj lengthPin)
                    subst restNil
                    rfl⟩
  vcompCongrLeft := fun gatedRel =>
    bunchedBimonoidBracketGatedVcompCongrLeft _ _ _ _ gatedRel
  vcompCongrRight := fun gatedRel =>
    bunchedBimonoidBracketGatedVcompCongrRight _ _ _ _ gatedRel
  whiskerLeftCongr := fun gatedRel =>
    bunchedBimonoidBracketGatedWhiskerLeftCongr _ _ _ _ gatedRel
  whiskerRightCongr := fun gatedRel =>
    bunchedBimonoidBracketGatedWhiskerRightCongr _ _ _ _ gatedRel
  idCongr := fun gatedRel =>
    bunchedBimonoidBracketGatedIdCongr _ _ _ gatedRel
  whiskerLeftWhiskerCongr := fun gatedRel =>
    bunchedBimonoidBracketGatedWhiskerLeftWhiskerCongr _ _ _ _ gatedRel
  whiskerRightWhiskerCongr := fun gatedRel =>
    bunchedBimonoidBracketGatedWhiskerRightWhiskerCongr _ _ _ _ gatedRel
  refl := fun cell => ⟨Iff.rfl, bunchedBimonoidBracketAgreeRefl cell⟩
  symm := fun gatedRel => ⟨gatedRel.1.symm, bunchedBimonoidBracketAgreeSymm gatedRel.2⟩
  trans := fun gatedLeft gatedRight =>
    ⟨gatedLeft.1.trans gatedRight.1,
      bunchedBimonoidBracketAgreeTrans gatedLeft.1.mp gatedLeft.2 gatedRight.2⟩

/-- ★★★ **THE FOLD** — unital-scope convertibility implies gated bracket equality. -/
theorem bunchedBimonoidBracketGatedEqOfUnitalConv {dim : Nat}
    {cellAlpha cellBeta : CellExpr bunchedBimonoidOmegaComputad dim}
    (conv : SaturatedConvOverWithId bunchedBimonoidOmegaComputad
      bunchedBimonoidUnitalStarCongruenceScope cellAlpha cellBeta) :
    bunchedBimonoidBracketGatedEq cellAlpha cellBeta :=
  SaturatedConvOverWithId.recInto bunchedBimonoidBracketGatedAbsorbsUnitalScope conv

/-! ## The honesty markers -/

/-- ★★★ **ESTABLISHED — the bracket-magma semantics absorbs the FULL unital star scope,
composability-gated.**  `= true` records `bunchedBimonoidBracketGatedAbsorbsUnitalScope`: all eleven strict
omega-law rows (Clean-equivalences reused from the r30 affine absorber by projection; the gated splits routed
by the bracket shape invariant), the 15 sound rows, the 3 hexagon rows, AND the four r30 (co)unit rows hold
pointwise in the free commutative unital magma, with all eleven congruence fields transporting.  The
association-order invariant (`bunchedBimonoidLeftAssocBracketValue` vs `bunchedBimonoidRightAssocBracketValue`)
now folds through EVERY unital-scope derivation. -/
def fxBunchedBimonoid_bracketMagmaAbsorberShipped : Bool := true

end FX1Poly.Polygraph.Omega
