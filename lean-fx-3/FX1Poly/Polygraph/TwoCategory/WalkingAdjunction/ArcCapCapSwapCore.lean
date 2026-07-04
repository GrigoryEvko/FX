import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcPartitionSimStep
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcWindowCommutation
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcFreshBlockTransposition

/-! # WalkingAdjunction/ArcCapCapSwapCore — the CAP x CAP two-step partition-simulation core

The FOURTH two-step swap combo, in the corrected vehicle.  Both cap-cap obstructions
(`ArcCapCapSwapObstruction`, `ArcCapCapAgreeObstruction`) showed the renaming and plain-agreement
vehicles fail here; the target is `ArcPartitionSim` under the EVENT TRANSPOSITION
`arcFreshBlockTransposition state.nextFresh 1 1` (the swap `nf <-> nf + 1` of the two cap event
nodes, fixing everything else).

This file opens the core with the WIRE leg: the two run orders produce the SAME open-wire list
(`natListRemoveTwoAt_removeAbove_commute` — removing the high pair first and then the low pair
equals removing low-first and then at the down-shifted position), and the transposition fixes
every remaining wire (wires are OLD nodes, strictly below `nextFresh`), so the `openMap` field
holds with the map degenerating to the identity. -/

namespace FX1Poly.Polygraph

/-- ★ **The cap-cap `openMap` leg.**  HIGH-first wires (`removeTwoAt` at `gap + 2 + positionLow`
then at `positionLow`) equal the `sigma`-image of LOW-first wires (`removeTwoAt` at
`positionLow` then at `gap + positionLow`): the raw lists agree by the unconditional
remove-remove commutation, and the event transposition fixes every surviving wire
(`arcFreshBlockTransposition_ofBelow` on the freshness bound, through two `removeTwoAt`
membership projections). -/
theorem capCapSwap_openMap (state : ArcWireState) (positionLow gap : Nat)
    (wiresFresh : ∀ wire ∈ state.openWires, wire < state.nextFresh) :
    (stepCapArc (stepCapArc state (gap + 2 + positionLow)) positionLow).openWires
      = ((stepCapArc (stepCapArc state positionLow) (gap + positionLow)).openWires).map
          (arcFreshBlockTransposition state.nextFresh 1 1) := by
  show natListRemoveTwoAt (natListRemoveTwoAt state.openWires (gap + 2 + positionLow))
        positionLow
     = (natListRemoveTwoAt (natListRemoveTwoAt state.openWires positionLow)
         (gap + positionLow)).map (arcFreshBlockTransposition state.nextFresh 1 1)
  rw [natListRemoveTwoAt_removeAbove_commute state.openWires positionLow gap,
    mapFixedOn (arcFreshBlockTransposition state.nextFresh 1 1)
      (natListRemoveTwoAt (natListRemoveTwoAt state.openWires positionLow) (gap + positionLow))
      (fun wire wireMember =>
        arcFreshBlockTransposition_ofBelow state.nextFresh 1 1 wire
          (wiresFresh wire
            (mem_natListRemoveTwoAt state.openWires positionLow wire
              (mem_natListRemoveTwoAt
                (natListRemoveTwoAt state.openWires positionLow)
                (gap + positionLow) wire wireMember))))]

/-- `Nat` boolean equality is reflexive (`==` is `decide (· = ·)`). -/
theorem natBeq_self (value : Nat) : (value == value) = true :=
  decide_eq_true rfl

/-- `Nat` boolean equality is symmetric as a `Bool`-valued equation. -/
theorem natBeq_comm (firstValue secondValue : Nat) :
    (firstValue == secondValue) = (secondValue == firstValue) := by
  cases forwardWitness : (firstValue == secondValue) with
  | true =>
      have valuesEqual : firstValue = secondValue := of_decide_eq_true forwardWitness
      rw [valuesEqual, natBeq_self]
  | false =>
      cases backwardWitness : (secondValue == firstValue) with
      | true =>
          have valuesEqual : secondValue = firstValue := of_decide_eq_true backwardWitness
          rw [valuesEqual, natBeq_self] at forwardWitness
          exact Bool.noConfusion forwardWitness
      | false => rfl

/-- `false && bit = false` as a rewritable equation (definitional, but `rw` needs the lemma). -/
theorem boolFalseAnd (bit : Bool) : (false && bit) = false := rfl

/-- `bit || false = bit` — `||` matches on its FIRST argument, so this needs a case split. -/
theorem boolOrFalse (bit : Bool) : (bit || false) = bit := by
  cases bit with
  | true => rfl
  | false => rfl

/-- `true || bit = true` as a rewritable equation. -/
theorem boolTrueOr (bit : Bool) : (true || bit) = true := rfl

/-- `false || bit = bit` as a rewritable equation. -/
theorem boolFalseOr (bit : Bool) : (false || bit) = bit := rfl

/-- `true && bit = bit` as a rewritable equation. -/
theorem boolTrueAnd (bit : Bool) : (true && bit) = bit := rfl

/-- ★ **The boolean JOIN SPLIT — one merge, characterized at the partition level.**  After
joining `firstNode` and `secondNode`, two queries share a component iff they already did, or
they sit crosswise in the two merged components.  This is the elementwise characterization the
cap-cap `componentsCorr` and `loopsEq` legs case over: it expresses the after-join partition
purely in PRE-join same-component booleans, with no representative mentioned.  Four cases over
the two after-join root-formula guards; each leaf reduces by `Nat`-beq reflexivity/symmetry and
`Bool` absorption. -/
theorem isSameComponent_unionFindJoin_split (links : List (Nat × Nat))
    (hforest : isUnionFindForest links)
    (firstNode secondNode queryLeft queryRight : Nat) :
    isSameComponent (unionFindJoin links firstNode secondNode) queryLeft queryRight
      = (isSameComponent links queryLeft queryRight
          || (isSameComponent links firstNode queryLeft
               && isSameComponent links secondNode queryRight)
          || (isSameComponent links firstNode queryRight
               && isSameComponent links secondNode queryLeft)) := by
  show (unionFindRootOf (unionFindJoin links firstNode secondNode) queryLeft
          == unionFindRootOf (unionFindJoin links firstNode secondNode) queryRight)
     = ((unionFindRootOf links queryLeft == unionFindRootOf links queryRight)
         || ((unionFindRootOf links firstNode == unionFindRootOf links queryLeft)
              && (unionFindRootOf links secondNode == unionFindRootOf links queryRight))
         || ((unionFindRootOf links firstNode == unionFindRootOf links queryRight)
              && (unionFindRootOf links secondNode == unionFindRootOf links queryLeft)))
  rw [unionFindRootOf_unionFindJoin links firstNode secondNode queryLeft hforest,
    unionFindRootOf_unionFindJoin links firstNode secondNode queryRight hforest]
  cases guardLeft : (unionFindRootOf links firstNode == unionFindRootOf links queryLeft) with
  | true =>
      have rootLeftEq : unionFindRootOf links firstNode = unionFindRootOf links queryLeft :=
        of_decide_eq_true guardLeft
      cases guardRight : (unionFindRootOf links firstNode
          == unionFindRootOf links queryRight) with
      | true =>
          have rootRightEq : unionFindRootOf links firstNode
              = unionFindRootOf links queryRight := of_decide_eq_true guardRight
          show (unionFindRootOf links secondNode == unionFindRootOf links secondNode)
             = ((unionFindRootOf links queryLeft == unionFindRootOf links queryRight)
                 || (true && (unionFindRootOf links secondNode
                       == unionFindRootOf links queryRight))
                 || (true && (unionFindRootOf links secondNode
                       == unionFindRootOf links queryLeft)))
          rw [natBeq_self (unionFindRootOf links secondNode), ← rootLeftEq, ← rootRightEq,
            natBeq_self (unionFindRootOf links firstNode), boolTrueOr, boolTrueOr]
      | false =>
          show (unionFindRootOf links secondNode == unionFindRootOf links queryRight)
             = ((unionFindRootOf links queryLeft == unionFindRootOf links queryRight)
                 || (true && (unionFindRootOf links secondNode
                       == unionFindRootOf links queryRight))
                 || (false && (unionFindRootOf links secondNode
                       == unionFindRootOf links queryLeft)))
          rw [← rootLeftEq, guardRight,
            boolFalseAnd (unionFindRootOf links secondNode == unionFindRootOf links firstNode),
            boolOrFalse, boolFalseOr, boolTrueAnd]
  | false =>
      cases guardRight : (unionFindRootOf links firstNode
          == unionFindRootOf links queryRight) with
      | true =>
          have rootRightEq : unionFindRootOf links firstNode
              = unionFindRootOf links queryRight := of_decide_eq_true guardRight
          show (unionFindRootOf links queryLeft == unionFindRootOf links secondNode)
             = ((unionFindRootOf links queryLeft == unionFindRootOf links queryRight)
                 || (false && (unionFindRootOf links secondNode
                       == unionFindRootOf links queryRight))
                 || (true && (unionFindRootOf links secondNode
                       == unionFindRootOf links queryLeft)))
          rw [← rootRightEq,
            natBeq_comm (unionFindRootOf links queryLeft) (unionFindRootOf links firstNode),
            guardLeft,
            natBeq_comm (unionFindRootOf links secondNode) (unionFindRootOf links queryLeft),
            boolFalseAnd (unionFindRootOf links secondNode == unionFindRootOf links firstNode),
            boolFalseOr, boolFalseOr, boolTrueAnd]
      | false =>
          show (unionFindRootOf links queryLeft == unionFindRootOf links queryRight)
             = ((unionFindRootOf links queryLeft == unionFindRootOf links queryRight)
                 || (false && (unionFindRootOf links secondNode
                       == unionFindRootOf links queryRight))
                 || (false && (unionFindRootOf links secondNode
                       == unionFindRootOf links queryLeft)))
          rw [boolFalseAnd (unionFindRootOf links secondNode
              == unionFindRootOf links queryRight),
            boolFalseAnd (unionFindRootOf links secondNode
              == unionFindRootOf links queryLeft),
            boolOrFalse, boolOrFalse]

/-- `Bool` equality from the two `= true` implications — the zero-axiom `Bool`-of-iff shuttle. -/
theorem boolEqOfIff (leftBit rightBit : Bool)
    (forward : leftBit = true → rightBit = true)
    (backward : rightBit = true → leftBit = true) : leftBit = rightBit := by
  cases leftBit with
  | true =>
      cases rightBit with
      | true => rfl
      | false => exact Bool.noConfusion (forward rfl)
  | false =>
      cases rightBit with
      | true => exact Bool.noConfusion (backward rfl)
      | false => rfl

/-- Destructor: a true disjunction has a true disjunct. -/
theorem orElimBit (left right : Bool) (h : (left || right) = true) :
    left = true ∨ right = true := by
  cases left with
  | true => exact Or.inl rfl
  | false =>
      rw [boolFalseOr] at h
      exact Or.inr h

/-- Constructor: a true LEFT disjunct makes the disjunction true. -/
theorem orIntroLeftBit (left right : Bool) (h : left = true) : (left || right) = true := by
  rw [h, boolTrueOr]

/-- Constructor: a true RIGHT disjunct makes the disjunction true. -/
theorem orIntroRightBit (left right : Bool) (h : right = true) : (left || right) = true := by
  rw [h]
  cases left with
  | true => exact boolTrueOr true
  | false => exact boolFalseOr true

/-- Destructor: a true conjunction has two true conjuncts. -/
theorem andElimBit (left right : Bool) (h : (left && right) = true) :
    left = true ∧ right = true := by
  cases left with
  | true =>
      rw [boolTrueAnd] at h
      exact And.intro rfl h
  | false =>
      rw [boolFalseAnd] at h
      exact Bool.noConfusion h

/-- Constructor: two true conjuncts make the conjunction true. -/
theorem andIntroBit (left right : Bool) (leftTrue : left = true) (rightTrue : right = true) :
    (left && right) = true := by
  rw [leftTrue, rightTrue, boolTrueAnd]

/-- The `Prop` reading of `isSameComponent`: the boolean is true exactly when the two roots are
EQUAL as naturals — the shuttle that makes same-component facts compose by `Eq.trans`/`Eq.symm`. -/
theorem isSameComponent_true_iff_rootsEqual (links : List (Nat × Nat))
    (firstNode secondNode : Nat) :
    isSameComponent links firstNode secondNode = true
      ↔ unionFindRootOf links firstNode = unionFindRootOf links secondNode :=
  Iff.intro
    (fun sameTrue => of_decide_eq_true
      (show (unionFindRootOf links firstNode == unionFindRootOf links secondNode) = true
        from sameTrue))
    (fun rootsEqual =>
      show (unionFindRootOf links firstNode == unionFindRootOf links secondNode) = true
        from decide_eq_true rootsEqual)

/-- Same-component truth is symmetric (through the root reading). -/
theorem isSameComponent_true_symm (links : List (Nat × Nat)) (firstNode secondNode : Nat)
    (h : isSameComponent links firstNode secondNode = true) :
    isSameComponent links secondNode firstNode = true :=
  (isSameComponent_true_iff_rootsEqual links secondNode firstNode).mpr
    ((isSameComponent_true_iff_rootsEqual links firstNode secondNode).mp h).symm

/-- The `Prop`-level reading of the boolean join split: after-join same-component truth is the
three-way disjunction over pre-join same-component truths. -/
theorem isSameComponent_unionFindJoin_true_iff (links : List (Nat × Nat))
    (hforest : isUnionFindForest links) (firstNode secondNode queryLeft queryRight : Nat) :
    isSameComponent (unionFindJoin links firstNode secondNode) queryLeft queryRight = true
      ↔ (isSameComponent links queryLeft queryRight = true
          ∨ (isSameComponent links firstNode queryLeft = true
               ∧ isSameComponent links secondNode queryRight = true)
          ∨ (isSameComponent links firstNode queryRight = true
               ∧ isSameComponent links secondNode queryLeft = true)) := by
  rw [isSameComponent_unionFindJoin_split links hforest firstNode secondNode
    queryLeft queryRight]
  constructor
  · intro combinedTrue
    cases orElimBit _ _ combinedTrue with
    | inl frontTrue =>
        cases orElimBit _ _ frontTrue with
        | inl directTrue => exact Or.inl directTrue
        | inr crossTrue => exact Or.inr (Or.inl (andElimBit _ _ crossTrue))
    | inr mirrorTrue => exact Or.inr (Or.inr (andElimBit _ _ mirrorTrue))
  · intro disjunction
    cases disjunction with
    | inl directTrue => exact orIntroLeftBit _ _ (orIntroLeftBit _ _ directTrue)
    | inr crossOrMirror =>
        cases crossOrMirror with
        | inl crossPair =>
            exact orIntroLeftBit _ _
              (orIntroRightBit _ _ (andIntroBit _ _ crossPair.1 crossPair.2))
        | inr mirrorPair =>
            exact orIntroRightBit _ _ (andIntroBit _ _ mirrorPair.1 mirrorPair.2)

/-- ★ **The cross-connection swap core.**  If the two later-join nodes reach the two queries
THROUGH the first join (`laterFirst ~ queryLeft` and `laterSecond ~ queryRight` over
`join links firstNode secondNode`), then the queries are connected in the SWAPPED double join
(`firstNode`/`secondNode` joined over `join links laterFirst laterSecond`).  Nine leaves: each
cross hypothesis splits three ways at the base level, and every combination reassembles on the
swapped side by root symmetry/transitivity. -/
theorem isSameComponent_join_cross_swap (links : List (Nat × Nat))
    (hforest : isUnionFindForest links)
    (firstNode secondNode laterFirst laterSecond queryLeft queryRight : Nat)
    (crossLeft : isSameComponent (unionFindJoin links firstNode secondNode)
        laterFirst queryLeft = true)
    (crossRight : isSameComponent (unionFindJoin links firstNode secondNode)
        laterSecond queryRight = true) :
    isSameComponent (unionFindJoin (unionFindJoin links laterFirst laterSecond)
        firstNode secondNode) queryLeft queryRight = true := by
  have forestLater : isUnionFindForest (unionFindJoin links laterFirst laterSecond) :=
    isUnionFindForest_unionFindJoin links laterFirst laterSecond hforest
  refine (isSameComponent_unionFindJoin_true_iff (unionFindJoin links laterFirst laterSecond)
    forestLater firstNode secondNode queryLeft queryRight).mpr ?_
  cases (isSameComponent_unionFindJoin_true_iff links hforest firstNode secondNode
      laterFirst queryLeft).mp crossLeft with
  | inl sameLaterFirstLeft =>
      cases (isSameComponent_unionFindJoin_true_iff links hforest firstNode secondNode
          laterSecond queryRight).mp crossRight with
      | inl sameLaterSecondRight =>
          exact Or.inl ((isSameComponent_unionFindJoin_true_iff links hforest laterFirst
            laterSecond queryLeft queryRight).mpr
            (Or.inr (Or.inl (And.intro sameLaterFirstLeft sameLaterSecondRight))))
      | inr rightCrossOrMirror =>
          cases rightCrossOrMirror with
          | inl rightCross =>
              exact Or.inr (Or.inl (And.intro
                ((isSameComponent_unionFindJoin_true_iff links hforest laterFirst laterSecond
                  firstNode queryLeft).mpr (Or.inr (Or.inr (And.intro sameLaterFirstLeft
                    (isSameComponent_true_symm links firstNode laterSecond rightCross.1)))))
                ((isSameComponent_unionFindJoin_true_iff links hforest laterFirst laterSecond
                  secondNode queryRight).mpr (Or.inl rightCross.2))))
          | inr rightMirror =>
              exact Or.inr (Or.inr (And.intro
                ((isSameComponent_unionFindJoin_true_iff links hforest laterFirst laterSecond
                  firstNode queryRight).mpr (Or.inl rightMirror.1))
                ((isSameComponent_unionFindJoin_true_iff links hforest laterFirst laterSecond
                  secondNode queryLeft).mpr (Or.inr (Or.inr (And.intro sameLaterFirstLeft
                    (isSameComponent_true_symm links secondNode laterSecond
                      rightMirror.2)))))))
  | inr leftCrossOrMirror =>
      cases leftCrossOrMirror with
      | inl leftCross =>
          cases (isSameComponent_unionFindJoin_true_iff links hforest firstNode secondNode
              laterSecond queryRight).mp crossRight with
          | inl sameLaterSecondRight =>
              exact Or.inr (Or.inr (And.intro
                ((isSameComponent_unionFindJoin_true_iff links hforest laterFirst laterSecond
                  firstNode queryRight).mpr (Or.inr (Or.inl (And.intro
                    (isSameComponent_true_symm links firstNode laterFirst leftCross.1)
                    sameLaterSecondRight))))
                ((isSameComponent_unionFindJoin_true_iff links hforest laterFirst laterSecond
                  secondNode queryLeft).mpr (Or.inl leftCross.2))))
          | inr rightCrossOrMirror =>
              cases rightCrossOrMirror with
              | inl rightCross =>
                  have rootsLeftRight : unionFindRootOf links queryLeft
                      = unionFindRootOf links queryRight :=
                    ((isSameComponent_true_iff_rootsEqual links secondNode
                      queryLeft).mp leftCross.2).symm.trans
                      ((isSameComponent_true_iff_rootsEqual links secondNode
                        queryRight).mp rightCross.2)
                  exact Or.inl ((isSameComponent_unionFindJoin_true_iff links hforest laterFirst
                    laterSecond queryLeft queryRight).mpr (Or.inl
                    ((isSameComponent_true_iff_rootsEqual links queryLeft
                      queryRight).mpr rootsLeftRight)))
              | inr rightMirror =>
                  exact Or.inr (Or.inr (And.intro
                    ((isSameComponent_unionFindJoin_true_iff links hforest laterFirst
                      laterSecond firstNode queryRight).mpr (Or.inl rightMirror.1))
                    ((isSameComponent_unionFindJoin_true_iff links hforest laterFirst
                      laterSecond secondNode queryLeft).mpr (Or.inl leftCross.2))))
      | inr leftMirror =>
          cases (isSameComponent_unionFindJoin_true_iff links hforest firstNode secondNode
              laterSecond queryRight).mp crossRight with
          | inl sameLaterSecondRight =>
              exact Or.inr (Or.inl (And.intro
                ((isSameComponent_unionFindJoin_true_iff links hforest laterFirst laterSecond
                  firstNode queryLeft).mpr (Or.inl leftMirror.1))
                ((isSameComponent_unionFindJoin_true_iff links hforest laterFirst laterSecond
                  secondNode queryRight).mpr (Or.inr (Or.inl (And.intro
                    (isSameComponent_true_symm links secondNode laterFirst leftMirror.2)
                    sameLaterSecondRight))))))
          | inr rightCrossOrMirror =>
              cases rightCrossOrMirror with
              | inl rightCross =>
                  exact Or.inr (Or.inl (And.intro
                    ((isSameComponent_unionFindJoin_true_iff links hforest laterFirst
                      laterSecond firstNode queryLeft).mpr (Or.inl leftMirror.1))
                    ((isSameComponent_unionFindJoin_true_iff links hforest laterFirst
                      laterSecond secondNode queryRight).mpr (Or.inl rightCross.2))))
              | inr rightMirror =>
                  have rootsLeftRight : unionFindRootOf links queryLeft
                      = unionFindRootOf links queryRight :=
                    ((isSameComponent_true_iff_rootsEqual links firstNode
                      queryLeft).mp leftMirror.1).symm.trans
                      ((isSameComponent_true_iff_rootsEqual links firstNode
                        queryRight).mp rightMirror.1)
                  exact Or.inl ((isSameComponent_unionFindJoin_true_iff links hforest laterFirst
                    laterSecond queryLeft queryRight).mpr (Or.inl
                    ((isSameComponent_true_iff_rootsEqual links queryLeft
                      queryRight).mpr rootsLeftRight)))

/-- One direction of the two-join commutation: connectivity in `join (join links a b) c d`
transfers to `join (join links c d) a b`.  Three top cases: a through-first-join connection
re-expands and lifts disjunct-by-disjunct; the two cross connections are the cross-swap core
(the mirror one after swapping the queries and symmetrizing). -/
theorem isSameComponent_two_joins_swap (links : List (Nat × Nat))
    (hforest : isUnionFindForest links)
    (firstNode secondNode laterFirst laterSecond queryLeft queryRight : Nat)
    (h : isSameComponent (unionFindJoin (unionFindJoin links firstNode secondNode)
        laterFirst laterSecond) queryLeft queryRight = true) :
    isSameComponent (unionFindJoin (unionFindJoin links laterFirst laterSecond)
        firstNode secondNode) queryLeft queryRight = true := by
  have forestFirst : isUnionFindForest (unionFindJoin links firstNode secondNode) :=
    isUnionFindForest_unionFindJoin links firstNode secondNode hforest
  have forestLater : isUnionFindForest (unionFindJoin links laterFirst laterSecond) :=
    isUnionFindForest_unionFindJoin links laterFirst laterSecond hforest
  cases (isSameComponent_unionFindJoin_true_iff (unionFindJoin links firstNode secondNode)
      forestFirst laterFirst laterSecond queryLeft queryRight).mp h with
  | inl throughFirst =>
      refine (isSameComponent_unionFindJoin_true_iff (unionFindJoin links laterFirst laterSecond)
        forestLater firstNode secondNode queryLeft queryRight).mpr ?_
      cases (isSameComponent_unionFindJoin_true_iff links hforest firstNode secondNode
          queryLeft queryRight).mp throughFirst with
      | inl direct =>
          exact Or.inl ((isSameComponent_unionFindJoin_true_iff links hforest laterFirst
            laterSecond queryLeft queryRight).mpr (Or.inl direct))
      | inr crossOrMirror =>
          cases crossOrMirror with
          | inl crossPair =>
              exact Or.inr (Or.inl (And.intro
                ((isSameComponent_unionFindJoin_true_iff links hforest laterFirst laterSecond
                  firstNode queryLeft).mpr (Or.inl crossPair.1))
                ((isSameComponent_unionFindJoin_true_iff links hforest laterFirst laterSecond
                  secondNode queryRight).mpr (Or.inl crossPair.2))))
          | inr mirrorPair =>
              exact Or.inr (Or.inr (And.intro
                ((isSameComponent_unionFindJoin_true_iff links hforest laterFirst laterSecond
                  firstNode queryRight).mpr (Or.inl mirrorPair.1))
                ((isSameComponent_unionFindJoin_true_iff links hforest laterFirst laterSecond
                  secondNode queryLeft).mpr (Or.inl mirrorPair.2))))
  | inr crossOrMirror =>
      cases crossOrMirror with
      | inl crossPair =>
          exact isSameComponent_join_cross_swap links hforest firstNode secondNode laterFirst
            laterSecond queryLeft queryRight crossPair.1 crossPair.2
      | inr mirrorPair =>
          exact isSameComponent_true_symm _ queryRight queryLeft
            (isSameComponent_join_cross_swap links hforest firstNode secondNode laterFirst
              laterSecond queryRight queryLeft mirrorPair.1 mirrorPair.2)

/-- ★ **Two adjacent union-find joins COMMUTE at the partition level.**  The boolean
same-component relation of `join (join links a b) c d` equals that of
`join (join links c d) a b` on every query pair — the reorder engine for the cap-cap
`componentsCorr` leg (the two run orders perform the same four merges in different orders).
NOTE: this is NOT a free boolean identity in the pre-join atoms (transitivity-violating
assignments separate the two expansions); it genuinely needs the root reading. -/
theorem isSameComponent_two_joins_comm (links : List (Nat × Nat))
    (hforest : isUnionFindForest links)
    (firstNode secondNode laterFirst laterSecond queryLeft queryRight : Nat) :
    isSameComponent (unionFindJoin (unionFindJoin links firstNode secondNode)
        laterFirst laterSecond) queryLeft queryRight
      = isSameComponent (unionFindJoin (unionFindJoin links laterFirst laterSecond)
          firstNode secondNode) queryLeft queryRight :=
  boolEqOfIff _ _
    (isSameComponent_two_joins_swap links hforest firstNode secondNode laterFirst laterSecond
      queryLeft queryRight)
    (isSameComponent_two_joins_swap links hforest laterFirst laterSecond firstNode secondNode
      queryLeft queryRight)

/-- One join RESPECTS pointwise partition equality: if two link lists induce the same
same-component relation, so do their joins by a common pair.  Direct from the boolean join
split — both sides expand to the same formula over pointwise-equal atoms. -/
theorem isSameComponent_unionFindJoin_congr (linksLeft linksRight : List (Nat × Nat))
    (forestLeft : isUnionFindForest linksLeft) (forestRight : isUnionFindForest linksRight)
    (partitionsAgree : ∀ probeLeft probeRight,
      isSameComponent linksLeft probeLeft probeRight
        = isSameComponent linksRight probeLeft probeRight)
    (firstNode secondNode queryLeft queryRight : Nat) :
    isSameComponent (unionFindJoin linksLeft firstNode secondNode) queryLeft queryRight
      = isSameComponent (unionFindJoin linksRight firstNode secondNode)
          queryLeft queryRight := by
  rw [isSameComponent_unionFindJoin_split linksLeft forestLeft firstNode secondNode
      queryLeft queryRight,
    isSameComponent_unionFindJoin_split linksRight forestRight firstNode secondNode
      queryLeft queryRight,
    partitionsAgree queryLeft queryRight, partitionsAgree firstNode queryLeft,
    partitionsAgree secondNode queryRight, partitionsAgree firstNode queryRight,
    partitionsAgree secondNode queryLeft]

/-- ★ **Two two-join BLOCKS commute at the partition level.**  A "block" is a pair merge
followed by an attach join — the link shape of one cap (and of one cup).  Executing the front
block then the rear block induces the same same-component relation as the rear block then the
front block: four adjacent join transpositions, each `isSameComponent_two_joins_comm` lifted
through the outer joins by `isSameComponent_unionFindJoin_congr`.  This is the tower-reorder
engine that aligns the two cap-cap run orders up to the fresh-name transposition. -/
theorem isSameComponent_join_blocks_comm (links : List (Nat × Nat))
    (hforest : isUnionFindForest links)
    (frontPairLeft frontPairRight frontAttachNode frontAttachTarget
      rearPairLeft rearPairRight rearAttachNode rearAttachTarget
      queryLeft queryRight : Nat) :
    isSameComponent (unionFindJoin (unionFindJoin (unionFindJoin (unionFindJoin links
        frontPairLeft frontPairRight) frontAttachNode frontAttachTarget)
        rearPairLeft rearPairRight) rearAttachNode rearAttachTarget) queryLeft queryRight
      = isSameComponent (unionFindJoin (unionFindJoin (unionFindJoin (unionFindJoin links
          rearPairLeft rearPairRight) rearAttachNode rearAttachTarget)
          frontPairLeft frontPairRight) frontAttachNode frontAttachTarget)
          queryLeft queryRight := by
  have forestFront : isUnionFindForest (unionFindJoin links frontPairLeft frontPairRight) :=
    isUnionFindForest_unionFindJoin links frontPairLeft frontPairRight hforest
  have forestRear : isUnionFindForest (unionFindJoin links rearPairLeft rearPairRight) :=
    isUnionFindForest_unionFindJoin links rearPairLeft rearPairRight hforest
  exact Eq.trans
    (isSameComponent_unionFindJoin_congr _ _
      (isUnionFindForest_unionFindJoin _ _ _
        (isUnionFindForest_unionFindJoin _ _ _ forestFront))
      (isUnionFindForest_unionFindJoin _ _ _
        (isUnionFindForest_unionFindJoin _ _ _ forestFront))
      (fun probeLeft probeRight => isSameComponent_two_joins_comm
        (unionFindJoin links frontPairLeft frontPairRight) forestFront
        frontAttachNode frontAttachTarget rearPairLeft rearPairRight probeLeft probeRight)
      rearAttachNode rearAttachTarget queryLeft queryRight)
    (Eq.trans
      (isSameComponent_unionFindJoin_congr _ _
        (isUnionFindForest_unionFindJoin _ _ _
          (isUnionFindForest_unionFindJoin _ _ _ forestFront))
        (isUnionFindForest_unionFindJoin _ _ _
          (isUnionFindForest_unionFindJoin _ _ _ forestRear))
        (fun probeLeft probeRight => isSameComponent_unionFindJoin_congr _ _
          (isUnionFindForest_unionFindJoin _ _ _ forestFront)
          (isUnionFindForest_unionFindJoin _ _ _ forestRear)
          (fun innerLeft innerRight => isSameComponent_two_joins_comm links hforest
            frontPairLeft frontPairRight rearPairLeft rearPairRight innerLeft innerRight)
          frontAttachNode frontAttachTarget probeLeft probeRight)
        rearAttachNode rearAttachTarget queryLeft queryRight)
      (Eq.trans
        (isSameComponent_two_joins_comm
          (unionFindJoin (unionFindJoin links rearPairLeft rearPairRight)
            frontPairLeft frontPairRight)
          (isUnionFindForest_unionFindJoin _ _ _ forestRear)
          frontAttachNode frontAttachTarget rearAttachNode rearAttachTarget
          queryLeft queryRight)
        (isSameComponent_unionFindJoin_congr _ _
          (isUnionFindForest_unionFindJoin _ _ _
            (isUnionFindForest_unionFindJoin _ _ _ forestRear))
          (isUnionFindForest_unionFindJoin _ _ _
            (isUnionFindForest_unionFindJoin _ _ _ forestRear))
          (fun probeLeft probeRight => isSameComponent_two_joins_comm
            (unionFindJoin links rearPairLeft rearPairRight) forestRear
            frontPairLeft frontPairRight rearAttachNode rearAttachTarget
            probeLeft probeRight)
          frontAttachNode frontAttachTarget queryLeft queryRight)))

/-- A renaming that fixes every link entry leaves the link list unchanged. -/
theorem renameLinks_ofFixedEntries (sigma : Nat → Nat) (links : List (Nat × Nat))
    (entriesFixed : ∀ edge ∈ links, sigma edge.1 = edge.1 ∧ sigma edge.2 = edge.2) :
    renameLinks sigma links = links := by
  induction links with
  | nil => rfl
  | cons headEdge restEdges restHolds =>
      obtain ⟨headLeft, headRight⟩ := headEdge
      have headLeftFixed : sigma headLeft = headLeft :=
        (entriesFixed (headLeft, headRight) (List.Mem.head restEdges)).1
      have headRightFixed : sigma headRight = headRight :=
        (entriesFixed (headLeft, headRight) (List.Mem.head restEdges)).2
      show (sigma headLeft, sigma headRight) :: renameLinks sigma restEdges
          = (headLeft, headRight) :: restEdges
      rw [headLeftFixed, headRightFixed,
        restHolds (fun edge edgeMember =>
          entriesFixed edge (List.Mem.tail (headLeft, headRight) edgeMember))]

/-- ★ **The same-component relation is invariant under an injective renaming**: querying the
renamed links at the renamed probes is querying the original links at the original probes —
the root commutes with the renaming and boolean equality is congruent along injections. -/
theorem isSameComponent_renameLinks (sigma : Nat → Nat)
    (inj : ∀ firstId secondId, sigma firstId = sigma secondId → firstId = secondId)
    (links : List (Nat × Nat)) (queryLeft queryRight : Nat) :
    isSameComponent (renameLinks sigma links) (sigma queryLeft) (sigma queryRight)
      = isSameComponent links queryLeft queryRight := by
  show (unionFindRootOf (renameLinks sigma links) (sigma queryLeft)
        == unionFindRootOf (renameLinks sigma links) (sigma queryRight))
     = (unionFindRootOf links queryLeft == unionFindRootOf links queryRight)
  rw [unionFindRootOf_rename sigma inj links queryLeft,
    unionFindRootOf_rename sigma inj links queryRight,
    beq_congr_inj sigma inj]

/-- The width-`1`/`1` event transposition sends the fresh base UP: `sigma nf = nf + 1`. -/
theorem arcFreshBlockTransposition_atBase (baseFresh : Nat) :
    arcFreshBlockTransposition baseFresh 1 1 baseFresh = baseFresh + 1 :=
  arcFreshBlockTransposition_onFirstBlock baseFresh 1 1 0 Nat.le.refl

/-- The width-`1`/`1` event transposition sends the successor DOWN: `sigma (nf + 1) = nf`. -/
theorem arcFreshBlockTransposition_atSuccessor (baseFresh : Nat) :
    arcFreshBlockTransposition baseFresh 1 1 (baseFresh + 1) = baseFresh :=
  arcFreshBlockTransposition_onSecondBlock baseFresh 1 1 0 Nat.le.refl

/-- ★ **The cap-cap `componentsCorr` leg, ABSTRACT TOWER FORM.**  The HIGH-first four-join
tower queried at transposed probes equals the LOW-first tower at the original probes.  Route:
`isSameComponent_join_blocks_comm` reorders the high-first tower into low-block-first order;
the reordered tower IS `renameLinks sigma` of the low-first tower AS A LIST
(`renameLinks_unionFindJoin` four times, the transposition fixing the old base links and the
four old wires, swapping only `nf <-> nf + 1` in the attach slots); and
`isSameComponent_renameLinks` strips the renaming against the transposed probes. -/
theorem capCapSwap_componentsCorr (links : List (Nat × Nat))
    (hforest : isUnionFindForest links) (freshBase : Nat)
    (linkEntriesFresh : ∀ edge ∈ links, edge.1 < freshBase ∧ edge.2 < freshBase)
    (lowLeftWire lowRightWire highLeftWire highRightWire : Nat)
    (lowLeftBelow : lowLeftWire < freshBase) (lowRightBelow : lowRightWire < freshBase)
    (highLeftBelow : highLeftWire < freshBase) (highRightBelow : highRightWire < freshBase)
    (probeLeft probeRight : Nat) :
    isSameComponent (unionFindJoin (unionFindJoin (unionFindJoin (unionFindJoin links
        highLeftWire highRightWire) freshBase highLeftWire) lowLeftWire lowRightWire)
        (freshBase + 1) lowLeftWire)
        (arcFreshBlockTransposition freshBase 1 1 probeLeft)
        (arcFreshBlockTransposition freshBase 1 1 probeRight)
      = isSameComponent (unionFindJoin (unionFindJoin (unionFindJoin (unionFindJoin links
          lowLeftWire lowRightWire) freshBase lowLeftWire) highLeftWire highRightWire)
          (freshBase + 1) highLeftWire) probeLeft probeRight := by
  have injSigma : ∀ firstId secondId, arcFreshBlockTransposition freshBase 1 1 firstId
      = arcFreshBlockTransposition freshBase 1 1 secondId → firstId = secondId :=
    fun firstId secondId =>
      arcFreshBlockTransposition_injective freshBase 1 1 firstId secondId
  have renameTower : renameLinks (arcFreshBlockTransposition freshBase 1 1)
      (unionFindJoin (unionFindJoin (unionFindJoin (unionFindJoin links
        lowLeftWire lowRightWire) freshBase lowLeftWire) highLeftWire highRightWire)
        (freshBase + 1) highLeftWire)
      = unionFindJoin (unionFindJoin (unionFindJoin (unionFindJoin links
          lowLeftWire lowRightWire) (freshBase + 1) lowLeftWire) highLeftWire highRightWire)
          freshBase highLeftWire := by
    rw [renameLinks_unionFindJoin _ injSigma, renameLinks_unionFindJoin _ injSigma,
      renameLinks_unionFindJoin _ injSigma, renameLinks_unionFindJoin _ injSigma,
      renameLinks_ofFixedEntries _ links (fun edge edgeMember =>
        And.intro
          (arcFreshBlockTransposition_ofBelow freshBase 1 1 edge.1
            (linkEntriesFresh edge edgeMember).1)
          (arcFreshBlockTransposition_ofBelow freshBase 1 1 edge.2
            (linkEntriesFresh edge edgeMember).2)),
      arcFreshBlockTransposition_ofBelow freshBase 1 1 lowLeftWire lowLeftBelow,
      arcFreshBlockTransposition_ofBelow freshBase 1 1 lowRightWire lowRightBelow,
      arcFreshBlockTransposition_ofBelow freshBase 1 1 highLeftWire highLeftBelow,
      arcFreshBlockTransposition_ofBelow freshBase 1 1 highRightWire highRightBelow,
      arcFreshBlockTransposition_atBase freshBase,
      arcFreshBlockTransposition_atSuccessor freshBase]
  rw [isSameComponent_join_blocks_comm links hforest highLeftWire highRightWire freshBase
      highLeftWire lowLeftWire lowRightWire (freshBase + 1) lowLeftWire
      (arcFreshBlockTransposition freshBase 1 1 probeLeft)
      (arcFreshBlockTransposition freshBase 1 1 probeRight),
    ← renameTower,
    isSameComponent_renameLinks (arcFreshBlockTransposition freshBase 1 1) injSigma]

/-- Boolean conjunction commutes — both arguments cased, all four leaves definitional. -/
theorem boolAndComm (left right : Bool) : (left && right) = (right && left) := by
  cases left with
  | true =>
      cases right with
      | true => rfl
      | false => rfl
  | false =>
      cases right with
      | true => rfl
      | false => rfl

/-- ★ **Fresh-attach TRANSPARENCY**: joining a node at or above the freshness bound onto any
target does not change same-component truth between two queries below the bound.  The fresh
node is parentless, so its root is itself and cannot equal either query's root (which stays
below the bound); both cross disjuncts of the join split evaluate to `false`. -/
theorem isSameComponent_freshAttach_transparent (links : List (Nat × Nat))
    (hforest : isUnionFindForest links) (freshBound : Nat)
    (linkEntriesBelow : ∀ edge ∈ links, edge.1 < freshBound ∧ edge.2 < freshBound)
    (freshNode target queryLeft queryRight : Nat) (freshAtOrAbove : freshBound ≤ freshNode)
    (queryLeftBelow : queryLeft < freshBound) (queryRightBelow : queryRight < freshBound) :
    isSameComponent (unionFindJoin links freshNode target) queryLeft queryRight
      = isSameComponent links queryLeft queryRight := by
  have freshRoot : unionFindRootOf links freshNode = freshNode :=
    unionFindRootOf_of_parentless links freshNode
      (unionFindParent_none_of_lt freshBound links
        (fun edge edgeMember => (linkEntriesBelow edge edgeMember).1) freshNode freshAtOrAbove)
  have atomLeft : isSameComponent links freshNode queryLeft = false := by
    show (unionFindRootOf links freshNode == unionFindRootOf links queryLeft) = false
    rw [freshRoot]
    exact decide_eq_false (fun freshHitsRoot =>
      Nat.lt_irrefl (unionFindRootOf links queryLeft)
        (Nat.lt_of_lt_of_le
          (unionFindRootOf_lt_of_fresh links freshBound
            (fun edge edgeMember => (linkEntriesBelow edge edgeMember).2)
            queryLeft queryLeftBelow)
          (freshHitsRoot ▸ freshAtOrAbove)))
  have atomRight : isSameComponent links freshNode queryRight = false := by
    show (unionFindRootOf links freshNode == unionFindRootOf links queryRight) = false
    rw [freshRoot]
    exact decide_eq_false (fun freshHitsRoot =>
      Nat.lt_irrefl (unionFindRootOf links queryRight)
        (Nat.lt_of_lt_of_le
          (unionFindRootOf_lt_of_fresh links freshBound
            (fun edge edgeMember => (linkEntriesBelow edge edgeMember).2)
            queryRight queryRightBelow)
          (freshHitsRoot ▸ freshAtOrAbove)))
  rw [isSameComponent_unionFindJoin_split links hforest freshNode target queryLeft queryRight,
    atomLeft, atomRight, boolFalseAnd, boolFalseAnd, boolOrFalse, boolOrFalse]

/-- Joining an ALREADY-CONNECTED pair is a partition no-op: same-component truth between any
two queries is unchanged.  Forward direction folds both cross disjuncts back into the direct
one through the merged pair's shared root. -/
theorem isSameComponent_unionFindJoin_ofMerged (links : List (Nat × Nat))
    (hforest : isUnionFindForest links) (firstNode secondNode : Nat)
    (alreadySame : isSameComponent links firstNode secondNode = true)
    (queryLeft queryRight : Nat) :
    isSameComponent (unionFindJoin links firstNode secondNode) queryLeft queryRight
      = isSameComponent links queryLeft queryRight := by
  have rootsMerged : unionFindRootOf links firstNode = unionFindRootOf links secondNode :=
    (isSameComponent_true_iff_rootsEqual links firstNode secondNode).mp alreadySame
  apply boolEqOfIff
  · intro joinedTrue
    cases (isSameComponent_unionFindJoin_true_iff links hforest firstNode secondNode
        queryLeft queryRight).mp joinedTrue with
    | inl direct => exact direct
    | inr crossOrMirror =>
        cases crossOrMirror with
        | inl crossPair =>
            exact (isSameComponent_true_iff_rootsEqual links queryLeft queryRight).mpr
              (((isSameComponent_true_iff_rootsEqual links firstNode queryLeft).mp
                crossPair.1).symm.trans (rootsMerged.trans
                  ((isSameComponent_true_iff_rootsEqual links secondNode queryRight).mp
                    crossPair.2)))
        | inr mirrorPair =>
            exact (isSameComponent_true_iff_rootsEqual links queryLeft queryRight).mpr
              (((isSameComponent_true_iff_rootsEqual links secondNode queryLeft).mp
                mirrorPair.2).symm.trans (rootsMerged.symm.trans
                  ((isSameComponent_true_iff_rootsEqual links firstNode queryRight).mp
                    mirrorPair.1)))
  · intro baseTrue
    exact (isSameComponent_unionFindJoin_true_iff links hforest firstNode secondNode
      queryLeft queryRight).mpr (Or.inl baseTrue)

/-- ★ **The cap-cap `loopsEq` leg, ABSTRACT FORM.**  Both run orders produce the same loop
count: each side's SECOND cap guard sees the other pair's merge (fresh-attach joins are
transparent to old queries), and the four guard cases exchange — when either base guard is
true the other side's second guard collapses through `isSameComponent_unionFindJoin_ofMerged`;
when both are false the two second guards are the SAME cross disjunction up to root-equality
symmetry and conjunction commutativity. -/
theorem capCapSwap_loopsEq (links : List (Nat × Nat)) (hforest : isUnionFindForest links)
    (freshBase : Nat)
    (linkEntriesFresh : ∀ edge ∈ links, edge.1 < freshBase ∧ edge.2 < freshBase)
    (lowLeftWire lowRightWire highLeftWire highRightWire : Nat)
    (lowLeftBelow : lowLeftWire < freshBase) (lowRightBelow : lowRightWire < freshBase)
    (highLeftBelow : highLeftWire < freshBase) (highRightBelow : highRightWire < freshBase)
    (loopsBefore : Nat) :
    (if isSameComponent (unionFindJoin (unionFindJoin links highLeftWire highRightWire)
          freshBase highLeftWire) lowLeftWire lowRightWire
      then (if isSameComponent links highLeftWire highRightWire
            then loopsBefore + 1 else loopsBefore) + 1
      else (if isSameComponent links highLeftWire highRightWire
            then loopsBefore + 1 else loopsBefore))
      = (if isSameComponent (unionFindJoin (unionFindJoin links lowLeftWire lowRightWire)
            freshBase lowLeftWire) highLeftWire highRightWire
        then (if isSameComponent links lowLeftWire lowRightWire
              then loopsBefore + 1 else loopsBefore) + 1
        else (if isSameComponent links lowLeftWire lowRightWire
              then loopsBefore + 1 else loopsBefore)) := by
  have rootBelow : ∀ wire, wire < freshBase → unionFindRootOf links wire < freshBase :=
    fun wire wireBelow => unionFindRootOf_lt_of_fresh links freshBase
      (fun edge edgeMember => (linkEntriesFresh edge edgeMember).2) wire wireBelow
  rw [isSameComponent_freshAttach_transparent
      (unionFindJoin links highLeftWire highRightWire)
      (isUnionFindForest_unionFindJoin links highLeftWire highRightWire hforest) freshBase
      (unionFindJoin_all_lt freshBase links highLeftWire highRightWire linkEntriesFresh
        (rootBelow highLeftWire highLeftBelow) (rootBelow highRightWire highRightBelow))
      freshBase highLeftWire lowLeftWire lowRightWire (Nat.le_refl freshBase)
      lowLeftBelow lowRightBelow,
    isSameComponent_freshAttach_transparent
      (unionFindJoin links lowLeftWire lowRightWire)
      (isUnionFindForest_unionFindJoin links lowLeftWire lowRightWire hforest) freshBase
      (unionFindJoin_all_lt freshBase links lowLeftWire lowRightWire linkEntriesFresh
        (rootBelow lowLeftWire lowLeftBelow) (rootBelow lowRightWire lowRightBelow))
      freshBase lowLeftWire highLeftWire highRightWire (Nat.le_refl freshBase)
      highLeftBelow highRightBelow]
  cases guardLow : isSameComponent links lowLeftWire lowRightWire with
  | true =>
      have leftOuterTrue : isSameComponent (unionFindJoin links highLeftWire highRightWire)
          lowLeftWire lowRightWire = true :=
        (isSameComponent_unionFindJoin_true_iff links hforest highLeftWire highRightWire
          lowLeftWire lowRightWire).mpr (Or.inl guardLow)
      rw [leftOuterTrue,
        isSameComponent_unionFindJoin_ofMerged links hforest lowLeftWire lowRightWire
          guardLow highLeftWire highRightWire]
      cases guardHigh : isSameComponent links highLeftWire highRightWire with
      | true => rfl
      | false => rfl
  | false =>
      cases guardHigh : isSameComponent links highLeftWire highRightWire with
      | true =>
          have rightOuterTrue : isSameComponent (unionFindJoin links lowLeftWire lowRightWire)
              highLeftWire highRightWire = true :=
            (isSameComponent_unionFindJoin_true_iff links hforest lowLeftWire lowRightWire
              highLeftWire highRightWire).mpr (Or.inl guardHigh)
          rw [rightOuterTrue,
            isSameComponent_unionFindJoin_ofMerged links hforest highLeftWire highRightWire
              guardHigh lowLeftWire lowRightWire,
            guardLow]
          rfl
      | false =>
          rw [isSameComponent_unionFindJoin_split links hforest highLeftWire highRightWire
              lowLeftWire lowRightWire,
            isSameComponent_unionFindJoin_split links hforest lowLeftWire lowRightWire
              highLeftWire highRightWire,
            guardLow, guardHigh]
          have crossLeftSymm : isSameComponent links highLeftWire lowLeftWire
              = isSameComponent links lowLeftWire highLeftWire := by
            show (unionFindRootOf links highLeftWire == unionFindRootOf links lowLeftWire)
               = (unionFindRootOf links lowLeftWire == unionFindRootOf links highLeftWire)
            exact natBeq_comm (unionFindRootOf links highLeftWire)
              (unionFindRootOf links lowLeftWire)
          have crossRightSymm : isSameComponent links highRightWire lowRightWire
              = isSameComponent links lowRightWire highRightWire := by
            show (unionFindRootOf links highRightWire == unionFindRootOf links lowRightWire)
               = (unionFindRootOf links lowRightWire == unionFindRootOf links highRightWire)
            exact natBeq_comm (unionFindRootOf links highRightWire)
              (unionFindRootOf links lowRightWire)
          have mirrorLeftSymm : isSameComponent links highLeftWire lowRightWire
              = isSameComponent links lowRightWire highLeftWire := by
            show (unionFindRootOf links highLeftWire == unionFindRootOf links lowRightWire)
               = (unionFindRootOf links lowRightWire == unionFindRootOf links highLeftWire)
            exact natBeq_comm (unionFindRootOf links highLeftWire)
              (unionFindRootOf links lowRightWire)
          have mirrorRightSymm : isSameComponent links highRightWire lowLeftWire
              = isSameComponent links lowLeftWire highRightWire := by
            show (unionFindRootOf links highRightWire == unionFindRootOf links lowLeftWire)
               = (unionFindRootOf links lowLeftWire == unionFindRootOf links highRightWire)
            exact natBeq_comm (unionFindRootOf links highRightWire)
              (unionFindRootOf links lowLeftWire)
          rw [crossLeftSymm, crossRightSymm, mirrorLeftSymm, mirrorRightSymm,
            boolAndComm (isSameComponent links lowRightWire highLeftWire)
              (isSameComponent links lowLeftWire highRightWire)]

/-- ★ **The sigma-fixed COUNT transport**: a partition correspondence between two link lists
carries the per-root event count across, for any event list the transposition fixes.  Each
event's indicator IS a same-component boolean, so `componentsCorr` rewrites it directly —
structural induction on the events. -/
theorem countEventsInRoot_sigmaFixed_partitionCorr (sigma : Nat → Nat)
    (linksT linksS : List (Nat × Nat))
    (componentsCorr : ∀ probeLeft probeRight,
      isSameComponent linksT (sigma probeLeft) (sigma probeRight)
        = isSameComponent linksS probeLeft probeRight)
    (probe : Nat) :
    (events : List Nat) → (∀ event ∈ events, sigma event = event) →
    countEventsInRoot linksT (unionFindRootOf linksT (sigma probe)) events
      = countEventsInRoot linksS (unionFindRootOf linksS probe) events
  | [], _ => rfl
  | headEvent :: restEvents, eventsFixed => by
      have headFixed : sigma headEvent = headEvent :=
        eventsFixed headEvent (List.Mem.head restEvents)
      have headIndicator : (unionFindRootOf linksT headEvent
            == unionFindRootOf linksT (sigma probe))
          = (unionFindRootOf linksS headEvent == unionFindRootOf linksS probe) := by
        have viaCorr := componentsCorr headEvent probe
        rw [headFixed] at viaCorr
        exact viaCorr
      show (if unionFindRootOf linksT headEvent == unionFindRootOf linksT (sigma probe)
            then 1 else 0)
          + countEventsInRoot linksT (unionFindRootOf linksT (sigma probe)) restEvents
        = (if unionFindRootOf linksS headEvent == unionFindRootOf linksS probe
            then 1 else 0)
          + countEventsInRoot linksS (unionFindRootOf linksS probe) restEvents
      rw [headIndicator,
        countEventsInRoot_sigmaFixed_partitionCorr sigma linksT linksS componentsCorr probe
          restEvents (fun event eventMember =>
            eventsFixed event (List.Mem.tail headEvent eventMember))]

/-- ★ **The SWAPPED-HEADS count transport** — the cap-cap `capCountCorr` engine.  Both run
orders record the SAME event list `freshHigh :: freshLow :: oldEvents`, but the transposition
swaps the two fresh heads; their indicators exchange CROSSWISE through `componentsCorr`
(`sigma freshLow = freshHigh` makes the T-side `freshHigh` indicator the S-side `freshLow`
indicator, and vice versa), the old tail rides the sigma-fixed transport, and the two head
contributions trade places by `Nat.add_left_comm`. -/
theorem countEventsInRoot_swappedHeads_partitionCorr (sigma : Nat → Nat)
    (linksT linksS : List (Nat × Nat))
    (componentsCorr : ∀ probeLeft probeRight,
      isSameComponent linksT (sigma probeLeft) (sigma probeRight)
        = isSameComponent linksS probeLeft probeRight)
    (freshLow freshHigh : Nat) (lowMapsUp : sigma freshLow = freshHigh)
    (highMapsDown : sigma freshHigh = freshLow) (probe : Nat) (oldEvents : List Nat)
    (oldEventsFixed : ∀ event ∈ oldEvents, sigma event = event) :
    countEventsInRoot linksT (unionFindRootOf linksT (sigma probe))
        (freshHigh :: freshLow :: oldEvents)
      = countEventsInRoot linksS (unionFindRootOf linksS probe)
          (freshHigh :: freshLow :: oldEvents) := by
  have highIndicator : (unionFindRootOf linksT freshHigh
        == unionFindRootOf linksT (sigma probe))
      = (unionFindRootOf linksS freshLow == unionFindRootOf linksS probe) := by
    have viaCorr := componentsCorr freshLow probe
    rw [lowMapsUp] at viaCorr
    exact viaCorr
  have lowIndicator : (unionFindRootOf linksT freshLow
        == unionFindRootOf linksT (sigma probe))
      = (unionFindRootOf linksS freshHigh == unionFindRootOf linksS probe) := by
    have viaCorr := componentsCorr freshHigh probe
    rw [highMapsDown] at viaCorr
    exact viaCorr
  show (if unionFindRootOf linksT freshHigh == unionFindRootOf linksT (sigma probe)
        then 1 else 0)
      + ((if unionFindRootOf linksT freshLow == unionFindRootOf linksT (sigma probe)
          then 1 else 0)
        + countEventsInRoot linksT (unionFindRootOf linksT (sigma probe)) oldEvents)
    = (if unionFindRootOf linksS freshHigh == unionFindRootOf linksS probe
        then 1 else 0)
      + ((if unionFindRootOf linksS freshLow == unionFindRootOf linksS probe
          then 1 else 0)
        + countEventsInRoot linksS (unionFindRootOf linksS probe) oldEvents)
  rw [highIndicator, lowIndicator,
    countEventsInRoot_sigmaFixed_partitionCorr sigma linksT linksS componentsCorr probe
      oldEvents oldEventsFixed]
  exact Nat.add_left_comm
    (if unionFindRootOf linksS freshLow == unionFindRootOf linksS probe then 1 else 0)
    (if unionFindRootOf linksS freshHigh == unionFindRootOf linksS probe then 1 else 0)
    (countEventsInRoot linksS (unionFindRootOf linksS probe) oldEvents)

/-- **Honesty marker — the cap-cap core's WIRE leg, JOIN-SPLIT, and JOIN-COMMUTATION substrate
are BUILT.**  `capCapSwap_openMap` discharges the `openMap` field of the target
`ArcPartitionSim (arcFreshBlockTransposition state.nextFresh 1 1)` instance between the two
cap-cap run orders (`nfEq` and the event-LIST equalities are definitional: both orders allocate
`nf` then `nf + 1` and cons them in the same order); `isSameComponent_unionFindJoin_split`
characterizes one merge purely in pre-join same-component booleans; and
`isSameComponent_two_joins_comm` commutes two adjacent joins at the partition level;
`isSameComponent_unionFindJoin_congr` lifts pointwise partition equality through a join; and
`isSameComponent_join_blocks_comm` commutes two whole two-join BLOCKS (pair merge + attach —
the cap link shape); `capCapSwap_componentsCorr` discharges the `componentsCorr` leg in
ABSTRACT TOWER FORM (blocks-comm reorder, then the reordered tower IS `renameLinks sigma` of
the low-first tower as a list, then `isSameComponent_renameLinks` strips the renaming); and
`capCapSwap_loopsEq` discharges the `loopsEq` leg abstractly (fresh-attach transparency
exposes both second-cap guards over the single pair joins, and the four guard cases exchange
via `isSameComponent_unionFindJoin_ofMerged` plus the cross-disjunction symmetry); and the two
COUNT ENGINES are built — `countEventsInRoot_sigmaFixed_partitionCorr` (any componentsCorr
carries per-root counts across sigma-fixed event lists: the cup leg) and
`countEventsInRoot_swappedHeads_partitionCorr` (the two fresh cap heads exchange crosswise and
trade places by `Nat.add_left_comm`: the cap leg).  What this marker does NOT claim: the
wire-read alignment from the concrete `stepCapArc` states to the abstract towers and the
assembled core instance.  `= true` records the wire leg + the split + the reorder engine + the
abstract `componentsCorr` + the abstract `loopsEq` + the count engines. -/
def fxMode_hasCapCapSwapWireLeg : Bool := true

end FX1Poly.Polygraph
