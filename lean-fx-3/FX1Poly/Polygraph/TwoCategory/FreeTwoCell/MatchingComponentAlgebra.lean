import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingFoldCongruence

/-! # mode-3 keystone — the same-component algebra of the union-find join

The block-swap witness's `componentComm` field is the join-order INDEPENDENCE of the partition — comparing the
same-component view after two DIFFERENT join sequences.  The root-after-join characterization
(`unionFindRootOf_unionFindJoin`) speaks in nested root-ifs, which compose badly across reordered joins; this
file ships the SEMANTIC form the reorder bashes consume:

  ★ `isSameComponent_unionFindJoin` — the flat-disjunction characterization: after joining
    `firstNode`/`secondNode`, two probes share a component iff they already did, or one sat with `firstNode`
    and the other with `secondNode`.  Forest-conditioned; a nine-leaf boolean case tree whose inconsistent
    leaves are refuted by root-equality transitivity.
  ★ `unionFindJoin_ofSameComponent` + `stepCap_links_eq_unionFindJoin` — the join's built-in no-op test makes
    the cap's OUTER same-component test redundant for `links`: every fold step's link update is a UNIFORM
    `unionFindJoin` (cup on the fresh legs, cap on the read wires) — the event fold is join-homogeneous.
  ★ `isSameComponent_self` / `_symm` / `_trans` — the equivalence-relation kit the reorder bashes discharge
    their inconsistent branches with.

Raw Lean 4 + Init; `decide`-level boolean reasoning (`of_decide_eq_true` / `decide_eq_true`), no `omega` /
`simp`-AC.  Per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## The equivalence-relation kit -/

/-- Same-component is reflexive. -/
theorem isSameComponent_self (links : List (Nat × Nat)) (node : Nat) :
    isSameComponent links node node = true :=
  decide_eq_true rfl

/-- Same-component is symmetric. -/
theorem isSameComponent_symm (links : List (Nat × Nat)) (firstNode secondNode : Nat) :
    isSameComponent links firstNode secondNode = isSameComponent links secondNode firstNode := by
  cases hforward : isSameComponent links firstNode secondNode with
  | true => exact (decide_eq_true (of_decide_eq_true hforward).symm).symm
  | false =>
      exact (decide_eq_false
        (fun rootsEq => of_decide_eq_false hforward rootsEq.symm)).symm

/-- Same-component is transitive. -/
theorem isSameComponent_trans (links : List (Nat × Nat)) (firstNode middleNode lastNode : Nat)
    (firstMiddle : isSameComponent links firstNode middleNode = true)
    (middleLast : isSameComponent links middleNode lastNode = true) :
    isSameComponent links firstNode lastNode = true :=
  decide_eq_true ((of_decide_eq_true firstMiddle).trans (of_decide_eq_true middleLast))

/-! ## The join fold is join-homogeneous -/

/-- Joining two already-connected nodes is a no-op (the join's internal test). -/
theorem unionFindJoin_ofSameComponent (links : List (Nat × Nat)) (firstNode secondNode : Nat)
    (sameComponent : isSameComponent links firstNode secondNode = true) :
    unionFindJoin links firstNode secondNode = links := by
  have rootsEqTrue : (unionFindRootOf links firstNode == unionFindRootOf links secondNode) = true :=
    sameComponent
  dsimp only [unionFindJoin]
  rw [rootsEqTrue]
  rfl

/-- ★ **The cap's link update is an UNCONDITIONAL join** — the outer same-component test (which drives the
loop count) is redundant for `links`, because `unionFindJoin` performs the same test internally.  So every
fold step's link update is a uniform `unionFindJoin`: the cup on its two fresh legs, the cap on its two read
wires — the partition evolution is a homogeneous join fold over the read pairs. -/
theorem stepCap_links_eq_unionFindJoin (state : WireState) (position : Nat) :
    (stepCap state position).links
      = unionFindJoin state.links (natListGetAt state.openWires position)
          (natListGetAt state.openWires (position + 1)) := by
  rw [stepCap_links]
  cases htest : isSameComponent state.links (natListGetAt state.openWires position)
      (natListGetAt state.openWires (position + 1)) with
  | true =>
      exact (unionFindJoin_ofSameComponent state.links _ _ htest).symm
  | false => rfl

/-! ## The flat-disjunction characterization of the join -/

/-- ★ **The same-component view after a join, as a flat disjunction.**  After joining
`firstNode`/`secondNode` (forest-conditioned), two probes share a component iff they ALREADY did, or
`probeOne` sat with `firstNode` and `probeTwo` with `secondNode`, or vice versa.  The semantic replacement
for composing nested `unionFindRootOf_unionFindJoin` root-ifs — everything the join-reorder bashes
(`componentComm` of the block swap) read off the partition goes through this one equation.  The mixed
argument orientations match the root-if conditions exactly, so every leaf of the nine-leaf case tree reduces
definitionally; the two inconsistent leaves are refuted by root-equality transitivity. -/
theorem isSameComponent_unionFindJoin (links : List (Nat × Nat)) (forest : isUnionFindForest links)
    (firstNode secondNode probeOne probeTwo : Nat) :
    isSameComponent (unionFindJoin links firstNode secondNode) probeOne probeTwo
      = (isSameComponent links probeOne probeTwo
          || (isSameComponent links firstNode probeOne && isSameComponent links secondNode probeTwo)
          || (isSameComponent links firstNode probeTwo && isSameComponent links probeOne secondNode)) := by
  show (unionFindRootOf (unionFindJoin links firstNode secondNode) probeOne
        == unionFindRootOf (unionFindJoin links firstNode secondNode) probeTwo)
      = ((unionFindRootOf links probeOne == unionFindRootOf links probeTwo)
          || ((unionFindRootOf links firstNode == unionFindRootOf links probeOne)
              && (unionFindRootOf links secondNode == unionFindRootOf links probeTwo))
          || ((unionFindRootOf links firstNode == unionFindRootOf links probeTwo)
              && (unionFindRootOf links probeOne == unionFindRootOf links secondNode)))
  rw [unionFindRootOf_unionFindJoin links firstNode secondNode probeOne forest,
    unionFindRootOf_unionFindJoin links firstNode secondNode probeTwo forest]
  cases hfirstOne : unionFindRootOf links firstNode == unionFindRootOf links probeOne with
  | true =>
      cases hfirstTwo : unionFindRootOf links firstNode == unionFindRootOf links probeTwo with
      | true =>
          cases hprobes : unionFindRootOf links probeOne == unionFindRootOf links probeTwo with
          | true => exact decide_eq_true rfl
          | false =>
              exact absurd ((of_decide_eq_true hfirstOne).symm.trans (of_decide_eq_true hfirstTwo))
                (of_decide_eq_false hprobes)
      | false =>
          cases hprobes : unionFindRootOf links probeOne == unionFindRootOf links probeTwo with
          | true =>
              exact absurd ((of_decide_eq_true hfirstOne).trans (of_decide_eq_true hprobes))
                (of_decide_eq_false hfirstTwo)
          | false =>
              cases hsecondTwo : unionFindRootOf links secondNode == unionFindRootOf links probeTwo with
              | true => exact hsecondTwo
              | false => exact hsecondTwo
  | false =>
      cases hfirstTwo : unionFindRootOf links firstNode == unionFindRootOf links probeTwo with
      | true =>
          cases hprobes : unionFindRootOf links probeOne == unionFindRootOf links probeTwo with
          | true =>
              exact absurd ((of_decide_eq_true hfirstTwo).trans (of_decide_eq_true hprobes).symm)
                (of_decide_eq_false hfirstOne)
          | false => rfl
      | false =>
          cases hprobes : unionFindRootOf links probeOne == unionFindRootOf links probeTwo with
          | true => exact hprobes
          | false => exact hprobes

/-! ## The join-order swap -/

/-- Same-component transport across an argument flip (the kit's symmetry, in implication form). -/
theorem isSameComponent_flip (links : List (Nat × Nat)) (firstNode secondNode : Nat)
    (forward : isSameComponent links firstNode secondNode = true) :
    isSameComponent links secondNode firstNode = true :=
  (isSameComponent_symm links secondNode firstNode).trans forward

/-- Base membership survives a join (monotonicity of the same-component view under `unionFindJoin`). -/
theorem isSameComponent_unionFindJoin_ofBase (links : List (Nat × Nat))
    (forest : isUnionFindForest links) (joinLeft joinRight probeOne probeTwo : Nat)
    (base : isSameComponent links probeOne probeTwo = true) :
    isSameComponent (unionFindJoin links joinLeft joinRight) probeOne probeTwo = true := by
  rw [isSameComponent_unionFindJoin links forest joinLeft joinRight probeOne probeTwo, base]
  rfl

/-- The join relates the two nodes it joins. -/
theorem isSameComponent_unionFindJoin_joined (links : List (Nat × Nat))
    (forest : isUnionFindForest links) (joinLeft joinRight : Nat) :
    isSameComponent (unionFindJoin links joinLeft joinRight) joinLeft joinRight = true := by
  rw [isSameComponent_unionFindJoin links forest joinLeft joinRight joinLeft joinRight,
    isSameComponent_self links joinLeft, isSameComponent_self links joinRight]
  cases hpair : isSameComponent links joinLeft joinRight with
  | true => rfl
  | false => rfl

/-- ★ **The universal property of the join** (elimination): anything the join relates is related by ANY
same-component view that (i) contains the base view and (ii) relates the joined pair.  Forest-conditioned
on the base only (that is the characterization's hypothesis); the target view is an arbitrary link list —
the kit closes the chains unconditionally.  This is the lemma that lets a join be RE-PLAYED at a different
position in a join sequence: decompose membership by the characterization, re-assemble through the target's
`liftBase`/`joined` facts. -/
theorem isSameComponent_unionFindJoin_lift (links target : List (Nat × Nat))
    (forest : isUnionFindForest links) (joinLeft joinRight : Nat)
    (liftBase : ∀ nodeOne nodeTwo : Nat, isSameComponent links nodeOne nodeTwo = true →
      isSameComponent target nodeOne nodeTwo = true)
    (joined : isSameComponent target joinLeft joinRight = true)
    (probeOne probeTwo : Nat)
    (inJoin : isSameComponent (unionFindJoin links joinLeft joinRight) probeOne probeTwo = true) :
    isSameComponent target probeOne probeTwo = true := by
  rw [isSameComponent_unionFindJoin links forest joinLeft joinRight probeOne probeTwo] at inJoin
  cases hbase : isSameComponent links probeOne probeTwo with
  | true => exact liftBase probeOne probeTwo hbase
  | false =>
      rw [hbase] at inJoin
      cases hjoinLeftOne : isSameComponent links joinLeft probeOne with
      | true =>
          rw [hjoinLeftOne] at inJoin
          cases hjoinRightTwo : isSameComponent links joinRight probeTwo with
          | true =>
              exact isSameComponent_trans target probeOne joinRight probeTwo
                (isSameComponent_trans target probeOne joinLeft joinRight
                  (isSameComponent_flip target joinLeft probeOne
                    (liftBase joinLeft probeOne hjoinLeftOne))
                  joined)
                (liftBase joinRight probeTwo hjoinRightTwo)
          | false =>
              rw [hjoinRightTwo] at inJoin
              cases hjoinLeftTwo : isSameComponent links joinLeft probeTwo with
              | true =>
                  cases hprobeOneRight : isSameComponent links probeOne joinRight with
                  | true =>
                      exact isSameComponent_trans target probeOne joinLeft probeTwo
                        (isSameComponent_trans target probeOne joinRight joinLeft
                          (liftBase probeOne joinRight hprobeOneRight)
                          (isSameComponent_flip target joinLeft joinRight joined))
                        (liftBase joinLeft probeTwo hjoinLeftTwo)
                  | false =>
                      rw [hjoinLeftTwo, hprobeOneRight] at inJoin
                      exact Bool.noConfusion inJoin
              | false =>
                  rw [hjoinLeftTwo] at inJoin
                  exact Bool.noConfusion inJoin
      | false =>
          rw [hjoinLeftOne] at inJoin
          cases hjoinLeftTwo : isSameComponent links joinLeft probeTwo with
          | true =>
              cases hprobeOneRight : isSameComponent links probeOne joinRight with
              | true =>
                  exact isSameComponent_trans target probeOne joinLeft probeTwo
                    (isSameComponent_trans target probeOne joinRight joinLeft
                      (liftBase probeOne joinRight hprobeOneRight)
                      (isSameComponent_flip target joinLeft joinRight joined))
                    (liftBase joinLeft probeTwo hjoinLeftTwo)
              | false =>
                  rw [hjoinLeftTwo, hprobeOneRight] at inJoin
                  exact Bool.noConfusion inJoin
          | false =>
              rw [hjoinLeftTwo] at inJoin
              exact Bool.noConfusion inJoin

/-- Transport across the swapped two-join chain (one direction of the swap): both chains contain the base
view and relate both joined pairs, so each eliminates into the other by the universal property, applied
once per join. -/
theorem isSameComponent_acrossSwappedJoins (links : List (Nat × Nat))
    (forest : isUnionFindForest links) (firstA secondA firstB secondB probeOne probeTwo : Nat)
    (inOrdered : isSameComponent
        (unionFindJoin (unionFindJoin links firstA secondA) firstB secondB)
        probeOne probeTwo = true) :
    isSameComponent
        (unionFindJoin (unionFindJoin links firstB secondB) firstA secondA)
        probeOne probeTwo = true := by
  have forestA : isUnionFindForest (unionFindJoin links firstA secondA) :=
    isUnionFindForest_unionFindJoin links firstA secondA forest
  have forestB : isUnionFindForest (unionFindJoin links firstB secondB) :=
    isUnionFindForest_unionFindJoin links firstB secondB forest
  have liftBaseSwapped : ∀ nodeOne nodeTwo : Nat, isSameComponent links nodeOne nodeTwo = true →
      isSameComponent (unionFindJoin (unionFindJoin links firstB secondB) firstA secondA)
        nodeOne nodeTwo = true := fun nodeOne nodeTwo base =>
    isSameComponent_unionFindJoin_ofBase (unionFindJoin links firstB secondB) forestB
      firstA secondA nodeOne nodeTwo
      (isSameComponent_unionFindJoin_ofBase links forest firstB secondB nodeOne nodeTwo base)
  have joinedA : isSameComponent (unionFindJoin (unionFindJoin links firstB secondB) firstA secondA)
      firstA secondA = true :=
    isSameComponent_unionFindJoin_joined (unionFindJoin links firstB secondB) forestB firstA secondA
  have joinedB : isSameComponent (unionFindJoin (unionFindJoin links firstB secondB) firstA secondA)
      firstB secondB = true :=
    isSameComponent_unionFindJoin_ofBase (unionFindJoin links firstB secondB) forestB
      firstA secondA firstB secondB
      (isSameComponent_unionFindJoin_joined links forest firstB secondB)
  have liftInner : ∀ nodeOne nodeTwo : Nat,
      isSameComponent (unionFindJoin links firstA secondA) nodeOne nodeTwo = true →
      isSameComponent (unionFindJoin (unionFindJoin links firstB secondB) firstA secondA)
        nodeOne nodeTwo = true := fun nodeOne nodeTwo inInner =>
    isSameComponent_unionFindJoin_lift links
      (unionFindJoin (unionFindJoin links firstB secondB) firstA secondA)
      forest firstA secondA liftBaseSwapped joinedA nodeOne nodeTwo inInner
  exact isSameComponent_unionFindJoin_lift (unionFindJoin links firstA secondA)
    (unionFindJoin (unionFindJoin links firstB secondB) firstA secondA)
    forestA firstB secondB liftInner joinedB probeOne probeTwo inOrdered

/-- ★ **Join-order independence of the same-component view** — the two-join swap.  Swapping two
`unionFindJoin`s leaves the same-component view pointwise EQUAL (forest-conditioned on the base).  This is
the partition-side atom of the block-swap witness's `componentComm`: the two run orders' partition
evolutions are homogeneous join folds (`stepCap_links_eq_unionFindJoin`), and transposing adjacent joins is
invisible to the component view. -/
theorem isSameComponent_unionFindJoin_swap (links : List (Nat × Nat))
    (forest : isUnionFindForest links) (firstA secondA firstB secondB probeOne probeTwo : Nat) :
    isSameComponent (unionFindJoin (unionFindJoin links firstA secondA) firstB secondB)
        probeOne probeTwo
      = isSameComponent (unionFindJoin (unionFindJoin links firstB secondB) firstA secondA)
        probeOne probeTwo := by
  cases hordered : isSameComponent
      (unionFindJoin (unionFindJoin links firstA secondA) firstB secondB) probeOne probeTwo with
  | true =>
      exact (isSameComponent_acrossSwappedJoins links forest firstA secondA firstB secondB
        probeOne probeTwo hordered).symm
  | false =>
      cases hswapped : isSameComponent
          (unionFindJoin (unionFindJoin links firstB secondB) firstA secondA) probeOne probeTwo with
      | true =>
          have backTransported : isSameComponent
              (unionFindJoin (unionFindJoin links firstA secondA) firstB secondB)
              probeOne probeTwo = true :=
            isSameComponent_acrossSwappedJoins links forest firstB secondB firstA secondA
              probeOne probeTwo hswapped
          rw [hordered] at backTransported
          exact Bool.noConfusion backTransported
      | false => rfl

/-! ## The loop-increment exchange -/

/-- The cap's loop bookkeeping, additively: loops after a cap = loops before + the same-component test
(as a `Bool.toNat` increment).  The additive form the exchange law composes through. -/
theorem stepCap_loops_eq_addIncrement (state : WireState) (position : Nat) :
    (stepCap state position).loops
      = state.loops
          + (isSameComponent state.links (natListGetAt state.openWires position)
              (natListGetAt state.openWires (position + 1))).toNat := by
  rw [stepCap_loops]
  cases htest : isSameComponent state.links (natListGetAt state.openWires position)
      (natListGetAt state.openWires (position + 1)) with
  | true => rfl
  | false => rfl

/-- ★ **The loop-increment exchange** — the total loop increment of two caps is join-order invariant.
The cap's increment is its outer same-component test; when two caps fire in transposed order, each one's
test runs against the OTHER's join in exactly one of the two orders.  The mixed cases collapse without any
transitivity argument: if the first pair is already connected, its join is a NO-OP
(`unionFindJoin_ofSameComponent`) so the other cap's test is unchanged, while its own membership survives
as the first disjunct of the characterization.  The both-disconnected case is the flat-disjunction
identity up to `&&`-commutation, closed by casing the cross atoms. -/
theorem sameComponentIncrement_unionFindJoin_swap (links : List (Nat × Nat))
    (forest : isUnionFindForest links) (firstLeft firstRight secondLeft secondRight : Nat) :
    (isSameComponent links firstLeft firstRight).toNat
        + (isSameComponent (unionFindJoin links firstLeft firstRight)
            secondLeft secondRight).toNat
      = (isSameComponent links secondLeft secondRight).toNat
          + (isSameComponent (unionFindJoin links secondLeft secondRight)
              firstLeft firstRight).toNat := by
  cases hfirst : isSameComponent links firstLeft firstRight with
  | true =>
      rw [unionFindJoin_ofSameComponent links firstLeft firstRight hfirst]
      cases hsecond : isSameComponent links secondLeft secondRight with
      | true =>
          rw [unionFindJoin_ofSameComponent links secondLeft secondRight hsecond, hfirst]
      | false =>
          rw [isSameComponent_unionFindJoin links forest secondLeft secondRight
            firstLeft firstRight, hfirst]
          rfl
  | false =>
      cases hsecond : isSameComponent links secondLeft secondRight with
      | true =>
          rw [unionFindJoin_ofSameComponent links secondLeft secondRight hsecond, hfirst,
            isSameComponent_unionFindJoin links forest firstLeft firstRight
              secondLeft secondRight, hsecond]
          rfl
      | false =>
          rw [isSameComponent_unionFindJoin links forest firstLeft firstRight
              secondLeft secondRight,
            isSameComponent_unionFindJoin links forest secondLeft secondRight
              firstLeft firstRight,
            hfirst, hsecond,
            isSameComponent_symm links secondLeft firstLeft,
            isSameComponent_symm links secondRight firstRight]
          cases hcrossLeftLeft : isSameComponent links firstLeft secondLeft with
          | true =>
              cases hcrossRightRight : isSameComponent links firstRight secondRight with
              | true => rfl
              | false =>
                  cases hcrossLeftRight : isSameComponent links firstLeft secondRight with
                  | true =>
                      cases hcrossRightLeft : isSameComponent links secondLeft firstRight with
                      | true => rfl
                      | false => rfl
                  | false =>
                      cases hcrossRightLeft : isSameComponent links secondLeft firstRight with
                      | true => rfl
                      | false => rfl
          | false =>
              cases hcrossLeftRight : isSameComponent links firstLeft secondRight with
              | true =>
                  cases hcrossRightLeft : isSameComponent links secondLeft firstRight with
                  | true => rfl
                  | false => rfl
              | false =>
                  cases hcrossRightLeft : isSameComponent links secondLeft firstRight with
                  | true => rfl
                  | false => rfl

/-! ## Honesty marker -/

/-- **Honesty marker — the same-component join algebra is PROVED, including the join-order swap.**  The
flat-disjunction characterization (`isSameComponent_unionFindJoin`, forest-conditioned), the
join-homogeneity of the fold's link updates (`stepCap_links_eq_unionFindJoin` — the cap's outer test is
redundant for `links`), the equivalence-relation kit (`_self` / `_symm` / `_trans` / `_flip`), the
join monotonicity/pairing facts (`_ofBase` / `_joined`), the universal-property elimination (`_lift`),
★ the two-join swap (`isSameComponent_unionFindJoin_swap`) — join-order independence of the same-component
view, the partition-side atom of the block-swap witness's `componentComm` — and ★ the loop-increment
exchange (`sameComponentIncrement_unionFindJoin_swap` + `stepCap_loops_eq_addIncrement`) — the total loop
increment of two transposed caps is order-invariant, the `loopsEq` atom.  Remaining for the witness: the
wire-window locality (`openMap`) and the `blockRotate` assembly; see
`fxMode_hasMatchingComponentCoreSwapWitness`.  `= true`. -/
def fxMode_hasSameComponentJoinAlgebra : Bool := true

end FX1Poly.Polygraph
