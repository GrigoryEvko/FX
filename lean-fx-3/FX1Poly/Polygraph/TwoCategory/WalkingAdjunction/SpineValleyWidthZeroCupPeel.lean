import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.SpineValleyCellDegenerate
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCupSortComplete
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.AdjunctionAtomRigidity

/-! # SpineValleyWidthZeroCupPeel — the width-0 pure-cup determinacy, reduced to a positivity-FREE
head-cup diagram peel (Track B)

`WidthZeroPureCupDeterminacy` (`SpineValleyCellDegenerate`) is the crux Tier-D residual: two
boundary-chained pure-cup spines over the width-`0` bottom boundary with equal `matchingOfSpineList 0`
are `SpineTraceEquiv`.  Its previously-stated residual was the width-`0` ARC-level cup sort — but that is
positivity-BLOCKED: the shipped `pureCupSpine_sort` hard-requires `0 < bottomCount`, whose sole genuine
consumers (`extractArc_eq_of_atomicTraceEquiv`'s `sigmaFixesZero`, the `arcDiagram_eq_matching` bridge's
`nfPos`) are GENUINELY FALSE at the width-`0` seed, where the fresh counter `nextFresh = bottomCount = 0`
puts identifier `0` on a real cup leg colliding with the extract's `0`-fallback sentinel.

This file ROUTES AROUND that wall by a **first-cup peel that lifts the sub-problem to width `2`** (strictly
positive, where every shipped tool applies).  The enabling fact is seed rigidity: the head cup of a
width-`0` pure-cup spine is forced — it fires at boundary `0`, so its whisker contexts are empty, its
generator's source 1-cell is empty, and the ONLY empty-source generator at the walking adjunction is the
`unit`.  Hence both spines share an IDENTICAL head cup `C0` (`cupHeadChainedZero_eq`, from the shipped
`adjunctionSpineAtom_eq_of_readOffs`), whose target boundary is width `2`.  The tails are pure cups chained
at width `2`.

Given the single positivity-FREE residual `WidthZeroCupHeadDiagramPeel` — that peeling the shared head cup
carries the width-`0` boundary `matchingOf` equality to a width-`2` ARC-structure equality of the tails —
the shipped POSITIVE cup sort `pureCupSpine_sort` (at `bottomCount = 2`) sorts the tails, and
`SpineTraceEquiv.consCongr` re-glues the head.  This lands, all zero-axiom:

  * ★ `cupHeadChainedZero_eq` — the head cup of a width-`0` pure-cup spine is determined (seed rigidity).
  * ★ `WidthZeroCupHeadDiagramPeel` — the isolated positivity-FREE residual: a shared width-`0` head cup's
    boundary-matching equality descends to a width-`2` ARC equality of the tails.  This REPLACES the
    positivity-blocked width-`0` arc sort with a width-`2` diagram identity — the honest, tractable node.
  * ★ `widthZeroPureCupDeterminacy_of_headDiagramPeel` — `WidthZeroPureCupDeterminacy` FROM the peel: the
    empty cross-cases die by a top-port count mismatch; the both-`cons` case peels the shared head, applies
    the peel + the shipped width-`2` sort, and re-glues.  No gate flag is flipped.

Raw Lean 4 + Init; per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## Small `Nat` / `List` length kit (hand-rolled, `propext`-free) -/

/-- Left-cancellation for `Nat` addition (core `Nat.add_left_cancel` is `propext`-tainted). -/
private theorem natAddLeftCancel :
    (base : Nat) → {leftValue rightValue : Nat} →
    base + leftValue = base + rightValue → leftValue = rightValue
  | 0, _, _, sumsEqual => by rw [Nat.zero_add, Nat.zero_add] at sumsEqual; exact sumsEqual
  | base + 1, _, _, sumsEqual =>
      natAddLeftCancel base (Nat.succ.inj (by rw [Nat.succ_add, Nat.succ_add] at sumsEqual; exact sumsEqual))

/-- A sum of two naturals is zero exactly when both summands are (structural, `propext`-free). -/
private theorem natAddZeroSplit :
    (leftValue rightValue : Nat) → leftValue + rightValue = 0 → leftValue = 0 ∧ rightValue = 0
  | 0, 0, _ => ⟨rfl, rfl⟩
  | 0, _ + 1, sumZero => by rw [Nat.zero_add] at sumZero; exact Nat.noConfusion sumZero
  | _ + 1, _, sumZero => by rw [Nat.succ_add] at sumZero; exact Nat.noConfusion sumZero

/-- `(xs ++ ys).length = xs.length + ys.length` (core `List.length_append` leaks `propext`). -/
private theorem peelLengthAppend : (xs ys : List Nat) → (xs ++ ys).length = xs.length + ys.length
  | [], ys => (Nat.zero_add ys.length).symm
  | headWire :: restWires, ys => by
      show (restWires ++ ys).length + 1 = (restWires.length + 1) + ys.length
      rw [peelLengthAppend restWires ys]
      exact Nat.add_right_comm restWires.length ys.length 1

/-- Inserting a `block` grows a wire list's length by `block.length` (position-independent). -/
private theorem peelNatListInsertAtLength :
    (wires : List Nat) → (position : Nat) → (block : List Nat) →
    (natListInsertAt wires position block).length = wires.length + block.length
  | [], 0, block => by
      show (block ++ ([] : List Nat)).length = ([] : List Nat).length + block.length
      rw [peelLengthAppend block []]
      exact Nat.add_comm block.length ([] : List Nat).length
  | [], _ + 1, block => (Nat.zero_add block.length).symm
  | headWire :: restWires, 0, block => by
      show (block ++ (headWire :: restWires)).length = (headWire :: restWires).length + block.length
      rw [peelLengthAppend block (headWire :: restWires)]
      exact Nat.add_comm block.length (headWire :: restWires).length
  | headWire :: restWires, position + 1, block => by
      show (natListInsertAt restWires position block).length + 1 = (restWires.length + 1) + block.length
      rw [peelNatListInsertAtLength restWires position block]
      exact Nat.add_right_comm restWires.length block.length 1

/-- A wire-level cup step adds exactly two open wires (splices the two fresh legs at its window). -/
private theorem stepCup_openWires_length (state : WireState) (position : Nat) :
    (stepCup state position).openWires.length = state.openWires.length + 2 := by
  show (natListInsertAt state.openWires position [state.nextFresh, state.nextFresh + 1]).length
    = state.openWires.length + 2
  rw [peelNatListInsertAtLength]
  rfl

/-- A cup-arity atom's wire step IS the cup step at its window. -/
private theorem stepAtom_cupReduce {overallSource overallTarget : adjunctionGraph.Mode}
    (state : WireState)
    (atom : SpineAtom adjunctionModeSignature overallSource overallTarget)
    (hasCupDomArity : atom.generatorDom.length = 0)
    (hasCupCodArity : atom.generatorCod.length = 2) :
    stepAtom state atom = stepCup state atom.leftContext.length := by
  dsimp only [stepAtom]
  rw [hasCupDomArity, hasCupCodArity]

/-- **A pure-cup spine's final wire-process open-wire count is the seed plus `2 * length`.**  Every atom is
a cup, so every fold step adds two wires; the count accumulates `2` per atom.  Wire-process mirror of
`pureCupProcessArcSpine_openWires_length`. -/
private theorem pureCupProcessSpine_openWires_length
    {overallSource overallTarget : adjunctionGraph.Mode}
    (atoms : List (SpineAtom adjunctionModeSignature overallSource overallTarget))
    (pureCup : AllCupArity atoms) :
    ∀ (state : WireState),
      (processSpine state atoms).openWires.length = state.openWires.length + 2 * atoms.length := by
  induction pureCup with
  | nil =>
      intro state
      show state.openWires.length = state.openWires.length + 2 * 0
      rw [Nat.mul_zero, Nat.add_zero]
  | cons hasCupDomArity hasCupCodArity restAllCup restIH =>
      rename_i headAtom rest
      intro state
      show (processSpine (stepAtom state headAtom) rest).openWires.length
        = state.openWires.length + 2 * (rest.length + 1)
      rw [stepAtom_cupReduce state headAtom hasCupDomArity hasCupCodArity,
        restIH (stepCup state headAtom.leftContext.length), stepCup_openWires_length]
      show state.openWires.length + 2 + 2 * rest.length = state.openWires.length + 2 * (rest.length + 1)
      rw [Nat.mul_succ, Nat.add_assoc, Nat.add_comm 2 (2 * rest.length)]

/-! ## Head-cup rigidity — the head of a width-0 pure-cup spine is determined -/

/-- The whisker contexts of a cup head firing at boundary `0` are empty.  The head's dom boundary width
`leftContext.length + generatorDom.length + rightContext.length` is `0`, and the cup's `generatorDom.length`
is `0`, so both contexts have length `0`. -/
private theorem cupHeadChainedZero_contextsEmpty
    {overallSource overallTarget : adjunctionGraph.Mode}
    (headCup : SpineAtom adjunctionModeSignature overallSource overallTarget)
    (hasCupDomArity : headCup.generatorDom.length = 0)
    (domBoundaryZero : headCup.domBoundaryLength = 0) :
    headCup.leftContext.length = 0 ∧ headCup.rightContext.length = 0 := by
  dsimp only [SpineAtom.domBoundaryLength] at domBoundaryZero
  rw [hasCupDomArity, Nat.add_zero] at domBoundaryZero
  exact natAddZeroSplit _ _ domBoundaryZero

/-- ★ **Head-cup rigidity.**  Two cup heads that both fire at boundary `0` (empty whisker contexts, empty
generator source, cup target) are EQUAL.  Their three arc read-off lengths agree (`0`, `0`, `2`), and their
dom-boundary 1-cells are parallel length-`0` paths, hence equal by seed path rigidity; the shipped
`adjunctionSpineAtom_eq_of_readOffs` then forces the atoms equal. -/
theorem cupHeadChainedZero_eq
    {overallSource overallTarget : adjunctionGraph.Mode}
    (headA headB : SpineAtom adjunctionModeSignature overallSource overallTarget)
    (domArityA : headA.generatorDom.length = 0) (codArityA : headA.generatorCod.length = 2)
    (leftZeroA : headA.leftContext.length = 0) (rightZeroA : headA.rightContext.length = 0)
    (domArityB : headB.generatorDom.length = 0) (codArityB : headB.generatorCod.length = 2)
    (leftZeroB : headB.leftContext.length = 0) (rightZeroB : headB.rightContext.length = 0) :
    headA = headB := by
  have leftLengthsEqual : headA.leftContext.length = headB.leftContext.length := by
    rw [leftZeroA, leftZeroB]
  have domLengthsEqual : headA.generatorDom.length = headB.generatorDom.length := by
    rw [domArityA, domArityB]
  have codLengthsEqual : headA.generatorCod.length = headB.generatorCod.length := by
    rw [codArityA, codArityB]
  have domBoundaryLengthsEqual :
      (composePath headA.leftContext (composePath headA.generatorDom headA.rightContext)).length
        = (composePath headB.leftContext (composePath headB.generatorDom headB.rightContext)).length := by
    rw [composePath_length headA.leftContext (composePath headA.generatorDom headA.rightContext),
      composePath_length headA.generatorDom headA.rightContext,
      composePath_length headB.leftContext (composePath headB.generatorDom headB.rightContext),
      composePath_length headB.generatorDom headB.rightContext,
      leftZeroA, rightZeroA, domArityA, leftZeroB, rightZeroB, domArityB]
  exact adjunctionSpineAtom_eq_of_readOffs headA headB
    (adjunctionPath_eq_of_length_eq _ _ domBoundaryLengthsEqual)
    leftLengthsEqual domLengthsEqual codLengthsEqual

/-! ## The isolated positivity-FREE residual — the head-cup diagram peel -/

/-- ★ **The head-cup diagram peel (the isolated residual).**  Peeling a SHARED width-`0` cup head `headCup`
off two pure-cup tails carries the width-`0` boundary `matchingOf` equality of the headed spines to a
width-`2` ARC-structure equality of the tails.  This is the honest, positivity-FREE replacement for the
positivity-blocked width-`0` arc cup sort: `headCup` fires `0 ⇒ 2`, so its target boundary is width `2`
where every shipped tool (the arc bridge, the positive cup sort) applies; the only content is that removing
the head cup's short chord relates the two diagram computations — a width-`2` diagram identity carrying NO
`0 < …` obligation. -/
def WidthZeroCupHeadDiagramPeel : Prop :=
  ∀ {overallSource overallTarget : adjunctionGraph.Mode}
    (headCup : SpineAtom adjunctionModeSignature overallSource overallTarget)
    (tailFirst tailSecond : List (SpineAtom adjunctionModeSignature overallSource overallTarget)),
    headCup.generatorDom.length = 0 → headCup.generatorCod.length = 2 →
    headCup.leftContext.length = 0 → headCup.rightContext.length = 0 →
    AllCupArity tailFirst → AllCupArity tailSecond →
    SpineBoundaryChained 2 tailFirst → SpineBoundaryChained 2 tailSecond →
    matchingOfSpineList 0 (headCup :: tailFirst) = matchingOfSpineList 0 (headCup :: tailSecond) →
    arcStructureOfSpineList 2 tailFirst = arcStructureOfSpineList 2 tailSecond

/-! ## The reduction — `WidthZeroPureCupDeterminacy` from the peel -/

/-- A cup head chained at `0` hands its tail the width-`2` boundary: its codomain boundary width is
`leftContext.length + generatorCod.length + rightContext.length = 0 + 2 + 0 = 2`. -/
private theorem cupHeadChainedZero_codTwo
    {overallSource overallTarget : adjunctionGraph.Mode}
    (headCup : SpineAtom adjunctionModeSignature overallSource overallTarget)
    (codArity : headCup.generatorCod.length = 2)
    (leftZero : headCup.leftContext.length = 0) (rightZero : headCup.rightContext.length = 0) :
    headCup.codBoundaryLength = 2 := by
  dsimp only [SpineAtom.codBoundaryLength]
  rw [leftZero, codArity, rightZero]

/-- The top-port count of a width-`0` pure-cup spine is `2 * length` — its wire-process open-wire count from
the empty seed.  Used to refute the empty-vs-`cons` cross cases (an empty spine has count `0`, a `cons` cup
spine has count `≥ 2`). -/
private theorem widthZeroPureCup_topCount
    {overallSource overallTarget : adjunctionGraph.Mode}
    (atoms : List (SpineAtom adjunctionModeSignature overallSource overallTarget))
    (pureCup : AllCupArity atoms) :
    (matchingOfSpineList 0 atoms).topCount = (List.range 0).length + 2 * atoms.length := by
  show (processSpine { openWires := List.range 0, links := [], nextFresh := 0, loops := 0 } atoms).openWires.length
    = (List.range 0).length + 2 * atoms.length
  exact pureCupProcessSpine_openWires_length atoms pureCup
    { openWires := List.range 0, links := [], nextFresh := 0, loops := 0 }

/-- ★ **`WidthZeroPureCupDeterminacy` from the head-cup diagram peel.**  The empty cross-cases die by the
top-port count mismatch (`widthZeroPureCup_topCount`: `0 ≠ 2 * (length + 1)`); the both-`cons` case forces
the two heads equal (`cupHeadChainedZero_eq`), applies the peel to descend to a width-`2` ARC equality of the
tails, sorts them with the shipped POSITIVE `pureCupSpine_sort` (`0 < 2`), and re-glues the head with
`SpineTraceEquiv.consCongr`.  So the width-`0` pure-cup determinacy holds GIVEN the single positivity-FREE
residual — no gate flag flipped. -/
theorem widthZeroPureCupDeterminacy_of_headDiagramPeel
    (peel : WidthZeroCupHeadDiagramPeel) : WidthZeroPureCupDeterminacy := by
  intro overallSource overallTarget cupFirst cupSecond pureFirst pureSecond chainedFirst chainedSecond matchEq
  cases pureFirst with
  | nil =>
      cases pureSecond with
      | nil => exact SpineTraceEquiv.refl []
      | cons domArityB codArityB restCupB =>
          rename_i headB tailB
          exfalso
          have countEq : (matchingOfSpineList 0 ([] : List (SpineAtom adjunctionModeSignature overallSource overallTarget))).topCount
              = (matchingOfSpineList 0 (headB :: tailB)).topCount := congrArg DiagramType.topCount matchEq
          rw [widthZeroPureCup_topCount [] AllCupArity.nil,
            widthZeroPureCup_topCount (headB :: tailB) (AllCupArity.cons domArityB codArityB restCupB)] at countEq
          have zeroEq : 0 = 2 * (tailB.length + 1) := natAddLeftCancel (List.range 0).length countEq
          exact Nat.noConfusion zeroEq
  | cons domArityA codArityA restCupA =>
      rename_i headA tailA
      cases pureSecond with
      | nil =>
          exfalso
          have countEq : (matchingOfSpineList 0 (headA :: tailA)).topCount
              = (matchingOfSpineList 0 ([] : List (SpineAtom adjunctionModeSignature overallSource overallTarget))).topCount :=
            congrArg DiagramType.topCount matchEq
          rw [widthZeroPureCup_topCount (headA :: tailA) (AllCupArity.cons domArityA codArityA restCupA),
            widthZeroPureCup_topCount [] AllCupArity.nil] at countEq
          have zeroEq : 0 = 2 * (tailA.length + 1) := natAddLeftCancel (List.range 0).length countEq.symm
          exact Nat.noConfusion zeroEq
      | cons domArityB codArityB restCupB =>
          rename_i headB tailB
          -- both heads fire at boundary 0 with empty whisker contexts
          obtain ⟨headDomZeroA, tailChainedA⟩ := spineBoundaryChained_tail chainedFirst
          obtain ⟨headDomZeroB, tailChainedB⟩ := spineBoundaryChained_tail chainedSecond
          obtain ⟨leftZeroA, rightZeroA⟩ := cupHeadChainedZero_contextsEmpty headA domArityA headDomZeroA
          obtain ⟨leftZeroB, rightZeroB⟩ := cupHeadChainedZero_contextsEmpty headB domArityB headDomZeroB
          -- the two heads are IDENTICAL (seed rigidity)
          have headsEqual : headA = headB :=
            cupHeadChainedZero_eq headA headB domArityA codArityA leftZeroA rightZeroA
              domArityB codArityB leftZeroB rightZeroB
          -- the tails are pure cups chained at width 2
          have tailTwoChainedA : SpineBoundaryChained 2 tailA := by
            rw [cupHeadChainedZero_codTwo headA codArityA leftZeroA rightZeroA] at tailChainedA
            exact tailChainedA
          have tailTwoChainedB : SpineBoundaryChained 2 tailB := by
            rw [cupHeadChainedZero_codTwo headB codArityB leftZeroB rightZeroB] at tailChainedB
            exact tailChainedB
          -- rewrite the second head to the first, then peel to a width-2 arc equality
          subst headsEqual
          have arcTailsEqual : arcStructureOfSpineList 2 tailA = arcStructureOfSpineList 2 tailB :=
            peel headA tailA tailB domArityA codArityA leftZeroA rightZeroA restCupA restCupB
              tailTwoChainedA tailTwoChainedB matchEq
          -- sort the tails with the shipped POSITIVE cup sort
          have tailTrace : SpineTraceEquiv adjunctionModeSignature tailA tailB :=
            pureCupSpine_sort 2 tailA tailB tailTwoChainedA tailTwoChainedB restCupA restCupB
              (by decide) arcTailsEqual
          exact SpineTraceEquiv.consCongr headA tailTrace

/-! ## Honesty marker -/

/-- **★ ESTABLISHED — the width-0 pure-cup determinacy is reduced to a positivity-FREE residual.**
`widthZeroPureCupDeterminacy_of_headDiagramPeel` proves `WidthZeroPureCupDeterminacy` from the single
`WidthZeroCupHeadDiagramPeel` residual by a first-cup peel to width `2`, routing around the width-`0` seed
collision entirely: the head cup is forced to the seed `unit` (`cupHeadChainedZero_eq`, seed rigidity), the
tails run from the strictly-positive width `2`, and the shipped POSITIVE `pureCupSpine_sort` sorts them.

  What this marker does NOT claim (the gate stays `false`):
  * `WidthZeroCupHeadDiagramPeel` — that peeling the shared head cup carries the width-`0` boundary matching
    to a width-`2` tail ARC equality.  This is a positivity-FREE width-`2` diagram identity (a bottom-cup
    chord removal), STRICTLY more tractable than the positivity-blocked width-`0` arc sort it replaces:
    it carries NO `0 < …` obligation, so it is immune to the `nextFresh = bottomCount = 0` collision that
    made the direct `pureCupSpine_sort` at width `0` genuinely false.

So `WidthZeroPureCupDeterminacy` (hence the second residual of `SpineValleyCellDriver`'s reduction) now
reduces to ONE positivity-free diagram peel, not to a positivity-blocked sort.  `convOfMapEq` and the fib-3
gate flags stay `false`.  `= true`. -/
def fxMode_hasSpineValleyWidthZeroCupPeel : Bool := true

end FX1Poly.Polygraph
