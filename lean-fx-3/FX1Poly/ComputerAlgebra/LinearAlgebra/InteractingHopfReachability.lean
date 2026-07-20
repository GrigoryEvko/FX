import FX1Poly.ComputerAlgebra.LinearAlgebra.InteractingHopfCompleteness

/-! # LinearAlgebra/InteractingHopfReachability — the IH_Q reachability leg

The committed toolbox (`InteractingHopfSchema`) ships the presentation
congruence `IhzConv` (padded schema steps + reflexivity + symmetry +
transitivity) with the fourteen scalar `IhzRowMove` schemas and the whisker
embedding of every seed row, ALL sound (`ihzConvSpanEqB`).  What was owner-false
was `ihzReachabilityStatement` — span-equal well-formed diagrams on matching
boundaries are `IhzConv`-related — with the residual named as an
absorption-style layer induction (LEG B, confluence) plus RREF uniqueness
(LEG A canonicity).

This file supplies:

* T1 — the fourteen scalar `IhzRowMove` schemas re-exposed as named `IhzConv`
  per-layer rewrite STEPS (the toolbox atoms the induction chains).  Each is a
  one-line instance of the committed `ihzMoveConv`; nothing is re-derived.

* T2 — the A8 bimonoid, I3/I4 white/black Frobenius (both chain equations), and
  I7/I8 special collapses re-exposed as named `IhzConv` absorption STEPS (the
  confluence-critical rewrites), each an instance of `ihzMoveConv` on the
  committed `whiskerMove` row arm.

* T3 — the reachability FACTORIZATION.  `ihkConvOfCommonReduct` is the
  reduce-both-to-a-common-form principle (transitivity + symmetry).
  `ihkReachabilityOfChooserReductionAndCanonicity` PROVES that
  `ihzReachabilityStatement` follows from any normal-form chooser satisfying
  (i) a reduction leg (`IhzConv diagram (chooseNf diagram)`) and (ii) a
  canonicity leg (span-equal WF diagrams pick the SAME chooser output).  This
  machine-checks the honest content: reachability = reduction ∧ canonicity.
  The reflexive fragment `ihkReachabilityDiagonal` is proven outright.

* T4 — the PAYOFF, honestly conditional.  `ihkWordProblemGivenReachability`
  routes the committed capstone: given reachability, `IhzConv` is EQUIVALENT to
  the executable span decision.  `ihkWordProblemOfChooserReductionAndCanonicity`
  combines T3 + the capstone: modulo the two owner-false legs, the FULL IH_Q
  syntactic word problem is unconditional.

* T5 — ground fires: a scalar product step, a bimonoid absorption, a sum
  diagram reduced to its scalar normal form, a cancel-to-wire, a two-different
  -diagram common-reduct fire, and a discriminating FALSE control (scalar 2 and
  scalar 3 lines are NOT `IhzConv`).

WALLS.  The full layer-induction reachability is NOT proven; the two legs of
the factorization are owner-false.  `ihkHasReductionLeg := false` (LEG B: the
absorption rewrite system's confluence — the unjoined critical peak is the A8
bimonoid / A18 sum overlap on an interior `blackComult ; whiteMult` interface,
whose two normal forms are only span-equal, not committed-`IhzConv`).
`ihkHasCanonicityLeg := false` (LEG A: span-equal ⇒ equal canonical matrix is
`ihqRrefUniquenessStatement`, owner-false).  `ihkHasFullReachabilityInduction
:= false`.

Raw Lean 4 + Init + the committed ComputerAlgebra bricks only; zero-axiom;
structural only; no wildcard match arms over inductive scrutinees.
Per-declaration gate in the audit twin. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 8192

namespace FX1Poly.ComputerAlgebra

/-! ## T1 — the fourteen scalar schemas as named `IhzConv` per-layer steps -/

/-- A12: two scalar boxes in series fuse to their product box. -/
theorem ihkProductStep (firstScalar secondScalar : QnfRat) :
    IhzConv
      { sourceArity := 1
        layers := [[IhsCell.scalarBox firstScalar],
          [IhsCell.scalarBox secondScalar]] }
      { sourceArity := 1
        layers := [[IhsCell.scalarBox (qnfMul firstScalar secondScalar)]] } :=
  ihzMoveConv (IhzRowMove.productSchema firstScalar secondScalar)

/-- A12op: the mirror product. -/
theorem ihkProductMirrorStep (firstScalar secondScalar : QnfRat) :
    IhzConv
      { sourceArity := 1
        layers := [[IhsCell.scalarBoxMirror firstScalar],
          [IhsCell.scalarBoxMirror secondScalar]] }
      { sourceArity := 1
        layers := [[IhsCell.scalarBoxMirror (qnfMul firstScalar secondScalar)]] } :=
  ihzMoveConv (IhzRowMove.productMirrorSchema firstScalar secondScalar)

/-- A13: a scalar pushed backward through a white multiply duplicates. -/
theorem ihkThroughAddStep (scalarValue : QnfRat) :
    IhzConv
      { sourceArity := 2
        layers := [[IhsCell.whiteMult], [IhsCell.scalarBox scalarValue]] }
      { sourceArity := 2
        layers := [[IhsCell.scalarBox scalarValue, IhsCell.scalarBox scalarValue],
          [IhsCell.whiteMult]] } :=
  ihzMoveConv (IhzRowMove.throughAddSchema scalarValue)

/-- A13op: a mirror scalar pushed forward through a white comultiply. -/
theorem ihkThroughCoaddStep (scalarValue : QnfRat) :
    IhzConv
      { sourceArity := 1
        layers := [[IhsCell.scalarBoxMirror scalarValue], [IhsCell.whiteComult]] }
      { sourceArity := 1
        layers := [[IhsCell.whiteComult],
          [IhsCell.scalarBoxMirror scalarValue,
            IhsCell.scalarBoxMirror scalarValue]] } :=
  ihzMoveConv (IhzRowMove.throughCoaddSchema scalarValue)

/-- A14: a scalar after a white unit is absorbed. -/
theorem ihkZeroAbsorbStep (scalarValue : QnfRat) :
    IhzConv
      { sourceArity := 0
        layers := [[IhsCell.whiteUnit], [IhsCell.scalarBox scalarValue]] }
      { sourceArity := 0, layers := [[IhsCell.whiteUnit]] } :=
  ihzMoveConv (IhzRowMove.zeroAbsorbSchema scalarValue)

/-- A14op: a mirror scalar before a white counit is absorbed. -/
theorem ihkCozeroAbsorbStep (scalarValue : QnfRat) :
    IhzConv
      { sourceArity := 1
        layers := [[IhsCell.scalarBoxMirror scalarValue], [IhsCell.whiteCounit]] }
      { sourceArity := 1, layers := [[IhsCell.whiteCounit]] } :=
  ihzMoveConv (IhzRowMove.cozeroAbsorbSchema scalarValue)

/-- A15: a scalar pushed forward through a black comultiply duplicates. -/
theorem ihkThroughCopyStep (scalarValue : QnfRat) :
    IhzConv
      { sourceArity := 1
        layers := [[IhsCell.scalarBox scalarValue], [IhsCell.blackComult]] }
      { sourceArity := 1
        layers := [[IhsCell.blackComult],
          [IhsCell.scalarBox scalarValue, IhsCell.scalarBox scalarValue]] } :=
  ihzMoveConv (IhzRowMove.throughCopySchema scalarValue)

/-- A15op: a mirror scalar pushed backward through a black multiply. -/
theorem ihkThroughCocopyStep (scalarValue : QnfRat) :
    IhzConv
      { sourceArity := 2
        layers := [[IhsCell.blackMult], [IhsCell.scalarBoxMirror scalarValue]] }
      { sourceArity := 2
        layers := [[IhsCell.scalarBoxMirror scalarValue,
          IhsCell.scalarBoxMirror scalarValue], [IhsCell.blackMult]] } :=
  ihzMoveConv (IhzRowMove.throughCocopySchema scalarValue)

/-- A16: a scalar into a black counit is absorbed. -/
theorem ihkDiscardAbsorbStep (scalarValue : QnfRat) :
    IhzConv
      { sourceArity := 1
        layers := [[IhsCell.scalarBox scalarValue], [IhsCell.blackCounit]] }
      { sourceArity := 1, layers := [[IhsCell.blackCounit]] } :=
  ihzMoveConv (IhzRowMove.discardAbsorbSchema scalarValue)

/-- A16op: a mirror scalar after a black unit is absorbed. -/
theorem ihkUnitAbsorbStep (scalarValue : QnfRat) :
    IhzConv
      { sourceArity := 0
        layers := [[IhsCell.blackUnit], [IhsCell.scalarBoxMirror scalarValue]] }
      { sourceArity := 0, layers := [[IhsCell.blackUnit]] } :=
  ihzMoveConv (IhzRowMove.unitAbsorbSchema scalarValue)

/-- A18: a copy fan, a scalar pair, and an add fan fuse to the SUM box. -/
theorem ihkSumStep (firstScalar secondScalar : QnfRat) :
    IhzConv
      { sourceArity := 1
        layers := [[IhsCell.blackComult],
          [IhsCell.scalarBox firstScalar, IhsCell.scalarBox secondScalar],
          [IhsCell.whiteMult]] }
      { sourceArity := 1
        layers := [[IhsCell.scalarBox (qnfAdd firstScalar secondScalar)]] } :=
  ihzMoveConv (IhzRowMove.sumSchema firstScalar secondScalar)

/-- A18op: the mirror sum. -/
theorem ihkSumMirrorStep (firstScalar secondScalar : QnfRat) :
    IhzConv
      { sourceArity := 1
        layers := [[IhsCell.whiteComult],
          [IhsCell.scalarBoxMirror firstScalar,
            IhsCell.scalarBoxMirror secondScalar],
          [IhsCell.blackMult]] }
      { sourceArity := 1
        layers := [[IhsCell.scalarBoxMirror (qnfAdd firstScalar secondScalar)]] } :=
  ihzMoveConv (IhzRowMove.sumMirrorSchema firstScalar secondScalar)

/-- I1: a nonzero scalar cancels against its mirror to the wire. -/
theorem ihkForwardCancelStep (scalarValue : QnfRat)
    (hNonzero : scalarValue ≠ qnfZero) :
    IhzConv
      { sourceArity := 1
        layers := [[IhsCell.scalarBox scalarValue],
          [IhsCell.scalarBoxMirror scalarValue]] }
      { sourceArity := 1, layers := [[IhsCell.wire]] } :=
  ihzMoveConv (IhzRowMove.forwardCancelSchema scalarValue hNonzero)

/-- I2: a nonzero mirror scalar cancels against its box to the wire. -/
theorem ihkBackwardCancelStep (scalarValue : QnfRat)
    (hNonzero : scalarValue ≠ qnfZero) :
    IhzConv
      { sourceArity := 1
        layers := [[IhsCell.scalarBoxMirror scalarValue],
          [IhsCell.scalarBox scalarValue]] }
      { sourceArity := 1, layers := [[IhsCell.wire]] } :=
  ihzMoveConv (IhzRowMove.backwardCancelSchema scalarValue hNonzero)

/-! ## T2 — the A8 / I3 / I4 / I7 / I8 absorption steps as named `IhzConv` -/

/-- A8 bimonoid: a white multiply above a black comultiply absorbs into the
copy/add tangle `(copy⊗copy);(id⊗swap⊗id);(add⊗add)`. -/
theorem ihkBimonoidStep :
    IhzConv (ihsRowLhs IhsRowTag.bimonoid) (ihsRowRhs IhsRowTag.bimonoid) :=
  ihzMoveConv (IhzRowMove.whiskerMove (IhwWindowMove.row IhsRowTag.bimonoid))

/-- A8op bimonoid mirror. -/
theorem ihkBimonoidOpStep :
    IhzConv (ihsRowLhs IhsRowTag.bimonoidOp) (ihsRowRhs IhsRowTag.bimonoidOp) :=
  ihzMoveConv (IhzRowMove.whiskerMove (IhwWindowMove.row IhsRowTag.bimonoidOp))

/-- I3 white Frobenius, left equation: `(coadd⊗id);(id⊗add) = add;coadd`. -/
theorem ihkWhiteFrobeniusLeftStep :
    IhzConv (ihsRowLhs IhsRowTag.whiteFrobeniusLeft)
      (ihsRowRhs IhsRowTag.whiteFrobeniusLeft) :=
  ihzMoveConv
    (IhzRowMove.whiskerMove (IhwWindowMove.row IhsRowTag.whiteFrobeniusLeft))

/-- I3 white Frobenius, right equation: `(id⊗coadd);(add⊗id) = add;coadd`. -/
theorem ihkWhiteFrobeniusRightStep :
    IhzConv (ihsRowLhs IhsRowTag.whiteFrobeniusRight)
      (ihsRowRhs IhsRowTag.whiteFrobeniusRight) :=
  ihzMoveConv
    (IhzRowMove.whiskerMove (IhwWindowMove.row IhsRowTag.whiteFrobeniusRight))

/-- I4 black Frobenius, left equation: `(copy⊗id);(id⊗cocopy) = cocopy;copy`. -/
theorem ihkBlackFrobeniusLeftStep :
    IhzConv (ihsRowLhs IhsRowTag.blackFrobeniusLeft)
      (ihsRowRhs IhsRowTag.blackFrobeniusLeft) :=
  ihzMoveConv
    (IhzRowMove.whiskerMove (IhwWindowMove.row IhsRowTag.blackFrobeniusLeft))

/-- I4 black Frobenius, right equation: `(id⊗copy);(cocopy⊗id) = cocopy;copy`. -/
theorem ihkBlackFrobeniusRightStep :
    IhzConv (ihsRowLhs IhsRowTag.blackFrobeniusRight)
      (ihsRowRhs IhsRowTag.blackFrobeniusRight) :=
  ihzMoveConv
    (IhzRowMove.whiskerMove (IhwWindowMove.row IhsRowTag.blackFrobeniusRight))

/-- I7 white special: `coadd;add = id` — the white bubble collapses. -/
theorem ihkWhiteSpecialStep :
    IhzConv (ihsRowLhs IhsRowTag.whiteSpecial)
      (ihsRowRhs IhsRowTag.whiteSpecial) :=
  ihzMoveConv (IhzRowMove.whiskerMove (IhwWindowMove.row IhsRowTag.whiteSpecial))

/-- I8 black special: `copy;cocopy = id` — the black bubble collapses. -/
theorem ihkBlackSpecialStep :
    IhzConv (ihsRowLhs IhsRowTag.blackSpecial)
      (ihsRowRhs IhsRowTag.blackSpecial) :=
  ihzMoveConv (IhzRowMove.whiskerMove (IhwWindowMove.row IhsRowTag.blackSpecial))

/-! ## T3 — the reachability factorization -/

/-- THE COMMON-REDUCT PRINCIPLE: if two diagrams both convert to a shared form,
they convert to each other.  Pure transitivity + symmetry of `IhzConv` — the
shape every reachability argument takes. -/
theorem ihkConvOfCommonReduct {firstDiagram secondDiagram normalForm : IhsDiagram}
    (hFirst : IhzConv firstDiagram normalForm)
    (hSecond : IhzConv secondDiagram normalForm) :
    IhzConv firstDiagram secondDiagram :=
  IhzConv.trans hFirst (IhzConv.symm hSecond)

/-- THE REFLEXIVE FRAGMENT of reachability: a well-formed diagram is `IhzConv`
to itself (the diagonal case, unconditional). -/
theorem ihkReachabilityDiagonal (diagram : IhsDiagram)
    (hWF : IhsDiagramWF diagram) : IhzConv diagram diagram :=
  IhzConv.refl diagram hWF

/-- **THE REACHABILITY FACTORIZATION**: `ihzReachabilityStatement` follows from
any normal-form chooser equipped with two legs —

  (reduction leg) every well-formed diagram converts to its chooser output;
  (canonicity leg) span-equal well-formed diagrams on matching boundaries pick
    the SAME chooser output —

joined by the common-reduct principle.  This machine-checks the honest content
of the reachability problem: it is EXACTLY the conjunction of a reduction leg
(LEG B, the absorption confluence) and a canonicity leg (LEG A, RREF
uniqueness).  Both legs are owner-false in the committed kit (see the walls);
this theorem is the reduction of the whole problem to those two, with nothing
else missing. -/
theorem ihkReachabilityOfChooserReductionAndCanonicity
    (chooseNormalForm : IhsDiagram -> IhsDiagram)
    (hReduce : (diagram : IhsDiagram) -> IhsDiagramWF diagram ->
      IhzConv diagram (chooseNormalForm diagram))
    (hCanon : (firstDiagram secondDiagram : IhsDiagram) ->
      IhsDiagramWF firstDiagram -> IhsDiagramWF secondDiagram ->
      firstDiagram.sourceArity = secondDiagram.sourceArity ->
      ihsDiagramCodArity firstDiagram = ihsDiagramCodArity secondDiagram ->
      IhsRelEquiv firstDiagram.sourceArity (ihsDiagramCodArity firstDiagram)
        (ihsDiagramDenote firstDiagram) (ihsDiagramDenote secondDiagram) ->
      chooseNormalForm firstDiagram = chooseNormalForm secondDiagram) :
    ihzReachabilityStatement := by
  intro firstDiagram secondDiagram hFirstWF hSecondWF hSource hCod hEquiv
  have hReduceFirst : IhzConv firstDiagram (chooseNormalForm firstDiagram) :=
    hReduce firstDiagram hFirstWF
  have hReduceSecond : IhzConv secondDiagram (chooseNormalForm secondDiagram) :=
    hReduce secondDiagram hSecondWF
  have hSame : chooseNormalForm firstDiagram = chooseNormalForm secondDiagram :=
    hCanon firstDiagram secondDiagram hFirstWF hSecondWF hSource hCod hEquiv
  rw [<- hSame] at hReduceSecond
  exact ihkConvOfCommonReduct hReduceFirst hReduceSecond

/-! ## T4 — the payoff (conditional on the reachability legs) -/

/-- Given reachability, `IhzConv` is EQUIVALENT to the executable span decision:
the committed conditional capstone, re-exposed at the reachability leg. -/
theorem ihkWordProblemGivenReachability (hReach : ihzReachabilityStatement)
    (firstDiagram secondDiagram : IhsDiagram)
    (hFirstWF : IhsDiagramWF firstDiagram) (hSecondWF : IhsDiagramWF secondDiagram)
    (hSource : firstDiagram.sourceArity = secondDiagram.sourceArity)
    (hCod : ihsDiagramCodArity firstDiagram = ihsDiagramCodArity secondDiagram) :
    IhzConv firstDiagram secondDiagram
      <-> ihqSpanEqB (ihsDiagramDenote firstDiagram)
            (ihsDiagramDenote secondDiagram) = true :=
  cvzWordProblemBiconditionalGivenReachability hReach firstDiagram secondDiagram
    hFirstWF hSecondWF hSource hCod

/-- **THE FULL WORD PROBLEM MODULO THE TWO LEGS**: supplying a chooser with the
reduction and canonicity legs discharges reachability (T3) and hence makes the
IH_Q syntactic word problem UNCONDITIONAL — `IhzConv` is equivalent to the
executable span decision on every well-formed pair with matching boundaries.
The only remaining obligations are the two owner-false legs. -/
theorem ihkWordProblemOfChooserReductionAndCanonicity
    (chooseNormalForm : IhsDiagram -> IhsDiagram)
    (hReduce : (diagram : IhsDiagram) -> IhsDiagramWF diagram ->
      IhzConv diagram (chooseNormalForm diagram))
    (hCanon : (firstDiagram secondDiagram : IhsDiagram) ->
      IhsDiagramWF firstDiagram -> IhsDiagramWF secondDiagram ->
      firstDiagram.sourceArity = secondDiagram.sourceArity ->
      ihsDiagramCodArity firstDiagram = ihsDiagramCodArity secondDiagram ->
      IhsRelEquiv firstDiagram.sourceArity (ihsDiagramCodArity firstDiagram)
        (ihsDiagramDenote firstDiagram) (ihsDiagramDenote secondDiagram) ->
      chooseNormalForm firstDiagram = chooseNormalForm secondDiagram)
    (firstDiagram secondDiagram : IhsDiagram)
    (hFirstWF : IhsDiagramWF firstDiagram) (hSecondWF : IhsDiagramWF secondDiagram)
    (hSource : firstDiagram.sourceArity = secondDiagram.sourceArity)
    (hCod : ihsDiagramCodArity firstDiagram = ihsDiagramCodArity secondDiagram) :
    IhzConv firstDiagram secondDiagram
      <-> ihqSpanEqB (ihsDiagramDenote firstDiagram)
            (ihsDiagramDenote secondDiagram) = true :=
  ihkWordProblemGivenReachability
    (ihkReachabilityOfChooserReductionAndCanonicity chooseNormalForm hReduce hCanon)
    firstDiagram secondDiagram hFirstWF hSecondWF hSource hCod

/-! ## Decision markers and walls -/

/-- DECIDED (T1+T2): the fourteen scalar schemas and the A8/I3/I4/I7/I8
absorption rows all ship as named `IhzConv` per-layer steps. -/
def ihkHasRewriteSteps : Bool := true

/-- DECIDED (T3): the common-reduct principle and the reachability
factorization (`ihkReachabilityOfChooserReductionAndCanonicity`) ship, reducing
reachability to a reduction leg plus a canonicity leg. -/
def ihkHasReachabilityFactorization : Bool := true

/-- DECIDED (T4): the word problem is unconditional modulo the two legs
(`ihkWordProblemOfChooserReductionAndCanonicity`). -/
def ihkHasConditionalWordProblem : Bool := true

/-- OWNER FALSE (LEG B, the reduction leg): no committed chooser satisfies the
reduction leg `IhzConv diagram (chooseNormalForm diagram)` for every well-formed
diagram.  The residual is the absorption-style layer induction whose confluence
is unestablished.  Burned attack (1): structural induction over
`firstDiagram.layers` stalls at the inductive step — absorbing the leading
generator into the accumulated span form is a whisker-context rewrite `IhzConv`
witnesses, but the repeated absorption has no committed termination/confluence
argument.  Burned attack (2): reduce-via-the-compiler stalls because the NF
compiler recurses on the DENOTATION matrix, not the layers, so no structural
handle relates the two syntactically.  THE UNJOINED CRITICAL PEAK: the A8
`bimonoid` rewrite (`whiteMult ; blackComult ⟿ (copy⊗copy);(id⊗swap⊗id);
(add⊗add)`) overlaps the A18 `sumSchema` (`blackComult ; [box,box] ; whiteMult
⟿ box(a+b)`) on an interior `blackComult ; whiteMult` interface when sum
gadgets are stacked; the two resulting forms are span-equal but no committed
`IhzConv` derivation joins them without RREF uniqueness. -/
def ihkHasReductionLeg : Bool := false

/-- OWNER FALSE (LEG A, the canonicity leg): no committed chooser satisfies the
canonicity leg — span-equal well-formed diagrams need not pick the same chooser
output, because that is precisely span-equal ⇒ equal canonical matrix, i.e.
`ihqRrefUniquenessStatement` (`ihqRrefUniquenessIsProven := false`), which needs
a rank/independence/exchange apparatus absent from the `QnfRat` kit (MathComp
`mxalgebra` never proves RREF uniqueness either). -/
def ihkHasCanonicityLeg : Bool := false

/-- OWNER FALSE: the full layer-induction reachability is NOT proven.  It is
`ihkReachabilityOfChooserReductionAndCanonicity` applied to a chooser meeting
both `ihkHasReductionLeg` and `ihkHasCanonicityLeg`, both owner-false; coincides
with the committed `ihzReachabilityIsProven := false`. -/
def ihkHasFullReachabilityInduction : Bool := false

/-! ## T5 — ground fires and a discriminating control -/

/-- `scalarBox 2` in the singleton line diagram (control carrier). -/
def ihkScalarTwoLineDiagram : IhsDiagram :=
  { sourceArity := 1, layers := [[IhsCell.scalarBox ihsScalarTwo]] }

/-- `scalarBox 3` in the singleton line diagram (control carrier). -/
def ihkScalarThreeLineDiagram : IhsDiagram :=
  { sourceArity := 1, layers := [[IhsCell.scalarBox ihsScalarThree]] }

/-- The canonical scalar 2 is apart from zero (needed by the cancel schemas). -/
theorem ihkScalarTwoIsNonzero : ihsScalarTwo ≠ qnfZero :=
  ihqQnfNeZeroOfBeqZeroFalse rfl

/-- FIRE 1 (scalar row-move): `scalarBox 2 ; scalarBox 3` converts to the
product box, on the concrete two-layer diagram. -/
theorem ihkFireProductConcrete :
    IhzConv
      { sourceArity := 1
        layers := [[IhsCell.scalarBox ihsScalarTwo],
          [IhsCell.scalarBox ihsScalarThree]] }
      { sourceArity := 1
        layers := [[IhsCell.scalarBox (qnfMul ihsScalarTwo ihsScalarThree)]] } :=
  ihkProductStep ihsScalarTwo ihsScalarThree

/-- FIRE 2 (absorption step): the concrete white-multiply-above-black-comultiply
diagram absorbs into the bimonoid tangle. -/
theorem ihkFireBimonoidConcrete :
    IhzConv
      { sourceArity := 2, layers := [[IhsCell.whiteMult], [IhsCell.blackComult]] }
      (ihsRowRhs IhsRowTag.bimonoid) :=
  ihkBimonoidStep

/-- FIRE 3 (small diagram reduced to its normal form): the copy/scalar-pair/add
sum gadget for scalars 2 and 3 reduces to the single scalar box `2 + 3`. -/
theorem ihkFireSumToNormalForm :
    IhzConv
      { sourceArity := 1
        layers := [[IhsCell.blackComult],
          [IhsCell.scalarBox ihsScalarTwo, IhsCell.scalarBox ihsScalarThree],
          [IhsCell.whiteMult]] }
      { sourceArity := 1
        layers := [[IhsCell.scalarBox (qnfAdd ihsScalarTwo ihsScalarThree)]] } :=
  ihkSumStep ihsScalarTwo ihsScalarThree

/-- FIRE 4 (cancel to wire): `scalarBox 2 ; scalarBoxMirror 2` reduces to the
wire (2 is nonzero). -/
theorem ihkFireForwardCancelToWire :
    IhzConv
      { sourceArity := 1
        layers := [[IhsCell.scalarBox ihsScalarTwo],
          [IhsCell.scalarBoxMirror ihsScalarTwo]] }
      { sourceArity := 1, layers := [[IhsCell.wire]] } :=
  ihkForwardCancelStep ihsScalarTwo ihkScalarTwoIsNonzero

/-- FIRE 5 (common reduct between two DIFFERENT diagrams): both the forward
`box 2 ; mirror 2` and the backward `mirror 2 ; box 2` cancel to the wire, so
they convert to each other through the common-reduct principle. -/
theorem ihkFireCommonReductCancel :
    IhzConv
      { sourceArity := 1
        layers := [[IhsCell.scalarBox ihsScalarTwo],
          [IhsCell.scalarBoxMirror ihsScalarTwo]] }
      { sourceArity := 1
        layers := [[IhsCell.scalarBoxMirror ihsScalarTwo],
          [IhsCell.scalarBox ihsScalarTwo]] } :=
  ihkConvOfCommonReduct
    (ihkForwardCancelStep ihsScalarTwo ihkScalarTwoIsNonzero)
    (ihkBackwardCancelStep ihsScalarTwo ihkScalarTwoIsNonzero)

set_option maxHeartbeats 4000000 in
/-- FALSE CONTROL (kernel span): the scalar 2 and scalar 3 lines denote DIFFERENT
subspaces of Q² — the executable span decision refutes. -/
theorem ihkFireControlSpanDistinct :
    ihqSpanEqB (ihsDiagramDenote ihkScalarTwoLineDiagram)
      (ihsDiagramDenote ihkScalarThreeLineDiagram) = false := rfl

/-- FALSE CONTROL (discriminating): the scalar 2 and scalar 3 lines are NOT
`IhzConv` — soundness (`ihzConvSpanEqB`) would force the span decision to fire
`true`, contradicting the kernel `false` pin. -/
theorem ihkFireControlNotConv :
    Not (IhzConv ihkScalarTwoLineDiagram ihkScalarThreeLineDiagram) :=
  fun hConv =>
    Bool.noConfusion
      ((ihzConvSpanEqB hConv).symm.trans ihkFireControlSpanDistinct)

end FX1Poly.ComputerAlgebra
